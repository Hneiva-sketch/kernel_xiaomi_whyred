/*
 * qca-bringup.c — Puesta en marcha del chip Bluetooth Qualcomm QCA "cherokee"
 * (Redmi Note 5 Pro / whyred / SDM636) desde userspace, sin HAL propietario.
 *
 * Objetivo: tras ejecutarlo, el kernel debe tener un hci0 registrado que
 * bluetoothd pueda usar, sin necesidad de recompilar el kernel ni tocar el DT.
 *
 * Protocolo: implementación directa de la secuencia de
 *   drivers/bluetooth/btqca.c  (qca_uart_setup, qca_download_firmware,
 *                               qca_tlv_send_segment, qca_read_soc_version)
 *   drivers/bluetooth/hci_qca.c (qca_set_baudrate, qca_send_power_pulse,
 *                                qca_wcn3990_init)
 * Ver QCA_PROTOCOLO.md para la especificación completa.
 *
 * Licencia: GPL-2.0 (deriva de código del kernel GPL-2.0)
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <termios.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <time.h>

/* ------------------------------------------------------------------ */
/* Constantes del protocolo (de btqca.h)                              */
/* ------------------------------------------------------------------ */

#define EDL_PATCH_CMD_OPCODE        0xFC00
#define EDL_PATCH_VER_REQ_CMD       0x19
#define EDL_PATCH_TLV_REQ_CMD       0x1E
#define MAX_SIZE_PER_TLV_SEGMENT    243

#define EDL_CMD_REQ_RES_EVT         0x00
#define EDL_APP_VER_RES_EVT         0x02
#define EDL_TVL_DNLD_RES_EVT        0x04

#define EDL_TAG_ID_HCI              17
#define EDL_TAG_ID_DEEP_SLEEP       27

#define QCA_POWERON_PULSE           0xFC
#define QCA_POWEROFF_PULSE          0xC0

/* ---------------- Line discipline / ioctls ---------------- */
/* De include/uapi/linux/tty.h y drivers/bluetooth/hci_uart.h */
#define N_HCI                       15
#define TIOCSETD                    0x5423
#define HCIUARTSETPROTO             _IOW('U', 200, int)
#define HCI_UART_H4                 0    /* protocolo H4 simple, SIN serdev */
#define HCI_UART_QCA                8    /* NO usar: qca_setup exige serdev */

/* HCI */
#define HCI_COMMAND_PKT             0x01
#define HCI_ACLDATA_PKT             0x02
#define HCI_SCODATA_PKT             0x03
#define HCI_EVENT_PKT               0x04
#define HCI_EV_VENDOR               0xFF
#define HCI_EV_CMD_COMPLETE         0x0E
#define HCI_OP_RESET                0x0C03

/* Baudrate enum (índices, de btqca.h: enum qca_bardrate) */
#define QCA_BAUDRATE_115200         0x00
#define QCA_BAUDRATE_921600         0x0A
#define QCA_BAUDRATE_2000000        0x0D
#define QCA_BAUDRATE_3000000        0x0E

/* Modo de descarga (enum rome_tlv_dnld_mode) */
#define ROME_SKIP_EVT_NONE          0
#define ROME_SKIP_EVT_VSE           1
#define ROME_SKIP_EVT_CC            2
#define ROME_SKIP_EVT_VSE_CC        3

/* Timeouts (HCI_INIT_TIMEOUT en el kernel = 10 s) */
#define HCI_INIT_TIMEOUT_MS         10000
#define BAUDRATE_SETTLE_MS          300

/* ------------------------------------------------------------------ */
/* Utilidades                                                          */
/* ------------------------------------------------------------------ */

static int g_verbose = 1;

#define LOG(fmt, ...) do { \
    if (g_verbose) { \
        struct timespec _ts; clock_gettime(CLOCK_MONOTONIC, &_ts); \
        fprintf(stderr, "[%3ld.%03ld] " fmt "\n", \
                (long)_ts.tv_sec, _ts.tv_nsec / 1000000, ##__VA_ARGS__); \
    } \
} while (0)

#define ERR(fmt, ...) fprintf(stderr, "ERROR: " fmt "\n", ##__VA_ARGS__)

static void hexdump(const char *tag, const uint8_t *d, size_t n)
{
    if (!g_verbose) return;
    fprintf(stderr, "  %s (%zu bytes):", tag, n);
    for (size_t i = 0; i < n && i < 64; i++)
        fprintf(stderr, " %02x", d[i]);
    if (n > 64) fprintf(stderr, " ...");
    fprintf(stderr, "\n");
}

static int open_serial(const char *dev)
{
    int fd = open(dev, O_RDWR | O_NOCTTY | O_NONBLOCK);
    if (fd < 0) {
        ERR("no puedo abrir %s: %s", dev, strerror(errno));
        return -1;
    }
    /* volver a modo bloqueante con timeout */
    int fl = fcntl(fd, F_GETFL, 0);
    if (fl >= 0) fcntl(fd, F_SETFL, fl & ~O_NONBLOCK);
    return fd;
}

static int set_baud(int fd, int speed)
{
    struct termios tio;
    if (tcgetattr(fd, &tio) < 0) {
        ERR("tcgetattr: %s", strerror(errno));
        return -1;
    }
    cfmakeraw(&tio);
    tio.c_cflag |= (CLOCAL | CREAD);
    tio.c_cflag &= ~CRTSCTS;          /* flow control se controla aparte */
    tio.c_cc[VMIN]  = 0;
    tio.c_cc[VTIME] = 10;             /* 1 s por lectura */
    if (cfsetispeed(&tio, speed) < 0 || cfsetospeed(&tio, speed) < 0) {
        ERR("cfset*speed(%d): %s", speed, strerror(errno));
        return -1;
    }
    if (tcsetattr(fd, TCSANOW, &tio) < 0) {
        ERR("tcsetattr: %s", strerror(errno));
        return -1;
    }
    if (tcflush(fd, TCIOFLUSH) < 0) {
        ERR("tcflush: %s", strerror(errno));
        return -1;
    }
    return 0;
}

static int set_flow_control(int fd, int on)
{
    struct termios tio;
    if (tcgetattr(fd, &tio) < 0) return -1;
    if (on) tio.c_cflag |=  CRTSCTS;
    else    tio.c_cflag &= ~CRTSCTS;
    return tcsetattr(fd, TCSANOW, &tio);
}

/* ------------------------------------------------------------------ */
/* E/S H4 cruda                                                        */
/* ------------------------------------------------------------------ */

static int write_all(int fd, const uint8_t *buf, size_t n)
{
    size_t off = 0;
    while (off < n) {
        ssize_t w = write(fd, buf + off, n - off);
        if (w < 0) {
            if (errno == EINTR || errno == EAGAIN) continue;
            ERR("write: %s", strerror(errno));
            return -1;
        }
        if (w == 0) { ERR("write devolvió 0"); return -1; }
        off += (size_t)w;
    }
    return 0;
}

/* Lee exactamente n bytes con timeout en ms. Devuelve 0 ok, -1 error/timeout */
static int read_exact(int fd, uint8_t *buf, size_t n, int timeout_ms)
{
    size_t got = 0;
    struct timespec start, now;
    clock_gettime(CLOCK_MONOTONIC, &start);

    while (got < n) {
        ssize_t r = read(fd, buf + got, n - got);
        if (r > 0) { got += (size_t)r; continue; }
        if (r == 0) { /* timeout del VMIN/VTIME */ }
        else if (errno != EINTR && errno != EAGAIN) {
            ERR("read: %s", strerror(errno));
            return -1;
        }
        clock_gettime(CLOCK_MONOTONIC, &now);
        long elapsed = (now.tv_sec - start.tv_sec) * 1000
                     + (now.tv_nsec - start.tv_nsec) / 1000000;
        if (elapsed > timeout_ms) {
            ERR("timeout leyendo %zu bytes (recibidos %zu)", n, got);
            return -1;
        }
    }
    return 0;
}

/* Envía un comando HCI (H4: 01 <len_lo> <len_hi> <opcode_lo> <opcode_hi> <params>) */
static int send_cmd(int fd, uint16_t opcode, const uint8_t *params, uint8_t plen)
{
    uint8_t pkt[3 + 2 + 256];
    size_t n = 0;
    pkt[n++] = HCI_COMMAND_PKT;
    pkt[n++] = plen + 2;
    pkt[n++] = 0x00;
    pkt[n++] = opcode & 0xFF;
    pkt[n++] = (opcode >> 8) & 0xFF;
    if (plen && params) { memcpy(pkt + n, params, plen); n += plen; }
    LOG("TX cmd opcode=0x%04X len=%u", opcode, plen);
    if (g_verbose > 1) hexdump("TX", pkt, n);
    return write_all(fd, pkt, n);
}

/* Envía un byte como HCI_COMMAND_PKT: 01 01 00 <byte>  (para los power pulses) */
static int send_cmd_byte(int fd, uint8_t byte)
{
    uint8_t pkt[4];
    pkt[0] = HCI_COMMAND_PKT;
    pkt[1] = 0x01;
    pkt[2] = 0x00;
    pkt[3] = byte;
    LOG("TX power pulse 0x%02X (raw)", byte);
    return write_all(fd, pkt, sizeof(pkt));
}

/* ------------------------------------------------------------------ */
/* Recepción de eventos                                                */
/* ------------------------------------------------------------------ */

struct event {
    uint8_t  ev;
    uint8_t  data[600];
    size_t   len;
    uint16_t opcode;    /* para CMD_COMPLETE */
    uint8_t  status;
};

static int recv_event(int fd, struct event *ev, int timeout_ms)
{
    uint8_t hdr[2];
    memset(ev, 0, sizeof(*ev));

    /* esperar el byte de tipo de paquete */
    for (;;) {
        if (read_exact(fd, hdr, 1, timeout_ms) < 0) return -1;
        if (hdr[0] == HCI_EVENT_PKT) break;
        LOG("  (descartado byte 0x%02X en espera de evento)", hdr[0]);
    }
    if (read_exact(fd, hdr, 1, timeout_ms) < 0) return -1;
    ev->ev = hdr[0];
    uint8_t plen;
    if (read_exact(fd, &plen, 1, timeout_ms) < 0) return -1;
    if (plen > sizeof(ev->data)) {
        ERR("evento demasiado grande (%u)", plen);
        return -1;
    }
    if (plen && read_exact(fd, ev->data, plen, timeout_ms) < 0) return -1;
    ev->len = plen;

    if (g_verbose > 1) {
        fprintf(stderr, "  RX event 0x%02X len=%u:", ev->ev, plen);
        for (size_t i = 0; i < plen && i < 48; i++)
            fprintf(stderr, " %02x", ev->data[i]);
        fprintf(stderr, "\n");
    }

    if (ev->ev == HCI_EV_CMD_COMPLETE && plen >= 3) {
        ev->status = ev->data[0];
        ev->opcode = ev->data[1] | (ev->data[2] << 8);
    }
    return 0;
}

/* Espera un evento VS (0xFF) y opcionalmente valida cresp/rtype.
 * Devuelve 0 ok; rellena out/outlen con los datos tras la cabecera EDL. */
static int wait_vendor_event(int fd, uint8_t want_rtype,
                             uint8_t *out, size_t *outlen, int timeout_ms)
{
    struct timespec start, now;
    clock_gettime(CLOCK_MONOTONIC, &start);

    for (;;) {
        struct event ev;
        clock_gettime(CLOCK_MONOTONIC, &now);
        long elapsed = (now.tv_sec - start.tv_sec) * 1000
                     + (now.tv_nsec - start.tv_nsec) / 1000000;
        int remain = timeout_ms - (int)elapsed;
        if (remain <= 0) { ERR("timeout esperando evento VS"); return -1; }

        if (recv_event(fd, &ev, remain) < 0) return -1;

        if (ev.ev != HCI_EV_VENDOR) {
            LOG("  evento ignorado 0x%02X", ev.ev);
            continue;
        }
        if (ev.len < 2) { ERR("evento VS corto (%zu)", ev.len); return -1; }

        uint8_t cresp = ev.data[0];
        uint8_t rtype = ev.data[1];
        if (want_rtype != 0xFF && rtype != want_rtype) {
            ERR("evento VS con rtype 0x%02X (esperaba 0x%02X) cresp=0x%02X",
                rtype, want_rtype, cresp);
            return -1;
        }
        if (cresp != EDL_CMD_REQ_RES_EVT) {
            ERR("evento VS con cresp 0x%02X (esperaba 0x00)", cresp);
            return -1;
        }
        if (out && outlen) {
            size_t dl = ev.len - 2;
            if (dl > *outlen) dl = *outlen;
            memcpy(out, ev.data + 2, dl);
            *outlen = dl;
        }
        return 0;
    }
}

/* ------------------------------------------------------------------ */
/* Pasos del protocolo                                                 */
/* ------------------------------------------------------------------ */

/* Petición de versión. Devuelve soc_version o -1. */
static long qca_read_soc_version(int fd)
{
    LOG("== Paso 1: pedir versión del SoC ==");
    uint8_t cmd = EDL_PATCH_VER_REQ_CMD;
    if (send_cmd(fd, EDL_PATCH_CMD_OPCODE, &cmd, 1) < 0) return -1;

    uint8_t data[64]; size_t dl = sizeof(data);
    if (wait_vendor_event(fd, EDL_APP_VER_RES_EVT, data, &dl, HCI_INIT_TIMEOUT_MS) < 0)
        return -1;
    if (dl < 12) { ERR("respuesta de versión corta (%zu < 12)", dl); return -1; }

    uint32_t product_id = (uint32_t)data[0] | ((uint32_t)data[1] << 8)
                        | ((uint32_t)data[2] << 16) | ((uint32_t)data[3] << 24);
    uint16_t patch_ver  = (uint16_t)data[4] | ((uint16_t)data[5] << 8);
    uint16_t rome_ver   = (uint16_t)data[6] | ((uint16_t)data[7] << 8);
    uint32_t soc_id     = (uint32_t)data[8] | ((uint32_t)data[9] << 8)
                        | ((uint32_t)data[10] << 16) | ((uint32_t)data[11] << 24);

    LOG("  product_id=0x%08X patch=0x%04X rom=0x%04X soc_id=0x%08X",
        product_id, patch_ver, rome_ver, soc_id);

    long soc_version = ((long)soc_id << 16) | (rome_ver & 0xFFFF);
    if (soc_version == 0) { ERR("soc_version == 0"); return -1; }
    LOG("  soc_version = 0x%08lX", soc_version);
    return soc_version;
}

/* Lee un fichero completo. */
static uint8_t *read_file(const char *path, size_t *outlen)
{
    FILE *f = fopen(path, "rb");
    if (!f) { ERR("no puedo abrir %s: %s", path, strerror(errno)); return NULL; }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (sz <= 0) { ERR("%s vacío o error", path); fclose(f); return NULL; }
    uint8_t *buf = malloc((size_t)sz);
    if (!buf) { ERR("sin memoria (%ld)", sz); fclose(f); return NULL; }
    if (fread(buf, 1, (size_t)sz, f) != (size_t)sz) {
        ERR("lectura corta de %s", path); free(buf); fclose(f); return NULL;
    }
    fclose(f);
    *outlen = (size_t)sz;
    LOG("  leído %s: %zu bytes", path, *outlen);
    return buf;
}

static uint32_t le32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8)
         | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}
static uint16_t le16(const uint8_t *p) {
    return (uint16_t)p[0] | ((uint16_t)p[1] << 8);
}

/* Envía un segmento TLV. mode controla si se espera respuesta.
 *
 * IMPORTANTE (kernel mainline, qca_download_firmware):
 *   "The last segment is always acked regardless download mode"
 * El llamante pasa mode=NONE en el último segmento. Aquí, además, forzamos
 * la espera si el segmento es más corto que el máximo (equivale a "último"). */
static int tlv_send_segment(int fd, const uint8_t *data, size_t seg,
                            int mode)
{
    uint8_t cmd[MAX_SIZE_PER_TLV_SEGMENT + 2];
    cmd[0] = EDL_PATCH_TLV_REQ_CMD;
    cmd[1] = (uint8_t)seg;
    memcpy(cmd + 2, data, seg);

    if (send_cmd(fd, EDL_PATCH_CMD_OPCODE, cmd, (uint8_t)(seg + 2)) < 0)
        return -1;

    /* En modo VSE/VSE_CC el controlador no responde a cada segmento;
     * solo lo hace en el último. El llamante ya cambia el modo a NONE en
     * el último, pero reforzamos aquí por seguridad. */
    if ((mode == ROME_SKIP_EVT_VSE || mode == ROME_SKIP_EVT_VSE_CC) &&
        seg == MAX_SIZE_PER_TLV_SEGMENT)
        return 0;

    uint8_t data_out[16]; size_t dl = sizeof(data_out);
    if (wait_vendor_event(fd, EDL_TVL_DNLD_RES_EVT, data_out, &dl,
                          HCI_INIT_TIMEOUT_MS) < 0)
        return -1;
    /* respuesta esperada: 1 byte, result == 0x00 */
    if (dl < 1) { ERR("respuesta TLV corta"); return -1; }
    if (data_out[0] != 0x00) {
        ERR("segmento TLV con result 0x%02X", data_out[0]);
        return -1;
    }
    return 0;
}

/* Descarga un fichero TLV (patch o nvm). */
static int qca_download_firmware(int fd, const char *path, int is_nvm,
                                 uint8_t user_baud)
{
    size_t fwlen = 0;
    uint8_t *fw = read_file(path, &fwlen);
    if (!fw) return -1;

    int ret = -1;
    int mode = ROME_SKIP_EVT_NONE;

    if (fwlen < 4) { ERR("TLV sin cabecera"); goto out; }

    if (!is_nvm) {
        /* ---- PATCH ----
         * struct tlv_type_hdr { le32 type_len; }  en offset 0
         * struct tlv_type_patch empieza en offset 4:
         *   le32 total_size    @4
         *   le32 data_length   @8
         *   u8   format_version@12
         *   u8   signature     @13
         *   u8   download_mode @14     <-- lo que necesitamos
         */
        uint32_t type_len = le32(fw);
        uint32_t length   = (type_len >> 8) & 0x00FFFFFF;
        LOG("  PATCH: tipo=%u longitud=%u (fichero %zu)",
            type_len & 0xFF, length, fwlen);
        if (fwlen < 4 + 24) { ERR("TLV de patch corto"); goto out; }
        mode = fw[14];
        LOG("  download_mode = %d (%s)", mode,
            mode == ROME_SKIP_EVT_NONE  ? "NONE" :
            mode == ROME_SKIP_EVT_VSE   ? "VSE" :
            mode == ROME_SKIP_EVT_CC    ? "CC" : "VSE_CC");
        LOG("  total_size=%u data_length=%u",
            le32(fw + 4), le32(fw + 8));
    } else {
        /* ---- NVM ----
         * Lógica del kernel MAINLINE (btqca.c):
         *   "Some NVM files have more than one set of tags ... When there is
         *    more than one set there is an enclosing header of type 4."
         * Cabecera externa @0 -> si type == 4, saltar 4 bytes y leer la
         * cabecera interna @4 -> si type == 2, los tags empiezan @8.
         */
        size_t hdr_off = 0;
        uint32_t type_len = le32(fw);
        uint32_t length   = (type_len >> 8) & 0x00FFFFFF;
        uint8_t  type     = type_len & 0xFF;

        LOG("  NVM cabecera externa @0: tipo=%u longitud=%u", type, length);

        if (type == 4) {
            if (fwlen < 8) { ERR("NVM demasiado corto"); goto out; }
            hdr_off = 4;
            type_len = le32(fw + 4);
            length   = (type_len >> 8) & 0x00FFFFFF;
            type     = type_len & 0xFF;
            LOG("  NVM cabecera interna @4: tipo=%u longitud=%u", type, length);
        }

        if (type != 2) {
            ERR("NVM con tipo %u (esperaba 2); no se parsean los tags", type);
            goto out;
        }

        size_t data_off = hdr_off + 4;
        if (fwlen < length + data_off) {
            ERR("NVM: fichero corto (%zu < %u + %zu)",
                fwlen, length, data_off);
            goto out;
        }

        LOG("  NVM: tags desde el offset %zu, %u bytes de tags",
            data_off, length);

        size_t idx = 0;
        int ntags = 0;
        while (idx + 12 <= length) {
            size_t ao = data_off + idx;
            uint16_t tag_id  = le16(fw + ao);
            uint16_t tag_len = le16(fw + ao + 2);

            if (length < idx + 12 + tag_len) {
                ERR("NVM: tag %u con longitud %u excede", tag_id, tag_len);
                goto out;
            }

            if (tag_id == EDL_TAG_ID_HCI) {
                if (tag_len < 3) { ERR("tag HCI corto"); goto out; }
                fw[ao + 12 + 0] |= 0x80;        /* inband sleep */
                fw[ao + 12 + 2] = user_baud;    /* cherokee < WCN3991 -> [2] */
                LOG("  NVM tag %u (HCI): inband sleep + baud indice %u",
                    tag_id, user_baud);
            } else if (tag_id == EDL_TAG_ID_DEEP_SLEEP) {
                if (tag_len < 1) { ERR("tag DEEP_SLEEP corto"); goto out; }
                fw[ao + 12 + 0] |= 0x01;
                LOG("  NVM tag %u (DEEP_SLEEP)", tag_id);
            }

            idx += 12 + tag_len;
            ntags++;
        }
        LOG("  NVM: %d tags parseados, consumidos %zu de %u bytes",
            ntags, idx, length);
        if (idx != length)
            LOG("  NVM aviso: quedan %u bytes sin parsear", length - (uint32_t)idx);
    }

    /* ---- enviar en segmentos de 243 ---- */
    size_t off = 0, sent = 0;
    while (off < fwlen) {
        size_t seg = fwlen - off;
        if (seg > MAX_SIZE_PER_TLV_SEGMENT) seg = MAX_SIZE_PER_TLV_SEGMENT;

        int seg_mode = mode;
        /* El último segmento SIEMPRE se confirma (kernel mainline) */
        if (off + seg >= fwlen || seg < MAX_SIZE_PER_TLV_SEGMENT)
            seg_mode = ROME_SKIP_EVT_NONE;

        if (tlv_send_segment(fd, fw + off, seg, seg_mode) < 0) {
            ERR("fallo en el segmento %zu (offset %zu)", sent, off);
            goto out;
        }
        off += seg;
        sent++;
        if (sent % 50 == 0) LOG("  ... %zu/%zu segmentos", sent,
                                (fwlen + MAX_SIZE_PER_TLV_SEGMENT - 1) / MAX_SIZE_PER_TLV_SEGMENT);
    }
    LOG("  descargados %zu segmentos (%zu bytes)", sent, fwlen);
    ret = 0;
out:
    free(fw);
    return ret;
}

/* Cambia el baudrate del chip. Desactiva flow control alrededor. */
static int qca_set_baudrate(int fd, uint8_t baudrate)
{
    LOG("== Cambiar baudrate del chip a índice %u ==", baudrate);
    set_flow_control(fd, 0);
    uint8_t p = baudrate;
    if (send_cmd(fd, 0xFC48, &p, 1) < 0) return -1;
    /* el chip tarda 300 ms en cambiar */
    usleep(BAUDRATE_SETTLE_MS * 1000);
    set_flow_control(fd, 1);
    return 0;
}

/* ------------------------------------------------------------------ */
/* Paso final: entregar el puerto al kernel como hci0                  */
/* ------------------------------------------------------------------ */

/* Pone la disciplina n_hci y el protocolo H4 (id 0).
 *
 * IMPORTANTE: NO usamos HCI_UART_QCA (8). Su qca_setup() hace
 *   qcadev = serdev_device_get_drvdata(hu->serdev);   // hu->serdev == NULL
 * por la vía tty -> desreferencia NULL -> kernel panic.
 * Como YA hemos hecho nosotros toda la secuencia QCA (power + patch + NVM +
 * baud), basta con H4 puro: hci_h4.c no depende de serdev en absoluto. */
static int attach_h4(int fd)
{
    int ldisc = N_HCI;
    LOG("== Paso 7: adjuntar n_hci con protocolo H4 (id %d) ==", HCI_UART_H4);

    if (ioctl(fd, TIOCSETD, &ldisc) < 0) {
        ERR("TIOCSETD(N_HCI): %s", strerror(errno));
        ERR("  ¿está cargado el módulo/ldisc n_hci? (cat /proc/tty/ldiscs)");
        return -1;
    }
    LOG("  disciplina n_hci puesta");

    int proto = HCI_UART_H4;
    if (ioctl(fd, HCIUARTSETPROTO, proto) < 0) {
        ERR("HCIUARTSETPROTO(H4): %s", strerror(errno));
        return -1;
    }
    LOG("  protocolo H4 puesto");

    int got = ioctl(fd, _IOR('U', 201, int));   /* HCIUARTGETPROTO */
    if (got >= 0)
        LOG("  protocolo confirmado: %d", got);
    return 0;
}

/* ------------------------------------------------------------------ */
/* main                                                                */
/* ------------------------------------------------------------------ */

static void usage(const char *argv0)
{
    fprintf(stderr,
        "Uso: %s [opciones]\n"
        "  -d, --device <dev>    puerto serie (def: /dev/ttyHS0)\n"
        "  -f, --firmware <dir>  directorio de firmware (def: /vendor/bt_firmware/image)\n"
        "  -b, --baud <n>        baudrate final: 115200|921600|2000000|3000000 (def: 115200)\n"
        "  -p, --no-power-pulse  no enviar los pulsos de encendido\n"
        "  -n, --no-attach       no adjuntar n_hci al final (solo descargar firmware)\n"
        "  -q, --quiet           menos salida\n"
        "  -v, --verbose         más salida\n"
        "  -h, --help            esta ayuda\n",
        argv0);
}

int main(int argc, char **argv)
{
    const char *dev = "/dev/ttyHS0";
    const char *fwdir = "/vendor/bt_firmware/image";
    int final_baud = 115200;
    int do_power_pulse = 1;
    int do_attach = 1;

    static const struct { int baud; uint8_t val; } baud_tbl[] = {
        { 115200,  QCA_BAUDRATE_115200  },
        { 921600,  QCA_BAUDRATE_921600  },
        { 2000000, QCA_BAUDRATE_2000000 },
        { 3000000, QCA_BAUDRATE_3000000 },
    };

    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-d") || !strcmp(argv[i], "--device")) {
            if (++i >= argc) { usage(argv[0]); return 2; }
            dev = argv[i];
        } else if (!strcmp(argv[i], "-f") || !strcmp(argv[i], "--firmware")) {
            if (++i >= argc) { usage(argv[0]); return 2; }
            fwdir = argv[i];
        } else if (!strcmp(argv[i], "-b") || !strcmp(argv[i], "--baud")) {
            if (++i >= argc) { usage(argv[0]); return 2; }
            final_baud = atoi(argv[i]);
        } else if (!strcmp(argv[i], "-p") || !strcmp(argv[i], "--no-power-pulse")) {
            do_power_pulse = 0;
        } else if (!strcmp(argv[i], "-n") || !strcmp(argv[i], "--no-attach")) {
            do_attach = 0;
        } else if (!strcmp(argv[i], "-q") || !strcmp(argv[i], "--quiet")) {
            g_verbose = 0;
        } else if (!strcmp(argv[i], "-v") || !strcmp(argv[i], "--verbose")) {
            g_verbose = 2;
        } else if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
            usage(argv[0]);
            return 0;
        } else {
            ERR("opción desconocida: %s", argv[i]);
            usage(argv[0]);
            return 2;
        }
    }

    uint8_t final_val = QCA_BAUDRATE_115200;
    for (size_t i = 0; i < sizeof(baud_tbl)/sizeof(baud_tbl[0]); i++)
        if (baud_tbl[i].baud == final_baud) final_val = baud_tbl[i].val;

    LOG("qca-bringup: dev=%s fw=%s baud_final=%d", dev, fwdir, final_baud);

    int fd = open_serial(dev);
    if (fd < 0) return 1;

    /* --- Opcional: pulsos de encendido --- */
    if (do_power_pulse) {
        LOG("== Paso 0: pulsos de encendido (2400 -> 115200) ==");
        if (set_baud(fd, B2400) < 0) goto fail;
        set_flow_control(fd, 0);
        if (send_cmd_byte(fd, QCA_POWEROFF_PULSE) < 0) goto fail;
        usleep(200);
        if (set_baud(fd, B115200) < 0) goto fail;
        if (send_cmd_byte(fd, QCA_POWERON_PULSE) < 0) goto fail;
        usleep(200);
        LOG("  pulsos enviados, esperando 100 ms a que arranque el SoC");
        usleep(100 * 1000);
        /* reabrir para sincronizar RTS/CTS */
        close(fd);
        usleep(50 * 1000);
        fd = open_serial(dev);
        if (fd < 0) return 1;
    } else {
        LOG("== sin pulsos de encendido (--no-power-pulse) ==");
    }

    if (set_baud(fd, B115200) < 0) goto fail;
    set_flow_control(fd, 1);
    usleep(100 * 1000);

    /* --- Paso 1: versión --- */
    long soc_version = qca_read_soc_version(fd);
    if (soc_version < 0) {
        ERR("no se pudo leer la versión del SoC");
        ERR("  ¿está el chip encendido? ¿el puerto lo tiene otro proceso?");
        goto fail;
    }

    /* --- rom_ver -> nombres de fichero --- */
    uint8_t rom_ver = (uint8_t)(((soc_version & 0x00000F00) >> 4)
                              | (soc_version & 0x0000000F));
    LOG("== Paso 2: rom_ver = 0x%02X ==", rom_ver);

    char fw_patch[512], fw_nvm[512];
    snprintf(fw_patch, sizeof(fw_patch), "%s/crbtfw%02x.tlv", fwdir, rom_ver);
    snprintf(fw_nvm,   sizeof(fw_nvm),   "%s/crnv%02x.bin",   fwdir, rom_ver);
    LOG("  patch: %s", fw_patch);
    LOG("  nvm  : %s", fw_nvm);

    /* --- Paso 3: subir baudrate (antes de descargar, como el kernel) --- */
    if (final_val != QCA_BAUDRATE_115200) {
        if (qca_set_baudrate(fd, final_val) < 0) {
            ERR("fallo al cambiar baudrate");
            goto fail;
        }
        if (set_baud(fd, final_baud) < 0) goto fail;
    }

    /* --- Paso 4: descargar patch --- */
    LOG("== Paso 4: descargar patch ==");
    if (qca_download_firmware(fd, fw_patch, 0, final_val) < 0) {
        ERR("fallo descargando %s", fw_patch);
        goto fail;
    }
    usleep(10 * 1000);   /* msleep(10) del kernel */

    /* --- Paso 5: descargar NVM --- */
    LOG("== Paso 5: descargar NVM ==");
    if (qca_download_firmware(fd, fw_nvm, 1, final_val) < 0) {
        ERR("fallo descargando %s", fw_nvm);
        goto fail;
    }

    /* --- Paso 6: HCI Reset --- */
    LOG("== Paso 6: HCI Reset ==");
    if (send_cmd(fd, HCI_OP_RESET, NULL, 0) < 0) goto fail;
    {
        struct event ev;
        if (recv_event(fd, &ev, HCI_INIT_TIMEOUT_MS) < 0) {
            ERR("sin respuesta al HCI Reset");
            goto fail;
        }
        if (ev.ev == HCI_EV_CMD_COMPLETE && ev.status == 0)
            LOG("  HCI Reset OK");
        else
            LOG("  respuesta al reset: evento 0x%02X status 0x%02X",
                ev.ev, ev.status);
    }

    LOG("== LISTO (firmware cargado) ==");

    /* --- Paso 7: adjuntar n_hci/H4 para que aparezca hci0 --- */
    if (do_attach) {
        if (attach_h4(fd) < 0) {
            ERR("no se pudo adjuntar n_hci");
            LOG("El chip está listo; se puede reintentar el attach aparte:");
            LOG("  (n_hci/H4 ya se puede poner sin repetir la descarga)");
            close(fd);
            return 1;
        }
        LOG("== hci0 debería existir ya ==");
        LOG("  comprobar con: cat /sys/class/bluetooth/");
        LOG("  NO cerrar este proceso: al cerrar el fd se suelta la disciplina.");
        LOG("  Manteniendo el proceso vivo, bluetoothd puede usar hci0.");
        /* Nos quedamos vivos para no soltar la disciplina.
         * El proceso debe seguir en ejecución mientras se use el adaptador. */
        LOG("  (permaneciendo en ejecución; Ctrl-C para terminar)");
        for (;;) pause();
    } else {
        LOG("(--no-attach: no se adjunta n_hci; cerrando)");
        close(fd);
    }
    return 0;

fail:
    ERR("secuencia abortada");
    close(fd);
    return 1;
}
