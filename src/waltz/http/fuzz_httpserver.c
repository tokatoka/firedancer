#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <pthread.h>
#include <poll.h>
#include <sched.h>
#include <errno.h>

#include "../../util/fd_util.h"
#include "../../util/sanitize/fd_fuzz.h"
#include "fd_http_server_private.h"
#include "fd_http_server.h"

#define FD_HTTP_SERVER_GUI_MAX_CONNS             4
#define FD_HTTP_SERVER_GUI_MAX_REQUEST_LEN       2048
#define FD_HTTP_SERVER_GUI_MAX_WS_CONNS          4
#define FD_HTTP_SERVER_GUI_MAX_WS_RECV_FRAME_LEN 2048
#define FD_HTTP_SERVER_GUI_MAX_WS_SEND_FRAME_CNT 8192
#define FD_HTTP_SERVER_GUI_OUTGOING_BUFFER_SZ    (1UL<<28UL) /* 256MiB reserved for buffering GUI websockets */

const fd_http_server_params_t PARAMS = {
  .max_connection_cnt    = FD_HTTP_SERVER_GUI_MAX_CONNS,
  .max_ws_connection_cnt = FD_HTTP_SERVER_GUI_MAX_WS_CONNS,
  .max_request_len       = FD_HTTP_SERVER_GUI_MAX_REQUEST_LEN,
  .max_ws_recv_frame_len = FD_HTTP_SERVER_GUI_MAX_WS_RECV_FRAME_LEN,
  .max_ws_send_frame_cnt = FD_HTTP_SERVER_GUI_MAX_WS_SEND_FRAME_CNT,
  .outgoing_buffer_sz    = FD_HTTP_SERVER_GUI_OUTGOING_BUFFER_SZ,
};

struct Unstructured {
    uchar const * data;
    ulong         size;
    ulong         used;
};

static void unstructured_take(struct Unstructured *u, ulong len, void *out) {
    uchar *o = (uchar *)out;
    for (ulong i = 0UL; i < len; ++i) {
        if (u->used >= u->size) u->used = 0UL;
        o[i] = u->data[ u->used++ ];
    }
}

uchar rand_uchar(struct Unstructured *u) {
    uchar v;
    unstructured_take(u, sizeof(v), &v);
    return v;
}

uint rand_uint(struct Unstructured *u) {
    uint v;
    unstructured_take(u, sizeof(v), &v);
    return v;
}

ulong rand_ulong(struct Unstructured *u) {
    ulong v;
    unstructured_take(u, sizeof(v), &v);
    return v;
}

void rand_bytes(struct Unstructured *u, ulong len, uchar *p) {
    unstructured_take(u, len, p);
}

static ulong rand_range(struct Unstructured *u, ulong n) {
    if (!n) return 0UL;
    return (ulong)rand_uchar(u) % n;
}

void build_http_req(struct Unstructured *u, uchar *buf, int *len, int *use_websocket);
void build_ws_req(struct Unstructured *u, uchar *buf, int *len);

static fd_http_server_t *http_server = NULL;
uint16_t port = 0;
static int clients_fd[FD_HTTP_SERVER_GUI_MAX_CONNS * 2];
static char clients_ws_fd[FD_HTTP_SERVER_GUI_MAX_CONNS * 2];
static uint clients_fd_cnt = 0;

static void set_linger_reset(int fd) {
    struct linger lg = { .l_onoff = 1, .l_linger = 0 };
    setsockopt(fd, SOL_SOCKET, SO_LINGER, &lg, sizeof(lg));
}

void reset_clients_fd(void) {
  clients_fd_cnt = 0;
  for (ulong i = 0; i < FD_HTTP_SERVER_GUI_MAX_CONNS * 2; ++i) {
    clients_fd[i] = -1;
    clients_ws_fd[i] = 0;
  }
}

int
LLVMFuzzerInitialize( int  *   argc,
                      char *** argv ) {
  /* Set up shell without signal handlers */
  putenv( "FD_LOG_BACKTRACE=0" );
  setenv( "FD_LOG_PATH", "", 0 );
  fd_boot( argc, argv );
  atexit( fd_halt );
  fd_log_level_core_set(3);

  /* Disable parsing error logging */
  fd_log_level_stderr_set(4);

  reset_clients_fd();

  return 0;
}

typedef struct {
    uint32_t state;
} Xorshift;

void xorshift_init(Xorshift* x, uint32_t seed) {
    x->state = seed ? seed : 1;
}

uint32_t xorshift_next(Xorshift* x) {
    uint32_t s = x->state;
    s ^= s << 13;
    s ^= s >> 17;
    s ^= s << 5;
    x->state = s;
    return s;
}

static Xorshift poll_rng;

void random_api_call(Xorshift *u) {
    switch(xorshift_next(u) % 10) {
        case 0:
        {
            ulong pos = xorshift_next(u) % (FD_HTTP_SERVER_GUI_MAX_WS_CONNS);
            if (http_server->pollfds[ pos + http_server->max_conns ].fd != -1)
                fd_http_server_ws_send(http_server, pos);
        }
        break;
        case 1:
        {
            fd_http_server_ws_broadcast(http_server);
        }
        break;
        case 2:
        {
            char data[128];
            uint len = xorshift_next(u) % 128;
            memset(data, 0xcc, len);
            fd_http_server_memcpy(http_server, (uchar *)data, len);
        }
        break;
        case 3:
        {
            char data[128];
            uint len = xorshift_next(u) % 128;
            memset(data, 0xcc, len);
            data[len] = '\0';
            fd_http_server_printf(http_server, "%s", data);
        }
        break;
        case 4:
        {
            ulong pos = xorshift_next(u) % http_server->max_conns;
            if (http_server->pollfds[ pos ].fd != -1)
                fd_http_server_close(http_server, pos, (int)(xorshift_next(u) % 24));
        }
        break;
        case 5:
        {
            ulong pos = xorshift_next(u) % FD_HTTP_SERVER_GUI_MAX_WS_CONNS;
            if (http_server->pollfds[ pos + http_server->max_conns ].fd != -1)
                fd_http_server_ws_close(http_server, pos, (int)(xorshift_next(u) % 24));
        }
        break;
        case 6:
        {
            ulong staged = fd_http_server_stage_len(http_server);
            fd_http_server_stage_trunc(http_server, staged ? xorshift_next(u) % (staged+1UL) : 0UL);
        }
        break;
        case 7:
        {
            fd_http_server_unstage(http_server);
        }
        break;
        case 8:
        {
            fd_http_server_response_t resp;
            memset(&resp, 0, sizeof(resp));
            resp.status = 200;
            fd_http_server_stage_body(http_server, &resp);
        }
        break;
        case 9:
        {
            ulong len = xorshift_next(u) % 128;
            uchar * p = fd_http_server_append_start(http_server, len);
            if (p) {
                memset(p, 0xdd, len);
                fd_http_server_append_end(http_server, len);
            }
        }
        break;
    }
}

// finite set of characters we use in fuzz_etag_matches
static const char ETAG_CS[] = " \t,\"*W/abcdef";

static void fuzz_etag_matches(struct Unstructured *u) {
    static const char * const ETAGS[] = { "\"abc\"", "\"\"", "\"a\"", "\"a,b\"" };

    char  inm[96];
    uchar raw[sizeof(inm)-1UL];
    ulong n = 1UL + rand_range(u, sizeof(raw));

    // we prepare a buf filled with random bytes
    rand_bytes(u, n, raw);

    int pass_raw = (rand_uchar(u) % 8 == 0);
    ulong i = 0UL;
    for (; i < n; ++i) {
        // now fill the inm. choosing from either the finite set or the random buffer
        inm[i] = pass_raw ? (char)raw[i] : ETAG_CS[ raw[i] % (sizeof(ETAG_CS)-1UL) ];
    }
    inm[i] = '\0';

    char const * etag = ETAGS[ rand_uchar(u) % (sizeof(ETAGS)/sizeof(ETAGS[0])) ];
    fd_http_server_etag_matches(inm, etag);
}

void open_callback( ulong conn_id, int sockfd, void * ctx ) {
    (void)conn_id;
    (void)ctx;

    set_linger_reset(sockfd);

    for (uint i = 0; i < xorshift_next(&poll_rng) % 3; ++i) {
        random_api_call(&poll_rng);
    }
}

void close_callback( ulong conn_id, int reason, void * ctx ) {
    (void)conn_id;
    (void)reason;
    (void)ctx;

    for (uint i = 0; i < xorshift_next(&poll_rng) % 3; ++i) {
        random_api_call(&poll_rng);
    }
}

fd_http_server_response_t request_callback( fd_http_server_request_t const * request ) {
    fd_http_server_response_t resp;
    memset(&resp, 0, sizeof(fd_http_server_response_t));

    switch(xorshift_next(&poll_rng) % 7) {
        case 0:
        {
            resp.status = 200;
            resp.upgrade_websocket = xorshift_next(&poll_rng) % 2;
            resp.compress_websocket = xorshift_next(&poll_rng) % 2;
        }
        break;
        case 1:
        {
            resp.status = 204;
        }
        break;
        case 2:
        {
            resp.status = 400;
        }
        break;
        case 3:
        {
            resp.status = 404;
        }
        break;
        case 4:
        {
            resp.status = 405;
        }
        break;
        case 5:
        {
            resp.status = 500;
        }
        break;
        default:
        {
            resp.status = xorshift_next(&poll_rng);
        }
        break;
    }

    if (xorshift_next(&poll_rng) % 2 == 0) {
        resp.content_type = "Any content_type";
    }

    if (xorshift_next(&poll_rng) % 2 == 0) {
        resp.cache_control = "Any cache_control";
    }

    if (xorshift_next(&poll_rng) % 2 == 0) {
        resp.content_encoding = "Any content_encoding";
    }

    if (xorshift_next(&poll_rng) % 2 == 0) {
        resp.access_control_allow_origin = "Any access_control_allow_origin";
    }

    if (xorshift_next(&poll_rng) % 2 == 0) {
        resp.access_control_allow_methods = "Any access_control_allow_methods";
    }

    if (xorshift_next(&poll_rng) % 2 == 0) {
        resp.access_control_allow_headers = "Any access_control_allow_headers";
    }

    if (xorshift_next(&poll_rng) % 2 == 0) {
        resp.access_control_max_age = ((ulong)xorshift_next(&poll_rng) << 32) | (ulong)xorshift_next(&poll_rng);
    }

    if (xorshift_next(&poll_rng) % 2 == 0) {
        resp.static_body = (const uchar *) "resp_body";
        resp.static_body_len = 9;
    }

    if (request->headers.upgrade_websocket && (xorshift_next(&poll_rng) % 100) > 0) {
        resp.status = 200;
        resp.upgrade_websocket = 1;
    }

    for (uint i = 0; i < xorshift_next(&poll_rng) % 3; ++i) {
        random_api_call(&poll_rng);
    }

    return resp;
}

void ws_open_callback( ulong ws_conn_id, void * ctx ) {
    (void) ws_conn_id;
    (void) ctx;

    for (uint i = 0; i < xorshift_next(&poll_rng) % 3; ++i) {
        random_api_call(&poll_rng);
    }
}

void ws_close_callback( ulong ws_conn_id, int reason, void * ctx ) {
    (void) ws_conn_id;
    (void) reason;
    (void) ctx;

    for (uint i = 0; i < xorshift_next(&poll_rng) % 3; ++i) {
        random_api_call(&poll_rng);
    }
}

void ws_message_callback( ulong ws_conn_id, uchar const * data, ulong data_len, void * ctx ) {
    (void) ws_conn_id;
    (void) data;
    (void) data_len;
    (void) ctx;

    for (uint i = 0; i < xorshift_next(&poll_rng) % 3; ++i) {
        random_api_call(&poll_rng);
    }
}

void close_reset_clients_fd(fd_http_server_t * http) {
  for (ulong i = 0; i < clients_fd_cnt; ++i) {
    if (clients_fd[i] != -1) {
        close(clients_fd[i]);
        clients_fd[i] = -1;
        clients_ws_fd[i] = 0;
    }
  }
  clients_fd_cnt = 0;

  for (ulong conn_idx = 0; conn_idx < (PARAMS.max_connection_cnt + PARAMS.max_ws_connection_cnt); ++conn_idx) {
    if (http->pollfds[ conn_idx ].fd != -1) {
        close(http->pollfds[ conn_idx ].fd);
        http->pollfds[ conn_idx ].fd = -1;
    }
  }
}

int *reserve_client_fd(void) {
    for (uint i = 0; i < clients_fd_cnt; ++i) {
        if (clients_fd[i] == -1) return &clients_fd[i];
    }
    if (clients_fd_cnt >= (FD_HTTP_SERVER_GUI_MAX_CONNS * 2)) {
        return NULL;
    }
    return &clients_fd[clients_fd_cnt++];
}

// finite set of URIs to choose from
static const char * const URIS[] = {
    "/", "/home", "/index.html", "/websocket", "/a/b/c",
    "/home?x=1&y=2", "/%2e%2e/%2e%2e/etc", "/home#frag",
    "*", "http://127.0.0.1/home", "//", "/\x80\xff"
};
// finite set of charater set to choose from
static const char URI_CS[] = "abcXYZ019/-._~%?&=#+:@[]{}<>\\\"' \t\x7f\x80\xff";

static void build_uri(struct Unstructured *u, char *out, ulong out_sz) {
    uchar sel = rand_uchar(u);

    // in this case we choose from URIs
    if (sel % 8) {
        ulong idx = (ulong)(sel / 8U) % (sizeof(URIS)/sizeof(URIS[0]));
        snprintf(out, out_sz, "%s", URIS[idx]);
        return;
    }
    // else we build randomly from CS.
    uchar raw[160];
    ulong n = 1UL + rand_range(u, sizeof(raw) - 1UL);
    if (n > out_sz - 1UL) n = out_sz - 1UL;
    rand_bytes(u, n, raw);
    ulong i = 0UL;
    for (; i < n; ++i) out[i] = URI_CS[ raw[i] % (sizeof(URI_CS)-1UL) ];
    out[i] = '\0';
}

int build_http_header(struct Unstructured *u, char *buf, int max_len, int *use_websocket) {
    if (max_len <= 0) return 0;

    int used = 0;
    int is_ws_header = 0;

    switch (rand_uchar(u) % 7) {
        // Content-type
        case 0:
        {
            const char *CONTENT_TYPES[] = {"text/plain", "text/html", "application/json", "application/xml", "application/x-www-form-urlencoded", "multipart/form-data", "application/octet-stream", "image/png", "image/jpeg", "audio/mpeg", "video/mp4", "application/pdf"};
            const char *CHARSET = "; charset=UTF-8";
            const char *content_type = CONTENT_TYPES[rand_uchar(u) % (sizeof(CONTENT_TYPES)/sizeof(CONTENT_TYPES[0]))];
            if (rand_uchar(u) % 2 == 0) {
                used = snprintf(buf, (size_t) max_len, "Content-Type: %s\r\n", content_type);
            } else {
                used = snprintf(buf, (size_t)max_len, "Content-Type: %s%s\r\n", content_type, CHARSET);
            }
        }
        break;
        // Accept-encoding
        case 1:
        {
            const char *ACCEPT_ENCODINGS[] = {"gzip", "compress", "deflate", "br", "identity", "*"};
            char accept_encoding[64];
            memset(accept_encoding, 0, 64);
            char *cur_encoding_pos = &accept_encoding[0];
            int rem = 64;

            int n_encodings = 1 + (rand_uchar(u) % 6);
            for (int i = 0; i < n_encodings; ++i) {
                int size = snprintf(cur_encoding_pos, (size_t) rem, "%s%s", i ? ", " : "", ACCEPT_ENCODINGS[rand_uchar(u) % (sizeof(ACCEPT_ENCODINGS)/sizeof(ACCEPT_ENCODINGS[0]))]);
                if (size < 0 || size >= rem) break;
                cur_encoding_pos += size;
                rem -= size;
            }

            used = snprintf(buf, (size_t)max_len, "Accept-Encoding: %s\r\n", accept_encoding);
        }
        break;
        // websocket
        case 2:
        {
            static const char * const WS_KEYS[] = {
                "dGhlIHNhbXBsZSBub25jZQ==",
                "short",
                "dGhlIHNhbXBsZSBub25jZQ=!",
                "dGhlIHNhbXBsZSBub25jZQAA",
                "dGhlIHNhbXBs=SBub25jZQ==",
            };
            static const char * const WS_VERSIONS[] = { "13", "12", "1" };
            const char *key = WS_KEYS[rand_uchar(u) % (sizeof(WS_KEYS)/sizeof(WS_KEYS[0]))];
            const char *ver = WS_VERSIONS[rand_uchar(u) % (sizeof(WS_VERSIONS)/sizeof(WS_VERSIONS[0]))];
            if (rand_uchar(u) % 8 == 0) {
                used = snprintf(buf, (size_t)max_len, "Upgrade: websocket\r\nSec-WebSocket-Key: %s\r\nSec-WebSocket-Version: %s\r\n", key, ver);
            } else {
                used = snprintf(buf, (size_t)max_len, "Upgrade: websocket\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n");
            }
            is_ws_header = 1;
        }
        break;
        case 3:
        {
            // connection header
            static const char * const CONNS[] = { "keep-alive", "close", "Upgrade", "keep-alive, Upgrade", "" };
            used = snprintf(buf, (size_t)max_len, "Connection: %s\r\n", CONNS[rand_uchar(u) % (sizeof(CONNS)/sizeof(CONNS[0]))]);
        }
        break;
        case 4:
        {
            // random header
            char  name[32];
            char  value[32];
            uchar raw[sizeof(name) + sizeof(value)];

            ulong name_len  = 1UL + rand_range(u, sizeof(name) - 1UL);
            ulong value_len = rand_range(u, sizeof(value));
            rand_bytes(u, name_len + value_len, raw);

            ulong i = 0UL;
            for (; i < name_len; ++i) {
                uchar c = (uchar)(raw[i] % 94U + 33U);
                // don't use : as it'll terminate the name
                if (c == ':') c = 'X';
                name[i] = (char)c;
            }
            name[i] = '\0';

            int dirty = (rand_uchar(u) % 4 == 0);
            for (i = 0UL; i < value_len; ++i) {
                uchar c = raw[name_len + i];
                value[i] = (char)(dirty ? c : (uchar)(c % 94U + 33U));
            }
            value[i] = '\0';

            used = snprintf(buf, (size_t)max_len, "%s: %s\r\n", name, value);
        }
        break;
        case 5:
        {
            // if-none-match header
            char  inm[100];
            uchar raw[sizeof(inm) - 1UL];
            ulong n = 1UL + rand_range(u, sizeof(raw));
            rand_bytes(u, n, raw);
            ulong i = 0UL;
            for (; i < n; ++i) inm[i] = ETAG_CS[ raw[i] % (sizeof(ETAG_CS)-1UL) ];
            inm[i] = '\0';
            used = snprintf(buf, (size_t)max_len, "If-None-Match: %s\r\n", inm);
        }
        break;
        default:
        {
            static const char * const MISC[] = {
                "Transfer-Encoding: chunked\r\n",
                "Content-Length: 99999999999999999999\r\n",
                "Expect: 100-continue\r\n",
                "Origin: http://localhost\r\n",
                "Sec-WebSocket-Extensions: permessage-deflate\r\n",
                "Access-Control-Request-Method: POST\r\n",
            };
            used = snprintf(buf, (size_t)max_len, "%s", MISC[rand_uchar(u) % (sizeof(MISC)/sizeof(MISC[0]))]);
        }
        break;
    }

    if (used < 0 || used >= max_len) {
        buf[0] = 0;
        used = 0;
    }

    /* Only if the upgrade header really went out. */
    if (used && is_ws_header) *use_websocket = 1;

    return used;
}

void build_http_req(struct Unstructured *u, uchar *buf, int *len, int *use_websocket) {
    int max_size = *len;
    *len = 0;
    if (max_size <= 0) return;

    memset((char *)buf, 0, (size_t)max_size);

    static const char * const METHODS[]      = {"GET", "POST", "OPTIONS", "PUT"};
    static const char * const ODD_METHODS[]  = {"DELETE", "HEAD", "TRACE", "get", "", "GETX", "G ET"};
    static const char * const VERSIONS[]     = {"HTTP/1.1", "HTTP/1.0"};
    static const char * const ODD_VERSIONS[] = {"HTTP/2.0", "HTTP/0.9", "HTTP/1.1 ", "HTTP/1.11", "http/1.1", ""};

    int odd_method  = (rand_uchar(u) % 8 == 0);
    int odd_version = (rand_uchar(u) % 8 == 0);

    const char *method = odd_method ? ODD_METHODS[rand_uchar(u) % (sizeof(ODD_METHODS)/sizeof(ODD_METHODS[0]))]
                                    : METHODS[rand_uchar(u) % (sizeof(METHODS)/sizeof(METHODS[0]))];
    int body_method = (strcmp(method, "POST") == 0) || (strcmp(method, "PUT") == 0);
    int with_len    = body_method ? (rand_uchar(u) % 16 != 0) : (rand_uchar(u) % 16 == 0);

    char uri[160];
    build_uri(u, uri, sizeof(uri));

    const char *version = odd_version ? ODD_VERSIONS[rand_uchar(u) % (sizeof(ODD_VERSIONS)/sizeof(ODD_VERSIONS[0]))]
                                      : VERSIONS[rand_uchar(u) % (sizeof(VERSIONS)/sizeof(VERSIONS[0]))];

    uchar body[64];
    ulong body_len = 0UL;
    ulong content_length = 0UL;
    if (body_method || with_len) {
        body_len = rand_range(u, sizeof(body) + 1UL);
        rand_bytes(u, body_len, body);
        content_length = body_len;
        if (rand_uchar(u) % 8 == 0) {
            if (rand_uchar(u) % 4) content_length = rand_range(u, 2UL * sizeof(body) + 1UL);
            else                   content_length = (ulong)rand_uint(u);
        }
    }

    char headers[1024];
    memset(headers, 0, sizeof(headers));
    uint n_headers = 0;
    char *cur_header_pos = &headers[0];
    int rem = (int)sizeof(headers);
    if (with_len) {
        int used = snprintf(cur_header_pos, (size_t) rem, "Content-Length: %lu\r\n", content_length);
        if (used < 0 || used >= rem) return;
        cur_header_pos += used;
        rem -= used;
        n_headers++;
    }

    uint n_headers_target = (uint)rand_range(u, 40UL);
    while (n_headers < n_headers_target) {
        int used = build_http_header(u, cur_header_pos, rem, use_websocket);
        cur_header_pos += used;
        rem -= used;
        n_headers++;
    }

    int size = snprintf((char *)buf, (size_t) max_size, "%s %s %s\r\n%s\r\n", method, uri, version, headers);
    if (size < 0 || size >= max_size) return;

    if (body_len) {
        if ((ulong)(max_size - size) < body_len) return;
        memcpy(buf + size, body, body_len);
        size += (int)body_len;
    }

    *len = size;
}

void build_ws_req(struct Unstructured *u, uchar *buf, int *len) {
    int cap = *len;
    *len = 0;

    const uchar OPCODES[] = {0x0, 0x1, 0x2, 0x3, 0x8, 0x9, 0xA, 0xF};
    uchar opcode = OPCODES[rand_uchar(u) % (sizeof(OPCODES)/sizeof(OPCODES[0]))];

    // these are "control" opcodes, close, ping, pong each.
    int is_control = (opcode == 0x8 || opcode == 0x9 || opcode == 0xA);

    // we start building the websocket frame from here.
    // This is how the frame is made.
    // https://www.rfc-editor.org/info/rfc6455/. 
    uchar b0 = opcode;

    // set FIN bit at 50% prob.
    if (rand_uchar(u) % 2 == 0) b0 |= 0x80; // FIN sets the 0th bit.

    int   len_bytes;
    ulong declared_len;

    // this part is about websocket frames's 8th-15th bit. (payload len)
    if (is_control && rand_uchar(u) % 8 != 0) {
        len_bytes = 1;
        declared_len = rand_range(u, 126UL);
    } else {
        switch (rand_uchar(u) % 8) {
            case 0:  len_bytes = 1; declared_len = rand_range(u, 126UL);             break;
            case 1:  len_bytes = 3; declared_len = 126UL + rand_range(u, 130UL);     break;
            case 2:  len_bytes = 3; declared_len = (ulong)(rand_uint(u) % 65536U);   break;
            case 3:  len_bytes = 3; declared_len = 2030UL + rand_range(u, 30UL);     break;
            case 4:  len_bytes = 9; declared_len = 126UL + rand_range(u, 130UL);     break;
            case 5:  len_bytes = 9; declared_len = rand_ulong(u);                    break;
            case 6:  len_bytes = 9; declared_len = ULONG_MAX - rand_range(u, 16UL);  break;
            default: len_bytes = (rand_uchar(u) % 2) ? 3 : 9;
                     declared_len = rand_range(u, 126UL);                            break;
        }
    }

    int masked = (rand_uchar(u) % 16 != 0);

    int header_len = 1 + len_bytes + (masked ? 4 : 0);
    if (header_len > cap) return;

    ulong avail = (ulong)(cap - header_len);
    ulong actual_len = declared_len <= avail ? declared_len : avail;

    uchar len_code;
    if (len_bytes == 1)      len_code = (uchar)declared_len;
    else if (len_bytes == 3) len_code = 126;
    else                     len_code = 127;

    uchar *p = buf;
    *p++ = b0; // b0 sets 0-7th bit.
    *p++ = (uchar)(len_code | (masked ? 0x80 : 0)); // sets payload len

    // this part is about "extended payload length"
    // again. check https://www.rfc-editor.org/info/rfc6455/
    if (len_bytes == 3) {
        *p++ = (uchar)((declared_len >> 8) & 0xFF);
        *p++ = (uchar)( declared_len       & 0xFF);
    } else if (len_bytes == 9) {
        for (int i = 7; i >= 0; --i) *p++ = (uchar)((declared_len >> (8*i)) & 0xFF);
    }

    // masking key.
    uchar mask[4] = {0, 0, 0, 0};
    if (masked) {
        if (rand_uchar(u) % 4 != 0) rand_bytes(u, sizeof(mask), mask);
        memcpy(p, mask, sizeof(mask));
        p += sizeof(mask);
    }

    for (ulong i = 0UL; i < actual_len; ++i) {
        p[i] = (uchar)(rand_uchar(u) ^ mask[i % 4UL]);
    }
    p += actual_len;

    *len = (int)(p - buf);
}

static void corrupt(struct Unstructured *u, uchar *buf, int len) {
    if (len <= 0) return;
    if (rand_uchar(u) % 5 != 0) return;
    ulong n = 1UL + rand_range(u, 8UL);
    for (ulong i = 0UL; i < n; ++i) {
        ulong off = rand_ulong(u) % (ulong)len;
        buf[off] = rand_uchar(u);
    }
}

static ulong stem_iters = 0;
static int stop = 0;
void* stem_thread(void* arg) {
    (void) arg;

    while (1) {
        for (uint i = 0; i < xorshift_next(&poll_rng) % 3; ++i) {
            random_api_call(&poll_rng);
        }

        fd_http_server_poll(http_server, 0, ULONG_MAX);

        for (uint i = 0; i < xorshift_next(&poll_rng) % 3; ++i) {
            random_api_call(&poll_rng);
        }

        FD_COMPILER_MFENCE();
        FD_VOLATILE( stem_iters ) = stem_iters + 1UL;
        FD_COMPILER_MFENCE();

        if (FD_VOLATILE_CONST( stop )) break;
        sched_yield();
    }
    return NULL;
}

enum Action {
    HttpOpen = 0,
    Close,
    Send,
    Recv,
    ActionEnd,
};

void do_action(struct Unstructured *u) {
    switch(rand_uchar(u) % ActionEnd) {
        case HttpOpen:
        {
            int *client_fd = reserve_client_fd();
            if (!client_fd) return;
            clients_ws_fd[client_fd - clients_fd] = 0;

            struct sockaddr_in server_addr;
            *client_fd = socket(AF_INET, SOCK_STREAM, 0);
            if (*client_fd < 0) {
                *client_fd = -1;
                return;
            }
            set_linger_reset(*client_fd);

            memset(&server_addr, 0, sizeof(server_addr));
            server_addr.sin_family = AF_INET;
            server_addr.sin_port = htons(port);

            if (inet_pton(AF_INET, "127.0.0.1", &server_addr.sin_addr) != 1) {
                close(*client_fd);
                *client_fd = -1;
                return;
            }

            struct sockaddr sa;
            memcpy(&sa, &server_addr, sizeof(struct sockaddr));

            if (connect(*client_fd, &sa, sizeof(server_addr)) < 0) {
                close(*client_fd);
                *client_fd = -1;
            }
        }
        break;
        case Close:
        {
            if (clients_fd_cnt > 0) {
                uchar pos = rand_uchar(u) % ((uchar) clients_fd_cnt);
                if (clients_fd[pos] != -1) {
                    close(clients_fd[pos]);
                    clients_fd[pos] = -1;
                    clients_ws_fd[pos] = 0;
                }
            }
        }
        break;
        case Send:
        {
            if (clients_fd_cnt > 0) {
                uchar buf[2048];
                int len = (int)sizeof(buf);
                int use_websocket = 0;
                uchar pos = rand_uchar(u) % ((uchar) clients_fd_cnt);

                if (clients_fd[pos] != -1 && clients_ws_fd[pos] == 0) {
                    build_http_req(u, buf, &len, &use_websocket);
                    corrupt(u, buf, len);
                    if (len > 0) send(clients_fd[pos], buf, (size_t)len, MSG_NOSIGNAL | MSG_DONTWAIT);
                    if (use_websocket) {
                        clients_ws_fd[pos] = 1;
                    }
                }

                else if (clients_fd[pos] != -1 && clients_ws_fd[pos] == 1) {
                    build_ws_req(u, buf, &len);

                    // add up to 2 messages
                    ulong extra = rand_range(u, 3UL);
                    for (ulong i = 0; i < extra && len < (int)sizeof(buf); ++i) {
                        int len2 = (int)sizeof(buf) - len;
                        build_ws_req(u, buf + len, &len2);
                        if (len2 <= 0) break;
                        len += len2;
                    }

                    corrupt(u, buf, len);

                    if (len > 0) send(clients_fd[pos], buf, (size_t)len, MSG_NOSIGNAL | MSG_DONTWAIT);
                }
            }
        }
        break;
        case Recv:
        {
            if (clients_fd_cnt > 0) {
                uchar buf[4096];
                uchar pos = rand_uchar(u) % ((uchar) clients_fd_cnt);
                if (clients_fd[pos] != -1) {
                    for (int i = 0; i < 4; ++i) {
                        long sz = recv(clients_fd[pos], buf, sizeof(buf), MSG_DONTWAIT);
                        if (sz <= 0) break;
                    }
                }
            }
        }
        break;
    }
}

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         size ) {

  if (size >= sizeof(uint)) {
    struct Unstructured u = {
        .data      = data,
        .size      = size,
        .used      = 0
    };
    for (uint i = 0; i < 4; ++i) fuzz_etag_matches(&u);
    pthread_t thread;
    uint32_t ip_as_int;
    inet_pton(AF_INET, "127.0.0.1", &ip_as_int);

    void * shmem = aligned_alloc( fd_http_server_align(), fd_http_server_footprint( PARAMS ) );
    FD_TEST( shmem );

    fd_http_server_callbacks_t gui_callbacks = {
        .open = open_callback,
        .close = close_callback,
        .request = request_callback,
        .ws_open = ws_open_callback,
        .ws_close = ws_close_callback,
        .ws_message = ws_message_callback,
    };

    http_server = fd_http_server_join( fd_http_server_new( shmem, PARAMS, gui_callbacks, NULL ) );
    http_server = fd_http_server_listen( http_server, ip_as_int, 0 );

    union sockaddr_pun {
        struct sockaddr_in addr_in;
        struct sockaddr    sa;
    };

    union sockaddr_pun addr_pun;
    memset(&addr_pun, 0, sizeof(addr_pun));

    socklen_t addr_len = sizeof(addr_pun);

    if (getsockname(http_server->socket_fd, &addr_pun.sa, &addr_len) == -1) {
        printf( "bind failed (%i-%s)", errno, strerror( errno ) );
        abort();
    }

    port = ntohs(addr_pun.addr_in.sin_port);

    xorshift_init(&poll_rng, rand_uint(&u));

    FD_VOLATILE( stop ) = 0;
    FD_VOLATILE( stem_iters ) = 0UL;
    pthread_create(&thread, NULL, stem_thread, NULL);

    uchar n_actions = rand_uchar(&u) % 32;
    for (uchar i = 0; i < n_actions; ++i) {
        do_action(&u);

        ulong iters = FD_VOLATILE_CONST( stem_iters );
        while (FD_VOLATILE_CONST( stem_iters ) < iters + 2UL) sched_yield();
    }

    FD_VOLATILE( stop ) = 1;
    pthread_join(thread, NULL);

    close_reset_clients_fd(http_server);
    close(http_server->socket_fd);
    fd_http_server_delete(fd_http_server_leave(http_server));
    free( shmem );
  }

  return 0;
}
