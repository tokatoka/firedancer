#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#define _GNU_SOURCE

#include <stdlib.h>
#include <string.h>
#include <stddef.h>

#include "../../disco/topo/fd_topo.h"
#include "../../disco/keyguard/fd_keyguard_client.h"
#include "../../disco/store/fd_shredb.h"
#include "../../ballet/shred/fd_shred.h"
#include "../../ballet/ed25519/fd_ed25519.h"
#include "../../ballet/sha256/fd_sha256.h"
#include "../../util/sanitize/fd_fuzz.h"

static ulong mock_publish_cnt;

#undef  fd_stem_publish
#define fd_stem_publish( stem, out_idx, sig, chunk, sz, ctl, tsorig, tspub ) \
  do { (void)(stem); (void)(out_idx); (void)(sig); (void)(chunk); (void)(sz); \
       (void)(ctl); (void)(tsorig); (void)(tspub); mock_publish_cnt++; } while(0)

static int   mock_shred_len = -1;
static uchar mock_shred[ FD_SHRED_MAX_SZ ];

static int
mock_shredb_query( ulong   slot,
                   uint    shred_idx,
                   uchar * out ) {
  (void)slot; (void)shred_idx;
  if( mock_shred_len<0 ) return -1;
  memcpy( out, mock_shred, (ulong)mock_shred_len );
  return mock_shred_len;
}

#define fd_shredb_query( store, slot, shred_idx, out )         mock_shredb_query( (slot), (shred_idx), (out) )
#define fd_shredb_query_highest( store, slot, shred_idx, out ) mock_shredb_query( (slot), (shred_idx), (out) )

static void
mock_keyguard_sign( uchar *       signature,
                    uchar const * data,
                    ulong         data_len ) {
  memset( signature, 0x5a, 64UL );
  if( FD_LIKELY( data_len ) ) signature[ 0 ] = data[ 0 ];
}

#define fd_keyguard_client_sign( client, signature, data, data_len, type ) \
  mock_keyguard_sign( (signature), (data), (data_len) )

#include "fd_rserve_tile.c"

#define PING_CACHE_ENTRIES (4UL)
#define PEER_CNT           (3UL)
#define ADDR_CNT           (3UL)
#define NET_OUT_SZ         (1UL<<17)
#define NET_OUT_WMARK_SZ   (1UL<<16)

#define PKT_OFF_SIG   (sizeof(uint) + offsetof( fd_repair_shred_req_t, sig   ))
#define PKT_OFF_FROM  (sizeof(uint) + offsetof( fd_repair_shred_req_t, from  ))
#define PKT_OFF_TO    (sizeof(uint) + offsetof( fd_repair_shred_req_t, to    ))
#define PKT_OFF_TS    (sizeof(uint) + offsetof( fd_repair_shred_req_t, ts    ))
#define PKT_OFF_NONCE (sizeof(uint) + offsetof( fd_repair_shred_req_t, nonce ))
#define PKT_OFF_SLOT  (sizeof(uint) + offsetof( fd_repair_shred_req_t, slot  ))
#define PKT_OFF_IDX   (sizeof(uint) + offsetof( fd_repair_shred_req_t, shred_idx ))

#define PONG_OFF_FROM (sizeof(uint) + offsetof( fd_repair_pong_t, from ))
#define PONG_OFF_HASH (sizeof(uint) + offsetof( fd_repair_pong_t, hash ))
#define PONG_OFF_SIG  (sizeof(uint) + offsetof( fd_repair_pong_t, sig  ))

#define PKT_SZ_SHRED  (sizeof(uint) + sizeof(fd_repair_shred_req_t))
#define PKT_SZ_ORPHAN (sizeof(uint) + sizeof(fd_repair_orphan_req_t))
#define PKT_SZ_PONG   (sizeof(uint) + sizeof(fd_repair_pong_t))

struct unstructured {
  uchar const * data;
  ulong         size;
  ulong         used;
};

typedef struct unstructured unstructured_t;

static void
u_take( unstructured_t * u,
        ulong            len,
        void *           out ) {
  uchar * o = (uchar *)out;
  if( FD_UNLIKELY( !u->size ) ) {
    memset( out, 0, len );
    return;
  }
  for( ulong i=0UL; i<len; i++ ) {
    if( FD_UNLIKELY( u->used>=u->size ) ) u->used = 0UL;
    o[ i ] = u->data[ u->used++ ];
  }
}

static uchar
u_byte( unstructured_t * u ) {
  uchar v; u_take( u, sizeof(v), &v ); return v;
}

static uint
u_uint( unstructured_t * u ) {
  uint v; u_take( u, sizeof(v), &v ); return v;
}

static ulong
u_ulong( unstructured_t * u ) {
  ulong v; u_take( u, sizeof(v), &v ); return v;
}

static ulong
u_range( unstructured_t * u,
         ulong            n ) {
  if( FD_UNLIKELY( !n ) ) return 0UL;
  return (ulong)u_byte( u ) % n;
}

static ctx_t *      ctx;
static void *       rserve_mem;
static fd_sha512_t  harness_sha[ 1 ];

static uchar peer_priv[ PEER_CNT ][ 32 ];
static uchar peer_pub [ PEER_CNT ][ 32 ];
static uchar server_priv[ 32 ];

static uint   addr_ip4 [ ADDR_CNT ] = { 0x0100007fU, 0x0200007fU, 0x0a000001U };
static ushort addr_port[ ADDR_CNT ] = { 8001, 8002, 8003 };

static int    have_last;
static ulong  last_peer;
static uint   last_saddr;
static ushort last_sport;

static uchar const rserve_secret[ 32 ] = {
  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,
  0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f, 0x60,
  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,
  0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70
};

int
LLVMFuzzerInitialize( int  *   argc,
                      char *** argv ) {
  putenv( "FD_LOG_BACKTRACE=0" );
  setenv( "FD_LOG_PATH", "", 0 );
  fd_boot( argc, argv );
  atexit( fd_halt );
  fd_log_level_core_set( 3 );
  fd_log_level_stderr_set( 4 );

  fd_sha512_new( harness_sha );

  for( ulong i=0UL; i<PEER_CNT; i++ ) {
    memset( peer_priv[ i ], (int)(0x11U+i), 32UL );
    fd_ed25519_public_from_private( peer_pub[ i ], peer_priv[ i ], harness_sha );
  }
  memset( server_priv, 0x77, 32UL );

  ctx = aligned_alloc( 4096UL, fd_ulong_align_up( sizeof(ctx_t), 4096UL ) );
  FD_TEST( ctx );
  memset( ctx, 0, sizeof(ctx_t) );

  fd_sha512_new( ctx->sha512 );
  fd_ed25519_public_from_private( ctx->identity_public_key.uc, server_priv, harness_sha );

  rserve_mem = aligned_alloc( fd_rserve_align(), fd_rserve_footprint( PING_CACHE_ENTRIES ) );
  FD_TEST( rserve_mem );

  ctx->shredb = NULL;

  ctx->net_out_mem    = aligned_alloc( 4096UL, NET_OUT_SZ );
  FD_TEST( ctx->net_out_mem );
  memset( ctx->net_out_mem, 0, NET_OUT_SZ );
  ctx->net_out_idx    = 0U;
  ctx->net_out_chunk0 = 0UL;
  ctx->net_out_wmark  = (NET_OUT_WMARK_SZ>>FD_CHUNK_LG_SZ) - 1UL;
  ctx->net_out_chunk  = ctx->net_out_chunk0;

  fd_ip4_udp_hdr_init( ctx->serve_hdr, FD_RSERVE_MAX_PACKET_SIZE, 0U, 8000 );

  return 0;
}

static void
pick_addr( unstructured_t * u,
           uint *           ip4,
           ushort *         port ) {
  uchar sel = u_byte( u );
  if( FD_LIKELY( sel & 7U ) ) {
    ulong idx = (ulong)(sel>>3) % ADDR_CNT;
    *ip4  = addr_ip4 [ idx ];
    *port = addr_port[ idx ];
  } else {
    *ip4  = u_uint( u );
    *port = (ushort)u_uint( u );
  }
}

static void
dispatch( unstructured_t * u,
          uchar const *    pkt,
          ulong            pkt_sz,
          uint             saddr,
          ushort           sport ) {
  fd_ip4_udp_hdrs_t hdrs[ 1 ];
  fd_ip4_udp_hdr_init( hdrs, FD_RSERVE_MAX_PACKET_SIZE, 0U, 8000 );
  hdrs->ip4->saddr     = saddr;
  hdrs->ip4->daddr     = 0x0100007fU;
  hdrs->udp->net_sport = sport;

  fd_stem_context_t stem[ 1 ];
  memset( stem, 0, sizeof(stem) );

  (void)u;
  handle_net_request( ctx, stem, pkt, pkt_sz, hdrs->udp, hdrs->ip4 );
}

static void
action_pong( unstructured_t * u ) {
  uchar pkt[ PKT_SZ_PONG ];
  memset( pkt, 0, sizeof(pkt) );

  ulong  peer = u_range( u, PEER_CNT );
  uint   saddr;
  ushort sport;
  pick_addr( u, &saddr, &sport );

  uint kind = FD_REPAIR_KIND_PONG;
  memcpy( pkt, &kind, sizeof(uint) );
  memcpy( pkt+PONG_OFF_FROM, peer_pub[ peer ], 32UL );

  uchar pong_hash[ 32 ];
  uchar tok_sel = u_byte( u );
  if( FD_LIKELY( tok_sel & 7U ) ) {
    uchar token   [ 32 ];
    uchar preimage[ FD_REPAIR_PONG_PREIMAGE_SZ ];
    fd_rserve_ping_token( ctx->rserve, token, (fd_pubkey_t const *)fd_type_pun_const( peer_pub[ peer ] ), saddr, sport );
    preimage_pong( (fd_hash_t const *)fd_type_pun_const( token ), preimage );
    fd_sha256_hash( preimage, FD_REPAIR_PONG_PREIMAGE_SZ, pong_hash );
  } else {
    u_take( u, sizeof(pong_hash), pong_hash );
  }
  memcpy( pkt+PONG_OFF_HASH, pong_hash, 32UL );

  uchar sig[ 64 ];
  if( FD_LIKELY( u_byte( u ) & 7U ) ) {
    fd_ed25519_sign( sig, pkt+PONG_OFF_HASH, 32UL, peer_pub[ peer ], peer_priv[ peer ], harness_sha );
  } else {
    u_take( u, sizeof(sig), sig );
  }
  memcpy( pkt+PONG_OFF_SIG, sig, 64UL );

  if( FD_UNLIKELY( !(u_byte( u ) & 15U) ) ) {
    ulong off = u_ulong( u ) % sizeof(pkt);
    pkt[ off ] = u_byte( u );
  }

  have_last  = 1;
  last_peer  = peer;
  last_saddr = saddr;
  last_sport = sport;

  dispatch( u, pkt, sizeof(pkt), saddr, sport );
}

static void
action_request( unstructured_t * u ) {
  static uint const TAGS[]     = { FD_REPAIR_KIND_SHRED, FD_REPAIR_KIND_HIGHEST_SHRED, FD_REPAIR_KIND_ORPHAN };
  static uint const ODD_TAGS[] = { FD_REPAIR_KIND_PING, FD_REPAIR_KIND_ANCESTOR_HASHES, AG_REPAIR_KIND_PARENT_FEC_COUNT,
                                   AG_REPAIR_KIND_FEC_ROOT, AG_REPAIR_KIND_SHRED_FOR_BLOCK_ID, 0xdeadbeefU };

  uchar weird = u_byte( u );
  uint  tag   = (weird & 7U) ? TAGS[ u_range( u, 3UL ) ] : ODD_TAGS[ u_range( u, 6UL ) ];

  ulong pkt_sz = tag==FD_REPAIR_KIND_ORPHAN ? PKT_SZ_ORPHAN : PKT_SZ_SHRED;
  ulong sign_sz = tag==FD_REPAIR_KIND_ORPHAN ? 88UL : 96UL;

  if( FD_UNLIKELY( !(weird & 56U) ) ) {
    pkt_sz = u_range( u, PKT_SZ_SHRED + 8UL );
  }

  uchar pkt[ PKT_SZ_SHRED + 8UL ];
  memset( pkt, 0, sizeof(pkt) );
  if( FD_UNLIKELY( pkt_sz>sizeof(pkt) ) ) pkt_sz = sizeof(pkt);

  uint   saddr;
  ushort sport;
  ulong  peer;

  if( FD_LIKELY( have_last && (u_byte( u ) & 3U) ) ) {
    peer  = last_peer;
    saddr = last_saddr;
    sport = last_sport;
  } else {
    pick_addr( u, &saddr, &sport );
    peer = u_range( u, PEER_CNT );
  }

  if( FD_LIKELY( pkt_sz>=sizeof(uint) ) ) memcpy( pkt, &tag, sizeof(uint) );

  if( FD_LIKELY( pkt_sz>=PKT_SZ_ORPHAN ) ) {
    uchar who = u_byte( u );
    if( FD_LIKELY( who & 7U ) ) memcpy( pkt+PKT_OFF_FROM, peer_pub[ peer ], 32UL );
    else                        memcpy( pkt+PKT_OFF_FROM, ctx->identity_public_key.uc, 32UL );

    if( FD_LIKELY( who & 56U ) ) memcpy( pkt+PKT_OFF_TO, ctx->identity_public_key.uc, 32UL );
    else                         u_take( u, 32UL, pkt+PKT_OFF_TO );

    long now_ms = FD_NANOSEC_TO_MILLI( fd_log_wallclock() );
    ulong ts;
    uchar ts_sel = u_byte( u );
    if( FD_LIKELY( ts_sel & 7U ) ) ts = (ulong)(now_ms - (long)u_range( u, 1000UL ));
    else                           ts = u_ulong( u );
    memcpy( pkt+PKT_OFF_TS, &ts, sizeof(ulong) );

    uint nonce = u_uint( u );
    memcpy( pkt+PKT_OFF_NONCE, &nonce, sizeof(uint) );

    ulong slot = u_ulong( u ) % 1024UL;
    memcpy( pkt+PKT_OFF_SLOT, &slot, sizeof(ulong) );
  }

  if( FD_LIKELY( pkt_sz>=PKT_SZ_SHRED ) ) {
    ulong shred_idx;
    if( FD_LIKELY( u_byte( u ) & 7U ) ) shred_idx = u_ulong( u ) & fd_ulong_mask( 0, 14 );
    else                                shred_idx = u_ulong( u );
    memcpy( pkt+PKT_OFF_IDX, &shred_idx, sizeof(ulong) );
  }

  if( FD_LIKELY( pkt_sz>=PKT_SZ_ORPHAN ) ) {
    uchar signable[ 96 ];
    memcpy( signable,     pkt,      sizeof(uint)  );
    memcpy( signable+4UL, pkt+68UL, sign_sz-4UL   );

    uchar sig[ 64 ];
    if( FD_LIKELY( u_byte( u ) & 7U ) ) {
      fd_ed25519_sign( sig, signable, sign_sz, peer_pub[ peer ], peer_priv[ peer ], harness_sha );
    } else {
      u_take( u, sizeof(sig), sig );
    }
    memcpy( pkt+PKT_OFF_SIG, sig, 64UL );
  }

  uchar len_sel = u_byte( u );
  if( FD_UNLIKELY( !(len_sel & 3U) ) ) {
    mock_shred_len = -1;
  } else {
    mock_shred_len = (int)( FD_SHRED_MIN_SZ + u_range( u, FD_SHRED_MAX_SZ-FD_SHRED_MIN_SZ+1UL ) );
    u_take( u, (ulong)mock_shred_len, mock_shred );
    ushort parent_off;
    if( FD_LIKELY( u_byte( u ) & 3U ) ) parent_off = (ushort)u_range( u, 4UL );
    else                                parent_off = (ushort)u_uint( u );
    memcpy( mock_shred+offsetof( fd_shred_t, data.parent_off ), &parent_off, sizeof(ushort) );
  }

  if( FD_UNLIKELY( !(u_byte( u ) & 15U) ) && pkt_sz ) {
    ulong off = u_ulong( u ) % pkt_sz;
    pkt[ off ] = u_byte( u );
  }

  dispatch( u, pkt, pkt_sz, saddr, sport );
}

static void
action_raw( unstructured_t * u ) {
  uchar pkt[ 256 ];
  ulong pkt_sz = u_range( u, sizeof(pkt)+1UL );
  u_take( u, pkt_sz, pkt );

  if( FD_LIKELY( pkt_sz>=sizeof(uint) ) && (u_byte( u ) & 1U) ) {
    static uint const TAGS[] = { FD_REPAIR_KIND_PING, FD_REPAIR_KIND_PONG, FD_REPAIR_KIND_SHRED,
                                 FD_REPAIR_KIND_HIGHEST_SHRED, FD_REPAIR_KIND_ORPHAN, FD_REPAIR_KIND_ANCESTOR_HASHES };
    uint tag = TAGS[ u_range( u, 6UL ) ];
    memcpy( pkt, &tag, sizeof(uint) );
  }

  uint   saddr;
  ushort sport;
  pick_addr( u, &saddr, &sport );

  dispatch( u, pkt, pkt_sz, saddr, sport );
}

enum action {
  ACT_PONG = 0,
  ACT_REQUEST,
  ACT_RAW,
  ACT_ROTATE,
  ACT_CNT
};

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         size ) {
  if( FD_UNLIKELY( size<2UL ) ) return 0;

  unstructured_t u = { .data = data, .size = size, .used = 0UL };

  ctx->rserve = fd_rserve_join( fd_rserve_new( rserve_mem, PING_CACHE_ENTRIES, 0UL, rserve_secret ) );
  FD_TEST( ctx->rserve );

  memset( ctx->metrics, 0, sizeof(ctx->metrics) );
  ctx->net_out_chunk = ctx->net_out_chunk0;
  mock_shred_len     = -1;
  have_last          = 0;

  ulong n_actions = 1UL + u_range( &u, 12UL );
  for( ulong i=0UL; i<n_actions; i++ ) {
    switch( u_byte( &u ) % ACT_CNT ) {
      case ACT_PONG:    action_pong   ( &u ); break;
      case ACT_REQUEST: action_request( &u ); break;
      case ACT_RAW:     action_raw    ( &u ); break;
      case ACT_ROTATE:  fd_rserve_maybe_rotate( ctx->rserve, u_ulong( &u ) ); break;
    }
  }

  fd_rserve_delete( fd_rserve_leave( ctx->rserve ) );
  ctx->rserve = NULL;

  return 0;
}
