#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "../../util/fd_util.h"
#include "../../util/sanitize/fd_fuzz.h"
#include "../../ballet/bmtree/fd_bmtree.h"
#include "fd_repair.h"

#define MAX_MSG_SZ (512UL)

int
LLVMFuzzerInitialize( int  *   argc,
                      char *** argv ) {
  /* Set up shell without signal handlers */
  putenv( "FD_LOG_BACKTRACE=0" );
  setenv( "FD_LOG_PATH", "", 0 );
  fd_boot( argc, argv );
  atexit( fd_halt );
  fd_log_level_core_set(3); /* crash on warning log */
  return 0;
}

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
build_response( unstructured_t * u,
                uchar *          buf ) {
  uchar  sel  = u_byte( u );
  uint   kind = (sel & 1U) ? AG_REPAIR_RESPONSE_FEC_SET_ROOT : AG_REPAIR_RESPONSE_PARENT_FEC_SET_COUNT;
  if( FD_UNLIKELY( !(sel & 62U) ) ) kind = u_uint( u );

  uint  fec_set_count = u_uint( u ) % (FD_FEC_BLK_MAX+2U);
  ulong proof_len;

  if( FD_LIKELY( sel & 4U ) ) {
    proof_len = fd_bmtree_depth( (ulong)fec_set_count+1UL )-1UL;
  } else {
    proof_len = u_ulong( u ) % (AG_MAX_FEC_PROOF_NODE_CNT+3UL);
  }

  ulong proof_sz = proof_len*FD_SHRED_MERKLE_NODE_SZ;
  if( FD_UNLIKELY( !(sel & 8U) ) ) proof_sz = u_ulong( u );

  ulong off = 0UL;
  memcpy( buf+off, &kind, sizeof(uint) ); off += sizeof(uint);

  if( kind==AG_REPAIR_RESPONSE_PARENT_FEC_SET_COUNT ) {
    memcpy( buf+off, &fec_set_count, sizeof(uint) ); off += sizeof(uint);
    ulong parent_slot = u_ulong( u );
    memcpy( buf+off, &parent_slot, sizeof(ulong) ); off += sizeof(ulong);
    u_take( u, sizeof(fd_hash_t), buf+off ); off += sizeof(fd_hash_t);
  } else {
    u_take( u, FD_SHRED_MERKLE_NODE_SZ, buf+off ); off += FD_SHRED_MERKLE_NODE_SZ;
  }

  memcpy( buf+off, &proof_sz, sizeof(ulong) ); off += sizeof(ulong);

  ulong proof_bytes = proof_sz;
  if( FD_UNLIKELY( proof_bytes > MAX_MSG_SZ-off-sizeof(uint) ) ) proof_bytes = MAX_MSG_SZ-off-sizeof(uint);
  u_take( u, proof_bytes, buf+off ); off += proof_bytes;

  uint nonce = u_uint( u );
  memcpy( buf+off, &nonce, sizeof(uint) ); off += sizeof(uint);

  if( FD_UNLIKELY( !(sel & 16U) ) ) {
    ulong delta = (ulong)u_byte( u ) % 9UL;
    if( u_byte( u ) & 1U ) off = off>delta ? off-delta : 0UL;
    else                   off = fd_ulong_min( off+delta, MAX_MSG_SZ );
  }

  return off;
}

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         data_sz ) {

  fd_repair_ping_t ping[1];
  memset( ping, 0, sizeof(fd_repair_ping_t) );
  fd_repair_ping_de( ping, data, data_sz );

  unstructured_t u = { .data = data, .size = data_sz, .used = 0UL };

  uchar buf[ MAX_MSG_SZ ];
  memset( buf, 0, sizeof(buf) );

  ulong buf_sz;
  if( FD_LIKELY( u_byte( &u ) & 3U ) ) {
    buf_sz = build_response( &u, buf );
  } else {
    buf_sz = fd_ulong_min( data_sz, MAX_MSG_SZ );
    memcpy( buf, data, buf_sz );
  }

  ag_repair_response_t response[1];
  memset( response, 0, sizeof(ag_repair_response_t) );

  int de_err = ag_repair_response_de( response, buf, buf_sz );
  if( de_err ) {
    FD_FUZZ_MUST_BE_COVERED;
    return 0;
  }

  FD_FUZZ_MUST_BE_COVERED;

  assert( response->kind==AG_REPAIR_RESPONSE_PARENT_FEC_SET_COUNT ||
          response->kind==AG_REPAIR_RESPONSE_FEC_SET_ROOT );

  fd_hash_t block_id[1];
  u_take( &u, sizeof(fd_hash_t), block_id->uc );

  if( response->kind==AG_REPAIR_RESPONSE_PARENT_FEC_SET_COUNT ) {
    ag_parent_fec_count_res_t const * res = &response->parent_fec_set_res;

    assert( res->proof_len<=AG_MAX_FEC_PROOF_NODE_CNT );
    assert( res->fec_set_count<=FD_FEC_BLK_MAX );

    assert( buf_sz==60UL+res->proof_len*FD_SHRED_MERKLE_NODE_SZ );

    ag_repair_parent_fec_count_verify( res, block_id );
  } else {
    ag_fec_root_res_t const * res = &response->fec_set_root;

    assert( res->proof_len<=AG_MAX_FEC_PROOF_NODE_CNT );

    assert( buf_sz==36UL+res->proof_len*FD_SHRED_MERKLE_NODE_SZ );

    ag_repair_fec_set_root_verify( res, block_id, u_uint( &u ) );
  }

  FD_FUZZ_MUST_BE_COVERED;
  return 0;
}
