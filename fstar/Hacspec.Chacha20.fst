module Hacspec.Chacha20

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

type state_t        = lseq uint32 16
let state_idx_t     = nat_mod 16
type constants_t    = lseq uint32 4
let constants_idx_t = nat_mod 4
type block_t        = lseq uint8 64
type cha_cha_iv_t   = lseq uint8 12
type cha_cha_key_t  = lseq uint8 32

let chacha20_line (a b d: state_idx_t) (s: pos {s < 32}) (state: state_t): state_t =
  let state = array_upd state a (array_index state a +. array_index state b) in
  let state = array_upd state d (array_index state d ^. array_index state a) in
  let state = array_upd state d (uint32_rotate_left (array_index state d) s) in
  state

let chacha20_quarter_round (a b c d: state_idx_t) (state: state_t): state_t =
  let state = chacha20_line a b d 16 state in
  let state = chacha20_line c d b 12 state in
  let state = chacha20_line a b d 8  state in
              chacha20_line c d b 7  state

let chacha20_double_round (state : state_t) : state_t =
  let state = chacha20_quarter_round 0 4 8  12 state in
  let state = chacha20_quarter_round 1 5 9  13 state in
  let state = chacha20_quarter_round 2 6 10 14 state in
  let state = chacha20_quarter_round 3 7 11 15 state in
  let state = chacha20_quarter_round 0 5 10 15 state in
  let state = chacha20_quarter_round 1 6 11 12 state in
  let state = chacha20_quarter_round 2 7 8  13 state in
              chacha20_quarter_round 3 4 9  14 state

let chacha20_rounds (st : state_t) : state_t =
    foldi 0 10 (fun _ -> chacha20_double_round) st

let chacha20_core (ctr: uint32) (st0: state_t): state_t =
  let state = array_upd st0 12 (array_index st0 12 +. ctr) in
  chacha20_rounds state `array_add (+.)` (state)

let x: FStar.UInt8.t = 2uy

let chacha20_constants_init (): constants_t =
  let constants: constants_t = array_new_ (secret 0ul) (4) in
  let constants = array_upd constants 0 (secret 0x61707865ul) in
  let constants = array_upd constants 1 (secret 0x3320646eul) in
  let constants = array_upd constants 2 (secret 0x79622d32ul) in
  let constants = array_upd constants 3 (secret 0x6b206574ul) in
  constants

let chacha20_init (key: cha_cha_key_t) (iv: cha_cha_iv_t) (ctr: uint32): state_t =
  let st: state_t = array_new_ (secret 0ul) 16    in
  let st = array_update st 0 (chacha20_constants_init ()) in
  let st = array_update st 4 (array_to_le_uint32s key)    in
  let st = array_upd st 12 ctr                            in
           array_update st 13 (array_to_le_uint32s (iv))

let chacha20_key_block (state : state_t) : block_t =
  let state: state_t = chacha20_core (secret 0ul) state in
  array_from_seq 64 (array_to_le_bytes state)

let chacha20_key_block0 (key: cha_cha_key_t) (iv: cha_cha_iv_t): block_t =
  let state: state_t = chacha20_init (key) (iv) (secret 0ul) in
  chacha20_key_block state

let chacha20_encrypt_block (st0: state_t) (ctr: uint32) (plain: block_t): block_t =
  let st: state_t = chacha20_core ctr st0 in
  let pl: state_t = array_from_seq 16 (array_to_le_uint32s plain) in
  let st : state_t = pl `array_xor (^.)` st in
  array_from_seq 64 (array_to_le_bytes st)

let chacha20_encrypt_last (st0:state_t) (ctr:uint32) (plain: byte_seq {seq_len plain <= 64})
  : r: byte_seq { seq_len r = seq_chunk_len plain 64 0 }
  = let b: block_t = array_new_ (secret (pub_u8 0)) 64 in
  let b = array_update b 0 plain in
  let b = chacha20_encrypt_block st0 ctr b in
  array_slice b 0 (seq_len plain)

let chacha20_update (st0:state_t) (m :byte_seq {seq_len m >= 64}): byte_seq =
  let blocks_out: seq uint8 = seq_new_ (secret (pub_u8 0x0)) (seq_len m) in
  let n_blocks: uint_size = seq_num_exact_chunks m 64 in
  // [n_blocks] is the number of chunks of size [64] in [m]
  let blocks_out =
    foldi #(lseq uint8 (seq_len m)) 0 n_blocks (fun i blocks_out ->
      // here, [i] ranges from [0] to [n_blocks-1], that is, we consider only complete blocks
      let msg_block: seq uint8 = seq_get_exact_chunk m 64 i in
      let b: block_t = chacha20_encrypt_block st0 (secret (pub_u32 i)) (array_from_seq 64 msg_block) in
      seq_set_exact_chunk blocks_out 64 i b
    ) blocks_out 
  in
  // [last_block] is the [seq_num_chunks s 64 - 1]th chunk
  let last_block: seq uint8 = seq_get_remainder_chunk m 64 in
  if seq_len last_block <> 0 then (
    let b: seq uint8 = chacha20_encrypt_last st0 (secret (pub_u32 n_blocks)) last_block in
    // we're updating the [n_blocks]th chunk
    let seq_seq_chunk_precondition = seq_len b == seq_chunk_len blocks_out 64 n_blocks in
    if seq_len m = 64 then (
      assert (seq_num_exact_chunks m 64 == 1);
      assert (seq_num_chunks m 64 - 1 == 0);
      assert (~seq_seq_chunk_precondition);
      ()
    );
    admitP (seq_seq_chunk_precondition);
    if seq_len m = 64 then assert (false);
    seq_set_chunk blocks_out 64 n_blocks b
    // [seq_num_chunks m 64 - 1] ≠ [n_blocks]
    // [seq_num_chunks m 64 - 1] ≠ [seq_num_exact_chunks m 64]
    // but `seq_set_chunk` expects `b` to be of same length as `n_blocks`th chunk
  ) else blocks_out

let chacha20
  (key_58 : cha_cha_key_t)
  (iv_59 : cha_cha_iv_t)
  (ctr_60 : pub_uint32)
  (m_61 : byte_seq {Seq.length m_61 >= 64})
  : byte_seq =
  let state_62 : state_t =
    chacha20_init (key_58) (iv_59) (secret (ctr_60))
  in
  chacha20_update (state_62) m_61

