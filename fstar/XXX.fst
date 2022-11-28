module XXX

open FStar.Tactics
open Hacspec.Lib
open FStar.Mul
open Hacspec.Chacha20

module S = Spec.Chacha20
module H = Hacspec.Chacha20
module Seq = Lib.Sequence

module LC = Lib.LoopCombinators

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

let rec foldi
  (lo: uint_size)
  (hi: uint_size{lo <= hi})
  (f: (i:uint_size{i < hi}) -> 'a -> 'a)
  (init: 'a)
  : Tot 'a (decreases (hi - lo))
  = if lo = hi then init
               else foldi (lo+1) hi f (f lo init)

unfold let map_blocks_foldi
    (#len: uint_size) (blocksize: size_pos)
    (max: uint_size {max * blocksize <= len})
    (n: uint_size {n * blocksize <= len /\ n <= max})
    (original_s: lseq 'a len)
    (s: lseq 'a len)
    (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
    : lseq 'a len
  = foldi #(lseq 'a len) 0 n (fun (i: nat{i<max}) (s: lseq 'a len) -> seq_set_exact_chunk #'a #len s blocksize i (f i (seq_get_exact_chunk #'a original_s blocksize i))) s

#push-options "--print_implicits --print_universes"

let manual_rewrite (): Lemma (uint8 == int_t U8 SEC) = ()


// let seq_set_exact_chunk
//   (#a: Type)
//   (#len:uint_size) (* change to nseq but update_sub missing for nseq *)
//   (s: lseq a len)
//   (chunk_len: uint_size)
//   (chunk_num: uint_size)
//   (chunk: seq a )
//     : Pure (lseq a len)
//       (requires (
//         chunk_len * (chunk_num + 1) <= FStar.Seq.length s /\
//         Seq.length chunk = seq_chunk_len s chunk_len chunk_num
//       ))
//       (ensures (fun out -> True))
//   = s


let chacha20_update0' (st0 : state_t) (cipher : byte_seq) =
  let blocks_out: seq uint8 = seq_new_ (secret (pub_u8 0x0)) (seq_len cipher) in
  let n_blocks: uint_size = seq_num_exact_chunks cipher 64 in
    
  let rr = foldi #(lseq (int_t U8 SEC) (seq_len #(int_t U8 SEC) cipher))
          0
          (seq_num_exact_chunks #(int_t U8 SEC) cipher 64)
          (fun i s ->
              seq_set_exact_chunk #(int_t U8 SEC)
                #(seq_len #(int_t U8 SEC) cipher)
                s
                64
                i
                (chacha20_encrypt_block st0
                    (secret #U32 (pub_u32 i))
                    (array_from_seq #(int_t U8 SEC)
                        64
                        (seq_get_exact_chunk #(int_t U8 SEC) cipher 64 i))
                  <:
                  Prims.Tot block_t))
          (seq_new_ #(int_t U8 SEC) (secret #U8 (pub_u8 0x0)) (seq_len #(int_t U8 SEC) cipher)) in

  let f2 (i: nat {i<n_blocks}) (msg_block: lseq uint8 64): block_t = 
    chacha20_encrypt_block st0 (secret (pub_u32 i)) (array_from_seq 64 msg_block)
  in
  let r2 = map_blocks_foldi #uint8 #(seq_len cipher) 64 n_blocks n_blocks cipher blocks_out f2 in

  assert (eq2 #(seq _) r2 rr) by (
    norm [delta_only [`%map_blocks_foldi;`%uint8;`%uint_t;`%lseq;`%seq_len]; zeta_full];
    norm [unascribe];
    norm [delta_only [`%Seq.lseq;`%seq_len]];
    l_to_r [`manual_rewrite];
    let goal = cur_goal () in
    let _squash, [goal,_] = admit (); collect_app goal in
    let _eq2, [_;(l,_);(r,_)] = admit (); collect_app goal in
    print ("lllllllllllllllll");
    print (term_to_string l);
    print ("rrrrrrrrrrrrrrrrr");
    print (term_to_string r);
    // if compare_term l r = FStar.Order.Eq
    // then fail "hey";
    // trefl ();
    fail "x"
  );
  admit ()
