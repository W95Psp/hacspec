module Hacspec.Poly1305.Proof

open Hacspec.Lib
open FStar.Mul

module S = Spec.Poly1305
module H = Hacspec.Poly1305
module Seq = Lib.Sequence

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

let poly1305_encode_r_equiv (b:H.poly_block_t)
  : Lemma (H.poly1305_encode_r b == S.poly1305_encode_r b)
          [SMTPat (H.poly1305_encode_r b)] =
  let n_1 = uint128_from_le_bytes (array_from_seq (16) (b)) in
  let lo : uint64 = Lib.ByteSequence.uint_from_bytes_le (Lib.Sequence.sub b 0 8) in
  let hi : uint64 = Lib.ByteSequence.uint_from_bytes_le (Lib.Sequence.sub b 8 8) in
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U64 #SEC (Lib.Sequence.sub b 0 8);
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U64 #SEC (Lib.Sequence.sub b 8 8);
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC (array_from_seq 16 b);
  Lib.ByteSequence.nat_from_intseq_le_slice_lemma b 8;
  assert (v n_1 == v lo + pow2 64 * v hi);

  let mask128 = (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff)) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  assert (v mask128 == v mask0 + pow2 64 * v mask1);

  let n_2 = (n_1) &. mask128 in
  let lo' = lo &. mask0 in
  let hi' = hi &. mask1 in
  logand_spec n_1 mask128;
  logand_spec lo mask0;
  logand_spec hi mask1;
  assert (v n_2 == UInt.logand #128 (v n_1) (v mask128));
  assert (v lo' == UInt.logand #64 (v lo) (v mask0));
  assert (v hi' == UInt.logand #64 (v hi) (v mask1));
  logand_uint64_uint128 (v lo) (v mask0) (v hi) (v mask1);
  ()

let prime_equiv:_:unit{S.prime == 0x03fffffffffffffffffffffffffffffffb} =
  assert_norm(S.prime == 0x03fffffffffffffffffffffffffffffffb)

let poly1305_encode_block_equiv (b:H.poly_block_t)
  : Lemma (H.poly1305_encode_block b == S.encode (seq_len b) b)
          [SMTPat (H.poly1305_encode_block b)] =
    Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC (b <: Lib.ByteSequence.lbytes 16)

let poly1305_encode_last_equiv (b:H.sub_block_t {range (Seq.length b) U32})
  : Lemma (H.poly1305_encode_last (seq_len b) b == S.encode (seq_len b) b)
          [SMTPat (H.poly1305_encode_last (seq_len b) b)] =
  let fb = array_from_slice (secret (pub_u8 0x0)) (16) (b) (usize 0) (seq_len (b)) in
  let n_1 = uint128_from_le_bytes fb in
  let n_2 = Lib.ByteSequence.nat_from_bytes_le b in
  assert (Lib.Sequence.sub fb 0 (seq_len b) == b);
  assert (forall i. i >= seq_len b ==> v fb.[i] == 0);
  nat_from_zero_bytes (Lib.Sequence.sub fb (seq_len b) (seq_len fb - seq_len b));
  assert (Lib.ByteSequence.nat_from_intseq_le (Lib.Sequence.sub fb (seq_len b) (seq_len fb - seq_len b)) == 0);
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC fb;
  Lib.ByteSequence.nat_from_intseq_le_slice_lemma fb (seq_len b);
  assert (v n_1 == n_2);
  ()


let poly1305_init_equiv (k:H.poly_key_t)
  : Lemma (let (a,r,k') = H.poly1305_init k in
           let (a',r') = S.poly1305_init k in
           a == a' /\ r == r' /\ k' == k)
           [SMTPat (H.poly1305_init k)] =
           ()

let poly1305_update_block_equiv (b:H.poly_block_t) (st:H.poly_state_t)
  : Lemma (let (a,r,k) = st in
           let a' = S.poly1305_update1 r (seq_len b) b a in
           H.poly1305_update_block b st == (a',r,k))
           [SMTPat (H.poly1305_update_block b st)]
           = ()

// let poly1305_update_blocks_equiv (m:byte_seq) (st:H.poly_state)
//   : Lemma (let (a,r,k) = st in
//            let (a',_,_) = H.poly1305_update_blocks m st in
//            let nblocks = seq_len m / 16 in
//            let m' = Lib.Sequence.sub #_ #(seq_len m) m 0 (nblocks * 16) in
//            a' == Lib.Sequence.repeat_blocks_multi 16 m' (S.poly1305_update1 r 16) a) 
//            [SMTPat (H.poly1305_update_blocks m st)]
//            =
//            admit()


let poly1305_update_last_equiv (b:H.sub_block_t{seq_len b < 16}) (st:H.poly_state_t)
  : Lemma (let (a,r,k) = st in
           let a' = S.poly1305_update_last r (seq_len b) b a in
           H.poly1305_update_last (seq_len b) b st == (a',r,k))
           [SMTPat (H.poly1305_update_last (seq_len b) b st)]
           = ()

let poly1305_finish_equiv (st:H.poly_state_t)
  : Lemma (let (a,r,k) = st in
           H.poly1305_finish st == S.poly1305_finish k a)
           [SMTPat (H.poly1305_finish st)] =
  let (a,r,k) = st in
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC (Lib.Sequence.sub k 16 16);
  let s : uint128 = Lib.ByteSequence.uint_from_bytes_le #U128 (Lib.Sequence.sub k 16 16) in
  let aby = nat_to_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) 16 (a) 
  in
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC aby;
  let a' = a % pow2 128 in
  assert (aby == Lib.ByteSequence.nat_to_bytes_le #SEC 16 a');
  let afull = Lib.ByteSequence.nat_from_bytes_le aby in
  let a128 = Lib.ByteSequence.uint_from_bytes_le #U128 aby in
  Lib.ByteSequence.lemma_nat_to_from_bytes_le_preserves_value aby 16 (a % pow2 128);
  assert (afull == a % pow2 128);
  let res1 =  (a + v s) % pow2 128 in
  let res2 : uint128 = a128 +. s in
  Math.Lemmas.lemma_mod_add_distr (v s) a (pow2 128);
  assert ((a + v s) % pow2 128 == (a % pow2 128 + v s) % pow2 128);
  assert (res1 == v res2);
  let resby1 = Lib.ByteSequence.nat_to_bytes_le #SEC 16 res1 in
  let resby2 = Lib.ByteSequence.uint_to_bytes_le #U128 #SEC res2 in
  Lib.ByteSequence.lemma_uint_to_bytes_le_preserves_value res2;
  Lib.ByteSequence.lemma_nat_to_from_bytes_le_preserves_value resby1 16 res1;
  Lib.ByteSequence.nat_from_intseq_le_inj resby1 resby2;
  assert (resby1 == resby2);
  admitP (H.poly1305_finish st == resby2);
  assert (S.poly1305_finish k a == resby1);
  ()

(*
  The above proof assumes that a.to_byte_seq_le() is changed to a.to_byte_seq_le(16)
  which is then translated as above. If we instead extract 17 bytes, then we have
  to use the nat_from_intseq_le_slice lemma, to cut off the bytstream at 16 bytes
  and then use % pow2 128 etc. This works, but I have removed the proof, since
  it won't be necessary.
*)

// let poly1305_update_block
//   (b_11 : poly_block_t)
//   (st_12 : poly_state_t)
//   : poly_state_t =
//   let (acc_13, r_14, k_15) : (field_element_t & field_element_t & poly_key_t) =
//     st_12
//   in
//   (((poly1305_encode_block (b_11)) +% (acc_13)) *% (r_14), r_14, k_15)

// let poly1305_update1 (r:felem) (len:size_nat{len <= size_block}) (b:lbytes len) (acc:felem) : Tot felem =
//   (encode len b `fadd` acc) `fmul` r

let poly1305_update_blocks
  (m : byte_seq)
  (st : H.poly_state_t)
  : r:H.poly_state_t{r == H.poly1305_update_blocks m st} =
  let blocks: uint_size = seq_len m / H.blocksize_v in
  let f (i: uint_size {i < blocks}) (s: H.poly_state_t) = H.poly1305_update_block (array_from_seq 16 (seq_get_exact_chunk m H.blocksize_v i)) s in
  let f' = (fun (i: uint_size {i < blocks}) (s: H.poly_state_t) -> 
          let (a, r, k) = s in
          let b = array_from_seq 16 (seq_get_exact_chunk m H.blocksize_v i) in
          let a' = S.poly1305_update1 r (seq_len b) b a in
           // H.poly1305_update_block b st == (a',r,k)
           (a',r,k)
        // S.poly1305_update1 (array_from_seq 16 (seq_get_exact_chunk m H.blocksize_v i)) s
  ) in
  assert (forall i x. f i x == f' i x);
  let _ = foldi 0 blocks f' st in
  let r: H.poly_state_t = foldi 0 blocks f st in
  r
  

let poly1305_update_equiv (m:byte_seq) (st:H.poly_state)
  : Lemma (let (a,r,k) = st in
           let a' = S.poly1305_update m a r in
           H.poly1305_update m st == (a',r,k))
           [SMTPat (H.poly1305_update m st)]
  =
    admit()

let poly1305_mac_equiv (m:byte_seq) (k:H.poly_key)
  : Lemma (H.poly1305 m k == S.poly1305_mac m k) =
    ()
