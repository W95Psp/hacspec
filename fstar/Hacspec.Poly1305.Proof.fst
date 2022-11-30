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
  logand_uint64_uint128 (v lo) (v mask0) (v hi) (v mask1)

let prime_equiv: squash (S.prime == 0x03fffffffffffffffffffffffffffffffb)
  = _ by (Tactics.compute ())

// [H.field_element_t] is [x:ℕ{x<S.prime}] while [S.felem] is
// [x:ℕ{x<=S.prime-1}]
let lemma_field_element_t_felem: squash (H.field_element_t == S.felem)
  = _ by FStar.Tactics.(
      compute ();
      // Rewrite [a≤b] into [a<b+1]
      l_to_r [binder_to_term (tcut (quote ((a:int) -> (b:int) -> squash ((a <= b) == (a < b + 1)))))];
      // normalize that `b+1`
      norm [primops];
      // we're left with the arrow goal [tcut] introduced, convert it to an implication
      trefl (); let _ = intros () in ()
    )

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
  assert (v n_1 == n_2)

let poly1305_init_equiv (k:H.poly_key_t)
  : Lemma ( let a , r, k'= H.poly1305_init k in
            let a', r'   = S.poly1305_init k in
            a == a' /\ r == r' /\ k' == k
          ) [SMTPat (H.poly1305_init k)] = ()

let poly1305_update_block_equiv (b:H.poly_block_t) (st:H.poly_state_t)
  : Lemma ( let a, r, k = st in
            let a' = S.poly1305_update1 r (seq_len b) b a in
            H.poly1305_update_block b st == (a', r, k)
          ) [SMTPat (H.poly1305_update_block b st)] = ()

let poly1305_update_last_equiv (b:H.sub_block_t{seq_len b < 16}) (st:H.poly_state_t)
  : Lemma ( let a, r, k = st in
            let a' = S.poly1305_update_last r (seq_len b) b a in
            H.poly1305_update_last (seq_len b) b st == (a',r,k)
          ) [SMTPat (H.poly1305_update_last (seq_len b) b st)] = ()

let nat_to_byte_seq_le_lemma (n: pos) (len: uint_size) (x: nat_mod n) 
  : Lemma (forall (i: nat {i < len}). FStar.Seq.index (nat_to_byte_seq_le n len x) i
                            == uint #U8 #SEC ((x / pow2 (8 * i)) % pow2 8))
  = let y = x % (pow2 (8 * len)) in
    introduce forall (i: nat {i < len}). FStar.Seq.index (Lib.ByteSequence.nat_to_intseq_le #U8 #SEC len y) i
                               == uint #U8 #SEC ((x / pow2 (8 * i)) % pow2 8)
         with begin let j = len - i in
                    Lib.ByteSequence.index_nat_to_intseq_le #U8 #SEC len y i;
                    Math.Lemmas.modulo_division_lemma x (pow2 (8*i)) (pow2 (8*j));
                    Math.Lemmas.pow2_plus (8*(j-1)) 8;
                    Math.Lemmas.modulo_modulo_lemma (x / pow2 (8*i)) (pow2 8) (pow2 (8*(j-1)));
                    Math.Lemmas.pow2_plus (8*i) (8*j) end

let poly1305_finish_equiv (st:H.poly_state_t)
  : Lemma (let (a,r,k) = st in
           H.poly1305_finish st == S.poly1305_finish k a)
           [SMTPat (H.poly1305_finish st)] =
  let (a,r,k) = st in
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC (Lib.Sequence.sub k 16 16);
  let s : uint128 = Lib.ByteSequence.uint_from_bytes_le #U128 (Lib.Sequence.sub k 16 16) in
  let aby' = nat_to_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) 17 (a) in
  let aby = nat_to_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) 16 (a) in
  let sliced_aby = array_from_slice (secret (pub_u8 0x0)) 16 aby' 0 16 in
  nat_to_byte_seq_le_lemma 0x03fffffffffffffffffffffffffffffffb 17 a;
  nat_to_byte_seq_le_lemma 0x03fffffffffffffffffffffffffffffffb 16 a;
  assert (aby `Seq.equal` sliced_aby);
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
  assert (H.poly1305_finish st == resby2);
  assert (S.poly1305_finish k a == resby1)

let transitivity_eq (a b c: 'a): Lemma (requires a == b /\ b == c) (ensures a == c)
  = ()

#push-options "--z3rlimit 15"
let poly1305_update_equiv'
  (m : byte_seq)
  (st : H.poly_state_t)
  : r:H.poly_state_t{
      r == H.poly1305_update m st
    /\ r._1 == S.poly1305_update m st._1 st._2
  } =
  let blocks: uint_size = seq_len m / H.blocksize_v in
  let f0: (i:uint_size {i < blocks}) -> H.poly_state_t -> H.poly_state_t
    = fun i s -> H.poly1305_update_block (array_from_seq 16 (seq_get_exact_chunk m H.blocksize_v i)) s in
  let f1: (i:uint_size {i < blocks}) -> H.poly_state_t -> H.poly_state_t
    = fun i s -> let a, r, k = s in
              let b = array_from_seq 16 (seq_get_exact_chunk m H.blocksize_v i) in
              let a' = S.poly1305_update1 r (seq_len b) b a in
              a', r, k
  in
  let f2: (i:uint_size {i < blocks}) -> s:H.poly_state_t -> s':H.poly_state_t{
      let a0, r0, k0 = s  in
      let a1, r1, k1 = s' in
      r0 == r1 /\ k0 == k1
    }
    = fun i s -> let a, r, k = s in
              let b = array_from_seq 16 (seq_get_exact_chunk m H.blocksize_v i) in
              let a' = S.poly1305_update1 r (seq_len b) b a in
              a', r, k
  in
  let f3: r:H.field_element_t -> (i:uint_size {i < blocks}) -> a0:H.field_element_t -> a1:H.field_element_t
    = fun r i a0 -> let b = array_from_seq 16 (seq_get_exact_chunk m H.blocksize_v i) in
                let a1 = S.poly1305_update1 r (seq_len b) b a0 in
                a1
  in
  assert (forall (i: uint_size {i < blocks}) (s: H.poly_state_t). f1 i s == f2 i s);
  introduce forall (i: uint_size {i < blocks}) (s: H.poly_state_t). f0 i s == f1 i s
  with begin let b = array_from_seq 16 (seq_get_exact_chunk m H.blocksize_v i) in
             poly1305_update_block_equiv (array_from_seq 16 (seq_get_exact_chunk m H.blocksize_v i)) s;
             assert (f1 i s == H.poly1305_update_block b s) end;
  Hacspec.Lib.FoldiLemmas.foldi_extensionality 0 blocks f0 f1 st;
  let r0: H.poly_state_t = foldi 0 blocks f0 st in
  let r1: H.poly_state_t = foldi 0 blocks f1 st in
  let r2: H.poly_state_t = foldi 0 blocks f2 st in
  transitivity_eq r0 r1 r2;
  let r3'0: H.field_element_t = foldi 0 blocks (f3 st._2) st._1 in
  let r3: H.poly_state_t = (r3'0, st._2, st._3) in
  Hacspec.Lib.FoldiLemmas.foldi_relation 0 blocks
                 f2 (f3 st._2)
                 (fun (a, r, k) a' -> a' == a /\ r == st._2 /\ k == st._3)
                 st st._1;
  transitivity_eq r0 r2 r3;
  assert (r3 == r0);
  let r3'1 = Seq.repeat_blocks #uint8 #S.felem S.size_block m
    (S.poly1305_update1 st._2 S.size_block)
    (S.poly1305_update_last st._2) st._1 in
    
  Seq.lemma_repeat_blocks #uint8 #S.felem S.size_block m
    (S.poly1305_update1 st._2 S.size_block)
    (S.poly1305_update_last st._2) st._1;
    
  let r3'3: H.field_element_t = Lib.LoopCombinators.repeat_right 0 blocks (Lib.LoopCombinators.fixed_a S.felem) (f3 st._2) st._1  in
  foldi_equiv_repeat_right 0 blocks (f3 st._2) st._1;

  let last0 : seq uint8 = seq_get_remainder_chunk m H.blocksize_v in
  let all0 = H.poly1305_update_last (seq_len last0) last0 r3 in

  let len = FStar.Seq.length m in
  let nb = len / S.size_block in
  let rem = len % S.size_block in
  let r3'2'0 = Lib.LoopCombinators.repeati nb (Seq.repeat_blocks_f S.size_block m (S.poly1305_update1 st._2 S.size_block) nb) st._1 in
  let r3'2'1 = Lib.LoopCombinators.repeati nb (f3 st._2) st._1 in
  Lib.Sequence.Lemmas.repeati_extensionality #S.felem nb (f3 st._2) (Seq.repeat_blocks_f S.size_block m (S.poly1305_update1 st._2 S.size_block) nb) st._1;
  assert (r3'2'1 == r3'2'0);
  // assert (Lib.LoopCombinators.repeati nb (Seq.repeat_blocks_f S.size_block m (S.poly1305_update1 st._2 S.size_block) nb) st._1 == Lib.LoopCombinators.repeati nb (f3 st._2) st._1);
  let r3'2'2 = Lib.LoopCombinators.repeat_right 0 nb (Lib.LoopCombinators.fixed_a S.felem) (f3 st._2) st._1 in
  Lib.LoopCombinators.repeati_def nb (f3 st._2) st._1;
  assert (r3'2'1 == r3'2'2);
  assert (r3'2'2 == r3'3);
  assert (r3'2'0 == r3'0);
  let last1 = FStar.Seq.slice m (nb * S.size_block) len in
  assert (last0 `FStar.Seq.equal` last1);
  let all1 = S.poly1305_update_last st._2 rem last1 r3'2'0 in
  assert (r3'1 == all1);
  assert (all0._1 == all1);
  assert (r3'2'0 == r3'2'0);
  all0
#pop-options

let poly1305_update_equiv (m:byte_seq) (st:H.poly_state_t)
  : Lemma ( let a, r, k = st in
            let a' = S.poly1305_update m a r in
            H.poly1305_update m st == (a',r,k)
          ) [SMTPat (H.poly1305_update m st)]
  = let _ = poly1305_update_equiv' m st in
    ()

let poly1305_mac_equiv (m:byte_seq) (k:H.poly_key_t)
  : Lemma (H.poly1305 m k == S.poly1305_mac m k) =
    ()
