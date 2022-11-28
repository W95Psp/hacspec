module Hacspec.Chacha20.NProof

open FStar.Tactics
open Hacspec.Chacha20
module H = Hacspec.Chacha20
module S = Spec.Chacha20

open FStar.Mul
open Hacspec.Lib
open Lib.LoopCombinators

/// Utility lemmas
let rec make_list (elem: 'a) (n: nat): list 'a
  = if n = 0 then [] else elem::make_list elem (n-1)

let unfold_repeat (f: 'a -> 'a) (acc0: 'a) (i:pos)
  : Lemma (repeat i f acc0 == f (repeat (i - 1) f acc0))
  = unfold_repeat i f acc0 (i-1) 

let unfold_foldi (lo: uint_size) (hi: uint_size{lo <= hi})
                 (f: (i:uint_size{i < hi}) -> 'a -> 'a)
                 (init: 'a)
  : Lemma (foldi lo hi f init == (if lo = hi then init else
                                 foldi_ (lo + 1) hi f (f lo init)))
  = assert_norm ((foldi lo hi f init == (if lo = hi then init else
                                 foldi (lo + 1) hi f (f lo init))))

let eq_foldi0 (hi: uint_size) (f: (i:uint_size{i < hi}) -> 'a -> 'a) (init: 'a)
  : Lemma (foldi hi hi f init == init)
  = assert_norm (foldi hi hi f init == init)
let map_blocks_foldi'
    (#len: uint_size) (blen:uint_size) (lo: uint_size) (hi: uint_size {hi * blen <= len /\ lo <= hi})
    (f: (i:uint_size{i < hi}) -> lseq 'a blen) (s: lseq 'a len)
    : lseq 'a len
  = foldi lo hi (fun i (s: lseq 'a len) -> seq_set_exact_chunk #_ #(Seq.length s) s blen i (f i)) s

open IndexableContent

#push-options "--max_fuel 0 --z3rlimit 15"
let foldi_update_block
    (#len: uint_size) (blen:uint_size {blen > 0 /\ blen < len}) (lo: uint_size) (hi: uint_size {blen * hi <= len /\ lo <= hi})
    (f: (i:uint_size{i < hi}) -> lseq 'a blen) (s0: lseq 'a len)
  : Lemma (assert (forall (i:nat). i < hi ==> blen * (i+1) <= len);
    let sn = map_blocks_foldi' #'a #len blen lo hi f s0 in
      (forall (i:nat). i >= lo /\ i < hi ==> seq_get_exact_chunk sn blen i == f i)
    /\ (forall (i:nat). i < lo /\ i < hi ==> seq_get_exact_chunk sn blen i == seq_get_exact_chunk s0 blen i))
  = let c = chunked_seq_to_indexable_content 'a len blen hi in
    foldi_indexable_content_lemma c lo hi (fun i -> f i) s0;
    let sn = foldi lo hi (fun i x1 -> c.set x1 i (f i)) s0 in
    assert (sn == map_blocks_foldi' #'a #len blen lo hi f s0)
        by (compute (); trefl ())
#pop-options

let rewrite_eq_of_application #a #b (f: a -> b) (g: a -> b) s0 s1
  : Lemma (requires s0 == s1 /\ (forall x. f x == g x))
          (ensures f s0 == g s1)
  = ()

let array_upd_twice_ignore (#a: Type) (#len:uint_size) (s: lseq a len) (i: uint_size{i < len}) (v1 v2: a)
  : Lemma (array_upd (array_upd s i v1) i v2 == array_upd s i v2)
  = assert (FStar.Seq.equal (array_upd (array_upd s i v1) i v2) (array_upd s i v2))

let rec foldi_update (lo: uint_size) (hi: uint_size {lo <= hi})
  (f: (i:uint_size{i < hi}) -> 'a) (s0: lseq 'a hi)
  : Lemma (ensures (let sn: lseq 'a hi = foldi lo hi (fun i s -> array_upd s i (f i)) s0
                   in (forall (i:nat). i >= lo /\ i < hi ==> Seq.index sn i == f i)
                    /\ (forall (i:nat). i < lo          ==> Seq.index sn i == Seq.index s0 i))
          ) (decreases hi - lo)
  = if lo = hi
    then eq_foldi0 hi (fun i s -> array_upd s i (f i)) s0
    else foldi_update (lo + 1) hi f (array_upd s0 lo (f lo));
         unfold_foldi lo hi (fun i s -> array_upd s i (f i)) s0

let array_add_lemma #len (f: 'a -> 'a -> 'a) (k s: lseq 'a len)
  : Lemma (Lib.Sequence.map2 f k s == array_add f k s)
          [SMTPat (array_add f k s)]
  = let g (i:uint_size{i < len}) = array_index k i `f` array_index s i in
    foldi_update 0 len g k;
    array_add f k s `Seq.lemma_eq_intro` (*TODO: issue with map2 here*) Lib.Sequence.map2' f k s

let array_xor_lemma #len (f: 'a -> 'a -> 'a) (k s: lseq 'a len)
  : Lemma (Lib.Sequence.map2 f k s == array_xor f k s)
          [SMTPat (array_xor f k s)]
  = let g (i:uint_size{i < len}) = array_index k i `f` array_index s i in
    foldi_update 0 len g k;
    array_add f k s `Seq.lemma_eq_intro` (*TODO: issue with map2 here*) Lib.Sequence.map2' f k s

let equal_up_to_secrecy #len (s1: lseq (uint_t 't PUB) len) (s2: lseq (uint_t 't SEC) len)
  = forall i. secret (Seq.index s1 i) == Seq.index s2 i

let secrecy_equal_implies_map_equal
  #len (s1: lseq (uint_t 't PUB) len) (s2: lseq (uint_t 't SEC) len)
  : Lemma (requires equal_up_to_secrecy s1 s2)
          (ensures Lib.Sequence.map secret s1 `Seq.equal` s2)
          [SMTPat (equal_up_to_secrecy s1 s2)]
  = let open Lib.Sequence in
    let ll: (s2:lseq (uint_t 't SEC) len{(forall (i:nat).{:pattern (index s2 i)} i < len ==> index s2 i == secret s1.[i])}) = Lib.Sequence.map secret s1 in
    assert(forall (i:nat). i < len ==> index ll i == secret s1.[i]);
    assert (forall (i:nat{i < len}). index (Lib.Sequence.map secret s1) i == secret (Seq.index s1 i))

/// Proofs of equivalence
let equiv_line (a b d: state_idx_t) (s: pos {s < 32}) (state: state_t)
  : Lemma (S.line a b d (pub_u32 s) state == H.chacha20_line a b d s state)
          [SMTPat (H.chacha20_line a b d s state)]
  = let state = array_upd state a (array_index state a +. array_index state b) in
    array_upd_twice_ignore state d (array_index state d ^. array_index state a) (uint32_rotate_left (array_index state d ^. array_index state a) s)
 
let equiv_quarter_round (a b c d: state_idx_t) (state: state_t)
  : Lemma (S.quarter_round a b c d state == H.chacha20_quarter_round a b c d state)
          [SMTPat (chacha20_quarter_round a b c d state)]
  = ()

let equiv_double_round (state: state_t)
  : Lemma (S.double_round state == H.chacha20_double_round state)
          [SMTPat (H.chacha20_double_round state)]
  = ()

let equiv_rounds (st: state_t)
  : Lemma (S.rounds st == H.chacha20_rounds st)
          [SMTPat (H.chacha20_rounds st)]
  = assert (S.rounds st == chacha20_rounds st) by (
      norm [delta_only [`%S.rounds; `%chacha20_rounds]];
      iter (fun _ ->
        l_to_r [`unfold_repeat; `unfold_foldi];
        norm [primops; iota; delta_only [`%usize]]
      ) (make_list () 10);
      l_to_r [`eq_repeat0; `eq_foldi0];
      repeat' (fun _ -> apply_lemma (`rewrite_eq_of_application))
    )

let _chacha20_core (ctr: uint32) (st0: state_t): state_t =
  let state = array_upd st0 12 (array_index st0 12 +. ctr) in
  chacha20_rounds state `array_add (+.)` state

let s_chacha20_core (ctr:S.counter) (s0:S.state): Tot S.state =
  let k = S.chacha20_add_counter s0 ctr in
  let k = S.rounds k in
  let k = S.sum_state k s0 in
  k
  // S.chacha20_add_counter k  ctr

let _chacha20_core' (ctr: uint32) (s0: state_t)
  : r:state_t{r == _chacha20_core ctr s0} =
  let s1 = array_upd s0 12 (array_index s0 12 +. ctr) in
  let k = S.chacha20_add_counter s0 (v ctr) in
  assert (s1 == k);
  let s2 = chacha20_rounds s1 in
  assert (s2 == S.rounds k);
  s2 `array_add (+.)` s1

let equiv_core (ctr: uint32) (st0: state_t)
  : Lemma (S.chacha20_core (v ctr) st0 == chacha20_core ctr st0)
          [SMTPat (chacha20_core ctr st0)]
  = admit ()

#pop-options

let equiv_constants_init
  : squash (Lib.Sequence.map secret S.chacha20_constants == chacha20_constants_init ())
  = let l = S.([c0;c1;c2;c3]) in
    assert_norm (FStar.List.Tot.length l == 4);
    assert_norm S.(let h (i:nat{i<4}) = FStar.List.Tot.index l i in h 0 = c0 /\ h 1 = c1 /\ h 2 = c2 /\ h 3 = c3);
    Lib.Sequence.eq_intro (Lib.Sequence.map #_ #_ #(4 <: size_nat) secret S.chacha20_constants) (chacha20_constants_init ())
    
let equiv_init (key: cha_cha_key_t) (iv: cha_cha_iv_t) (ctr: uint32)
  : Lemma (S.chacha20_init key iv (v ctr) == chacha20_init key iv ctr)
          [SMTPat (chacha20_init key iv ctr)]
  = ()

let equiv_key_block (state: state_t)
  : Lemma (S.chacha20_key_block state == chacha20_key_block state)
          [SMTPat (chacha20_key_block state)]
  = ()

let equiv_key_block0 (key: cha_cha_key_t) (iv: cha_cha_iv_t)
  : Lemma (chacha20_key_block0 key iv == S.chacha20_key_block0 key iv)
          [SMTPat (chacha20_key_block0 key iv)]
  = ()

let equiv_encrypt_block (st0: state_t) (ctr: uint32) (plain: block_t)
  : Lemma (H.chacha20_encrypt_block st0 ctr plain == S.chacha20_encrypt_block st0 (v ctr) plain)
          [SMTPat (chacha20_encrypt_block st0 ctr plain)]
  = ()

let equiv_encrypt_last (st0:state_t) (ctr:uint32) (plain: byte_seq {seq_len plain < 64})
  : Lemma (H.chacha20_encrypt_last st0 ctr plain == S.chacha20_encrypt_last st0 (v ctr) (seq_len plain) plain)
          [SMTPat (H.chacha20_encrypt_last st0 ctr plain)]
  = ()


unfold let map_blocks_foldi'0
    (#len: uint_size) (blen:uint_size) (lo: uint_size) (hi: uint_size {hi * blen <= len /\ lo <= hi})
    (f: (i:uint_size{i < hi}) -> lseq 'a blen) (s: lseq 'a len)
    : r:lseq 'a len {r == u7u7u7map_blocks_foldi' #'a #len blen lo hi f s}
  = foldi lo hi (fun i (s: lseq 'a len) ->
      seq_set_exact_chunk #_ #(Seq.length s) s blen i (f i)
    ) s

// let chacha20_update ctx msg =
//   let cipher = msg in
//   Lib.Sequence.map_blocks size_block cipher
//     (chacha20_encrypt_block ctx)
//     (chacha20_encrypt_last ctx)


let chacha20_update (st : state_t) (m : byte_seq {Seq.length m > 64}) : x:byte_seq{x == H.chacha20_update st m} =
  let blocks_out: seq uint8 = seq_new_ (secret (pub_u8 0)) (seq_len m) in
  let n_blocks: uint_size = seq_num_exact_chunks m 64 in
  let f (i: nat {i<n_blocks}): block_t = 
    let msg_block = seq_get_exact_chunk m 64 i in
    chacha20_encrypt_block st (secret (pub_u32 i)) (array_from_seq 64 msg_block)
  in
  let blocks_out = map_blocks_foldi'0 #_ #(Seq.length m) 64 0 n_blocks f blocks_out in
  let last_block = seq_get_remainder_chunk m 64 in
  if seq_len last_block <> 64 then
    let b = chacha20_encrypt_last st (secret (pub_u32 n_blocks)) last_block in
    seq_set_chunk blocks_out 64 (seq_num_chunks m 64 - 1) b
  else blocks_out



  // = if lo = hi
  //   then eq_foldi0 hi (fun i s -> array_upd s i (f i)) s0
  //   else foldi_update (lo + 1) hi f (array_upd s0 lo (f lo));
  //        unfold_foldi lo hi (fun i s -> array_upd s i (f i)) s0

