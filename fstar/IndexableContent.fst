module IndexableContent

open FStar.Tactics
open Hacspec.Chacha20
module H = Hacspec.Chacha20
module S = Spec.Chacha20

open FStar.Mul
open Hacspec.Lib
open Lib.LoopCombinators

open FStar.Math.Lemmas
open FStar.Preorder

/// Utility lemmas
let unfold_foldi (lo: uint_size) (hi: uint_size{lo <= hi})
                 (f: (i:uint_size{i < hi}) -> 'a -> 'a)
                 (init: 'a)
  : Lemma (foldi lo hi f init == (if lo = hi then init else
                                 foldi (lo + 1) hi f (f lo init)))
  = assert_norm ((foldi lo hi f init == (if lo = hi then init else
                                 foldi (lo + 1) hi f (f lo init))))

noeq type indexable_content (t: Type)
  = { len: uint_size
    ; a: Type
    ; inv: preorder t
    ; get: x:t -> i:nat{i<len} ->   a
    ; set: x:t -> i:nat{i<len} -> v:a 
         -> r:t{inv x r /\ get r i == v /\ (forall (j:nat). j<len /\ i<>j ==> get r j == get x j)}
    }

let rec foldi_indexable_content_lemma
    (c: indexable_content 't) (lo: nat) (hi: uint_size {hi <= c.len /\ lo <= hi})
    (f: (i: nat{i < hi}) -> c.a) (x: 't)
  : Lemma (ensures (let x' = foldi lo hi (fun i x1 -> c.set x1 i (f i)) x in
                    c.inv x x' /\ (forall (i:nat). i>=lo /\ i<hi ==> c.get x' i == f i)
                             /\ (forall (i:nat). i<lo /\ i<hi ==> c.get x' i == c.get x i)))
          (decreases hi - lo)
  = unfold_foldi lo hi (fun i x -> c.set x i (f i)) x;
    if lo <> hi then foldi_indexable_content_lemma c (lo+1) hi f (c.set x lo (f lo))

#push-options "--z3rlimit 5"
let set_chunk_leave_everything_else_proof_i
  (len chunk_len: nat)
  (max_chunk: nat {max_chunk * chunk_len <= len})
  (nth:       nat {nth < max_chunk})
  (i:         nat {i < chunk_len})
  : Lemma (ensures nth * chunk_len + i < len)
  = assert (nth * chunk_len + i < (nth + 1) * chunk_len)
#pop-options

#push-options "--z3rlimit 5"
let expand_subtraction (a b d: int): Lemma ((a - b) * d == a * d - b * d) = ()
let division_order_lemma_ge (a b:nat) (d:pos): Lemma (requires a >= b) (ensures a/d >= b/d)
  = let ka, kb = a/d, b/d in
    euclidean_division_definition a d;
    euclidean_division_definition b d;
    if ka < kb then expand_subtraction kb ka d else ()

let division_order_lemma_gt (a b:nat) (d:pos): Lemma (requires a > b) (ensures a/d >= b/d)
  = division_order_lemma_ge a b d

let multipliciation_plus_remainder_order_lemma (a1 a2 b: nat) (i: int {abs i < b})
  : Lemma (requires a1 * b + i >= a2 * b)
          (ensures  a1 * b     >= a2 * b)
  = if a1 * b < a2 * b
    then (assert (a1 < a2);
          division_order_lemma_ge (a1 * b + i) (a2 * b) b;
          assert ((a1*b + i)/b >= (a2*b)/b);
          lemma_div_plus i a1 b; lemma_div_plus 0 a2 b; small_div (abs i) b;
          assert (a1 >= a2))
#pop-options

let _ = Lib.Sequence.repeat_blocks

#push-options "--z3rlimit 15"
let seq_set_chunk_pointwise_equality
  (#a: Type) (#len:uint_size) (s: lseq a len)
  (chunk_len: uint_size)
  (max_chunk: uint_size {max_chunk * chunk_len <= len})
  (chunk_num: uint_size {chunk_num < max_chunk})
  (chunk: seq a)
  (nth: nat {nth < max_chunk /\ nth <> chunk_num})
  (i: nat {i < chunk_len})
  : Lemma (requires chunk_len * (chunk_num + 1) <= Seq.length s /\
                    Seq.length chunk = seq_chunk_len s chunk_len chunk_num)
          (ensures (set_chunk_leave_everything_else_proof_i len chunk_len max_chunk nth i;
                    (Lib.Sequence.index (seq_set_exact_chunk s chunk_len chunk_num chunk) (nth * chunk_len + i) == Lib.Sequence.index s (nth * chunk_len + i))))
  = let o = seq_set_exact_chunk s chunk_len chunk_num chunk in
    let k = nth * chunk_len + i in
    set_chunk_leave_everything_else_proof_i len chunk_len max_chunk nth i;
    introduce k >= chunk_len * chunk_num /\ k < chunk_len * (chunk_num + 1) ==> False
    with _. ( multipliciation_plus_remainder_order_lemma nth chunk_num chunk_len i;
              multiplication_order_lemma nth chunk_num chunk_len;
              multipliciation_plus_remainder_order_lemma (chunk_num + 1) nth chunk_len (- i - 1);
              multiplication_order_lemma (chunk_num + 1) nth chunk_len;
              assert (nth >= chunk_num /\ nth < chunk_num)
            );
    assert ((0 <= k /\ k < chunk_len * chunk_num) \/ (chunk_len * (chunk_num + 1) <= k /\ k < len))

let seq_set_chunk_nthchunk_equality
  (#a: Type) (#len:uint_size) (s: lseq a len)
  (chunk_len: uint_size) 
  (max_chunk: uint_size {max_chunk * chunk_len <= len})
  (chunk_num: uint_size {chunk_num < max_chunk})
  (chunk: seq a)
  (nth: nat {nth < max_chunk /\ nth <> chunk_num /\ (nth + 1) * chunk_len <= len})
  : Lemma (requires chunk_len * (chunk_num + 1) <= Seq.length s /\ 
                    Seq.length chunk = seq_chunk_len s chunk_len chunk_num)
          (ensures seq_get_exact_chunk s chunk_len nth 
                == seq_get_exact_chunk (seq_set_exact_chunk s chunk_len chunk_num chunk) chunk_len nth)
  = let o = seq_set_exact_chunk s chunk_len chunk_num chunk in
    introduce forall i. (set_chunk_leave_everything_else_proof_i len chunk_len max_chunk nth i;
                    Lib.Sequence.index o (nth * chunk_len + i) == Lib.Sequence.index s (nth * chunk_len + i))
         with begin
           set_chunk_leave_everything_else_proof_i len chunk_len max_chunk nth i;
           seq_set_chunk_pointwise_equality s chunk_len max_chunk chunk_num chunk nth i
         end;
    let nth_chunk : lseq _ chunk_len = seq_get_exact_chunk s chunk_len nth in
    let nth_chunk': lseq _ chunk_len = seq_get_exact_chunk o chunk_len nth in
    assert (forall (i:nat {i < chunk_len}). Lib.Sequence.index o (nth * chunk_len + i) == Lib.Sequence.index s (nth * chunk_len + i));
    assert (forall (i:nat {i < chunk_len}). Lib.Sequence.index nth_chunk i == Lib.Sequence.index s (nth * chunk_len + i));
    assert (forall (i:nat {i < chunk_len}). Lib.Sequence.index nth_chunk' i == Lib.Sequence.index o (nth * chunk_len + i));
    assert (forall (i:nat {i < chunk_len}). Lib.Sequence.index nth_chunk' i == Lib.Sequence.index nth_chunk i);
    Lib.Sequence.eq_intro nth_chunk' nth_chunk
#pop-options

#push-options "--z3rlimit 100"
let seq_set_chunk_chunkwise_equality
  (#a: Type) (#len:uint_size) (s: lseq a len)
  (chunk_len: uint_size) 
  (max_chunk: uint_size {max_chunk * chunk_len <= len})
  (chunk_num: uint_size {chunk_num < max_chunk})
  (chunk: seq a)
  : Lemma (requires chunk_len * (chunk_num + 1) <= Seq.length s /\ 
                    Seq.length chunk = seq_chunk_len s chunk_len chunk_num)
          (ensures (forall (nth:nat{nth < max_chunk /\ nth <> chunk_num}).
                      seq_get_exact_chunk s chunk_len nth 
                   == seq_get_exact_chunk (seq_set_exact_chunk s chunk_len chunk_num chunk) chunk_len nth))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (seq_set_chunk_nthchunk_equality s chunk_len max_chunk chunk_num chunk))
#pop-options

let set_chunk_leave_everything_else_above
  (#a: Type) (#len:uint_size) (s: lseq a len)
  (chunk_len: uint_size) 
  (max_chunk: uint_size {max_chunk * chunk_len <= len})
  (chunk_num: uint_size {chunk_num < max_chunk})
  (chunk: seq a)
  : Lemma (requires chunk_len * (chunk_num + 1) <= Seq.length s /\
                    Seq.length chunk = seq_chunk_len s chunk_len chunk_num)
          (ensures 
            forall (i: nat). i >= max_chunk * chunk_len /\ i < len ==> Lib.Sequence.index s i == Lib.Sequence.index (seq_set_exact_chunk s chunk_len chunk_num chunk) i
          )
  = ()

let chunked_seq_to_indexable_content (t: Type0)
  (seq_len: uint_size)
  (chunk_len: pos {chunk_len <= seq_len})
  (max_chunk: uint_size {max_chunk * chunk_len <= seq_len})
  : indexable_content (lseq t seq_len)
  = let inv: preorder (lseq t seq_len) = (fun (x y: lseq t seq_len) -> 
      forall (i:nat). i >= max_chunk * chunk_len /\ i < seq_len ==> Seq.index x i == Seq.index y i
    ) in
    let get (s: lseq t seq_len) (i: nat {i < max_chunk}): lseq t chunk_len =
          seq_get_exact_chunk #t s chunk_len i
    in
    let set (s: lseq t seq_len) (i: nat {i < max_chunk}) (v: lseq t chunk_len): r: lseq t seq_len {
          inv s r
        /\ get r i == v
        /\ (forall (j: nat). j < max_chunk /\ i <> j ==> get r j == get s j)
      } =
          let r = seq_set_exact_chunk #t #(seq_len) s chunk_len i v in
          assert (get r i `Seq.equal` v);
          seq_set_chunk_chunkwise_equality s chunk_len max_chunk i v;
          set_chunk_leave_everything_else_above s chunk_len max_chunk i v;
          r
    in { len = max_chunk; inv; a = lseq t chunk_len; get; set }

let seq_to_indexable_content (t: Type)
  (len: uint_size)
  : indexable_content (lseq t len)
  = { len; inv = (fun _ _ -> True);
      get = (fun s i -> array_index s i);
      set = (fun s i v -> array_upd s i v);
      a = t; }

let map_blocks_foldi'
    (#len: uint_size) (blen:uint_size) (lo: uint_size) (hi: uint_size {hi * blen <= len /\ lo <= hi})
    (f: (i:uint_size{i < hi}) -> lseq 'a blen) (s: lseq 'a len)
    : lseq 'a len
  = foldi lo hi (fun i (s: lseq 'a len) -> seq_set_exact_chunk #_ #len s blen i (f i)) s

unfold let map_blocks_foldi'0
    (#len: uint_size) (blen:uint_size) (lo: uint_size) (hi: uint_size {hi * blen <= len /\ lo <= hi})
    (f: (i:uint_size{i < hi}) -> lseq 'a blen) (s: lseq 'a len)
    : r:lseq 'a len {r == map_blocks_foldi' #'a #len blen lo hi f s}
  = foldi lo hi (fun i (s: lseq 'a len) ->
      seq_set_exact_chunk #_ #len s blen i (f i)
    ) s

#push-options "--max_fuel 0 --z3rlimit 15"
let foldi_update_block
    (#len: uint_size) (blen:pos {blen < len}) (lo: uint_size) (hi: uint_size {hi * blen <= len /\ lo <= hi})
    (f: (i:uint_size{i < hi}) -> lseq 'a blen) (s0: lseq 'a len)
  : Lemma (
      assert (forall (i:nat). i < hi ==> blen * (i+1) <= len);
      let sn = map_blocks_foldi' #'a #len blen lo hi f s0 in
        (forall (i:nat). i >= lo /\ i < hi ==> seq_get_exact_chunk sn blen i == f i)
      /\ (forall (i:nat). i < lo /\ i < hi ==> seq_get_exact_chunk sn blen i == seq_get_exact_chunk s0 blen i)
      // /\ seq_get_remainder_chunk sn == seq_get_remainder_chunk s0
      /\ (forall (i:nat). i >= hi * blen /\ i < len ==> Seq.index sn i == Seq.index s0 i)
    )
  = let c = chunked_seq_to_indexable_content 'a len blen hi in
    foldi_indexable_content_lemma c lo hi (fun i -> f i) s0;
    let sn = foldi lo hi (fun i x1 -> c.set x1 i (f i)) s0 in
    assert (sn == map_blocks_foldi' #'a #len blen lo hi f s0)
        by (compute (); trefl ())

let foldi_update_block_at
    (#len: uint_size) (blen:pos {blen < len}) (lo: uint_size) (hi: uint_size {hi * blen <= len /\ lo <= hi})
    (f: (i:uint_size{i < hi}) -> lseq 'a blen) (s0: lseq 'a len)
    (i:nat{i >= lo /\ i < hi})
  : Lemma (assert (i < hi ==> blen * (i+1) <= len);
           let sn = map_blocks_foldi' #'a #len blen lo hi f s0 in
           seq_get_exact_chunk sn blen i == f i
          )
  = foldi_update_block blen lo hi f s0
#pop-options


#push-options "--max_fuel 0 --z3rlimit 50"
let foldi_update_block_pointwise_blocks_at
    (#len: uint_size) (blen:pos {blen < len})
    (lo: uint_size) (hi: uint_size {hi * blen <= len /\ lo <= hi})
    (f: (i:uint_size{i < hi}) -> lseq 'a blen) (s0: lseq 'a len)
    (i:nat{i >= lo * blen /\ i < hi * blen})
  : Lemma (Seq.index (map_blocks_foldi' #'a #len blen lo hi f s0) i == Seq.index (f (i / blen)) (i % blen))
  = let sn = map_blocks_foldi' #'a #len blen lo hi f s0 in
    Lib.Sequence.div_mul_lt blen i hi;
    let nth = i / blen in
    admitP (nth >= lo /\ nth < hi);
    admitP (i >= nth * lo /\ i < nth * hi);
    foldi_update_block_at blen lo hi f s0 nth;
    assert (seq_get_exact_chunk sn blen nth == f nth);
    assert (Seq.index (seq_get_exact_chunk sn blen nth) (i % blen) == Seq.index (f nth) (i % blen));
    assert (Seq.index (seq_get_exact_chunk sn blen nth) (i % blen) == Seq.index sn i);
    assert (Seq.index (f nth) (i % blen) == Seq.index sn i)
#pop-options

#push-options "--max_fuel 0 --z3rlimit 5 --split_queries"
let foldi_update_block_pointwise_blocks
    (#len: uint_size) (blen:pos {blen < len})
    (lo: uint_size) (hi: uint_size {hi * blen <= len /\ lo <= hi})
    (f: (i:uint_size{i < hi}) -> lseq 'a blen) (s0: lseq 'a len)
  : Lemma (forall (i:nat{i >= lo * blen /\ i < hi * blen}).
             Seq.index (map_blocks_foldi' #'a #len blen lo hi f s0) i == Seq.index (f (i / blen)) (i % blen)
           )
  = FStar.Classical.forall_intro (foldi_update_block_pointwise_blocks_at blen lo hi f s0)

let foldi_update_block_pointwise
    (#len: uint_size) (blen:pos {blen < len})
    (lo: uint_size) (hi: uint_size {hi * blen <= len /\ lo <= hi})
    (f: (i:uint_size{i < hi}) -> lseq 'a blen) (s0: lseq 'a len)
  : Lemma (forall (i:nat{i < len}).
             (i >= lo * blen && i < hi * blen ==> Seq.index (map_blocks_foldi' #'a #len blen lo hi f s0) i == Seq.index (f (i / blen)) (i % blen))
           /\ (i >= hi * blen ==> Seq.index (map_blocks_foldi' #'a #len blen lo hi f s0) i == Seq.index s0 i)
           )
  = foldi_update_block blen lo hi f s0;
    foldi_update_block_pointwise_blocks blen lo hi f s0
#pop-options

// (forall (i:nat). i >= hi * blen /\ i < len ==> Seq.index sn i == Seq.index s0 i)


