module PPP

open FStar.Tactics
open Hacspec.Lib
open FStar.Mul
open Hacspec.Chacha20

module S = Spec.Chacha20
module H = Hacspec.Chacha20
module Seq = Lib.Sequence

module LC = Lib.LoopCombinators

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

let equiv_line (a b d: state_idx_t) (s: pos {s < 32}) (state: state_t)
  : Lemma (S.line a b d (pub_u32 s) state == H.chacha20_line a b d s state)
          [SMTPat (H.chacha20_line a b d s state)]
  = assert (S.line a b d (pub_u32 s) state `Seq.equal` H.chacha20_line a b d s state)

let equiv_constants_init
  : squash (Lib.Sequence.map secret S.chacha20_constants == chacha20_constants_init ())
  = let l = S.([c0;c1;c2;c3]) in
    assert_norm (FStar.List.Tot.length l == 4);
    assert_norm S.(let h (i:nat{i<4}) = FStar.List.Tot.index l i in h 0 = c0 /\ h 1 = c1 /\ h 2 = c2 /\ h 3 = c3);
    Lib.Sequence.eq_intro (Lib.Sequence.map #_ #_ #(4 <: size_nat) secret S.chacha20_constants) (chacha20_constants_init ())

let equiv_init (key: cha_cha_key_t) (iv: cha_cha_iv_t) (ctr: uint32)
  : Lemma (S.chacha20_init key iv (v ctr) == H.chacha20_init key iv ctr)
          [SMTPat (chacha20_init key iv ctr)]
  = ()

let equiv_quarter_round (a b c d: state_idx_t) (state: state_t)
  : Lemma (S.quarter_round a b c d state == H.chacha20_quarter_round a b c d state)
          [SMTPat (chacha20_quarter_round a b c d state)]
  = ()

let equiv_double_round (state: state_t)
  : Lemma (S.double_round state == H.chacha20_double_round state)
          [SMTPat (H.chacha20_double_round state)]
  = ()


let rec make_list (elem: 'a) (n: nat): list 'a
  = if n = 0 then [] else elem::make_list elem (n-1)

let unfold_foldi (lo: uint_size) (hi: uint_size{lo <= hi})
                 (f: (i:uint_size{i < hi}) -> 'a -> 'a)
                 (init: 'a)
  : Lemma (foldi lo hi f init == (if lo = hi then init else
                                 foldi (lo + 1) hi f (f lo init)))
  = assert_norm ((foldi lo hi f init == (if lo = hi then init else
                                 foldi (lo + 1) hi f (f lo init))))


let unfold_repeat (f: 'a -> 'a) (acc0: 'a) (i:pos)
  : Lemma (LC.repeat i f acc0 == f (LC.repeat (i - 1) f acc0))
  = LC.unfold_repeat i f acc0 (i-1) 

let eq_foldi0 (hi: uint_size) (f: (i:uint_size{i < hi}) -> 'a -> 'a) (init: 'a)
  : Lemma (foldi hi hi f init == init)
  = assert_norm (foldi hi hi f init == init)

#push-options "--max_fuel 0 --z3rlimit 15"
let equiv_rounds (st: state_t)
  : Lemma (S.rounds st == H.chacha20_rounds st)
          [SMTPat (H.chacha20_rounds st)]
  = assert (S.rounds st == chacha20_rounds st) 
        by (norm [delta_only [`%S.rounds; `%chacha20_rounds]];
            iter (fun _ -> l_to_r [`unfold_repeat]) (make_list () 10);
            l_to_r [`LC.eq_repeat0];
            norm [primops; iota; delta_only [`%usize; `%foldi]; zeta_full])
#pop-options

let equiv_core (ctr: uint32) (st0: state_t)
  : Lemma (S.chacha20_core (v ctr) st0 == chacha20_core ctr st0)
          [SMTPat (chacha20_core ctr st0)]
  = let s0 = st0 in
    let s1 = array_upd st0 (usize 12) (
                      (array_index (s0) (usize 12)) +. (ctr)) in
    let k = H.chacha20_rounds s1 in
    let ka = k `array_add (+.)` s1 in
    let kb = k `array_add (+.)` s0 in
    let kb' = array_upd kb (usize 12) (
                      (array_index (kb) (usize 12)) +. (ctr)) in
    assert (u32 (v ctr) == ctr);
    assert(S.chacha20_add_counter s0 (v ctr) == s1);
    assert(S.rounds s1 == H.chacha20_rounds s1);
    assert(S.sum_state k s0 == kb);
    assert(S.chacha20_add_counter kb (v ctr) == kb');
    assert(ka == H.chacha20_core ctr st0);
    assert(kb' == S.chacha20_core (v ctr) st0);
    assert(forall i. i <> 12 ==> s0.[i] ==  s1.[i]);
    assert(forall i. i <> 12 ==> ka.[i] ==  kb.[i]);
    assert(forall i. i <> 12 ==> ka.[i] ==  kb'.[i]);
    assert(s1.[12] ==  s0.[12] +. ctr);
    assert(ka.[12] ==  k.[12] +. s1.[12]);
    assert(kb.[12] ==  k.[12] +. s0.[12]);
    assert(kb'.[12] ==  k.[12] +. s0.[12] +. ctr);
    assert(kb'.[12] ==  k.[12] +. (s0.[12] +. ctr));
    assert(kb'.[12] ==  k.[12] +. s1.[12]);
    assert(forall i. i >= 0 /\ i < 16 ==> ka.[i] ==  kb'.[i]);
    Lib.Sequence.eq_intro ka kb'

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

let s_chacha20_update (ctx: S.state) (cipher: seq (int_t U8 SEC)): seq _ =
  Lib.Sequence.map_blocks 64 cipher
    (S.chacha20_encrypt_block ctx)
    (S.chacha20_encrypt_last ctx)

  // (f:(Seq.block (Seq.length input) blocksize -> lseq 'a blocksize -> lseq 'a blocksize))
  // (g:(Seq.last (Seq.length input) blocksize -> rem:size_nat{rem < blocksize} -> s:lseq 'a rem -> lseq 'a rem))

module IC = IndexableContent

#push-options "--ifuel 0 --z3rlimit 4"
let map_blocks_pointwise_spec'
  (len: uint_size)
  (limit: uint_size {limit <= len})
  (blocksize: size_pos)
  (blocks: Seq.block len blocksize -> lseq 'a blocksize)
  (last_block: lseq 'a (len % blocksize))
  (output: lseq 'a len)
  = let last_block_n = len / blocksize in
    forall (i:nat {i < limit}).
      let block_n = i / blocksize in
      let local_i = i % blocksize in
      assert (i < len);
      IC.division_order_lemma_ge len i blocksize;
      assert (block_n <= last_block_n);
      ( if block_n = last_block_n
        then let local_i: i:nat {i < len % blocksize} = local_i in
             Seq.index last_block local_i
        else Seq.index (blocks block_n) local_i
      ) == Seq.index output i
#pop-options

let map_blocks_pointwise_spec'0
  (len: uint_size)
  (blocksize: size_pos)
  (blocks: Seq.block len blocksize -> lseq 'a blocksize)
  (last_block: lseq 'a (len % blocksize))
  (output: lseq 'a len)
  : Lemma (map_blocks_pointwise_spec' len 0 blocksize blocks last_block output)
  = ()


let map_blocks_pointwise_spec
  (len: uint_size)
  (blocksize: size_pos)
  (blocks: Seq.block len blocksize -> lseq 'a blocksize)
  (last_block: lseq 'a (len % blocksize))
  (output: lseq 'a len)
  = map_blocks_pointwise_spec' len len blocksize blocks last_block output


#push-options "--z3rlimit 30"
let sub_rem_lemma (a b: nat) (k: pos)
  : Lemma (requires (a + 1) * k > b /\ a * k < b)
          (ensures  b - a * k == b % k)
  = assert ((a + 1) * k > b);
    let kb, rb = b / k, b % k in
    Math.Lemmas.euclidean_division_definition b k;
    Math.Lemmas.small_div rb k;
    if kb > a
    then (
      IC.division_order_lemma_gt (a + 1) (kb * k + rb) k
    ) else if kb < a then (
      IC.division_order_lemma_gt (k * kb + rb) (a * k) k;
      Math.Lemmas.cancel_mul_div  a k;
      Math.Lemmas.cancel_mul_div kb k
    )
#pop-options

#push-options "--z3rlimit 100"
let seq_get_remainder_chunk_length_lemma (inp:seq 'a) (blocksize:size_pos)
  : Lemma (Seq.length (seq_get_remainder_chunk inp blocksize) == Seq.length inp % blocksize)
  = let r = seq_get_remainder_chunk inp blocksize in
    let chunks = seq_num_chunks inp blocksize in
    let last_chunk = if chunks > 0 then chunks - 1 else 0 in
    assert (seq_chunk_len inp blocksize last_chunk == (
      if blocksize * (last_chunk + 1) > Seq.length inp
      then (if blocksize * last_chunk < Seq.length inp
            then sub_rem_lemma last_chunk (Seq.length inp) blocksize;
            Seq.length inp % blocksize)
      else blocksize
    ));
    let (_, chunk) = seq_get_chunk inp blocksize last_chunk in
    if Seq.length chunk = blocksize
    then Math.Lemmas.cancel_mul_mod (last_chunk + 1) blocksize
#pop-options

// let map_blocks_foldi'
//     (#len: uint_size) (blen:uint_size) (lo: uint_size) (hi: uint_size {hi * blen <= len /\ lo <= hi})
//     (f: (i:uint_size{i < hi}) -> lseq 'a blen) (s: lseq 'a len)
//     : lseq 'a len
//   = foldi lo hi (fun i (s: lseq 'a len) -> seq_set_exact_chunk #_ #len s blen i (f i)) s

#push-options "--z3rlimit 150"
let map_blocks_f_equiv_lemma
  (len: uint_size) (blocksize: size_pos)
  (max: uint_size {max * blocksize <= len})
  (original_s: lseq 'a len)
  (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  (i: nat{i < max})
  (updated_s: lseq 'a len {forall (j:nat{j >= i * blocksize /\ j < len}). FStar.Seq.index original_s j == FStar.Seq.index updated_s j})
  (acc: lseq 'a (i * blocksize) {forall (j:nat{j < i * blocksize}). FStar.Seq.index acc j == FStar.Seq.index updated_s j})
  // (acc: lseq 'a (i * blocksize) {acc == FStar.Seq.slice updated_s 0 (i * blocksize)})
  : Lemma (
          let slice_s = FStar.Seq.slice original_s 0 (max * blocksize) in
          forall (j: nat{j < (i+1) * blocksize}).
            FStar.Seq.index (Seq.map_blocks_f blocksize max slice_s f i acc) j
         == FStar.Seq.index (seq_set_exact_chunk #_ #len updated_s blocksize i (f i (seq_get_exact_chunk updated_s blocksize i))) j
    )
  = let slice_s = FStar.Seq.slice original_s 0 (max * blocksize) in
    Math.Lemmas.lemma_mult_le_right blocksize (i+1) max;
    let block = FStar.Seq.slice original_s (i*blocksize) ((i+1)*blocksize) in
    let r1 = FStar.Seq.append acc (f i block) in
    assert (r1 == Seq.map_blocks_f blocksize max slice_s f i acc);

    let idx_start = blocksize * i in
    let out_len = seq_chunk_len updated_s blocksize i in
    let new_block = f i (seq_get_exact_chunk updated_s blocksize i) in
    assert (Seq.equal block (seq_get_exact_chunk updated_s blocksize i));
    assert (f i block == new_block);

    let r2 = Seq.update_sub updated_s idx_start out_len new_block in
    assert (seq_chunk_len updated_s blocksize i == (
      if blocksize * (i + 1) > Seq.length updated_s
      then (if blocksize * i < Seq.length updated_s
            then sub_rem_lemma i (Seq.length updated_s) blocksize;
            Seq.length updated_s % blocksize)
      else blocksize
    ));
    let proof_r2 (k:nat{(0 <= k /\ k < idx_start) \/ (idx_start + out_len <= k /\ k < len)}): Lemma (Seq.index r2 k == Seq.index updated_s k) = () in
    assert (seq_set_exact_chunk #_ #len updated_s blocksize i new_block == r2);
    let proof (j:nat{j < (i+1) * blocksize})
      : Lemma (FStar.Seq.index r1 j == FStar.Seq.index r2 j)
      = if j >= i * blocksize
        then (
          assert (FStar.Seq.index r1 j == FStar.Seq.index (f i block) (j - i * blocksize));
          assert (FStar.Seq.index r2 j == FStar.Seq.index (f i (seq_get_exact_chunk updated_s blocksize i)) (j - i * blocksize));
          assert (FStar.Seq.index r1 j == FStar.Seq.index r2 j)
        ) else (
          assert (FStar.Seq.index r1 j == FStar.Seq.index acc j);
          assert (FStar.Seq.index r1 j == FStar.Seq.index updated_s j);
          assert (i < max /\ max * blocksize <= len);
          assert ((i+1) * blocksize <= len ==> j < len);
          assert (j < len);
          assert (j < idx_start);
          proof_r2 j;
          assert (FStar.Seq.index r2 j == FStar.Seq.index updated_s j);
          assert (FStar.Seq.index r1 j == FStar.Seq.index r2 j);
          ()
        )
    in
    FStar.Classical.forall_intro proof
#pop-options

unfold let map_blocks_foldi_fun
  (len: uint_size) (blocksize: size_pos)
  (max: uint_size {max * blocksize <= len})
  (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  (i: nat{i<max}) (s: lseq 'a len)
  = seq_set_exact_chunk #_ #len s blocksize i (f i (seq_get_exact_chunk s blocksize i))

#push-options "--z3rlimit 40"
let map_blocks_foldi_fun_preserve_above
  (len: uint_size) (blocksize: size_pos)
  (max: uint_size {max * blocksize <= len})
  (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  (i: nat{i < max}) (s: lseq 'a len)
  : Lemma (
    forall (j:nat{j >= blocksize * (i+1) /\ j < len}).
       FStar.Seq.index (map_blocks_foldi_fun len blocksize max f i s) j
    == FStar.Seq.index s j
  )
  = let r = seq_set_exact_chunk #_ #len s blocksize i (f i (seq_get_exact_chunk s blocksize i)) in
    let idx_start = blocksize * i in
    let out_len = seq_chunk_len s blocksize i in
    assert (out_len == (
      if blocksize * (i + 1) > Seq.length s
      then (if blocksize * i < Seq.length s
            then sub_rem_lemma i (Seq.length s) blocksize;
            Seq.length s % blocksize)
      else blocksize
    ));
    let r'
        = Seq.update_sub s idx_start out_len (f i (seq_get_exact_chunk s blocksize i)) in
    assert ((forall (k:nat{(0 <= k /\ k < blocksize * i) \/ (blocksize * i + out_len <= k /\ k < len)}).
       Seq.index r' k == Seq.index s k));
    if blocksize * (i + 1) > Seq.length s
    then assert (false)
    else introduce forall (j:nat{j >= blocksize * (i+1) /\ j < len}). Seq.index r' j == Seq.index s j
              with ()

unfold let map_blocks_foldi
    (#len: uint_size) (blocksize: size_pos)
    (max: uint_size {max * blocksize <= len})
    (n: uint_size {n * blocksize <= len /\ n <= max})
    (s: lseq 'a len)
    (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
    : lseq 'a len
  = foldi 0 n (map_blocks_foldi_fun len blocksize max f) s

let rec foldi_extensionality_squash
  (lo: uint_size)
  (hi: uint_size{lo <= hi})
  (f: (i:uint_size{i < hi}) -> 'a -> 'a)
  (g: (i:uint_size{i < hi}) -> 'a -> 'a {forall i x. f i x == g i x})
  (init: 'a)
  : squash (foldi lo hi f init == foldi lo hi g init)
  = if lo = hi
    then ( unfold_foldi lo hi f init;
           unfold_foldi lo hi g init
         )
    else ( unfold_left_foldi lo hi f init;
           unfold_left_foldi lo hi g init;
           foldi_extensionality_squash lo (hi - 1) f g init
         )

let foldi_extensionality
  (lo: uint_size)
  (hi: uint_size{lo <= hi})
  (f: (i:uint_size{i < hi}) -> 'a -> 'a)
  (g: (i:uint_size{i < hi}) -> 'a -> 'a {forall i x. f i x == g i x})
  (init: 'a)
  : Lemma (foldi lo hi f init == foldi lo hi g init)
  = foldi_extensionality_squash lo hi f g init

#push-options "--ifuel 0 --fuel 0 --z3rlimit 15 --split_queries"
let map_blocks_foldi_fun_simplify
  (#len: uint_size) (blocksize: size_pos)
  (max: uint_size {max * blocksize <= len})
  (n: uint_size {n * blocksize <= len /\ n <= max})
  (s: lseq 'a len)
  (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  : squash (
       foldi 0 n (map_blocks_foldi_fun len blocksize max f) s
    == foldi 0 n (fun (i: nat{i<max}) (s: lseq 'a len) -> seq_set_exact_chunk #'a #len s blocksize i (f i (seq_get_exact_chunk s blocksize i))) s
  ) = foldi_extensionality_squash 0 n
                                  (map_blocks_foldi_fun len blocksize max f)
                                  (fun (i: nat{i<max}) (s: lseq 'a len) -> seq_set_exact_chunk #'a #len s blocksize i (f i (seq_get_exact_chunk s blocksize i)))
                                  s
#pop-options

#push-options "--z3rlimit 20 --split_queries"
let map_blocks_foldi_simplify
  (#len: uint_size) (blocksize: size_pos)
  (max: uint_size {max * blocksize <= len})
  (n: uint_size {n * blocksize <= len /\ n <= max})
  (s: lseq 'a len)
  (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  : Lemma (
       map_blocks_foldi blocksize max n s f
    == foldi 0 n (fun (i: nat{i<max}) (s: lseq 'a len) -> seq_set_exact_chunk #'a #len s blocksize i (f i (seq_get_exact_chunk s blocksize i))) s
  ) = map_blocks_foldi_fun_simplify blocksize max n s f
#pop-options

#push-options "--z3rlimit 40"
let rec map_blocks_foldi_preserves
    (len: uint_size) (blocksize: size_pos)
    (max: uint_size {max * blocksize <= len})
    (n: uint_size {n * blocksize <= len /\ n <= max})
    (s0: lseq 'a len)
    (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  : Lemma (forall (i:nat{i >= blocksize * n /\ i < len}). FStar.Seq.index s0 i == FStar.Seq.index (map_blocks_foldi blocksize max n s0 f) i)
   = if n = 0
     then unfold_foldi 0 0 (map_blocks_foldi_fun len blocksize max f) s0
     else (
       unfold_left_foldi 0 n (map_blocks_foldi_fun len blocksize max f) s0;
       assert (
            map_blocks_foldi_fun len blocksize max f (n - 1) (map_blocks_foldi blocksize max (n - 1) s0 f)
         == map_blocks_foldi blocksize max n s0 f
       );
       map_blocks_foldi_preserves len blocksize max (n - 1) s0 f;
       assert (forall (i:nat{i >= blocksize * (n-1) /\ i < len}). FStar.Seq.index s0 i == FStar.Seq.index (map_blocks_foldi blocksize max (n-1) s0 f) i);
       introduce forall (i: nat{i < max}) (s: lseq 'a len). forall (j:nat{j >= blocksize * (i+1) /\ j < len}).
                          FStar.Seq.index (map_blocks_foldi_fun len blocksize max f i s) j
                       == FStar.Seq.index s j
            with map_blocks_foldi_fun_preserve_above len blocksize max f i s;
       ()
     )
#pop-options

#push-options "--print_implicits"
unfold let direct_statement
    (len: uint_size) (blocksize: size_pos)
    (max: uint_size {max * blocksize <= len})
    (n: uint_size {n * blocksize <= len /\ n <= max})
    (s: lseq 'a len)
    (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  = let slice_s = FStar.Seq.slice s 0 (max * blocksize) in
    let r1: Seq.map_blocks_a 'a blocksize max n = LC.repeat_gen n (Seq.map_blocks_a 'a blocksize max) (Seq.map_blocks_f blocksize max slice_s f) FStar.Seq.empty in
    let r2 = map_blocks_foldi blocksize max n s f in
    (forall (i:nat{i < blocksize * n}). FStar.Seq.index r1 i == FStar.Seq.index r2 i)

// #push-options "--fuel 0 --ifuel 0 --z3rlimit 150 --split_queries"
#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let rec direct
  (len: uint_size) (blocksize: size_pos)
  (max: uint_size {max * blocksize <= len})
  (n: uint_size {n * blocksize <= len /\ n <= max})
  (s: lseq 'a len)
  (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  : Lemma (ensures direct_statement len blocksize max n s f) (decreases n)
  = if n <> 0 then begin
      let n': uint_size = n - 1 in
      let slice_s = FStar.Seq.slice s 0 (max * blocksize) in
      
      let r1' = LC.repeat_gen (n-1) (Seq.map_blocks_a 'a blocksize max) (Seq.map_blocks_f blocksize max slice_s f) FStar.Seq.empty in
      let r2' = map_blocks_foldi blocksize max (n - 1) s f in
      let all1 = Seq.map_blocks_f blocksize max slice_s f (n-1) r1' in
      let all2 = seq_set_exact_chunk #_ #len r2' blocksize (n-1) (f (n-1) (seq_get_exact_chunk r2' blocksize (n-1))) in
      let _: squash (forall (i:nat{i < blocksize * (n - 1)}). FStar.Seq.index r1' i == FStar.Seq.index r2' i)
        = direct len blocksize max (n - 1) s f;
          assert (direct_statement len blocksize max (n - 1) s f);
          assert ((forall (i:nat{i < blocksize * (n - 1)}). FStar.Seq.index r1' i == FStar.Seq.index r2' i))
      in
      map_blocks_foldi_preserves len blocksize max (n-1) s f;
      map_blocks_f_equiv_lemma len blocksize max s f (n-1) r2' r1';
      assert (forall (j: nat{j < n * blocksize}). FStar.Seq.index all1 j == FStar.Seq.index all2 j);
      unfold_left_foldi 0 n (map_blocks_foldi_fun len blocksize max f) s;
      LC.unfold_repeat_gen n (Seq.map_blocks_a 'a blocksize max) (Seq.map_blocks_f blocksize max slice_s f) FStar.Seq.empty (n - 1)
    end
#pop-options

#push-options "--z3rlimit 160"
let s_chacha20_update' (ctx: S.state) (cipher: seq (int_t U8 SEC)): (r:seq _{r==s_chacha20_update ctx cipher}) =
  Seq.lemma_map_blocks 64 cipher (S.chacha20_encrypt_block ctx) (S.chacha20_encrypt_last ctx);
  let len = Seq.length cipher in
  let nb  = len / 64 in
  let rem = len % 64 in
  let blocks = Seq.slice #_ #(seq_len cipher) cipher 0 (nb * 64) in
  let last   = Seq.slice #_ #(seq_len cipher) cipher (nb * 64) len in
  Math.Lemmas.cancel_mul_div nb 64;
  let bs: seq _ = Seq.map_blocks_multi 64 nb nb blocks (S.chacha20_encrypt_block ctx) in

  let aux (i: nat {i < nb * 64}): Lemma (
      Seq.div_mul_lt 64 i nb;
      let j = i / 64 in
      let block: lseq (int_t U8 SEC) 64 = Seq.slice blocks (j * 64) ((j + 1) * 64) in
      Seq.index #_ #(nb * 64) bs i == Seq.index (S.chacha20_encrypt_block ctx j block) (i % 64)
  ) =
      Seq.div_mul_lt 64 i nb;
      Seq.index_map_blocks_multi 64 nb nb blocks (S.chacha20_encrypt_block ctx) i
  in

  FStar.Seq.append_empty_r bs;
  let r = FStar.Seq.append bs (S.chacha20_encrypt_last ctx nb rem last) in
  assert (r==s_chacha20_update ctx cipher);
  // Classical.forall_intro aux;
  r
#pop-options


// let map_blocks_foldi_simplify
//   (#len: uint_size) (blocksize: size_pos)
//   (max: uint_size {max * blocksize <= len})
//   (n: uint_size {n * blocksize <= len /\ n <= max})
//   (s: lseq 'a len)
//   (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
//   : Lemma (
//        map_blocks_foldi blocksize max n s f
//     == foldi 0 n (fun (i: nat{i<max}) (s: lseq 'a len) -> seq_set_exact_chunk #'a #len s blocksize i (f i (seq_get_exact_chunk s blocksize i))) s
//   ) = map_blocks_foldi_fun_simplify blocksize max n s f


let chacha20_update0 (st0 : state_t) (cipher : byte_seq): lseq uint8 (FStar.Seq.length cipher) =
  let blocks_out: seq uint8 = seq_new_ (secret (pub_u8 0x0)) (seq_len cipher) in
  let n_blocks: uint_size = seq_num_exact_chunks cipher 64 in
  
  let f (i: nat {i<n_blocks}): block_t = 
    let msg_block: seq uint8 = seq_get_exact_chunk cipher 64 i in
    chacha20_encrypt_block st0 (secret (pub_u32 i)) (array_from_seq 64 msg_block)
  in
  foldi 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq _ (seq_len #uint8 cipher)) -> seq_set_exact_chunk s 64 i (f i)) blocks_out

let chacha20_update0' (st0 : state_t) (cipher : byte_seq): lseq uint8 (FStar.Seq.length cipher) =
  let blocks_out: seq uint8 = seq_new_ (secret (pub_u8 0x0)) (seq_len cipher) in
  let n_blocks: uint_size = seq_num_exact_chunks cipher 64 in

    
  let f0 (i: nat {i<n_blocks}): block_t = 
    let msg_block: seq uint8 = seq_get_exact_chunk cipher 64 i in
    chacha20_encrypt_block st0 (secret (pub_u32 i)) (array_from_seq 64 msg_block)
  in
  let r0 = foldi 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq uint8 (seq_len #uint8 cipher)) -> seq_set_exact_chunk #uint8 #(seq_len #uint8 cipher) s 64 i (f0 i)) blocks_out in
  
  // let r1 = foldi 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq uint8 (FStar.Seq.length #uint8 cipher)) -> seq_set_exact_chunk s 64 i (f0 i)) blocks_out in
  // let proof
  //   : squash (
  //      foldi 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq uint8 (seq_len #uint8 cipher)) -> seq_set_exact_chunk #uint8 #(seq_len #uint8 cipher) s 64 i (f0 i)) blocks_out
  //   == foldi 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq uint8 (FStar.Seq.length #uint8 cipher)) -> seq_set_exact_chunk s 64 i (f0 i)) blocks_out
  // ) =
  //   foldi_extensionality 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq uint8 (seq_len #uint8 cipher)) -> seq_set_exact_chunk #uint8 #(seq_len #uint8 cipher) s 64 i (f0 i))
  //                                 (fun (i: uint_size{i<n_blocks}) (s: lseq uint8 (FStar.Seq.length #uint8 cipher)) -> seq_set_exact_chunk s 64 i (f0 i))
  //                                 blocks_out in
// assert (foldi 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq uint8 (seq_len #uint8 cipher)) -> seq_set_exact_chunk #uint8 #(seq_len #uint8 cipher) s 64 i (f0 i)) blocks_out
//     == foldi 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq uint8 (FStar.Seq.length #uint8 cipher)) -> seq_set_exact_chunk s 64 i (f0 i)) blocks_out);
//   assert (r0 == foldi 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq uint8 (seq_len #uint8 cipher)) -> seq_set_exact_chunk #uint8 #(seq_len #uint8 cipher) s 64 i (f0 i)) blocks_out);
//   assert (r1 == foldi 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq uint8 (FStar.Seq.length #uint8 cipher)) -> seq_set_exact_chunk s 64 i (f0 i)) blocks_out);

  let f2 (i: nat {i<n_blocks}) (msg_block: lseq uint8 64): block_t = 
    chacha20_encrypt_block st0 (secret (pub_u32 i)) (array_from_seq 64 msg_block)
  in
  let r2 = map_blocks_foldi #uint8 #(seq_len cipher) 64 n_blocks n_blocks blocks_out f2 in

  assert (r2 == r0) by (
    norm [delta_only [`%map_blocks_foldi;`%map_blocks_foldi_fun;`%uint8]];
    // compute ()
    fail "x"
  );

  r0

// let chacha20_update0_equiv (st0 : state_t) (cipher : byte_seq)
//   : Lemma (chacha20_update0 st0 cipher == chacha20_update0' st0 cipher)
//   = assert (chacha20_update0 st0 cipher == chacha20_update0' st0 cipher) by

#push-options "--z3rlimit 160"
let chacha20_update_ (st0 : state_t) (cipher : byte_seq) 
  : r:byte_seq{r == chacha20_update st0 cipher} =
  let blocks_out: seq uint8 = seq_new_ (secret (pub_u8 0x0)) (seq_len cipher) in
  let n_blocks: uint_size = seq_num_exact_chunks cipher 64 in
  
  let f (i: nat {i<n_blocks}): block_t = 
    let msg_block: seq uint8 = seq_get_exact_chunk cipher 64 i in
    chacha20_encrypt_block st0 (secret (pub_u32 i)) (array_from_seq 64 msg_block)
  in
  let blocks_out = foldi 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq uint8 (seq_len #uint8 cipher)) -> seq_set_exact_chunk #uint8 #(seq_len #uint8 cipher) s 64 i (f i)) blocks_out in
  // let blocks_out' = foldi 0 n_blocks (fun (i: uint_size{i<n_blocks}) (s: lseq _ (Seq.length cipher)) -> seq_set_exact_chunk s 64 i (f i)) blocks_out in
  
  let last_block: seq uint8 = seq_get_remainder_chunk cipher 64 in
  if seq_len last_block <> 0 then
    let b : seq uint8 = chacha20_encrypt_last st0 (secret (pub_u32 n_blocks)) last_block in
    seq_set_chunk (blocks_out <: lseq _ (seq_len cipher)) 64 n_blocks b
  else blocks_out

let chacha20_update_ (st0 : state_t) (cipher : byte_seq) =
  // : byte_seq =
  let blocks_out: seq uint8 = seq_new_ (secret (pub_u8 0x0)) (seq_len cipher) in
  let n_blocks: uint_size = seq_num_exact_chunks cipher 64 in
  let f (i: nat {i<n_blocks}) (msg_block: lseq uint8 64): block_t = 
    chacha20_encrypt_block st0 (secret (pub_u32 i)) (array_from_seq 64 msg_block)
  in
  let blocks_out = map_blocks_foldi 64 n_blocks n_blocks blocks_out f in
  let last_block: seq uint8 = seq_get_remainder_chunk cipher 64 in
  if seq_len last_block <> 0 then
    let b : seq uint8 = chacha20_encrypt_last st0 (secret (pub_u32 n_blocks)) last_block in
    seq_set_chunk (blocks_out <: lseq _ (seq_len cipher)) 64 n_blocks b
  else blocks_out

