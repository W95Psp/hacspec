(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Bls12_381.

Require Import Hacspec.Lib.

Require Import Hacspec.Sha256.

Definition fp_hash_canvas := nseq (int8) (64).
Definition fp_hash :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition arr_fp := nseq (uint64) (usize 6).

Definition b_in_bytes : uint_size :=
  usize 32.

Definition s_in_bytes : uint_size :=
  usize 64.

Definition l : uint_size :=
  usize 64.

Definition p_1_2 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 936899308823769933);
        secret (@repr WORDSIZE64 2706051889235351147);
        secret (@repr WORDSIZE64 12843041017062132063);
        secret (@repr WORDSIZE64 12941209323636816658);
        secret (@repr WORDSIZE64 1105070755758604287);
        secret (@repr WORDSIZE64 15924587544893707605)
      ] in  l).

Definition p_1_4 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 468449654411884966);
        secret (@repr WORDSIZE64 10576397981472451381);
        secret (@repr WORDSIZE64 15644892545385841839);
        secret (@repr WORDSIZE64 15693976698673184137);
        secret (@repr WORDSIZE64 552535377879302143);
        secret (@repr WORDSIZE64 17185665809301629611)
      ] in  l).

Definition p_3_4 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 468449654411884966);
        secret (@repr WORDSIZE64 10576397981472451381);
        secret (@repr WORDSIZE64 15644892545385841839);
        secret (@repr WORDSIZE64 15693976698673184137);
        secret (@repr WORDSIZE64 552535377879302143);
        secret (@repr WORDSIZE64 17185665809301629610)
      ] in  l).

Definition expand_message_xmd
  (msg_0 : byte_seq)
  (dst_1 : byte_seq)
  (len_in_bytes_2 : uint_size)
  : byte_seq :=
  let ell_3 : uint_size :=
    (((len_in_bytes_2) + (b_in_bytes)) - (usize 1)) / (b_in_bytes) in 
  let dst_prime_4 : seq uint8 :=
    seq_push (dst_1) (uint8_from_usize (seq_len (dst_1))) in 
  let z_pad_5 : seq uint8 :=
    seq_new_ (default) (s_in_bytes) in 
  let l_i_b_str_6 : seq uint8 :=
    seq_new_ (default) (usize 2) in 
  let l_i_b_str_6 :=
    seq_upd l_i_b_str_6 (usize 0) (uint8_from_usize ((len_in_bytes_2) / (
          usize 256))) in 
  let l_i_b_str_6 :=
    seq_upd l_i_b_str_6 (usize 1) (uint8_from_usize (len_in_bytes_2)) in 
  let msg_prime_7 : seq uint8 :=
    seq_concat (seq_concat (seq_concat (seq_concat (z_pad_5) (msg_0)) (
          l_i_b_str_6)) (seq_new_ (default) (usize 1))) (dst_prime_4) in 
  let b_0_8 : seq uint8 :=
    seq_from_seq (hash (msg_prime_7)) in 
  let b_i_9 : seq uint8 :=
    seq_from_seq (hash (seq_concat (seq_push (b_0_8) (secret (
              @repr WORDSIZE8 1))) (dst_prime_4))) in 
  let uniform_bytes_10 : seq uint8 :=
    seq_from_seq (b_i_9) in 
  let '(b_i_9, uniform_bytes_10) :=
    foldi (usize 2) ((ell_3) + (usize 1)) (fun i_11 '(b_i_9, uniform_bytes_10
      ) =>
      let t_12 : seq uint8 :=
        seq_from_seq (b_0_8) in 
      let b_i_9 :=
        seq_from_seq (hash (seq_concat (seq_push ((t_12) seq_xor (b_i_9)) (
                uint8_from_usize (i_11))) (dst_prime_4))) in 
      let uniform_bytes_10 :=
        seq_concat (uniform_bytes_10) (b_i_9) in 
      (b_i_9, uniform_bytes_10))
    (b_i_9, uniform_bytes_10) in 
  seq_truncate (uniform_bytes_10) (len_in_bytes_2).

Definition fp_hash_to_field
  (msg_13 : byte_seq)
  (dst_14 : byte_seq)
  (count_15 : uint_size)
  : seq fp :=
  let len_in_bytes_16 : uint_size :=
    (count_15) * (l) in 
  let uniform_bytes_17 : seq uint8 :=
    expand_message_xmd (msg_13) (dst_14) (len_in_bytes_16) in 
  let output_18 : seq fp :=
    seq_new_ (default) (count_15) in 
  let output_18 :=
    foldi (usize 0) (count_15) (fun i_19 output_18 =>
      let elm_offset_20 : uint_size :=
        (l) * (i_19) in 
      let tv_21 : seq uint8 :=
        seq_slice (uniform_bytes_17) (elm_offset_20) (l) in 
      let u_i_22 : fp :=
        nat_mod_from_byte_seq_be (seq_slice (tv_21) (usize 16) (usize 48)) in 
      let output_18 :=
        seq_upd output_18 (i_19) (u_i_22) in 
      (output_18))
    output_18 in 
  output_18.

Definition fp_sgn0 (x_23 : fp) : bool :=
  ((x_23) rem (nat_mod_two )) =.? (nat_mod_one ).

Definition fp_is_square (x_24 : fp) : bool :=
  let c1_25 : fp :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2)) in 
  let tv_26 : fp :=
    nat_mod_pow_self (x_24) (c1_25) in 
  ((tv_26) =.? (nat_mod_zero )) || ((tv_26) =.? (nat_mod_one )).

Definition fp_sqrt (x_27 : fp) : fp :=
  let c1_28 : fp :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_4)) in 
  nat_mod_pow_self (x_27) (c1_28).

Definition g1_curve_func (x_29 : fp) : fp :=
  (((x_29) *% (x_29)) *% (x_29)) +% (nat_mod_from_literal (_) (
      @repr WORDSIZE128 4)).

Definition g1_map_to_curve_svdw (u_30 : fp) : g1 :=
  let z_31 : fp :=
    (nat_mod_zero ) -% (nat_mod_from_literal (_) (@repr WORDSIZE128 3)) in 
  let gz_32 : fp :=
    g1_curve_func (z_31) in 
  let tv1_33 : fp :=
    ((u_30) *% (u_30)) *% (gz_32) in 
  let tv2_34 : fp :=
    (nat_mod_one ) +% (tv1_33) in 
  let tv1_35 : fp :=
    (nat_mod_one ) -% (tv1_33) in 
  let tv3_36 : fp :=
    nat_mod_inv ((tv1_35) *% (tv2_34)) in 
  let tv4_37 : fp :=
    fp_sqrt (((nat_mod_zero ) -% (gz_32)) *% (((nat_mod_from_literal (_) (
              @repr WORDSIZE128 3)) *% (z_31)) *% (z_31))) in 
  let '(tv4_37) :=
    if fp_sgn0 (tv4_37):bool then (let tv4_37 :=
        (nat_mod_zero ) -% (tv4_37) in 
      (tv4_37)) else ((tv4_37)) in 
  let tv5_38 : fp :=
    (((u_30) *% (tv1_35)) *% (tv3_36)) *% (tv4_37) in 
  let tv6_39 : fp :=
    (((nat_mod_zero ) -% (nat_mod_from_literal (_) (@repr WORDSIZE128 4))) *% (
        gz_32)) *% (nat_mod_inv (((nat_mod_from_literal (_) (
              @repr WORDSIZE128 3)) *% (z_31)) *% (z_31))) in 
  let x1_40 : fp :=
    (((nat_mod_zero ) -% (z_31)) *% (nat_mod_inv (nat_mod_two ))) -% (
      tv5_38) in 
  let x2_41 : fp :=
    (((nat_mod_zero ) -% (z_31)) *% (nat_mod_inv (nat_mod_two ))) +% (
      tv5_38) in 
  let x3_42 : fp :=
    (z_31) +% (((tv6_39) *% (((tv2_34) *% (tv2_34)) *% (tv3_36))) *% (((
            tv2_34) *% (tv2_34)) *% (tv3_36))) in 
  let x_43 : fp :=
    (if (fp_is_square (g1_curve_func (x1_40))):bool then (x1_40) else ((if (
            fp_is_square (g1_curve_func (x2_41))):bool then (x2_41) else (
            x3_42)))) in 
  let y_44 : fp :=
    fp_sqrt (g1_curve_func (x_43)) in 
  let '(y_44) :=
    if (fp_sgn0 (u_30)) !=.? (fp_sgn0 (y_44)):bool then (let y_44 :=
        (nat_mod_zero ) -% (y_44) in 
      (y_44)) else ((y_44)) in 
  (x_43, y_44, false).

Definition g1_clear_cofactor (x_45 : g1) : g1 :=
  let h_eff_46 : scalar :=
    nat_mod_from_literal (_) (@repr WORDSIZE128 15132376222941642753) in 
  g1mul (h_eff_46) (x_45).

Definition g1_hash_to_curve_svdw (msg_47 : byte_seq) (dst_48 : byte_seq) : g1 :=
  let u_49 : seq fp :=
    fp_hash_to_field (msg_47) (dst_48) (usize 2) in 
  let q0_50 : (fp × fp × bool) :=
    g1_map_to_curve_svdw (seq_index (u_49) (usize 0)) in 
  let q1_51 : (fp × fp × bool) :=
    g1_map_to_curve_svdw (seq_index (u_49) (usize 1)) in 
  let r_52 : (fp × fp × bool) :=
    g1add (q0_50) (q1_51) in 
  let p_53 : (fp × fp × bool) :=
    g1_clear_cofactor (r_52) in 
  p_53.

Definition g1_encode_to_curve_svdw
  (msg_54 : byte_seq)
  (dst_55 : byte_seq)
  : g1 :=
  let u_56 : seq fp :=
    fp_hash_to_field (msg_54) (dst_55) (usize 1) in 
  let q_57 : (fp × fp × bool) :=
    g1_map_to_curve_svdw (seq_index (u_56) (usize 0)) in 
  let p_58 : (fp × fp × bool) :=
    g1_clear_cofactor (q_57) in 
  p_58.

Definition fp2_hash_to_field
  (msg_59 : byte_seq)
  (dst_60 : byte_seq)
  (count_61 : uint_size)
  : seq fp2 :=
  let len_in_bytes_62 : uint_size :=
    ((count_61) * (usize 2)) * (l) in 
  let uniform_bytes_63 : seq uint8 :=
    expand_message_xmd (msg_59) (dst_60) (len_in_bytes_62) in 
  let output_64 : seq (fp × fp) :=
    seq_new_ (default) (count_61) in 
  let output_64 :=
    foldi (usize 0) (count_61) (fun i_65 output_64 =>
      let elm_offset_66 : uint_size :=
        ((l) * (i_65)) * (usize 2) in 
      let tv_67 : seq uint8 :=
        seq_slice (uniform_bytes_63) (elm_offset_66) (l) in 
      let e_1_68 : fp :=
        nat_mod_from_byte_seq_be (seq_slice (tv_67) (usize 16) (usize 48)) in 
      let elm_offset_69 : uint_size :=
        (l) * ((usize 1) + ((i_65) * (usize 2))) in 
      let tv_70 : seq uint8 :=
        seq_slice (uniform_bytes_63) (elm_offset_69) (l) in 
      let e_2_71 : fp :=
        nat_mod_from_byte_seq_be (seq_slice (tv_70) (usize 16) (usize 48)) in 
      let output_64 :=
        seq_upd output_64 (i_65) ((e_1_68, e_2_71)) in 
      (output_64))
    output_64 in 
  output_64.

Definition fp2_sgn0 (x_72 : fp2) : bool :=
  let '(x0_73, x1_74) :=
    x_72 in 
  let sign_0_75 : bool :=
    fp_sgn0 (x0_73) in 
  let zero_0_76 : bool :=
    (x0_73) =.? (nat_mod_zero ) in 
  let sign_1_77 : bool :=
    fp_sgn0 (x1_74) in 
  (sign_0_75) || ((zero_0_76) && (sign_1_77)).

Definition fp2_is_square (x_78 : fp2) : bool :=
  let c1_79 : fp :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2)) in 
  let '(x1_80, x2_81) :=
    x_78 in 
  let tv1_82 : fp :=
    (x1_80) *% (x1_80) in 
  let tv2_83 : fp :=
    (x2_81) *% (x2_81) in 
  let tv1_84 : fp :=
    (tv1_82) +% (tv2_83) in 
  let tv1_85 : fp :=
    nat_mod_pow_self (tv1_84) (c1_79) in 
  let neg1_86 : fp :=
    (nat_mod_zero ) -% (nat_mod_one ) in 
  (tv1_85) !=.? (neg1_86).

Definition fp2exp (n_87 : fp2) (k_88 : fp) : fp2 :=
  let c_89 : (fp × fp) :=
    fp2fromfp (nat_mod_one ) in 
  let c_89 :=
    foldi (usize 0) (usize 381) (fun i_90 c_89 =>
      let c_89 :=
        fp2mul (c_89) (c_89) in 
      let '(c_89) :=
        if nat_mod_bit (k_88) ((usize 380) - (i_90)):bool then (let c_89 :=
            fp2mul (c_89) (n_87) in 
          (c_89)) else ((c_89)) in 
      (c_89))
    c_89 in 
  c_89.

Definition fp2_sqrt (a_91 : fp2) : fp2 :=
  let c1_92 : fp :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_3_4)) in 
  let c2_93 : fp :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2)) in 
  let a1_94 : (fp × fp) :=
    fp2exp (a_91) (c1_92) in 
  let alpha_95 : (fp × fp) :=
    fp2mul (a1_94) (fp2mul (a1_94) (a_91)) in 
  let x0_96 : (fp × fp) :=
    fp2mul (a1_94) (a_91) in 
  let neg1_97 : (fp × fp) :=
    ((nat_mod_zero ) -% (nat_mod_one ), nat_mod_zero ) in 
  let b_98 : (fp × fp) :=
    fp2exp (fp2add (fp2fromfp (nat_mod_one )) (alpha_95)) (c2_93) in 
  (if ((alpha_95) =.? (neg1_97)):bool then (fp2mul ((nat_mod_zero , nat_mod_one 
        )) (x0_96)) else (fp2mul (b_98) (x0_96))).

Definition g2_curve_func (x_99 : fp2) : fp2 :=
  fp2add (fp2mul (x_99) (fp2mul (x_99) (x_99))) ((
      nat_mod_from_literal (_) (@repr WORDSIZE128 4),
      nat_mod_from_literal (_) (@repr WORDSIZE128 4)
    )).

Definition g2_map_to_curve_svdw (u_100 : fp2) : g2 :=
  let z_101 : (fp × fp) :=
    fp2neg (fp2fromfp (nat_mod_one )) in 
  let gz_102 : (fp × fp) :=
    g2_curve_func (z_101) in 
  let tv1_103 : (fp × fp) :=
    fp2mul (fp2mul (u_100) (u_100)) (gz_102) in 
  let tv2_104 : (fp × fp) :=
    fp2add (fp2fromfp (nat_mod_one )) (tv1_103) in 
  let tv1_105 : (fp × fp) :=
    fp2sub (fp2fromfp (nat_mod_one )) (tv1_103) in 
  let tv3_106 : (fp × fp) :=
    fp2inv (fp2mul (tv1_105) (tv2_104)) in 
  let tv4_107 : (fp × fp) :=
    fp2_sqrt (fp2mul (fp2neg (gz_102)) (fp2mul (fp2fromfp (
            nat_mod_from_literal (_) (@repr WORDSIZE128 3))) (fp2mul (z_101) (
            z_101)))) in 
  let '(tv4_107) :=
    if fp2_sgn0 (tv4_107):bool then (let tv4_107 :=
        fp2neg (tv4_107) in 
      (tv4_107)) else ((tv4_107)) in 
  let tv5_108 : (fp × fp) :=
    fp2mul (fp2mul (fp2mul (u_100) (tv1_105)) (tv3_106)) (tv4_107) in 
  let tv6_109 : (fp × fp) :=
    fp2mul (fp2mul (fp2neg (fp2fromfp (nat_mod_from_literal (_) (
              @repr WORDSIZE128 4)))) (gz_102)) (fp2inv (fp2mul (fp2fromfp (
            nat_mod_from_literal (_) (@repr WORDSIZE128 3))) (fp2mul (z_101) (
            z_101)))) in 
  let x1_110 : (fp × fp) :=
    fp2sub (fp2mul (fp2neg (z_101)) (fp2inv (fp2fromfp (nat_mod_two )))) (
      tv5_108) in 
  let x2_111 : (fp × fp) :=
    fp2add (fp2mul (fp2neg (z_101)) (fp2inv (fp2fromfp (nat_mod_two )))) (
      tv5_108) in 
  let tv7_112 : (fp × fp) :=
    fp2mul (fp2mul (tv2_104) (tv2_104)) (tv3_106) in 
  let x3_113 : (fp × fp) :=
    fp2add (z_101) (fp2mul (tv6_109) (fp2mul (tv7_112) (tv7_112))) in 
  let x_114 : (fp × fp) :=
    (if (fp2_is_square (g2_curve_func (x1_110))):bool then (x1_110) else ((if (
            fp2_is_square (g2_curve_func (x2_111))):bool then (x2_111) else (
            x3_113)))) in 
  let y_115 : (fp × fp) :=
    fp2_sqrt (g2_curve_func (x_114)) in 
  let '(y_115) :=
    if (fp2_sgn0 (u_100)) !=.? (fp2_sgn0 (y_115)):bool then (let y_115 :=
        fp2neg (y_115) in 
      (y_115)) else ((y_115)) in 
  (x_114, y_115, false).

Definition psi (p_116 : g2) : g2 :=
  let c1_117 : (fp × fp) :=
    fp2inv (fp2exp ((nat_mod_one , nat_mod_one )) (((nat_mod_zero ) -% (
            nat_mod_one )) *% (nat_mod_inv (nat_mod_from_literal (_) (
              @repr WORDSIZE128 3))))) in 
  let c2_118 : (fp × fp) :=
    fp2inv (fp2exp ((nat_mod_one , nat_mod_one )) (((nat_mod_zero ) -% (
            nat_mod_one )) *% (nat_mod_inv (nat_mod_two )))) in 
  let '(x_119, y_120, inf_121) :=
    p_116 in 
  let qx_122 : (fp × fp) :=
    fp2mul (c1_117) (fp2conjugate (x_119)) in 
  let qy_123 : (fp × fp) :=
    fp2mul (c2_118) (fp2conjugate (y_120)) in 
  (qx_122, qy_123, inf_121).

Definition g2_clear_cofactor (p_124 : g2) : g2 :=
  let c1_125 : scalar :=
    nat_mod_from_literal (_) (@repr WORDSIZE128 15132376222941642752) in 
  let t1_126 : ((fp × fp) × (fp × fp) × bool) :=
    g2mul (c1_125) (p_124) in 
  let t1_127 : ((fp × fp) × (fp × fp) × bool) :=
    g2neg (t1_126) in 
  let t2_128 : ((fp × fp) × (fp × fp) × bool) :=
    psi (p_124) in 
  let t3_129 : ((fp × fp) × (fp × fp) × bool) :=
    g2double (p_124) in 
  let t3_130 : ((fp × fp) × (fp × fp) × bool) :=
    psi (psi (t3_129)) in 
  let t3_131 : ((fp × fp) × (fp × fp) × bool) :=
    g2add (t3_130) (g2neg (t2_128)) in 
  let t2_132 : ((fp × fp) × (fp × fp) × bool) :=
    g2add (t1_127) (t2_128) in 
  let t2_133 : ((fp × fp) × (fp × fp) × bool) :=
    g2mul (c1_125) (t2_132) in 
  let t2_134 : ((fp × fp) × (fp × fp) × bool) :=
    g2neg (t2_133) in 
  let t3_135 : ((fp × fp) × (fp × fp) × bool) :=
    g2add (t3_131) (t2_134) in 
  let t3_136 : ((fp × fp) × (fp × fp) × bool) :=
    g2add (t3_135) (g2neg (t1_127)) in 
  let q_137 : ((fp × fp) × (fp × fp) × bool) :=
    g2add (t3_136) (g2neg (p_124)) in 
  q_137.

Definition g2_hash_to_curve_svdw
  (msg_138 : byte_seq)
  (dst_139 : byte_seq)
  : g2 :=
  let u_140 : seq fp2 :=
    fp2_hash_to_field (msg_138) (dst_139) (usize 2) in 
  let q0_141 : ((fp × fp) × (fp × fp) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_140) (usize 0)) in 
  let q1_142 : ((fp × fp) × (fp × fp) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_140) (usize 1)) in 
  let r_143 : ((fp × fp) × (fp × fp) × bool) :=
    g2add (q0_141) (q1_142) in 
  let p_144 : ((fp × fp) × (fp × fp) × bool) :=
    g2_clear_cofactor (r_143) in 
  p_144.

Definition g2_encode_to_curve_svdw
  (msg_145 : byte_seq)
  (dst_146 : byte_seq)
  : g2 :=
  let u_147 : seq fp2 :=
    fp2_hash_to_field (msg_145) (dst_146) (usize 1) in 
  let q_148 : ((fp × fp) × (fp × fp) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_147) (usize 0)) in 
  let p_149 : ((fp × fp) × (fp × fp) × bool) :=
    g2_clear_cofactor (q_148) in 
  p_149.

Definition g1_iso_a : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 5707120929990979);
        secret (@repr WORDSIZE64 4425131892511951234);
        secret (@repr WORDSIZE64 12748169179688756904);
        secret (@repr WORDSIZE64 15629909748249821612);
        secret (@repr WORDSIZE64 10994253769421683071);
        secret (@repr WORDSIZE64 6698022561392380957)
      ] in  l).

Definition g1_iso_b : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1360808972976160816);
        secret (@repr WORDSIZE64 111203405409480251);
        secret (@repr WORDSIZE64 2312248699302920304);
        secret (@repr WORDSIZE64 11581500465278574325);
        secret (@repr WORDSIZE64 6495071758858381989);
        secret (@repr WORDSIZE64 15117538217124375520)
      ] in  l).

Definition g1_xnum_k_0 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1270119733718627136);
        secret (@repr WORDSIZE64 13261148298159854981);
        secret (@repr WORDSIZE64 7723742117508874335);
        secret (@repr WORDSIZE64 17465657917644792520);
        secret (@repr WORDSIZE64 6201670911048166766);
        secret (@repr WORDSIZE64 12586459670690286007)
      ] in  l).

Definition g1_xnum_k_1 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1668951808976071471);
        secret (@repr WORDSIZE64 398773841247578140);
        secret (@repr WORDSIZE64 8941869963990959127);
        secret (@repr WORDSIZE64 17682789360670468203);
        secret (@repr WORDSIZE64 5204176168283587414);
        secret (@repr WORDSIZE64 16732261237459223483)
      ] in  l).

Definition g1_xnum_k_2 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 960393023080265964);
        secret (@repr WORDSIZE64 2094253841180170779);
        secret (@repr WORDSIZE64 14844748873776858085);
        secret (@repr WORDSIZE64 7528018573573808732);
        secret (@repr WORDSIZE64 10776056440809943711);
        secret (@repr WORDSIZE64 16147550488514976944)
      ] in  l).

Definition g1_xnum_k_3 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1691355743628586423);
        secret (@repr WORDSIZE64 5622191986793862162);
        secret (@repr WORDSIZE64 15561595211679121189);
        secret (@repr WORDSIZE64 17416319752018800771);
        secret (@repr WORDSIZE64 5996228842464768403);
        secret (@repr WORDSIZE64 14245880009877842017)
      ] in  l).

Definition g1_xnum_k_4 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1051997788391994435);
        secret (@repr WORDSIZE64 7368650625050054228);
        secret (@repr WORDSIZE64 11086623519836470079);
        secret (@repr WORDSIZE64 607681821319080984);
        secret (@repr WORDSIZE64 10978131499682789316);
        secret (@repr WORDSIZE64 5842660658088809945)
      ] in  l).

Definition g1_xnum_k_5 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1598992431623377919);
        secret (@repr WORDSIZE64 130921168661596853);
        secret (@repr WORDSIZE64 15797696746983946651);
        secret (@repr WORDSIZE64 11444679715590672272);
        secret (@repr WORDSIZE64 11567228658253249817);
        secret (@repr WORDSIZE64 14777367860349315459)
      ] in  l).

Definition g1_xnum_k_6 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 967946631563726121);
        secret (@repr WORDSIZE64 7653628713030275775);
        secret (@repr WORDSIZE64 12760252618317466849);
        secret (@repr WORDSIZE64 10378793938173061930);
        secret (@repr WORDSIZE64 10205808941053849290);
        secret (@repr WORDSIZE64 15985511645807504772)
      ] in  l).

Definition g1_xnum_k_7 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1709149555065084898);
        secret (@repr WORDSIZE64 16750075057192140371);
        secret (@repr WORDSIZE64 3849985779734105521);
        secret (@repr WORDSIZE64 11998370262181639475);
        secret (@repr WORDSIZE64 4159013751748851119);
        secret (@repr WORDSIZE64 11298218755092433038)
      ] in  l).

Definition g1_xnum_k_8 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 580186936973955012);
        secret (@repr WORDSIZE64 8903813505199544589);
        secret (@repr WORDSIZE64 14140024565662700916);
        secret (@repr WORDSIZE64 11728946595272970718);
        secret (@repr WORDSIZE64 5738313744366653077);
        secret (@repr WORDSIZE64 7886252005760951063)
      ] in  l).

Definition g1_xnum_k_9 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1628930385436977092);
        secret (@repr WORDSIZE64 3318087848058654498);
        secret (@repr WORDSIZE64 15937899882900905113);
        secret (@repr WORDSIZE64 7449821001803307903);
        secret (@repr WORDSIZE64 11752436998487615353);
        secret (@repr WORDSIZE64 9161465579737517214)
      ] in  l).

Definition g1_xnum_k_10 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1167027828517898210);
        secret (@repr WORDSIZE64 8275623842221021965);
        secret (@repr WORDSIZE64 18049808134997311382);
        secret (@repr WORDSIZE64 15351349873550116966);
        secret (@repr WORDSIZE64 17769927732099571180);
        secret (@repr WORDSIZE64 14584871380308065147)
      ] in  l).

Definition g1_xnum_k_11 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 495550047642324592);
        secret (@repr WORDSIZE64 13627494601717575229);
        secret (@repr WORDSIZE64 3591512392926246844);
        secret (@repr WORDSIZE64 2576269112800734056);
        secret (@repr WORDSIZE64 14000314106239596831);
        secret (@repr WORDSIZE64 12234233096825917993)
      ] in  l).

Definition g1_xden_k_0 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 633474091881273774);
        secret (@repr WORDSIZE64 1779737893574802031);
        secret (@repr WORDSIZE64 132274872219551930);
        secret (@repr WORDSIZE64 11283074393783708770);
        secret (@repr WORDSIZE64 13067430171545714168);
        secret (@repr WORDSIZE64 11041975239630265116)
      ] in  l).

Definition g1_xden_k_1 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1321272531362356291);
        secret (@repr WORDSIZE64 5238936591227237942);
        secret (@repr WORDSIZE64 8089002360232247308);
        secret (@repr WORDSIZE64 82967328719421271);
        secret (@repr WORDSIZE64 1430641118356186857);
        secret (@repr WORDSIZE64 16557527386785790975)
      ] in  l).

Definition g1_xden_k_2 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 804282852993868382);
        secret (@repr WORDSIZE64 9311163821600184607);
        secret (@repr WORDSIZE64 8037026956533927121);
        secret (@repr WORDSIZE64 18205324308570099372);
        secret (@repr WORDSIZE64 15466434890074226396);
        secret (@repr WORDSIZE64 18213183315621985817)
      ] in  l).

Definition g1_xden_k_3 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 234844145893171966);
        secret (@repr WORDSIZE64 14428037799351479124);
        secret (@repr WORDSIZE64 6559532710647391569);
        secret (@repr WORDSIZE64 6110444250091843536);
        secret (@repr WORDSIZE64 5293652763671852484);
        secret (@repr WORDSIZE64 1373009181854280920)
      ] in  l).

Definition g1_xden_k_4 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1416629893867312296);
        secret (@repr WORDSIZE64 751851957792514173);
        secret (@repr WORDSIZE64 18437674587247370939);
        secret (@repr WORDSIZE64 10190314345946351322);
        secret (@repr WORDSIZE64 11228207967368476701);
        secret (@repr WORDSIZE64 6025034940388909598)
      ] in  l).

Definition g1_xden_k_5 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1041270466333271993);
        secret (@repr WORDSIZE64 6140956605115975401);
        secret (@repr WORDSIZE64 4131830461445745997);
        secret (@repr WORDSIZE64 739642499118176303);
        secret (@repr WORDSIZE64 8358912131254619921);
        secret (@repr WORDSIZE64 13847998906088228005)
      ] in  l).

Definition g1_xden_k_6 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 536714149743900185);
        secret (@repr WORDSIZE64 1098328982230230817);
        secret (@repr WORDSIZE64 6273329123533496713);
        secret (@repr WORDSIZE64 5633448088282521244);
        secret (@repr WORDSIZE64 16894043798660571244);
        secret (@repr WORDSIZE64 17016134625831438906)
      ] in  l).

Definition g1_xden_k_7 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1488347500898461874);
        secret (@repr WORDSIZE64 3509418672874520985);
        secret (@repr WORDSIZE64 7962192351555381416);
        secret (@repr WORDSIZE64 1843909372225399896);
        secret (@repr WORDSIZE64 1127511003250156243);
        secret (@repr WORDSIZE64 1294742680819751518)
      ] in  l).

Definition g1_xden_k_8 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 725340084226051970);
        secret (@repr WORDSIZE64 6814521545734988748);
        secret (@repr WORDSIZE64 16176803544133875307);
        secret (@repr WORDSIZE64 8363199516777220149);
        secret (@repr WORDSIZE64 252877309218538352);
        secret (@repr WORDSIZE64 5149562959837648449)
      ] in  l).

Definition g1_xden_k_9 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 675470927100193492);
        secret (@repr WORDSIZE64 5146891164735334016);
        secret (@repr WORDSIZE64 17762958817130696759);
        secret (@repr WORDSIZE64 8565656522589412373);
        secret (@repr WORDSIZE64 10599026333335446784);
        secret (@repr WORDSIZE64 3270603789344496906)
      ] in  l).

Definition g1_ynum_k_0 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 652344406751465184);
        secret (@repr WORDSIZE64 2710356675495255290);
        secret (@repr WORDSIZE64 1273695771440998738);
        secret (@repr WORDSIZE64 3121750372618945491);
        secret (@repr WORDSIZE64 14775319642720936898);
        secret (@repr WORDSIZE64 13733803417833814835)
      ] in  l).

Definition g1_ynum_k_1 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1389807578337138705);
        secret (@repr WORDSIZE64 15352831428748068483);
        secret (@repr WORDSIZE64 1307144967559264317);
        secret (@repr WORDSIZE64 1121505450578652468);
        secret (@repr WORDSIZE64 15475889019760388287);
        secret (@repr WORDSIZE64 16183658160488302230)
      ] in  l).

Definition g1_ynum_k_2 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 57553299067792998);
        secret (@repr WORDSIZE64 17628079362768849300);
        secret (@repr WORDSIZE64 2689461337731570914);
        secret (@repr WORDSIZE64 14070580367580990887);
        secret (@repr WORDSIZE64 15162865775551710499);
        secret (@repr WORDSIZE64 13321614990632673782)
      ] in  l).

Definition g1_ynum_k_3 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 141972750621744161);
        secret (@repr WORDSIZE64 8689824239172478807);
        secret (@repr WORDSIZE64 15288216298323671324);
        secret (@repr WORDSIZE64 712874875091754233);
        secret (@repr WORDSIZE64 16014900032503684588);
        secret (@repr WORDSIZE64 11976580453200426187)
      ] in  l).

Definition g1_ynum_k_4 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 633886036738506515);
        secret (@repr WORDSIZE64 6678644607214234052);
        secret (@repr WORDSIZE64 1825425679455244472);
        secret (@repr WORDSIZE64 8755912272271186652);
        secret (@repr WORDSIZE64 3379943669301788840);
        secret (@repr WORDSIZE64 4735212769449148123)
      ] in  l).

Definition g1_ynum_k_5 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1612358804494830442);
        secret (@repr WORDSIZE64 2454990789666711200);
        secret (@repr WORDSIZE64 8405916841409361853);
        secret (@repr WORDSIZE64 8525415512662168654);
        secret (@repr WORDSIZE64 2323684950984523890);
        secret (@repr WORDSIZE64 11074978966450447856)
      ] in  l).

Definition g1_ynum_k_6 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 336375361001233340);
        secret (@repr WORDSIZE64 12882959944969186108);
        secret (@repr WORDSIZE64 16671121624101127371);
        secret (@repr WORDSIZE64 5922586712221110071);
        secret (@repr WORDSIZE64 5163511947597922654);
        secret (@repr WORDSIZE64 14511152726087948018)
      ] in  l).

Definition g1_ynum_k_7 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 686738286210365551);
        secret (@repr WORDSIZE64 16039894141796533876);
        secret (@repr WORDSIZE64 1660145734357211167);
        secret (@repr WORDSIZE64 18231571463891878950);
        secret (@repr WORDSIZE64 4825120264949852469);
        secret (@repr WORDSIZE64 11627815551290637097)
      ] in  l).

Definition g1_ynum_k_8 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 719520515476580427);
        secret (@repr WORDSIZE64 16756942182913253819);
        secret (@repr WORDSIZE64 10320769399998235244);
        secret (@repr WORDSIZE64 2200974244968450750);
        secret (@repr WORDSIZE64 7626373186594408355);
        secret (@repr WORDSIZE64 6933025920263103879)
      ] in  l).

Definition g1_ynum_k_9 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1016611174344998325);
        secret (@repr WORDSIZE64 2466492548686891555);
        secret (@repr WORDSIZE64 14135124294293452542);
        secret (@repr WORDSIZE64 475233659467912251);
        secret (@repr WORDSIZE64 11186783513499056751);
        secret (@repr WORDSIZE64 3147922594245844016)
      ] in  l).

Definition g1_ynum_k_10 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1833315000454533566);
        secret (@repr WORDSIZE64 1007974600900082579);
        secret (@repr WORDSIZE64 14785260176242854207);
        secret (@repr WORDSIZE64 15066861003931772432);
        secret (@repr WORDSIZE64 3584647998681889532);
        secret (@repr WORDSIZE64 16722834201330696498)
      ] in  l).

Definition g1_ynum_k_11 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1780164921828767454);
        secret (@repr WORDSIZE64 13337622794239929804);
        secret (@repr WORDSIZE64 5923739534552515142);
        secret (@repr WORDSIZE64 3345046972101780530);
        secret (@repr WORDSIZE64 5321510883028162054);
        secret (@repr WORDSIZE64 14846055306840460686)
      ] in  l).

Definition g1_ynum_k_12 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 799438051374502809);
        secret (@repr WORDSIZE64 15083972834952036164);
        secret (@repr WORDSIZE64 8838227588559581326);
        secret (@repr WORDSIZE64 13846054168121598783);
        secret (@repr WORDSIZE64 488730451382505970);
        secret (@repr WORDSIZE64 958146249756188408)
      ] in  l).

Definition g1_ynum_k_13 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 163716820423854747);
        secret (@repr WORDSIZE64 8285498163857659356);
        secret (@repr WORDSIZE64 8465424830341846400);
        secret (@repr WORDSIZE64 1433942577299613084);
        secret (@repr WORDSIZE64 14325828012864645732);
        secret (@repr WORDSIZE64 4817114329354076467)
      ] in  l).

Definition g1_ynum_k_14 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 414658151749832465);
        secret (@repr WORDSIZE64 189531577938912252);
        secret (@repr WORDSIZE64 6802473390048830824);
        secret (@repr WORDSIZE64 15684647020317539556);
        secret (@repr WORDSIZE64 7755485098777620407);
        secret (@repr WORDSIZE64 9685868895687483979)
      ] in  l).

Definition g1_ynum_k_15 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1578157964224562126);
        secret (@repr WORDSIZE64 5666948055268535989);
        secret (@repr WORDSIZE64 14634479491382401593);
        secret (@repr WORDSIZE64 6317940024988860850);
        secret (@repr WORDSIZE64 13142913832013798519);
        secret (@repr WORDSIZE64 338991247778166276)
      ] in  l).

Definition g1_yden_k_0 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1590100849350973618);
        secret (@repr WORDSIZE64 5915497081334721257);
        secret (@repr WORDSIZE64 6924968209373727718);
        secret (@repr WORDSIZE64 17204633670617869946);
        secret (@repr WORDSIZE64 572916540828819565);
        secret (@repr WORDSIZE64 92203205520679873)
      ] in  l).

Definition g1_yden_k_1 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1829261189398470686);
        secret (@repr WORDSIZE64 1877083417397643448);
        secret (@repr WORDSIZE64 9640042925497046428);
        secret (@repr WORDSIZE64 11862766565471805471);
        secret (@repr WORDSIZE64 8693114993904885301);
        secret (@repr WORDSIZE64 3672140328108400701)
      ] in  l).

Definition g1_yden_k_2 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 400243331105348135);
        secret (@repr WORDSIZE64 8046435537999802711);
        secret (@repr WORDSIZE64 8702226981475745585);
        secret (@repr WORDSIZE64 879791671491744492);
        secret (@repr WORDSIZE64 11994630442058346377);
        secret (@repr WORDSIZE64 2172204746352322546)
      ] in  l).

Definition g1_yden_k_3 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1637008473169220501);
        secret (@repr WORDSIZE64 17441636237435581649);
        secret (@repr WORDSIZE64 15066165676546511630);
        secret (@repr WORDSIZE64 1314387578457599809);
        secret (@repr WORDSIZE64 8247046336453711789);
        secret (@repr WORDSIZE64 12164906044230685718)
      ] in  l).

Definition g1_yden_k_4 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 855930740911588324);
        secret (@repr WORDSIZE64 12685735333705453020);
        secret (@repr WORDSIZE64 14326404096614579120);
        secret (@repr WORDSIZE64 6066025509460822294);
        secret (@repr WORDSIZE64 11676450493790612973);
        secret (@repr WORDSIZE64 15724621714793234461)
      ] in  l).

Definition g1_yden_k_5 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 637792788410719021);
        secret (@repr WORDSIZE64 11507373155986977154);
        secret (@repr WORDSIZE64 13186912195705886849);
        secret (@repr WORDSIZE64 14262012144631372388);
        secret (@repr WORDSIZE64 5328758613570342114);
        secret (@repr WORDSIZE64 199925847119476652)
      ] in  l).

Definition g1_yden_k_6 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1612297190139091759);
        secret (@repr WORDSIZE64 14103733843373163083);
        secret (@repr WORDSIZE64 6840121186619029743);
        secret (@repr WORDSIZE64 6760859324815900753);
        secret (@repr WORDSIZE64 15418807805142572985);
        secret (@repr WORDSIZE64 4402853133867972444)
      ] in  l).

Definition g1_yden_k_7 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1631410310868805610);
        secret (@repr WORDSIZE64 269334146695233390);
        secret (@repr WORDSIZE64 16547411811928854487);
        secret (@repr WORDSIZE64 18353100669930795314);
        secret (@repr WORDSIZE64 13339932232668798692);
        secret (@repr WORDSIZE64 6984591927261867737)
      ] in  l).

Definition g1_yden_k_8 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1758313625630302499);
        secret (@repr WORDSIZE64 1881349400343039172);
        secret (@repr WORDSIZE64 18013005311323887904);
        secret (@repr WORDSIZE64 12377427846571989832);
        secret (@repr WORDSIZE64 5967237584920922243);
        secret (@repr WORDSIZE64 7720081932193848650)
      ] in  l).

Definition g1_yden_k_9 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1619701357752249884);
        secret (@repr WORDSIZE64 16898074901591262352);
        secret (@repr WORDSIZE64 3609344159736760251);
        secret (@repr WORDSIZE64 5983130161189999867);
        secret (@repr WORDSIZE64 14355327869992416094);
        secret (@repr WORDSIZE64 3778226018344582997)
      ] in  l).

Definition g1_yden_k_10 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 347606589330687421);
        secret (@repr WORDSIZE64 5255719044972187933);
        secret (@repr WORDSIZE64 11271894388753671721);
        secret (@repr WORDSIZE64 1033887512062764488);
        secret (@repr WORDSIZE64 8189165486932690436);
        secret (@repr WORDSIZE64 70004379462101672)
      ] in  l).

Definition g1_yden_k_11 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 778202887894139711);
        secret (@repr WORDSIZE64 17691595219776375879);
        secret (@repr WORDSIZE64 9193253711563866834);
        secret (@repr WORDSIZE64 10092455202333888821);
        secret (@repr WORDSIZE64 1655469341950262250);
        secret (@repr WORDSIZE64 10845992994110574738)
      ] in  l).

Definition g1_yden_k_12 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 781015344221683683);
        secret (@repr WORDSIZE64 14078588081290548374);
        secret (@repr WORDSIZE64 6067271023149908518);
        secret (@repr WORDSIZE64 9033357708497886086);
        secret (@repr WORDSIZE64 10592474449179118273);
        secret (@repr WORDSIZE64 2204988348113831372)
      ] in  l).

Definition g1_yden_k_13 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 172830037692534587);
        secret (@repr WORDSIZE64 7101012286790006514);
        secret (@repr WORDSIZE64 13787308004332873665);
        secret (@repr WORDSIZE64 14660498759553796110);
        secret (@repr WORDSIZE64 4757234684169342080);
        secret (@repr WORDSIZE64 15130647872920159991)
      ] in  l).

Definition g1_yden_k_14 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1013206390650290238);
        secret (@repr WORDSIZE64 7720336747103001025);
        secret (@repr WORDSIZE64 8197694151986493523);
        secret (@repr WORDSIZE64 3625112747029342752);
        secret (@repr WORDSIZE64 6675167463148394368);
        secret (@repr WORDSIZE64 4905905684016745359)
      ] in  l).

Definition g1_simple_swu_iso (u_150 : fp) : (fp × fp) :=
  let z_151 : fp :=
    nat_mod_from_literal (_) (@repr WORDSIZE128 11) in 
  let a_152 : fp :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (g1_iso_a)) in 
  let b_153 : fp :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (g1_iso_b)) in 
  let tv1_154 : fp :=
    nat_mod_inv ((((z_151) *% (z_151)) *% (nat_mod_exp (u_150) (
            @repr WORDSIZE32 4))) +% (((z_151) *% (u_150)) *% (u_150))) in 
  let x1_155 : fp :=
    (((nat_mod_zero ) -% (b_153)) *% (nat_mod_inv (a_152))) *% ((
        nat_mod_one ) +% (tv1_154)) in 
  let '(x1_155) :=
    if (tv1_154) =.? (nat_mod_zero ):bool then (let x1_155 :=
        (b_153) *% (nat_mod_inv ((z_151) *% (a_152))) in 
      (x1_155)) else ((x1_155)) in 
  let gx1_156 : fp :=
    ((nat_mod_exp (x1_155) (@repr WORDSIZE32 3)) +% ((a_152) *% (x1_155))) +% (
      b_153) in 
  let x2_157 : fp :=
    (((z_151) *% (u_150)) *% (u_150)) *% (x1_155) in 
  let gx2_158 : fp :=
    ((nat_mod_exp (x2_157) (@repr WORDSIZE32 3)) +% ((a_152) *% (x2_157))) +% (
      b_153) in 
  let '(x_159, y_160) :=
    (if (fp_is_square (gx1_156)):bool then ((x1_155, fp_sqrt (gx1_156))) else ((
          x2_157,
          fp_sqrt (gx2_158)
        ))) in 
  let '(y_160) :=
    if (fp_sgn0 (u_150)) !=.? (fp_sgn0 (y_160)):bool then (let y_160 :=
        (nat_mod_zero ) -% (y_160) in 
      (y_160)) else ((y_160)) in 
  (x_159, y_160).

Definition g1_isogeny_map (x_161 : fp) (y_162 : fp) : g1 :=
  let xnum_k_163 : seq fp :=
    seq_new_ (default) (usize 12) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_0))) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_1))) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_2))) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_3))) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_4))) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_5))) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_6))) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_7))) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_8))) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_9))) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 10) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_10))) in 
  let xnum_k_163 :=
    seq_upd xnum_k_163 (usize 11) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_11))) in 
  let xden_k_164 : seq fp :=
    seq_new_ (default) (usize 10) in 
  let xden_k_164 :=
    seq_upd xden_k_164 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_0))) in 
  let xden_k_164 :=
    seq_upd xden_k_164 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_1))) in 
  let xden_k_164 :=
    seq_upd xden_k_164 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_2))) in 
  let xden_k_164 :=
    seq_upd xden_k_164 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_3))) in 
  let xden_k_164 :=
    seq_upd xden_k_164 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_4))) in 
  let xden_k_164 :=
    seq_upd xden_k_164 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_5))) in 
  let xden_k_164 :=
    seq_upd xden_k_164 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_6))) in 
  let xden_k_164 :=
    seq_upd xden_k_164 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_7))) in 
  let xden_k_164 :=
    seq_upd xden_k_164 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_8))) in 
  let xden_k_164 :=
    seq_upd xden_k_164 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_9))) in 
  let ynum_k_165 : seq fp :=
    seq_new_ (default) (usize 16) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_0))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_1))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_2))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_3))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_4))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_5))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_6))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_7))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_8))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_9))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 10) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_10))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 11) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_11))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 12) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_12))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 13) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_13))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 14) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_14))) in 
  let ynum_k_165 :=
    seq_upd ynum_k_165 (usize 15) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_15))) in 
  let yden_k_166 : seq fp :=
    seq_new_ (default) (usize 15) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_0))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_1))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_2))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_3))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_4))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_5))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_6))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_7))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_8))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_9))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 10) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_10))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 11) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_11))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 12) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_12))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 13) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_13))) in 
  let yden_k_166 :=
    seq_upd yden_k_166 (usize 14) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_14))) in 
  let xnum_167 : fp :=
    nat_mod_zero  in 
  let xx_168 : fp :=
    nat_mod_one  in 
  let '(xnum_167, xx_168) :=
    foldi (usize 0) (seq_len (xnum_k_163)) (fun i_169 '(xnum_167, xx_168) =>
      let xnum_167 :=
        (xnum_167) +% ((xx_168) *% (seq_index (xnum_k_163) (i_169))) in 
      let xx_168 :=
        (xx_168) *% (x_161) in 
      (xnum_167, xx_168))
    (xnum_167, xx_168) in 
  let xden_170 : fp :=
    nat_mod_zero  in 
  let xx_171 : fp :=
    nat_mod_one  in 
  let '(xden_170, xx_171) :=
    foldi (usize 0) (seq_len (xden_k_164)) (fun i_172 '(xden_170, xx_171) =>
      let xden_170 :=
        (xden_170) +% ((xx_171) *% (seq_index (xden_k_164) (i_172))) in 
      let xx_171 :=
        (xx_171) *% (x_161) in 
      (xden_170, xx_171))
    (xden_170, xx_171) in 
  let xden_170 :=
    (xden_170) +% (xx_171) in 
  let ynum_173 : fp :=
    nat_mod_zero  in 
  let xx_174 : fp :=
    nat_mod_one  in 
  let '(ynum_173, xx_174) :=
    foldi (usize 0) (seq_len (ynum_k_165)) (fun i_175 '(ynum_173, xx_174) =>
      let ynum_173 :=
        (ynum_173) +% ((xx_174) *% (seq_index (ynum_k_165) (i_175))) in 
      let xx_174 :=
        (xx_174) *% (x_161) in 
      (ynum_173, xx_174))
    (ynum_173, xx_174) in 
  let yden_176 : fp :=
    nat_mod_zero  in 
  let xx_177 : fp :=
    nat_mod_one  in 
  let '(yden_176, xx_177) :=
    foldi (usize 0) (seq_len (yden_k_166)) (fun i_178 '(yden_176, xx_177) =>
      let yden_176 :=
        (yden_176) +% ((xx_177) *% (seq_index (yden_k_166) (i_178))) in 
      let xx_177 :=
        (xx_177) *% (x_161) in 
      (yden_176, xx_177))
    (yden_176, xx_177) in 
  let yden_176 :=
    (yden_176) +% (xx_177) in 
  let xr_179 : fp :=
    (xnum_167) *% (nat_mod_inv (xden_170)) in 
  let yr_180 : fp :=
    ((y_162) *% (ynum_173)) *% (nat_mod_inv (yden_176)) in 
  let inf_181 : bool :=
    false in 
  let '(inf_181) :=
    if ((xden_170) =.? (nat_mod_zero )) || ((yden_176) =.? (
        nat_mod_zero )):bool then (let inf_181 :=
        true in 
      (inf_181)) else ((inf_181)) in 
  (xr_179, yr_180, inf_181).

Definition g1_map_to_curve_sswu (u_182 : fp) : g1 :=
  let '(xp_183, yp_184) :=
    g1_simple_swu_iso (u_182) in 
  let p_185 : (fp × fp × bool) :=
    g1_isogeny_map (xp_183) (yp_184) in 
  p_185.

Definition g1_hash_to_curve_sswu
  (msg_186 : byte_seq)
  (dst_187 : byte_seq)
  : g1 :=
  let u_188 : seq fp :=
    fp_hash_to_field (msg_186) (dst_187) (usize 2) in 
  let q0_189 : (fp × fp × bool) :=
    g1_map_to_curve_sswu (seq_index (u_188) (usize 0)) in 
  let q1_190 : (fp × fp × bool) :=
    g1_map_to_curve_sswu (seq_index (u_188) (usize 1)) in 
  let r_191 : (fp × fp × bool) :=
    g1add (q0_189) (q1_190) in 
  let p_192 : (fp × fp × bool) :=
    g1_clear_cofactor (r_191) in 
  p_192.

Definition g1_encode_to_curve_sswu
  (msg_193 : byte_seq)
  (dst_194 : byte_seq)
  : g1 :=
  let u_195 : seq fp :=
    fp_hash_to_field (msg_193) (dst_194) (usize 1) in 
  let q_196 : (fp × fp × bool) :=
    g1_map_to_curve_sswu (seq_index (u_195) (usize 0)) in 
  let p_197 : (fp × fp × bool) :=
    g1_clear_cofactor (q_196) in 
  p_197.

Definition g2_xnum_k_0 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 416399692810564414);
        secret (@repr WORDSIZE64 13500519111022079365);
        secret (@repr WORDSIZE64 3658379999393219626);
        secret (@repr WORDSIZE64 9850925049107374429);
        secret (@repr WORDSIZE64 6640057249351452444);
        secret (@repr WORDSIZE64 7077594464397203414)
      ] in  l).

Definition g2_xnum_k_1_i : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244);
        secret (@repr WORDSIZE64 3608069185647134863);
        secret (@repr WORDSIZE64 10975139998179658879);
        secret (@repr WORDSIZE64 11106031073612571672);
        secret (@repr WORDSIZE64 1473427674344805717);
        secret (@repr WORDSIZE64 2786039319482058522)
      ] in  l).

Definition g2_xnum_k_2_r : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244);
        secret (@repr WORDSIZE64 3608069185647134863);
        secret (@repr WORDSIZE64 10975139998179658879);
        secret (@repr WORDSIZE64 11106031073612571672);
        secret (@repr WORDSIZE64 1473427674344805717);
        secret (@repr WORDSIZE64 2786039319482058526)
      ] in  l).

Definition g2_xnum_k_2_i : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 624599539215846622);
        secret (@repr WORDSIZE64 1804034592823567431);
        secret (@repr WORDSIZE64 14710942035944605247);
        secret (@repr WORDSIZE64 14776387573661061644);
        secret (@repr WORDSIZE64 736713837172402858);
        secret (@repr WORDSIZE64 10616391696595805069)
      ] in  l).

Definition g2_xnum_k_3_r : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1665598771242257658);
        secret (@repr WORDSIZE64 17108588296669214228);
        secret (@repr WORDSIZE64 14633519997572878506);
        secret (@repr WORDSIZE64 2510212049010394485);
        secret (@repr WORDSIZE64 8113484923696258161);
        secret (@repr WORDSIZE64 9863633783879261905)
      ] in  l).

Definition g2_xden_k_0_i : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866);
        secret (@repr WORDSIZE64 5412103778470702295);
        secret (@repr WORDSIZE64 7239337960414712511);
        secret (@repr WORDSIZE64 7435674573564081700);
        secret (@repr WORDSIZE64 2210141511517208575);
        secret (@repr WORDSIZE64 13402431016077863523)
      ] in  l).

Definition g2_xden_k_1_i : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866);
        secret (@repr WORDSIZE64 5412103778470702295);
        secret (@repr WORDSIZE64 7239337960414712511);
        secret (@repr WORDSIZE64 7435674573564081700);
        secret (@repr WORDSIZE64 2210141511517208575);
        secret (@repr WORDSIZE64 13402431016077863583)
      ] in  l).

Definition g2_ynum_k_0 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1526798873638736187);
        secret (@repr WORDSIZE64 6459500568425337235);
        secret (@repr WORDSIZE64 1116230615302104219);
        secret (@repr WORDSIZE64 17673314439684154624);
        secret (@repr WORDSIZE64 18197961889718808424);
        secret (@repr WORDSIZE64 1355520937843676934)
      ] in  l).

Definition g2_ynum_k_1_i : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 416399692810564414);
        secret (@repr WORDSIZE64 13500519111022079365);
        secret (@repr WORDSIZE64 3658379999393219626);
        secret (@repr WORDSIZE64 9850925049107374429);
        secret (@repr WORDSIZE64 6640057249351452444);
        secret (@repr WORDSIZE64 7077594464397203390)
      ] in  l).

Definition g2_ynum_k_2_r : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244);
        secret (@repr WORDSIZE64 3608069185647134863);
        secret (@repr WORDSIZE64 10975139998179658879);
        secret (@repr WORDSIZE64 11106031073612571672);
        secret (@repr WORDSIZE64 1473427674344805717);
        secret (@repr WORDSIZE64 2786039319482058524)
      ] in  l).

Definition g2_ynum_k_2_i : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 624599539215846622);
        secret (@repr WORDSIZE64 1804034592823567431);
        secret (@repr WORDSIZE64 14710942035944605247);
        secret (@repr WORDSIZE64 14776387573661061644);
        secret (@repr WORDSIZE64 736713837172402858);
        secret (@repr WORDSIZE64 10616391696595805071)
      ] in  l).

Definition g2_ynum_k_3_r : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1318599027233453979);
        secret (@repr WORDSIZE64 18155985086623849168);
        secret (@repr WORDSIZE64 8510412652460270214);
        secret (@repr WORDSIZE64 12747851915130467410);
        secret (@repr WORDSIZE64 5654561228188306393);
        secret (@repr WORDSIZE64 16263467779354626832)
      ] in  l).

Definition g2_yden_k_0 : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866);
        secret (@repr WORDSIZE64 5412103778470702295);
        secret (@repr WORDSIZE64 7239337960414712511);
        secret (@repr WORDSIZE64 7435674573564081700);
        secret (@repr WORDSIZE64 2210141511517208575);
        secret (@repr WORDSIZE64 13402431016077863163)
      ] in  l).

Definition g2_yden_k_1_i : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866);
        secret (@repr WORDSIZE64 5412103778470702295);
        secret (@repr WORDSIZE64 7239337960414712511);
        secret (@repr WORDSIZE64 7435674573564081700);
        secret (@repr WORDSIZE64 2210141511517208575);
        secret (@repr WORDSIZE64 13402431016077863379)
      ] in  l).

Definition g2_yden_k_2_i : arr_fp :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866);
        secret (@repr WORDSIZE64 5412103778470702295);
        secret (@repr WORDSIZE64 7239337960414712511);
        secret (@repr WORDSIZE64 7435674573564081700);
        secret (@repr WORDSIZE64 2210141511517208575);
        secret (@repr WORDSIZE64 13402431016077863577)
      ] in  l).

Definition g2_simple_swu_iso (u_198 : fp2) : (fp2 × fp2) :=
  let z_199 : (fp × fp) :=
    fp2neg ((nat_mod_two , nat_mod_one )) in 
  let a_200 : (fp × fp) :=
    (nat_mod_zero , nat_mod_from_literal (_) (@repr WORDSIZE128 240)) in 
  let b_201 : (fp × fp) :=
    (
      nat_mod_from_literal (_) (@repr WORDSIZE128 1012),
      nat_mod_from_literal (_) (@repr WORDSIZE128 1012)
    ) in 
  let tv1_202 : (fp × fp) :=
    fp2inv (fp2add (fp2mul (fp2mul (z_199) (z_199)) (fp2mul (fp2mul (u_198) (
              u_198)) (fp2mul (u_198) (u_198)))) (fp2mul (z_199) (fp2mul (
            u_198) (u_198)))) in 
  let x1_203 : (fp × fp) :=
    fp2mul (fp2mul (fp2neg (b_201)) (fp2inv (a_200))) (fp2add (fp2fromfp (
          nat_mod_one )) (tv1_202)) in 
  let '(x1_203) :=
    if (tv1_202) =.? (fp2zero ):bool then (let x1_203 :=
        fp2mul (b_201) (fp2inv (fp2mul (z_199) (a_200))) in 
      (x1_203)) else ((x1_203)) in 
  let gx1_204 : (fp × fp) :=
    fp2add (fp2add (fp2mul (fp2mul (x1_203) (x1_203)) (x1_203)) (fp2mul (
          a_200) (x1_203))) (b_201) in 
  let x2_205 : (fp × fp) :=
    fp2mul (fp2mul (z_199) (fp2mul (u_198) (u_198))) (x1_203) in 
  let gx2_206 : (fp × fp) :=
    fp2add (fp2add (fp2mul (fp2mul (x2_205) (x2_205)) (x2_205)) (fp2mul (
          a_200) (x2_205))) (b_201) in 
  let '(x_207, y_208) :=
    (if (fp2_is_square (gx1_204)):bool then ((x1_203, fp2_sqrt (gx1_204)
        )) else ((x2_205, fp2_sqrt (gx2_206)))) in 
  let '(y_208) :=
    if (fp2_sgn0 (u_198)) !=.? (fp2_sgn0 (y_208)):bool then (let y_208 :=
        fp2neg (y_208) in 
      (y_208)) else ((y_208)) in 
  (x_207, y_208).

Definition g2_isogeny_map (x_209 : fp2) (y_210 : fp2) : g2 :=
  let xnum_k_211 : seq (fp × fp) :=
    seq_new_ (default) (usize 4) in 
  let xnum_k_211 :=
    seq_upd xnum_k_211 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_0)),
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_0))
      )) in 
  let xnum_k_211 :=
    seq_upd xnum_k_211 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_1_i))
      )) in 
  let xnum_k_211 :=
    seq_upd xnum_k_211 (usize 2) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_2_r)),
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_2_i))
      )) in 
  let xnum_k_211 :=
    seq_upd xnum_k_211 (usize 3) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_3_r)),
        nat_mod_zero 
      )) in 
  let xden_k_212 : seq (fp × fp) :=
    seq_new_ (default) (usize 2) in 
  let xden_k_212 :=
    seq_upd xden_k_212 (usize 0) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xden_k_0_i))
      )) in 
  let xden_k_212 :=
    seq_upd xden_k_212 (usize 1) ((
        nat_mod_from_literal (_) (@repr WORDSIZE128 12),
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xden_k_1_i))
      )) in 
  let ynum_k_213 : seq (fp × fp) :=
    seq_new_ (default) (usize 4) in 
  let ynum_k_213 :=
    seq_upd ynum_k_213 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_0)),
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_0))
      )) in 
  let ynum_k_213 :=
    seq_upd ynum_k_213 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_1_i))
      )) in 
  let ynum_k_213 :=
    seq_upd ynum_k_213 (usize 2) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_2_r)),
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_2_i))
      )) in 
  let ynum_k_213 :=
    seq_upd ynum_k_213 (usize 3) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_3_r)),
        nat_mod_zero 
      )) in 
  let yden_k_214 : seq (fp × fp) :=
    seq_new_ (default) (usize 3) in 
  let yden_k_214 :=
    seq_upd yden_k_214 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_0)),
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_0))
      )) in 
  let yden_k_214 :=
    seq_upd yden_k_214 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_1_i))
      )) in 
  let yden_k_214 :=
    seq_upd yden_k_214 (usize 2) ((
        nat_mod_from_literal (_) (@repr WORDSIZE128 18),
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_2_i))
      )) in 
  let xnum_215 : (fp × fp) :=
    fp2zero  in 
  let xx_216 : (fp × fp) :=
    fp2fromfp (nat_mod_one ) in 
  let '(xnum_215, xx_216) :=
    foldi (usize 0) (seq_len (xnum_k_211)) (fun i_217 '(xnum_215, xx_216) =>
      let xnum_215 :=
        fp2add (xnum_215) (fp2mul (xx_216) (seq_index (xnum_k_211) (i_217))) in 
      let xx_216 :=
        fp2mul (xx_216) (x_209) in 
      (xnum_215, xx_216))
    (xnum_215, xx_216) in 
  let xden_218 : (fp × fp) :=
    fp2zero  in 
  let xx_219 : (fp × fp) :=
    fp2fromfp (nat_mod_one ) in 
  let '(xden_218, xx_219) :=
    foldi (usize 0) (seq_len (xden_k_212)) (fun i_220 '(xden_218, xx_219) =>
      let xden_218 :=
        fp2add (xden_218) (fp2mul (xx_219) (seq_index (xden_k_212) (i_220))) in 
      let xx_219 :=
        fp2mul (xx_219) (x_209) in 
      (xden_218, xx_219))
    (xden_218, xx_219) in 
  let xden_218 :=
    fp2add (xden_218) (xx_219) in 
  let ynum_221 : (fp × fp) :=
    fp2zero  in 
  let xx_222 : (fp × fp) :=
    fp2fromfp (nat_mod_one ) in 
  let '(ynum_221, xx_222) :=
    foldi (usize 0) (seq_len (ynum_k_213)) (fun i_223 '(ynum_221, xx_222) =>
      let ynum_221 :=
        fp2add (ynum_221) (fp2mul (xx_222) (seq_index (ynum_k_213) (i_223))) in 
      let xx_222 :=
        fp2mul (xx_222) (x_209) in 
      (ynum_221, xx_222))
    (ynum_221, xx_222) in 
  let yden_224 : (fp × fp) :=
    fp2zero  in 
  let xx_225 : (fp × fp) :=
    fp2fromfp (nat_mod_one ) in 
  let '(yden_224, xx_225) :=
    foldi (usize 0) (seq_len (yden_k_214)) (fun i_226 '(yden_224, xx_225) =>
      let yden_224 :=
        fp2add (yden_224) (fp2mul (xx_225) (seq_index (yden_k_214) (i_226))) in 
      let xx_225 :=
        fp2mul (xx_225) (x_209) in 
      (yden_224, xx_225))
    (yden_224, xx_225) in 
  let yden_224 :=
    fp2add (yden_224) (xx_225) in 
  let xr_227 : (fp × fp) :=
    fp2mul (xnum_215) (fp2inv (xden_218)) in 
  let yr_228 : (fp × fp) :=
    fp2mul (y_210) (fp2mul (ynum_221) (fp2inv (yden_224))) in 
  let inf_229 : bool :=
    false in 
  let '(inf_229) :=
    if ((xden_218) =.? (fp2zero )) || ((yden_224) =.? (fp2zero )):bool then (
      let inf_229 :=
        true in 
      (inf_229)) else ((inf_229)) in 
  (xr_227, yr_228, inf_229).

Definition g2_map_to_curve_sswu (u_230 : fp2) : g2 :=
  let '(xp_231, yp_232) :=
    g2_simple_swu_iso (u_230) in 
  let p_233 : ((fp × fp) × (fp × fp) × bool) :=
    g2_isogeny_map (xp_231) (yp_232) in 
  p_233.

Definition g2_hash_to_curve_sswu
  (msg_234 : byte_seq)
  (dst_235 : byte_seq)
  : g2 :=
  let u_236 : seq fp2 :=
    fp2_hash_to_field (msg_234) (dst_235) (usize 2) in 
  let q0_237 : ((fp × fp) × (fp × fp) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_236) (usize 0)) in 
  let q1_238 : ((fp × fp) × (fp × fp) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_236) (usize 1)) in 
  let r_239 : ((fp × fp) × (fp × fp) × bool) :=
    g2add (q0_237) (q1_238) in 
  let p_240 : ((fp × fp) × (fp × fp) × bool) :=
    g2_clear_cofactor (r_239) in 
  p_240.

Definition g2_encode_to_curve_sswu
  (msg_241 : byte_seq)
  (dst_242 : byte_seq)
  : g2 :=
  let u_243 : seq fp2 :=
    fp2_hash_to_field (msg_241) (dst_242) (usize 1) in 
  let q_244 : ((fp × fp) × (fp × fp) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_243) (usize 0)) in 
  let p_245 : ((fp × fp) × (fp × fp) × bool) :=
    g2_clear_cofactor (q_244) in 
  p_245.

