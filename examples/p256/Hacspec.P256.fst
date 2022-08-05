module Hacspec.P256

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

noeq type error_t =
| InvalidAddition_error_t : error_t

let bits_v : uint_size =
  usize 256

type field_canvas_t = lseq (pub_uint8) (32)

type p256_field_element_t =
  nat_mod 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

type scalar_canvas_t = lseq (pub_uint8) (32)

type p256_scalar_t =
  nat_mod 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

type affine_t = (p256_field_element_t & p256_field_element_t)

type affine_result_t = (result affine_t error_t)

type p256_jacobian_t = (
  p256_field_element_t &
  p256_field_element_t &
  p256_field_element_t
)

type jacobian_result_t = (result p256_jacobian_t error_t)

type element_t = lseq (uint8) (usize 32)

let jacobian_to_affine (p_0 : p256_jacobian_t) : affine_t =
  let (x_1, y_2, z_3) : (
      p256_field_element_t &
      p256_field_element_t &
      p256_field_element_t
    ) =
    p_0
  in
  let z2_4 : p256_field_element_t =
    nat_exp (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      z_3) (pub_u32 0x2)
  in
  let z2i_5 : p256_field_element_t =
    nat_inv (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (z2_4)
  in
  let z3_6 : p256_field_element_t =
    (z_3) *% (z2_4)
  in
  let z3i_7 : p256_field_element_t =
    nat_inv (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (z3_6)
  in
  let x_8 : p256_field_element_t =
    (x_1) *% (z2i_5)
  in
  let y_9 : p256_field_element_t =
    (y_2) *% (z3i_7)
  in
  (x_8, y_9)

let affine_to_jacobian (p_10 : affine_t) : p256_jacobian_t =
  let (x_11, y_12) : (p256_field_element_t & p256_field_element_t) =
    p_10
  in
  (
    x_11,
    y_12,
    nat_from_literal (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      pub_u128 0x1)
  )

let point_double (p_13 : p256_jacobian_t) : p256_jacobian_t =
  let (x1_14, y1_15, z1_16) : (
      p256_field_element_t &
      p256_field_element_t &
      p256_field_element_t
    ) =
    p_13
  in
  let delta_17 : p256_field_element_t =
    nat_exp (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      z1_16) (pub_u32 0x2)
  in
  let gamma_18 : p256_field_element_t =
    nat_exp (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      y1_15) (pub_u32 0x2)
  in
  let beta_19 : p256_field_element_t =
    (x1_14) *% (gamma_18)
  in
  let alpha_1_20 : p256_field_element_t =
    (x1_14) -% (delta_17)
  in
  let alpha_2_21 : p256_field_element_t =
    (x1_14) +% (delta_17)
  in
  let alpha_22 : p256_field_element_t =
    (
      nat_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        pub_u128 0x3)) *% ((alpha_1_20) *% (alpha_2_21))
  in
  let x3_23 : p256_field_element_t =
    (
      nat_exp (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        alpha_22) (pub_u32 0x2)) -% (
      (
        nat_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          pub_u128 0x8)) *% (beta_19))
  in
  let z3_24 : p256_field_element_t =
    nat_exp (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      (y1_15) +% (z1_16)) (pub_u32 0x2)
  in
  let z3_25 : p256_field_element_t =
    (z3_24) -% ((gamma_18) +% (delta_17))
  in
  let y3_1_26 : p256_field_element_t =
    (
      (
        nat_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          pub_u128 0x4)) *% (beta_19)) -% (x3_23)
  in
  let y3_2_27 : p256_field_element_t =
    (
      nat_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        pub_u128 0x8)) *% ((gamma_18) *% (gamma_18))
  in
  let y3_28 : p256_field_element_t =
    ((alpha_22) *% (y3_1_26)) -% (y3_2_27)
  in
  (x3_23, y3_28, z3_25)

let is_point_at_infinity (p_29 : p256_jacobian_t) : bool =
  let (x_30, y_31, z_32) : (
      p256_field_element_t &
      p256_field_element_t &
      p256_field_element_t
    ) =
    p_29
  in
  nat_equal (
    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (z_32) (
    nat_from_literal (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      pub_u128 0x0))

let s1_equal_s2
  (s1_33 : p256_field_element_t)
  (s2_34 : p256_field_element_t)
  : jacobian_result_t =
  if (
    nat_equal (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      s1_33) (s2_34)) then (Err (InvalidAddition_error_t)) else (
    Ok (
      (
        nat_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          pub_u128 0x0),
        nat_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          pub_u128 0x1),
        nat_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          pub_u128 0x0)
      )))

let point_add_jacob
  (p_35 : p256_jacobian_t)
  (q_36 : p256_jacobian_t)
  : jacobian_result_t =
  let result_37 : (result p256_jacobian_t error_t) =
    Ok (q_36)
  in
  let (result_37) =
    if not (is_point_at_infinity (p_35)) then begin
      let (result_37) =
        if is_point_at_infinity (q_36) then begin
          let result_37 =
            Ok (p_35)
          in
          (result_37)
        end else begin
          let (x1_38, y1_39, z1_40) : (
              p256_field_element_t &
              p256_field_element_t &
              p256_field_element_t
            ) =
            p_35
          in
          let (x2_41, y2_42, z2_43) : (
              p256_field_element_t &
              p256_field_element_t &
              p256_field_element_t
            ) =
            q_36
          in
          let z1z1_44 : p256_field_element_t =
            nat_exp (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              z1_40) (pub_u32 0x2)
          in
          let z2z2_45 : p256_field_element_t =
            nat_exp (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              z2_43) (pub_u32 0x2)
          in
          let u1_46 : p256_field_element_t =
            (x1_38) *% (z2z2_45)
          in
          let u2_47 : p256_field_element_t =
            (x2_41) *% (z1z1_44)
          in
          let s1_48 : p256_field_element_t =
            ((y1_39) *% (z2_43)) *% (z2z2_45)
          in
          let s2_49 : p256_field_element_t =
            ((y2_42) *% (z1_40)) *% (z1z1_44)
          in
          let (result_37) =
            if nat_equal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              u1_46) (u2_47) then begin
              let result_37 =
                s1_equal_s2 (s1_48) (s2_49)
              in
              (result_37)
            end else begin
              let h_50 : p256_field_element_t =
                (u2_47) -% (u1_46)
              in
              let i_51 : p256_field_element_t =
                nat_exp (
                  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                  (
                    nat_from_literal (
                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                      pub_u128 0x2)) *% (h_50)) (pub_u32 0x2)
              in
              let j_52 : p256_field_element_t =
                (h_50) *% (i_51)
              in
              let r_53 : p256_field_element_t =
                (
                  nat_from_literal (
                    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                    pub_u128 0x2)) *% ((s2_49) -% (s1_48))
              in
              let v_54 : p256_field_element_t =
                (u1_46) *% (i_51)
              in
              let x3_1_55 : p256_field_element_t =
                (
                  nat_from_literal (
                    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                    pub_u128 0x2)) *% (v_54)
              in
              let x3_2_56 : p256_field_element_t =
                (
                  nat_exp (
                    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                    r_53) (pub_u32 0x2)) -% (j_52)
              in
              let x3_57 : p256_field_element_t =
                (x3_2_56) -% (x3_1_55)
              in
              let y3_1_58 : p256_field_element_t =
                (
                  (
                    nat_from_literal (
                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                      pub_u128 0x2)) *% (s1_48)) *% (j_52)
              in
              let y3_2_59 : p256_field_element_t =
                (r_53) *% ((v_54) -% (x3_57))
              in
              let y3_60 : p256_field_element_t =
                (y3_2_59) -% (y3_1_58)
              in
              let z3_61 : p256_field_element_t =
                nat_exp (
                  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                  (z1_40) +% (z2_43)) (pub_u32 0x2)
              in
              let z3_62 : p256_field_element_t =
                ((z3_61) -% ((z1z1_44) +% (z2z2_45))) *% (h_50)
              in
              let result_37 =
                Ok ((x3_57, y3_60, z3_62))
              in
              (result_37)
            end
          in
          (result_37)
        end
      in
      (result_37)
    end else begin (result_37)
    end
  in
  result_37

let ltr_mul
  (k_63 : p256_scalar_t)
  (p_64 : p256_jacobian_t)
  : jacobian_result_t =
  let q_65 : (p256_field_element_t & p256_field_element_t & p256_field_element_t
    ) =
    (
      nat_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        pub_u128 0x0),
      nat_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        pub_u128 0x1),
      nat_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        pub_u128 0x0)
    )
  in
  match (
    foldi_result (usize 0) (bits_v) (fun i_66 (q_65) ->
      let q_65 =
        point_double (q_65)
      in
      match (
        if nat_equal (
          0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551) (
          nat_get_bit (
            0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551) (
            k_63) (((bits_v) - (usize 1)) - (i_66))) (
          nat_one (
            0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551)) then begin
          match (point_add_jacob (q_65) (p_64)) with
          | Err x -> Err x
          | Ok  q_65 ->
            Ok ((q_65))
        end else begin Ok ((q_65))
        end) with
      | Err x -> Err x
      | Ok  (q_65) ->
        Ok ((q_65)))
    (q_65)) with
  | Err x -> Err x
  | Ok  (q_65) ->
    Ok (q_65)

let p256_point_mul (k_67 : p256_scalar_t) (p_68 : affine_t) : affine_result_t =
  match (ltr_mul (k_67) (affine_to_jacobian (p_68))) with
  | Err x -> Err x
  | Ok  jac_69 : p256_jacobian_t ->
    Ok (jacobian_to_affine (jac_69))

let p256_point_mul_base (k_70 : p256_scalar_t) : affine_result_t =
  let base_point_71 : (p256_field_element_t & p256_field_element_t) =
    (
      nat_from_byte_seq_be (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        32) (
        array_from_list (
          let l =
            [
              secret (pub_u8 0x6b);
              secret (pub_u8 0x17);
              secret (pub_u8 0xd1);
              secret (pub_u8 0xf2);
              secret (pub_u8 0xe1);
              secret (pub_u8 0x2c);
              secret (pub_u8 0x42);
              secret (pub_u8 0x47);
              secret (pub_u8 0xf8);
              secret (pub_u8 0xbc);
              secret (pub_u8 0xe6);
              secret (pub_u8 0xe5);
              secret (pub_u8 0x63);
              secret (pub_u8 0xa4);
              secret (pub_u8 0x40);
              secret (pub_u8 0xf2);
              secret (pub_u8 0x77);
              secret (pub_u8 0x3);
              secret (pub_u8 0x7d);
              secret (pub_u8 0x81);
              secret (pub_u8 0x2d);
              secret (pub_u8 0xeb);
              secret (pub_u8 0x33);
              secret (pub_u8 0xa0);
              secret (pub_u8 0xf4);
              secret (pub_u8 0xa1);
              secret (pub_u8 0x39);
              secret (pub_u8 0x45);
              secret (pub_u8 0xd8);
              secret (pub_u8 0x98);
              secret (pub_u8 0xc2);
              secret (pub_u8 0x96)
            ]
          in assert_norm (List.Tot.length l == 32); l)),
      nat_from_byte_seq_be (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        32) (
        array_from_list (
          let l =
            [
              secret (pub_u8 0x4f);
              secret (pub_u8 0xe3);
              secret (pub_u8 0x42);
              secret (pub_u8 0xe2);
              secret (pub_u8 0xfe);
              secret (pub_u8 0x1a);
              secret (pub_u8 0x7f);
              secret (pub_u8 0x9b);
              secret (pub_u8 0x8e);
              secret (pub_u8 0xe7);
              secret (pub_u8 0xeb);
              secret (pub_u8 0x4a);
              secret (pub_u8 0x7c);
              secret (pub_u8 0xf);
              secret (pub_u8 0x9e);
              secret (pub_u8 0x16);
              secret (pub_u8 0x2b);
              secret (pub_u8 0xce);
              secret (pub_u8 0x33);
              secret (pub_u8 0x57);
              secret (pub_u8 0x6b);
              secret (pub_u8 0x31);
              secret (pub_u8 0x5e);
              secret (pub_u8 0xce);
              secret (pub_u8 0xcb);
              secret (pub_u8 0xb6);
              secret (pub_u8 0x40);
              secret (pub_u8 0x68);
              secret (pub_u8 0x37);
              secret (pub_u8 0xbf);
              secret (pub_u8 0x51);
              secret (pub_u8 0xf5)
            ]
          in assert_norm (List.Tot.length l == 32); l))
    )
  in
  p256_point_mul (k_70) (base_point_71)

let point_add_distinct (p_72 : affine_t) (q_73 : affine_t) : affine_result_t =
  match (
    point_add_jacob (affine_to_jacobian (p_72)) (
      affine_to_jacobian (q_73))) with
  | Err x -> Err x
  | Ok  r_74 : p256_jacobian_t ->
    Ok (jacobian_to_affine (r_74))

let point_add (p_75 : affine_t) (q_76 : affine_t) : affine_result_t =
  if ((p_75) <> (q_76)) then (point_add_distinct (p_75) (q_76)) else (
    Ok (jacobian_to_affine (point_double (affine_to_jacobian (p_75)))))

let p256_validate_private_key (k_77 : byte_seq) : bool =
  let valid_78 : bool =
    true
  in
  let k_element_79 : p256_scalar_t =
    nat_from_byte_seq_be (
      0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551) (32) (
      k_77)
  in
  let k_element_bytes_80 : seq uint8 =
    nat_to_byte_seq_be (
      0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551) (32) (
      k_element_79)
  in
  let all_zero_81 : bool =
    true
  in
  let (valid_78, all_zero_81) =
    foldi (usize 0) (seq_len (k_77)) (fun i_82 (valid_78, all_zero_81) ->
      let (all_zero_81) =
        if not (
          uint8_equal (seq_index (k_77) (i_82)) (
            secret (pub_u8 0x0))) then begin
          let all_zero_81 =
            false
          in
          (all_zero_81)
        end else begin (all_zero_81)
        end
      in
      let (valid_78) =
        if not (
          uint8_equal (seq_index (k_element_bytes_80) (i_82)) (
            seq_index (k_77) (i_82))) then begin
          let valid_78 =
            false
          in
          (valid_78)
        end else begin (valid_78)
        end
      in
      (valid_78, all_zero_81))
    (valid_78, all_zero_81)
  in
  (valid_78) && (not (all_zero_81))

let p256_validate_public_key (p_83 : affine_t) : bool =
  let b_84 : p256_field_element_t =
    nat_from_byte_seq_be (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (32) (
      array_from_list (
        let l =
          [
            secret (pub_u8 0x5a);
            secret (pub_u8 0xc6);
            secret (pub_u8 0x35);
            secret (pub_u8 0xd8);
            secret (pub_u8 0xaa);
            secret (pub_u8 0x3a);
            secret (pub_u8 0x93);
            secret (pub_u8 0xe7);
            secret (pub_u8 0xb3);
            secret (pub_u8 0xeb);
            secret (pub_u8 0xbd);
            secret (pub_u8 0x55);
            secret (pub_u8 0x76);
            secret (pub_u8 0x98);
            secret (pub_u8 0x86);
            secret (pub_u8 0xbc);
            secret (pub_u8 0x65);
            secret (pub_u8 0x1d);
            secret (pub_u8 0x6);
            secret (pub_u8 0xb0);
            secret (pub_u8 0xcc);
            secret (pub_u8 0x53);
            secret (pub_u8 0xb0);
            secret (pub_u8 0xf6);
            secret (pub_u8 0x3b);
            secret (pub_u8 0xce);
            secret (pub_u8 0x3c);
            secret (pub_u8 0x3e);
            secret (pub_u8 0x27);
            secret (pub_u8 0xd2);
            secret (pub_u8 0x60);
            secret (pub_u8 0x4b)
          ]
        in assert_norm (List.Tot.length l == 32); l))
  in
  let point_at_infinity_85 : bool =
    is_point_at_infinity (affine_to_jacobian (p_83))
  in
  let (x_86, y_87) : (p256_field_element_t & p256_field_element_t) =
    p_83
  in
  let on_curve_88 : bool =
    ((y_87) *% (y_87)) =% (
      (
        (((x_86) *% (x_86)) *% (x_86)) -% (
          (
            nat_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              pub_u128 0x3)) *% (x_86))) +% (b_84))
  in
  (not (point_at_infinity_85)) && (on_curve_88)

let p256_calculate_w (x_89 : p256_field_element_t) : p256_field_element_t =
  let b_90 : p256_field_element_t =
    nat_from_byte_seq_be (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (32) (
      array_from_list (
        let l =
          [
            secret (pub_u8 0x5a);
            secret (pub_u8 0xc6);
            secret (pub_u8 0x35);
            secret (pub_u8 0xd8);
            secret (pub_u8 0xaa);
            secret (pub_u8 0x3a);
            secret (pub_u8 0x93);
            secret (pub_u8 0xe7);
            secret (pub_u8 0xb3);
            secret (pub_u8 0xeb);
            secret (pub_u8 0xbd);
            secret (pub_u8 0x55);
            secret (pub_u8 0x76);
            secret (pub_u8 0x98);
            secret (pub_u8 0x86);
            secret (pub_u8 0xbc);
            secret (pub_u8 0x65);
            secret (pub_u8 0x1d);
            secret (pub_u8 0x6);
            secret (pub_u8 0xb0);
            secret (pub_u8 0xcc);
            secret (pub_u8 0x53);
            secret (pub_u8 0xb0);
            secret (pub_u8 0xf6);
            secret (pub_u8 0x3b);
            secret (pub_u8 0xce);
            secret (pub_u8 0x3c);
            secret (pub_u8 0x3e);
            secret (pub_u8 0x27);
            secret (pub_u8 0xd2);
            secret (pub_u8 0x60);
            secret (pub_u8 0x4b)
          ]
        in assert_norm (List.Tot.length l == 32); l))
  in
  let exp_91 : p256_field_element_t =
    nat_from_byte_seq_be (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (32) (
      array_from_list (
        let l =
          [
            secret (pub_u8 0x3f);
            secret (pub_u8 0xff);
            secret (pub_u8 0xff);
            secret (pub_u8 0xff);
            secret (pub_u8 0xc0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x40);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x40);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0);
            secret (pub_u8 0x0)
          ]
        in assert_norm (List.Tot.length l == 32); l))
  in
  let z_92 : p256_field_element_t =
    (
      (((x_89) *% (x_89)) *% (x_89)) -% (
        (
          nat_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            pub_u128 0x3)) *% (x_89))) +% (b_90)
  in
  let w_93 : p256_field_element_t =
    nat_pow_felem (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      z_92) (exp_91)
  in
  w_93

