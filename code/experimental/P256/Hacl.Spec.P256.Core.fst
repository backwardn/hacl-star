module Hacl.Spec.P256.Core

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib

open Hacl.Spec.Curve25519.Field64.Definition
open Hacl.Spec.P256.Definitions
open Hacl.Spec.Curve25519.Field64.Core
open Hacl.Spec.P256.Lemmas

open FStar.Mul

(*
inline_for_extraction noextract
val sub4_prime:
    f1:felem4
  -> Pure (uint64 & felem4)
    (requires True)
    (ensures fun (c, r) -> True)


let sub4_prime (f10, f11, f12, f13)  =
  let o0, c0 = subborrow f10 (u64 0xffffffffffffffff) (u64 0) in
  let o1, c1 = subborrow f11 (u64 0xffffffff) c0 in
  let o2, c2 = subborrow f12 (u64 0) c1 in
  let o3, c3 = subborrow f13 (u64 0xffffffff00000001) c2 in
  (*!!!!*)
  (*lemma_mul_assos_5 (v c3) (pow2 64) (pow2 64) (pow2 64) (pow2 64); *)
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  c3, (o0, o1, o2, o3)
*) 

inline_for_extraction noextract
val lt_u64:a:uint64 -> b:uint64 -> Tot bool

let lt_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)


inline_for_extraction noextract
val gt: a: uint64 -> b: uint64 -> Tot uint64

let gt a b = 
  if lt_u64 b a then u64 1 else u64 0


let eq_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)


let eq_0_u64 a = 
  let b = u64 0 in 
  eq_u64 a b

inline_for_extraction noextract
val cmovznz: mask : uint64 ->  x: uint64 -> y: uint64 -> 
  Pure uint64
  (requires True)
  (ensures fun r ->(* if uint_v cin = 0 then uint_v r == uint_v x else uint_v r == uint_v y) *) True)

#reset-options "--z3refresh --z3rlimit 100"

(* reprove!  *)
let cmovznz cin x y  = 
    let x2 = neq_mask cin (u64 0) in 
    let x3 = logor (logand y x2) (logand x (lognot x2)) in
    let ln = lognot (neq_mask cin (u64 0)) in 
    log_and y x2; 
    log_not_lemma x2;
    log_and x ln;
    log_or (logand y x2) (logand x (lognot (x2)));
    admit();
    x3


inline_for_extraction noextract
val cmovznz4: cin: uint64{uint_v cin <=1} -> x: felem4 -> y: felem4 -> Pure (r: felem4)
(requires True)
(ensures fun r -> if uint_v cin = 0 then as_nat4 r == as_nat4 x else as_nat4 r == as_nat4 y)

let cmovznz4 cin (x0, x1, x2, x3) (y0, y1, y2, y3) = 
  let mask = neq_mask cin (u64 0) in 
  let r0 = logor (logand y0 mask) (logand x0 (lognot mask)) in 
  let r1 = logor (logand y1 mask) (logand x1 (lognot mask)) in 
  let r2 = logor (logand y2 mask) (logand x2 (lognot mask))  in 
  let r3 = logor (logand y3 mask) (logand x3 (lognot mask))  in 
  (r0, r1, r2, r3)


inline_for_extraction noextract
#set-options "--z3rlimit 100"
let felem_add (a0, a1, a2, a3) (b0, b1, b2, b3) = 
  let (x8, (x1, x3, x5, x7)) = add4 (a0, a1, a2, a3) (b0, b1, b2, b3)  in 
   lemma_nat_4 (x1, x3, x5, x7);
  assert_norm (as_nat4  (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) == prime);
  let (x16, x9, x11, x13, x15) = sub4 (x1, x3, x5, x7) (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001)  in 
  (* lemma_for_multiplication_1 (a0, a1, a2, a3) (b0, b1, b2, b3); *)
    lemma_nat_4 (x9, x11, x13, x15); 
  let (x17, x18) = subborrow x8 (u64 0) x16  in 
    prime_lemma (as_nat4 (a0, a1, a2, a3)  + as_nat4 (b0, b1, b2, b3));
    small_modulo_lemma_extended (as_nat4 (x1, x3, x5, x7)) prime; 
  let (r0, r1, r2, r3) = cmovznz4 x18 (x9, x11, x13, x15) (x1, x3, x5, x7) in 
  assert(as_nat4 (r0, r1, r2, r3) = (as_nat4 (a0, a1, a2, a3)  + as_nat4 (b0, b1, b2, b3)) % prime);
  (r0, r1, r2, r3)




(*  opening anything calls growing up the code*)
#reset-options "--z3rlimit 400"
let felem_sub (a0, a1, a2, a3) (b0, b1, b2, b3) = 
  let (c, r_0, r_1, r_2, r_3) = sub4  (a0, a1, a2, a3) (b0, b1, b2, b3) in 
    (* lemma_adding_prime arg1 arg2;     *)
 
  let x9 = cmovznz c (u64 0) (u64 0xffffffffffffffff) in 

  let prime_temp_0 = logand (u64 0xffffffffffffffff) x9 in 
  let prime_temp_1 = logand (u64 0xffffffff) x9 in 
  let prime_temp_2 = u64 0 in 
  let prime_temp_3 = logand (u64 0xffffffff00000001) x9 in 
  (* let prime_temp = (prime_temp_0, prime_temp_1, prime_temp_2, prime_temp_3) in  *)

  log_and (u64 0xffffffffffffffff) x9;
  log_and (u64 0xffffffff) x9;
  log_and (u64 0xffffffff00000001) x9;

  assert_norm (as_nat4 (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) == prime);
  
  let (c1, (r0, r1, r2, r3)) = add4 (prime_temp_0, prime_temp_1, prime_temp_2, prime_temp_3) (r_0, r_1, r_2, r_3) in 
    (* lemma_add4_zero prime_temp r; *)
    (* lemma_sub_add arg1 arg2 prime_temp r; *)
 (r0, r1, r2, r3)


let get_high_part a = 
  to_u32(shift_right a (size 32))


let get_low_part a = to_u32 a


val lemma_xor_zero: low: uint64{uint_v (get_high_part low) ==  0} -> high: uint64{uint_v (get_low_part high) == 0} ->  Lemma (uint_v (logxor low high) = uint_v high * pow2 32 + uint_v low)

let lemma_xor_zero low high = 
  assert(uint_v low = uint_v (get_low_part low));
  assert(uint_v high = uint_v (get_high_part high) * pow2 32);
  admit()


let store_high_low_u high low = 
  let as_uint64_high = to_u64 high in 
  let as_uint64_high = Lib.IntTypes.shift_left as_uint64_high (size 32) in 
  let as_uint64_low = to_u64 low in
  lemma_xor_zero as_uint64_low as_uint64_high;
  logxor as_uint64_low as_uint64_high


let reduction_prime_2prime (a0, a1, a2, a3) = 
  assert_norm (as_nat4 (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) == prime);
  let (x16, r0, r1, r2, r3) = sub4 (a0, a1, a2, a3) (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) in 
  cmovznz4 x16 (r0, r1, r2, r3) (a0, a1, a2, a3)

val reduction_prime_2prime_with_carry: carry: uint64{uint_v carry <= 1} -> a0: uint64 -> a1: uint64 -> a2: uint64 -> a3: uint64 -> Tot (r: felem4) (*{as_nat4 r == (as_nat4 a + uint_v carry * pow2 256) % prime} *)


let reduction_prime_2prime_with_carry carry a0 a1 a2 a3 = 
  (* lemma_nat_4 a; *)
    assert_norm (as_nat4 (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) == prime);
  let (x16, r0, r1, r2, r3) = sub4 (a0, a1, a2, a3) (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) in 
  let (result, c) = subborrow carry (u64 0) x16  in  
    (* assert(if as_nat4 a < prime then uint_v x16 = 1 else uint_v x16 = 0); *)
    (* lemma_nat_4 (a0, a1, a2, a3); *)

   (*  assert(if uint_v x16 = 0 then as_nat4 a - prime = as_nat4 r else True);
    assert(as_nat4 (a0, a1, a2, a3) < pow2 256);
    assert_norm (prime < pow2 256);
    assert(as_nat4 a + pow2 256 > prime);
    assert(if uint_v c = 0 then uint_v carry = uint_v x16 else uint_v carry < uint_v x16);
    *) 
    (* assert(if uint_v c = 0 then uint_v carry = 0 && uint_v x16 = 0 \/ uint_v carry = 1 && uint_v x16 = 1 else uint_v carry = 0 && uint_v x16 = 1); *)

  let (r_0, r_1, r_2, r_3) = cmovznz4 c (r0, r1, r2, r3) (a0, a1, a2, a3)  in 
    (* assert(if uint_v carry = 1 && uint_v x16 = 1 then as_nat4  (r0, r1, r2, r3) = (as_nat4 a + uint_v carry * pow2 256) % prime else True); *)
    (* assert(if uint_v carry = 1 && uint_v x16 = 0 then as_nat4  (r0, r1, r2, r3) = (as_nat4 a + uint_v carry * pow2 256) % prime else True); *)
    (* assert(if uint_v carry = 0 && uint_v x16 = 1 then as_nat4  (r0, r1, r2, r3) = (as_nat4 a + uint_v carry * pow2 256) % prime else True); *)
   (r_0, r_1, r_2, r_3) 

inline_for_extraction noextract
val shift_carry: x: uint64 -> cin: uint64{uint_v cin <=1} -> Tot (r: uint64 {uint_v r = (uint_v x * 2) % pow2 64 + uint_v cin})

let shift_carry x cin = 
  add (Lib.IntTypes.shift_left x (size 1)) cin


val lemma_get_number: a: nat {a < pow2 64} -> Lemma (
	let mask = 0x7fffffffffffffff in 
	let carry= if a> mask then 1 else 0 in 
	(a * 2) = (a * 2) % pow2 64 + carry * pow2 64)	

let lemma_get_number a = ()


val shift_left_lemma: a0: nat {a0 < pow2 64} -> a1: nat {a1 < pow2 64} -> a2: nat {a2 < pow2 64} -> a3: nat {a3 < pow2 64 /\
a0 + a1 * pow2 64 + a2 * pow2 128 + a3 * pow2 192 < prime} -> Lemma (let input = a0 + a1 * pow2 64 + a2 * pow2 128 + a3 * pow2 192 in 
  let mask = 0x7fffffffffffffff in 
 
  let carry0 = if a0 > mask then 1 else 0 in 
  let carry1 = if a1 > mask then 1 else 0 in 
  let carry2 = if a2 > mask then 1 else 0 in 
  let carry3 = if a3 > mask then 1 else 0 in 

  let a0_u = (a0 * 2) % pow2 64 + 0 in 
  let a1_u = (a1 * 2) % pow2 64 + carry0 in    
  let a2_u = (a2 * 2) % pow2 64 + carry1 in 
  let a3_u = (a3 * 2) % pow2 64 + carry2 in

  input * 2 = a0_u + a1_u * pow2 64 + a2_u * pow2 128 + a3_u * pow2 192 + carry3 * pow2 256 /\
  a0_u + a1_u * pow2 64 + a2_u * pow2 128 + a3_u * pow2 192 + carry3 * pow2 256 < 2 * prime)


let shift_left_lemma a0 a1 a2 a3 = 
  let input: nat = a0+ a1 * pow2 64 + a2 * pow2 128 + a3 * pow2 192 in 

  let mask = 0x7fffffffffffffff in 
  let carry0 = if a0 > mask then 1 else 0 in 
  let carry1 = if a1 > mask then 1 else 0 in 
  let carry2 = if a2 > mask then 1 else 0 in 
  let carry3 = if a3 > mask then 1 else 0 in 


  let a0_u = (a0 * 2) % pow2 64  in 
   lemma_get_number a0;
  let a1_u = (a1 * 2) % pow2 64 + carry0 in   
    lemma_get_number a1;
  let a2_u = (a2 * 2) % pow2 64 + carry1 in 
    lemma_get_number a2;
  let a3_u = (a3 * 2) % pow2 64 + carry2 in 
    lemma_get_number a3;

  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 128 = pow2 192);
  assert_norm (pow2 64 * pow2 192 = pow2 256)


#reset-options "--z3rlimit 500"
let shift_left_felem (a0, a1, a2, a3) =  
  let mask = u64 0x7fffffffffffffff in   
  let carry0 = gt a0 mask in 
  let carry1 = gt a1 mask in 
  let carry2 = gt a2 mask in 
  let carry3 = gt a3 mask in 

  let a0_updated = shift_carry a0 (u64 0) in 
  let a1_updated = shift_carry a1 carry0 in 
  let a2_updated = shift_carry a2 carry1 in 
  let a3_updated = shift_carry a3 carry2 in 

  assert_norm(pow2 64 * pow2 64 = pow2 128);
  assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);

  shift_left_lemma (uint_v a0) (uint_v a1) (uint_v a2) (uint_v a3); 
  assert(as_nat4 (a0, a1, a2, a3) * 2 = uint_v a0_updated + uint_v a1_updated * pow2 64 + uint_v a2_updated * pow2 128 + uint_v  a3_updated * pow2 192 + uint_v carry3 * pow2 256);
  assert_norm(uint_v a2_updated * pow2 64 * pow2 64 == uint_v a2_updated * pow2 128);
  assert_norm(uint_v a3_updated * pow2 64 * pow2 64 * pow2 64 == uint_v a3_updated * pow2 192);
  reduction_prime_2prime_with_carry carry3 a0_updated  a1_updated  a2_updated a3_updated


let upload_prime () = 
  assert_norm (as_nat4 (u64 (0xffffffffffffffff), u64 (0x00000000ffffffff), u64 (0), u64 (0xffffffff00000001))  == prime);
  (u64 (0xffffffffffffffff), u64 (0x00000000ffffffff), u64 (0), u64 (0xffffffff00000001)) 


let shift_256 (c0, c1, c2, c3)  = 
    assert_norm(pow2 64 * pow2 64 = pow2 128);
    assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 (5 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 * pow2 64 = pow2 (8 * 64));
    (u64(0), u64(0), u64 (0), u64 (0), c0, c1, c2, c3)


val lemma_wide: o: felem8 -> Lemma (wide_as_nat4 o =
  (let (o0, o1, o2, o3, o4, o5, o6, o7) = o in 
   v o0 + v o1 * pow2 64 +  v o2 * pow2 (64 * 2) + v o3 * pow2 (3 * 64) + 
   v o4 * pow2 (4 * 64) + v o5 * pow2 (5 * 64) +  v o6 * pow2 (6 * 64) + v o7 * pow2 (7 * 64)))

let lemma_wide o = 
    assert_norm(pow2 64 * pow2 64 = pow2 128);
    assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 (5 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
    ()

inline_for_extraction noextract
val add8: a: felem8 -> b: felem8 -> Pure (felem9)
  (requires True) 
  (ensures fun r ->True (*uint_v c <= 1 /\  wide_as_nat4 a + wide_as_nat4 b = wide_as_nat4 r + uint_v c * pow2 512) *) )

let add8  (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) = 
    assert_norm(pow2 64 * pow2 64 = pow2 128);
    assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 (5 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 * pow2 64 = pow2 512);
  let c3, (o0, o1, o2, o3) = add4 (a0, a1, a2, a3) (b0, b1, b2, b3) in 
  let o4, c4 = addcarry a4 b4 c3 in
  let o5, c5 = addcarry a5 b5 c4 in 
  let o6, c6 = addcarry a6 b6 c5 in 
  let o7, c7 = addcarry a7 b7 c6 in 
  (* let (o0, o1, o2, o3) = r in 

  assert(wide_as_nat4 (a0, a1, a2, a3, a4, a5, a6, a7)  + wide_as_nat4 (b0, b1, b2, b3, b4, b5, b6, b7) = 
   v o0 + v o1 * pow2 64 +  v o2 * pow2 (2 * 64) + v o3 * pow2 (3 * 64) + 
   v o4 * pow2 (4 * 64) + v o5 * pow2 (5 * 64) +  v o6 * pow2 (6 * 64) + v o7 * pow2 (7 * 64) + v c7 * pow2 512);
 *)
  (* let out = o0, o1, o2, o3, o4, o5, o6, o7 in  *)
  lemma_wide (o0, o1, o2, o3, o4, o5, o6, o7);
  (c7, o0, o1, o2, o3, o4, o5, o6, o7)

inline_for_extraction noextract
val add9: a : felem8 -> b: felem8 -> Pure (felem9)
  (requires True)
  (ensures fun r -> wide_as_nat4 a + wide_as_nat4 b = as_nat9 r)

let add9 (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) = 
    assert_norm(pow2 64 * pow2 64 = pow2 128);
    assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 (5 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 * pow2 64 = pow2 512);
  let c3, (o0, o1, o2, o3) = add4 (a0, a1, a2, a3) (b0, b1, b2, b3) in 
  let o4, c4 = addcarry a4 b4 c3 in
  let o5, c5 = addcarry a5 b5 c4 in 
  let o6, c6 = addcarry a6 b6 c5 in 
  let o7, c7 = addcarry a7 b7 c6 in 

  assert(wide_as_nat4 (a0, a1, a2, a3, a4, a5, a6, a7)  + wide_as_nat4 (b0, b1, b2, b3, b4, b5, b6, b7) = 
   v o0 + v o1 * pow2 64 +  v o2 * pow2 (2 * 64) + v o3 * pow2 (3 * 64) + 
   v o4 * pow2 (4 * 64) + v o5 * pow2 (5 * 64) +  v o6 * pow2 (6 * 64) + v o7 * pow2 (7 * 64) + v c7 * pow2 512);
  lemma_wide (o0, o1, o2, o3, o4, o5, o6, o7 );

  o0, o1, o2, o3, o4, o5, o6, o7,  c7


inline_for_extraction noextract
val add8_without_carry: a: felem8{wide_as_nat4 a < pow2 449} -> b: felem8 {wide_as_nat4 b < pow2 320} -> Tot (r: felem8 {wide_as_nat4 r = wide_as_nat4 a + wide_as_nat4 b})

let add8_without_carry (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) = 
  let (carry, r0, r1, r2, r3, r4, r5, r6, r7)  = add8 (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) in 
  assert_norm(pow2 320 + pow2 449 < pow2 512);   
  assert(uint_v carry = 0);
  (r0, r1, r2, r3, r4, r5, r6, r7)


inline_for_extraction noextract
val shortened_mul: a: felem4 -> b: uint64 -> Tot (r: felem8 {as_nat4 a * uint_v b = wide_as_nat4 r /\ wide_as_nat4 r < pow2 320})

let shortened_mul (a0, a1, a2, a3) b = 
  let (c, f0, f1, f2, f3) = mul1 (a0, a1, a2, a3) b in 
   assert_norm(pow2 64 * pow2 64 = pow2 128);
   assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
   assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 320);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
  f0, f1, f2, f3, c, (u64 0), (u64 0), u64(0)  


inline_for_extraction noextract
val mod_64: a: felem8 -> Tot (r: uint64 {wide_as_nat4 a % pow2 64 = uint_v r})

let mod_64 (a0, a1, a2, a3, a4, a5, a6, a7) =  a0

inline_for_extraction noextract
val shift_9: a: felem9 -> Tot (r: felem8 {as_nat9 a / pow2 64 = wide_as_nat4 r})

let shift_9 (a0, a1, a2, a3, a4, a5, a6, a7, a8) = 
  (a1, a2, a3, a4, a5, a6, a7, a8)

inline_for_extraction noextract
val shift_8: a: felem8 -> Tot (r: felem8 {wide_as_nat4 a / pow2 64 = wide_as_nat4 r})

let shift_8 (a0, a1, a2, a3, a4, a5, a6, a7) = 
  (a1, a2, a3, a4, a5, a6, a7, (u64 0))


#reset-options "--z3rlimit 1000"  
val lemma_less_than_primes : a: nat {a < prime} -> b: nat {b < prime} -> Lemma (ensures (
  let s = 64 in 
  let t = a * b in 

  let t1 = t % pow2 s in 
  let t2 = t1 * prime in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 
 
  let t = tU in 
  let t1 = t % pow2 s in 
  let t2 = t1 * prime in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 

  let t = tU in 
  let t1 = t % pow2 s in 
  let t2 = t1 * prime in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 

  let t = tU in 
  let t1 = t % pow2 s in  
  let t2 = t1 * prime in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 
  tU < 2 * prime))

let lemma_less_than_primes a b = 
  let s = 64 in 
  let t = a * b in 
  assert(t < prime * prime);

  let t1 = t % pow2 s in 
  let t2 = t1 * prime in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 
 
  let t = tU in 
  let t1 = t % pow2 s in 
  let t2 = t1 * prime in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 

  let t = tU in 
  let t1 = t % pow2 s in 
  let t2 = t1 * prime in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 

  let t = tU in 
  let t1 = t % pow2 s in  
  let t2 = t1 * prime in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 
  assert(tU < 2 * prime)

(*!*)
(* let  *)


val montgomery_multiplication_one_round_proof: t: felem8 {wide_as_nat4 t < pow2 449} -> 
  result: felem8 {wide_as_nat4 result = (wide_as_nat4 t + (wide_as_nat4 t % pow2 64) * prime) / pow2 64} ->
  co: nat{ co % prime == wide_as_nat4 t % prime} -> Lemma (
    wide_as_nat4 result % prime == co * modp_inv2 (pow2 64) % prime /\
    wide_as_nat4 result = (wide_as_nat4 t + (wide_as_nat4 t % pow2 64) * prime) / pow2 64 /\
    wide_as_nat4 result < pow2 449)

let montgomery_multiplication_one_round_proof t result co = 
  let primeU = upload_prime () in 
  let t1 = mod_64 t in 
  let t2 = shortened_mul primeU t1 in 
    assert_norm(pow2 256 * pow2 64 = pow2 320);
    assert(wide_as_nat4 t2 = uint_v t1 * prime);
  let t3 = add8_without_carry t t2 in 
    assert_norm (pow2 320 + pow2 449 < pow2 513);
  let result = shift_8 t3 in 
    lemma_div_lt (wide_as_nat4 t3) 513 64;
    mult_one_round (wide_as_nat4 t) co


inline_for_extraction noextract
val montgomery_multiplication_one_round: t: felem8{wide_as_nat4 t < pow2 449} -> 
  primeU: felem4 -> 
Tot (result: felem8 { wide_as_nat4 result = (wide_as_nat4 t + (wide_as_nat4 t % pow2 64) * prime) / pow2 64 /\wide_as_nat4 result < pow2 449})

let montgomery_multiplication_one_round (a0, a1, a2, a3, a4, a5, a6, a7) (prim0, prim1, prim2, prim3) = 
  let t1 = mod_64 (a0, a1, a2, a3, a4, a5, a6, a7) in 
  let (t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7) = shortened_mul (prim0, prim1, prim2, prim3) t1 in 
    assert_norm(pow2 256 * pow2 64 = pow2 320);
    assert(wide_as_nat4 (t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7) = uint_v t1 * prime);
  let (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7) = add8_without_carry (a0, a1, a2, a3, a4, a5, a6, a7) (t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7) in 
    assert_norm (pow2 320 + pow2 449 < pow2 513); 
    lemma_div_lt (wide_as_nat4 (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7)) 513 64;
  let (r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7)  = shift_8 (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7)  in 
    lemma_div_lt (wide_as_nat4 (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7)) 513 64;
  (r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7)


#reset-options "--z3refresh" 
let montgomery_multiplication (a0, a1, a2, a3) (b0, b1, b2, b3) = 
  let (prim0, prim1, prim2, prim3) = upload_prime () in 
  assert_norm(prime < pow2 256);
  assert_norm (pow2 256 * pow2 256 = pow2 512);
  assert_norm (pow2 320 + pow2 512 < pow2 513);
 
  border_felem4 (a0, a1, a2, a3) ;
  border_felem4 (b0, b1, b2, b3) ;
  lemma_mult_lt_sqr (as_nat4 (a0, a1, a2, a3)) (as_nat4 (b0, b1, b2, b3)) (pow2 256);
  
  let (t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7) = mul4 (a0, a1, a2, a3)  (b0, b1, b2, b3) in 
  let t1 = mod_64 (t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7) in 
  let (t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7) = shortened_mul (prim0, prim1, prim2, prim3) t1 in 
  let (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7, t3_8) = add9 (t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7) (t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7) in 
  let (st0, st1, st2, st3, st4, st5, st6, st7) = shift_9 (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7, t3_8) in  
    lemma_div_lt (as_nat9 (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7, t3_8)) 513 64;
    
    mult_one_round (wide_as_nat4 (t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7)) (as_nat4 (a0, a1, a2, a3) * as_nat4  (b0, b1, b2, b3) );
    lemma_mul_nat (as_nat4  (a0, a1, a2, a3)) (as_nat4  (b0, b1, b2, b3)) (modp_inv2 (pow2 64));

  let (st10, st11, st12, st13, st14, st15, st16, st17)  = montgomery_multiplication_one_round (st0, st1, st2, st3, st4, st5, st6, st7) (prim0, prim1, prim2, prim3) in
    montgomery_multiplication_one_round_proof (st0, st1, st2, st3, st4, st5, st6, st7)  (st10, st11, st12, st13, st14, st15, st16, st17) (as_nat4  (a0, a1, a2, a3) * as_nat4 (b0, b1, b2, b3) * modp_inv2 (pow2 64));
    lemma_mul_nat4 (as_nat4  (a0, a1, a2, a3)) (as_nat4 (b0, b1, b2, b3)) (modp_inv2 (pow2 64)) (modp_inv2(pow2 64));
  let (st20, st21, st22, st23, st24, st25, st26, st27) = montgomery_multiplication_one_round (st10, st11, st12, st13, st14, st15, st16, st17) (prim0, prim1, prim2, prim3) in 
    montgomery_multiplication_one_round_proof (st10, st11, st12, st13, st14, st15, st16, st17) (st20, st21, st22, st23, st24, st25, st26, st27) (as_nat4  (a0, a1, a2, a3) * as_nat4  (b0, b1, b2, b3) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64));
    lemma_mul_nat5 (as_nat4  (a0, a1, a2, a3)) (as_nat4 (b0, b1, b2, b3)) (modp_inv2 (pow2 64)) (modp_inv2 (pow2 64)) (modp_inv2 (pow2 64));
  let (st30, st31, st32, st33, st34, st35, st36, st37) = montgomery_multiplication_one_round (st20, st21, st22, st23, st24, st25, st26, st27) (prim0, prim1, prim2, prim3) in 
    montgomery_multiplication_one_round_proof (st20, st21, st22, st23, st24, st25, st26, st27) 
      (st30, st31, st32, st33, st34, st35, st36, st37)  (as_nat4 (a0, a1, a2, a3)* as_nat4 (b0, b1, b2, b3) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64));
    lemma_decrease_pow (as_nat4  (a0, a1, a2, a3) * as_nat4 (b0, b1, b2, b3));
    lemma_less_than_primes (as_nat4  (a0, a1, a2, a3)) (as_nat4 (b0, b1, b2, b3));
    assert(wide_as_nat4  (st30, st31, st32, st33, st34, st35, st36, st37) < 2 * prime);
    lemma_prime_as_wild_nat  (st30, st31, st32, st33, st34, st35, st36, st37);
  reduction_prime_2prime_with_carry st34 st30 st31 st32 st33


let cube_tuple (a0, a1, a2, a3) = 
  let (s0, s1, s2, s3) = montgomery_multiplication (a0, a1, a2, a3) (a0, a1, a2, a3) in 
  let (c0, c1, c2, c3) = montgomery_multiplication (s0, s1, s2, s3) (a0, a1, a2, a3) in 
    lemma_mul_nat (as_nat4 (a0, a1, a2, a3)) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256));
    lemma_mul_nat2   (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256));
    lemma_brackets ((as_nat4 (a0, a1, a2, a3) * as_nat4 (a0, a1, a2, a3) * modp_inv2(pow2 256)) % prime) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256));
    lemma_mod_mul_distr_l (as_nat4 (a0, a1, a2, a3) * as_nat4 (a0, a1, a2, a3) * modp_inv2(pow2 256)) (as_nat4 (a0, a1, a2, a3) * modp_inv2 (pow2 256)) prime;
    lemma_brackets5 (as_nat4 (a0, a1, a2, a3)) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256)) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256));
    lemma_distr_mult (as_nat4 (a0, a1, a2, a3)) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256)) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256));
  (c0, c1, c2, c3) 


let quatre_tuple (a0, a1, a2, a3) = 
  let (s0, s1, s2, s3) = montgomery_multiplication (a0, a1, a2, a3) (a0, a1, a2, a3) in 
  let (c0, c1, c2, c3) = montgomery_multiplication (s0, s1, s2, s3) (s0, s1, s2, s3) in 
   (*  lemma_brackets ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime) ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime) (modp_inv2 (pow2 256));
    lemma_mod_mul_distr_l (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) (((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime) * modp_inv2 (pow2 256)) prime;
    lemma_brackets (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime) (modp_inv2 (pow2 256));
    lemma_distr_mult3 (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime) (modp_inv2 (pow2 256));
    lemma_brackets_l (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) (modp_inv2 (pow2 256)) ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime);
    lemma_mod_mul_distr_r ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) * modp_inv2 (pow2 256)) (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) prime;
    lemma_brackets_l (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256))(modp_inv2 (pow2 256)) (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256));
    lemma_distr_mult3 (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) (modp_inv2 (pow2 256)) (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256));
    lemma_twice_brackets (as_nat4 a) (as_nat4 a) (modp_inv2 (pow2 256)) (as_nat4 a) (as_nat4 a) (modp_inv2 (pow2 256)) (modp_inv2 (pow2 256));
    lemma_distr_mult7  (as_nat4 a) (as_nat4 a) (modp_inv2 (pow2 256)) (as_nat4 a) (as_nat4 a) (modp_inv2 (pow2 256)) (modp_inv2 (pow2 256));
 *)  (c0, c1, c2, c3)

val lemma_three: a: nat -> Lemma (a * 2 + a == 3 * a)
let lemma_three a = ()

val lemma_four: a: nat -> Lemma ((a * 2) * 2 == 4 * a)
let lemma_four a = ()

val lemma_eight: a: nat -> Lemma  ((a * 4) * 2 == 8 * a)
let lemma_eight a = ()

val lemma_minus_three: a: nat -> Lemma (0 - 3 * a == (-3) * a)
let lemma_minus_three a = ()


let multByThree_tuple (a0, a1, a2, a3) = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
    let (m0, m1, m2, m3) = shift_left_felem (a0, a1, a2, a3) in 
    let (th0, th1, th2, th3) = felem_add (m0, m1, m2, m3) (a0, a1, a2, a3) in 
    lemma_mod_plus_distr_l (as_nat4 (a0, a1, a2, a3)  * 2) (as_nat4 (a0, a1, a2, a3) ) prime;
    lemma_three (as_nat4 (a0, a1, a2, a3) );
    (th0, th1, th2, th3) 


let multByFour_tuple (a0, a1, a2, a3) = 
  let (m0, m1, m2, m3) = shift_left_felem (a0, a1, a2, a3) in 
  let (th0, th1, th2, th3) = shift_left_felem (m0, m1, m2, m3) in 
    lemma_mod_mul_distr_l (as_nat4 (a0, a1, a2, a3) * 2) 2 prime;
    lemma_four (as_nat4 (a0, a1, a2, a3));
  (th0, th1, th2, th3)


let multByEight_tuple (a0, a1, a2, a3) = 
  let (m0, m1, m2, m3) = multByFour_tuple (a0, a1, a2, a3)  in 
  let  (th0, th1, th2, th3)  = shift_left_felem (m0, m1, m2, m3) in 
    lemma_mod_mul_distr_l (as_nat4 (a0, a1, a2, a3)  * 4) 2 prime;
    lemma_eight (as_nat4 (a0, a1, a2, a3) );
  (th0, th1, th2, th3) 


let multByMinusThree_tuple (a0, a1, a2, a3) = 
  let (th0, th1, th2, th3) = multByThree_tuple (a0, a1, a2, a3) in 
  (* let zero = (u64 (0), u64(0), u64(0), u64(0)) in  *)
    assert_norm (as_nat4 (u64 (0), u64(0), u64(0), u64(0))  = 0);
  let (c0, c1, c2, c3) = felem_sub (u64 (0), u64(0), u64(0), u64(0))  (th0, th1, th2, th3) in 
  lemma_mod_sub_distr 0 (as_nat4 (a0, a1, a2, a3) * 3) prime;
  lemma_minus_three (as_nat4 (a0, a1, a2, a3));
  (c0, c1, c2, c3)

 
(* takes felem4 and returns boolean *)
let isOne_tuple (a0, a1, a2, a3) = 
  let r0 = eq_mask a0 (u64 1) in 
  let r1 = eq_mask a1 (u64 0) in 
  let r2 = eq_mask a2 (u64 0) in 
  let r3 = eq_mask a3 (u64 0) in  
  let r01 = logand r0 r1 in 
    logand_lemma r0 r1;
  let r23 = logand r2 r3 in 
    lemma_log_and1 r2 r3;
  let r = logand r01 r23 in 
    lemma_log_and1 r01 r23;
  let f = eq_u64 r (u64 0xffffffffffffffff) in  
  f


let equalFelem (a_0, a_1, a_2, a_3) (b_0, b_1, b_2, b_3) = 
    let r_0 = eq_mask a_0 b_0 in 
      eq_mask_lemma a_0 b_0;
    let r_1 = eq_mask a_1 b_1 in 
      eq_mask_lemma a_1 b_1;
    let r_2 = eq_mask a_2 b_2 in 
      eq_mask_lemma a_2 b_2;
    let r_3 = eq_mask a_3 b_3 in 
      eq_mask_lemma a_3 b_3;
    let r01 = logand r_0 r_1 in 
      logand_lemma r_0 r_1;
    let r23 = logand r_2 r_3 in 
      logand_lemma r_2 r_3;
    let r = logand r01 r23 in 
      logand_lemma r01 r23;
      lemma_equality (a_0, a_1, a_2, a_3) (b_0, b_1, b_2, b_3) ; 
    r


let isZero_tuple_u (a0, a1, a2, a3)  = 
  let r0 = eq_mask a0 (u64 0) in 
  let r1 = eq_mask a1 (u64 0) in 
  let r2 = eq_mask a2 (u64 0) in 
  let r3 = eq_mask a3 (u64 0) in 
  let r01 = logand r0 r1 in 
     lemma_log_and1 r0 r1;
  let r23 = logand r2 r3 in 
     lemma_log_and1 r2 r3;
  let r = logand r01 r23 in 
   lemma_log_and1 r01 r23;
      r
  

let isZero_tuple_b (a0, a1, a2, a3)  = 
  assert_norm (0xffffffffffffffff = pow2 64 - 1);
  let r0 = eq_mask a0 (u64 0) in 
  let r1 = eq_mask a1 (u64 0) in 
  let r2 = eq_mask a2 (u64 0) in 
  let r3 = eq_mask a3 (u64 0) in 
  let r01 = logand r0 r1 in 
    lemma_log_and1 r0 r1;
  let r23 = logand r2 r3 in 
    lemma_log_and1 r2 r3;
  let r = logand r01 r23 in 
    lemma_log_and1 r01 r23;    
  let f = eq_u64 r (u64 0xffffffffffffffff) in  
   f
   