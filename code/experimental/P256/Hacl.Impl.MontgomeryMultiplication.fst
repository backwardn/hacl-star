module Hacl.Impl.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer


open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Impl.LowLevel
open Hacl.Spec.P256.Basic

open FStar.Mul

#reset-options "--z3refresh --z3rlimit 200"

val load_buffer8: 
  a0: uint64 -> a1: uint64 -> 
  a2: uint64 -> a3: uint64 -> 
  a4: uint64 -> a5: uint64 -> 
  a6: uint64 -> a7: uint64 ->  
  o: lbuffer uint64 (size 8) -> 
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ 
      (
	wide_as_nat h1 o == wide_as_nat4 (a0, a1, a2, a3, a4, a5, a6, a7)
      )
)

let load_buffer8 a0 a1 a2 a3 a4 a5 a6 a7  o = 
    let h0 = ST.get() in 
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (7 * 64));

  upd o (size 0) a0;
  upd o (size 1) a1;
  upd o (size 2) a2;
  upd o (size 3) a3;
  
  upd o (size 4) a4;
  upd o (size 5) a5;
  upd o (size 6) a6;
  upd o (size 7) a7;
  let h1 = ST.get() in 
    assert(felem_seq_as_nat_8 (as_seq h1 o) 
      ==   uint_v a0 + 
  uint_v a1 * pow2 64 + 
  uint_v a2 * pow2 128 + 
  uint_v a3 * pow2 192 + 
  uint_v a4 * pow2 256 + 
  uint_v a5 * pow2 (5 * 64) + 
  uint_v a6 * pow2 (6 * 64) + 
  uint_v a7 * pow2 (7 * 64));
  assert(modifies1 o h0 h1)
  
  

val mul: f1: felem -> r: felem -> out: widefelem
  -> Stack unit
    (requires fun h -> live h out /\ live h f1 /\ live h r)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      wide_as_nat h1 out == as_nat h0 f1 * as_nat h0 r)
      
[@ CInline]
let mul f1 r out =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in

  let r0 = r.(0ul) in
  let r1 = r.(1ul) in
  let r2 = r.(2ul) in
  let r3 = r.(3ul) in
  let (o0, o1, o2, o3, o4, o5, o6, o7) = mul4 (f10, f11, f12, f13) (r0, r1, r2, r3) in
    assert(wide_as_nat4  (o0, o1, o2, o3, o4, o5, o6, o7) == as_nat4 (f10, f11, f12, f13) * as_nat4 (r0, r1, r2, r3));
  load_buffer8 o0 o1 o2 o3 o4 o5 o6 o7 out


assume val mod64: a: widefelem -> Stack uint64 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

assume val shortened_mul: a: felem -> b: uint64 -> result: widefelem -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


assume val add8_without_carry: t: widefelem -> t1: widefelem -> result: widefelem -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

assume val shift8: t: widefelem -> t1: widefelem -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


assume val montgomery_multiplication_round: t: widefelem -> prime: felem -> round: widefelem -> 
  Stack unit 
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)

assume val reduction_prime_2_prime_with_carry:  round3: widefelem -> result: felem -> 
  Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)


val montgomery_multiplication_test: a: felem -> b: felem ->primeBuffer: felem -> result: felem -> 
  Stack unit 
    (requires fun h -> live h a /\ live h b /\ live h result /\ as_nat h a < as_nat h primeBuffer /\
    as_nat h b < as_nat h primeBuffer)
    (ensures fun h0 _ h1 -> True)


let montgomery_multiplication_test a b primeBuffer result =
  push_frame();
    let t = create (size 8) (u64 0) in 
    let t2 = create (size 8) (u64 0) in 
    let t3 = create (size 8) (u64 0) in 
    let round1 = create (size 8) (u64 0) in 
    let round2 = create (size 8) (u64 0) in 
    let round3 = create (size 8) (u64 0) in 
    
  mul a b t;
  let t1 = mod64 t in 
  shortened_mul primeBuffer t1 t2;
  add8_without_carry t t2 t3;
  shift8 t3 t3;

  montgomery_multiplication_round t3 prime round1;
  montgomery_multiplication_round round1 prime round2;
  montgomery_multiplication_round round2 prime round3;

  reduction_prime_2_prime_with_carry round3 result;
    pop_frame()
