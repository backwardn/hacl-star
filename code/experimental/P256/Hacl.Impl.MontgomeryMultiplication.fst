module Hacl.Impl.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Impl.LowLevel
open Hacl.Spec.P256.Basic
open Hacl.Spec.P256.Core

open FStar.Mul

let prime:pos = 115792089210356248762697446949407573529996955224135760342422259061068512044369

#reset-options "--z3refresh --z3rlimit 200"
inline_for_extraction noextract
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


val mod64: a: widefelem -> Stack uint64 
  (requires fun h -> live h a) 
  (ensures fun h0 r h1 ->modifies0 h0 h1 /\  wide_as_nat h1 a % pow2 64 = uint_v r)

let mod64 a = 
  index a (size 0)


inline_for_extraction noextract
val shortened_mul_tuple: a: felem4 -> b: uint64 -> Tot (r: felem8 {as_nat4 a * uint_v b = wide_as_nat4 r /\ wide_as_nat4 r < pow2 320})

let shortened_mul_tuple (a0, a1, a2, a3) b = 
  let (c, (f0, f1, f2, f3)) = mul1 (a0, a1, a2, a3) b in 
   assert_norm(pow2 64 * pow2 64 = pow2 128);
   assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
   assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 320);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
  f0, f1, f2, f3, c, (u64 0), (u64 0), u64(0)  


val shortened_mul: a: felem -> b: uint64 -> result: widefelem -> Stack unit
  (requires fun h -> live h a /\ live h result)
  (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ 
    as_nat h0 a * uint_v b = wide_as_nat h1 result /\ 
    wide_as_nat h1 result < pow2 320)

let shortened_mul a b result = 
  let a0 = index a (size 0) in 
  let a1 = index a (size 1) in 
  let a2 = index a (size 2) in 
  let a3 = index a (size 3) in 
  let (f0, f1, f2, f3, f4, f5, f6, f7) = shortened_mul_tuple (a0, a1, a2, a3) b in 
  load_buffer8 f0 f1 f2 f3 f4 f5 f6 f7 result

inline_for_extraction noextract
val add8_without_carry:
  a: felem8 {wide_as_nat4 a < prime * prime} -> 
  b: felem8 {wide_as_nat4 b < pow2 320}  -> Tot (r:felem8 {wide_as_nat4 r = wide_as_nat4 a + wide_as_nat4 b})


let add8_without_carry (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) = 
  let (carry, r0, r1, r2, r3, r4, r5, r6, r7)  = add8 (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) in 
  assert_norm (pow2 320 +  prime * prime  < pow2 512);
  assert(uint_v carry = 0);
  (r0, r1, r2, r3, r4, r5, r6, r7)


val add8_without_carry1:  t: widefelem -> t1: widefelem -> result: widefelem  -> Stack unit
  (requires fun h -> live h t /\ live h t1 /\ live h result /\ wide_as_nat h t1 < pow2 320 /\
    wide_as_nat h t <  prime * prime  )
  (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\  wide_as_nat h1 result = wide_as_nat h0 t + wide_as_nat h0 t1)

let add8_without_carry1 t r result  = 
  let t0 = index t (size 0) in 
  let t1 = index t (size 1) in 
  let t2 = index t (size 2) in 
  let t3 = index t (size 3) in 
  let t4 = index t (size 4) in 
  let t5 = index t (size 5) in 
  let t6 = index t (size 6) in 
  let t7 = index t (size 7) in 

  let r0 = index r (size 0) in 
  let r1 = index r (size 1) in 
  let r2 = index r (size 2) in 
  let r3 = index r (size 3) in 
  let r4 = index r (size 4) in 
  let r5 = index r (size 5) in 
  let r6 = index r (size 6) in  
  let r7 = index r (size 7) in 

  let (r0, r1, r2, r3, r4, r5, r6, r7) = add8_without_carry (t0, t1, t2, t3, t4, t5, t6, t7) (r0, r1, r2, r3, r4, r5, r6, r7) in 
  load_buffer8 r0 r1 r2 r3 r4 r5 r6 r7 result


val shift8: t: widefelem -> t1: widefelem -> Stack unit 
  (requires fun h -> live h t /\ live h t1 /\ eq_or_disjoint t t1)
  (ensures fun h0 _ h1 -> modifies1 t1 h0 h1 /\ wide_as_nat h0 t / pow2 64 = wide_as_nat h1 t1)

let shift8 t out = 
  let t1 = index t (size 1) in 
  let t2 = index t (size 2) in 
  let t3 = index t (size 3) in 
  let t4 = index t (size 4) in 
  let t5 = index t (size 5) in 
  let t6 = index t (size 6) in 
  let t7 = index t (size 7) in 

  upd out (size 0) t1;
  upd out (size 1) t2;
  upd out (size 2) t3;
  upd out (size 3) t4;
  upd out (size 4) t5;
  upd out (size 5) t6;
  upd out (size 6) t7;
  upd out (size 7) (u64 0)



private let add_l (a: nat) (b: nat) (c: nat) (d: nat) : Lemma (requires a < c /\ b < d) (ensures (a + b < c + d)) = ()
private let mul_lemma_1 (a: nat) (c: nat) (b: pos) : Lemma (requires (a < c)) (ensures (a * b < c * b)) = ()
private let mul_lemma_ (a: nat) (b: nat) (c: nat) : Lemma (requires (a < c /\ b < c)) (ensures (a * b < c * c)) = ()

private let add_l2 (a: int) (b: nat) (c: int) (d: nat) : Lemma (requires a <= c /\ b < d) (ensures (a + b < c + d)) = ()

private let div_lemma (a: int) (b: pos) (c: nat) : Lemma (requires a < b) (ensures a / b <= c / b) = ()


val lemma_montgomery_mult_1: prime : pos {prime = 115792089210356248762697446949407573529996955224135760342422259061068512044369} -> 
t : int  -> k0:nat {k0 = modp_inv2 (-prime) (pow2 64)} -> r: nat {t <= r} -> 
Lemma (ensures (t + (((t % pow2 64) * k0) % pow2 64 * prime)) / pow2 64 <= (pow2 64 * prime + r) / pow2 64)


let lemma_montgomery_mult_1 prime t k0 r = 
  let t1 = t % pow2 64 in 
    assert(t1 < pow2 64);
  let y = (t1 * k0) % pow2 64 in 
    assert(y < pow2 64);
  let t2 = y * prime in 
    mul_lemma_1 y (pow2 64) prime;
    assert(t2 < pow2 64 * prime); 
  let t3 = t + t2 in
    add_l2 t t2 r (pow2 64 * prime); 
    assert(t3 < (r + pow2 64 * prime));
  let t = t3 / pow2 64 in 
    assert_norm (pow2 64 * prime + r > 0); 
    div_lemma t3 (r + pow2 64 * prime) (pow2 64);
    assert(t <= (pow2 64 * prime + r) / pow2 64); 
    let r = (pow2 64 * prime + r) / pow2 64 in 
    assert(t <= r)




#reset-options "--z3refresh --z3rlimit 300"
val lemma_montgomery_mult_result_less_than_prime: 
  a: nat{a < prime} -> b: nat{b < prime} -> k0:nat {k0 = modp_inv2 (-prime) (pow2 64)} -> 
  Lemma
  (ensures (  
    let t = a * b in 
    let s = 64 in 
  
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * prime in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
  
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * prime in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
  
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * prime in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
    
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * prime in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
    t < 2 * prime))




let lemma_montgomery_mult_result_less_than_prime a b k0 = 
  let t = a * b in 
  let s = 64 in 
    mul_lemma_ a b prime;

  let r = prime * prime + 1 in 
      assert(t <= r); 
      assert(t < prime * prime);

  let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * prime in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  lemma_montgomery_mult_1 prime t k0 r; 

  let t = tU in 
  let r = (pow2 64 * prime + r) / pow2 64 in 
    let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * prime in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  
  assert(t <= r); 
  lemma_montgomery_mult_1 prime t k0 r; 

   let t = tU in 
   let r = (pow2 64 * prime + r) / pow2 64 in 
    
    let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * prime in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  lemma_montgomery_mult_1 prime t k0 r; 

  let r = (pow2 64 * prime + r) / pow2 64 in 
  let t = tU in 

    let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * prime in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  lemma_montgomery_mult_1 prime t k0 r; 
  
  let r = (pow2 64 * prime + r) / pow2 64 in 
  assert(tU <= r);
  assert(tU <=  (pow2 64 * prime +  (pow2 64 * prime +  (pow2 64 * prime +  (pow2 64 * prime +  prime * prime + 1) / pow2 64) / pow2 64) / pow2 64) / pow2 64);
  assert_norm ((pow2 64 * prime +  (pow2 64 * prime +  (pow2 64 * prime +  (pow2 64 * prime +  prime * prime + 1) / pow2 64) / pow2 64) / pow2 64) / pow2 64 < 2 * prime);
  assert(tU < 2 * prime)



val montgomery_multiplication_one_round_proof: t: int ->k0: int ->  round: nat {round = (t + prime * (k0 * (t % pow2 64)) % pow2 64) / pow2 64} -> co: nat {co % prime = t % prime} -> 
  Lemma (round  % prime == co * (modp_inv2 (pow2 64) prime) % prime )

let montgomery_multiplication_one_round_proof t k0 round co = 
  let round0 = (t + prime * (k0 * (t % pow2 64) % pow2 64)) in 
  modulo_addition_lemma t prime (k0 * (t % pow2 64) % pow2 64);
  assert(round0 % prime == co % prime)



val montgomery_multiplication_round: t: widefelem ->  round: widefelem -> k0: felem -> primeBuffer: lbuffer uint64 (size 4)  ->
  Stack unit 
    (requires fun h -> live h t /\ live h round /\ live h k0 /\ live h primeBuffer /\ as_nat h primeBuffer == prime /\
      wide_as_nat h t < prime * prime)
    (ensures fun h0 _ h1 -> modifies1 round h0 h1 /\ wide_as_nat h1 round = (wide_as_nat h0 t + prime * ((as_nat h0 k0) * (wide_as_nat h0 t % pow2 64) % pow2 64) ) / pow2 64
    )


let montgomery_multiplication_round t round k0 primeBuffer = 
  push_frame(); 
    let h0 = ST.get() in 
    let yBuffer = create (size 8) (u64 0) in 
    let t2 = create (size 8) (u64 0) in 
    let t3 = create (size 8) (u64 0) in 
    let t1 = mod64 t in 
    shortened_mul k0 t1 yBuffer; 
      let h1 = ST.get() in 
      assert(wide_as_nat h1 yBuffer < pow2 320);
    let y = mod64 yBuffer in 
    shortened_mul primeBuffer y t2;
      let h2 = ST.get() in 
    add8_without_carry1 t t2 t3;
      let h3 = ST.get() in 
    shift8 t3 round;
      let h4 = ST.get() in 

  pop_frame()


(*


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
  add8_without_carry1 t t2 t3;
  shift8 t3 t3;

  montgomery_multiplication_round t3 prime round1;
  montgomery_multiplication_round round1 prime round2;
  montgomery_multiplication_round round2 prime round3;

  reduction_prime_2_prime_with_carry round3 result;
    pop_frame()
