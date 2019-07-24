module Hacl.Spec.P256.Lemmas

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.P256.Basic

open FStar.Mul

open Hacl.Spec.P256.Definitions

assume val log_and: a: uint64 -> b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} -> 
Lemma (if uint_v b = 0 then uint_v (logand a b) == 0 else uint_v (logand a b) == uint_v a)

assume val log_or: a: uint64 -> b: uint64 {uint_v b == 0 \/ uint_v a == 0} -> 
Lemma (if uint_v b = 0 then uint_v (logor a b) == uint_v a else uint_v (logor a b) == uint_v b)

assume val log_not_lemma: b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} -> 
Lemma(if uint_v b = 0 then uint_v (lognot (b)) == pow2 64 -1 else uint_v (lognot b) == 0)


val lemma_nat_4: f: felem4 -> Lemma (as_nat4 f < pow2 256)

let lemma_nat_4 f = 
  let (s0, s1, s2, s3) = f in 
  let r_n = as_nat4 f in 
  let r = uint_v s0 + uint_v s1 * pow2 64 + uint_v s2 * pow2 64 * pow2 64 + 
  uint_v s3 * pow2 64 * pow2 64 * pow2 64 in 
  assert(r_n == r);
  assert_norm(r < pow2 256)


val lemma_enough_to_carry: a: felem4 -> b: felem4 -> Lemma (
  if as_nat4 b >= (pow2 256 - as_nat4 a) then 
    let (c, r) = add4 a b in 
    uint_v c == 1
    else True)
    
let lemma_enough_to_carry a b = 
 if as_nat4 b >= (pow2 256 - as_nat4 a) then begin
  let (c, r) = add4 a b in 
    lemma_nat_4 r
  end
  else
  ()


let ( +% ) a b = (a + b) % prime
let ( -% ) a b = (a - b) % prime
let ( *% ) a b = (a * b) % prime


val ( **% ) : e: nat -> n: nat{n > 0} -> Tot (r: nat) (decreases n)

let rec ( **% ) e n =
  if n = 1 then e
  else
    if n % 2 = 0 then 
    begin
     	(e *% e) **% (n / 2)
    end
    else e *% ((e *% e) **% ((n-1)/2))


let modp_inv (x: nat {x < prime}) : Tot (r: nat{r < prime}) = 
	(x **% (prime - 2)) % prime


let modp_inv2 (x: nat) : Tot (r: nat {r < prime}) = 
  assert_norm (prime > 0);
  let r = x % prime in 
  modp_inv r


#reset-options "--max_fuel 0 --z3rlimit 100" 


val modulo_distributivity_mult: a: int -> b: int -> c: pos -> Lemma ((a * b) % c = ((a % c) * (b % c)) % c)

let modulo_distributivity_mult a b c = 
  lemma_mod_mul_distr_l a b c;
  lemma_mod_mul_distr_r (a%c) b c


val pow_plus: a: nat -> b: nat -> c: nat -> Lemma (ensures (pow a b * pow a c = pow a (b +c)))
(decreases b)

let rec pow_plus a b c = 
  match b with 
  | 0 -> assert_norm (pow a 0 = 1)
  | _ -> pow_plus a (b -1) c; 
    assert_norm(pow a (b - 1) * a = pow a b)


val power_distributivity: a: nat -> b: nat -> c: pos -> Lemma ((pow (a % c) b) % c = (pow a b) % c)

let rec power_distributivity a b c =
   match b with 
   | 0 -> ()
   | _ -> 
     power_distributivity a (b - 1) c; 
     modulo_distributivity_mult (pow a (b -1)) a c;
     lemma_mod_twice a c;
     modulo_distributivity_mult (pow (a % c) (b -1)) (a % c) c


val power_mult: a: nat -> b: nat -> c: nat -> Lemma (pow (pow a b) c == pow a (b * c))

let rec power_mult a b c = 
  match c with 
  |0 -> assert_norm(pow a 0 = 1); assert(pow (pow a b) 0  = 1)
  |_ ->  power_mult a b (c -1); pow_plus a (b * (c -1)) b


let modp_inv2_pow (x: nat) : Tot (r: nat {r < prime}) = 
   power_distributivity x (prime - 2) prime;
   pow x (prime - 2) % prime
  

val modulo_distributivity_mult_last_two: a: int -> b: int -> c: int -> d: int -> e: int -> f: pos -> 
Lemma ((a * b * c * d * e) % f = (a * b * c * ((d * e) % f)) % f)

let modulo_distributivity_mult_last_two a b c d e f = admit()


#reset-options "--max_fuel 0 --z3rlimit 100" 

val lemma_mod_twice : a:int -> p:pos -> Lemma ((a % p) % p == a % p)
let lemma_mod_twice a p = lemma_mod_mod (a % p) a p

val lemma_multiplication_to_same_number: a: nat -> b: nat ->c: nat ->  
  Lemma (requires (a % prime = b % prime)) (ensures ((a * c) % prime = (b * c) % prime))

let lemma_multiplication_to_same_number a b c = 
  lemma_mod_mul_distr_l a c prime;
  lemma_mod_mul_distr_l b c prime

val lemma_division_is_multiplication: t3: nat{ exists (k: nat) . k * pow2 64 = t3} -> Lemma (ensures (t3 * modp_inv2 (pow2 64) % prime = (t3 / pow2 64) % prime))

let lemma_division_is_multiplication t3 =  
  let t_new = t3 * modp_inv2 (pow2 64) % prime in 
  let remainder = t3 / pow2 64 in 
  assert_norm(modp_inv2 (pow2 64) * pow2 64 % prime = 1);
  modulo_distributivity_mult remainder (modp_inv2 (pow2 64) * pow2 64) prime;
  lemma_mod_twice remainder prime


val mult_one_round: t: nat -> co: nat{t % prime == co% prime}  -> Lemma
(requires True)
(ensures (let result = (t + (t % pow2 64) * prime) / pow2 64 % prime in result == (co * modp_inv2 (pow2 64)) % prime))

let mult_one_round t co = 
    let t1 = t % pow2 64 in 
    let t2 = t1 * prime in 
    let t3 = t + t2 in 
      assert(t3 % prime = co % prime);
    let t = t3 / pow2 64 in 
      assert(let rem = t3/ pow2 64 in rem * pow2 64 = t3);
      assert(exists (k: nat). k * pow2 64 = t3);
      lemma_division_is_multiplication t3;
      lemma_multiplication_to_same_number t3 co (modp_inv2 (pow2 64))


val lemma_decrease_pow: a: nat -> Lemma (ensures (a * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64))  % prime == (a * modp_inv2 (pow2 256)) % prime) 

let lemma_decrease_pow a = 
  assert_norm(modp_inv2 (pow2 64) = 6277101733925179126845168871924920046849447032244165148672);
  assert_norm(pow2 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936);
  assert_norm(modp_inv2 (pow2 256) =115792089183396302114378112356516095823261736990586219612555396166510339686400 );
  assert((modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64))% prime  = (modp_inv2 (pow2 256)) % prime);

  lemma_mod_mul_distr_r a (modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64)) prime;
  lemma_mod_mul_distr_r a (modp_inv2 (pow2 256)) prime



val lemma_brackets : a: int -> b: int -> c: int -> Lemma (a * b * c = a * (b * c))

let lemma_brackets a b c = ()

val lemma_brackets_l: a: int -> b: int -> c: int -> Lemma (a * b * c = (a * b) * c)

let lemma_brackets_l a b c = ()

val lemma_brackets1: a: int -> b: int -> c: int -> Lemma (a * (b * c) = b * (a * c))

let lemma_brackets1 a b c = ()

val lemma_brackets5: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e = a * b * c * (d * e))

let lemma_brackets5 a b c d e = ()

val lemma_brackets5_twice: a: int -> b: int -> c: int -> d: int -> e: int -> Lemma (a * b * c * d * e = (a * d) * (b * e) * c)

let lemma_brackets5_twice a b c d e = admit()

val lemma_brackets7: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> Lemma (a * b * c * d * e * f * g = a * b * c * d * e * (f * g))

let lemma_brackets7 a b c d e f g = admit()


val lemma_brackets7_twice: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> Lemma (a * b * c * d * e * f * g = (a * e) * (b * f) * (c * g) * d)

let lemma_brackets7_twice a b c d e f g = admit()


val lemma_distr_mult3: a: int -> b: int -> c: int -> Lemma (a * b * c = a * c * b)

let lemma_distr_mult3 a b c = ()

val lemma_distr_mult : a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e = a * b * d * c * e) 

let lemma_distr_mult a b c d e = ()

val lemma_twice_brackets: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> h: int-> Lemma 
  ((a * b * c) * (d * e * f) * h = a * b * c * d * e * f * h)

let lemma_twice_brackets a b c d e f h = () 

val lemma_distr_mult7: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> h: int-> Lemma 
  ( a * b * c * d * e * f * h = a * b * d * e * f * h * c)


val lemma_prime_as_wild_nat: a: felem8{wide_as_nat4 a < 2* prime} -> Lemma (let (t0, t1, t2, t3, t4, t5, t6, t7) = a in 
  uint_v t7 = 0 /\ uint_v t6 = 0 /\ uint_v t5 = 0 /\ (uint_v t4 = 0 \/ uint_v t4 = 1) /\
  as_nat4 (t0, t1, t2, t3) + uint_v t4 * pow2 256 = wide_as_nat4 a)

let lemma_prime_as_wild_nat a =
   assert_norm(pow2 64 * pow2 64 = pow2 128);
   assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
   assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 320);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64))
  

val lemma_mul_nat2: a: nat -> b: nat -> Lemma (a * b >= 0)
let lemma_mul_nat2 a b = ()

val lemma_mul_nat: a:nat -> b:nat -> c: nat -> Lemma (a * b * c >= 0)
let lemma_mul_nat a b c = ()

val lemma_mul_nat4: a:nat -> b:nat -> c: nat -> d: nat -> Lemma (a * b * c * d >= 0)
let lemma_mul_nat4 a b c d = ()

val lemma_mul_nat5: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e >= 0)
let lemma_mul_nat5 a b c d e = ()



val modulo_distributivity_mult2: a: int -> b: int -> c: int -> d: pos -> Lemma (((a % d) * (b % d) * c) % d = (a * b * c)% d)

let modulo_distributivity_mult2 a b c d = 
  let start = ((a % d) * (b % d) * c) % d in 
  lemma_mod_mul_distr_l a ((b % d) * c) d;
  lemma_distr_mult3 a (b % d) c;
  lemma_mod_mul_distr_r (a * c) b d

assume val lemma_minus_distr (a: int) (b: int): Lemma ((a % prime - b % prime) % prime = (a - b)%prime)


val lemma_multiplication_not_mod_prime: a: nat{a < prime} -> b: nat {b > 0 /\ b % prime <> 0} -> 
  Lemma ((a * b) % prime == 0 <==> a == 0)

let lemma_multiplication_not_mod_prime a b = admit()

(*If k a ≡ k b (mod n) and k is coprime with n, then a ≡ b (mod n) *)

val lemma_modular_multiplication_p256: a: nat{a < prime} -> b: nat{b < prime} -> 
  Lemma 
  (a * modp_inv2 (pow2 256) % prime = b * modp_inv2 (pow2 256) % prime  ==> a == b)

let lemma_modular_multiplication_p256 a b = admit()



val lemma_mod_sub_distr (a:int) (b:int) (n:pos) : Lemma ((a - b % n) % n = (a - b) % n)

let lemma_mod_sub_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  distributivity_sub_left 0 (b / n) n;
  // (a - b) % n == (a - (b % n) - (b / n) * n) % n
  lemma_mod_plus (a - (b % n)) (-(b / n)) n


val lemma_mod_add_distr (a:int) (b:int) (n:pos) : Lemma ((a + b % n) % n = (a + b) % n)
let lemma_mod_add_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  // (a + b) % n == (a + (b % n) + (b / n) * n) % n
  lemma_mod_plus (a + (b % n)) (b / n) n

val lemma_log_and1: a: uint64 {v a = 0 \/ v a = maxint U64} ->
  b: uint64 {v b = 0 \/ v b = maxint U64}  -> 
  Lemma (uint_v a = pow2 64 - 1 && uint_v b = pow2 64 - 1 <==> uint_v (logand a b) == pow2 64 - 1)

let lemma_log_and1 a b = 
  logand_lemma a b


val lemma_xor_copy_cond: a: uint64 -> b: uint64 -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 -1} ->
  Lemma(let r = logxor a (logand mask (logxor a b)) in 
  if uint_v mask = pow2 64 - 1 then r == b else r == a)

let lemma_xor_copy_cond a b mask = 
  let fst = logxor a b in 
  let snd = logand mask fst in 
    logand_lemma mask fst;
  let thrd = logxor a snd in    
    logxor_lemma a snd;
    logxor_lemma a b


val lognot_lemma: #t:inttype{~(U1? t)} -> a:uint_t t SEC -> Lemma
  (requires v a = 0 \/ v a = maxint t)
  (ensures (if v a = 0 then v (lognot a) == maxint t else v (lognot a) == 0)) 


val lemma_equality: a: felem4 -> b: felem4 -> Lemma
    (
      let (a_0, a_1, a_2, a_3) = a in 
      let (b_0, b_1, b_2, b_3) = b in 

      if  (uint_v a_0 = uint_v b_0 && uint_v a_1 = uint_v b_1 && uint_v a_2 = uint_v b_2 && uint_v a_3 = uint_v b_3) then as_nat4 a == as_nat4 b else as_nat4 a <> as_nat4 b)

let lemma_equality a b = ()



assume val neq_mask_lemma: #t:inttype -> a:uint_t t SEC -> b:uint_t t SEC -> Lemma
  (requires True)
  (ensures  (v a <> v b ==> v (neq_mask a b) == maxint t) /\
            (v a == v b ==> v (neq_mask a b) == 0))


val cmovznz4_lemma: cin: uint64 -> x: uint64 -> y: uint64 -> Lemma (
  let mask = neq_mask cin (u64 0) in 
  let r = logor (logand y mask) (logand x (lognot mask)) in 
  if uint_v cin = 0 then uint_v r == uint_v x else uint_v r == uint_v y)

let cmovznz4_lemma cin x y = 
  let x2 = neq_mask cin (u64 0) in 
      neq_mask_lemma cin (u64 0);
  let x3 = logor (logand y x2) (logand x (lognot x2)) in
  let ln = lognot (neq_mask cin (u64 0)) in 
    log_and y x2; 
    log_not_lemma x2;
    log_and x ln;
    log_or (logand y x2) (logand x (lognot (x2)))



val lemma_equ_felem: a: nat{ a < pow2 64} -> b: nat {b < pow2 64} -> c: nat {c < pow2 64} -> d: nat {d < pow2 64} ->
   a1: nat{a1 < pow2 64} -> b1: nat {b1 < pow2 64} -> c1: nat {c1 < pow2 64} -> d1: nat {d1 < pow2 64} ->
  Lemma (requires (
    a + b * pow2 64 + c * pow2 64 * pow2 64 + d *  pow2 64 * pow2 64 * pow2 64 == 
    a1 + b1 * pow2 64 + c1 * pow2 64 * pow2 64  + d1 *  pow2 64 * pow2 64 * pow2 64))
  (ensures (a == a1 /\ b == b1 /\ c == c1 /\ d == d1))
  
let lemma_equ_felem a b c d  a1 b1 c1 d1  = 
  assert(a = a1 + b1 * pow2 64 + c1 * pow2 128 + d1 * pow2 192 -  b * pow2 64 - c * pow2 128 - d * pow2 192);
  assert(a == a1);
  assert(b == b1);
  assert(c == c1);
  assert(d == d1)


val lemma_eq_funct: a: felem_seq -> b: felem_seq -> Lemma
   (requires (felem_seq_as_nat a == felem_seq_as_nat b))
   (ensures (a == b))

let lemma_eq_funct a b = 
  let a_seq = felem_seq_as_nat a in 
  let b_seq = felem_seq_as_nat b in 

  
  let a0 = Lib.Sequence.index a 0 in 
  let a1 =  Lib.Sequence.index a 1 in 
  let a2 =  Lib.Sequence.index  a 2 in 
  let a3 =  Lib.Sequence.index a 3 in 

  let b0 = Lib.Sequence.index b 0 in 
  let b1 = Lib.Sequence.index b 1 in 
  let b2 = Lib.Sequence.index b 2 in 
  let b3 = Lib.Sequence.index b 3 in 

  assert(uint_v a0 < pow2 64);
  assert(uint_v b0 < pow2 64);
  
  assert(uint_v a0 < pow2 64);
  assert(uint_v b0 < pow2 64);

  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  
  assert(
  uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 128 + uint_v a3 * pow2 192 == 
  uint_v b0 + uint_v b1 * pow2 64 + uint_v b2 * pow2 128 + uint_v b3 * pow2 192);

  lemma_equ_felem (uint_v a0) (uint_v a1) (uint_v a2) (uint_v a3) (uint_v b0) (uint_v b1) (uint_v b2) (uint_v b3);

  assert(Lib.Sequence.index a 0 == Lib.Sequence.index b 0);
  assert(Lib.Sequence.index a 1 == Lib.Sequence.index b 1);
  assert(Lib.Sequence.index a 2 == Lib.Sequence.index b 2);
  assert(Lib.Sequence.index a 3 == Lib.Sequence.index b 3);  

  assert(Lib.Sequence.equal a b)

