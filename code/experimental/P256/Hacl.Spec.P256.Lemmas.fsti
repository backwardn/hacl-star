module Hacl.Spec.P256.Lemmas

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.P256.Basic

open FStar.Mul

open Hacl.Spec.P256.Definitions

noextract
val log_and: a: uint64 -> b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} -> 
Lemma (if uint_v b = 0 then uint_v (logand a b) == 0 else uint_v (logand a b) == uint_v a)

noextract
val log_or: a: uint64 -> b: uint64 {uint_v b == 0 \/ uint_v a == 0} -> 
Lemma (if uint_v b = 0 then uint_v (logor a b) == uint_v a else uint_v (logor a b) == uint_v b)

noextract
val log_not_lemma: b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} -> 
Lemma(if uint_v b = 0 then uint_v (lognot (b)) == pow2 64 -1 else uint_v (lognot b) == 0)

noextract
val lemma_nat_4: f: felem4 -> Lemma (as_nat4 f < pow2 256)

noextract
val lemma_enough_to_carry: a: felem4 -> b: felem4 -> Lemma (
  if as_nat4 b >= (pow2 256 - as_nat4 a) then 
    let (c, r) = add4 a b in 
    uint_v c == 1
    else True)


noextract   
let ( +% ) a b = (a + b) % prime
noextract
let ( -% ) a b = (a - b) % prime
noextract
let ( *% ) a b prime = (a * b) % prime


noextract
let rec exp (e: nat) (n:nat {n > 0}) (prime: pos) : Tot (r: nat) (decreases n)  =
  let ( *%) a b =  ( *% ) a b prime in 

  if n = 1 then e
  else
    if n % 2 = 0 then 
    begin
      exp (e *% e) (n/2) prime
    end
    else e *% (exp (e *% e)((n-1)/2) prime)

noextract 
let modp_inv_prime (prime: pos {prime > 3}) (x: nat {x < prime})  : Tot (r: nat{r < prime}) = 
  (exp x (prime - 2) prime) % prime

noextract
let modp_inv2_prime (x: nat) (p: nat {p > 3}) : Tot (r: nat {r < p}) = 
  assert_norm (prime > 0);
  let r:nat = x % p in  
  modp_inv_prime p r

noextract
let modp_inv (x: nat {x < prime}) : Tot (r: nat{r < prime}) = 
  assert_norm (prime > 3);
  modp_inv_prime prime x

noextract
let modp_inv2 (x: nat) : Tot (r: nat {r < prime}) = 
  assert_norm (prime > 3);
  modp_inv2_prime x prime


#reset-options "--max_fuel 0 --z3rlimit 100" 

noextract
val modulo_distributivity_mult: a: int -> b: int -> c: pos -> Lemma ((a * b) % c = ((a % c) * (b % c)) % c)

noextract
val pow_plus: a: nat -> b: nat -> c: nat -> Lemma (ensures (pow a b * pow a c = pow a (b +c)))
(decreases b)

noextract
val power_distributivity: a: nat -> b: nat -> c: pos -> Lemma ((pow (a % c) b) % c = (pow a b) % c)

noextract
val power_mult: a: nat -> b: nat -> c: nat -> Lemma (pow (pow a b) c == pow a (b * c))

noextract
let modp_inv2_pow (x: nat) : Tot (r: nat {r < prime}) = 
   power_distributivity x (prime - 2) prime;
   pow x (prime - 2) % prime
  

val modulo_distributivity_mult_last_two: a: int -> b: int -> c: int -> d: int -> e: int -> f: pos -> 
Lemma ((a * b * c * d * e) % f = (a * b * c * ((d * e) % f)) % f)


#reset-options "--max_fuel 0 --z3rlimit 100" 

val lemma_mod_twice : a:int -> p:pos -> Lemma ((a % p) % p == a % p)

val lemma_multiplication_to_same_number: a: nat -> b: nat ->c: nat -> prime: pos ->  
  Lemma (requires (a % prime = b % prime)) (ensures ((a * c) % prime = (b * c) % prime))


val lemma_division_is_multiplication: t3: nat{ exists (k: nat) . k * pow2 64 = t3} -> prime_: pos {prime_ > 3 /\
  (prime_ = 115792089210356248762697446949407573529996955224135760342422259061068512044369 \/ prime_ = prime)} ->   
  Lemma (ensures (t3 * modp_inv2_prime (pow2 64) prime_  % prime_ = (t3 / pow2 64) % prime_))

#reset-options " --z3rlimit 300 --z3refresh" 

val lemma_reduce_mod_by_sub: t: nat -> Lemma
    ((t - t % pow2 64) % pow2 64 == 0)

val lemma_multiplication_same_number2: a: int -> b: int -> c: int{a * b = c} -> d: int -> Lemma
    (a * b * d == c* d) 

val lemma_add_mod: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> f: nat {f = a - b + c + d - e} -> k: pos -> 
  Lemma (
    f % k == ((a % k) - (b % k) + ( c % k) + (d % k) - (e % k)) % k)


val lemma_reduce_mod_by_sub2: t: nat -> 
  Lemma ((prime * (t % pow2 64)) % pow2 64 == (-t)  % pow2 64)

val lemma_reduce_mod_by_sub3 : t: nat -> Lemma ((t + (t % pow2 64) * prime) % pow2 64 == 0)


val mult_one_round: t: nat -> co: nat{t % prime == co% prime}  -> Lemma
(let result = (t + (t % pow2 64) * prime) / pow2 64 % prime in result == (co * modp_inv2 (pow2 64)) % prime)

val lemma_reduce_mod_ecdsa_prime:
  prime : nat {prime = 115792089210356248762697446949407573529996955224135760342422259061068512044369} ->
  t: nat -> k0: nat {k0 = modp_inv2_prime (-prime) (pow2 64)} ->  
  Lemma
    ((t + prime * (k0 * (t % pow2 64) % pow2 64)) % pow2 64 == 0)
    


val mult_one_round_ecdsa_prime: t: nat -> 
  prime: pos {prime = 115792089210356248762697446949407573529996955224135760342422259061068512044369} -> 
  co: nat {t % prime == co % prime} -> k0: nat {k0 = modp_inv2_prime (-prime) (pow2 64)} -> Lemma
  (let result = (t + prime * ((k0 * (t % pow2 64)) % pow2 64)) / pow2 64 in 
    result % prime == (co * modp_inv2_prime (pow2 64) prime) % prime)

val lemma_decrease_pow: a: nat -> Lemma (ensures (a * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64))  % prime == (a * modp_inv2 (pow2 256)) % prime) 


val lemma_brackets : a: int -> b: int -> c: int -> Lemma (a * b * c = a * (b * c))

val lemma_brackets_l: a: int -> b: int -> c: int -> Lemma (a * b * c = (a * b) * c)


val lemma_brackets1: a: int -> b: int -> c: int -> Lemma (a * (b * c) = b * (a * c))


val lemma_brackets5: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e = a * b * c * (d * e))


val lemma_brackets5_twice: a: int -> b: int -> c: int -> d: int -> e: int -> Lemma (a * b * c * d * e = (a * d) * (b * e) * c)


val lemma_brackets7: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> Lemma (a * b * c * d * e * f * g = a * b * c * d * e * (f * g))



val lemma_brackets7_twice: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> Lemma (a * b * c * d * e * f * g = (a * e) * (b * f) * (c * g) * d)




val lemma_distr_mult3: a: int -> b: int -> c: int -> Lemma (a * b * c = a * c * b)


val lemma_distr_mult : a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e = a * b * d * c * e) 


val lemma_twice_brackets: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> h: int-> Lemma 
  ((a * b * c) * (d * e * f) * h = a * b * c * d * e * f * h)


val lemma_distr_mult7: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> h: int-> Lemma 
  ( a * b * c * d * e * f * h = a * b * d * e * f * h * c)


val lemma_prime_as_wild_nat: a: felem8{wide_as_nat4 a < 2* prime} -> Lemma (let (t0, t1, t2, t3, t4, t5, t6, t7) = a in 
  uint_v t7 = 0 /\ uint_v t6 = 0 /\ uint_v t5 = 0 /\ (uint_v t4 = 0 \/ uint_v t4 = 1) /\
  as_nat4 (t0, t1, t2, t3) + uint_v t4 * pow2 256 = wide_as_nat4 a)


val lemma_mul_nat2: a: nat -> b: nat -> Lemma (a * b >= 0)


val lemma_mul_nat: a:nat -> b:nat -> c: nat -> Lemma (a * b * c >= 0)


val lemma_mul_nat4: a:nat -> b:nat -> c: nat -> d: nat -> Lemma (a * b * c * d >= 0)


val lemma_mul_nat5: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e >= 0)

val modulo_distributivity_mult2: a: int -> b: int -> c: int -> d: pos -> Lemma (((a % d) * (b % d) * c) % d = (a * b * c)% d)

val lemma_minus_distr (a: int) (b: int): Lemma ((a % prime - b % prime) % prime = (a - b)%prime)


val lemma_multiplication_not_mod_prime: a: nat{a < prime} -> b: nat {b > 0 /\ b % prime <> 0} -> 
  Lemma ((a * b) % prime == 0 <==> a == 0)

(*If k a ≡ k b (mod n) and k is coprime with n, then a ≡ b (mod n) *)

val lemma_modular_multiplication_p256: a: nat{a < prime} -> b: nat{b < prime} -> 
  Lemma 
  (a * modp_inv2 (pow2 256) % prime = b * modp_inv2 (pow2 256) % prime  ==> a == b)


val lemma_mod_sub_distr (a:int) (b:int) (n:pos) : Lemma ((a - b % n) % n = (a - b) % n)


val lemma_mod_add_distr (a:int) (b:int) (n:pos) : Lemma ((a + b % n) % n = (a + b) % n)

val lemma_log_and1: a: uint64 {v a = 0 \/ v a = maxint U64} ->
  b: uint64 {v b = 0 \/ v b = maxint U64}  -> 
  Lemma (uint_v a = pow2 64 - 1 && uint_v b = pow2 64 - 1 <==> uint_v (logand a b) == pow2 64 - 1)

val lemma_xor_copy_cond: a: uint64 -> b: uint64 -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 -1} ->
  Lemma(let r = logxor a (logand mask (logxor a b)) in 
  if uint_v mask = pow2 64 - 1 then r == b else r == a)


val lognot_lemma: #t:inttype{~(U1? t)} -> a:uint_t t SEC -> Lemma
  (requires v a = 0 \/ v a = maxint t)
  (ensures (if v a = 0 then v (lognot a) == maxint t else v (lognot a) == 0)) 


val lemma_equality: a: felem4 -> b: felem4 -> Lemma
    (
      let (a_0, a_1, a_2, a_3) = a in 
      let (b_0, b_1, b_2, b_3) = b in 

      if  (uint_v a_0 = uint_v b_0 && uint_v a_1 = uint_v b_1 && uint_v a_2 = uint_v b_2 && uint_v a_3 = uint_v b_3) then as_nat4 a == as_nat4 b else as_nat4 a <> as_nat4 b)

 val neq_mask_lemma: #t:inttype -> a:uint_t t SEC -> b:uint_t t SEC -> Lemma
  (requires True)
  (ensures  (v a <> v b ==> v (neq_mask a b) == maxint t) /\
            (v a == v b ==> v (neq_mask a b) == 0))


val cmovznz4_lemma: cin: uint64 -> x: uint64 -> y: uint64 -> Lemma (
  let mask = neq_mask cin (u64 0) in 
  let r = logor (logand y mask) (logand x (lognot mask)) in 
  if uint_v cin = 0 then uint_v r == uint_v x else uint_v r == uint_v y)


val lemma_equ_felem: a: nat{ a < pow2 64} -> b: nat {b < pow2 64} -> c: nat {c < pow2 64} -> d: nat {d < pow2 64} ->
   a1: nat{a1 < pow2 64} -> b1: nat {b1 < pow2 64} -> c1: nat {c1 < pow2 64} -> d1: nat {d1 < pow2 64} ->
  Lemma (requires (
    a + b * pow2 64 + c * pow2 64 * pow2 64 + d *  pow2 64 * pow2 64 * pow2 64 == 
    a1 + b1 * pow2 64 + c1 * pow2 64 * pow2 64  + d1 *  pow2 64 * pow2 64 * pow2 64))
  (ensures (a == a1 /\ b == b1 /\ c == c1 /\ d == d1))

val lemma_eq_funct: a: felem_seq -> b: felem_seq -> Lemma
   (requires (felem_seq_as_nat a == felem_seq_as_nat b))
   (ensures (a == b))
