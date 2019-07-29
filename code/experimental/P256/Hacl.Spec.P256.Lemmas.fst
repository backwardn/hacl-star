module Hacl.Spec.P256.Lemmas

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.P256.Basic

open FStar.Mul

open Hacl.Spec.P256.Definitions

let log_and a b = admit()
let log_or a b = admit()
let log_not_lemma a = admit()


let lemma_nat_4 f = 
  let (s0, s1, s2, s3) = f in 
  let r_n = as_nat4 f in 
  let r = uint_v s0 + uint_v s1 * pow2 64 + uint_v s2 * pow2 64 * pow2 64 + 
  uint_v s3 * pow2 64 * pow2 64 * pow2 64 in 
  assert(r_n == r);
  assert_norm(r < pow2 256)


    
let lemma_enough_to_carry a b = 
 if as_nat4 b >= (pow2 256 - as_nat4 a) then begin
  let (c, r) = add4 a b in 
    lemma_nat_4 r
  end
  else
  ()


let rec ( **% ) e n =
  if n = 1 then e
  else
    if n % 2 = 0 then 
    begin
      (e *% e) **% (n / 2)
    end
    else e *% ((e *% e) **% ((n-1)/2))

#reset-options "--max_fuel 0 --z3rlimit 100" 



let modulo_distributivity_mult a b c = 
  lemma_mod_mul_distr_l a b c;
  lemma_mod_mul_distr_r (a%c) b c


let rec pow_plus a b c = 
  match b with 
  | 0 -> assert_norm (pow a 0 = 1)
  | _ -> pow_plus a (b -1) c; 
    assert_norm(pow a (b - 1) * a = pow a b)

let rec power_distributivity a b c =
   match b with 
   | 0 -> ()
   | _ -> 
     power_distributivity a (b - 1) c; 
     modulo_distributivity_mult (pow a (b -1)) a c;
     lemma_mod_twice a c;
     modulo_distributivity_mult (pow (a % c) (b -1)) (a % c) c


let rec power_mult a b c = 
  match c with 
  |0 -> assert_norm(pow a 0 = 1); assert(pow (pow a b) 0  = 1)
  |_ ->  power_mult a b (c -1); pow_plus a (b * (c -1)) b


let modulo_distributivity_mult_last_two a b c d e f = admit()


#reset-options "--max_fuel 0 --z3rlimit 100" 


let lemma_mod_twice a p = lemma_mod_mod (a % p) a p

let lemma_multiplication_to_same_number a b c prime = 
  lemma_mod_mul_distr_l a c prime;
  lemma_mod_mul_distr_l b c prime

let lemma_division_is_multiplication t3 prime_ =  
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  let remainder = t3 / pow2 64 in 
  (*
  SAGE: 
    prime = 2** 256 - 2** 224 + 2** 192 + 2** 96 -1
    inverse_mod ((2 ** 64), prime) * 2 ** 64 % prime
    1;

    prime = 115792089210356248762697446949407573529996955224135760342422259061068512044369
    inverse_mod ((2 ** 64), prime) * 2 ** 64 % prime
  
  *)
  assert_norm(prime > 3);
  let prime2 = 115792089210356248762697446949407573529996955224135760342422259061068512044369 in 
  assume(modp_inv2_prime (pow2 64) prime * pow2 64 % prime = 1); 
  assume(modp_inv2_prime (pow2 64) prime2 * pow2 64 % prime2 = 1);

  let k =  (modp_inv2_prime (pow2 64) prime_ * pow2 64) in 
  
  modulo_distributivity_mult remainder k prime_;
  assert((remainder * k) % prime_ = ((remainder % prime_)) % prime_);
  lemma_mod_twice remainder prime_;
    assert_by_tactic (t3 / pow2 64 * (modp_inv2_prime (pow2 64) prime_ * pow2 64) == t3/ pow2 64 * pow2 64 * modp_inv2_prime (pow2 64) prime_) canon;
  assert((t3 / pow2 64 * (modp_inv2_prime (pow2 64) prime_ * pow2 64)) % prime_ = remainder % prime_);
  assert((t3  * modp_inv2_prime (pow2 64) prime_) % prime_ = remainder % prime_)


#reset-options " --z3rlimit 300 --z3refresh" 

let lemma_reduce_mod_by_sub t = ()


let lemma_multiplication_same_number2 a b c d = ()


let lemma_add_mod a b c d e f k = admit()


let lemma_reduce_mod_by_sub2 t = 
  let t_ = t % pow2 64 in   
  let f = (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1) * (t % pow2 64) in 
  assert(f == pow2 256 * t_ - pow2 224 * t_ + pow2 192 * t_ + pow2 96 * t_ - t_);
  lemma_add_mod (pow2 256 * t_) (pow2 224 * t_) (pow2 192 * t_) (pow2 96 * t_) t_ f (pow2 64);
  assert(f % (pow2 64) ==  ((pow2 256 * t_) % pow2 64 -  (pow2 224 * t_) % pow2 64 +  (pow2 192 * t_) % pow2 64 +  (pow2 96 * t_) % pow2 64 -  t_) % pow2 64);

    pow2_plus 192 64;
    lemma_multiplication_same_number2 (pow2 192) (pow2 64) (pow2 256) t_;
    multiple_modulo_lemma (pow2 192 * t_) (pow2 64);
    assert((pow2 256 * t_) % pow2 64 == 0);

    pow2_plus 160 64;
    lemma_multiplication_same_number2 (pow2 160) (pow2 64) (pow2 224) t_;
    multiple_modulo_lemma (pow2 160 * t_) (pow2 64);
    assert((pow2 224 * t_) % pow2 64 == 0);

    pow2_plus 128 64;
    lemma_multiplication_same_number2 (pow2 128) (pow2 64) (pow2 192) t_;
    multiple_modulo_lemma (pow2 128 * t_) (pow2 64);
    assert((pow2 192 * t_) % pow2 64 == 0);

    pow2_plus 32 64; 
    assert(pow2 32 * pow2 64 = pow2 96);

    lemma_multiplication_same_number2 (pow2 32) (pow2 64) (pow2 96) t_; 
    multiple_modulo_lemma (pow2 32 * t_) (pow2 64);
    assert((pow2 96 * t_) % pow2 64 == 0);

  assert(f % pow2 64 == (- (t % pow2 64)) % pow2 64);
  lemma_mod_sub_distr 0 t (pow2 64);
  assert(f % pow2 64 == (- t) % pow2 64)

let lemma_reduce_mod_by_sub3 t = 
  lemma_reduce_mod_by_sub2 t

let mult_one_round t co = 
    let t1 = t % pow2 64 in 
    let t2 = t1 * prime in 
    let t3 = t + t2 in 
      modulo_addition_lemma t prime (t % pow2 64);
      assert(t3 % prime = co % prime);
      lemma_div_mod t3 (pow2 64);
      lemma_reduce_mod_by_sub3 t;
      assert(t3 % pow2 64 == 0);
      assert(let rem = t3/ pow2 64 in rem * pow2 64 = t3);
      assert(exists (k: nat). k * pow2 64 = t3);
      assert_norm (prime > 3);
      lemma_division_is_multiplication t3 prime;
      lemma_multiplication_to_same_number t3 co (modp_inv2 (pow2 64)) prime


let lemma_reduce_mod_ecdsa_prime prime t k0 = 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
  
  let f = prime * (k0 * (t % pow2 64) % pow2 64) in 
  let t0 = (t + f) % pow2 64 in 
  lemma_mod_add_distr t f (pow2 64);
  
  modulo_addition_lemma t (pow2 64) f;
  assert(t0 == (t + f % pow2 64) % pow2 64);
  lemma_mod_mul_distr_r k0 t (pow2 64);
    assert(k0 * (t % pow2 64) % pow2 64 = (k0 * t) % pow2 64);
  lemma_mod_mul_distr_r prime (k0 * t) (pow2 64);
    assert((prime * (k0 * (t % pow2 64) % pow2 64)) % pow2 64 == (prime * (k0 * t)) % pow2 64);
    assert_by_tactic(prime * (k0 * t) == (prime * k0) * t) canon;
    assert((prime * (k0 * (t % pow2 64) % pow2 64)) % pow2 64 == ((prime * k0) * t) % pow2 64);
    lemma_mod_mul_distr_l (prime * k0) t (pow2 64); 
      (*
       SAGE: 
       prime = 115792089210356248762697446949407573529996955224135760342422259061068512044369
       inverse_mod (- prime, 2 ** 64) * prime % 2 ** 64  == (-1) % 2** 64	*)
       assume((prime * k0) % pow2 64 == (-1) % pow2 64);  
    assert((prime * (k0 * (t % pow2 64) % pow2 64)) % pow2 64 == ((-1) % pow2 64 * t) % pow2 64);
    lemma_mod_mul_distr_l (-1) t (pow2 64);
    assert(f % pow2 64 == (-t) % pow2 64);

    assert((t + f) % pow2 64 == (t + (- t % pow2 64)) % pow2 64);
    lemma_mod_add_distr t (-t) (pow2 64);
    assert((t + f) % pow2 64 == 0)
  


let mult_one_round_ecdsa_prime t prime co k0 = 
  assert_norm (prime > 3);
  let t2 = ((k0 * (t % pow2 64)) % pow2 64) * prime in 
  let t3 = t + t2 in 
    modulo_addition_lemma t prime ((k0 * (t % pow2 64)) % pow2 64);
    assert(t3 % prime = co % prime);
    lemma_div_mod t3 (pow2 64);
    lemma_reduce_mod_ecdsa_prime prime t k0;
    assert(let rem = t3/ pow2 64 in rem * pow2 64 = t3);
    assert(exists (k: nat). k * pow2 64 = t3);
    lemma_division_is_multiplication t3 prime;
    lemma_multiplication_to_same_number t3 co (modp_inv2_prime (pow2 64) prime) prime


let lemma_decrease_pow a = 
  assert_norm(modp_inv2 (pow2 64) = 6277101733925179126845168871924920046849447032244165148672);
  assert_norm(pow2 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936);
  assert_norm(modp_inv2 (pow2 256) =115792089183396302114378112356516095823261736990586219612555396166510339686400 );
  assert((modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64))% prime  = (modp_inv2 (pow2 256)) % prime);

  lemma_mod_mul_distr_r a (modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64)) prime;
  lemma_mod_mul_distr_r a (modp_inv2 (pow2 256)) prime



let lemma_brackets a b c = ()


let lemma_brackets_l a b c = ()


let lemma_brackets1 a b c = ()


let lemma_brackets5 a b c d e = ()


let lemma_brackets5_twice a b c d e = admit()


let lemma_brackets7 a b c d e f g = admit()


let lemma_brackets7_twice a b c d e f g = admit()



let lemma_distr_mult3 a b c = ()

let lemma_distr_mult a b c d e = ()


let lemma_twice_brackets a b c d e f h = () 

let lemma_distr_mult7 a b c d e f h = admit()


let lemma_prime_as_wild_nat a =
   assert_norm(pow2 64 * pow2 64 = pow2 128);
   assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
   assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 320);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64))
  

let lemma_mul_nat2 a b = ()

let lemma_mul_nat a b c = ()
let lemma_mul_nat4 a b c d = ()

let lemma_mul_nat5 a b c d e = ()


let modulo_distributivity_mult2 a b c d = 
  let start = ((a % d) * (b % d) * c) % d in 
  lemma_mod_mul_distr_l a ((b % d) * c) d;
  lemma_distr_mult3 a (b % d) c;
  lemma_mod_mul_distr_r (a * c) b d

let lemma_minus_distr a d = admit()


let lemma_multiplication_not_mod_prime a b = admit()

(*If k a ≡ k b (mod n) and k is coprime with n, then a ≡ b (mod n) *)


let lemma_modular_multiplication_p256 a b = admit()



let lemma_mod_sub_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  distributivity_sub_left 0 (b / n) n;
  // (a - b) % n == (a - (b % n) - (b / n) * n) % n
  lemma_mod_plus (a - (b % n)) (-(b / n)) n

let lemma_mod_add_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  // (a + b) % n == (a + (b % n) + (b / n) * n) % n
  lemma_mod_plus (a + (b % n)) (b / n) n

let lemma_log_and1 a b = 
  logand_lemma a b


let lemma_xor_copy_cond a b mask = 
  let fst = logxor a b in 
  let snd = logand mask fst in 
    logand_lemma mask fst;
  let thrd = logxor a snd in    
    logxor_lemma a snd;
    logxor_lemma a b

let lognot_lemma #t a = admit()

let lemma_equality a b = ()

let neq_mask_lemma #t a b = admit()


let cmovznz4_lemma cin x y = 
  let x2 = neq_mask cin (u64 0) in 
      neq_mask_lemma cin (u64 0);
  let x3 = logor (logand y x2) (logand x (lognot x2)) in
  let ln = lognot (neq_mask cin (u64 0)) in 
    log_and y x2; 
    log_not_lemma x2;
    log_and x ln;
    log_or (logand y x2) (logand x (lognot (x2)))


  
let lemma_equ_felem a b c d  a1 b1 c1 d1  = 
  assert(a = a1 + b1 * pow2 64 + c1 * pow2 128 + d1 * pow2 192 -  b * pow2 64 - c * pow2 128 - d * pow2 192);
  assert(a == a1);
  assert(b == b1);
  assert(c == c1);
  assert(d == d1)



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

