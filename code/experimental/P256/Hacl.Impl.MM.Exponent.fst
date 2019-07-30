module Hacl.Impl.MM.Exponent


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

open Hacl.Impl.MontgomeryMultiplication
open Lib.Loops

noextract
val fromDomain_: a: nat -> Tot nat

let fromDomain_ a = (a * modp_inv2_prime (pow2 256) prime) % prime

noextract
val toDomain_: a: nat -> Tot nat
let toDomain_ a = (a * pow2 256) % prime 


assume val lemmaFromDomainToDomain:  a: nat -> Lemma (toDomain_ (fromDomain_ a)  == a)

assume val inDomain_mod_is_not_mod: a: nat ->  Lemma (toDomain_ a == toDomain_ (a % prime))

assume val lemmaFromDomainToDomainModuloPrime: a: nat -> Lemma (a % prime == fromDomain_(toDomain_ a))



open Hacl.Spec.P256.Ladder

[@ CInline]
val cswap: bit:uint64{v bit <= 1} -> p:felem -> q:felem
  -> Stack unit
    (requires fun h ->
      live h p /\ live h q /\ (disjoint p q \/ p == q) /\
           
      as_nat h (gsub p (size 0) (size 4)) < prime /\ 
      as_nat h (gsub p (size 4) (size 4)) < prime /\
      as_nat h (gsub p (size 8) (size 4)) < prime /\
	     
      as_nat h (gsub q (size 0) (size 4)) < prime /\  
      as_nat h (gsub q (size 4) (size 4)) < prime /\
      as_nat h (gsub q (size 8) (size 4)) < prime
)
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1 /\
      (let pBefore = as_seq h0 p in let qBefore = as_seq h0 q in 
	let pAfter = as_seq h1 p in let qAfter = as_seq h1 q in 
	let condP0, condP1 = conditional_swap bit pBefore qBefore  in 
	condP0 == pAfter /\ condP1 == qAfter) /\ 

      (v bit == 1 ==> as_seq h1 p == as_seq h0 q /\ as_seq h1 q == as_seq h0 p) /\
      (v bit == 0 ==> as_seq h1 p == as_seq h0 p /\ as_seq h1 q == as_seq h0 q))


let cswap bit p1 p2 =
  let h0 = ST.get () in
  let mask = u64 0 -. bit in
  let open Lib.Sequence in 
  [@ inline_let]
  let inv h1 (i:nat{i <= 4}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 12}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in
 
  Lib.Loops.for 0ul 4ul inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in
  Lib.Sequence.eq_intro (as_seq h1 p1) (if v bit = 1 then as_seq h0 p2 else as_seq h0 p1);
  Lib.Sequence.eq_intro (as_seq h1 p2) (if v bit = 1 then as_seq h0 p1 else as_seq h0 p2)

inline_for_extraction noextract
val montgomery_ladder_exponent_step0: a: felem -> b: felem -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let montgomery_ladder_exponent_step0 a b = 
  montgomery_multiplication_ecdsa_module a b b;
  montgomery_multiplication_ecdsa_module a a a



(* this piece of code is taken from Hacl.Curve25519 *)
inline_for_extraction noextract 
val scalar_bit:
  s:lbuffer uint8 (size 32)
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 (*/\ r == ith_bit (as_seq h0 s) (v n) /\ v r <= 1) *) )

let scalar_bit s n =
 let h0 = ST.get () in
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  uintv_extensionality (mod_mask #U8 1ul) (u8 1);
  to_u64 ((s.(n /. 8ul) >>. (n %. 8ul)) &. u8 1)

inline_for_extraction noextract 
val montgomery_ladder_exponent_step: a: felem -> b: felem ->scalar: lbuffer uint8 (size 32) ->   i:size_t{v i < 256} ->  Stack unit
  (requires fun h -> live h a  /\ live h b)
  (ensures fun h0 _ h1 -> True)


let montgomery_ladder_exponent_step a b scalar i = 
  let bit0 = (size 255) -. i in 
  let bit = scalar_bit scalar bit0 in 
  cswap bit a b;
  montgomery_ladder_exponent_step0 a b;
  cswap bit a b;
  
  ()

inline_for_extraction noextract 
val _montgomery_ladder_exponent: a: felem ->b: felem ->  scalar: lbuffer uint8 (size 32) -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let _montgomery_ladder_exponent a b scalar = 
  [@inline_let]
  let inv h (i: nat {i <= 256}) = 
    True in 

  for 0ul 256ul inv (fun i -> montgomery_ladder_exponent_step a b scalar i)

inline_for_extraction noextract 
val upload_zero_montg_form: b: felem -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let upload_zero_montg_form b = ()

inline_for_extraction noextract 
val upload_scalar: b: lbuffer uint8 (size 32) -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let upload_scalar b = ()


val montgomery_ladder_exponent: a: felem -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let montgomery_ladder_exponent a = 
  push_frame(); 
    let b = create (size 4) (u64 0) in 
    let scalar = create (size 32) (u8 0) in 
    upload_zero_montg_form b;
    upload_scalar scalar;

    _montgomery_ladder_exponent a b scalar;
  pop_frame()  

inline_for_extraction noextract 
val upload_one: one: felem -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let upload_one one = admit()


val fromDomainImpl: a: felem -> result: felem -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let fromDomainImpl a result = 
  push_frame();
    let one = create (size 4) (u64 0) in 
    upload_one one;
    montgomery_multiplication_ecdsa_module one a result;
  pop_frame()   


val multPower: a: felem -> b: felem ->  result: felem -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let multPower a b result = 
  push_frame();
    let tempB1 = create (size 4) (u64 0) in 
  fromDomainImpl a tempB1;
  montgomery_ladder_exponent tempB1;
  montgomery_multiplication_ecdsa_module tempB1 b result;
  pop_frame()
