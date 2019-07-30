module Hacl.Impl.MM.Exponent


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.ECDSAP256.Definition
open Hacl.Spec.ECDSA
open Hacl.Impl.LowLevel
open Hacl.Spec.P256.Basic
open Hacl.Spec.P256.Core
open Hacl.Spec.P256.Ladder

open FStar.Mul

open Hacl.Impl.MontgomeryMultiplication
open Lib.Loops

#reset-options "--z3refresh --z3rlimit 200"

noextract
let prime = prime_p256_order

(*
assume val lemmaFromDomainToDomain:  a: nat -> Lemma (toDomain_ (fromDomain_ a)  == a)

assume val inDomain_mod_is_not_mod: a: nat ->  Lemma (toDomain_ a == toDomain_ (a % prime))

assume val lemmaFromDomainToDomainModuloPrime: a: nat -> Lemma (a % prime == fromDomain_(toDomain_ a))
*)



[@ CInline]
val cswap: bit:uint64{v bit <= 1} -> p:felem -> q:felem
  -> Stack unit
    (requires fun h ->
      live h p /\ live h q /\ (disjoint p q \/ p == q))
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1 /\
      (
	let pBefore = as_seq h0 p in let qBefore = as_seq h0 q in 
	let pAfter = as_seq h1 p in let qAfter = as_seq h1 q in 
      (v bit == 1 ==> as_seq h1 p == as_seq h0 q /\ as_seq h1 q == as_seq h0 p) /\
      (v bit == 0 ==> as_seq h1 p == as_seq h0 p /\ as_seq h1 q == as_seq h0 q)))


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
    (forall (k:nat{i <= k /\ k < 4}).
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
  (requires fun h -> live h a /\ live h b /\ as_nat h a < prime /\ as_nat h b < prime /\ disjoint a b )
  (ensures fun h0 _ h1 -> modifies2 a b h0 h1 /\ as_nat h1 a < prime /\ as_nat h1 b < prime /\
    (
      let (r0D, r1D) = _exp_step1 (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b)) in 
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b)  
    )
)

let montgomery_ladder_exponent_step0 a b = 
    let h0 = ST.get() in 
  montgomery_multiplication_ecdsa_module a b a;
    let h1 = ST.get() in 
    assert(as_nat h1 a = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime));
    lemmaToDomainFromDomain (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime);
    assert(fromDomain_ (as_nat h1 a) = (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime));
  montgomery_multiplication_ecdsa_module b b b;
    let h2 = ST.get() in 
    assert(fromDomain_ (as_nat h2 b) = fromDomain_ (toDomain_ (fromDomain_ (as_nat h0 b) * fromDomain_ (as_nat h0 b) % prime)));
    lemmaToDomainFromDomain (fromDomain_ (as_nat h0 b) * fromDomain_ (as_nat h0 b) % prime);
    assert(fromDomain_ (as_nat h2 b) = fromDomain_ (as_nat h0 b) * fromDomain_ (as_nat h0 b) % prime);

  let (t0, t1) = _exp_step1 (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b)) in 
  assert(t1 = fromDomain_(as_nat h0 b) * fromDomain_ (as_nat h0 b) % prime);
  assert(t0 = fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime);
  assert(t0 == fromDomain_ (as_nat h1 a));
  assert(t1 == fromDomain_ (as_nat h2 b))


(* this piece of code is taken from Hacl.Curve25519 *)
inline_for_extraction noextract 
val scalar_bit:
  s:lbuffer uint8 (size 32)
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\ r == Hacl.Spec.ECDSA.ith_bit (as_seq h0 s) (v n) /\ v r <= 1)

let scalar_bit s n =
 let h0 = ST.get () in
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  uintv_extensionality (mod_mask #U8 1ul) (u8 1);
  to_u64 ((s.(n /. 8ul) >>. (n %. 8ul)) &. u8 1)


inline_for_extraction noextract 
val montgomery_ladder_exponent_step: a: felem -> b: felem ->scalar: lbuffer uint8 (size 32) ->   i:size_t{v i < 256} ->  Stack unit
  (requires fun h -> live h a  /\ live h b /\ live h scalar /\ as_nat h a < prime /\ as_nat h b < prime /\ disjoint a b)
  (ensures fun h0 _ h1 -> modifies2 a b h0 h1)


let montgomery_ladder_exponent_step a b scalar i = 
    let h0 = ST.get() in 
  let bit0 = (size 255) -. i in 
  let bit = scalar_bit scalar bit0 in 
  cswap bit a b;
    let h1 = ST.get() in 
  montgomery_ladder_exponent_step0 a b;
    let h2 = ST.get() in 
  cswap bit a b



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
