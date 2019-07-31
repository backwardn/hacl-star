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
      as_nat h p < prime /\ as_nat h q < prime /\ 
      live h p /\ live h q /\ (disjoint p q \/ p == q))
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1 /\
	(
	  let (r0, r1) = Hacl.Spec.ECDSA.conditional_swap bit (as_nat h0 p) (as_nat h0 q) in 
	  if uint_v bit = 0 then r0 == as_nat h0 p /\ r1 == as_nat h0 q else r0 == as_nat h0 q /\ r1 == as_nat h0 p) /\
	  as_nat h1 p < prime /\ as_nat h1 q < prime /\
	
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
      let (r0D, r1D) = _exp_step0 (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b)) in 
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b)  /\
      as_nat h1 a < prime /\ as_nat h1 b < prime
    )
)

let montgomery_ladder_exponent_step0 a b = 
    let h0 = ST.get() in 
  montgomery_multiplication_ecdsa_module a b b;
    let h1 = ST.get() in 
    assert(as_nat h1 b = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime));
    lemmaToDomainFromDomain (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime);
    assert(fromDomain_ (as_nat h1 b) = (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime));
  montgomery_multiplication_ecdsa_module a a a ;
    let h2 = ST.get() in 
    assert(fromDomain_ (as_nat h2 a) = fromDomain_ (toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime)));
    lemmaToDomainFromDomain (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime);
    assert(fromDomain_ (as_nat h2 a) = fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime) 


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
  (ensures fun h0 _ h1 -> modifies2 a b h0 h1  /\
    (
      let a_ = fromDomain_ (as_nat h0 a) in 
      let b_ = fromDomain_ (as_nat h0 b) in 
      let (r0D, r1D) = _exp_step (as_seq h0 scalar) (uint_v i) (a_, b_) in 
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b) /\ 
      as_nat h1 a < prime /\ as_nat h1 b < prime
    ) 
  )  

let montgomery_ladder_exponent_step a b scalar i = 
    let h0 = ST.get() in 
  let bit0 = (size 255) -. i in 
  let bit = scalar_bit scalar bit0 in 
  cswap bit a b;
    let h1 = ST.get() in 
  montgomery_ladder_exponent_step0 a b;
    let h2 = ST.get() in 
  cswap bit a b;
    let h3 = ST.get() in 

  (*assert(if uint_v bit = 0 
    then 
      as_nat h1 a == as_nat h0 a /\ as_nat h1 b == as_nat h0 b 
    else
      as_nat h1 a == as_nat h0 b /\ as_nat h1 b == as_nat h0 a);

  assert(
    if uint_v bit = 0 then 
    let (r0D, r1D) = _exp_step0 (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b)) in 
      r0D == fromDomain_ (as_nat h2 a) /\ r1D == fromDomain_ (as_nat h2 b) 
    else
      let (r0D, r1D) = _exp_step0 (fromDomain_ (as_nat h0 b)) (fromDomain_ (as_nat h0 a)) in 
      r0D == fromDomain_ (as_nat h2 a) /\ r1D == fromDomain_ (as_nat h2 b));

  assert(if uint_v bit = 0 
    then  
      let (r0D, r1D) = _exp_step0 (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b)) in 
      fromDomain_ (as_nat h3 a) == r0D /\ fromDomain_ (as_nat h3 b) == r1D
    else
      let (r0D, r1D) = _exp_step0 (fromDomain_ (as_nat h0 b)) (fromDomain_ (as_nat h0 a)) in 
      fromDomain_ (as_nat h3 a) == r1D /\ fromDomain_ (as_nat h3 b) == r0D); *)
       
   Hacl.Spec.ECDSA.lemma_swaped_steps (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b));
   assert(
      let r0D_f, r1D_f = _exp_step (as_seq h0 scalar) (uint_v i) (fromDomain_ (as_nat h0 a), fromDomain_ (as_nat h0 b)) in 
   
      if uint_v bit = 0 then 
      let (r0D, r1D) = _exp_step0 (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b)) in 
      fromDomain_ (as_nat h3 a) == r0D /\ fromDomain_ (as_nat h3 b) == r1D /\ r0D == r0D_f /\ r1D == r1D_f
    else
      let (r0D, r1D) = _exp_step1 (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b)) in 
      fromDomain_ (as_nat h3 a) == r0D /\ fromDomain_ (as_nat h3 b) == r1D /\ r0D == r0D_f /\ r1D == r1D_f)
  

inline_for_extraction noextract 
val _montgomery_ladder_exponent: a: felem ->b: felem ->  scalar: lbuffer uint8 (size 32) -> Stack unit
  (requires fun h -> live h a /\ live h b /\ live h scalar /\ as_nat h a < prime /\ 
    as_nat h b < prime /\ disjoint a b /\disjoint a scalar /\ disjoint b scalar)
  (ensures fun h0 _ h1 -> modifies2 a b h0 h1 /\ 
    (
      let a_ = fromDomain_ (as_nat h0 a) in 
      let b_ = fromDomain_ (as_nat h0 b) in 
      let (r0D, r1D) = _exponent_spec (as_seq h0 scalar) (a_, b_) in 
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b)
  )
  )


let _montgomery_ladder_exponent a b scalar = 
  let h0 = ST.get() in 

  [@inline_let]
  let spec_exp h0  = _exp_step (as_seq h0 scalar) in 

  [@inline_let]
  let acc (h: mem) : GTot (tuple2 nat_prime nat_prime) = 
    (fromDomain_ (as_nat h a), fromDomain_ (as_nat h b)) in 

  Lib.LoopCombinators.eq_repeati0 256 (spec_exp h0) (acc h0);

  [@inline_let]
  let inv h (i: nat {i <= 256}) = 
    live h a /\ live h b /\ live h scalar /\ 
    modifies2 a b h0 h /\ 
    as_nat h a < prime /\ as_nat h b < prime /\
    acc h == Lib.LoopCombinators.repeati i (spec_exp h0) (acc h0)     
    in 

  for 0ul 256ul inv (
    fun i -> 
	let h3 = ST.get() in
	  montgomery_ladder_exponent_step a b scalar i;
	  let h4 = ST.get() in   
	  assert(modifies2 a b h3 h4);
	  assert(modifies2 a b h0 h4);
	  assert(
	    let a_ = fromDomain_ (as_nat h3 a) in 
	    let b_ = fromDomain_ (as_nat h3 b) in 
	    let (r0D, r1D) = _exp_step (as_seq h0 scalar) (uint_v i) (a_, b_) in  
	    r0D == fromDomain_ (as_nat h4 a));

	  Lib.LoopCombinators.unfold_repeati 256 (spec_exp h0) (acc h0) (uint_v i);
	assert(acc h4 == Lib.LoopCombinators.repeati (uint_v i + 1) (spec_exp h0) (acc h0))
  )



inline_for_extraction noextract 
val upload_one_montg_form: b: felem -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies1 b h0 h1 /\ as_nat h1 b == toDomain_ (1))

let upload_one_montg_form b =
  upd b (size 0) (u64 884452912994769583);
  upd b (size 1) (u64 4834901526196019579);
  upd b (size 2) (u64 0);
  upd b (size 3) (u64 4294967295)

inline_for_extraction noextract 
val upload_one: b: felem -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies1 b h0 h1 /\ as_nat h1 b == 1)

let upload_one b = 
  upd b (size 0) (u64 1);
  upd b (size 1) (u64 0);
  upd b (size 2) (u64 0);
  upd b (size 3) (u64 0)


inline_for_extraction noextract 
val upload_scalar: b: lbuffer uint8 (size 32) -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> True)

let upload_scalar b = 
  upd b (size 0) (u8 81);
  upd b (size 0) (u8 37);
  upd b (size 0) (u8 99);
  upd b (size 0) (u8 252);
  upd b (size 0) (u8 194);
  upd b (size 0) (u8 202);
  upd b (size 0) (u8 185);
  upd b (size 0) (u8 243);
  upd b (size 0) (u8 132);
  upd b (size 0) (u8 158);
  upd b (size 0) (u8 23);
  upd b (size 0) (u8 167);
  upd b (size 0) (u8 173);
  upd b (size 0) (u8 250);
  upd b (size 0) (u8 230);
  upd b (size 0) (u8 188);
  upd b (size 0) (u8 255);
  upd b (size 0) (u8 255);
  upd b (size 0) (u8 255);
  upd b (size 0) (u8 255);
  upd b (size 0) (u8 255);
  upd b (size 0) (u8 255);
  upd b (size 0) (u8 255);
  upd b (size 0) (u8 255);
  upd b (size 0) (u8 0);
  upd b (size 0) (u8 0);
  upd b (size 0) (u8 0);
  upd b (size 0) (u8 0);
  upd b (size 0) (u8 255);
  upd b (size 0) (u8 255);
  upd b (size 0) (u8 255);
  upd b (size 0) (u8 255)


val montgomery_ladder_exponent: a: felem -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let montgomery_ladder_exponent a = 
  push_frame(); 
    let b = create (size 4) (u64 0) in 
    let scalar = create (size 32) (u8 0) in 
    upload_one_montg_form b;
    upload_scalar scalar;

    _montgomery_ladder_exponent a b scalar;
  pop_frame()  

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
