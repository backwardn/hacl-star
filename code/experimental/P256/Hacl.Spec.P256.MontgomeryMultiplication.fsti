module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Core

open Hacl.Impl.Curve25519.Field64.Core
module D = Hacl.Spec.Curve25519.Field64.Definition

open Lib.IntTypes
open Lib.Buffer
open Lib.Sequence


noextract
val fromDomain_: a: int -> Tot (r: nat (*{ r = a * modp_inv2 (pow2 256) % prime}*))

noextract
val fromDomainPoint: a: tuple3 nat nat nat -> Tot (r: tuple3 nat nat nat 
  {
    let x, y, z = a in
    let x3, y3, z3 = r in 
    x3 == fromDomain_ x /\ y3 == fromDomain_ y /\ z3 == fromDomain_ z
  }
)


noextract
val toDomain_: a: int -> Tot (r: nat (*{r =  a * pow2 256 % prime}*))

val lemmaFromDomain: a: int -> Lemma (fromDomain_ (a) == a * modp_inv2 (pow2 256) % prime)

val lemmaToDomain: a: int -> Lemma (toDomain_(a) == a * (pow2 256) % prime)

val lemmaToDomainAndBackIsTheSame: a: nat { a < prime} -> Lemma (fromDomain_ (toDomain_ a) == a)
  [SMTPat (fromDomain_ (toDomain_ a))]

val lemmaFromDomainToDomain: a: nat { a < prime} -> Lemma (toDomain_ (fromDomain_ a) == a)

(* the lemma shows the equivalence between toDomain(a:nat) and toDomain(a % prime) *)
val inDomain_mod_is_not_mod: a: int -> Lemma (toDomain_ a == toDomain_ (a % prime))

val additionInDomain2Nat: a: nat {a < prime} -> b: nat {b < prime} -> Lemma 
  (
    let result = (a + b) % prime in 
    result = toDomain_ (fromDomain_ a + fromDomain_ b)
  )
  
val substractionInDomain2Nat: a: nat {a < prime} -> b: nat { b < prime} -> Lemma 
  ((a - b) % prime == toDomain_ (fromDomain_ a - fromDomain_ b))
  

noextract 
val felem_add_seq: a: felem_seq{felem_seq_as_nat a < prime} -> b: felem_seq{felem_seq_as_nat b < prime} -> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime /\ 
    felem_seq_as_nat r = toDomain_ ((fromDomain_ (felem_seq_as_nat a) + fromDomain_ (felem_seq_as_nat b)) % prime)})

noextract
val felem_sub_seq: a: felem_seq{felem_seq_as_nat a < prime} -> b: felem_seq{felem_seq_as_nat b < prime} -> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime /\ 
  felem_seq_as_nat r = toDomain_ ((fromDomain_ (felem_seq_as_nat a) - fromDomain_(felem_seq_as_nat b))% prime)})


noextract
val montgomery_multiplication_seq: a: felem_seq {felem_seq_as_nat a < prime} -> b: felem_seq {felem_seq_as_nat b < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\ 
  felem_seq_as_nat r = toDomain_ (fromDomain_ (felem_seq_as_nat a) * fromDomain_(felem_seq_as_nat b) % prime)
  }) 
   
val montgomery_multiplication_buffer: a: felem -> b: felem -> r: felem ->  Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime /\ live h b /\ live h r /\ as_nat h b < prime)) 
  (ensures (fun h0 _ h1 -> modifies1 r h0 h1 /\ 
    as_nat h1 r < prime /\
    as_seq h1 r == montgomery_multiplication_seq (as_seq h0 a) (as_seq h0 b)))

noextract
val mm_cube_seq: a: felem_seq {felem_seq_as_nat a < prime}-> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime /\ 
  felem_seq_as_nat r = toDomain_ (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) % prime) })

noextract
val mm_quatre_seq: a: felem_seq {felem_seq_as_nat a < prime} -> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime /\ 
  felem_seq_as_nat r = toDomain_ (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) % prime)})

noextract 
val mm_byTwo_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ (2 * fromDomain_ (felem_seq_as_nat a) % prime)})


val lemma_add_same_value_is_by_two: a: felem_seq {felem_seq_as_nat a < prime} -> 
  Lemma (felem_add_seq a a  == mm_byTwo_seq a)

noextract 
val mm_byThree_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ (3 * fromDomain_ (felem_seq_as_nat a) % prime )})

noextract 
val mm_byFour_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ (4 * fromDomain_ (felem_seq_as_nat a) % prime)})

noextract 
val mm_byEight_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ (8 * fromDomain_ (felem_seq_as_nat a) % prime)})


val lemma_add_same_value_is_by_three: a: felem_seq {felem_seq_as_nat a < prime} -> 
  Lemma (let two = mm_byTwo_seq a in let three = felem_add_seq a two in three  == mm_byThree_seq a)


val lemma_add_same_value_is_by_four: a: felem_seq {felem_seq_as_nat a < prime} -> 
  Lemma (let two = mm_byTwo_seq a in let four = mm_byTwo_seq two  in four  == mm_byFour_seq a)


val lemma_add_same_value_is_by_eight: a: felem_seq {felem_seq_as_nat a < prime} -> 
  Lemma (let two = mm_byTwo_seq a in let four = mm_byTwo_seq two in let eight = mm_byTwo_seq four in eight  == mm_byEight_seq a)


noextract 
val mm_byMinusThree_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ ((-3) * fromDomain_ (felem_seq_as_nat a) % prime)})


val lemma_add_same_value_is_by_minus_three: a: felem_seq{felem_seq_as_nat a < prime} -> zero: felem_seq{felem_seq_as_nat zero = 0} ->
  Lemma ( 
      let three = mm_byThree_seq a in 
      let minusThree = felem_sub_seq zero three in 
      minusThree == mm_byMinusThree_seq a)


val lemmaEraseToDomainFromDomain: z: nat-> Lemma (toDomain_ (fromDomain_ (toDomain_ (z * z % prime)) * z % prime) == toDomain_ (z * z * z % prime))

val exponent: a: felem ->result: felem -> tempBuffer: lbuffer uint64 (size 20) ->  Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
  disjoint a tempBuffer /\ as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1 /\ (let k = fromDomain_ (as_nat h0 a) in 
    as_nat h1 result =  toDomain_ ((pow k (prime-2)) % prime)))