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

noextract
val pow: a:nat -> b:nat -> res:nat

val power_distributivity: a: nat -> b: nat -> c: pos -> Lemma ((pow (a % c) b) % c = (pow a b) % c)

noextract 
val felem_add_seq: a: felem_seq{felem_seq_as_nat a < prime} -> b: felem_seq{felem_seq_as_nat b < prime} -> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime /\ felem_seq_as_nat r = toDomain_ ((fromDomain_ (felem_seq_as_nat a) + fromDomain_ (felem_seq_as_nat b)) % prime)})

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

noextract 
val mm_byThree_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ (3 * fromDomain_ (felem_seq_as_nat a) % prime )})

noextract 
val mm_byFour_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ (4 * fromDomain_ (felem_seq_as_nat a) % prime)})

noextract 
val mm_byEight_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ (8 * fromDomain_ (felem_seq_as_nat a) % prime)})

noextract 
val mm_byMinusThree_seq: a: felem_seq {felem_seq_as_nat a < prime} -> Tot (r: felem_seq {felem_seq_as_nat r < prime /\
  felem_seq_as_nat r = toDomain_ ((-3) * fromDomain_ (felem_seq_as_nat a) % prime)})

val lemmaEraseToDomainFromDomain: z: nat-> Lemma (toDomain_ (fromDomain_ (toDomain_ (z * z % prime)) * z % prime) == toDomain_ (z * z * z % prime))

val exponent: a: felem ->result: felem -> tempBuffer: lbuffer uint64 (size 20) ->  Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
  disjoint a tempBuffer /\ as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1 /\ (let k = fromDomain_ (as_nat h0 a) in 
    as_nat h1 result =  toDomain_ ((pow k (prime-2)) % prime)))


[@ CInline]
val cswap: bit:uint64{v bit <= 1} -> p1:point -> p2:point
  -> Stack unit
    (requires fun h ->
      live h p1 /\ live h p2 /\
      (disjoint p1 p2 \/ p1 == p2))
    (ensures  fun h0 _ h1 ->
      modifies (loc p1 |+| loc p2) h0 h1 /\
      (v bit == 1 ==> as_seq h1 p1 == as_seq h0 p2 /\ as_seq h1 p2 == as_seq h0 p1) /\
      (v bit == 0 ==> as_seq h1 p1 == as_seq h0 p1 /\ as_seq h1 p2 == as_seq h0 p2))
