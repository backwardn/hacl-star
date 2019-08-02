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


inline_for_extraction noextract 
val upload_scalar: b: lbuffer uint8 (size 32) -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies1 b h0 h1 /\ scalar_as_nat h1 b == prime - 2 /\ as_seq h1 b == genScalar() )


val montgomery_ladder_exponent: a: felem -> Stack unit 
  (requires fun h -> live h a /\ as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies1 a h0 h1 /\ 
    (
      let b_ = fromDomain_ (as_nat h0 a) in 
      let r0D = exponent_spec b_ in 
      fromDomain_ (as_nat h1 a) == r0D  /\
      as_nat h1 a < prime
    )
)

val fromDomainImpl: a: felem -> result: felem -> Stack unit
  (requires fun h -> live h a /\ live h result /\ as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ as_nat h1 result == fromDomain_ (as_nat h0 a))


val multPower: a: felem -> b: felem ->  result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h b /\ live h result /\ as_nat h a < prime /\ as_nat h b < prime)
  (ensures fun h0 _ h1 -> modifies1 result h0 h1)


(* a = inverse_mod smth *) 
val multPowerPartial: a: felem -> b: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h b /\ as_nat h a < prime /\ as_nat h b < prime)
  (ensures fun h0 _ h1 -> modifies1 result h0 h1)
