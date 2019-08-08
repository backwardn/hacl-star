module Hacl.Impl.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.ECDSAP256.Definition
open Hacl.Impl.LowLevel
open Hacl.Spec.P256.Basic
open Hacl.Spec.P256.Core

open FStar.Mul

noextract
let prime = prime_p256_order

inline_for_extraction
let prime256order_buffer: x: ilbuffer uint64 (size 4)  
{witnessed #uint64 #(size 4) x 
(Lib.Sequence.of_list p256_order_prime_list) /\ recallable x /\ 
felem_seq_as_nat (Lib.Sequence.of_list (p256_order_prime_list)) == prime_p256_order} = 
createL_global p256_order_prime_list


inline_for_extraction noextract
val reduction_prime_p256_order_2prime_p256_order_with_carry_impl_5: x: widefelem -> result: felem -> prime_p256_orderBuffer: felem -> 
  Stack unit 
    (requires fun h -> live h x /\ live h result /\  eq_or_disjoint x result /\ live h prime_p256_orderBuffer /\
      (as_nat h prime_p256_orderBuffer == prime_p256_order) /\ wide_as_nat h x < 2 * prime_p256_order)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ as_nat h1 result = wide_as_nat h0 x % prime_p256_order)  


val reduction_prime_2prime_order: x: felem -> result: felem -> 
  Stack unit 
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ 
      as_nat h1 result == as_nat h0 x % prime_p256_order
    )  


noextract
val fromDomain_: a: nat -> Tot nat 

noextract
val toDomain_: a: nat -> Tot nat


val lemmaFromDomainToDomain: a: nat { a < prime} -> Lemma (toDomain_ (fromDomain_ a) == a)

val lemmaToDomainFromDomain: a: nat { a < prime} -> Lemma (fromDomain_ (toDomain_ a) == a)



val montgomery_multiplication_ecdsa_module: a: felem -> b: felem ->result: felem-> 
  Stack unit 
    (requires fun h -> live h a /\ live h b /\ live h result /\
      as_nat h a < prime_p256_order /\ as_nat h b < prime_p256_order)
    (
      ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ as_nat h1 result = (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order /\ 
      as_nat h1 result = fromDomain_(as_nat h0 a * as_nat h0 b) /\
      as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime)
    )

