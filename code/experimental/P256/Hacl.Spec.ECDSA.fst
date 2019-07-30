module Hacl.Spec.ECDSA

open FStar.Mul 
open Hacl.Spec.ECDSAP256.Definition
open Hacl.Spec.P256.Lemmas

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence


let prime = prime_p256_order 
let nat_prime = (n: nat {n < prime})


let scalar = lbytes 32

let ith_bit (k:lbytes 32) (i:nat{i < 256}) : uint64 =
  let q = i / 8 in let r = size (i % 8) in
  to_u64 ((index k q >>. r) &. u8 1)

let ( *% ) a b = (a * b) % prime


val _exp_step0: p: nat_prime -> q: nat_prime -> tuple2 nat_prime nat_prime

let _exp_step0 r0 r1 = 
  let r1 = r0 *% r1 in 
  let r0 = r0 *% r0 in 
  r0, r1

val _exp_step1: p: nat_prime -> q: nat_prime -> tuple2 nat_prime nat_prime 

let _exp_step1 r0 r1 = 
  let r0 = r0 *% r1 in 
  let r1 = r1 *% r1 in 
  (r0, r1)


val _exp_step: k: scalar->  i: nat{i < 256} ->  (tuple2 nat_prime nat_prime) -> Tot (r: tuple2 nat_prime nat_prime)

let _exp_step k i (p, q) = 
  let bit = 255 - i in 
  let bit = ith_bit k bit in 
  let open Lib.RawIntTypes in 
  if uint_to_nat bit = 0 then 
      _exp_step1 p q 
  else _exp_step0 p q  


val exponent_spec: k: scalar -> tuple2 nat_prime nat_prime -> Tot (tuple2 nat_prime nat_prime)

let exponent_spec k (p, q) = 
  Lib.LoopCombinators.repeati 256  (_exp_step k) (p, q)

