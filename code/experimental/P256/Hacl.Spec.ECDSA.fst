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


val swap: p: nat_prime -> q: nat_prime -> Tot (r: tuple2 nat_prime nat_prime{let pNew, qNew = r in 
  pNew == q /\ qNew == p})

let swap p q = (q, p)


val conditional_swap: i: uint64 -> p: nat_prime -> q: nat_prime -> Tot (r: tuple2 nat_prime nat_prime
  {
    let pNew, qNew = r in 
    if uint_v i = 0 then pNew == p /\ qNew == q
    else
      let p1, q1 = swap p q in 
      p1 == pNew /\ q1 == qNew
 }
)

#reset-options "--z3refresh --z3rlimit  100"

let conditional_swap i p q = 
  if  i = 0 then 
    (p, q)
  else
    (q, p)

val lemma_swaped_steps: p: nat_prime -> q: nat_prime -> 
  Lemma (
    let (afterSwapP, afterSwapQ) = swap p q in 
    let p1, q1 = _exp_step0 afterSwapP afterSwapQ in 
    let p2, q2 = swap p1 q1 in 
    let r0, r1 = _exp_step1 p q in 
    p2 == r0 /\ q2 == r1)

let lemma_swaped_steps p q = ()


val _exp_step: k: scalar->  i: nat{i < 256} ->  (tuple2 nat_prime nat_prime) -> Tot (r: tuple2 nat_prime nat_prime)

let _exp_step k i (p, q) = 
  let bit = 255 - i in 
  let bit = ith_bit k bit in 
  let open Lib.RawIntTypes in 
  if uint_to_nat bit = 0 then 
      _exp_step0 p q 
  else _exp_step1 p q  


val _exponent_spec: k: scalar -> tuple2 nat_prime nat_prime -> Tot (tuple2 nat_prime nat_prime)

let _exponent_spec k (p, q) = 
  Lib.LoopCombinators.repeati 256  (_exp_step k) (p, q)


val genScalar: unit -> Tot (lseq uint8 32)

let genScalar () = 
    let s = Lib.Sequence.create 32 (u8 0) in 
    let s = upd s 0 (u8 79) in 
    let s = upd s 1 (u8 37) in
    let s = upd s 2 (u8 99) in
    let s = upd s 3 (u8 252) in
    let s = upd s 4 (u8 194) in
    let s = upd s 5 (u8 202) in
    let s = upd s 6 (u8 185) in
    let s = upd s 7 (u8 243) in
    let s = upd s 8 (u8 132) in
    let s = upd s 9 (u8 158) in
    let s = upd s 10  (u8 23) in
    let s = upd s 11  (u8 167) in
    let s = upd s 12  (u8 173) in
    let s = upd s 13  (u8 250) in
    let s = upd s 14  (u8 230) in
    let s = upd s 15  (u8 188) in
    let s = upd s 16  (u8 255) in
    let s = upd s 17  (u8 255) in
    let s = upd s 18  (u8 255) in
    let s = upd s 19  (u8 255) in
    let s = upd s 20  (u8 255) in
    let s = upd s 21  (u8 255) in
    let s = upd s 22  (u8 255) in
    let s = upd s 23  (u8 255) in
    let s = upd s 24  (u8 0) in
    let s = upd s 25  (u8 0) in
    let s = upd s 26  (u8 0) in
    let s = upd s 27  (u8 0) in
    let s = upd s 28  (u8 255) in
    let s = upd s 29  (u8 255) in
    let s = upd s 30  (u8 255) in
    let s = upd s 31  (u8 255) in 
    s


val exponent_spec: a: nat_prime -> Tot nat_prime

let exponent_spec a = 
    let scalar = genScalar() in 
    let a0, _ = _exponent_spec scalar (1, a) in 
    a0
