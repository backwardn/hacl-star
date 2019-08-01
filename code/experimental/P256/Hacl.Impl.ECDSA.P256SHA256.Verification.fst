module Hacl.Impl.ECDSA.P256SHA256.Verification

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definitions
open Hacl.Impl.LowLevel
open Hacl.Impl.P256
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Impl.MM.Exponent

val isCoordinateValid: p: lbuffer uint64 (size 12) -> Stack bool 
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> h0 == h1 /\
    as_nat h1 (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h1 (gsub p (size 4) (size 4)) < prime /\
    as_nat h1 (gsub p (size 8) (size 4)) < prime
  )


let isCoordinateValid p = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    let x = sub p (size 0) (size 4) in 
    let y = sub p (size 4) (size 4) in 
    let z = sub p (size 8) (size 4) in 
    let carryX = sub4_il x prime256_buffer tempBuffer in 
    let carryY = sub4_il y prime256_buffer tempBuffer in 
    let carryZ = sub4_il z prime256_buffer tempBuffer in 

    let lessX = eq #U64  carryX (u64 0) in 
    let lessY = eq #U64 carryY (u64 0) in 
    let lessZ = eq #U64  carryZ (u64 0) in 

      pop_frame()  ; 
    lessX && lessY && lessZ



val isOrderCorrect: p: lbuffer uint64 (size 12) -> tempBuffer: lbuffer uint64 (size 100) ->  Stack bool
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> h0 == h1)

let isOrderCorrect p tempBuffer= 
  push_frame(); 
    let order = create (size 32) (u8 0) in 
    let multResult = create (size 4) (u64 0) in 
    upload_scalar order;
    scalarMultiplication p multResult order tempBuffer;
    let result = isPointAtInfinity multResult in 
 pop_frame();
   result
  




val ecdsa_verification: 
  pubKey: point -> 
  r: lbuffer uint64 (size 4) ->
  s: lbuffer uint64 (size 4) ->
  mLen: size_t ->
  m: lbuffer uint64 mLen -> 
  tempBuffer: lbuffer uint64 (size 10000) -> 
  Stack bool
    (requires fun h -> True)  
    (ensures fun h0 _ h1 -> True)


let ecdsa_verification pubKey r s mLen m tempBuffer = 
  push_frame();
    let tempBuffer = create (size 100) (u64 0) in 
    (*check that publicKey is not equal to the identity element O *)
  (*let pointInfinityPublicKey = isPointAtInfinity pubKey in 
    if pointInfinityPublicKey = true then false else *)
  let coordinatesValid = isCoordinateValid pubKey in
    if coordinatesValid = true then false else 
  let belongsToCurve =  isPointOnCurve pubKey in 
    if belongsToCurve = false then false else 
  let orderCorrect = isOrderCorrect pubKey tempBuffer in 
    if orderCorrect = false then false else true
