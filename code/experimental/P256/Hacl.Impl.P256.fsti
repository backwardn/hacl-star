module Hacl.Impl.P256

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer

open  Hacl.Spec.P256.Core
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.SolinasReduction
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256.MontgomeryMultiplication.PointDouble
open Hacl.Spec.P256.MontgomeryMultiplication.PointAdd
open Hacl.Spec.P256.Normalisation 
open Hacl.Spec.P256.Ladder

open Hacl.Spec.P256

open Lib.Loops
open FStar.Math.Lemmas

module B = LowStar.Buffer
open FStar.Mul


noextract 
let point_x_as_nat (h: mem) (e: point) : GTot nat = 
  let open Lib.Sequence in 
  let s = as_seq h e in 
  let s0 = s.[0] in
  let s1 = s.[1] in 
  let s2 = s.[2] in 
  let s3 = s.[3] in 
  as_nat4 (s0, s1, s2, s3)

noextract 
let point_y_as_nat (h: mem) (e: point) : GTot nat = 
  let open Lib.Sequence in 
  let s = as_seq h e in 
  let s0 = s.[4] in
  let s1 = s.[5] in 
  let s2 = s.[6] in 
  let s3 = s.[7] in 
  as_nat4 (s0, s1, s2, s3)

noextract 
let point_z_as_nat (h: mem) (e: point) : GTot nat = 
  let open Lib.Sequence in 
  let s = as_seq h e in 
  let s0 = s.[8] in
  let s1 = s.[9] in 
  let s2 = s.[10] in 
  let s3 = s.[11] in 
  as_nat4 (s0, s1, s2, s3)


val pointToDomain: p: point -> result: point -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ eq_or_disjoint p result /\ 
    point_x_as_nat h p < prime /\ point_y_as_nat h p < prime /\ point_z_as_nat h p < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    point_x_as_nat h1 result == toDomain_ (point_x_as_nat h0 p) /\
    point_y_as_nat h1 result == toDomain_ (point_y_as_nat h0 p) /\
    point_z_as_nat h1 result == toDomain_ (point_z_as_nat h0 p))


val pointFromDomain: p: point -> result: point-> Stack unit 
  (requires fun h -> live h p /\ live h result /\ eq_or_disjoint p result /\ 
  point_x_as_nat h p < prime /\ point_y_as_nat h p < prime /\ point_z_as_nat h p < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    point_x_as_nat h1 result == fromDomain_ (point_x_as_nat h0 p) /\
    point_y_as_nat h1 result == fromDomain_ (point_y_as_nat h0 p) /\
    point_z_as_nat h1 result == fromDomain_ (point_z_as_nat h0 p))


val point_double: p: point -> result: point -> tempBuffer: lbuffer uint64 (size 88) -> Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ live h result /\
    disjoint p tempBuffer /\ disjoint result tempBuffer /\
    eq_or_disjoint p result /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime)
  (ensures fun h0 _ h1 -> modifies2 tempBuffer result  h0 h1 /\  
    as_seq h1 result == point_double_seq (as_seq h0 p) /\
    as_nat h1 (gsub result (size 8) (size 4)) < prime /\ 
    as_nat h1 (gsub result (size 0) (size 4)) < prime /\ 
    as_nat h1 (gsub result (size 4) (size 4)) < prime 
  ) 


 
val compare_felem: a: felem -> b: felem -> Stack uint64
  (requires fun h -> live h a /\ live h b /\ as_nat h a < prime /\ as_nat h b < prime ) 
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r == compare_felem_seq (as_seq h0 a) (as_seq h0 b)) 

val point_add: p: point -> q: point -> result: point -> tempBuffer: lbuffer uint64 (size 88) -> 
   Stack unit (requires fun h -> live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
   eq_or_disjoint q result /\
   disjoint p q /\ disjoint p tempBuffer /\ disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    as_nat h (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub q (size 8) (size 4)) < prime /\ 
    as_nat h (gsub q (size 0) (size 4)) < prime /\  
    as_nat h (gsub q (size 4) (size 4)) < prime 
    ) 
   (ensures fun h0 _ h1 -> 
     modifies2 tempBuffer result h0 h1 /\ 
     as_seq h1 result == point_add_seq (as_seq h0 p) (as_seq h0 q) /\
     as_nat h1 (gsub result (size 8) (size 4)) < prime /\ 
     as_nat h1 (gsub result (size 0) (size 4)) < prime /\ 
     as_nat h1 (gsub result (size 4) (size 4)) < prime 
  )


val norm: p: point -> resultPoint: point -> tempBuffer: lbuffer uint64 (size 88) -> Stack unit
  (requires fun h -> live h p /\ live h resultPoint /\ live h tempBuffer /\ disjoint p tempBuffer /\ disjoint tempBuffer resultPoint /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime 
  ) 
  (ensures fun h0 _ h1 -> 
      modifies2 tempBuffer resultPoint h0 h1 /\	(
      let x3 = point_x_as_nat h1 resultPoint in  
      let y3 = point_y_as_nat h1 resultPoint in 
      let z3 = point_z_as_nat h1 resultPoint in 

      let xD = fromDomain_ (point_x_as_nat h0 p) in 
      let yD = fromDomain_ (point_y_as_nat h0 p) in 
      let zD = fromDomain_ (point_z_as_nat h0 p) in 

      let (xN, yN, zN) = _norm (xD, yD, zD) in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
   )   
  )



val scalarMultiplication: p: point -> result: point -> 
  scalar: lbuffer uint8 (size 32) -> 
  tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h -> 
      live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    eq_or_disjoint p result /\
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime
    )
  (ensures fun h0 _ h1 -> modifies3 p result tempBuffer h0 h1 /\
    (
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      let (xN, yN, zN) = scalar_multiplication (as_seq h0 scalar) (point_prime_to_coordinates (as_seq h0 p)) in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
  )
) 

val secretToPublic: result: point -> scalar: lbuffer uint8 (size 32) -> 
 tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (
      requires fun h -> 
      live h result /\ live h scalar /\ live h tempBuffer /\
      LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc result]
    )
  (
    ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1
  )  


val isPointAtInfinity: p: point -> Stack bool
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> h0 == h1) 

val isPointOnCurve: p: point -> Stack bool
  (requires fun h -> live h p /\    
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime)

  (ensures fun h0 r h1 ->      
    modifies0 h0 h1 /\ 
    (
      let x = gsub p (size 0) (size 4) in 
      let y = gsub p (size 4) (size 4) in 
      let x_ = as_nat h0 x in  if r = false then (as_nat h0 y) * (as_nat h0 y) % prime <>  (x_ * x_ * x_ - 3 * x_ - 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime
       else
       (as_nat h0 y) * (as_nat h0 y) % prime == (x_ * x_ * x_ - 3 * x_ - 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime))


