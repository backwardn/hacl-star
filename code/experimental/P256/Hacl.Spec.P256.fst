module Hacl.Spec.P256

open FStar.Mul 
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Lemmas

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence


let prime = prime256
noextract
let _point_double  (p:point_nat) :  (p:point_nat) =
  let x, y, z = p in 
  let s = (4 * x * y * y) % prime256 in 
  let m = ((-3) * z * z * z * z + 3 * x * x) % prime256 in 
  let x3 = (m * m - 2 * s) % prime256 in 
  let y3 = (m * (s - x3) - 8 * y * y * y * y) % prime256 in 
  let z3 = (2 * y * z) % prime256 in 
  (x3, y3, z3)



noextract
let _point_add (p:point_nat) (q:point_nat) : point_nat = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in 

  let z2z2 = z2 * z2 in 
  let z1z1 = z1 * z1 in 

  let u1 = x1 * z2z2 % prime256 in 
  let u2 = x2 * z1z1 % prime256 in 

  assert_by_tactic (x1 * z2 * z2 = x1 * (z2 * z2)) canon;
  assert_by_tactic (x2 * z1 * z1 = x2 * (z1 * z1)) canon;
  
  let s1 = y1 * z2 * z2z2 % prime256 in 
  let s2 = y2 * z1 * z1z1 % prime256 in

  assert_by_tactic (y1 * z2 * (z2 * z2) = y1 * z2 * z2 * z2) canon;
  assert_by_tactic (y2 * z1 * (z1 * z1) = y2 * z1 * z1 * z1) canon;

  if u1 = u2 && s1 = s2 && z1 <> 0 && z2 <> 0 then 
     _point_double (x1, y1, z1) 
  else 
    begin

      let h = (u2 - u1) % prime256 in 
      let r = (s2 - s1) % prime256 in

      let rr = (r * r)in 
      let hh = (h * h) in 
      let hhh = (h * h * h) in  

  assert_by_tactic (forall (n: nat). n * h * h = n * (h * h)) canon; 
  assert_by_tactic (s1 * (h * h * h) = s1 * h * h * h) canon;
      let x3 = (rr - hhh - 2 * u1 * hh) % prime256 in 
  assert(x3 = (r * r - h * h * h - 2 * u1 * h * h) % prime256);
      let y3 = (r * (u1 * hh - x3) - s1 * hhh) % prime256 in
  assert(y3 = (r * (u1 * h*h - x3) - s1 * h*h*h) % prime256);
      let z3 = (h * z1 * z2) % prime256 in
      if z2 = 0 then 
  (x1, y1, z1) 
      else if z1 = 0 then
  (x2, y2, z2) 
      else  
  (x3, y3, z3)
    end 

let _norm (p:point_nat): (point_nat) =
  let (x, y, z) = p in 
  let z2 = z * z in 
  let z2i = modp_inv2_pow z2 in 
  let z3 = z * z * z in 
  let z3i = modp_inv2_pow z3 in 
  let x3 = (z2i * x) % prime256 in 
  let y3 = (z3i * y) % prime256 in 
  let z3 = 1 in 
  assert(x3 == (x * (pow (z * z) (prime256 -2) % prime256) % prime256));
  assert(y3 == (y * (pow (z * z * z) (prime256 - 2) % prime256) % prime256));
  assert(z3 == 1);
  (x3, y3, z3)


let scalar = lbytes 32

let ith_bit (k:lbytes 32) (i:nat{i < 256}) : uint64 =
  let q = i / 8 in let r = size (i % 8) in
  to_u64 ((index k q >>. r) &. u8 1)

val _ml_step0: p: point_nat -> q: point_nat -> tuple2 point_nat point_nat

let _ml_step0 r0 r1 = 
  let r0 = _point_add r1 r0 in
  let r1 = _point_double r1 in 
  (r0, r1) 

val _ml_step1: p: point_nat -> q: point_nat -> tuple2 point_nat point_nat

let _ml_step1 r0 r1 = 
  let r1 = _point_add r0 r1 in 
  let r0 = _point_double r0 in 
  (r0, r1)


val _ml_step: k: scalar->  i: nat{i < 256} ->  (tuple2 point_nat point_nat) -> Tot (r: tuple2 point_nat point_nat)

let _ml_step k i (p, q) = 
  let bit = 255 - i in 
  let bit = ith_bit k bit in 
  let open Lib.RawIntTypes in 
  if uint_to_nat bit = 0 then 
      _ml_step1 p q 
  else _ml_step0 p q  


val montgomery_ladder_spec: k: scalar -> tuple2 point_nat point_nat -> Tot (tuple2 point_nat point_nat)

let montgomery_ladder_spec k (p, q) = 
  Lib.LoopCombinators.repeati 256  (_ml_step k) (p, q)


val scalar_multiplication: k: scalar -> p: point_nat -> Tot point_nat
  
let scalar_multiplication k p = 
  let pai = (0, 0, 0) in 
  let q, f = montgomery_ladder_spec k (pai, p) in 
  _norm q


val isPointAtInfinity: p: point_nat -> Tot bool

let isPointAtInfinity p = 
    let (x, y, z) = p in 
    z = 0


val isPointOnCurve: p: point_nat -> Tot bool

let isPointOnCurve p = 
  let (x, y, z) = p in 
  if (y * y) % prime = (x * x * x - 3 * x - 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime then 
  true
  else false