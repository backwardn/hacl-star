module Hacl.Spec.P256

open FStar.Mul 
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Lemmas


let _norm (p:point_nat): (point_nat) =
  let (x, y, z) = p in 
  let z2 = z * z in 
  let z2i = modp_inv2_pow z2 in 
  let z3 = z * z * z in 
  let z3i = modp_inv2_pow z3 in 
  let x3 = (z2i * x) % prime in 
  let y3 = (z3i * y) % prime in 
  let z3 = 1 in 
  assert(x3 == (x * (pow (z * z) (prime -2) % prime) % prime));
  assert(y3 == (y * (pow (z * z * z) (prime - 2) % prime) % prime));
  assert(z3 == 1);
  (x3, y3, z3)
