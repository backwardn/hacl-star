module Hacl.Spec.ECDSA.Definition

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

noextract
assume val as_nat: h: mem -> Tot nat

