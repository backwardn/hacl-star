module Hacl.Spec.ECDSAP256.Definition

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open Lib.Buffer
open FStar.Mul

noextract
let prime_p256_order:pos =
  assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044369> 0);
  115792089210356248762697446949407573529996955224135760342422259061068512044369

inline_for_extraction
let felem = lbuffer uint64 (size 4)
inline_for_extraction 
let widefelem = lbuffer uint64 (size 8)


inline_for_extraction noextract
let felem4 = tuple4 uint64 uint64 uint64 uint64
inline_for_extraction noextract
let felem8 = tuple8 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64

noextract
val as_nat4: f:felem4 -> GTot nat
let as_nat4 f =
  let (s0, s1, s2, s3) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64


noextract
val wide_as_nat4: f:felem8 -> GTot nat
let wide_as_nat4 f =
  let (s0, s1, s2, s3, s4, s5, s6, s7) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64 +
  v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64



noextract
let as_nat (h:mem) (e:felem) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  as_nat4 (s0, s1, s2, s3)


noextract
let wide_as_nat (h:mem) (e:widefelem) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  let s5 = s.[5] in
  let s6 = s.[6] in
  let s7 = s.[7] in
  wide_as_nat4 (s0, s1, s2, s3, s4, s5, s6, s7)


noextract
let scalar_as_nat (h: mem) (e: lbuffer uint8 (size 32)) = 
    let s = as_seq h e in 
    let s0 = s.[0] in
    let s1 = s.[1] in
    let s2 = s.[2] in
    let s3 = s.[3] in
    let s4 = s.[4] in
    let s5 = s.[5] in
    let s6 = s.[6] in
    let s7 = s.[7] in
    let s8 = s.[8] in
    let s9 = s.[9] in
    let s10 = s.[10] in
    let s11 = s.[11] in
    let s12 = s.[12] in
    let s13 = s.[13] in
    let s14 = s.[14] in
    let s15 = s.[15] in
    let s16 = s.[16] in
    let s17 = s.[17] in
    let s18 = s.[18] in
    let s19 = s.[19] in
    let s20 = s.[20] in
    let s21 = s.[21] in
    let s22 = s.[22] in
    let s23 = s.[23] in
    let s24 = s.[24] in
    let s25 = s.[25] in
    let s26 = s.[26] in
    let s27 = s.[27] in
    let s28 = s.[28] in
    let s29 = s.[29] in
    let s30 = s.[30] in
    let s31 = s.[31] in
    v s0 + v s1 * pow2 8 + v s2 * (pow2 (2 * 8)) + 
    v s3 * (pow2 (3 * 8)) +
    v s4 * (pow2 (4 * 8)) +
    v s5 * (pow2 (5 * 8)) +
    v s6 * (pow2 (6 * 8)) +
    v s7 * (pow2 (7 * 8)) +
    v s8 * (pow2 (8 * 8)) +
    v s9 * (pow2 (9 * 8)) +
    v s10 * (pow2 (10 * 8)) +
    v s11 * (pow2 (11 * 8)) +
    v s12 * (pow2 (12 * 8)) +
    v s13 * (pow2 (13 * 8)) +
    v s14 * (pow2 (14 * 8)) +
    v s15 * (pow2 (15 * 8)) +
    v s16 * (pow2 (16 * 8)) +
    v s17 * (pow2 (17 * 8)) +
    v s18 * (pow2 (18 * 8)) +
    v s19 * (pow2 (19 * 8)) +
    v s20 * (pow2 (20 * 8)) +
    v s21 * (pow2 (21 * 8)) +
    v s22 * (pow2 (22 * 8)) +
    v s23 * (pow2 (23 * 8)) +
    v s24 * (pow2 (24 * 8)) +
    v s25 * (pow2 (25 * 8)) +
    v s26 * (pow2 (26 * 8)) +
    v s27 * (pow2 (27 * 8)) +
    v s28 * (pow2 (28 * 8)) +
    v s29 * (pow2 (29 * 8)) +
    v s30 * (pow2 (30 * 8)) +
    v s31 * (pow2 (31 * 8))

    



noextract
let felem_seq_as_nat_8 (a: lseq uint64 8) : Tot nat = 
  let open FStar.Mul in 
  let a0 = Lib.Sequence.index a 0 in 
  let a1 = Lib.Sequence.index a 1 in 
  let a2 = Lib.Sequence.index a 2 in 
  let a3 = Lib.Sequence.index a 3 in 
  let a4 = Lib.Sequence.index a 4 in 
  let a5 = Lib.Sequence.index a 5 in 
  let a6 = Lib.Sequence.index a 6 in 
  let a7 = Lib.Sequence.index a 7 in
  uint_v a0 + 
  uint_v a1 * pow2 64 + 
  uint_v a2 * pow2 64 * pow2 64 + 
  uint_v a3 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64

