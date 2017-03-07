module Hacl.Spec.EC.AddAndDouble2

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Fsquare
open Hacl.Spec.Bignum.Fmul
open Hacl.Spec.EC.AddAndDouble


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

let s_513 = s:seqelem{red_513 s}
let s_52 = s:seqelem{red_52 s}
let s_53 = s:seqelem{red_53 s}
let s_5413 = s:seqelem{red_5413 s}

let lemma_53_is_5413 (s:seqelem{red_53 s}) : Lemma (red_5413 s) = ()
let lemma_513_is_53 (s:seqelem{red_513 s}) : Lemma (red_53 s) = ()
let lemma_513_is_55 (s:seqelem{red_513 s}) : Lemma (red_55 s) = ()
let lemma_513_is_5413 (s:seqelem{red_513 s}) : Lemma (red_5413 s) = ()
let lemma_513_is_52 (s:seqelem{red_513 s}) : Lemma (red_52 s) = ()
let lemma_5413_is_55 (s:seqelem{red_5413 s}) : Lemma (Hacl.Spec.EC.AddAndDouble.red_55 s) = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val fmonty_tot:
  px:s_513 -> pz:s_513 ->
  pqx:s_513 -> pqz:s_513 ->
  qx:s_513 ->
  Tot (t:(s_513 * s_513 * s_513 * s_513){
    let x2 = selem (Mktuple4?._1 t) in
    let z2 = selem (Mktuple4?._2 t) in
    let x3 = selem (Mktuple4?._3 t) in
    let z3 = selem (Mktuple4?._4 t) in
    let x_2 = selem px in let z_2 = selem pz in
    let x_3 = selem pqx in let z_3 = selem pqz in let x_1 = selem qx in
    let a  = x_2 +@ z_2 in
    let aa = a *@ a in
    let b  = x_2 -@ z_2 in
    let bb = b *@ b in
    let e = aa -@ bb in
    let c = x_3 +@ z_3 in
    let d = x_3 -@ z_3 in
    let da = d *@ a in
    let cb = c *@ b in
    x3 = (da +@ cb) *@ (da +@ cb) /\ 
    z3 = x_1 *@ ((da -@ cb) *@ (da -@ cb)) /\
    x2 = aa *@ bb /\
    z2 = e *@ (aa +@ ((121665 % prime) *@ e))
    })
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let fmonty_tot px pz pqx pqz qx =
  fsum_513_is_53 px pz;
  let px' = fsum_tot px pz in
  (* assert(selem px' = selem px +@ selem pz); *) // a = x_2 + z2
  lemma_fdifference_unrolled'' pz px;
  lemma_fdifference_unrolled''' pz px;
  let pz' = fdifference_tot pz px in
  (* assert(selem pz' = selem px -@ selem pz); *) // b = x_2 - z2
  fsum_513_is_53 pqx pqz;
  let pqx' = fsum_tot pqx pqz in
  (* assert(selem pqx' = selem pqx +@ selem pqz); *) // c = x_3 + z_3
  lemma_fdifference_unrolled'' pqz pqx;
  let pqz' = fdifference_tot pqz pqx in
  (* assert(selem pqz' = selem pqx -@ selem pqz); *) // d = x_3 - z_3
  fmul_53_55_is_fine pqx' pz';
  let xxprime = fmul_tot pqx' pz' in // cb = c * b
  fmul_53_55_is_fine px' pqz';
  let zzprime = fmul_tot px' pqz' in // da = a * d <<<<
  fsum_513_is_53 xxprime zzprime;
  let xxprime' = fsum_tot xxprime zzprime in // cbda = cb + da <<<<
  lemma_fdifference_unrolled''' zzprime xxprime;
  let zzprime' = fdifference_tot zzprime xxprime in // da - cb
  lemma_53_is_5413 xxprime';
  fsquare_5413_is_fine xxprime';
  let x3 = fsquare_times_tot xxprime' 1 in // x3 = cbda ^ 2
  fsquare_5413_is_fine zzprime';
  let zzzprime = fsquare_times_tot zzprime' 1 in // zzzprime = (da - cb) ^ 2
  lemma_513_is_53 zzzprime; lemma_513_is_55 qx;
  fmul_53_55_is_fine zzzprime qx;
  let z3 = fmul_tot zzzprime qx in
  lemma_53_is_5413 px';
  fsquare_5413_is_fine px';
  let xx = fsquare_times_tot px' 1 in
  fsquare_5413_is_fine pz';
  let zz = fsquare_times_tot pz' 1 in
  lemma_513_is_53 xx;
  lemma_513_is_55 zz;
  fmul_53_55_is_fine xx zz;
  let x2 = fmul_tot xx zz in
  lemma_fdifference_unrolled''' zz xx;
  let zz' = fdifference_tot zz xx in
  let scalar = (uint64_to_limb Hacl.Bignum.Constants.a24) in
  fscalar_is_fine zz' scalar;
  let zzz = fscalar_tot zz' scalar in
  lemma_513_is_52 xx;
  fsum_52_is_53 zzz xx;
  let zzz' = fsum_tot zzz xx in
  lemma_5413_is_55 zz';
  fmul_53_55_is_fine zzz' zz';
  let z2 = fmul_tot zzz' zz' in
  (x2, z2, x3, z3)


val fmonty_tot_1:
  px:s_513 -> pz:s_513 ->
  pqx:s_513 -> pqz:s_513 ->
  qx:s_513 ->
  Tot (s_53 * s_5413 * s_513 * s_513)
let fmonty_tot_1 px pz pqx pqz qx =
  fsum_513_is_53 px pz;
  let px' = fsum_tot px pz in
  lemma_fdifference_unrolled'' pz px;
  lemma_fdifference_unrolled''' pz px;
  let pz' = fdifference_tot pz px in
  fsum_513_is_53 pqx pqz;
  let pqx' = fsum_tot pqx pqz in
  lemma_fdifference_unrolled'' pqz pqx;
  let pqz' = fdifference_tot pqz pqx in
  fmul_53_55_is_fine pqx' pz';
  let xxprime = fmul_tot pqx' pz' in
  fmul_53_55_is_fine px' pqz';
  let zzprime = fmul_tot px' pqz' in
  px', pz', xxprime, zzprime


val fmonty_tot_2:
  px':s_53 -> pz':s_5413 -> qx:s_513 -> xxprime:s_513 -> zzprime:s_513 ->
  Tot (s_513 * s_513 * s_513 * s_513)
let fmonty_tot_2 px' pz' qx xxprime zzprime =
  fsum_513_is_53 xxprime zzprime;
  let xxprime' = fsum_tot xxprime zzprime in
  lemma_fdifference_unrolled''' zzprime xxprime;
  let zzprime' = fdifference_tot zzprime xxprime in
  lemma_53_is_5413 xxprime';
  fsquare_5413_is_fine xxprime';
  let x3 = fsquare_times_tot xxprime' 1 in
  fsquare_5413_is_fine zzprime';
  let zzzprime = fsquare_times_tot zzprime' 1 in
  lemma_513_is_53 zzzprime; lemma_513_is_55 qx;
  fmul_53_55_is_fine zzzprime qx;
  let z3 = fmul_tot zzzprime qx in
  lemma_53_is_5413 px';
  fsquare_5413_is_fine px';
  let xx = fsquare_times_tot px' 1 in
  fsquare_5413_is_fine pz';
  let zz = fsquare_times_tot pz' 1 in
  x3, z3, xx, zz


val fmonty_tot_3: s_513 -> s_513 -> s_513 -> s_513 -> Tot (s_513 * s_513 * s_513 * s_513)
let fmonty_tot_3 x3 z3 xx zz =
  lemma_513_is_53 xx;
  lemma_513_is_55 zz;
  fmul_53_55_is_fine xx zz;
  let x2 = fmul_tot xx zz in
  lemma_fdifference_unrolled''' zz xx;
  let zz' = fdifference_tot zz xx in
  let scalar = (uint64_to_limb Hacl.Bignum.Constants.a24) in
  fscalar_is_fine zz' scalar;
  let zzz = fscalar_tot zz' scalar in
  lemma_513_is_52 xx;
  fsum_52_is_53 zzz xx;
  let zzz' = fsum_tot zzz xx in
  lemma_5413_is_55 zz';
  fmul_53_55_is_fine zzz' zz';
  let z2 = fmul_tot zzz' zz' in
  (x2, z2, x3, z3)


val lemma_fmonty_split:   px:s_513 -> pz:s_513 -> pqx:s_513 -> pqz:s_513 -> qx:s_513 ->
  Lemma (let px', pz', xxprime, zzprime = fmonty_tot_1 px pz pqx pqz qx in
    let x3, z3, xx, zz = fmonty_tot_2 px' pz' qx xxprime zzprime in
    let x2, z2, x3, z3 = fmonty_tot_3 x3 z3 xx zz in
    (x2, z2, x3, z3) == fmonty_tot px pz pqx pqz qx)
let lemma_fmonty_split px pz pqx pqz qx = ()
