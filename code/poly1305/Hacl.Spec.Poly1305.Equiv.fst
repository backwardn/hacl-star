module Hacl.Spec.Poly1305.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Loops = Lib.LoopCombinators
module S = Spec.Poly1305
module Lemmas = Hacl.Spec.Poly1305.Equiv.Lemmas

include Hacl.Spec.Poly1305.Vec

#reset-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -Hacl.Spec.*'"

val poly_update_repeat_blocks_multi_lemma:
    #w:lanes
  -> text:bytes{length text % (w * size_block) = 0}
  -> acc:elem w
  -> r:pfelem ->
  Lemma
    (normalize_n #w (repeat_blocks_multi #uint8 #(elem w) (w * size_block) text (poly1305_update_nblocks #w (compute_rw #w r)) acc) r ==
      repeat_blocks_multi #uint8 #pfelem size_block text (S.poly1305_update1 r size_block) (normalize_n #w acc r))
let poly_update_repeat_blocks_multi_lemma #w text acc r =
  match w with
  | 1 -> Lemmas.poly_update_repeat_blocks_multi_lemma1 text acc r
  | 2 -> Lemmas.poly_update_repeat_blocks_multi_lemma2 text acc r
  | 4 -> Lemmas.poly_update_repeat_blocks_multi_lemma4 text acc r

val poly_update_multi_lemma_load:
    #w:lanes
  -> text:bytes{0 < length text /\ length text % (w * size_block) = 0}
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
   (let t0 = Seq.slice text 0 (w * size_block) in
    normalize_n #w (load_acc #w acc0 t0) r ==
      repeat_blocks_multi #uint8 #pfelem size_block t0 (S.poly1305_update1 r size_block) acc0)
let poly_update_multi_lemma_load #w text acc0 r =
  match w with
  | 1 -> Lemmas.poly_update_multi_lemma_load1 text acc0 r
  | 2 -> Lemmas.poly_update_multi_lemma_load2 text acc0 r
  | 4 -> Lemmas.poly_update_multi_lemma_load4 text acc0 r

val repeati_extensionality:
    #a:Type
  -> n:nat
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{i < n} -> a -> a)
  -> acc0:a ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g i acc))
  (ensures (Loops.repeati n f acc0 == Loops.repeati n g acc0))
let rec repeati_extensionality #a n f g acc0 =
  if n = 0 then begin
    Loops.eq_repeati0 n f acc0;
    Loops.eq_repeati0 n g acc0 end
  else begin
    Loops.unfold_repeati n f acc0 (n-1);
    Loops.unfold_repeati n g acc0 (n-1);
    repeati_extensionality #a (n-1) f g acc0 end

val repeati_right_extensionality:
    #a:Type
  -> n:nat
  -> lo_g:nat
  -> hi_g:nat{lo_g + n <= hi_g}
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{lo_g <= i /\ i < hi_g} -> a -> a)
  -> acc0:a ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g (lo_g + i) acc))
  (ensures (Loops.repeat_right 0 n (Loops.fixed_a a) f acc0 ==
    Loops.repeat_right lo_g (lo_g + n) (Loops.fixed_a a) g acc0))
let rec repeati_right_extensionality #a n lo_g hi_g f g acc0 =
  if n = 0 then begin
    Loops.eq_repeat_right 0 n (Loops.fixed_a a) f acc0;
    Loops.eq_repeat_right lo_g (lo_g+n) (Loops.fixed_a a) g acc0 end
  else begin
    Loops.unfold_repeat_right 0 n (Loops.fixed_a a) f acc0 (n-1);
    Loops.unfold_repeat_right lo_g (lo_g+n) (Loops.fixed_a a) g acc0 (lo_g+n-1);
    repeati_right_extensionality #a (n-1) lo_g hi_g f g acc0 end

//
// Lemma
//   (poly_update_multi #w text acc0 r ==
//      repeat_blocks_multi #uint8 #pfelem size_block text (update1 r size_block) acc0)
//

#set-options "--max_fuel 0"

val poly_update_multi_lemma1:
    #w:lanes
  -> text:bytes{0 < length text /\ length text % (w * size_block) = 0}
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
   (let rw = compute_rw #w r in
    let len = length text in
    let len0 = w * size_block in
    let t0 = Seq.slice text 0 len0 in
    let f = S.poly1305_update1 r size_block in
    let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in
    normalize_n #w (load_acc #w acc0 t0) r ==
      Loops.repeat_right 0 (len0 / size_block) (Loops.fixed_a pfelem) repeat_bf_t0 acc0)
let poly_update_multi_lemma1 #w text acc0 r =
  let rw = compute_rw #w r in
  let len = length text in
  let len0 = w * size_block in
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;

  let f = S.poly1305_update1 r size_block in
  let repeat_bf_s0 = repeat_blocks_f size_block t0 f (len0 / size_block) in
  let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in

  let aux_repeat_bf (i:nat{i < len0 / size_block}) (acc:pfelem) : Lemma
    (repeat_bf_s0 i acc == repeat_bf_t0 i acc)
    = let nb = len0 / size_block in
      assert ((i+1) * size_block <= nb * size_block);
      let block = Seq.slice text (i*size_block) (i*size_block+size_block) in
      FStar.Seq.lemma_len_slice text (i*size_block) (i*size_block+size_block);
      assert (repeat_bf_s0 i acc == f block acc);
      assert (repeat_bf_t0 i acc == f block acc)
  in

  let acc1 = load_acc #w acc0 t0 in
  poly_update_multi_lemma_load #w text acc0 r;
  //assert (normalize_n #w acc1 r == repeat_blocks_multi #uint8 #pfelem size_block t0 (S.poly1305_update1 r size_block) acc0);
  lemma_repeat_blocks_multi #uint8 #pfelem size_block t0 (S.poly1305_update1 r size_block) acc0;
  //assert (normalize_n #w acc1 r == Loops.repeati (len0 / size_block) repeat_bf_s0 acc0);

  FStar.Classical.forall_intro_2 (aux_repeat_bf);
  repeati_extensionality #pfelem (len0 / size_block) repeat_bf_s0 repeat_bf_t0 acc0;
  assert (Loops.repeati (len0 / size_block) repeat_bf_s0 acc0 == Loops.repeati (len0 / size_block) repeat_bf_t0 acc0);

  assert (normalize_n #w acc1 r == Loops.repeati (len0 / size_block) repeat_bf_t0 acc0);
  Loops.repeati_def (len0 / size_block) repeat_bf_t0 acc0

val poly_update_multi_lemma2:
    #w:lanes
  -> text:bytes{0 < length text /\ length text % (w * size_block) = 0}
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
   (let rw = compute_rw #w r in
    let len = length text in
    let len0 = w * size_block in
    let t0 = Seq.slice text 0 len0 in
    let t1 = Seq.slice text len0 len in
    let f = S.poly1305_update1 r size_block in
    let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in

    let acc1 = load_acc #w acc0 t0 in
    let acc2 = repeat_blocks_multi #uint8 #(elem w) (w * size_block) t1 (poly1305_update_nblocks #w rw) acc1 in
    normalize_n #w acc2 r ==
      Loops.repeat_right (len0 / size_block) (len / size_block)
        (Loops.fixed_a pfelem) repeat_bf_t1 (normalize_n #w acc1 r))
let poly_update_multi_lemma2 #w text acc0 r =
  let rw = compute_rw #w r in
  let len = length text in
  let len0 = w * size_block in
  let len1 = len - len0 in
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;
  let t1 = Seq.slice text len0 len in
  FStar.Seq.Base.lemma_len_slice text len0 len;

  let f = S.poly1305_update1 r size_block in
  let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
  let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in

  let i_start = len0 / size_block in
  let nb = len1 / size_block in
  assert (i_start + nb = len / size_block);

  let aux_repeat_bf (i:nat{i < nb}) (acc:pfelem) : Lemma
    (repeat_bf_s1 i acc == repeat_bf_t1 (i_start + i) acc)
    =
      let start = i_start * size_block in
      assert (start + (i+1) * size_block <= start + nb * size_block);
      let block = Seq.slice text (start+i*size_block) (start+i*size_block+size_block) in
      FStar.Seq.lemma_len_slice text (start+i*size_block) (start+i*size_block+size_block);
      assert (repeat_bf_s1 i acc == f block acc);
      assert (repeat_bf_t1 (len0 / size_block + i) acc == f block acc)
  in

  let acc1 = load_acc #w acc0 t0 in
  let acc2 = repeat_blocks_multi #uint8 #(elem w) (w * size_block) t1 (poly1305_update_nblocks #w rw) acc1 in
  let acc3 = normalize_n #w acc2 r in
  assert (acc3 == poly1305_update_multi #w text acc0 r);
  poly_update_repeat_blocks_multi_lemma #w t1 acc1 r;
  //assert (acc3 == repeat_blocks_multi #uint8 #pfelem size_block t1 (S.poly1305_update1 r size_block) (normalize_n #w acc1 r));
  lemma_repeat_blocks_multi #uint8 #pfelem size_block t1 (S.poly1305_update1 r size_block) (normalize_n #w acc1 r);
  //assert (acc3 == Loops.repeati (len1 / size_block) repeat_bf_s1 (normalize_n #w acc1 r));
  let acc1_s = normalize_n #w acc1 r in
  Loops.repeati_def (len1 / size_block) repeat_bf_s1 acc1_s;
  //assert (acc3 == Loops.repeat_right 0 (len1 / size_block) (Loops.fixed_a pfelem) repeat_bf_s1 acc1_s);

  FStar.Classical.forall_intro_2 (aux_repeat_bf);
  repeati_right_extensionality nb i_start (nb+i_start) repeat_bf_s1 repeat_bf_t1 acc1_s;
  assert (
    Loops.repeat_right 0 nb (Loops.fixed_a pfelem) repeat_bf_s1 acc1_s ==
    Loops.repeat_right i_start (i_start+nb) (Loops.fixed_a pfelem) repeat_bf_t1 acc1_s);

  assert (acc3 ==
    Loops.repeat_right (len0 / size_block) (len / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_t1 acc1_s)

val poly_update_multi_lemma:
    #w:lanes
  -> text:bytes{0 < length text /\ length text % (w * size_block) = 0}
  -> acc0:pfelem
  -> r:pfelem ->
    Lemma
    (poly1305_update_multi #w text acc0 r ==
      repeat_blocks_multi #uint8 #pfelem size_block text (S.poly1305_update1 r size_block) acc0)
let poly_update_multi_lemma #w text acc0 r =
  let rw = compute_rw #w r in
  let len = length text in
  let f = S.poly1305_update1 r size_block in
  let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in

  let len0 = w * size_block in
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;
  let t1 = Seq.slice text len0 len in
  FStar.Seq.Base.lemma_len_slice text len0 len;

  let acc1 = load_acc #w acc0 t0 in
  let acc2 = repeat_blocks_multi #uint8 #(elem w) (w * size_block) t1 (poly1305_update_nblocks #w rw) acc1 in
  let acc3 = normalize_n #w acc2 r in
  assert (acc3 == poly1305_update_multi #w text acc0 r);
  poly_update_repeat_blocks_multi_lemma #w t1 acc1 r;
  assert (acc3 == repeat_blocks_multi #uint8 #pfelem size_block t1 (S.poly1305_update1 r size_block) (normalize_n acc1 r));
  poly_update_multi_lemma2 #w text acc0 r;
  assert (acc3 ==
   Loops.repeat_right (len0 / size_block) (len / size_block)
     (Loops.fixed_a pfelem) repeat_bf_t0 (normalize_n #w acc1 r));

  poly_update_multi_lemma1 #w text acc0 r;

  Loops.repeat_right_plus
    0 (len0 / size_block) (len / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_t0 acc0;
  assert (acc3 ==
    Loops.repeat_right 0 (len / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_t0 acc0);
  Loops.repeati_def (len / size_block) repeat_bf_t0 acc0;
  lemma_repeat_blocks_multi #uint8 #pfelem size_block text (S.poly1305_update1 r size_block) acc0;
  assert (acc3 == repeat_blocks_multi #uint8 #pfelem size_block text (S.poly1305_update1 r size_block) acc0)

//
// Lemma
//   (poly #w text acc0 r == S.poly1305_update1 text acc0 r)
//

val poly_eq_lemma1:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
  (requires (
    let len = length text in
    let sz_block = w * size_block in
    len / sz_block * sz_block > 0))
  (ensures (
    let len = length text in
    let sz_block = w * size_block in
    let len0 = len / sz_block * sz_block in
    let f = S.poly1305_update1 r size_block in
    let t0 = Seq.slice text 0 len0 in
    let repeat_bf_s0 = repeat_blocks_f size_block t0 f (len0 / size_block) in
    let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in
    Loops.repeati (len0 / size_block) repeat_bf_s0 acc0 ==
      Loops.repeat_right 0 (len0 / size_block) (Loops.fixed_a pfelem) repeat_bf_t0 acc0))
let poly_eq_lemma1 #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;

  let f = S.poly1305_update1 r size_block in
  let repeat_bf_s0 = repeat_blocks_f size_block t0 f (len0 / size_block) in
  let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in

  let aux_repeat_bf (i:nat{i < len0 / size_block}) (acc:pfelem) : Lemma
    (repeat_bf_s0 i acc == repeat_bf_t0 i acc)
    = let nb = len0 / size_block in
      assert ((i+1) * size_block <= nb * size_block);
      let block = Seq.slice text (i*size_block) (i*size_block+size_block) in
      FStar.Seq.lemma_len_slice text (i*size_block) (i*size_block+size_block);
      assert (repeat_bf_s0 i acc == f block acc);
      assert (repeat_bf_t0 i acc == f block acc)
  in

  let acc1 = poly1305_update_multi #w t0 acc0 r in
  poly_update_multi_lemma #w t0 acc0 r;
  lemma_repeat_blocks_multi #uint8 #pfelem size_block t0 (S.poly1305_update1 r size_block) acc0;

  FStar.Classical.forall_intro_2 (aux_repeat_bf);
  repeati_extensionality #pfelem (len0 / size_block) repeat_bf_s0 repeat_bf_t0 acc0;
  assert (Loops.repeati (len0 / size_block) repeat_bf_s0 acc0 == Loops.repeati (len0 / size_block) repeat_bf_t0 acc0);

  assert (acc1 == Loops.repeati (len0 / size_block) repeat_bf_t0 acc0);
  Loops.repeati_def (len0 / size_block) repeat_bf_t0 acc0

val poly_eq_lemma2:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
  (requires (
    let len = length text in
    let sz_block = w * size_block in
    len / sz_block * sz_block > 0))
  (ensures (
    let len = length text in
    let sz_block = w * size_block in
    let len0 = len / sz_block * sz_block in
    let len1 = len - len0 in
    let t0 = Seq.slice text 0 len0 in
    let t1 = Seq.slice text len0 len in

    let f = S.poly1305_update1 r size_block in
    let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
    let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in

    let acc1 = poly1305_update_multi #w t0 acc0 r in
    Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 ==
      Loops.repeat_right (len0 / size_block) (len / size_block) (Loops.fixed_a pfelem) repeat_bf_t1 acc1))
let poly_eq_lemma2 #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  FStar.Math.Lemmas.multiple_modulo_lemma len0 size_block;
  assert (len0 % size_block = 0);
  let len1 = len - len0 in
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;
  let t1 = Seq.slice text len0 len in
  FStar.Seq.Base.lemma_len_slice text len0 len;

  let f = S.poly1305_update1 r size_block in
  let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
  let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in

  let i_start = len0 / size_block in
  let nb = len1 / size_block in
  assert (i_start + nb = len / size_block);

  let aux_repeat_bf (i:nat{i < nb}) (acc:pfelem) : Lemma
    (repeat_bf_s1 i acc == repeat_bf_t1 (i_start + i) acc)
    =
      let start = i_start * size_block in
      assert (start + (i+1) * size_block <= start + nb * size_block);
      let block = Seq.slice text (start+i*size_block) (start+i*size_block+size_block) in
      FStar.Seq.lemma_len_slice text (start+i*size_block) (start+i*size_block+size_block);
      assert (repeat_bf_s1 i acc == f block acc);
      assert (repeat_bf_t1 (i_start + i) acc == f block acc)
  in

  let acc1 = poly1305_update_multi #w t0 acc0 r in
  let acc3 = Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 in
  Loops.repeati_def (len1 / size_block) repeat_bf_s1 acc1;

  FStar.Classical.forall_intro_2 (aux_repeat_bf);
  repeati_right_extensionality nb i_start (nb+i_start) repeat_bf_s1 repeat_bf_t1 acc1;
  assert (
    Loops.repeat_right 0 nb (Loops.fixed_a pfelem) repeat_bf_s1 acc1 ==
    Loops.repeat_right i_start (i_start+nb) (Loops.fixed_a pfelem) repeat_bf_t1 acc1);

  assert (
    acc3 == Loops.repeat_right (len0 / size_block) (len / size_block) (Loops.fixed_a pfelem) repeat_bf_t1 acc1)

val poly_eq_lemma12:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
  (requires (
    let len = length text in
    let sz_block = w * size_block in
    len / sz_block * sz_block > 0))
  (ensures (
    let len = length text in
    let sz_block = w * size_block in
    let len0 = len / sz_block * sz_block in
    let len1 = len - len0 in
    let f = S.poly1305_update1 r size_block in
    let repeat_bf_s1 = repeat_blocks_f size_block (Seq.slice text len0 len) f (len1 / size_block) in
    let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in

    let acc1 = poly1305_update_multi #w (Seq.slice text 0 len0) acc0 r in
    Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 ==
      Loops.repeati (len / size_block) repeat_bf_t1 acc0))
let poly_eq_lemma12 #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  assert (len0 % size_block = 0);
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;
  let acc1 = poly1305_update_multi #w t0 acc0 r in
  poly_update_multi_lemma #w t0 acc0 r;
  lemma_repeat_blocks_multi #uint8 #pfelem size_block t0 (S.poly1305_update1 r size_block) acc0;

  let f = S.poly1305_update1 r size_block in
  let repeat_bf_s0 = repeat_blocks_f size_block (Seq.slice text 0 len0) f (len0 / size_block) in
  let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in
  assert (acc1 == Loops.repeati (len0 / size_block) repeat_bf_s0 acc0);
  poly_eq_lemma1 #w text acc0 r;
  assert (acc1 ==
    Loops.repeat_right 0 (len0 / size_block)
    (Loops.fixed_a pfelem) repeat_bf_t0 acc0);

  let t1 = Seq.slice text len0 len in
  let len1 = len - len0 in
  FStar.Seq.Base.lemma_len_slice text len0 len;
  let acc2 = S.poly1305_update t1 acc1 r in
  lemma_repeat_blocks #uint8 #pfelem size_block t1 f (S.poly1305_update_last r) acc1;

  let repeat_bf_s1 = repeat_blocks_f size_block (Seq.slice text len0 len) f (len1 / size_block) in
  let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in
  let acc3 = Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 in
  poly_eq_lemma2 #w text acc0 r;
  assert (acc3 ==
    Loops.repeat_right (len0 / size_block) (len / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_t1 acc1);

  Loops.repeat_right_plus
    0 (len0 / size_block) (len / size_block)
    (Loops.fixed_a pfelem)
    (repeat_blocks_f size_block text (S.poly1305_update1 r size_block) (len / size_block)) acc0;
  assert (acc3 ==
    Loops.repeat_right 0 (len / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_t1 acc0);
  Loops.repeati_def (len / size_block) repeat_bf_t1 acc0

val poly_eq_lemma_pos:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
  (requires (
    let len = length text in
    let sz_block = w * size_block in
    len / sz_block * sz_block > 0))
  (ensures poly1305_update #w text acc0 r == S.poly1305_update text acc0 r)
let poly_eq_lemma_pos #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  assert (len0 % size_block = 0);
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;
  let acc1 = poly1305_update_multi #w t0 acc0 r in

  let t1 = Seq.slice text len0 len in
  let len1 = len - len0 in
  FStar.Seq.Base.lemma_len_slice text len0 len;
  let acc2 = S.poly1305_update t1 acc1 r in

  let f = S.poly1305_update1 r size_block in
  lemma_repeat_blocks #uint8 #pfelem size_block t1 f (S.poly1305_update_last r) acc1;

  let repeat_bf_s1 = repeat_blocks_f size_block (Seq.slice text len0 len) f (len1 / size_block) in
  let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in
  let acc3 = Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 in
  let last = Seq.slice t1 (len1 / size_block * size_block) len1 in
  let acc4 = S.poly1305_update_last r (len1 % size_block) last acc3 in
  assert (acc2 == acc4);

  poly_eq_lemma12 #w text acc0 r;
  assert (acc3 == Loops.repeati (len / size_block) repeat_bf_t1 acc0);

  assert (last == Seq.slice (Seq.slice text len0 len) (len1 / size_block * size_block) len1);
  FStar.Seq.Properties.slice_slice text len0 len (len1 / size_block * size_block) len1;
  assert (last == Seq.slice text (len / size_block * size_block) len);

  lemma_repeat_blocks #uint8 #pfelem size_block text f (S.poly1305_update_last r) acc0


val poly_eq_lemma_zero:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
  (requires length text < w*size_block)
  (ensures poly1305_update #w text acc0 r == S.poly1305_update text acc0 r)
let poly_eq_lemma_zero #w text acc0 r = ()

val poly_eq_lemma:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
    (poly1305_update #w text acc0 r == S.poly1305_update text acc0 r)
let poly_eq_lemma #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  if len0 > 0 then
    poly_eq_lemma_pos #w text acc0 r
  else
    poly_eq_lemma_zero #w text acc0 r

val poly1305_vec_is_poly1305:
    #w:lanes
  -> msg:bytes
  -> k:S.key ->
  Lemma
    (poly1305_mac #w msg k == S.poly1305_mac msg k)
let poly1305_vec_is_poly1305 #w msg k =
  let acc0, r = S.poly1305_init k in
  poly_eq_lemma #w msg acc0 r
