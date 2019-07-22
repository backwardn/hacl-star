module Hacl.Impl.ECDSA.Verification

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.ECDSA.Definition

assume val getPointLength : unit -> Tot size_t
let pointType  = lbuffer uint64 (getPointLength ())

assume val getHashFunctionLen: unit -> Tot size_t

noextract
let signature_len = getHashFunctionLen () 

assume val getPointInv: unit  -> Tot (mem -> pointType ->  Type0)
let pointInv = getPointInv ()


assume val getOrder: order:  lbuffer uint8 (size 32) -> Stack unit
  (requires fun h -> live h order)
  (ensures fun h0 _ h1 -> modifies1 order h0 h1) 

assume val getOrderLenght: unit -> Tot (size_t)

assume val isPointAtInfinity: p: pointType -> Stack bool 
  (requires fun h -> pointInv h p)
  (ensures fun h0 _ h1 -> h0 == h1)

assume val isPointAtCurve: p: pointType -> Stack bool 
  (requires fun h -> pointInv h p)
  (ensures fun h0 _ h1 -> h0 == h1)

assume val scalar_mult: p: pointType -> scalar: lbuffer uint8 (size 32) -> result: pointType -> Stack unit
  (requires fun h -> pointInv h p)
  (ensures fun h0 _ h1 -> pointInv h1 p /\ pointInv h1 result)


assume val compare_buffer_less: a: lbuffer uint64 (size 4) -> b: lbuffer uint64 (size 4) -> Stack bool 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

assume val compare_felem_equal: a: lbuffer uint64 (size 4) -> b: lbuffer uint64 (size 4) -> Stack bool
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


assume val hash_f: mLen: size_t -> m: lbuffer uint64 mLen -> bufferSign: lbuffer uint64 signature_len -> Stack bool
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

assume val inverse_mod: num: lbuffer uint64 (size 4) -> result: lbuffer uint64 (size 4) -> 
  Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

assume val mod_mul: num: lbuffer uint64 (size 4) -> num2: lbuffer uint64 (size 4) -> result: lbuffer uint64 (size 4) -> 
  Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

assume val mod_add: num: lbuffer uint64 (size 4) -> num2: lbuffer uint64 (size 4) -> result: lbuffer uint64 (size 4) -> 
  Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


val ecdsa_verification:  
  pubKey: pointType ->
  r: lbuffer uint64 (size 4) -> 
  s: lbuffer uint64 (size 4) -> 
  mLen: size_t -> 
  m: lbuffer uint64 mLen -> 
  tempBuffer: lbuffer uint64 (size 1000) -> 
  Stack bool 
    (requires fun h -> pointInv h pubKey )
    (ensures fun h0 _ h1 -> True)

let ecdsa_verification pubKey r s mLen m tempBuffer = 
  let bufferPAI = sub tempBuffer (size 0) (size 4) in 
  let inverseS = sub tempBuffer (size 4) (size 4) in
  let mul1 = sub tempBuffer (size 8) (size 4) in
  let mul2 = sub tempBuffer (size 12) (size 4) in 
  let bufferSignature = sub tempBuffer (size 4) signature_len in 
  

  let bufferOrder = create (size 32) (u8 0) in 
    getOrder bufferOrder;

  (* step1 *)
  let equalIdentity = isPointAtInfinity pubKey in 
    if equalIdentity = false then false else
  (*step 2*) 
  let onCurve = isPointAtCurve pubKey in 
    if onCurve = false then false else
  (* step 3*)
  let orderTrue = scalar_mult pubKey bufferOrder bufferPAI in 
  let orderTrueResult = isPointAtInfinity orderTrue in 
    if orderTrueResult = false then false else

  (* step 4 *)
  let compare1 = compare_buffer_less bufferOrder r in 
    if compare1 = false then false
    else 
  (* step 5*)   
  let compare2 = compare_buffer_less bufferOrder s in 
    if compare2 = false then false else
  
  let e = hash_f mLen m bufferSignature in 
    if e = false then false else
    
  let orderSize = getOrderLenght () in   
  let e_working = Lib.Buffer.sub #_ #_ #(v orderSize) bufferSignature (size 0) orderSize in 

  inverse_mod s inverseS;
  mod_mul inverseS e_working mul1; 
  mod_mul inverseS r mul2; 
  mod_add mul1 mul2 mul1;
  


  true 
  
    
