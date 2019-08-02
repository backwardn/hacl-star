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
open Hacl.Impl.MontgomeryMultiplication
open Hacl.Impl.MM.Exponent
open Hacl.Spec.P256.Core

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

inline_for_extraction noextract
val equalZeroBuffer: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> h0 == h1)

let equalZeroBuffer f =        
    let f0 = index f (size 0) in 
    let f1 = index f (size 1) in 
    let f2 = index f (size 2) in 
    let f3 = index f (size 3) in 

    let z0_zero = eq_0_u64 f0 in 
    let z1_zero = eq_0_u64 f1 in 
    let z2_zero = eq_0_u64 f2 in 
    let z3_zero = eq_0_u64 f3 in 
  
    z0_zero && z1_zero && z2_zero && z3_zero
  
  
val isMoreThanZeroLessThanOrderMinusOne: f: felem -> order: felem ->  Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> h0 == h1)

let isMoreThanZeroLessThanOrderMinusOne f order = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    let carry = sub4 f order tempBuffer in 
    let less = eq #U64 carry (u64 0) in 
    let more = equalZeroBuffer f in 
    less && more


val isOrderCorrect: p: lbuffer uint64 (size 12) -> order: felem -> tempBuffer: lbuffer uint64 (size 100) ->  Stack bool
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> h0 == h1)

let isOrderCorrect p order tempBuffer= 
  push_frame(); 
    let multResult = create (size 4) (u64 0) in 
    upload_scalar order;
    scalarMultiplication p multResult order tempBuffer;
    let result = isPointAtInfinity multResult in 
 pop_frame();
   result


open Lib.ByteBuffer 

val toUint64: i: lbuffer uint8 (32ul) -> o: felem ->  Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies1 o h0 h1)

let toUint64 i o = 
  uints_from_bytes_le o i


val toUint8: i: felem ->  o: lbuffer uint8 (32ul) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies1 o h0 h1)

let toUint8 i o = 
  uints_to_bytes_le (size 4) o i


inline_for_extraction
let hLen = 32ul

assume val hash:
    mHash:lbuffer uint8 (v hLen)
  -> len:size_t
  -> m:lbuffer uint8 (v len)
  -> Stack unit
    (requires fun h -> live h mHash /\ live h m /\ disjoint m mHash)
    (ensures  fun h0 _ h1 -> modifies  mHash h0 h1)



val ecdsa_verification: 
  pubKey: point -> 
  r: lbuffer uint64 (size 4) ->
  s: lbuffer uint64 (size 4) ->
  mLen: size_t ->
  m: lbuffer uint8 (v mLen) -> 
  Stack bool
    (requires fun h -> True)  
    (ensures fun h0 _ h1 -> True)


let ecdsa_verification pubKey r s mLen m = 
  push_frame();
    let mHash = create (size 32) (u8 0) in 
    let hashAsFelem = create (size 4) (u64 0) in 
    let tempBuffer = create (size 100) (u64 0) in 
    let order = create (size 32) (u8 0) in 
    let inverseS = create (size 4) (u64 0) in 
    let u1 = create (size 4) (u64 0) in 
    let u2 = create (size 4) (u64 0) in 

    let bufferU1 = create (size 32) (u8 0) in 
    let bufferU2 = create (size 32) (u8 0) in 

    let pointu1G = create (size 12) (u64 0) in 
    let pointu2Q = create (size 12) (u64 0) in 
    let pointSum = create (size 12) (u64 0) in 
    let xBuffer = create (size 4) (u64 0) in 
    
    copy s inverseS;
    
    upload_scalar order;
    (*check that publicKey is not equal to the identity element O *)
  (*let pointInfinityPublicKey = isPointAtInfinity pubKey in 
    if pointInfinityPublicKey = true then false else *)
  let coordinatesValid = isCoordinateValid pubKey in
    if coordinatesValid = true then false else 
    (*Check that {\displaystyle Q_{A}} Q_{A} lies on the curve *)
  let belongsToCurve =  isPointOnCurve pubKey in 
    if belongsToCurve = false then false else 
    (* Check that {\displaystyle n\times Q_{A}=O} n\times Q_{A}=O *)
  let orderCorrect = isOrderCorrect pubKey order tempBuffer in 
    if orderCorrect = false then false else 
    (* Verify that {\displaystyle r} r and {\displaystyle s} s are integers in {\displaystyle [1,n-1]} [1,n-1]. If not, the signature is invalid. *)
  let isRCorrect = isMoreThanZeroLessThanOrderMinusOne r order in 
    if isRCorrect = false then false else
  let isSCorrect = isMoreThanZeroLessThanOrderMinusOne s order in 
    if isSCorrect = false then false else 
      begin
	hash mHash mLen m;
	toUint64 mHash hashAsFelem;
	
	montgomery_ladder_exponent inverseS;
	multPowerPartial inverseS hashAsFelem u1;
	multPowerPartial inverseS r u2;
  
	toUint8 u1 bufferU1;
	toUint8 u2 bufferU2;

	secretToPublic pointu1G u1 tempBuffer;
	scalarMultiplication pubKey pointu2Q bufferU2 tempBuffer;
	point_add pointu1G pointu2Q pointSum tempBuffer;
	
	let resultIsPAI = isPointAtInfinity pointSum in 
	if resultIsPAI then false else 

	let x = sub pointSum (size 0) (size 4) in 

	reduction_prime_2prime_order x xBuffer;
	let r = compare_felem xBuffer r in 
	eq_0_u64 r
	end
