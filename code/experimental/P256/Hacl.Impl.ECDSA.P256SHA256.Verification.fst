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
open Hacl.Spec.ECDSAP256.Definition
open Hacl.Spec.ECDSA
open Hacl.Spec.P256
open Hacl.Spec.P256.Ladder



(* checks whether the coordinates are valid = 
   all of them are less than prime 
*) 
val isCoordinateValid: p: lbuffer uint64 (size 12) -> Stack bool 
  (requires fun h -> live h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1  /\ 
    (
      let x = gsub p (size 0) (size 4) in 
      let y = gsub p (size 4) (size 4) in 
      let z = gsub p (size 8) (size 4) in 
      r = true ==> as_nat h0 x < prime256 /\ as_nat h0 y < prime256 /\ as_nat h0 z < prime256
  )  
)

#reset-options "--z3refresh --z3rlimit 300"

open FStar.Mul 

let isCoordinateValid p = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
    let x = sub p (size 0) (size 4) in 
    let y = sub p (size 4) (size 4) in 
    let z = sub p (size 8) (size 4) in 
      let h0 = ST.get() in 
      assert(felem_seq_as_nat (as_seq h0 prime256_buffer) == prime256);
    let carryX = sub4_il x prime256_buffer tempBuffer in
    let carryY = sub4_il y prime256_buffer tempBuffer in 
    let carryZ = sub4_il z prime256_buffer tempBuffer in 
      
      let h1 = ST.get() in 
      assert(modifies1 tempBuffer h0 h1);
      assert(if uint_v carryX = 1 then as_nat h0 x < prime256 else True); 
      assert(if uint_v carryY = 1 then as_nat h0 y < prime256 else True); 
      assert(if uint_v carryZ = 1 then as_nat h0 z < prime256 else True);

    let lessX = eq_u64 carryX (u64 1) in   
    let lessY = eq_u64 carryY (u64 1) in 
    let lessZ = eq_u64 carryZ (u64 1) in 

    let r = lessX && lessY && lessZ in 
      assert(r = true ==> as_nat h0 x < prime256 /\ as_nat h0 y < prime256 /\ as_nat h0 z < prime256);
    pop_frame();
    r  


inline_for_extraction noextract
val equalZeroBuffer: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (if r = true then  as_nat h0 f == 0 else as_nat h0 f > 0))

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
  

(* checks whether the intefer f is between 1 and (n- 1) (incl).  *)
(* [1, n - 1] <==> a > 0 /\ a < n) *)

val isMoreThanZeroLessThanOrderMinusOne: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r == true ==> as_nat h0 f > 0 && as_nat h0 f < prime_p256_order)

let isMoreThanZeroLessThanOrderMinusOne f = 
  push_frame();
    let h0 = ST.get() in 
    let tempBuffer = create (size 4) (u64 0) in 
        recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);
	let h0 = ST.get() in 
    let carry = sub4_il f prime256order_buffer tempBuffer in  
      assert(if uint_v carry = 1 then as_nat h0 f < prime_p256_order else True);
	let h1 = ST.get() in 
	assert(modifies1 tempBuffer h0 h1);
    let less = eq_u64 carry (u64 1) in
      assert(less == true ==> as_nat h0 f < prime_p256_order);
	let h2 = ST.get() in 
    let more = equalZeroBuffer f in 
      assert(not more == true ==> as_nat h0 f > 0);
    let result = less &&  not more in 
      assert(less && not more ==> as_nat h0 f > 0 && as_nat h0 f < prime_p256_order);
  pop_frame();  
    result

inline_for_extraction noextract
val multByOrder: p: point -> result: point ->  tempBuffer: lbuffer uint64 (size 100) -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ live h tempBuffer /\
     as_nat h (gsub p (size 0) (size 4)) < prime256 /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime256 /\
    as_nat h (gsub p (size 8) (size 4)) < prime256 /\
   LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer;loc result]
  )
  (ensures fun h0 _ h1 -> modifies3 p result tempBuffer h0 h1 /\
    (
      let xN, yN, zN = scalar_multiplication (genOrderOfCurve()) (point_prime_to_coordinates (as_seq h0 p)) in 
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
) 
)


let multByOrder p result tempBuffer =
  push_frame();
    let order = create (size 32) (u8 0) in 
      let h0 = ST.get() in 
    upload_order order;
      let h1 = ST.get() in 
      modifies1_is_modifies4 p result tempBuffer order h0 h1;
      assert(modifies4 p result tempBuffer order h0 h1);
    scalarMultiplication p result order tempBuffer;
      let h2 = ST.get() in 
      assert(
      let xN, yN, zN = scalar_multiplication (genOrderOfCurve()) (point_prime_to_coordinates (as_seq h0 p)) in 
      let x3, y3, z3 = point_x_as_nat h2 result, point_y_as_nat h2 result, point_z_as_nat h2 result in 
      x3 == xN /\ y3 == yN /\ z3 == zN);
      assert(modifies3 p result tempBuffer h1 h2);
      modifies3_is_modifies4 tempBuffer p result order h1 h2;
      assert (modifies4 order p result tempBuffer h0 h1);
   pop_frame()

inline_for_extraction noextract
val multByOrder2: p: point -> result: point -> tempBuffer: lbuffer uint64 (size 100) -> Stack unit 
  (requires fun h -> 
    live h p /\ live h result /\ live h tempBuffer /\
    as_nat h (gsub p (size 0) (size 4)) < prime256 /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime256 /\
    as_nat h (gsub p (size 8) (size 4)) < prime256 /\
   LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer;loc result]
  )
  (ensures fun h0 _ h1  -> modifies2 result tempBuffer h0 h1 /\
    (
      let xN, yN, zN = scalar_multiplication (genOrderOfCurve()) (point_prime_to_coordinates (as_seq h0 p)) in 
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
))

let multByOrder2 p result tempBuffer = 
  push_frame();
    let pBuffer = create (size 12) (u64 0) in 
    copy pBuffer p;
    multByOrder pBuffer result tempBuffer;
  pop_frame()  
    

#reset-options "--z3refresh --z3rlimit 100"
(*checks whether the base point * order is point at infinity *)
val isOrderCorrect: p: point -> tempBuffer: lbuffer uint64 (size 100) ->  Stack bool
  (requires fun h -> live h p /\ live h tempBuffer /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime256 /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime256 /\
    as_nat h (gsub p (size 8) (size 4)) < prime256 /\
    disjoint p tempBuffer)
  (ensures fun h0 r h1 -> modifies1 tempBuffer h0 h1 /\ (
      let (xN, yN, zN) = scalar_multiplication (genOrderOfCurve()) (point_prime_to_coordinates (as_seq h0 p)) in 
      r == Hacl.Spec.P256.isPointAtInfinity (xN, yN, zN)
  ) 
  
  )

let isOrderCorrect p tempBuffer = 
  push_frame(); 
    let multResult = create (size 12) (u64 0) in 
    multByOrder2 p multResult tempBuffer;
    let result = Hacl.Impl.P256.isPointAtInfinity multResult in  
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
    
    (*check that publicKey is not equal to the identity element O *)
  (*let pointInfinityPublicKey = isPointAtInfinity pubKey in 
    if pointInfinityPublicKey = true then false else *)
  let coordinatesValid = isCoordinateValid pubKey in
    if coordinatesValid = true then false else 
    (*Check that {\displaystyle Q_{A}} Q_{A} lies on the curve *)
  let belongsToCurve =  isPointOnCurve pubKey in 
    if belongsToCurve = false then false else 
    (* Check that {\displaystyle n\times Q_{A}=O} n\times Q_{A}=O *)
  let orderCorrect = isOrderCorrect pubKey tempBuffer in 
    if orderCorrect = false then false else 
    (* Verify that {\displaystyle r} r and {\displaystyle s} s are integers in {\displaystyle [1,n-1]} [1,n-1]. If not, the signature is invalid. *)
  let isRCorrect = isMoreThanZeroLessThanOrderMinusOne r in 
    if isRCorrect = false then false else
  let isSCorrect = isMoreThanZeroLessThanOrderMinusOne s in 
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

	Hacl.Impl.MontgomeryMultiplication.reduction_prime_2prime_order x xBuffer;
	let r = compare_felem xBuffer r in 
	eq_0_u64 r
	end
