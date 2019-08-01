/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /home/nkulatov/new/kremlin/krml -fbuiltin-uint128 -funroll-loops 8 -add-include "TestLib.h" /dist/generic/testlib.c -skip-compilation -bundle Lib.* -bundle Spec.* -bundle Hacl.Impl.ECDSA.Verification=Hacl.Impl.ECDSA.Verification -library C,FStar -drop LowStar,Spec,Prims,Lib,C.Loops.*,Hacl.Spec.ECDSA.Definition -add-include "c/Lib_PrintBuffer.h" -add-include "FStar_UInt_8_16_32_64.h" -tmpdir ecdsa-c .output/prims.krml .output/FStar_Pervasives_Native.krml .output/FStar_Pervasives.krml .output/FStar_Mul.krml .output/FStar_Preorder.krml .output/FStar_Calc.krml .output/FStar_Squash.krml .output/FStar_Classical.krml .output/FStar_StrongExcludedMiddle.krml .output/FStar_FunctionalExtensionality.krml .output/FStar_List_Tot_Base.krml .output/FStar_List_Tot_Properties.krml .output/FStar_List_Tot.krml .output/FStar_Seq_Base.krml .output/FStar_Seq_Properties.krml .output/FStar_Seq.krml .output/FStar_Math_Lib.krml .output/FStar_Math_Lemmas.krml .output/FStar_BitVector.krml .output/FStar_UInt.krml .output/FStar_UInt32.krml .output/FStar_Int.krml .output/FStar_Int16.krml .output/FStar_Reflection_Types.krml .output/FStar_Reflection_Data.krml .output/FStar_Order.krml .output/FStar_Reflection_Basic.krml .output/FStar_Ghost.krml .output/FStar_ErasedLogic.krml .output/FStar_UInt64.krml .output/FStar_Set.krml .output/FStar_PropositionalExtensionality.krml .output/FStar_PredicateExtensionality.krml .output/FStar_TSet.krml .output/FStar_Monotonic_Heap.krml .output/FStar_Heap.krml .output/FStar_Map.krml .output/FStar_Monotonic_HyperHeap.krml .output/FStar_Monotonic_HyperStack.krml .output/FStar_HyperStack.krml .output/FStar_Monotonic_Witnessed.krml .output/FStar_HyperStack_ST.krml .output/FStar_HyperStack_All.krml .output/FStar_Int64.krml .output/FStar_Int63.krml .output/FStar_Int32.krml .output/FStar_Int8.krml .output/FStar_UInt63.krml .output/FStar_UInt16.krml .output/FStar_UInt8.krml .output/FStar_Int_Cast.krml .output/FStar_UInt128.krml .output/FStar_Int_Cast_Full.krml .output/Lib_IntTypes.krml .output/Lib_RawIntTypes.krml .output/FStar_Char.krml .output/FStar_Exn.krml .output/FStar_ST.krml .output/FStar_All.krml .output/FStar_List.krml .output/FStar_String.krml .output/FStar_Reflection_Const.krml .output/FStar_Reflection_Derived.krml .output/FStar_Reflection_Derived_Lemmas.krml .output/Lib_LoopCombinators.krml .output/Lib_Sequence.krml .output/FStar_Universe.krml .output/FStar_GSet.krml .output/FStar_ModifiesGen.krml .output/FStar_Range.krml .output/FStar_Tactics_Types.krml .output/FStar_Tactics_Result.krml .output/FStar_Tactics_Effect.krml .output/FStar_Tactics_Util.krml .output/FStar_Tactics_Builtins.krml .output/FStar_Reflection_Formula.krml .output/FStar_Reflection.krml .output/FStar_Tactics_Derived.krml .output/FStar_Tactics_Logic.krml .output/FStar_Tactics.krml .output/FStar_BigOps.krml .output/LowStar_Monotonic_Buffer.krml .output/LowStar_Buffer.krml .output/Spec_Loops.krml .output/LowStar_BufferOps.krml .output/C_Loops.krml .output/Lib_Loops.krml .output/Lib_ByteSequence.krml .output/LowStar_ImmutableBuffer.krml .output/Lib_Buffer.krml .output/Hacl_Spec_ECDSA_Definition.krml .output/Hacl_Impl_ECDSA_Verification.krml
  F* version: f2134fe1
  KreMLin version: f534ac02
 */

#include "kremlib.h"
#ifndef __Hacl_Impl_ECDSA_Verification_H
#define __Hacl_Impl_ECDSA_Verification_H


#include "TestLib.h"
#include "c/Lib_PrintBuffer.h"
#include "FStar_UInt_8_16_32_64.h"

extern uint32_t Hacl_Impl_ECDSA_Verification_getPointLength();

typedef uint64_t *Hacl_Impl_ECDSA_Verification_pointType;

extern uint32_t Hacl_Impl_ECDSA_Verification_getHashFunctionLen();

extern void Hacl_Impl_ECDSA_Verification_getOrder(uint8_t *x0);

extern uint32_t Hacl_Impl_ECDSA_Verification_getOrderLenght();

extern bool Hacl_Impl_ECDSA_Verification_isPointAtInfinity(uint64_t *x0);

extern bool Hacl_Impl_ECDSA_Verification_isPointAtCurve(uint64_t *x0);

extern void Hacl_Impl_ECDSA_Verification_scalar_mult(uint64_t *x0, uint8_t *x1, uint64_t *x2);

extern bool Hacl_Impl_ECDSA_Verification_compare_buffer_less(uint64_t *x0, uint64_t *x1);

extern bool Hacl_Impl_ECDSA_Verification_compare_felem_equal(uint64_t *x0, uint64_t *x1);

extern bool Hacl_Impl_ECDSA_Verification_hash_f(uint32_t x0, uint64_t *x1, uint64_t *x2);

extern void Hacl_Impl_ECDSA_Verification_inverse_mod(uint64_t *x0, uint64_t *x1);

extern void Hacl_Impl_ECDSA_Verification_mod_mul(uint64_t *x0, uint64_t *x1, uint64_t *x2);

extern void Hacl_Impl_ECDSA_Verification_mod_add(uint64_t *x0, uint64_t *x1, uint64_t *x2);

bool
Hacl_Impl_ECDSA_Verification_ecdsa_verification(
  uint64_t *pubKey,
  uint64_t *r,
  uint64_t *s,
  uint32_t mLen,
  uint64_t *m,
  uint64_t *tempBuffer
);

#define __Hacl_Impl_ECDSA_Verification_H_DEFINED
#endif