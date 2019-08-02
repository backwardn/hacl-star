/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /home/nkulatov/new/kremlin/krml -fbuiltin-uint128 -funroll-loops 8 -add-include "TestLib.h" /dist/generic/testlib.c -skip-compilation -no-prefix Hacl.Impl.P256 -bundle Lib.* -bundle Spec.* -bundle Hacl.Impl.P256=Hacl.Impl.P256,Hacl.Impl.LowLevel,Hacl.Impl.SolinasReduction,Hacl.Spec.P256.*,Hacl.Spec.Curve25519.*,Hacl.Impl.Curve25519.* -bundle Hacl.Impl.ECDSA.P256SHA256.Verification=Hacl.Impl.MontgomeryMultiplication,Hacl.Impl.ECDSA.P256SHA256.Verification,Hacl.Impl.MM.Exponent -library C,FStar -drop LowStar,Spec,Prims,Lib,C.Loops.*,Hacl.Spec.P256.Lemmas,Hacl.Spec.P256,Hacl.Spec.ECDSA -add-include "c/Lib_PrintBuffer.h" -add-include "FStar_UInt_8_16_32_64.h" -tmpdir p256-c .output/prims.krml .output/FStar_Pervasives_Native.krml .output/FStar_Pervasives.krml .output/FStar_Reflection_Types.krml .output/FStar_Reflection_Data.krml .output/FStar_Order.krml .output/FStar_Reflection_Basic.krml .output/FStar_Mul.krml .output/FStar_Math_Lib.krml .output/FStar_Math_Lemmas.krml .output/FStar_Squash.krml .output/FStar_Classical.krml .output/FStar_StrongExcludedMiddle.krml .output/FStar_FunctionalExtensionality.krml .output/FStar_List_Tot_Base.krml .output/FStar_List_Tot_Properties.krml .output/FStar_List_Tot.krml .output/FStar_Seq_Base.krml .output/FStar_Seq_Properties.krml .output/FStar_Seq.krml .output/FStar_Set.krml .output/FStar_Preorder.krml .output/FStar_Ghost.krml .output/FStar_ErasedLogic.krml .output/FStar_PropositionalExtensionality.krml .output/FStar_PredicateExtensionality.krml .output/FStar_TSet.krml .output/FStar_Monotonic_Heap.krml .output/FStar_Heap.krml .output/FStar_Map.krml .output/FStar_Monotonic_Witnessed.krml .output/FStar_Monotonic_HyperHeap.krml .output/FStar_Monotonic_HyperStack.krml .output/FStar_HyperStack.krml .output/FStar_HyperStack_ST.krml .output/FStar_Calc.krml .output/FStar_BitVector.krml .output/FStar_UInt.krml .output/FStar_UInt32.krml .output/FStar_Universe.krml .output/FStar_GSet.krml .output/FStar_ModifiesGen.krml .output/FStar_Range.krml .output/FStar_Tactics_Types.krml .output/FStar_Tactics_Result.krml .output/FStar_Tactics_Effect.krml .output/FStar_Tactics_Util.krml .output/FStar_Reflection_Const.krml .output/FStar_Char.krml .output/FStar_Exn.krml .output/FStar_ST.krml .output/FStar_All.krml .output/FStar_List.krml .output/FStar_String.krml .output/FStar_Reflection_Derived.krml .output/FStar_Tactics_Builtins.krml .output/FStar_Reflection_Formula.krml .output/FStar_Reflection_Derived_Lemmas.krml .output/FStar_Reflection.krml .output/FStar_Tactics_Derived.krml .output/FStar_Tactics_Logic.krml .output/FStar_Tactics.krml .output/FStar_BigOps.krml .output/LowStar_Monotonic_Buffer.krml .output/LowStar_Buffer.krml .output/LowStar_BufferOps.krml .output/Spec_Loops.krml .output/FStar_UInt64.krml .output/C_Loops.krml .output/FStar_Int.krml .output/FStar_Int64.krml .output/FStar_Int63.krml .output/FStar_Int32.krml .output/FStar_Int16.krml .output/FStar_Int8.krml .output/FStar_UInt63.krml .output/FStar_UInt16.krml .output/FStar_UInt8.krml .output/FStar_Int_Cast.krml .output/FStar_UInt128.krml .output/FStar_Int_Cast_Full.krml .output/Lib_IntTypes.krml .output/Lib_Loops.krml .output/Lib_LoopCombinators.krml .output/Lib_RawIntTypes.krml .output/Lib_Sequence.krml .output/Lib_ByteSequence.krml .output/LowStar_ImmutableBuffer.krml .output/Lib_Buffer.krml .output/FStar_HyperStack_All.krml .output/Hacl_Spec_ECDSAP256_Definition.krml .output/FStar_Reflection_Arith.krml .output/FStar_Tactics_Canon.krml .output/Hacl_Impl_Curve25519_Lemmas.krml .output/Spec_Curve25519_Lemmas.krml .output/Spec_Curve25519.krml .output/Hacl_Spec_Curve25519_Field64_Definition.krml .output/Hacl_Spec_Curve25519_Field64_Lemmas.krml .output/Hacl_Spec_P256_Definitions.krml .output/Hacl_Spec_P256_Basic.krml .output/Hacl_Spec_P256_Lemmas.krml .output/Hacl_Spec_P256_Core.krml .output/Hacl_Spec_P256_SolinasReduction.krml .output/FStar_Kremlin_Endianness.krml .output/Hacl_Spec_P256.krml .output/Hacl_Spec_P256_MontgomeryMultiplication.krml .output/Hacl_Spec_P256_MontgomeryMultiplication_PointDouble.krml .output/Hacl_Spec_P256_MontgomeryMultiplication_PointAdd.krml .output/Hacl_Spec_P256_Ladder.krml .output/Hacl_Impl_LowLevel.krml .output/Hacl_Spec_P256_Normalisation.krml .output/Hacl_Impl_SolinasReduction.krml .output/Hacl_Impl_P256.krml .output/C_Endianness.krml .output/Hacl_Spec_ECDSA.krml .output/C.krml .output/Lib_ByteBuffer.krml .output/Hacl_Impl_MontgomeryMultiplication.krml .output/Hacl_Impl_MM_Exponent.krml .output/Hacl_Impl_ECDSA_P256SHA256_Verification.krml
  F* version: f2134fe1
  KreMLin version: f534ac02
 */

#include "C_Endianness.h"

uint32_t index_32_be(uint8_t *b, uint32_t i)
{
  return load32_be(b + (uint32_t)4U * i);
}

uint32_t index_32_le(uint8_t *b, uint32_t i)
{
  return load32_le(b + (uint32_t)4U * i);
}

uint64_t index_64_be(uint8_t *b, uint32_t i)
{
  return load64_be(b + (uint32_t)8U * i);
}

uint64_t index_64_le(uint8_t *b, uint32_t i)
{
  return load64_le(b + (uint32_t)8U * i);
}

void upd_32_be(uint8_t *b, uint32_t i, uint32_t v1)
{
  store32_be(b + (uint32_t)4U * i, v1);
}

