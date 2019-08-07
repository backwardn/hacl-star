/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /home/nkulatov/new/kremlin/krml -fbuiltin-uint128 -funroll-loops 8 -add-include "TestLib.h" /dist/generic/testlib.c -skip-compilation -no-prefix Hacl.Impl.P256 -bundle Lib.* -bundle Spec.* -bundle Hacl.Impl.P256=Hacl.Impl.P256,Hacl.Impl.LowLevel,Hacl.Impl.SolinasReduction,Hacl.Spec.P256.*,Hacl.Spec.Curve25519.*,Hacl.Impl.Curve25519.* -bundle Hacl.Impl.ECDSA.P256SHA256.Verification=Hacl.Impl.MontgomeryMultiplication,Hacl.Impl.ECDSA.P256SHA256.Verification,Hacl.Impl.MM.Exponent -library C,FStar -drop LowStar,Spec,Prims,Lib,C.Loops.*,Hacl.Spec.P256.Lemmas,Hacl.Spec.P256,Hacl.Spec.ECDSA -add-include "c/Lib_PrintBuffer.h" -add-include "FStar_UInt_8_16_32_64.h" -tmpdir p256-c .output/prims.krml .output/FStar_Pervasives_Native.krml .output/FStar_Pervasives.krml .output/FStar_Reflection_Types.krml .output/FStar_Reflection_Data.krml .output/FStar_Order.krml .output/FStar_Reflection_Basic.krml .output/FStar_Squash.krml .output/FStar_Classical.krml .output/FStar_StrongExcludedMiddle.krml .output/FStar_FunctionalExtensionality.krml .output/FStar_List_Tot_Base.krml .output/FStar_List_Tot_Properties.krml .output/FStar_List_Tot.krml .output/FStar_Mul.krml .output/FStar_Math_Lib.krml .output/FStar_Math_Lemmas.krml .output/FStar_Seq_Base.krml .output/FStar_Seq_Properties.krml .output/FStar_Seq.krml .output/FStar_Set.krml .output/FStar_Preorder.krml .output/FStar_Ghost.krml .output/FStar_ErasedLogic.krml .output/FStar_PropositionalExtensionality.krml .output/FStar_PredicateExtensionality.krml .output/FStar_TSet.krml .output/FStar_Monotonic_Heap.krml .output/FStar_Heap.krml .output/FStar_Map.krml .output/FStar_Monotonic_Witnessed.krml .output/FStar_Monotonic_HyperHeap.krml .output/FStar_Monotonic_HyperStack.krml .output/FStar_HyperStack.krml .output/FStar_HyperStack_ST.krml .output/FStar_Calc.krml .output/FStar_BitVector.krml .output/FStar_UInt.krml .output/FStar_UInt32.krml .output/FStar_Universe.krml .output/FStar_GSet.krml .output/FStar_ModifiesGen.krml .output/FStar_Range.krml .output/FStar_Tactics_Types.krml .output/FStar_Tactics_Result.krml .output/FStar_Tactics_Effect.krml .output/FStar_Tactics_Util.krml .output/FStar_Reflection_Const.krml .output/FStar_Char.krml .output/FStar_Exn.krml .output/FStar_ST.krml .output/FStar_All.krml .output/FStar_List.krml .output/FStar_String.krml .output/FStar_Reflection_Derived.krml .output/FStar_Tactics_Builtins.krml .output/FStar_Reflection_Formula.krml .output/FStar_Reflection_Derived_Lemmas.krml .output/FStar_Reflection.krml .output/FStar_Tactics_Derived.krml .output/FStar_Tactics_Logic.krml .output/FStar_Tactics.krml .output/FStar_BigOps.krml .output/LowStar_Monotonic_Buffer.krml .output/LowStar_Buffer.krml .output/LowStar_BufferOps.krml .output/Spec_Loops.krml .output/FStar_UInt64.krml .output/C_Loops.krml .output/FStar_Int.krml .output/FStar_Int64.krml .output/FStar_Int63.krml .output/FStar_Int32.krml .output/FStar_Int16.krml .output/FStar_Int8.krml .output/FStar_UInt63.krml .output/FStar_UInt16.krml .output/FStar_UInt8.krml .output/FStar_Int_Cast.krml .output/FStar_UInt128.krml .output/FStar_Int_Cast_Full.krml .output/Lib_IntTypes.krml .output/Lib_Loops.krml .output/Lib_LoopCombinators.krml .output/Lib_RawIntTypes.krml .output/Lib_Sequence.krml .output/Lib_ByteSequence.krml .output/LowStar_ImmutableBuffer.krml .output/Lib_Buffer.krml .output/FStar_HyperStack_All.krml .output/Hacl_Spec_ECDSAP256_Definition.krml .output/FStar_Reflection_Arith.krml .output/FStar_Tactics_Canon.krml .output/Hacl_Impl_Curve25519_Lemmas.krml .output/Spec_Curve25519_Lemmas.krml .output/Spec_Curve25519.krml .output/Hacl_Spec_Curve25519_Field64_Definition.krml .output/Hacl_Spec_Curve25519_Field64_Lemmas.krml .output/Hacl_Spec_P256_Definitions.krml .output/Hacl_Spec_P256_Basic.krml .output/Hacl_Spec_P256_Lemmas.krml .output/Hacl_Spec_P256_Core.krml .output/Hacl_Spec_P256_SolinasReduction.krml .output/FStar_Kremlin_Endianness.krml .output/Hacl_Spec_P256.krml .output/Hacl_Spec_P256_MontgomeryMultiplication.krml .output/Hacl_Spec_P256_MontgomeryMultiplication_PointDouble.krml .output/Hacl_Spec_P256_MontgomeryMultiplication_PointAdd.krml .output/Hacl_Spec_P256_Ladder.krml .output/Hacl_Impl_LowLevel.krml .output/Hacl_Spec_P256_Normalisation.krml .output/Hacl_Impl_SolinasReduction.krml .output/Hacl_Impl_P256.krml .output/C_Endianness.krml .output/Hacl_Spec_ECDSA.krml .output/C.krml .output/Lib_ByteBuffer.krml .output/Hacl_Impl_MontgomeryMultiplication.krml .output/Hacl_Impl_MM_Exponent.krml .output/Hacl_Impl_ECDSA_P256SHA256_Verification.krml
  F* version: f2134fe1
  KreMLin version: f534ac02
 */

#include "Hacl_Impl_ECDSA_P256SHA256_Verification.h"

static uint64_t
Hacl_Impl_MontgomeryMultiplication_prime256order_buffer[4U] =
  {
    (uint64_t)17562291160714782033U,
    (uint64_t)13611842547513532036U,
    (uint64_t)18446744073709551615U,
    (uint64_t)18446744069414584320U
  };

inline static void
Hacl_Impl_MontgomeryMultiplication_mul(uint64_t *f1, uint64_t *r, uint64_t *out)
{
  uint64_t f10 = f1[0U];
  uint64_t f11 = f1[1U];
  uint64_t f12 = f1[2U];
  uint64_t f13 = f1[3U];
  uint64_t r0 = r[0U];
  uint64_t r1 = r[1U];
  uint64_t r2 = r[2U];
  uint64_t r3 = r[3U];
  uint128_t res0 = (uint128_t)r0 * f10;
  uint64_t l00 = (uint64_t)res0;
  uint64_t h00 = (uint64_t)(res0 >> (uint32_t)64U);
  uint128_t res1 = (uint128_t)r1 * f10;
  uint64_t l10 = (uint64_t)res1;
  uint64_t h10 = (uint64_t)(res1 >> (uint32_t)64U);
  uint128_t res2 = (uint128_t)r2 * f10;
  uint64_t l20 = (uint64_t)res2;
  uint64_t h20 = (uint64_t)(res2 >> (uint32_t)64U);
  uint128_t res3 = (uint128_t)r3 * f10;
  uint64_t l30 = (uint64_t)res3;
  uint64_t h30 = (uint64_t)(res3 >> (uint32_t)64U);
  uint64_t o04 = l00;
  K___uint64_t_uint64_t scrut0 = Hacl_Spec_P256_Basic_addcarry(l10, h00, (uint64_t)0U);
  uint64_t o10 = scrut0.fst;
  uint64_t c00 = scrut0.snd;
  K___uint64_t_uint64_t scrut1 = Hacl_Spec_P256_Basic_addcarry(l20, h10, c00);
  uint64_t o20 = scrut1.fst;
  uint64_t c10 = scrut1.snd;
  K___uint64_t_uint64_t scrut2 = Hacl_Spec_P256_Basic_addcarry(l30, h20, c10);
  uint64_t o30 = scrut2.fst;
  uint64_t c20 = scrut2.snd;
  uint64_t c30 = h30 + c20;
  K___uint64_t_K___uint64_t_uint64_t_uint64_t_uint64_t
  scrut3 = { .fst = c30, .snd = { .fst = o04, .snd = o10, .thd = o20, .f3 = o30 } };
  uint64_t o03 = scrut3.snd.f3;
  uint64_t o02 = scrut3.snd.thd;
  uint64_t o01 = scrut3.snd.snd;
  uint64_t o00 = scrut3.snd.fst;
  uint64_t c0 = scrut3.fst;
  uint128_t res4 = (uint128_t)r0 * f11;
  uint64_t l01 = (uint64_t)res4;
  uint64_t h01 = (uint64_t)(res4 >> (uint32_t)64U);
  uint128_t res5 = (uint128_t)r1 * f11;
  uint64_t l11 = (uint64_t)res5;
  uint64_t h11 = (uint64_t)(res5 >> (uint32_t)64U);
  uint128_t res6 = (uint128_t)r2 * f11;
  uint64_t l21 = (uint64_t)res6;
  uint64_t h21 = (uint64_t)(res6 >> (uint32_t)64U);
  uint128_t res7 = (uint128_t)r3 * f11;
  uint64_t l31 = (uint64_t)res7;
  uint64_t h31 = (uint64_t)(res7 >> (uint32_t)64U);
  uint64_t o05 = l01;
  K___uint64_t_uint64_t scrut4 = Hacl_Spec_P256_Basic_addcarry(l11, h01, (uint64_t)0U);
  uint64_t o15 = scrut4.fst;
  uint64_t c010 = scrut4.snd;
  K___uint64_t_uint64_t scrut5 = Hacl_Spec_P256_Basic_addcarry(l21, h11, c010);
  uint64_t o21 = scrut5.fst;
  uint64_t c12 = scrut5.snd;
  K___uint64_t_uint64_t scrut6 = Hacl_Spec_P256_Basic_addcarry(l31, h21, c12);
  uint64_t o31 = scrut6.fst;
  uint64_t c22 = scrut6.snd;
  uint64_t c31 = h31 + c22;
  K___uint64_t_K___uint64_t_uint64_t_uint64_t_uint64_t
  scrut7 = { .fst = c31, .snd = { .fst = o05, .snd = o15, .thd = o21, .f3 = o31 } };
  uint64_t c5 = scrut7.fst;
  K___uint64_t_uint64_t_uint64_t_uint64_t out00 = scrut7.snd;
  uint64_t o06 = out00.fst;
  uint64_t o16 = out00.snd;
  uint64_t o26 = out00.thd;
  uint64_t o32 = out00.f3;
  uint64_t f300 = o01;
  uint64_t f310 = o02;
  uint64_t f320 = o03;
  uint64_t f330 = c0;
  K___uint64_t_uint64_t scrut8 = Hacl_Spec_P256_Basic_addcarry(f300, o06, (uint64_t)0U);
  uint64_t o0_ = scrut8.fst;
  uint64_t c011 = scrut8.snd;
  K___uint64_t_uint64_t scrut9 = Hacl_Spec_P256_Basic_addcarry(f310, o16, c011);
  uint64_t o1_ = scrut9.fst;
  uint64_t c13 = scrut9.snd;
  K___uint64_t_uint64_t scrut10 = Hacl_Spec_P256_Basic_addcarry(f320, o26, c13);
  uint64_t o2_ = scrut10.fst;
  uint64_t c23 = scrut10.snd;
  K___uint64_t_uint64_t scrut11 = Hacl_Spec_P256_Basic_addcarry(f330, o32, c23);
  uint64_t o3_ = scrut11.fst;
  uint64_t c32 = scrut11.snd;
  K___uint64_t_uint64_t_uint64_t_uint64_t
  out10 = { .fst = o0_, .snd = o1_, .thd = o2_, .f3 = o3_ };
  uint64_t c40 = c5 + c32;
  K___uint64_t_K___uint64_t_uint64_t_uint64_t_uint64_t scrut12 = { .fst = c40, .snd = out10 };
  uint64_t o14 = scrut12.snd.f3;
  uint64_t o13 = scrut12.snd.thd;
  uint64_t o12 = scrut12.snd.snd;
  uint64_t o11 = scrut12.snd.fst;
  uint64_t c1 = scrut12.fst;
  uint128_t res8 = (uint128_t)r0 * f12;
  uint64_t l02 = (uint64_t)res8;
  uint64_t h02 = (uint64_t)(res8 >> (uint32_t)64U);
  uint128_t res9 = (uint128_t)r1 * f12;
  uint64_t l12 = (uint64_t)res9;
  uint64_t h12 = (uint64_t)(res9 >> (uint32_t)64U);
  uint128_t res10 = (uint128_t)r2 * f12;
  uint64_t l22 = (uint64_t)res10;
  uint64_t h22 = (uint64_t)(res10 >> (uint32_t)64U);
  uint128_t res11 = (uint128_t)r3 * f12;
  uint64_t l32 = (uint64_t)res11;
  uint64_t h32 = (uint64_t)(res11 >> (uint32_t)64U);
  uint64_t o07 = l02;
  K___uint64_t_uint64_t scrut13 = Hacl_Spec_P256_Basic_addcarry(l12, h02, (uint64_t)0U);
  uint64_t o17 = scrut13.fst;
  uint64_t c012 = scrut13.snd;
  K___uint64_t_uint64_t scrut14 = Hacl_Spec_P256_Basic_addcarry(l22, h12, c012);
  uint64_t o27 = scrut14.fst;
  uint64_t c110 = scrut14.snd;
  K___uint64_t_uint64_t scrut15 = Hacl_Spec_P256_Basic_addcarry(l32, h22, c110);
  uint64_t o37 = scrut15.fst;
  uint64_t c24 = scrut15.snd;
  uint64_t c33 = h32 + c24;
  K___uint64_t_K___uint64_t_uint64_t_uint64_t_uint64_t
  scrut16 = { .fst = c33, .snd = { .fst = o07, .snd = o17, .thd = o27, .f3 = o37 } };
  uint64_t c6 = scrut16.fst;
  K___uint64_t_uint64_t_uint64_t_uint64_t out01 = scrut16.snd;
  uint64_t o08 = out01.fst;
  uint64_t o18 = out01.snd;
  uint64_t o28 = out01.thd;
  uint64_t o38 = out01.f3;
  uint64_t f301 = o12;
  uint64_t f311 = o13;
  uint64_t f321 = o14;
  uint64_t f331 = c1;
  K___uint64_t_uint64_t scrut17 = Hacl_Spec_P256_Basic_addcarry(f301, o08, (uint64_t)0U);
  uint64_t o0_0 = scrut17.fst;
  uint64_t c013 = scrut17.snd;
  K___uint64_t_uint64_t scrut18 = Hacl_Spec_P256_Basic_addcarry(f311, o18, c013);
  uint64_t o1_0 = scrut18.fst;
  uint64_t c111 = scrut18.snd;
  K___uint64_t_uint64_t scrut19 = Hacl_Spec_P256_Basic_addcarry(f321, o28, c111);
  uint64_t o2_0 = scrut19.fst;
  uint64_t c25 = scrut19.snd;
  K___uint64_t_uint64_t scrut20 = Hacl_Spec_P256_Basic_addcarry(f331, o38, c25);
  uint64_t o3_0 = scrut20.fst;
  uint64_t c34 = scrut20.snd;
  K___uint64_t_uint64_t_uint64_t_uint64_t
  out11 = { .fst = o0_0, .snd = o1_0, .thd = o2_0, .f3 = o3_0 };
  uint64_t c41 = c6 + c34;
  K___uint64_t_K___uint64_t_uint64_t_uint64_t_uint64_t scrut21 = { .fst = c41, .snd = out11 };
  uint64_t o25 = scrut21.snd.f3;
  uint64_t o24 = scrut21.snd.thd;
  uint64_t o23 = scrut21.snd.snd;
  uint64_t o22 = scrut21.snd.fst;
  uint64_t c2 = scrut21.fst;
  uint128_t res12 = (uint128_t)r0 * f13;
  uint64_t l0 = (uint64_t)res12;
  uint64_t h0 = (uint64_t)(res12 >> (uint32_t)64U);
  uint128_t res13 = (uint128_t)r1 * f13;
  uint64_t l1 = (uint64_t)res13;
  uint64_t h1 = (uint64_t)(res13 >> (uint32_t)64U);
  uint128_t res14 = (uint128_t)r2 * f13;
  uint64_t l2 = (uint64_t)res14;
  uint64_t h2 = (uint64_t)(res14 >> (uint32_t)64U);
  uint128_t res = (uint128_t)r3 * f13;
  uint64_t l3 = (uint64_t)res;
  uint64_t h3 = (uint64_t)(res >> (uint32_t)64U);
  uint64_t o09 = l0;
  K___uint64_t_uint64_t scrut22 = Hacl_Spec_P256_Basic_addcarry(l1, h0, (uint64_t)0U);
  uint64_t o19 = scrut22.fst;
  uint64_t c014 = scrut22.snd;
  K___uint64_t_uint64_t scrut23 = Hacl_Spec_P256_Basic_addcarry(l2, h1, c014);
  uint64_t o29 = scrut23.fst;
  uint64_t c112 = scrut23.snd;
  K___uint64_t_uint64_t scrut24 = Hacl_Spec_P256_Basic_addcarry(l3, h2, c112);
  uint64_t o39 = scrut24.fst;
  uint64_t c210 = scrut24.snd;
  uint64_t c35 = h3 + c210;
  K___uint64_t_K___uint64_t_uint64_t_uint64_t_uint64_t
  scrut25 = { .fst = c35, .snd = { .fst = o09, .snd = o19, .thd = o29, .f3 = o39 } };
  uint64_t c = scrut25.fst;
  K___uint64_t_uint64_t_uint64_t_uint64_t out0 = scrut25.snd;
  uint64_t o010 = out0.fst;
  uint64_t o110 = out0.snd;
  uint64_t o210 = out0.thd;
  uint64_t o310 = out0.f3;
  uint64_t f30 = o23;
  uint64_t f31 = o24;
  uint64_t f32 = o25;
  uint64_t f33 = c2;
  K___uint64_t_uint64_t scrut = Hacl_Spec_P256_Basic_addcarry(f30, o010, (uint64_t)0U);
  uint64_t o0_1 = scrut.fst;
  uint64_t c01 = scrut.snd;
  K___uint64_t_uint64_t scrut26 = Hacl_Spec_P256_Basic_addcarry(f31, o110, c01);
  uint64_t o1_1 = scrut26.fst;
  uint64_t c11 = scrut26.snd;
  K___uint64_t_uint64_t scrut27 = Hacl_Spec_P256_Basic_addcarry(f32, o210, c11);
  uint64_t o2_1 = scrut27.fst;
  uint64_t c21 = scrut27.snd;
  K___uint64_t_uint64_t scrut28 = Hacl_Spec_P256_Basic_addcarry(f33, o310, c21);
  uint64_t o3_1 = scrut28.fst;
  uint64_t c36 = scrut28.snd;
  K___uint64_t_uint64_t_uint64_t_uint64_t
  out1 = { .fst = o0_1, .snd = o1_1, .thd = o2_1, .f3 = o3_1 };
  uint64_t c4 = c + c36;
  K___uint64_t_K___uint64_t_uint64_t_uint64_t_uint64_t scrut29 = { .fst = c4, .snd = out1 };
  uint64_t o36 = scrut29.snd.f3;
  uint64_t o35 = scrut29.snd.thd;
  uint64_t o34 = scrut29.snd.snd;
  uint64_t o33 = scrut29.snd.fst;
  uint64_t c3 = scrut29.fst;
  K___uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t
  scrut30 =
    { .fst = o00, .snd = o11, .thd = o22, .f3 = o33, .f4 = o34, .f5 = o35, .f6 = o36, .f7 = c3 };
  uint64_t o0 = scrut30.fst;
  uint64_t o1 = scrut30.snd;
  uint64_t o2 = scrut30.thd;
  uint64_t o3 = scrut30.f3;
  uint64_t o4 = scrut30.f4;
  uint64_t o5 = scrut30.f5;
  uint64_t o6 = scrut30.f6;
  uint64_t o7 = scrut30.f7;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
  out[4U] = o4;
  out[5U] = o5;
  out[6U] = o6;
  out[7U] = o7;
}

static void
Hacl_Impl_MontgomeryMultiplication_shortened_mul(uint64_t *a, uint64_t b, uint64_t *result)
{
  uint64_t a0 = a[0U];
  uint64_t a1 = a[1U];
  uint64_t a2 = a[2U];
  uint64_t a3 = a[3U];
  uint128_t res0 = (uint128_t)a0 * b;
  uint64_t l0 = (uint64_t)res0;
  uint64_t h0 = (uint64_t)(res0 >> (uint32_t)64U);
  uint128_t res1 = (uint128_t)a1 * b;
  uint64_t l1 = (uint64_t)res1;
  uint64_t h1 = (uint64_t)(res1 >> (uint32_t)64U);
  uint128_t res2 = (uint128_t)a2 * b;
  uint64_t l2 = (uint64_t)res2;
  uint64_t h2 = (uint64_t)(res2 >> (uint32_t)64U);
  uint128_t res = (uint128_t)a3 * b;
  uint64_t l3 = (uint64_t)res;
  uint64_t h3 = (uint64_t)(res >> (uint32_t)64U);
  uint64_t o0 = l0;
  K___uint64_t_uint64_t scrut = Hacl_Spec_P256_Basic_addcarry(l1, h0, (uint64_t)0U);
  uint64_t o1 = scrut.fst;
  uint64_t c0 = scrut.snd;
  K___uint64_t_uint64_t scrut0 = Hacl_Spec_P256_Basic_addcarry(l2, h1, c0);
  uint64_t o2 = scrut0.fst;
  uint64_t c1 = scrut0.snd;
  K___uint64_t_uint64_t scrut1 = Hacl_Spec_P256_Basic_addcarry(l3, h2, c1);
  uint64_t o3 = scrut1.fst;
  uint64_t c2 = scrut1.snd;
  uint64_t c3 = h3 + c2;
  K___uint64_t_K___uint64_t_uint64_t_uint64_t_uint64_t
  scrut2 = { .fst = c3, .snd = { .fst = o0, .snd = o1, .thd = o2, .f3 = o3 } };
  uint64_t f30 = scrut2.snd.f3;
  uint64_t f20 = scrut2.snd.thd;
  uint64_t f10 = scrut2.snd.snd;
  uint64_t f00 = scrut2.snd.fst;
  uint64_t c = scrut2.fst;
  K___uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t
  scrut3 =
    {
      .fst = f00, .snd = f10, .thd = f20, .f3 = f30, .f4 = c, .f5 = (uint64_t)0U, .f6 = (uint64_t)0U,
      .f7 = (uint64_t)0U
    };
  uint64_t f0 = scrut3.fst;
  uint64_t f1 = scrut3.snd;
  uint64_t f2 = scrut3.thd;
  uint64_t f3 = scrut3.f3;
  uint64_t f4 = scrut3.f4;
  uint64_t f5 = scrut3.f5;
  uint64_t f6 = scrut3.f6;
  uint64_t f7 = scrut3.f7;
  result[0U] = f0;
  result[1U] = f1;
  result[2U] = f2;
  result[3U] = f3;
  result[4U] = f4;
  result[5U] = f5;
  result[6U] = f6;
  result[7U] = f7;
}

static void
Hacl_Impl_MontgomeryMultiplication_add8_without_carry1(
  uint64_t *t,
  uint64_t *r,
  uint64_t *result
)
{
  uint64_t t0 = t[0U];
  uint64_t t1 = t[1U];
  uint64_t t2 = t[2U];
  uint64_t t3 = t[3U];
  uint64_t t4 = t[4U];
  uint64_t t5 = t[5U];
  uint64_t t6 = t[6U];
  uint64_t t7 = t[7U];
  uint64_t r0 = r[0U];
  uint64_t r1 = r[1U];
  uint64_t r2 = r[2U];
  uint64_t r3 = r[3U];
  uint64_t r4 = r[4U];
  uint64_t r5 = r[5U];
  uint64_t r6 = r[6U];
  uint64_t r7 = r[7U];
  K___uint64_t_uint64_t scrut = Hacl_Spec_P256_Basic_addcarry(t0, r0, (uint64_t)0U);
  uint64_t o00 = scrut.fst;
  uint64_t c0 = scrut.snd;
  K___uint64_t_uint64_t scrut0 = Hacl_Spec_P256_Basic_addcarry(t1, r1, c0);
  uint64_t o10 = scrut0.fst;
  uint64_t c1 = scrut0.snd;
  K___uint64_t_uint64_t scrut1 = Hacl_Spec_P256_Basic_addcarry(t2, r2, c1);
  uint64_t o20 = scrut1.fst;
  uint64_t c2 = scrut1.snd;
  K___uint64_t_uint64_t scrut2 = Hacl_Spec_P256_Basic_addcarry(t3, r3, c2);
  uint64_t o30 = scrut2.fst;
  uint64_t c30 = scrut2.snd;
  K___uint64_t_K___uint64_t_uint64_t_uint64_t_uint64_t
  scrut3 = { .fst = c30, .snd = { .fst = o00, .snd = o10, .thd = o20, .f3 = o30 } };
  uint64_t o3 = scrut3.snd.f3;
  uint64_t o2 = scrut3.snd.thd;
  uint64_t o1 = scrut3.snd.snd;
  uint64_t o0 = scrut3.snd.fst;
  uint64_t c3 = scrut3.fst;
  K___uint64_t_uint64_t scrut4 = Hacl_Spec_P256_Basic_addcarry(t4, r4, c3);
  uint64_t o4 = scrut4.fst;
  uint64_t c4 = scrut4.snd;
  K___uint64_t_uint64_t scrut5 = Hacl_Spec_P256_Basic_addcarry(t5, r5, c4);
  uint64_t o5 = scrut5.fst;
  uint64_t c5 = scrut5.snd;
  K___uint64_t_uint64_t scrut6 = Hacl_Spec_P256_Basic_addcarry(t6, r6, c5);
  uint64_t o6 = scrut6.fst;
  uint64_t c6 = scrut6.snd;
  K___uint64_t_uint64_t scrut7 = Hacl_Spec_P256_Basic_addcarry(t7, r7, c6);
  uint64_t o7 = scrut7.fst;
  uint64_t c7 = scrut7.snd;
  K___uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t
  scrut8 =
    { .fst = c7, .snd = o0, .thd = o1, .f3 = o2, .f4 = o3, .f5 = o4, .f6 = o5, .f7 = o6, .f8 = o7 };
  uint64_t r010 = scrut8.snd;
  uint64_t r110 = scrut8.thd;
  uint64_t r210 = scrut8.f3;
  uint64_t r310 = scrut8.f4;
  uint64_t r410 = scrut8.f5;
  uint64_t r510 = scrut8.f6;
  uint64_t r610 = scrut8.f7;
  uint64_t r710 = scrut8.f8;
  K___uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t
  scrut9 =
    {
      .fst = r010, .snd = r110, .thd = r210, .f3 = r310, .f4 = r410, .f5 = r510, .f6 = r610,
      .f7 = r710
    };
  uint64_t r01 = scrut9.fst;
  uint64_t r11 = scrut9.snd;
  uint64_t r21 = scrut9.thd;
  uint64_t r31 = scrut9.f3;
  uint64_t r41 = scrut9.f4;
  uint64_t r51 = scrut9.f5;
  uint64_t r61 = scrut9.f6;
  uint64_t r71 = scrut9.f7;
  result[0U] = r01;
  result[1U] = r11;
  result[2U] = r21;
  result[3U] = r31;
  result[4U] = r41;
  result[5U] = r51;
  result[6U] = r61;
  result[7U] = r71;
}

static void Hacl_Impl_MontgomeryMultiplication_shift8(uint64_t *t, uint64_t *out)
{
  uint64_t t1 = t[1U];
  uint64_t t2 = t[2U];
  uint64_t t3 = t[3U];
  uint64_t t4 = t[4U];
  uint64_t t5 = t[5U];
  uint64_t t6 = t[6U];
  uint64_t t7 = t[7U];
  out[0U] = t1;
  out[1U] = t2;
  out[2U] = t3;
  out[3U] = t4;
  out[4U] = t5;
  out[5U] = t6;
  out[6U] = t7;
  out[7U] = (uint64_t)0U;
}

static void
Hacl_Impl_MontgomeryMultiplication_montgomery_multiplication_round(
  uint64_t *t,
  uint64_t *round,
  uint64_t k0
)
{
  uint64_t yBuffer[8U] = { 0U };
  uint64_t t2[8U] = { 0U };
  uint64_t t3[8U] = { 0U };
  uint64_t t1 = t[0U];
  uint128_t res = (uint128_t)t1 * k0;
  K___uint64_t_uint64_t
  scrut = { .fst = (uint64_t)res, .snd = (uint64_t)(res >> (uint32_t)64U) };
  uint64_t y = scrut.fst;
  Hacl_Impl_MontgomeryMultiplication_shortened_mul(Hacl_Impl_MontgomeryMultiplication_prime256order_buffer,
    y,
    t2);
  Hacl_Impl_MontgomeryMultiplication_add8_without_carry1(t, t2, t3);
  Hacl_Impl_MontgomeryMultiplication_shift8(t3, round);
}

static void
Hacl_Impl_MontgomeryMultiplication_reduction_prime_2prime_order(uint64_t *x, uint64_t *result)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t
  c =
    Hacl_Impl_LowLevel_sub4_il(x,
      Hacl_Impl_MontgomeryMultiplication_prime256order_buffer,
      tempBuffer);
  Hacl_Impl_LowLevel_cmovznz4(c, tempBuffer, x, result);
}

static uint64_t Hacl_Impl_MontgomeryMultiplication_upload_k0()
{
  return (uint64_t)14758798090332847183U;
}

static void
Hacl_Impl_MontgomeryMultiplication_montgomery_multiplication_ecdsa_module(
  uint64_t *a,
  uint64_t *b,
  uint64_t *result
)
{
  uint64_t t[8U] = { 0U };
  uint64_t round2[8U] = { 0U };
  uint64_t round4[8U] = { 0U };
  uint64_t prime_p256_orderBuffer[4U] = { 0U };
  uint64_t k0 = Hacl_Impl_MontgomeryMultiplication_upload_k0();
  Hacl_Impl_MontgomeryMultiplication_mul(a, b, t);
  uint64_t tempRound[8U] = { 0U };
  Hacl_Impl_MontgomeryMultiplication_montgomery_multiplication_round(t, tempRound, k0);
  Hacl_Impl_MontgomeryMultiplication_montgomery_multiplication_round(tempRound, round2, k0);
  uint64_t tempRound0[8U] = { 0U };
  Hacl_Impl_MontgomeryMultiplication_montgomery_multiplication_round(round2, tempRound0, k0);
  Hacl_Impl_MontgomeryMultiplication_montgomery_multiplication_round(tempRound0, round4, k0);
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t cin = round4[4U];
  uint64_t *x = round4;
  uint64_t
  c =
    Hacl_Impl_LowLevel_sub4(x,
      Hacl_Impl_MontgomeryMultiplication_prime256order_buffer,
      tempBuffer);
  uint64_t carry = Hacl_Impl_LowLevel_sub_borrow(c, cin, (uint64_t)0U, &tempBufferForSubborrow);
  Hacl_Impl_LowLevel_cmovznz4(carry, tempBuffer, x, result);
}

static void Hacl_Impl_MM_Exponent_cswap(uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  uint64_t mask = (uint64_t)0U - bit;
  {
    uint64_t dummy = mask & (p1[0U] ^ p2[0U]);
    p1[0U] = p1[0U] ^ dummy;
    p2[0U] = p2[0U] ^ dummy;
  }
  {
    uint64_t dummy = mask & (p1[1U] ^ p2[1U]);
    p1[1U] = p1[1U] ^ dummy;
    p2[1U] = p2[1U] ^ dummy;
  }
  {
    uint64_t dummy = mask & (p1[2U] ^ p2[2U]);
    p1[2U] = p1[2U] ^ dummy;
    p2[2U] = p2[2U] ^ dummy;
  }
  {
    uint64_t dummy = mask & (p1[3U] ^ p2[3U]);
    p1[3U] = p1[3U] ^ dummy;
    p2[3U] = p2[3U] ^ dummy;
  }
}

static void Hacl_Impl_MM_Exponent_montgomery_ladder_exponent(uint64_t *r)
{
  uint64_t p[4U] = { 0U };
  uint8_t scalar[32U] = { 0U };
  p[0U] = (uint64_t)884452912994769583U;
  p[1U] = (uint64_t)4834901526196019579U;
  p[2U] = (uint64_t)0U;
  p[3U] = (uint64_t)4294967295U;
  scalar[0U] = (uint8_t)79U;
  scalar[1U] = (uint8_t)37U;
  scalar[2U] = (uint8_t)99U;
  scalar[3U] = (uint8_t)252U;
  scalar[4U] = (uint8_t)194U;
  scalar[5U] = (uint8_t)202U;
  scalar[6U] = (uint8_t)185U;
  scalar[7U] = (uint8_t)243U;
  scalar[8U] = (uint8_t)132U;
  scalar[9U] = (uint8_t)158U;
  scalar[10U] = (uint8_t)23U;
  scalar[11U] = (uint8_t)167U;
  scalar[12U] = (uint8_t)173U;
  scalar[13U] = (uint8_t)250U;
  scalar[14U] = (uint8_t)230U;
  scalar[15U] = (uint8_t)188U;
  scalar[16U] = (uint8_t)255U;
  scalar[17U] = (uint8_t)255U;
  scalar[18U] = (uint8_t)255U;
  scalar[19U] = (uint8_t)255U;
  scalar[20U] = (uint8_t)255U;
  scalar[21U] = (uint8_t)255U;
  scalar[22U] = (uint8_t)255U;
  scalar[23U] = (uint8_t)255U;
  scalar[24U] = (uint8_t)0U;
  scalar[25U] = (uint8_t)0U;
  scalar[26U] = (uint8_t)0U;
  scalar[27U] = (uint8_t)0U;
  scalar[28U] = (uint8_t)255U;
  scalar[29U] = (uint8_t)255U;
  scalar[30U] = (uint8_t)255U;
  scalar[31U] = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i = i + (uint32_t)1U)
  {
    uint32_t bit0 = (uint32_t)255U - i;
    uint64_t bit = (uint64_t)(scalar[bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    Hacl_Impl_MM_Exponent_cswap(bit, p, r);
    Hacl_Impl_MontgomeryMultiplication_montgomery_multiplication_ecdsa_module(p, r, r);
    Hacl_Impl_MontgomeryMultiplication_montgomery_multiplication_ecdsa_module(p, p, p);
    Hacl_Impl_MM_Exponent_cswap(bit, p, r);
  }
  memcpy(r, p, (uint32_t)4U * sizeof p[0U]);
}

static void Hacl_Impl_MM_Exponent_fromDomainImpl(uint64_t *a, uint64_t *result)
{
  uint64_t one1[4U] = { 0U };
  one1[0U] = (uint64_t)1U;
  one1[1U] = (uint64_t)0U;
  one1[2U] = (uint64_t)0U;
  one1[3U] = (uint64_t)0U;
  Hacl_Impl_MontgomeryMultiplication_montgomery_multiplication_ecdsa_module(one1, a, result);
}

static void Hacl_Impl_MM_Exponent_multPowerPartial(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint64_t buffFromDB[4U] = { 0U };
  Hacl_Impl_MM_Exponent_fromDomainImpl(b, buffFromDB);
  Hacl_Impl_MM_Exponent_fromDomainImpl(buffFromDB, buffFromDB);
  Hacl_Impl_MontgomeryMultiplication_montgomery_multiplication_ecdsa_module(a,
    buffFromDB,
    result);
}

void Hacl_Impl_ECDSA_P256SHA256_Verification_bufferToJac(uint64_t *p, uint64_t *result)
{
  uint64_t *partPoint = result;
  memcpy(partPoint, p, (uint32_t)8U * sizeof p[0U]);
  result[8U] = (uint64_t)1U;
  result[9U] = (uint64_t)0U;
  result[10U] = (uint64_t)0U;
  result[11U] = (uint64_t)0U;
}

bool Hacl_Impl_ECDSA_P256SHA256_Verification_isCoordinateValid(uint64_t *p)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t *x = p;
  uint64_t *y = p + (uint32_t)4U;
  uint64_t *z = p + (uint32_t)8U;
  uint64_t
  carryX = Hacl_Impl_LowLevel_sub4_il(x, Hacl_Impl_LowLevel_prime256_buffer, tempBuffer);
  uint64_t
  carryY = Hacl_Impl_LowLevel_sub4_il(y, Hacl_Impl_LowLevel_prime256_buffer, tempBuffer);
  uint64_t
  carryZ = Hacl_Impl_LowLevel_sub4_il(z, Hacl_Impl_LowLevel_prime256_buffer, tempBuffer);
  bool lessX = carryX == (uint64_t)1U;
  bool lessY = carryY == (uint64_t)1U;
  bool lessZ = carryZ == (uint64_t)1U;
  bool r = lessX && lessY && lessZ;
  return r;
}

bool Hacl_Impl_ECDSA_P256SHA256_Verification_isMoreThanZeroLessThanOrderMinusOne(uint64_t *f)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t
  carry =
    Hacl_Impl_LowLevel_sub4_il(f,
      Hacl_Impl_MontgomeryMultiplication_prime256order_buffer,
      tempBuffer);
  bool less = carry == (uint64_t)1U;
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t b0 = (uint64_t)0U;
  bool z0_zero = f0 == b0;
  uint64_t b1 = (uint64_t)0U;
  bool z1_zero = f1 == b1;
  uint64_t b2 = (uint64_t)0U;
  bool z2_zero = f2 == b2;
  uint64_t b = (uint64_t)0U;
  bool z3_zero = f3 == b;
  bool more = z0_zero && z1_zero && z2_zero && z3_zero;
  bool result = less && !more;
  return result;
}

bool Hacl_Impl_ECDSA_P256SHA256_Verification_isOrderCorrect(uint64_t *p, uint64_t *tempBuffer)
{
  uint64_t multResult[12U] = { 0U };
  uint64_t pBuffer[12U] = { 0U };
  memcpy(pBuffer, p, (uint32_t)12U * sizeof p[0U]);
  uint8_t order[32U] = { 0U };
  order[0U] = (uint8_t)81U;
  order[1U] = (uint8_t)37U;
  order[2U] = (uint8_t)99U;
  order[3U] = (uint8_t)252U;
  order[4U] = (uint8_t)194U;
  order[5U] = (uint8_t)202U;
  order[6U] = (uint8_t)185U;
  order[7U] = (uint8_t)243U;
  order[8U] = (uint8_t)132U;
  order[9U] = (uint8_t)158U;
  order[10U] = (uint8_t)23U;
  order[11U] = (uint8_t)167U;
  order[12U] = (uint8_t)173U;
  order[13U] = (uint8_t)250U;
  order[14U] = (uint8_t)230U;
  order[15U] = (uint8_t)188U;
  order[16U] = (uint8_t)255U;
  order[17U] = (uint8_t)255U;
  order[18U] = (uint8_t)255U;
  order[19U] = (uint8_t)255U;
  order[20U] = (uint8_t)255U;
  order[21U] = (uint8_t)255U;
  order[22U] = (uint8_t)255U;
  order[23U] = (uint8_t)255U;
  order[24U] = (uint8_t)0U;
  order[25U] = (uint8_t)0U;
  order[26U] = (uint8_t)0U;
  order[27U] = (uint8_t)0U;
  order[28U] = (uint8_t)255U;
  order[29U] = (uint8_t)255U;
  order[30U] = (uint8_t)255U;
  order[31U] = (uint8_t)255U;
  scalarMultiplication(pBuffer, multResult, order, tempBuffer);
  bool result = isPointAtInfinity(multResult);
  return result;
}

void Hacl_Impl_ECDSA_P256SHA256_Verification_toUint64(uint8_t *i, uint64_t *o)
{
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)0U * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[0U] = x;
  }
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)1U * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[1U] = x;
  }
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)2U * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[2U] = x;
  }
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)3U * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[3U] = x;
  }
}

void Hacl_Impl_ECDSA_P256SHA256_Verification_toUint8(uint64_t *i, uint8_t *o)
{
  {
    store64_le(o + (uint32_t)0U * (uint32_t)8U, i[0U]);
  }
  {
    store64_le(o + (uint32_t)1U * (uint32_t)8U, i[1U]);
  }
  {
    store64_le(o + (uint32_t)2U * (uint32_t)8U, i[2U]);
  }
  {
    store64_le(o + (uint32_t)3U * (uint32_t)8U, i[3U]);
  }
}

uint32_t Hacl_Impl_ECDSA_P256SHA256_Verification_hLen = (uint32_t)32U;

bool
Hacl_Impl_ECDSA_P256SHA256_Verification_verifyQValidCurvePoint(
  uint64_t *pubKey,
  uint64_t *pubKeyAsPoint,
  uint64_t *tempBuffer
)
{
  Hacl_Impl_ECDSA_P256SHA256_Verification_bufferToJac(pubKey, pubKeyAsPoint);
  bool
  coordinatesValid = Hacl_Impl_ECDSA_P256SHA256_Verification_isCoordinateValid(pubKeyAsPoint);
  if (coordinatesValid == false)
    return false;
  else
  {
    bool belongsToCurve = isPointOnCurve(pubKeyAsPoint);
    if (belongsToCurve == false)
      return false;
    else
    {
      bool
      orderCorrect =
        Hacl_Impl_ECDSA_P256SHA256_Verification_isOrderCorrect(pubKeyAsPoint,
          tempBuffer);
      if (orderCorrect == false)
        return false;
      else
        return true;
    }
  }
}

bool
Hacl_Impl_ECDSA_P256SHA256_Verification_ecdsa_verification(
  uint64_t *pubKey,
  uint64_t *r,
  uint64_t *s1,
  uint32_t mLen,
  uint8_t *m
)
{
  uint8_t mHash[32U] = { 0U };
  uint64_t hashAsFelem[4U] = { 0U };
  uint64_t tempBuffer[100U] = { 0U };
  uint64_t inverseS[4U] = { 0U };
  uint64_t u11[4U] = { 0U };
  uint64_t u2[4U] = { 0U };
  uint8_t bufferU1[32U] = { 0U };
  uint8_t bufferU2[32U] = { 0U };
  uint64_t pointu1G[12U] = { 0U };
  uint64_t pointu2Q[12U] = { 0U };
  uint64_t pointSum[12U] = { 0U };
  uint64_t xBuffer[4U] = { 0U };
  memcpy(s1, inverseS, (uint32_t)4U * sizeof inverseS[0U]);
  bool coordinatesValid = Hacl_Impl_ECDSA_P256SHA256_Verification_isCoordinateValid(pubKey);
  if (coordinatesValid == true)
    return false;
  else
  {
    bool belongsToCurve = isPointOnCurve(pubKey);
    if (belongsToCurve == false)
      return false;
    else
    {
      bool
      orderCorrect = Hacl_Impl_ECDSA_P256SHA256_Verification_isOrderCorrect(pubKey, tempBuffer);
      if (orderCorrect == false)
        return false;
      else
      {
        bool
        isRCorrect = Hacl_Impl_ECDSA_P256SHA256_Verification_isMoreThanZeroLessThanOrderMinusOne(r);
        if (isRCorrect == false)
          return false;
        else
        {
          bool
          isSCorrect =
            Hacl_Impl_ECDSA_P256SHA256_Verification_isMoreThanZeroLessThanOrderMinusOne(s1);
          if (isSCorrect == false)
            return false;
          else
          {
            Hacl_Impl_ECDSA_P256SHA256_Verification_hash(mHash, mLen, m);
            Hacl_Impl_ECDSA_P256SHA256_Verification_toUint64(mHash, hashAsFelem);
            Hacl_Impl_MM_Exponent_montgomery_ladder_exponent(inverseS);
            Hacl_Impl_MM_Exponent_multPowerPartial(inverseS, hashAsFelem, u11);
            Hacl_Impl_MM_Exponent_multPowerPartial(inverseS, r, u2);
            Hacl_Impl_ECDSA_P256SHA256_Verification_toUint8(u11, bufferU1);
            Hacl_Impl_ECDSA_P256SHA256_Verification_toUint8(u2, bufferU2);
            secretToPublic(pointu1G, (uint8_t *)u11, tempBuffer);
            scalarMultiplication(pubKey, pointu2Q, bufferU2, tempBuffer);
            point_add(pointu1G, pointu2Q, pointSum, tempBuffer);
            bool resultIsPAI = isPointAtInfinity(pointSum);
            if (resultIsPAI)
              return false;
            else
            {
              uint64_t *x = pointSum;
              Hacl_Impl_MontgomeryMultiplication_reduction_prime_2prime_order(x, xBuffer);
              uint64_t r1 = compare_felem(xBuffer, r);
              uint64_t b = (uint64_t)0U;
              return r1 == b;
            }
          }
        }
      }
    }
  }
}

