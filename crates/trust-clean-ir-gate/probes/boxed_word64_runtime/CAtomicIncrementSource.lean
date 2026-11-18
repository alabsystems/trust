-- Copyright 2026 Andrew Yates | Apache-2.0
import CAtomicDropSyntax
import CAtomicIncrementSyntax

/-! Untrusted byte/cut advice. All original bytes+all8 mutants remain. Whole-TU/span, macro/type and C11 execution relations remain open. -/
namespace CAtomicIncrementSource
open CAtomicDropSyntax
def proposal : Proposal := ⟨"clean_inc", "o", "CLEAN_RC_STICKY"⟩

def actual_r0 : List String := []
def actual_s0 : State := initial
def actual_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def actual_r1 : List String := ["static"] ++ actual_r0
def actual_s1 : State := ⟨.ident, [105], actual_r1⟩
theorem actual_cut0 : feed (some actual_s0) actual_c0 = some actual_s1 := by rfl
def actual_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def actual_r2 : List String := ["inline"] ++ actual_r1
def actual_s2 : State := ⟨.ident, [111, 118], actual_r2⟩
theorem actual_cut1 : feed (some actual_s1) actual_c1 = some actual_s2 := by rfl
def actual_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def actual_r3 : List String := ["void"] ++ actual_r2
def actual_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], actual_r3⟩
theorem actual_cut2 : feed (some actual_s2) actual_c2 = some actual_s3 := by rfl
def actual_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def actual_r4 : List String := ["(", "clean_inc"] ++ actual_r3
def actual_s4 : State := ⟨.ident, [101, 108, 99], actual_r4⟩
theorem actual_cut3 : feed (some actual_s3) actual_c3 = some actual_s4 := by rfl
def actual_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def actual_r5 : List String := ["*", "clean_obj"] ++ actual_r4
def actual_s5 : State := ⟨.normal, [], actual_r5⟩
theorem actual_cut4 : feed (some actual_s4) actual_c4 = some actual_s5 := by rfl
def actual_c5 : List UInt8 := [111, 41, 32, 123, 10, 32, 32, 32]
def actual_r6 : List String := ["{", ")", "o"] ++ actual_r5
def actual_s6 : State := ⟨.normal, [], actual_r6⟩
theorem actual_cut5 : feed (some actual_s5) actual_c5 = some actual_s6 := by rfl
def actual_c6 : List UInt8 := [32, 105, 102, 32, 40, 33, 99, 108]
def actual_r7 : List String := ["!", "(", "if"] ++ actual_r6
def actual_s7 : State := ⟨.ident, [108, 99], actual_r7⟩
theorem actual_cut6 : feed (some actual_s6) actual_c6 = some actual_s7 := by rfl
def actual_c7 : List UInt8 := [101, 97, 110, 95, 105, 115, 95, 115]
def actual_r8 : List String := [] ++ actual_r7
def actual_s8 : State := ⟨.ident, [115, 95, 115, 105, 95, 110, 97, 101, 108, 99], actual_r8⟩
theorem actual_cut7 : feed (some actual_s7) actual_c7 = some actual_s8 := by rfl
def actual_c8 : List UInt8 := [99, 97, 108, 97, 114, 40, 111, 41]
def actual_r9 : List String := [")", "o", "(", "clean_is_scalar"] ++ actual_r8
def actual_s9 : State := ⟨.normal, [], actual_r9⟩
theorem actual_cut8 : feed (some actual_s8) actual_c8 = some actual_s9 := by rfl
def actual_c9 : List UInt8 := [32, 38, 38, 10, 32, 32, 32, 32]
def actual_r10 : List String := ["&&"] ++ actual_r9
def actual_s10 : State := ⟨.normal, [], actual_r10⟩
theorem actual_cut9 : feed (some actual_s9) actual_c9 = some actual_s10 := by rfl
def actual_c10 : List UInt8 := [32, 32, 32, 32, 97, 116, 111, 109]
def actual_r11 : List String := [] ++ actual_r10
def actual_s11 : State := ⟨.ident, [109, 111, 116, 97], actual_r11⟩
theorem actual_cut10 : feed (some actual_s10) actual_c10 = some actual_s11 := by rfl
def actual_c11 : List UInt8 := [105, 99, 95, 108, 111, 97, 100, 95]
def actual_r12 : List String := [] ++ actual_r11
def actual_s12 : State := ⟨.ident, [95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], actual_r12⟩
theorem actual_cut11 : feed (some actual_s11) actual_c11 = some actual_s12 := by rfl
def actual_c12 : List UInt8 := [101, 120, 112, 108, 105, 99, 105, 116]
def actual_r13 : List String := [] ++ actual_r12
def actual_s13 : State := ⟨.ident, [116, 105, 99, 105, 108, 112, 120, 101, 95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], actual_r13⟩
theorem actual_cut12 : feed (some actual_s12) actual_c12 = some actual_s13 := by rfl
def actual_c13 : List UInt8 := [40, 38, 111, 45, 62, 104, 101, 97]
def actual_r14 : List String := ["->", "o", "&", "(", "atomic_load_explicit"] ++ actual_r13
def actual_s14 : State := ⟨.ident, [97, 101, 104], actual_r14⟩
theorem actual_cut13 : feed (some actual_s13) actual_c13 = some actual_s14 := by rfl
def actual_c14 : List UInt8 := [100, 101, 114, 46, 114, 101, 102, 95]
def actual_r15 : List String := [".", "header"] ++ actual_r14
def actual_s15 : State := ⟨.ident, [95, 102, 101, 114], actual_r15⟩
theorem actual_cut14 : feed (some actual_s14) actual_c14 = some actual_s15 := by rfl
def actual_c15 : List UInt8 := [99, 111, 117, 110, 116, 44, 32, 109]
def actual_r16 : List String := [",", "ref_count"] ++ actual_r15
def actual_s16 : State := ⟨.ident, [109], actual_r16⟩
theorem actual_cut15 : feed (some actual_s15) actual_c15 = some actual_s16 := by rfl
def actual_c16 : List UInt8 := [101, 109, 111, 114, 121, 95, 111, 114]
def actual_r17 : List String := [] ++ actual_r16
def actual_s17 : State := ⟨.ident, [114, 111, 95, 121, 114, 111, 109, 101, 109], actual_r17⟩
theorem actual_cut16 : feed (some actual_s16) actual_c16 = some actual_s17 := by rfl
def actual_c17 : List UInt8 := [100, 101, 114, 95, 114, 101, 108, 97]
def actual_r18 : List String := [] ++ actual_r17
def actual_s18 : State := ⟨.ident, [97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], actual_r18⟩
theorem actual_cut17 : feed (some actual_s17) actual_c17 = some actual_s18 := by rfl
def actual_c18 : List UInt8 := [120, 101, 100, 41, 32, 60, 32, 67]
def actual_r19 : List String := ["<", ")", "memory_order_relaxed"] ++ actual_r18
def actual_s19 : State := ⟨.ident, [67], actual_r19⟩
theorem actual_cut18 : feed (some actual_s18) actual_c18 = some actual_s19 := by rfl
def actual_c19 : List UInt8 := [76, 69, 65, 78, 95, 82, 67, 95]
def actual_r20 : List String := [] ++ actual_r19
def actual_s20 : State := ⟨.ident, [95, 67, 82, 95, 78, 65, 69, 76, 67], actual_r20⟩
theorem actual_cut19 : feed (some actual_s19) actual_c19 = some actual_s20 := by rfl
def actual_c20 : List UInt8 := [83, 84, 73, 67, 75, 89, 41, 32]
def actual_r21 : List String := [")", "CLEAN_RC_STICKY"] ++ actual_r20
def actual_s21 : State := ⟨.normal, [], actual_r21⟩
theorem actual_cut20 : feed (some actual_s20) actual_c20 = some actual_s21 := by rfl
def actual_c21 : List UInt8 := [123, 10, 32, 32, 32, 32, 32, 32]
def actual_r22 : List String := ["{"] ++ actual_r21
def actual_s22 : State := ⟨.normal, [], actual_r22⟩
theorem actual_cut21 : feed (some actual_s21) actual_c21 = some actual_s22 := by rfl
def actual_c22 : List UInt8 := [32, 32, 97, 116, 111, 109, 105, 99]
def actual_r23 : List String := [] ++ actual_r22
def actual_s23 : State := ⟨.ident, [99, 105, 109, 111, 116, 97], actual_r23⟩
theorem actual_cut22 : feed (some actual_s22) actual_c22 = some actual_s23 := by rfl
def actual_c23 : List UInt8 := [95, 102, 101, 116, 99, 104, 95, 97]
def actual_r24 : List String := [] ++ actual_r23
def actual_s24 : State := ⟨.ident, [97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], actual_r24⟩
theorem actual_cut23 : feed (some actual_s23) actual_c23 = some actual_s24 := by rfl
def actual_c24 : List UInt8 := [100, 100, 95, 101, 120, 112, 108, 105]
def actual_r25 : List String := [] ++ actual_r24
def actual_s25 : State := ⟨.ident, [105, 108, 112, 120, 101, 95, 100, 100, 97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], actual_r25⟩
theorem actual_cut24 : feed (some actual_s24) actual_c24 = some actual_s25 := by rfl
def actual_c25 : List UInt8 := [99, 105, 116, 40, 38, 111, 45, 62]
def actual_r26 : List String := ["->", "o", "&", "(", "atomic_fetch_add_explicit"] ++ actual_r25
def actual_s26 : State := ⟨.normal, [], actual_r26⟩
theorem actual_cut25 : feed (some actual_s25) actual_c25 = some actual_s26 := by rfl
def actual_c26 : List UInt8 := [104, 101, 97, 100, 101, 114, 46, 114]
def actual_r27 : List String := [".", "header"] ++ actual_r26
def actual_s27 : State := ⟨.ident, [114], actual_r27⟩
theorem actual_cut26 : feed (some actual_s26) actual_c26 = some actual_s27 := by rfl
def actual_c27 : List UInt8 := [101, 102, 95, 99, 111, 117, 110, 116]
def actual_r28 : List String := [] ++ actual_r27
def actual_s28 : State := ⟨.ident, [116, 110, 117, 111, 99, 95, 102, 101, 114], actual_r28⟩
theorem actual_cut27 : feed (some actual_s27) actual_c27 = some actual_s28 := by rfl
def actual_c28 : List UInt8 := [44, 32, 49, 44, 32, 109, 101, 109]
def actual_r29 : List String := [",", "1", ",", "ref_count"] ++ actual_r28
def actual_s29 : State := ⟨.ident, [109, 101, 109], actual_r29⟩
theorem actual_cut28 : feed (some actual_s28) actual_c28 = some actual_s29 := by rfl
def actual_c29 : List UInt8 := [111, 114, 121, 95, 111, 114, 100, 101]
def actual_r30 : List String := [] ++ actual_r29
def actual_s30 : State := ⟨.ident, [101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], actual_r30⟩
theorem actual_cut29 : feed (some actual_s29) actual_c29 = some actual_s30 := by rfl
def actual_c30 : List UInt8 := [114, 95, 114, 101, 108, 97, 120, 101]
def actual_r31 : List String := [] ++ actual_r30
def actual_s31 : State := ⟨.ident, [101, 120, 97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], actual_r31⟩
theorem actual_cut30 : feed (some actual_s30) actual_c30 = some actual_s31 := by rfl
def actual_c31 : List UInt8 := [100, 41, 59, 10, 32, 32, 32, 32]
def actual_r32 : List String := [";", ")", "memory_order_relaxed"] ++ actual_r31
def actual_s32 : State := ⟨.normal, [], actual_r32⟩
theorem actual_cut31 : feed (some actual_s31) actual_c31 = some actual_s32 := by rfl
def actual_c32 : List UInt8 := [125, 10, 125]
def actual_r33 : List String := ["}", "}"] ++ actual_r32
def actual_s33 : State := ⟨.normal, [], actual_r33⟩
theorem actual_cut32 : feed (some actual_s32) actual_c32 = some actual_s33 := by rfl
def actual_chunks : List (List UInt8) := [actual_c0, actual_c1, actual_c2, actual_c3, actual_c4, actual_c5, actual_c6, actual_c7, actual_c8, actual_c9, actual_c10, actual_c11, actual_c12, actual_c13, actual_c14, actual_c15, actual_c16, actual_c17, actual_c18, actual_c19, actual_c20, actual_c21, actual_c22, actual_c23, actual_c24, actual_c25, actual_c26, actual_c27, actual_c28, actual_c29, actual_c30, actual_c31, actual_c32]
def actualSource : List UInt8 := actual_chunks.flatten
theorem actual_feed : actual_chunks.foldl feed (some initial) = some actual_s33 := by
  change actual_chunks.foldl feed (some actual_s0) = _
  simp only [actual_chunks, List.foldl_cons, List.foldl_nil]
  rw [actual_cut0, actual_cut1, actual_cut2, actual_cut3, actual_cut4, actual_cut5, actual_cut6, actual_cut7, actual_cut8, actual_cut9, actual_cut10, actual_cut11, actual_cut12, actual_cut13, actual_cut14, actual_cut15, actual_cut16, actual_cut17, actual_cut18, actual_cut19, actual_cut20, actual_cut21, actual_cut22, actual_cut23, actual_cut24, actual_cut25, actual_cut26, actual_cut27, actual_cut28, actual_cut29, actual_cut30, actual_cut31, actual_cut32]
theorem actual_tokens : tokenize actualSource = some (CAtomicIncrementSyntax.tokens proposal) := by
  rw [actualSource, ← chunks_exact, tokenizeChunks, actual_feed]
  rfl
theorem actual_syntax : CAtomicIncrementSyntax.check actualSource proposal = true := by
  unfold CAtomicIncrementSyntax.check
  rw [actual_tokens]
  simp

def changed_guard_r0 : List String := []
def changed_guard_s0 : State := initial
def changed_guard_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def changed_guard_r1 : List String := ["static"] ++ changed_guard_r0
def changed_guard_s1 : State := ⟨.ident, [105], changed_guard_r1⟩
theorem changed_guard_cut0 : feed (some changed_guard_s0) changed_guard_c0 = some changed_guard_s1 := by rfl
def changed_guard_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def changed_guard_r2 : List String := ["inline"] ++ changed_guard_r1
def changed_guard_s2 : State := ⟨.ident, [111, 118], changed_guard_r2⟩
theorem changed_guard_cut1 : feed (some changed_guard_s1) changed_guard_c1 = some changed_guard_s2 := by rfl
def changed_guard_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def changed_guard_r3 : List String := ["void"] ++ changed_guard_r2
def changed_guard_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], changed_guard_r3⟩
theorem changed_guard_cut2 : feed (some changed_guard_s2) changed_guard_c2 = some changed_guard_s3 := by rfl
def changed_guard_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def changed_guard_r4 : List String := ["(", "clean_inc"] ++ changed_guard_r3
def changed_guard_s4 : State := ⟨.ident, [101, 108, 99], changed_guard_r4⟩
theorem changed_guard_cut3 : feed (some changed_guard_s3) changed_guard_c3 = some changed_guard_s4 := by rfl
def changed_guard_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def changed_guard_r5 : List String := ["*", "clean_obj"] ++ changed_guard_r4
def changed_guard_s5 : State := ⟨.normal, [], changed_guard_r5⟩
theorem changed_guard_cut4 : feed (some changed_guard_s4) changed_guard_c4 = some changed_guard_s5 := by rfl
def changed_guard_c5 : List UInt8 := [111, 41, 32, 123, 10, 32, 32, 32]
def changed_guard_r6 : List String := ["{", ")", "o"] ++ changed_guard_r5
def changed_guard_s6 : State := ⟨.normal, [], changed_guard_r6⟩
theorem changed_guard_cut5 : feed (some changed_guard_s5) changed_guard_c5 = some changed_guard_s6 := by rfl
def changed_guard_c6 : List UInt8 := [32, 105, 102, 32, 40, 33, 99, 108]
def changed_guard_r7 : List String := ["!", "(", "if"] ++ changed_guard_r6
def changed_guard_s7 : State := ⟨.ident, [108, 99], changed_guard_r7⟩
theorem changed_guard_cut6 : feed (some changed_guard_s6) changed_guard_c6 = some changed_guard_s7 := by rfl
def changed_guard_c7 : List UInt8 := [101, 97, 110, 95, 105, 115, 95, 115]
def changed_guard_r8 : List String := [] ++ changed_guard_r7
def changed_guard_s8 : State := ⟨.ident, [115, 95, 115, 105, 95, 110, 97, 101, 108, 99], changed_guard_r8⟩
theorem changed_guard_cut7 : feed (some changed_guard_s7) changed_guard_c7 = some changed_guard_s8 := by rfl
def changed_guard_c8 : List UInt8 := [99, 97, 108, 97, 114, 40, 111, 41]
def changed_guard_r9 : List String := [")", "o", "(", "clean_is_scalar"] ++ changed_guard_r8
def changed_guard_s9 : State := ⟨.normal, [], changed_guard_r9⟩
theorem changed_guard_cut8 : feed (some changed_guard_s8) changed_guard_c8 = some changed_guard_s9 := by rfl
def changed_guard_c9 : List UInt8 := [32, 38, 38, 10, 32, 32, 32, 32]
def changed_guard_r10 : List String := ["&&"] ++ changed_guard_r9
def changed_guard_s10 : State := ⟨.normal, [], changed_guard_r10⟩
theorem changed_guard_cut9 : feed (some changed_guard_s9) changed_guard_c9 = some changed_guard_s10 := by rfl
def changed_guard_c10 : List UInt8 := [32, 32, 32, 32, 97, 116, 111, 109]
def changed_guard_r11 : List String := [] ++ changed_guard_r10
def changed_guard_s11 : State := ⟨.ident, [109, 111, 116, 97], changed_guard_r11⟩
theorem changed_guard_cut10 : feed (some changed_guard_s10) changed_guard_c10 = some changed_guard_s11 := by rfl
def changed_guard_c11 : List UInt8 := [105, 99, 95, 108, 111, 97, 100, 95]
def changed_guard_r12 : List String := [] ++ changed_guard_r11
def changed_guard_s12 : State := ⟨.ident, [95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], changed_guard_r12⟩
theorem changed_guard_cut11 : feed (some changed_guard_s11) changed_guard_c11 = some changed_guard_s12 := by rfl
def changed_guard_c12 : List UInt8 := [101, 120, 112, 108, 105, 99, 105, 116]
def changed_guard_r13 : List String := [] ++ changed_guard_r12
def changed_guard_s13 : State := ⟨.ident, [116, 105, 99, 105, 108, 112, 120, 101, 95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], changed_guard_r13⟩
theorem changed_guard_cut12 : feed (some changed_guard_s12) changed_guard_c12 = some changed_guard_s13 := by rfl
def changed_guard_c13 : List UInt8 := [40, 38, 111, 45, 62, 104, 101, 97]
def changed_guard_r14 : List String := ["->", "o", "&", "(", "atomic_load_explicit"] ++ changed_guard_r13
def changed_guard_s14 : State := ⟨.ident, [97, 101, 104], changed_guard_r14⟩
theorem changed_guard_cut13 : feed (some changed_guard_s13) changed_guard_c13 = some changed_guard_s14 := by rfl
def changed_guard_c14 : List UInt8 := [100, 101, 114, 46, 114, 101, 102, 95]
def changed_guard_r15 : List String := [".", "header"] ++ changed_guard_r14
def changed_guard_s15 : State := ⟨.ident, [95, 102, 101, 114], changed_guard_r15⟩
theorem changed_guard_cut14 : feed (some changed_guard_s14) changed_guard_c14 = some changed_guard_s15 := by rfl
def changed_guard_c15 : List UInt8 := [99, 111, 117, 110, 116, 44, 32, 109]
def changed_guard_r16 : List String := [",", "ref_count"] ++ changed_guard_r15
def changed_guard_s16 : State := ⟨.ident, [109], changed_guard_r16⟩
theorem changed_guard_cut15 : feed (some changed_guard_s15) changed_guard_c15 = some changed_guard_s16 := by rfl
def changed_guard_c16 : List UInt8 := [101, 109, 111, 114, 121, 95, 111, 114]
def changed_guard_r17 : List String := [] ++ changed_guard_r16
def changed_guard_s17 : State := ⟨.ident, [114, 111, 95, 121, 114, 111, 109, 101, 109], changed_guard_r17⟩
theorem changed_guard_cut16 : feed (some changed_guard_s16) changed_guard_c16 = some changed_guard_s17 := by rfl
def changed_guard_c17 : List UInt8 := [100, 101, 114, 95, 114, 101, 108, 97]
def changed_guard_r18 : List String := [] ++ changed_guard_r17
def changed_guard_s18 : State := ⟨.ident, [97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_guard_r18⟩
theorem changed_guard_cut17 : feed (some changed_guard_s17) changed_guard_c17 = some changed_guard_s18 := by rfl
def changed_guard_c18 : List UInt8 := [120, 101, 100, 41, 32, 62, 32, 67]
def changed_guard_r19 : List String := [">", ")", "memory_order_relaxed"] ++ changed_guard_r18
def changed_guard_s19 : State := ⟨.ident, [67], changed_guard_r19⟩
theorem changed_guard_cut18 : feed (some changed_guard_s18) changed_guard_c18 = some changed_guard_s19 := by rfl
def changed_guard_c19 : List UInt8 := [76, 69, 65, 78, 95, 82, 67, 95]
def changed_guard_r20 : List String := [] ++ changed_guard_r19
def changed_guard_s20 : State := ⟨.ident, [95, 67, 82, 95, 78, 65, 69, 76, 67], changed_guard_r20⟩
theorem changed_guard_cut19 : feed (some changed_guard_s19) changed_guard_c19 = some changed_guard_s20 := by rfl
def changed_guard_c20 : List UInt8 := [83, 84, 73, 67, 75, 89, 41, 32]
def changed_guard_r21 : List String := [")", "CLEAN_RC_STICKY"] ++ changed_guard_r20
def changed_guard_s21 : State := ⟨.normal, [], changed_guard_r21⟩
theorem changed_guard_cut20 : feed (some changed_guard_s20) changed_guard_c20 = some changed_guard_s21 := by rfl
def changed_guard_c21 : List UInt8 := [123, 10, 32, 32, 32, 32, 32, 32]
def changed_guard_r22 : List String := ["{"] ++ changed_guard_r21
def changed_guard_s22 : State := ⟨.normal, [], changed_guard_r22⟩
theorem changed_guard_cut21 : feed (some changed_guard_s21) changed_guard_c21 = some changed_guard_s22 := by rfl
def changed_guard_c22 : List UInt8 := [32, 32, 97, 116, 111, 109, 105, 99]
def changed_guard_r23 : List String := [] ++ changed_guard_r22
def changed_guard_s23 : State := ⟨.ident, [99, 105, 109, 111, 116, 97], changed_guard_r23⟩
theorem changed_guard_cut22 : feed (some changed_guard_s22) changed_guard_c22 = some changed_guard_s23 := by rfl
def changed_guard_c23 : List UInt8 := [95, 102, 101, 116, 99, 104, 95, 97]
def changed_guard_r24 : List String := [] ++ changed_guard_r23
def changed_guard_s24 : State := ⟨.ident, [97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], changed_guard_r24⟩
theorem changed_guard_cut23 : feed (some changed_guard_s23) changed_guard_c23 = some changed_guard_s24 := by rfl
def changed_guard_c24 : List UInt8 := [100, 100, 95, 101, 120, 112, 108, 105]
def changed_guard_r25 : List String := [] ++ changed_guard_r24
def changed_guard_s25 : State := ⟨.ident, [105, 108, 112, 120, 101, 95, 100, 100, 97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], changed_guard_r25⟩
theorem changed_guard_cut24 : feed (some changed_guard_s24) changed_guard_c24 = some changed_guard_s25 := by rfl
def changed_guard_c25 : List UInt8 := [99, 105, 116, 40, 38, 111, 45, 62]
def changed_guard_r26 : List String := ["->", "o", "&", "(", "atomic_fetch_add_explicit"] ++ changed_guard_r25
def changed_guard_s26 : State := ⟨.normal, [], changed_guard_r26⟩
theorem changed_guard_cut25 : feed (some changed_guard_s25) changed_guard_c25 = some changed_guard_s26 := by rfl
def changed_guard_c26 : List UInt8 := [104, 101, 97, 100, 101, 114, 46, 114]
def changed_guard_r27 : List String := [".", "header"] ++ changed_guard_r26
def changed_guard_s27 : State := ⟨.ident, [114], changed_guard_r27⟩
theorem changed_guard_cut26 : feed (some changed_guard_s26) changed_guard_c26 = some changed_guard_s27 := by rfl
def changed_guard_c27 : List UInt8 := [101, 102, 95, 99, 111, 117, 110, 116]
def changed_guard_r28 : List String := [] ++ changed_guard_r27
def changed_guard_s28 : State := ⟨.ident, [116, 110, 117, 111, 99, 95, 102, 101, 114], changed_guard_r28⟩
theorem changed_guard_cut27 : feed (some changed_guard_s27) changed_guard_c27 = some changed_guard_s28 := by rfl
def changed_guard_c28 : List UInt8 := [44, 32, 49, 44, 32, 109, 101, 109]
def changed_guard_r29 : List String := [",", "1", ",", "ref_count"] ++ changed_guard_r28
def changed_guard_s29 : State := ⟨.ident, [109, 101, 109], changed_guard_r29⟩
theorem changed_guard_cut28 : feed (some changed_guard_s28) changed_guard_c28 = some changed_guard_s29 := by rfl
def changed_guard_c29 : List UInt8 := [111, 114, 121, 95, 111, 114, 100, 101]
def changed_guard_r30 : List String := [] ++ changed_guard_r29
def changed_guard_s30 : State := ⟨.ident, [101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_guard_r30⟩
theorem changed_guard_cut29 : feed (some changed_guard_s29) changed_guard_c29 = some changed_guard_s30 := by rfl
def changed_guard_c30 : List UInt8 := [114, 95, 114, 101, 108, 97, 120, 101]
def changed_guard_r31 : List String := [] ++ changed_guard_r30
def changed_guard_s31 : State := ⟨.ident, [101, 120, 97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_guard_r31⟩
theorem changed_guard_cut30 : feed (some changed_guard_s30) changed_guard_c30 = some changed_guard_s31 := by rfl
def changed_guard_c31 : List UInt8 := [100, 41, 59, 10, 32, 32, 32, 32]
def changed_guard_r32 : List String := [";", ")", "memory_order_relaxed"] ++ changed_guard_r31
def changed_guard_s32 : State := ⟨.normal, [], changed_guard_r32⟩
theorem changed_guard_cut31 : feed (some changed_guard_s31) changed_guard_c31 = some changed_guard_s32 := by rfl
def changed_guard_c32 : List UInt8 := [125, 10, 125]
def changed_guard_r33 : List String := ["}", "}"] ++ changed_guard_r32
def changed_guard_s33 : State := ⟨.normal, [], changed_guard_r33⟩
theorem changed_guard_cut32 : feed (some changed_guard_s32) changed_guard_c32 = some changed_guard_s33 := by rfl
def changed_guard_chunks : List (List UInt8) := [changed_guard_c0, changed_guard_c1, changed_guard_c2, changed_guard_c3, changed_guard_c4, changed_guard_c5, changed_guard_c6, changed_guard_c7, changed_guard_c8, changed_guard_c9, changed_guard_c10, changed_guard_c11, changed_guard_c12, changed_guard_c13, changed_guard_c14, changed_guard_c15, changed_guard_c16, changed_guard_c17, changed_guard_c18, changed_guard_c19, changed_guard_c20, changed_guard_c21, changed_guard_c22, changed_guard_c23, changed_guard_c24, changed_guard_c25, changed_guard_c26, changed_guard_c27, changed_guard_c28, changed_guard_c29, changed_guard_c30, changed_guard_c31, changed_guard_c32]
def changed_guard : List UInt8 := changed_guard_chunks.flatten
theorem changed_guard_feed : changed_guard_chunks.foldl feed (some initial) = some changed_guard_s33 := by
  change changed_guard_chunks.foldl feed (some changed_guard_s0) = _
  simp only [changed_guard_chunks, List.foldl_cons, List.foldl_nil]
  rw [changed_guard_cut0, changed_guard_cut1, changed_guard_cut2, changed_guard_cut3, changed_guard_cut4, changed_guard_cut5, changed_guard_cut6, changed_guard_cut7, changed_guard_cut8, changed_guard_cut9, changed_guard_cut10, changed_guard_cut11, changed_guard_cut12, changed_guard_cut13, changed_guard_cut14, changed_guard_cut15, changed_guard_cut16, changed_guard_cut17, changed_guard_cut18, changed_guard_cut19, changed_guard_cut20, changed_guard_cut21, changed_guard_cut22, changed_guard_cut23, changed_guard_cut24, changed_guard_cut25, changed_guard_cut26, changed_guard_cut27, changed_guard_cut28, changed_guard_cut29, changed_guard_cut30, changed_guard_cut31, changed_guard_cut32]
theorem changed_guard_refuses : CAtomicIncrementSyntax.check changed_guard proposal = false := by
  unfold CAtomicIncrementSyntax.check
  rw [changed_guard, ← chunks_exact, tokenizeChunks, changed_guard_feed]
  decide

def changed_cutoff_r0 : List String := []
def changed_cutoff_s0 : State := initial
def changed_cutoff_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def changed_cutoff_r1 : List String := ["static"] ++ changed_cutoff_r0
def changed_cutoff_s1 : State := ⟨.ident, [105], changed_cutoff_r1⟩
theorem changed_cutoff_cut0 : feed (some changed_cutoff_s0) changed_cutoff_c0 = some changed_cutoff_s1 := by rfl
def changed_cutoff_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def changed_cutoff_r2 : List String := ["inline"] ++ changed_cutoff_r1
def changed_cutoff_s2 : State := ⟨.ident, [111, 118], changed_cutoff_r2⟩
theorem changed_cutoff_cut1 : feed (some changed_cutoff_s1) changed_cutoff_c1 = some changed_cutoff_s2 := by rfl
def changed_cutoff_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def changed_cutoff_r3 : List String := ["void"] ++ changed_cutoff_r2
def changed_cutoff_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], changed_cutoff_r3⟩
theorem changed_cutoff_cut2 : feed (some changed_cutoff_s2) changed_cutoff_c2 = some changed_cutoff_s3 := by rfl
def changed_cutoff_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def changed_cutoff_r4 : List String := ["(", "clean_inc"] ++ changed_cutoff_r3
def changed_cutoff_s4 : State := ⟨.ident, [101, 108, 99], changed_cutoff_r4⟩
theorem changed_cutoff_cut3 : feed (some changed_cutoff_s3) changed_cutoff_c3 = some changed_cutoff_s4 := by rfl
def changed_cutoff_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def changed_cutoff_r5 : List String := ["*", "clean_obj"] ++ changed_cutoff_r4
def changed_cutoff_s5 : State := ⟨.normal, [], changed_cutoff_r5⟩
theorem changed_cutoff_cut4 : feed (some changed_cutoff_s4) changed_cutoff_c4 = some changed_cutoff_s5 := by rfl
def changed_cutoff_c5 : List UInt8 := [111, 41, 32, 123, 10, 32, 32, 32]
def changed_cutoff_r6 : List String := ["{", ")", "o"] ++ changed_cutoff_r5
def changed_cutoff_s6 : State := ⟨.normal, [], changed_cutoff_r6⟩
theorem changed_cutoff_cut5 : feed (some changed_cutoff_s5) changed_cutoff_c5 = some changed_cutoff_s6 := by rfl
def changed_cutoff_c6 : List UInt8 := [32, 105, 102, 32, 40, 33, 99, 108]
def changed_cutoff_r7 : List String := ["!", "(", "if"] ++ changed_cutoff_r6
def changed_cutoff_s7 : State := ⟨.ident, [108, 99], changed_cutoff_r7⟩
theorem changed_cutoff_cut6 : feed (some changed_cutoff_s6) changed_cutoff_c6 = some changed_cutoff_s7 := by rfl
def changed_cutoff_c7 : List UInt8 := [101, 97, 110, 95, 105, 115, 95, 115]
def changed_cutoff_r8 : List String := [] ++ changed_cutoff_r7
def changed_cutoff_s8 : State := ⟨.ident, [115, 95, 115, 105, 95, 110, 97, 101, 108, 99], changed_cutoff_r8⟩
theorem changed_cutoff_cut7 : feed (some changed_cutoff_s7) changed_cutoff_c7 = some changed_cutoff_s8 := by rfl
def changed_cutoff_c8 : List UInt8 := [99, 97, 108, 97, 114, 40, 111, 41]
def changed_cutoff_r9 : List String := [")", "o", "(", "clean_is_scalar"] ++ changed_cutoff_r8
def changed_cutoff_s9 : State := ⟨.normal, [], changed_cutoff_r9⟩
theorem changed_cutoff_cut8 : feed (some changed_cutoff_s8) changed_cutoff_c8 = some changed_cutoff_s9 := by rfl
def changed_cutoff_c9 : List UInt8 := [32, 38, 38, 10, 32, 32, 32, 32]
def changed_cutoff_r10 : List String := ["&&"] ++ changed_cutoff_r9
def changed_cutoff_s10 : State := ⟨.normal, [], changed_cutoff_r10⟩
theorem changed_cutoff_cut9 : feed (some changed_cutoff_s9) changed_cutoff_c9 = some changed_cutoff_s10 := by rfl
def changed_cutoff_c10 : List UInt8 := [32, 32, 32, 32, 97, 116, 111, 109]
def changed_cutoff_r11 : List String := [] ++ changed_cutoff_r10
def changed_cutoff_s11 : State := ⟨.ident, [109, 111, 116, 97], changed_cutoff_r11⟩
theorem changed_cutoff_cut10 : feed (some changed_cutoff_s10) changed_cutoff_c10 = some changed_cutoff_s11 := by rfl
def changed_cutoff_c11 : List UInt8 := [105, 99, 95, 108, 111, 97, 100, 95]
def changed_cutoff_r12 : List String := [] ++ changed_cutoff_r11
def changed_cutoff_s12 : State := ⟨.ident, [95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], changed_cutoff_r12⟩
theorem changed_cutoff_cut11 : feed (some changed_cutoff_s11) changed_cutoff_c11 = some changed_cutoff_s12 := by rfl
def changed_cutoff_c12 : List UInt8 := [101, 120, 112, 108, 105, 99, 105, 116]
def changed_cutoff_r13 : List String := [] ++ changed_cutoff_r12
def changed_cutoff_s13 : State := ⟨.ident, [116, 105, 99, 105, 108, 112, 120, 101, 95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], changed_cutoff_r13⟩
theorem changed_cutoff_cut12 : feed (some changed_cutoff_s12) changed_cutoff_c12 = some changed_cutoff_s13 := by rfl
def changed_cutoff_c13 : List UInt8 := [40, 38, 111, 45, 62, 104, 101, 97]
def changed_cutoff_r14 : List String := ["->", "o", "&", "(", "atomic_load_explicit"] ++ changed_cutoff_r13
def changed_cutoff_s14 : State := ⟨.ident, [97, 101, 104], changed_cutoff_r14⟩
theorem changed_cutoff_cut13 : feed (some changed_cutoff_s13) changed_cutoff_c13 = some changed_cutoff_s14 := by rfl
def changed_cutoff_c14 : List UInt8 := [100, 101, 114, 46, 114, 101, 102, 95]
def changed_cutoff_r15 : List String := [".", "header"] ++ changed_cutoff_r14
def changed_cutoff_s15 : State := ⟨.ident, [95, 102, 101, 114], changed_cutoff_r15⟩
theorem changed_cutoff_cut14 : feed (some changed_cutoff_s14) changed_cutoff_c14 = some changed_cutoff_s15 := by rfl
def changed_cutoff_c15 : List UInt8 := [99, 111, 117, 110, 116, 44, 32, 109]
def changed_cutoff_r16 : List String := [",", "ref_count"] ++ changed_cutoff_r15
def changed_cutoff_s16 : State := ⟨.ident, [109], changed_cutoff_r16⟩
theorem changed_cutoff_cut15 : feed (some changed_cutoff_s15) changed_cutoff_c15 = some changed_cutoff_s16 := by rfl
def changed_cutoff_c16 : List UInt8 := [101, 109, 111, 114, 121, 95, 111, 114]
def changed_cutoff_r17 : List String := [] ++ changed_cutoff_r16
def changed_cutoff_s17 : State := ⟨.ident, [114, 111, 95, 121, 114, 111, 109, 101, 109], changed_cutoff_r17⟩
theorem changed_cutoff_cut16 : feed (some changed_cutoff_s16) changed_cutoff_c16 = some changed_cutoff_s17 := by rfl
def changed_cutoff_c17 : List UInt8 := [100, 101, 114, 95, 114, 101, 108, 97]
def changed_cutoff_r18 : List String := [] ++ changed_cutoff_r17
def changed_cutoff_s18 : State := ⟨.ident, [97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_cutoff_r18⟩
theorem changed_cutoff_cut17 : feed (some changed_cutoff_s17) changed_cutoff_c17 = some changed_cutoff_s18 := by rfl
def changed_cutoff_c18 : List UInt8 := [120, 101, 100, 41, 32, 60, 32, 67]
def changed_cutoff_r19 : List String := ["<", ")", "memory_order_relaxed"] ++ changed_cutoff_r18
def changed_cutoff_s19 : State := ⟨.ident, [67], changed_cutoff_r19⟩
theorem changed_cutoff_cut18 : feed (some changed_cutoff_s18) changed_cutoff_c18 = some changed_cutoff_s19 := by rfl
def changed_cutoff_c19 : List UInt8 := [76, 69, 65, 78, 95, 82, 67, 95]
def changed_cutoff_r20 : List String := [] ++ changed_cutoff_r19
def changed_cutoff_s20 : State := ⟨.ident, [95, 67, 82, 95, 78, 65, 69, 76, 67], changed_cutoff_r20⟩
theorem changed_cutoff_cut19 : feed (some changed_cutoff_s19) changed_cutoff_c19 = some changed_cutoff_s20 := by rfl
def changed_cutoff_c20 : List UInt8 := [83, 84, 73, 67, 75, 89, 95, 68]
def changed_cutoff_r21 : List String := [] ++ changed_cutoff_r20
def changed_cutoff_s21 : State := ⟨.ident, [68, 95, 89, 75, 67, 73, 84, 83, 95, 67, 82, 95, 78, 65, 69, 76, 67], changed_cutoff_r21⟩
theorem changed_cutoff_cut20 : feed (some changed_cutoff_s20) changed_cutoff_c20 = some changed_cutoff_s21 := by rfl
def changed_cutoff_c21 : List UInt8 := [82, 79, 80, 41, 32, 123, 10, 32]
def changed_cutoff_r22 : List String := ["{", ")", "CLEAN_RC_STICKY_DROP"] ++ changed_cutoff_r21
def changed_cutoff_s22 : State := ⟨.normal, [], changed_cutoff_r22⟩
theorem changed_cutoff_cut21 : feed (some changed_cutoff_s21) changed_cutoff_c21 = some changed_cutoff_s22 := by rfl
def changed_cutoff_c22 : List UInt8 := [32, 32, 32, 32, 32, 32, 32, 97]
def changed_cutoff_r23 : List String := [] ++ changed_cutoff_r22
def changed_cutoff_s23 : State := ⟨.ident, [97], changed_cutoff_r23⟩
theorem changed_cutoff_cut22 : feed (some changed_cutoff_s22) changed_cutoff_c22 = some changed_cutoff_s23 := by rfl
def changed_cutoff_c23 : List UInt8 := [116, 111, 109, 105, 99, 95, 102, 101]
def changed_cutoff_r24 : List String := [] ++ changed_cutoff_r23
def changed_cutoff_s24 : State := ⟨.ident, [101, 102, 95, 99, 105, 109, 111, 116, 97], changed_cutoff_r24⟩
theorem changed_cutoff_cut23 : feed (some changed_cutoff_s23) changed_cutoff_c23 = some changed_cutoff_s24 := by rfl
def changed_cutoff_c24 : List UInt8 := [116, 99, 104, 95, 97, 100, 100, 95]
def changed_cutoff_r25 : List String := [] ++ changed_cutoff_r24
def changed_cutoff_s25 : State := ⟨.ident, [95, 100, 100, 97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], changed_cutoff_r25⟩
theorem changed_cutoff_cut24 : feed (some changed_cutoff_s24) changed_cutoff_c24 = some changed_cutoff_s25 := by rfl
def changed_cutoff_c25 : List UInt8 := [101, 120, 112, 108, 105, 99, 105, 116]
def changed_cutoff_r26 : List String := [] ++ changed_cutoff_r25
def changed_cutoff_s26 : State := ⟨.ident, [116, 105, 99, 105, 108, 112, 120, 101, 95, 100, 100, 97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], changed_cutoff_r26⟩
theorem changed_cutoff_cut25 : feed (some changed_cutoff_s25) changed_cutoff_c25 = some changed_cutoff_s26 := by rfl
def changed_cutoff_c26 : List UInt8 := [40, 38, 111, 45, 62, 104, 101, 97]
def changed_cutoff_r27 : List String := ["->", "o", "&", "(", "atomic_fetch_add_explicit"] ++ changed_cutoff_r26
def changed_cutoff_s27 : State := ⟨.ident, [97, 101, 104], changed_cutoff_r27⟩
theorem changed_cutoff_cut26 : feed (some changed_cutoff_s26) changed_cutoff_c26 = some changed_cutoff_s27 := by rfl
def changed_cutoff_c27 : List UInt8 := [100, 101, 114, 46, 114, 101, 102, 95]
def changed_cutoff_r28 : List String := [".", "header"] ++ changed_cutoff_r27
def changed_cutoff_s28 : State := ⟨.ident, [95, 102, 101, 114], changed_cutoff_r28⟩
theorem changed_cutoff_cut27 : feed (some changed_cutoff_s27) changed_cutoff_c27 = some changed_cutoff_s28 := by rfl
def changed_cutoff_c28 : List UInt8 := [99, 111, 117, 110, 116, 44, 32, 49]
def changed_cutoff_r29 : List String := [",", "ref_count"] ++ changed_cutoff_r28
def changed_cutoff_s29 : State := ⟨.ident, [49], changed_cutoff_r29⟩
theorem changed_cutoff_cut28 : feed (some changed_cutoff_s28) changed_cutoff_c28 = some changed_cutoff_s29 := by rfl
def changed_cutoff_c29 : List UInt8 := [44, 32, 109, 101, 109, 111, 114, 121]
def changed_cutoff_r30 : List String := [",", "1"] ++ changed_cutoff_r29
def changed_cutoff_s30 : State := ⟨.ident, [121, 114, 111, 109, 101, 109], changed_cutoff_r30⟩
theorem changed_cutoff_cut29 : feed (some changed_cutoff_s29) changed_cutoff_c29 = some changed_cutoff_s30 := by rfl
def changed_cutoff_c30 : List UInt8 := [95, 111, 114, 100, 101, 114, 95, 114]
def changed_cutoff_r31 : List String := [] ++ changed_cutoff_r30
def changed_cutoff_s31 : State := ⟨.ident, [114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_cutoff_r31⟩
theorem changed_cutoff_cut30 : feed (some changed_cutoff_s30) changed_cutoff_c30 = some changed_cutoff_s31 := by rfl
def changed_cutoff_c31 : List UInt8 := [101, 108, 97, 120, 101, 100, 41, 59]
def changed_cutoff_r32 : List String := [";", ")", "memory_order_relaxed"] ++ changed_cutoff_r31
def changed_cutoff_s32 : State := ⟨.normal, [], changed_cutoff_r32⟩
theorem changed_cutoff_cut31 : feed (some changed_cutoff_s31) changed_cutoff_c31 = some changed_cutoff_s32 := by rfl
def changed_cutoff_c32 : List UInt8 := [10, 32, 32, 32, 32, 125, 10, 125]
def changed_cutoff_r33 : List String := ["}", "}"] ++ changed_cutoff_r32
def changed_cutoff_s33 : State := ⟨.normal, [], changed_cutoff_r33⟩
theorem changed_cutoff_cut32 : feed (some changed_cutoff_s32) changed_cutoff_c32 = some changed_cutoff_s33 := by rfl
def changed_cutoff_chunks : List (List UInt8) := [changed_cutoff_c0, changed_cutoff_c1, changed_cutoff_c2, changed_cutoff_c3, changed_cutoff_c4, changed_cutoff_c5, changed_cutoff_c6, changed_cutoff_c7, changed_cutoff_c8, changed_cutoff_c9, changed_cutoff_c10, changed_cutoff_c11, changed_cutoff_c12, changed_cutoff_c13, changed_cutoff_c14, changed_cutoff_c15, changed_cutoff_c16, changed_cutoff_c17, changed_cutoff_c18, changed_cutoff_c19, changed_cutoff_c20, changed_cutoff_c21, changed_cutoff_c22, changed_cutoff_c23, changed_cutoff_c24, changed_cutoff_c25, changed_cutoff_c26, changed_cutoff_c27, changed_cutoff_c28, changed_cutoff_c29, changed_cutoff_c30, changed_cutoff_c31, changed_cutoff_c32]
def changed_cutoff : List UInt8 := changed_cutoff_chunks.flatten
theorem changed_cutoff_feed : changed_cutoff_chunks.foldl feed (some initial) = some changed_cutoff_s33 := by
  change changed_cutoff_chunks.foldl feed (some changed_cutoff_s0) = _
  simp only [changed_cutoff_chunks, List.foldl_cons, List.foldl_nil]
  rw [changed_cutoff_cut0, changed_cutoff_cut1, changed_cutoff_cut2, changed_cutoff_cut3, changed_cutoff_cut4, changed_cutoff_cut5, changed_cutoff_cut6, changed_cutoff_cut7, changed_cutoff_cut8, changed_cutoff_cut9, changed_cutoff_cut10, changed_cutoff_cut11, changed_cutoff_cut12, changed_cutoff_cut13, changed_cutoff_cut14, changed_cutoff_cut15, changed_cutoff_cut16, changed_cutoff_cut17, changed_cutoff_cut18, changed_cutoff_cut19, changed_cutoff_cut20, changed_cutoff_cut21, changed_cutoff_cut22, changed_cutoff_cut23, changed_cutoff_cut24, changed_cutoff_cut25, changed_cutoff_cut26, changed_cutoff_cut27, changed_cutoff_cut28, changed_cutoff_cut29, changed_cutoff_cut30, changed_cutoff_cut31, changed_cutoff_cut32]
theorem changed_cutoff_refuses : CAtomicIncrementSyntax.check changed_cutoff proposal = false := by
  unfold CAtomicIncrementSyntax.check
  rw [changed_cutoff, ← chunks_exact, tokenizeChunks, changed_cutoff_feed]
  decide

def changed_scalar_guard_r0 : List String := []
def changed_scalar_guard_s0 : State := initial
def changed_scalar_guard_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def changed_scalar_guard_r1 : List String := ["static"] ++ changed_scalar_guard_r0
def changed_scalar_guard_s1 : State := ⟨.ident, [105], changed_scalar_guard_r1⟩
theorem changed_scalar_guard_cut0 : feed (some changed_scalar_guard_s0) changed_scalar_guard_c0 = some changed_scalar_guard_s1 := by rfl
def changed_scalar_guard_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def changed_scalar_guard_r2 : List String := ["inline"] ++ changed_scalar_guard_r1
def changed_scalar_guard_s2 : State := ⟨.ident, [111, 118], changed_scalar_guard_r2⟩
theorem changed_scalar_guard_cut1 : feed (some changed_scalar_guard_s1) changed_scalar_guard_c1 = some changed_scalar_guard_s2 := by rfl
def changed_scalar_guard_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def changed_scalar_guard_r3 : List String := ["void"] ++ changed_scalar_guard_r2
def changed_scalar_guard_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], changed_scalar_guard_r3⟩
theorem changed_scalar_guard_cut2 : feed (some changed_scalar_guard_s2) changed_scalar_guard_c2 = some changed_scalar_guard_s3 := by rfl
def changed_scalar_guard_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def changed_scalar_guard_r4 : List String := ["(", "clean_inc"] ++ changed_scalar_guard_r3
def changed_scalar_guard_s4 : State := ⟨.ident, [101, 108, 99], changed_scalar_guard_r4⟩
theorem changed_scalar_guard_cut3 : feed (some changed_scalar_guard_s3) changed_scalar_guard_c3 = some changed_scalar_guard_s4 := by rfl
def changed_scalar_guard_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def changed_scalar_guard_r5 : List String := ["*", "clean_obj"] ++ changed_scalar_guard_r4
def changed_scalar_guard_s5 : State := ⟨.normal, [], changed_scalar_guard_r5⟩
theorem changed_scalar_guard_cut4 : feed (some changed_scalar_guard_s4) changed_scalar_guard_c4 = some changed_scalar_guard_s5 := by rfl
def changed_scalar_guard_c5 : List UInt8 := [111, 41, 32, 123, 10, 32, 32, 32]
def changed_scalar_guard_r6 : List String := ["{", ")", "o"] ++ changed_scalar_guard_r5
def changed_scalar_guard_s6 : State := ⟨.normal, [], changed_scalar_guard_r6⟩
theorem changed_scalar_guard_cut5 : feed (some changed_scalar_guard_s5) changed_scalar_guard_c5 = some changed_scalar_guard_s6 := by rfl
def changed_scalar_guard_c6 : List UInt8 := [32, 105, 102, 32, 40, 99, 108, 101]
def changed_scalar_guard_r7 : List String := ["(", "if"] ++ changed_scalar_guard_r6
def changed_scalar_guard_s7 : State := ⟨.ident, [101, 108, 99], changed_scalar_guard_r7⟩
theorem changed_scalar_guard_cut6 : feed (some changed_scalar_guard_s6) changed_scalar_guard_c6 = some changed_scalar_guard_s7 := by rfl
def changed_scalar_guard_c7 : List UInt8 := [97, 110, 95, 105, 115, 95, 115, 99]
def changed_scalar_guard_r8 : List String := [] ++ changed_scalar_guard_r7
def changed_scalar_guard_s8 : State := ⟨.ident, [99, 115, 95, 115, 105, 95, 110, 97, 101, 108, 99], changed_scalar_guard_r8⟩
theorem changed_scalar_guard_cut7 : feed (some changed_scalar_guard_s7) changed_scalar_guard_c7 = some changed_scalar_guard_s8 := by rfl
def changed_scalar_guard_c8 : List UInt8 := [97, 108, 97, 114, 40, 111, 41, 32]
def changed_scalar_guard_r9 : List String := [")", "o", "(", "clean_is_scalar"] ++ changed_scalar_guard_r8
def changed_scalar_guard_s9 : State := ⟨.normal, [], changed_scalar_guard_r9⟩
theorem changed_scalar_guard_cut8 : feed (some changed_scalar_guard_s8) changed_scalar_guard_c8 = some changed_scalar_guard_s9 := by rfl
def changed_scalar_guard_c9 : List UInt8 := [38, 38, 10, 32, 32, 32, 32, 32]
def changed_scalar_guard_r10 : List String := ["&&"] ++ changed_scalar_guard_r9
def changed_scalar_guard_s10 : State := ⟨.normal, [], changed_scalar_guard_r10⟩
theorem changed_scalar_guard_cut9 : feed (some changed_scalar_guard_s9) changed_scalar_guard_c9 = some changed_scalar_guard_s10 := by rfl
def changed_scalar_guard_c10 : List UInt8 := [32, 32, 32, 97, 116, 111, 109, 105]
def changed_scalar_guard_r11 : List String := [] ++ changed_scalar_guard_r10
def changed_scalar_guard_s11 : State := ⟨.ident, [105, 109, 111, 116, 97], changed_scalar_guard_r11⟩
theorem changed_scalar_guard_cut10 : feed (some changed_scalar_guard_s10) changed_scalar_guard_c10 = some changed_scalar_guard_s11 := by rfl
def changed_scalar_guard_c11 : List UInt8 := [99, 95, 108, 111, 97, 100, 95, 101]
def changed_scalar_guard_r12 : List String := [] ++ changed_scalar_guard_r11
def changed_scalar_guard_s12 : State := ⟨.ident, [101, 95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], changed_scalar_guard_r12⟩
theorem changed_scalar_guard_cut11 : feed (some changed_scalar_guard_s11) changed_scalar_guard_c11 = some changed_scalar_guard_s12 := by rfl
def changed_scalar_guard_c12 : List UInt8 := [120, 112, 108, 105, 99, 105, 116, 40]
def changed_scalar_guard_r13 : List String := ["(", "atomic_load_explicit"] ++ changed_scalar_guard_r12
def changed_scalar_guard_s13 : State := ⟨.normal, [], changed_scalar_guard_r13⟩
theorem changed_scalar_guard_cut12 : feed (some changed_scalar_guard_s12) changed_scalar_guard_c12 = some changed_scalar_guard_s13 := by rfl
def changed_scalar_guard_c13 : List UInt8 := [38, 111, 45, 62, 104, 101, 97, 100]
def changed_scalar_guard_r14 : List String := ["->", "o", "&"] ++ changed_scalar_guard_r13
def changed_scalar_guard_s14 : State := ⟨.ident, [100, 97, 101, 104], changed_scalar_guard_r14⟩
theorem changed_scalar_guard_cut13 : feed (some changed_scalar_guard_s13) changed_scalar_guard_c13 = some changed_scalar_guard_s14 := by rfl
def changed_scalar_guard_c14 : List UInt8 := [101, 114, 46, 114, 101, 102, 95, 99]
def changed_scalar_guard_r15 : List String := [".", "header"] ++ changed_scalar_guard_r14
def changed_scalar_guard_s15 : State := ⟨.ident, [99, 95, 102, 101, 114], changed_scalar_guard_r15⟩
theorem changed_scalar_guard_cut14 : feed (some changed_scalar_guard_s14) changed_scalar_guard_c14 = some changed_scalar_guard_s15 := by rfl
def changed_scalar_guard_c15 : List UInt8 := [111, 117, 110, 116, 44, 32, 109, 101]
def changed_scalar_guard_r16 : List String := [",", "ref_count"] ++ changed_scalar_guard_r15
def changed_scalar_guard_s16 : State := ⟨.ident, [101, 109], changed_scalar_guard_r16⟩
theorem changed_scalar_guard_cut15 : feed (some changed_scalar_guard_s15) changed_scalar_guard_c15 = some changed_scalar_guard_s16 := by rfl
def changed_scalar_guard_c16 : List UInt8 := [109, 111, 114, 121, 95, 111, 114, 100]
def changed_scalar_guard_r17 : List String := [] ++ changed_scalar_guard_r16
def changed_scalar_guard_s17 : State := ⟨.ident, [100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_scalar_guard_r17⟩
theorem changed_scalar_guard_cut16 : feed (some changed_scalar_guard_s16) changed_scalar_guard_c16 = some changed_scalar_guard_s17 := by rfl
def changed_scalar_guard_c17 : List UInt8 := [101, 114, 95, 114, 101, 108, 97, 120]
def changed_scalar_guard_r18 : List String := [] ++ changed_scalar_guard_r17
def changed_scalar_guard_s18 : State := ⟨.ident, [120, 97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_scalar_guard_r18⟩
theorem changed_scalar_guard_cut17 : feed (some changed_scalar_guard_s17) changed_scalar_guard_c17 = some changed_scalar_guard_s18 := by rfl
def changed_scalar_guard_c18 : List UInt8 := [101, 100, 41, 32, 60, 32, 67, 76]
def changed_scalar_guard_r19 : List String := ["<", ")", "memory_order_relaxed"] ++ changed_scalar_guard_r18
def changed_scalar_guard_s19 : State := ⟨.ident, [76, 67], changed_scalar_guard_r19⟩
theorem changed_scalar_guard_cut18 : feed (some changed_scalar_guard_s18) changed_scalar_guard_c18 = some changed_scalar_guard_s19 := by rfl
def changed_scalar_guard_c19 : List UInt8 := [69, 65, 78, 95, 82, 67, 95, 83]
def changed_scalar_guard_r20 : List String := [] ++ changed_scalar_guard_r19
def changed_scalar_guard_s20 : State := ⟨.ident, [83, 95, 67, 82, 95, 78, 65, 69, 76, 67], changed_scalar_guard_r20⟩
theorem changed_scalar_guard_cut19 : feed (some changed_scalar_guard_s19) changed_scalar_guard_c19 = some changed_scalar_guard_s20 := by rfl
def changed_scalar_guard_c20 : List UInt8 := [84, 73, 67, 75, 89, 41, 32, 123]
def changed_scalar_guard_r21 : List String := ["{", ")", "CLEAN_RC_STICKY"] ++ changed_scalar_guard_r20
def changed_scalar_guard_s21 : State := ⟨.normal, [], changed_scalar_guard_r21⟩
theorem changed_scalar_guard_cut20 : feed (some changed_scalar_guard_s20) changed_scalar_guard_c20 = some changed_scalar_guard_s21 := by rfl
def changed_scalar_guard_c21 : List UInt8 := [10, 32, 32, 32, 32, 32, 32, 32]
def changed_scalar_guard_r22 : List String := [] ++ changed_scalar_guard_r21
def changed_scalar_guard_s22 : State := ⟨.normal, [], changed_scalar_guard_r22⟩
theorem changed_scalar_guard_cut21 : feed (some changed_scalar_guard_s21) changed_scalar_guard_c21 = some changed_scalar_guard_s22 := by rfl
def changed_scalar_guard_c22 : List UInt8 := [32, 97, 116, 111, 109, 105, 99, 95]
def changed_scalar_guard_r23 : List String := [] ++ changed_scalar_guard_r22
def changed_scalar_guard_s23 : State := ⟨.ident, [95, 99, 105, 109, 111, 116, 97], changed_scalar_guard_r23⟩
theorem changed_scalar_guard_cut22 : feed (some changed_scalar_guard_s22) changed_scalar_guard_c22 = some changed_scalar_guard_s23 := by rfl
def changed_scalar_guard_c23 : List UInt8 := [102, 101, 116, 99, 104, 95, 97, 100]
def changed_scalar_guard_r24 : List String := [] ++ changed_scalar_guard_r23
def changed_scalar_guard_s24 : State := ⟨.ident, [100, 97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], changed_scalar_guard_r24⟩
theorem changed_scalar_guard_cut23 : feed (some changed_scalar_guard_s23) changed_scalar_guard_c23 = some changed_scalar_guard_s24 := by rfl
def changed_scalar_guard_c24 : List UInt8 := [100, 95, 101, 120, 112, 108, 105, 99]
def changed_scalar_guard_r25 : List String := [] ++ changed_scalar_guard_r24
def changed_scalar_guard_s25 : State := ⟨.ident, [99, 105, 108, 112, 120, 101, 95, 100, 100, 97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], changed_scalar_guard_r25⟩
theorem changed_scalar_guard_cut24 : feed (some changed_scalar_guard_s24) changed_scalar_guard_c24 = some changed_scalar_guard_s25 := by rfl
def changed_scalar_guard_c25 : List UInt8 := [105, 116, 40, 38, 111, 45, 62, 104]
def changed_scalar_guard_r26 : List String := ["->", "o", "&", "(", "atomic_fetch_add_explicit"] ++ changed_scalar_guard_r25
def changed_scalar_guard_s26 : State := ⟨.ident, [104], changed_scalar_guard_r26⟩
theorem changed_scalar_guard_cut25 : feed (some changed_scalar_guard_s25) changed_scalar_guard_c25 = some changed_scalar_guard_s26 := by rfl
def changed_scalar_guard_c26 : List UInt8 := [101, 97, 100, 101, 114, 46, 114, 101]
def changed_scalar_guard_r27 : List String := [".", "header"] ++ changed_scalar_guard_r26
def changed_scalar_guard_s27 : State := ⟨.ident, [101, 114], changed_scalar_guard_r27⟩
theorem changed_scalar_guard_cut26 : feed (some changed_scalar_guard_s26) changed_scalar_guard_c26 = some changed_scalar_guard_s27 := by rfl
def changed_scalar_guard_c27 : List UInt8 := [102, 95, 99, 111, 117, 110, 116, 44]
def changed_scalar_guard_r28 : List String := [",", "ref_count"] ++ changed_scalar_guard_r27
def changed_scalar_guard_s28 : State := ⟨.normal, [], changed_scalar_guard_r28⟩
theorem changed_scalar_guard_cut27 : feed (some changed_scalar_guard_s27) changed_scalar_guard_c27 = some changed_scalar_guard_s28 := by rfl
def changed_scalar_guard_c28 : List UInt8 := [32, 49, 44, 32, 109, 101, 109, 111]
def changed_scalar_guard_r29 : List String := [",", "1"] ++ changed_scalar_guard_r28
def changed_scalar_guard_s29 : State := ⟨.ident, [111, 109, 101, 109], changed_scalar_guard_r29⟩
theorem changed_scalar_guard_cut28 : feed (some changed_scalar_guard_s28) changed_scalar_guard_c28 = some changed_scalar_guard_s29 := by rfl
def changed_scalar_guard_c29 : List UInt8 := [114, 121, 95, 111, 114, 100, 101, 114]
def changed_scalar_guard_r30 : List String := [] ++ changed_scalar_guard_r29
def changed_scalar_guard_s30 : State := ⟨.ident, [114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_scalar_guard_r30⟩
theorem changed_scalar_guard_cut29 : feed (some changed_scalar_guard_s29) changed_scalar_guard_c29 = some changed_scalar_guard_s30 := by rfl
def changed_scalar_guard_c30 : List UInt8 := [95, 114, 101, 108, 97, 120, 101, 100]
def changed_scalar_guard_r31 : List String := [] ++ changed_scalar_guard_r30
def changed_scalar_guard_s31 : State := ⟨.ident, [100, 101, 120, 97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_scalar_guard_r31⟩
theorem changed_scalar_guard_cut30 : feed (some changed_scalar_guard_s30) changed_scalar_guard_c30 = some changed_scalar_guard_s31 := by rfl
def changed_scalar_guard_c31 : List UInt8 := [41, 59, 10, 32, 32, 32, 32, 125]
def changed_scalar_guard_r32 : List String := ["}", ";", ")", "memory_order_relaxed"] ++ changed_scalar_guard_r31
def changed_scalar_guard_s32 : State := ⟨.normal, [], changed_scalar_guard_r32⟩
theorem changed_scalar_guard_cut31 : feed (some changed_scalar_guard_s31) changed_scalar_guard_c31 = some changed_scalar_guard_s32 := by rfl
def changed_scalar_guard_c32 : List UInt8 := [10, 125]
def changed_scalar_guard_r33 : List String := ["}"] ++ changed_scalar_guard_r32
def changed_scalar_guard_s33 : State := ⟨.normal, [], changed_scalar_guard_r33⟩
theorem changed_scalar_guard_cut32 : feed (some changed_scalar_guard_s32) changed_scalar_guard_c32 = some changed_scalar_guard_s33 := by rfl
def changed_scalar_guard_chunks : List (List UInt8) := [changed_scalar_guard_c0, changed_scalar_guard_c1, changed_scalar_guard_c2, changed_scalar_guard_c3, changed_scalar_guard_c4, changed_scalar_guard_c5, changed_scalar_guard_c6, changed_scalar_guard_c7, changed_scalar_guard_c8, changed_scalar_guard_c9, changed_scalar_guard_c10, changed_scalar_guard_c11, changed_scalar_guard_c12, changed_scalar_guard_c13, changed_scalar_guard_c14, changed_scalar_guard_c15, changed_scalar_guard_c16, changed_scalar_guard_c17, changed_scalar_guard_c18, changed_scalar_guard_c19, changed_scalar_guard_c20, changed_scalar_guard_c21, changed_scalar_guard_c22, changed_scalar_guard_c23, changed_scalar_guard_c24, changed_scalar_guard_c25, changed_scalar_guard_c26, changed_scalar_guard_c27, changed_scalar_guard_c28, changed_scalar_guard_c29, changed_scalar_guard_c30, changed_scalar_guard_c31, changed_scalar_guard_c32]
def changed_scalar_guard : List UInt8 := changed_scalar_guard_chunks.flatten
theorem changed_scalar_guard_feed : changed_scalar_guard_chunks.foldl feed (some initial) = some changed_scalar_guard_s33 := by
  change changed_scalar_guard_chunks.foldl feed (some changed_scalar_guard_s0) = _
  simp only [changed_scalar_guard_chunks, List.foldl_cons, List.foldl_nil]
  rw [changed_scalar_guard_cut0, changed_scalar_guard_cut1, changed_scalar_guard_cut2, changed_scalar_guard_cut3, changed_scalar_guard_cut4, changed_scalar_guard_cut5, changed_scalar_guard_cut6, changed_scalar_guard_cut7, changed_scalar_guard_cut8, changed_scalar_guard_cut9, changed_scalar_guard_cut10, changed_scalar_guard_cut11, changed_scalar_guard_cut12, changed_scalar_guard_cut13, changed_scalar_guard_cut14, changed_scalar_guard_cut15, changed_scalar_guard_cut16, changed_scalar_guard_cut17, changed_scalar_guard_cut18, changed_scalar_guard_cut19, changed_scalar_guard_cut20, changed_scalar_guard_cut21, changed_scalar_guard_cut22, changed_scalar_guard_cut23, changed_scalar_guard_cut24, changed_scalar_guard_cut25, changed_scalar_guard_cut26, changed_scalar_guard_cut27, changed_scalar_guard_cut28, changed_scalar_guard_cut29, changed_scalar_guard_cut30, changed_scalar_guard_cut31, changed_scalar_guard_cut32]
theorem changed_scalar_guard_refuses : CAtomicIncrementSyntax.check changed_scalar_guard proposal = false := by
  unfold CAtomicIncrementSyntax.check
  rw [changed_scalar_guard, ← chunks_exact, tokenizeChunks, changed_scalar_guard_feed]
  decide

def changed_operand_r0 : List String := []
def changed_operand_s0 : State := initial
def changed_operand_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def changed_operand_r1 : List String := ["static"] ++ changed_operand_r0
def changed_operand_s1 : State := ⟨.ident, [105], changed_operand_r1⟩
theorem changed_operand_cut0 : feed (some changed_operand_s0) changed_operand_c0 = some changed_operand_s1 := by rfl
def changed_operand_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def changed_operand_r2 : List String := ["inline"] ++ changed_operand_r1
def changed_operand_s2 : State := ⟨.ident, [111, 118], changed_operand_r2⟩
theorem changed_operand_cut1 : feed (some changed_operand_s1) changed_operand_c1 = some changed_operand_s2 := by rfl
def changed_operand_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def changed_operand_r3 : List String := ["void"] ++ changed_operand_r2
def changed_operand_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], changed_operand_r3⟩
theorem changed_operand_cut2 : feed (some changed_operand_s2) changed_operand_c2 = some changed_operand_s3 := by rfl
def changed_operand_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def changed_operand_r4 : List String := ["(", "clean_inc"] ++ changed_operand_r3
def changed_operand_s4 : State := ⟨.ident, [101, 108, 99], changed_operand_r4⟩
theorem changed_operand_cut3 : feed (some changed_operand_s3) changed_operand_c3 = some changed_operand_s4 := by rfl
def changed_operand_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def changed_operand_r5 : List String := ["*", "clean_obj"] ++ changed_operand_r4
def changed_operand_s5 : State := ⟨.normal, [], changed_operand_r5⟩
theorem changed_operand_cut4 : feed (some changed_operand_s4) changed_operand_c4 = some changed_operand_s5 := by rfl
def changed_operand_c5 : List UInt8 := [111, 41, 32, 123, 10, 32, 32, 32]
def changed_operand_r6 : List String := ["{", ")", "o"] ++ changed_operand_r5
def changed_operand_s6 : State := ⟨.normal, [], changed_operand_r6⟩
theorem changed_operand_cut5 : feed (some changed_operand_s5) changed_operand_c5 = some changed_operand_s6 := by rfl
def changed_operand_c6 : List UInt8 := [32, 105, 102, 32, 40, 33, 99, 108]
def changed_operand_r7 : List String := ["!", "(", "if"] ++ changed_operand_r6
def changed_operand_s7 : State := ⟨.ident, [108, 99], changed_operand_r7⟩
theorem changed_operand_cut6 : feed (some changed_operand_s6) changed_operand_c6 = some changed_operand_s7 := by rfl
def changed_operand_c7 : List UInt8 := [101, 97, 110, 95, 105, 115, 95, 115]
def changed_operand_r8 : List String := [] ++ changed_operand_r7
def changed_operand_s8 : State := ⟨.ident, [115, 95, 115, 105, 95, 110, 97, 101, 108, 99], changed_operand_r8⟩
theorem changed_operand_cut7 : feed (some changed_operand_s7) changed_operand_c7 = some changed_operand_s8 := by rfl
def changed_operand_c8 : List UInt8 := [99, 97, 108, 97, 114, 40, 111, 41]
def changed_operand_r9 : List String := [")", "o", "(", "clean_is_scalar"] ++ changed_operand_r8
def changed_operand_s9 : State := ⟨.normal, [], changed_operand_r9⟩
theorem changed_operand_cut8 : feed (some changed_operand_s8) changed_operand_c8 = some changed_operand_s9 := by rfl
def changed_operand_c9 : List UInt8 := [32, 38, 38, 10, 32, 32, 32, 32]
def changed_operand_r10 : List String := ["&&"] ++ changed_operand_r9
def changed_operand_s10 : State := ⟨.normal, [], changed_operand_r10⟩
theorem changed_operand_cut9 : feed (some changed_operand_s9) changed_operand_c9 = some changed_operand_s10 := by rfl
def changed_operand_c10 : List UInt8 := [32, 32, 32, 32, 97, 116, 111, 109]
def changed_operand_r11 : List String := [] ++ changed_operand_r10
def changed_operand_s11 : State := ⟨.ident, [109, 111, 116, 97], changed_operand_r11⟩
theorem changed_operand_cut10 : feed (some changed_operand_s10) changed_operand_c10 = some changed_operand_s11 := by rfl
def changed_operand_c11 : List UInt8 := [105, 99, 95, 108, 111, 97, 100, 95]
def changed_operand_r12 : List String := [] ++ changed_operand_r11
def changed_operand_s12 : State := ⟨.ident, [95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], changed_operand_r12⟩
theorem changed_operand_cut11 : feed (some changed_operand_s11) changed_operand_c11 = some changed_operand_s12 := by rfl
def changed_operand_c12 : List UInt8 := [101, 120, 112, 108, 105, 99, 105, 116]
def changed_operand_r13 : List String := [] ++ changed_operand_r12
def changed_operand_s13 : State := ⟨.ident, [116, 105, 99, 105, 108, 112, 120, 101, 95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], changed_operand_r13⟩
theorem changed_operand_cut12 : feed (some changed_operand_s12) changed_operand_c12 = some changed_operand_s13 := by rfl
def changed_operand_c13 : List UInt8 := [40, 38, 111, 45, 62, 104, 101, 97]
def changed_operand_r14 : List String := ["->", "o", "&", "(", "atomic_load_explicit"] ++ changed_operand_r13
def changed_operand_s14 : State := ⟨.ident, [97, 101, 104], changed_operand_r14⟩
theorem changed_operand_cut13 : feed (some changed_operand_s13) changed_operand_c13 = some changed_operand_s14 := by rfl
def changed_operand_c14 : List UInt8 := [100, 101, 114, 46, 114, 101, 102, 95]
def changed_operand_r15 : List String := [".", "header"] ++ changed_operand_r14
def changed_operand_s15 : State := ⟨.ident, [95, 102, 101, 114], changed_operand_r15⟩
theorem changed_operand_cut14 : feed (some changed_operand_s14) changed_operand_c14 = some changed_operand_s15 := by rfl
def changed_operand_c15 : List UInt8 := [99, 111, 117, 110, 116, 44, 32, 109]
def changed_operand_r16 : List String := [",", "ref_count"] ++ changed_operand_r15
def changed_operand_s16 : State := ⟨.ident, [109], changed_operand_r16⟩
theorem changed_operand_cut15 : feed (some changed_operand_s15) changed_operand_c15 = some changed_operand_s16 := by rfl
def changed_operand_c16 : List UInt8 := [101, 109, 111, 114, 121, 95, 111, 114]
def changed_operand_r17 : List String := [] ++ changed_operand_r16
def changed_operand_s17 : State := ⟨.ident, [114, 111, 95, 121, 114, 111, 109, 101, 109], changed_operand_r17⟩
theorem changed_operand_cut16 : feed (some changed_operand_s16) changed_operand_c16 = some changed_operand_s17 := by rfl
def changed_operand_c17 : List UInt8 := [100, 101, 114, 95, 114, 101, 108, 97]
def changed_operand_r18 : List String := [] ++ changed_operand_r17
def changed_operand_s18 : State := ⟨.ident, [97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_operand_r18⟩
theorem changed_operand_cut17 : feed (some changed_operand_s17) changed_operand_c17 = some changed_operand_s18 := by rfl
def changed_operand_c18 : List UInt8 := [120, 101, 100, 41, 32, 60, 32, 67]
def changed_operand_r19 : List String := ["<", ")", "memory_order_relaxed"] ++ changed_operand_r18
def changed_operand_s19 : State := ⟨.ident, [67], changed_operand_r19⟩
theorem changed_operand_cut18 : feed (some changed_operand_s18) changed_operand_c18 = some changed_operand_s19 := by rfl
def changed_operand_c19 : List UInt8 := [76, 69, 65, 78, 95, 82, 67, 95]
def changed_operand_r20 : List String := [] ++ changed_operand_r19
def changed_operand_s20 : State := ⟨.ident, [95, 67, 82, 95, 78, 65, 69, 76, 67], changed_operand_r20⟩
theorem changed_operand_cut19 : feed (some changed_operand_s19) changed_operand_c19 = some changed_operand_s20 := by rfl
def changed_operand_c20 : List UInt8 := [83, 84, 73, 67, 75, 89, 41, 32]
def changed_operand_r21 : List String := [")", "CLEAN_RC_STICKY"] ++ changed_operand_r20
def changed_operand_s21 : State := ⟨.normal, [], changed_operand_r21⟩
theorem changed_operand_cut20 : feed (some changed_operand_s20) changed_operand_c20 = some changed_operand_s21 := by rfl
def changed_operand_c21 : List UInt8 := [123, 10, 32, 32, 32, 32, 32, 32]
def changed_operand_r22 : List String := ["{"] ++ changed_operand_r21
def changed_operand_s22 : State := ⟨.normal, [], changed_operand_r22⟩
theorem changed_operand_cut21 : feed (some changed_operand_s21) changed_operand_c21 = some changed_operand_s22 := by rfl
def changed_operand_c22 : List UInt8 := [32, 32, 97, 116, 111, 109, 105, 99]
def changed_operand_r23 : List String := [] ++ changed_operand_r22
def changed_operand_s23 : State := ⟨.ident, [99, 105, 109, 111, 116, 97], changed_operand_r23⟩
theorem changed_operand_cut22 : feed (some changed_operand_s22) changed_operand_c22 = some changed_operand_s23 := by rfl
def changed_operand_c23 : List UInt8 := [95, 102, 101, 116, 99, 104, 95, 97]
def changed_operand_r24 : List String := [] ++ changed_operand_r23
def changed_operand_s24 : State := ⟨.ident, [97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], changed_operand_r24⟩
theorem changed_operand_cut23 : feed (some changed_operand_s23) changed_operand_c23 = some changed_operand_s24 := by rfl
def changed_operand_c24 : List UInt8 := [100, 100, 95, 101, 120, 112, 108, 105]
def changed_operand_r25 : List String := [] ++ changed_operand_r24
def changed_operand_s25 : State := ⟨.ident, [105, 108, 112, 120, 101, 95, 100, 100, 97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], changed_operand_r25⟩
theorem changed_operand_cut24 : feed (some changed_operand_s24) changed_operand_c24 = some changed_operand_s25 := by rfl
def changed_operand_c25 : List UInt8 := [99, 105, 116, 40, 38, 111, 116, 104]
def changed_operand_r26 : List String := ["&", "(", "atomic_fetch_add_explicit"] ++ changed_operand_r25
def changed_operand_s26 : State := ⟨.ident, [104, 116, 111], changed_operand_r26⟩
theorem changed_operand_cut25 : feed (some changed_operand_s25) changed_operand_c25 = some changed_operand_s26 := by rfl
def changed_operand_c26 : List UInt8 := [101, 114, 45, 62, 104, 101, 97, 100]
def changed_operand_r27 : List String := ["->", "other"] ++ changed_operand_r26
def changed_operand_s27 : State := ⟨.ident, [100, 97, 101, 104], changed_operand_r27⟩
theorem changed_operand_cut26 : feed (some changed_operand_s26) changed_operand_c26 = some changed_operand_s27 := by rfl
def changed_operand_c27 : List UInt8 := [101, 114, 46, 114, 101, 102, 95, 99]
def changed_operand_r28 : List String := [".", "header"] ++ changed_operand_r27
def changed_operand_s28 : State := ⟨.ident, [99, 95, 102, 101, 114], changed_operand_r28⟩
theorem changed_operand_cut27 : feed (some changed_operand_s27) changed_operand_c27 = some changed_operand_s28 := by rfl
def changed_operand_c28 : List UInt8 := [111, 117, 110, 116, 44, 32, 49, 44]
def changed_operand_r29 : List String := [",", "1", ",", "ref_count"] ++ changed_operand_r28
def changed_operand_s29 : State := ⟨.normal, [], changed_operand_r29⟩
theorem changed_operand_cut28 : feed (some changed_operand_s28) changed_operand_c28 = some changed_operand_s29 := by rfl
def changed_operand_c29 : List UInt8 := [32, 109, 101, 109, 111, 114, 121, 95]
def changed_operand_r30 : List String := [] ++ changed_operand_r29
def changed_operand_s30 : State := ⟨.ident, [95, 121, 114, 111, 109, 101, 109], changed_operand_r30⟩
theorem changed_operand_cut29 : feed (some changed_operand_s29) changed_operand_c29 = some changed_operand_s30 := by rfl
def changed_operand_c30 : List UInt8 := [111, 114, 100, 101, 114, 95, 114, 101]
def changed_operand_r31 : List String := [] ++ changed_operand_r30
def changed_operand_s31 : State := ⟨.ident, [101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_operand_r31⟩
theorem changed_operand_cut30 : feed (some changed_operand_s30) changed_operand_c30 = some changed_operand_s31 := by rfl
def changed_operand_c31 : List UInt8 := [108, 97, 120, 101, 100, 41, 59, 10]
def changed_operand_r32 : List String := [";", ")", "memory_order_relaxed"] ++ changed_operand_r31
def changed_operand_s32 : State := ⟨.normal, [], changed_operand_r32⟩
theorem changed_operand_cut31 : feed (some changed_operand_s31) changed_operand_c31 = some changed_operand_s32 := by rfl
def changed_operand_c32 : List UInt8 := [32, 32, 32, 32, 125, 10, 125]
def changed_operand_r33 : List String := ["}", "}"] ++ changed_operand_r32
def changed_operand_s33 : State := ⟨.normal, [], changed_operand_r33⟩
theorem changed_operand_cut32 : feed (some changed_operand_s32) changed_operand_c32 = some changed_operand_s33 := by rfl
def changed_operand_chunks : List (List UInt8) := [changed_operand_c0, changed_operand_c1, changed_operand_c2, changed_operand_c3, changed_operand_c4, changed_operand_c5, changed_operand_c6, changed_operand_c7, changed_operand_c8, changed_operand_c9, changed_operand_c10, changed_operand_c11, changed_operand_c12, changed_operand_c13, changed_operand_c14, changed_operand_c15, changed_operand_c16, changed_operand_c17, changed_operand_c18, changed_operand_c19, changed_operand_c20, changed_operand_c21, changed_operand_c22, changed_operand_c23, changed_operand_c24, changed_operand_c25, changed_operand_c26, changed_operand_c27, changed_operand_c28, changed_operand_c29, changed_operand_c30, changed_operand_c31, changed_operand_c32]
def changed_operand : List UInt8 := changed_operand_chunks.flatten
theorem changed_operand_feed : changed_operand_chunks.foldl feed (some initial) = some changed_operand_s33 := by
  change changed_operand_chunks.foldl feed (some changed_operand_s0) = _
  simp only [changed_operand_chunks, List.foldl_cons, List.foldl_nil]
  rw [changed_operand_cut0, changed_operand_cut1, changed_operand_cut2, changed_operand_cut3, changed_operand_cut4, changed_operand_cut5, changed_operand_cut6, changed_operand_cut7, changed_operand_cut8, changed_operand_cut9, changed_operand_cut10, changed_operand_cut11, changed_operand_cut12, changed_operand_cut13, changed_operand_cut14, changed_operand_cut15, changed_operand_cut16, changed_operand_cut17, changed_operand_cut18, changed_operand_cut19, changed_operand_cut20, changed_operand_cut21, changed_operand_cut22, changed_operand_cut23, changed_operand_cut24, changed_operand_cut25, changed_operand_cut26, changed_operand_cut27, changed_operand_cut28, changed_operand_cut29, changed_operand_cut30, changed_operand_cut31, changed_operand_cut32]
theorem changed_operand_refuses : CAtomicIncrementSyntax.check changed_operand proposal = false := by
  unfold CAtomicIncrementSyntax.check
  rw [changed_operand, ← chunks_exact, tokenizeChunks, changed_operand_feed]
  decide

def missing_rmw_r0 : List String := []
def missing_rmw_s0 : State := initial
def missing_rmw_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def missing_rmw_r1 : List String := ["static"] ++ missing_rmw_r0
def missing_rmw_s1 : State := ⟨.ident, [105], missing_rmw_r1⟩
theorem missing_rmw_cut0 : feed (some missing_rmw_s0) missing_rmw_c0 = some missing_rmw_s1 := by rfl
def missing_rmw_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def missing_rmw_r2 : List String := ["inline"] ++ missing_rmw_r1
def missing_rmw_s2 : State := ⟨.ident, [111, 118], missing_rmw_r2⟩
theorem missing_rmw_cut1 : feed (some missing_rmw_s1) missing_rmw_c1 = some missing_rmw_s2 := by rfl
def missing_rmw_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def missing_rmw_r3 : List String := ["void"] ++ missing_rmw_r2
def missing_rmw_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], missing_rmw_r3⟩
theorem missing_rmw_cut2 : feed (some missing_rmw_s2) missing_rmw_c2 = some missing_rmw_s3 := by rfl
def missing_rmw_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def missing_rmw_r4 : List String := ["(", "clean_inc"] ++ missing_rmw_r3
def missing_rmw_s4 : State := ⟨.ident, [101, 108, 99], missing_rmw_r4⟩
theorem missing_rmw_cut3 : feed (some missing_rmw_s3) missing_rmw_c3 = some missing_rmw_s4 := by rfl
def missing_rmw_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def missing_rmw_r5 : List String := ["*", "clean_obj"] ++ missing_rmw_r4
def missing_rmw_s5 : State := ⟨.normal, [], missing_rmw_r5⟩
theorem missing_rmw_cut4 : feed (some missing_rmw_s4) missing_rmw_c4 = some missing_rmw_s5 := by rfl
def missing_rmw_c5 : List UInt8 := [111, 41, 32, 123, 10, 32, 32, 32]
def missing_rmw_r6 : List String := ["{", ")", "o"] ++ missing_rmw_r5
def missing_rmw_s6 : State := ⟨.normal, [], missing_rmw_r6⟩
theorem missing_rmw_cut5 : feed (some missing_rmw_s5) missing_rmw_c5 = some missing_rmw_s6 := by rfl
def missing_rmw_c6 : List UInt8 := [32, 105, 102, 32, 40, 33, 99, 108]
def missing_rmw_r7 : List String := ["!", "(", "if"] ++ missing_rmw_r6
def missing_rmw_s7 : State := ⟨.ident, [108, 99], missing_rmw_r7⟩
theorem missing_rmw_cut6 : feed (some missing_rmw_s6) missing_rmw_c6 = some missing_rmw_s7 := by rfl
def missing_rmw_c7 : List UInt8 := [101, 97, 110, 95, 105, 115, 95, 115]
def missing_rmw_r8 : List String := [] ++ missing_rmw_r7
def missing_rmw_s8 : State := ⟨.ident, [115, 95, 115, 105, 95, 110, 97, 101, 108, 99], missing_rmw_r8⟩
theorem missing_rmw_cut7 : feed (some missing_rmw_s7) missing_rmw_c7 = some missing_rmw_s8 := by rfl
def missing_rmw_c8 : List UInt8 := [99, 97, 108, 97, 114, 40, 111, 41]
def missing_rmw_r9 : List String := [")", "o", "(", "clean_is_scalar"] ++ missing_rmw_r8
def missing_rmw_s9 : State := ⟨.normal, [], missing_rmw_r9⟩
theorem missing_rmw_cut8 : feed (some missing_rmw_s8) missing_rmw_c8 = some missing_rmw_s9 := by rfl
def missing_rmw_c9 : List UInt8 := [32, 38, 38, 10, 32, 32, 32, 32]
def missing_rmw_r10 : List String := ["&&"] ++ missing_rmw_r9
def missing_rmw_s10 : State := ⟨.normal, [], missing_rmw_r10⟩
theorem missing_rmw_cut9 : feed (some missing_rmw_s9) missing_rmw_c9 = some missing_rmw_s10 := by rfl
def missing_rmw_c10 : List UInt8 := [32, 32, 32, 32, 97, 116, 111, 109]
def missing_rmw_r11 : List String := [] ++ missing_rmw_r10
def missing_rmw_s11 : State := ⟨.ident, [109, 111, 116, 97], missing_rmw_r11⟩
theorem missing_rmw_cut10 : feed (some missing_rmw_s10) missing_rmw_c10 = some missing_rmw_s11 := by rfl
def missing_rmw_c11 : List UInt8 := [105, 99, 95, 108, 111, 97, 100, 95]
def missing_rmw_r12 : List String := [] ++ missing_rmw_r11
def missing_rmw_s12 : State := ⟨.ident, [95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], missing_rmw_r12⟩
theorem missing_rmw_cut11 : feed (some missing_rmw_s11) missing_rmw_c11 = some missing_rmw_s12 := by rfl
def missing_rmw_c12 : List UInt8 := [101, 120, 112, 108, 105, 99, 105, 116]
def missing_rmw_r13 : List String := [] ++ missing_rmw_r12
def missing_rmw_s13 : State := ⟨.ident, [116, 105, 99, 105, 108, 112, 120, 101, 95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], missing_rmw_r13⟩
theorem missing_rmw_cut12 : feed (some missing_rmw_s12) missing_rmw_c12 = some missing_rmw_s13 := by rfl
def missing_rmw_c13 : List UInt8 := [40, 38, 111, 45, 62, 104, 101, 97]
def missing_rmw_r14 : List String := ["->", "o", "&", "(", "atomic_load_explicit"] ++ missing_rmw_r13
def missing_rmw_s14 : State := ⟨.ident, [97, 101, 104], missing_rmw_r14⟩
theorem missing_rmw_cut13 : feed (some missing_rmw_s13) missing_rmw_c13 = some missing_rmw_s14 := by rfl
def missing_rmw_c14 : List UInt8 := [100, 101, 114, 46, 114, 101, 102, 95]
def missing_rmw_r15 : List String := [".", "header"] ++ missing_rmw_r14
def missing_rmw_s15 : State := ⟨.ident, [95, 102, 101, 114], missing_rmw_r15⟩
theorem missing_rmw_cut14 : feed (some missing_rmw_s14) missing_rmw_c14 = some missing_rmw_s15 := by rfl
def missing_rmw_c15 : List UInt8 := [99, 111, 117, 110, 116, 44, 32, 109]
def missing_rmw_r16 : List String := [",", "ref_count"] ++ missing_rmw_r15
def missing_rmw_s16 : State := ⟨.ident, [109], missing_rmw_r16⟩
theorem missing_rmw_cut15 : feed (some missing_rmw_s15) missing_rmw_c15 = some missing_rmw_s16 := by rfl
def missing_rmw_c16 : List UInt8 := [101, 109, 111, 114, 121, 95, 111, 114]
def missing_rmw_r17 : List String := [] ++ missing_rmw_r16
def missing_rmw_s17 : State := ⟨.ident, [114, 111, 95, 121, 114, 111, 109, 101, 109], missing_rmw_r17⟩
theorem missing_rmw_cut16 : feed (some missing_rmw_s16) missing_rmw_c16 = some missing_rmw_s17 := by rfl
def missing_rmw_c17 : List UInt8 := [100, 101, 114, 95, 114, 101, 108, 97]
def missing_rmw_r18 : List String := [] ++ missing_rmw_r17
def missing_rmw_s18 : State := ⟨.ident, [97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], missing_rmw_r18⟩
theorem missing_rmw_cut17 : feed (some missing_rmw_s17) missing_rmw_c17 = some missing_rmw_s18 := by rfl
def missing_rmw_c18 : List UInt8 := [120, 101, 100, 41, 32, 60, 32, 67]
def missing_rmw_r19 : List String := ["<", ")", "memory_order_relaxed"] ++ missing_rmw_r18
def missing_rmw_s19 : State := ⟨.ident, [67], missing_rmw_r19⟩
theorem missing_rmw_cut18 : feed (some missing_rmw_s18) missing_rmw_c18 = some missing_rmw_s19 := by rfl
def missing_rmw_c19 : List UInt8 := [76, 69, 65, 78, 95, 82, 67, 95]
def missing_rmw_r20 : List String := [] ++ missing_rmw_r19
def missing_rmw_s20 : State := ⟨.ident, [95, 67, 82, 95, 78, 65, 69, 76, 67], missing_rmw_r20⟩
theorem missing_rmw_cut19 : feed (some missing_rmw_s19) missing_rmw_c19 = some missing_rmw_s20 := by rfl
def missing_rmw_c20 : List UInt8 := [83, 84, 73, 67, 75, 89, 41, 32]
def missing_rmw_r21 : List String := [")", "CLEAN_RC_STICKY"] ++ missing_rmw_r20
def missing_rmw_s21 : State := ⟨.normal, [], missing_rmw_r21⟩
theorem missing_rmw_cut20 : feed (some missing_rmw_s20) missing_rmw_c20 = some missing_rmw_s21 := by rfl
def missing_rmw_c21 : List UInt8 := [123, 10, 32, 32, 32, 32, 125, 10]
def missing_rmw_r22 : List String := ["}", "{"] ++ missing_rmw_r21
def missing_rmw_s22 : State := ⟨.normal, [], missing_rmw_r22⟩
theorem missing_rmw_cut21 : feed (some missing_rmw_s21) missing_rmw_c21 = some missing_rmw_s22 := by rfl
def missing_rmw_c22 : List UInt8 := [125]
def missing_rmw_r23 : List String := ["}"] ++ missing_rmw_r22
def missing_rmw_s23 : State := ⟨.normal, [], missing_rmw_r23⟩
theorem missing_rmw_cut22 : feed (some missing_rmw_s22) missing_rmw_c22 = some missing_rmw_s23 := by rfl
def missing_rmw_chunks : List (List UInt8) := [missing_rmw_c0, missing_rmw_c1, missing_rmw_c2, missing_rmw_c3, missing_rmw_c4, missing_rmw_c5, missing_rmw_c6, missing_rmw_c7, missing_rmw_c8, missing_rmw_c9, missing_rmw_c10, missing_rmw_c11, missing_rmw_c12, missing_rmw_c13, missing_rmw_c14, missing_rmw_c15, missing_rmw_c16, missing_rmw_c17, missing_rmw_c18, missing_rmw_c19, missing_rmw_c20, missing_rmw_c21, missing_rmw_c22]
def missing_rmw : List UInt8 := missing_rmw_chunks.flatten
theorem missing_rmw_feed : missing_rmw_chunks.foldl feed (some initial) = some missing_rmw_s23 := by
  change missing_rmw_chunks.foldl feed (some missing_rmw_s0) = _
  simp only [missing_rmw_chunks, List.foldl_cons, List.foldl_nil]
  rw [missing_rmw_cut0, missing_rmw_cut1, missing_rmw_cut2, missing_rmw_cut3, missing_rmw_cut4, missing_rmw_cut5, missing_rmw_cut6, missing_rmw_cut7, missing_rmw_cut8, missing_rmw_cut9, missing_rmw_cut10, missing_rmw_cut11, missing_rmw_cut12, missing_rmw_cut13, missing_rmw_cut14, missing_rmw_cut15, missing_rmw_cut16, missing_rmw_cut17, missing_rmw_cut18, missing_rmw_cut19, missing_rmw_cut20, missing_rmw_cut21, missing_rmw_cut22]
theorem missing_rmw_refuses : CAtomicIncrementSyntax.check missing_rmw proposal = false := by
  unfold CAtomicIncrementSyntax.check
  rw [missing_rmw, ← chunks_exact, tokenizeChunks, missing_rmw_feed]
  decide

def changed_addend_r0 : List String := []
def changed_addend_s0 : State := initial
def changed_addend_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def changed_addend_r1 : List String := ["static"] ++ changed_addend_r0
def changed_addend_s1 : State := ⟨.ident, [105], changed_addend_r1⟩
theorem changed_addend_cut0 : feed (some changed_addend_s0) changed_addend_c0 = some changed_addend_s1 := by rfl
def changed_addend_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def changed_addend_r2 : List String := ["inline"] ++ changed_addend_r1
def changed_addend_s2 : State := ⟨.ident, [111, 118], changed_addend_r2⟩
theorem changed_addend_cut1 : feed (some changed_addend_s1) changed_addend_c1 = some changed_addend_s2 := by rfl
def changed_addend_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def changed_addend_r3 : List String := ["void"] ++ changed_addend_r2
def changed_addend_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], changed_addend_r3⟩
theorem changed_addend_cut2 : feed (some changed_addend_s2) changed_addend_c2 = some changed_addend_s3 := by rfl
def changed_addend_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def changed_addend_r4 : List String := ["(", "clean_inc"] ++ changed_addend_r3
def changed_addend_s4 : State := ⟨.ident, [101, 108, 99], changed_addend_r4⟩
theorem changed_addend_cut3 : feed (some changed_addend_s3) changed_addend_c3 = some changed_addend_s4 := by rfl
def changed_addend_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def changed_addend_r5 : List String := ["*", "clean_obj"] ++ changed_addend_r4
def changed_addend_s5 : State := ⟨.normal, [], changed_addend_r5⟩
theorem changed_addend_cut4 : feed (some changed_addend_s4) changed_addend_c4 = some changed_addend_s5 := by rfl
def changed_addend_c5 : List UInt8 := [111, 41, 32, 123, 10, 32, 32, 32]
def changed_addend_r6 : List String := ["{", ")", "o"] ++ changed_addend_r5
def changed_addend_s6 : State := ⟨.normal, [], changed_addend_r6⟩
theorem changed_addend_cut5 : feed (some changed_addend_s5) changed_addend_c5 = some changed_addend_s6 := by rfl
def changed_addend_c6 : List UInt8 := [32, 105, 102, 32, 40, 33, 99, 108]
def changed_addend_r7 : List String := ["!", "(", "if"] ++ changed_addend_r6
def changed_addend_s7 : State := ⟨.ident, [108, 99], changed_addend_r7⟩
theorem changed_addend_cut6 : feed (some changed_addend_s6) changed_addend_c6 = some changed_addend_s7 := by rfl
def changed_addend_c7 : List UInt8 := [101, 97, 110, 95, 105, 115, 95, 115]
def changed_addend_r8 : List String := [] ++ changed_addend_r7
def changed_addend_s8 : State := ⟨.ident, [115, 95, 115, 105, 95, 110, 97, 101, 108, 99], changed_addend_r8⟩
theorem changed_addend_cut7 : feed (some changed_addend_s7) changed_addend_c7 = some changed_addend_s8 := by rfl
def changed_addend_c8 : List UInt8 := [99, 97, 108, 97, 114, 40, 111, 41]
def changed_addend_r9 : List String := [")", "o", "(", "clean_is_scalar"] ++ changed_addend_r8
def changed_addend_s9 : State := ⟨.normal, [], changed_addend_r9⟩
theorem changed_addend_cut8 : feed (some changed_addend_s8) changed_addend_c8 = some changed_addend_s9 := by rfl
def changed_addend_c9 : List UInt8 := [32, 38, 38, 10, 32, 32, 32, 32]
def changed_addend_r10 : List String := ["&&"] ++ changed_addend_r9
def changed_addend_s10 : State := ⟨.normal, [], changed_addend_r10⟩
theorem changed_addend_cut9 : feed (some changed_addend_s9) changed_addend_c9 = some changed_addend_s10 := by rfl
def changed_addend_c10 : List UInt8 := [32, 32, 32, 32, 97, 116, 111, 109]
def changed_addend_r11 : List String := [] ++ changed_addend_r10
def changed_addend_s11 : State := ⟨.ident, [109, 111, 116, 97], changed_addend_r11⟩
theorem changed_addend_cut10 : feed (some changed_addend_s10) changed_addend_c10 = some changed_addend_s11 := by rfl
def changed_addend_c11 : List UInt8 := [105, 99, 95, 108, 111, 97, 100, 95]
def changed_addend_r12 : List String := [] ++ changed_addend_r11
def changed_addend_s12 : State := ⟨.ident, [95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], changed_addend_r12⟩
theorem changed_addend_cut11 : feed (some changed_addend_s11) changed_addend_c11 = some changed_addend_s12 := by rfl
def changed_addend_c12 : List UInt8 := [101, 120, 112, 108, 105, 99, 105, 116]
def changed_addend_r13 : List String := [] ++ changed_addend_r12
def changed_addend_s13 : State := ⟨.ident, [116, 105, 99, 105, 108, 112, 120, 101, 95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], changed_addend_r13⟩
theorem changed_addend_cut12 : feed (some changed_addend_s12) changed_addend_c12 = some changed_addend_s13 := by rfl
def changed_addend_c13 : List UInt8 := [40, 38, 111, 45, 62, 104, 101, 97]
def changed_addend_r14 : List String := ["->", "o", "&", "(", "atomic_load_explicit"] ++ changed_addend_r13
def changed_addend_s14 : State := ⟨.ident, [97, 101, 104], changed_addend_r14⟩
theorem changed_addend_cut13 : feed (some changed_addend_s13) changed_addend_c13 = some changed_addend_s14 := by rfl
def changed_addend_c14 : List UInt8 := [100, 101, 114, 46, 114, 101, 102, 95]
def changed_addend_r15 : List String := [".", "header"] ++ changed_addend_r14
def changed_addend_s15 : State := ⟨.ident, [95, 102, 101, 114], changed_addend_r15⟩
theorem changed_addend_cut14 : feed (some changed_addend_s14) changed_addend_c14 = some changed_addend_s15 := by rfl
def changed_addend_c15 : List UInt8 := [99, 111, 117, 110, 116, 44, 32, 109]
def changed_addend_r16 : List String := [",", "ref_count"] ++ changed_addend_r15
def changed_addend_s16 : State := ⟨.ident, [109], changed_addend_r16⟩
theorem changed_addend_cut15 : feed (some changed_addend_s15) changed_addend_c15 = some changed_addend_s16 := by rfl
def changed_addend_c16 : List UInt8 := [101, 109, 111, 114, 121, 95, 111, 114]
def changed_addend_r17 : List String := [] ++ changed_addend_r16
def changed_addend_s17 : State := ⟨.ident, [114, 111, 95, 121, 114, 111, 109, 101, 109], changed_addend_r17⟩
theorem changed_addend_cut16 : feed (some changed_addend_s16) changed_addend_c16 = some changed_addend_s17 := by rfl
def changed_addend_c17 : List UInt8 := [100, 101, 114, 95, 114, 101, 108, 97]
def changed_addend_r18 : List String := [] ++ changed_addend_r17
def changed_addend_s18 : State := ⟨.ident, [97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_addend_r18⟩
theorem changed_addend_cut17 : feed (some changed_addend_s17) changed_addend_c17 = some changed_addend_s18 := by rfl
def changed_addend_c18 : List UInt8 := [120, 101, 100, 41, 32, 60, 32, 67]
def changed_addend_r19 : List String := ["<", ")", "memory_order_relaxed"] ++ changed_addend_r18
def changed_addend_s19 : State := ⟨.ident, [67], changed_addend_r19⟩
theorem changed_addend_cut18 : feed (some changed_addend_s18) changed_addend_c18 = some changed_addend_s19 := by rfl
def changed_addend_c19 : List UInt8 := [76, 69, 65, 78, 95, 82, 67, 95]
def changed_addend_r20 : List String := [] ++ changed_addend_r19
def changed_addend_s20 : State := ⟨.ident, [95, 67, 82, 95, 78, 65, 69, 76, 67], changed_addend_r20⟩
theorem changed_addend_cut19 : feed (some changed_addend_s19) changed_addend_c19 = some changed_addend_s20 := by rfl
def changed_addend_c20 : List UInt8 := [83, 84, 73, 67, 75, 89, 41, 32]
def changed_addend_r21 : List String := [")", "CLEAN_RC_STICKY"] ++ changed_addend_r20
def changed_addend_s21 : State := ⟨.normal, [], changed_addend_r21⟩
theorem changed_addend_cut20 : feed (some changed_addend_s20) changed_addend_c20 = some changed_addend_s21 := by rfl
def changed_addend_c21 : List UInt8 := [123, 10, 32, 32, 32, 32, 32, 32]
def changed_addend_r22 : List String := ["{"] ++ changed_addend_r21
def changed_addend_s22 : State := ⟨.normal, [], changed_addend_r22⟩
theorem changed_addend_cut21 : feed (some changed_addend_s21) changed_addend_c21 = some changed_addend_s22 := by rfl
def changed_addend_c22 : List UInt8 := [32, 32, 97, 116, 111, 109, 105, 99]
def changed_addend_r23 : List String := [] ++ changed_addend_r22
def changed_addend_s23 : State := ⟨.ident, [99, 105, 109, 111, 116, 97], changed_addend_r23⟩
theorem changed_addend_cut22 : feed (some changed_addend_s22) changed_addend_c22 = some changed_addend_s23 := by rfl
def changed_addend_c23 : List UInt8 := [95, 102, 101, 116, 99, 104, 95, 97]
def changed_addend_r24 : List String := [] ++ changed_addend_r23
def changed_addend_s24 : State := ⟨.ident, [97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], changed_addend_r24⟩
theorem changed_addend_cut23 : feed (some changed_addend_s23) changed_addend_c23 = some changed_addend_s24 := by rfl
def changed_addend_c24 : List UInt8 := [100, 100, 95, 101, 120, 112, 108, 105]
def changed_addend_r25 : List String := [] ++ changed_addend_r24
def changed_addend_s25 : State := ⟨.ident, [105, 108, 112, 120, 101, 95, 100, 100, 97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], changed_addend_r25⟩
theorem changed_addend_cut24 : feed (some changed_addend_s24) changed_addend_c24 = some changed_addend_s25 := by rfl
def changed_addend_c25 : List UInt8 := [99, 105, 116, 40, 38, 111, 45, 62]
def changed_addend_r26 : List String := ["->", "o", "&", "(", "atomic_fetch_add_explicit"] ++ changed_addend_r25
def changed_addend_s26 : State := ⟨.normal, [], changed_addend_r26⟩
theorem changed_addend_cut25 : feed (some changed_addend_s25) changed_addend_c25 = some changed_addend_s26 := by rfl
def changed_addend_c26 : List UInt8 := [104, 101, 97, 100, 101, 114, 46, 114]
def changed_addend_r27 : List String := [".", "header"] ++ changed_addend_r26
def changed_addend_s27 : State := ⟨.ident, [114], changed_addend_r27⟩
theorem changed_addend_cut26 : feed (some changed_addend_s26) changed_addend_c26 = some changed_addend_s27 := by rfl
def changed_addend_c27 : List UInt8 := [101, 102, 95, 99, 111, 117, 110, 116]
def changed_addend_r28 : List String := [] ++ changed_addend_r27
def changed_addend_s28 : State := ⟨.ident, [116, 110, 117, 111, 99, 95, 102, 101, 114], changed_addend_r28⟩
theorem changed_addend_cut27 : feed (some changed_addend_s27) changed_addend_c27 = some changed_addend_s28 := by rfl
def changed_addend_c28 : List UInt8 := [44, 32, 50, 44, 32, 109, 101, 109]
def changed_addend_r29 : List String := [",", "2", ",", "ref_count"] ++ changed_addend_r28
def changed_addend_s29 : State := ⟨.ident, [109, 101, 109], changed_addend_r29⟩
theorem changed_addend_cut28 : feed (some changed_addend_s28) changed_addend_c28 = some changed_addend_s29 := by rfl
def changed_addend_c29 : List UInt8 := [111, 114, 121, 95, 111, 114, 100, 101]
def changed_addend_r30 : List String := [] ++ changed_addend_r29
def changed_addend_s30 : State := ⟨.ident, [101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_addend_r30⟩
theorem changed_addend_cut29 : feed (some changed_addend_s29) changed_addend_c29 = some changed_addend_s30 := by rfl
def changed_addend_c30 : List UInt8 := [114, 95, 114, 101, 108, 97, 120, 101]
def changed_addend_r31 : List String := [] ++ changed_addend_r30
def changed_addend_s31 : State := ⟨.ident, [101, 120, 97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], changed_addend_r31⟩
theorem changed_addend_cut30 : feed (some changed_addend_s30) changed_addend_c30 = some changed_addend_s31 := by rfl
def changed_addend_c31 : List UInt8 := [100, 41, 59, 10, 32, 32, 32, 32]
def changed_addend_r32 : List String := [";", ")", "memory_order_relaxed"] ++ changed_addend_r31
def changed_addend_s32 : State := ⟨.normal, [], changed_addend_r32⟩
theorem changed_addend_cut31 : feed (some changed_addend_s31) changed_addend_c31 = some changed_addend_s32 := by rfl
def changed_addend_c32 : List UInt8 := [125, 10, 125]
def changed_addend_r33 : List String := ["}", "}"] ++ changed_addend_r32
def changed_addend_s33 : State := ⟨.normal, [], changed_addend_r33⟩
theorem changed_addend_cut32 : feed (some changed_addend_s32) changed_addend_c32 = some changed_addend_s33 := by rfl
def changed_addend_chunks : List (List UInt8) := [changed_addend_c0, changed_addend_c1, changed_addend_c2, changed_addend_c3, changed_addend_c4, changed_addend_c5, changed_addend_c6, changed_addend_c7, changed_addend_c8, changed_addend_c9, changed_addend_c10, changed_addend_c11, changed_addend_c12, changed_addend_c13, changed_addend_c14, changed_addend_c15, changed_addend_c16, changed_addend_c17, changed_addend_c18, changed_addend_c19, changed_addend_c20, changed_addend_c21, changed_addend_c22, changed_addend_c23, changed_addend_c24, changed_addend_c25, changed_addend_c26, changed_addend_c27, changed_addend_c28, changed_addend_c29, changed_addend_c30, changed_addend_c31, changed_addend_c32]
def changed_addend : List UInt8 := changed_addend_chunks.flatten
theorem changed_addend_feed : changed_addend_chunks.foldl feed (some initial) = some changed_addend_s33 := by
  change changed_addend_chunks.foldl feed (some changed_addend_s0) = _
  simp only [changed_addend_chunks, List.foldl_cons, List.foldl_nil]
  rw [changed_addend_cut0, changed_addend_cut1, changed_addend_cut2, changed_addend_cut3, changed_addend_cut4, changed_addend_cut5, changed_addend_cut6, changed_addend_cut7, changed_addend_cut8, changed_addend_cut9, changed_addend_cut10, changed_addend_cut11, changed_addend_cut12, changed_addend_cut13, changed_addend_cut14, changed_addend_cut15, changed_addend_cut16, changed_addend_cut17, changed_addend_cut18, changed_addend_cut19, changed_addend_cut20, changed_addend_cut21, changed_addend_cut22, changed_addend_cut23, changed_addend_cut24, changed_addend_cut25, changed_addend_cut26, changed_addend_cut27, changed_addend_cut28, changed_addend_cut29, changed_addend_cut30, changed_addend_cut31, changed_addend_cut32]
theorem changed_addend_refuses : CAtomicIncrementSyntax.check changed_addend proposal = false := by
  unfold CAtomicIncrementSyntax.check
  rw [changed_addend, ← chunks_exact, tokenizeChunks, changed_addend_feed]
  decide

def appended_statement_r0 : List String := []
def appended_statement_s0 : State := initial
def appended_statement_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def appended_statement_r1 : List String := ["static"] ++ appended_statement_r0
def appended_statement_s1 : State := ⟨.ident, [105], appended_statement_r1⟩
theorem appended_statement_cut0 : feed (some appended_statement_s0) appended_statement_c0 = some appended_statement_s1 := by rfl
def appended_statement_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def appended_statement_r2 : List String := ["inline"] ++ appended_statement_r1
def appended_statement_s2 : State := ⟨.ident, [111, 118], appended_statement_r2⟩
theorem appended_statement_cut1 : feed (some appended_statement_s1) appended_statement_c1 = some appended_statement_s2 := by rfl
def appended_statement_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def appended_statement_r3 : List String := ["void"] ++ appended_statement_r2
def appended_statement_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], appended_statement_r3⟩
theorem appended_statement_cut2 : feed (some appended_statement_s2) appended_statement_c2 = some appended_statement_s3 := by rfl
def appended_statement_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def appended_statement_r4 : List String := ["(", "clean_inc"] ++ appended_statement_r3
def appended_statement_s4 : State := ⟨.ident, [101, 108, 99], appended_statement_r4⟩
theorem appended_statement_cut3 : feed (some appended_statement_s3) appended_statement_c3 = some appended_statement_s4 := by rfl
def appended_statement_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def appended_statement_r5 : List String := ["*", "clean_obj"] ++ appended_statement_r4
def appended_statement_s5 : State := ⟨.normal, [], appended_statement_r5⟩
theorem appended_statement_cut4 : feed (some appended_statement_s4) appended_statement_c4 = some appended_statement_s5 := by rfl
def appended_statement_c5 : List UInt8 := [111, 41, 32, 123, 10, 32, 32, 32]
def appended_statement_r6 : List String := ["{", ")", "o"] ++ appended_statement_r5
def appended_statement_s6 : State := ⟨.normal, [], appended_statement_r6⟩
theorem appended_statement_cut5 : feed (some appended_statement_s5) appended_statement_c5 = some appended_statement_s6 := by rfl
def appended_statement_c6 : List UInt8 := [32, 105, 102, 32, 40, 33, 99, 108]
def appended_statement_r7 : List String := ["!", "(", "if"] ++ appended_statement_r6
def appended_statement_s7 : State := ⟨.ident, [108, 99], appended_statement_r7⟩
theorem appended_statement_cut6 : feed (some appended_statement_s6) appended_statement_c6 = some appended_statement_s7 := by rfl
def appended_statement_c7 : List UInt8 := [101, 97, 110, 95, 105, 115, 95, 115]
def appended_statement_r8 : List String := [] ++ appended_statement_r7
def appended_statement_s8 : State := ⟨.ident, [115, 95, 115, 105, 95, 110, 97, 101, 108, 99], appended_statement_r8⟩
theorem appended_statement_cut7 : feed (some appended_statement_s7) appended_statement_c7 = some appended_statement_s8 := by rfl
def appended_statement_c8 : List UInt8 := [99, 97, 108, 97, 114, 40, 111, 41]
def appended_statement_r9 : List String := [")", "o", "(", "clean_is_scalar"] ++ appended_statement_r8
def appended_statement_s9 : State := ⟨.normal, [], appended_statement_r9⟩
theorem appended_statement_cut8 : feed (some appended_statement_s8) appended_statement_c8 = some appended_statement_s9 := by rfl
def appended_statement_c9 : List UInt8 := [32, 38, 38, 10, 32, 32, 32, 32]
def appended_statement_r10 : List String := ["&&"] ++ appended_statement_r9
def appended_statement_s10 : State := ⟨.normal, [], appended_statement_r10⟩
theorem appended_statement_cut9 : feed (some appended_statement_s9) appended_statement_c9 = some appended_statement_s10 := by rfl
def appended_statement_c10 : List UInt8 := [32, 32, 32, 32, 97, 116, 111, 109]
def appended_statement_r11 : List String := [] ++ appended_statement_r10
def appended_statement_s11 : State := ⟨.ident, [109, 111, 116, 97], appended_statement_r11⟩
theorem appended_statement_cut10 : feed (some appended_statement_s10) appended_statement_c10 = some appended_statement_s11 := by rfl
def appended_statement_c11 : List UInt8 := [105, 99, 95, 108, 111, 97, 100, 95]
def appended_statement_r12 : List String := [] ++ appended_statement_r11
def appended_statement_s12 : State := ⟨.ident, [95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], appended_statement_r12⟩
theorem appended_statement_cut11 : feed (some appended_statement_s11) appended_statement_c11 = some appended_statement_s12 := by rfl
def appended_statement_c12 : List UInt8 := [101, 120, 112, 108, 105, 99, 105, 116]
def appended_statement_r13 : List String := [] ++ appended_statement_r12
def appended_statement_s13 : State := ⟨.ident, [116, 105, 99, 105, 108, 112, 120, 101, 95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], appended_statement_r13⟩
theorem appended_statement_cut12 : feed (some appended_statement_s12) appended_statement_c12 = some appended_statement_s13 := by rfl
def appended_statement_c13 : List UInt8 := [40, 38, 111, 45, 62, 104, 101, 97]
def appended_statement_r14 : List String := ["->", "o", "&", "(", "atomic_load_explicit"] ++ appended_statement_r13
def appended_statement_s14 : State := ⟨.ident, [97, 101, 104], appended_statement_r14⟩
theorem appended_statement_cut13 : feed (some appended_statement_s13) appended_statement_c13 = some appended_statement_s14 := by rfl
def appended_statement_c14 : List UInt8 := [100, 101, 114, 46, 114, 101, 102, 95]
def appended_statement_r15 : List String := [".", "header"] ++ appended_statement_r14
def appended_statement_s15 : State := ⟨.ident, [95, 102, 101, 114], appended_statement_r15⟩
theorem appended_statement_cut14 : feed (some appended_statement_s14) appended_statement_c14 = some appended_statement_s15 := by rfl
def appended_statement_c15 : List UInt8 := [99, 111, 117, 110, 116, 44, 32, 109]
def appended_statement_r16 : List String := [",", "ref_count"] ++ appended_statement_r15
def appended_statement_s16 : State := ⟨.ident, [109], appended_statement_r16⟩
theorem appended_statement_cut15 : feed (some appended_statement_s15) appended_statement_c15 = some appended_statement_s16 := by rfl
def appended_statement_c16 : List UInt8 := [101, 109, 111, 114, 121, 95, 111, 114]
def appended_statement_r17 : List String := [] ++ appended_statement_r16
def appended_statement_s17 : State := ⟨.ident, [114, 111, 95, 121, 114, 111, 109, 101, 109], appended_statement_r17⟩
theorem appended_statement_cut16 : feed (some appended_statement_s16) appended_statement_c16 = some appended_statement_s17 := by rfl
def appended_statement_c17 : List UInt8 := [100, 101, 114, 95, 114, 101, 108, 97]
def appended_statement_r18 : List String := [] ++ appended_statement_r17
def appended_statement_s18 : State := ⟨.ident, [97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], appended_statement_r18⟩
theorem appended_statement_cut17 : feed (some appended_statement_s17) appended_statement_c17 = some appended_statement_s18 := by rfl
def appended_statement_c18 : List UInt8 := [120, 101, 100, 41, 32, 60, 32, 67]
def appended_statement_r19 : List String := ["<", ")", "memory_order_relaxed"] ++ appended_statement_r18
def appended_statement_s19 : State := ⟨.ident, [67], appended_statement_r19⟩
theorem appended_statement_cut18 : feed (some appended_statement_s18) appended_statement_c18 = some appended_statement_s19 := by rfl
def appended_statement_c19 : List UInt8 := [76, 69, 65, 78, 95, 82, 67, 95]
def appended_statement_r20 : List String := [] ++ appended_statement_r19
def appended_statement_s20 : State := ⟨.ident, [95, 67, 82, 95, 78, 65, 69, 76, 67], appended_statement_r20⟩
theorem appended_statement_cut19 : feed (some appended_statement_s19) appended_statement_c19 = some appended_statement_s20 := by rfl
def appended_statement_c20 : List UInt8 := [83, 84, 73, 67, 75, 89, 41, 32]
def appended_statement_r21 : List String := [")", "CLEAN_RC_STICKY"] ++ appended_statement_r20
def appended_statement_s21 : State := ⟨.normal, [], appended_statement_r21⟩
theorem appended_statement_cut20 : feed (some appended_statement_s20) appended_statement_c20 = some appended_statement_s21 := by rfl
def appended_statement_c21 : List UInt8 := [123, 10, 32, 32, 32, 32, 32, 32]
def appended_statement_r22 : List String := ["{"] ++ appended_statement_r21
def appended_statement_s22 : State := ⟨.normal, [], appended_statement_r22⟩
theorem appended_statement_cut21 : feed (some appended_statement_s21) appended_statement_c21 = some appended_statement_s22 := by rfl
def appended_statement_c22 : List UInt8 := [32, 32, 97, 116, 111, 109, 105, 99]
def appended_statement_r23 : List String := [] ++ appended_statement_r22
def appended_statement_s23 : State := ⟨.ident, [99, 105, 109, 111, 116, 97], appended_statement_r23⟩
theorem appended_statement_cut22 : feed (some appended_statement_s22) appended_statement_c22 = some appended_statement_s23 := by rfl
def appended_statement_c23 : List UInt8 := [95, 102, 101, 116, 99, 104, 95, 97]
def appended_statement_r24 : List String := [] ++ appended_statement_r23
def appended_statement_s24 : State := ⟨.ident, [97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], appended_statement_r24⟩
theorem appended_statement_cut23 : feed (some appended_statement_s23) appended_statement_c23 = some appended_statement_s24 := by rfl
def appended_statement_c24 : List UInt8 := [100, 100, 95, 101, 120, 112, 108, 105]
def appended_statement_r25 : List String := [] ++ appended_statement_r24
def appended_statement_s25 : State := ⟨.ident, [105, 108, 112, 120, 101, 95, 100, 100, 97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], appended_statement_r25⟩
theorem appended_statement_cut24 : feed (some appended_statement_s24) appended_statement_c24 = some appended_statement_s25 := by rfl
def appended_statement_c25 : List UInt8 := [99, 105, 116, 40, 38, 111, 45, 62]
def appended_statement_r26 : List String := ["->", "o", "&", "(", "atomic_fetch_add_explicit"] ++ appended_statement_r25
def appended_statement_s26 : State := ⟨.normal, [], appended_statement_r26⟩
theorem appended_statement_cut25 : feed (some appended_statement_s25) appended_statement_c25 = some appended_statement_s26 := by rfl
def appended_statement_c26 : List UInt8 := [104, 101, 97, 100, 101, 114, 46, 114]
def appended_statement_r27 : List String := [".", "header"] ++ appended_statement_r26
def appended_statement_s27 : State := ⟨.ident, [114], appended_statement_r27⟩
theorem appended_statement_cut26 : feed (some appended_statement_s26) appended_statement_c26 = some appended_statement_s27 := by rfl
def appended_statement_c27 : List UInt8 := [101, 102, 95, 99, 111, 117, 110, 116]
def appended_statement_r28 : List String := [] ++ appended_statement_r27
def appended_statement_s28 : State := ⟨.ident, [116, 110, 117, 111, 99, 95, 102, 101, 114], appended_statement_r28⟩
theorem appended_statement_cut27 : feed (some appended_statement_s27) appended_statement_c27 = some appended_statement_s28 := by rfl
def appended_statement_c28 : List UInt8 := [44, 32, 49, 44, 32, 109, 101, 109]
def appended_statement_r29 : List String := [",", "1", ",", "ref_count"] ++ appended_statement_r28
def appended_statement_s29 : State := ⟨.ident, [109, 101, 109], appended_statement_r29⟩
theorem appended_statement_cut28 : feed (some appended_statement_s28) appended_statement_c28 = some appended_statement_s29 := by rfl
def appended_statement_c29 : List UInt8 := [111, 114, 121, 95, 111, 114, 100, 101]
def appended_statement_r30 : List String := [] ++ appended_statement_r29
def appended_statement_s30 : State := ⟨.ident, [101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], appended_statement_r30⟩
theorem appended_statement_cut29 : feed (some appended_statement_s29) appended_statement_c29 = some appended_statement_s30 := by rfl
def appended_statement_c30 : List UInt8 := [114, 95, 114, 101, 108, 97, 120, 101]
def appended_statement_r31 : List String := [] ++ appended_statement_r30
def appended_statement_s31 : State := ⟨.ident, [101, 120, 97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], appended_statement_r31⟩
theorem appended_statement_cut30 : feed (some appended_statement_s30) appended_statement_c30 = some appended_statement_s31 := by rfl
def appended_statement_c31 : List UInt8 := [100, 41, 59, 10, 32, 32, 32, 32]
def appended_statement_r32 : List String := [";", ")", "memory_order_relaxed"] ++ appended_statement_r31
def appended_statement_s32 : State := ⟨.normal, [], appended_statement_r32⟩
theorem appended_statement_cut31 : feed (some appended_statement_s31) appended_statement_c31 = some appended_statement_s32 := by rfl
def appended_statement_c32 : List UInt8 := [125, 10, 125, 32, 114, 101, 116, 117]
def appended_statement_r33 : List String := ["}", "}"] ++ appended_statement_r32
def appended_statement_s33 : State := ⟨.ident, [117, 116, 101, 114], appended_statement_r33⟩
theorem appended_statement_cut32 : feed (some appended_statement_s32) appended_statement_c32 = some appended_statement_s33 := by rfl
def appended_statement_c33 : List UInt8 := [114, 110, 59]
def appended_statement_r34 : List String := [";", "return"] ++ appended_statement_r33
def appended_statement_s34 : State := ⟨.normal, [], appended_statement_r34⟩
theorem appended_statement_cut33 : feed (some appended_statement_s33) appended_statement_c33 = some appended_statement_s34 := by rfl
def appended_statement_chunks : List (List UInt8) := [appended_statement_c0, appended_statement_c1, appended_statement_c2, appended_statement_c3, appended_statement_c4, appended_statement_c5, appended_statement_c6, appended_statement_c7, appended_statement_c8, appended_statement_c9, appended_statement_c10, appended_statement_c11, appended_statement_c12, appended_statement_c13, appended_statement_c14, appended_statement_c15, appended_statement_c16, appended_statement_c17, appended_statement_c18, appended_statement_c19, appended_statement_c20, appended_statement_c21, appended_statement_c22, appended_statement_c23, appended_statement_c24, appended_statement_c25, appended_statement_c26, appended_statement_c27, appended_statement_c28, appended_statement_c29, appended_statement_c30, appended_statement_c31, appended_statement_c32, appended_statement_c33]
def appended_statement : List UInt8 := appended_statement_chunks.flatten
theorem appended_statement_feed : appended_statement_chunks.foldl feed (some initial) = some appended_statement_s34 := by
  change appended_statement_chunks.foldl feed (some appended_statement_s0) = _
  simp only [appended_statement_chunks, List.foldl_cons, List.foldl_nil]
  rw [appended_statement_cut0, appended_statement_cut1, appended_statement_cut2, appended_statement_cut3, appended_statement_cut4, appended_statement_cut5, appended_statement_cut6, appended_statement_cut7, appended_statement_cut8, appended_statement_cut9, appended_statement_cut10, appended_statement_cut11, appended_statement_cut12, appended_statement_cut13, appended_statement_cut14, appended_statement_cut15, appended_statement_cut16, appended_statement_cut17, appended_statement_cut18, appended_statement_cut19, appended_statement_cut20, appended_statement_cut21, appended_statement_cut22, appended_statement_cut23, appended_statement_cut24, appended_statement_cut25, appended_statement_cut26, appended_statement_cut27, appended_statement_cut28, appended_statement_cut29, appended_statement_cut30, appended_statement_cut31, appended_statement_cut32, appended_statement_cut33]
theorem appended_statement_refuses : CAtomicIncrementSyntax.check appended_statement proposal = false := by
  unfold CAtomicIncrementSyntax.check
  rw [appended_statement, ← chunks_exact, tokenizeChunks, appended_statement_feed]
  decide

def unterminated_comment_r0 : List String := []
def unterminated_comment_s0 : State := initial
def unterminated_comment_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def unterminated_comment_r1 : List String := ["static"] ++ unterminated_comment_r0
def unterminated_comment_s1 : State := ⟨.ident, [105], unterminated_comment_r1⟩
theorem unterminated_comment_cut0 : feed (some unterminated_comment_s0) unterminated_comment_c0 = some unterminated_comment_s1 := by rfl
def unterminated_comment_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def unterminated_comment_r2 : List String := ["inline"] ++ unterminated_comment_r1
def unterminated_comment_s2 : State := ⟨.ident, [111, 118], unterminated_comment_r2⟩
theorem unterminated_comment_cut1 : feed (some unterminated_comment_s1) unterminated_comment_c1 = some unterminated_comment_s2 := by rfl
def unterminated_comment_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def unterminated_comment_r3 : List String := ["void"] ++ unterminated_comment_r2
def unterminated_comment_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], unterminated_comment_r3⟩
theorem unterminated_comment_cut2 : feed (some unterminated_comment_s2) unterminated_comment_c2 = some unterminated_comment_s3 := by rfl
def unterminated_comment_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def unterminated_comment_r4 : List String := ["(", "clean_inc"] ++ unterminated_comment_r3
def unterminated_comment_s4 : State := ⟨.ident, [101, 108, 99], unterminated_comment_r4⟩
theorem unterminated_comment_cut3 : feed (some unterminated_comment_s3) unterminated_comment_c3 = some unterminated_comment_s4 := by rfl
def unterminated_comment_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def unterminated_comment_r5 : List String := ["*", "clean_obj"] ++ unterminated_comment_r4
def unterminated_comment_s5 : State := ⟨.normal, [], unterminated_comment_r5⟩
theorem unterminated_comment_cut4 : feed (some unterminated_comment_s4) unterminated_comment_c4 = some unterminated_comment_s5 := by rfl
def unterminated_comment_c5 : List UInt8 := [111, 41, 32, 123, 10, 32, 32, 32]
def unterminated_comment_r6 : List String := ["{", ")", "o"] ++ unterminated_comment_r5
def unterminated_comment_s6 : State := ⟨.normal, [], unterminated_comment_r6⟩
theorem unterminated_comment_cut5 : feed (some unterminated_comment_s5) unterminated_comment_c5 = some unterminated_comment_s6 := by rfl
def unterminated_comment_c6 : List UInt8 := [32, 105, 102, 32, 40, 33, 99, 108]
def unterminated_comment_r7 : List String := ["!", "(", "if"] ++ unterminated_comment_r6
def unterminated_comment_s7 : State := ⟨.ident, [108, 99], unterminated_comment_r7⟩
theorem unterminated_comment_cut6 : feed (some unterminated_comment_s6) unterminated_comment_c6 = some unterminated_comment_s7 := by rfl
def unterminated_comment_c7 : List UInt8 := [101, 97, 110, 95, 105, 115, 95, 115]
def unterminated_comment_r8 : List String := [] ++ unterminated_comment_r7
def unterminated_comment_s8 : State := ⟨.ident, [115, 95, 115, 105, 95, 110, 97, 101, 108, 99], unterminated_comment_r8⟩
theorem unterminated_comment_cut7 : feed (some unterminated_comment_s7) unterminated_comment_c7 = some unterminated_comment_s8 := by rfl
def unterminated_comment_c8 : List UInt8 := [99, 97, 108, 97, 114, 40, 111, 41]
def unterminated_comment_r9 : List String := [")", "o", "(", "clean_is_scalar"] ++ unterminated_comment_r8
def unterminated_comment_s9 : State := ⟨.normal, [], unterminated_comment_r9⟩
theorem unterminated_comment_cut8 : feed (some unterminated_comment_s8) unterminated_comment_c8 = some unterminated_comment_s9 := by rfl
def unterminated_comment_c9 : List UInt8 := [32, 38, 38, 10, 32, 32, 32, 32]
def unterminated_comment_r10 : List String := ["&&"] ++ unterminated_comment_r9
def unterminated_comment_s10 : State := ⟨.normal, [], unterminated_comment_r10⟩
theorem unterminated_comment_cut9 : feed (some unterminated_comment_s9) unterminated_comment_c9 = some unterminated_comment_s10 := by rfl
def unterminated_comment_c10 : List UInt8 := [32, 32, 32, 32, 97, 116, 111, 109]
def unterminated_comment_r11 : List String := [] ++ unterminated_comment_r10
def unterminated_comment_s11 : State := ⟨.ident, [109, 111, 116, 97], unterminated_comment_r11⟩
theorem unterminated_comment_cut10 : feed (some unterminated_comment_s10) unterminated_comment_c10 = some unterminated_comment_s11 := by rfl
def unterminated_comment_c11 : List UInt8 := [105, 99, 95, 108, 111, 97, 100, 95]
def unterminated_comment_r12 : List String := [] ++ unterminated_comment_r11
def unterminated_comment_s12 : State := ⟨.ident, [95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], unterminated_comment_r12⟩
theorem unterminated_comment_cut11 : feed (some unterminated_comment_s11) unterminated_comment_c11 = some unterminated_comment_s12 := by rfl
def unterminated_comment_c12 : List UInt8 := [101, 120, 112, 108, 105, 99, 105, 116]
def unterminated_comment_r13 : List String := [] ++ unterminated_comment_r12
def unterminated_comment_s13 : State := ⟨.ident, [116, 105, 99, 105, 108, 112, 120, 101, 95, 100, 97, 111, 108, 95, 99, 105, 109, 111, 116, 97], unterminated_comment_r13⟩
theorem unterminated_comment_cut12 : feed (some unterminated_comment_s12) unterminated_comment_c12 = some unterminated_comment_s13 := by rfl
def unterminated_comment_c13 : List UInt8 := [40, 38, 111, 45, 62, 104, 101, 97]
def unterminated_comment_r14 : List String := ["->", "o", "&", "(", "atomic_load_explicit"] ++ unterminated_comment_r13
def unterminated_comment_s14 : State := ⟨.ident, [97, 101, 104], unterminated_comment_r14⟩
theorem unterminated_comment_cut13 : feed (some unterminated_comment_s13) unterminated_comment_c13 = some unterminated_comment_s14 := by rfl
def unterminated_comment_c14 : List UInt8 := [100, 101, 114, 46, 114, 101, 102, 95]
def unterminated_comment_r15 : List String := [".", "header"] ++ unterminated_comment_r14
def unterminated_comment_s15 : State := ⟨.ident, [95, 102, 101, 114], unterminated_comment_r15⟩
theorem unterminated_comment_cut14 : feed (some unterminated_comment_s14) unterminated_comment_c14 = some unterminated_comment_s15 := by rfl
def unterminated_comment_c15 : List UInt8 := [99, 111, 117, 110, 116, 44, 32, 109]
def unterminated_comment_r16 : List String := [",", "ref_count"] ++ unterminated_comment_r15
def unterminated_comment_s16 : State := ⟨.ident, [109], unterminated_comment_r16⟩
theorem unterminated_comment_cut15 : feed (some unterminated_comment_s15) unterminated_comment_c15 = some unterminated_comment_s16 := by rfl
def unterminated_comment_c16 : List UInt8 := [101, 109, 111, 114, 121, 95, 111, 114]
def unterminated_comment_r17 : List String := [] ++ unterminated_comment_r16
def unterminated_comment_s17 : State := ⟨.ident, [114, 111, 95, 121, 114, 111, 109, 101, 109], unterminated_comment_r17⟩
theorem unterminated_comment_cut16 : feed (some unterminated_comment_s16) unterminated_comment_c16 = some unterminated_comment_s17 := by rfl
def unterminated_comment_c17 : List UInt8 := [100, 101, 114, 95, 114, 101, 108, 97]
def unterminated_comment_r18 : List String := [] ++ unterminated_comment_r17
def unterminated_comment_s18 : State := ⟨.ident, [97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], unterminated_comment_r18⟩
theorem unterminated_comment_cut17 : feed (some unterminated_comment_s17) unterminated_comment_c17 = some unterminated_comment_s18 := by rfl
def unterminated_comment_c18 : List UInt8 := [120, 101, 100, 41, 32, 60, 32, 67]
def unterminated_comment_r19 : List String := ["<", ")", "memory_order_relaxed"] ++ unterminated_comment_r18
def unterminated_comment_s19 : State := ⟨.ident, [67], unterminated_comment_r19⟩
theorem unterminated_comment_cut18 : feed (some unterminated_comment_s18) unterminated_comment_c18 = some unterminated_comment_s19 := by rfl
def unterminated_comment_c19 : List UInt8 := [76, 69, 65, 78, 95, 82, 67, 95]
def unterminated_comment_r20 : List String := [] ++ unterminated_comment_r19
def unterminated_comment_s20 : State := ⟨.ident, [95, 67, 82, 95, 78, 65, 69, 76, 67], unterminated_comment_r20⟩
theorem unterminated_comment_cut19 : feed (some unterminated_comment_s19) unterminated_comment_c19 = some unterminated_comment_s20 := by rfl
def unterminated_comment_c20 : List UInt8 := [83, 84, 73, 67, 75, 89, 41, 32]
def unterminated_comment_r21 : List String := [")", "CLEAN_RC_STICKY"] ++ unterminated_comment_r20
def unterminated_comment_s21 : State := ⟨.normal, [], unterminated_comment_r21⟩
theorem unterminated_comment_cut20 : feed (some unterminated_comment_s20) unterminated_comment_c20 = some unterminated_comment_s21 := by rfl
def unterminated_comment_c21 : List UInt8 := [123, 10, 32, 32, 32, 32, 32, 32]
def unterminated_comment_r22 : List String := ["{"] ++ unterminated_comment_r21
def unterminated_comment_s22 : State := ⟨.normal, [], unterminated_comment_r22⟩
theorem unterminated_comment_cut21 : feed (some unterminated_comment_s21) unterminated_comment_c21 = some unterminated_comment_s22 := by rfl
def unterminated_comment_c22 : List UInt8 := [32, 32, 97, 116, 111, 109, 105, 99]
def unterminated_comment_r23 : List String := [] ++ unterminated_comment_r22
def unterminated_comment_s23 : State := ⟨.ident, [99, 105, 109, 111, 116, 97], unterminated_comment_r23⟩
theorem unterminated_comment_cut22 : feed (some unterminated_comment_s22) unterminated_comment_c22 = some unterminated_comment_s23 := by rfl
def unterminated_comment_c23 : List UInt8 := [95, 102, 101, 116, 99, 104, 95, 97]
def unterminated_comment_r24 : List String := [] ++ unterminated_comment_r23
def unterminated_comment_s24 : State := ⟨.ident, [97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], unterminated_comment_r24⟩
theorem unterminated_comment_cut23 : feed (some unterminated_comment_s23) unterminated_comment_c23 = some unterminated_comment_s24 := by rfl
def unterminated_comment_c24 : List UInt8 := [100, 100, 95, 101, 120, 112, 108, 105]
def unterminated_comment_r25 : List String := [] ++ unterminated_comment_r24
def unterminated_comment_s25 : State := ⟨.ident, [105, 108, 112, 120, 101, 95, 100, 100, 97, 95, 104, 99, 116, 101, 102, 95, 99, 105, 109, 111, 116, 97], unterminated_comment_r25⟩
theorem unterminated_comment_cut24 : feed (some unterminated_comment_s24) unterminated_comment_c24 = some unterminated_comment_s25 := by rfl
def unterminated_comment_c25 : List UInt8 := [99, 105, 116, 40, 38, 111, 45, 62]
def unterminated_comment_r26 : List String := ["->", "o", "&", "(", "atomic_fetch_add_explicit"] ++ unterminated_comment_r25
def unterminated_comment_s26 : State := ⟨.normal, [], unterminated_comment_r26⟩
theorem unterminated_comment_cut25 : feed (some unterminated_comment_s25) unterminated_comment_c25 = some unterminated_comment_s26 := by rfl
def unterminated_comment_c26 : List UInt8 := [104, 101, 97, 100, 101, 114, 46, 114]
def unterminated_comment_r27 : List String := [".", "header"] ++ unterminated_comment_r26
def unterminated_comment_s27 : State := ⟨.ident, [114], unterminated_comment_r27⟩
theorem unterminated_comment_cut26 : feed (some unterminated_comment_s26) unterminated_comment_c26 = some unterminated_comment_s27 := by rfl
def unterminated_comment_c27 : List UInt8 := [101, 102, 95, 99, 111, 117, 110, 116]
def unterminated_comment_r28 : List String := [] ++ unterminated_comment_r27
def unterminated_comment_s28 : State := ⟨.ident, [116, 110, 117, 111, 99, 95, 102, 101, 114], unterminated_comment_r28⟩
theorem unterminated_comment_cut27 : feed (some unterminated_comment_s27) unterminated_comment_c27 = some unterminated_comment_s28 := by rfl
def unterminated_comment_c28 : List UInt8 := [44, 32, 49, 44, 32, 109, 101, 109]
def unterminated_comment_r29 : List String := [",", "1", ",", "ref_count"] ++ unterminated_comment_r28
def unterminated_comment_s29 : State := ⟨.ident, [109, 101, 109], unterminated_comment_r29⟩
theorem unterminated_comment_cut28 : feed (some unterminated_comment_s28) unterminated_comment_c28 = some unterminated_comment_s29 := by rfl
def unterminated_comment_c29 : List UInt8 := [111, 114, 121, 95, 111, 114, 100, 101]
def unterminated_comment_r30 : List String := [] ++ unterminated_comment_r29
def unterminated_comment_s30 : State := ⟨.ident, [101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], unterminated_comment_r30⟩
theorem unterminated_comment_cut29 : feed (some unterminated_comment_s29) unterminated_comment_c29 = some unterminated_comment_s30 := by rfl
def unterminated_comment_c30 : List UInt8 := [114, 95, 114, 101, 108, 97, 120, 101]
def unterminated_comment_r31 : List String := [] ++ unterminated_comment_r30
def unterminated_comment_s31 : State := ⟨.ident, [101, 120, 97, 108, 101, 114, 95, 114, 101, 100, 114, 111, 95, 121, 114, 111, 109, 101, 109], unterminated_comment_r31⟩
theorem unterminated_comment_cut30 : feed (some unterminated_comment_s30) unterminated_comment_c30 = some unterminated_comment_s31 := by rfl
def unterminated_comment_c31 : List UInt8 := [100, 41, 59, 10, 32, 32, 32, 32]
def unterminated_comment_r32 : List String := [";", ")", "memory_order_relaxed"] ++ unterminated_comment_r31
def unterminated_comment_s32 : State := ⟨.normal, [], unterminated_comment_r32⟩
theorem unterminated_comment_cut31 : feed (some unterminated_comment_s31) unterminated_comment_c31 = some unterminated_comment_s32 := by rfl
def unterminated_comment_c32 : List UInt8 := [125, 10, 125, 32, 47, 42]
def unterminated_comment_r33 : List String := ["}", "}"] ++ unterminated_comment_r32
def unterminated_comment_s33 : State := ⟨.block, [], unterminated_comment_r33⟩
theorem unterminated_comment_cut32 : feed (some unterminated_comment_s32) unterminated_comment_c32 = some unterminated_comment_s33 := by rfl
def unterminated_comment_chunks : List (List UInt8) := [unterminated_comment_c0, unterminated_comment_c1, unterminated_comment_c2, unterminated_comment_c3, unterminated_comment_c4, unterminated_comment_c5, unterminated_comment_c6, unterminated_comment_c7, unterminated_comment_c8, unterminated_comment_c9, unterminated_comment_c10, unterminated_comment_c11, unterminated_comment_c12, unterminated_comment_c13, unterminated_comment_c14, unterminated_comment_c15, unterminated_comment_c16, unterminated_comment_c17, unterminated_comment_c18, unterminated_comment_c19, unterminated_comment_c20, unterminated_comment_c21, unterminated_comment_c22, unterminated_comment_c23, unterminated_comment_c24, unterminated_comment_c25, unterminated_comment_c26, unterminated_comment_c27, unterminated_comment_c28, unterminated_comment_c29, unterminated_comment_c30, unterminated_comment_c31, unterminated_comment_c32]
def unterminated_comment : List UInt8 := unterminated_comment_chunks.flatten
theorem unterminated_comment_feed : unterminated_comment_chunks.foldl feed (some initial) = some unterminated_comment_s33 := by
  change unterminated_comment_chunks.foldl feed (some unterminated_comment_s0) = _
  simp only [unterminated_comment_chunks, List.foldl_cons, List.foldl_nil]
  rw [unterminated_comment_cut0, unterminated_comment_cut1, unterminated_comment_cut2, unterminated_comment_cut3, unterminated_comment_cut4, unterminated_comment_cut5, unterminated_comment_cut6, unterminated_comment_cut7, unterminated_comment_cut8, unterminated_comment_cut9, unterminated_comment_cut10, unterminated_comment_cut11, unterminated_comment_cut12, unterminated_comment_cut13, unterminated_comment_cut14, unterminated_comment_cut15, unterminated_comment_cut16, unterminated_comment_cut17, unterminated_comment_cut18, unterminated_comment_cut19, unterminated_comment_cut20, unterminated_comment_cut21, unterminated_comment_cut22, unterminated_comment_cut23, unterminated_comment_cut24, unterminated_comment_cut25, unterminated_comment_cut26, unterminated_comment_cut27, unterminated_comment_cut28, unterminated_comment_cut29, unterminated_comment_cut30, unterminated_comment_cut31, unterminated_comment_cut32]
theorem unterminated_comment_refuses : CAtomicIncrementSyntax.check unterminated_comment proposal = false := by
  unfold CAtomicIncrementSyntax.check
  rw [unterminated_comment, ← chunks_exact, tokenizeChunks, unterminated_comment_feed]
  decide

def line_splice_r0 : List String := []
def line_splice_s0 : State := initial
def line_splice_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def line_splice_r1 : List String := ["static"] ++ line_splice_r0
def line_splice_s1 : State := ⟨.ident, [105], line_splice_r1⟩
theorem line_splice_cut0 : feed (some line_splice_s0) line_splice_c0 = some line_splice_s1 := by rfl
def line_splice_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def line_splice_r2 : List String := ["inline"] ++ line_splice_r1
def line_splice_s2 : State := ⟨.ident, [111, 118], line_splice_r2⟩
theorem line_splice_cut1 : feed (some line_splice_s1) line_splice_c1 = some line_splice_s2 := by rfl
def line_splice_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def line_splice_r3 : List String := ["void"] ++ line_splice_r2
def line_splice_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], line_splice_r3⟩
theorem line_splice_cut2 : feed (some line_splice_s2) line_splice_c2 = some line_splice_s3 := by rfl
def line_splice_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def line_splice_r4 : List String := ["(", "clean_inc"] ++ line_splice_r3
def line_splice_s4 : State := ⟨.ident, [101, 108, 99], line_splice_r4⟩
theorem line_splice_cut3 : feed (some line_splice_s3) line_splice_c3 = some line_splice_s4 := by rfl
def line_splice_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def line_splice_r5 : List String := ["*", "clean_obj"] ++ line_splice_r4
def line_splice_s5 : State := ⟨.normal, [], line_splice_r5⟩
theorem line_splice_cut4 : feed (some line_splice_s4) line_splice_c4 = some line_splice_s5 := by rfl
def line_splice_c5 : List UInt8 := [111, 41, 32, 123, 32, 47, 47, 32]
def line_splice_r6 : List String := ["{", ")", "o"] ++ line_splice_r5
def line_splice_s6 : State := ⟨.line, [], line_splice_r6⟩
theorem line_splice_cut5 : feed (some line_splice_s5) line_splice_c5 = some line_splice_s6 := by rfl
def line_splice_c6 : List UInt8 := [92, 10, 32, 32, 32, 32, 105, 102]
theorem line_splice_cut6 : feed (some line_splice_s6) line_splice_c6 = none := by rfl
def line_splice_c7 : List UInt8 := [32, 40, 33, 99, 108, 101, 97, 110]
theorem line_splice_cut7 : feed (none) line_splice_c7 = none := by rfl
def line_splice_c8 : List UInt8 := [95, 105, 115, 95, 115, 99, 97, 108]
theorem line_splice_cut8 : feed (none) line_splice_c8 = none := by rfl
def line_splice_c9 : List UInt8 := [97, 114, 40, 111, 41, 32, 38, 38]
theorem line_splice_cut9 : feed (none) line_splice_c9 = none := by rfl
def line_splice_c10 : List UInt8 := [10, 32, 32, 32, 32, 32, 32, 32]
theorem line_splice_cut10 : feed (none) line_splice_c10 = none := by rfl
def line_splice_c11 : List UInt8 := [32, 97, 116, 111, 109, 105, 99, 95]
theorem line_splice_cut11 : feed (none) line_splice_c11 = none := by rfl
def line_splice_c12 : List UInt8 := [108, 111, 97, 100, 95, 101, 120, 112]
theorem line_splice_cut12 : feed (none) line_splice_c12 = none := by rfl
def line_splice_c13 : List UInt8 := [108, 105, 99, 105, 116, 40, 38, 111]
theorem line_splice_cut13 : feed (none) line_splice_c13 = none := by rfl
def line_splice_c14 : List UInt8 := [45, 62, 104, 101, 97, 100, 101, 114]
theorem line_splice_cut14 : feed (none) line_splice_c14 = none := by rfl
def line_splice_c15 : List UInt8 := [46, 114, 101, 102, 95, 99, 111, 117]
theorem line_splice_cut15 : feed (none) line_splice_c15 = none := by rfl
def line_splice_c16 : List UInt8 := [110, 116, 44, 32, 109, 101, 109, 111]
theorem line_splice_cut16 : feed (none) line_splice_c16 = none := by rfl
def line_splice_c17 : List UInt8 := [114, 121, 95, 111, 114, 100, 101, 114]
theorem line_splice_cut17 : feed (none) line_splice_c17 = none := by rfl
def line_splice_c18 : List UInt8 := [95, 114, 101, 108, 97, 120, 101, 100]
theorem line_splice_cut18 : feed (none) line_splice_c18 = none := by rfl
def line_splice_c19 : List UInt8 := [41, 32, 60, 32, 67, 76, 69, 65]
theorem line_splice_cut19 : feed (none) line_splice_c19 = none := by rfl
def line_splice_c20 : List UInt8 := [78, 95, 82, 67, 95, 83, 84, 73]
theorem line_splice_cut20 : feed (none) line_splice_c20 = none := by rfl
def line_splice_c21 : List UInt8 := [67, 75, 89, 41, 32, 123, 10, 32]
theorem line_splice_cut21 : feed (none) line_splice_c21 = none := by rfl
def line_splice_c22 : List UInt8 := [32, 32, 32, 32, 32, 32, 32, 97]
theorem line_splice_cut22 : feed (none) line_splice_c22 = none := by rfl
def line_splice_c23 : List UInt8 := [116, 111, 109, 105, 99, 95, 102, 101]
theorem line_splice_cut23 : feed (none) line_splice_c23 = none := by rfl
def line_splice_c24 : List UInt8 := [116, 99, 104, 95, 97, 100, 100, 95]
theorem line_splice_cut24 : feed (none) line_splice_c24 = none := by rfl
def line_splice_c25 : List UInt8 := [101, 120, 112, 108, 105, 99, 105, 116]
theorem line_splice_cut25 : feed (none) line_splice_c25 = none := by rfl
def line_splice_c26 : List UInt8 := [40, 38, 111, 45, 62, 104, 101, 97]
theorem line_splice_cut26 : feed (none) line_splice_c26 = none := by rfl
def line_splice_c27 : List UInt8 := [100, 101, 114, 46, 114, 101, 102, 95]
theorem line_splice_cut27 : feed (none) line_splice_c27 = none := by rfl
def line_splice_c28 : List UInt8 := [99, 111, 117, 110, 116, 44, 32, 49]
theorem line_splice_cut28 : feed (none) line_splice_c28 = none := by rfl
def line_splice_c29 : List UInt8 := [44, 32, 109, 101, 109, 111, 114, 121]
theorem line_splice_cut29 : feed (none) line_splice_c29 = none := by rfl
def line_splice_c30 : List UInt8 := [95, 111, 114, 100, 101, 114, 95, 114]
theorem line_splice_cut30 : feed (none) line_splice_c30 = none := by rfl
def line_splice_c31 : List UInt8 := [101, 108, 97, 120, 101, 100, 41, 59]
theorem line_splice_cut31 : feed (none) line_splice_c31 = none := by rfl
def line_splice_c32 : List UInt8 := [10, 32, 32, 32, 32, 125, 10, 125]
theorem line_splice_cut32 : feed (none) line_splice_c32 = none := by rfl
def line_splice_chunks : List (List UInt8) := [line_splice_c0, line_splice_c1, line_splice_c2, line_splice_c3, line_splice_c4, line_splice_c5, line_splice_c6, line_splice_c7, line_splice_c8, line_splice_c9, line_splice_c10, line_splice_c11, line_splice_c12, line_splice_c13, line_splice_c14, line_splice_c15, line_splice_c16, line_splice_c17, line_splice_c18, line_splice_c19, line_splice_c20, line_splice_c21, line_splice_c22, line_splice_c23, line_splice_c24, line_splice_c25, line_splice_c26, line_splice_c27, line_splice_c28, line_splice_c29, line_splice_c30, line_splice_c31, line_splice_c32]
def line_splice : List UInt8 := line_splice_chunks.flatten
theorem line_splice_feed : line_splice_chunks.foldl feed (some initial) = none := by
  change line_splice_chunks.foldl feed (some line_splice_s0) = _
  simp only [line_splice_chunks, List.foldl_cons, List.foldl_nil]
  rw [line_splice_cut0, line_splice_cut1, line_splice_cut2, line_splice_cut3, line_splice_cut4, line_splice_cut5, line_splice_cut6, line_splice_cut7, line_splice_cut8, line_splice_cut9, line_splice_cut10, line_splice_cut11, line_splice_cut12, line_splice_cut13, line_splice_cut14, line_splice_cut15, line_splice_cut16, line_splice_cut17, line_splice_cut18, line_splice_cut19, line_splice_cut20, line_splice_cut21, line_splice_cut22, line_splice_cut23, line_splice_cut24, line_splice_cut25, line_splice_cut26, line_splice_cut27, line_splice_cut28, line_splice_cut29, line_splice_cut30, line_splice_cut31, line_splice_cut32]
theorem line_splice_refuses : CAtomicIncrementSyntax.check line_splice proposal = false := by
  unfold CAtomicIncrementSyntax.check
  rw [line_splice, ← chunks_exact, tokenizeChunks, line_splice_feed]
  decide

def trigraph_splice_r0 : List String := []
def trigraph_splice_s0 : State := initial
def trigraph_splice_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def trigraph_splice_r1 : List String := ["static"] ++ trigraph_splice_r0
def trigraph_splice_s1 : State := ⟨.ident, [105], trigraph_splice_r1⟩
theorem trigraph_splice_cut0 : feed (some trigraph_splice_s0) trigraph_splice_c0 = some trigraph_splice_s1 := by rfl
def trigraph_splice_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def trigraph_splice_r2 : List String := ["inline"] ++ trigraph_splice_r1
def trigraph_splice_s2 : State := ⟨.ident, [111, 118], trigraph_splice_r2⟩
theorem trigraph_splice_cut1 : feed (some trigraph_splice_s1) trigraph_splice_c1 = some trigraph_splice_s2 := by rfl
def trigraph_splice_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def trigraph_splice_r3 : List String := ["void"] ++ trigraph_splice_r2
def trigraph_splice_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], trigraph_splice_r3⟩
theorem trigraph_splice_cut2 : feed (some trigraph_splice_s2) trigraph_splice_c2 = some trigraph_splice_s3 := by rfl
def trigraph_splice_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def trigraph_splice_r4 : List String := ["(", "clean_inc"] ++ trigraph_splice_r3
def trigraph_splice_s4 : State := ⟨.ident, [101, 108, 99], trigraph_splice_r4⟩
theorem trigraph_splice_cut3 : feed (some trigraph_splice_s3) trigraph_splice_c3 = some trigraph_splice_s4 := by rfl
def trigraph_splice_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def trigraph_splice_r5 : List String := ["*", "clean_obj"] ++ trigraph_splice_r4
def trigraph_splice_s5 : State := ⟨.normal, [], trigraph_splice_r5⟩
theorem trigraph_splice_cut4 : feed (some trigraph_splice_s4) trigraph_splice_c4 = some trigraph_splice_s5 := by rfl
def trigraph_splice_c5 : List UInt8 := [111, 41, 32, 123, 32, 47, 47, 32]
def trigraph_splice_r6 : List String := ["{", ")", "o"] ++ trigraph_splice_r5
def trigraph_splice_s6 : State := ⟨.line, [], trigraph_splice_r6⟩
theorem trigraph_splice_cut5 : feed (some trigraph_splice_s5) trigraph_splice_c5 = some trigraph_splice_s6 := by rfl
def trigraph_splice_c6 : List UInt8 := [63, 63, 47, 10, 32, 32, 32, 32]
theorem trigraph_splice_cut6 : feed (some trigraph_splice_s6) trigraph_splice_c6 = none := by rfl
def trigraph_splice_c7 : List UInt8 := [105, 102, 32, 40, 33, 99, 108, 101]
theorem trigraph_splice_cut7 : feed (none) trigraph_splice_c7 = none := by rfl
def trigraph_splice_c8 : List UInt8 := [97, 110, 95, 105, 115, 95, 115, 99]
theorem trigraph_splice_cut8 : feed (none) trigraph_splice_c8 = none := by rfl
def trigraph_splice_c9 : List UInt8 := [97, 108, 97, 114, 40, 111, 41, 32]
theorem trigraph_splice_cut9 : feed (none) trigraph_splice_c9 = none := by rfl
def trigraph_splice_c10 : List UInt8 := [38, 38, 10, 32, 32, 32, 32, 32]
theorem trigraph_splice_cut10 : feed (none) trigraph_splice_c10 = none := by rfl
def trigraph_splice_c11 : List UInt8 := [32, 32, 32, 97, 116, 111, 109, 105]
theorem trigraph_splice_cut11 : feed (none) trigraph_splice_c11 = none := by rfl
def trigraph_splice_c12 : List UInt8 := [99, 95, 108, 111, 97, 100, 95, 101]
theorem trigraph_splice_cut12 : feed (none) trigraph_splice_c12 = none := by rfl
def trigraph_splice_c13 : List UInt8 := [120, 112, 108, 105, 99, 105, 116, 40]
theorem trigraph_splice_cut13 : feed (none) trigraph_splice_c13 = none := by rfl
def trigraph_splice_c14 : List UInt8 := [38, 111, 45, 62, 104, 101, 97, 100]
theorem trigraph_splice_cut14 : feed (none) trigraph_splice_c14 = none := by rfl
def trigraph_splice_c15 : List UInt8 := [101, 114, 46, 114, 101, 102, 95, 99]
theorem trigraph_splice_cut15 : feed (none) trigraph_splice_c15 = none := by rfl
def trigraph_splice_c16 : List UInt8 := [111, 117, 110, 116, 44, 32, 109, 101]
theorem trigraph_splice_cut16 : feed (none) trigraph_splice_c16 = none := by rfl
def trigraph_splice_c17 : List UInt8 := [109, 111, 114, 121, 95, 111, 114, 100]
theorem trigraph_splice_cut17 : feed (none) trigraph_splice_c17 = none := by rfl
def trigraph_splice_c18 : List UInt8 := [101, 114, 95, 114, 101, 108, 97, 120]
theorem trigraph_splice_cut18 : feed (none) trigraph_splice_c18 = none := by rfl
def trigraph_splice_c19 : List UInt8 := [101, 100, 41, 32, 60, 32, 67, 76]
theorem trigraph_splice_cut19 : feed (none) trigraph_splice_c19 = none := by rfl
def trigraph_splice_c20 : List UInt8 := [69, 65, 78, 95, 82, 67, 95, 83]
theorem trigraph_splice_cut20 : feed (none) trigraph_splice_c20 = none := by rfl
def trigraph_splice_c21 : List UInt8 := [84, 73, 67, 75, 89, 41, 32, 123]
theorem trigraph_splice_cut21 : feed (none) trigraph_splice_c21 = none := by rfl
def trigraph_splice_c22 : List UInt8 := [10, 32, 32, 32, 32, 32, 32, 32]
theorem trigraph_splice_cut22 : feed (none) trigraph_splice_c22 = none := by rfl
def trigraph_splice_c23 : List UInt8 := [32, 97, 116, 111, 109, 105, 99, 95]
theorem trigraph_splice_cut23 : feed (none) trigraph_splice_c23 = none := by rfl
def trigraph_splice_c24 : List UInt8 := [102, 101, 116, 99, 104, 95, 97, 100]
theorem trigraph_splice_cut24 : feed (none) trigraph_splice_c24 = none := by rfl
def trigraph_splice_c25 : List UInt8 := [100, 95, 101, 120, 112, 108, 105, 99]
theorem trigraph_splice_cut25 : feed (none) trigraph_splice_c25 = none := by rfl
def trigraph_splice_c26 : List UInt8 := [105, 116, 40, 38, 111, 45, 62, 104]
theorem trigraph_splice_cut26 : feed (none) trigraph_splice_c26 = none := by rfl
def trigraph_splice_c27 : List UInt8 := [101, 97, 100, 101, 114, 46, 114, 101]
theorem trigraph_splice_cut27 : feed (none) trigraph_splice_c27 = none := by rfl
def trigraph_splice_c28 : List UInt8 := [102, 95, 99, 111, 117, 110, 116, 44]
theorem trigraph_splice_cut28 : feed (none) trigraph_splice_c28 = none := by rfl
def trigraph_splice_c29 : List UInt8 := [32, 49, 44, 32, 109, 101, 109, 111]
theorem trigraph_splice_cut29 : feed (none) trigraph_splice_c29 = none := by rfl
def trigraph_splice_c30 : List UInt8 := [114, 121, 95, 111, 114, 100, 101, 114]
theorem trigraph_splice_cut30 : feed (none) trigraph_splice_c30 = none := by rfl
def trigraph_splice_c31 : List UInt8 := [95, 114, 101, 108, 97, 120, 101, 100]
theorem trigraph_splice_cut31 : feed (none) trigraph_splice_c31 = none := by rfl
def trigraph_splice_c32 : List UInt8 := [41, 59, 10, 32, 32, 32, 32, 125]
theorem trigraph_splice_cut32 : feed (none) trigraph_splice_c32 = none := by rfl
def trigraph_splice_c33 : List UInt8 := [10, 125]
theorem trigraph_splice_cut33 : feed (none) trigraph_splice_c33 = none := by rfl
def trigraph_splice_chunks : List (List UInt8) := [trigraph_splice_c0, trigraph_splice_c1, trigraph_splice_c2, trigraph_splice_c3, trigraph_splice_c4, trigraph_splice_c5, trigraph_splice_c6, trigraph_splice_c7, trigraph_splice_c8, trigraph_splice_c9, trigraph_splice_c10, trigraph_splice_c11, trigraph_splice_c12, trigraph_splice_c13, trigraph_splice_c14, trigraph_splice_c15, trigraph_splice_c16, trigraph_splice_c17, trigraph_splice_c18, trigraph_splice_c19, trigraph_splice_c20, trigraph_splice_c21, trigraph_splice_c22, trigraph_splice_c23, trigraph_splice_c24, trigraph_splice_c25, trigraph_splice_c26, trigraph_splice_c27, trigraph_splice_c28, trigraph_splice_c29, trigraph_splice_c30, trigraph_splice_c31, trigraph_splice_c32, trigraph_splice_c33]
def trigraph_splice : List UInt8 := trigraph_splice_chunks.flatten
theorem trigraph_splice_feed : trigraph_splice_chunks.foldl feed (some initial) = none := by
  change trigraph_splice_chunks.foldl feed (some trigraph_splice_s0) = _
  simp only [trigraph_splice_chunks, List.foldl_cons, List.foldl_nil]
  rw [trigraph_splice_cut0, trigraph_splice_cut1, trigraph_splice_cut2, trigraph_splice_cut3, trigraph_splice_cut4, trigraph_splice_cut5, trigraph_splice_cut6, trigraph_splice_cut7, trigraph_splice_cut8, trigraph_splice_cut9, trigraph_splice_cut10, trigraph_splice_cut11, trigraph_splice_cut12, trigraph_splice_cut13, trigraph_splice_cut14, trigraph_splice_cut15, trigraph_splice_cut16, trigraph_splice_cut17, trigraph_splice_cut18, trigraph_splice_cut19, trigraph_splice_cut20, trigraph_splice_cut21, trigraph_splice_cut22, trigraph_splice_cut23, trigraph_splice_cut24, trigraph_splice_cut25, trigraph_splice_cut26, trigraph_splice_cut27, trigraph_splice_cut28, trigraph_splice_cut29, trigraph_splice_cut30, trigraph_splice_cut31, trigraph_splice_cut32, trigraph_splice_cut33]
theorem trigraph_splice_refuses : CAtomicIncrementSyntax.check trigraph_splice proposal = false := by
  unfold CAtomicIncrementSyntax.check
  rw [trigraph_splice, ← chunks_exact, tokenizeChunks, trigraph_splice_feed]
  decide

def carriage_return_r0 : List String := []
def carriage_return_s0 : State := initial
def carriage_return_c0 : List UInt8 := [115, 116, 97, 116, 105, 99, 32, 105]
def carriage_return_r1 : List String := ["static"] ++ carriage_return_r0
def carriage_return_s1 : State := ⟨.ident, [105], carriage_return_r1⟩
theorem carriage_return_cut0 : feed (some carriage_return_s0) carriage_return_c0 = some carriage_return_s1 := by rfl
def carriage_return_c1 : List UInt8 := [110, 108, 105, 110, 101, 32, 118, 111]
def carriage_return_r2 : List String := ["inline"] ++ carriage_return_r1
def carriage_return_s2 : State := ⟨.ident, [111, 118], carriage_return_r2⟩
theorem carriage_return_cut1 : feed (some carriage_return_s1) carriage_return_c1 = some carriage_return_s2 := by rfl
def carriage_return_c2 : List UInt8 := [105, 100, 32, 99, 108, 101, 97, 110]
def carriage_return_r3 : List String := ["void"] ++ carriage_return_r2
def carriage_return_s3 : State := ⟨.ident, [110, 97, 101, 108, 99], carriage_return_r3⟩
theorem carriage_return_cut2 : feed (some carriage_return_s2) carriage_return_c2 = some carriage_return_s3 := by rfl
def carriage_return_c3 : List UInt8 := [95, 105, 110, 99, 40, 99, 108, 101]
def carriage_return_r4 : List String := ["(", "clean_inc"] ++ carriage_return_r3
def carriage_return_s4 : State := ⟨.ident, [101, 108, 99], carriage_return_r4⟩
theorem carriage_return_cut3 : feed (some carriage_return_s3) carriage_return_c3 = some carriage_return_s4 := by rfl
def carriage_return_c4 : List UInt8 := [97, 110, 95, 111, 98, 106, 42, 32]
def carriage_return_r5 : List String := ["*", "clean_obj"] ++ carriage_return_r4
def carriage_return_s5 : State := ⟨.normal, [], carriage_return_r5⟩
theorem carriage_return_cut4 : feed (some carriage_return_s4) carriage_return_c4 = some carriage_return_s5 := by rfl
def carriage_return_c5 : List UInt8 := [111, 41, 32, 123, 13, 32, 32, 32]
theorem carriage_return_cut5 : feed (some carriage_return_s5) carriage_return_c5 = none := by rfl
def carriage_return_c6 : List UInt8 := [32, 105, 102, 32, 40, 33, 99, 108]
theorem carriage_return_cut6 : feed (none) carriage_return_c6 = none := by rfl
def carriage_return_c7 : List UInt8 := [101, 97, 110, 95, 105, 115, 95, 115]
theorem carriage_return_cut7 : feed (none) carriage_return_c7 = none := by rfl
def carriage_return_c8 : List UInt8 := [99, 97, 108, 97, 114, 40, 111, 41]
theorem carriage_return_cut8 : feed (none) carriage_return_c8 = none := by rfl
def carriage_return_c9 : List UInt8 := [32, 38, 38, 13, 32, 32, 32, 32]
theorem carriage_return_cut9 : feed (none) carriage_return_c9 = none := by rfl
def carriage_return_c10 : List UInt8 := [32, 32, 32, 32, 97, 116, 111, 109]
theorem carriage_return_cut10 : feed (none) carriage_return_c10 = none := by rfl
def carriage_return_c11 : List UInt8 := [105, 99, 95, 108, 111, 97, 100, 95]
theorem carriage_return_cut11 : feed (none) carriage_return_c11 = none := by rfl
def carriage_return_c12 : List UInt8 := [101, 120, 112, 108, 105, 99, 105, 116]
theorem carriage_return_cut12 : feed (none) carriage_return_c12 = none := by rfl
def carriage_return_c13 : List UInt8 := [40, 38, 111, 45, 62, 104, 101, 97]
theorem carriage_return_cut13 : feed (none) carriage_return_c13 = none := by rfl
def carriage_return_c14 : List UInt8 := [100, 101, 114, 46, 114, 101, 102, 95]
theorem carriage_return_cut14 : feed (none) carriage_return_c14 = none := by rfl
def carriage_return_c15 : List UInt8 := [99, 111, 117, 110, 116, 44, 32, 109]
theorem carriage_return_cut15 : feed (none) carriage_return_c15 = none := by rfl
def carriage_return_c16 : List UInt8 := [101, 109, 111, 114, 121, 95, 111, 114]
theorem carriage_return_cut16 : feed (none) carriage_return_c16 = none := by rfl
def carriage_return_c17 : List UInt8 := [100, 101, 114, 95, 114, 101, 108, 97]
theorem carriage_return_cut17 : feed (none) carriage_return_c17 = none := by rfl
def carriage_return_c18 : List UInt8 := [120, 101, 100, 41, 32, 60, 32, 67]
theorem carriage_return_cut18 : feed (none) carriage_return_c18 = none := by rfl
def carriage_return_c19 : List UInt8 := [76, 69, 65, 78, 95, 82, 67, 95]
theorem carriage_return_cut19 : feed (none) carriage_return_c19 = none := by rfl
def carriage_return_c20 : List UInt8 := [83, 84, 73, 67, 75, 89, 41, 32]
theorem carriage_return_cut20 : feed (none) carriage_return_c20 = none := by rfl
def carriage_return_c21 : List UInt8 := [123, 13, 32, 32, 32, 32, 32, 32]
theorem carriage_return_cut21 : feed (none) carriage_return_c21 = none := by rfl
def carriage_return_c22 : List UInt8 := [32, 32, 97, 116, 111, 109, 105, 99]
theorem carriage_return_cut22 : feed (none) carriage_return_c22 = none := by rfl
def carriage_return_c23 : List UInt8 := [95, 102, 101, 116, 99, 104, 95, 97]
theorem carriage_return_cut23 : feed (none) carriage_return_c23 = none := by rfl
def carriage_return_c24 : List UInt8 := [100, 100, 95, 101, 120, 112, 108, 105]
theorem carriage_return_cut24 : feed (none) carriage_return_c24 = none := by rfl
def carriage_return_c25 : List UInt8 := [99, 105, 116, 40, 38, 111, 45, 62]
theorem carriage_return_cut25 : feed (none) carriage_return_c25 = none := by rfl
def carriage_return_c26 : List UInt8 := [104, 101, 97, 100, 101, 114, 46, 114]
theorem carriage_return_cut26 : feed (none) carriage_return_c26 = none := by rfl
def carriage_return_c27 : List UInt8 := [101, 102, 95, 99, 111, 117, 110, 116]
theorem carriage_return_cut27 : feed (none) carriage_return_c27 = none := by rfl
def carriage_return_c28 : List UInt8 := [44, 32, 49, 44, 32, 109, 101, 109]
theorem carriage_return_cut28 : feed (none) carriage_return_c28 = none := by rfl
def carriage_return_c29 : List UInt8 := [111, 114, 121, 95, 111, 114, 100, 101]
theorem carriage_return_cut29 : feed (none) carriage_return_c29 = none := by rfl
def carriage_return_c30 : List UInt8 := [114, 95, 114, 101, 108, 97, 120, 101]
theorem carriage_return_cut30 : feed (none) carriage_return_c30 = none := by rfl
def carriage_return_c31 : List UInt8 := [100, 41, 59, 13, 32, 32, 32, 32]
theorem carriage_return_cut31 : feed (none) carriage_return_c31 = none := by rfl
def carriage_return_c32 : List UInt8 := [125, 13, 125]
theorem carriage_return_cut32 : feed (none) carriage_return_c32 = none := by rfl
def carriage_return_chunks : List (List UInt8) := [carriage_return_c0, carriage_return_c1, carriage_return_c2, carriage_return_c3, carriage_return_c4, carriage_return_c5, carriage_return_c6, carriage_return_c7, carriage_return_c8, carriage_return_c9, carriage_return_c10, carriage_return_c11, carriage_return_c12, carriage_return_c13, carriage_return_c14, carriage_return_c15, carriage_return_c16, carriage_return_c17, carriage_return_c18, carriage_return_c19, carriage_return_c20, carriage_return_c21, carriage_return_c22, carriage_return_c23, carriage_return_c24, carriage_return_c25, carriage_return_c26, carriage_return_c27, carriage_return_c28, carriage_return_c29, carriage_return_c30, carriage_return_c31, carriage_return_c32]
def carriage_return : List UInt8 := carriage_return_chunks.flatten
theorem carriage_return_feed : carriage_return_chunks.foldl feed (some initial) = none := by
  change carriage_return_chunks.foldl feed (some carriage_return_s0) = _
  simp only [carriage_return_chunks, List.foldl_cons, List.foldl_nil]
  rw [carriage_return_cut0, carriage_return_cut1, carriage_return_cut2, carriage_return_cut3, carriage_return_cut4, carriage_return_cut5, carriage_return_cut6, carriage_return_cut7, carriage_return_cut8, carriage_return_cut9, carriage_return_cut10, carriage_return_cut11, carriage_return_cut12, carriage_return_cut13, carriage_return_cut14, carriage_return_cut15, carriage_return_cut16, carriage_return_cut17, carriage_return_cut18, carriage_return_cut19, carriage_return_cut20, carriage_return_cut21, carriage_return_cut22, carriage_return_cut23, carriage_return_cut24, carriage_return_cut25, carriage_return_cut26, carriage_return_cut27, carriage_return_cut28, carriage_return_cut29, carriage_return_cut30, carriage_return_cut31, carriage_return_cut32]
theorem carriage_return_refuses : CAtomicIncrementSyntax.check carriage_return proposal = false := by
  unfold CAtomicIncrementSyntax.check
  rw [carriage_return, ← chunks_exact, tokenizeChunks, carriage_return_feed]
  decide

#print axioms actual_syntax
#print axioms actual_tokens
end CAtomicIncrementSource
