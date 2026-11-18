-- Copyright 2026 Andrew Yates | Apache-2.0
import C11DirectiveLines
import C11ConditionCuts
namespace C11ConditionDirectiveCuts
open C11DirectiveLines C11ConditionCuts
def state1 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut0 : C11DirectiveLines.feed (some initial) branch_chunk0 = state1 := by rfl
def state2 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut1 : C11DirectiveLines.feed state1 branch_chunk1 = state2 := by rfl
def state3 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut2 : C11DirectiveLines.feed state2 branch_chunk2 = state3 := by rfl
def state4 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut3 : C11DirectiveLines.feed state3 branch_chunk3 = state4 := by rfl
def state5 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut4 : C11DirectiveLines.feed state4 branch_chunk4 = state5 := by rfl
def state6 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut5 : C11DirectiveLines.feed state5 branch_chunk5 = state6 := by rfl
def state7 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut6 : C11DirectiveLines.feed state6 branch_chunk6 = state7 := by rfl
def state8 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := false }
theorem cut7 : C11DirectiveLines.feed state7 branch_chunk7 = state8 := by rfl
def state9 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut8 : C11DirectiveLines.feed state8 branch_chunk8 = state9 := by rfl
def state10 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut9 : C11DirectiveLines.feed state9 branch_chunk9 = state10 := by rfl
def state11 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut10 : C11DirectiveLines.feed state10 branch_chunk10 = state11 := by rfl
def state12 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := false }
theorem cut11 : C11DirectiveLines.feed state11 branch_chunk11 = state12 := by rfl
def state13 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut12 : C11DirectiveLines.feed state12 branch_chunk12 = state13 := by rfl
def state14 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := false }
theorem cut13 : C11DirectiveLines.feed state13 branch_chunk13 = state14 := by rfl
def state15 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut14 : C11DirectiveLines.feed state14 branch_chunk14 = state15 := by rfl
def state16 : Option C11DirectiveLines.State := some { mode := .normal, beginning := true, directive := false }
theorem cut15 : C11DirectiveLines.feed state15 branch_chunk15 = state16 := by rfl
theorem complete_characters_supported : supportedCharacters branch_chunks.flatten = true := by
  rw [← C11DirectiveLines.chunks_exact]
  simp only [supportedChunks, branch_chunks, List.foldl_cons, List.foldl_nil]
  rw [cut0, cut1, cut2, cut3, cut4, cut5, cut6, cut7, cut8, cut9, cut10, cut11, cut12, cut13, cut14, cut15]
  rfl
theorem complete_source_supported : supported C11ConditionData.branch_0 = true := by
  unfold supported
  rw [← branch_string_exact, branch_node_0_16_characters, branch_flatten_exact]
  exact complete_characters_supported
end C11ConditionDirectiveCuts
