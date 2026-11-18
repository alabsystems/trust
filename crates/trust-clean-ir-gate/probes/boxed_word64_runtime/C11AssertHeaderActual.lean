-- Copyright 2026 Andrew Yates | Apache-2.0
import C11ConditionalHeaders
import C11AssertHeaderCuts
import C11AssertDirectiveCuts
namespace C11AssertHeaderActual
open C11ConditionalHeaders C11AssertHeaderCuts
theorem final_chunk_newline : assertHeader_chunk150.getLast? = some '\n' := by rfl
theorem last_149_151 : assertHeader_node_149_151_chars.getLast? = some '\n' := by
  rw [assertHeader_node_149_151_chars, List.getLast?_append, final_chunk_newline]
  rfl
theorem last_148_151 : assertHeader_node_148_151_chars.getLast? = some '\n' := by
  rw [assertHeader_node_148_151_chars, List.getLast?_append, last_149_151]
  rfl
theorem last_146_151 : assertHeader_node_146_151_chars.getLast? = some '\n' := by
  rw [assertHeader_node_146_151_chars, List.getLast?_append, last_148_151]
  rfl
theorem last_141_151 : assertHeader_node_141_151_chars.getLast? = some '\n' := by
  rw [assertHeader_node_141_151_chars, List.getLast?_append, last_146_151]
  rfl
theorem last_132_151 : assertHeader_node_132_151_chars.getLast? = some '\n' := by
  rw [assertHeader_node_132_151_chars, List.getLast?_append, last_141_151]
  rfl
theorem last_113_151 : assertHeader_node_113_151_chars.getLast? = some '\n' := by
  rw [assertHeader_node_113_151_chars, List.getLast?_append, last_132_151]
  rfl
theorem last_75_151 : assertHeader_node_75_151_chars.getLast? = some '\n' := by
  rw [assertHeader_node_75_151_chars, List.getLast?_append, last_113_151]
  rfl
theorem last_0_151 : assertHeader_node_0_151_chars.getLast? = some '\n' := by
  rw [assertHeader_node_0_151_chars, List.getLast?_append, last_75_151]
  rfl
theorem complete_source_final_newline : C11AssertHeaderData.assertHeader_0.toList.getLast? = some '\n' := by
  rw [← assertHeader_string_exact, assertHeader_node_0_151_characters]
  exact last_0_151
/- Complete actual1205B owner under explicitly PROPOSED context; captured
predefines and activeTU association are not claimed by this equation. -/
theorem source_201112_selects_definition :
    (process [("__STDC_VERSION__", ["201112L"])] C11AssertHeaderData.assertHeader_0).map
      (fun state => (state.macros, state.reversedOutput, state.stack)) = some ([("__STDC_VERSION__", ["201112L"]), ("_ASSERT_H_", []), ("static_assert", ["_Static_assert"])], [], []) := by
  unfold process
  rw [C11AssertDirectiveCuts.complete_source_supported, complete_source_final_newline]
  rw [Bool.and_comm, C11AssertHeaderCuts.assertHeader_source_lex]
  rfl
/- Complete actual1205B owner under explicitly PROPOSED context; captured
predefines and activeTU association are not claimed by this equation. -/
theorem source_199901_omits_definition :
    (process [("__STDC_VERSION__", ["199901L"])] C11AssertHeaderData.assertHeader_0).map
      (fun state => (state.macros, state.reversedOutput, state.stack)) = some ([("__STDC_VERSION__", ["199901L"]), ("_ASSERT_H_", [])], [], []) := by
  unfold process
  rw [C11AssertDirectiveCuts.complete_source_supported, complete_source_final_newline]
  rw [Bool.and_comm, C11AssertHeaderCuts.assertHeader_source_lex]
  rfl
/- Complete actual1205B owner under explicitly PROPOSED context; captured
predefines and activeTU association are not claimed by this equation. -/
theorem source_cpp_presence_suppresses_definition :
    (process [("__STDC_VERSION__", ["201112L"]), ("__cplusplus", ["201703L"])] C11AssertHeaderData.assertHeader_0).map
      (fun state => (state.macros, state.reversedOutput, state.stack)) = some ([("__STDC_VERSION__", ["201112L"]), ("__cplusplus", ["201703L"]), ("_ASSERT_H_", [])], [], []) := by
  unfold process
  rw [C11AssertDirectiveCuts.complete_source_supported, complete_source_final_newline]
  rw [Bool.and_comm, C11AssertHeaderCuts.assertHeader_source_lex]
  rfl
/- Complete actual1205B owner under explicitly PROPOSED context; captured
predefines and activeTU association are not claimed by this equation. -/
theorem source_repeated_guard_omits_definition :
    (process [("_ASSERT_H_", []), ("__STDC_VERSION__", ["201112L"])] C11AssertHeaderData.assertHeader_0).map
      (fun state => (state.macros, state.reversedOutput, state.stack)) = some ([("_ASSERT_H_", []), ("__STDC_VERSION__", ["201112L"])], [], []) := by
  unfold process
  rw [C11AssertDirectiveCuts.complete_source_supported, complete_source_final_newline]
  rw [Bool.and_comm, C11AssertHeaderCuts.assertHeader_source_lex]
  rfl
end C11AssertHeaderActual
