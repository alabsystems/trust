-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderGuards
import C11GuardHeaderCuts
import C11GuardDirectiveCuts
namespace C11GuardHeaderActual
open C11HeaderGuards
open C11GuardHeaderCuts
theorem final_chunk_newline : uint32Full_chunk176.getLast? = some '\n' := by rfl
theorem last_175_177 : uint32Full_node_175_177_chars.getLast? = some '\n' := by
  rw [uint32Full_node_175_177_chars, List.getLast?_append, final_chunk_newline]
  rfl
theorem last_174_177 : uint32Full_node_174_177_chars.getLast? = some '\n' := by
  rw [uint32Full_node_174_177_chars, List.getLast?_append, last_175_177]
  rfl
theorem last_171_177 : uint32Full_node_171_177_chars.getLast? = some '\n' := by
  rw [uint32Full_node_171_177_chars, List.getLast?_append, last_174_177]
  rfl
theorem last_165_177 : uint32Full_node_165_177_chars.getLast? = some '\n' := by
  rw [uint32Full_node_165_177_chars, List.getLast?_append, last_171_177]
  rfl
theorem last_154_177 : uint32Full_node_154_177_chars.getLast? = some '\n' := by
  rw [uint32Full_node_154_177_chars, List.getLast?_append, last_165_177]
  rfl
theorem last_132_177 : uint32Full_node_132_177_chars.getLast? = some '\n' := by
  rw [uint32Full_node_132_177_chars, List.getLast?_append, last_154_177]
  rfl
theorem last_88_177 : uint32Full_node_88_177_chars.getLast? = some '\n' := by
  rw [uint32Full_node_88_177_chars, List.getLast?_append, last_132_177]
  rfl
theorem last_0_177 : uint32Full_node_0_177_chars.getLast? = some '\n' := by
  rw [uint32Full_node_0_177_chars, List.getLast?_append, last_88_177]
  rfl
theorem complete_source_final_newline : C11GuardHeaderData.uint32Full_0.toList.getLast? = some '\n' := by
  rw [← uint32Full_string_exact, uint32Full_node_0_177_characters]
  exact last_0_177

/-- Entire actual1415-byte SDKowner, not its manually selected declaration
or guard tail. Active output remains unexpanded and context/profileauth open. -/
theorem complete_header_first_include :
    (process [] C11GuardHeaderData.uint32Full_0).map (fun state =>
      (state.macros, state.reversedOutput.reverse, state.stack)) =
    some ([("_UINT32_T", [])], [["typedef", "unsigned", "int", "uint32_t", ";"]], []) := by
  unfold process
  rw [C11GuardDirectiveCuts.complete_source_supported]
  rw [complete_source_final_newline]
  rw [Bool.and_comm]
  rw [C11GuardHeaderCuts.uint32Full_source_lex]
  rfl

theorem complete_header_repeated_include :
    (process [("_UINT32_T", [])] C11GuardHeaderData.uint32Full_0).map (fun state =>
      (state.macros, state.reversedOutput, state.stack)) =
    some ([("_UINT32_T", [])], [], []) := by
  unfold process
  rw [C11GuardDirectiveCuts.complete_source_supported]
  rw [complete_source_final_newline]
  rw [Bool.and_comm]
  rw [C11GuardHeaderCuts.uint32Full_source_lex]
  rfl
/-- Presence, not replacement-value truth, controls #ifndef. -/
theorem predefined_zero_guard_still_skips :
    (processTokens [("_UINT32_T", ["0"])] C11GuardHeaderCuts.uint32Full_tokens).map
      (fun state => (state.macros, state.reversedOutput, state.stack)) =
    some ([("_UINT32_T", ["0"])], [], []) := by rfl

/-- A shortened proposed token stream cannot erase the closing-guard obligation.
The original complete-source lexical witness remains unchanged. -/
theorem omitted_closing_guard_refused :
    processTokens [] (C11GuardHeaderCuts.uint32Full_tokens.take
      (C11GuardHeaderCuts.uint32Full_tokens.length - 3)) = none := by rfl

end C11GuardHeaderActual
