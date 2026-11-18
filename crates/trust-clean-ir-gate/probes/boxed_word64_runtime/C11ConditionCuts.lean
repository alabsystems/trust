-- Copyright 2026 Andrew Yates | Apache-2.0
import C11DirectiveLexer
import C11ConditionData
import Init.Data.String.Lemmas.Basic
namespace C11ConditionCuts
open C11DirectiveLexer

def branch_state0 : Option State := some initial
def branch_chunk0 : List Char := [Char.ofNat 35, Char.ofNat 105, Char.ofNat 102, Char.ofNat 32, Char.ofNat 100, Char.ofNat 101, Char.ofNat 102, Char.ofNat 105]
def branch_state1 : Option State := some { base := { mode := .word, word := [Char.ofNat 105, Char.ofNat 102, Char.ofNat 101, Char.ofNat 100], reversed := ["if", "#"] }, pending := .none }
theorem branch_cut0 : feed (some initial) branch_chunk0 = branch_state1 := by rfl
def branch_chunk1 : List Char := [Char.ofNat 110, Char.ofNat 101, Char.ofNat 100, Char.ofNat 40, Char.ofNat 95, Char.ofNat 95, Char.ofNat 83, Char.ofNat 84]
def branch_state2 : Option State := some { base := { mode := .word, word := [Char.ofNat 84, Char.ofNat 83, Char.ofNat 95, Char.ofNat 95], reversed := ["(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut1 : feed branch_state1 branch_chunk1 = branch_state2 := by rfl
def branch_chunk2 : List Char := [Char.ofNat 68, Char.ofNat 67, Char.ofNat 95, Char.ofNat 86, Char.ofNat 69, Char.ofNat 82, Char.ofNat 83, Char.ofNat 73]
def branch_state3 : Option State := some { base := { mode := .word, word := [Char.ofNat 73, Char.ofNat 83, Char.ofNat 82, Char.ofNat 69, Char.ofNat 86, Char.ofNat 95, Char.ofNat 67, Char.ofNat 68, Char.ofNat 84, Char.ofNat 83, Char.ofNat 95, Char.ofNat 95], reversed := ["(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut2 : feed branch_state2 branch_chunk2 = branch_state3 := by rfl
def branch_chunk3 : List Char := [Char.ofNat 79, Char.ofNat 78, Char.ofNat 95, Char.ofNat 95, Char.ofNat 41, Char.ofNat 32, Char.ofNat 38, Char.ofNat 38]
def branch_state4 : Option State := some { base := { mode := .normal, word := [], reversed := ["&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut3 : feed branch_state3 branch_chunk3 = branch_state4 := by rfl
def branch_chunk4 : List Char := [Char.ofNat 32, Char.ofNat 95, Char.ofNat 95, Char.ofNat 83, Char.ofNat 84, Char.ofNat 68, Char.ofNat 67, Char.ofNat 95]
def branch_state5 : Option State := some { base := { mode := .word, word := [Char.ofNat 95, Char.ofNat 67, Char.ofNat 68, Char.ofNat 84, Char.ofNat 83, Char.ofNat 95, Char.ofNat 95], reversed := ["&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut4 : feed branch_state4 branch_chunk4 = branch_state5 := by rfl
def branch_chunk5 : List Char := [Char.ofNat 86, Char.ofNat 69, Char.ofNat 82, Char.ofNat 83, Char.ofNat 73, Char.ofNat 79, Char.ofNat 78, Char.ofNat 95]
def branch_state6 : Option State := some { base := { mode := .word, word := [Char.ofNat 95, Char.ofNat 78, Char.ofNat 79, Char.ofNat 73, Char.ofNat 83, Char.ofNat 82, Char.ofNat 69, Char.ofNat 86, Char.ofNat 95, Char.ofNat 67, Char.ofNat 68, Char.ofNat 84, Char.ofNat 83, Char.ofNat 95, Char.ofNat 95], reversed := ["&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut5 : feed branch_state5 branch_chunk5 = branch_state6 := by rfl
def branch_chunk6 : List Char := [Char.ofNat 95, Char.ofNat 32, Char.ofNat 62, Char.ofNat 32, Char.ofNat 50, Char.ofNat 48, Char.ofNat 49, Char.ofNat 55]
def branch_state7 : Option State := some { base := { mode := .word, word := [Char.ofNat 55, Char.ofNat 49, Char.ofNat 48, Char.ofNat 50], reversed := [">", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut6 : feed branch_state6 branch_chunk6 = branch_state7 := by rfl
def branch_chunk7 : List Char := [Char.ofNat 49, Char.ofNat 48, Char.ofNat 76, Char.ofNat 10, Char.ofNat 110, Char.ofNat 101, Char.ofNat 119, Char.ofNat 101]
def branch_state8 : Option State := some { base := { mode := .word, word := [Char.ofNat 101, Char.ofNat 119, Char.ofNat 101, Char.ofNat 110], reversed := ["\n", "201710L", ">", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut7 : feed branch_state7 branch_chunk7 = branch_state8 := by rfl
def branch_chunk8 : List Char := [Char.ofNat 114, Char.ofNat 10, Char.ofNat 35, Char.ofNat 101, Char.ofNat 108, Char.ofNat 105, Char.ofNat 102, Char.ofNat 32]
def branch_state9 : Option State := some { base := { mode := .normal, word := [], reversed := ["elif", "#", "\n", "newer", "\n", "201710L", ">", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut8 : feed branch_state8 branch_chunk8 = branch_state9 := by rfl
def branch_chunk9 : List Char := [Char.ofNat 33, Char.ofNat 100, Char.ofNat 101, Char.ofNat 102, Char.ofNat 105, Char.ofNat 110, Char.ofNat 101, Char.ofNat 100]
def branch_state10 : Option State := some { base := { mode := .word, word := [Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 105, Char.ofNat 102, Char.ofNat 101, Char.ofNat 100], reversed := ["!", "elif", "#", "\n", "newer", "\n", "201710L", ">", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut9 : feed branch_state9 branch_chunk9 = branch_state10 := by rfl
def branch_chunk10 : List Char := [Char.ofNat 40, Char.ofNat 95, Char.ofNat 95, Char.ofNat 99, Char.ofNat 112, Char.ofNat 108, Char.ofNat 117, Char.ofNat 115]
def branch_state11 : Option State := some { base := { mode := .word, word := [Char.ofNat 115, Char.ofNat 117, Char.ofNat 108, Char.ofNat 112, Char.ofNat 99, Char.ofNat 95, Char.ofNat 95], reversed := ["(", "defined", "!", "elif", "#", "\n", "newer", "\n", "201710L", ">", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut10 : feed branch_state10 branch_chunk10 = branch_state11 := by rfl
def branch_chunk11 : List Char := [Char.ofNat 112, Char.ofNat 108, Char.ofNat 117, Char.ofNat 115, Char.ofNat 41, Char.ofNat 10, Char.ofNat 115, Char.ofNat 101]
def branch_state12 : Option State := some { base := { mode := .word, word := [Char.ofNat 101, Char.ofNat 115], reversed := ["\n", ")", "__cplusplus", "(", "defined", "!", "elif", "#", "\n", "newer", "\n", "201710L", ">", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut11 : feed branch_state11 branch_chunk11 = branch_state12 := by rfl
def branch_chunk12 : List Char := [Char.ofNat 108, Char.ofNat 101, Char.ofNat 99, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100, Char.ofNat 10, Char.ofNat 35]
def branch_state13 : Option State := some { base := { mode := .hash, word := [], reversed := ["\n", "selected", "\n", ")", "__cplusplus", "(", "defined", "!", "elif", "#", "\n", "newer", "\n", "201710L", ">", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut12 : feed branch_state12 branch_chunk12 = branch_state13 := by rfl
def branch_chunk13 : List Char := [Char.ofNat 101, Char.ofNat 108, Char.ofNat 115, Char.ofNat 101, Char.ofNat 10, Char.ofNat 111, Char.ofNat 116, Char.ofNat 104]
def branch_state14 : Option State := some { base := { mode := .word, word := [Char.ofNat 104, Char.ofNat 116, Char.ofNat 111], reversed := ["\n", "else", "#", "\n", "selected", "\n", ")", "__cplusplus", "(", "defined", "!", "elif", "#", "\n", "newer", "\n", "201710L", ">", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut13 : feed branch_state13 branch_chunk13 = branch_state14 := by rfl
def branch_chunk14 : List Char := [Char.ofNat 101, Char.ofNat 114, Char.ofNat 10, Char.ofNat 35, Char.ofNat 101, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105]
def branch_state15 : Option State := some { base := { mode := .word, word := [Char.ofNat 105, Char.ofNat 100, Char.ofNat 110, Char.ofNat 101], reversed := ["#", "\n", "other", "\n", "else", "#", "\n", "selected", "\n", ")", "__cplusplus", "(", "defined", "!", "elif", "#", "\n", "newer", "\n", "201710L", ">", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut14 : feed branch_state14 branch_chunk14 = branch_state15 := by rfl
def branch_chunk15 : List Char := [Char.ofNat 102, Char.ofNat 10]
def branch_state16 : Option State := some { base := { mode := .normal, word := [], reversed := ["\n", "endif", "#", "\n", "other", "\n", "else", "#", "\n", "selected", "\n", ")", "__cplusplus", "(", "defined", "!", "elif", "#", "\n", "newer", "\n", "201710L", ">", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#"] }, pending := .none }
theorem branch_cut15 : feed branch_state15 branch_chunk15 = branch_state16 := by rfl
def branch_chunks : List (List Char) := [branch_chunk0, branch_chunk1, branch_chunk2, branch_chunk3, branch_chunk4, branch_chunk5, branch_chunk6, branch_chunk7, branch_chunk8, branch_chunk9, branch_chunk10, branch_chunk11, branch_chunk12, branch_chunk13, branch_chunk14, branch_chunk15]
def branch_tokens : List String := ["#", "if", "defined", "(", "__STDC_VERSION__", ")", "&&", "__STDC_VERSION__", ">", "201710L", "\n", "newer", "\n", "#", "elif", "!", "defined", "(", "__cplusplus", ")", "\n", "selected", "\n", "#", "else", "\n", "other", "\n", "#", "endif", "\n"]
theorem branch_characters_lex : tokenizeCharacters branch_chunks.flatten = some branch_tokens := by
  rw [← chunks_exact]
  simp only [tokenizeChunks, branch_chunks, List.foldl_cons, List.foldl_nil]
  rw [branch_cut0, branch_cut1, branch_cut2, branch_cut3, branch_cut4, branch_cut5, branch_cut6, branch_cut7, branch_cut8, branch_cut9, branch_cut10, branch_cut11, branch_cut12, branch_cut13, branch_cut14, branch_cut15]
  rfl
def branch_string_leaf0 : String := "#if defi"
theorem branch_chunk_chars0 : branch_string_leaf0.toList = branch_chunk0 := by rfl
def branch_string_leaf1 : String := "ned(__ST"
theorem branch_chunk_chars1 : branch_string_leaf1.toList = branch_chunk1 := by rfl
def branch_string_leaf2 : String := "DC_VERSI"
theorem branch_chunk_chars2 : branch_string_leaf2.toList = branch_chunk2 := by rfl
def branch_string_leaf3 : String := "ON__) &&"
theorem branch_chunk_chars3 : branch_string_leaf3.toList = branch_chunk3 := by rfl
def branch_string_leaf4 : String := " __STDC_"
theorem branch_chunk_chars4 : branch_string_leaf4.toList = branch_chunk4 := by rfl
def branch_string_leaf5 : String := "VERSION_"
theorem branch_chunk_chars5 : branch_string_leaf5.toList = branch_chunk5 := by rfl
def branch_string_leaf6 : String := "_ > 2017"
theorem branch_chunk_chars6 : branch_string_leaf6.toList = branch_chunk6 := by rfl
def branch_string_leaf7 : String := "10L\nnewe"
theorem branch_chunk_chars7 : branch_string_leaf7.toList = branch_chunk7 := by rfl
def branch_string_leaf8 : String := "r\n#elif "
theorem branch_chunk_chars8 : branch_string_leaf8.toList = branch_chunk8 := by rfl
def branch_string_leaf9 : String := "!defined"
theorem branch_chunk_chars9 : branch_string_leaf9.toList = branch_chunk9 := by rfl
def branch_string_leaf10 : String := "(__cplus"
theorem branch_chunk_chars10 : branch_string_leaf10.toList = branch_chunk10 := by rfl
def branch_string_leaf11 : String := "plus)\nse"
theorem branch_chunk_chars11 : branch_string_leaf11.toList = branch_chunk11 := by rfl
def branch_string_leaf12 : String := "lected\n#"
theorem branch_chunk_chars12 : branch_string_leaf12.toList = branch_chunk12 := by rfl
def branch_string_leaf13 : String := "else\noth"
theorem branch_chunk_chars13 : branch_string_leaf13.toList = branch_chunk13 := by rfl
def branch_string_leaf14 : String := "er\n#endi"
theorem branch_chunk_chars14 : branch_string_leaf14.toList = branch_chunk14 := by rfl
def branch_string_leaf15 : String := "f\n"
theorem branch_chunk_chars15 : branch_string_leaf15.toList = branch_chunk15 := by rfl
def branch_parts_leaf0 : List (List Char) := [branch_chunk0]
theorem branch_parts_leaf0_flatten : branch_chunk0 = branch_parts_leaf0.flatten := by
  simp only [branch_parts_leaf0, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_parts_leaf1 : List (List Char) := [branch_chunk1]
theorem branch_parts_leaf1_flatten : branch_chunk1 = branch_parts_leaf1.flatten := by
  simp only [branch_parts_leaf1, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_node_0_2 : String := branch_string_leaf0 ++ branch_string_leaf1
def branch_node_0_2_chars : List Char := branch_chunk0 ++ branch_chunk1
theorem branch_node_0_2_literal : branch_node_0_2 = "#if defined(__ST" := by
  unfold branch_node_0_2
  cbv
theorem branch_node_0_2_characters : branch_node_0_2.toList = branch_node_0_2_chars := by
  unfold branch_node_0_2 branch_node_0_2_chars
  rw [String.toList_append, branch_chunk_chars0, branch_chunk_chars1]
def branch_node_0_2_parts : List (List Char) := branch_parts_leaf0 ++ branch_parts_leaf1
theorem branch_node_0_2_parts_literal : branch_node_0_2_parts = [branch_chunk0, branch_chunk1] := by
  unfold branch_node_0_2_parts
  rfl
theorem branch_node_0_2_parts_flatten : branch_node_0_2_chars = branch_node_0_2_parts.flatten := by
  unfold branch_node_0_2_chars branch_node_0_2_parts
  rw [List.flatten_append, ← branch_parts_leaf0_flatten, ← branch_parts_leaf1_flatten]
def branch_parts_leaf2 : List (List Char) := [branch_chunk2]
theorem branch_parts_leaf2_flatten : branch_chunk2 = branch_parts_leaf2.flatten := by
  simp only [branch_parts_leaf2, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_parts_leaf3 : List (List Char) := [branch_chunk3]
theorem branch_parts_leaf3_flatten : branch_chunk3 = branch_parts_leaf3.flatten := by
  simp only [branch_parts_leaf3, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_node_2_4 : String := branch_string_leaf2 ++ branch_string_leaf3
def branch_node_2_4_chars : List Char := branch_chunk2 ++ branch_chunk3
theorem branch_node_2_4_literal : branch_node_2_4 = "DC_VERSION__) &&" := by
  unfold branch_node_2_4
  cbv
theorem branch_node_2_4_characters : branch_node_2_4.toList = branch_node_2_4_chars := by
  unfold branch_node_2_4 branch_node_2_4_chars
  rw [String.toList_append, branch_chunk_chars2, branch_chunk_chars3]
def branch_node_2_4_parts : List (List Char) := branch_parts_leaf2 ++ branch_parts_leaf3
theorem branch_node_2_4_parts_literal : branch_node_2_4_parts = [branch_chunk2, branch_chunk3] := by
  unfold branch_node_2_4_parts
  rfl
theorem branch_node_2_4_parts_flatten : branch_node_2_4_chars = branch_node_2_4_parts.flatten := by
  unfold branch_node_2_4_chars branch_node_2_4_parts
  rw [List.flatten_append, ← branch_parts_leaf2_flatten, ← branch_parts_leaf3_flatten]
def branch_node_0_4 : String := branch_node_0_2 ++ branch_node_2_4
def branch_node_0_4_chars : List Char := branch_node_0_2_chars ++ branch_node_2_4_chars
theorem branch_node_0_4_literal : branch_node_0_4 = "#if defined(__STDC_VERSION__) &&" := by
  unfold branch_node_0_4
  rw [branch_node_0_2_literal]
  rw [branch_node_2_4_literal]
  cbv
theorem branch_node_0_4_characters : branch_node_0_4.toList = branch_node_0_4_chars := by
  unfold branch_node_0_4 branch_node_0_4_chars
  rw [String.toList_append, branch_node_0_2_characters, branch_node_2_4_characters]
def branch_node_0_4_parts : List (List Char) := branch_node_0_2_parts ++ branch_node_2_4_parts
theorem branch_node_0_4_parts_literal : branch_node_0_4_parts = [branch_chunk0, branch_chunk1, branch_chunk2, branch_chunk3] := by
  unfold branch_node_0_4_parts
  rw [branch_node_0_2_parts_literal]
  rw [branch_node_2_4_parts_literal]
  rfl
theorem branch_node_0_4_parts_flatten : branch_node_0_4_chars = branch_node_0_4_parts.flatten := by
  unfold branch_node_0_4_chars branch_node_0_4_parts
  rw [List.flatten_append, ← branch_node_0_2_parts_flatten, ← branch_node_2_4_parts_flatten]
def branch_parts_leaf4 : List (List Char) := [branch_chunk4]
theorem branch_parts_leaf4_flatten : branch_chunk4 = branch_parts_leaf4.flatten := by
  simp only [branch_parts_leaf4, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_parts_leaf5 : List (List Char) := [branch_chunk5]
theorem branch_parts_leaf5_flatten : branch_chunk5 = branch_parts_leaf5.flatten := by
  simp only [branch_parts_leaf5, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_node_4_6 : String := branch_string_leaf4 ++ branch_string_leaf5
def branch_node_4_6_chars : List Char := branch_chunk4 ++ branch_chunk5
theorem branch_node_4_6_literal : branch_node_4_6 = " __STDC_VERSION_" := by
  unfold branch_node_4_6
  cbv
theorem branch_node_4_6_characters : branch_node_4_6.toList = branch_node_4_6_chars := by
  unfold branch_node_4_6 branch_node_4_6_chars
  rw [String.toList_append, branch_chunk_chars4, branch_chunk_chars5]
def branch_node_4_6_parts : List (List Char) := branch_parts_leaf4 ++ branch_parts_leaf5
theorem branch_node_4_6_parts_literal : branch_node_4_6_parts = [branch_chunk4, branch_chunk5] := by
  unfold branch_node_4_6_parts
  rfl
theorem branch_node_4_6_parts_flatten : branch_node_4_6_chars = branch_node_4_6_parts.flatten := by
  unfold branch_node_4_6_chars branch_node_4_6_parts
  rw [List.flatten_append, ← branch_parts_leaf4_flatten, ← branch_parts_leaf5_flatten]
def branch_parts_leaf6 : List (List Char) := [branch_chunk6]
theorem branch_parts_leaf6_flatten : branch_chunk6 = branch_parts_leaf6.flatten := by
  simp only [branch_parts_leaf6, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_parts_leaf7 : List (List Char) := [branch_chunk7]
theorem branch_parts_leaf7_flatten : branch_chunk7 = branch_parts_leaf7.flatten := by
  simp only [branch_parts_leaf7, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_node_6_8 : String := branch_string_leaf6 ++ branch_string_leaf7
def branch_node_6_8_chars : List Char := branch_chunk6 ++ branch_chunk7
theorem branch_node_6_8_literal : branch_node_6_8 = "_ > 201710L\nnewe" := by
  unfold branch_node_6_8
  cbv
theorem branch_node_6_8_characters : branch_node_6_8.toList = branch_node_6_8_chars := by
  unfold branch_node_6_8 branch_node_6_8_chars
  rw [String.toList_append, branch_chunk_chars6, branch_chunk_chars7]
def branch_node_6_8_parts : List (List Char) := branch_parts_leaf6 ++ branch_parts_leaf7
theorem branch_node_6_8_parts_literal : branch_node_6_8_parts = [branch_chunk6, branch_chunk7] := by
  unfold branch_node_6_8_parts
  rfl
theorem branch_node_6_8_parts_flatten : branch_node_6_8_chars = branch_node_6_8_parts.flatten := by
  unfold branch_node_6_8_chars branch_node_6_8_parts
  rw [List.flatten_append, ← branch_parts_leaf6_flatten, ← branch_parts_leaf7_flatten]
def branch_node_4_8 : String := branch_node_4_6 ++ branch_node_6_8
def branch_node_4_8_chars : List Char := branch_node_4_6_chars ++ branch_node_6_8_chars
theorem branch_node_4_8_literal : branch_node_4_8 = " __STDC_VERSION__ > 201710L\nnewe" := by
  unfold branch_node_4_8
  rw [branch_node_4_6_literal]
  rw [branch_node_6_8_literal]
  cbv
theorem branch_node_4_8_characters : branch_node_4_8.toList = branch_node_4_8_chars := by
  unfold branch_node_4_8 branch_node_4_8_chars
  rw [String.toList_append, branch_node_4_6_characters, branch_node_6_8_characters]
def branch_node_4_8_parts : List (List Char) := branch_node_4_6_parts ++ branch_node_6_8_parts
theorem branch_node_4_8_parts_literal : branch_node_4_8_parts = [branch_chunk4, branch_chunk5, branch_chunk6, branch_chunk7] := by
  unfold branch_node_4_8_parts
  rw [branch_node_4_6_parts_literal]
  rw [branch_node_6_8_parts_literal]
  rfl
theorem branch_node_4_8_parts_flatten : branch_node_4_8_chars = branch_node_4_8_parts.flatten := by
  unfold branch_node_4_8_chars branch_node_4_8_parts
  rw [List.flatten_append, ← branch_node_4_6_parts_flatten, ← branch_node_6_8_parts_flatten]
def branch_node_0_8 : String := branch_node_0_4 ++ branch_node_4_8
def branch_node_0_8_chars : List Char := branch_node_0_4_chars ++ branch_node_4_8_chars
theorem branch_node_0_8_literal : branch_node_0_8 = "#if defined(__STDC_VERSION__) && __STDC_VERSION__ > 201710L\nnewe" := by
  unfold branch_node_0_8
  rw [branch_node_0_4_literal]
  rw [branch_node_4_8_literal]
  cbv
theorem branch_node_0_8_characters : branch_node_0_8.toList = branch_node_0_8_chars := by
  unfold branch_node_0_8 branch_node_0_8_chars
  rw [String.toList_append, branch_node_0_4_characters, branch_node_4_8_characters]
def branch_node_0_8_parts : List (List Char) := branch_node_0_4_parts ++ branch_node_4_8_parts
theorem branch_node_0_8_parts_literal : branch_node_0_8_parts = [branch_chunk0, branch_chunk1, branch_chunk2, branch_chunk3, branch_chunk4, branch_chunk5, branch_chunk6, branch_chunk7] := by
  unfold branch_node_0_8_parts
  rw [branch_node_0_4_parts_literal]
  rw [branch_node_4_8_parts_literal]
  rfl
theorem branch_node_0_8_parts_flatten : branch_node_0_8_chars = branch_node_0_8_parts.flatten := by
  unfold branch_node_0_8_chars branch_node_0_8_parts
  rw [List.flatten_append, ← branch_node_0_4_parts_flatten, ← branch_node_4_8_parts_flatten]
def branch_parts_leaf8 : List (List Char) := [branch_chunk8]
theorem branch_parts_leaf8_flatten : branch_chunk8 = branch_parts_leaf8.flatten := by
  simp only [branch_parts_leaf8, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_parts_leaf9 : List (List Char) := [branch_chunk9]
theorem branch_parts_leaf9_flatten : branch_chunk9 = branch_parts_leaf9.flatten := by
  simp only [branch_parts_leaf9, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_node_8_10 : String := branch_string_leaf8 ++ branch_string_leaf9
def branch_node_8_10_chars : List Char := branch_chunk8 ++ branch_chunk9
theorem branch_node_8_10_literal : branch_node_8_10 = "r\n#elif !defined" := by
  unfold branch_node_8_10
  cbv
theorem branch_node_8_10_characters : branch_node_8_10.toList = branch_node_8_10_chars := by
  unfold branch_node_8_10 branch_node_8_10_chars
  rw [String.toList_append, branch_chunk_chars8, branch_chunk_chars9]
def branch_node_8_10_parts : List (List Char) := branch_parts_leaf8 ++ branch_parts_leaf9
theorem branch_node_8_10_parts_literal : branch_node_8_10_parts = [branch_chunk8, branch_chunk9] := by
  unfold branch_node_8_10_parts
  rfl
theorem branch_node_8_10_parts_flatten : branch_node_8_10_chars = branch_node_8_10_parts.flatten := by
  unfold branch_node_8_10_chars branch_node_8_10_parts
  rw [List.flatten_append, ← branch_parts_leaf8_flatten, ← branch_parts_leaf9_flatten]
def branch_parts_leaf10 : List (List Char) := [branch_chunk10]
theorem branch_parts_leaf10_flatten : branch_chunk10 = branch_parts_leaf10.flatten := by
  simp only [branch_parts_leaf10, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_parts_leaf11 : List (List Char) := [branch_chunk11]
theorem branch_parts_leaf11_flatten : branch_chunk11 = branch_parts_leaf11.flatten := by
  simp only [branch_parts_leaf11, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_node_10_12 : String := branch_string_leaf10 ++ branch_string_leaf11
def branch_node_10_12_chars : List Char := branch_chunk10 ++ branch_chunk11
theorem branch_node_10_12_literal : branch_node_10_12 = "(__cplusplus)\nse" := by
  unfold branch_node_10_12
  cbv
theorem branch_node_10_12_characters : branch_node_10_12.toList = branch_node_10_12_chars := by
  unfold branch_node_10_12 branch_node_10_12_chars
  rw [String.toList_append, branch_chunk_chars10, branch_chunk_chars11]
def branch_node_10_12_parts : List (List Char) := branch_parts_leaf10 ++ branch_parts_leaf11
theorem branch_node_10_12_parts_literal : branch_node_10_12_parts = [branch_chunk10, branch_chunk11] := by
  unfold branch_node_10_12_parts
  rfl
theorem branch_node_10_12_parts_flatten : branch_node_10_12_chars = branch_node_10_12_parts.flatten := by
  unfold branch_node_10_12_chars branch_node_10_12_parts
  rw [List.flatten_append, ← branch_parts_leaf10_flatten, ← branch_parts_leaf11_flatten]
def branch_node_8_12 : String := branch_node_8_10 ++ branch_node_10_12
def branch_node_8_12_chars : List Char := branch_node_8_10_chars ++ branch_node_10_12_chars
theorem branch_node_8_12_literal : branch_node_8_12 = "r\n#elif !defined(__cplusplus)\nse" := by
  unfold branch_node_8_12
  rw [branch_node_8_10_literal]
  rw [branch_node_10_12_literal]
  cbv
theorem branch_node_8_12_characters : branch_node_8_12.toList = branch_node_8_12_chars := by
  unfold branch_node_8_12 branch_node_8_12_chars
  rw [String.toList_append, branch_node_8_10_characters, branch_node_10_12_characters]
def branch_node_8_12_parts : List (List Char) := branch_node_8_10_parts ++ branch_node_10_12_parts
theorem branch_node_8_12_parts_literal : branch_node_8_12_parts = [branch_chunk8, branch_chunk9, branch_chunk10, branch_chunk11] := by
  unfold branch_node_8_12_parts
  rw [branch_node_8_10_parts_literal]
  rw [branch_node_10_12_parts_literal]
  rfl
theorem branch_node_8_12_parts_flatten : branch_node_8_12_chars = branch_node_8_12_parts.flatten := by
  unfold branch_node_8_12_chars branch_node_8_12_parts
  rw [List.flatten_append, ← branch_node_8_10_parts_flatten, ← branch_node_10_12_parts_flatten]
def branch_parts_leaf12 : List (List Char) := [branch_chunk12]
theorem branch_parts_leaf12_flatten : branch_chunk12 = branch_parts_leaf12.flatten := by
  simp only [branch_parts_leaf12, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_parts_leaf13 : List (List Char) := [branch_chunk13]
theorem branch_parts_leaf13_flatten : branch_chunk13 = branch_parts_leaf13.flatten := by
  simp only [branch_parts_leaf13, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_node_12_14 : String := branch_string_leaf12 ++ branch_string_leaf13
def branch_node_12_14_chars : List Char := branch_chunk12 ++ branch_chunk13
theorem branch_node_12_14_literal : branch_node_12_14 = "lected\n#else\noth" := by
  unfold branch_node_12_14
  cbv
theorem branch_node_12_14_characters : branch_node_12_14.toList = branch_node_12_14_chars := by
  unfold branch_node_12_14 branch_node_12_14_chars
  rw [String.toList_append, branch_chunk_chars12, branch_chunk_chars13]
def branch_node_12_14_parts : List (List Char) := branch_parts_leaf12 ++ branch_parts_leaf13
theorem branch_node_12_14_parts_literal : branch_node_12_14_parts = [branch_chunk12, branch_chunk13] := by
  unfold branch_node_12_14_parts
  rfl
theorem branch_node_12_14_parts_flatten : branch_node_12_14_chars = branch_node_12_14_parts.flatten := by
  unfold branch_node_12_14_chars branch_node_12_14_parts
  rw [List.flatten_append, ← branch_parts_leaf12_flatten, ← branch_parts_leaf13_flatten]
def branch_parts_leaf14 : List (List Char) := [branch_chunk14]
theorem branch_parts_leaf14_flatten : branch_chunk14 = branch_parts_leaf14.flatten := by
  simp only [branch_parts_leaf14, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_parts_leaf15 : List (List Char) := [branch_chunk15]
theorem branch_parts_leaf15_flatten : branch_chunk15 = branch_parts_leaf15.flatten := by
  simp only [branch_parts_leaf15, List.flatten_cons, List.flatten_nil, List.append_nil]
def branch_node_14_16 : String := branch_string_leaf14 ++ branch_string_leaf15
def branch_node_14_16_chars : List Char := branch_chunk14 ++ branch_chunk15
theorem branch_node_14_16_literal : branch_node_14_16 = "er\n#endif\n" := by
  unfold branch_node_14_16
  cbv
theorem branch_node_14_16_characters : branch_node_14_16.toList = branch_node_14_16_chars := by
  unfold branch_node_14_16 branch_node_14_16_chars
  rw [String.toList_append, branch_chunk_chars14, branch_chunk_chars15]
def branch_node_14_16_parts : List (List Char) := branch_parts_leaf14 ++ branch_parts_leaf15
theorem branch_node_14_16_parts_literal : branch_node_14_16_parts = [branch_chunk14, branch_chunk15] := by
  unfold branch_node_14_16_parts
  rfl
theorem branch_node_14_16_parts_flatten : branch_node_14_16_chars = branch_node_14_16_parts.flatten := by
  unfold branch_node_14_16_chars branch_node_14_16_parts
  rw [List.flatten_append, ← branch_parts_leaf14_flatten, ← branch_parts_leaf15_flatten]
def branch_node_12_16 : String := branch_node_12_14 ++ branch_node_14_16
def branch_node_12_16_chars : List Char := branch_node_12_14_chars ++ branch_node_14_16_chars
theorem branch_node_12_16_literal : branch_node_12_16 = "lected\n#else\nother\n#endif\n" := by
  unfold branch_node_12_16
  rw [branch_node_12_14_literal]
  rw [branch_node_14_16_literal]
  cbv
theorem branch_node_12_16_characters : branch_node_12_16.toList = branch_node_12_16_chars := by
  unfold branch_node_12_16 branch_node_12_16_chars
  rw [String.toList_append, branch_node_12_14_characters, branch_node_14_16_characters]
def branch_node_12_16_parts : List (List Char) := branch_node_12_14_parts ++ branch_node_14_16_parts
theorem branch_node_12_16_parts_literal : branch_node_12_16_parts = [branch_chunk12, branch_chunk13, branch_chunk14, branch_chunk15] := by
  unfold branch_node_12_16_parts
  rw [branch_node_12_14_parts_literal]
  rw [branch_node_14_16_parts_literal]
  rfl
theorem branch_node_12_16_parts_flatten : branch_node_12_16_chars = branch_node_12_16_parts.flatten := by
  unfold branch_node_12_16_chars branch_node_12_16_parts
  rw [List.flatten_append, ← branch_node_12_14_parts_flatten, ← branch_node_14_16_parts_flatten]
def branch_node_8_16 : String := branch_node_8_12 ++ branch_node_12_16
def branch_node_8_16_chars : List Char := branch_node_8_12_chars ++ branch_node_12_16_chars
theorem branch_node_8_16_literal : branch_node_8_16 = "r\n#elif !defined(__cplusplus)\nselected\n#else\nother\n#endif\n" := by
  unfold branch_node_8_16
  rw [branch_node_8_12_literal]
  rw [branch_node_12_16_literal]
  cbv
theorem branch_node_8_16_characters : branch_node_8_16.toList = branch_node_8_16_chars := by
  unfold branch_node_8_16 branch_node_8_16_chars
  rw [String.toList_append, branch_node_8_12_characters, branch_node_12_16_characters]
def branch_node_8_16_parts : List (List Char) := branch_node_8_12_parts ++ branch_node_12_16_parts
theorem branch_node_8_16_parts_literal : branch_node_8_16_parts = [branch_chunk8, branch_chunk9, branch_chunk10, branch_chunk11, branch_chunk12, branch_chunk13, branch_chunk14, branch_chunk15] := by
  unfold branch_node_8_16_parts
  rw [branch_node_8_12_parts_literal]
  rw [branch_node_12_16_parts_literal]
  rfl
theorem branch_node_8_16_parts_flatten : branch_node_8_16_chars = branch_node_8_16_parts.flatten := by
  unfold branch_node_8_16_chars branch_node_8_16_parts
  rw [List.flatten_append, ← branch_node_8_12_parts_flatten, ← branch_node_12_16_parts_flatten]
def branch_node_0_16 : String := branch_node_0_8 ++ branch_node_8_16
def branch_node_0_16_chars : List Char := branch_node_0_8_chars ++ branch_node_8_16_chars
theorem branch_node_0_16_literal : branch_node_0_16 = "#if defined(__STDC_VERSION__) && __STDC_VERSION__ > 201710L\nnewer\n#elif !defined(__cplusplus)\nselected\n#else\nother\n#endif\n" := by
  unfold branch_node_0_16
  rw [branch_node_0_8_literal]
  rw [branch_node_8_16_literal]
  cbv
theorem branch_node_0_16_characters : branch_node_0_16.toList = branch_node_0_16_chars := by
  unfold branch_node_0_16 branch_node_0_16_chars
  rw [String.toList_append, branch_node_0_8_characters, branch_node_8_16_characters]
def branch_node_0_16_parts : List (List Char) := branch_node_0_8_parts ++ branch_node_8_16_parts
theorem branch_node_0_16_parts_literal : branch_node_0_16_parts = [branch_chunk0, branch_chunk1, branch_chunk2, branch_chunk3, branch_chunk4, branch_chunk5, branch_chunk6, branch_chunk7, branch_chunk8, branch_chunk9, branch_chunk10, branch_chunk11, branch_chunk12, branch_chunk13, branch_chunk14, branch_chunk15] := by
  unfold branch_node_0_16_parts
  rw [branch_node_0_8_parts_literal]
  rw [branch_node_8_16_parts_literal]
  rfl
theorem branch_node_0_16_parts_flatten : branch_node_0_16_chars = branch_node_0_16_parts.flatten := by
  unfold branch_node_0_16_chars branch_node_0_16_parts
  rw [List.flatten_append, ← branch_node_0_8_parts_flatten, ← branch_node_8_16_parts_flatten]
theorem branch_string_exact : branch_node_0_16 = C11ConditionData.branch_0 := by
  exact branch_node_0_16_literal
theorem branch_flatten_exact : branch_node_0_16_chars = branch_chunks.flatten := by
  rw [branch_node_0_16_parts_flatten, branch_node_0_16_parts_literal]
  rfl
theorem branch_source_lex : tokenize C11ConditionData.branch_0 = some branch_tokens := by
  unfold tokenize
  rw [← branch_string_exact, branch_node_0_16_characters, branch_flatten_exact]
  exact branch_characters_lex

end C11ConditionCuts
