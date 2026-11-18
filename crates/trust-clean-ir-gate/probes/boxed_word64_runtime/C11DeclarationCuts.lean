-- Copyright 2026 Andrew Yates | Apache-2.0
import C11DeclarationLexer
import C11ActualDeclarationData
import Init.Data.String.Lemmas.Basic
namespace C11DeclarationCuts
open C11DeclarationLexer

def clean_obj_header_state0 : Option State := some initial
def clean_obj_header_chunk0 : List Char := [Char.ofNat 116, Char.ofNat 121, Char.ofNat 112, Char.ofNat 101, Char.ofNat 100, Char.ofNat 101, Char.ofNat 102, Char.ofNat 32]
def clean_obj_header_state1 : Option State := some { mode := .normal, word := [], reversed := ["typedef"] }
theorem clean_obj_header_cut0 : feed (some initial) clean_obj_header_chunk0 = clean_obj_header_state1 := by rfl
def clean_obj_header_chunk1 : List Char := [Char.ofNat 115, Char.ofNat 116, Char.ofNat 114, Char.ofNat 117, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 99]
def clean_obj_header_state2 : Option State := some { mode := .word, word := [Char.ofNat 99], reversed := ["struct", "typedef"] }
theorem clean_obj_header_cut1 : feed clean_obj_header_state1 clean_obj_header_chunk1 = clean_obj_header_state2 := by rfl
def clean_obj_header_chunk2 : List Char := [Char.ofNat 108, Char.ofNat 101, Char.ofNat 97, Char.ofNat 110, Char.ofNat 95, Char.ofNat 111, Char.ofNat 98, Char.ofNat 106]
def clean_obj_header_state3 : Option State := some { mode := .word, word := [Char.ofNat 106, Char.ofNat 98, Char.ofNat 111, Char.ofNat 95, Char.ofNat 110, Char.ofNat 97, Char.ofNat 101, Char.ofNat 108, Char.ofNat 99], reversed := ["struct", "typedef"] }
theorem clean_obj_header_cut2 : feed clean_obj_header_state2 clean_obj_header_chunk2 = clean_obj_header_state3 := by rfl
def clean_obj_header_chunk3 : List Char := [Char.ofNat 95, Char.ofNat 104, Char.ofNat 101, Char.ofNat 97, Char.ofNat 100, Char.ofNat 101, Char.ofNat 114, Char.ofNat 32]
def clean_obj_header_state4 : Option State := some { mode := .normal, word := [], reversed := ["clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut3 : feed clean_obj_header_state3 clean_obj_header_chunk3 = clean_obj_header_state4 := by rfl
def clean_obj_header_chunk4 : List Char := [Char.ofNat 123, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 95, Char.ofNat 65]
def clean_obj_header_state5 : Option State := some { mode := .word, word := [Char.ofNat 65, Char.ofNat 95], reversed := ["\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut4 : feed clean_obj_header_state4 clean_obj_header_chunk4 = clean_obj_header_state5 := by rfl
def clean_obj_header_chunk5 : List Char := [Char.ofNat 116, Char.ofNat 111, Char.ofNat 109, Char.ofNat 105, Char.ofNat 99, Char.ofNat 32, Char.ofNat 117, Char.ofNat 105]
def clean_obj_header_state6 : Option State := some { mode := .word, word := [Char.ofNat 105, Char.ofNat 117], reversed := ["_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut5 : feed clean_obj_header_state5 clean_obj_header_chunk5 = clean_obj_header_state6 := by rfl
def clean_obj_header_chunk6 : List Char := [Char.ofNat 110, Char.ofNat 116, Char.ofNat 51, Char.ofNat 50, Char.ofNat 95, Char.ofNat 116, Char.ofNat 32, Char.ofNat 114]
def clean_obj_header_state7 : Option State := some { mode := .word, word := [Char.ofNat 114], reversed := ["uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut6 : feed clean_obj_header_state6 clean_obj_header_chunk6 = clean_obj_header_state7 := by rfl
def clean_obj_header_chunk7 : List Char := [Char.ofNat 101, Char.ofNat 102, Char.ofNat 95, Char.ofNat 99, Char.ofNat 111, Char.ofNat 117, Char.ofNat 110, Char.ofNat 116]
def clean_obj_header_state8 : Option State := some { mode := .word, word := [Char.ofNat 116, Char.ofNat 110, Char.ofNat 117, Char.ofNat 111, Char.ofNat 99, Char.ofNat 95, Char.ofNat 102, Char.ofNat 101, Char.ofNat 114], reversed := ["uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut7 : feed clean_obj_header_state7 clean_obj_header_chunk7 = clean_obj_header_state8 := by rfl
def clean_obj_header_chunk8 : List Char := [Char.ofNat 59, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 117, Char.ofNat 105]
def clean_obj_header_state9 : Option State := some { mode := .word, word := [Char.ofNat 105, Char.ofNat 117], reversed := ["\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut8 : feed clean_obj_header_state8 clean_obj_header_chunk8 = clean_obj_header_state9 := by rfl
def clean_obj_header_chunk9 : List Char := [Char.ofNat 110, Char.ofNat 116, Char.ofNat 56, Char.ofNat 95, Char.ofNat 116, Char.ofNat 32, Char.ofNat 116, Char.ofNat 97]
def clean_obj_header_state10 : Option State := some { mode := .word, word := [Char.ofNat 97, Char.ofNat 116], reversed := ["uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut9 : feed clean_obj_header_state9 clean_obj_header_chunk9 = clean_obj_header_state10 := by rfl
def clean_obj_header_chunk10 : List Char := [Char.ofNat 103, Char.ofNat 59, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 117]
def clean_obj_header_state11 : Option State := some { mode := .word, word := [Char.ofNat 117], reversed := ["\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut10 : feed clean_obj_header_state10 clean_obj_header_chunk10 = clean_obj_header_state11 := by rfl
def clean_obj_header_chunk11 : List Char := [Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 56, Char.ofNat 95, Char.ofNat 116, Char.ofNat 32, Char.ofNat 107]
def clean_obj_header_state12 : Option State := some { mode := .word, word := [Char.ofNat 107], reversed := ["uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut11 : feed clean_obj_header_state11 clean_obj_header_chunk11 = clean_obj_header_state12 := by rfl
def clean_obj_header_chunk12 : List Char := [Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 59, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32]
def clean_obj_header_state13 : Option State := some { mode := .normal, word := [], reversed := ["\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut12 : feed clean_obj_header_state12 clean_obj_header_chunk12 = clean_obj_header_state13 := by rfl
def clean_obj_header_chunk13 : List Char := [Char.ofNat 32, Char.ofNat 117, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 56, Char.ofNat 95, Char.ofNat 116]
def clean_obj_header_state14 : Option State := some { mode := .word, word := [Char.ofNat 116, Char.ofNat 95, Char.ofNat 56, Char.ofNat 116, Char.ofNat 110, Char.ofNat 105, Char.ofNat 117], reversed := ["\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut13 : feed clean_obj_header_state13 clean_obj_header_chunk13 = clean_obj_header_state14 := by rfl
def clean_obj_header_chunk14 : List Char := [Char.ofNat 32, Char.ofNat 110, Char.ofNat 117, Char.ofNat 109, Char.ofNat 95, Char.ofNat 111, Char.ofNat 98, Char.ofNat 106]
def clean_obj_header_state15 : Option State := some { mode := .word, word := [Char.ofNat 106, Char.ofNat 98, Char.ofNat 111, Char.ofNat 95, Char.ofNat 109, Char.ofNat 117, Char.ofNat 110], reversed := ["uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut14 : feed clean_obj_header_state14 clean_obj_header_chunk14 = clean_obj_header_state15 := by rfl
def clean_obj_header_chunk15 : List Char := [Char.ofNat 115, Char.ofNat 59, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 47, Char.ofNat 42, Char.ofNat 32]
def clean_obj_header_state16 : Option State := some { mode := .block, word := [], reversed := [";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut15 : feed clean_obj_header_state15 clean_obj_header_chunk15 = clean_obj_header_state16 := by rfl
def clean_obj_header_chunk16 : List Char := [Char.ofNat 119, Char.ofNat 97, Char.ofNat 115, Char.ofNat 32, Char.ofNat 117, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]
def clean_obj_header_state17 : Option State := some { mode := .block, word := [], reversed := [";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut16 : feed clean_obj_header_state16 clean_obj_header_chunk16 = clean_obj_header_state17 := by rfl
def clean_obj_header_chunk17 : List Char := [Char.ofNat 49, Char.ofNat 54, Char.ofNat 95, Char.ofNat 116, Char.ofNat 32, Char.ofNat 8212, Char.ofNat 32, Char.ofNat 110]
def clean_obj_header_state18 : Option State := some { mode := .block, word := [], reversed := [";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut17 : feed clean_obj_header_state17 clean_obj_header_chunk17 = clean_obj_header_state18 := by rfl
def clean_obj_header_chunk18 : List Char := [Char.ofNat 111, Char.ofNat 119, Char.ofNat 32, Char.ofNat 117, Char.ofNat 56, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97]
def clean_obj_header_state19 : Option State := some { mode := .block, word := [], reversed := [";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut18 : feed clean_obj_header_state18 clean_obj_header_chunk18 = clean_obj_header_state19 := by rfl
def clean_obj_header_chunk19 : List Char := [Char.ofNat 116, Char.ofNat 99, Char.ofNat 104, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 32, Char.ofNat 76]
def clean_obj_header_state20 : Option State := some { mode := .block, word := [], reversed := [";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut19 : feed clean_obj_header_state19 clean_obj_header_chunk19 = clean_obj_header_state20 := by rfl
def clean_obj_header_chunk20 : List Char := [Char.ofNat 101, Char.ofNat 97, Char.ofNat 110, Char.ofNat 32, Char.ofNat 52, Char.ofNat 32, Char.ofNat 109, Char.ofNat 95]
def clean_obj_header_state21 : Option State := some { mode := .block, word := [], reversed := [";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut20 : feed clean_obj_header_state20 clean_obj_header_chunk20 = clean_obj_header_state21 := by rfl
def clean_obj_header_chunk21 : List Char := [Char.ofNat 111, Char.ofNat 116, Char.ofNat 104, Char.ofNat 101, Char.ofNat 114, Char.ofNat 32, Char.ofNat 40, Char.ofNat 80]
def clean_obj_header_state22 : Option State := some { mode := .block, word := [], reversed := [";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut21 : feed clean_obj_header_state21 clean_obj_header_chunk21 = clean_obj_header_state22 := by rfl
def clean_obj_header_chunk22 : List Char := [Char.ofNat 97, Char.ofNat 114, Char.ofNat 116, Char.ofNat 32, Char.ofNat 111, Char.ofNat 102, Char.ofNat 32, Char.ofNat 35]
def clean_obj_header_state23 : Option State := some { mode := .block, word := [], reversed := [";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut22 : feed clean_obj_header_state22 clean_obj_header_chunk22 = clean_obj_header_state23 := by rfl
def clean_obj_header_chunk23 : List Char := [Char.ofNat 49, Char.ofNat 57, Char.ofNat 57, Char.ofNat 48, Char.ofNat 41, Char.ofNat 32, Char.ofNat 42, Char.ofNat 47]
def clean_obj_header_state24 : Option State := some { mode := .normal, word := [], reversed := [";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut23 : feed clean_obj_header_state23 clean_obj_header_chunk23 = clean_obj_header_state24 := by rfl
def clean_obj_header_chunk24 : List Char := [Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 117, Char.ofNat 105, Char.ofNat 110]
def clean_obj_header_state25 : Option State := some { mode := .word, word := [Char.ofNat 110, Char.ofNat 105, Char.ofNat 117], reversed := ["\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut24 : feed clean_obj_header_state24 clean_obj_header_chunk24 = clean_obj_header_state25 := by rfl
def clean_obj_header_chunk25 : List Char := [Char.ofNat 116, Char.ofNat 56, Char.ofNat 95, Char.ofNat 116, Char.ofNat 32, Char.ofNat 115, Char.ofNat 99, Char.ofNat 97]
def clean_obj_header_state26 : Option State := some { mode := .word, word := [Char.ofNat 97, Char.ofNat 99, Char.ofNat 115], reversed := ["uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut25 : feed clean_obj_header_state25 clean_obj_header_chunk25 = clean_obj_header_state26 := by rfl
def clean_obj_header_chunk26 : List Char := [Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 95, Char.ofNat 115, Char.ofNat 122, Char.ofNat 59, Char.ofNat 32]
def clean_obj_header_state27 : Option State := some { mode := .normal, word := [], reversed := [";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut26 : feed clean_obj_header_state26 clean_obj_header_chunk26 = clean_obj_header_state27 := by rfl
def clean_obj_header_chunk27 : List Char := [Char.ofNat 32, Char.ofNat 47, Char.ofNat 42, Char.ofNat 32, Char.ofNat 98, Char.ofNat 121, Char.ofNat 116, Char.ofNat 101]
def clean_obj_header_state28 : Option State := some { mode := .block, word := [], reversed := [";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut27 : feed clean_obj_header_state27 clean_obj_header_chunk27 = clean_obj_header_state28 := by rfl
def clean_obj_header_chunk28 : List Char := [Char.ofNat 115, Char.ofNat 32, Char.ofNat 111, Char.ofNat 102, Char.ofNat 32, Char.ofNat 115, Char.ofNat 99, Char.ofNat 97]
def clean_obj_header_state29 : Option State := some { mode := .block, word := [], reversed := [";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut28 : feed clean_obj_header_state28 clean_obj_header_chunk28 = clean_obj_header_state29 := by rfl
def clean_obj_header_chunk29 : List Char := [Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 32, Char.ofNat 112, Char.ofNat 97, Char.ofNat 121, Char.ofNat 108]
def clean_obj_header_state30 : Option State := some { mode := .block, word := [], reversed := [";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut29 : feed clean_obj_header_state29 clean_obj_header_chunk29 = clean_obj_header_state30 := by rfl
def clean_obj_header_chunk30 : List Char := [Char.ofNat 111, Char.ofNat 97, Char.ofNat 100, Char.ofNat 32, Char.ofNat 97, Char.ofNat 102, Char.ofNat 116, Char.ofNat 101]
def clean_obj_header_state31 : Option State := some { mode := .block, word := [], reversed := [";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut30 : feed clean_obj_header_state30 clean_obj_header_chunk30 = clean_obj_header_state31 := by rfl
def clean_obj_header_chunk31 : List Char := [Char.ofNat 114, Char.ofNat 32, Char.ofNat 111, Char.ofNat 98, Char.ofNat 106, Char.ofNat 101, Char.ofNat 99, Char.ofNat 116]
def clean_obj_header_state32 : Option State := some { mode := .block, word := [], reversed := [";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut31 : feed clean_obj_header_state31 clean_obj_header_chunk31 = clean_obj_header_state32 := by rfl
def clean_obj_header_chunk32 : List Char := [Char.ofNat 32, Char.ofNat 112, Char.ofNat 111, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]
def clean_obj_header_state33 : Option State := some { mode := .block, word := [], reversed := [";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut32 : feed clean_obj_header_state32 clean_obj_header_chunk32 = clean_obj_header_state33 := by rfl
def clean_obj_header_chunk33 : List Char := [Char.ofNat 115, Char.ofNat 32, Char.ofNat 40, Char.ofNat 80, Char.ofNat 97, Char.ofNat 114, Char.ofNat 116, Char.ofNat 32]
def clean_obj_header_state34 : Option State := some { mode := .block, word := [], reversed := [";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut33 : feed clean_obj_header_state33 clean_obj_header_chunk33 = clean_obj_header_state34 := by rfl
def clean_obj_header_chunk34 : List Char := [Char.ofNat 111, Char.ofNat 102, Char.ofNat 32, Char.ofNat 35, Char.ofNat 49, Char.ofNat 57, Char.ofNat 57, Char.ofNat 48]
def clean_obj_header_state35 : Option State := some { mode := .block, word := [], reversed := [";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut34 : feed clean_obj_header_state34 clean_obj_header_chunk34 = clean_obj_header_state35 := by rfl
def clean_obj_header_chunk35 : List Char := [Char.ofNat 41, Char.ofNat 32, Char.ofNat 42, Char.ofNat 47, Char.ofNat 10, Char.ofNat 125, Char.ofNat 32, Char.ofNat 99]
def clean_obj_header_state36 : Option State := some { mode := .word, word := [Char.ofNat 99], reversed := ["}", "\n", ";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut35 : feed clean_obj_header_state35 clean_obj_header_chunk35 = clean_obj_header_state36 := by rfl
def clean_obj_header_chunk36 : List Char := [Char.ofNat 108, Char.ofNat 101, Char.ofNat 97, Char.ofNat 110, Char.ofNat 95, Char.ofNat 111, Char.ofNat 98, Char.ofNat 106]
def clean_obj_header_state37 : Option State := some { mode := .word, word := [Char.ofNat 106, Char.ofNat 98, Char.ofNat 111, Char.ofNat 95, Char.ofNat 110, Char.ofNat 97, Char.ofNat 101, Char.ofNat 108, Char.ofNat 99], reversed := ["}", "\n", ";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut36 : feed clean_obj_header_state36 clean_obj_header_chunk36 = clean_obj_header_state37 := by rfl
def clean_obj_header_chunk37 : List Char := [Char.ofNat 95, Char.ofNat 104, Char.ofNat 101, Char.ofNat 97, Char.ofNat 100, Char.ofNat 101, Char.ofNat 114, Char.ofNat 59]
def clean_obj_header_state38 : Option State := some { mode := .normal, word := [], reversed := [";", "clean_obj_header", "}", "\n", ";", "scalar_sz", "uint8_t", "\n", ";", "num_objs", "uint8_t", "\n", ";", "kind", "uint8_t", "\n", ";", "tag", "uint8_t", "\n", ";", "ref_count", "uint32_t", "_Atomic", "\n", "{", "clean_obj_header", "struct", "typedef"] }
theorem clean_obj_header_cut37 : feed clean_obj_header_state37 clean_obj_header_chunk37 = clean_obj_header_state38 := by rfl
def clean_obj_header_chunks : List (List Char) := [clean_obj_header_chunk0, clean_obj_header_chunk1, clean_obj_header_chunk2, clean_obj_header_chunk3, clean_obj_header_chunk4, clean_obj_header_chunk5, clean_obj_header_chunk6, clean_obj_header_chunk7, clean_obj_header_chunk8, clean_obj_header_chunk9, clean_obj_header_chunk10, clean_obj_header_chunk11, clean_obj_header_chunk12, clean_obj_header_chunk13, clean_obj_header_chunk14, clean_obj_header_chunk15, clean_obj_header_chunk16, clean_obj_header_chunk17, clean_obj_header_chunk18, clean_obj_header_chunk19, clean_obj_header_chunk20, clean_obj_header_chunk21, clean_obj_header_chunk22, clean_obj_header_chunk23, clean_obj_header_chunk24, clean_obj_header_chunk25, clean_obj_header_chunk26, clean_obj_header_chunk27, clean_obj_header_chunk28, clean_obj_header_chunk29, clean_obj_header_chunk30, clean_obj_header_chunk31, clean_obj_header_chunk32, clean_obj_header_chunk33, clean_obj_header_chunk34, clean_obj_header_chunk35, clean_obj_header_chunk36, clean_obj_header_chunk37]
def clean_obj_header_tokens : List String := ["typedef", "struct", "clean_obj_header", "{", "\n", "_Atomic", "uint32_t", "ref_count", ";", "\n", "uint8_t", "tag", ";", "\n", "uint8_t", "kind", ";", "\n", "uint8_t", "num_objs", ";", "\n", "uint8_t", "scalar_sz", ";", "\n", "}", "clean_obj_header", ";"]
theorem clean_obj_header_characters_lex : tokenizeCharacters clean_obj_header_chunks.flatten = some clean_obj_header_tokens := by
  rw [← chunks_exact]
  simp only [tokenizeChunks, clean_obj_header_chunks, List.foldl_cons, List.foldl_nil]
  rw [clean_obj_header_cut0, clean_obj_header_cut1, clean_obj_header_cut2, clean_obj_header_cut3, clean_obj_header_cut4, clean_obj_header_cut5, clean_obj_header_cut6, clean_obj_header_cut7, clean_obj_header_cut8, clean_obj_header_cut9, clean_obj_header_cut10, clean_obj_header_cut11, clean_obj_header_cut12, clean_obj_header_cut13, clean_obj_header_cut14, clean_obj_header_cut15, clean_obj_header_cut16, clean_obj_header_cut17, clean_obj_header_cut18, clean_obj_header_cut19, clean_obj_header_cut20, clean_obj_header_cut21, clean_obj_header_cut22, clean_obj_header_cut23, clean_obj_header_cut24, clean_obj_header_cut25, clean_obj_header_cut26, clean_obj_header_cut27, clean_obj_header_cut28, clean_obj_header_cut29, clean_obj_header_cut30, clean_obj_header_cut31, clean_obj_header_cut32, clean_obj_header_cut33, clean_obj_header_cut34, clean_obj_header_cut35, clean_obj_header_cut36, clean_obj_header_cut37]
  rfl
def clean_obj_header_string_leaf0 : String := "typedef "
theorem clean_obj_header_chunk_chars0 : clean_obj_header_string_leaf0.toList = clean_obj_header_chunk0 := by rfl
def clean_obj_header_string_leaf1 : String := "struct c"
theorem clean_obj_header_chunk_chars1 : clean_obj_header_string_leaf1.toList = clean_obj_header_chunk1 := by rfl
def clean_obj_header_string_leaf2 : String := "lean_obj"
theorem clean_obj_header_chunk_chars2 : clean_obj_header_string_leaf2.toList = clean_obj_header_chunk2 := by rfl
def clean_obj_header_string_leaf3 : String := "_header "
theorem clean_obj_header_chunk_chars3 : clean_obj_header_string_leaf3.toList = clean_obj_header_chunk3 := by rfl
def clean_obj_header_string_leaf4 : String := "{\n    _A"
theorem clean_obj_header_chunk_chars4 : clean_obj_header_string_leaf4.toList = clean_obj_header_chunk4 := by rfl
def clean_obj_header_string_leaf5 : String := "tomic ui"
theorem clean_obj_header_chunk_chars5 : clean_obj_header_string_leaf5.toList = clean_obj_header_chunk5 := by rfl
def clean_obj_header_string_leaf6 : String := "nt32_t r"
theorem clean_obj_header_chunk_chars6 : clean_obj_header_string_leaf6.toList = clean_obj_header_chunk6 := by rfl
def clean_obj_header_string_leaf7 : String := "ef_count"
theorem clean_obj_header_chunk_chars7 : clean_obj_header_string_leaf7.toList = clean_obj_header_chunk7 := by rfl
def clean_obj_header_string_leaf8 : String := ";\n    ui"
theorem clean_obj_header_chunk_chars8 : clean_obj_header_string_leaf8.toList = clean_obj_header_chunk8 := by rfl
def clean_obj_header_string_leaf9 : String := "nt8_t ta"
theorem clean_obj_header_chunk_chars9 : clean_obj_header_string_leaf9.toList = clean_obj_header_chunk9 := by rfl
def clean_obj_header_string_leaf10 : String := "g;\n    u"
theorem clean_obj_header_chunk_chars10 : clean_obj_header_string_leaf10.toList = clean_obj_header_chunk10 := by rfl
def clean_obj_header_string_leaf11 : String := "int8_t k"
theorem clean_obj_header_chunk_chars11 : clean_obj_header_string_leaf11.toList = clean_obj_header_chunk11 := by rfl
def clean_obj_header_string_leaf12 : String := "ind;\n   "
theorem clean_obj_header_chunk_chars12 : clean_obj_header_string_leaf12.toList = clean_obj_header_chunk12 := by rfl
def clean_obj_header_string_leaf13 : String := " uint8_t"
theorem clean_obj_header_chunk_chars13 : clean_obj_header_string_leaf13.toList = clean_obj_header_chunk13 := by rfl
def clean_obj_header_string_leaf14 : String := " num_obj"
theorem clean_obj_header_chunk_chars14 : clean_obj_header_string_leaf14.toList = clean_obj_header_chunk14 := by rfl
def clean_obj_header_string_leaf15 : String := "s;   /* "
theorem clean_obj_header_chunk_chars15 : clean_obj_header_string_leaf15.toList = clean_obj_header_chunk15 := by rfl
def clean_obj_header_string_leaf16 : String := "was uint"
theorem clean_obj_header_chunk_chars16 : clean_obj_header_string_leaf16.toList = clean_obj_header_chunk16 := by rfl
def clean_obj_header_string_leaf17 : String := "16_t — n"
theorem clean_obj_header_chunk_chars17 : clean_obj_header_string_leaf17.toList = clean_obj_header_chunk17 := by rfl
def clean_obj_header_string_leaf18 : String := "ow u8 ma"
theorem clean_obj_header_chunk_chars18 : clean_obj_header_string_leaf18.toList = clean_obj_header_chunk18 := by rfl
def clean_obj_header_string_leaf19 : String := "tching L"
theorem clean_obj_header_chunk_chars19 : clean_obj_header_string_leaf19.toList = clean_obj_header_chunk19 := by rfl
def clean_obj_header_string_leaf20 : String := "ean 4 m_"
theorem clean_obj_header_chunk_chars20 : clean_obj_header_string_leaf20.toList = clean_obj_header_chunk20 := by rfl
def clean_obj_header_string_leaf21 : String := "other (P"
theorem clean_obj_header_chunk_chars21 : clean_obj_header_string_leaf21.toList = clean_obj_header_chunk21 := by rfl
def clean_obj_header_string_leaf22 : String := "art of #"
theorem clean_obj_header_chunk_chars22 : clean_obj_header_string_leaf22.toList = clean_obj_header_chunk22 := by rfl
def clean_obj_header_string_leaf23 : String := "1990) */"
theorem clean_obj_header_chunk_chars23 : clean_obj_header_string_leaf23.toList = clean_obj_header_chunk23 := by rfl
def clean_obj_header_string_leaf24 : String := "\n    uin"
theorem clean_obj_header_chunk_chars24 : clean_obj_header_string_leaf24.toList = clean_obj_header_chunk24 := by rfl
def clean_obj_header_string_leaf25 : String := "t8_t sca"
theorem clean_obj_header_chunk_chars25 : clean_obj_header_string_leaf25.toList = clean_obj_header_chunk25 := by rfl
def clean_obj_header_string_leaf26 : String := "lar_sz; "
theorem clean_obj_header_chunk_chars26 : clean_obj_header_string_leaf26.toList = clean_obj_header_chunk26 := by rfl
def clean_obj_header_string_leaf27 : String := " /* byte"
theorem clean_obj_header_chunk_chars27 : clean_obj_header_string_leaf27.toList = clean_obj_header_chunk27 := by rfl
def clean_obj_header_string_leaf28 : String := "s of sca"
theorem clean_obj_header_chunk_chars28 : clean_obj_header_string_leaf28.toList = clean_obj_header_chunk28 := by rfl
def clean_obj_header_string_leaf29 : String := "lar payl"
theorem clean_obj_header_chunk_chars29 : clean_obj_header_string_leaf29.toList = clean_obj_header_chunk29 := by rfl
def clean_obj_header_string_leaf30 : String := "oad afte"
theorem clean_obj_header_chunk_chars30 : clean_obj_header_string_leaf30.toList = clean_obj_header_chunk30 := by rfl
def clean_obj_header_string_leaf31 : String := "r object"
theorem clean_obj_header_chunk_chars31 : clean_obj_header_string_leaf31.toList = clean_obj_header_chunk31 := by rfl
def clean_obj_header_string_leaf32 : String := " pointer"
theorem clean_obj_header_chunk_chars32 : clean_obj_header_string_leaf32.toList = clean_obj_header_chunk32 := by rfl
def clean_obj_header_string_leaf33 : String := "s (Part "
theorem clean_obj_header_chunk_chars33 : clean_obj_header_string_leaf33.toList = clean_obj_header_chunk33 := by rfl
def clean_obj_header_string_leaf34 : String := "of #1990"
theorem clean_obj_header_chunk_chars34 : clean_obj_header_string_leaf34.toList = clean_obj_header_chunk34 := by rfl
def clean_obj_header_string_leaf35 : String := ") */\n} c"
theorem clean_obj_header_chunk_chars35 : clean_obj_header_string_leaf35.toList = clean_obj_header_chunk35 := by rfl
def clean_obj_header_string_leaf36 : String := "lean_obj"
theorem clean_obj_header_chunk_chars36 : clean_obj_header_string_leaf36.toList = clean_obj_header_chunk36 := by rfl
def clean_obj_header_string_leaf37 : String := "_header;"
theorem clean_obj_header_chunk_chars37 : clean_obj_header_string_leaf37.toList = clean_obj_header_chunk37 := by rfl
def clean_obj_header_node_0_2 : String := clean_obj_header_string_leaf0 ++ clean_obj_header_string_leaf1
def clean_obj_header_node_0_2_chars : List Char := clean_obj_header_chunk0 ++ clean_obj_header_chunk1
theorem clean_obj_header_node_0_2_literal : clean_obj_header_node_0_2 = "typedef struct c" := by
  unfold clean_obj_header_node_0_2
  cbv
theorem clean_obj_header_node_0_2_characters : clean_obj_header_node_0_2.toList = clean_obj_header_node_0_2_chars := by
  unfold clean_obj_header_node_0_2 clean_obj_header_node_0_2_chars
  rw [String.toList_append, clean_obj_header_chunk_chars0, clean_obj_header_chunk_chars1]
def clean_obj_header_node_2_4 : String := clean_obj_header_string_leaf2 ++ clean_obj_header_string_leaf3
def clean_obj_header_node_2_4_chars : List Char := clean_obj_header_chunk2 ++ clean_obj_header_chunk3
theorem clean_obj_header_node_2_4_literal : clean_obj_header_node_2_4 = "lean_obj_header " := by
  unfold clean_obj_header_node_2_4
  cbv
theorem clean_obj_header_node_2_4_characters : clean_obj_header_node_2_4.toList = clean_obj_header_node_2_4_chars := by
  unfold clean_obj_header_node_2_4 clean_obj_header_node_2_4_chars
  rw [String.toList_append, clean_obj_header_chunk_chars2, clean_obj_header_chunk_chars3]
def clean_obj_header_node_0_4 : String := clean_obj_header_node_0_2 ++ clean_obj_header_node_2_4
def clean_obj_header_node_0_4_chars : List Char := clean_obj_header_node_0_2_chars ++ clean_obj_header_node_2_4_chars
theorem clean_obj_header_node_0_4_literal : clean_obj_header_node_0_4 = "typedef struct clean_obj_header " := by
  unfold clean_obj_header_node_0_4
  rw [clean_obj_header_node_0_2_literal]
  rw [clean_obj_header_node_2_4_literal]
  cbv
theorem clean_obj_header_node_0_4_characters : clean_obj_header_node_0_4.toList = clean_obj_header_node_0_4_chars := by
  unfold clean_obj_header_node_0_4 clean_obj_header_node_0_4_chars
  rw [String.toList_append, clean_obj_header_node_0_2_characters, clean_obj_header_node_2_4_characters]
def clean_obj_header_node_4_6 : String := clean_obj_header_string_leaf4 ++ clean_obj_header_string_leaf5
def clean_obj_header_node_4_6_chars : List Char := clean_obj_header_chunk4 ++ clean_obj_header_chunk5
theorem clean_obj_header_node_4_6_literal : clean_obj_header_node_4_6 = "{\n    _Atomic ui" := by
  unfold clean_obj_header_node_4_6
  cbv
theorem clean_obj_header_node_4_6_characters : clean_obj_header_node_4_6.toList = clean_obj_header_node_4_6_chars := by
  unfold clean_obj_header_node_4_6 clean_obj_header_node_4_6_chars
  rw [String.toList_append, clean_obj_header_chunk_chars4, clean_obj_header_chunk_chars5]
def clean_obj_header_node_7_9 : String := clean_obj_header_string_leaf7 ++ clean_obj_header_string_leaf8
def clean_obj_header_node_7_9_chars : List Char := clean_obj_header_chunk7 ++ clean_obj_header_chunk8
theorem clean_obj_header_node_7_9_literal : clean_obj_header_node_7_9 = "ef_count;\n    ui" := by
  unfold clean_obj_header_node_7_9
  cbv
theorem clean_obj_header_node_7_9_characters : clean_obj_header_node_7_9.toList = clean_obj_header_node_7_9_chars := by
  unfold clean_obj_header_node_7_9 clean_obj_header_node_7_9_chars
  rw [String.toList_append, clean_obj_header_chunk_chars7, clean_obj_header_chunk_chars8]
def clean_obj_header_node_6_9 : String := clean_obj_header_string_leaf6 ++ clean_obj_header_node_7_9
def clean_obj_header_node_6_9_chars : List Char := clean_obj_header_chunk6 ++ clean_obj_header_node_7_9_chars
theorem clean_obj_header_node_6_9_literal : clean_obj_header_node_6_9 = "nt32_t ref_count;\n    ui" := by
  unfold clean_obj_header_node_6_9
  rw [clean_obj_header_node_7_9_literal]
  cbv
theorem clean_obj_header_node_6_9_characters : clean_obj_header_node_6_9.toList = clean_obj_header_node_6_9_chars := by
  unfold clean_obj_header_node_6_9 clean_obj_header_node_6_9_chars
  rw [String.toList_append, clean_obj_header_chunk_chars6, clean_obj_header_node_7_9_characters]
def clean_obj_header_node_4_9 : String := clean_obj_header_node_4_6 ++ clean_obj_header_node_6_9
def clean_obj_header_node_4_9_chars : List Char := clean_obj_header_node_4_6_chars ++ clean_obj_header_node_6_9_chars
theorem clean_obj_header_node_4_9_literal : clean_obj_header_node_4_9 = "{\n    _Atomic uint32_t ref_count;\n    ui" := by
  unfold clean_obj_header_node_4_9
  rw [clean_obj_header_node_4_6_literal]
  rw [clean_obj_header_node_6_9_literal]
  cbv
theorem clean_obj_header_node_4_9_characters : clean_obj_header_node_4_9.toList = clean_obj_header_node_4_9_chars := by
  unfold clean_obj_header_node_4_9 clean_obj_header_node_4_9_chars
  rw [String.toList_append, clean_obj_header_node_4_6_characters, clean_obj_header_node_6_9_characters]
def clean_obj_header_node_0_9 : String := clean_obj_header_node_0_4 ++ clean_obj_header_node_4_9
def clean_obj_header_node_0_9_chars : List Char := clean_obj_header_node_0_4_chars ++ clean_obj_header_node_4_9_chars
theorem clean_obj_header_node_0_9_literal : clean_obj_header_node_0_9 = "typedef struct clean_obj_header {\n    _Atomic uint32_t ref_count;\n    ui" := by
  unfold clean_obj_header_node_0_9
  rw [clean_obj_header_node_0_4_literal]
  rw [clean_obj_header_node_4_9_literal]
  cbv
theorem clean_obj_header_node_0_9_characters : clean_obj_header_node_0_9.toList = clean_obj_header_node_0_9_chars := by
  unfold clean_obj_header_node_0_9 clean_obj_header_node_0_9_chars
  rw [String.toList_append, clean_obj_header_node_0_4_characters, clean_obj_header_node_4_9_characters]
def clean_obj_header_node_9_11 : String := clean_obj_header_string_leaf9 ++ clean_obj_header_string_leaf10
def clean_obj_header_node_9_11_chars : List Char := clean_obj_header_chunk9 ++ clean_obj_header_chunk10
theorem clean_obj_header_node_9_11_literal : clean_obj_header_node_9_11 = "nt8_t tag;\n    u" := by
  unfold clean_obj_header_node_9_11
  cbv
theorem clean_obj_header_node_9_11_characters : clean_obj_header_node_9_11.toList = clean_obj_header_node_9_11_chars := by
  unfold clean_obj_header_node_9_11 clean_obj_header_node_9_11_chars
  rw [String.toList_append, clean_obj_header_chunk_chars9, clean_obj_header_chunk_chars10]
def clean_obj_header_node_12_14 : String := clean_obj_header_string_leaf12 ++ clean_obj_header_string_leaf13
def clean_obj_header_node_12_14_chars : List Char := clean_obj_header_chunk12 ++ clean_obj_header_chunk13
theorem clean_obj_header_node_12_14_literal : clean_obj_header_node_12_14 = "ind;\n    uint8_t" := by
  unfold clean_obj_header_node_12_14
  cbv
theorem clean_obj_header_node_12_14_characters : clean_obj_header_node_12_14.toList = clean_obj_header_node_12_14_chars := by
  unfold clean_obj_header_node_12_14 clean_obj_header_node_12_14_chars
  rw [String.toList_append, clean_obj_header_chunk_chars12, clean_obj_header_chunk_chars13]
def clean_obj_header_node_11_14 : String := clean_obj_header_string_leaf11 ++ clean_obj_header_node_12_14
def clean_obj_header_node_11_14_chars : List Char := clean_obj_header_chunk11 ++ clean_obj_header_node_12_14_chars
theorem clean_obj_header_node_11_14_literal : clean_obj_header_node_11_14 = "int8_t kind;\n    uint8_t" := by
  unfold clean_obj_header_node_11_14
  rw [clean_obj_header_node_12_14_literal]
  cbv
theorem clean_obj_header_node_11_14_characters : clean_obj_header_node_11_14.toList = clean_obj_header_node_11_14_chars := by
  unfold clean_obj_header_node_11_14 clean_obj_header_node_11_14_chars
  rw [String.toList_append, clean_obj_header_chunk_chars11, clean_obj_header_node_12_14_characters]
def clean_obj_header_node_9_14 : String := clean_obj_header_node_9_11 ++ clean_obj_header_node_11_14
def clean_obj_header_node_9_14_chars : List Char := clean_obj_header_node_9_11_chars ++ clean_obj_header_node_11_14_chars
theorem clean_obj_header_node_9_14_literal : clean_obj_header_node_9_14 = "nt8_t tag;\n    uint8_t kind;\n    uint8_t" := by
  unfold clean_obj_header_node_9_14
  rw [clean_obj_header_node_9_11_literal]
  rw [clean_obj_header_node_11_14_literal]
  cbv
theorem clean_obj_header_node_9_14_characters : clean_obj_header_node_9_14.toList = clean_obj_header_node_9_14_chars := by
  unfold clean_obj_header_node_9_14 clean_obj_header_node_9_14_chars
  rw [String.toList_append, clean_obj_header_node_9_11_characters, clean_obj_header_node_11_14_characters]
def clean_obj_header_node_14_16 : String := clean_obj_header_string_leaf14 ++ clean_obj_header_string_leaf15
def clean_obj_header_node_14_16_chars : List Char := clean_obj_header_chunk14 ++ clean_obj_header_chunk15
theorem clean_obj_header_node_14_16_literal : clean_obj_header_node_14_16 = " num_objs;   /* " := by
  unfold clean_obj_header_node_14_16
  cbv
theorem clean_obj_header_node_14_16_characters : clean_obj_header_node_14_16.toList = clean_obj_header_node_14_16_chars := by
  unfold clean_obj_header_node_14_16 clean_obj_header_node_14_16_chars
  rw [String.toList_append, clean_obj_header_chunk_chars14, clean_obj_header_chunk_chars15]
def clean_obj_header_node_17_19 : String := clean_obj_header_string_leaf17 ++ clean_obj_header_string_leaf18
def clean_obj_header_node_17_19_chars : List Char := clean_obj_header_chunk17 ++ clean_obj_header_chunk18
theorem clean_obj_header_node_17_19_literal : clean_obj_header_node_17_19 = "16_t — now u8 ma" := by
  unfold clean_obj_header_node_17_19
  cbv
theorem clean_obj_header_node_17_19_characters : clean_obj_header_node_17_19.toList = clean_obj_header_node_17_19_chars := by
  unfold clean_obj_header_node_17_19 clean_obj_header_node_17_19_chars
  rw [String.toList_append, clean_obj_header_chunk_chars17, clean_obj_header_chunk_chars18]
def clean_obj_header_node_16_19 : String := clean_obj_header_string_leaf16 ++ clean_obj_header_node_17_19
def clean_obj_header_node_16_19_chars : List Char := clean_obj_header_chunk16 ++ clean_obj_header_node_17_19_chars
theorem clean_obj_header_node_16_19_literal : clean_obj_header_node_16_19 = "was uint16_t — now u8 ma" := by
  unfold clean_obj_header_node_16_19
  rw [clean_obj_header_node_17_19_literal]
  cbv
theorem clean_obj_header_node_16_19_characters : clean_obj_header_node_16_19.toList = clean_obj_header_node_16_19_chars := by
  unfold clean_obj_header_node_16_19 clean_obj_header_node_16_19_chars
  rw [String.toList_append, clean_obj_header_chunk_chars16, clean_obj_header_node_17_19_characters]
def clean_obj_header_node_14_19 : String := clean_obj_header_node_14_16 ++ clean_obj_header_node_16_19
def clean_obj_header_node_14_19_chars : List Char := clean_obj_header_node_14_16_chars ++ clean_obj_header_node_16_19_chars
theorem clean_obj_header_node_14_19_literal : clean_obj_header_node_14_19 = " num_objs;   /* was uint16_t — now u8 ma" := by
  unfold clean_obj_header_node_14_19
  rw [clean_obj_header_node_14_16_literal]
  rw [clean_obj_header_node_16_19_literal]
  cbv
theorem clean_obj_header_node_14_19_characters : clean_obj_header_node_14_19.toList = clean_obj_header_node_14_19_chars := by
  unfold clean_obj_header_node_14_19 clean_obj_header_node_14_19_chars
  rw [String.toList_append, clean_obj_header_node_14_16_characters, clean_obj_header_node_16_19_characters]
def clean_obj_header_node_9_19 : String := clean_obj_header_node_9_14 ++ clean_obj_header_node_14_19
def clean_obj_header_node_9_19_chars : List Char := clean_obj_header_node_9_14_chars ++ clean_obj_header_node_14_19_chars
theorem clean_obj_header_node_9_19_literal : clean_obj_header_node_9_19 = "nt8_t tag;\n    uint8_t kind;\n    uint8_t num_objs;   /* was uint16_t — now u8 ma" := by
  unfold clean_obj_header_node_9_19
  rw [clean_obj_header_node_9_14_literal]
  rw [clean_obj_header_node_14_19_literal]
  cbv
theorem clean_obj_header_node_9_19_characters : clean_obj_header_node_9_19.toList = clean_obj_header_node_9_19_chars := by
  unfold clean_obj_header_node_9_19 clean_obj_header_node_9_19_chars
  rw [String.toList_append, clean_obj_header_node_9_14_characters, clean_obj_header_node_14_19_characters]
def clean_obj_header_node_0_19 : String := clean_obj_header_node_0_9 ++ clean_obj_header_node_9_19
def clean_obj_header_node_0_19_chars : List Char := clean_obj_header_node_0_9_chars ++ clean_obj_header_node_9_19_chars
theorem clean_obj_header_node_0_19_literal : clean_obj_header_node_0_19 = "typedef struct clean_obj_header {\n    _Atomic uint32_t ref_count;\n    uint8_t tag;\n    uint8_t kind;\n    uint8_t num_objs;   /* was uint16_t — now u8 ma" := by
  unfold clean_obj_header_node_0_19
  rw [clean_obj_header_node_0_9_literal]
  rw [clean_obj_header_node_9_19_literal]
  cbv
theorem clean_obj_header_node_0_19_characters : clean_obj_header_node_0_19.toList = clean_obj_header_node_0_19_chars := by
  unfold clean_obj_header_node_0_19 clean_obj_header_node_0_19_chars
  rw [String.toList_append, clean_obj_header_node_0_9_characters, clean_obj_header_node_9_19_characters]
def clean_obj_header_node_19_21 : String := clean_obj_header_string_leaf19 ++ clean_obj_header_string_leaf20
def clean_obj_header_node_19_21_chars : List Char := clean_obj_header_chunk19 ++ clean_obj_header_chunk20
theorem clean_obj_header_node_19_21_literal : clean_obj_header_node_19_21 = "tching Lean 4 m_" := by
  unfold clean_obj_header_node_19_21
  cbv
theorem clean_obj_header_node_19_21_characters : clean_obj_header_node_19_21.toList = clean_obj_header_node_19_21_chars := by
  unfold clean_obj_header_node_19_21 clean_obj_header_node_19_21_chars
  rw [String.toList_append, clean_obj_header_chunk_chars19, clean_obj_header_chunk_chars20]
def clean_obj_header_node_21_23 : String := clean_obj_header_string_leaf21 ++ clean_obj_header_string_leaf22
def clean_obj_header_node_21_23_chars : List Char := clean_obj_header_chunk21 ++ clean_obj_header_chunk22
theorem clean_obj_header_node_21_23_literal : clean_obj_header_node_21_23 = "other (Part of #" := by
  unfold clean_obj_header_node_21_23
  cbv
theorem clean_obj_header_node_21_23_characters : clean_obj_header_node_21_23.toList = clean_obj_header_node_21_23_chars := by
  unfold clean_obj_header_node_21_23 clean_obj_header_node_21_23_chars
  rw [String.toList_append, clean_obj_header_chunk_chars21, clean_obj_header_chunk_chars22]
def clean_obj_header_node_19_23 : String := clean_obj_header_node_19_21 ++ clean_obj_header_node_21_23
def clean_obj_header_node_19_23_chars : List Char := clean_obj_header_node_19_21_chars ++ clean_obj_header_node_21_23_chars
theorem clean_obj_header_node_19_23_literal : clean_obj_header_node_19_23 = "tching Lean 4 m_other (Part of #" := by
  unfold clean_obj_header_node_19_23
  rw [clean_obj_header_node_19_21_literal]
  rw [clean_obj_header_node_21_23_literal]
  cbv
theorem clean_obj_header_node_19_23_characters : clean_obj_header_node_19_23.toList = clean_obj_header_node_19_23_chars := by
  unfold clean_obj_header_node_19_23 clean_obj_header_node_19_23_chars
  rw [String.toList_append, clean_obj_header_node_19_21_characters, clean_obj_header_node_21_23_characters]
def clean_obj_header_node_23_25 : String := clean_obj_header_string_leaf23 ++ clean_obj_header_string_leaf24
def clean_obj_header_node_23_25_chars : List Char := clean_obj_header_chunk23 ++ clean_obj_header_chunk24
theorem clean_obj_header_node_23_25_literal : clean_obj_header_node_23_25 = "1990) */\n    uin" := by
  unfold clean_obj_header_node_23_25
  cbv
theorem clean_obj_header_node_23_25_characters : clean_obj_header_node_23_25.toList = clean_obj_header_node_23_25_chars := by
  unfold clean_obj_header_node_23_25 clean_obj_header_node_23_25_chars
  rw [String.toList_append, clean_obj_header_chunk_chars23, clean_obj_header_chunk_chars24]
def clean_obj_header_node_26_28 : String := clean_obj_header_string_leaf26 ++ clean_obj_header_string_leaf27
def clean_obj_header_node_26_28_chars : List Char := clean_obj_header_chunk26 ++ clean_obj_header_chunk27
theorem clean_obj_header_node_26_28_literal : clean_obj_header_node_26_28 = "lar_sz;  /* byte" := by
  unfold clean_obj_header_node_26_28
  cbv
theorem clean_obj_header_node_26_28_characters : clean_obj_header_node_26_28.toList = clean_obj_header_node_26_28_chars := by
  unfold clean_obj_header_node_26_28 clean_obj_header_node_26_28_chars
  rw [String.toList_append, clean_obj_header_chunk_chars26, clean_obj_header_chunk_chars27]
def clean_obj_header_node_25_28 : String := clean_obj_header_string_leaf25 ++ clean_obj_header_node_26_28
def clean_obj_header_node_25_28_chars : List Char := clean_obj_header_chunk25 ++ clean_obj_header_node_26_28_chars
theorem clean_obj_header_node_25_28_literal : clean_obj_header_node_25_28 = "t8_t scalar_sz;  /* byte" := by
  unfold clean_obj_header_node_25_28
  rw [clean_obj_header_node_26_28_literal]
  cbv
theorem clean_obj_header_node_25_28_characters : clean_obj_header_node_25_28.toList = clean_obj_header_node_25_28_chars := by
  unfold clean_obj_header_node_25_28 clean_obj_header_node_25_28_chars
  rw [String.toList_append, clean_obj_header_chunk_chars25, clean_obj_header_node_26_28_characters]
def clean_obj_header_node_23_28 : String := clean_obj_header_node_23_25 ++ clean_obj_header_node_25_28
def clean_obj_header_node_23_28_chars : List Char := clean_obj_header_node_23_25_chars ++ clean_obj_header_node_25_28_chars
theorem clean_obj_header_node_23_28_literal : clean_obj_header_node_23_28 = "1990) */\n    uint8_t scalar_sz;  /* byte" := by
  unfold clean_obj_header_node_23_28
  rw [clean_obj_header_node_23_25_literal]
  rw [clean_obj_header_node_25_28_literal]
  cbv
theorem clean_obj_header_node_23_28_characters : clean_obj_header_node_23_28.toList = clean_obj_header_node_23_28_chars := by
  unfold clean_obj_header_node_23_28 clean_obj_header_node_23_28_chars
  rw [String.toList_append, clean_obj_header_node_23_25_characters, clean_obj_header_node_25_28_characters]
def clean_obj_header_node_19_28 : String := clean_obj_header_node_19_23 ++ clean_obj_header_node_23_28
def clean_obj_header_node_19_28_chars : List Char := clean_obj_header_node_19_23_chars ++ clean_obj_header_node_23_28_chars
theorem clean_obj_header_node_19_28_literal : clean_obj_header_node_19_28 = "tching Lean 4 m_other (Part of #1990) */\n    uint8_t scalar_sz;  /* byte" := by
  unfold clean_obj_header_node_19_28
  rw [clean_obj_header_node_19_23_literal]
  rw [clean_obj_header_node_23_28_literal]
  cbv
theorem clean_obj_header_node_19_28_characters : clean_obj_header_node_19_28.toList = clean_obj_header_node_19_28_chars := by
  unfold clean_obj_header_node_19_28 clean_obj_header_node_19_28_chars
  rw [String.toList_append, clean_obj_header_node_19_23_characters, clean_obj_header_node_23_28_characters]
def clean_obj_header_node_28_30 : String := clean_obj_header_string_leaf28 ++ clean_obj_header_string_leaf29
def clean_obj_header_node_28_30_chars : List Char := clean_obj_header_chunk28 ++ clean_obj_header_chunk29
theorem clean_obj_header_node_28_30_literal : clean_obj_header_node_28_30 = "s of scalar payl" := by
  unfold clean_obj_header_node_28_30
  cbv
theorem clean_obj_header_node_28_30_characters : clean_obj_header_node_28_30.toList = clean_obj_header_node_28_30_chars := by
  unfold clean_obj_header_node_28_30 clean_obj_header_node_28_30_chars
  rw [String.toList_append, clean_obj_header_chunk_chars28, clean_obj_header_chunk_chars29]
def clean_obj_header_node_31_33 : String := clean_obj_header_string_leaf31 ++ clean_obj_header_string_leaf32
def clean_obj_header_node_31_33_chars : List Char := clean_obj_header_chunk31 ++ clean_obj_header_chunk32
theorem clean_obj_header_node_31_33_literal : clean_obj_header_node_31_33 = "r object pointer" := by
  unfold clean_obj_header_node_31_33
  cbv
theorem clean_obj_header_node_31_33_characters : clean_obj_header_node_31_33.toList = clean_obj_header_node_31_33_chars := by
  unfold clean_obj_header_node_31_33 clean_obj_header_node_31_33_chars
  rw [String.toList_append, clean_obj_header_chunk_chars31, clean_obj_header_chunk_chars32]
def clean_obj_header_node_30_33 : String := clean_obj_header_string_leaf30 ++ clean_obj_header_node_31_33
def clean_obj_header_node_30_33_chars : List Char := clean_obj_header_chunk30 ++ clean_obj_header_node_31_33_chars
theorem clean_obj_header_node_30_33_literal : clean_obj_header_node_30_33 = "oad after object pointer" := by
  unfold clean_obj_header_node_30_33
  rw [clean_obj_header_node_31_33_literal]
  cbv
theorem clean_obj_header_node_30_33_characters : clean_obj_header_node_30_33.toList = clean_obj_header_node_30_33_chars := by
  unfold clean_obj_header_node_30_33 clean_obj_header_node_30_33_chars
  rw [String.toList_append, clean_obj_header_chunk_chars30, clean_obj_header_node_31_33_characters]
def clean_obj_header_node_28_33 : String := clean_obj_header_node_28_30 ++ clean_obj_header_node_30_33
def clean_obj_header_node_28_33_chars : List Char := clean_obj_header_node_28_30_chars ++ clean_obj_header_node_30_33_chars
theorem clean_obj_header_node_28_33_literal : clean_obj_header_node_28_33 = "s of scalar payload after object pointer" := by
  unfold clean_obj_header_node_28_33
  rw [clean_obj_header_node_28_30_literal]
  rw [clean_obj_header_node_30_33_literal]
  cbv
theorem clean_obj_header_node_28_33_characters : clean_obj_header_node_28_33.toList = clean_obj_header_node_28_33_chars := by
  unfold clean_obj_header_node_28_33 clean_obj_header_node_28_33_chars
  rw [String.toList_append, clean_obj_header_node_28_30_characters, clean_obj_header_node_30_33_characters]
def clean_obj_header_node_33_35 : String := clean_obj_header_string_leaf33 ++ clean_obj_header_string_leaf34
def clean_obj_header_node_33_35_chars : List Char := clean_obj_header_chunk33 ++ clean_obj_header_chunk34
theorem clean_obj_header_node_33_35_literal : clean_obj_header_node_33_35 = "s (Part of #1990" := by
  unfold clean_obj_header_node_33_35
  cbv
theorem clean_obj_header_node_33_35_characters : clean_obj_header_node_33_35.toList = clean_obj_header_node_33_35_chars := by
  unfold clean_obj_header_node_33_35 clean_obj_header_node_33_35_chars
  rw [String.toList_append, clean_obj_header_chunk_chars33, clean_obj_header_chunk_chars34]
def clean_obj_header_node_36_38 : String := clean_obj_header_string_leaf36 ++ clean_obj_header_string_leaf37
def clean_obj_header_node_36_38_chars : List Char := clean_obj_header_chunk36 ++ clean_obj_header_chunk37
theorem clean_obj_header_node_36_38_literal : clean_obj_header_node_36_38 = "lean_obj_header;" := by
  unfold clean_obj_header_node_36_38
  cbv
theorem clean_obj_header_node_36_38_characters : clean_obj_header_node_36_38.toList = clean_obj_header_node_36_38_chars := by
  unfold clean_obj_header_node_36_38 clean_obj_header_node_36_38_chars
  rw [String.toList_append, clean_obj_header_chunk_chars36, clean_obj_header_chunk_chars37]
def clean_obj_header_node_35_38 : String := clean_obj_header_string_leaf35 ++ clean_obj_header_node_36_38
def clean_obj_header_node_35_38_chars : List Char := clean_obj_header_chunk35 ++ clean_obj_header_node_36_38_chars
theorem clean_obj_header_node_35_38_literal : clean_obj_header_node_35_38 = ") */\n} clean_obj_header;" := by
  unfold clean_obj_header_node_35_38
  rw [clean_obj_header_node_36_38_literal]
  cbv
theorem clean_obj_header_node_35_38_characters : clean_obj_header_node_35_38.toList = clean_obj_header_node_35_38_chars := by
  unfold clean_obj_header_node_35_38 clean_obj_header_node_35_38_chars
  rw [String.toList_append, clean_obj_header_chunk_chars35, clean_obj_header_node_36_38_characters]
def clean_obj_header_node_33_38 : String := clean_obj_header_node_33_35 ++ clean_obj_header_node_35_38
def clean_obj_header_node_33_38_chars : List Char := clean_obj_header_node_33_35_chars ++ clean_obj_header_node_35_38_chars
theorem clean_obj_header_node_33_38_literal : clean_obj_header_node_33_38 = "s (Part of #1990) */\n} clean_obj_header;" := by
  unfold clean_obj_header_node_33_38
  rw [clean_obj_header_node_33_35_literal]
  rw [clean_obj_header_node_35_38_literal]
  cbv
theorem clean_obj_header_node_33_38_characters : clean_obj_header_node_33_38.toList = clean_obj_header_node_33_38_chars := by
  unfold clean_obj_header_node_33_38 clean_obj_header_node_33_38_chars
  rw [String.toList_append, clean_obj_header_node_33_35_characters, clean_obj_header_node_35_38_characters]
def clean_obj_header_node_28_38 : String := clean_obj_header_node_28_33 ++ clean_obj_header_node_33_38
def clean_obj_header_node_28_38_chars : List Char := clean_obj_header_node_28_33_chars ++ clean_obj_header_node_33_38_chars
theorem clean_obj_header_node_28_38_literal : clean_obj_header_node_28_38 = "s of scalar payload after object pointers (Part of #1990) */\n} clean_obj_header;" := by
  unfold clean_obj_header_node_28_38
  rw [clean_obj_header_node_28_33_literal]
  rw [clean_obj_header_node_33_38_literal]
  cbv
theorem clean_obj_header_node_28_38_characters : clean_obj_header_node_28_38.toList = clean_obj_header_node_28_38_chars := by
  unfold clean_obj_header_node_28_38 clean_obj_header_node_28_38_chars
  rw [String.toList_append, clean_obj_header_node_28_33_characters, clean_obj_header_node_33_38_characters]
def clean_obj_header_node_19_38 : String := clean_obj_header_node_19_28 ++ clean_obj_header_node_28_38
def clean_obj_header_node_19_38_chars : List Char := clean_obj_header_node_19_28_chars ++ clean_obj_header_node_28_38_chars
theorem clean_obj_header_node_19_38_literal : clean_obj_header_node_19_38 = "tching Lean 4 m_other (Part of #1990) */\n    uint8_t scalar_sz;  /* bytes of scalar payload after object pointers (Part of #1990) */\n} clean_obj_header;" := by
  unfold clean_obj_header_node_19_38
  rw [clean_obj_header_node_19_28_literal]
  rw [clean_obj_header_node_28_38_literal]
  cbv
theorem clean_obj_header_node_19_38_characters : clean_obj_header_node_19_38.toList = clean_obj_header_node_19_38_chars := by
  unfold clean_obj_header_node_19_38 clean_obj_header_node_19_38_chars
  rw [String.toList_append, clean_obj_header_node_19_28_characters, clean_obj_header_node_28_38_characters]
def clean_obj_header_node_0_38 : String := clean_obj_header_node_0_19 ++ clean_obj_header_node_19_38
def clean_obj_header_node_0_38_chars : List Char := clean_obj_header_node_0_19_chars ++ clean_obj_header_node_19_38_chars
theorem clean_obj_header_node_0_38_literal : clean_obj_header_node_0_38 = "typedef struct clean_obj_header {\n    _Atomic uint32_t ref_count;\n    uint8_t tag;\n    uint8_t kind;\n    uint8_t num_objs;   /* was uint16_t — now u8 matching Lean 4 m_other (Part of #1990) */\n    uint8_t scalar_sz;  /* bytes of scalar payload after object pointers (Part of #1990) */\n} clean_obj_header;" := by
  unfold clean_obj_header_node_0_38
  rw [clean_obj_header_node_0_19_literal]
  rw [clean_obj_header_node_19_38_literal]
  cbv
theorem clean_obj_header_node_0_38_characters : clean_obj_header_node_0_38.toList = clean_obj_header_node_0_38_chars := by
  unfold clean_obj_header_node_0_38 clean_obj_header_node_0_38_chars
  rw [String.toList_append, clean_obj_header_node_0_19_characters, clean_obj_header_node_19_38_characters]
theorem clean_obj_header_string_exact : clean_obj_header_node_0_38 = C11ActualDeclarationData.clean_obj_header_0 := by
  exact clean_obj_header_node_0_38_literal
theorem clean_obj_header_flatten_exact : clean_obj_header_node_0_38_chars = clean_obj_header_chunks.flatten := by
  simp only [clean_obj_header_node_0_2_chars, clean_obj_header_node_2_4_chars, clean_obj_header_node_0_4_chars, clean_obj_header_node_4_6_chars, clean_obj_header_node_7_9_chars, clean_obj_header_node_6_9_chars, clean_obj_header_node_4_9_chars, clean_obj_header_node_0_9_chars, clean_obj_header_node_9_11_chars, clean_obj_header_node_12_14_chars, clean_obj_header_node_11_14_chars, clean_obj_header_node_9_14_chars, clean_obj_header_node_14_16_chars, clean_obj_header_node_17_19_chars, clean_obj_header_node_16_19_chars, clean_obj_header_node_14_19_chars, clean_obj_header_node_9_19_chars, clean_obj_header_node_0_19_chars, clean_obj_header_node_19_21_chars, clean_obj_header_node_21_23_chars, clean_obj_header_node_19_23_chars, clean_obj_header_node_23_25_chars, clean_obj_header_node_26_28_chars, clean_obj_header_node_25_28_chars, clean_obj_header_node_23_28_chars, clean_obj_header_node_19_28_chars, clean_obj_header_node_28_30_chars, clean_obj_header_node_31_33_chars, clean_obj_header_node_30_33_chars, clean_obj_header_node_28_33_chars, clean_obj_header_node_33_35_chars, clean_obj_header_node_36_38_chars, clean_obj_header_node_35_38_chars, clean_obj_header_node_33_38_chars, clean_obj_header_node_28_38_chars, clean_obj_header_node_19_38_chars, clean_obj_header_node_0_38_chars, clean_obj_header_chunks, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]
theorem clean_obj_header_source_lex : tokenize C11ActualDeclarationData.clean_obj_header_0 = some clean_obj_header_tokens := by
  unfold tokenize
  rw [← clean_obj_header_string_exact, clean_obj_header_node_0_38_characters, clean_obj_header_flatten_exact]
  exact clean_obj_header_characters_lex

def clean_obj_state0 : Option State := some initial
def clean_obj_chunk0 : List Char := [Char.ofNat 116, Char.ofNat 121, Char.ofNat 112, Char.ofNat 101, Char.ofNat 100, Char.ofNat 101, Char.ofNat 102, Char.ofNat 32]
def clean_obj_state1 : Option State := some { mode := .normal, word := [], reversed := ["typedef"] }
theorem clean_obj_cut0 : feed (some initial) clean_obj_chunk0 = clean_obj_state1 := by rfl
def clean_obj_chunk1 : List Char := [Char.ofNat 115, Char.ofNat 116, Char.ofNat 114, Char.ofNat 117, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 99]
def clean_obj_state2 : Option State := some { mode := .word, word := [Char.ofNat 99], reversed := ["struct", "typedef"] }
theorem clean_obj_cut1 : feed clean_obj_state1 clean_obj_chunk1 = clean_obj_state2 := by rfl
def clean_obj_chunk2 : List Char := [Char.ofNat 108, Char.ofNat 101, Char.ofNat 97, Char.ofNat 110, Char.ofNat 95, Char.ofNat 111, Char.ofNat 98, Char.ofNat 106]
def clean_obj_state3 : Option State := some { mode := .word, word := [Char.ofNat 106, Char.ofNat 98, Char.ofNat 111, Char.ofNat 95, Char.ofNat 110, Char.ofNat 97, Char.ofNat 101, Char.ofNat 108, Char.ofNat 99], reversed := ["struct", "typedef"] }
theorem clean_obj_cut2 : feed clean_obj_state2 clean_obj_chunk2 = clean_obj_state3 := by rfl
def clean_obj_chunk3 : List Char := [Char.ofNat 32, Char.ofNat 123, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 99]
def clean_obj_state4 : Option State := some { mode := .word, word := [Char.ofNat 99], reversed := ["\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut3 : feed clean_obj_state3 clean_obj_chunk3 = clean_obj_state4 := by rfl
def clean_obj_chunk4 : List Char := [Char.ofNat 108, Char.ofNat 101, Char.ofNat 97, Char.ofNat 110, Char.ofNat 95, Char.ofNat 111, Char.ofNat 98, Char.ofNat 106]
def clean_obj_state5 : Option State := some { mode := .word, word := [Char.ofNat 106, Char.ofNat 98, Char.ofNat 111, Char.ofNat 95, Char.ofNat 110, Char.ofNat 97, Char.ofNat 101, Char.ofNat 108, Char.ofNat 99], reversed := ["\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut4 : feed clean_obj_state4 clean_obj_chunk4 = clean_obj_state5 := by rfl
def clean_obj_chunk5 : List Char := [Char.ofNat 95, Char.ofNat 104, Char.ofNat 101, Char.ofNat 97, Char.ofNat 100, Char.ofNat 101, Char.ofNat 114, Char.ofNat 32]
def clean_obj_state6 : Option State := some { mode := .normal, word := [], reversed := ["clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut5 : feed clean_obj_state5 clean_obj_chunk5 = clean_obj_state6 := by rfl
def clean_obj_chunk6 : List Char := [Char.ofNat 104, Char.ofNat 101, Char.ofNat 97, Char.ofNat 100, Char.ofNat 101, Char.ofNat 114, Char.ofNat 59, Char.ofNat 10]
def clean_obj_state7 : Option State := some { mode := .normal, word := [], reversed := ["\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut6 : feed clean_obj_state6 clean_obj_chunk6 = clean_obj_state7 := by rfl
def clean_obj_chunk7 : List Char := [Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 47, Char.ofNat 42, Char.ofNat 32, Char.ofNat 79]
def clean_obj_state8 : Option State := some { mode := .block, word := [], reversed := ["\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut7 : feed clean_obj_state7 clean_obj_chunk7 = clean_obj_state8 := by rfl
def clean_obj_chunk8 : List Char := [Char.ofNat 98, Char.ofNat 106, Char.ofNat 101, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 102, Char.ofNat 105]
def clean_obj_state9 : Option State := some { mode := .block, word := [], reversed := ["\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut8 : feed clean_obj_state8 clean_obj_chunk8 = clean_obj_state9 := by rfl
def clean_obj_chunk9 : List Char := [Char.ofNat 101, Char.ofNat 108, Char.ofNat 100, Char.ofNat 115, Char.ofNat 32, Char.ofNat 102, Char.ofNat 111, Char.ofNat 108]
def clean_obj_state10 : Option State := some { mode := .block, word := [], reversed := ["\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut9 : feed clean_obj_state9 clean_obj_chunk9 = clean_obj_state10 := by rfl
def clean_obj_chunk10 : List Char := [Char.ofNat 108, Char.ofNat 111, Char.ofNat 119, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32]
def clean_obj_state11 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut10 : feed clean_obj_state10 clean_obj_chunk10 = clean_obj_state11 := by rfl
def clean_obj_chunk11 : List Char := [Char.ofNat 32, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 45, Char.ofNat 32, Char.ofNat 79, Char.ofNat 98]
def clean_obj_state12 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut11 : feed clean_obj_state11 clean_obj_chunk11 = clean_obj_state12 := by rfl
def clean_obj_chunk12 : List Char := [Char.ofNat 106, Char.ofNat 101, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 112, Char.ofNat 111, Char.ofNat 105]
def clean_obj_state13 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut12 : feed clean_obj_state12 clean_obj_chunk12 = clean_obj_state13 := by rfl
def clean_obj_chunk13 : List Char := [Char.ofNat 110, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 115, Char.ofNat 32, Char.ofNat 102, Char.ofNat 105]
def clean_obj_state14 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut13 : feed clean_obj_state13 clean_obj_chunk13 = clean_obj_state14 := by rfl
def clean_obj_chunk14 : List Char := [Char.ofNat 114, Char.ofNat 115, Char.ofNat 116, Char.ofNat 32, Char.ofNat 40, Char.ofNat 110, Char.ofNat 117, Char.ofNat 109]
def clean_obj_state15 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut14 : feed clean_obj_state14 clean_obj_chunk14 = clean_obj_state15 := by rfl
def clean_obj_chunk15 : List Char := [Char.ofNat 95, Char.ofNat 111, Char.ofNat 98, Char.ofNat 106, Char.ofNat 115, Char.ofNat 32, Char.ofNat 99, Char.ofNat 111]
def clean_obj_state16 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut15 : feed clean_obj_state15 clean_obj_chunk15 = clean_obj_state16 := by rfl
def clean_obj_chunk16 : List Char := [Char.ofNat 117, Char.ofNat 110, Char.ofNat 116, Char.ofNat 41, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32]
def clean_obj_state17 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut16 : feed clean_obj_state16 clean_obj_chunk16 = clean_obj_state17 := by rfl
def clean_obj_chunk17 : List Char := [Char.ofNat 32, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 45, Char.ofNat 32, Char.ofNat 83, Char.ofNat 99]
def clean_obj_state18 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut17 : feed clean_obj_state17 clean_obj_chunk17 = clean_obj_state18 := by rfl
def clean_obj_chunk18 : List Char := [Char.ofNat 97, Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 32, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101]
def clean_obj_state19 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut18 : feed clean_obj_state18 clean_obj_chunk18 = clean_obj_state19 := by rfl
def clean_obj_chunk19 : List Char := [Char.ofNat 108, Char.ofNat 100, Char.ofNat 115, Char.ofNat 32, Char.ofNat 97, Char.ofNat 102, Char.ofNat 116, Char.ofNat 101]
def clean_obj_state20 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut19 : feed clean_obj_state19 clean_obj_chunk19 = clean_obj_state20 := by rfl
def clean_obj_chunk20 : List Char := [Char.ofNat 114, Char.ofNat 32, Char.ofNat 40, Char.ofNat 115, Char.ofNat 105, Char.ofNat 122, Char.ofNat 101, Char.ofNat 32]
def clean_obj_state21 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut20 : feed clean_obj_state20 clean_obj_chunk20 = clean_obj_state21 := by rfl
def clean_obj_chunk21 : List Char := [Char.ofNat 118, Char.ofNat 97, Char.ofNat 114, Char.ofNat 105, Char.ofNat 101, Char.ofNat 115, Char.ofNat 32, Char.ofNat 98]
def clean_obj_state22 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut21 : feed clean_obj_state21 clean_obj_chunk21 = clean_obj_state22 := by rfl
def clean_obj_chunk22 : List Char := [Char.ofNat 121, Char.ofNat 32, Char.ofNat 99, Char.ofNat 111, Char.ofNat 110, Char.ofNat 115, Char.ofNat 116, Char.ofNat 114]
def clean_obj_state23 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut22 : feed clean_obj_state22 clean_obj_chunk22 = clean_obj_state23 := by rfl
def clean_obj_chunk23 : List Char := [Char.ofNat 117, Char.ofNat 99, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 41, Char.ofNat 10, Char.ofNat 32]
def clean_obj_state24 : Option State := some { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut23 : feed clean_obj_state23 clean_obj_chunk23 = clean_obj_state24 := by rfl
def clean_obj_chunk24 : List Char := [Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 42, Char.ofNat 47, Char.ofNat 10, Char.ofNat 32]
def clean_obj_state25 : Option State := some { mode := .normal, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut24 : feed clean_obj_state24 clean_obj_chunk24 = clean_obj_state25 := by rfl
def clean_obj_chunk25 : List Char := [Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 115, Char.ofNat 116, Char.ofNat 114, Char.ofNat 117, Char.ofNat 99]
def clean_obj_state26 : Option State := some { mode := .word, word := [Char.ofNat 99, Char.ofNat 117, Char.ofNat 114, Char.ofNat 116, Char.ofNat 115], reversed := ["\n", "\n", "\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut25 : feed clean_obj_state25 clean_obj_chunk25 = clean_obj_state26 := by rfl
def clean_obj_chunk26 : List Char := [Char.ofNat 116, Char.ofNat 32, Char.ofNat 99, Char.ofNat 108, Char.ofNat 101, Char.ofNat 97, Char.ofNat 110, Char.ofNat 95]
def clean_obj_state27 : Option State := some { mode := .word, word := [Char.ofNat 95, Char.ofNat 110, Char.ofNat 97, Char.ofNat 101, Char.ofNat 108, Char.ofNat 99], reversed := ["struct", "\n", "\n", "\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut26 : feed clean_obj_state26 clean_obj_chunk26 = clean_obj_state27 := by rfl
def clean_obj_chunk27 : List Char := [Char.ofNat 111, Char.ofNat 98, Char.ofNat 106, Char.ofNat 42, Char.ofNat 32, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101]
def clean_obj_state28 : Option State := some { mode := .word, word := [Char.ofNat 101, Char.ofNat 105, Char.ofNat 102], reversed := ["*", "clean_obj", "struct", "\n", "\n", "\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut27 : feed clean_obj_state27 clean_obj_chunk27 = clean_obj_state28 := by rfl
def clean_obj_chunk28 : List Char := [Char.ofNat 108, Char.ofNat 100, Char.ofNat 115, Char.ofNat 91, Char.ofNat 93, Char.ofNat 59, Char.ofNat 10, Char.ofNat 125]
def clean_obj_state29 : Option State := some { mode := .normal, word := [], reversed := ["}", "\n", ";", "]", "[", "fields", "*", "clean_obj", "struct", "\n", "\n", "\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut28 : feed clean_obj_state28 clean_obj_chunk28 = clean_obj_state29 := by rfl
def clean_obj_chunk29 : List Char := [Char.ofNat 32, Char.ofNat 99, Char.ofNat 108, Char.ofNat 101, Char.ofNat 97, Char.ofNat 110, Char.ofNat 95, Char.ofNat 111]
def clean_obj_state30 : Option State := some { mode := .word, word := [Char.ofNat 111, Char.ofNat 95, Char.ofNat 110, Char.ofNat 97, Char.ofNat 101, Char.ofNat 108, Char.ofNat 99], reversed := ["}", "\n", ";", "]", "[", "fields", "*", "clean_obj", "struct", "\n", "\n", "\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut29 : feed clean_obj_state29 clean_obj_chunk29 = clean_obj_state30 := by rfl
def clean_obj_chunk30 : List Char := [Char.ofNat 98, Char.ofNat 106, Char.ofNat 59]
def clean_obj_state31 : Option State := some { mode := .normal, word := [], reversed := [";", "clean_obj", "}", "\n", ";", "]", "[", "fields", "*", "clean_obj", "struct", "\n", "\n", "\n", "\n", "\n", ";", "header", "clean_obj_header", "\n", "{", "clean_obj", "struct", "typedef"] }
theorem clean_obj_cut30 : feed clean_obj_state30 clean_obj_chunk30 = clean_obj_state31 := by rfl
def clean_obj_chunks : List (List Char) := [clean_obj_chunk0, clean_obj_chunk1, clean_obj_chunk2, clean_obj_chunk3, clean_obj_chunk4, clean_obj_chunk5, clean_obj_chunk6, clean_obj_chunk7, clean_obj_chunk8, clean_obj_chunk9, clean_obj_chunk10, clean_obj_chunk11, clean_obj_chunk12, clean_obj_chunk13, clean_obj_chunk14, clean_obj_chunk15, clean_obj_chunk16, clean_obj_chunk17, clean_obj_chunk18, clean_obj_chunk19, clean_obj_chunk20, clean_obj_chunk21, clean_obj_chunk22, clean_obj_chunk23, clean_obj_chunk24, clean_obj_chunk25, clean_obj_chunk26, clean_obj_chunk27, clean_obj_chunk28, clean_obj_chunk29, clean_obj_chunk30]
def clean_obj_tokens : List String := ["typedef", "struct", "clean_obj", "{", "\n", "clean_obj_header", "header", ";", "\n", "\n", "\n", "\n", "\n", "struct", "clean_obj", "*", "fields", "[", "]", ";", "\n", "}", "clean_obj", ";"]
theorem clean_obj_characters_lex : tokenizeCharacters clean_obj_chunks.flatten = some clean_obj_tokens := by
  rw [← chunks_exact]
  simp only [tokenizeChunks, clean_obj_chunks, List.foldl_cons, List.foldl_nil]
  rw [clean_obj_cut0, clean_obj_cut1, clean_obj_cut2, clean_obj_cut3, clean_obj_cut4, clean_obj_cut5, clean_obj_cut6, clean_obj_cut7, clean_obj_cut8, clean_obj_cut9, clean_obj_cut10, clean_obj_cut11, clean_obj_cut12, clean_obj_cut13, clean_obj_cut14, clean_obj_cut15, clean_obj_cut16, clean_obj_cut17, clean_obj_cut18, clean_obj_cut19, clean_obj_cut20, clean_obj_cut21, clean_obj_cut22, clean_obj_cut23, clean_obj_cut24, clean_obj_cut25, clean_obj_cut26, clean_obj_cut27, clean_obj_cut28, clean_obj_cut29, clean_obj_cut30]
  rfl
def clean_obj_string_leaf0 : String := "typedef "
theorem clean_obj_chunk_chars0 : clean_obj_string_leaf0.toList = clean_obj_chunk0 := by rfl
def clean_obj_string_leaf1 : String := "struct c"
theorem clean_obj_chunk_chars1 : clean_obj_string_leaf1.toList = clean_obj_chunk1 := by rfl
def clean_obj_string_leaf2 : String := "lean_obj"
theorem clean_obj_chunk_chars2 : clean_obj_string_leaf2.toList = clean_obj_chunk2 := by rfl
def clean_obj_string_leaf3 : String := " {\n    c"
theorem clean_obj_chunk_chars3 : clean_obj_string_leaf3.toList = clean_obj_chunk3 := by rfl
def clean_obj_string_leaf4 : String := "lean_obj"
theorem clean_obj_chunk_chars4 : clean_obj_string_leaf4.toList = clean_obj_chunk4 := by rfl
def clean_obj_string_leaf5 : String := "_header "
theorem clean_obj_chunk_chars5 : clean_obj_string_leaf5.toList = clean_obj_chunk5 := by rfl
def clean_obj_string_leaf6 : String := "header;\n"
theorem clean_obj_chunk_chars6 : clean_obj_string_leaf6.toList = clean_obj_chunk6 := by rfl
def clean_obj_string_leaf7 : String := "    /* O"
theorem clean_obj_chunk_chars7 : clean_obj_string_leaf7.toList = clean_obj_chunk7 := by rfl
def clean_obj_string_leaf8 : String := "bject fi"
theorem clean_obj_chunk_chars8 : clean_obj_string_leaf8.toList = clean_obj_chunk8 := by rfl
def clean_obj_string_leaf9 : String := "elds fol"
theorem clean_obj_chunk_chars9 : clean_obj_string_leaf9.toList = clean_obj_chunk9 := by rfl
def clean_obj_string_leaf10 : String := "low:\n   "
theorem clean_obj_chunk_chars10 : clean_obj_string_leaf10.toList = clean_obj_chunk10 := by rfl
def clean_obj_string_leaf11 : String := "  * - Ob"
theorem clean_obj_chunk_chars11 : clean_obj_string_leaf11.toList = clean_obj_chunk11 := by rfl
def clean_obj_string_leaf12 : String := "ject poi"
theorem clean_obj_chunk_chars12 : clean_obj_string_leaf12.toList = clean_obj_chunk12 := by rfl
def clean_obj_string_leaf13 : String := "nters fi"
theorem clean_obj_chunk_chars13 : clean_obj_string_leaf13.toList = clean_obj_chunk13 := by rfl
def clean_obj_string_leaf14 : String := "rst (num"
theorem clean_obj_chunk_chars14 : clean_obj_string_leaf14.toList = clean_obj_chunk14 := by rfl
def clean_obj_string_leaf15 : String := "_objs co"
theorem clean_obj_chunk_chars15 : clean_obj_string_leaf15.toList = clean_obj_chunk15 := by rfl
def clean_obj_string_leaf16 : String := "unt)\n   "
theorem clean_obj_chunk_chars16 : clean_obj_string_leaf16.toList = clean_obj_chunk16 := by rfl
def clean_obj_string_leaf17 : String := "  * - Sc"
theorem clean_obj_chunk_chars17 : clean_obj_string_leaf17.toList = clean_obj_chunk17 := by rfl
def clean_obj_string_leaf18 : String := "alar fie"
theorem clean_obj_chunk_chars18 : clean_obj_string_leaf18.toList = clean_obj_chunk18 := by rfl
def clean_obj_string_leaf19 : String := "lds afte"
theorem clean_obj_chunk_chars19 : clean_obj_string_leaf19.toList = clean_obj_chunk19 := by rfl
def clean_obj_string_leaf20 : String := "r (size "
theorem clean_obj_chunk_chars20 : clean_obj_string_leaf20.toList = clean_obj_chunk20 := by rfl
def clean_obj_string_leaf21 : String := "varies b"
theorem clean_obj_chunk_chars21 : clean_obj_string_leaf21.toList = clean_obj_chunk21 := by rfl
def clean_obj_string_leaf22 : String := "y constr"
theorem clean_obj_chunk_chars22 : clean_obj_string_leaf22.toList = clean_obj_chunk22 := by rfl
def clean_obj_string_leaf23 : String := "uctor)\n "
theorem clean_obj_chunk_chars23 : clean_obj_string_leaf23.toList = clean_obj_chunk23 := by rfl
def clean_obj_string_leaf24 : String := "    */\n "
theorem clean_obj_chunk_chars24 : clean_obj_string_leaf24.toList = clean_obj_chunk24 := by rfl
def clean_obj_string_leaf25 : String := "   struc"
theorem clean_obj_chunk_chars25 : clean_obj_string_leaf25.toList = clean_obj_chunk25 := by rfl
def clean_obj_string_leaf26 : String := "t clean_"
theorem clean_obj_chunk_chars26 : clean_obj_string_leaf26.toList = clean_obj_chunk26 := by rfl
def clean_obj_string_leaf27 : String := "obj* fie"
theorem clean_obj_chunk_chars27 : clean_obj_string_leaf27.toList = clean_obj_chunk27 := by rfl
def clean_obj_string_leaf28 : String := "lds[];\n}"
theorem clean_obj_chunk_chars28 : clean_obj_string_leaf28.toList = clean_obj_chunk28 := by rfl
def clean_obj_string_leaf29 : String := " clean_o"
theorem clean_obj_chunk_chars29 : clean_obj_string_leaf29.toList = clean_obj_chunk29 := by rfl
def clean_obj_string_leaf30 : String := "bj;"
theorem clean_obj_chunk_chars30 : clean_obj_string_leaf30.toList = clean_obj_chunk30 := by rfl
def clean_obj_node_1_3 : String := clean_obj_string_leaf1 ++ clean_obj_string_leaf2
def clean_obj_node_1_3_chars : List Char := clean_obj_chunk1 ++ clean_obj_chunk2
theorem clean_obj_node_1_3_literal : clean_obj_node_1_3 = "struct clean_obj" := by
  unfold clean_obj_node_1_3
  cbv
theorem clean_obj_node_1_3_characters : clean_obj_node_1_3.toList = clean_obj_node_1_3_chars := by
  unfold clean_obj_node_1_3 clean_obj_node_1_3_chars
  rw [String.toList_append, clean_obj_chunk_chars1, clean_obj_chunk_chars2]
def clean_obj_node_0_3 : String := clean_obj_string_leaf0 ++ clean_obj_node_1_3
def clean_obj_node_0_3_chars : List Char := clean_obj_chunk0 ++ clean_obj_node_1_3_chars
theorem clean_obj_node_0_3_literal : clean_obj_node_0_3 = "typedef struct clean_obj" := by
  unfold clean_obj_node_0_3
  rw [clean_obj_node_1_3_literal]
  cbv
theorem clean_obj_node_0_3_characters : clean_obj_node_0_3.toList = clean_obj_node_0_3_chars := by
  unfold clean_obj_node_0_3 clean_obj_node_0_3_chars
  rw [String.toList_append, clean_obj_chunk_chars0, clean_obj_node_1_3_characters]
def clean_obj_node_3_5 : String := clean_obj_string_leaf3 ++ clean_obj_string_leaf4
def clean_obj_node_3_5_chars : List Char := clean_obj_chunk3 ++ clean_obj_chunk4
theorem clean_obj_node_3_5_literal : clean_obj_node_3_5 = " {\n    clean_obj" := by
  unfold clean_obj_node_3_5
  cbv
theorem clean_obj_node_3_5_characters : clean_obj_node_3_5.toList = clean_obj_node_3_5_chars := by
  unfold clean_obj_node_3_5 clean_obj_node_3_5_chars
  rw [String.toList_append, clean_obj_chunk_chars3, clean_obj_chunk_chars4]
def clean_obj_node_5_7 : String := clean_obj_string_leaf5 ++ clean_obj_string_leaf6
def clean_obj_node_5_7_chars : List Char := clean_obj_chunk5 ++ clean_obj_chunk6
theorem clean_obj_node_5_7_literal : clean_obj_node_5_7 = "_header header;\n" := by
  unfold clean_obj_node_5_7
  cbv
theorem clean_obj_node_5_7_characters : clean_obj_node_5_7.toList = clean_obj_node_5_7_chars := by
  unfold clean_obj_node_5_7 clean_obj_node_5_7_chars
  rw [String.toList_append, clean_obj_chunk_chars5, clean_obj_chunk_chars6]
def clean_obj_node_3_7 : String := clean_obj_node_3_5 ++ clean_obj_node_5_7
def clean_obj_node_3_7_chars : List Char := clean_obj_node_3_5_chars ++ clean_obj_node_5_7_chars
theorem clean_obj_node_3_7_literal : clean_obj_node_3_7 = " {\n    clean_obj_header header;\n" := by
  unfold clean_obj_node_3_7
  rw [clean_obj_node_3_5_literal]
  rw [clean_obj_node_5_7_literal]
  cbv
theorem clean_obj_node_3_7_characters : clean_obj_node_3_7.toList = clean_obj_node_3_7_chars := by
  unfold clean_obj_node_3_7 clean_obj_node_3_7_chars
  rw [String.toList_append, clean_obj_node_3_5_characters, clean_obj_node_5_7_characters]
def clean_obj_node_0_7 : String := clean_obj_node_0_3 ++ clean_obj_node_3_7
def clean_obj_node_0_7_chars : List Char := clean_obj_node_0_3_chars ++ clean_obj_node_3_7_chars
theorem clean_obj_node_0_7_literal : clean_obj_node_0_7 = "typedef struct clean_obj {\n    clean_obj_header header;\n" := by
  unfold clean_obj_node_0_7
  rw [clean_obj_node_0_3_literal]
  rw [clean_obj_node_3_7_literal]
  cbv
theorem clean_obj_node_0_7_characters : clean_obj_node_0_7.toList = clean_obj_node_0_7_chars := by
  unfold clean_obj_node_0_7 clean_obj_node_0_7_chars
  rw [String.toList_append, clean_obj_node_0_3_characters, clean_obj_node_3_7_characters]
def clean_obj_node_7_9 : String := clean_obj_string_leaf7 ++ clean_obj_string_leaf8
def clean_obj_node_7_9_chars : List Char := clean_obj_chunk7 ++ clean_obj_chunk8
theorem clean_obj_node_7_9_literal : clean_obj_node_7_9 = "    /* Object fi" := by
  unfold clean_obj_node_7_9
  cbv
theorem clean_obj_node_7_9_characters : clean_obj_node_7_9.toList = clean_obj_node_7_9_chars := by
  unfold clean_obj_node_7_9 clean_obj_node_7_9_chars
  rw [String.toList_append, clean_obj_chunk_chars7, clean_obj_chunk_chars8]
def clean_obj_node_9_11 : String := clean_obj_string_leaf9 ++ clean_obj_string_leaf10
def clean_obj_node_9_11_chars : List Char := clean_obj_chunk9 ++ clean_obj_chunk10
theorem clean_obj_node_9_11_literal : clean_obj_node_9_11 = "elds follow:\n   " := by
  unfold clean_obj_node_9_11
  cbv
theorem clean_obj_node_9_11_characters : clean_obj_node_9_11.toList = clean_obj_node_9_11_chars := by
  unfold clean_obj_node_9_11 clean_obj_node_9_11_chars
  rw [String.toList_append, clean_obj_chunk_chars9, clean_obj_chunk_chars10]
def clean_obj_node_7_11 : String := clean_obj_node_7_9 ++ clean_obj_node_9_11
def clean_obj_node_7_11_chars : List Char := clean_obj_node_7_9_chars ++ clean_obj_node_9_11_chars
theorem clean_obj_node_7_11_literal : clean_obj_node_7_11 = "    /* Object fields follow:\n   " := by
  unfold clean_obj_node_7_11
  rw [clean_obj_node_7_9_literal]
  rw [clean_obj_node_9_11_literal]
  cbv
theorem clean_obj_node_7_11_characters : clean_obj_node_7_11.toList = clean_obj_node_7_11_chars := by
  unfold clean_obj_node_7_11 clean_obj_node_7_11_chars
  rw [String.toList_append, clean_obj_node_7_9_characters, clean_obj_node_9_11_characters]
def clean_obj_node_11_13 : String := clean_obj_string_leaf11 ++ clean_obj_string_leaf12
def clean_obj_node_11_13_chars : List Char := clean_obj_chunk11 ++ clean_obj_chunk12
theorem clean_obj_node_11_13_literal : clean_obj_node_11_13 = "  * - Object poi" := by
  unfold clean_obj_node_11_13
  cbv
theorem clean_obj_node_11_13_characters : clean_obj_node_11_13.toList = clean_obj_node_11_13_chars := by
  unfold clean_obj_node_11_13 clean_obj_node_11_13_chars
  rw [String.toList_append, clean_obj_chunk_chars11, clean_obj_chunk_chars12]
def clean_obj_node_13_15 : String := clean_obj_string_leaf13 ++ clean_obj_string_leaf14
def clean_obj_node_13_15_chars : List Char := clean_obj_chunk13 ++ clean_obj_chunk14
theorem clean_obj_node_13_15_literal : clean_obj_node_13_15 = "nters first (num" := by
  unfold clean_obj_node_13_15
  cbv
theorem clean_obj_node_13_15_characters : clean_obj_node_13_15.toList = clean_obj_node_13_15_chars := by
  unfold clean_obj_node_13_15 clean_obj_node_13_15_chars
  rw [String.toList_append, clean_obj_chunk_chars13, clean_obj_chunk_chars14]
def clean_obj_node_11_15 : String := clean_obj_node_11_13 ++ clean_obj_node_13_15
def clean_obj_node_11_15_chars : List Char := clean_obj_node_11_13_chars ++ clean_obj_node_13_15_chars
theorem clean_obj_node_11_15_literal : clean_obj_node_11_15 = "  * - Object pointers first (num" := by
  unfold clean_obj_node_11_15
  rw [clean_obj_node_11_13_literal]
  rw [clean_obj_node_13_15_literal]
  cbv
theorem clean_obj_node_11_15_characters : clean_obj_node_11_15.toList = clean_obj_node_11_15_chars := by
  unfold clean_obj_node_11_15 clean_obj_node_11_15_chars
  rw [String.toList_append, clean_obj_node_11_13_characters, clean_obj_node_13_15_characters]
def clean_obj_node_7_15 : String := clean_obj_node_7_11 ++ clean_obj_node_11_15
def clean_obj_node_7_15_chars : List Char := clean_obj_node_7_11_chars ++ clean_obj_node_11_15_chars
theorem clean_obj_node_7_15_literal : clean_obj_node_7_15 = "    /* Object fields follow:\n     * - Object pointers first (num" := by
  unfold clean_obj_node_7_15
  rw [clean_obj_node_7_11_literal]
  rw [clean_obj_node_11_15_literal]
  cbv
theorem clean_obj_node_7_15_characters : clean_obj_node_7_15.toList = clean_obj_node_7_15_chars := by
  unfold clean_obj_node_7_15 clean_obj_node_7_15_chars
  rw [String.toList_append, clean_obj_node_7_11_characters, clean_obj_node_11_15_characters]
def clean_obj_node_0_15 : String := clean_obj_node_0_7 ++ clean_obj_node_7_15
def clean_obj_node_0_15_chars : List Char := clean_obj_node_0_7_chars ++ clean_obj_node_7_15_chars
theorem clean_obj_node_0_15_literal : clean_obj_node_0_15 = "typedef struct clean_obj {\n    clean_obj_header header;\n    /* Object fields follow:\n     * - Object pointers first (num" := by
  unfold clean_obj_node_0_15
  rw [clean_obj_node_0_7_literal]
  rw [clean_obj_node_7_15_literal]
  cbv
theorem clean_obj_node_0_15_characters : clean_obj_node_0_15.toList = clean_obj_node_0_15_chars := by
  unfold clean_obj_node_0_15 clean_obj_node_0_15_chars
  rw [String.toList_append, clean_obj_node_0_7_characters, clean_obj_node_7_15_characters]
def clean_obj_node_15_17 : String := clean_obj_string_leaf15 ++ clean_obj_string_leaf16
def clean_obj_node_15_17_chars : List Char := clean_obj_chunk15 ++ clean_obj_chunk16
theorem clean_obj_node_15_17_literal : clean_obj_node_15_17 = "_objs count)\n   " := by
  unfold clean_obj_node_15_17
  cbv
theorem clean_obj_node_15_17_characters : clean_obj_node_15_17.toList = clean_obj_node_15_17_chars := by
  unfold clean_obj_node_15_17 clean_obj_node_15_17_chars
  rw [String.toList_append, clean_obj_chunk_chars15, clean_obj_chunk_chars16]
def clean_obj_node_17_19 : String := clean_obj_string_leaf17 ++ clean_obj_string_leaf18
def clean_obj_node_17_19_chars : List Char := clean_obj_chunk17 ++ clean_obj_chunk18
theorem clean_obj_node_17_19_literal : clean_obj_node_17_19 = "  * - Scalar fie" := by
  unfold clean_obj_node_17_19
  cbv
theorem clean_obj_node_17_19_characters : clean_obj_node_17_19.toList = clean_obj_node_17_19_chars := by
  unfold clean_obj_node_17_19 clean_obj_node_17_19_chars
  rw [String.toList_append, clean_obj_chunk_chars17, clean_obj_chunk_chars18]
def clean_obj_node_15_19 : String := clean_obj_node_15_17 ++ clean_obj_node_17_19
def clean_obj_node_15_19_chars : List Char := clean_obj_node_15_17_chars ++ clean_obj_node_17_19_chars
theorem clean_obj_node_15_19_literal : clean_obj_node_15_19 = "_objs count)\n     * - Scalar fie" := by
  unfold clean_obj_node_15_19
  rw [clean_obj_node_15_17_literal]
  rw [clean_obj_node_17_19_literal]
  cbv
theorem clean_obj_node_15_19_characters : clean_obj_node_15_19.toList = clean_obj_node_15_19_chars := by
  unfold clean_obj_node_15_19 clean_obj_node_15_19_chars
  rw [String.toList_append, clean_obj_node_15_17_characters, clean_obj_node_17_19_characters]
def clean_obj_node_19_21 : String := clean_obj_string_leaf19 ++ clean_obj_string_leaf20
def clean_obj_node_19_21_chars : List Char := clean_obj_chunk19 ++ clean_obj_chunk20
theorem clean_obj_node_19_21_literal : clean_obj_node_19_21 = "lds after (size " := by
  unfold clean_obj_node_19_21
  cbv
theorem clean_obj_node_19_21_characters : clean_obj_node_19_21.toList = clean_obj_node_19_21_chars := by
  unfold clean_obj_node_19_21 clean_obj_node_19_21_chars
  rw [String.toList_append, clean_obj_chunk_chars19, clean_obj_chunk_chars20]
def clean_obj_node_21_23 : String := clean_obj_string_leaf21 ++ clean_obj_string_leaf22
def clean_obj_node_21_23_chars : List Char := clean_obj_chunk21 ++ clean_obj_chunk22
theorem clean_obj_node_21_23_literal : clean_obj_node_21_23 = "varies by constr" := by
  unfold clean_obj_node_21_23
  cbv
theorem clean_obj_node_21_23_characters : clean_obj_node_21_23.toList = clean_obj_node_21_23_chars := by
  unfold clean_obj_node_21_23 clean_obj_node_21_23_chars
  rw [String.toList_append, clean_obj_chunk_chars21, clean_obj_chunk_chars22]
def clean_obj_node_19_23 : String := clean_obj_node_19_21 ++ clean_obj_node_21_23
def clean_obj_node_19_23_chars : List Char := clean_obj_node_19_21_chars ++ clean_obj_node_21_23_chars
theorem clean_obj_node_19_23_literal : clean_obj_node_19_23 = "lds after (size varies by constr" := by
  unfold clean_obj_node_19_23
  rw [clean_obj_node_19_21_literal]
  rw [clean_obj_node_21_23_literal]
  cbv
theorem clean_obj_node_19_23_characters : clean_obj_node_19_23.toList = clean_obj_node_19_23_chars := by
  unfold clean_obj_node_19_23 clean_obj_node_19_23_chars
  rw [String.toList_append, clean_obj_node_19_21_characters, clean_obj_node_21_23_characters]
def clean_obj_node_15_23 : String := clean_obj_node_15_19 ++ clean_obj_node_19_23
def clean_obj_node_15_23_chars : List Char := clean_obj_node_15_19_chars ++ clean_obj_node_19_23_chars
theorem clean_obj_node_15_23_literal : clean_obj_node_15_23 = "_objs count)\n     * - Scalar fields after (size varies by constr" := by
  unfold clean_obj_node_15_23
  rw [clean_obj_node_15_19_literal]
  rw [clean_obj_node_19_23_literal]
  cbv
theorem clean_obj_node_15_23_characters : clean_obj_node_15_23.toList = clean_obj_node_15_23_chars := by
  unfold clean_obj_node_15_23 clean_obj_node_15_23_chars
  rw [String.toList_append, clean_obj_node_15_19_characters, clean_obj_node_19_23_characters]
def clean_obj_node_23_25 : String := clean_obj_string_leaf23 ++ clean_obj_string_leaf24
def clean_obj_node_23_25_chars : List Char := clean_obj_chunk23 ++ clean_obj_chunk24
theorem clean_obj_node_23_25_literal : clean_obj_node_23_25 = "uctor)\n     */\n " := by
  unfold clean_obj_node_23_25
  cbv
theorem clean_obj_node_23_25_characters : clean_obj_node_23_25.toList = clean_obj_node_23_25_chars := by
  unfold clean_obj_node_23_25 clean_obj_node_23_25_chars
  rw [String.toList_append, clean_obj_chunk_chars23, clean_obj_chunk_chars24]
def clean_obj_node_25_27 : String := clean_obj_string_leaf25 ++ clean_obj_string_leaf26
def clean_obj_node_25_27_chars : List Char := clean_obj_chunk25 ++ clean_obj_chunk26
theorem clean_obj_node_25_27_literal : clean_obj_node_25_27 = "   struct clean_" := by
  unfold clean_obj_node_25_27
  cbv
theorem clean_obj_node_25_27_characters : clean_obj_node_25_27.toList = clean_obj_node_25_27_chars := by
  unfold clean_obj_node_25_27 clean_obj_node_25_27_chars
  rw [String.toList_append, clean_obj_chunk_chars25, clean_obj_chunk_chars26]
def clean_obj_node_23_27 : String := clean_obj_node_23_25 ++ clean_obj_node_25_27
def clean_obj_node_23_27_chars : List Char := clean_obj_node_23_25_chars ++ clean_obj_node_25_27_chars
theorem clean_obj_node_23_27_literal : clean_obj_node_23_27 = "uctor)\n     */\n    struct clean_" := by
  unfold clean_obj_node_23_27
  rw [clean_obj_node_23_25_literal]
  rw [clean_obj_node_25_27_literal]
  cbv
theorem clean_obj_node_23_27_characters : clean_obj_node_23_27.toList = clean_obj_node_23_27_chars := by
  unfold clean_obj_node_23_27 clean_obj_node_23_27_chars
  rw [String.toList_append, clean_obj_node_23_25_characters, clean_obj_node_25_27_characters]
def clean_obj_node_27_29 : String := clean_obj_string_leaf27 ++ clean_obj_string_leaf28
def clean_obj_node_27_29_chars : List Char := clean_obj_chunk27 ++ clean_obj_chunk28
theorem clean_obj_node_27_29_literal : clean_obj_node_27_29 = "obj* fields[];\n}" := by
  unfold clean_obj_node_27_29
  cbv
theorem clean_obj_node_27_29_characters : clean_obj_node_27_29.toList = clean_obj_node_27_29_chars := by
  unfold clean_obj_node_27_29 clean_obj_node_27_29_chars
  rw [String.toList_append, clean_obj_chunk_chars27, clean_obj_chunk_chars28]
def clean_obj_node_29_31 : String := clean_obj_string_leaf29 ++ clean_obj_string_leaf30
def clean_obj_node_29_31_chars : List Char := clean_obj_chunk29 ++ clean_obj_chunk30
theorem clean_obj_node_29_31_literal : clean_obj_node_29_31 = " clean_obj;" := by
  unfold clean_obj_node_29_31
  cbv
theorem clean_obj_node_29_31_characters : clean_obj_node_29_31.toList = clean_obj_node_29_31_chars := by
  unfold clean_obj_node_29_31 clean_obj_node_29_31_chars
  rw [String.toList_append, clean_obj_chunk_chars29, clean_obj_chunk_chars30]
def clean_obj_node_27_31 : String := clean_obj_node_27_29 ++ clean_obj_node_29_31
def clean_obj_node_27_31_chars : List Char := clean_obj_node_27_29_chars ++ clean_obj_node_29_31_chars
theorem clean_obj_node_27_31_literal : clean_obj_node_27_31 = "obj* fields[];\n} clean_obj;" := by
  unfold clean_obj_node_27_31
  rw [clean_obj_node_27_29_literal]
  rw [clean_obj_node_29_31_literal]
  cbv
theorem clean_obj_node_27_31_characters : clean_obj_node_27_31.toList = clean_obj_node_27_31_chars := by
  unfold clean_obj_node_27_31 clean_obj_node_27_31_chars
  rw [String.toList_append, clean_obj_node_27_29_characters, clean_obj_node_29_31_characters]
def clean_obj_node_23_31 : String := clean_obj_node_23_27 ++ clean_obj_node_27_31
def clean_obj_node_23_31_chars : List Char := clean_obj_node_23_27_chars ++ clean_obj_node_27_31_chars
theorem clean_obj_node_23_31_literal : clean_obj_node_23_31 = "uctor)\n     */\n    struct clean_obj* fields[];\n} clean_obj;" := by
  unfold clean_obj_node_23_31
  rw [clean_obj_node_23_27_literal]
  rw [clean_obj_node_27_31_literal]
  cbv
theorem clean_obj_node_23_31_characters : clean_obj_node_23_31.toList = clean_obj_node_23_31_chars := by
  unfold clean_obj_node_23_31 clean_obj_node_23_31_chars
  rw [String.toList_append, clean_obj_node_23_27_characters, clean_obj_node_27_31_characters]
def clean_obj_node_15_31 : String := clean_obj_node_15_23 ++ clean_obj_node_23_31
def clean_obj_node_15_31_chars : List Char := clean_obj_node_15_23_chars ++ clean_obj_node_23_31_chars
theorem clean_obj_node_15_31_literal : clean_obj_node_15_31 = "_objs count)\n     * - Scalar fields after (size varies by constructor)\n     */\n    struct clean_obj* fields[];\n} clean_obj;" := by
  unfold clean_obj_node_15_31
  rw [clean_obj_node_15_23_literal]
  rw [clean_obj_node_23_31_literal]
  cbv
theorem clean_obj_node_15_31_characters : clean_obj_node_15_31.toList = clean_obj_node_15_31_chars := by
  unfold clean_obj_node_15_31 clean_obj_node_15_31_chars
  rw [String.toList_append, clean_obj_node_15_23_characters, clean_obj_node_23_31_characters]
def clean_obj_node_0_31 : String := clean_obj_node_0_15 ++ clean_obj_node_15_31
def clean_obj_node_0_31_chars : List Char := clean_obj_node_0_15_chars ++ clean_obj_node_15_31_chars
theorem clean_obj_node_0_31_literal : clean_obj_node_0_31 = "typedef struct clean_obj {\n    clean_obj_header header;\n    /* Object fields follow:\n     * - Object pointers first (num_objs count)\n     * - Scalar fields after (size varies by constructor)\n     */\n    struct clean_obj* fields[];\n} clean_obj;" := by
  unfold clean_obj_node_0_31
  rw [clean_obj_node_0_15_literal]
  rw [clean_obj_node_15_31_literal]
  cbv
theorem clean_obj_node_0_31_characters : clean_obj_node_0_31.toList = clean_obj_node_0_31_chars := by
  unfold clean_obj_node_0_31 clean_obj_node_0_31_chars
  rw [String.toList_append, clean_obj_node_0_15_characters, clean_obj_node_15_31_characters]
theorem clean_obj_string_exact : clean_obj_node_0_31 = C11ActualDeclarationData.clean_obj_0 := by
  exact clean_obj_node_0_31_literal
theorem clean_obj_flatten_exact : clean_obj_node_0_31_chars = clean_obj_chunks.flatten := by
  simp only [clean_obj_node_1_3_chars, clean_obj_node_0_3_chars, clean_obj_node_3_5_chars, clean_obj_node_5_7_chars, clean_obj_node_3_7_chars, clean_obj_node_0_7_chars, clean_obj_node_7_9_chars, clean_obj_node_9_11_chars, clean_obj_node_7_11_chars, clean_obj_node_11_13_chars, clean_obj_node_13_15_chars, clean_obj_node_11_15_chars, clean_obj_node_7_15_chars, clean_obj_node_0_15_chars, clean_obj_node_15_17_chars, clean_obj_node_17_19_chars, clean_obj_node_15_19_chars, clean_obj_node_19_21_chars, clean_obj_node_21_23_chars, clean_obj_node_19_23_chars, clean_obj_node_15_23_chars, clean_obj_node_23_25_chars, clean_obj_node_25_27_chars, clean_obj_node_23_27_chars, clean_obj_node_27_29_chars, clean_obj_node_29_31_chars, clean_obj_node_27_31_chars, clean_obj_node_23_31_chars, clean_obj_node_15_31_chars, clean_obj_node_0_31_chars, clean_obj_chunks, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]
theorem clean_obj_source_lex : tokenize C11ActualDeclarationData.clean_obj_0 = some clean_obj_tokens := by
  unfold tokenize
  rw [← clean_obj_string_exact, clean_obj_node_0_31_characters, clean_obj_flatten_exact]
  exact clean_obj_characters_lex

end C11DeclarationCuts
