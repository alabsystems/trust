-- Copyright 2026 Andrew Yates | Apache-2.0
import C11DirectiveLexer
import C11AssertHeaderData
import Init.Data.String.Lemmas.Basic
namespace C11AssertHeaderCuts
open C11DirectiveLexer

def assertHeader_state0 : Option State := some initial
def assertHeader_chunk0 : List Char := [Char.ofNat 47, Char.ofNat 42, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 67, Char.ofNat 111]
def assertHeader_state1 : Option State := some { base := { mode := .block, word := [], reversed := ["\n"] }, pending := .none }
theorem assertHeader_cut0 : feed (some initial) assertHeader_chunk0 = assertHeader_state1 := by rfl
def assertHeader_chunk1 : List Char := [Char.ofNat 112, Char.ofNat 121, Char.ofNat 114, Char.ofNat 105, Char.ofNat 103, Char.ofNat 104, Char.ofNat 116, Char.ofNat 32]
def assertHeader_state2 : Option State := some { base := { mode := .block, word := [], reversed := ["\n"] }, pending := .none }
theorem assertHeader_cut1 : feed assertHeader_state1 assertHeader_chunk1 = assertHeader_state2 := by rfl
def assertHeader_chunk2 : List Char := [Char.ofNat 40, Char.ofNat 99, Char.ofNat 41, Char.ofNat 32, Char.ofNat 50, Char.ofNat 48, Char.ofNat 50, Char.ofNat 51]
def assertHeader_state3 : Option State := some { base := { mode := .block, word := [], reversed := ["\n"] }, pending := .none }
theorem assertHeader_cut2 : feed assertHeader_state2 assertHeader_chunk2 = assertHeader_state3 := by rfl
def assertHeader_chunk3 : List Char := [Char.ofNat 32, Char.ofNat 65, Char.ofNat 112, Char.ofNat 112, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 73]
def assertHeader_state4 : Option State := some { base := { mode := .block, word := [], reversed := ["\n"] }, pending := .none }
theorem assertHeader_cut3 : feed assertHeader_state3 assertHeader_chunk3 = assertHeader_state4 := by rfl
def assertHeader_chunk4 : List Char := [Char.ofNat 110, Char.ofNat 99, Char.ofNat 46, Char.ofNat 32, Char.ofNat 65, Char.ofNat 108, Char.ofNat 108, Char.ofNat 32]
def assertHeader_state5 : Option State := some { base := { mode := .block, word := [], reversed := ["\n"] }, pending := .none }
theorem assertHeader_cut4 : feed assertHeader_state4 assertHeader_chunk4 = assertHeader_state5 := by rfl
def assertHeader_chunk5 : List Char := [Char.ofNat 114, Char.ofNat 105, Char.ofNat 103, Char.ofNat 104, Char.ofNat 116, Char.ofNat 115, Char.ofNat 32, Char.ofNat 114]
def assertHeader_state6 : Option State := some { base := { mode := .block, word := [], reversed := ["\n"] }, pending := .none }
theorem assertHeader_cut5 : feed assertHeader_state5 assertHeader_chunk5 = assertHeader_state6 := by rfl
def assertHeader_chunk6 : List Char := [Char.ofNat 101, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101, Char.ofNat 100, Char.ofNat 46]
def assertHeader_state7 : Option State := some { base := { mode := .block, word := [], reversed := ["\n"] }, pending := .none }
theorem assertHeader_cut6 : feed assertHeader_state6 assertHeader_chunk6 = assertHeader_state7 := by rfl
def assertHeader_chunk7 : List Char := [Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 64]
def assertHeader_state8 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut7 : feed assertHeader_state7 assertHeader_chunk7 = assertHeader_state8 := by rfl
def assertHeader_chunk8 : List Char := [Char.ofNat 65, Char.ofNat 80, Char.ofNat 80, Char.ofNat 76, Char.ofNat 69, Char.ofNat 95, Char.ofNat 76, Char.ofNat 73]
def assertHeader_state9 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut8 : feed assertHeader_state8 assertHeader_chunk8 = assertHeader_state9 := by rfl
def assertHeader_chunk9 : List Char := [Char.ofNat 67, Char.ofNat 69, Char.ofNat 78, Char.ofNat 83, Char.ofNat 69, Char.ofNat 95, Char.ofNat 72, Char.ofNat 69]
def assertHeader_state10 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut9 : feed assertHeader_state9 assertHeader_chunk9 = assertHeader_state10 := by rfl
def assertHeader_chunk10 : List Char := [Char.ofNat 65, Char.ofNat 68, Char.ofNat 69, Char.ofNat 82, Char.ofNat 95, Char.ofNat 83, Char.ofNat 84, Char.ofNat 65]
def assertHeader_state11 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut10 : feed assertHeader_state10 assertHeader_chunk10 = assertHeader_state11 := by rfl
def assertHeader_chunk11 : List Char := [Char.ofNat 82, Char.ofNat 84, Char.ofNat 64, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 10, Char.ofNat 32]
def assertHeader_state12 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut11 : feed assertHeader_state11 assertHeader_chunk11 = assertHeader_state12 := by rfl
def assertHeader_chunk12 : List Char := [Char.ofNat 42, Char.ofNat 32, Char.ofNat 84, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 32, Char.ofNat 102]
def assertHeader_state13 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut12 : feed assertHeader_state12 assertHeader_chunk12 = assertHeader_state13 := by rfl
def assertHeader_chunk13 : List Char := [Char.ofNat 105, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 99, Char.ofNat 111, Char.ofNat 110, Char.ofNat 116]
def assertHeader_state14 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut13 : feed assertHeader_state13 assertHeader_chunk13 = assertHeader_state14 := by rfl
def assertHeader_chunk14 : List Char := [Char.ofNat 97, Char.ofNat 105, Char.ofNat 110, Char.ofNat 115, Char.ofNat 32, Char.ofNat 79, Char.ofNat 114, Char.ofNat 105]
def assertHeader_state15 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut14 : feed assertHeader_state14 assertHeader_chunk14 = assertHeader_state15 := by rfl
def assertHeader_chunk15 : List Char := [Char.ofNat 103, Char.ofNat 105, Char.ofNat 110, Char.ofNat 97, Char.ofNat 108, Char.ofNat 32, Char.ofNat 67, Char.ofNat 111]
def assertHeader_state16 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut15 : feed assertHeader_state15 assertHeader_chunk15 = assertHeader_state16 := by rfl
def assertHeader_chunk16 : List Char := [Char.ofNat 100, Char.ofNat 101, Char.ofNat 32, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 47, Char.ofNat 111]
def assertHeader_state17 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut16 : feed assertHeader_state16 assertHeader_chunk16 = assertHeader_state17 := by rfl
def assertHeader_chunk17 : List Char := [Char.ofNat 114, Char.ofNat 32, Char.ofNat 77, Char.ofNat 111, Char.ofNat 100, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105]
def assertHeader_state18 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut17 : feed assertHeader_state17 assertHeader_chunk17 = assertHeader_state18 := by rfl
def assertHeader_chunk18 : List Char := [Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110, Char.ofNat 115, Char.ofNat 32]
def assertHeader_state19 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut18 : feed assertHeader_state18 assertHeader_chunk18 = assertHeader_state19 := by rfl
def assertHeader_chunk19 : List Char := [Char.ofNat 111, Char.ofNat 102, Char.ofNat 32, Char.ofNat 79, Char.ofNat 114, Char.ofNat 105, Char.ofNat 103, Char.ofNat 105]
def assertHeader_state20 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut19 : feed assertHeader_state19 assertHeader_chunk19 = assertHeader_state20 := by rfl
def assertHeader_chunk20 : List Char := [Char.ofNat 110, Char.ofNat 97, Char.ofNat 108, Char.ofNat 32, Char.ofNat 67, Char.ofNat 111, Char.ofNat 100, Char.ofNat 101]
def assertHeader_state21 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut20 : feed assertHeader_state20 assertHeader_chunk20 = assertHeader_state21 := by rfl
def assertHeader_chunk21 : List Char := [Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 97, Char.ofNat 115, Char.ofNat 32, Char.ofNat 100]
def assertHeader_state22 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut21 : feed assertHeader_state21 assertHeader_chunk21 = assertHeader_state22 := by rfl
def assertHeader_chunk22 : List Char := [Char.ofNat 101, Char.ofNat 102, Char.ofNat 105, Char.ofNat 110, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 105]
def assertHeader_state23 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut22 : feed assertHeader_state22 assertHeader_chunk22 = assertHeader_state23 := by rfl
def assertHeader_chunk23 : List Char := [Char.ofNat 110, Char.ofNat 32, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104]
def assertHeader_state24 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut23 : feed assertHeader_state23 assertHeader_chunk23 = assertHeader_state24 := by rfl
def assertHeader_chunk24 : List Char := [Char.ofNat 97, Char.ofNat 116, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115]
def assertHeader_state25 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut24 : feed assertHeader_state24 assertHeader_chunk24 = assertHeader_state25 := by rfl
def assertHeader_chunk25 : List Char := [Char.ofNat 117, Char.ofNat 98, Char.ofNat 106, Char.ofNat 101, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 116]
def assertHeader_state26 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut25 : feed assertHeader_state25 assertHeader_chunk25 = assertHeader_state26 := by rfl
def assertHeader_chunk26 : List Char := [Char.ofNat 111, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 101, Char.ofNat 32, Char.ofNat 65, Char.ofNat 112]
def assertHeader_state27 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut26 : feed assertHeader_state26 assertHeader_chunk26 = assertHeader_state27 := by rfl
def assertHeader_chunk27 : List Char := [Char.ofNat 112, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 80, Char.ofNat 117, Char.ofNat 98, Char.ofNat 108]
def assertHeader_state28 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut27 : feed assertHeader_state27 assertHeader_chunk27 = assertHeader_state28 := by rfl
def assertHeader_chunk28 : List Char := [Char.ofNat 105, Char.ofNat 99, Char.ofNat 32, Char.ofNat 83, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 99]
def assertHeader_state29 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut28 : feed assertHeader_state28 assertHeader_chunk28 = assertHeader_state29 := by rfl
def assertHeader_chunk29 : List Char := [Char.ofNat 101, Char.ofNat 32, Char.ofNat 76, Char.ofNat 105, Char.ofNat 99, Char.ofNat 101, Char.ofNat 110, Char.ofNat 115]
def assertHeader_state30 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut29 : feed assertHeader_state29 assertHeader_chunk29 = assertHeader_state30 := by rfl
def assertHeader_chunk30 : List Char := [Char.ofNat 101, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 86, Char.ofNat 101, Char.ofNat 114]
def assertHeader_state31 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut30 : feed assertHeader_state30 assertHeader_chunk30 = assertHeader_state31 := by rfl
def assertHeader_chunk31 : List Char := [Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110, Char.ofNat 32, Char.ofNat 50, Char.ofNat 46, Char.ofNat 48]
def assertHeader_state32 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut31 : feed assertHeader_state31 assertHeader_chunk31 = assertHeader_state32 := by rfl
def assertHeader_chunk32 : List Char := [Char.ofNat 32, Char.ofNat 40, Char.ofNat 116, Char.ofNat 104, Char.ofNat 101, Char.ofNat 32, Char.ofNat 39, Char.ofNat 76]
def assertHeader_state33 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut32 : feed assertHeader_state32 assertHeader_chunk32 = assertHeader_state33 := by rfl
def assertHeader_chunk33 : List Char := [Char.ofNat 105, Char.ofNat 99, Char.ofNat 101, Char.ofNat 110, Char.ofNat 115, Char.ofNat 101, Char.ofNat 39, Char.ofNat 41]
def assertHeader_state34 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut33 : feed assertHeader_state33 assertHeader_chunk33 = assertHeader_state34 := by rfl
def assertHeader_chunk34 : List Char := [Char.ofNat 46, Char.ofNat 32, Char.ofNat 89, Char.ofNat 111, Char.ofNat 117, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97]
def assertHeader_state35 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut34 : feed assertHeader_state34 assertHeader_chunk34 = assertHeader_state35 := by rfl
def assertHeader_chunk35 : List Char := [Char.ofNat 121, Char.ofNat 32, Char.ofNat 110, Char.ofNat 111, Char.ofNat 116, Char.ofNat 32, Char.ofNat 117, Char.ofNat 115]
def assertHeader_state36 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut35 : feed assertHeader_state35 assertHeader_chunk35 = assertHeader_state36 := by rfl
def assertHeader_chunk36 : List Char := [Char.ofNat 101, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 32, Char.ofNat 102]
def assertHeader_state37 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut36 : feed assertHeader_state36 assertHeader_chunk36 = assertHeader_state37 := by rfl
def assertHeader_chunk37 : List Char := [Char.ofNat 105, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 101, Char.ofNat 120, Char.ofNat 99, Char.ofNat 101]
def assertHeader_state38 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut37 : feed assertHeader_state37 assertHeader_chunk37 = assertHeader_state38 := by rfl
def assertHeader_chunk38 : List Char := [Char.ofNat 112, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42]
def assertHeader_state39 : Option State := some { base := { mode := .star, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut38 : feed assertHeader_state38 assertHeader_chunk38 = assertHeader_state39 := by rfl
def assertHeader_chunk39 : List Char := [Char.ofNat 32, Char.ofNat 99, Char.ofNat 111, Char.ofNat 109, Char.ofNat 112, Char.ofNat 108, Char.ofNat 105, Char.ofNat 97]
def assertHeader_state40 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut39 : feed assertHeader_state39 assertHeader_chunk39 = assertHeader_state40 := by rfl
def assertHeader_chunk40 : List Char := [Char.ofNat 110, Char.ofNat 99, Char.ofNat 101, Char.ofNat 32, Char.ofNat 119, Char.ofNat 105, Char.ofNat 116, Char.ofNat 104]
def assertHeader_state41 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut40 : feed assertHeader_state40 assertHeader_chunk40 = assertHeader_state41 := by rfl
def assertHeader_chunk41 : List Char := [Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 101, Char.ofNat 32, Char.ofNat 76, Char.ofNat 105, Char.ofNat 99]
def assertHeader_state42 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut41 : feed assertHeader_state41 assertHeader_chunk41 = assertHeader_state42 := by rfl
def assertHeader_chunk42 : List Char := [Char.ofNat 101, Char.ofNat 110, Char.ofNat 115, Char.ofNat 101, Char.ofNat 46, Char.ofNat 32, Char.ofNat 80, Char.ofNat 108]
def assertHeader_state43 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut42 : feed assertHeader_state42 assertHeader_chunk42 = assertHeader_state43 := by rfl
def assertHeader_chunk43 : List Char := [Char.ofNat 101, Char.ofNat 97, Char.ofNat 115, Char.ofNat 101, Char.ofNat 32, Char.ofNat 111, Char.ofNat 98, Char.ofNat 116]
def assertHeader_state44 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut43 : feed assertHeader_state43 assertHeader_chunk43 = assertHeader_state44 := by rfl
def assertHeader_chunk44 : List Char := [Char.ofNat 97, Char.ofNat 105, Char.ofNat 110, Char.ofNat 32, Char.ofNat 97, Char.ofNat 32, Char.ofNat 99, Char.ofNat 111]
def assertHeader_state45 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut44 : feed assertHeader_state44 assertHeader_chunk44 = assertHeader_state45 := by rfl
def assertHeader_chunk45 : List Char := [Char.ofNat 112, Char.ofNat 121, Char.ofNat 32, Char.ofNat 111, Char.ofNat 102, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104]
def assertHeader_state46 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut45 : feed assertHeader_state45 assertHeader_chunk45 = assertHeader_state46 := by rfl
def assertHeader_chunk46 : List Char := [Char.ofNat 101, Char.ofNat 32, Char.ofNat 76, Char.ofNat 105, Char.ofNat 99, Char.ofNat 101, Char.ofNat 110, Char.ofNat 115]
def assertHeader_state47 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut46 : feed assertHeader_state46 assertHeader_chunk46 = assertHeader_state47 := by rfl
def assertHeader_chunk47 : List Char := [Char.ofNat 101, Char.ofNat 32, Char.ofNat 97, Char.ofNat 116, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32]
def assertHeader_state48 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut47 : feed assertHeader_state47 assertHeader_chunk47 = assertHeader_state48 := by rfl
def assertHeader_chunk48 : List Char := [Char.ofNat 104, Char.ofNat 116, Char.ofNat 116, Char.ofNat 112, Char.ofNat 58, Char.ofNat 47, Char.ofNat 47, Char.ofNat 119]
def assertHeader_state49 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut48 : feed assertHeader_state48 assertHeader_chunk48 = assertHeader_state49 := by rfl
def assertHeader_chunk49 : List Char := [Char.ofNat 119, Char.ofNat 119, Char.ofNat 46, Char.ofNat 111, Char.ofNat 112, Char.ofNat 101, Char.ofNat 110, Char.ofNat 115]
def assertHeader_state50 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut49 : feed assertHeader_state49 assertHeader_chunk49 = assertHeader_state50 := by rfl
def assertHeader_chunk50 : List Char := [Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 99, Char.ofNat 101, Char.ofNat 46, Char.ofNat 97, Char.ofNat 112]
def assertHeader_state51 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut50 : feed assertHeader_state50 assertHeader_chunk50 = assertHeader_state51 := by rfl
def assertHeader_chunk51 : List Char := [Char.ofNat 112, Char.ofNat 108, Char.ofNat 101, Char.ofNat 46, Char.ofNat 99, Char.ofNat 111, Char.ofNat 109, Char.ofNat 47]
def assertHeader_state52 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut51 : feed assertHeader_state51 assertHeader_chunk51 = assertHeader_state52 := by rfl
def assertHeader_chunk52 : List Char := [Char.ofNat 97, Char.ofNat 112, Char.ofNat 115, Char.ofNat 108, Char.ofNat 47, Char.ofNat 32, Char.ofNat 97, Char.ofNat 110]
def assertHeader_state53 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut52 : feed assertHeader_state52 assertHeader_chunk52 = assertHeader_state53 := by rfl
def assertHeader_chunk53 : List Char := [Char.ofNat 100, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 97, Char.ofNat 100, Char.ofNat 32, Char.ofNat 105]
def assertHeader_state54 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut53 : feed assertHeader_state53 assertHeader_chunk53 = assertHeader_state54 := by rfl
def assertHeader_chunk54 : List Char := [Char.ofNat 116, Char.ofNat 32, Char.ofNat 98, Char.ofNat 101, Char.ofNat 102, Char.ofNat 111, Char.ofNat 114, Char.ofNat 101]
def assertHeader_state55 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut54 : feed assertHeader_state54 assertHeader_chunk54 = assertHeader_state55 := by rfl
def assertHeader_chunk55 : List Char := [Char.ofNat 32, Char.ofNat 117, Char.ofNat 115, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 32, Char.ofNat 116]
def assertHeader_state56 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut55 : feed assertHeader_state55 assertHeader_chunk55 = assertHeader_state56 := by rfl
def assertHeader_chunk56 : List Char := [Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 102]
def assertHeader_state57 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut56 : feed assertHeader_state56 assertHeader_chunk56 = assertHeader_state57 := by rfl
def assertHeader_chunk57 : List Char := [Char.ofNat 105, Char.ofNat 108, Char.ofNat 101, Char.ofNat 46, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 10]
def assertHeader_state58 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut57 : feed assertHeader_state57 assertHeader_chunk57 = assertHeader_state58 := by rfl
def assertHeader_chunk58 : List Char := [Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 84, Char.ofNat 104, Char.ofNat 101, Char.ofNat 32, Char.ofNat 79]
def assertHeader_state59 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut58 : feed assertHeader_state58 assertHeader_chunk58 = assertHeader_state59 := by rfl
def assertHeader_chunk59 : List Char := [Char.ofNat 114, Char.ofNat 105, Char.ofNat 103, Char.ofNat 105, Char.ofNat 110, Char.ofNat 97, Char.ofNat 108, Char.ofNat 32]
def assertHeader_state60 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut59 : feed assertHeader_state59 assertHeader_chunk59 = assertHeader_state60 := by rfl
def assertHeader_chunk60 : List Char := [Char.ofNat 67, Char.ofNat 111, Char.ofNat 100, Char.ofNat 101, Char.ofNat 32, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100]
def assertHeader_state61 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut60 : feed assertHeader_state60 assertHeader_chunk60 = assertHeader_state61 := by rfl
def assertHeader_chunk61 : List Char := [Char.ofNat 32, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 32, Char.ofNat 115, Char.ofNat 111, Char.ofNat 102]
def assertHeader_state62 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut61 : feed assertHeader_state61 assertHeader_chunk61 = assertHeader_state62 := by rfl
def assertHeader_chunk62 : List Char := [Char.ofNat 116, Char.ofNat 119, Char.ofNat 97, Char.ofNat 114, Char.ofNat 101, Char.ofNat 32, Char.ofNat 100, Char.ofNat 105]
def assertHeader_state63 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut62 : feed assertHeader_state62 assertHeader_chunk62 = assertHeader_state63 := by rfl
def assertHeader_chunk63 : List Char := [Char.ofNat 115, Char.ofNat 116, Char.ofNat 114, Char.ofNat 105, Char.ofNat 98, Char.ofNat 117, Char.ofNat 116, Char.ofNat 101]
def assertHeader_state64 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut63 : feed assertHeader_state63 assertHeader_chunk63 = assertHeader_state64 := by rfl
def assertHeader_chunk64 : List Char := [Char.ofNat 100, Char.ofNat 32, Char.ofNat 117, Char.ofNat 110, Char.ofNat 100, Char.ofNat 101, Char.ofNat 114, Char.ofNat 32]
def assertHeader_state65 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut64 : feed assertHeader_state64 assertHeader_chunk64 = assertHeader_state65 := by rfl
def assertHeader_chunk65 : List Char := [Char.ofNat 116, Char.ofNat 104, Char.ofNat 101, Char.ofNat 32, Char.ofNat 76, Char.ofNat 105, Char.ofNat 99, Char.ofNat 101]
def assertHeader_state66 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut65 : feed assertHeader_state65 assertHeader_chunk65 = assertHeader_state66 := by rfl
def assertHeader_chunk66 : List Char := [Char.ofNat 110, Char.ofNat 115, Char.ofNat 101, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 101, Char.ofNat 10]
def assertHeader_state67 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut66 : feed assertHeader_state66 assertHeader_chunk66 = assertHeader_state67 := by rfl
def assertHeader_chunk67 : List Char := [Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 100, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 114]
def assertHeader_state68 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut67 : feed assertHeader_state67 assertHeader_chunk67 = assertHeader_state68 := by rfl
def assertHeader_chunk68 : List Char := [Char.ofNat 105, Char.ofNat 98, Char.ofNat 117, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 111]
def assertHeader_state69 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut68 : feed assertHeader_state68 assertHeader_chunk68 = assertHeader_state69 := by rfl
def assertHeader_chunk69 : List Char := [Char.ofNat 110, Char.ofNat 32, Char.ofNat 97, Char.ofNat 110, Char.ofNat 32, Char.ofNat 39, Char.ofNat 65, Char.ofNat 83]
def assertHeader_state70 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut69 : feed assertHeader_state69 assertHeader_chunk69 = assertHeader_state70 := by rfl
def assertHeader_chunk70 : List Char := [Char.ofNat 32, Char.ofNat 73, Char.ofNat 83, Char.ofNat 39, Char.ofNat 32, Char.ofNat 98, Char.ofNat 97, Char.ofNat 115]
def assertHeader_state71 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut70 : feed assertHeader_state70 assertHeader_chunk70 = assertHeader_state71 := by rfl
def assertHeader_chunk71 : List Char := [Char.ofNat 105, Char.ofNat 115, Char.ofNat 44, Char.ofNat 32, Char.ofNat 87, Char.ofNat 73, Char.ofNat 84, Char.ofNat 72]
def assertHeader_state72 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut71 : feed assertHeader_state71 assertHeader_chunk71 = assertHeader_state72 := by rfl
def assertHeader_chunk72 : List Char := [Char.ofNat 79, Char.ofNat 85, Char.ofNat 84, Char.ofNat 32, Char.ofNat 87, Char.ofNat 65, Char.ofNat 82, Char.ofNat 82]
def assertHeader_state73 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut72 : feed assertHeader_state72 assertHeader_chunk72 = assertHeader_state73 := by rfl
def assertHeader_chunk73 : List Char := [Char.ofNat 65, Char.ofNat 78, Char.ofNat 84, Char.ofNat 89, Char.ofNat 32, Char.ofNat 79, Char.ofNat 70, Char.ofNat 32]
def assertHeader_state74 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut73 : feed assertHeader_state73 assertHeader_chunk73 = assertHeader_state74 := by rfl
def assertHeader_chunk74 : List Char := [Char.ofNat 65, Char.ofNat 78, Char.ofNat 89, Char.ofNat 32, Char.ofNat 75, Char.ofNat 73, Char.ofNat 78, Char.ofNat 68]
def assertHeader_state75 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut74 : feed assertHeader_state74 assertHeader_chunk74 = assertHeader_state75 := by rfl
def assertHeader_chunk75 : List Char := [Char.ofNat 44, Char.ofNat 32, Char.ofNat 69, Char.ofNat 73, Char.ofNat 84, Char.ofNat 72, Char.ofNat 69, Char.ofNat 82]
def assertHeader_state76 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut75 : feed assertHeader_state75 assertHeader_chunk75 = assertHeader_state76 := by rfl
def assertHeader_chunk76 : List Char := [Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 69, Char.ofNat 88, Char.ofNat 80, Char.ofNat 82]
def assertHeader_state77 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut76 : feed assertHeader_state76 assertHeader_chunk76 = assertHeader_state77 := by rfl
def assertHeader_chunk77 : List Char := [Char.ofNat 69, Char.ofNat 83, Char.ofNat 83, Char.ofNat 32, Char.ofNat 79, Char.ofNat 82, Char.ofNat 32, Char.ofNat 73]
def assertHeader_state78 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut77 : feed assertHeader_state77 assertHeader_chunk77 = assertHeader_state78 := by rfl
def assertHeader_chunk78 : List Char := [Char.ofNat 77, Char.ofNat 80, Char.ofNat 76, Char.ofNat 73, Char.ofNat 69, Char.ofNat 68, Char.ofNat 44, Char.ofNat 32]
def assertHeader_state79 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut78 : feed assertHeader_state78 assertHeader_chunk78 = assertHeader_state79 := by rfl
def assertHeader_chunk79 : List Char := [Char.ofNat 65, Char.ofNat 78, Char.ofNat 68, Char.ofNat 32, Char.ofNat 65, Char.ofNat 80, Char.ofNat 80, Char.ofNat 76]
def assertHeader_state80 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut79 : feed assertHeader_state79 assertHeader_chunk79 = assertHeader_state80 := by rfl
def assertHeader_chunk80 : List Char := [Char.ofNat 69, Char.ofNat 32, Char.ofNat 72, Char.ofNat 69, Char.ofNat 82, Char.ofNat 69, Char.ofNat 66, Char.ofNat 89]
def assertHeader_state81 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut80 : feed assertHeader_state80 assertHeader_chunk80 = assertHeader_state81 := by rfl
def assertHeader_chunk81 : List Char := [Char.ofNat 32, Char.ofNat 68, Char.ofNat 73, Char.ofNat 83, Char.ofNat 67, Char.ofNat 76, Char.ofNat 65, Char.ofNat 73]
def assertHeader_state82 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut81 : feed assertHeader_state81 assertHeader_chunk81 = assertHeader_state82 := by rfl
def assertHeader_chunk82 : List Char := [Char.ofNat 77, Char.ofNat 83, Char.ofNat 32, Char.ofNat 65, Char.ofNat 76, Char.ofNat 76, Char.ofNat 32, Char.ofNat 83]
def assertHeader_state83 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut82 : feed assertHeader_state82 assertHeader_chunk82 = assertHeader_state83 := by rfl
def assertHeader_chunk83 : List Char := [Char.ofNat 85, Char.ofNat 67, Char.ofNat 72, Char.ofNat 32, Char.ofNat 87, Char.ofNat 65, Char.ofNat 82, Char.ofNat 82]
def assertHeader_state84 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut83 : feed assertHeader_state83 assertHeader_chunk83 = assertHeader_state84 := by rfl
def assertHeader_chunk84 : List Char := [Char.ofNat 65, Char.ofNat 78, Char.ofNat 84, Char.ofNat 73, Char.ofNat 69, Char.ofNat 83, Char.ofNat 44, Char.ofNat 10]
def assertHeader_state85 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut84 : feed assertHeader_state84 assertHeader_chunk84 = assertHeader_state85 := by rfl
def assertHeader_chunk85 : List Char := [Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 73, Char.ofNat 78, Char.ofNat 67, Char.ofNat 76, Char.ofNat 85]
def assertHeader_state86 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut85 : feed assertHeader_state85 assertHeader_chunk85 = assertHeader_state86 := by rfl
def assertHeader_chunk86 : List Char := [Char.ofNat 68, Char.ofNat 73, Char.ofNat 78, Char.ofNat 71, Char.ofNat 32, Char.ofNat 87, Char.ofNat 73, Char.ofNat 84]
def assertHeader_state87 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut86 : feed assertHeader_state86 assertHeader_chunk86 = assertHeader_state87 := by rfl
def assertHeader_chunk87 : List Char := [Char.ofNat 72, Char.ofNat 79, Char.ofNat 85, Char.ofNat 84, Char.ofNat 32, Char.ofNat 76, Char.ofNat 73, Char.ofNat 77]
def assertHeader_state88 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut87 : feed assertHeader_state87 assertHeader_chunk87 = assertHeader_state88 := by rfl
def assertHeader_chunk88 : List Char := [Char.ofNat 73, Char.ofNat 84, Char.ofNat 65, Char.ofNat 84, Char.ofNat 73, Char.ofNat 79, Char.ofNat 78, Char.ofNat 44]
def assertHeader_state89 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut88 : feed assertHeader_state88 assertHeader_chunk88 = assertHeader_state89 := by rfl
def assertHeader_chunk89 : List Char := [Char.ofNat 32, Char.ofNat 65, Char.ofNat 78, Char.ofNat 89, Char.ofNat 32, Char.ofNat 87, Char.ofNat 65, Char.ofNat 82]
def assertHeader_state90 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut89 : feed assertHeader_state89 assertHeader_chunk89 = assertHeader_state90 := by rfl
def assertHeader_chunk90 : List Char := [Char.ofNat 82, Char.ofNat 65, Char.ofNat 78, Char.ofNat 84, Char.ofNat 73, Char.ofNat 69, Char.ofNat 83, Char.ofNat 32]
def assertHeader_state91 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut90 : feed assertHeader_state90 assertHeader_chunk90 = assertHeader_state91 := by rfl
def assertHeader_chunk91 : List Char := [Char.ofNat 79, Char.ofNat 70, Char.ofNat 32, Char.ofNat 77, Char.ofNat 69, Char.ofNat 82, Char.ofNat 67, Char.ofNat 72]
def assertHeader_state92 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut91 : feed assertHeader_state91 assertHeader_chunk91 = assertHeader_state92 := by rfl
def assertHeader_chunk92 : List Char := [Char.ofNat 65, Char.ofNat 78, Char.ofNat 84, Char.ofNat 65, Char.ofNat 66, Char.ofNat 73, Char.ofNat 76, Char.ofNat 73]
def assertHeader_state93 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut92 : feed assertHeader_state92 assertHeader_chunk92 = assertHeader_state93 := by rfl
def assertHeader_chunk93 : List Char := [Char.ofNat 84, Char.ofNat 89, Char.ofNat 44, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 70]
def assertHeader_state94 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut93 : feed assertHeader_state93 assertHeader_chunk93 = assertHeader_state94 := by rfl
def assertHeader_chunk94 : List Char := [Char.ofNat 73, Char.ofNat 84, Char.ofNat 78, Char.ofNat 69, Char.ofNat 83, Char.ofNat 83, Char.ofNat 32, Char.ofNat 70]
def assertHeader_state95 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut94 : feed assertHeader_state94 assertHeader_chunk94 = assertHeader_state95 := by rfl
def assertHeader_chunk95 : List Char := [Char.ofNat 79, Char.ofNat 82, Char.ofNat 32, Char.ofNat 65, Char.ofNat 32, Char.ofNat 80, Char.ofNat 65, Char.ofNat 82]
def assertHeader_state96 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut95 : feed assertHeader_state95 assertHeader_chunk95 = assertHeader_state96 := by rfl
def assertHeader_chunk96 : List Char := [Char.ofNat 84, Char.ofNat 73, Char.ofNat 67, Char.ofNat 85, Char.ofNat 76, Char.ofNat 65, Char.ofNat 82, Char.ofNat 32]
def assertHeader_state97 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut96 : feed assertHeader_state96 assertHeader_chunk96 = assertHeader_state97 := by rfl
def assertHeader_chunk97 : List Char := [Char.ofNat 80, Char.ofNat 85, Char.ofNat 82, Char.ofNat 80, Char.ofNat 79, Char.ofNat 83, Char.ofNat 69, Char.ofNat 44]
def assertHeader_state98 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut97 : feed assertHeader_state97 assertHeader_chunk97 = assertHeader_state98 := by rfl
def assertHeader_chunk98 : List Char := [Char.ofNat 32, Char.ofNat 81, Char.ofNat 85, Char.ofNat 73, Char.ofNat 69, Char.ofNat 84, Char.ofNat 32, Char.ofNat 69]
def assertHeader_state99 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut98 : feed assertHeader_state98 assertHeader_chunk98 = assertHeader_state99 := by rfl
def assertHeader_chunk99 : List Char := [Char.ofNat 78, Char.ofNat 74, Char.ofNat 79, Char.ofNat 89, Char.ofNat 77, Char.ofNat 69, Char.ofNat 78, Char.ofNat 84]
def assertHeader_state100 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut99 : feed assertHeader_state99 assertHeader_chunk99 = assertHeader_state100 := by rfl
def assertHeader_chunk100 : List Char := [Char.ofNat 32, Char.ofNat 79, Char.ofNat 82, Char.ofNat 32, Char.ofNat 78, Char.ofNat 79, Char.ofNat 78, Char.ofNat 45]
def assertHeader_state101 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut100 : feed assertHeader_state100 assertHeader_chunk100 = assertHeader_state101 := by rfl
def assertHeader_chunk101 : List Char := [Char.ofNat 73, Char.ofNat 78, Char.ofNat 70, Char.ofNat 82, Char.ofNat 73, Char.ofNat 78, Char.ofNat 71, Char.ofNat 69]
def assertHeader_state102 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut101 : feed assertHeader_state101 assertHeader_chunk101 = assertHeader_state102 := by rfl
def assertHeader_chunk102 : List Char := [Char.ofNat 77, Char.ofNat 69, Char.ofNat 78, Char.ofNat 84, Char.ofNat 46, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42]
def assertHeader_state103 : Option State := some { base := { mode := .star, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut102 : feed assertHeader_state102 assertHeader_chunk102 = assertHeader_state103 := by rfl
def assertHeader_chunk103 : List Char := [Char.ofNat 32, Char.ofNat 80, Char.ofNat 108, Char.ofNat 101, Char.ofNat 97, Char.ofNat 115, Char.ofNat 101, Char.ofNat 32]
def assertHeader_state104 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut103 : feed assertHeader_state103 assertHeader_chunk103 = assertHeader_state104 := by rfl
def assertHeader_chunk104 : List Char := [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 101, Char.ofNat 32]
def assertHeader_state105 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut104 : feed assertHeader_state104 assertHeader_chunk104 = assertHeader_state105 := by rfl
def assertHeader_chunk105 : List Char := [Char.ofNat 76, Char.ofNat 105, Char.ofNat 99, Char.ofNat 101, Char.ofNat 110, Char.ofNat 115, Char.ofNat 101, Char.ofNat 32]
def assertHeader_state106 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut105 : feed assertHeader_state105 assertHeader_chunk105 = assertHeader_state106 := by rfl
def assertHeader_chunk106 : List Char := [Char.ofNat 102, Char.ofNat 111, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 101, Char.ofNat 32]
def assertHeader_state107 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut106 : feed assertHeader_state106 assertHeader_chunk106 = assertHeader_state107 := by rfl
def assertHeader_chunk107 : List Char := [Char.ofNat 115, Char.ofNat 112, Char.ofNat 101, Char.ofNat 99, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 99]
def assertHeader_state108 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut107 : feed assertHeader_state107 assertHeader_chunk107 = assertHeader_state108 := by rfl
def assertHeader_chunk108 : List Char := [Char.ofNat 32, Char.ofNat 108, Char.ofNat 97, Char.ofNat 110, Char.ofNat 103, Char.ofNat 117, Char.ofNat 97, Char.ofNat 103]
def assertHeader_state109 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut108 : feed assertHeader_state108 assertHeader_chunk108 = assertHeader_state109 := by rfl
def assertHeader_chunk109 : List Char := [Char.ofNat 101, Char.ofNat 32, Char.ofNat 103, Char.ofNat 111, Char.ofNat 118, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]
def assertHeader_state110 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut109 : feed assertHeader_state109 assertHeader_chunk109 = assertHeader_state110 := by rfl
def assertHeader_chunk110 : List Char := [Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 32, Char.ofNat 114, Char.ofNat 105, Char.ofNat 103, Char.ofNat 104]
def assertHeader_state111 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut110 : feed assertHeader_state110 assertHeader_chunk110 = assertHeader_state111 := by rfl
def assertHeader_chunk111 : List Char := [Char.ofNat 116, Char.ofNat 115, Char.ofNat 32, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 10, Char.ofNat 32]
def assertHeader_state112 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut111 : feed assertHeader_state111 assertHeader_chunk111 = assertHeader_state112 := by rfl
def assertHeader_chunk112 : List Char := [Char.ofNat 42, Char.ofNat 32, Char.ofNat 108, Char.ofNat 105, Char.ofNat 109, Char.ofNat 105, Char.ofNat 116, Char.ofNat 97]
def assertHeader_state113 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut112 : feed assertHeader_state112 assertHeader_chunk112 = assertHeader_state113 := by rfl
def assertHeader_chunk113 : List Char := [Char.ofNat 116, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110, Char.ofNat 115, Char.ofNat 32, Char.ofNat 117, Char.ofNat 110]
def assertHeader_state114 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut113 : feed assertHeader_state113 assertHeader_chunk113 = assertHeader_state114 := by rfl
def assertHeader_chunk114 : List Char := [Char.ofNat 100, Char.ofNat 101, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 101, Char.ofNat 32]
def assertHeader_state115 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut114 : feed assertHeader_state114 assertHeader_chunk114 = assertHeader_state115 := by rfl
def assertHeader_chunk115 : List Char := [Char.ofNat 76, Char.ofNat 105, Char.ofNat 99, Char.ofNat 101, Char.ofNat 110, Char.ofNat 115, Char.ofNat 101, Char.ofNat 46]
def assertHeader_state116 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut115 : feed assertHeader_state115 assertHeader_chunk115 = assertHeader_state116 := by rfl
def assertHeader_chunk116 : List Char := [Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 64]
def assertHeader_state117 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut116 : feed assertHeader_state116 assertHeader_chunk116 = assertHeader_state117 := by rfl
def assertHeader_chunk117 : List Char := [Char.ofNat 65, Char.ofNat 80, Char.ofNat 80, Char.ofNat 76, Char.ofNat 69, Char.ofNat 95, Char.ofNat 76, Char.ofNat 73]
def assertHeader_state118 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut117 : feed assertHeader_state117 assertHeader_chunk117 = assertHeader_state118 := by rfl
def assertHeader_chunk118 : List Char := [Char.ofNat 67, Char.ofNat 69, Char.ofNat 78, Char.ofNat 83, Char.ofNat 69, Char.ofNat 95, Char.ofNat 72, Char.ofNat 69]
def assertHeader_state119 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut118 : feed assertHeader_state118 assertHeader_chunk118 = assertHeader_state119 := by rfl
def assertHeader_chunk119 : List Char := [Char.ofNat 65, Char.ofNat 68, Char.ofNat 69, Char.ofNat 82, Char.ofNat 95, Char.ofNat 69, Char.ofNat 78, Char.ofNat 68]
def assertHeader_state120 : Option State := some { base := { mode := .block, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut119 : feed assertHeader_state119 assertHeader_chunk119 = assertHeader_state120 := by rfl
def assertHeader_chunk120 : List Char := [Char.ofNat 64, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 47, Char.ofNat 10, Char.ofNat 10, Char.ofNat 35]
def assertHeader_state121 : Option State := some { base := { mode := .hash, word := [], reversed := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut120 : feed assertHeader_state120 assertHeader_chunk120 = assertHeader_state121 := by rfl
def assertHeader_chunk121 : List Char := [Char.ofNat 105, Char.ofNat 102, Char.ofNat 110, Char.ofNat 100, Char.ofNat 101, Char.ofNat 102, Char.ofNat 32, Char.ofNat 95]
def assertHeader_state122 : Option State := some { base := { mode := .word, word := [Char.ofNat 95], reversed := ["ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut121 : feed assertHeader_state121 assertHeader_chunk121 = assertHeader_state122 := by rfl
def assertHeader_chunk122 : List Char := [Char.ofNat 65, Char.ofNat 83, Char.ofNat 83, Char.ofNat 69, Char.ofNat 82, Char.ofNat 84, Char.ofNat 95, Char.ofNat 72]
def assertHeader_state123 : Option State := some { base := { mode := .word, word := [Char.ofNat 72, Char.ofNat 95, Char.ofNat 84, Char.ofNat 82, Char.ofNat 69, Char.ofNat 83, Char.ofNat 83, Char.ofNat 65, Char.ofNat 95], reversed := ["ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut122 : feed assertHeader_state122 assertHeader_chunk122 = assertHeader_state123 := by rfl
def assertHeader_chunk123 : List Char := [Char.ofNat 95, Char.ofNat 10, Char.ofNat 35, Char.ofNat 100, Char.ofNat 101, Char.ofNat 102, Char.ofNat 105, Char.ofNat 110]
def assertHeader_state124 : Option State := some { base := { mode := .word, word := [Char.ofNat 110, Char.ofNat 105, Char.ofNat 102, Char.ofNat 101, Char.ofNat 100], reversed := ["#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut123 : feed assertHeader_state123 assertHeader_chunk123 = assertHeader_state124 := by rfl
def assertHeader_chunk124 : List Char := [Char.ofNat 101, Char.ofNat 32, Char.ofNat 95, Char.ofNat 65, Char.ofNat 83, Char.ofNat 83, Char.ofNat 69, Char.ofNat 82]
def assertHeader_state125 : Option State := some { base := { mode := .word, word := [Char.ofNat 82, Char.ofNat 69, Char.ofNat 83, Char.ofNat 83, Char.ofNat 65, Char.ofNat 95], reversed := ["define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut124 : feed assertHeader_state124 assertHeader_chunk124 = assertHeader_state125 := by rfl
def assertHeader_chunk125 : List Char := [Char.ofNat 84, Char.ofNat 95, Char.ofNat 72, Char.ofNat 95, Char.ofNat 10, Char.ofNat 10, Char.ofNat 35, Char.ofNat 105]
def assertHeader_state126 : Option State := some { base := { mode := .word, word := [Char.ofNat 105], reversed := ["#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut125 : feed assertHeader_state125 assertHeader_chunk125 = assertHeader_state126 := by rfl
def assertHeader_chunk126 : List Char := [Char.ofNat 102, Char.ofNat 110, Char.ofNat 100, Char.ofNat 101, Char.ofNat 102, Char.ofNat 32, Char.ofNat 95, Char.ofNat 95]
def assertHeader_state127 : Option State := some { base := { mode := .word, word := [Char.ofNat 95, Char.ofNat 95], reversed := ["ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut126 : feed assertHeader_state126 assertHeader_chunk126 = assertHeader_state127 := by rfl
def assertHeader_chunk127 : List Char := [Char.ofNat 99, Char.ofNat 112, Char.ofNat 108, Char.ofNat 117, Char.ofNat 115, Char.ofNat 112, Char.ofNat 108, Char.ofNat 117]
def assertHeader_state128 : Option State := some { base := { mode := .word, word := [Char.ofNat 117, Char.ofNat 108, Char.ofNat 112, Char.ofNat 115, Char.ofNat 117, Char.ofNat 108, Char.ofNat 112, Char.ofNat 99, Char.ofNat 95, Char.ofNat 95], reversed := ["ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut127 : feed assertHeader_state127 assertHeader_chunk127 = assertHeader_state128 := by rfl
def assertHeader_chunk128 : List Char := [Char.ofNat 115, Char.ofNat 10, Char.ofNat 35, Char.ofNat 105, Char.ofNat 102, Char.ofNat 32, Char.ofNat 100, Char.ofNat 101]
def assertHeader_state129 : Option State := some { base := { mode := .word, word := [Char.ofNat 101, Char.ofNat 100], reversed := ["if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut128 : feed assertHeader_state128 assertHeader_chunk128 = assertHeader_state129 := by rfl
def assertHeader_chunk129 : List Char := [Char.ofNat 102, Char.ofNat 105, Char.ofNat 110, Char.ofNat 101, Char.ofNat 100, Char.ofNat 40, Char.ofNat 95, Char.ofNat 95]
def assertHeader_state130 : Option State := some { base := { mode := .word, word := [Char.ofNat 95, Char.ofNat 95], reversed := ["(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut129 : feed assertHeader_state129 assertHeader_chunk129 = assertHeader_state130 := by rfl
def assertHeader_chunk130 : List Char := [Char.ofNat 83, Char.ofNat 84, Char.ofNat 68, Char.ofNat 67, Char.ofNat 95, Char.ofNat 86, Char.ofNat 69, Char.ofNat 82]
def assertHeader_state131 : Option State := some { base := { mode := .word, word := [Char.ofNat 82, Char.ofNat 69, Char.ofNat 86, Char.ofNat 95, Char.ofNat 67, Char.ofNat 68, Char.ofNat 84, Char.ofNat 83, Char.ofNat 95, Char.ofNat 95], reversed := ["(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut130 : feed assertHeader_state130 assertHeader_chunk130 = assertHeader_state131 := by rfl
def assertHeader_chunk131 : List Char := [Char.ofNat 83, Char.ofNat 73, Char.ofNat 79, Char.ofNat 78, Char.ofNat 95, Char.ofNat 95, Char.ofNat 41, Char.ofNat 32]
def assertHeader_state132 : Option State := some { base := { mode := .normal, word := [], reversed := [")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut131 : feed assertHeader_state131 assertHeader_chunk131 = assertHeader_state132 := by rfl
def assertHeader_chunk132 : List Char := [Char.ofNat 38, Char.ofNat 38, Char.ofNat 32, Char.ofNat 95, Char.ofNat 95, Char.ofNat 83, Char.ofNat 84, Char.ofNat 68]
def assertHeader_state133 : Option State := some { base := { mode := .word, word := [Char.ofNat 68, Char.ofNat 84, Char.ofNat 83, Char.ofNat 95, Char.ofNat 95], reversed := ["&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut132 : feed assertHeader_state132 assertHeader_chunk132 = assertHeader_state133 := by rfl
def assertHeader_chunk133 : List Char := [Char.ofNat 67, Char.ofNat 95, Char.ofNat 86, Char.ofNat 69, Char.ofNat 82, Char.ofNat 83, Char.ofNat 73, Char.ofNat 79]
def assertHeader_state134 : Option State := some { base := { mode := .word, word := [Char.ofNat 79, Char.ofNat 73, Char.ofNat 83, Char.ofNat 82, Char.ofNat 69, Char.ofNat 86, Char.ofNat 95, Char.ofNat 67, Char.ofNat 68, Char.ofNat 84, Char.ofNat 83, Char.ofNat 95, Char.ofNat 95], reversed := ["&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut133 : feed assertHeader_state133 assertHeader_chunk133 = assertHeader_state134 := by rfl
def assertHeader_chunk134 : List Char := [Char.ofNat 78, Char.ofNat 95, Char.ofNat 95, Char.ofNat 32, Char.ofNat 62, Char.ofNat 61, Char.ofNat 32, Char.ofNat 50]
def assertHeader_state135 : Option State := some { base := { mode := .word, word := [Char.ofNat 50], reversed := [">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut134 : feed assertHeader_state134 assertHeader_chunk134 = assertHeader_state135 := by rfl
def assertHeader_chunk135 : List Char := [Char.ofNat 48, Char.ofNat 49, Char.ofNat 49, Char.ofNat 49, Char.ofNat 50, Char.ofNat 76, Char.ofNat 10, Char.ofNat 35]
def assertHeader_state136 : Option State := some { base := { mode := .hash, word := [], reversed := ["\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut135 : feed assertHeader_state135 assertHeader_chunk135 = assertHeader_state136 := by rfl
def assertHeader_chunk136 : List Char := [Char.ofNat 100, Char.ofNat 101, Char.ofNat 102, Char.ofNat 105, Char.ofNat 110, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115]
def assertHeader_state137 : Option State := some { base := { mode := .word, word := [Char.ofNat 115], reversed := ["define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut136 : feed assertHeader_state136 assertHeader_chunk136 = assertHeader_state137 := by rfl
def assertHeader_chunk137 : List Char := [Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 95, Char.ofNat 97, Char.ofNat 115]
def assertHeader_state138 : Option State := some { base := { mode := .word, word := [Char.ofNat 115, Char.ofNat 97, Char.ofNat 95, Char.ofNat 99, Char.ofNat 105, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 115], reversed := ["define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut137 : feed assertHeader_state137 assertHeader_chunk137 = assertHeader_state138 := by rfl
def assertHeader_chunk138 : List Char := [Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 116, Char.ofNat 32, Char.ofNat 95, Char.ofNat 83, Char.ofNat 116]
def assertHeader_state139 : Option State := some { base := { mode := .word, word := [Char.ofNat 116, Char.ofNat 83, Char.ofNat 95], reversed := ["static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut138 : feed assertHeader_state138 assertHeader_chunk138 = assertHeader_state139 := by rfl
def assertHeader_chunk139 : List Char := [Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 95, Char.ofNat 97, Char.ofNat 115, Char.ofNat 115]
def assertHeader_state140 : Option State := some { base := { mode := .word, word := [Char.ofNat 115, Char.ofNat 115, Char.ofNat 97, Char.ofNat 95, Char.ofNat 99, Char.ofNat 105, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 83, Char.ofNat 95], reversed := ["static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut139 : feed assertHeader_state139 assertHeader_chunk139 = assertHeader_state140 := by rfl
def assertHeader_chunk140 : List Char := [Char.ofNat 101, Char.ofNat 114, Char.ofNat 116, Char.ofNat 10, Char.ofNat 35, Char.ofNat 101, Char.ofNat 110, Char.ofNat 100]
def assertHeader_state141 : Option State := some { base := { mode := .word, word := [Char.ofNat 100, Char.ofNat 110, Char.ofNat 101], reversed := ["#", "\n", "_Static_assert", "static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut140 : feed assertHeader_state140 assertHeader_chunk140 = assertHeader_state141 := by rfl
def assertHeader_chunk141 : List Char := [Char.ofNat 105, Char.ofNat 102, Char.ofNat 32, Char.ofNat 47, Char.ofNat 42, Char.ofNat 32, Char.ofNat 95, Char.ofNat 95]
def assertHeader_state142 : Option State := some { base := { mode := .block, word := [], reversed := ["endif", "#", "\n", "_Static_assert", "static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut141 : feed assertHeader_state141 assertHeader_chunk141 = assertHeader_state142 := by rfl
def assertHeader_chunk142 : List Char := [Char.ofNat 83, Char.ofNat 84, Char.ofNat 68, Char.ofNat 67, Char.ofNat 95, Char.ofNat 86, Char.ofNat 69, Char.ofNat 82]
def assertHeader_state143 : Option State := some { base := { mode := .block, word := [], reversed := ["endif", "#", "\n", "_Static_assert", "static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut142 : feed assertHeader_state142 assertHeader_chunk142 = assertHeader_state143 := by rfl
def assertHeader_chunk143 : List Char := [Char.ofNat 83, Char.ofNat 73, Char.ofNat 79, Char.ofNat 78, Char.ofNat 95, Char.ofNat 95, Char.ofNat 32, Char.ofNat 42]
def assertHeader_state144 : Option State := some { base := { mode := .star, word := [], reversed := ["endif", "#", "\n", "_Static_assert", "static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut143 : feed assertHeader_state143 assertHeader_chunk143 = assertHeader_state144 := by rfl
def assertHeader_chunk144 : List Char := [Char.ofNat 47, Char.ofNat 10, Char.ofNat 35, Char.ofNat 101, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 102]
def assertHeader_state145 : Option State := some { base := { mode := .word, word := [Char.ofNat 102, Char.ofNat 105, Char.ofNat 100, Char.ofNat 110, Char.ofNat 101], reversed := ["#", "\n", "endif", "#", "\n", "_Static_assert", "static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut144 : feed assertHeader_state144 assertHeader_chunk144 = assertHeader_state145 := by rfl
def assertHeader_chunk145 : List Char := [Char.ofNat 32, Char.ofNat 47, Char.ofNat 42, Char.ofNat 32, Char.ofNat 33, Char.ofNat 95, Char.ofNat 95, Char.ofNat 99]
def assertHeader_state146 : Option State := some { base := { mode := .block, word := [], reversed := ["endif", "#", "\n", "endif", "#", "\n", "_Static_assert", "static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut145 : feed assertHeader_state145 assertHeader_chunk145 = assertHeader_state146 := by rfl
def assertHeader_chunk146 : List Char := [Char.ofNat 112, Char.ofNat 108, Char.ofNat 117, Char.ofNat 115, Char.ofNat 112, Char.ofNat 108, Char.ofNat 117, Char.ofNat 115]
def assertHeader_state147 : Option State := some { base := { mode := .block, word := [], reversed := ["endif", "#", "\n", "endif", "#", "\n", "_Static_assert", "static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut146 : feed assertHeader_state146 assertHeader_chunk146 = assertHeader_state147 := by rfl
def assertHeader_chunk147 : List Char := [Char.ofNat 32, Char.ofNat 42, Char.ofNat 47, Char.ofNat 10, Char.ofNat 10, Char.ofNat 35, Char.ofNat 101, Char.ofNat 110]
def assertHeader_state148 : Option State := some { base := { mode := .word, word := [Char.ofNat 110, Char.ofNat 101], reversed := ["#", "\n", "\n", "endif", "#", "\n", "endif", "#", "\n", "_Static_assert", "static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut147 : feed assertHeader_state147 assertHeader_chunk147 = assertHeader_state148 := by rfl
def assertHeader_chunk148 : List Char := [Char.ofNat 100, Char.ofNat 105, Char.ofNat 102, Char.ofNat 32, Char.ofNat 47, Char.ofNat 42, Char.ofNat 32, Char.ofNat 95]
def assertHeader_state149 : Option State := some { base := { mode := .block, word := [], reversed := ["endif", "#", "\n", "\n", "endif", "#", "\n", "endif", "#", "\n", "_Static_assert", "static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut148 : feed assertHeader_state148 assertHeader_chunk148 = assertHeader_state149 := by rfl
def assertHeader_chunk149 : List Char := [Char.ofNat 65, Char.ofNat 83, Char.ofNat 83, Char.ofNat 69, Char.ofNat 82, Char.ofNat 84, Char.ofNat 95, Char.ofNat 72]
def assertHeader_state150 : Option State := some { base := { mode := .block, word := [], reversed := ["endif", "#", "\n", "\n", "endif", "#", "\n", "endif", "#", "\n", "_Static_assert", "static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut149 : feed assertHeader_state149 assertHeader_chunk149 = assertHeader_state150 := by rfl
def assertHeader_chunk150 : List Char := [Char.ofNat 95, Char.ofNat 32, Char.ofNat 42, Char.ofNat 47, Char.ofNat 10]
def assertHeader_state151 : Option State := some { base := { mode := .normal, word := [], reversed := ["\n", "endif", "#", "\n", "\n", "endif", "#", "\n", "endif", "#", "\n", "_Static_assert", "static_assert", "define", "#", "\n", "201112L", ">=", "__STDC_VERSION__", "&&", ")", "__STDC_VERSION__", "(", "defined", "if", "#", "\n", "__cplusplus", "ifndef", "#", "\n", "\n", "_ASSERT_H_", "define", "#", "\n", "_ASSERT_H_", "ifndef", "#", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n"] }, pending := .none }
theorem assertHeader_cut150 : feed assertHeader_state150 assertHeader_chunk150 = assertHeader_state151 := by rfl
def assertHeader_chunks : List (List Char) := [assertHeader_chunk0, assertHeader_chunk1, assertHeader_chunk2, assertHeader_chunk3, assertHeader_chunk4, assertHeader_chunk5, assertHeader_chunk6, assertHeader_chunk7, assertHeader_chunk8, assertHeader_chunk9, assertHeader_chunk10, assertHeader_chunk11, assertHeader_chunk12, assertHeader_chunk13, assertHeader_chunk14, assertHeader_chunk15, assertHeader_chunk16, assertHeader_chunk17, assertHeader_chunk18, assertHeader_chunk19, assertHeader_chunk20, assertHeader_chunk21, assertHeader_chunk22, assertHeader_chunk23, assertHeader_chunk24, assertHeader_chunk25, assertHeader_chunk26, assertHeader_chunk27, assertHeader_chunk28, assertHeader_chunk29, assertHeader_chunk30, assertHeader_chunk31, assertHeader_chunk32, assertHeader_chunk33, assertHeader_chunk34, assertHeader_chunk35, assertHeader_chunk36, assertHeader_chunk37, assertHeader_chunk38, assertHeader_chunk39, assertHeader_chunk40, assertHeader_chunk41, assertHeader_chunk42, assertHeader_chunk43, assertHeader_chunk44, assertHeader_chunk45, assertHeader_chunk46, assertHeader_chunk47, assertHeader_chunk48, assertHeader_chunk49, assertHeader_chunk50, assertHeader_chunk51, assertHeader_chunk52, assertHeader_chunk53, assertHeader_chunk54, assertHeader_chunk55, assertHeader_chunk56, assertHeader_chunk57, assertHeader_chunk58, assertHeader_chunk59, assertHeader_chunk60, assertHeader_chunk61, assertHeader_chunk62, assertHeader_chunk63, assertHeader_chunk64, assertHeader_chunk65, assertHeader_chunk66, assertHeader_chunk67, assertHeader_chunk68, assertHeader_chunk69, assertHeader_chunk70, assertHeader_chunk71, assertHeader_chunk72, assertHeader_chunk73, assertHeader_chunk74, assertHeader_chunk75, assertHeader_chunk76, assertHeader_chunk77, assertHeader_chunk78, assertHeader_chunk79, assertHeader_chunk80, assertHeader_chunk81, assertHeader_chunk82, assertHeader_chunk83, assertHeader_chunk84, assertHeader_chunk85, assertHeader_chunk86, assertHeader_chunk87, assertHeader_chunk88, assertHeader_chunk89, assertHeader_chunk90, assertHeader_chunk91, assertHeader_chunk92, assertHeader_chunk93, assertHeader_chunk94, assertHeader_chunk95, assertHeader_chunk96, assertHeader_chunk97, assertHeader_chunk98, assertHeader_chunk99, assertHeader_chunk100, assertHeader_chunk101, assertHeader_chunk102, assertHeader_chunk103, assertHeader_chunk104, assertHeader_chunk105, assertHeader_chunk106, assertHeader_chunk107, assertHeader_chunk108, assertHeader_chunk109, assertHeader_chunk110, assertHeader_chunk111, assertHeader_chunk112, assertHeader_chunk113, assertHeader_chunk114, assertHeader_chunk115, assertHeader_chunk116, assertHeader_chunk117, assertHeader_chunk118, assertHeader_chunk119, assertHeader_chunk120, assertHeader_chunk121, assertHeader_chunk122, assertHeader_chunk123, assertHeader_chunk124, assertHeader_chunk125, assertHeader_chunk126, assertHeader_chunk127, assertHeader_chunk128, assertHeader_chunk129, assertHeader_chunk130, assertHeader_chunk131, assertHeader_chunk132, assertHeader_chunk133, assertHeader_chunk134, assertHeader_chunk135, assertHeader_chunk136, assertHeader_chunk137, assertHeader_chunk138, assertHeader_chunk139, assertHeader_chunk140, assertHeader_chunk141, assertHeader_chunk142, assertHeader_chunk143, assertHeader_chunk144, assertHeader_chunk145, assertHeader_chunk146, assertHeader_chunk147, assertHeader_chunk148, assertHeader_chunk149, assertHeader_chunk150]
def assertHeader_tokens : List String := ["\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "\n", "#", "ifndef", "_ASSERT_H_", "\n", "#", "define", "_ASSERT_H_", "\n", "\n", "#", "ifndef", "__cplusplus", "\n", "#", "if", "defined", "(", "__STDC_VERSION__", ")", "&&", "__STDC_VERSION__", ">=", "201112L", "\n", "#", "define", "static_assert", "_Static_assert", "\n", "#", "endif", "\n", "#", "endif", "\n", "\n", "#", "endif", "\n"]
theorem assertHeader_characters_lex : tokenizeCharacters assertHeader_chunks.flatten = some assertHeader_tokens := by
  rw [← chunks_exact]
  simp only [tokenizeChunks, assertHeader_chunks, List.foldl_cons, List.foldl_nil]
  rw [assertHeader_cut0, assertHeader_cut1, assertHeader_cut2, assertHeader_cut3, assertHeader_cut4, assertHeader_cut5, assertHeader_cut6, assertHeader_cut7, assertHeader_cut8, assertHeader_cut9, assertHeader_cut10, assertHeader_cut11, assertHeader_cut12, assertHeader_cut13, assertHeader_cut14, assertHeader_cut15, assertHeader_cut16, assertHeader_cut17, assertHeader_cut18, assertHeader_cut19, assertHeader_cut20, assertHeader_cut21, assertHeader_cut22, assertHeader_cut23, assertHeader_cut24, assertHeader_cut25, assertHeader_cut26, assertHeader_cut27, assertHeader_cut28, assertHeader_cut29, assertHeader_cut30, assertHeader_cut31, assertHeader_cut32, assertHeader_cut33, assertHeader_cut34, assertHeader_cut35, assertHeader_cut36, assertHeader_cut37, assertHeader_cut38, assertHeader_cut39, assertHeader_cut40, assertHeader_cut41, assertHeader_cut42, assertHeader_cut43, assertHeader_cut44, assertHeader_cut45, assertHeader_cut46, assertHeader_cut47, assertHeader_cut48, assertHeader_cut49, assertHeader_cut50, assertHeader_cut51, assertHeader_cut52, assertHeader_cut53, assertHeader_cut54, assertHeader_cut55, assertHeader_cut56, assertHeader_cut57, assertHeader_cut58, assertHeader_cut59, assertHeader_cut60, assertHeader_cut61, assertHeader_cut62, assertHeader_cut63, assertHeader_cut64, assertHeader_cut65, assertHeader_cut66, assertHeader_cut67, assertHeader_cut68, assertHeader_cut69, assertHeader_cut70, assertHeader_cut71, assertHeader_cut72, assertHeader_cut73, assertHeader_cut74, assertHeader_cut75, assertHeader_cut76, assertHeader_cut77, assertHeader_cut78, assertHeader_cut79, assertHeader_cut80, assertHeader_cut81, assertHeader_cut82, assertHeader_cut83, assertHeader_cut84, assertHeader_cut85, assertHeader_cut86, assertHeader_cut87, assertHeader_cut88, assertHeader_cut89, assertHeader_cut90, assertHeader_cut91, assertHeader_cut92, assertHeader_cut93, assertHeader_cut94, assertHeader_cut95, assertHeader_cut96, assertHeader_cut97, assertHeader_cut98, assertHeader_cut99, assertHeader_cut100, assertHeader_cut101, assertHeader_cut102, assertHeader_cut103, assertHeader_cut104, assertHeader_cut105, assertHeader_cut106, assertHeader_cut107, assertHeader_cut108, assertHeader_cut109, assertHeader_cut110, assertHeader_cut111, assertHeader_cut112, assertHeader_cut113, assertHeader_cut114, assertHeader_cut115, assertHeader_cut116, assertHeader_cut117, assertHeader_cut118, assertHeader_cut119, assertHeader_cut120, assertHeader_cut121, assertHeader_cut122, assertHeader_cut123, assertHeader_cut124, assertHeader_cut125, assertHeader_cut126, assertHeader_cut127, assertHeader_cut128, assertHeader_cut129, assertHeader_cut130, assertHeader_cut131, assertHeader_cut132, assertHeader_cut133, assertHeader_cut134, assertHeader_cut135, assertHeader_cut136, assertHeader_cut137, assertHeader_cut138, assertHeader_cut139, assertHeader_cut140, assertHeader_cut141, assertHeader_cut142, assertHeader_cut143, assertHeader_cut144, assertHeader_cut145, assertHeader_cut146, assertHeader_cut147, assertHeader_cut148, assertHeader_cut149, assertHeader_cut150]
  rfl
def assertHeader_string_leaf0 : String := "/*\n * Co"
theorem assertHeader_chunk_chars0 : assertHeader_string_leaf0.toList = assertHeader_chunk0 := by rfl
def assertHeader_string_leaf1 : String := "pyright "
theorem assertHeader_chunk_chars1 : assertHeader_string_leaf1.toList = assertHeader_chunk1 := by rfl
def assertHeader_string_leaf2 : String := "(c) 2023"
theorem assertHeader_chunk_chars2 : assertHeader_string_leaf2.toList = assertHeader_chunk2 := by rfl
def assertHeader_string_leaf3 : String := " Apple I"
theorem assertHeader_chunk_chars3 : assertHeader_string_leaf3.toList = assertHeader_chunk3 := by rfl
def assertHeader_string_leaf4 : String := "nc. All "
theorem assertHeader_chunk_chars4 : assertHeader_string_leaf4.toList = assertHeader_chunk4 := by rfl
def assertHeader_string_leaf5 : String := "rights r"
theorem assertHeader_chunk_chars5 : assertHeader_string_leaf5.toList = assertHeader_chunk5 := by rfl
def assertHeader_string_leaf6 : String := "eserved."
theorem assertHeader_chunk_chars6 : assertHeader_string_leaf6.toList = assertHeader_chunk6 := by rfl
def assertHeader_string_leaf7 : String := "\n *\n * @"
theorem assertHeader_chunk_chars7 : assertHeader_string_leaf7.toList = assertHeader_chunk7 := by rfl
def assertHeader_string_leaf8 : String := "APPLE_LI"
theorem assertHeader_chunk_chars8 : assertHeader_string_leaf8.toList = assertHeader_chunk8 := by rfl
def assertHeader_string_leaf9 : String := "CENSE_HE"
theorem assertHeader_chunk_chars9 : assertHeader_string_leaf9.toList = assertHeader_chunk9 := by rfl
def assertHeader_string_leaf10 : String := "ADER_STA"
theorem assertHeader_chunk_chars10 : assertHeader_string_leaf10.toList = assertHeader_chunk10 := by rfl
def assertHeader_string_leaf11 : String := "RT@\n *\n "
theorem assertHeader_chunk_chars11 : assertHeader_string_leaf11.toList = assertHeader_chunk11 := by rfl
def assertHeader_string_leaf12 : String := "* This f"
theorem assertHeader_chunk_chars12 : assertHeader_string_leaf12.toList = assertHeader_chunk12 := by rfl
def assertHeader_string_leaf13 : String := "ile cont"
theorem assertHeader_chunk_chars13 : assertHeader_string_leaf13.toList = assertHeader_chunk13 := by rfl
def assertHeader_string_leaf14 : String := "ains Ori"
theorem assertHeader_chunk_chars14 : assertHeader_string_leaf14.toList = assertHeader_chunk14 := by rfl
def assertHeader_string_leaf15 : String := "ginal Co"
theorem assertHeader_chunk_chars15 : assertHeader_string_leaf15.toList = assertHeader_chunk15 := by rfl
def assertHeader_string_leaf16 : String := "de and/o"
theorem assertHeader_chunk_chars16 : assertHeader_string_leaf16.toList = assertHeader_chunk16 := by rfl
def assertHeader_string_leaf17 : String := "r Modifi"
theorem assertHeader_chunk_chars17 : assertHeader_string_leaf17.toList = assertHeader_chunk17 := by rfl
def assertHeader_string_leaf18 : String := "cations "
theorem assertHeader_chunk_chars18 : assertHeader_string_leaf18.toList = assertHeader_chunk18 := by rfl
def assertHeader_string_leaf19 : String := "of Origi"
theorem assertHeader_chunk_chars19 : assertHeader_string_leaf19.toList = assertHeader_chunk19 := by rfl
def assertHeader_string_leaf20 : String := "nal Code"
theorem assertHeader_chunk_chars20 : assertHeader_string_leaf20.toList = assertHeader_chunk20 := by rfl
def assertHeader_string_leaf21 : String := "\n * as d"
theorem assertHeader_chunk_chars21 : assertHeader_string_leaf21.toList = assertHeader_chunk21 := by rfl
def assertHeader_string_leaf22 : String := "efined i"
theorem assertHeader_chunk_chars22 : assertHeader_string_leaf22.toList = assertHeader_chunk22 := by rfl
def assertHeader_string_leaf23 : String := "n and th"
theorem assertHeader_chunk_chars23 : assertHeader_string_leaf23.toList = assertHeader_chunk23 := by rfl
def assertHeader_string_leaf24 : String := "at are s"
theorem assertHeader_chunk_chars24 : assertHeader_string_leaf24.toList = assertHeader_chunk24 := by rfl
def assertHeader_string_leaf25 : String := "ubject t"
theorem assertHeader_chunk_chars25 : assertHeader_string_leaf25.toList = assertHeader_chunk25 := by rfl
def assertHeader_string_leaf26 : String := "o the Ap"
theorem assertHeader_chunk_chars26 : assertHeader_string_leaf26.toList = assertHeader_chunk26 := by rfl
def assertHeader_string_leaf27 : String := "ple Publ"
theorem assertHeader_chunk_chars27 : assertHeader_string_leaf27.toList = assertHeader_chunk27 := by rfl
def assertHeader_string_leaf28 : String := "ic Sourc"
theorem assertHeader_chunk_chars28 : assertHeader_string_leaf28.toList = assertHeader_chunk28 := by rfl
def assertHeader_string_leaf29 : String := "e Licens"
theorem assertHeader_chunk_chars29 : assertHeader_string_leaf29.toList = assertHeader_chunk29 := by rfl
def assertHeader_string_leaf30 : String := "e\n * Ver"
theorem assertHeader_chunk_chars30 : assertHeader_string_leaf30.toList = assertHeader_chunk30 := by rfl
def assertHeader_string_leaf31 : String := "sion 2.0"
theorem assertHeader_chunk_chars31 : assertHeader_string_leaf31.toList = assertHeader_chunk31 := by rfl
def assertHeader_string_leaf32 : String := " (the 'L"
theorem assertHeader_chunk_chars32 : assertHeader_string_leaf32.toList = assertHeader_chunk32 := by rfl
def assertHeader_string_leaf33 : String := "icense')"
theorem assertHeader_chunk_chars33 : assertHeader_string_leaf33.toList = assertHeader_chunk33 := by rfl
def assertHeader_string_leaf34 : String := ". You ma"
theorem assertHeader_chunk_chars34 : assertHeader_string_leaf34.toList = assertHeader_chunk34 := by rfl
def assertHeader_string_leaf35 : String := "y not us"
theorem assertHeader_chunk_chars35 : assertHeader_string_leaf35.toList = assertHeader_chunk35 := by rfl
def assertHeader_string_leaf36 : String := "e this f"
theorem assertHeader_chunk_chars36 : assertHeader_string_leaf36.toList = assertHeader_chunk36 := by rfl
def assertHeader_string_leaf37 : String := "ile exce"
theorem assertHeader_chunk_chars37 : assertHeader_string_leaf37.toList = assertHeader_chunk37 := by rfl
def assertHeader_string_leaf38 : String := "pt in\n *"
theorem assertHeader_chunk_chars38 : assertHeader_string_leaf38.toList = assertHeader_chunk38 := by rfl
def assertHeader_string_leaf39 : String := " complia"
theorem assertHeader_chunk_chars39 : assertHeader_string_leaf39.toList = assertHeader_chunk39 := by rfl
def assertHeader_string_leaf40 : String := "nce with"
theorem assertHeader_chunk_chars40 : assertHeader_string_leaf40.toList = assertHeader_chunk40 := by rfl
def assertHeader_string_leaf41 : String := " the Lic"
theorem assertHeader_chunk_chars41 : assertHeader_string_leaf41.toList = assertHeader_chunk41 := by rfl
def assertHeader_string_leaf42 : String := "ense. Pl"
theorem assertHeader_chunk_chars42 : assertHeader_string_leaf42.toList = assertHeader_chunk42 := by rfl
def assertHeader_string_leaf43 : String := "ease obt"
theorem assertHeader_chunk_chars43 : assertHeader_string_leaf43.toList = assertHeader_chunk43 := by rfl
def assertHeader_string_leaf44 : String := "ain a co"
theorem assertHeader_chunk_chars44 : assertHeader_string_leaf44.toList = assertHeader_chunk44 := by rfl
def assertHeader_string_leaf45 : String := "py of th"
theorem assertHeader_chunk_chars45 : assertHeader_string_leaf45.toList = assertHeader_chunk45 := by rfl
def assertHeader_string_leaf46 : String := "e Licens"
theorem assertHeader_chunk_chars46 : assertHeader_string_leaf46.toList = assertHeader_chunk46 := by rfl
def assertHeader_string_leaf47 : String := "e at\n * "
theorem assertHeader_chunk_chars47 : assertHeader_string_leaf47.toList = assertHeader_chunk47 := by rfl
def assertHeader_string_leaf48 : String := "http://w"
theorem assertHeader_chunk_chars48 : assertHeader_string_leaf48.toList = assertHeader_chunk48 := by rfl
def assertHeader_string_leaf49 : String := "ww.opens"
theorem assertHeader_chunk_chars49 : assertHeader_string_leaf49.toList = assertHeader_chunk49 := by rfl
def assertHeader_string_leaf50 : String := "ource.ap"
theorem assertHeader_chunk_chars50 : assertHeader_string_leaf50.toList = assertHeader_chunk50 := by rfl
def assertHeader_string_leaf51 : String := "ple.com/"
theorem assertHeader_chunk_chars51 : assertHeader_string_leaf51.toList = assertHeader_chunk51 := by rfl
def assertHeader_string_leaf52 : String := "apsl/ an"
theorem assertHeader_chunk_chars52 : assertHeader_string_leaf52.toList = assertHeader_chunk52 := by rfl
def assertHeader_string_leaf53 : String := "d read i"
theorem assertHeader_chunk_chars53 : assertHeader_string_leaf53.toList = assertHeader_chunk53 := by rfl
def assertHeader_string_leaf54 : String := "t before"
theorem assertHeader_chunk_chars54 : assertHeader_string_leaf54.toList = assertHeader_chunk54 := by rfl
def assertHeader_string_leaf55 : String := " using t"
theorem assertHeader_chunk_chars55 : assertHeader_string_leaf55.toList = assertHeader_chunk55 := by rfl
def assertHeader_string_leaf56 : String := "his\n * f"
theorem assertHeader_chunk_chars56 : assertHeader_string_leaf56.toList = assertHeader_chunk56 := by rfl
def assertHeader_string_leaf57 : String := "ile.\n *\n"
theorem assertHeader_chunk_chars57 : assertHeader_string_leaf57.toList = assertHeader_chunk57 := by rfl
def assertHeader_string_leaf58 : String := " * The O"
theorem assertHeader_chunk_chars58 : assertHeader_string_leaf58.toList = assertHeader_chunk58 := by rfl
def assertHeader_string_leaf59 : String := "riginal "
theorem assertHeader_chunk_chars59 : assertHeader_string_leaf59.toList = assertHeader_chunk59 := by rfl
def assertHeader_string_leaf60 : String := "Code and"
theorem assertHeader_chunk_chars60 : assertHeader_string_leaf60.toList = assertHeader_chunk60 := by rfl
def assertHeader_string_leaf61 : String := " all sof"
theorem assertHeader_chunk_chars61 : assertHeader_string_leaf61.toList = assertHeader_chunk61 := by rfl
def assertHeader_string_leaf62 : String := "tware di"
theorem assertHeader_chunk_chars62 : assertHeader_string_leaf62.toList = assertHeader_chunk62 := by rfl
def assertHeader_string_leaf63 : String := "stribute"
theorem assertHeader_chunk_chars63 : assertHeader_string_leaf63.toList = assertHeader_chunk63 := by rfl
def assertHeader_string_leaf64 : String := "d under "
theorem assertHeader_chunk_chars64 : assertHeader_string_leaf64.toList = assertHeader_chunk64 := by rfl
def assertHeader_string_leaf65 : String := "the Lice"
theorem assertHeader_chunk_chars65 : assertHeader_string_leaf65.toList = assertHeader_chunk65 := by rfl
def assertHeader_string_leaf66 : String := "nse are\n"
theorem assertHeader_chunk_chars66 : assertHeader_string_leaf66.toList = assertHeader_chunk66 := by rfl
def assertHeader_string_leaf67 : String := " * distr"
theorem assertHeader_chunk_chars67 : assertHeader_string_leaf67.toList = assertHeader_chunk67 := by rfl
def assertHeader_string_leaf68 : String := "ibuted o"
theorem assertHeader_chunk_chars68 : assertHeader_string_leaf68.toList = assertHeader_chunk68 := by rfl
def assertHeader_string_leaf69 : String := "n an 'AS"
theorem assertHeader_chunk_chars69 : assertHeader_string_leaf69.toList = assertHeader_chunk69 := by rfl
def assertHeader_string_leaf70 : String := " IS' bas"
theorem assertHeader_chunk_chars70 : assertHeader_string_leaf70.toList = assertHeader_chunk70 := by rfl
def assertHeader_string_leaf71 : String := "is, WITH"
theorem assertHeader_chunk_chars71 : assertHeader_string_leaf71.toList = assertHeader_chunk71 := by rfl
def assertHeader_string_leaf72 : String := "OUT WARR"
theorem assertHeader_chunk_chars72 : assertHeader_string_leaf72.toList = assertHeader_chunk72 := by rfl
def assertHeader_string_leaf73 : String := "ANTY OF "
theorem assertHeader_chunk_chars73 : assertHeader_string_leaf73.toList = assertHeader_chunk73 := by rfl
def assertHeader_string_leaf74 : String := "ANY KIND"
theorem assertHeader_chunk_chars74 : assertHeader_string_leaf74.toList = assertHeader_chunk74 := by rfl
def assertHeader_string_leaf75 : String := ", EITHER"
theorem assertHeader_chunk_chars75 : assertHeader_string_leaf75.toList = assertHeader_chunk75 := by rfl
def assertHeader_string_leaf76 : String := "\n * EXPR"
theorem assertHeader_chunk_chars76 : assertHeader_string_leaf76.toList = assertHeader_chunk76 := by rfl
def assertHeader_string_leaf77 : String := "ESS OR I"
theorem assertHeader_chunk_chars77 : assertHeader_string_leaf77.toList = assertHeader_chunk77 := by rfl
def assertHeader_string_leaf78 : String := "MPLIED, "
theorem assertHeader_chunk_chars78 : assertHeader_string_leaf78.toList = assertHeader_chunk78 := by rfl
def assertHeader_string_leaf79 : String := "AND APPL"
theorem assertHeader_chunk_chars79 : assertHeader_string_leaf79.toList = assertHeader_chunk79 := by rfl
def assertHeader_string_leaf80 : String := "E HEREBY"
theorem assertHeader_chunk_chars80 : assertHeader_string_leaf80.toList = assertHeader_chunk80 := by rfl
def assertHeader_string_leaf81 : String := " DISCLAI"
theorem assertHeader_chunk_chars81 : assertHeader_string_leaf81.toList = assertHeader_chunk81 := by rfl
def assertHeader_string_leaf82 : String := "MS ALL S"
theorem assertHeader_chunk_chars82 : assertHeader_string_leaf82.toList = assertHeader_chunk82 := by rfl
def assertHeader_string_leaf83 : String := "UCH WARR"
theorem assertHeader_chunk_chars83 : assertHeader_string_leaf83.toList = assertHeader_chunk83 := by rfl
def assertHeader_string_leaf84 : String := "ANTIES,\n"
theorem assertHeader_chunk_chars84 : assertHeader_string_leaf84.toList = assertHeader_chunk84 := by rfl
def assertHeader_string_leaf85 : String := " * INCLU"
theorem assertHeader_chunk_chars85 : assertHeader_string_leaf85.toList = assertHeader_chunk85 := by rfl
def assertHeader_string_leaf86 : String := "DING WIT"
theorem assertHeader_chunk_chars86 : assertHeader_string_leaf86.toList = assertHeader_chunk86 := by rfl
def assertHeader_string_leaf87 : String := "HOUT LIM"
theorem assertHeader_chunk_chars87 : assertHeader_string_leaf87.toList = assertHeader_chunk87 := by rfl
def assertHeader_string_leaf88 : String := "ITATION,"
theorem assertHeader_chunk_chars88 : assertHeader_string_leaf88.toList = assertHeader_chunk88 := by rfl
def assertHeader_string_leaf89 : String := " ANY WAR"
theorem assertHeader_chunk_chars89 : assertHeader_string_leaf89.toList = assertHeader_chunk89 := by rfl
def assertHeader_string_leaf90 : String := "RANTIES "
theorem assertHeader_chunk_chars90 : assertHeader_string_leaf90.toList = assertHeader_chunk90 := by rfl
def assertHeader_string_leaf91 : String := "OF MERCH"
theorem assertHeader_chunk_chars91 : assertHeader_string_leaf91.toList = assertHeader_chunk91 := by rfl
def assertHeader_string_leaf92 : String := "ANTABILI"
theorem assertHeader_chunk_chars92 : assertHeader_string_leaf92.toList = assertHeader_chunk92 := by rfl
def assertHeader_string_leaf93 : String := "TY,\n * F"
theorem assertHeader_chunk_chars93 : assertHeader_string_leaf93.toList = assertHeader_chunk93 := by rfl
def assertHeader_string_leaf94 : String := "ITNESS F"
theorem assertHeader_chunk_chars94 : assertHeader_string_leaf94.toList = assertHeader_chunk94 := by rfl
def assertHeader_string_leaf95 : String := "OR A PAR"
theorem assertHeader_chunk_chars95 : assertHeader_string_leaf95.toList = assertHeader_chunk95 := by rfl
def assertHeader_string_leaf96 : String := "TICULAR "
theorem assertHeader_chunk_chars96 : assertHeader_string_leaf96.toList = assertHeader_chunk96 := by rfl
def assertHeader_string_leaf97 : String := "PURPOSE,"
theorem assertHeader_chunk_chars97 : assertHeader_string_leaf97.toList = assertHeader_chunk97 := by rfl
def assertHeader_string_leaf98 : String := " QUIET E"
theorem assertHeader_chunk_chars98 : assertHeader_string_leaf98.toList = assertHeader_chunk98 := by rfl
def assertHeader_string_leaf99 : String := "NJOYMENT"
theorem assertHeader_chunk_chars99 : assertHeader_string_leaf99.toList = assertHeader_chunk99 := by rfl
def assertHeader_string_leaf100 : String := " OR NON-"
theorem assertHeader_chunk_chars100 : assertHeader_string_leaf100.toList = assertHeader_chunk100 := by rfl
def assertHeader_string_leaf101 : String := "INFRINGE"
theorem assertHeader_chunk_chars101 : assertHeader_string_leaf101.toList = assertHeader_chunk101 := by rfl
def assertHeader_string_leaf102 : String := "MENT.\n *"
theorem assertHeader_chunk_chars102 : assertHeader_string_leaf102.toList = assertHeader_chunk102 := by rfl
def assertHeader_string_leaf103 : String := " Please "
theorem assertHeader_chunk_chars103 : assertHeader_string_leaf103.toList = assertHeader_chunk103 := by rfl
def assertHeader_string_leaf104 : String := "see the "
theorem assertHeader_chunk_chars104 : assertHeader_string_leaf104.toList = assertHeader_chunk104 := by rfl
def assertHeader_string_leaf105 : String := "License "
theorem assertHeader_chunk_chars105 : assertHeader_string_leaf105.toList = assertHeader_chunk105 := by rfl
def assertHeader_string_leaf106 : String := "for the "
theorem assertHeader_chunk_chars106 : assertHeader_string_leaf106.toList = assertHeader_chunk106 := by rfl
def assertHeader_string_leaf107 : String := "specific"
theorem assertHeader_chunk_chars107 : assertHeader_string_leaf107.toList = assertHeader_chunk107 := by rfl
def assertHeader_string_leaf108 : String := " languag"
theorem assertHeader_chunk_chars108 : assertHeader_string_leaf108.toList = assertHeader_chunk108 := by rfl
def assertHeader_string_leaf109 : String := "e govern"
theorem assertHeader_chunk_chars109 : assertHeader_string_leaf109.toList = assertHeader_chunk109 := by rfl
def assertHeader_string_leaf110 : String := "ing righ"
theorem assertHeader_chunk_chars110 : assertHeader_string_leaf110.toList = assertHeader_chunk110 := by rfl
def assertHeader_string_leaf111 : String := "ts and\n "
theorem assertHeader_chunk_chars111 : assertHeader_string_leaf111.toList = assertHeader_chunk111 := by rfl
def assertHeader_string_leaf112 : String := "* limita"
theorem assertHeader_chunk_chars112 : assertHeader_string_leaf112.toList = assertHeader_chunk112 := by rfl
def assertHeader_string_leaf113 : String := "tions un"
theorem assertHeader_chunk_chars113 : assertHeader_string_leaf113.toList = assertHeader_chunk113 := by rfl
def assertHeader_string_leaf114 : String := "der the "
theorem assertHeader_chunk_chars114 : assertHeader_string_leaf114.toList = assertHeader_chunk114 := by rfl
def assertHeader_string_leaf115 : String := "License."
theorem assertHeader_chunk_chars115 : assertHeader_string_leaf115.toList = assertHeader_chunk115 := by rfl
def assertHeader_string_leaf116 : String := "\n *\n * @"
theorem assertHeader_chunk_chars116 : assertHeader_string_leaf116.toList = assertHeader_chunk116 := by rfl
def assertHeader_string_leaf117 : String := "APPLE_LI"
theorem assertHeader_chunk_chars117 : assertHeader_string_leaf117.toList = assertHeader_chunk117 := by rfl
def assertHeader_string_leaf118 : String := "CENSE_HE"
theorem assertHeader_chunk_chars118 : assertHeader_string_leaf118.toList = assertHeader_chunk118 := by rfl
def assertHeader_string_leaf119 : String := "ADER_END"
theorem assertHeader_chunk_chars119 : assertHeader_string_leaf119.toList = assertHeader_chunk119 := by rfl
def assertHeader_string_leaf120 : String := "@\n */\n\n#"
theorem assertHeader_chunk_chars120 : assertHeader_string_leaf120.toList = assertHeader_chunk120 := by rfl
def assertHeader_string_leaf121 : String := "ifndef _"
theorem assertHeader_chunk_chars121 : assertHeader_string_leaf121.toList = assertHeader_chunk121 := by rfl
def assertHeader_string_leaf122 : String := "ASSERT_H"
theorem assertHeader_chunk_chars122 : assertHeader_string_leaf122.toList = assertHeader_chunk122 := by rfl
def assertHeader_string_leaf123 : String := "_\n#defin"
theorem assertHeader_chunk_chars123 : assertHeader_string_leaf123.toList = assertHeader_chunk123 := by rfl
def assertHeader_string_leaf124 : String := "e _ASSER"
theorem assertHeader_chunk_chars124 : assertHeader_string_leaf124.toList = assertHeader_chunk124 := by rfl
def assertHeader_string_leaf125 : String := "T_H_\n\n#i"
theorem assertHeader_chunk_chars125 : assertHeader_string_leaf125.toList = assertHeader_chunk125 := by rfl
def assertHeader_string_leaf126 : String := "fndef __"
theorem assertHeader_chunk_chars126 : assertHeader_string_leaf126.toList = assertHeader_chunk126 := by rfl
def assertHeader_string_leaf127 : String := "cplusplu"
theorem assertHeader_chunk_chars127 : assertHeader_string_leaf127.toList = assertHeader_chunk127 := by rfl
def assertHeader_string_leaf128 : String := "s\n#if de"
theorem assertHeader_chunk_chars128 : assertHeader_string_leaf128.toList = assertHeader_chunk128 := by rfl
def assertHeader_string_leaf129 : String := "fined(__"
theorem assertHeader_chunk_chars129 : assertHeader_string_leaf129.toList = assertHeader_chunk129 := by rfl
def assertHeader_string_leaf130 : String := "STDC_VER"
theorem assertHeader_chunk_chars130 : assertHeader_string_leaf130.toList = assertHeader_chunk130 := by rfl
def assertHeader_string_leaf131 : String := "SION__) "
theorem assertHeader_chunk_chars131 : assertHeader_string_leaf131.toList = assertHeader_chunk131 := by rfl
def assertHeader_string_leaf132 : String := "&& __STD"
theorem assertHeader_chunk_chars132 : assertHeader_string_leaf132.toList = assertHeader_chunk132 := by rfl
def assertHeader_string_leaf133 : String := "C_VERSIO"
theorem assertHeader_chunk_chars133 : assertHeader_string_leaf133.toList = assertHeader_chunk133 := by rfl
def assertHeader_string_leaf134 : String := "N__ >= 2"
theorem assertHeader_chunk_chars134 : assertHeader_string_leaf134.toList = assertHeader_chunk134 := by rfl
def assertHeader_string_leaf135 : String := "01112L\n#"
theorem assertHeader_chunk_chars135 : assertHeader_string_leaf135.toList = assertHeader_chunk135 := by rfl
def assertHeader_string_leaf136 : String := "define s"
theorem assertHeader_chunk_chars136 : assertHeader_string_leaf136.toList = assertHeader_chunk136 := by rfl
def assertHeader_string_leaf137 : String := "tatic_as"
theorem assertHeader_chunk_chars137 : assertHeader_string_leaf137.toList = assertHeader_chunk137 := by rfl
def assertHeader_string_leaf138 : String := "sert _St"
theorem assertHeader_chunk_chars138 : assertHeader_string_leaf138.toList = assertHeader_chunk138 := by rfl
def assertHeader_string_leaf139 : String := "atic_ass"
theorem assertHeader_chunk_chars139 : assertHeader_string_leaf139.toList = assertHeader_chunk139 := by rfl
def assertHeader_string_leaf140 : String := "ert\n#end"
theorem assertHeader_chunk_chars140 : assertHeader_string_leaf140.toList = assertHeader_chunk140 := by rfl
def assertHeader_string_leaf141 : String := "if /* __"
theorem assertHeader_chunk_chars141 : assertHeader_string_leaf141.toList = assertHeader_chunk141 := by rfl
def assertHeader_string_leaf142 : String := "STDC_VER"
theorem assertHeader_chunk_chars142 : assertHeader_string_leaf142.toList = assertHeader_chunk142 := by rfl
def assertHeader_string_leaf143 : String := "SION__ *"
theorem assertHeader_chunk_chars143 : assertHeader_string_leaf143.toList = assertHeader_chunk143 := by rfl
def assertHeader_string_leaf144 : String := "/\n#endif"
theorem assertHeader_chunk_chars144 : assertHeader_string_leaf144.toList = assertHeader_chunk144 := by rfl
def assertHeader_string_leaf145 : String := " /* !__c"
theorem assertHeader_chunk_chars145 : assertHeader_string_leaf145.toList = assertHeader_chunk145 := by rfl
def assertHeader_string_leaf146 : String := "plusplus"
theorem assertHeader_chunk_chars146 : assertHeader_string_leaf146.toList = assertHeader_chunk146 := by rfl
def assertHeader_string_leaf147 : String := " */\n\n#en"
theorem assertHeader_chunk_chars147 : assertHeader_string_leaf147.toList = assertHeader_chunk147 := by rfl
def assertHeader_string_leaf148 : String := "dif /* _"
theorem assertHeader_chunk_chars148 : assertHeader_string_leaf148.toList = assertHeader_chunk148 := by rfl
def assertHeader_string_leaf149 : String := "ASSERT_H"
theorem assertHeader_chunk_chars149 : assertHeader_string_leaf149.toList = assertHeader_chunk149 := by rfl
def assertHeader_string_leaf150 : String := "_ */\n"
theorem assertHeader_chunk_chars150 : assertHeader_string_leaf150.toList = assertHeader_chunk150 := by rfl
def assertHeader_parts_leaf0 : List (List Char) := [assertHeader_chunk0]
theorem assertHeader_parts_leaf0_flatten : assertHeader_chunk0 = assertHeader_parts_leaf0.flatten := by
  simp only [assertHeader_parts_leaf0, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf1 : List (List Char) := [assertHeader_chunk1]
theorem assertHeader_parts_leaf1_flatten : assertHeader_chunk1 = assertHeader_parts_leaf1.flatten := by
  simp only [assertHeader_parts_leaf1, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_0_2 : String := assertHeader_string_leaf0 ++ assertHeader_string_leaf1
def assertHeader_node_0_2_chars : List Char := assertHeader_chunk0 ++ assertHeader_chunk1
theorem assertHeader_node_0_2_literal : assertHeader_node_0_2 = "/*\n * Copyright " := by
  unfold assertHeader_node_0_2
  cbv
theorem assertHeader_node_0_2_characters : assertHeader_node_0_2.toList = assertHeader_node_0_2_chars := by
  unfold assertHeader_node_0_2 assertHeader_node_0_2_chars
  rw [String.toList_append, assertHeader_chunk_chars0, assertHeader_chunk_chars1]
def assertHeader_node_0_2_parts : List (List Char) := assertHeader_parts_leaf0 ++ assertHeader_parts_leaf1
theorem assertHeader_node_0_2_parts_literal : assertHeader_node_0_2_parts = [assertHeader_chunk0, assertHeader_chunk1] := by
  unfold assertHeader_node_0_2_parts
  rfl
theorem assertHeader_node_0_2_parts_flatten : assertHeader_node_0_2_chars = assertHeader_node_0_2_parts.flatten := by
  unfold assertHeader_node_0_2_chars assertHeader_node_0_2_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf0_flatten, ← assertHeader_parts_leaf1_flatten]
def assertHeader_parts_leaf2 : List (List Char) := [assertHeader_chunk2]
theorem assertHeader_parts_leaf2_flatten : assertHeader_chunk2 = assertHeader_parts_leaf2.flatten := by
  simp only [assertHeader_parts_leaf2, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf3 : List (List Char) := [assertHeader_chunk3]
theorem assertHeader_parts_leaf3_flatten : assertHeader_chunk3 = assertHeader_parts_leaf3.flatten := by
  simp only [assertHeader_parts_leaf3, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_2_4 : String := assertHeader_string_leaf2 ++ assertHeader_string_leaf3
def assertHeader_node_2_4_chars : List Char := assertHeader_chunk2 ++ assertHeader_chunk3
theorem assertHeader_node_2_4_literal : assertHeader_node_2_4 = "(c) 2023 Apple I" := by
  unfold assertHeader_node_2_4
  cbv
theorem assertHeader_node_2_4_characters : assertHeader_node_2_4.toList = assertHeader_node_2_4_chars := by
  unfold assertHeader_node_2_4 assertHeader_node_2_4_chars
  rw [String.toList_append, assertHeader_chunk_chars2, assertHeader_chunk_chars3]
def assertHeader_node_2_4_parts : List (List Char) := assertHeader_parts_leaf2 ++ assertHeader_parts_leaf3
theorem assertHeader_node_2_4_parts_literal : assertHeader_node_2_4_parts = [assertHeader_chunk2, assertHeader_chunk3] := by
  unfold assertHeader_node_2_4_parts
  rfl
theorem assertHeader_node_2_4_parts_flatten : assertHeader_node_2_4_chars = assertHeader_node_2_4_parts.flatten := by
  unfold assertHeader_node_2_4_chars assertHeader_node_2_4_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf2_flatten, ← assertHeader_parts_leaf3_flatten]
def assertHeader_node_0_4 : String := assertHeader_node_0_2 ++ assertHeader_node_2_4
def assertHeader_node_0_4_chars : List Char := assertHeader_node_0_2_chars ++ assertHeader_node_2_4_chars
theorem assertHeader_node_0_4_literal : assertHeader_node_0_4 = "/*\n * Copyright (c) 2023 Apple I" := by
  unfold assertHeader_node_0_4
  rw [assertHeader_node_0_2_literal]
  rw [assertHeader_node_2_4_literal]
  cbv
theorem assertHeader_node_0_4_characters : assertHeader_node_0_4.toList = assertHeader_node_0_4_chars := by
  unfold assertHeader_node_0_4 assertHeader_node_0_4_chars
  rw [String.toList_append, assertHeader_node_0_2_characters, assertHeader_node_2_4_characters]
def assertHeader_node_0_4_parts : List (List Char) := assertHeader_node_0_2_parts ++ assertHeader_node_2_4_parts
theorem assertHeader_node_0_4_parts_literal : assertHeader_node_0_4_parts = [assertHeader_chunk0, assertHeader_chunk1, assertHeader_chunk2, assertHeader_chunk3] := by
  unfold assertHeader_node_0_4_parts
  rw [assertHeader_node_0_2_parts_literal]
  rw [assertHeader_node_2_4_parts_literal]
  rfl
theorem assertHeader_node_0_4_parts_flatten : assertHeader_node_0_4_chars = assertHeader_node_0_4_parts.flatten := by
  unfold assertHeader_node_0_4_chars assertHeader_node_0_4_parts
  rw [List.flatten_append, ← assertHeader_node_0_2_parts_flatten, ← assertHeader_node_2_4_parts_flatten]
def assertHeader_parts_leaf4 : List (List Char) := [assertHeader_chunk4]
theorem assertHeader_parts_leaf4_flatten : assertHeader_chunk4 = assertHeader_parts_leaf4.flatten := by
  simp only [assertHeader_parts_leaf4, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf5 : List (List Char) := [assertHeader_chunk5]
theorem assertHeader_parts_leaf5_flatten : assertHeader_chunk5 = assertHeader_parts_leaf5.flatten := by
  simp only [assertHeader_parts_leaf5, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_4_6 : String := assertHeader_string_leaf4 ++ assertHeader_string_leaf5
def assertHeader_node_4_6_chars : List Char := assertHeader_chunk4 ++ assertHeader_chunk5
theorem assertHeader_node_4_6_literal : assertHeader_node_4_6 = "nc. All rights r" := by
  unfold assertHeader_node_4_6
  cbv
theorem assertHeader_node_4_6_characters : assertHeader_node_4_6.toList = assertHeader_node_4_6_chars := by
  unfold assertHeader_node_4_6 assertHeader_node_4_6_chars
  rw [String.toList_append, assertHeader_chunk_chars4, assertHeader_chunk_chars5]
def assertHeader_node_4_6_parts : List (List Char) := assertHeader_parts_leaf4 ++ assertHeader_parts_leaf5
theorem assertHeader_node_4_6_parts_literal : assertHeader_node_4_6_parts = [assertHeader_chunk4, assertHeader_chunk5] := by
  unfold assertHeader_node_4_6_parts
  rfl
theorem assertHeader_node_4_6_parts_flatten : assertHeader_node_4_6_chars = assertHeader_node_4_6_parts.flatten := by
  unfold assertHeader_node_4_6_chars assertHeader_node_4_6_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf4_flatten, ← assertHeader_parts_leaf5_flatten]
def assertHeader_parts_leaf6 : List (List Char) := [assertHeader_chunk6]
theorem assertHeader_parts_leaf6_flatten : assertHeader_chunk6 = assertHeader_parts_leaf6.flatten := by
  simp only [assertHeader_parts_leaf6, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf7 : List (List Char) := [assertHeader_chunk7]
theorem assertHeader_parts_leaf7_flatten : assertHeader_chunk7 = assertHeader_parts_leaf7.flatten := by
  simp only [assertHeader_parts_leaf7, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf8 : List (List Char) := [assertHeader_chunk8]
theorem assertHeader_parts_leaf8_flatten : assertHeader_chunk8 = assertHeader_parts_leaf8.flatten := by
  simp only [assertHeader_parts_leaf8, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_7_9 : String := assertHeader_string_leaf7 ++ assertHeader_string_leaf8
def assertHeader_node_7_9_chars : List Char := assertHeader_chunk7 ++ assertHeader_chunk8
theorem assertHeader_node_7_9_literal : assertHeader_node_7_9 = "\n *\n * @APPLE_LI" := by
  unfold assertHeader_node_7_9
  cbv
theorem assertHeader_node_7_9_characters : assertHeader_node_7_9.toList = assertHeader_node_7_9_chars := by
  unfold assertHeader_node_7_9 assertHeader_node_7_9_chars
  rw [String.toList_append, assertHeader_chunk_chars7, assertHeader_chunk_chars8]
def assertHeader_node_7_9_parts : List (List Char) := assertHeader_parts_leaf7 ++ assertHeader_parts_leaf8
theorem assertHeader_node_7_9_parts_literal : assertHeader_node_7_9_parts = [assertHeader_chunk7, assertHeader_chunk8] := by
  unfold assertHeader_node_7_9_parts
  rfl
theorem assertHeader_node_7_9_parts_flatten : assertHeader_node_7_9_chars = assertHeader_node_7_9_parts.flatten := by
  unfold assertHeader_node_7_9_chars assertHeader_node_7_9_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf7_flatten, ← assertHeader_parts_leaf8_flatten]
def assertHeader_node_6_9 : String := assertHeader_string_leaf6 ++ assertHeader_node_7_9
def assertHeader_node_6_9_chars : List Char := assertHeader_chunk6 ++ assertHeader_node_7_9_chars
theorem assertHeader_node_6_9_literal : assertHeader_node_6_9 = "eserved.\n *\n * @APPLE_LI" := by
  unfold assertHeader_node_6_9
  rw [assertHeader_node_7_9_literal]
  cbv
theorem assertHeader_node_6_9_characters : assertHeader_node_6_9.toList = assertHeader_node_6_9_chars := by
  unfold assertHeader_node_6_9 assertHeader_node_6_9_chars
  rw [String.toList_append, assertHeader_chunk_chars6, assertHeader_node_7_9_characters]
def assertHeader_node_6_9_parts : List (List Char) := assertHeader_parts_leaf6 ++ assertHeader_node_7_9_parts
theorem assertHeader_node_6_9_parts_literal : assertHeader_node_6_9_parts = [assertHeader_chunk6, assertHeader_chunk7, assertHeader_chunk8] := by
  unfold assertHeader_node_6_9_parts
  rw [assertHeader_node_7_9_parts_literal]
  rfl
theorem assertHeader_node_6_9_parts_flatten : assertHeader_node_6_9_chars = assertHeader_node_6_9_parts.flatten := by
  unfold assertHeader_node_6_9_chars assertHeader_node_6_9_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf6_flatten, ← assertHeader_node_7_9_parts_flatten]
def assertHeader_node_4_9 : String := assertHeader_node_4_6 ++ assertHeader_node_6_9
def assertHeader_node_4_9_chars : List Char := assertHeader_node_4_6_chars ++ assertHeader_node_6_9_chars
theorem assertHeader_node_4_9_literal : assertHeader_node_4_9 = "nc. All rights reserved.\n *\n * @APPLE_LI" := by
  unfold assertHeader_node_4_9
  rw [assertHeader_node_4_6_literal]
  rw [assertHeader_node_6_9_literal]
  cbv
theorem assertHeader_node_4_9_characters : assertHeader_node_4_9.toList = assertHeader_node_4_9_chars := by
  unfold assertHeader_node_4_9 assertHeader_node_4_9_chars
  rw [String.toList_append, assertHeader_node_4_6_characters, assertHeader_node_6_9_characters]
def assertHeader_node_4_9_parts : List (List Char) := assertHeader_node_4_6_parts ++ assertHeader_node_6_9_parts
theorem assertHeader_node_4_9_parts_literal : assertHeader_node_4_9_parts = [assertHeader_chunk4, assertHeader_chunk5, assertHeader_chunk6, assertHeader_chunk7, assertHeader_chunk8] := by
  unfold assertHeader_node_4_9_parts
  rw [assertHeader_node_4_6_parts_literal]
  rw [assertHeader_node_6_9_parts_literal]
  rfl
theorem assertHeader_node_4_9_parts_flatten : assertHeader_node_4_9_chars = assertHeader_node_4_9_parts.flatten := by
  unfold assertHeader_node_4_9_chars assertHeader_node_4_9_parts
  rw [List.flatten_append, ← assertHeader_node_4_6_parts_flatten, ← assertHeader_node_6_9_parts_flatten]
def assertHeader_node_0_9 : String := assertHeader_node_0_4 ++ assertHeader_node_4_9
def assertHeader_node_0_9_chars : List Char := assertHeader_node_0_4_chars ++ assertHeader_node_4_9_chars
theorem assertHeader_node_0_9_literal : assertHeader_node_0_9 = "/*\n * Copyright (c) 2023 Apple Inc. All rights reserved.\n *\n * @APPLE_LI" := by
  unfold assertHeader_node_0_9
  rw [assertHeader_node_0_4_literal]
  rw [assertHeader_node_4_9_literal]
  cbv
theorem assertHeader_node_0_9_characters : assertHeader_node_0_9.toList = assertHeader_node_0_9_chars := by
  unfold assertHeader_node_0_9 assertHeader_node_0_9_chars
  rw [String.toList_append, assertHeader_node_0_4_characters, assertHeader_node_4_9_characters]
def assertHeader_node_0_9_parts : List (List Char) := assertHeader_node_0_4_parts ++ assertHeader_node_4_9_parts
theorem assertHeader_node_0_9_parts_literal : assertHeader_node_0_9_parts = [assertHeader_chunk0, assertHeader_chunk1, assertHeader_chunk2, assertHeader_chunk3, assertHeader_chunk4, assertHeader_chunk5, assertHeader_chunk6, assertHeader_chunk7, assertHeader_chunk8] := by
  unfold assertHeader_node_0_9_parts
  rw [assertHeader_node_0_4_parts_literal]
  rw [assertHeader_node_4_9_parts_literal]
  rfl
theorem assertHeader_node_0_9_parts_flatten : assertHeader_node_0_9_chars = assertHeader_node_0_9_parts.flatten := by
  unfold assertHeader_node_0_9_chars assertHeader_node_0_9_parts
  rw [List.flatten_append, ← assertHeader_node_0_4_parts_flatten, ← assertHeader_node_4_9_parts_flatten]
def assertHeader_parts_leaf9 : List (List Char) := [assertHeader_chunk9]
theorem assertHeader_parts_leaf9_flatten : assertHeader_chunk9 = assertHeader_parts_leaf9.flatten := by
  simp only [assertHeader_parts_leaf9, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf10 : List (List Char) := [assertHeader_chunk10]
theorem assertHeader_parts_leaf10_flatten : assertHeader_chunk10 = assertHeader_parts_leaf10.flatten := by
  simp only [assertHeader_parts_leaf10, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_9_11 : String := assertHeader_string_leaf9 ++ assertHeader_string_leaf10
def assertHeader_node_9_11_chars : List Char := assertHeader_chunk9 ++ assertHeader_chunk10
theorem assertHeader_node_9_11_literal : assertHeader_node_9_11 = "CENSE_HEADER_STA" := by
  unfold assertHeader_node_9_11
  cbv
theorem assertHeader_node_9_11_characters : assertHeader_node_9_11.toList = assertHeader_node_9_11_chars := by
  unfold assertHeader_node_9_11 assertHeader_node_9_11_chars
  rw [String.toList_append, assertHeader_chunk_chars9, assertHeader_chunk_chars10]
def assertHeader_node_9_11_parts : List (List Char) := assertHeader_parts_leaf9 ++ assertHeader_parts_leaf10
theorem assertHeader_node_9_11_parts_literal : assertHeader_node_9_11_parts = [assertHeader_chunk9, assertHeader_chunk10] := by
  unfold assertHeader_node_9_11_parts
  rfl
theorem assertHeader_node_9_11_parts_flatten : assertHeader_node_9_11_chars = assertHeader_node_9_11_parts.flatten := by
  unfold assertHeader_node_9_11_chars assertHeader_node_9_11_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf9_flatten, ← assertHeader_parts_leaf10_flatten]
def assertHeader_parts_leaf11 : List (List Char) := [assertHeader_chunk11]
theorem assertHeader_parts_leaf11_flatten : assertHeader_chunk11 = assertHeader_parts_leaf11.flatten := by
  simp only [assertHeader_parts_leaf11, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf12 : List (List Char) := [assertHeader_chunk12]
theorem assertHeader_parts_leaf12_flatten : assertHeader_chunk12 = assertHeader_parts_leaf12.flatten := by
  simp only [assertHeader_parts_leaf12, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_11_13 : String := assertHeader_string_leaf11 ++ assertHeader_string_leaf12
def assertHeader_node_11_13_chars : List Char := assertHeader_chunk11 ++ assertHeader_chunk12
theorem assertHeader_node_11_13_literal : assertHeader_node_11_13 = "RT@\n *\n * This f" := by
  unfold assertHeader_node_11_13
  cbv
theorem assertHeader_node_11_13_characters : assertHeader_node_11_13.toList = assertHeader_node_11_13_chars := by
  unfold assertHeader_node_11_13 assertHeader_node_11_13_chars
  rw [String.toList_append, assertHeader_chunk_chars11, assertHeader_chunk_chars12]
def assertHeader_node_11_13_parts : List (List Char) := assertHeader_parts_leaf11 ++ assertHeader_parts_leaf12
theorem assertHeader_node_11_13_parts_literal : assertHeader_node_11_13_parts = [assertHeader_chunk11, assertHeader_chunk12] := by
  unfold assertHeader_node_11_13_parts
  rfl
theorem assertHeader_node_11_13_parts_flatten : assertHeader_node_11_13_chars = assertHeader_node_11_13_parts.flatten := by
  unfold assertHeader_node_11_13_chars assertHeader_node_11_13_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf11_flatten, ← assertHeader_parts_leaf12_flatten]
def assertHeader_node_9_13 : String := assertHeader_node_9_11 ++ assertHeader_node_11_13
def assertHeader_node_9_13_chars : List Char := assertHeader_node_9_11_chars ++ assertHeader_node_11_13_chars
theorem assertHeader_node_9_13_literal : assertHeader_node_9_13 = "CENSE_HEADER_START@\n *\n * This f" := by
  unfold assertHeader_node_9_13
  rw [assertHeader_node_9_11_literal]
  rw [assertHeader_node_11_13_literal]
  cbv
theorem assertHeader_node_9_13_characters : assertHeader_node_9_13.toList = assertHeader_node_9_13_chars := by
  unfold assertHeader_node_9_13 assertHeader_node_9_13_chars
  rw [String.toList_append, assertHeader_node_9_11_characters, assertHeader_node_11_13_characters]
def assertHeader_node_9_13_parts : List (List Char) := assertHeader_node_9_11_parts ++ assertHeader_node_11_13_parts
theorem assertHeader_node_9_13_parts_literal : assertHeader_node_9_13_parts = [assertHeader_chunk9, assertHeader_chunk10, assertHeader_chunk11, assertHeader_chunk12] := by
  unfold assertHeader_node_9_13_parts
  rw [assertHeader_node_9_11_parts_literal]
  rw [assertHeader_node_11_13_parts_literal]
  rfl
theorem assertHeader_node_9_13_parts_flatten : assertHeader_node_9_13_chars = assertHeader_node_9_13_parts.flatten := by
  unfold assertHeader_node_9_13_chars assertHeader_node_9_13_parts
  rw [List.flatten_append, ← assertHeader_node_9_11_parts_flatten, ← assertHeader_node_11_13_parts_flatten]
def assertHeader_parts_leaf13 : List (List Char) := [assertHeader_chunk13]
theorem assertHeader_parts_leaf13_flatten : assertHeader_chunk13 = assertHeader_parts_leaf13.flatten := by
  simp only [assertHeader_parts_leaf13, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf14 : List (List Char) := [assertHeader_chunk14]
theorem assertHeader_parts_leaf14_flatten : assertHeader_chunk14 = assertHeader_parts_leaf14.flatten := by
  simp only [assertHeader_parts_leaf14, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_13_15 : String := assertHeader_string_leaf13 ++ assertHeader_string_leaf14
def assertHeader_node_13_15_chars : List Char := assertHeader_chunk13 ++ assertHeader_chunk14
theorem assertHeader_node_13_15_literal : assertHeader_node_13_15 = "ile contains Ori" := by
  unfold assertHeader_node_13_15
  cbv
theorem assertHeader_node_13_15_characters : assertHeader_node_13_15.toList = assertHeader_node_13_15_chars := by
  unfold assertHeader_node_13_15 assertHeader_node_13_15_chars
  rw [String.toList_append, assertHeader_chunk_chars13, assertHeader_chunk_chars14]
def assertHeader_node_13_15_parts : List (List Char) := assertHeader_parts_leaf13 ++ assertHeader_parts_leaf14
theorem assertHeader_node_13_15_parts_literal : assertHeader_node_13_15_parts = [assertHeader_chunk13, assertHeader_chunk14] := by
  unfold assertHeader_node_13_15_parts
  rfl
theorem assertHeader_node_13_15_parts_flatten : assertHeader_node_13_15_chars = assertHeader_node_13_15_parts.flatten := by
  unfold assertHeader_node_13_15_chars assertHeader_node_13_15_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf13_flatten, ← assertHeader_parts_leaf14_flatten]
def assertHeader_parts_leaf15 : List (List Char) := [assertHeader_chunk15]
theorem assertHeader_parts_leaf15_flatten : assertHeader_chunk15 = assertHeader_parts_leaf15.flatten := by
  simp only [assertHeader_parts_leaf15, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf16 : List (List Char) := [assertHeader_chunk16]
theorem assertHeader_parts_leaf16_flatten : assertHeader_chunk16 = assertHeader_parts_leaf16.flatten := by
  simp only [assertHeader_parts_leaf16, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf17 : List (List Char) := [assertHeader_chunk17]
theorem assertHeader_parts_leaf17_flatten : assertHeader_chunk17 = assertHeader_parts_leaf17.flatten := by
  simp only [assertHeader_parts_leaf17, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_16_18 : String := assertHeader_string_leaf16 ++ assertHeader_string_leaf17
def assertHeader_node_16_18_chars : List Char := assertHeader_chunk16 ++ assertHeader_chunk17
theorem assertHeader_node_16_18_literal : assertHeader_node_16_18 = "de and/or Modifi" := by
  unfold assertHeader_node_16_18
  cbv
theorem assertHeader_node_16_18_characters : assertHeader_node_16_18.toList = assertHeader_node_16_18_chars := by
  unfold assertHeader_node_16_18 assertHeader_node_16_18_chars
  rw [String.toList_append, assertHeader_chunk_chars16, assertHeader_chunk_chars17]
def assertHeader_node_16_18_parts : List (List Char) := assertHeader_parts_leaf16 ++ assertHeader_parts_leaf17
theorem assertHeader_node_16_18_parts_literal : assertHeader_node_16_18_parts = [assertHeader_chunk16, assertHeader_chunk17] := by
  unfold assertHeader_node_16_18_parts
  rfl
theorem assertHeader_node_16_18_parts_flatten : assertHeader_node_16_18_chars = assertHeader_node_16_18_parts.flatten := by
  unfold assertHeader_node_16_18_chars assertHeader_node_16_18_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf16_flatten, ← assertHeader_parts_leaf17_flatten]
def assertHeader_node_15_18 : String := assertHeader_string_leaf15 ++ assertHeader_node_16_18
def assertHeader_node_15_18_chars : List Char := assertHeader_chunk15 ++ assertHeader_node_16_18_chars
theorem assertHeader_node_15_18_literal : assertHeader_node_15_18 = "ginal Code and/or Modifi" := by
  unfold assertHeader_node_15_18
  rw [assertHeader_node_16_18_literal]
  cbv
theorem assertHeader_node_15_18_characters : assertHeader_node_15_18.toList = assertHeader_node_15_18_chars := by
  unfold assertHeader_node_15_18 assertHeader_node_15_18_chars
  rw [String.toList_append, assertHeader_chunk_chars15, assertHeader_node_16_18_characters]
def assertHeader_node_15_18_parts : List (List Char) := assertHeader_parts_leaf15 ++ assertHeader_node_16_18_parts
theorem assertHeader_node_15_18_parts_literal : assertHeader_node_15_18_parts = [assertHeader_chunk15, assertHeader_chunk16, assertHeader_chunk17] := by
  unfold assertHeader_node_15_18_parts
  rw [assertHeader_node_16_18_parts_literal]
  rfl
theorem assertHeader_node_15_18_parts_flatten : assertHeader_node_15_18_chars = assertHeader_node_15_18_parts.flatten := by
  unfold assertHeader_node_15_18_chars assertHeader_node_15_18_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf15_flatten, ← assertHeader_node_16_18_parts_flatten]
def assertHeader_node_13_18 : String := assertHeader_node_13_15 ++ assertHeader_node_15_18
def assertHeader_node_13_18_chars : List Char := assertHeader_node_13_15_chars ++ assertHeader_node_15_18_chars
theorem assertHeader_node_13_18_literal : assertHeader_node_13_18 = "ile contains Original Code and/or Modifi" := by
  unfold assertHeader_node_13_18
  rw [assertHeader_node_13_15_literal]
  rw [assertHeader_node_15_18_literal]
  cbv
theorem assertHeader_node_13_18_characters : assertHeader_node_13_18.toList = assertHeader_node_13_18_chars := by
  unfold assertHeader_node_13_18 assertHeader_node_13_18_chars
  rw [String.toList_append, assertHeader_node_13_15_characters, assertHeader_node_15_18_characters]
def assertHeader_node_13_18_parts : List (List Char) := assertHeader_node_13_15_parts ++ assertHeader_node_15_18_parts
theorem assertHeader_node_13_18_parts_literal : assertHeader_node_13_18_parts = [assertHeader_chunk13, assertHeader_chunk14, assertHeader_chunk15, assertHeader_chunk16, assertHeader_chunk17] := by
  unfold assertHeader_node_13_18_parts
  rw [assertHeader_node_13_15_parts_literal]
  rw [assertHeader_node_15_18_parts_literal]
  rfl
theorem assertHeader_node_13_18_parts_flatten : assertHeader_node_13_18_chars = assertHeader_node_13_18_parts.flatten := by
  unfold assertHeader_node_13_18_chars assertHeader_node_13_18_parts
  rw [List.flatten_append, ← assertHeader_node_13_15_parts_flatten, ← assertHeader_node_15_18_parts_flatten]
def assertHeader_node_9_18 : String := assertHeader_node_9_13 ++ assertHeader_node_13_18
def assertHeader_node_9_18_chars : List Char := assertHeader_node_9_13_chars ++ assertHeader_node_13_18_chars
theorem assertHeader_node_9_18_literal : assertHeader_node_9_18 = "CENSE_HEADER_START@\n *\n * This file contains Original Code and/or Modifi" := by
  unfold assertHeader_node_9_18
  rw [assertHeader_node_9_13_literal]
  rw [assertHeader_node_13_18_literal]
  cbv
theorem assertHeader_node_9_18_characters : assertHeader_node_9_18.toList = assertHeader_node_9_18_chars := by
  unfold assertHeader_node_9_18 assertHeader_node_9_18_chars
  rw [String.toList_append, assertHeader_node_9_13_characters, assertHeader_node_13_18_characters]
def assertHeader_node_9_18_parts : List (List Char) := assertHeader_node_9_13_parts ++ assertHeader_node_13_18_parts
theorem assertHeader_node_9_18_parts_literal : assertHeader_node_9_18_parts = [assertHeader_chunk9, assertHeader_chunk10, assertHeader_chunk11, assertHeader_chunk12, assertHeader_chunk13, assertHeader_chunk14, assertHeader_chunk15, assertHeader_chunk16, assertHeader_chunk17] := by
  unfold assertHeader_node_9_18_parts
  rw [assertHeader_node_9_13_parts_literal]
  rw [assertHeader_node_13_18_parts_literal]
  rfl
theorem assertHeader_node_9_18_parts_flatten : assertHeader_node_9_18_chars = assertHeader_node_9_18_parts.flatten := by
  unfold assertHeader_node_9_18_chars assertHeader_node_9_18_parts
  rw [List.flatten_append, ← assertHeader_node_9_13_parts_flatten, ← assertHeader_node_13_18_parts_flatten]
def assertHeader_node_0_18 : String := assertHeader_node_0_9 ++ assertHeader_node_9_18
def assertHeader_node_0_18_chars : List Char := assertHeader_node_0_9_chars ++ assertHeader_node_9_18_chars
theorem assertHeader_node_0_18_literal : assertHeader_node_0_18 = "/*\n * Copyright (c) 2023 Apple Inc. All rights reserved.\n *\n * @APPLE_LICENSE_HEADER_START@\n *\n * This file contains Original Code and/or Modifi" := by
  unfold assertHeader_node_0_18
  rw [assertHeader_node_0_9_literal]
  rw [assertHeader_node_9_18_literal]
  cbv
theorem assertHeader_node_0_18_characters : assertHeader_node_0_18.toList = assertHeader_node_0_18_chars := by
  unfold assertHeader_node_0_18 assertHeader_node_0_18_chars
  rw [String.toList_append, assertHeader_node_0_9_characters, assertHeader_node_9_18_characters]
def assertHeader_node_0_18_parts : List (List Char) := assertHeader_node_0_9_parts ++ assertHeader_node_9_18_parts
theorem assertHeader_node_0_18_parts_literal : assertHeader_node_0_18_parts = [assertHeader_chunk0, assertHeader_chunk1, assertHeader_chunk2, assertHeader_chunk3, assertHeader_chunk4, assertHeader_chunk5, assertHeader_chunk6, assertHeader_chunk7, assertHeader_chunk8, assertHeader_chunk9, assertHeader_chunk10, assertHeader_chunk11, assertHeader_chunk12, assertHeader_chunk13, assertHeader_chunk14, assertHeader_chunk15, assertHeader_chunk16, assertHeader_chunk17] := by
  unfold assertHeader_node_0_18_parts
  rw [assertHeader_node_0_9_parts_literal]
  rw [assertHeader_node_9_18_parts_literal]
  rfl
theorem assertHeader_node_0_18_parts_flatten : assertHeader_node_0_18_chars = assertHeader_node_0_18_parts.flatten := by
  unfold assertHeader_node_0_18_chars assertHeader_node_0_18_parts
  rw [List.flatten_append, ← assertHeader_node_0_9_parts_flatten, ← assertHeader_node_9_18_parts_flatten]
def assertHeader_parts_leaf18 : List (List Char) := [assertHeader_chunk18]
theorem assertHeader_parts_leaf18_flatten : assertHeader_chunk18 = assertHeader_parts_leaf18.flatten := by
  simp only [assertHeader_parts_leaf18, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf19 : List (List Char) := [assertHeader_chunk19]
theorem assertHeader_parts_leaf19_flatten : assertHeader_chunk19 = assertHeader_parts_leaf19.flatten := by
  simp only [assertHeader_parts_leaf19, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_18_20 : String := assertHeader_string_leaf18 ++ assertHeader_string_leaf19
def assertHeader_node_18_20_chars : List Char := assertHeader_chunk18 ++ assertHeader_chunk19
theorem assertHeader_node_18_20_literal : assertHeader_node_18_20 = "cations of Origi" := by
  unfold assertHeader_node_18_20
  cbv
theorem assertHeader_node_18_20_characters : assertHeader_node_18_20.toList = assertHeader_node_18_20_chars := by
  unfold assertHeader_node_18_20 assertHeader_node_18_20_chars
  rw [String.toList_append, assertHeader_chunk_chars18, assertHeader_chunk_chars19]
def assertHeader_node_18_20_parts : List (List Char) := assertHeader_parts_leaf18 ++ assertHeader_parts_leaf19
theorem assertHeader_node_18_20_parts_literal : assertHeader_node_18_20_parts = [assertHeader_chunk18, assertHeader_chunk19] := by
  unfold assertHeader_node_18_20_parts
  rfl
theorem assertHeader_node_18_20_parts_flatten : assertHeader_node_18_20_chars = assertHeader_node_18_20_parts.flatten := by
  unfold assertHeader_node_18_20_chars assertHeader_node_18_20_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf18_flatten, ← assertHeader_parts_leaf19_flatten]
def assertHeader_parts_leaf20 : List (List Char) := [assertHeader_chunk20]
theorem assertHeader_parts_leaf20_flatten : assertHeader_chunk20 = assertHeader_parts_leaf20.flatten := by
  simp only [assertHeader_parts_leaf20, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf21 : List (List Char) := [assertHeader_chunk21]
theorem assertHeader_parts_leaf21_flatten : assertHeader_chunk21 = assertHeader_parts_leaf21.flatten := by
  simp only [assertHeader_parts_leaf21, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_20_22 : String := assertHeader_string_leaf20 ++ assertHeader_string_leaf21
def assertHeader_node_20_22_chars : List Char := assertHeader_chunk20 ++ assertHeader_chunk21
theorem assertHeader_node_20_22_literal : assertHeader_node_20_22 = "nal Code\n * as d" := by
  unfold assertHeader_node_20_22
  cbv
theorem assertHeader_node_20_22_characters : assertHeader_node_20_22.toList = assertHeader_node_20_22_chars := by
  unfold assertHeader_node_20_22 assertHeader_node_20_22_chars
  rw [String.toList_append, assertHeader_chunk_chars20, assertHeader_chunk_chars21]
def assertHeader_node_20_22_parts : List (List Char) := assertHeader_parts_leaf20 ++ assertHeader_parts_leaf21
theorem assertHeader_node_20_22_parts_literal : assertHeader_node_20_22_parts = [assertHeader_chunk20, assertHeader_chunk21] := by
  unfold assertHeader_node_20_22_parts
  rfl
theorem assertHeader_node_20_22_parts_flatten : assertHeader_node_20_22_chars = assertHeader_node_20_22_parts.flatten := by
  unfold assertHeader_node_20_22_chars assertHeader_node_20_22_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf20_flatten, ← assertHeader_parts_leaf21_flatten]
def assertHeader_node_18_22 : String := assertHeader_node_18_20 ++ assertHeader_node_20_22
def assertHeader_node_18_22_chars : List Char := assertHeader_node_18_20_chars ++ assertHeader_node_20_22_chars
theorem assertHeader_node_18_22_literal : assertHeader_node_18_22 = "cations of Original Code\n * as d" := by
  unfold assertHeader_node_18_22
  rw [assertHeader_node_18_20_literal]
  rw [assertHeader_node_20_22_literal]
  cbv
theorem assertHeader_node_18_22_characters : assertHeader_node_18_22.toList = assertHeader_node_18_22_chars := by
  unfold assertHeader_node_18_22 assertHeader_node_18_22_chars
  rw [String.toList_append, assertHeader_node_18_20_characters, assertHeader_node_20_22_characters]
def assertHeader_node_18_22_parts : List (List Char) := assertHeader_node_18_20_parts ++ assertHeader_node_20_22_parts
theorem assertHeader_node_18_22_parts_literal : assertHeader_node_18_22_parts = [assertHeader_chunk18, assertHeader_chunk19, assertHeader_chunk20, assertHeader_chunk21] := by
  unfold assertHeader_node_18_22_parts
  rw [assertHeader_node_18_20_parts_literal]
  rw [assertHeader_node_20_22_parts_literal]
  rfl
theorem assertHeader_node_18_22_parts_flatten : assertHeader_node_18_22_chars = assertHeader_node_18_22_parts.flatten := by
  unfold assertHeader_node_18_22_chars assertHeader_node_18_22_parts
  rw [List.flatten_append, ← assertHeader_node_18_20_parts_flatten, ← assertHeader_node_20_22_parts_flatten]
def assertHeader_parts_leaf22 : List (List Char) := [assertHeader_chunk22]
theorem assertHeader_parts_leaf22_flatten : assertHeader_chunk22 = assertHeader_parts_leaf22.flatten := by
  simp only [assertHeader_parts_leaf22, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf23 : List (List Char) := [assertHeader_chunk23]
theorem assertHeader_parts_leaf23_flatten : assertHeader_chunk23 = assertHeader_parts_leaf23.flatten := by
  simp only [assertHeader_parts_leaf23, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_22_24 : String := assertHeader_string_leaf22 ++ assertHeader_string_leaf23
def assertHeader_node_22_24_chars : List Char := assertHeader_chunk22 ++ assertHeader_chunk23
theorem assertHeader_node_22_24_literal : assertHeader_node_22_24 = "efined in and th" := by
  unfold assertHeader_node_22_24
  cbv
theorem assertHeader_node_22_24_characters : assertHeader_node_22_24.toList = assertHeader_node_22_24_chars := by
  unfold assertHeader_node_22_24 assertHeader_node_22_24_chars
  rw [String.toList_append, assertHeader_chunk_chars22, assertHeader_chunk_chars23]
def assertHeader_node_22_24_parts : List (List Char) := assertHeader_parts_leaf22 ++ assertHeader_parts_leaf23
theorem assertHeader_node_22_24_parts_literal : assertHeader_node_22_24_parts = [assertHeader_chunk22, assertHeader_chunk23] := by
  unfold assertHeader_node_22_24_parts
  rfl
theorem assertHeader_node_22_24_parts_flatten : assertHeader_node_22_24_chars = assertHeader_node_22_24_parts.flatten := by
  unfold assertHeader_node_22_24_chars assertHeader_node_22_24_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf22_flatten, ← assertHeader_parts_leaf23_flatten]
def assertHeader_parts_leaf24 : List (List Char) := [assertHeader_chunk24]
theorem assertHeader_parts_leaf24_flatten : assertHeader_chunk24 = assertHeader_parts_leaf24.flatten := by
  simp only [assertHeader_parts_leaf24, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf25 : List (List Char) := [assertHeader_chunk25]
theorem assertHeader_parts_leaf25_flatten : assertHeader_chunk25 = assertHeader_parts_leaf25.flatten := by
  simp only [assertHeader_parts_leaf25, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf26 : List (List Char) := [assertHeader_chunk26]
theorem assertHeader_parts_leaf26_flatten : assertHeader_chunk26 = assertHeader_parts_leaf26.flatten := by
  simp only [assertHeader_parts_leaf26, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_25_27 : String := assertHeader_string_leaf25 ++ assertHeader_string_leaf26
def assertHeader_node_25_27_chars : List Char := assertHeader_chunk25 ++ assertHeader_chunk26
theorem assertHeader_node_25_27_literal : assertHeader_node_25_27 = "ubject to the Ap" := by
  unfold assertHeader_node_25_27
  cbv
theorem assertHeader_node_25_27_characters : assertHeader_node_25_27.toList = assertHeader_node_25_27_chars := by
  unfold assertHeader_node_25_27 assertHeader_node_25_27_chars
  rw [String.toList_append, assertHeader_chunk_chars25, assertHeader_chunk_chars26]
def assertHeader_node_25_27_parts : List (List Char) := assertHeader_parts_leaf25 ++ assertHeader_parts_leaf26
theorem assertHeader_node_25_27_parts_literal : assertHeader_node_25_27_parts = [assertHeader_chunk25, assertHeader_chunk26] := by
  unfold assertHeader_node_25_27_parts
  rfl
theorem assertHeader_node_25_27_parts_flatten : assertHeader_node_25_27_chars = assertHeader_node_25_27_parts.flatten := by
  unfold assertHeader_node_25_27_chars assertHeader_node_25_27_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf25_flatten, ← assertHeader_parts_leaf26_flatten]
def assertHeader_node_24_27 : String := assertHeader_string_leaf24 ++ assertHeader_node_25_27
def assertHeader_node_24_27_chars : List Char := assertHeader_chunk24 ++ assertHeader_node_25_27_chars
theorem assertHeader_node_24_27_literal : assertHeader_node_24_27 = "at are subject to the Ap" := by
  unfold assertHeader_node_24_27
  rw [assertHeader_node_25_27_literal]
  cbv
theorem assertHeader_node_24_27_characters : assertHeader_node_24_27.toList = assertHeader_node_24_27_chars := by
  unfold assertHeader_node_24_27 assertHeader_node_24_27_chars
  rw [String.toList_append, assertHeader_chunk_chars24, assertHeader_node_25_27_characters]
def assertHeader_node_24_27_parts : List (List Char) := assertHeader_parts_leaf24 ++ assertHeader_node_25_27_parts
theorem assertHeader_node_24_27_parts_literal : assertHeader_node_24_27_parts = [assertHeader_chunk24, assertHeader_chunk25, assertHeader_chunk26] := by
  unfold assertHeader_node_24_27_parts
  rw [assertHeader_node_25_27_parts_literal]
  rfl
theorem assertHeader_node_24_27_parts_flatten : assertHeader_node_24_27_chars = assertHeader_node_24_27_parts.flatten := by
  unfold assertHeader_node_24_27_chars assertHeader_node_24_27_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf24_flatten, ← assertHeader_node_25_27_parts_flatten]
def assertHeader_node_22_27 : String := assertHeader_node_22_24 ++ assertHeader_node_24_27
def assertHeader_node_22_27_chars : List Char := assertHeader_node_22_24_chars ++ assertHeader_node_24_27_chars
theorem assertHeader_node_22_27_literal : assertHeader_node_22_27 = "efined in and that are subject to the Ap" := by
  unfold assertHeader_node_22_27
  rw [assertHeader_node_22_24_literal]
  rw [assertHeader_node_24_27_literal]
  cbv
theorem assertHeader_node_22_27_characters : assertHeader_node_22_27.toList = assertHeader_node_22_27_chars := by
  unfold assertHeader_node_22_27 assertHeader_node_22_27_chars
  rw [String.toList_append, assertHeader_node_22_24_characters, assertHeader_node_24_27_characters]
def assertHeader_node_22_27_parts : List (List Char) := assertHeader_node_22_24_parts ++ assertHeader_node_24_27_parts
theorem assertHeader_node_22_27_parts_literal : assertHeader_node_22_27_parts = [assertHeader_chunk22, assertHeader_chunk23, assertHeader_chunk24, assertHeader_chunk25, assertHeader_chunk26] := by
  unfold assertHeader_node_22_27_parts
  rw [assertHeader_node_22_24_parts_literal]
  rw [assertHeader_node_24_27_parts_literal]
  rfl
theorem assertHeader_node_22_27_parts_flatten : assertHeader_node_22_27_chars = assertHeader_node_22_27_parts.flatten := by
  unfold assertHeader_node_22_27_chars assertHeader_node_22_27_parts
  rw [List.flatten_append, ← assertHeader_node_22_24_parts_flatten, ← assertHeader_node_24_27_parts_flatten]
def assertHeader_node_18_27 : String := assertHeader_node_18_22 ++ assertHeader_node_22_27
def assertHeader_node_18_27_chars : List Char := assertHeader_node_18_22_chars ++ assertHeader_node_22_27_chars
theorem assertHeader_node_18_27_literal : assertHeader_node_18_27 = "cations of Original Code\n * as defined in and that are subject to the Ap" := by
  unfold assertHeader_node_18_27
  rw [assertHeader_node_18_22_literal]
  rw [assertHeader_node_22_27_literal]
  cbv
theorem assertHeader_node_18_27_characters : assertHeader_node_18_27.toList = assertHeader_node_18_27_chars := by
  unfold assertHeader_node_18_27 assertHeader_node_18_27_chars
  rw [String.toList_append, assertHeader_node_18_22_characters, assertHeader_node_22_27_characters]
def assertHeader_node_18_27_parts : List (List Char) := assertHeader_node_18_22_parts ++ assertHeader_node_22_27_parts
theorem assertHeader_node_18_27_parts_literal : assertHeader_node_18_27_parts = [assertHeader_chunk18, assertHeader_chunk19, assertHeader_chunk20, assertHeader_chunk21, assertHeader_chunk22, assertHeader_chunk23, assertHeader_chunk24, assertHeader_chunk25, assertHeader_chunk26] := by
  unfold assertHeader_node_18_27_parts
  rw [assertHeader_node_18_22_parts_literal]
  rw [assertHeader_node_22_27_parts_literal]
  rfl
theorem assertHeader_node_18_27_parts_flatten : assertHeader_node_18_27_chars = assertHeader_node_18_27_parts.flatten := by
  unfold assertHeader_node_18_27_chars assertHeader_node_18_27_parts
  rw [List.flatten_append, ← assertHeader_node_18_22_parts_flatten, ← assertHeader_node_22_27_parts_flatten]
def assertHeader_parts_leaf27 : List (List Char) := [assertHeader_chunk27]
theorem assertHeader_parts_leaf27_flatten : assertHeader_chunk27 = assertHeader_parts_leaf27.flatten := by
  simp only [assertHeader_parts_leaf27, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf28 : List (List Char) := [assertHeader_chunk28]
theorem assertHeader_parts_leaf28_flatten : assertHeader_chunk28 = assertHeader_parts_leaf28.flatten := by
  simp only [assertHeader_parts_leaf28, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_27_29 : String := assertHeader_string_leaf27 ++ assertHeader_string_leaf28
def assertHeader_node_27_29_chars : List Char := assertHeader_chunk27 ++ assertHeader_chunk28
theorem assertHeader_node_27_29_literal : assertHeader_node_27_29 = "ple Public Sourc" := by
  unfold assertHeader_node_27_29
  cbv
theorem assertHeader_node_27_29_characters : assertHeader_node_27_29.toList = assertHeader_node_27_29_chars := by
  unfold assertHeader_node_27_29 assertHeader_node_27_29_chars
  rw [String.toList_append, assertHeader_chunk_chars27, assertHeader_chunk_chars28]
def assertHeader_node_27_29_parts : List (List Char) := assertHeader_parts_leaf27 ++ assertHeader_parts_leaf28
theorem assertHeader_node_27_29_parts_literal : assertHeader_node_27_29_parts = [assertHeader_chunk27, assertHeader_chunk28] := by
  unfold assertHeader_node_27_29_parts
  rfl
theorem assertHeader_node_27_29_parts_flatten : assertHeader_node_27_29_chars = assertHeader_node_27_29_parts.flatten := by
  unfold assertHeader_node_27_29_chars assertHeader_node_27_29_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf27_flatten, ← assertHeader_parts_leaf28_flatten]
def assertHeader_parts_leaf29 : List (List Char) := [assertHeader_chunk29]
theorem assertHeader_parts_leaf29_flatten : assertHeader_chunk29 = assertHeader_parts_leaf29.flatten := by
  simp only [assertHeader_parts_leaf29, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf30 : List (List Char) := [assertHeader_chunk30]
theorem assertHeader_parts_leaf30_flatten : assertHeader_chunk30 = assertHeader_parts_leaf30.flatten := by
  simp only [assertHeader_parts_leaf30, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf31 : List (List Char) := [assertHeader_chunk31]
theorem assertHeader_parts_leaf31_flatten : assertHeader_chunk31 = assertHeader_parts_leaf31.flatten := by
  simp only [assertHeader_parts_leaf31, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_30_32 : String := assertHeader_string_leaf30 ++ assertHeader_string_leaf31
def assertHeader_node_30_32_chars : List Char := assertHeader_chunk30 ++ assertHeader_chunk31
theorem assertHeader_node_30_32_literal : assertHeader_node_30_32 = "e\n * Version 2.0" := by
  unfold assertHeader_node_30_32
  cbv
theorem assertHeader_node_30_32_characters : assertHeader_node_30_32.toList = assertHeader_node_30_32_chars := by
  unfold assertHeader_node_30_32 assertHeader_node_30_32_chars
  rw [String.toList_append, assertHeader_chunk_chars30, assertHeader_chunk_chars31]
def assertHeader_node_30_32_parts : List (List Char) := assertHeader_parts_leaf30 ++ assertHeader_parts_leaf31
theorem assertHeader_node_30_32_parts_literal : assertHeader_node_30_32_parts = [assertHeader_chunk30, assertHeader_chunk31] := by
  unfold assertHeader_node_30_32_parts
  rfl
theorem assertHeader_node_30_32_parts_flatten : assertHeader_node_30_32_chars = assertHeader_node_30_32_parts.flatten := by
  unfold assertHeader_node_30_32_chars assertHeader_node_30_32_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf30_flatten, ← assertHeader_parts_leaf31_flatten]
def assertHeader_node_29_32 : String := assertHeader_string_leaf29 ++ assertHeader_node_30_32
def assertHeader_node_29_32_chars : List Char := assertHeader_chunk29 ++ assertHeader_node_30_32_chars
theorem assertHeader_node_29_32_literal : assertHeader_node_29_32 = "e License\n * Version 2.0" := by
  unfold assertHeader_node_29_32
  rw [assertHeader_node_30_32_literal]
  cbv
theorem assertHeader_node_29_32_characters : assertHeader_node_29_32.toList = assertHeader_node_29_32_chars := by
  unfold assertHeader_node_29_32 assertHeader_node_29_32_chars
  rw [String.toList_append, assertHeader_chunk_chars29, assertHeader_node_30_32_characters]
def assertHeader_node_29_32_parts : List (List Char) := assertHeader_parts_leaf29 ++ assertHeader_node_30_32_parts
theorem assertHeader_node_29_32_parts_literal : assertHeader_node_29_32_parts = [assertHeader_chunk29, assertHeader_chunk30, assertHeader_chunk31] := by
  unfold assertHeader_node_29_32_parts
  rw [assertHeader_node_30_32_parts_literal]
  rfl
theorem assertHeader_node_29_32_parts_flatten : assertHeader_node_29_32_chars = assertHeader_node_29_32_parts.flatten := by
  unfold assertHeader_node_29_32_chars assertHeader_node_29_32_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf29_flatten, ← assertHeader_node_30_32_parts_flatten]
def assertHeader_node_27_32 : String := assertHeader_node_27_29 ++ assertHeader_node_29_32
def assertHeader_node_27_32_chars : List Char := assertHeader_node_27_29_chars ++ assertHeader_node_29_32_chars
theorem assertHeader_node_27_32_literal : assertHeader_node_27_32 = "ple Public Source License\n * Version 2.0" := by
  unfold assertHeader_node_27_32
  rw [assertHeader_node_27_29_literal]
  rw [assertHeader_node_29_32_literal]
  cbv
theorem assertHeader_node_27_32_characters : assertHeader_node_27_32.toList = assertHeader_node_27_32_chars := by
  unfold assertHeader_node_27_32 assertHeader_node_27_32_chars
  rw [String.toList_append, assertHeader_node_27_29_characters, assertHeader_node_29_32_characters]
def assertHeader_node_27_32_parts : List (List Char) := assertHeader_node_27_29_parts ++ assertHeader_node_29_32_parts
theorem assertHeader_node_27_32_parts_literal : assertHeader_node_27_32_parts = [assertHeader_chunk27, assertHeader_chunk28, assertHeader_chunk29, assertHeader_chunk30, assertHeader_chunk31] := by
  unfold assertHeader_node_27_32_parts
  rw [assertHeader_node_27_29_parts_literal]
  rw [assertHeader_node_29_32_parts_literal]
  rfl
theorem assertHeader_node_27_32_parts_flatten : assertHeader_node_27_32_chars = assertHeader_node_27_32_parts.flatten := by
  unfold assertHeader_node_27_32_chars assertHeader_node_27_32_parts
  rw [List.flatten_append, ← assertHeader_node_27_29_parts_flatten, ← assertHeader_node_29_32_parts_flatten]
def assertHeader_parts_leaf32 : List (List Char) := [assertHeader_chunk32]
theorem assertHeader_parts_leaf32_flatten : assertHeader_chunk32 = assertHeader_parts_leaf32.flatten := by
  simp only [assertHeader_parts_leaf32, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf33 : List (List Char) := [assertHeader_chunk33]
theorem assertHeader_parts_leaf33_flatten : assertHeader_chunk33 = assertHeader_parts_leaf33.flatten := by
  simp only [assertHeader_parts_leaf33, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_32_34 : String := assertHeader_string_leaf32 ++ assertHeader_string_leaf33
def assertHeader_node_32_34_chars : List Char := assertHeader_chunk32 ++ assertHeader_chunk33
theorem assertHeader_node_32_34_literal : assertHeader_node_32_34 = " (the 'License')" := by
  unfold assertHeader_node_32_34
  cbv
theorem assertHeader_node_32_34_characters : assertHeader_node_32_34.toList = assertHeader_node_32_34_chars := by
  unfold assertHeader_node_32_34 assertHeader_node_32_34_chars
  rw [String.toList_append, assertHeader_chunk_chars32, assertHeader_chunk_chars33]
def assertHeader_node_32_34_parts : List (List Char) := assertHeader_parts_leaf32 ++ assertHeader_parts_leaf33
theorem assertHeader_node_32_34_parts_literal : assertHeader_node_32_34_parts = [assertHeader_chunk32, assertHeader_chunk33] := by
  unfold assertHeader_node_32_34_parts
  rfl
theorem assertHeader_node_32_34_parts_flatten : assertHeader_node_32_34_chars = assertHeader_node_32_34_parts.flatten := by
  unfold assertHeader_node_32_34_chars assertHeader_node_32_34_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf32_flatten, ← assertHeader_parts_leaf33_flatten]
def assertHeader_parts_leaf34 : List (List Char) := [assertHeader_chunk34]
theorem assertHeader_parts_leaf34_flatten : assertHeader_chunk34 = assertHeader_parts_leaf34.flatten := by
  simp only [assertHeader_parts_leaf34, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf35 : List (List Char) := [assertHeader_chunk35]
theorem assertHeader_parts_leaf35_flatten : assertHeader_chunk35 = assertHeader_parts_leaf35.flatten := by
  simp only [assertHeader_parts_leaf35, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf36 : List (List Char) := [assertHeader_chunk36]
theorem assertHeader_parts_leaf36_flatten : assertHeader_chunk36 = assertHeader_parts_leaf36.flatten := by
  simp only [assertHeader_parts_leaf36, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_35_37 : String := assertHeader_string_leaf35 ++ assertHeader_string_leaf36
def assertHeader_node_35_37_chars : List Char := assertHeader_chunk35 ++ assertHeader_chunk36
theorem assertHeader_node_35_37_literal : assertHeader_node_35_37 = "y not use this f" := by
  unfold assertHeader_node_35_37
  cbv
theorem assertHeader_node_35_37_characters : assertHeader_node_35_37.toList = assertHeader_node_35_37_chars := by
  unfold assertHeader_node_35_37 assertHeader_node_35_37_chars
  rw [String.toList_append, assertHeader_chunk_chars35, assertHeader_chunk_chars36]
def assertHeader_node_35_37_parts : List (List Char) := assertHeader_parts_leaf35 ++ assertHeader_parts_leaf36
theorem assertHeader_node_35_37_parts_literal : assertHeader_node_35_37_parts = [assertHeader_chunk35, assertHeader_chunk36] := by
  unfold assertHeader_node_35_37_parts
  rfl
theorem assertHeader_node_35_37_parts_flatten : assertHeader_node_35_37_chars = assertHeader_node_35_37_parts.flatten := by
  unfold assertHeader_node_35_37_chars assertHeader_node_35_37_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf35_flatten, ← assertHeader_parts_leaf36_flatten]
def assertHeader_node_34_37 : String := assertHeader_string_leaf34 ++ assertHeader_node_35_37
def assertHeader_node_34_37_chars : List Char := assertHeader_chunk34 ++ assertHeader_node_35_37_chars
theorem assertHeader_node_34_37_literal : assertHeader_node_34_37 = ". You may not use this f" := by
  unfold assertHeader_node_34_37
  rw [assertHeader_node_35_37_literal]
  cbv
theorem assertHeader_node_34_37_characters : assertHeader_node_34_37.toList = assertHeader_node_34_37_chars := by
  unfold assertHeader_node_34_37 assertHeader_node_34_37_chars
  rw [String.toList_append, assertHeader_chunk_chars34, assertHeader_node_35_37_characters]
def assertHeader_node_34_37_parts : List (List Char) := assertHeader_parts_leaf34 ++ assertHeader_node_35_37_parts
theorem assertHeader_node_34_37_parts_literal : assertHeader_node_34_37_parts = [assertHeader_chunk34, assertHeader_chunk35, assertHeader_chunk36] := by
  unfold assertHeader_node_34_37_parts
  rw [assertHeader_node_35_37_parts_literal]
  rfl
theorem assertHeader_node_34_37_parts_flatten : assertHeader_node_34_37_chars = assertHeader_node_34_37_parts.flatten := by
  unfold assertHeader_node_34_37_chars assertHeader_node_34_37_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf34_flatten, ← assertHeader_node_35_37_parts_flatten]
def assertHeader_node_32_37 : String := assertHeader_node_32_34 ++ assertHeader_node_34_37
def assertHeader_node_32_37_chars : List Char := assertHeader_node_32_34_chars ++ assertHeader_node_34_37_chars
theorem assertHeader_node_32_37_literal : assertHeader_node_32_37 = " (the 'License'). You may not use this f" := by
  unfold assertHeader_node_32_37
  rw [assertHeader_node_32_34_literal]
  rw [assertHeader_node_34_37_literal]
  cbv
theorem assertHeader_node_32_37_characters : assertHeader_node_32_37.toList = assertHeader_node_32_37_chars := by
  unfold assertHeader_node_32_37 assertHeader_node_32_37_chars
  rw [String.toList_append, assertHeader_node_32_34_characters, assertHeader_node_34_37_characters]
def assertHeader_node_32_37_parts : List (List Char) := assertHeader_node_32_34_parts ++ assertHeader_node_34_37_parts
theorem assertHeader_node_32_37_parts_literal : assertHeader_node_32_37_parts = [assertHeader_chunk32, assertHeader_chunk33, assertHeader_chunk34, assertHeader_chunk35, assertHeader_chunk36] := by
  unfold assertHeader_node_32_37_parts
  rw [assertHeader_node_32_34_parts_literal]
  rw [assertHeader_node_34_37_parts_literal]
  rfl
theorem assertHeader_node_32_37_parts_flatten : assertHeader_node_32_37_chars = assertHeader_node_32_37_parts.flatten := by
  unfold assertHeader_node_32_37_chars assertHeader_node_32_37_parts
  rw [List.flatten_append, ← assertHeader_node_32_34_parts_flatten, ← assertHeader_node_34_37_parts_flatten]
def assertHeader_node_27_37 : String := assertHeader_node_27_32 ++ assertHeader_node_32_37
def assertHeader_node_27_37_chars : List Char := assertHeader_node_27_32_chars ++ assertHeader_node_32_37_chars
theorem assertHeader_node_27_37_literal : assertHeader_node_27_37 = "ple Public Source License\n * Version 2.0 (the 'License'). You may not use this f" := by
  unfold assertHeader_node_27_37
  rw [assertHeader_node_27_32_literal]
  rw [assertHeader_node_32_37_literal]
  cbv
theorem assertHeader_node_27_37_characters : assertHeader_node_27_37.toList = assertHeader_node_27_37_chars := by
  unfold assertHeader_node_27_37 assertHeader_node_27_37_chars
  rw [String.toList_append, assertHeader_node_27_32_characters, assertHeader_node_32_37_characters]
def assertHeader_node_27_37_parts : List (List Char) := assertHeader_node_27_32_parts ++ assertHeader_node_32_37_parts
theorem assertHeader_node_27_37_parts_literal : assertHeader_node_27_37_parts = [assertHeader_chunk27, assertHeader_chunk28, assertHeader_chunk29, assertHeader_chunk30, assertHeader_chunk31, assertHeader_chunk32, assertHeader_chunk33, assertHeader_chunk34, assertHeader_chunk35, assertHeader_chunk36] := by
  unfold assertHeader_node_27_37_parts
  rw [assertHeader_node_27_32_parts_literal]
  rw [assertHeader_node_32_37_parts_literal]
  rfl
theorem assertHeader_node_27_37_parts_flatten : assertHeader_node_27_37_chars = assertHeader_node_27_37_parts.flatten := by
  unfold assertHeader_node_27_37_chars assertHeader_node_27_37_parts
  rw [List.flatten_append, ← assertHeader_node_27_32_parts_flatten, ← assertHeader_node_32_37_parts_flatten]
def assertHeader_node_18_37 : String := assertHeader_node_18_27 ++ assertHeader_node_27_37
def assertHeader_node_18_37_chars : List Char := assertHeader_node_18_27_chars ++ assertHeader_node_27_37_chars
theorem assertHeader_node_18_37_literal : assertHeader_node_18_37 = "cations of Original Code\n * as defined in and that are subject to the Apple Public Source License\n * Version 2.0 (the 'License'). You may not use this f" := by
  unfold assertHeader_node_18_37
  rw [assertHeader_node_18_27_literal]
  rw [assertHeader_node_27_37_literal]
  cbv
theorem assertHeader_node_18_37_characters : assertHeader_node_18_37.toList = assertHeader_node_18_37_chars := by
  unfold assertHeader_node_18_37 assertHeader_node_18_37_chars
  rw [String.toList_append, assertHeader_node_18_27_characters, assertHeader_node_27_37_characters]
def assertHeader_node_18_37_parts : List (List Char) := assertHeader_node_18_27_parts ++ assertHeader_node_27_37_parts
theorem assertHeader_node_18_37_parts_literal : assertHeader_node_18_37_parts = [assertHeader_chunk18, assertHeader_chunk19, assertHeader_chunk20, assertHeader_chunk21, assertHeader_chunk22, assertHeader_chunk23, assertHeader_chunk24, assertHeader_chunk25, assertHeader_chunk26, assertHeader_chunk27, assertHeader_chunk28, assertHeader_chunk29, assertHeader_chunk30, assertHeader_chunk31, assertHeader_chunk32, assertHeader_chunk33, assertHeader_chunk34, assertHeader_chunk35, assertHeader_chunk36] := by
  unfold assertHeader_node_18_37_parts
  rw [assertHeader_node_18_27_parts_literal]
  rw [assertHeader_node_27_37_parts_literal]
  rfl
theorem assertHeader_node_18_37_parts_flatten : assertHeader_node_18_37_chars = assertHeader_node_18_37_parts.flatten := by
  unfold assertHeader_node_18_37_chars assertHeader_node_18_37_parts
  rw [List.flatten_append, ← assertHeader_node_18_27_parts_flatten, ← assertHeader_node_27_37_parts_flatten]
def assertHeader_node_0_37 : String := assertHeader_node_0_18 ++ assertHeader_node_18_37
def assertHeader_node_0_37_chars : List Char := assertHeader_node_0_18_chars ++ assertHeader_node_18_37_chars
theorem assertHeader_node_0_37_literal : assertHeader_node_0_37 = "/*\n * Copyright (c) 2023 Apple Inc. All rights reserved.\n *\n * @APPLE_LICENSE_HEADER_START@\n *\n * This file contains Original Code and/or Modifications of Original Code\n * as defined in and that are subject to the Apple Public Source License\n * Version 2.0 (the 'License'). You may not use this f" := by
  unfold assertHeader_node_0_37
  rw [assertHeader_node_0_18_literal]
  rw [assertHeader_node_18_37_literal]
  cbv
theorem assertHeader_node_0_37_characters : assertHeader_node_0_37.toList = assertHeader_node_0_37_chars := by
  unfold assertHeader_node_0_37 assertHeader_node_0_37_chars
  rw [String.toList_append, assertHeader_node_0_18_characters, assertHeader_node_18_37_characters]
def assertHeader_node_0_37_parts : List (List Char) := assertHeader_node_0_18_parts ++ assertHeader_node_18_37_parts
theorem assertHeader_node_0_37_parts_literal : assertHeader_node_0_37_parts = [assertHeader_chunk0, assertHeader_chunk1, assertHeader_chunk2, assertHeader_chunk3, assertHeader_chunk4, assertHeader_chunk5, assertHeader_chunk6, assertHeader_chunk7, assertHeader_chunk8, assertHeader_chunk9, assertHeader_chunk10, assertHeader_chunk11, assertHeader_chunk12, assertHeader_chunk13, assertHeader_chunk14, assertHeader_chunk15, assertHeader_chunk16, assertHeader_chunk17, assertHeader_chunk18, assertHeader_chunk19, assertHeader_chunk20, assertHeader_chunk21, assertHeader_chunk22, assertHeader_chunk23, assertHeader_chunk24, assertHeader_chunk25, assertHeader_chunk26, assertHeader_chunk27, assertHeader_chunk28, assertHeader_chunk29, assertHeader_chunk30, assertHeader_chunk31, assertHeader_chunk32, assertHeader_chunk33, assertHeader_chunk34, assertHeader_chunk35, assertHeader_chunk36] := by
  unfold assertHeader_node_0_37_parts
  rw [assertHeader_node_0_18_parts_literal]
  rw [assertHeader_node_18_37_parts_literal]
  rfl
theorem assertHeader_node_0_37_parts_flatten : assertHeader_node_0_37_chars = assertHeader_node_0_37_parts.flatten := by
  unfold assertHeader_node_0_37_chars assertHeader_node_0_37_parts
  rw [List.flatten_append, ← assertHeader_node_0_18_parts_flatten, ← assertHeader_node_18_37_parts_flatten]
def assertHeader_parts_leaf37 : List (List Char) := [assertHeader_chunk37]
theorem assertHeader_parts_leaf37_flatten : assertHeader_chunk37 = assertHeader_parts_leaf37.flatten := by
  simp only [assertHeader_parts_leaf37, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf38 : List (List Char) := [assertHeader_chunk38]
theorem assertHeader_parts_leaf38_flatten : assertHeader_chunk38 = assertHeader_parts_leaf38.flatten := by
  simp only [assertHeader_parts_leaf38, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_37_39 : String := assertHeader_string_leaf37 ++ assertHeader_string_leaf38
def assertHeader_node_37_39_chars : List Char := assertHeader_chunk37 ++ assertHeader_chunk38
theorem assertHeader_node_37_39_literal : assertHeader_node_37_39 = "ile except in\n *" := by
  unfold assertHeader_node_37_39
  cbv
theorem assertHeader_node_37_39_characters : assertHeader_node_37_39.toList = assertHeader_node_37_39_chars := by
  unfold assertHeader_node_37_39 assertHeader_node_37_39_chars
  rw [String.toList_append, assertHeader_chunk_chars37, assertHeader_chunk_chars38]
def assertHeader_node_37_39_parts : List (List Char) := assertHeader_parts_leaf37 ++ assertHeader_parts_leaf38
theorem assertHeader_node_37_39_parts_literal : assertHeader_node_37_39_parts = [assertHeader_chunk37, assertHeader_chunk38] := by
  unfold assertHeader_node_37_39_parts
  rfl
theorem assertHeader_node_37_39_parts_flatten : assertHeader_node_37_39_chars = assertHeader_node_37_39_parts.flatten := by
  unfold assertHeader_node_37_39_chars assertHeader_node_37_39_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf37_flatten, ← assertHeader_parts_leaf38_flatten]
def assertHeader_parts_leaf39 : List (List Char) := [assertHeader_chunk39]
theorem assertHeader_parts_leaf39_flatten : assertHeader_chunk39 = assertHeader_parts_leaf39.flatten := by
  simp only [assertHeader_parts_leaf39, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf40 : List (List Char) := [assertHeader_chunk40]
theorem assertHeader_parts_leaf40_flatten : assertHeader_chunk40 = assertHeader_parts_leaf40.flatten := by
  simp only [assertHeader_parts_leaf40, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_39_41 : String := assertHeader_string_leaf39 ++ assertHeader_string_leaf40
def assertHeader_node_39_41_chars : List Char := assertHeader_chunk39 ++ assertHeader_chunk40
theorem assertHeader_node_39_41_literal : assertHeader_node_39_41 = " compliance with" := by
  unfold assertHeader_node_39_41
  cbv
theorem assertHeader_node_39_41_characters : assertHeader_node_39_41.toList = assertHeader_node_39_41_chars := by
  unfold assertHeader_node_39_41 assertHeader_node_39_41_chars
  rw [String.toList_append, assertHeader_chunk_chars39, assertHeader_chunk_chars40]
def assertHeader_node_39_41_parts : List (List Char) := assertHeader_parts_leaf39 ++ assertHeader_parts_leaf40
theorem assertHeader_node_39_41_parts_literal : assertHeader_node_39_41_parts = [assertHeader_chunk39, assertHeader_chunk40] := by
  unfold assertHeader_node_39_41_parts
  rfl
theorem assertHeader_node_39_41_parts_flatten : assertHeader_node_39_41_chars = assertHeader_node_39_41_parts.flatten := by
  unfold assertHeader_node_39_41_chars assertHeader_node_39_41_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf39_flatten, ← assertHeader_parts_leaf40_flatten]
def assertHeader_node_37_41 : String := assertHeader_node_37_39 ++ assertHeader_node_39_41
def assertHeader_node_37_41_chars : List Char := assertHeader_node_37_39_chars ++ assertHeader_node_39_41_chars
theorem assertHeader_node_37_41_literal : assertHeader_node_37_41 = "ile except in\n * compliance with" := by
  unfold assertHeader_node_37_41
  rw [assertHeader_node_37_39_literal]
  rw [assertHeader_node_39_41_literal]
  cbv
theorem assertHeader_node_37_41_characters : assertHeader_node_37_41.toList = assertHeader_node_37_41_chars := by
  unfold assertHeader_node_37_41 assertHeader_node_37_41_chars
  rw [String.toList_append, assertHeader_node_37_39_characters, assertHeader_node_39_41_characters]
def assertHeader_node_37_41_parts : List (List Char) := assertHeader_node_37_39_parts ++ assertHeader_node_39_41_parts
theorem assertHeader_node_37_41_parts_literal : assertHeader_node_37_41_parts = [assertHeader_chunk37, assertHeader_chunk38, assertHeader_chunk39, assertHeader_chunk40] := by
  unfold assertHeader_node_37_41_parts
  rw [assertHeader_node_37_39_parts_literal]
  rw [assertHeader_node_39_41_parts_literal]
  rfl
theorem assertHeader_node_37_41_parts_flatten : assertHeader_node_37_41_chars = assertHeader_node_37_41_parts.flatten := by
  unfold assertHeader_node_37_41_chars assertHeader_node_37_41_parts
  rw [List.flatten_append, ← assertHeader_node_37_39_parts_flatten, ← assertHeader_node_39_41_parts_flatten]
def assertHeader_parts_leaf41 : List (List Char) := [assertHeader_chunk41]
theorem assertHeader_parts_leaf41_flatten : assertHeader_chunk41 = assertHeader_parts_leaf41.flatten := by
  simp only [assertHeader_parts_leaf41, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf42 : List (List Char) := [assertHeader_chunk42]
theorem assertHeader_parts_leaf42_flatten : assertHeader_chunk42 = assertHeader_parts_leaf42.flatten := by
  simp only [assertHeader_parts_leaf42, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_41_43 : String := assertHeader_string_leaf41 ++ assertHeader_string_leaf42
def assertHeader_node_41_43_chars : List Char := assertHeader_chunk41 ++ assertHeader_chunk42
theorem assertHeader_node_41_43_literal : assertHeader_node_41_43 = " the License. Pl" := by
  unfold assertHeader_node_41_43
  cbv
theorem assertHeader_node_41_43_characters : assertHeader_node_41_43.toList = assertHeader_node_41_43_chars := by
  unfold assertHeader_node_41_43 assertHeader_node_41_43_chars
  rw [String.toList_append, assertHeader_chunk_chars41, assertHeader_chunk_chars42]
def assertHeader_node_41_43_parts : List (List Char) := assertHeader_parts_leaf41 ++ assertHeader_parts_leaf42
theorem assertHeader_node_41_43_parts_literal : assertHeader_node_41_43_parts = [assertHeader_chunk41, assertHeader_chunk42] := by
  unfold assertHeader_node_41_43_parts
  rfl
theorem assertHeader_node_41_43_parts_flatten : assertHeader_node_41_43_chars = assertHeader_node_41_43_parts.flatten := by
  unfold assertHeader_node_41_43_chars assertHeader_node_41_43_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf41_flatten, ← assertHeader_parts_leaf42_flatten]
def assertHeader_parts_leaf43 : List (List Char) := [assertHeader_chunk43]
theorem assertHeader_parts_leaf43_flatten : assertHeader_chunk43 = assertHeader_parts_leaf43.flatten := by
  simp only [assertHeader_parts_leaf43, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf44 : List (List Char) := [assertHeader_chunk44]
theorem assertHeader_parts_leaf44_flatten : assertHeader_chunk44 = assertHeader_parts_leaf44.flatten := by
  simp only [assertHeader_parts_leaf44, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf45 : List (List Char) := [assertHeader_chunk45]
theorem assertHeader_parts_leaf45_flatten : assertHeader_chunk45 = assertHeader_parts_leaf45.flatten := by
  simp only [assertHeader_parts_leaf45, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_44_46 : String := assertHeader_string_leaf44 ++ assertHeader_string_leaf45
def assertHeader_node_44_46_chars : List Char := assertHeader_chunk44 ++ assertHeader_chunk45
theorem assertHeader_node_44_46_literal : assertHeader_node_44_46 = "ain a copy of th" := by
  unfold assertHeader_node_44_46
  cbv
theorem assertHeader_node_44_46_characters : assertHeader_node_44_46.toList = assertHeader_node_44_46_chars := by
  unfold assertHeader_node_44_46 assertHeader_node_44_46_chars
  rw [String.toList_append, assertHeader_chunk_chars44, assertHeader_chunk_chars45]
def assertHeader_node_44_46_parts : List (List Char) := assertHeader_parts_leaf44 ++ assertHeader_parts_leaf45
theorem assertHeader_node_44_46_parts_literal : assertHeader_node_44_46_parts = [assertHeader_chunk44, assertHeader_chunk45] := by
  unfold assertHeader_node_44_46_parts
  rfl
theorem assertHeader_node_44_46_parts_flatten : assertHeader_node_44_46_chars = assertHeader_node_44_46_parts.flatten := by
  unfold assertHeader_node_44_46_chars assertHeader_node_44_46_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf44_flatten, ← assertHeader_parts_leaf45_flatten]
def assertHeader_node_43_46 : String := assertHeader_string_leaf43 ++ assertHeader_node_44_46
def assertHeader_node_43_46_chars : List Char := assertHeader_chunk43 ++ assertHeader_node_44_46_chars
theorem assertHeader_node_43_46_literal : assertHeader_node_43_46 = "ease obtain a copy of th" := by
  unfold assertHeader_node_43_46
  rw [assertHeader_node_44_46_literal]
  cbv
theorem assertHeader_node_43_46_characters : assertHeader_node_43_46.toList = assertHeader_node_43_46_chars := by
  unfold assertHeader_node_43_46 assertHeader_node_43_46_chars
  rw [String.toList_append, assertHeader_chunk_chars43, assertHeader_node_44_46_characters]
def assertHeader_node_43_46_parts : List (List Char) := assertHeader_parts_leaf43 ++ assertHeader_node_44_46_parts
theorem assertHeader_node_43_46_parts_literal : assertHeader_node_43_46_parts = [assertHeader_chunk43, assertHeader_chunk44, assertHeader_chunk45] := by
  unfold assertHeader_node_43_46_parts
  rw [assertHeader_node_44_46_parts_literal]
  rfl
theorem assertHeader_node_43_46_parts_flatten : assertHeader_node_43_46_chars = assertHeader_node_43_46_parts.flatten := by
  unfold assertHeader_node_43_46_chars assertHeader_node_43_46_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf43_flatten, ← assertHeader_node_44_46_parts_flatten]
def assertHeader_node_41_46 : String := assertHeader_node_41_43 ++ assertHeader_node_43_46
def assertHeader_node_41_46_chars : List Char := assertHeader_node_41_43_chars ++ assertHeader_node_43_46_chars
theorem assertHeader_node_41_46_literal : assertHeader_node_41_46 = " the License. Please obtain a copy of th" := by
  unfold assertHeader_node_41_46
  rw [assertHeader_node_41_43_literal]
  rw [assertHeader_node_43_46_literal]
  cbv
theorem assertHeader_node_41_46_characters : assertHeader_node_41_46.toList = assertHeader_node_41_46_chars := by
  unfold assertHeader_node_41_46 assertHeader_node_41_46_chars
  rw [String.toList_append, assertHeader_node_41_43_characters, assertHeader_node_43_46_characters]
def assertHeader_node_41_46_parts : List (List Char) := assertHeader_node_41_43_parts ++ assertHeader_node_43_46_parts
theorem assertHeader_node_41_46_parts_literal : assertHeader_node_41_46_parts = [assertHeader_chunk41, assertHeader_chunk42, assertHeader_chunk43, assertHeader_chunk44, assertHeader_chunk45] := by
  unfold assertHeader_node_41_46_parts
  rw [assertHeader_node_41_43_parts_literal]
  rw [assertHeader_node_43_46_parts_literal]
  rfl
theorem assertHeader_node_41_46_parts_flatten : assertHeader_node_41_46_chars = assertHeader_node_41_46_parts.flatten := by
  unfold assertHeader_node_41_46_chars assertHeader_node_41_46_parts
  rw [List.flatten_append, ← assertHeader_node_41_43_parts_flatten, ← assertHeader_node_43_46_parts_flatten]
def assertHeader_node_37_46 : String := assertHeader_node_37_41 ++ assertHeader_node_41_46
def assertHeader_node_37_46_chars : List Char := assertHeader_node_37_41_chars ++ assertHeader_node_41_46_chars
theorem assertHeader_node_37_46_literal : assertHeader_node_37_46 = "ile except in\n * compliance with the License. Please obtain a copy of th" := by
  unfold assertHeader_node_37_46
  rw [assertHeader_node_37_41_literal]
  rw [assertHeader_node_41_46_literal]
  cbv
theorem assertHeader_node_37_46_characters : assertHeader_node_37_46.toList = assertHeader_node_37_46_chars := by
  unfold assertHeader_node_37_46 assertHeader_node_37_46_chars
  rw [String.toList_append, assertHeader_node_37_41_characters, assertHeader_node_41_46_characters]
def assertHeader_node_37_46_parts : List (List Char) := assertHeader_node_37_41_parts ++ assertHeader_node_41_46_parts
theorem assertHeader_node_37_46_parts_literal : assertHeader_node_37_46_parts = [assertHeader_chunk37, assertHeader_chunk38, assertHeader_chunk39, assertHeader_chunk40, assertHeader_chunk41, assertHeader_chunk42, assertHeader_chunk43, assertHeader_chunk44, assertHeader_chunk45] := by
  unfold assertHeader_node_37_46_parts
  rw [assertHeader_node_37_41_parts_literal]
  rw [assertHeader_node_41_46_parts_literal]
  rfl
theorem assertHeader_node_37_46_parts_flatten : assertHeader_node_37_46_chars = assertHeader_node_37_46_parts.flatten := by
  unfold assertHeader_node_37_46_chars assertHeader_node_37_46_parts
  rw [List.flatten_append, ← assertHeader_node_37_41_parts_flatten, ← assertHeader_node_41_46_parts_flatten]
def assertHeader_parts_leaf46 : List (List Char) := [assertHeader_chunk46]
theorem assertHeader_parts_leaf46_flatten : assertHeader_chunk46 = assertHeader_parts_leaf46.flatten := by
  simp only [assertHeader_parts_leaf46, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf47 : List (List Char) := [assertHeader_chunk47]
theorem assertHeader_parts_leaf47_flatten : assertHeader_chunk47 = assertHeader_parts_leaf47.flatten := by
  simp only [assertHeader_parts_leaf47, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_46_48 : String := assertHeader_string_leaf46 ++ assertHeader_string_leaf47
def assertHeader_node_46_48_chars : List Char := assertHeader_chunk46 ++ assertHeader_chunk47
theorem assertHeader_node_46_48_literal : assertHeader_node_46_48 = "e License at\n * " := by
  unfold assertHeader_node_46_48
  cbv
theorem assertHeader_node_46_48_characters : assertHeader_node_46_48.toList = assertHeader_node_46_48_chars := by
  unfold assertHeader_node_46_48 assertHeader_node_46_48_chars
  rw [String.toList_append, assertHeader_chunk_chars46, assertHeader_chunk_chars47]
def assertHeader_node_46_48_parts : List (List Char) := assertHeader_parts_leaf46 ++ assertHeader_parts_leaf47
theorem assertHeader_node_46_48_parts_literal : assertHeader_node_46_48_parts = [assertHeader_chunk46, assertHeader_chunk47] := by
  unfold assertHeader_node_46_48_parts
  rfl
theorem assertHeader_node_46_48_parts_flatten : assertHeader_node_46_48_chars = assertHeader_node_46_48_parts.flatten := by
  unfold assertHeader_node_46_48_chars assertHeader_node_46_48_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf46_flatten, ← assertHeader_parts_leaf47_flatten]
def assertHeader_parts_leaf48 : List (List Char) := [assertHeader_chunk48]
theorem assertHeader_parts_leaf48_flatten : assertHeader_chunk48 = assertHeader_parts_leaf48.flatten := by
  simp only [assertHeader_parts_leaf48, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf49 : List (List Char) := [assertHeader_chunk49]
theorem assertHeader_parts_leaf49_flatten : assertHeader_chunk49 = assertHeader_parts_leaf49.flatten := by
  simp only [assertHeader_parts_leaf49, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf50 : List (List Char) := [assertHeader_chunk50]
theorem assertHeader_parts_leaf50_flatten : assertHeader_chunk50 = assertHeader_parts_leaf50.flatten := by
  simp only [assertHeader_parts_leaf50, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_49_51 : String := assertHeader_string_leaf49 ++ assertHeader_string_leaf50
def assertHeader_node_49_51_chars : List Char := assertHeader_chunk49 ++ assertHeader_chunk50
theorem assertHeader_node_49_51_literal : assertHeader_node_49_51 = "ww.opensource.ap" := by
  unfold assertHeader_node_49_51
  cbv
theorem assertHeader_node_49_51_characters : assertHeader_node_49_51.toList = assertHeader_node_49_51_chars := by
  unfold assertHeader_node_49_51 assertHeader_node_49_51_chars
  rw [String.toList_append, assertHeader_chunk_chars49, assertHeader_chunk_chars50]
def assertHeader_node_49_51_parts : List (List Char) := assertHeader_parts_leaf49 ++ assertHeader_parts_leaf50
theorem assertHeader_node_49_51_parts_literal : assertHeader_node_49_51_parts = [assertHeader_chunk49, assertHeader_chunk50] := by
  unfold assertHeader_node_49_51_parts
  rfl
theorem assertHeader_node_49_51_parts_flatten : assertHeader_node_49_51_chars = assertHeader_node_49_51_parts.flatten := by
  unfold assertHeader_node_49_51_chars assertHeader_node_49_51_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf49_flatten, ← assertHeader_parts_leaf50_flatten]
def assertHeader_node_48_51 : String := assertHeader_string_leaf48 ++ assertHeader_node_49_51
def assertHeader_node_48_51_chars : List Char := assertHeader_chunk48 ++ assertHeader_node_49_51_chars
theorem assertHeader_node_48_51_literal : assertHeader_node_48_51 = "http://www.opensource.ap" := by
  unfold assertHeader_node_48_51
  rw [assertHeader_node_49_51_literal]
  cbv
theorem assertHeader_node_48_51_characters : assertHeader_node_48_51.toList = assertHeader_node_48_51_chars := by
  unfold assertHeader_node_48_51 assertHeader_node_48_51_chars
  rw [String.toList_append, assertHeader_chunk_chars48, assertHeader_node_49_51_characters]
def assertHeader_node_48_51_parts : List (List Char) := assertHeader_parts_leaf48 ++ assertHeader_node_49_51_parts
theorem assertHeader_node_48_51_parts_literal : assertHeader_node_48_51_parts = [assertHeader_chunk48, assertHeader_chunk49, assertHeader_chunk50] := by
  unfold assertHeader_node_48_51_parts
  rw [assertHeader_node_49_51_parts_literal]
  rfl
theorem assertHeader_node_48_51_parts_flatten : assertHeader_node_48_51_chars = assertHeader_node_48_51_parts.flatten := by
  unfold assertHeader_node_48_51_chars assertHeader_node_48_51_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf48_flatten, ← assertHeader_node_49_51_parts_flatten]
def assertHeader_node_46_51 : String := assertHeader_node_46_48 ++ assertHeader_node_48_51
def assertHeader_node_46_51_chars : List Char := assertHeader_node_46_48_chars ++ assertHeader_node_48_51_chars
theorem assertHeader_node_46_51_literal : assertHeader_node_46_51 = "e License at\n * http://www.opensource.ap" := by
  unfold assertHeader_node_46_51
  rw [assertHeader_node_46_48_literal]
  rw [assertHeader_node_48_51_literal]
  cbv
theorem assertHeader_node_46_51_characters : assertHeader_node_46_51.toList = assertHeader_node_46_51_chars := by
  unfold assertHeader_node_46_51 assertHeader_node_46_51_chars
  rw [String.toList_append, assertHeader_node_46_48_characters, assertHeader_node_48_51_characters]
def assertHeader_node_46_51_parts : List (List Char) := assertHeader_node_46_48_parts ++ assertHeader_node_48_51_parts
theorem assertHeader_node_46_51_parts_literal : assertHeader_node_46_51_parts = [assertHeader_chunk46, assertHeader_chunk47, assertHeader_chunk48, assertHeader_chunk49, assertHeader_chunk50] := by
  unfold assertHeader_node_46_51_parts
  rw [assertHeader_node_46_48_parts_literal]
  rw [assertHeader_node_48_51_parts_literal]
  rfl
theorem assertHeader_node_46_51_parts_flatten : assertHeader_node_46_51_chars = assertHeader_node_46_51_parts.flatten := by
  unfold assertHeader_node_46_51_chars assertHeader_node_46_51_parts
  rw [List.flatten_append, ← assertHeader_node_46_48_parts_flatten, ← assertHeader_node_48_51_parts_flatten]
def assertHeader_parts_leaf51 : List (List Char) := [assertHeader_chunk51]
theorem assertHeader_parts_leaf51_flatten : assertHeader_chunk51 = assertHeader_parts_leaf51.flatten := by
  simp only [assertHeader_parts_leaf51, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf52 : List (List Char) := [assertHeader_chunk52]
theorem assertHeader_parts_leaf52_flatten : assertHeader_chunk52 = assertHeader_parts_leaf52.flatten := by
  simp only [assertHeader_parts_leaf52, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_51_53 : String := assertHeader_string_leaf51 ++ assertHeader_string_leaf52
def assertHeader_node_51_53_chars : List Char := assertHeader_chunk51 ++ assertHeader_chunk52
theorem assertHeader_node_51_53_literal : assertHeader_node_51_53 = "ple.com/apsl/ an" := by
  unfold assertHeader_node_51_53
  cbv
theorem assertHeader_node_51_53_characters : assertHeader_node_51_53.toList = assertHeader_node_51_53_chars := by
  unfold assertHeader_node_51_53 assertHeader_node_51_53_chars
  rw [String.toList_append, assertHeader_chunk_chars51, assertHeader_chunk_chars52]
def assertHeader_node_51_53_parts : List (List Char) := assertHeader_parts_leaf51 ++ assertHeader_parts_leaf52
theorem assertHeader_node_51_53_parts_literal : assertHeader_node_51_53_parts = [assertHeader_chunk51, assertHeader_chunk52] := by
  unfold assertHeader_node_51_53_parts
  rfl
theorem assertHeader_node_51_53_parts_flatten : assertHeader_node_51_53_chars = assertHeader_node_51_53_parts.flatten := by
  unfold assertHeader_node_51_53_chars assertHeader_node_51_53_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf51_flatten, ← assertHeader_parts_leaf52_flatten]
def assertHeader_parts_leaf53 : List (List Char) := [assertHeader_chunk53]
theorem assertHeader_parts_leaf53_flatten : assertHeader_chunk53 = assertHeader_parts_leaf53.flatten := by
  simp only [assertHeader_parts_leaf53, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf54 : List (List Char) := [assertHeader_chunk54]
theorem assertHeader_parts_leaf54_flatten : assertHeader_chunk54 = assertHeader_parts_leaf54.flatten := by
  simp only [assertHeader_parts_leaf54, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf55 : List (List Char) := [assertHeader_chunk55]
theorem assertHeader_parts_leaf55_flatten : assertHeader_chunk55 = assertHeader_parts_leaf55.flatten := by
  simp only [assertHeader_parts_leaf55, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_54_56 : String := assertHeader_string_leaf54 ++ assertHeader_string_leaf55
def assertHeader_node_54_56_chars : List Char := assertHeader_chunk54 ++ assertHeader_chunk55
theorem assertHeader_node_54_56_literal : assertHeader_node_54_56 = "t before using t" := by
  unfold assertHeader_node_54_56
  cbv
theorem assertHeader_node_54_56_characters : assertHeader_node_54_56.toList = assertHeader_node_54_56_chars := by
  unfold assertHeader_node_54_56 assertHeader_node_54_56_chars
  rw [String.toList_append, assertHeader_chunk_chars54, assertHeader_chunk_chars55]
def assertHeader_node_54_56_parts : List (List Char) := assertHeader_parts_leaf54 ++ assertHeader_parts_leaf55
theorem assertHeader_node_54_56_parts_literal : assertHeader_node_54_56_parts = [assertHeader_chunk54, assertHeader_chunk55] := by
  unfold assertHeader_node_54_56_parts
  rfl
theorem assertHeader_node_54_56_parts_flatten : assertHeader_node_54_56_chars = assertHeader_node_54_56_parts.flatten := by
  unfold assertHeader_node_54_56_chars assertHeader_node_54_56_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf54_flatten, ← assertHeader_parts_leaf55_flatten]
def assertHeader_node_53_56 : String := assertHeader_string_leaf53 ++ assertHeader_node_54_56
def assertHeader_node_53_56_chars : List Char := assertHeader_chunk53 ++ assertHeader_node_54_56_chars
theorem assertHeader_node_53_56_literal : assertHeader_node_53_56 = "d read it before using t" := by
  unfold assertHeader_node_53_56
  rw [assertHeader_node_54_56_literal]
  cbv
theorem assertHeader_node_53_56_characters : assertHeader_node_53_56.toList = assertHeader_node_53_56_chars := by
  unfold assertHeader_node_53_56 assertHeader_node_53_56_chars
  rw [String.toList_append, assertHeader_chunk_chars53, assertHeader_node_54_56_characters]
def assertHeader_node_53_56_parts : List (List Char) := assertHeader_parts_leaf53 ++ assertHeader_node_54_56_parts
theorem assertHeader_node_53_56_parts_literal : assertHeader_node_53_56_parts = [assertHeader_chunk53, assertHeader_chunk54, assertHeader_chunk55] := by
  unfold assertHeader_node_53_56_parts
  rw [assertHeader_node_54_56_parts_literal]
  rfl
theorem assertHeader_node_53_56_parts_flatten : assertHeader_node_53_56_chars = assertHeader_node_53_56_parts.flatten := by
  unfold assertHeader_node_53_56_chars assertHeader_node_53_56_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf53_flatten, ← assertHeader_node_54_56_parts_flatten]
def assertHeader_node_51_56 : String := assertHeader_node_51_53 ++ assertHeader_node_53_56
def assertHeader_node_51_56_chars : List Char := assertHeader_node_51_53_chars ++ assertHeader_node_53_56_chars
theorem assertHeader_node_51_56_literal : assertHeader_node_51_56 = "ple.com/apsl/ and read it before using t" := by
  unfold assertHeader_node_51_56
  rw [assertHeader_node_51_53_literal]
  rw [assertHeader_node_53_56_literal]
  cbv
theorem assertHeader_node_51_56_characters : assertHeader_node_51_56.toList = assertHeader_node_51_56_chars := by
  unfold assertHeader_node_51_56 assertHeader_node_51_56_chars
  rw [String.toList_append, assertHeader_node_51_53_characters, assertHeader_node_53_56_characters]
def assertHeader_node_51_56_parts : List (List Char) := assertHeader_node_51_53_parts ++ assertHeader_node_53_56_parts
theorem assertHeader_node_51_56_parts_literal : assertHeader_node_51_56_parts = [assertHeader_chunk51, assertHeader_chunk52, assertHeader_chunk53, assertHeader_chunk54, assertHeader_chunk55] := by
  unfold assertHeader_node_51_56_parts
  rw [assertHeader_node_51_53_parts_literal]
  rw [assertHeader_node_53_56_parts_literal]
  rfl
theorem assertHeader_node_51_56_parts_flatten : assertHeader_node_51_56_chars = assertHeader_node_51_56_parts.flatten := by
  unfold assertHeader_node_51_56_chars assertHeader_node_51_56_parts
  rw [List.flatten_append, ← assertHeader_node_51_53_parts_flatten, ← assertHeader_node_53_56_parts_flatten]
def assertHeader_node_46_56 : String := assertHeader_node_46_51 ++ assertHeader_node_51_56
def assertHeader_node_46_56_chars : List Char := assertHeader_node_46_51_chars ++ assertHeader_node_51_56_chars
theorem assertHeader_node_46_56_literal : assertHeader_node_46_56 = "e License at\n * http://www.opensource.apple.com/apsl/ and read it before using t" := by
  unfold assertHeader_node_46_56
  rw [assertHeader_node_46_51_literal]
  rw [assertHeader_node_51_56_literal]
  cbv
theorem assertHeader_node_46_56_characters : assertHeader_node_46_56.toList = assertHeader_node_46_56_chars := by
  unfold assertHeader_node_46_56 assertHeader_node_46_56_chars
  rw [String.toList_append, assertHeader_node_46_51_characters, assertHeader_node_51_56_characters]
def assertHeader_node_46_56_parts : List (List Char) := assertHeader_node_46_51_parts ++ assertHeader_node_51_56_parts
theorem assertHeader_node_46_56_parts_literal : assertHeader_node_46_56_parts = [assertHeader_chunk46, assertHeader_chunk47, assertHeader_chunk48, assertHeader_chunk49, assertHeader_chunk50, assertHeader_chunk51, assertHeader_chunk52, assertHeader_chunk53, assertHeader_chunk54, assertHeader_chunk55] := by
  unfold assertHeader_node_46_56_parts
  rw [assertHeader_node_46_51_parts_literal]
  rw [assertHeader_node_51_56_parts_literal]
  rfl
theorem assertHeader_node_46_56_parts_flatten : assertHeader_node_46_56_chars = assertHeader_node_46_56_parts.flatten := by
  unfold assertHeader_node_46_56_chars assertHeader_node_46_56_parts
  rw [List.flatten_append, ← assertHeader_node_46_51_parts_flatten, ← assertHeader_node_51_56_parts_flatten]
def assertHeader_node_37_56 : String := assertHeader_node_37_46 ++ assertHeader_node_46_56
def assertHeader_node_37_56_chars : List Char := assertHeader_node_37_46_chars ++ assertHeader_node_46_56_chars
theorem assertHeader_node_37_56_literal : assertHeader_node_37_56 = "ile except in\n * compliance with the License. Please obtain a copy of the License at\n * http://www.opensource.apple.com/apsl/ and read it before using t" := by
  unfold assertHeader_node_37_56
  rw [assertHeader_node_37_46_literal]
  rw [assertHeader_node_46_56_literal]
  cbv
theorem assertHeader_node_37_56_characters : assertHeader_node_37_56.toList = assertHeader_node_37_56_chars := by
  unfold assertHeader_node_37_56 assertHeader_node_37_56_chars
  rw [String.toList_append, assertHeader_node_37_46_characters, assertHeader_node_46_56_characters]
def assertHeader_node_37_56_parts : List (List Char) := assertHeader_node_37_46_parts ++ assertHeader_node_46_56_parts
theorem assertHeader_node_37_56_parts_literal : assertHeader_node_37_56_parts = [assertHeader_chunk37, assertHeader_chunk38, assertHeader_chunk39, assertHeader_chunk40, assertHeader_chunk41, assertHeader_chunk42, assertHeader_chunk43, assertHeader_chunk44, assertHeader_chunk45, assertHeader_chunk46, assertHeader_chunk47, assertHeader_chunk48, assertHeader_chunk49, assertHeader_chunk50, assertHeader_chunk51, assertHeader_chunk52, assertHeader_chunk53, assertHeader_chunk54, assertHeader_chunk55] := by
  unfold assertHeader_node_37_56_parts
  rw [assertHeader_node_37_46_parts_literal]
  rw [assertHeader_node_46_56_parts_literal]
  rfl
theorem assertHeader_node_37_56_parts_flatten : assertHeader_node_37_56_chars = assertHeader_node_37_56_parts.flatten := by
  unfold assertHeader_node_37_56_chars assertHeader_node_37_56_parts
  rw [List.flatten_append, ← assertHeader_node_37_46_parts_flatten, ← assertHeader_node_46_56_parts_flatten]
def assertHeader_parts_leaf56 : List (List Char) := [assertHeader_chunk56]
theorem assertHeader_parts_leaf56_flatten : assertHeader_chunk56 = assertHeader_parts_leaf56.flatten := by
  simp only [assertHeader_parts_leaf56, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf57 : List (List Char) := [assertHeader_chunk57]
theorem assertHeader_parts_leaf57_flatten : assertHeader_chunk57 = assertHeader_parts_leaf57.flatten := by
  simp only [assertHeader_parts_leaf57, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_56_58 : String := assertHeader_string_leaf56 ++ assertHeader_string_leaf57
def assertHeader_node_56_58_chars : List Char := assertHeader_chunk56 ++ assertHeader_chunk57
theorem assertHeader_node_56_58_literal : assertHeader_node_56_58 = "his\n * file.\n *\n" := by
  unfold assertHeader_node_56_58
  cbv
theorem assertHeader_node_56_58_characters : assertHeader_node_56_58.toList = assertHeader_node_56_58_chars := by
  unfold assertHeader_node_56_58 assertHeader_node_56_58_chars
  rw [String.toList_append, assertHeader_chunk_chars56, assertHeader_chunk_chars57]
def assertHeader_node_56_58_parts : List (List Char) := assertHeader_parts_leaf56 ++ assertHeader_parts_leaf57
theorem assertHeader_node_56_58_parts_literal : assertHeader_node_56_58_parts = [assertHeader_chunk56, assertHeader_chunk57] := by
  unfold assertHeader_node_56_58_parts
  rfl
theorem assertHeader_node_56_58_parts_flatten : assertHeader_node_56_58_chars = assertHeader_node_56_58_parts.flatten := by
  unfold assertHeader_node_56_58_chars assertHeader_node_56_58_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf56_flatten, ← assertHeader_parts_leaf57_flatten]
def assertHeader_parts_leaf58 : List (List Char) := [assertHeader_chunk58]
theorem assertHeader_parts_leaf58_flatten : assertHeader_chunk58 = assertHeader_parts_leaf58.flatten := by
  simp only [assertHeader_parts_leaf58, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf59 : List (List Char) := [assertHeader_chunk59]
theorem assertHeader_parts_leaf59_flatten : assertHeader_chunk59 = assertHeader_parts_leaf59.flatten := by
  simp only [assertHeader_parts_leaf59, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_58_60 : String := assertHeader_string_leaf58 ++ assertHeader_string_leaf59
def assertHeader_node_58_60_chars : List Char := assertHeader_chunk58 ++ assertHeader_chunk59
theorem assertHeader_node_58_60_literal : assertHeader_node_58_60 = " * The Original " := by
  unfold assertHeader_node_58_60
  cbv
theorem assertHeader_node_58_60_characters : assertHeader_node_58_60.toList = assertHeader_node_58_60_chars := by
  unfold assertHeader_node_58_60 assertHeader_node_58_60_chars
  rw [String.toList_append, assertHeader_chunk_chars58, assertHeader_chunk_chars59]
def assertHeader_node_58_60_parts : List (List Char) := assertHeader_parts_leaf58 ++ assertHeader_parts_leaf59
theorem assertHeader_node_58_60_parts_literal : assertHeader_node_58_60_parts = [assertHeader_chunk58, assertHeader_chunk59] := by
  unfold assertHeader_node_58_60_parts
  rfl
theorem assertHeader_node_58_60_parts_flatten : assertHeader_node_58_60_chars = assertHeader_node_58_60_parts.flatten := by
  unfold assertHeader_node_58_60_chars assertHeader_node_58_60_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf58_flatten, ← assertHeader_parts_leaf59_flatten]
def assertHeader_node_56_60 : String := assertHeader_node_56_58 ++ assertHeader_node_58_60
def assertHeader_node_56_60_chars : List Char := assertHeader_node_56_58_chars ++ assertHeader_node_58_60_chars
theorem assertHeader_node_56_60_literal : assertHeader_node_56_60 = "his\n * file.\n *\n * The Original " := by
  unfold assertHeader_node_56_60
  rw [assertHeader_node_56_58_literal]
  rw [assertHeader_node_58_60_literal]
  cbv
theorem assertHeader_node_56_60_characters : assertHeader_node_56_60.toList = assertHeader_node_56_60_chars := by
  unfold assertHeader_node_56_60 assertHeader_node_56_60_chars
  rw [String.toList_append, assertHeader_node_56_58_characters, assertHeader_node_58_60_characters]
def assertHeader_node_56_60_parts : List (List Char) := assertHeader_node_56_58_parts ++ assertHeader_node_58_60_parts
theorem assertHeader_node_56_60_parts_literal : assertHeader_node_56_60_parts = [assertHeader_chunk56, assertHeader_chunk57, assertHeader_chunk58, assertHeader_chunk59] := by
  unfold assertHeader_node_56_60_parts
  rw [assertHeader_node_56_58_parts_literal]
  rw [assertHeader_node_58_60_parts_literal]
  rfl
theorem assertHeader_node_56_60_parts_flatten : assertHeader_node_56_60_chars = assertHeader_node_56_60_parts.flatten := by
  unfold assertHeader_node_56_60_chars assertHeader_node_56_60_parts
  rw [List.flatten_append, ← assertHeader_node_56_58_parts_flatten, ← assertHeader_node_58_60_parts_flatten]
def assertHeader_parts_leaf60 : List (List Char) := [assertHeader_chunk60]
theorem assertHeader_parts_leaf60_flatten : assertHeader_chunk60 = assertHeader_parts_leaf60.flatten := by
  simp only [assertHeader_parts_leaf60, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf61 : List (List Char) := [assertHeader_chunk61]
theorem assertHeader_parts_leaf61_flatten : assertHeader_chunk61 = assertHeader_parts_leaf61.flatten := by
  simp only [assertHeader_parts_leaf61, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_60_62 : String := assertHeader_string_leaf60 ++ assertHeader_string_leaf61
def assertHeader_node_60_62_chars : List Char := assertHeader_chunk60 ++ assertHeader_chunk61
theorem assertHeader_node_60_62_literal : assertHeader_node_60_62 = "Code and all sof" := by
  unfold assertHeader_node_60_62
  cbv
theorem assertHeader_node_60_62_characters : assertHeader_node_60_62.toList = assertHeader_node_60_62_chars := by
  unfold assertHeader_node_60_62 assertHeader_node_60_62_chars
  rw [String.toList_append, assertHeader_chunk_chars60, assertHeader_chunk_chars61]
def assertHeader_node_60_62_parts : List (List Char) := assertHeader_parts_leaf60 ++ assertHeader_parts_leaf61
theorem assertHeader_node_60_62_parts_literal : assertHeader_node_60_62_parts = [assertHeader_chunk60, assertHeader_chunk61] := by
  unfold assertHeader_node_60_62_parts
  rfl
theorem assertHeader_node_60_62_parts_flatten : assertHeader_node_60_62_chars = assertHeader_node_60_62_parts.flatten := by
  unfold assertHeader_node_60_62_chars assertHeader_node_60_62_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf60_flatten, ← assertHeader_parts_leaf61_flatten]
def assertHeader_parts_leaf62 : List (List Char) := [assertHeader_chunk62]
theorem assertHeader_parts_leaf62_flatten : assertHeader_chunk62 = assertHeader_parts_leaf62.flatten := by
  simp only [assertHeader_parts_leaf62, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf63 : List (List Char) := [assertHeader_chunk63]
theorem assertHeader_parts_leaf63_flatten : assertHeader_chunk63 = assertHeader_parts_leaf63.flatten := by
  simp only [assertHeader_parts_leaf63, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf64 : List (List Char) := [assertHeader_chunk64]
theorem assertHeader_parts_leaf64_flatten : assertHeader_chunk64 = assertHeader_parts_leaf64.flatten := by
  simp only [assertHeader_parts_leaf64, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_63_65 : String := assertHeader_string_leaf63 ++ assertHeader_string_leaf64
def assertHeader_node_63_65_chars : List Char := assertHeader_chunk63 ++ assertHeader_chunk64
theorem assertHeader_node_63_65_literal : assertHeader_node_63_65 = "stributed under " := by
  unfold assertHeader_node_63_65
  cbv
theorem assertHeader_node_63_65_characters : assertHeader_node_63_65.toList = assertHeader_node_63_65_chars := by
  unfold assertHeader_node_63_65 assertHeader_node_63_65_chars
  rw [String.toList_append, assertHeader_chunk_chars63, assertHeader_chunk_chars64]
def assertHeader_node_63_65_parts : List (List Char) := assertHeader_parts_leaf63 ++ assertHeader_parts_leaf64
theorem assertHeader_node_63_65_parts_literal : assertHeader_node_63_65_parts = [assertHeader_chunk63, assertHeader_chunk64] := by
  unfold assertHeader_node_63_65_parts
  rfl
theorem assertHeader_node_63_65_parts_flatten : assertHeader_node_63_65_chars = assertHeader_node_63_65_parts.flatten := by
  unfold assertHeader_node_63_65_chars assertHeader_node_63_65_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf63_flatten, ← assertHeader_parts_leaf64_flatten]
def assertHeader_node_62_65 : String := assertHeader_string_leaf62 ++ assertHeader_node_63_65
def assertHeader_node_62_65_chars : List Char := assertHeader_chunk62 ++ assertHeader_node_63_65_chars
theorem assertHeader_node_62_65_literal : assertHeader_node_62_65 = "tware distributed under " := by
  unfold assertHeader_node_62_65
  rw [assertHeader_node_63_65_literal]
  cbv
theorem assertHeader_node_62_65_characters : assertHeader_node_62_65.toList = assertHeader_node_62_65_chars := by
  unfold assertHeader_node_62_65 assertHeader_node_62_65_chars
  rw [String.toList_append, assertHeader_chunk_chars62, assertHeader_node_63_65_characters]
def assertHeader_node_62_65_parts : List (List Char) := assertHeader_parts_leaf62 ++ assertHeader_node_63_65_parts
theorem assertHeader_node_62_65_parts_literal : assertHeader_node_62_65_parts = [assertHeader_chunk62, assertHeader_chunk63, assertHeader_chunk64] := by
  unfold assertHeader_node_62_65_parts
  rw [assertHeader_node_63_65_parts_literal]
  rfl
theorem assertHeader_node_62_65_parts_flatten : assertHeader_node_62_65_chars = assertHeader_node_62_65_parts.flatten := by
  unfold assertHeader_node_62_65_chars assertHeader_node_62_65_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf62_flatten, ← assertHeader_node_63_65_parts_flatten]
def assertHeader_node_60_65 : String := assertHeader_node_60_62 ++ assertHeader_node_62_65
def assertHeader_node_60_65_chars : List Char := assertHeader_node_60_62_chars ++ assertHeader_node_62_65_chars
theorem assertHeader_node_60_65_literal : assertHeader_node_60_65 = "Code and all software distributed under " := by
  unfold assertHeader_node_60_65
  rw [assertHeader_node_60_62_literal]
  rw [assertHeader_node_62_65_literal]
  cbv
theorem assertHeader_node_60_65_characters : assertHeader_node_60_65.toList = assertHeader_node_60_65_chars := by
  unfold assertHeader_node_60_65 assertHeader_node_60_65_chars
  rw [String.toList_append, assertHeader_node_60_62_characters, assertHeader_node_62_65_characters]
def assertHeader_node_60_65_parts : List (List Char) := assertHeader_node_60_62_parts ++ assertHeader_node_62_65_parts
theorem assertHeader_node_60_65_parts_literal : assertHeader_node_60_65_parts = [assertHeader_chunk60, assertHeader_chunk61, assertHeader_chunk62, assertHeader_chunk63, assertHeader_chunk64] := by
  unfold assertHeader_node_60_65_parts
  rw [assertHeader_node_60_62_parts_literal]
  rw [assertHeader_node_62_65_parts_literal]
  rfl
theorem assertHeader_node_60_65_parts_flatten : assertHeader_node_60_65_chars = assertHeader_node_60_65_parts.flatten := by
  unfold assertHeader_node_60_65_chars assertHeader_node_60_65_parts
  rw [List.flatten_append, ← assertHeader_node_60_62_parts_flatten, ← assertHeader_node_62_65_parts_flatten]
def assertHeader_node_56_65 : String := assertHeader_node_56_60 ++ assertHeader_node_60_65
def assertHeader_node_56_65_chars : List Char := assertHeader_node_56_60_chars ++ assertHeader_node_60_65_chars
theorem assertHeader_node_56_65_literal : assertHeader_node_56_65 = "his\n * file.\n *\n * The Original Code and all software distributed under " := by
  unfold assertHeader_node_56_65
  rw [assertHeader_node_56_60_literal]
  rw [assertHeader_node_60_65_literal]
  cbv
theorem assertHeader_node_56_65_characters : assertHeader_node_56_65.toList = assertHeader_node_56_65_chars := by
  unfold assertHeader_node_56_65 assertHeader_node_56_65_chars
  rw [String.toList_append, assertHeader_node_56_60_characters, assertHeader_node_60_65_characters]
def assertHeader_node_56_65_parts : List (List Char) := assertHeader_node_56_60_parts ++ assertHeader_node_60_65_parts
theorem assertHeader_node_56_65_parts_literal : assertHeader_node_56_65_parts = [assertHeader_chunk56, assertHeader_chunk57, assertHeader_chunk58, assertHeader_chunk59, assertHeader_chunk60, assertHeader_chunk61, assertHeader_chunk62, assertHeader_chunk63, assertHeader_chunk64] := by
  unfold assertHeader_node_56_65_parts
  rw [assertHeader_node_56_60_parts_literal]
  rw [assertHeader_node_60_65_parts_literal]
  rfl
theorem assertHeader_node_56_65_parts_flatten : assertHeader_node_56_65_chars = assertHeader_node_56_65_parts.flatten := by
  unfold assertHeader_node_56_65_chars assertHeader_node_56_65_parts
  rw [List.flatten_append, ← assertHeader_node_56_60_parts_flatten, ← assertHeader_node_60_65_parts_flatten]
def assertHeader_parts_leaf65 : List (List Char) := [assertHeader_chunk65]
theorem assertHeader_parts_leaf65_flatten : assertHeader_chunk65 = assertHeader_parts_leaf65.flatten := by
  simp only [assertHeader_parts_leaf65, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf66 : List (List Char) := [assertHeader_chunk66]
theorem assertHeader_parts_leaf66_flatten : assertHeader_chunk66 = assertHeader_parts_leaf66.flatten := by
  simp only [assertHeader_parts_leaf66, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_65_67 : String := assertHeader_string_leaf65 ++ assertHeader_string_leaf66
def assertHeader_node_65_67_chars : List Char := assertHeader_chunk65 ++ assertHeader_chunk66
theorem assertHeader_node_65_67_literal : assertHeader_node_65_67 = "the License are\n" := by
  unfold assertHeader_node_65_67
  cbv
theorem assertHeader_node_65_67_characters : assertHeader_node_65_67.toList = assertHeader_node_65_67_chars := by
  unfold assertHeader_node_65_67 assertHeader_node_65_67_chars
  rw [String.toList_append, assertHeader_chunk_chars65, assertHeader_chunk_chars66]
def assertHeader_node_65_67_parts : List (List Char) := assertHeader_parts_leaf65 ++ assertHeader_parts_leaf66
theorem assertHeader_node_65_67_parts_literal : assertHeader_node_65_67_parts = [assertHeader_chunk65, assertHeader_chunk66] := by
  unfold assertHeader_node_65_67_parts
  rfl
theorem assertHeader_node_65_67_parts_flatten : assertHeader_node_65_67_chars = assertHeader_node_65_67_parts.flatten := by
  unfold assertHeader_node_65_67_chars assertHeader_node_65_67_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf65_flatten, ← assertHeader_parts_leaf66_flatten]
def assertHeader_parts_leaf67 : List (List Char) := [assertHeader_chunk67]
theorem assertHeader_parts_leaf67_flatten : assertHeader_chunk67 = assertHeader_parts_leaf67.flatten := by
  simp only [assertHeader_parts_leaf67, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf68 : List (List Char) := [assertHeader_chunk68]
theorem assertHeader_parts_leaf68_flatten : assertHeader_chunk68 = assertHeader_parts_leaf68.flatten := by
  simp only [assertHeader_parts_leaf68, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf69 : List (List Char) := [assertHeader_chunk69]
theorem assertHeader_parts_leaf69_flatten : assertHeader_chunk69 = assertHeader_parts_leaf69.flatten := by
  simp only [assertHeader_parts_leaf69, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_68_70 : String := assertHeader_string_leaf68 ++ assertHeader_string_leaf69
def assertHeader_node_68_70_chars : List Char := assertHeader_chunk68 ++ assertHeader_chunk69
theorem assertHeader_node_68_70_literal : assertHeader_node_68_70 = "ibuted on an 'AS" := by
  unfold assertHeader_node_68_70
  cbv
theorem assertHeader_node_68_70_characters : assertHeader_node_68_70.toList = assertHeader_node_68_70_chars := by
  unfold assertHeader_node_68_70 assertHeader_node_68_70_chars
  rw [String.toList_append, assertHeader_chunk_chars68, assertHeader_chunk_chars69]
def assertHeader_node_68_70_parts : List (List Char) := assertHeader_parts_leaf68 ++ assertHeader_parts_leaf69
theorem assertHeader_node_68_70_parts_literal : assertHeader_node_68_70_parts = [assertHeader_chunk68, assertHeader_chunk69] := by
  unfold assertHeader_node_68_70_parts
  rfl
theorem assertHeader_node_68_70_parts_flatten : assertHeader_node_68_70_chars = assertHeader_node_68_70_parts.flatten := by
  unfold assertHeader_node_68_70_chars assertHeader_node_68_70_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf68_flatten, ← assertHeader_parts_leaf69_flatten]
def assertHeader_node_67_70 : String := assertHeader_string_leaf67 ++ assertHeader_node_68_70
def assertHeader_node_67_70_chars : List Char := assertHeader_chunk67 ++ assertHeader_node_68_70_chars
theorem assertHeader_node_67_70_literal : assertHeader_node_67_70 = " * distributed on an 'AS" := by
  unfold assertHeader_node_67_70
  rw [assertHeader_node_68_70_literal]
  cbv
theorem assertHeader_node_67_70_characters : assertHeader_node_67_70.toList = assertHeader_node_67_70_chars := by
  unfold assertHeader_node_67_70 assertHeader_node_67_70_chars
  rw [String.toList_append, assertHeader_chunk_chars67, assertHeader_node_68_70_characters]
def assertHeader_node_67_70_parts : List (List Char) := assertHeader_parts_leaf67 ++ assertHeader_node_68_70_parts
theorem assertHeader_node_67_70_parts_literal : assertHeader_node_67_70_parts = [assertHeader_chunk67, assertHeader_chunk68, assertHeader_chunk69] := by
  unfold assertHeader_node_67_70_parts
  rw [assertHeader_node_68_70_parts_literal]
  rfl
theorem assertHeader_node_67_70_parts_flatten : assertHeader_node_67_70_chars = assertHeader_node_67_70_parts.flatten := by
  unfold assertHeader_node_67_70_chars assertHeader_node_67_70_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf67_flatten, ← assertHeader_node_68_70_parts_flatten]
def assertHeader_node_65_70 : String := assertHeader_node_65_67 ++ assertHeader_node_67_70
def assertHeader_node_65_70_chars : List Char := assertHeader_node_65_67_chars ++ assertHeader_node_67_70_chars
theorem assertHeader_node_65_70_literal : assertHeader_node_65_70 = "the License are\n * distributed on an 'AS" := by
  unfold assertHeader_node_65_70
  rw [assertHeader_node_65_67_literal]
  rw [assertHeader_node_67_70_literal]
  cbv
theorem assertHeader_node_65_70_characters : assertHeader_node_65_70.toList = assertHeader_node_65_70_chars := by
  unfold assertHeader_node_65_70 assertHeader_node_65_70_chars
  rw [String.toList_append, assertHeader_node_65_67_characters, assertHeader_node_67_70_characters]
def assertHeader_node_65_70_parts : List (List Char) := assertHeader_node_65_67_parts ++ assertHeader_node_67_70_parts
theorem assertHeader_node_65_70_parts_literal : assertHeader_node_65_70_parts = [assertHeader_chunk65, assertHeader_chunk66, assertHeader_chunk67, assertHeader_chunk68, assertHeader_chunk69] := by
  unfold assertHeader_node_65_70_parts
  rw [assertHeader_node_65_67_parts_literal]
  rw [assertHeader_node_67_70_parts_literal]
  rfl
theorem assertHeader_node_65_70_parts_flatten : assertHeader_node_65_70_chars = assertHeader_node_65_70_parts.flatten := by
  unfold assertHeader_node_65_70_chars assertHeader_node_65_70_parts
  rw [List.flatten_append, ← assertHeader_node_65_67_parts_flatten, ← assertHeader_node_67_70_parts_flatten]
def assertHeader_parts_leaf70 : List (List Char) := [assertHeader_chunk70]
theorem assertHeader_parts_leaf70_flatten : assertHeader_chunk70 = assertHeader_parts_leaf70.flatten := by
  simp only [assertHeader_parts_leaf70, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf71 : List (List Char) := [assertHeader_chunk71]
theorem assertHeader_parts_leaf71_flatten : assertHeader_chunk71 = assertHeader_parts_leaf71.flatten := by
  simp only [assertHeader_parts_leaf71, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_70_72 : String := assertHeader_string_leaf70 ++ assertHeader_string_leaf71
def assertHeader_node_70_72_chars : List Char := assertHeader_chunk70 ++ assertHeader_chunk71
theorem assertHeader_node_70_72_literal : assertHeader_node_70_72 = " IS' basis, WITH" := by
  unfold assertHeader_node_70_72
  cbv
theorem assertHeader_node_70_72_characters : assertHeader_node_70_72.toList = assertHeader_node_70_72_chars := by
  unfold assertHeader_node_70_72 assertHeader_node_70_72_chars
  rw [String.toList_append, assertHeader_chunk_chars70, assertHeader_chunk_chars71]
def assertHeader_node_70_72_parts : List (List Char) := assertHeader_parts_leaf70 ++ assertHeader_parts_leaf71
theorem assertHeader_node_70_72_parts_literal : assertHeader_node_70_72_parts = [assertHeader_chunk70, assertHeader_chunk71] := by
  unfold assertHeader_node_70_72_parts
  rfl
theorem assertHeader_node_70_72_parts_flatten : assertHeader_node_70_72_chars = assertHeader_node_70_72_parts.flatten := by
  unfold assertHeader_node_70_72_chars assertHeader_node_70_72_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf70_flatten, ← assertHeader_parts_leaf71_flatten]
def assertHeader_parts_leaf72 : List (List Char) := [assertHeader_chunk72]
theorem assertHeader_parts_leaf72_flatten : assertHeader_chunk72 = assertHeader_parts_leaf72.flatten := by
  simp only [assertHeader_parts_leaf72, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf73 : List (List Char) := [assertHeader_chunk73]
theorem assertHeader_parts_leaf73_flatten : assertHeader_chunk73 = assertHeader_parts_leaf73.flatten := by
  simp only [assertHeader_parts_leaf73, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf74 : List (List Char) := [assertHeader_chunk74]
theorem assertHeader_parts_leaf74_flatten : assertHeader_chunk74 = assertHeader_parts_leaf74.flatten := by
  simp only [assertHeader_parts_leaf74, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_73_75 : String := assertHeader_string_leaf73 ++ assertHeader_string_leaf74
def assertHeader_node_73_75_chars : List Char := assertHeader_chunk73 ++ assertHeader_chunk74
theorem assertHeader_node_73_75_literal : assertHeader_node_73_75 = "ANTY OF ANY KIND" := by
  unfold assertHeader_node_73_75
  cbv
theorem assertHeader_node_73_75_characters : assertHeader_node_73_75.toList = assertHeader_node_73_75_chars := by
  unfold assertHeader_node_73_75 assertHeader_node_73_75_chars
  rw [String.toList_append, assertHeader_chunk_chars73, assertHeader_chunk_chars74]
def assertHeader_node_73_75_parts : List (List Char) := assertHeader_parts_leaf73 ++ assertHeader_parts_leaf74
theorem assertHeader_node_73_75_parts_literal : assertHeader_node_73_75_parts = [assertHeader_chunk73, assertHeader_chunk74] := by
  unfold assertHeader_node_73_75_parts
  rfl
theorem assertHeader_node_73_75_parts_flatten : assertHeader_node_73_75_chars = assertHeader_node_73_75_parts.flatten := by
  unfold assertHeader_node_73_75_chars assertHeader_node_73_75_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf73_flatten, ← assertHeader_parts_leaf74_flatten]
def assertHeader_node_72_75 : String := assertHeader_string_leaf72 ++ assertHeader_node_73_75
def assertHeader_node_72_75_chars : List Char := assertHeader_chunk72 ++ assertHeader_node_73_75_chars
theorem assertHeader_node_72_75_literal : assertHeader_node_72_75 = "OUT WARRANTY OF ANY KIND" := by
  unfold assertHeader_node_72_75
  rw [assertHeader_node_73_75_literal]
  cbv
theorem assertHeader_node_72_75_characters : assertHeader_node_72_75.toList = assertHeader_node_72_75_chars := by
  unfold assertHeader_node_72_75 assertHeader_node_72_75_chars
  rw [String.toList_append, assertHeader_chunk_chars72, assertHeader_node_73_75_characters]
def assertHeader_node_72_75_parts : List (List Char) := assertHeader_parts_leaf72 ++ assertHeader_node_73_75_parts
theorem assertHeader_node_72_75_parts_literal : assertHeader_node_72_75_parts = [assertHeader_chunk72, assertHeader_chunk73, assertHeader_chunk74] := by
  unfold assertHeader_node_72_75_parts
  rw [assertHeader_node_73_75_parts_literal]
  rfl
theorem assertHeader_node_72_75_parts_flatten : assertHeader_node_72_75_chars = assertHeader_node_72_75_parts.flatten := by
  unfold assertHeader_node_72_75_chars assertHeader_node_72_75_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf72_flatten, ← assertHeader_node_73_75_parts_flatten]
def assertHeader_node_70_75 : String := assertHeader_node_70_72 ++ assertHeader_node_72_75
def assertHeader_node_70_75_chars : List Char := assertHeader_node_70_72_chars ++ assertHeader_node_72_75_chars
theorem assertHeader_node_70_75_literal : assertHeader_node_70_75 = " IS' basis, WITHOUT WARRANTY OF ANY KIND" := by
  unfold assertHeader_node_70_75
  rw [assertHeader_node_70_72_literal]
  rw [assertHeader_node_72_75_literal]
  cbv
theorem assertHeader_node_70_75_characters : assertHeader_node_70_75.toList = assertHeader_node_70_75_chars := by
  unfold assertHeader_node_70_75 assertHeader_node_70_75_chars
  rw [String.toList_append, assertHeader_node_70_72_characters, assertHeader_node_72_75_characters]
def assertHeader_node_70_75_parts : List (List Char) := assertHeader_node_70_72_parts ++ assertHeader_node_72_75_parts
theorem assertHeader_node_70_75_parts_literal : assertHeader_node_70_75_parts = [assertHeader_chunk70, assertHeader_chunk71, assertHeader_chunk72, assertHeader_chunk73, assertHeader_chunk74] := by
  unfold assertHeader_node_70_75_parts
  rw [assertHeader_node_70_72_parts_literal]
  rw [assertHeader_node_72_75_parts_literal]
  rfl
theorem assertHeader_node_70_75_parts_flatten : assertHeader_node_70_75_chars = assertHeader_node_70_75_parts.flatten := by
  unfold assertHeader_node_70_75_chars assertHeader_node_70_75_parts
  rw [List.flatten_append, ← assertHeader_node_70_72_parts_flatten, ← assertHeader_node_72_75_parts_flatten]
def assertHeader_node_65_75 : String := assertHeader_node_65_70 ++ assertHeader_node_70_75
def assertHeader_node_65_75_chars : List Char := assertHeader_node_65_70_chars ++ assertHeader_node_70_75_chars
theorem assertHeader_node_65_75_literal : assertHeader_node_65_75 = "the License are\n * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND" := by
  unfold assertHeader_node_65_75
  rw [assertHeader_node_65_70_literal]
  rw [assertHeader_node_70_75_literal]
  cbv
theorem assertHeader_node_65_75_characters : assertHeader_node_65_75.toList = assertHeader_node_65_75_chars := by
  unfold assertHeader_node_65_75 assertHeader_node_65_75_chars
  rw [String.toList_append, assertHeader_node_65_70_characters, assertHeader_node_70_75_characters]
def assertHeader_node_65_75_parts : List (List Char) := assertHeader_node_65_70_parts ++ assertHeader_node_70_75_parts
theorem assertHeader_node_65_75_parts_literal : assertHeader_node_65_75_parts = [assertHeader_chunk65, assertHeader_chunk66, assertHeader_chunk67, assertHeader_chunk68, assertHeader_chunk69, assertHeader_chunk70, assertHeader_chunk71, assertHeader_chunk72, assertHeader_chunk73, assertHeader_chunk74] := by
  unfold assertHeader_node_65_75_parts
  rw [assertHeader_node_65_70_parts_literal]
  rw [assertHeader_node_70_75_parts_literal]
  rfl
theorem assertHeader_node_65_75_parts_flatten : assertHeader_node_65_75_chars = assertHeader_node_65_75_parts.flatten := by
  unfold assertHeader_node_65_75_chars assertHeader_node_65_75_parts
  rw [List.flatten_append, ← assertHeader_node_65_70_parts_flatten, ← assertHeader_node_70_75_parts_flatten]
def assertHeader_node_56_75 : String := assertHeader_node_56_65 ++ assertHeader_node_65_75
def assertHeader_node_56_75_chars : List Char := assertHeader_node_56_65_chars ++ assertHeader_node_65_75_chars
theorem assertHeader_node_56_75_literal : assertHeader_node_56_75 = "his\n * file.\n *\n * The Original Code and all software distributed under the License are\n * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND" := by
  unfold assertHeader_node_56_75
  rw [assertHeader_node_56_65_literal]
  rw [assertHeader_node_65_75_literal]
  cbv
theorem assertHeader_node_56_75_characters : assertHeader_node_56_75.toList = assertHeader_node_56_75_chars := by
  unfold assertHeader_node_56_75 assertHeader_node_56_75_chars
  rw [String.toList_append, assertHeader_node_56_65_characters, assertHeader_node_65_75_characters]
def assertHeader_node_56_75_parts : List (List Char) := assertHeader_node_56_65_parts ++ assertHeader_node_65_75_parts
theorem assertHeader_node_56_75_parts_literal : assertHeader_node_56_75_parts = [assertHeader_chunk56, assertHeader_chunk57, assertHeader_chunk58, assertHeader_chunk59, assertHeader_chunk60, assertHeader_chunk61, assertHeader_chunk62, assertHeader_chunk63, assertHeader_chunk64, assertHeader_chunk65, assertHeader_chunk66, assertHeader_chunk67, assertHeader_chunk68, assertHeader_chunk69, assertHeader_chunk70, assertHeader_chunk71, assertHeader_chunk72, assertHeader_chunk73, assertHeader_chunk74] := by
  unfold assertHeader_node_56_75_parts
  rw [assertHeader_node_56_65_parts_literal]
  rw [assertHeader_node_65_75_parts_literal]
  rfl
theorem assertHeader_node_56_75_parts_flatten : assertHeader_node_56_75_chars = assertHeader_node_56_75_parts.flatten := by
  unfold assertHeader_node_56_75_chars assertHeader_node_56_75_parts
  rw [List.flatten_append, ← assertHeader_node_56_65_parts_flatten, ← assertHeader_node_65_75_parts_flatten]
def assertHeader_node_37_75 : String := assertHeader_node_37_56 ++ assertHeader_node_56_75
def assertHeader_node_37_75_chars : List Char := assertHeader_node_37_56_chars ++ assertHeader_node_56_75_chars
theorem assertHeader_node_37_75_literal : assertHeader_node_37_75 = "ile except in\n * compliance with the License. Please obtain a copy of the License at\n * http://www.opensource.apple.com/apsl/ and read it before using this\n * file.\n *\n * The Original Code and all software distributed under the License are\n * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND" := by
  unfold assertHeader_node_37_75
  rw [assertHeader_node_37_56_literal]
  rw [assertHeader_node_56_75_literal]
  cbv
theorem assertHeader_node_37_75_characters : assertHeader_node_37_75.toList = assertHeader_node_37_75_chars := by
  unfold assertHeader_node_37_75 assertHeader_node_37_75_chars
  rw [String.toList_append, assertHeader_node_37_56_characters, assertHeader_node_56_75_characters]
def assertHeader_node_37_75_parts : List (List Char) := assertHeader_node_37_56_parts ++ assertHeader_node_56_75_parts
theorem assertHeader_node_37_75_parts_literal : assertHeader_node_37_75_parts = [assertHeader_chunk37, assertHeader_chunk38, assertHeader_chunk39, assertHeader_chunk40, assertHeader_chunk41, assertHeader_chunk42, assertHeader_chunk43, assertHeader_chunk44, assertHeader_chunk45, assertHeader_chunk46, assertHeader_chunk47, assertHeader_chunk48, assertHeader_chunk49, assertHeader_chunk50, assertHeader_chunk51, assertHeader_chunk52, assertHeader_chunk53, assertHeader_chunk54, assertHeader_chunk55, assertHeader_chunk56, assertHeader_chunk57, assertHeader_chunk58, assertHeader_chunk59, assertHeader_chunk60, assertHeader_chunk61, assertHeader_chunk62, assertHeader_chunk63, assertHeader_chunk64, assertHeader_chunk65, assertHeader_chunk66, assertHeader_chunk67, assertHeader_chunk68, assertHeader_chunk69, assertHeader_chunk70, assertHeader_chunk71, assertHeader_chunk72, assertHeader_chunk73, assertHeader_chunk74] := by
  unfold assertHeader_node_37_75_parts
  rw [assertHeader_node_37_56_parts_literal]
  rw [assertHeader_node_56_75_parts_literal]
  rfl
theorem assertHeader_node_37_75_parts_flatten : assertHeader_node_37_75_chars = assertHeader_node_37_75_parts.flatten := by
  unfold assertHeader_node_37_75_chars assertHeader_node_37_75_parts
  rw [List.flatten_append, ← assertHeader_node_37_56_parts_flatten, ← assertHeader_node_56_75_parts_flatten]
def assertHeader_node_0_75 : String := assertHeader_node_0_37 ++ assertHeader_node_37_75
def assertHeader_node_0_75_chars : List Char := assertHeader_node_0_37_chars ++ assertHeader_node_37_75_chars
theorem assertHeader_node_0_75_literal : assertHeader_node_0_75 = "/*\n * Copyright (c) 2023 Apple Inc. All rights reserved.\n *\n * @APPLE_LICENSE_HEADER_START@\n *\n * This file contains Original Code and/or Modifications of Original Code\n * as defined in and that are subject to the Apple Public Source License\n * Version 2.0 (the 'License'). You may not use this file except in\n * compliance with the License. Please obtain a copy of the License at\n * http://www.opensource.apple.com/apsl/ and read it before using this\n * file.\n *\n * The Original Code and all software distributed under the License are\n * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND" := by
  unfold assertHeader_node_0_75
  rw [assertHeader_node_0_37_literal]
  rw [assertHeader_node_37_75_literal]
  cbv
theorem assertHeader_node_0_75_characters : assertHeader_node_0_75.toList = assertHeader_node_0_75_chars := by
  unfold assertHeader_node_0_75 assertHeader_node_0_75_chars
  rw [String.toList_append, assertHeader_node_0_37_characters, assertHeader_node_37_75_characters]
def assertHeader_node_0_75_parts : List (List Char) := assertHeader_node_0_37_parts ++ assertHeader_node_37_75_parts
theorem assertHeader_node_0_75_parts_literal : assertHeader_node_0_75_parts = [assertHeader_chunk0, assertHeader_chunk1, assertHeader_chunk2, assertHeader_chunk3, assertHeader_chunk4, assertHeader_chunk5, assertHeader_chunk6, assertHeader_chunk7, assertHeader_chunk8, assertHeader_chunk9, assertHeader_chunk10, assertHeader_chunk11, assertHeader_chunk12, assertHeader_chunk13, assertHeader_chunk14, assertHeader_chunk15, assertHeader_chunk16, assertHeader_chunk17, assertHeader_chunk18, assertHeader_chunk19, assertHeader_chunk20, assertHeader_chunk21, assertHeader_chunk22, assertHeader_chunk23, assertHeader_chunk24, assertHeader_chunk25, assertHeader_chunk26, assertHeader_chunk27, assertHeader_chunk28, assertHeader_chunk29, assertHeader_chunk30, assertHeader_chunk31, assertHeader_chunk32, assertHeader_chunk33, assertHeader_chunk34, assertHeader_chunk35, assertHeader_chunk36, assertHeader_chunk37, assertHeader_chunk38, assertHeader_chunk39, assertHeader_chunk40, assertHeader_chunk41, assertHeader_chunk42, assertHeader_chunk43, assertHeader_chunk44, assertHeader_chunk45, assertHeader_chunk46, assertHeader_chunk47, assertHeader_chunk48, assertHeader_chunk49, assertHeader_chunk50, assertHeader_chunk51, assertHeader_chunk52, assertHeader_chunk53, assertHeader_chunk54, assertHeader_chunk55, assertHeader_chunk56, assertHeader_chunk57, assertHeader_chunk58, assertHeader_chunk59, assertHeader_chunk60, assertHeader_chunk61, assertHeader_chunk62, assertHeader_chunk63, assertHeader_chunk64, assertHeader_chunk65, assertHeader_chunk66, assertHeader_chunk67, assertHeader_chunk68, assertHeader_chunk69, assertHeader_chunk70, assertHeader_chunk71, assertHeader_chunk72, assertHeader_chunk73, assertHeader_chunk74] := by
  unfold assertHeader_node_0_75_parts
  rw [assertHeader_node_0_37_parts_literal]
  rw [assertHeader_node_37_75_parts_literal]
  rfl
theorem assertHeader_node_0_75_parts_flatten : assertHeader_node_0_75_chars = assertHeader_node_0_75_parts.flatten := by
  unfold assertHeader_node_0_75_chars assertHeader_node_0_75_parts
  rw [List.flatten_append, ← assertHeader_node_0_37_parts_flatten, ← assertHeader_node_37_75_parts_flatten]
def assertHeader_parts_leaf75 : List (List Char) := [assertHeader_chunk75]
theorem assertHeader_parts_leaf75_flatten : assertHeader_chunk75 = assertHeader_parts_leaf75.flatten := by
  simp only [assertHeader_parts_leaf75, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf76 : List (List Char) := [assertHeader_chunk76]
theorem assertHeader_parts_leaf76_flatten : assertHeader_chunk76 = assertHeader_parts_leaf76.flatten := by
  simp only [assertHeader_parts_leaf76, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_75_77 : String := assertHeader_string_leaf75 ++ assertHeader_string_leaf76
def assertHeader_node_75_77_chars : List Char := assertHeader_chunk75 ++ assertHeader_chunk76
theorem assertHeader_node_75_77_literal : assertHeader_node_75_77 = ", EITHER\n * EXPR" := by
  unfold assertHeader_node_75_77
  cbv
theorem assertHeader_node_75_77_characters : assertHeader_node_75_77.toList = assertHeader_node_75_77_chars := by
  unfold assertHeader_node_75_77 assertHeader_node_75_77_chars
  rw [String.toList_append, assertHeader_chunk_chars75, assertHeader_chunk_chars76]
def assertHeader_node_75_77_parts : List (List Char) := assertHeader_parts_leaf75 ++ assertHeader_parts_leaf76
theorem assertHeader_node_75_77_parts_literal : assertHeader_node_75_77_parts = [assertHeader_chunk75, assertHeader_chunk76] := by
  unfold assertHeader_node_75_77_parts
  rfl
theorem assertHeader_node_75_77_parts_flatten : assertHeader_node_75_77_chars = assertHeader_node_75_77_parts.flatten := by
  unfold assertHeader_node_75_77_chars assertHeader_node_75_77_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf75_flatten, ← assertHeader_parts_leaf76_flatten]
def assertHeader_parts_leaf77 : List (List Char) := [assertHeader_chunk77]
theorem assertHeader_parts_leaf77_flatten : assertHeader_chunk77 = assertHeader_parts_leaf77.flatten := by
  simp only [assertHeader_parts_leaf77, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf78 : List (List Char) := [assertHeader_chunk78]
theorem assertHeader_parts_leaf78_flatten : assertHeader_chunk78 = assertHeader_parts_leaf78.flatten := by
  simp only [assertHeader_parts_leaf78, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_77_79 : String := assertHeader_string_leaf77 ++ assertHeader_string_leaf78
def assertHeader_node_77_79_chars : List Char := assertHeader_chunk77 ++ assertHeader_chunk78
theorem assertHeader_node_77_79_literal : assertHeader_node_77_79 = "ESS OR IMPLIED, " := by
  unfold assertHeader_node_77_79
  cbv
theorem assertHeader_node_77_79_characters : assertHeader_node_77_79.toList = assertHeader_node_77_79_chars := by
  unfold assertHeader_node_77_79 assertHeader_node_77_79_chars
  rw [String.toList_append, assertHeader_chunk_chars77, assertHeader_chunk_chars78]
def assertHeader_node_77_79_parts : List (List Char) := assertHeader_parts_leaf77 ++ assertHeader_parts_leaf78
theorem assertHeader_node_77_79_parts_literal : assertHeader_node_77_79_parts = [assertHeader_chunk77, assertHeader_chunk78] := by
  unfold assertHeader_node_77_79_parts
  rfl
theorem assertHeader_node_77_79_parts_flatten : assertHeader_node_77_79_chars = assertHeader_node_77_79_parts.flatten := by
  unfold assertHeader_node_77_79_chars assertHeader_node_77_79_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf77_flatten, ← assertHeader_parts_leaf78_flatten]
def assertHeader_node_75_79 : String := assertHeader_node_75_77 ++ assertHeader_node_77_79
def assertHeader_node_75_79_chars : List Char := assertHeader_node_75_77_chars ++ assertHeader_node_77_79_chars
theorem assertHeader_node_75_79_literal : assertHeader_node_75_79 = ", EITHER\n * EXPRESS OR IMPLIED, " := by
  unfold assertHeader_node_75_79
  rw [assertHeader_node_75_77_literal]
  rw [assertHeader_node_77_79_literal]
  cbv
theorem assertHeader_node_75_79_characters : assertHeader_node_75_79.toList = assertHeader_node_75_79_chars := by
  unfold assertHeader_node_75_79 assertHeader_node_75_79_chars
  rw [String.toList_append, assertHeader_node_75_77_characters, assertHeader_node_77_79_characters]
def assertHeader_node_75_79_parts : List (List Char) := assertHeader_node_75_77_parts ++ assertHeader_node_77_79_parts
theorem assertHeader_node_75_79_parts_literal : assertHeader_node_75_79_parts = [assertHeader_chunk75, assertHeader_chunk76, assertHeader_chunk77, assertHeader_chunk78] := by
  unfold assertHeader_node_75_79_parts
  rw [assertHeader_node_75_77_parts_literal]
  rw [assertHeader_node_77_79_parts_literal]
  rfl
theorem assertHeader_node_75_79_parts_flatten : assertHeader_node_75_79_chars = assertHeader_node_75_79_parts.flatten := by
  unfold assertHeader_node_75_79_chars assertHeader_node_75_79_parts
  rw [List.flatten_append, ← assertHeader_node_75_77_parts_flatten, ← assertHeader_node_77_79_parts_flatten]
def assertHeader_parts_leaf79 : List (List Char) := [assertHeader_chunk79]
theorem assertHeader_parts_leaf79_flatten : assertHeader_chunk79 = assertHeader_parts_leaf79.flatten := by
  simp only [assertHeader_parts_leaf79, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf80 : List (List Char) := [assertHeader_chunk80]
theorem assertHeader_parts_leaf80_flatten : assertHeader_chunk80 = assertHeader_parts_leaf80.flatten := by
  simp only [assertHeader_parts_leaf80, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_79_81 : String := assertHeader_string_leaf79 ++ assertHeader_string_leaf80
def assertHeader_node_79_81_chars : List Char := assertHeader_chunk79 ++ assertHeader_chunk80
theorem assertHeader_node_79_81_literal : assertHeader_node_79_81 = "AND APPLE HEREBY" := by
  unfold assertHeader_node_79_81
  cbv
theorem assertHeader_node_79_81_characters : assertHeader_node_79_81.toList = assertHeader_node_79_81_chars := by
  unfold assertHeader_node_79_81 assertHeader_node_79_81_chars
  rw [String.toList_append, assertHeader_chunk_chars79, assertHeader_chunk_chars80]
def assertHeader_node_79_81_parts : List (List Char) := assertHeader_parts_leaf79 ++ assertHeader_parts_leaf80
theorem assertHeader_node_79_81_parts_literal : assertHeader_node_79_81_parts = [assertHeader_chunk79, assertHeader_chunk80] := by
  unfold assertHeader_node_79_81_parts
  rfl
theorem assertHeader_node_79_81_parts_flatten : assertHeader_node_79_81_chars = assertHeader_node_79_81_parts.flatten := by
  unfold assertHeader_node_79_81_chars assertHeader_node_79_81_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf79_flatten, ← assertHeader_parts_leaf80_flatten]
def assertHeader_parts_leaf81 : List (List Char) := [assertHeader_chunk81]
theorem assertHeader_parts_leaf81_flatten : assertHeader_chunk81 = assertHeader_parts_leaf81.flatten := by
  simp only [assertHeader_parts_leaf81, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf82 : List (List Char) := [assertHeader_chunk82]
theorem assertHeader_parts_leaf82_flatten : assertHeader_chunk82 = assertHeader_parts_leaf82.flatten := by
  simp only [assertHeader_parts_leaf82, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf83 : List (List Char) := [assertHeader_chunk83]
theorem assertHeader_parts_leaf83_flatten : assertHeader_chunk83 = assertHeader_parts_leaf83.flatten := by
  simp only [assertHeader_parts_leaf83, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_82_84 : String := assertHeader_string_leaf82 ++ assertHeader_string_leaf83
def assertHeader_node_82_84_chars : List Char := assertHeader_chunk82 ++ assertHeader_chunk83
theorem assertHeader_node_82_84_literal : assertHeader_node_82_84 = "MS ALL SUCH WARR" := by
  unfold assertHeader_node_82_84
  cbv
theorem assertHeader_node_82_84_characters : assertHeader_node_82_84.toList = assertHeader_node_82_84_chars := by
  unfold assertHeader_node_82_84 assertHeader_node_82_84_chars
  rw [String.toList_append, assertHeader_chunk_chars82, assertHeader_chunk_chars83]
def assertHeader_node_82_84_parts : List (List Char) := assertHeader_parts_leaf82 ++ assertHeader_parts_leaf83
theorem assertHeader_node_82_84_parts_literal : assertHeader_node_82_84_parts = [assertHeader_chunk82, assertHeader_chunk83] := by
  unfold assertHeader_node_82_84_parts
  rfl
theorem assertHeader_node_82_84_parts_flatten : assertHeader_node_82_84_chars = assertHeader_node_82_84_parts.flatten := by
  unfold assertHeader_node_82_84_chars assertHeader_node_82_84_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf82_flatten, ← assertHeader_parts_leaf83_flatten]
def assertHeader_node_81_84 : String := assertHeader_string_leaf81 ++ assertHeader_node_82_84
def assertHeader_node_81_84_chars : List Char := assertHeader_chunk81 ++ assertHeader_node_82_84_chars
theorem assertHeader_node_81_84_literal : assertHeader_node_81_84 = " DISCLAIMS ALL SUCH WARR" := by
  unfold assertHeader_node_81_84
  rw [assertHeader_node_82_84_literal]
  cbv
theorem assertHeader_node_81_84_characters : assertHeader_node_81_84.toList = assertHeader_node_81_84_chars := by
  unfold assertHeader_node_81_84 assertHeader_node_81_84_chars
  rw [String.toList_append, assertHeader_chunk_chars81, assertHeader_node_82_84_characters]
def assertHeader_node_81_84_parts : List (List Char) := assertHeader_parts_leaf81 ++ assertHeader_node_82_84_parts
theorem assertHeader_node_81_84_parts_literal : assertHeader_node_81_84_parts = [assertHeader_chunk81, assertHeader_chunk82, assertHeader_chunk83] := by
  unfold assertHeader_node_81_84_parts
  rw [assertHeader_node_82_84_parts_literal]
  rfl
theorem assertHeader_node_81_84_parts_flatten : assertHeader_node_81_84_chars = assertHeader_node_81_84_parts.flatten := by
  unfold assertHeader_node_81_84_chars assertHeader_node_81_84_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf81_flatten, ← assertHeader_node_82_84_parts_flatten]
def assertHeader_node_79_84 : String := assertHeader_node_79_81 ++ assertHeader_node_81_84
def assertHeader_node_79_84_chars : List Char := assertHeader_node_79_81_chars ++ assertHeader_node_81_84_chars
theorem assertHeader_node_79_84_literal : assertHeader_node_79_84 = "AND APPLE HEREBY DISCLAIMS ALL SUCH WARR" := by
  unfold assertHeader_node_79_84
  rw [assertHeader_node_79_81_literal]
  rw [assertHeader_node_81_84_literal]
  cbv
theorem assertHeader_node_79_84_characters : assertHeader_node_79_84.toList = assertHeader_node_79_84_chars := by
  unfold assertHeader_node_79_84 assertHeader_node_79_84_chars
  rw [String.toList_append, assertHeader_node_79_81_characters, assertHeader_node_81_84_characters]
def assertHeader_node_79_84_parts : List (List Char) := assertHeader_node_79_81_parts ++ assertHeader_node_81_84_parts
theorem assertHeader_node_79_84_parts_literal : assertHeader_node_79_84_parts = [assertHeader_chunk79, assertHeader_chunk80, assertHeader_chunk81, assertHeader_chunk82, assertHeader_chunk83] := by
  unfold assertHeader_node_79_84_parts
  rw [assertHeader_node_79_81_parts_literal]
  rw [assertHeader_node_81_84_parts_literal]
  rfl
theorem assertHeader_node_79_84_parts_flatten : assertHeader_node_79_84_chars = assertHeader_node_79_84_parts.flatten := by
  unfold assertHeader_node_79_84_chars assertHeader_node_79_84_parts
  rw [List.flatten_append, ← assertHeader_node_79_81_parts_flatten, ← assertHeader_node_81_84_parts_flatten]
def assertHeader_node_75_84 : String := assertHeader_node_75_79 ++ assertHeader_node_79_84
def assertHeader_node_75_84_chars : List Char := assertHeader_node_75_79_chars ++ assertHeader_node_79_84_chars
theorem assertHeader_node_75_84_literal : assertHeader_node_75_84 = ", EITHER\n * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARR" := by
  unfold assertHeader_node_75_84
  rw [assertHeader_node_75_79_literal]
  rw [assertHeader_node_79_84_literal]
  cbv
theorem assertHeader_node_75_84_characters : assertHeader_node_75_84.toList = assertHeader_node_75_84_chars := by
  unfold assertHeader_node_75_84 assertHeader_node_75_84_chars
  rw [String.toList_append, assertHeader_node_75_79_characters, assertHeader_node_79_84_characters]
def assertHeader_node_75_84_parts : List (List Char) := assertHeader_node_75_79_parts ++ assertHeader_node_79_84_parts
theorem assertHeader_node_75_84_parts_literal : assertHeader_node_75_84_parts = [assertHeader_chunk75, assertHeader_chunk76, assertHeader_chunk77, assertHeader_chunk78, assertHeader_chunk79, assertHeader_chunk80, assertHeader_chunk81, assertHeader_chunk82, assertHeader_chunk83] := by
  unfold assertHeader_node_75_84_parts
  rw [assertHeader_node_75_79_parts_literal]
  rw [assertHeader_node_79_84_parts_literal]
  rfl
theorem assertHeader_node_75_84_parts_flatten : assertHeader_node_75_84_chars = assertHeader_node_75_84_parts.flatten := by
  unfold assertHeader_node_75_84_chars assertHeader_node_75_84_parts
  rw [List.flatten_append, ← assertHeader_node_75_79_parts_flatten, ← assertHeader_node_79_84_parts_flatten]
def assertHeader_parts_leaf84 : List (List Char) := [assertHeader_chunk84]
theorem assertHeader_parts_leaf84_flatten : assertHeader_chunk84 = assertHeader_parts_leaf84.flatten := by
  simp only [assertHeader_parts_leaf84, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf85 : List (List Char) := [assertHeader_chunk85]
theorem assertHeader_parts_leaf85_flatten : assertHeader_chunk85 = assertHeader_parts_leaf85.flatten := by
  simp only [assertHeader_parts_leaf85, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_84_86 : String := assertHeader_string_leaf84 ++ assertHeader_string_leaf85
def assertHeader_node_84_86_chars : List Char := assertHeader_chunk84 ++ assertHeader_chunk85
theorem assertHeader_node_84_86_literal : assertHeader_node_84_86 = "ANTIES,\n * INCLU" := by
  unfold assertHeader_node_84_86
  cbv
theorem assertHeader_node_84_86_characters : assertHeader_node_84_86.toList = assertHeader_node_84_86_chars := by
  unfold assertHeader_node_84_86 assertHeader_node_84_86_chars
  rw [String.toList_append, assertHeader_chunk_chars84, assertHeader_chunk_chars85]
def assertHeader_node_84_86_parts : List (List Char) := assertHeader_parts_leaf84 ++ assertHeader_parts_leaf85
theorem assertHeader_node_84_86_parts_literal : assertHeader_node_84_86_parts = [assertHeader_chunk84, assertHeader_chunk85] := by
  unfold assertHeader_node_84_86_parts
  rfl
theorem assertHeader_node_84_86_parts_flatten : assertHeader_node_84_86_chars = assertHeader_node_84_86_parts.flatten := by
  unfold assertHeader_node_84_86_chars assertHeader_node_84_86_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf84_flatten, ← assertHeader_parts_leaf85_flatten]
def assertHeader_parts_leaf86 : List (List Char) := [assertHeader_chunk86]
theorem assertHeader_parts_leaf86_flatten : assertHeader_chunk86 = assertHeader_parts_leaf86.flatten := by
  simp only [assertHeader_parts_leaf86, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf87 : List (List Char) := [assertHeader_chunk87]
theorem assertHeader_parts_leaf87_flatten : assertHeader_chunk87 = assertHeader_parts_leaf87.flatten := by
  simp only [assertHeader_parts_leaf87, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf88 : List (List Char) := [assertHeader_chunk88]
theorem assertHeader_parts_leaf88_flatten : assertHeader_chunk88 = assertHeader_parts_leaf88.flatten := by
  simp only [assertHeader_parts_leaf88, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_87_89 : String := assertHeader_string_leaf87 ++ assertHeader_string_leaf88
def assertHeader_node_87_89_chars : List Char := assertHeader_chunk87 ++ assertHeader_chunk88
theorem assertHeader_node_87_89_literal : assertHeader_node_87_89 = "HOUT LIMITATION," := by
  unfold assertHeader_node_87_89
  cbv
theorem assertHeader_node_87_89_characters : assertHeader_node_87_89.toList = assertHeader_node_87_89_chars := by
  unfold assertHeader_node_87_89 assertHeader_node_87_89_chars
  rw [String.toList_append, assertHeader_chunk_chars87, assertHeader_chunk_chars88]
def assertHeader_node_87_89_parts : List (List Char) := assertHeader_parts_leaf87 ++ assertHeader_parts_leaf88
theorem assertHeader_node_87_89_parts_literal : assertHeader_node_87_89_parts = [assertHeader_chunk87, assertHeader_chunk88] := by
  unfold assertHeader_node_87_89_parts
  rfl
theorem assertHeader_node_87_89_parts_flatten : assertHeader_node_87_89_chars = assertHeader_node_87_89_parts.flatten := by
  unfold assertHeader_node_87_89_chars assertHeader_node_87_89_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf87_flatten, ← assertHeader_parts_leaf88_flatten]
def assertHeader_node_86_89 : String := assertHeader_string_leaf86 ++ assertHeader_node_87_89
def assertHeader_node_86_89_chars : List Char := assertHeader_chunk86 ++ assertHeader_node_87_89_chars
theorem assertHeader_node_86_89_literal : assertHeader_node_86_89 = "DING WITHOUT LIMITATION," := by
  unfold assertHeader_node_86_89
  rw [assertHeader_node_87_89_literal]
  cbv
theorem assertHeader_node_86_89_characters : assertHeader_node_86_89.toList = assertHeader_node_86_89_chars := by
  unfold assertHeader_node_86_89 assertHeader_node_86_89_chars
  rw [String.toList_append, assertHeader_chunk_chars86, assertHeader_node_87_89_characters]
def assertHeader_node_86_89_parts : List (List Char) := assertHeader_parts_leaf86 ++ assertHeader_node_87_89_parts
theorem assertHeader_node_86_89_parts_literal : assertHeader_node_86_89_parts = [assertHeader_chunk86, assertHeader_chunk87, assertHeader_chunk88] := by
  unfold assertHeader_node_86_89_parts
  rw [assertHeader_node_87_89_parts_literal]
  rfl
theorem assertHeader_node_86_89_parts_flatten : assertHeader_node_86_89_chars = assertHeader_node_86_89_parts.flatten := by
  unfold assertHeader_node_86_89_chars assertHeader_node_86_89_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf86_flatten, ← assertHeader_node_87_89_parts_flatten]
def assertHeader_node_84_89 : String := assertHeader_node_84_86 ++ assertHeader_node_86_89
def assertHeader_node_84_89_chars : List Char := assertHeader_node_84_86_chars ++ assertHeader_node_86_89_chars
theorem assertHeader_node_84_89_literal : assertHeader_node_84_89 = "ANTIES,\n * INCLUDING WITHOUT LIMITATION," := by
  unfold assertHeader_node_84_89
  rw [assertHeader_node_84_86_literal]
  rw [assertHeader_node_86_89_literal]
  cbv
theorem assertHeader_node_84_89_characters : assertHeader_node_84_89.toList = assertHeader_node_84_89_chars := by
  unfold assertHeader_node_84_89 assertHeader_node_84_89_chars
  rw [String.toList_append, assertHeader_node_84_86_characters, assertHeader_node_86_89_characters]
def assertHeader_node_84_89_parts : List (List Char) := assertHeader_node_84_86_parts ++ assertHeader_node_86_89_parts
theorem assertHeader_node_84_89_parts_literal : assertHeader_node_84_89_parts = [assertHeader_chunk84, assertHeader_chunk85, assertHeader_chunk86, assertHeader_chunk87, assertHeader_chunk88] := by
  unfold assertHeader_node_84_89_parts
  rw [assertHeader_node_84_86_parts_literal]
  rw [assertHeader_node_86_89_parts_literal]
  rfl
theorem assertHeader_node_84_89_parts_flatten : assertHeader_node_84_89_chars = assertHeader_node_84_89_parts.flatten := by
  unfold assertHeader_node_84_89_chars assertHeader_node_84_89_parts
  rw [List.flatten_append, ← assertHeader_node_84_86_parts_flatten, ← assertHeader_node_86_89_parts_flatten]
def assertHeader_parts_leaf89 : List (List Char) := [assertHeader_chunk89]
theorem assertHeader_parts_leaf89_flatten : assertHeader_chunk89 = assertHeader_parts_leaf89.flatten := by
  simp only [assertHeader_parts_leaf89, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf90 : List (List Char) := [assertHeader_chunk90]
theorem assertHeader_parts_leaf90_flatten : assertHeader_chunk90 = assertHeader_parts_leaf90.flatten := by
  simp only [assertHeader_parts_leaf90, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_89_91 : String := assertHeader_string_leaf89 ++ assertHeader_string_leaf90
def assertHeader_node_89_91_chars : List Char := assertHeader_chunk89 ++ assertHeader_chunk90
theorem assertHeader_node_89_91_literal : assertHeader_node_89_91 = " ANY WARRANTIES " := by
  unfold assertHeader_node_89_91
  cbv
theorem assertHeader_node_89_91_characters : assertHeader_node_89_91.toList = assertHeader_node_89_91_chars := by
  unfold assertHeader_node_89_91 assertHeader_node_89_91_chars
  rw [String.toList_append, assertHeader_chunk_chars89, assertHeader_chunk_chars90]
def assertHeader_node_89_91_parts : List (List Char) := assertHeader_parts_leaf89 ++ assertHeader_parts_leaf90
theorem assertHeader_node_89_91_parts_literal : assertHeader_node_89_91_parts = [assertHeader_chunk89, assertHeader_chunk90] := by
  unfold assertHeader_node_89_91_parts
  rfl
theorem assertHeader_node_89_91_parts_flatten : assertHeader_node_89_91_chars = assertHeader_node_89_91_parts.flatten := by
  unfold assertHeader_node_89_91_chars assertHeader_node_89_91_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf89_flatten, ← assertHeader_parts_leaf90_flatten]
def assertHeader_parts_leaf91 : List (List Char) := [assertHeader_chunk91]
theorem assertHeader_parts_leaf91_flatten : assertHeader_chunk91 = assertHeader_parts_leaf91.flatten := by
  simp only [assertHeader_parts_leaf91, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf92 : List (List Char) := [assertHeader_chunk92]
theorem assertHeader_parts_leaf92_flatten : assertHeader_chunk92 = assertHeader_parts_leaf92.flatten := by
  simp only [assertHeader_parts_leaf92, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf93 : List (List Char) := [assertHeader_chunk93]
theorem assertHeader_parts_leaf93_flatten : assertHeader_chunk93 = assertHeader_parts_leaf93.flatten := by
  simp only [assertHeader_parts_leaf93, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_92_94 : String := assertHeader_string_leaf92 ++ assertHeader_string_leaf93
def assertHeader_node_92_94_chars : List Char := assertHeader_chunk92 ++ assertHeader_chunk93
theorem assertHeader_node_92_94_literal : assertHeader_node_92_94 = "ANTABILITY,\n * F" := by
  unfold assertHeader_node_92_94
  cbv
theorem assertHeader_node_92_94_characters : assertHeader_node_92_94.toList = assertHeader_node_92_94_chars := by
  unfold assertHeader_node_92_94 assertHeader_node_92_94_chars
  rw [String.toList_append, assertHeader_chunk_chars92, assertHeader_chunk_chars93]
def assertHeader_node_92_94_parts : List (List Char) := assertHeader_parts_leaf92 ++ assertHeader_parts_leaf93
theorem assertHeader_node_92_94_parts_literal : assertHeader_node_92_94_parts = [assertHeader_chunk92, assertHeader_chunk93] := by
  unfold assertHeader_node_92_94_parts
  rfl
theorem assertHeader_node_92_94_parts_flatten : assertHeader_node_92_94_chars = assertHeader_node_92_94_parts.flatten := by
  unfold assertHeader_node_92_94_chars assertHeader_node_92_94_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf92_flatten, ← assertHeader_parts_leaf93_flatten]
def assertHeader_node_91_94 : String := assertHeader_string_leaf91 ++ assertHeader_node_92_94
def assertHeader_node_91_94_chars : List Char := assertHeader_chunk91 ++ assertHeader_node_92_94_chars
theorem assertHeader_node_91_94_literal : assertHeader_node_91_94 = "OF MERCHANTABILITY,\n * F" := by
  unfold assertHeader_node_91_94
  rw [assertHeader_node_92_94_literal]
  cbv
theorem assertHeader_node_91_94_characters : assertHeader_node_91_94.toList = assertHeader_node_91_94_chars := by
  unfold assertHeader_node_91_94 assertHeader_node_91_94_chars
  rw [String.toList_append, assertHeader_chunk_chars91, assertHeader_node_92_94_characters]
def assertHeader_node_91_94_parts : List (List Char) := assertHeader_parts_leaf91 ++ assertHeader_node_92_94_parts
theorem assertHeader_node_91_94_parts_literal : assertHeader_node_91_94_parts = [assertHeader_chunk91, assertHeader_chunk92, assertHeader_chunk93] := by
  unfold assertHeader_node_91_94_parts
  rw [assertHeader_node_92_94_parts_literal]
  rfl
theorem assertHeader_node_91_94_parts_flatten : assertHeader_node_91_94_chars = assertHeader_node_91_94_parts.flatten := by
  unfold assertHeader_node_91_94_chars assertHeader_node_91_94_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf91_flatten, ← assertHeader_node_92_94_parts_flatten]
def assertHeader_node_89_94 : String := assertHeader_node_89_91 ++ assertHeader_node_91_94
def assertHeader_node_89_94_chars : List Char := assertHeader_node_89_91_chars ++ assertHeader_node_91_94_chars
theorem assertHeader_node_89_94_literal : assertHeader_node_89_94 = " ANY WARRANTIES OF MERCHANTABILITY,\n * F" := by
  unfold assertHeader_node_89_94
  rw [assertHeader_node_89_91_literal]
  rw [assertHeader_node_91_94_literal]
  cbv
theorem assertHeader_node_89_94_characters : assertHeader_node_89_94.toList = assertHeader_node_89_94_chars := by
  unfold assertHeader_node_89_94 assertHeader_node_89_94_chars
  rw [String.toList_append, assertHeader_node_89_91_characters, assertHeader_node_91_94_characters]
def assertHeader_node_89_94_parts : List (List Char) := assertHeader_node_89_91_parts ++ assertHeader_node_91_94_parts
theorem assertHeader_node_89_94_parts_literal : assertHeader_node_89_94_parts = [assertHeader_chunk89, assertHeader_chunk90, assertHeader_chunk91, assertHeader_chunk92, assertHeader_chunk93] := by
  unfold assertHeader_node_89_94_parts
  rw [assertHeader_node_89_91_parts_literal]
  rw [assertHeader_node_91_94_parts_literal]
  rfl
theorem assertHeader_node_89_94_parts_flatten : assertHeader_node_89_94_chars = assertHeader_node_89_94_parts.flatten := by
  unfold assertHeader_node_89_94_chars assertHeader_node_89_94_parts
  rw [List.flatten_append, ← assertHeader_node_89_91_parts_flatten, ← assertHeader_node_91_94_parts_flatten]
def assertHeader_node_84_94 : String := assertHeader_node_84_89 ++ assertHeader_node_89_94
def assertHeader_node_84_94_chars : List Char := assertHeader_node_84_89_chars ++ assertHeader_node_89_94_chars
theorem assertHeader_node_84_94_literal : assertHeader_node_84_94 = "ANTIES,\n * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,\n * F" := by
  unfold assertHeader_node_84_94
  rw [assertHeader_node_84_89_literal]
  rw [assertHeader_node_89_94_literal]
  cbv
theorem assertHeader_node_84_94_characters : assertHeader_node_84_94.toList = assertHeader_node_84_94_chars := by
  unfold assertHeader_node_84_94 assertHeader_node_84_94_chars
  rw [String.toList_append, assertHeader_node_84_89_characters, assertHeader_node_89_94_characters]
def assertHeader_node_84_94_parts : List (List Char) := assertHeader_node_84_89_parts ++ assertHeader_node_89_94_parts
theorem assertHeader_node_84_94_parts_literal : assertHeader_node_84_94_parts = [assertHeader_chunk84, assertHeader_chunk85, assertHeader_chunk86, assertHeader_chunk87, assertHeader_chunk88, assertHeader_chunk89, assertHeader_chunk90, assertHeader_chunk91, assertHeader_chunk92, assertHeader_chunk93] := by
  unfold assertHeader_node_84_94_parts
  rw [assertHeader_node_84_89_parts_literal]
  rw [assertHeader_node_89_94_parts_literal]
  rfl
theorem assertHeader_node_84_94_parts_flatten : assertHeader_node_84_94_chars = assertHeader_node_84_94_parts.flatten := by
  unfold assertHeader_node_84_94_chars assertHeader_node_84_94_parts
  rw [List.flatten_append, ← assertHeader_node_84_89_parts_flatten, ← assertHeader_node_89_94_parts_flatten]
def assertHeader_node_75_94 : String := assertHeader_node_75_84 ++ assertHeader_node_84_94
def assertHeader_node_75_94_chars : List Char := assertHeader_node_75_84_chars ++ assertHeader_node_84_94_chars
theorem assertHeader_node_75_94_literal : assertHeader_node_75_94 = ", EITHER\n * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,\n * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,\n * F" := by
  unfold assertHeader_node_75_94
  rw [assertHeader_node_75_84_literal]
  rw [assertHeader_node_84_94_literal]
  cbv
theorem assertHeader_node_75_94_characters : assertHeader_node_75_94.toList = assertHeader_node_75_94_chars := by
  unfold assertHeader_node_75_94 assertHeader_node_75_94_chars
  rw [String.toList_append, assertHeader_node_75_84_characters, assertHeader_node_84_94_characters]
def assertHeader_node_75_94_parts : List (List Char) := assertHeader_node_75_84_parts ++ assertHeader_node_84_94_parts
theorem assertHeader_node_75_94_parts_literal : assertHeader_node_75_94_parts = [assertHeader_chunk75, assertHeader_chunk76, assertHeader_chunk77, assertHeader_chunk78, assertHeader_chunk79, assertHeader_chunk80, assertHeader_chunk81, assertHeader_chunk82, assertHeader_chunk83, assertHeader_chunk84, assertHeader_chunk85, assertHeader_chunk86, assertHeader_chunk87, assertHeader_chunk88, assertHeader_chunk89, assertHeader_chunk90, assertHeader_chunk91, assertHeader_chunk92, assertHeader_chunk93] := by
  unfold assertHeader_node_75_94_parts
  rw [assertHeader_node_75_84_parts_literal]
  rw [assertHeader_node_84_94_parts_literal]
  rfl
theorem assertHeader_node_75_94_parts_flatten : assertHeader_node_75_94_chars = assertHeader_node_75_94_parts.flatten := by
  unfold assertHeader_node_75_94_chars assertHeader_node_75_94_parts
  rw [List.flatten_append, ← assertHeader_node_75_84_parts_flatten, ← assertHeader_node_84_94_parts_flatten]
def assertHeader_parts_leaf94 : List (List Char) := [assertHeader_chunk94]
theorem assertHeader_parts_leaf94_flatten : assertHeader_chunk94 = assertHeader_parts_leaf94.flatten := by
  simp only [assertHeader_parts_leaf94, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf95 : List (List Char) := [assertHeader_chunk95]
theorem assertHeader_parts_leaf95_flatten : assertHeader_chunk95 = assertHeader_parts_leaf95.flatten := by
  simp only [assertHeader_parts_leaf95, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_94_96 : String := assertHeader_string_leaf94 ++ assertHeader_string_leaf95
def assertHeader_node_94_96_chars : List Char := assertHeader_chunk94 ++ assertHeader_chunk95
theorem assertHeader_node_94_96_literal : assertHeader_node_94_96 = "ITNESS FOR A PAR" := by
  unfold assertHeader_node_94_96
  cbv
theorem assertHeader_node_94_96_characters : assertHeader_node_94_96.toList = assertHeader_node_94_96_chars := by
  unfold assertHeader_node_94_96 assertHeader_node_94_96_chars
  rw [String.toList_append, assertHeader_chunk_chars94, assertHeader_chunk_chars95]
def assertHeader_node_94_96_parts : List (List Char) := assertHeader_parts_leaf94 ++ assertHeader_parts_leaf95
theorem assertHeader_node_94_96_parts_literal : assertHeader_node_94_96_parts = [assertHeader_chunk94, assertHeader_chunk95] := by
  unfold assertHeader_node_94_96_parts
  rfl
theorem assertHeader_node_94_96_parts_flatten : assertHeader_node_94_96_chars = assertHeader_node_94_96_parts.flatten := by
  unfold assertHeader_node_94_96_chars assertHeader_node_94_96_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf94_flatten, ← assertHeader_parts_leaf95_flatten]
def assertHeader_parts_leaf96 : List (List Char) := [assertHeader_chunk96]
theorem assertHeader_parts_leaf96_flatten : assertHeader_chunk96 = assertHeader_parts_leaf96.flatten := by
  simp only [assertHeader_parts_leaf96, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf97 : List (List Char) := [assertHeader_chunk97]
theorem assertHeader_parts_leaf97_flatten : assertHeader_chunk97 = assertHeader_parts_leaf97.flatten := by
  simp only [assertHeader_parts_leaf97, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_96_98 : String := assertHeader_string_leaf96 ++ assertHeader_string_leaf97
def assertHeader_node_96_98_chars : List Char := assertHeader_chunk96 ++ assertHeader_chunk97
theorem assertHeader_node_96_98_literal : assertHeader_node_96_98 = "TICULAR PURPOSE," := by
  unfold assertHeader_node_96_98
  cbv
theorem assertHeader_node_96_98_characters : assertHeader_node_96_98.toList = assertHeader_node_96_98_chars := by
  unfold assertHeader_node_96_98 assertHeader_node_96_98_chars
  rw [String.toList_append, assertHeader_chunk_chars96, assertHeader_chunk_chars97]
def assertHeader_node_96_98_parts : List (List Char) := assertHeader_parts_leaf96 ++ assertHeader_parts_leaf97
theorem assertHeader_node_96_98_parts_literal : assertHeader_node_96_98_parts = [assertHeader_chunk96, assertHeader_chunk97] := by
  unfold assertHeader_node_96_98_parts
  rfl
theorem assertHeader_node_96_98_parts_flatten : assertHeader_node_96_98_chars = assertHeader_node_96_98_parts.flatten := by
  unfold assertHeader_node_96_98_chars assertHeader_node_96_98_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf96_flatten, ← assertHeader_parts_leaf97_flatten]
def assertHeader_node_94_98 : String := assertHeader_node_94_96 ++ assertHeader_node_96_98
def assertHeader_node_94_98_chars : List Char := assertHeader_node_94_96_chars ++ assertHeader_node_96_98_chars
theorem assertHeader_node_94_98_literal : assertHeader_node_94_98 = "ITNESS FOR A PARTICULAR PURPOSE," := by
  unfold assertHeader_node_94_98
  rw [assertHeader_node_94_96_literal]
  rw [assertHeader_node_96_98_literal]
  cbv
theorem assertHeader_node_94_98_characters : assertHeader_node_94_98.toList = assertHeader_node_94_98_chars := by
  unfold assertHeader_node_94_98 assertHeader_node_94_98_chars
  rw [String.toList_append, assertHeader_node_94_96_characters, assertHeader_node_96_98_characters]
def assertHeader_node_94_98_parts : List (List Char) := assertHeader_node_94_96_parts ++ assertHeader_node_96_98_parts
theorem assertHeader_node_94_98_parts_literal : assertHeader_node_94_98_parts = [assertHeader_chunk94, assertHeader_chunk95, assertHeader_chunk96, assertHeader_chunk97] := by
  unfold assertHeader_node_94_98_parts
  rw [assertHeader_node_94_96_parts_literal]
  rw [assertHeader_node_96_98_parts_literal]
  rfl
theorem assertHeader_node_94_98_parts_flatten : assertHeader_node_94_98_chars = assertHeader_node_94_98_parts.flatten := by
  unfold assertHeader_node_94_98_chars assertHeader_node_94_98_parts
  rw [List.flatten_append, ← assertHeader_node_94_96_parts_flatten, ← assertHeader_node_96_98_parts_flatten]
def assertHeader_parts_leaf98 : List (List Char) := [assertHeader_chunk98]
theorem assertHeader_parts_leaf98_flatten : assertHeader_chunk98 = assertHeader_parts_leaf98.flatten := by
  simp only [assertHeader_parts_leaf98, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf99 : List (List Char) := [assertHeader_chunk99]
theorem assertHeader_parts_leaf99_flatten : assertHeader_chunk99 = assertHeader_parts_leaf99.flatten := by
  simp only [assertHeader_parts_leaf99, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_98_100 : String := assertHeader_string_leaf98 ++ assertHeader_string_leaf99
def assertHeader_node_98_100_chars : List Char := assertHeader_chunk98 ++ assertHeader_chunk99
theorem assertHeader_node_98_100_literal : assertHeader_node_98_100 = " QUIET ENJOYMENT" := by
  unfold assertHeader_node_98_100
  cbv
theorem assertHeader_node_98_100_characters : assertHeader_node_98_100.toList = assertHeader_node_98_100_chars := by
  unfold assertHeader_node_98_100 assertHeader_node_98_100_chars
  rw [String.toList_append, assertHeader_chunk_chars98, assertHeader_chunk_chars99]
def assertHeader_node_98_100_parts : List (List Char) := assertHeader_parts_leaf98 ++ assertHeader_parts_leaf99
theorem assertHeader_node_98_100_parts_literal : assertHeader_node_98_100_parts = [assertHeader_chunk98, assertHeader_chunk99] := by
  unfold assertHeader_node_98_100_parts
  rfl
theorem assertHeader_node_98_100_parts_flatten : assertHeader_node_98_100_chars = assertHeader_node_98_100_parts.flatten := by
  unfold assertHeader_node_98_100_chars assertHeader_node_98_100_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf98_flatten, ← assertHeader_parts_leaf99_flatten]
def assertHeader_parts_leaf100 : List (List Char) := [assertHeader_chunk100]
theorem assertHeader_parts_leaf100_flatten : assertHeader_chunk100 = assertHeader_parts_leaf100.flatten := by
  simp only [assertHeader_parts_leaf100, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf101 : List (List Char) := [assertHeader_chunk101]
theorem assertHeader_parts_leaf101_flatten : assertHeader_chunk101 = assertHeader_parts_leaf101.flatten := by
  simp only [assertHeader_parts_leaf101, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf102 : List (List Char) := [assertHeader_chunk102]
theorem assertHeader_parts_leaf102_flatten : assertHeader_chunk102 = assertHeader_parts_leaf102.flatten := by
  simp only [assertHeader_parts_leaf102, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_101_103 : String := assertHeader_string_leaf101 ++ assertHeader_string_leaf102
def assertHeader_node_101_103_chars : List Char := assertHeader_chunk101 ++ assertHeader_chunk102
theorem assertHeader_node_101_103_literal : assertHeader_node_101_103 = "INFRINGEMENT.\n *" := by
  unfold assertHeader_node_101_103
  cbv
theorem assertHeader_node_101_103_characters : assertHeader_node_101_103.toList = assertHeader_node_101_103_chars := by
  unfold assertHeader_node_101_103 assertHeader_node_101_103_chars
  rw [String.toList_append, assertHeader_chunk_chars101, assertHeader_chunk_chars102]
def assertHeader_node_101_103_parts : List (List Char) := assertHeader_parts_leaf101 ++ assertHeader_parts_leaf102
theorem assertHeader_node_101_103_parts_literal : assertHeader_node_101_103_parts = [assertHeader_chunk101, assertHeader_chunk102] := by
  unfold assertHeader_node_101_103_parts
  rfl
theorem assertHeader_node_101_103_parts_flatten : assertHeader_node_101_103_chars = assertHeader_node_101_103_parts.flatten := by
  unfold assertHeader_node_101_103_chars assertHeader_node_101_103_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf101_flatten, ← assertHeader_parts_leaf102_flatten]
def assertHeader_node_100_103 : String := assertHeader_string_leaf100 ++ assertHeader_node_101_103
def assertHeader_node_100_103_chars : List Char := assertHeader_chunk100 ++ assertHeader_node_101_103_chars
theorem assertHeader_node_100_103_literal : assertHeader_node_100_103 = " OR NON-INFRINGEMENT.\n *" := by
  unfold assertHeader_node_100_103
  rw [assertHeader_node_101_103_literal]
  cbv
theorem assertHeader_node_100_103_characters : assertHeader_node_100_103.toList = assertHeader_node_100_103_chars := by
  unfold assertHeader_node_100_103 assertHeader_node_100_103_chars
  rw [String.toList_append, assertHeader_chunk_chars100, assertHeader_node_101_103_characters]
def assertHeader_node_100_103_parts : List (List Char) := assertHeader_parts_leaf100 ++ assertHeader_node_101_103_parts
theorem assertHeader_node_100_103_parts_literal : assertHeader_node_100_103_parts = [assertHeader_chunk100, assertHeader_chunk101, assertHeader_chunk102] := by
  unfold assertHeader_node_100_103_parts
  rw [assertHeader_node_101_103_parts_literal]
  rfl
theorem assertHeader_node_100_103_parts_flatten : assertHeader_node_100_103_chars = assertHeader_node_100_103_parts.flatten := by
  unfold assertHeader_node_100_103_chars assertHeader_node_100_103_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf100_flatten, ← assertHeader_node_101_103_parts_flatten]
def assertHeader_node_98_103 : String := assertHeader_node_98_100 ++ assertHeader_node_100_103
def assertHeader_node_98_103_chars : List Char := assertHeader_node_98_100_chars ++ assertHeader_node_100_103_chars
theorem assertHeader_node_98_103_literal : assertHeader_node_98_103 = " QUIET ENJOYMENT OR NON-INFRINGEMENT.\n *" := by
  unfold assertHeader_node_98_103
  rw [assertHeader_node_98_100_literal]
  rw [assertHeader_node_100_103_literal]
  cbv
theorem assertHeader_node_98_103_characters : assertHeader_node_98_103.toList = assertHeader_node_98_103_chars := by
  unfold assertHeader_node_98_103 assertHeader_node_98_103_chars
  rw [String.toList_append, assertHeader_node_98_100_characters, assertHeader_node_100_103_characters]
def assertHeader_node_98_103_parts : List (List Char) := assertHeader_node_98_100_parts ++ assertHeader_node_100_103_parts
theorem assertHeader_node_98_103_parts_literal : assertHeader_node_98_103_parts = [assertHeader_chunk98, assertHeader_chunk99, assertHeader_chunk100, assertHeader_chunk101, assertHeader_chunk102] := by
  unfold assertHeader_node_98_103_parts
  rw [assertHeader_node_98_100_parts_literal]
  rw [assertHeader_node_100_103_parts_literal]
  rfl
theorem assertHeader_node_98_103_parts_flatten : assertHeader_node_98_103_chars = assertHeader_node_98_103_parts.flatten := by
  unfold assertHeader_node_98_103_chars assertHeader_node_98_103_parts
  rw [List.flatten_append, ← assertHeader_node_98_100_parts_flatten, ← assertHeader_node_100_103_parts_flatten]
def assertHeader_node_94_103 : String := assertHeader_node_94_98 ++ assertHeader_node_98_103
def assertHeader_node_94_103_chars : List Char := assertHeader_node_94_98_chars ++ assertHeader_node_98_103_chars
theorem assertHeader_node_94_103_literal : assertHeader_node_94_103 = "ITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.\n *" := by
  unfold assertHeader_node_94_103
  rw [assertHeader_node_94_98_literal]
  rw [assertHeader_node_98_103_literal]
  cbv
theorem assertHeader_node_94_103_characters : assertHeader_node_94_103.toList = assertHeader_node_94_103_chars := by
  unfold assertHeader_node_94_103 assertHeader_node_94_103_chars
  rw [String.toList_append, assertHeader_node_94_98_characters, assertHeader_node_98_103_characters]
def assertHeader_node_94_103_parts : List (List Char) := assertHeader_node_94_98_parts ++ assertHeader_node_98_103_parts
theorem assertHeader_node_94_103_parts_literal : assertHeader_node_94_103_parts = [assertHeader_chunk94, assertHeader_chunk95, assertHeader_chunk96, assertHeader_chunk97, assertHeader_chunk98, assertHeader_chunk99, assertHeader_chunk100, assertHeader_chunk101, assertHeader_chunk102] := by
  unfold assertHeader_node_94_103_parts
  rw [assertHeader_node_94_98_parts_literal]
  rw [assertHeader_node_98_103_parts_literal]
  rfl
theorem assertHeader_node_94_103_parts_flatten : assertHeader_node_94_103_chars = assertHeader_node_94_103_parts.flatten := by
  unfold assertHeader_node_94_103_chars assertHeader_node_94_103_parts
  rw [List.flatten_append, ← assertHeader_node_94_98_parts_flatten, ← assertHeader_node_98_103_parts_flatten]
def assertHeader_parts_leaf103 : List (List Char) := [assertHeader_chunk103]
theorem assertHeader_parts_leaf103_flatten : assertHeader_chunk103 = assertHeader_parts_leaf103.flatten := by
  simp only [assertHeader_parts_leaf103, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf104 : List (List Char) := [assertHeader_chunk104]
theorem assertHeader_parts_leaf104_flatten : assertHeader_chunk104 = assertHeader_parts_leaf104.flatten := by
  simp only [assertHeader_parts_leaf104, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_103_105 : String := assertHeader_string_leaf103 ++ assertHeader_string_leaf104
def assertHeader_node_103_105_chars : List Char := assertHeader_chunk103 ++ assertHeader_chunk104
theorem assertHeader_node_103_105_literal : assertHeader_node_103_105 = " Please see the " := by
  unfold assertHeader_node_103_105
  cbv
theorem assertHeader_node_103_105_characters : assertHeader_node_103_105.toList = assertHeader_node_103_105_chars := by
  unfold assertHeader_node_103_105 assertHeader_node_103_105_chars
  rw [String.toList_append, assertHeader_chunk_chars103, assertHeader_chunk_chars104]
def assertHeader_node_103_105_parts : List (List Char) := assertHeader_parts_leaf103 ++ assertHeader_parts_leaf104
theorem assertHeader_node_103_105_parts_literal : assertHeader_node_103_105_parts = [assertHeader_chunk103, assertHeader_chunk104] := by
  unfold assertHeader_node_103_105_parts
  rfl
theorem assertHeader_node_103_105_parts_flatten : assertHeader_node_103_105_chars = assertHeader_node_103_105_parts.flatten := by
  unfold assertHeader_node_103_105_chars assertHeader_node_103_105_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf103_flatten, ← assertHeader_parts_leaf104_flatten]
def assertHeader_parts_leaf105 : List (List Char) := [assertHeader_chunk105]
theorem assertHeader_parts_leaf105_flatten : assertHeader_chunk105 = assertHeader_parts_leaf105.flatten := by
  simp only [assertHeader_parts_leaf105, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf106 : List (List Char) := [assertHeader_chunk106]
theorem assertHeader_parts_leaf106_flatten : assertHeader_chunk106 = assertHeader_parts_leaf106.flatten := by
  simp only [assertHeader_parts_leaf106, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf107 : List (List Char) := [assertHeader_chunk107]
theorem assertHeader_parts_leaf107_flatten : assertHeader_chunk107 = assertHeader_parts_leaf107.flatten := by
  simp only [assertHeader_parts_leaf107, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_106_108 : String := assertHeader_string_leaf106 ++ assertHeader_string_leaf107
def assertHeader_node_106_108_chars : List Char := assertHeader_chunk106 ++ assertHeader_chunk107
theorem assertHeader_node_106_108_literal : assertHeader_node_106_108 = "for the specific" := by
  unfold assertHeader_node_106_108
  cbv
theorem assertHeader_node_106_108_characters : assertHeader_node_106_108.toList = assertHeader_node_106_108_chars := by
  unfold assertHeader_node_106_108 assertHeader_node_106_108_chars
  rw [String.toList_append, assertHeader_chunk_chars106, assertHeader_chunk_chars107]
def assertHeader_node_106_108_parts : List (List Char) := assertHeader_parts_leaf106 ++ assertHeader_parts_leaf107
theorem assertHeader_node_106_108_parts_literal : assertHeader_node_106_108_parts = [assertHeader_chunk106, assertHeader_chunk107] := by
  unfold assertHeader_node_106_108_parts
  rfl
theorem assertHeader_node_106_108_parts_flatten : assertHeader_node_106_108_chars = assertHeader_node_106_108_parts.flatten := by
  unfold assertHeader_node_106_108_chars assertHeader_node_106_108_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf106_flatten, ← assertHeader_parts_leaf107_flatten]
def assertHeader_node_105_108 : String := assertHeader_string_leaf105 ++ assertHeader_node_106_108
def assertHeader_node_105_108_chars : List Char := assertHeader_chunk105 ++ assertHeader_node_106_108_chars
theorem assertHeader_node_105_108_literal : assertHeader_node_105_108 = "License for the specific" := by
  unfold assertHeader_node_105_108
  rw [assertHeader_node_106_108_literal]
  cbv
theorem assertHeader_node_105_108_characters : assertHeader_node_105_108.toList = assertHeader_node_105_108_chars := by
  unfold assertHeader_node_105_108 assertHeader_node_105_108_chars
  rw [String.toList_append, assertHeader_chunk_chars105, assertHeader_node_106_108_characters]
def assertHeader_node_105_108_parts : List (List Char) := assertHeader_parts_leaf105 ++ assertHeader_node_106_108_parts
theorem assertHeader_node_105_108_parts_literal : assertHeader_node_105_108_parts = [assertHeader_chunk105, assertHeader_chunk106, assertHeader_chunk107] := by
  unfold assertHeader_node_105_108_parts
  rw [assertHeader_node_106_108_parts_literal]
  rfl
theorem assertHeader_node_105_108_parts_flatten : assertHeader_node_105_108_chars = assertHeader_node_105_108_parts.flatten := by
  unfold assertHeader_node_105_108_chars assertHeader_node_105_108_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf105_flatten, ← assertHeader_node_106_108_parts_flatten]
def assertHeader_node_103_108 : String := assertHeader_node_103_105 ++ assertHeader_node_105_108
def assertHeader_node_103_108_chars : List Char := assertHeader_node_103_105_chars ++ assertHeader_node_105_108_chars
theorem assertHeader_node_103_108_literal : assertHeader_node_103_108 = " Please see the License for the specific" := by
  unfold assertHeader_node_103_108
  rw [assertHeader_node_103_105_literal]
  rw [assertHeader_node_105_108_literal]
  cbv
theorem assertHeader_node_103_108_characters : assertHeader_node_103_108.toList = assertHeader_node_103_108_chars := by
  unfold assertHeader_node_103_108 assertHeader_node_103_108_chars
  rw [String.toList_append, assertHeader_node_103_105_characters, assertHeader_node_105_108_characters]
def assertHeader_node_103_108_parts : List (List Char) := assertHeader_node_103_105_parts ++ assertHeader_node_105_108_parts
theorem assertHeader_node_103_108_parts_literal : assertHeader_node_103_108_parts = [assertHeader_chunk103, assertHeader_chunk104, assertHeader_chunk105, assertHeader_chunk106, assertHeader_chunk107] := by
  unfold assertHeader_node_103_108_parts
  rw [assertHeader_node_103_105_parts_literal]
  rw [assertHeader_node_105_108_parts_literal]
  rfl
theorem assertHeader_node_103_108_parts_flatten : assertHeader_node_103_108_chars = assertHeader_node_103_108_parts.flatten := by
  unfold assertHeader_node_103_108_chars assertHeader_node_103_108_parts
  rw [List.flatten_append, ← assertHeader_node_103_105_parts_flatten, ← assertHeader_node_105_108_parts_flatten]
def assertHeader_parts_leaf108 : List (List Char) := [assertHeader_chunk108]
theorem assertHeader_parts_leaf108_flatten : assertHeader_chunk108 = assertHeader_parts_leaf108.flatten := by
  simp only [assertHeader_parts_leaf108, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf109 : List (List Char) := [assertHeader_chunk109]
theorem assertHeader_parts_leaf109_flatten : assertHeader_chunk109 = assertHeader_parts_leaf109.flatten := by
  simp only [assertHeader_parts_leaf109, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_108_110 : String := assertHeader_string_leaf108 ++ assertHeader_string_leaf109
def assertHeader_node_108_110_chars : List Char := assertHeader_chunk108 ++ assertHeader_chunk109
theorem assertHeader_node_108_110_literal : assertHeader_node_108_110 = " language govern" := by
  unfold assertHeader_node_108_110
  cbv
theorem assertHeader_node_108_110_characters : assertHeader_node_108_110.toList = assertHeader_node_108_110_chars := by
  unfold assertHeader_node_108_110 assertHeader_node_108_110_chars
  rw [String.toList_append, assertHeader_chunk_chars108, assertHeader_chunk_chars109]
def assertHeader_node_108_110_parts : List (List Char) := assertHeader_parts_leaf108 ++ assertHeader_parts_leaf109
theorem assertHeader_node_108_110_parts_literal : assertHeader_node_108_110_parts = [assertHeader_chunk108, assertHeader_chunk109] := by
  unfold assertHeader_node_108_110_parts
  rfl
theorem assertHeader_node_108_110_parts_flatten : assertHeader_node_108_110_chars = assertHeader_node_108_110_parts.flatten := by
  unfold assertHeader_node_108_110_chars assertHeader_node_108_110_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf108_flatten, ← assertHeader_parts_leaf109_flatten]
def assertHeader_parts_leaf110 : List (List Char) := [assertHeader_chunk110]
theorem assertHeader_parts_leaf110_flatten : assertHeader_chunk110 = assertHeader_parts_leaf110.flatten := by
  simp only [assertHeader_parts_leaf110, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf111 : List (List Char) := [assertHeader_chunk111]
theorem assertHeader_parts_leaf111_flatten : assertHeader_chunk111 = assertHeader_parts_leaf111.flatten := by
  simp only [assertHeader_parts_leaf111, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf112 : List (List Char) := [assertHeader_chunk112]
theorem assertHeader_parts_leaf112_flatten : assertHeader_chunk112 = assertHeader_parts_leaf112.flatten := by
  simp only [assertHeader_parts_leaf112, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_111_113 : String := assertHeader_string_leaf111 ++ assertHeader_string_leaf112
def assertHeader_node_111_113_chars : List Char := assertHeader_chunk111 ++ assertHeader_chunk112
theorem assertHeader_node_111_113_literal : assertHeader_node_111_113 = "ts and\n * limita" := by
  unfold assertHeader_node_111_113
  cbv
theorem assertHeader_node_111_113_characters : assertHeader_node_111_113.toList = assertHeader_node_111_113_chars := by
  unfold assertHeader_node_111_113 assertHeader_node_111_113_chars
  rw [String.toList_append, assertHeader_chunk_chars111, assertHeader_chunk_chars112]
def assertHeader_node_111_113_parts : List (List Char) := assertHeader_parts_leaf111 ++ assertHeader_parts_leaf112
theorem assertHeader_node_111_113_parts_literal : assertHeader_node_111_113_parts = [assertHeader_chunk111, assertHeader_chunk112] := by
  unfold assertHeader_node_111_113_parts
  rfl
theorem assertHeader_node_111_113_parts_flatten : assertHeader_node_111_113_chars = assertHeader_node_111_113_parts.flatten := by
  unfold assertHeader_node_111_113_chars assertHeader_node_111_113_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf111_flatten, ← assertHeader_parts_leaf112_flatten]
def assertHeader_node_110_113 : String := assertHeader_string_leaf110 ++ assertHeader_node_111_113
def assertHeader_node_110_113_chars : List Char := assertHeader_chunk110 ++ assertHeader_node_111_113_chars
theorem assertHeader_node_110_113_literal : assertHeader_node_110_113 = "ing rights and\n * limita" := by
  unfold assertHeader_node_110_113
  rw [assertHeader_node_111_113_literal]
  cbv
theorem assertHeader_node_110_113_characters : assertHeader_node_110_113.toList = assertHeader_node_110_113_chars := by
  unfold assertHeader_node_110_113 assertHeader_node_110_113_chars
  rw [String.toList_append, assertHeader_chunk_chars110, assertHeader_node_111_113_characters]
def assertHeader_node_110_113_parts : List (List Char) := assertHeader_parts_leaf110 ++ assertHeader_node_111_113_parts
theorem assertHeader_node_110_113_parts_literal : assertHeader_node_110_113_parts = [assertHeader_chunk110, assertHeader_chunk111, assertHeader_chunk112] := by
  unfold assertHeader_node_110_113_parts
  rw [assertHeader_node_111_113_parts_literal]
  rfl
theorem assertHeader_node_110_113_parts_flatten : assertHeader_node_110_113_chars = assertHeader_node_110_113_parts.flatten := by
  unfold assertHeader_node_110_113_chars assertHeader_node_110_113_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf110_flatten, ← assertHeader_node_111_113_parts_flatten]
def assertHeader_node_108_113 : String := assertHeader_node_108_110 ++ assertHeader_node_110_113
def assertHeader_node_108_113_chars : List Char := assertHeader_node_108_110_chars ++ assertHeader_node_110_113_chars
theorem assertHeader_node_108_113_literal : assertHeader_node_108_113 = " language governing rights and\n * limita" := by
  unfold assertHeader_node_108_113
  rw [assertHeader_node_108_110_literal]
  rw [assertHeader_node_110_113_literal]
  cbv
theorem assertHeader_node_108_113_characters : assertHeader_node_108_113.toList = assertHeader_node_108_113_chars := by
  unfold assertHeader_node_108_113 assertHeader_node_108_113_chars
  rw [String.toList_append, assertHeader_node_108_110_characters, assertHeader_node_110_113_characters]
def assertHeader_node_108_113_parts : List (List Char) := assertHeader_node_108_110_parts ++ assertHeader_node_110_113_parts
theorem assertHeader_node_108_113_parts_literal : assertHeader_node_108_113_parts = [assertHeader_chunk108, assertHeader_chunk109, assertHeader_chunk110, assertHeader_chunk111, assertHeader_chunk112] := by
  unfold assertHeader_node_108_113_parts
  rw [assertHeader_node_108_110_parts_literal]
  rw [assertHeader_node_110_113_parts_literal]
  rfl
theorem assertHeader_node_108_113_parts_flatten : assertHeader_node_108_113_chars = assertHeader_node_108_113_parts.flatten := by
  unfold assertHeader_node_108_113_chars assertHeader_node_108_113_parts
  rw [List.flatten_append, ← assertHeader_node_108_110_parts_flatten, ← assertHeader_node_110_113_parts_flatten]
def assertHeader_node_103_113 : String := assertHeader_node_103_108 ++ assertHeader_node_108_113
def assertHeader_node_103_113_chars : List Char := assertHeader_node_103_108_chars ++ assertHeader_node_108_113_chars
theorem assertHeader_node_103_113_literal : assertHeader_node_103_113 = " Please see the License for the specific language governing rights and\n * limita" := by
  unfold assertHeader_node_103_113
  rw [assertHeader_node_103_108_literal]
  rw [assertHeader_node_108_113_literal]
  cbv
theorem assertHeader_node_103_113_characters : assertHeader_node_103_113.toList = assertHeader_node_103_113_chars := by
  unfold assertHeader_node_103_113 assertHeader_node_103_113_chars
  rw [String.toList_append, assertHeader_node_103_108_characters, assertHeader_node_108_113_characters]
def assertHeader_node_103_113_parts : List (List Char) := assertHeader_node_103_108_parts ++ assertHeader_node_108_113_parts
theorem assertHeader_node_103_113_parts_literal : assertHeader_node_103_113_parts = [assertHeader_chunk103, assertHeader_chunk104, assertHeader_chunk105, assertHeader_chunk106, assertHeader_chunk107, assertHeader_chunk108, assertHeader_chunk109, assertHeader_chunk110, assertHeader_chunk111, assertHeader_chunk112] := by
  unfold assertHeader_node_103_113_parts
  rw [assertHeader_node_103_108_parts_literal]
  rw [assertHeader_node_108_113_parts_literal]
  rfl
theorem assertHeader_node_103_113_parts_flatten : assertHeader_node_103_113_chars = assertHeader_node_103_113_parts.flatten := by
  unfold assertHeader_node_103_113_chars assertHeader_node_103_113_parts
  rw [List.flatten_append, ← assertHeader_node_103_108_parts_flatten, ← assertHeader_node_108_113_parts_flatten]
def assertHeader_node_94_113 : String := assertHeader_node_94_103 ++ assertHeader_node_103_113
def assertHeader_node_94_113_chars : List Char := assertHeader_node_94_103_chars ++ assertHeader_node_103_113_chars
theorem assertHeader_node_94_113_literal : assertHeader_node_94_113 = "ITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.\n * Please see the License for the specific language governing rights and\n * limita" := by
  unfold assertHeader_node_94_113
  rw [assertHeader_node_94_103_literal]
  rw [assertHeader_node_103_113_literal]
  cbv
theorem assertHeader_node_94_113_characters : assertHeader_node_94_113.toList = assertHeader_node_94_113_chars := by
  unfold assertHeader_node_94_113 assertHeader_node_94_113_chars
  rw [String.toList_append, assertHeader_node_94_103_characters, assertHeader_node_103_113_characters]
def assertHeader_node_94_113_parts : List (List Char) := assertHeader_node_94_103_parts ++ assertHeader_node_103_113_parts
theorem assertHeader_node_94_113_parts_literal : assertHeader_node_94_113_parts = [assertHeader_chunk94, assertHeader_chunk95, assertHeader_chunk96, assertHeader_chunk97, assertHeader_chunk98, assertHeader_chunk99, assertHeader_chunk100, assertHeader_chunk101, assertHeader_chunk102, assertHeader_chunk103, assertHeader_chunk104, assertHeader_chunk105, assertHeader_chunk106, assertHeader_chunk107, assertHeader_chunk108, assertHeader_chunk109, assertHeader_chunk110, assertHeader_chunk111, assertHeader_chunk112] := by
  unfold assertHeader_node_94_113_parts
  rw [assertHeader_node_94_103_parts_literal]
  rw [assertHeader_node_103_113_parts_literal]
  rfl
theorem assertHeader_node_94_113_parts_flatten : assertHeader_node_94_113_chars = assertHeader_node_94_113_parts.flatten := by
  unfold assertHeader_node_94_113_chars assertHeader_node_94_113_parts
  rw [List.flatten_append, ← assertHeader_node_94_103_parts_flatten, ← assertHeader_node_103_113_parts_flatten]
def assertHeader_node_75_113 : String := assertHeader_node_75_94 ++ assertHeader_node_94_113
def assertHeader_node_75_113_chars : List Char := assertHeader_node_75_94_chars ++ assertHeader_node_94_113_chars
theorem assertHeader_node_75_113_literal : assertHeader_node_75_113 = ", EITHER\n * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,\n * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,\n * FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.\n * Please see the License for the specific language governing rights and\n * limita" := by
  unfold assertHeader_node_75_113
  rw [assertHeader_node_75_94_literal]
  rw [assertHeader_node_94_113_literal]
  cbv
theorem assertHeader_node_75_113_characters : assertHeader_node_75_113.toList = assertHeader_node_75_113_chars := by
  unfold assertHeader_node_75_113 assertHeader_node_75_113_chars
  rw [String.toList_append, assertHeader_node_75_94_characters, assertHeader_node_94_113_characters]
def assertHeader_node_75_113_parts : List (List Char) := assertHeader_node_75_94_parts ++ assertHeader_node_94_113_parts
theorem assertHeader_node_75_113_parts_literal : assertHeader_node_75_113_parts = [assertHeader_chunk75, assertHeader_chunk76, assertHeader_chunk77, assertHeader_chunk78, assertHeader_chunk79, assertHeader_chunk80, assertHeader_chunk81, assertHeader_chunk82, assertHeader_chunk83, assertHeader_chunk84, assertHeader_chunk85, assertHeader_chunk86, assertHeader_chunk87, assertHeader_chunk88, assertHeader_chunk89, assertHeader_chunk90, assertHeader_chunk91, assertHeader_chunk92, assertHeader_chunk93, assertHeader_chunk94, assertHeader_chunk95, assertHeader_chunk96, assertHeader_chunk97, assertHeader_chunk98, assertHeader_chunk99, assertHeader_chunk100, assertHeader_chunk101, assertHeader_chunk102, assertHeader_chunk103, assertHeader_chunk104, assertHeader_chunk105, assertHeader_chunk106, assertHeader_chunk107, assertHeader_chunk108, assertHeader_chunk109, assertHeader_chunk110, assertHeader_chunk111, assertHeader_chunk112] := by
  unfold assertHeader_node_75_113_parts
  rw [assertHeader_node_75_94_parts_literal]
  rw [assertHeader_node_94_113_parts_literal]
  rfl
theorem assertHeader_node_75_113_parts_flatten : assertHeader_node_75_113_chars = assertHeader_node_75_113_parts.flatten := by
  unfold assertHeader_node_75_113_chars assertHeader_node_75_113_parts
  rw [List.flatten_append, ← assertHeader_node_75_94_parts_flatten, ← assertHeader_node_94_113_parts_flatten]
def assertHeader_parts_leaf113 : List (List Char) := [assertHeader_chunk113]
theorem assertHeader_parts_leaf113_flatten : assertHeader_chunk113 = assertHeader_parts_leaf113.flatten := by
  simp only [assertHeader_parts_leaf113, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf114 : List (List Char) := [assertHeader_chunk114]
theorem assertHeader_parts_leaf114_flatten : assertHeader_chunk114 = assertHeader_parts_leaf114.flatten := by
  simp only [assertHeader_parts_leaf114, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_113_115 : String := assertHeader_string_leaf113 ++ assertHeader_string_leaf114
def assertHeader_node_113_115_chars : List Char := assertHeader_chunk113 ++ assertHeader_chunk114
theorem assertHeader_node_113_115_literal : assertHeader_node_113_115 = "tions under the " := by
  unfold assertHeader_node_113_115
  cbv
theorem assertHeader_node_113_115_characters : assertHeader_node_113_115.toList = assertHeader_node_113_115_chars := by
  unfold assertHeader_node_113_115 assertHeader_node_113_115_chars
  rw [String.toList_append, assertHeader_chunk_chars113, assertHeader_chunk_chars114]
def assertHeader_node_113_115_parts : List (List Char) := assertHeader_parts_leaf113 ++ assertHeader_parts_leaf114
theorem assertHeader_node_113_115_parts_literal : assertHeader_node_113_115_parts = [assertHeader_chunk113, assertHeader_chunk114] := by
  unfold assertHeader_node_113_115_parts
  rfl
theorem assertHeader_node_113_115_parts_flatten : assertHeader_node_113_115_chars = assertHeader_node_113_115_parts.flatten := by
  unfold assertHeader_node_113_115_chars assertHeader_node_113_115_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf113_flatten, ← assertHeader_parts_leaf114_flatten]
def assertHeader_parts_leaf115 : List (List Char) := [assertHeader_chunk115]
theorem assertHeader_parts_leaf115_flatten : assertHeader_chunk115 = assertHeader_parts_leaf115.flatten := by
  simp only [assertHeader_parts_leaf115, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf116 : List (List Char) := [assertHeader_chunk116]
theorem assertHeader_parts_leaf116_flatten : assertHeader_chunk116 = assertHeader_parts_leaf116.flatten := by
  simp only [assertHeader_parts_leaf116, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_115_117 : String := assertHeader_string_leaf115 ++ assertHeader_string_leaf116
def assertHeader_node_115_117_chars : List Char := assertHeader_chunk115 ++ assertHeader_chunk116
theorem assertHeader_node_115_117_literal : assertHeader_node_115_117 = "License.\n *\n * @" := by
  unfold assertHeader_node_115_117
  cbv
theorem assertHeader_node_115_117_characters : assertHeader_node_115_117.toList = assertHeader_node_115_117_chars := by
  unfold assertHeader_node_115_117 assertHeader_node_115_117_chars
  rw [String.toList_append, assertHeader_chunk_chars115, assertHeader_chunk_chars116]
def assertHeader_node_115_117_parts : List (List Char) := assertHeader_parts_leaf115 ++ assertHeader_parts_leaf116
theorem assertHeader_node_115_117_parts_literal : assertHeader_node_115_117_parts = [assertHeader_chunk115, assertHeader_chunk116] := by
  unfold assertHeader_node_115_117_parts
  rfl
theorem assertHeader_node_115_117_parts_flatten : assertHeader_node_115_117_chars = assertHeader_node_115_117_parts.flatten := by
  unfold assertHeader_node_115_117_chars assertHeader_node_115_117_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf115_flatten, ← assertHeader_parts_leaf116_flatten]
def assertHeader_node_113_117 : String := assertHeader_node_113_115 ++ assertHeader_node_115_117
def assertHeader_node_113_117_chars : List Char := assertHeader_node_113_115_chars ++ assertHeader_node_115_117_chars
theorem assertHeader_node_113_117_literal : assertHeader_node_113_117 = "tions under the License.\n *\n * @" := by
  unfold assertHeader_node_113_117
  rw [assertHeader_node_113_115_literal]
  rw [assertHeader_node_115_117_literal]
  cbv
theorem assertHeader_node_113_117_characters : assertHeader_node_113_117.toList = assertHeader_node_113_117_chars := by
  unfold assertHeader_node_113_117 assertHeader_node_113_117_chars
  rw [String.toList_append, assertHeader_node_113_115_characters, assertHeader_node_115_117_characters]
def assertHeader_node_113_117_parts : List (List Char) := assertHeader_node_113_115_parts ++ assertHeader_node_115_117_parts
theorem assertHeader_node_113_117_parts_literal : assertHeader_node_113_117_parts = [assertHeader_chunk113, assertHeader_chunk114, assertHeader_chunk115, assertHeader_chunk116] := by
  unfold assertHeader_node_113_117_parts
  rw [assertHeader_node_113_115_parts_literal]
  rw [assertHeader_node_115_117_parts_literal]
  rfl
theorem assertHeader_node_113_117_parts_flatten : assertHeader_node_113_117_chars = assertHeader_node_113_117_parts.flatten := by
  unfold assertHeader_node_113_117_chars assertHeader_node_113_117_parts
  rw [List.flatten_append, ← assertHeader_node_113_115_parts_flatten, ← assertHeader_node_115_117_parts_flatten]
def assertHeader_parts_leaf117 : List (List Char) := [assertHeader_chunk117]
theorem assertHeader_parts_leaf117_flatten : assertHeader_chunk117 = assertHeader_parts_leaf117.flatten := by
  simp only [assertHeader_parts_leaf117, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf118 : List (List Char) := [assertHeader_chunk118]
theorem assertHeader_parts_leaf118_flatten : assertHeader_chunk118 = assertHeader_parts_leaf118.flatten := by
  simp only [assertHeader_parts_leaf118, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_117_119 : String := assertHeader_string_leaf117 ++ assertHeader_string_leaf118
def assertHeader_node_117_119_chars : List Char := assertHeader_chunk117 ++ assertHeader_chunk118
theorem assertHeader_node_117_119_literal : assertHeader_node_117_119 = "APPLE_LICENSE_HE" := by
  unfold assertHeader_node_117_119
  cbv
theorem assertHeader_node_117_119_characters : assertHeader_node_117_119.toList = assertHeader_node_117_119_chars := by
  unfold assertHeader_node_117_119 assertHeader_node_117_119_chars
  rw [String.toList_append, assertHeader_chunk_chars117, assertHeader_chunk_chars118]
def assertHeader_node_117_119_parts : List (List Char) := assertHeader_parts_leaf117 ++ assertHeader_parts_leaf118
theorem assertHeader_node_117_119_parts_literal : assertHeader_node_117_119_parts = [assertHeader_chunk117, assertHeader_chunk118] := by
  unfold assertHeader_node_117_119_parts
  rfl
theorem assertHeader_node_117_119_parts_flatten : assertHeader_node_117_119_chars = assertHeader_node_117_119_parts.flatten := by
  unfold assertHeader_node_117_119_chars assertHeader_node_117_119_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf117_flatten, ← assertHeader_parts_leaf118_flatten]
def assertHeader_parts_leaf119 : List (List Char) := [assertHeader_chunk119]
theorem assertHeader_parts_leaf119_flatten : assertHeader_chunk119 = assertHeader_parts_leaf119.flatten := by
  simp only [assertHeader_parts_leaf119, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf120 : List (List Char) := [assertHeader_chunk120]
theorem assertHeader_parts_leaf120_flatten : assertHeader_chunk120 = assertHeader_parts_leaf120.flatten := by
  simp only [assertHeader_parts_leaf120, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf121 : List (List Char) := [assertHeader_chunk121]
theorem assertHeader_parts_leaf121_flatten : assertHeader_chunk121 = assertHeader_parts_leaf121.flatten := by
  simp only [assertHeader_parts_leaf121, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_120_122 : String := assertHeader_string_leaf120 ++ assertHeader_string_leaf121
def assertHeader_node_120_122_chars : List Char := assertHeader_chunk120 ++ assertHeader_chunk121
theorem assertHeader_node_120_122_literal : assertHeader_node_120_122 = "@\n */\n\n#ifndef _" := by
  unfold assertHeader_node_120_122
  cbv
theorem assertHeader_node_120_122_characters : assertHeader_node_120_122.toList = assertHeader_node_120_122_chars := by
  unfold assertHeader_node_120_122 assertHeader_node_120_122_chars
  rw [String.toList_append, assertHeader_chunk_chars120, assertHeader_chunk_chars121]
def assertHeader_node_120_122_parts : List (List Char) := assertHeader_parts_leaf120 ++ assertHeader_parts_leaf121
theorem assertHeader_node_120_122_parts_literal : assertHeader_node_120_122_parts = [assertHeader_chunk120, assertHeader_chunk121] := by
  unfold assertHeader_node_120_122_parts
  rfl
theorem assertHeader_node_120_122_parts_flatten : assertHeader_node_120_122_chars = assertHeader_node_120_122_parts.flatten := by
  unfold assertHeader_node_120_122_chars assertHeader_node_120_122_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf120_flatten, ← assertHeader_parts_leaf121_flatten]
def assertHeader_node_119_122 : String := assertHeader_string_leaf119 ++ assertHeader_node_120_122
def assertHeader_node_119_122_chars : List Char := assertHeader_chunk119 ++ assertHeader_node_120_122_chars
theorem assertHeader_node_119_122_literal : assertHeader_node_119_122 = "ADER_END@\n */\n\n#ifndef _" := by
  unfold assertHeader_node_119_122
  rw [assertHeader_node_120_122_literal]
  cbv
theorem assertHeader_node_119_122_characters : assertHeader_node_119_122.toList = assertHeader_node_119_122_chars := by
  unfold assertHeader_node_119_122 assertHeader_node_119_122_chars
  rw [String.toList_append, assertHeader_chunk_chars119, assertHeader_node_120_122_characters]
def assertHeader_node_119_122_parts : List (List Char) := assertHeader_parts_leaf119 ++ assertHeader_node_120_122_parts
theorem assertHeader_node_119_122_parts_literal : assertHeader_node_119_122_parts = [assertHeader_chunk119, assertHeader_chunk120, assertHeader_chunk121] := by
  unfold assertHeader_node_119_122_parts
  rw [assertHeader_node_120_122_parts_literal]
  rfl
theorem assertHeader_node_119_122_parts_flatten : assertHeader_node_119_122_chars = assertHeader_node_119_122_parts.flatten := by
  unfold assertHeader_node_119_122_chars assertHeader_node_119_122_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf119_flatten, ← assertHeader_node_120_122_parts_flatten]
def assertHeader_node_117_122 : String := assertHeader_node_117_119 ++ assertHeader_node_119_122
def assertHeader_node_117_122_chars : List Char := assertHeader_node_117_119_chars ++ assertHeader_node_119_122_chars
theorem assertHeader_node_117_122_literal : assertHeader_node_117_122 = "APPLE_LICENSE_HEADER_END@\n */\n\n#ifndef _" := by
  unfold assertHeader_node_117_122
  rw [assertHeader_node_117_119_literal]
  rw [assertHeader_node_119_122_literal]
  cbv
theorem assertHeader_node_117_122_characters : assertHeader_node_117_122.toList = assertHeader_node_117_122_chars := by
  unfold assertHeader_node_117_122 assertHeader_node_117_122_chars
  rw [String.toList_append, assertHeader_node_117_119_characters, assertHeader_node_119_122_characters]
def assertHeader_node_117_122_parts : List (List Char) := assertHeader_node_117_119_parts ++ assertHeader_node_119_122_parts
theorem assertHeader_node_117_122_parts_literal : assertHeader_node_117_122_parts = [assertHeader_chunk117, assertHeader_chunk118, assertHeader_chunk119, assertHeader_chunk120, assertHeader_chunk121] := by
  unfold assertHeader_node_117_122_parts
  rw [assertHeader_node_117_119_parts_literal]
  rw [assertHeader_node_119_122_parts_literal]
  rfl
theorem assertHeader_node_117_122_parts_flatten : assertHeader_node_117_122_chars = assertHeader_node_117_122_parts.flatten := by
  unfold assertHeader_node_117_122_chars assertHeader_node_117_122_parts
  rw [List.flatten_append, ← assertHeader_node_117_119_parts_flatten, ← assertHeader_node_119_122_parts_flatten]
def assertHeader_node_113_122 : String := assertHeader_node_113_117 ++ assertHeader_node_117_122
def assertHeader_node_113_122_chars : List Char := assertHeader_node_113_117_chars ++ assertHeader_node_117_122_chars
theorem assertHeader_node_113_122_literal : assertHeader_node_113_122 = "tions under the License.\n *\n * @APPLE_LICENSE_HEADER_END@\n */\n\n#ifndef _" := by
  unfold assertHeader_node_113_122
  rw [assertHeader_node_113_117_literal]
  rw [assertHeader_node_117_122_literal]
  cbv
theorem assertHeader_node_113_122_characters : assertHeader_node_113_122.toList = assertHeader_node_113_122_chars := by
  unfold assertHeader_node_113_122 assertHeader_node_113_122_chars
  rw [String.toList_append, assertHeader_node_113_117_characters, assertHeader_node_117_122_characters]
def assertHeader_node_113_122_parts : List (List Char) := assertHeader_node_113_117_parts ++ assertHeader_node_117_122_parts
theorem assertHeader_node_113_122_parts_literal : assertHeader_node_113_122_parts = [assertHeader_chunk113, assertHeader_chunk114, assertHeader_chunk115, assertHeader_chunk116, assertHeader_chunk117, assertHeader_chunk118, assertHeader_chunk119, assertHeader_chunk120, assertHeader_chunk121] := by
  unfold assertHeader_node_113_122_parts
  rw [assertHeader_node_113_117_parts_literal]
  rw [assertHeader_node_117_122_parts_literal]
  rfl
theorem assertHeader_node_113_122_parts_flatten : assertHeader_node_113_122_chars = assertHeader_node_113_122_parts.flatten := by
  unfold assertHeader_node_113_122_chars assertHeader_node_113_122_parts
  rw [List.flatten_append, ← assertHeader_node_113_117_parts_flatten, ← assertHeader_node_117_122_parts_flatten]
def assertHeader_parts_leaf122 : List (List Char) := [assertHeader_chunk122]
theorem assertHeader_parts_leaf122_flatten : assertHeader_chunk122 = assertHeader_parts_leaf122.flatten := by
  simp only [assertHeader_parts_leaf122, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf123 : List (List Char) := [assertHeader_chunk123]
theorem assertHeader_parts_leaf123_flatten : assertHeader_chunk123 = assertHeader_parts_leaf123.flatten := by
  simp only [assertHeader_parts_leaf123, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_122_124 : String := assertHeader_string_leaf122 ++ assertHeader_string_leaf123
def assertHeader_node_122_124_chars : List Char := assertHeader_chunk122 ++ assertHeader_chunk123
theorem assertHeader_node_122_124_literal : assertHeader_node_122_124 = "ASSERT_H_\n#defin" := by
  unfold assertHeader_node_122_124
  cbv
theorem assertHeader_node_122_124_characters : assertHeader_node_122_124.toList = assertHeader_node_122_124_chars := by
  unfold assertHeader_node_122_124 assertHeader_node_122_124_chars
  rw [String.toList_append, assertHeader_chunk_chars122, assertHeader_chunk_chars123]
def assertHeader_node_122_124_parts : List (List Char) := assertHeader_parts_leaf122 ++ assertHeader_parts_leaf123
theorem assertHeader_node_122_124_parts_literal : assertHeader_node_122_124_parts = [assertHeader_chunk122, assertHeader_chunk123] := by
  unfold assertHeader_node_122_124_parts
  rfl
theorem assertHeader_node_122_124_parts_flatten : assertHeader_node_122_124_chars = assertHeader_node_122_124_parts.flatten := by
  unfold assertHeader_node_122_124_chars assertHeader_node_122_124_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf122_flatten, ← assertHeader_parts_leaf123_flatten]
def assertHeader_parts_leaf124 : List (List Char) := [assertHeader_chunk124]
theorem assertHeader_parts_leaf124_flatten : assertHeader_chunk124 = assertHeader_parts_leaf124.flatten := by
  simp only [assertHeader_parts_leaf124, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf125 : List (List Char) := [assertHeader_chunk125]
theorem assertHeader_parts_leaf125_flatten : assertHeader_chunk125 = assertHeader_parts_leaf125.flatten := by
  simp only [assertHeader_parts_leaf125, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf126 : List (List Char) := [assertHeader_chunk126]
theorem assertHeader_parts_leaf126_flatten : assertHeader_chunk126 = assertHeader_parts_leaf126.flatten := by
  simp only [assertHeader_parts_leaf126, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_125_127 : String := assertHeader_string_leaf125 ++ assertHeader_string_leaf126
def assertHeader_node_125_127_chars : List Char := assertHeader_chunk125 ++ assertHeader_chunk126
theorem assertHeader_node_125_127_literal : assertHeader_node_125_127 = "T_H_\n\n#ifndef __" := by
  unfold assertHeader_node_125_127
  cbv
theorem assertHeader_node_125_127_characters : assertHeader_node_125_127.toList = assertHeader_node_125_127_chars := by
  unfold assertHeader_node_125_127 assertHeader_node_125_127_chars
  rw [String.toList_append, assertHeader_chunk_chars125, assertHeader_chunk_chars126]
def assertHeader_node_125_127_parts : List (List Char) := assertHeader_parts_leaf125 ++ assertHeader_parts_leaf126
theorem assertHeader_node_125_127_parts_literal : assertHeader_node_125_127_parts = [assertHeader_chunk125, assertHeader_chunk126] := by
  unfold assertHeader_node_125_127_parts
  rfl
theorem assertHeader_node_125_127_parts_flatten : assertHeader_node_125_127_chars = assertHeader_node_125_127_parts.flatten := by
  unfold assertHeader_node_125_127_chars assertHeader_node_125_127_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf125_flatten, ← assertHeader_parts_leaf126_flatten]
def assertHeader_node_124_127 : String := assertHeader_string_leaf124 ++ assertHeader_node_125_127
def assertHeader_node_124_127_chars : List Char := assertHeader_chunk124 ++ assertHeader_node_125_127_chars
theorem assertHeader_node_124_127_literal : assertHeader_node_124_127 = "e _ASSERT_H_\n\n#ifndef __" := by
  unfold assertHeader_node_124_127
  rw [assertHeader_node_125_127_literal]
  cbv
theorem assertHeader_node_124_127_characters : assertHeader_node_124_127.toList = assertHeader_node_124_127_chars := by
  unfold assertHeader_node_124_127 assertHeader_node_124_127_chars
  rw [String.toList_append, assertHeader_chunk_chars124, assertHeader_node_125_127_characters]
def assertHeader_node_124_127_parts : List (List Char) := assertHeader_parts_leaf124 ++ assertHeader_node_125_127_parts
theorem assertHeader_node_124_127_parts_literal : assertHeader_node_124_127_parts = [assertHeader_chunk124, assertHeader_chunk125, assertHeader_chunk126] := by
  unfold assertHeader_node_124_127_parts
  rw [assertHeader_node_125_127_parts_literal]
  rfl
theorem assertHeader_node_124_127_parts_flatten : assertHeader_node_124_127_chars = assertHeader_node_124_127_parts.flatten := by
  unfold assertHeader_node_124_127_chars assertHeader_node_124_127_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf124_flatten, ← assertHeader_node_125_127_parts_flatten]
def assertHeader_node_122_127 : String := assertHeader_node_122_124 ++ assertHeader_node_124_127
def assertHeader_node_122_127_chars : List Char := assertHeader_node_122_124_chars ++ assertHeader_node_124_127_chars
theorem assertHeader_node_122_127_literal : assertHeader_node_122_127 = "ASSERT_H_\n#define _ASSERT_H_\n\n#ifndef __" := by
  unfold assertHeader_node_122_127
  rw [assertHeader_node_122_124_literal]
  rw [assertHeader_node_124_127_literal]
  cbv
theorem assertHeader_node_122_127_characters : assertHeader_node_122_127.toList = assertHeader_node_122_127_chars := by
  unfold assertHeader_node_122_127 assertHeader_node_122_127_chars
  rw [String.toList_append, assertHeader_node_122_124_characters, assertHeader_node_124_127_characters]
def assertHeader_node_122_127_parts : List (List Char) := assertHeader_node_122_124_parts ++ assertHeader_node_124_127_parts
theorem assertHeader_node_122_127_parts_literal : assertHeader_node_122_127_parts = [assertHeader_chunk122, assertHeader_chunk123, assertHeader_chunk124, assertHeader_chunk125, assertHeader_chunk126] := by
  unfold assertHeader_node_122_127_parts
  rw [assertHeader_node_122_124_parts_literal]
  rw [assertHeader_node_124_127_parts_literal]
  rfl
theorem assertHeader_node_122_127_parts_flatten : assertHeader_node_122_127_chars = assertHeader_node_122_127_parts.flatten := by
  unfold assertHeader_node_122_127_chars assertHeader_node_122_127_parts
  rw [List.flatten_append, ← assertHeader_node_122_124_parts_flatten, ← assertHeader_node_124_127_parts_flatten]
def assertHeader_parts_leaf127 : List (List Char) := [assertHeader_chunk127]
theorem assertHeader_parts_leaf127_flatten : assertHeader_chunk127 = assertHeader_parts_leaf127.flatten := by
  simp only [assertHeader_parts_leaf127, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf128 : List (List Char) := [assertHeader_chunk128]
theorem assertHeader_parts_leaf128_flatten : assertHeader_chunk128 = assertHeader_parts_leaf128.flatten := by
  simp only [assertHeader_parts_leaf128, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_127_129 : String := assertHeader_string_leaf127 ++ assertHeader_string_leaf128
def assertHeader_node_127_129_chars : List Char := assertHeader_chunk127 ++ assertHeader_chunk128
theorem assertHeader_node_127_129_literal : assertHeader_node_127_129 = "cplusplus\n#if de" := by
  unfold assertHeader_node_127_129
  cbv
theorem assertHeader_node_127_129_characters : assertHeader_node_127_129.toList = assertHeader_node_127_129_chars := by
  unfold assertHeader_node_127_129 assertHeader_node_127_129_chars
  rw [String.toList_append, assertHeader_chunk_chars127, assertHeader_chunk_chars128]
def assertHeader_node_127_129_parts : List (List Char) := assertHeader_parts_leaf127 ++ assertHeader_parts_leaf128
theorem assertHeader_node_127_129_parts_literal : assertHeader_node_127_129_parts = [assertHeader_chunk127, assertHeader_chunk128] := by
  unfold assertHeader_node_127_129_parts
  rfl
theorem assertHeader_node_127_129_parts_flatten : assertHeader_node_127_129_chars = assertHeader_node_127_129_parts.flatten := by
  unfold assertHeader_node_127_129_chars assertHeader_node_127_129_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf127_flatten, ← assertHeader_parts_leaf128_flatten]
def assertHeader_parts_leaf129 : List (List Char) := [assertHeader_chunk129]
theorem assertHeader_parts_leaf129_flatten : assertHeader_chunk129 = assertHeader_parts_leaf129.flatten := by
  simp only [assertHeader_parts_leaf129, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf130 : List (List Char) := [assertHeader_chunk130]
theorem assertHeader_parts_leaf130_flatten : assertHeader_chunk130 = assertHeader_parts_leaf130.flatten := by
  simp only [assertHeader_parts_leaf130, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf131 : List (List Char) := [assertHeader_chunk131]
theorem assertHeader_parts_leaf131_flatten : assertHeader_chunk131 = assertHeader_parts_leaf131.flatten := by
  simp only [assertHeader_parts_leaf131, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_130_132 : String := assertHeader_string_leaf130 ++ assertHeader_string_leaf131
def assertHeader_node_130_132_chars : List Char := assertHeader_chunk130 ++ assertHeader_chunk131
theorem assertHeader_node_130_132_literal : assertHeader_node_130_132 = "STDC_VERSION__) " := by
  unfold assertHeader_node_130_132
  cbv
theorem assertHeader_node_130_132_characters : assertHeader_node_130_132.toList = assertHeader_node_130_132_chars := by
  unfold assertHeader_node_130_132 assertHeader_node_130_132_chars
  rw [String.toList_append, assertHeader_chunk_chars130, assertHeader_chunk_chars131]
def assertHeader_node_130_132_parts : List (List Char) := assertHeader_parts_leaf130 ++ assertHeader_parts_leaf131
theorem assertHeader_node_130_132_parts_literal : assertHeader_node_130_132_parts = [assertHeader_chunk130, assertHeader_chunk131] := by
  unfold assertHeader_node_130_132_parts
  rfl
theorem assertHeader_node_130_132_parts_flatten : assertHeader_node_130_132_chars = assertHeader_node_130_132_parts.flatten := by
  unfold assertHeader_node_130_132_chars assertHeader_node_130_132_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf130_flatten, ← assertHeader_parts_leaf131_flatten]
def assertHeader_node_129_132 : String := assertHeader_string_leaf129 ++ assertHeader_node_130_132
def assertHeader_node_129_132_chars : List Char := assertHeader_chunk129 ++ assertHeader_node_130_132_chars
theorem assertHeader_node_129_132_literal : assertHeader_node_129_132 = "fined(__STDC_VERSION__) " := by
  unfold assertHeader_node_129_132
  rw [assertHeader_node_130_132_literal]
  cbv
theorem assertHeader_node_129_132_characters : assertHeader_node_129_132.toList = assertHeader_node_129_132_chars := by
  unfold assertHeader_node_129_132 assertHeader_node_129_132_chars
  rw [String.toList_append, assertHeader_chunk_chars129, assertHeader_node_130_132_characters]
def assertHeader_node_129_132_parts : List (List Char) := assertHeader_parts_leaf129 ++ assertHeader_node_130_132_parts
theorem assertHeader_node_129_132_parts_literal : assertHeader_node_129_132_parts = [assertHeader_chunk129, assertHeader_chunk130, assertHeader_chunk131] := by
  unfold assertHeader_node_129_132_parts
  rw [assertHeader_node_130_132_parts_literal]
  rfl
theorem assertHeader_node_129_132_parts_flatten : assertHeader_node_129_132_chars = assertHeader_node_129_132_parts.flatten := by
  unfold assertHeader_node_129_132_chars assertHeader_node_129_132_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf129_flatten, ← assertHeader_node_130_132_parts_flatten]
def assertHeader_node_127_132 : String := assertHeader_node_127_129 ++ assertHeader_node_129_132
def assertHeader_node_127_132_chars : List Char := assertHeader_node_127_129_chars ++ assertHeader_node_129_132_chars
theorem assertHeader_node_127_132_literal : assertHeader_node_127_132 = "cplusplus\n#if defined(__STDC_VERSION__) " := by
  unfold assertHeader_node_127_132
  rw [assertHeader_node_127_129_literal]
  rw [assertHeader_node_129_132_literal]
  cbv
theorem assertHeader_node_127_132_characters : assertHeader_node_127_132.toList = assertHeader_node_127_132_chars := by
  unfold assertHeader_node_127_132 assertHeader_node_127_132_chars
  rw [String.toList_append, assertHeader_node_127_129_characters, assertHeader_node_129_132_characters]
def assertHeader_node_127_132_parts : List (List Char) := assertHeader_node_127_129_parts ++ assertHeader_node_129_132_parts
theorem assertHeader_node_127_132_parts_literal : assertHeader_node_127_132_parts = [assertHeader_chunk127, assertHeader_chunk128, assertHeader_chunk129, assertHeader_chunk130, assertHeader_chunk131] := by
  unfold assertHeader_node_127_132_parts
  rw [assertHeader_node_127_129_parts_literal]
  rw [assertHeader_node_129_132_parts_literal]
  rfl
theorem assertHeader_node_127_132_parts_flatten : assertHeader_node_127_132_chars = assertHeader_node_127_132_parts.flatten := by
  unfold assertHeader_node_127_132_chars assertHeader_node_127_132_parts
  rw [List.flatten_append, ← assertHeader_node_127_129_parts_flatten, ← assertHeader_node_129_132_parts_flatten]
def assertHeader_node_122_132 : String := assertHeader_node_122_127 ++ assertHeader_node_127_132
def assertHeader_node_122_132_chars : List Char := assertHeader_node_122_127_chars ++ assertHeader_node_127_132_chars
theorem assertHeader_node_122_132_literal : assertHeader_node_122_132 = "ASSERT_H_\n#define _ASSERT_H_\n\n#ifndef __cplusplus\n#if defined(__STDC_VERSION__) " := by
  unfold assertHeader_node_122_132
  rw [assertHeader_node_122_127_literal]
  rw [assertHeader_node_127_132_literal]
  cbv
theorem assertHeader_node_122_132_characters : assertHeader_node_122_132.toList = assertHeader_node_122_132_chars := by
  unfold assertHeader_node_122_132 assertHeader_node_122_132_chars
  rw [String.toList_append, assertHeader_node_122_127_characters, assertHeader_node_127_132_characters]
def assertHeader_node_122_132_parts : List (List Char) := assertHeader_node_122_127_parts ++ assertHeader_node_127_132_parts
theorem assertHeader_node_122_132_parts_literal : assertHeader_node_122_132_parts = [assertHeader_chunk122, assertHeader_chunk123, assertHeader_chunk124, assertHeader_chunk125, assertHeader_chunk126, assertHeader_chunk127, assertHeader_chunk128, assertHeader_chunk129, assertHeader_chunk130, assertHeader_chunk131] := by
  unfold assertHeader_node_122_132_parts
  rw [assertHeader_node_122_127_parts_literal]
  rw [assertHeader_node_127_132_parts_literal]
  rfl
theorem assertHeader_node_122_132_parts_flatten : assertHeader_node_122_132_chars = assertHeader_node_122_132_parts.flatten := by
  unfold assertHeader_node_122_132_chars assertHeader_node_122_132_parts
  rw [List.flatten_append, ← assertHeader_node_122_127_parts_flatten, ← assertHeader_node_127_132_parts_flatten]
def assertHeader_node_113_132 : String := assertHeader_node_113_122 ++ assertHeader_node_122_132
def assertHeader_node_113_132_chars : List Char := assertHeader_node_113_122_chars ++ assertHeader_node_122_132_chars
theorem assertHeader_node_113_132_literal : assertHeader_node_113_132 = "tions under the License.\n *\n * @APPLE_LICENSE_HEADER_END@\n */\n\n#ifndef _ASSERT_H_\n#define _ASSERT_H_\n\n#ifndef __cplusplus\n#if defined(__STDC_VERSION__) " := by
  unfold assertHeader_node_113_132
  rw [assertHeader_node_113_122_literal]
  rw [assertHeader_node_122_132_literal]
  cbv
theorem assertHeader_node_113_132_characters : assertHeader_node_113_132.toList = assertHeader_node_113_132_chars := by
  unfold assertHeader_node_113_132 assertHeader_node_113_132_chars
  rw [String.toList_append, assertHeader_node_113_122_characters, assertHeader_node_122_132_characters]
def assertHeader_node_113_132_parts : List (List Char) := assertHeader_node_113_122_parts ++ assertHeader_node_122_132_parts
theorem assertHeader_node_113_132_parts_literal : assertHeader_node_113_132_parts = [assertHeader_chunk113, assertHeader_chunk114, assertHeader_chunk115, assertHeader_chunk116, assertHeader_chunk117, assertHeader_chunk118, assertHeader_chunk119, assertHeader_chunk120, assertHeader_chunk121, assertHeader_chunk122, assertHeader_chunk123, assertHeader_chunk124, assertHeader_chunk125, assertHeader_chunk126, assertHeader_chunk127, assertHeader_chunk128, assertHeader_chunk129, assertHeader_chunk130, assertHeader_chunk131] := by
  unfold assertHeader_node_113_132_parts
  rw [assertHeader_node_113_122_parts_literal]
  rw [assertHeader_node_122_132_parts_literal]
  rfl
theorem assertHeader_node_113_132_parts_flatten : assertHeader_node_113_132_chars = assertHeader_node_113_132_parts.flatten := by
  unfold assertHeader_node_113_132_chars assertHeader_node_113_132_parts
  rw [List.flatten_append, ← assertHeader_node_113_122_parts_flatten, ← assertHeader_node_122_132_parts_flatten]
def assertHeader_parts_leaf132 : List (List Char) := [assertHeader_chunk132]
theorem assertHeader_parts_leaf132_flatten : assertHeader_chunk132 = assertHeader_parts_leaf132.flatten := by
  simp only [assertHeader_parts_leaf132, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf133 : List (List Char) := [assertHeader_chunk133]
theorem assertHeader_parts_leaf133_flatten : assertHeader_chunk133 = assertHeader_parts_leaf133.flatten := by
  simp only [assertHeader_parts_leaf133, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_132_134 : String := assertHeader_string_leaf132 ++ assertHeader_string_leaf133
def assertHeader_node_132_134_chars : List Char := assertHeader_chunk132 ++ assertHeader_chunk133
theorem assertHeader_node_132_134_literal : assertHeader_node_132_134 = "&& __STDC_VERSIO" := by
  unfold assertHeader_node_132_134
  cbv
theorem assertHeader_node_132_134_characters : assertHeader_node_132_134.toList = assertHeader_node_132_134_chars := by
  unfold assertHeader_node_132_134 assertHeader_node_132_134_chars
  rw [String.toList_append, assertHeader_chunk_chars132, assertHeader_chunk_chars133]
def assertHeader_node_132_134_parts : List (List Char) := assertHeader_parts_leaf132 ++ assertHeader_parts_leaf133
theorem assertHeader_node_132_134_parts_literal : assertHeader_node_132_134_parts = [assertHeader_chunk132, assertHeader_chunk133] := by
  unfold assertHeader_node_132_134_parts
  rfl
theorem assertHeader_node_132_134_parts_flatten : assertHeader_node_132_134_chars = assertHeader_node_132_134_parts.flatten := by
  unfold assertHeader_node_132_134_chars assertHeader_node_132_134_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf132_flatten, ← assertHeader_parts_leaf133_flatten]
def assertHeader_parts_leaf134 : List (List Char) := [assertHeader_chunk134]
theorem assertHeader_parts_leaf134_flatten : assertHeader_chunk134 = assertHeader_parts_leaf134.flatten := by
  simp only [assertHeader_parts_leaf134, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf135 : List (List Char) := [assertHeader_chunk135]
theorem assertHeader_parts_leaf135_flatten : assertHeader_chunk135 = assertHeader_parts_leaf135.flatten := by
  simp only [assertHeader_parts_leaf135, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_134_136 : String := assertHeader_string_leaf134 ++ assertHeader_string_leaf135
def assertHeader_node_134_136_chars : List Char := assertHeader_chunk134 ++ assertHeader_chunk135
theorem assertHeader_node_134_136_literal : assertHeader_node_134_136 = "N__ >= 201112L\n#" := by
  unfold assertHeader_node_134_136
  cbv
theorem assertHeader_node_134_136_characters : assertHeader_node_134_136.toList = assertHeader_node_134_136_chars := by
  unfold assertHeader_node_134_136 assertHeader_node_134_136_chars
  rw [String.toList_append, assertHeader_chunk_chars134, assertHeader_chunk_chars135]
def assertHeader_node_134_136_parts : List (List Char) := assertHeader_parts_leaf134 ++ assertHeader_parts_leaf135
theorem assertHeader_node_134_136_parts_literal : assertHeader_node_134_136_parts = [assertHeader_chunk134, assertHeader_chunk135] := by
  unfold assertHeader_node_134_136_parts
  rfl
theorem assertHeader_node_134_136_parts_flatten : assertHeader_node_134_136_chars = assertHeader_node_134_136_parts.flatten := by
  unfold assertHeader_node_134_136_chars assertHeader_node_134_136_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf134_flatten, ← assertHeader_parts_leaf135_flatten]
def assertHeader_node_132_136 : String := assertHeader_node_132_134 ++ assertHeader_node_134_136
def assertHeader_node_132_136_chars : List Char := assertHeader_node_132_134_chars ++ assertHeader_node_134_136_chars
theorem assertHeader_node_132_136_literal : assertHeader_node_132_136 = "&& __STDC_VERSION__ >= 201112L\n#" := by
  unfold assertHeader_node_132_136
  rw [assertHeader_node_132_134_literal]
  rw [assertHeader_node_134_136_literal]
  cbv
theorem assertHeader_node_132_136_characters : assertHeader_node_132_136.toList = assertHeader_node_132_136_chars := by
  unfold assertHeader_node_132_136 assertHeader_node_132_136_chars
  rw [String.toList_append, assertHeader_node_132_134_characters, assertHeader_node_134_136_characters]
def assertHeader_node_132_136_parts : List (List Char) := assertHeader_node_132_134_parts ++ assertHeader_node_134_136_parts
theorem assertHeader_node_132_136_parts_literal : assertHeader_node_132_136_parts = [assertHeader_chunk132, assertHeader_chunk133, assertHeader_chunk134, assertHeader_chunk135] := by
  unfold assertHeader_node_132_136_parts
  rw [assertHeader_node_132_134_parts_literal]
  rw [assertHeader_node_134_136_parts_literal]
  rfl
theorem assertHeader_node_132_136_parts_flatten : assertHeader_node_132_136_chars = assertHeader_node_132_136_parts.flatten := by
  unfold assertHeader_node_132_136_chars assertHeader_node_132_136_parts
  rw [List.flatten_append, ← assertHeader_node_132_134_parts_flatten, ← assertHeader_node_134_136_parts_flatten]
def assertHeader_parts_leaf136 : List (List Char) := [assertHeader_chunk136]
theorem assertHeader_parts_leaf136_flatten : assertHeader_chunk136 = assertHeader_parts_leaf136.flatten := by
  simp only [assertHeader_parts_leaf136, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf137 : List (List Char) := [assertHeader_chunk137]
theorem assertHeader_parts_leaf137_flatten : assertHeader_chunk137 = assertHeader_parts_leaf137.flatten := by
  simp only [assertHeader_parts_leaf137, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_136_138 : String := assertHeader_string_leaf136 ++ assertHeader_string_leaf137
def assertHeader_node_136_138_chars : List Char := assertHeader_chunk136 ++ assertHeader_chunk137
theorem assertHeader_node_136_138_literal : assertHeader_node_136_138 = "define static_as" := by
  unfold assertHeader_node_136_138
  cbv
theorem assertHeader_node_136_138_characters : assertHeader_node_136_138.toList = assertHeader_node_136_138_chars := by
  unfold assertHeader_node_136_138 assertHeader_node_136_138_chars
  rw [String.toList_append, assertHeader_chunk_chars136, assertHeader_chunk_chars137]
def assertHeader_node_136_138_parts : List (List Char) := assertHeader_parts_leaf136 ++ assertHeader_parts_leaf137
theorem assertHeader_node_136_138_parts_literal : assertHeader_node_136_138_parts = [assertHeader_chunk136, assertHeader_chunk137] := by
  unfold assertHeader_node_136_138_parts
  rfl
theorem assertHeader_node_136_138_parts_flatten : assertHeader_node_136_138_chars = assertHeader_node_136_138_parts.flatten := by
  unfold assertHeader_node_136_138_chars assertHeader_node_136_138_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf136_flatten, ← assertHeader_parts_leaf137_flatten]
def assertHeader_parts_leaf138 : List (List Char) := [assertHeader_chunk138]
theorem assertHeader_parts_leaf138_flatten : assertHeader_chunk138 = assertHeader_parts_leaf138.flatten := by
  simp only [assertHeader_parts_leaf138, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf139 : List (List Char) := [assertHeader_chunk139]
theorem assertHeader_parts_leaf139_flatten : assertHeader_chunk139 = assertHeader_parts_leaf139.flatten := by
  simp only [assertHeader_parts_leaf139, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf140 : List (List Char) := [assertHeader_chunk140]
theorem assertHeader_parts_leaf140_flatten : assertHeader_chunk140 = assertHeader_parts_leaf140.flatten := by
  simp only [assertHeader_parts_leaf140, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_139_141 : String := assertHeader_string_leaf139 ++ assertHeader_string_leaf140
def assertHeader_node_139_141_chars : List Char := assertHeader_chunk139 ++ assertHeader_chunk140
theorem assertHeader_node_139_141_literal : assertHeader_node_139_141 = "atic_assert\n#end" := by
  unfold assertHeader_node_139_141
  cbv
theorem assertHeader_node_139_141_characters : assertHeader_node_139_141.toList = assertHeader_node_139_141_chars := by
  unfold assertHeader_node_139_141 assertHeader_node_139_141_chars
  rw [String.toList_append, assertHeader_chunk_chars139, assertHeader_chunk_chars140]
def assertHeader_node_139_141_parts : List (List Char) := assertHeader_parts_leaf139 ++ assertHeader_parts_leaf140
theorem assertHeader_node_139_141_parts_literal : assertHeader_node_139_141_parts = [assertHeader_chunk139, assertHeader_chunk140] := by
  unfold assertHeader_node_139_141_parts
  rfl
theorem assertHeader_node_139_141_parts_flatten : assertHeader_node_139_141_chars = assertHeader_node_139_141_parts.flatten := by
  unfold assertHeader_node_139_141_chars assertHeader_node_139_141_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf139_flatten, ← assertHeader_parts_leaf140_flatten]
def assertHeader_node_138_141 : String := assertHeader_string_leaf138 ++ assertHeader_node_139_141
def assertHeader_node_138_141_chars : List Char := assertHeader_chunk138 ++ assertHeader_node_139_141_chars
theorem assertHeader_node_138_141_literal : assertHeader_node_138_141 = "sert _Static_assert\n#end" := by
  unfold assertHeader_node_138_141
  rw [assertHeader_node_139_141_literal]
  cbv
theorem assertHeader_node_138_141_characters : assertHeader_node_138_141.toList = assertHeader_node_138_141_chars := by
  unfold assertHeader_node_138_141 assertHeader_node_138_141_chars
  rw [String.toList_append, assertHeader_chunk_chars138, assertHeader_node_139_141_characters]
def assertHeader_node_138_141_parts : List (List Char) := assertHeader_parts_leaf138 ++ assertHeader_node_139_141_parts
theorem assertHeader_node_138_141_parts_literal : assertHeader_node_138_141_parts = [assertHeader_chunk138, assertHeader_chunk139, assertHeader_chunk140] := by
  unfold assertHeader_node_138_141_parts
  rw [assertHeader_node_139_141_parts_literal]
  rfl
theorem assertHeader_node_138_141_parts_flatten : assertHeader_node_138_141_chars = assertHeader_node_138_141_parts.flatten := by
  unfold assertHeader_node_138_141_chars assertHeader_node_138_141_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf138_flatten, ← assertHeader_node_139_141_parts_flatten]
def assertHeader_node_136_141 : String := assertHeader_node_136_138 ++ assertHeader_node_138_141
def assertHeader_node_136_141_chars : List Char := assertHeader_node_136_138_chars ++ assertHeader_node_138_141_chars
theorem assertHeader_node_136_141_literal : assertHeader_node_136_141 = "define static_assert _Static_assert\n#end" := by
  unfold assertHeader_node_136_141
  rw [assertHeader_node_136_138_literal]
  rw [assertHeader_node_138_141_literal]
  cbv
theorem assertHeader_node_136_141_characters : assertHeader_node_136_141.toList = assertHeader_node_136_141_chars := by
  unfold assertHeader_node_136_141 assertHeader_node_136_141_chars
  rw [String.toList_append, assertHeader_node_136_138_characters, assertHeader_node_138_141_characters]
def assertHeader_node_136_141_parts : List (List Char) := assertHeader_node_136_138_parts ++ assertHeader_node_138_141_parts
theorem assertHeader_node_136_141_parts_literal : assertHeader_node_136_141_parts = [assertHeader_chunk136, assertHeader_chunk137, assertHeader_chunk138, assertHeader_chunk139, assertHeader_chunk140] := by
  unfold assertHeader_node_136_141_parts
  rw [assertHeader_node_136_138_parts_literal]
  rw [assertHeader_node_138_141_parts_literal]
  rfl
theorem assertHeader_node_136_141_parts_flatten : assertHeader_node_136_141_chars = assertHeader_node_136_141_parts.flatten := by
  unfold assertHeader_node_136_141_chars assertHeader_node_136_141_parts
  rw [List.flatten_append, ← assertHeader_node_136_138_parts_flatten, ← assertHeader_node_138_141_parts_flatten]
def assertHeader_node_132_141 : String := assertHeader_node_132_136 ++ assertHeader_node_136_141
def assertHeader_node_132_141_chars : List Char := assertHeader_node_132_136_chars ++ assertHeader_node_136_141_chars
theorem assertHeader_node_132_141_literal : assertHeader_node_132_141 = "&& __STDC_VERSION__ >= 201112L\n#define static_assert _Static_assert\n#end" := by
  unfold assertHeader_node_132_141
  rw [assertHeader_node_132_136_literal]
  rw [assertHeader_node_136_141_literal]
  cbv
theorem assertHeader_node_132_141_characters : assertHeader_node_132_141.toList = assertHeader_node_132_141_chars := by
  unfold assertHeader_node_132_141 assertHeader_node_132_141_chars
  rw [String.toList_append, assertHeader_node_132_136_characters, assertHeader_node_136_141_characters]
def assertHeader_node_132_141_parts : List (List Char) := assertHeader_node_132_136_parts ++ assertHeader_node_136_141_parts
theorem assertHeader_node_132_141_parts_literal : assertHeader_node_132_141_parts = [assertHeader_chunk132, assertHeader_chunk133, assertHeader_chunk134, assertHeader_chunk135, assertHeader_chunk136, assertHeader_chunk137, assertHeader_chunk138, assertHeader_chunk139, assertHeader_chunk140] := by
  unfold assertHeader_node_132_141_parts
  rw [assertHeader_node_132_136_parts_literal]
  rw [assertHeader_node_136_141_parts_literal]
  rfl
theorem assertHeader_node_132_141_parts_flatten : assertHeader_node_132_141_chars = assertHeader_node_132_141_parts.flatten := by
  unfold assertHeader_node_132_141_chars assertHeader_node_132_141_parts
  rw [List.flatten_append, ← assertHeader_node_132_136_parts_flatten, ← assertHeader_node_136_141_parts_flatten]
def assertHeader_parts_leaf141 : List (List Char) := [assertHeader_chunk141]
theorem assertHeader_parts_leaf141_flatten : assertHeader_chunk141 = assertHeader_parts_leaf141.flatten := by
  simp only [assertHeader_parts_leaf141, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf142 : List (List Char) := [assertHeader_chunk142]
theorem assertHeader_parts_leaf142_flatten : assertHeader_chunk142 = assertHeader_parts_leaf142.flatten := by
  simp only [assertHeader_parts_leaf142, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_141_143 : String := assertHeader_string_leaf141 ++ assertHeader_string_leaf142
def assertHeader_node_141_143_chars : List Char := assertHeader_chunk141 ++ assertHeader_chunk142
theorem assertHeader_node_141_143_literal : assertHeader_node_141_143 = "if /* __STDC_VER" := by
  unfold assertHeader_node_141_143
  cbv
theorem assertHeader_node_141_143_characters : assertHeader_node_141_143.toList = assertHeader_node_141_143_chars := by
  unfold assertHeader_node_141_143 assertHeader_node_141_143_chars
  rw [String.toList_append, assertHeader_chunk_chars141, assertHeader_chunk_chars142]
def assertHeader_node_141_143_parts : List (List Char) := assertHeader_parts_leaf141 ++ assertHeader_parts_leaf142
theorem assertHeader_node_141_143_parts_literal : assertHeader_node_141_143_parts = [assertHeader_chunk141, assertHeader_chunk142] := by
  unfold assertHeader_node_141_143_parts
  rfl
theorem assertHeader_node_141_143_parts_flatten : assertHeader_node_141_143_chars = assertHeader_node_141_143_parts.flatten := by
  unfold assertHeader_node_141_143_chars assertHeader_node_141_143_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf141_flatten, ← assertHeader_parts_leaf142_flatten]
def assertHeader_parts_leaf143 : List (List Char) := [assertHeader_chunk143]
theorem assertHeader_parts_leaf143_flatten : assertHeader_chunk143 = assertHeader_parts_leaf143.flatten := by
  simp only [assertHeader_parts_leaf143, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf144 : List (List Char) := [assertHeader_chunk144]
theorem assertHeader_parts_leaf144_flatten : assertHeader_chunk144 = assertHeader_parts_leaf144.flatten := by
  simp only [assertHeader_parts_leaf144, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf145 : List (List Char) := [assertHeader_chunk145]
theorem assertHeader_parts_leaf145_flatten : assertHeader_chunk145 = assertHeader_parts_leaf145.flatten := by
  simp only [assertHeader_parts_leaf145, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_144_146 : String := assertHeader_string_leaf144 ++ assertHeader_string_leaf145
def assertHeader_node_144_146_chars : List Char := assertHeader_chunk144 ++ assertHeader_chunk145
theorem assertHeader_node_144_146_literal : assertHeader_node_144_146 = "/\n#endif /* !__c" := by
  unfold assertHeader_node_144_146
  cbv
theorem assertHeader_node_144_146_characters : assertHeader_node_144_146.toList = assertHeader_node_144_146_chars := by
  unfold assertHeader_node_144_146 assertHeader_node_144_146_chars
  rw [String.toList_append, assertHeader_chunk_chars144, assertHeader_chunk_chars145]
def assertHeader_node_144_146_parts : List (List Char) := assertHeader_parts_leaf144 ++ assertHeader_parts_leaf145
theorem assertHeader_node_144_146_parts_literal : assertHeader_node_144_146_parts = [assertHeader_chunk144, assertHeader_chunk145] := by
  unfold assertHeader_node_144_146_parts
  rfl
theorem assertHeader_node_144_146_parts_flatten : assertHeader_node_144_146_chars = assertHeader_node_144_146_parts.flatten := by
  unfold assertHeader_node_144_146_chars assertHeader_node_144_146_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf144_flatten, ← assertHeader_parts_leaf145_flatten]
def assertHeader_node_143_146 : String := assertHeader_string_leaf143 ++ assertHeader_node_144_146
def assertHeader_node_143_146_chars : List Char := assertHeader_chunk143 ++ assertHeader_node_144_146_chars
theorem assertHeader_node_143_146_literal : assertHeader_node_143_146 = "SION__ */\n#endif /* !__c" := by
  unfold assertHeader_node_143_146
  rw [assertHeader_node_144_146_literal]
  cbv
theorem assertHeader_node_143_146_characters : assertHeader_node_143_146.toList = assertHeader_node_143_146_chars := by
  unfold assertHeader_node_143_146 assertHeader_node_143_146_chars
  rw [String.toList_append, assertHeader_chunk_chars143, assertHeader_node_144_146_characters]
def assertHeader_node_143_146_parts : List (List Char) := assertHeader_parts_leaf143 ++ assertHeader_node_144_146_parts
theorem assertHeader_node_143_146_parts_literal : assertHeader_node_143_146_parts = [assertHeader_chunk143, assertHeader_chunk144, assertHeader_chunk145] := by
  unfold assertHeader_node_143_146_parts
  rw [assertHeader_node_144_146_parts_literal]
  rfl
theorem assertHeader_node_143_146_parts_flatten : assertHeader_node_143_146_chars = assertHeader_node_143_146_parts.flatten := by
  unfold assertHeader_node_143_146_chars assertHeader_node_143_146_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf143_flatten, ← assertHeader_node_144_146_parts_flatten]
def assertHeader_node_141_146 : String := assertHeader_node_141_143 ++ assertHeader_node_143_146
def assertHeader_node_141_146_chars : List Char := assertHeader_node_141_143_chars ++ assertHeader_node_143_146_chars
theorem assertHeader_node_141_146_literal : assertHeader_node_141_146 = "if /* __STDC_VERSION__ */\n#endif /* !__c" := by
  unfold assertHeader_node_141_146
  rw [assertHeader_node_141_143_literal]
  rw [assertHeader_node_143_146_literal]
  cbv
theorem assertHeader_node_141_146_characters : assertHeader_node_141_146.toList = assertHeader_node_141_146_chars := by
  unfold assertHeader_node_141_146 assertHeader_node_141_146_chars
  rw [String.toList_append, assertHeader_node_141_143_characters, assertHeader_node_143_146_characters]
def assertHeader_node_141_146_parts : List (List Char) := assertHeader_node_141_143_parts ++ assertHeader_node_143_146_parts
theorem assertHeader_node_141_146_parts_literal : assertHeader_node_141_146_parts = [assertHeader_chunk141, assertHeader_chunk142, assertHeader_chunk143, assertHeader_chunk144, assertHeader_chunk145] := by
  unfold assertHeader_node_141_146_parts
  rw [assertHeader_node_141_143_parts_literal]
  rw [assertHeader_node_143_146_parts_literal]
  rfl
theorem assertHeader_node_141_146_parts_flatten : assertHeader_node_141_146_chars = assertHeader_node_141_146_parts.flatten := by
  unfold assertHeader_node_141_146_chars assertHeader_node_141_146_parts
  rw [List.flatten_append, ← assertHeader_node_141_143_parts_flatten, ← assertHeader_node_143_146_parts_flatten]
def assertHeader_parts_leaf146 : List (List Char) := [assertHeader_chunk146]
theorem assertHeader_parts_leaf146_flatten : assertHeader_chunk146 = assertHeader_parts_leaf146.flatten := by
  simp only [assertHeader_parts_leaf146, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf147 : List (List Char) := [assertHeader_chunk147]
theorem assertHeader_parts_leaf147_flatten : assertHeader_chunk147 = assertHeader_parts_leaf147.flatten := by
  simp only [assertHeader_parts_leaf147, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_146_148 : String := assertHeader_string_leaf146 ++ assertHeader_string_leaf147
def assertHeader_node_146_148_chars : List Char := assertHeader_chunk146 ++ assertHeader_chunk147
theorem assertHeader_node_146_148_literal : assertHeader_node_146_148 = "plusplus */\n\n#en" := by
  unfold assertHeader_node_146_148
  cbv
theorem assertHeader_node_146_148_characters : assertHeader_node_146_148.toList = assertHeader_node_146_148_chars := by
  unfold assertHeader_node_146_148 assertHeader_node_146_148_chars
  rw [String.toList_append, assertHeader_chunk_chars146, assertHeader_chunk_chars147]
def assertHeader_node_146_148_parts : List (List Char) := assertHeader_parts_leaf146 ++ assertHeader_parts_leaf147
theorem assertHeader_node_146_148_parts_literal : assertHeader_node_146_148_parts = [assertHeader_chunk146, assertHeader_chunk147] := by
  unfold assertHeader_node_146_148_parts
  rfl
theorem assertHeader_node_146_148_parts_flatten : assertHeader_node_146_148_chars = assertHeader_node_146_148_parts.flatten := by
  unfold assertHeader_node_146_148_chars assertHeader_node_146_148_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf146_flatten, ← assertHeader_parts_leaf147_flatten]
def assertHeader_parts_leaf148 : List (List Char) := [assertHeader_chunk148]
theorem assertHeader_parts_leaf148_flatten : assertHeader_chunk148 = assertHeader_parts_leaf148.flatten := by
  simp only [assertHeader_parts_leaf148, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf149 : List (List Char) := [assertHeader_chunk149]
theorem assertHeader_parts_leaf149_flatten : assertHeader_chunk149 = assertHeader_parts_leaf149.flatten := by
  simp only [assertHeader_parts_leaf149, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_parts_leaf150 : List (List Char) := [assertHeader_chunk150]
theorem assertHeader_parts_leaf150_flatten : assertHeader_chunk150 = assertHeader_parts_leaf150.flatten := by
  simp only [assertHeader_parts_leaf150, List.flatten_cons, List.flatten_nil, List.append_nil]
def assertHeader_node_149_151 : String := assertHeader_string_leaf149 ++ assertHeader_string_leaf150
def assertHeader_node_149_151_chars : List Char := assertHeader_chunk149 ++ assertHeader_chunk150
theorem assertHeader_node_149_151_literal : assertHeader_node_149_151 = "ASSERT_H_ */\n" := by
  unfold assertHeader_node_149_151
  cbv
theorem assertHeader_node_149_151_characters : assertHeader_node_149_151.toList = assertHeader_node_149_151_chars := by
  unfold assertHeader_node_149_151 assertHeader_node_149_151_chars
  rw [String.toList_append, assertHeader_chunk_chars149, assertHeader_chunk_chars150]
def assertHeader_node_149_151_parts : List (List Char) := assertHeader_parts_leaf149 ++ assertHeader_parts_leaf150
theorem assertHeader_node_149_151_parts_literal : assertHeader_node_149_151_parts = [assertHeader_chunk149, assertHeader_chunk150] := by
  unfold assertHeader_node_149_151_parts
  rfl
theorem assertHeader_node_149_151_parts_flatten : assertHeader_node_149_151_chars = assertHeader_node_149_151_parts.flatten := by
  unfold assertHeader_node_149_151_chars assertHeader_node_149_151_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf149_flatten, ← assertHeader_parts_leaf150_flatten]
def assertHeader_node_148_151 : String := assertHeader_string_leaf148 ++ assertHeader_node_149_151
def assertHeader_node_148_151_chars : List Char := assertHeader_chunk148 ++ assertHeader_node_149_151_chars
theorem assertHeader_node_148_151_literal : assertHeader_node_148_151 = "dif /* _ASSERT_H_ */\n" := by
  unfold assertHeader_node_148_151
  rw [assertHeader_node_149_151_literal]
  cbv
theorem assertHeader_node_148_151_characters : assertHeader_node_148_151.toList = assertHeader_node_148_151_chars := by
  unfold assertHeader_node_148_151 assertHeader_node_148_151_chars
  rw [String.toList_append, assertHeader_chunk_chars148, assertHeader_node_149_151_characters]
def assertHeader_node_148_151_parts : List (List Char) := assertHeader_parts_leaf148 ++ assertHeader_node_149_151_parts
theorem assertHeader_node_148_151_parts_literal : assertHeader_node_148_151_parts = [assertHeader_chunk148, assertHeader_chunk149, assertHeader_chunk150] := by
  unfold assertHeader_node_148_151_parts
  rw [assertHeader_node_149_151_parts_literal]
  rfl
theorem assertHeader_node_148_151_parts_flatten : assertHeader_node_148_151_chars = assertHeader_node_148_151_parts.flatten := by
  unfold assertHeader_node_148_151_chars assertHeader_node_148_151_parts
  rw [List.flatten_append, ← assertHeader_parts_leaf148_flatten, ← assertHeader_node_149_151_parts_flatten]
def assertHeader_node_146_151 : String := assertHeader_node_146_148 ++ assertHeader_node_148_151
def assertHeader_node_146_151_chars : List Char := assertHeader_node_146_148_chars ++ assertHeader_node_148_151_chars
theorem assertHeader_node_146_151_literal : assertHeader_node_146_151 = "plusplus */\n\n#endif /* _ASSERT_H_ */\n" := by
  unfold assertHeader_node_146_151
  rw [assertHeader_node_146_148_literal]
  rw [assertHeader_node_148_151_literal]
  cbv
theorem assertHeader_node_146_151_characters : assertHeader_node_146_151.toList = assertHeader_node_146_151_chars := by
  unfold assertHeader_node_146_151 assertHeader_node_146_151_chars
  rw [String.toList_append, assertHeader_node_146_148_characters, assertHeader_node_148_151_characters]
def assertHeader_node_146_151_parts : List (List Char) := assertHeader_node_146_148_parts ++ assertHeader_node_148_151_parts
theorem assertHeader_node_146_151_parts_literal : assertHeader_node_146_151_parts = [assertHeader_chunk146, assertHeader_chunk147, assertHeader_chunk148, assertHeader_chunk149, assertHeader_chunk150] := by
  unfold assertHeader_node_146_151_parts
  rw [assertHeader_node_146_148_parts_literal]
  rw [assertHeader_node_148_151_parts_literal]
  rfl
theorem assertHeader_node_146_151_parts_flatten : assertHeader_node_146_151_chars = assertHeader_node_146_151_parts.flatten := by
  unfold assertHeader_node_146_151_chars assertHeader_node_146_151_parts
  rw [List.flatten_append, ← assertHeader_node_146_148_parts_flatten, ← assertHeader_node_148_151_parts_flatten]
def assertHeader_node_141_151 : String := assertHeader_node_141_146 ++ assertHeader_node_146_151
def assertHeader_node_141_151_chars : List Char := assertHeader_node_141_146_chars ++ assertHeader_node_146_151_chars
theorem assertHeader_node_141_151_literal : assertHeader_node_141_151 = "if /* __STDC_VERSION__ */\n#endif /* !__cplusplus */\n\n#endif /* _ASSERT_H_ */\n" := by
  unfold assertHeader_node_141_151
  rw [assertHeader_node_141_146_literal]
  rw [assertHeader_node_146_151_literal]
  cbv
theorem assertHeader_node_141_151_characters : assertHeader_node_141_151.toList = assertHeader_node_141_151_chars := by
  unfold assertHeader_node_141_151 assertHeader_node_141_151_chars
  rw [String.toList_append, assertHeader_node_141_146_characters, assertHeader_node_146_151_characters]
def assertHeader_node_141_151_parts : List (List Char) := assertHeader_node_141_146_parts ++ assertHeader_node_146_151_parts
theorem assertHeader_node_141_151_parts_literal : assertHeader_node_141_151_parts = [assertHeader_chunk141, assertHeader_chunk142, assertHeader_chunk143, assertHeader_chunk144, assertHeader_chunk145, assertHeader_chunk146, assertHeader_chunk147, assertHeader_chunk148, assertHeader_chunk149, assertHeader_chunk150] := by
  unfold assertHeader_node_141_151_parts
  rw [assertHeader_node_141_146_parts_literal]
  rw [assertHeader_node_146_151_parts_literal]
  rfl
theorem assertHeader_node_141_151_parts_flatten : assertHeader_node_141_151_chars = assertHeader_node_141_151_parts.flatten := by
  unfold assertHeader_node_141_151_chars assertHeader_node_141_151_parts
  rw [List.flatten_append, ← assertHeader_node_141_146_parts_flatten, ← assertHeader_node_146_151_parts_flatten]
def assertHeader_node_132_151 : String := assertHeader_node_132_141 ++ assertHeader_node_141_151
def assertHeader_node_132_151_chars : List Char := assertHeader_node_132_141_chars ++ assertHeader_node_141_151_chars
theorem assertHeader_node_132_151_literal : assertHeader_node_132_151 = "&& __STDC_VERSION__ >= 201112L\n#define static_assert _Static_assert\n#endif /* __STDC_VERSION__ */\n#endif /* !__cplusplus */\n\n#endif /* _ASSERT_H_ */\n" := by
  unfold assertHeader_node_132_151
  rw [assertHeader_node_132_141_literal]
  rw [assertHeader_node_141_151_literal]
  cbv
theorem assertHeader_node_132_151_characters : assertHeader_node_132_151.toList = assertHeader_node_132_151_chars := by
  unfold assertHeader_node_132_151 assertHeader_node_132_151_chars
  rw [String.toList_append, assertHeader_node_132_141_characters, assertHeader_node_141_151_characters]
def assertHeader_node_132_151_parts : List (List Char) := assertHeader_node_132_141_parts ++ assertHeader_node_141_151_parts
theorem assertHeader_node_132_151_parts_literal : assertHeader_node_132_151_parts = [assertHeader_chunk132, assertHeader_chunk133, assertHeader_chunk134, assertHeader_chunk135, assertHeader_chunk136, assertHeader_chunk137, assertHeader_chunk138, assertHeader_chunk139, assertHeader_chunk140, assertHeader_chunk141, assertHeader_chunk142, assertHeader_chunk143, assertHeader_chunk144, assertHeader_chunk145, assertHeader_chunk146, assertHeader_chunk147, assertHeader_chunk148, assertHeader_chunk149, assertHeader_chunk150] := by
  unfold assertHeader_node_132_151_parts
  rw [assertHeader_node_132_141_parts_literal]
  rw [assertHeader_node_141_151_parts_literal]
  rfl
theorem assertHeader_node_132_151_parts_flatten : assertHeader_node_132_151_chars = assertHeader_node_132_151_parts.flatten := by
  unfold assertHeader_node_132_151_chars assertHeader_node_132_151_parts
  rw [List.flatten_append, ← assertHeader_node_132_141_parts_flatten, ← assertHeader_node_141_151_parts_flatten]
def assertHeader_node_113_151 : String := assertHeader_node_113_132 ++ assertHeader_node_132_151
def assertHeader_node_113_151_chars : List Char := assertHeader_node_113_132_chars ++ assertHeader_node_132_151_chars
theorem assertHeader_node_113_151_literal : assertHeader_node_113_151 = "tions under the License.\n *\n * @APPLE_LICENSE_HEADER_END@\n */\n\n#ifndef _ASSERT_H_\n#define _ASSERT_H_\n\n#ifndef __cplusplus\n#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L\n#define static_assert _Static_assert\n#endif /* __STDC_VERSION__ */\n#endif /* !__cplusplus */\n\n#endif /* _ASSERT_H_ */\n" := by
  unfold assertHeader_node_113_151
  rw [assertHeader_node_113_132_literal]
  rw [assertHeader_node_132_151_literal]
  cbv
theorem assertHeader_node_113_151_characters : assertHeader_node_113_151.toList = assertHeader_node_113_151_chars := by
  unfold assertHeader_node_113_151 assertHeader_node_113_151_chars
  rw [String.toList_append, assertHeader_node_113_132_characters, assertHeader_node_132_151_characters]
def assertHeader_node_113_151_parts : List (List Char) := assertHeader_node_113_132_parts ++ assertHeader_node_132_151_parts
theorem assertHeader_node_113_151_parts_literal : assertHeader_node_113_151_parts = [assertHeader_chunk113, assertHeader_chunk114, assertHeader_chunk115, assertHeader_chunk116, assertHeader_chunk117, assertHeader_chunk118, assertHeader_chunk119, assertHeader_chunk120, assertHeader_chunk121, assertHeader_chunk122, assertHeader_chunk123, assertHeader_chunk124, assertHeader_chunk125, assertHeader_chunk126, assertHeader_chunk127, assertHeader_chunk128, assertHeader_chunk129, assertHeader_chunk130, assertHeader_chunk131, assertHeader_chunk132, assertHeader_chunk133, assertHeader_chunk134, assertHeader_chunk135, assertHeader_chunk136, assertHeader_chunk137, assertHeader_chunk138, assertHeader_chunk139, assertHeader_chunk140, assertHeader_chunk141, assertHeader_chunk142, assertHeader_chunk143, assertHeader_chunk144, assertHeader_chunk145, assertHeader_chunk146, assertHeader_chunk147, assertHeader_chunk148, assertHeader_chunk149, assertHeader_chunk150] := by
  unfold assertHeader_node_113_151_parts
  rw [assertHeader_node_113_132_parts_literal]
  rw [assertHeader_node_132_151_parts_literal]
  rfl
theorem assertHeader_node_113_151_parts_flatten : assertHeader_node_113_151_chars = assertHeader_node_113_151_parts.flatten := by
  unfold assertHeader_node_113_151_chars assertHeader_node_113_151_parts
  rw [List.flatten_append, ← assertHeader_node_113_132_parts_flatten, ← assertHeader_node_132_151_parts_flatten]
def assertHeader_node_75_151 : String := assertHeader_node_75_113 ++ assertHeader_node_113_151
def assertHeader_node_75_151_chars : List Char := assertHeader_node_75_113_chars ++ assertHeader_node_113_151_chars
theorem assertHeader_node_75_151_literal : assertHeader_node_75_151 = ", EITHER\n * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,\n * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,\n * FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.\n * Please see the License for the specific language governing rights and\n * limitations under the License.\n *\n * @APPLE_LICENSE_HEADER_END@\n */\n\n#ifndef _ASSERT_H_\n#define _ASSERT_H_\n\n#ifndef __cplusplus\n#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L\n#define static_assert _Static_assert\n#endif /* __STDC_VERSION__ */\n#endif /* !__cplusplus */\n\n#endif /* _ASSERT_H_ */\n" := by
  unfold assertHeader_node_75_151
  rw [assertHeader_node_75_113_literal]
  rw [assertHeader_node_113_151_literal]
  cbv
theorem assertHeader_node_75_151_characters : assertHeader_node_75_151.toList = assertHeader_node_75_151_chars := by
  unfold assertHeader_node_75_151 assertHeader_node_75_151_chars
  rw [String.toList_append, assertHeader_node_75_113_characters, assertHeader_node_113_151_characters]
def assertHeader_node_75_151_parts : List (List Char) := assertHeader_node_75_113_parts ++ assertHeader_node_113_151_parts
theorem assertHeader_node_75_151_parts_literal : assertHeader_node_75_151_parts = [assertHeader_chunk75, assertHeader_chunk76, assertHeader_chunk77, assertHeader_chunk78, assertHeader_chunk79, assertHeader_chunk80, assertHeader_chunk81, assertHeader_chunk82, assertHeader_chunk83, assertHeader_chunk84, assertHeader_chunk85, assertHeader_chunk86, assertHeader_chunk87, assertHeader_chunk88, assertHeader_chunk89, assertHeader_chunk90, assertHeader_chunk91, assertHeader_chunk92, assertHeader_chunk93, assertHeader_chunk94, assertHeader_chunk95, assertHeader_chunk96, assertHeader_chunk97, assertHeader_chunk98, assertHeader_chunk99, assertHeader_chunk100, assertHeader_chunk101, assertHeader_chunk102, assertHeader_chunk103, assertHeader_chunk104, assertHeader_chunk105, assertHeader_chunk106, assertHeader_chunk107, assertHeader_chunk108, assertHeader_chunk109, assertHeader_chunk110, assertHeader_chunk111, assertHeader_chunk112, assertHeader_chunk113, assertHeader_chunk114, assertHeader_chunk115, assertHeader_chunk116, assertHeader_chunk117, assertHeader_chunk118, assertHeader_chunk119, assertHeader_chunk120, assertHeader_chunk121, assertHeader_chunk122, assertHeader_chunk123, assertHeader_chunk124, assertHeader_chunk125, assertHeader_chunk126, assertHeader_chunk127, assertHeader_chunk128, assertHeader_chunk129, assertHeader_chunk130, assertHeader_chunk131, assertHeader_chunk132, assertHeader_chunk133, assertHeader_chunk134, assertHeader_chunk135, assertHeader_chunk136, assertHeader_chunk137, assertHeader_chunk138, assertHeader_chunk139, assertHeader_chunk140, assertHeader_chunk141, assertHeader_chunk142, assertHeader_chunk143, assertHeader_chunk144, assertHeader_chunk145, assertHeader_chunk146, assertHeader_chunk147, assertHeader_chunk148, assertHeader_chunk149, assertHeader_chunk150] := by
  unfold assertHeader_node_75_151_parts
  rw [assertHeader_node_75_113_parts_literal]
  rw [assertHeader_node_113_151_parts_literal]
  rfl
theorem assertHeader_node_75_151_parts_flatten : assertHeader_node_75_151_chars = assertHeader_node_75_151_parts.flatten := by
  unfold assertHeader_node_75_151_chars assertHeader_node_75_151_parts
  rw [List.flatten_append, ← assertHeader_node_75_113_parts_flatten, ← assertHeader_node_113_151_parts_flatten]
def assertHeader_node_0_151 : String := assertHeader_node_0_75 ++ assertHeader_node_75_151
def assertHeader_node_0_151_chars : List Char := assertHeader_node_0_75_chars ++ assertHeader_node_75_151_chars
theorem assertHeader_node_0_151_literal : assertHeader_node_0_151 = "/*\n * Copyright (c) 2023 Apple Inc. All rights reserved.\n *\n * @APPLE_LICENSE_HEADER_START@\n *\n * This file contains Original Code and/or Modifications of Original Code\n * as defined in and that are subject to the Apple Public Source License\n * Version 2.0 (the 'License'). You may not use this file except in\n * compliance with the License. Please obtain a copy of the License at\n * http://www.opensource.apple.com/apsl/ and read it before using this\n * file.\n *\n * The Original Code and all software distributed under the License are\n * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER\n * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,\n * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,\n * FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.\n * Please see the License for the specific language governing rights and\n * limitations under the License.\n *\n * @APPLE_LICENSE_HEADER_END@\n */\n\n#ifndef _ASSERT_H_\n#define _ASSERT_H_\n\n#ifndef __cplusplus\n#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L\n#define static_assert _Static_assert\n#endif /* __STDC_VERSION__ */\n#endif /* !__cplusplus */\n\n#endif /* _ASSERT_H_ */\n" := by
  unfold assertHeader_node_0_151
  rw [assertHeader_node_0_75_literal]
  rw [assertHeader_node_75_151_literal]
  cbv
theorem assertHeader_node_0_151_characters : assertHeader_node_0_151.toList = assertHeader_node_0_151_chars := by
  unfold assertHeader_node_0_151 assertHeader_node_0_151_chars
  rw [String.toList_append, assertHeader_node_0_75_characters, assertHeader_node_75_151_characters]
def assertHeader_node_0_151_parts : List (List Char) := assertHeader_node_0_75_parts ++ assertHeader_node_75_151_parts
theorem assertHeader_node_0_151_parts_literal : assertHeader_node_0_151_parts = [assertHeader_chunk0, assertHeader_chunk1, assertHeader_chunk2, assertHeader_chunk3, assertHeader_chunk4, assertHeader_chunk5, assertHeader_chunk6, assertHeader_chunk7, assertHeader_chunk8, assertHeader_chunk9, assertHeader_chunk10, assertHeader_chunk11, assertHeader_chunk12, assertHeader_chunk13, assertHeader_chunk14, assertHeader_chunk15, assertHeader_chunk16, assertHeader_chunk17, assertHeader_chunk18, assertHeader_chunk19, assertHeader_chunk20, assertHeader_chunk21, assertHeader_chunk22, assertHeader_chunk23, assertHeader_chunk24, assertHeader_chunk25, assertHeader_chunk26, assertHeader_chunk27, assertHeader_chunk28, assertHeader_chunk29, assertHeader_chunk30, assertHeader_chunk31, assertHeader_chunk32, assertHeader_chunk33, assertHeader_chunk34, assertHeader_chunk35, assertHeader_chunk36, assertHeader_chunk37, assertHeader_chunk38, assertHeader_chunk39, assertHeader_chunk40, assertHeader_chunk41, assertHeader_chunk42, assertHeader_chunk43, assertHeader_chunk44, assertHeader_chunk45, assertHeader_chunk46, assertHeader_chunk47, assertHeader_chunk48, assertHeader_chunk49, assertHeader_chunk50, assertHeader_chunk51, assertHeader_chunk52, assertHeader_chunk53, assertHeader_chunk54, assertHeader_chunk55, assertHeader_chunk56, assertHeader_chunk57, assertHeader_chunk58, assertHeader_chunk59, assertHeader_chunk60, assertHeader_chunk61, assertHeader_chunk62, assertHeader_chunk63, assertHeader_chunk64, assertHeader_chunk65, assertHeader_chunk66, assertHeader_chunk67, assertHeader_chunk68, assertHeader_chunk69, assertHeader_chunk70, assertHeader_chunk71, assertHeader_chunk72, assertHeader_chunk73, assertHeader_chunk74, assertHeader_chunk75, assertHeader_chunk76, assertHeader_chunk77, assertHeader_chunk78, assertHeader_chunk79, assertHeader_chunk80, assertHeader_chunk81, assertHeader_chunk82, assertHeader_chunk83, assertHeader_chunk84, assertHeader_chunk85, assertHeader_chunk86, assertHeader_chunk87, assertHeader_chunk88, assertHeader_chunk89, assertHeader_chunk90, assertHeader_chunk91, assertHeader_chunk92, assertHeader_chunk93, assertHeader_chunk94, assertHeader_chunk95, assertHeader_chunk96, assertHeader_chunk97, assertHeader_chunk98, assertHeader_chunk99, assertHeader_chunk100, assertHeader_chunk101, assertHeader_chunk102, assertHeader_chunk103, assertHeader_chunk104, assertHeader_chunk105, assertHeader_chunk106, assertHeader_chunk107, assertHeader_chunk108, assertHeader_chunk109, assertHeader_chunk110, assertHeader_chunk111, assertHeader_chunk112, assertHeader_chunk113, assertHeader_chunk114, assertHeader_chunk115, assertHeader_chunk116, assertHeader_chunk117, assertHeader_chunk118, assertHeader_chunk119, assertHeader_chunk120, assertHeader_chunk121, assertHeader_chunk122, assertHeader_chunk123, assertHeader_chunk124, assertHeader_chunk125, assertHeader_chunk126, assertHeader_chunk127, assertHeader_chunk128, assertHeader_chunk129, assertHeader_chunk130, assertHeader_chunk131, assertHeader_chunk132, assertHeader_chunk133, assertHeader_chunk134, assertHeader_chunk135, assertHeader_chunk136, assertHeader_chunk137, assertHeader_chunk138, assertHeader_chunk139, assertHeader_chunk140, assertHeader_chunk141, assertHeader_chunk142, assertHeader_chunk143, assertHeader_chunk144, assertHeader_chunk145, assertHeader_chunk146, assertHeader_chunk147, assertHeader_chunk148, assertHeader_chunk149, assertHeader_chunk150] := by
  unfold assertHeader_node_0_151_parts
  rw [assertHeader_node_0_75_parts_literal]
  rw [assertHeader_node_75_151_parts_literal]
  rfl
theorem assertHeader_node_0_151_parts_flatten : assertHeader_node_0_151_chars = assertHeader_node_0_151_parts.flatten := by
  unfold assertHeader_node_0_151_chars assertHeader_node_0_151_parts
  rw [List.flatten_append, ← assertHeader_node_0_75_parts_flatten, ← assertHeader_node_75_151_parts_flatten]
theorem assertHeader_string_exact : assertHeader_node_0_151 = C11AssertHeaderData.assertHeader_0 := by
  exact assertHeader_node_0_151_literal
theorem assertHeader_flatten_exact : assertHeader_node_0_151_chars = assertHeader_chunks.flatten := by
  rw [assertHeader_node_0_151_parts_flatten, assertHeader_node_0_151_parts_literal]
  rfl
theorem assertHeader_source_lex : tokenize C11AssertHeaderData.assertHeader_0 = some assertHeader_tokens := by
  unfold tokenize
  rw [← assertHeader_string_exact, assertHeader_node_0_151_characters, assertHeader_flatten_exact]
  exact assertHeader_characters_lex

end C11AssertHeaderCuts
