-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- a mutual def whose members take two arguments. Historically planned to fail;
-- the current measured row requires checked ordinary definitions and equations.

namespace Trust
namespace Model

mutual
def sumE : Nat → List Nat → Nat
  | 0, _ => 0
  | n+1, xs => 1 + sumL n xs
def sumL : Nat → List Nat → Nat
  | 0, _ => 0
  | n+1, [] => 0
  | n+1, x :: xs => x + sumE n xs
end

theorem mutual_door : Nat.beq (sumE 20 [1, 2, 3]) 10 = true := rfl

theorem mutual_zero_e : Nat.beq (sumE 0 [3, 4]) 0 = true := rfl
theorem mutual_zero_l : Nat.beq (sumL 0 [3, 4]) 0 = true := rfl
theorem mutual_one_e : Nat.beq (sumE 1 [3, 4]) 1 = true := rfl
theorem mutual_one_l : Nat.beq (sumL 1 [3, 4]) 3 = true := rfl
theorem mutual_two_e : Nat.beq (sumE 2 [3, 4]) 4 = true := rfl
theorem mutual_empty_e : Nat.beq (sumE 20 []) 1 = true := rfl
theorem mutual_empty_l : Nat.beq (sumL 20 []) 0 = true := rfl
theorem mutual_cross_l : Nat.beq (sumL 20 [1, 2, 3]) 9 = true := rfl

end Model
end Trust
