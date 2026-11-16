-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- a partially applied @List.rec without its major premise. Historically planned
-- to fail; the current measured row requires its exact partial recursor semantics.
-- This matrix measures Clean elaboration and checked theorems, not Lean codegen.

namespace Trust
namespace Model

def sumList : List Nat → Nat := @List.rec Nat (fun _ => Nat) 0 (fun h _ acc => h + acc)

theorem sum_door : Nat.beq (sumList [1, 2, 3]) 6 = true := rfl

theorem sum_nil : Nat.beq (sumList []) 0 = true := rfl
theorem sum_singleton : Nat.beq (sumList [4]) 4 = true := rfl
theorem sum_repeat : Nat.beq (sumList [2, 2]) 4 = true := rfl

end Model
end Trust
