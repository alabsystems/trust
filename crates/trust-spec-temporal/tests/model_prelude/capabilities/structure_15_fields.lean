-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- a 15-field structure (Spec, design 10:180-205) and its projections; required pass.

namespace Trust
namespace Model

inductive IntMode where
  | tlc32 | unbounded

inductive ChoiceMode where
  | none | uniformStates

structure Spec where
  vars              : Nat
  intMode           : IntMode
  tokens            : List String
  pool              : List Nat
  defs              : List (Nat × Nat)
  actDefs           : List (Nat × Nat)
  assumes           : List Nat
  init              : Nat
  next              : Nat
  fairness          : List Nat
  invariants        : List Nat
  constraints       : List Nat
  actionConstraints : List Nat
  checkDeadlock     : Bool
  choice            : ChoiceMode

def sp1 : Spec :=
  Spec.mk 3 IntMode.tlc32 ["a"] [1] [(0, 1)] [] [] 7 8 [] [4, 5] [] [6] true ChoiceMode.none

theorem structure_15_fields_door :
    Nat.beq (sp1.vars + sp1.init + sp1.next + sp1.invariants.length + sp1.actionConstraints.length
      + sp1.defs.length) 22 = true := rfl

theorem structure_15_fields_last : sp1.choice = ChoiceMode.none := rfl
theorem structure_15_fields_bool : sp1.checkDeadlock = true := rfl

end Model
end Trust
