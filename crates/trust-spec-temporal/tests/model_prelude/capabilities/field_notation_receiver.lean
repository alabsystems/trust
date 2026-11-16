-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- generalized field notation with a non-first receiver (`o.invs sp`); required pass.

namespace Trust
namespace Model

structure Spec where
  vars       : Nat
  invariants : List Nat

structure SafetyObl where
  atoms : List Nat

-- The receiver `o` is the second explicit argument.
def SafetyObl.invs (sp : Spec) (o : SafetyObl) : List Nat := sp.invariants ++ o.atoms

def sp1 : Spec := Spec.mk 1 [2]
def o1 : SafetyObl := SafetyObl.mk [3]

theorem field_notation_receiver : o1.invs sp1 = [2, 3] := rfl
theorem field_notation_receiver_door : Nat.beq (o1.invs sp1).length 2 = true := rfl

end Model
end Trust
