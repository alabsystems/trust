-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- a _root_ extension of the finite-model vocabulary from inside Trust.Model; required pass.

namespace Trust
namespace Model

-- An extension of the finite-model vocabulary, written from inside Trust.Model.
def _root_.Trust.Temporal.FiniteModel.Model.actionCount
    (model : Trust.Temporal.FiniteModel.Model) : Nat :=
  model.actions.length

def m1 : Trust.Temporal.FiniteModel.Model :=
  Trust.Temporal.FiniteModel.Model.mk "m" [] [] [] [] []

theorem root_extension_door : Nat.beq m1.actionCount 0 = true := rfl

end Model
end Trust
