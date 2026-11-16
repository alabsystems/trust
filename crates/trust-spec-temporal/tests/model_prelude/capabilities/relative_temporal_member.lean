-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- the relative name Temporal.Member from inside namespace Trust.Model; required pass.

namespace Trust
namespace Temporal

@[reducible] def Member {α : Type} (value : α) (values : List α) : Prop :=
  FiniteModel.Member value values

end Temporal
end Trust

namespace Trust
namespace Model

def StateOk (s : List Nat) : Prop := ∀ v, Temporal.Member v s → v = v

theorem state_ok : StateOk [1, 2] := fun _ _ => rfl

theorem relative_member : Temporal.Member 1 [1] := Temporal.FiniteModel.Member.head []

end Model
end Trust
