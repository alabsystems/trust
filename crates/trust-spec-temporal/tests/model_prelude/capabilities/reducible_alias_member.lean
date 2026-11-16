-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- abbrev and @[reducible] def aliases, including the B1A-D04 Member alias of FiniteModel.Member; required pass.

namespace Trust
namespace Temporal

@[reducible] def Member {α : Type} (value : α) (values : List α) : Prop :=
  FiniteModel.Member value values

theorem member_bridge_to {α : Type} (value : α) (values : List α) :
    Member value values = FiniteModel.Member value values := rfl

theorem member_head : Member 2 [2, 5] := FiniteModel.Member.head [5]
theorem member_tail : Member 5 [2, 5] :=
  FiniteModel.Member.tail 2 [5] (FiniteModel.Member.head [])

end Temporal
end Trust

namespace Trust
namespace Model

abbrev State := List Nat
@[reducible] def Slots : Type := List Nat

def s1 : State := [1, 2]
def s2 : Slots := s1

theorem abbrev_door : Nat.beq s2.length 2 = true := rfl

end Model
end Trust
