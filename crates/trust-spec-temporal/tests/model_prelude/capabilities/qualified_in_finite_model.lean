-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- fully qualified Trust.Model names inside namespace Trust.Temporal.FiniteModel, whose own Value and State shadow them (FiniteModel.lean:121-127); required pass.

namespace Trust
namespace Model

inductive Value where
  | int : Int → Value
  | bool : Bool → Value

abbrev State := List Value

end Model
end Trust

namespace Trust
namespace Temporal
namespace FiniteModel

-- Inside this namespace `Value` and `State` are FiniteModel's own
-- (FiniteModel.lean:121-127), so the model's are written fully qualified.
def encodeNat (n : Nat) : Trust.Model.Value := Trust.Model.Value.int (Int.ofNat n)

def encodeRow (row : List Nat) : Trust.Model.State := row.map encodeNat

def localValue : Value := Value.nat 3

theorem qualified_door : Nat.beq (encodeRow [1, 2, 3]).length 3 = true := rfl
theorem shadowed_value_is_finite_models : localValue = Trust.Temporal.FiniteModel.Value.nat 3 := rfl
theorem qualified_value : encodeNat 2 = Trust.Model.Value.int 2 := rfl

end FiniteModel
end Temporal
end Trust
