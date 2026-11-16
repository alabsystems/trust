-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- TLC's floor div and mod on negative Int, hand-written over Nat.div (B1A-D08), by rfl; required pass.

namespace Trust
namespace Model

-- TLC's floor division and modulus for a positive divisor, hand-written over
-- Nat.div / Nat.mod and the sign of the dividend (B1A-D08).
def tlcDiv (a b : Int) : Int :=
  @Int.casesOn (fun _ => Int) a
    (fun n => @Int.casesOn (fun _ => Int) b (fun m => Int.ofNat (Nat.div n m)) (fun _ => 0))
    (fun n => @Int.casesOn (fun _ => Int) b (fun m => Int.negSucc (Nat.div n m)) (fun _ => 0))

def tlcMod (a b : Int) : Int := a - b * tlcDiv a b

theorem div_neg : tlcDiv (-7) 2 = -4 := rfl
theorem mod_neg : tlcMod (-7) 2 = 1 := rfl
theorem div_neg_exact : tlcDiv (-6) 3 = -2 := rfl
theorem mod_neg_exact : tlcMod (-6) 3 = 0 := rfl
theorem div_pos : tlcDiv 7 2 = 3 := rfl
theorem mod_pos : tlcMod 7 2 = 1 := rfl

end Model
end Trust
