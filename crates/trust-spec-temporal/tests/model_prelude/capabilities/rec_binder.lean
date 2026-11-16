-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- `rec` as a binder name; expected failure.

namespace Trust
namespace Model

def applyTwice (rec : Nat → Nat) (n : Nat) : Nat := rec (rec n)

theorem binder_door : Nat.beq (applyTwice (fun k => k + 1) 0) 2 = true := rfl

end Model
end Trust
