-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- `go` as a binder name; the workaround of rec_binder.

namespace Trust
namespace Model

def applyTwice (go : Nat → Nat) (n : Nat) : Nat := go (go n)

theorem binder_door : Nat.beq (applyTwice (fun k => k + 1) 0) 2 = true := rfl

end Model
end Trust
