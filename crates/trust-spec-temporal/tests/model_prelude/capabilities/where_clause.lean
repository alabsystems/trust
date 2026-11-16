-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- a `where` helper; expected failure (Sep 19 CLI).

namespace Trust
namespace Model

def total (xs : List Nat) : Nat := go xs
where
  go : List Nat → Nat
    | [] => 0
    | x :: rest => x + go rest

theorem total_door : Nat.beq (total [1, 2, 3]) 6 = true := rfl

end Model
end Trust
