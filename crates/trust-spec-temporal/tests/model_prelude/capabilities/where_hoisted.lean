-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- the `where` helper of where_clause hoisted to a top-level def; its workaround.

namespace Trust
namespace Model

def total.go : List Nat → Nat
  | [] => 0
  | x :: rest => x + total.go rest

def total (xs : List Nat) : Nat := total.go xs

theorem total_door : Nat.beq (total [1, 2, 3]) 6 = true := rfl

end Model
end Trust
