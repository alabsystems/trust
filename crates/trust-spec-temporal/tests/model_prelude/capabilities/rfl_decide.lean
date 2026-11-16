-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- rfl and decide theorems; required pass.

namespace Trust
namespace Model

def double (n : Nat) : Nat := n + n

theorem rfl_double : double 21 = 42 := rfl
theorem decide_lt : double 2 < 5 := by decide
theorem decide_eq : (double 3 = 6) := by decide
theorem decide_ne : ¬ (double 3 = 7) := by decide

end Model
end Trust
