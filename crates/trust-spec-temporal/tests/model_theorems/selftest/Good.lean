-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest (model_theorems.rs, harness_selftest): two theorems, both
-- accepted. Expected census, derived from the kernel's own construction rather than
-- read off a run: `refl_nat` is `rfl` and reaches no axiom; `fun_eq` is `funext`,
-- whose proof term (clean-kernel env/logic.rs, init_funext) is built from `Quot`,
-- `Quot.mk`, `Quot.lift` and `Quot.sound`, so its foundational closure is exactly
-- those four, all inside B1B-D06 (b)'s allowed set.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Good

theorem refl_nat (n : Nat) : n = n := rfl

theorem fun_eq (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := funext h

end Good
end B1bSelftest
end Trust
