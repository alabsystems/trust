-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest: a module that depends on Good (suffix chaining). Its one
-- theorem uses Good.fun_eq, so it elaborates only after Good, and its census is
-- Good.fun_eq's (the four quotient constants); Eq.symm adds no axiom.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Chain2

theorem fun_eq_symm (f g : Nat → Nat) (h : ∀ x, f x = g x) : g = f :=
  Eq.symm (Trust.B1bSelftest.Good.fun_eq f g h)

end Chain2
end B1bSelftest
end Trust
