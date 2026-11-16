-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01e: the fixed control of the `counterexamples` kernel test (B1B-D11; B1B-00
-- verifier item 3), checked on every run so the test never passes vacuously.
--
-- The toy statement, false as stated: `∀ n : Nat, n + 1 = n`.
-- Derivation (by hand, D39): at the concrete instance n = 0 the left side `0 + 1`
-- reduces (Nat.add's second argument is `Nat.succ Nat.zero`) to `Nat.succ 0`, so
-- `0 + 1 = 0` is decided false (`Nat.decEq` compares the two numerals), and `absurd`
-- turns the instance `h 0` of the assumed statement into `False`. So the statement's
-- negation holds, with the instance n = 0 as its witness.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace CounterexampleControl

theorem toy_refuted : ¬ (∀ n : Nat, n + 1 = n) := fun h => absurd (h 0) (by decide)

end CounterexampleControl
end B1bSelftest
end Trust
