-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest for the definitions runner (census rule (d), B1B-D06):
-- definitions that reach no axiom of their own. defs_plain uses only Nat; defs_member
-- uses B1a's Trust.Temporal.Member (Trust/List.lean); defs_cites_b1a cites B1a's theorem
-- Trust.Temporal.FiniteModel.exceptResultsSame, whose proof applies funext
-- (FiniteModel.lean, `funext candidate`), so it reaches Quot, Quot.lift, Quot.mk and
-- Quot.sound, and exactly those are its B1a callees' allowance. None adds a foundational
-- axiom beyond its B1a callees'; all three pass.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace DefsGood

def defs_plain (n : Nat) : Nat := n + 1

def defs_member (n : Nat) (ns : List Nat) : Prop := Trust.Temporal.Member n ns

def defs_cites_b1a := @Trust.Temporal.FiniteModel.exceptResultsSame

end DefsGood
end B1bSelftest
end Trust
