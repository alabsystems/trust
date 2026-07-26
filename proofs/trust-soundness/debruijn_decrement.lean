-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step C, formal leg of the OUROBOROS forward direction: a machine-checked proof,
-- in clean, of the discharge obligation for a real arm of clean's OWN kernel.
--
-- clean-kernel's `MicroExpr::subst` (micro/types.rs:289) decrements a de Bruijn index
-- `idx - 1` (a u32 subtraction that UNDERFLOWS / panics at idx == 0) guarded by
-- `idx > depth`. Its panic-freedom obligation is exactly: `depth < idx  ⟹  idx ≠ 0`
-- (so the predecessor `idx - 1` is total). Since de Bruijn indices are Nats and
-- `depth ≥ 0` always, `idx > depth ≥ 0` forces `idx ≥ 1`.
--
-- This property is established THREE independent ways, which is the rigor of the ouroboros:
--   1. EXECUTION (clean): `clean-kernel::debruijn_decrement_model_matches_subst` runs the
--      real `subst` over a grid incl. idx==0 and confirms it never panics.
--   2. SMT (Trust): `trust-mc soundness_oracle::ouroboros_clean_kernel_debruijn_decrement_
--      proven_safe` has Trust's own discharge PROVE the model panic-free for all inputs.
--   3. THIS FILE — a kernel-checked proof of the discharge obligation itself, in clean.
-- Kernel-checked through clean (no sorry / no axioms); covered by the ouroboros gate.

def bnot (a : Bool) : Bool := match a with | true => false | false => true

-- `b => true ; else bnot a` makes `bimplies _ true` reduce to `true` definitionally and
-- `bimplies a false` reduce to `bnot a` — so the proofs below close by `rfl` after one case.
def bimplies (a : Bool) (b : Bool) : Bool :=
  match b with
  | true => true
  | false => bnot a

-- de Bruijn index guard `depth < idx`, on Nat. Matches on the RIGHT operand first, so
-- `lt _ zero` reduces to `false` (nothing is < 0) without inspecting `depth`.
def lt (a : Nat) (b : Nat) : Bool :=
  match b with
  | Nat.zero => false
  | Nat.succ b' => (match a with | Nat.zero => true | Nat.succ a' => lt a' b')

-- The decrement `idx - 1` is well-defined (no u32 underflow) exactly when idx ≠ 0,
-- i.e. idx is a successor.
def nonzero (n : Nat) : Bool :=
  match n with
  | Nat.zero => false
  | Nat.succ _ => true

-- THE DISCHARGE OBLIGATION, proven: the guard `depth < idx` implies `idx ≠ 0`, so the
-- de Bruijn decrement `idx - 1` in `subst` never underflows. For EVERY (depth, idx) —
-- the same property Trust's discharge proves by SMT and the clean execution-test
-- validates against the real `subst`, here machine-checked in clean.
theorem debruijn_guard_no_underflow (depth : Nat) (idx : Nat) :
    bimplies (lt depth idx) (nonzero idx) = true := by
  cases idx with
  | zero => rfl       -- nonzero zero = false; lt depth zero = false; bimplies false false = bnot false = true
  | succ p => rfl     -- nonzero (succ p) = true; bimplies _ true = true
