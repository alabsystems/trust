-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Discharge soundness, mechanized as PROPOSITIONAL THEOREMS (apex Step B).
-- The faithful inductive model of `trust-types::discharge::Discharge<T>` and the
-- fail-closed lattice laws that make the 8-instance false-proof class impossible by
-- construction. Kernel-checked through clean (`clean check`), no `sorry`, no axioms.

inductive Dis (T : Type) where
  | modeled : T -> Dis T
  | unmodeled : Dis T

-- The eliminator: turning a Discharge into a verdict `R` REQUIRES the fail-closed
-- (may-panic) value `onUnmod`.
def elim (T : Type) (R : Type) (onMod : T -> R) (onUnmod : R) : Dis T -> R
  | Dis.modeled t => onMod t
  | Dis.unmodeled => onUnmod

-- SOUNDNESS 1 (no false-prove from absence): extracting a verdict from `unmodeled`
-- ALWAYS yields the fail-closed default. There is no consumer that turns `unmodeled`
-- into a "modeled" verdict — the `let len = len?` / `_ => None` idiom cannot pick safe.
theorem unmodeled_forces_failclosed (T : Type) (R : Type) (onMod : T -> R) (onUnmod : R) :
    elim T R onMod onUnmod Dis.unmodeled = onUnmod := rfl

-- The lattice join toward may-panic: `unmodeled` dominates.
def join (T : Type) (a : Dis T) (b : Dis T) : Dis T :=
  match a with
  | Dis.unmodeled => Dis.unmodeled
  | Dis.modeled x =>
    match b with
    | Dis.unmodeled => Dis.unmodeled
    | Dis.modeled _ => Dis.modeled x

-- SOUNDNESS 2 (a composite is never safer than its weakest part — Attack-5's lesson,
-- proven): joining with `unmodeled` on EITHER side is `unmodeled`.
theorem join_unmodeled_left (T : Type) (b : Dis T) :
    join T Dis.unmodeled b = Dis.unmodeled := rfl

theorem join_unmodeled_right (T : Type) (x : T) :
    join T (Dis.modeled x) Dis.unmodeled = Dis.unmodeled := rfl
