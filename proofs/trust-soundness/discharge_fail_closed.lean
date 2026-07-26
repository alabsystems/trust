-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- The mechanistic prevention invariant of Trust's verifier, formalized (Step B,
-- first checked artifact). The 2026-06-19 soundness sweep found 8 false-proofs, all
-- from ONE root cause: the result types let "could not model this" be the SAME value
-- as "proven safe", so `?` / `_ =>` silently picked the unsound default. The Rust fix
-- is `trust-types::discharge::Discharge<T>`. This is its faithful Church encoding,
-- and the soundness property expressed AS A TYPE: there is no total `Discharge T -> R`
-- that extracts a verdict WITHOUT supplying the fail-closed (may-panic) case.

-- Discharge T  =  Modeled T | Unmodeled   (Church-encoded sum, i.e. Maybe T)
def Discharge (T : Type) := forall (R : Type), (T -> R) -> R -> R

def modeled (T : Type) (t : T) : Discharge T :=
  fun (R : Type) (onModeled : T -> R) (onUnmodeled : R) => onModeled t

def unmodeled (T : Type) : Discharge T :=
  fun (R : Type) (onModeled : T -> R) (onUnmodeled : R) => onUnmodeled

-- The eliminator IS the soundness invariant, as a type: to turn a `Discharge` into a
-- verdict `R` you MUST provide `onUnmodeled : R` — the fail-closed (may-panic) value.
-- No well-typed consumer can reach a verdict while treating `Unmodeled` as absent;
-- the `let len = len?` / `_ => None` false-proof idiom is not expressible here.
def discharge_elim (T : Type) (R : Type) (d : Discharge T) (onModeled : T -> R) (onUnmodeled : R) : R :=
  d R onModeled onUnmodeled
