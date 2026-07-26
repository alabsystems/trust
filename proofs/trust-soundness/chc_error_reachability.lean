-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B: lift the contract to the CHC `error`-RULE structure — the Horn-clause layer
-- the encoder actually emits. For each potential panic site the encoder adds a rule
--     error <- pathGuard ∧ obligation
-- (the site's `error` is derivable iff it is reachable AND its obligation fires). The
-- verifier reports PROVED iff the `error` relation is UNREACHABLE — no rule body is
-- satisfiable. This proves that error-unreachability soundly implies safety, GIVEN each
-- rule's obligation captures its panic (the per-op soundness from the obligation classes).
-- It composes via the keystone over the GUARDED obligation `band pathGuard obligation`, with
-- `band_mono` lifting per-op soundness through the path guard. Kernel-checked; gated.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b

-- Per-op soundness lifts through a path guard: if the obligation captures the panic, then
-- the GUARDED obligation captures the guarded panic (a site panics-when-reached only if its
-- obligation fires-when-reached). `error <- pg ∧ ob` thus over-approximates `panic-on-pg`.
theorem band_mono (pg : Bool) (tp : Bool) (ob : Bool) (h : bimplies tp ob = true) :
    bimplies (band pg tp) (band pg ob) = true := by
  cases pg with
  | true => exact h
  | false => rfl

-- A CHC is a list of error-rules, each lowered to its (guarded-true-panic, guarded-obligation)
-- = (pathGuard ∧ truePanic, pathGuard ∧ obligation) pair via `chcRule`.
inductive Prog where
  | nil : Prog
  | cons : Bool -> Bool -> Prog -> Prog

def chcRule (pathGuard : Bool) (truePanic : Bool) (obligation : Bool) (rest : Prog) : Prog :=
  Prog.cons (band pathGuard truePanic) (band pathGuard obligation) rest

-- `error` is reachable iff SOME rule body `pathGuard ∧ obligation` is satisfiable — this is
-- `models` (the verifier reports PROVED iff it is false).
def errorReachable : Prog -> Bool
  | Prog.nil => false
  | Prog.cons _ ob rest => bor ob (errorReachable rest)
-- The program truly panics iff SOME site is reached AND truly panics.
def programPanics : Prog -> Bool
  | Prog.nil => false
  | Prog.cons tp _ rest => bor tp (programPanics rest)
def safe : Prog -> Bool
  | Prog.nil => true
  | Prog.cons tp _ rest => band (bnot tp) (safe rest)
def provedSound : Prog -> Bool
  | Prog.nil => true
  | Prog.cons tp ob rest => band (band (bnot ob) (bimplies tp ob)) (provedSound rest)

-- THE CHC ERROR-QUERY SOUNDNESS: if every error-rule is sound, then `error` UNREACHABLE
-- (no rule body satisfiable = PROVED) ⟹ the program is truly safe. A proof-grade "error
-- unreachable" CHC verdict is therefore sound. (Same composition as the keystone, now over
-- the Horn-rule error-reachability structure.)
theorem chc_error_sound (p : Prog) : bimplies (provedSound p) (safe p) = true := by
  induction p with
  | nil => rfl
  | cons tp ob rest ih =>
    cases tp with
    | true => cases ob with | true => rfl | false => rfl
    | false => cases ob with | true => rfl | false => exact ih

-- A concrete CHC: three sites, all REACHABLE (pathGuard = true) but none firing its
-- obligation (an in-range shift, a nonzero divisor, an in-bounds index). `error` is
-- unreachable ⇒ PROVED, and by chc_error_sound the program is truly safe.
def chc : Prog :=
  chcRule true false false (chcRule true false false (chcRule true false false Prog.nil))
theorem chc_error_unreachable : errorReachable chc = false := rfl
theorem chc_sound : provedSound chc = true := rfl
theorem chc_safe : safe chc = true := rfl
theorem chc_no_panic : programPanics chc = false := rfl

-- A CHC with a REACHABLE panicking site (pathGuard ∧ obligation both true): `error` IS
-- derivable, so the verifier correctly does NOT report PROVED.
def chcUnsafe : Prog := chcRule true true true Prog.nil
theorem chcUnsafe_error_reachable : errorReachable chcUnsafe = true := rfl
theorem chcUnsafe_panics : programPanics chcUnsafe = true := rfl

-- An UNREACHABLE panicking site (pathGuard = false, e.g. a panic past a dominating guard):
-- `error` is NOT derivable from it and the site cannot actually be reached — both the
-- guarded obligation and the guarded panic are false. The guard's soundness is structural.
def chcGuardedOut : Prog := chcRule false true true Prog.nil
theorem chcGuardedOut_error_unreachable : errorReachable chcGuardedOut = false := rfl
theorem chcGuardedOut_safe : safe chcGuardedOut = true := rfl
