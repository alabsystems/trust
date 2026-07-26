-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B, fidelity +2: extend whole-program PROVED ⟹ safe to programs containing
-- both guarded asserts AND CALLS (the totality-decision case — the root of 4 of the 8
-- false-proofs: Attack-5/6B/6C). A call carries its totality bit (the SOUND judgment:
-- judged-total ⟺ genuinely-total — the conservativeness invariant the crate-anchor /
-- closure-gate / element-allowlist fixes establish). Proven by induction. Kernel-checked.

inductive Verdict where
  | proved : Verdict
  | mayPanic : Verdict

def panicsHere (reachable : Bool) (cond : Bool) : Bool :=
  match reachable with
  | true => (match cond with | true => false | false => true)
  | false => false

def assertVerdict (reachable : Bool) (cond : Bool) : Verdict :=
  match panicsHere reachable cond with
  | true => Verdict.mayPanic
  | false => Verdict.proved

def verdictPanics (v : Verdict) : Bool :=
  match v with
  | Verdict.mayPanic => true
  | Verdict.proved => false

-- A step is a guarded assert OR a call (with its conservative totality bit).
inductive Step where
  | guardedAssert : Bool -> Bool -> Step
  | call : Bool -> Step

-- Ground truth: an assert panics per panicsHere; a NON-total call may panic.
def stepPanics : Step -> Bool
  | Step.guardedAssert r c => panicsHere r c
  | Step.call total => (match total with | true => false | false => true)

-- The verifier: assert per assertVerdict; a call is PROVED iff (conservatively) total,
-- else may-panic. (The SOUND totality decision — unmodeled/non-total ⟹ may-panic.)
def stepVerdict : Step -> Verdict
  | Step.guardedAssert r c => assertVerdict r c
  | Step.call total => (match total with | true => Verdict.proved | false => Verdict.mayPanic)

inductive Prog where
  | done : Prog
  | seq : Step -> Prog -> Prog

def progPanics : Prog -> Bool
  | Prog.done => false
  | Prog.seq s rest => (match stepPanics s with | true => true | false => progPanics rest)

def progVerdict : Prog -> Verdict
  | Prog.done => Verdict.proved
  | Prog.seq s rest =>
    (match stepVerdict s with | Verdict.mayPanic => Verdict.mayPanic | Verdict.proved => progVerdict rest)

-- THE THEOREM: for ANY program of guarded asserts AND calls (under conservative call
-- totality), the verifier reports may-panic EXACTLY when the program panics — hence
-- PROVED ⟹ safe. Proven by induction over the program. This is realPanics(p) =
-- models(verdict(p)) for the assert+call fragment of the encoding.
theorem prog_sound (p : Prog) : verdictPanics (progVerdict p) = progPanics p := by
  induction p with
  | done => rfl
  | seq s rest ih =>
    cases s with
    | guardedAssert r c =>
      cases r with
      | false => exact ih
      | true =>
        cases c with
        | false => rfl
        | true => exact ih
    | call total =>
      cases total with
      | true => exact ih
      | false => rfl
