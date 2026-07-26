-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B, fidelity +1: lift PROVED ⟹ safe from a single guarded assert to a
-- WHOLE PROGRAM (a finite sequence of guarded asserts — a straight-line path, the
-- first move toward a real CFG). Proven BY INDUCTION over the program. Kernel-checked.

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

-- A program: a finite sequence of guarded asserts (each carries reachability + cond).
inductive Prog where
  | done : Prog
  | step : Bool -> Bool -> Prog -> Prog

-- Ground truth: the program panics iff ANY assert on the path panics.
def progPanics : Prog -> Bool
  | Prog.done => false
  | Prog.step r c rest =>
    match panicsHere r c with
    | true => true
    | false => progPanics rest

-- The verifier: PROVED iff no assert yields may-panic; else may-panic.
def progVerdict : Prog -> Verdict
  | Prog.done => Verdict.proved
  | Prog.step r c rest =>
    match assertVerdict r c with
    | Verdict.mayPanic => Verdict.mayPanic
    | Verdict.proved => progVerdict rest

-- THE THEOREM (whole-program PROVED ⟹ safe): the verifier reports may-panic EXACTLY
-- when the program panics, for ANY finite path. Proven by induction over the program.
theorem prog_verdict_matches_semantics (p : Prog) :
    verdictPanics (progVerdict p) = progPanics p := by
  induction p with
  | done => rfl
  | step r c rest ih =>
    cases r with
    | false => exact ih
    | true =>
      cases c with
      | false => rfl
      | true => exact ih
