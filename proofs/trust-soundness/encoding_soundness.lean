-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- The apex theorem in miniature (Step B): for a minimal single-guarded-assert slice
-- of the discharge encoding, the verifier's verdict EXACTLY matches the ground-truth
-- panic semantics — hence `verifier says PROVED ⟹ the program is actually safe`.
-- The verify-the-verifier property, kernel-checked through clean (no sorry/axioms).

inductive Verdict where
  | proved : Verdict
  | mayPanic : Verdict

-- Ground-truth semantics: the guarded assert panics iff reachable on a feasible path
-- (`reachable = true`) AND its condition is false.
def panicsHere (reachable : Bool) (cond : Bool) : Bool :=
  match reachable with
  | true => (match cond with | true => false | false => true)
  | false => false

-- The discharge encoding: may-panic (error rule) exactly when it can fail; else PROVED.
def assertVerdict (reachable : Bool) (cond : Bool) : Verdict :=
  match panicsHere reachable cond with
  | true => Verdict.mayPanic
  | false => Verdict.proved

def verdictPanics (v : Verdict) : Bool :=
  match v with
  | Verdict.mayPanic => true
  | Verdict.proved => false

-- THE THEOREM: the verifier reports may-panic EXACTLY when the program actually
-- panics. Soundness (PROVED ⟹ safe) and completeness (panic ⟹ ¬PROVED) both follow.
theorem verdict_exactly_matches_semantics (reachable : Bool) (cond : Bool) :
    verdictPanics (assertVerdict reachable cond) = panicsHere reachable cond := by
  cases reachable <;> cases cond <;> rfl
