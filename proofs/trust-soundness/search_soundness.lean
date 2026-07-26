-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B, END-TO-END for P0#2: lift the local prune-decision proof
-- (fix_correctness.lean::p0_2_fix_exact, which proves the per-edge classifier table
-- sound) all the way to the search's FINAL verdict — the property that actually makes
-- a program safe:  `the acyclic search reports SAFE  ⟹  the program is truly safe`,
-- i.e. realPanics ⊆ models for this fragment.
--
-- This is a genuine strengthening, NOT a restatement: p0_2_fix_exact proves the local
-- table; here we prove the whole search's SAFE verdict is a SOUND OVER-APPROXIMATION
-- (an implication, not an equality) — and that the reverted bug breaks exactly this.
--
-- Model: the acyclic search considers a set of clause-body edges. Each edge carries the
-- SMT result on its body (sat/unsat/unknown) and the GROUND TRUTH `reachesError` (the
-- body is satisfiable AND its head is `error` — a real reachable panic). A flat edge
-- list is a sound abstraction of the least-fixpoint for the SOUNDNESS direction: every
-- edge ever considered passes the same per-edge classify decision, so "no live edge was
-- dropped" is a per-edge property that composes regardless of derivation order.
--
-- Trusted boundary: ay's UNSAT is sound — an `unsat`-classified edge truly does not
-- reach error. This is the `faithfulEdge` premise (the SMT solver is the trust base).
-- Kernel-checked through clean (no sorry / no axioms).

def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def bnot (a : Bool) : Bool := match a with | true => false | false => true
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b

inductive Sc where
  | sat : Sc        -- body satisfiable (witness)
  | unsat : Sc      -- definitively unsatisfiable
  | unknown : Sc    -- undecidable / timeout

-- Is this edge a refutation WITNESS? Only a `sat` body that heads to `error`.
def isWitness (smt : Sc) (reachesError : Bool) : Bool :=
  match smt with | Sc.sat => reachesError | _ => false

-- Does this edge TAINT exhaustiveness under THE FIX? Exactly the `unknown` edges
-- (three-valued SolveOutcome::Undecided sets `truncated`).
def fixTaints (smt : Sc) : Bool :=
  match smt with | Sc.unknown => true | _ => false

-- THE FIX deems an edge "safe to ignore" iff it is neither a witness nor a taint.
def fixedEdgeSafe (smt : Sc) (reachesError : Bool) : Bool :=
  band (bnot (isWitness smt reachesError)) (bnot (fixTaints smt))

-- SMT FAITHFULNESS (trusted): an `unsat` edge truly does not reach error.
def faithfulEdge (smt : Sc) (reachesError : Bool) : Bool :=
  match smt with | Sc.unsat => bnot reachesError | _ => true

-- PER-EDGE SOUNDNESS: if the fix deems this edge safe AND the solver was faithful,
-- then the edge truly does not reach error. Proven for every (smt, reachesError):
-- the `unknown` case is VACUOUS (fixedEdgeSafe = false there — that is the whole fix).
theorem edge_sound (smt : Sc) (reachesError : Bool) :
    bimplies (band (fixedEdgeSafe smt reachesError) (faithfulEdge smt reachesError))
             (bnot reachesError) = true := by
  cases smt with
  | sat => cases reachesError with | true => rfl | false => rfl
  | unsat => cases reachesError with | true => rfl | false => rfl
  | unknown => cases reachesError with | true => rfl | false => rfl

-- The set of clause-body edges the acyclic search considers.
inductive Edges where
  | nil : Edges
  | cons : Sc -> Bool -> Edges -> Edges     -- smt, reachesError, rest

-- PREMISE fold: every edge is (fix-deemed-safe AND faithfully solved).
-- `band (band fixedSafe faithful) rest` — the per-edge premise FIRST, so an unsound
-- edge collapses the whole premise to `false` definitionally (vacuous implication).
def premise : Edges -> Bool
  | Edges.nil => true
  | Edges.cons smt re rest =>
    band (band (fixedEdgeSafe smt re) (faithfulEdge smt re)) (premise rest)

-- GROUND TRUTH of the whole problem: safe iff NO edge actually reaches error.
def trulySafe : Edges -> Bool
  | Edges.nil => true
  | Edges.cons _ re rest => band (bnot re) (trulySafe rest)

-- THE END-TO-END SOUNDNESS THEOREM: if the search deems every edge safe (so it reports
-- SAFE) and the solver was faithful, then the program is TRULY safe. realPanics ⊆ models
-- for the acyclic direct-SMT fragment, all the way to the SAFE verdict.
theorem search_sound (e : Edges) : bimplies (premise e) (trulySafe e) = true := by
  induction e with
  | nil => rfl
  | cons smt re rest ih =>
    cases smt with
    | sat => cases re with | true => rfl | false => exact ih
    | unsat => cases re with | true => rfl | false => exact ih
    | unknown => cases re with | true => rfl | false => rfl

------------------------------------------------------------------------------------
-- THE BUG (07511178f) breaks exactly THIS end-to-end property.
-- The bug folds `unknown` into prunable WITHOUT tainting, so an unknown edge neither
-- counts as a witness nor taints exhaustiveness — the search reports SAFE on it.
------------------------------------------------------------------------------------

-- THE BUG deems an edge safe iff it is not a witness (it never taints on unknown).
def buggyEdgeSafe (smt : Sc) (reachesError : Bool) : Bool :=
  bnot (isWitness smt reachesError)

-- A concrete problem with ONE edge: an `unknown` body that ACTUALLY reaches error
-- (the undecidable-but-satisfiable nonlinear panic of `undecidable_satisfiable_body`).
def buggyExample : Edges := Edges.cons Sc.unknown true Edges.nil
def buggyPremise : Edges -> Bool
  | Edges.nil => true
  | Edges.cons smt re rest => band (buggyEdgeSafe smt re) (buggyPremise rest)

-- The bug reports SAFE on it (premise satisfied)...
theorem bug_says_safe : buggyPremise buggyExample = true := rfl
-- ...the fix does NOT (its premise collapses — the edge is a taint)...
theorem fix_says_not_safe : premise buggyExample = false := rfl
-- ...and the GROUND TRUTH is NOT safe: a real reachable panic was promoted to SAFE.
theorem truth_says_not_safe : trulySafe buggyExample = false := rfl
