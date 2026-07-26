-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B: NON-LINEAR CFG reachability. chc_reachability_fixpoint.lean computed block
-- reachability for a LINEAR chain (one predecessor each); real CFGs BRANCH and MERGE, and the
-- CHC solver's least fixpoint is exactly where MULTI-PREDECESSOR joins and LOOP back-edges
-- matter. This models a block reached iff ANY incoming edge fires — `merge` over an edge list
-- of (predReached ∧ edgeGuard) — i.e. the disjunctive join a CFG performs at a merge point.
--
-- The soundness is REACHABILITY-ASSIGNMENT-INDEPENDENT: each block is annotated with the pair
-- `(reached ∧ truePanic, reached ∧ obligation)`, scaling BOTH by the SAME `reached`, so the
-- per-node `bimplies tp ob` the keystone needs is preserved no matter HOW `reached` was
-- computed — multi-predecessor merge, or the loop fixpoint. That is precisely why a fixpoint
-- reachability (however the CHC solver iterates it) stays sound. We then exhibit (a) a diamond
-- where a panicking block is guarded out on ALL its incoming edges ⇒ unreachable ⇒ harmless,
-- and (b) a back-edge LOOP whose reachability is Kleene-iterated to a FIXED POINT, with the
-- loop body correctly reachable there.
-- Kernel-checked through clean; covered by the ouroboros gate.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b
theorem bimplies_refl (x : Bool) : bimplies x x = true := by
  cases x with | true => rfl | false => rfl

-- A program of (truePanic, obligation) pairs and the flat keystone (re-proven in-file, as in
-- chc_reachability_fixpoint.lean): PROVED (no obligation fires, each obligation ⊇ its panic) ⟹
-- truly safe (no panic fires). `realPanics ⊆ models`.
inductive Prog where
  | nil : Prog
  | cons : Bool -> Bool -> Prog -> Prog

def realPanics : Prog -> Bool
  | Prog.nil => false
  | Prog.cons tp _ rest => bor tp (realPanics rest)
def models : Prog -> Bool
  | Prog.nil => false
  | Prog.cons _ ob rest => bor ob (models rest)
def safe : Prog -> Bool
  | Prog.nil => true
  | Prog.cons tp _ rest => band (bnot tp) (safe rest)
def provedSound : Prog -> Bool
  | Prog.nil => true
  | Prog.cons tp ob rest => band (band (bnot ob) (bimplies tp ob)) (provedSound rest)

theorem encoding_sound (p : Prog) : bimplies (provedSound p) (safe p) = true := by
  induction p with
  | nil => rfl
  | cons tp ob rest ih =>
    cases tp with
    | true => cases ob with | true => rfl | false => rfl
    | false => cases ob with | true => rfl | false => exact ih

-- THE MULTI-PREDECESSOR JOIN. A block's incoming edges, each carrying the predecessor's
-- reached-flag and the edge guard; the block is reached iff SOME edge fires (the disjunctive
-- merge a CFG performs — unlike the chain's single predecessor).
inductive Edges where
  | none : Edges
  | edge : Bool -> Bool -> Edges -> Edges   -- predReached, edgeGuard, rest

def merge : Edges -> Bool
  | Edges.none => false
  | Edges.edge pr g rest => bor (band pr g) (merge rest)

-- A CFG as a list of blocks: each carries its incoming edges, its true panic, and the
-- obligation the encoder emits for it.
inductive Cfg where
  | nil : Cfg
  | block : Edges -> Bool -> Bool -> Cfg -> Cfg   -- edges, truePanic, obligation, rest

-- ANNOTATE: emit, per block, the reachability-GUARDED panic and obligation. `merge edges` is
-- the computed reachability (the join); a block unreachable on ALL edges contributes (·∧false).
def annotate : Cfg -> Prog
  | Cfg.nil => Prog.nil
  | Cfg.block edges tp ob rest =>
      Prog.cons (band (merge edges) tp) (band (merge edges) ob) (annotate rest)

-- THE CONTRACT over a non-linear CFG: for ANY block set with ANY incoming-edge structure,
-- PROVED (no REACHED block's obligation fires) ⟹ truly safe. The flat keystone does the work;
-- the multi-predecessor `merge` scales each block's panic and obligation by the SAME reached
-- flag, so soundness is invariant under however reachability was joined/iterated.
theorem cfg_reachability_sound (c : Cfg) :
    bimplies (provedSound (annotate c)) (safe (annotate c)) = true :=
  encoding_sound (annotate c)

-- ── Diamond: entry → {A (guard true), B (guard FALSE)} → C (merges A and B) ──────────────────
-- B would panic, but BOTH ways to reach B are false-guarded ⇒ merge = false ⇒ unreachable, so
-- its guarded panic/obligation are zeroed. A and C are total. The multi-predecessor merge at C
-- sees A's true-guarded edge, so C is reachable (and total).
def blkA : Edges := Edges.edge true true Edges.none           -- entry-reached, guard true ⇒ reached
def blkB : Edges := Edges.edge true false Edges.none          -- entry-reached, guard FALSE ⇒ NOT reached
def blkC : Edges := Edges.edge true true (Edges.edge false true Edges.none)  -- reached via A; B's edge dead
def diamond : Cfg :=
  Cfg.block blkA false false (
  Cfg.block blkB true true (              -- B panics, but is guarded out
  Cfg.block blkC false false Cfg.nil))

theorem diamondB_unreachable : merge blkB = false := rfl
theorem diamondC_reachable  : merge blkC = true := rfl
theorem diamond_no_real_panic : realPanics (annotate diamond) = false := rfl  -- B's panic guarded out
theorem diamond_proved : models (annotate diamond) = false := rfl
theorem diamond_safe   : safe (annotate diamond) = true := rfl
theorem diamond_sound  : provedSound (annotate diamond) = true := rfl

-- A REACHABLE panic: same block B but now an incoming edge IS true-guarded ⇒ merge = true ⇒ the
-- panic is reachable, so the obligation fires and the CFG is correctly NOT proved — decided by
-- the join, not assumed.
def blkBreached : Edges := Edges.edge true false (Edges.edge true true Edges.none)  -- second path open
def reachablePanicCfg : Cfg := Cfg.block blkBreached true true Cfg.nil
theorem reachablePanic_merge : merge blkBreached = true := rfl
theorem reachablePanic_not_proved : models (annotate reachablePanicCfg) = true := rfl
theorem reachablePanic_real : realPanics (annotate reachablePanicCfg) = true := rfl

-- ── Loop back-edge: header H (entry), body Bd (reached from H under loopGuard), back-edge Bd→H.
-- Reachability is the LEAST FIXPOINT of the transition; we Kleene-iterate the (rH, rB) pair from
-- ⊥ and show it CONVERGES — the body is reachable at the fixpoint (the back-edge does not change
-- that here, but the iteration is what the CHC solver runs). ──────────────────────────────────
def stepH (entry : Bool) (rB : Bool) (backGuard : Bool) : Bool := bor entry (band rB backGuard)
def stepB (rH : Bool) (loopGuard : Bool) : Bool := band rH loopGuard

-- Kleene iteration with entry = loopGuard = backGuard = true, starting from (false, false).
def rH1 : Bool := stepH true false true     -- header from entry
def rB1 : Bool := stepB false true          -- body from header (header not yet reached at step 0)
def rH2 : Bool := stepH true rB1 true
def rB2 : Bool := stepB rH1 true
def rH3 : Bool := stepH true rB2 true
def rB3 : Bool := stepB rH2 true

theorem loop_header_fixed : rH3 = rH2 := rfl
theorem loop_body_fixed   : rB3 = rB2 := rfl          -- (rH2, rB2) is a fixed point of the step
theorem loop_body_reachable_at_fixpoint : rB2 = true := rfl   -- the loop body IS reachable

-- Encode the loop at its fixpoint reachability. The body is reachable (rB2 = true); if it is
-- TOTAL the CFG is proved+safe (this case); a panicking loop body would, at the same fixpoint,
-- make its obligation reachable ⇒ correctly not proved.
def loopBodyEdges : Edges := Edges.edge rB2 true Edges.none   -- body reached at the LFP
def loopCfgTotal : Cfg :=
  Cfg.block (Edges.edge true true Edges.none) false false (   -- header, total
  Cfg.block loopBodyEdges false false Cfg.nil)               -- body reachable, total
theorem loop_body_merge_at_fixpoint : merge loopBodyEdges = true := rfl
theorem loopTotal_proved : models (annotate loopCfgTotal) = false := rfl
theorem loopTotal_safe   : safe (annotate loopCfgTotal) = true := rfl

-- Same loop, panicking body: reachable at the fixpoint ⇒ obligation fires ⇒ NOT proved.
def loopCfgPanic : Cfg :=
  Cfg.block (Edges.edge true true Edges.none) false false (
  Cfg.block loopBodyEdges true true Cfg.nil)
theorem loopPanic_not_proved : models (annotate loopCfgPanic) = true := rfl
theorem loopPanic_real : realPanics (annotate loopCfgPanic) = true := rfl
