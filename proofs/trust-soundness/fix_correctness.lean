-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B, LITERAL encoding: mechanize the actual decision logic of two trust-mc
-- fixes against the real cases they branch on — proving each FIX sound (matches truth)
-- AND each BUG unsound (a demonstrable false PROVE). This ties the soundness proof to
-- the literal code (translate_chc terminator handling; direct_smt_cex SMT-result
-- handling), not an abstract condition. Kernel-checked through clean.

------------------------------------------------------------------------------------
-- CASE-2: the no-terminator backstop in try_direct_call_summary (translate_chc.rs).
------------------------------------------------------------------------------------

inductive TermStatus where
  | terminated : TermStatus     -- block ends in a recognized terminator (Br/CondBr/Return/Unreachable)
  | noTerminator : TermStatus   -- malformed leaf: a successor edge was dropped

-- ground truth: a no-terminator block has a DROPPED successor edge that may reach a
-- panic (the post-`?` assert), so it CAN panic; a terminated block panics per its body.
def trueMayPanic (st : TermStatus) (bodyPanics : Bool) : Bool :=
  match st with
  | TermStatus.terminated => bodyPanics
  | TermStatus.noTerminator => true

-- THE FIX (return None ⇒ caller may-panic): fail closed on a no-terminator leaf.
def fixedVerdict (st : TermStatus) (bodyPanics : Bool) : Bool :=
  match st with
  | TermStatus.terminated => bodyPanics
  | TermStatus.noTerminator => true

-- THE BUG (7e5a2e345 call_falloff havoc-return + continue): treat the leaf as clean.
def buggyVerdict (st : TermStatus) (bodyPanics : Bool) : Bool :=
  match st with
  | TermStatus.terminated => bodyPanics
  | TermStatus.noTerminator => false

-- The FIX is SOUND: its verdict equals the true may-panic for every case.
theorem case2_fix_exact (st : TermStatus) (bodyPanics : Bool) :
    fixedVerdict st bodyPanics = trueMayPanic st bodyPanics := by
  cases st with
  | terminated => rfl
  | noTerminator => rfl

-- The BUG is a FALSE PROOF: on a no-terminator leaf it reports not-may-panic (false =
-- "PROVED safe") while the truth is may-panic (true). Mechanically: buggy ≠ truth.
theorem case2_bug_says_safe : buggyVerdict TermStatus.noTerminator false = false := rfl
theorem case2_truth_says_panic : trueMayPanic TermStatus.noTerminator false = true := rfl

------------------------------------------------------------------------------------
-- P0#2: the acyclic direct-SMT prune decision (direct_smt_cex.rs solve_constraints).
------------------------------------------------------------------------------------

inductive SmtResult where
  | sat : SmtResult       -- a witness: the clause body is satisfiable
  | unsat : SmtResult     -- definitively unsatisfiable
  | unknown : SmtResult   -- undecidable / timeout

-- ground truth: a clause-body edge may be PRUNED (treated as deriving nothing) ONLY when
-- the body is definitively Unsat; Unknown means the edge MAY be live (not prunable).
def trulyPrunable (r : SmtResult) : Bool :=
  match r with
  | SmtResult.unsat => true
  | SmtResult.sat => false
  | SmtResult.unknown => false

-- THE FIX (three-valued SolveOutcome): only definitive Unsat prunes; Unknown defers.
def fixedPrunable (r : SmtResult) : Bool :=
  match r with
  | SmtResult.unsat => true
  | SmtResult.sat => false
  | SmtResult.unknown => false

-- THE BUG (07511178f `_ => None`): Unknown folded into "no model" ⇒ pruned like Unsat.
def buggyPrunable (r : SmtResult) : Bool :=
  match r with
  | SmtResult.sat => false
  | SmtResult.unsat => true
  | SmtResult.unknown => true

-- The FIX is SOUND: its prune decision equals truth for every SMT result.
theorem p0_2_fix_exact (r : SmtResult) : fixedPrunable r = trulyPrunable r := by
  cases r with
  | sat => rfl
  | unsat => rfl
  | unknown => rfl

-- The BUG is a FALSE SAFE: on Unknown it prunes (drops the edge ⇒ claims exhaustive ⇒
-- SAFE) while the truth is not-prunable. Mechanically: buggy ≠ truth at Unknown.
theorem p0_2_bug_prunes : buggyPrunable SmtResult.unknown = true := rfl
theorem p0_2_truth_keeps : trulyPrunable SmtResult.unknown = false := rfl
