-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B for RUNG 2 (modular discharge), the hard part: RECURSION.
--
-- Today `try_direct_call_summary` fail-closes on a recursive callee (visited-block cycle
-- detection + MAX_STATES cap both `return None`) — sound but incomplete. To summarize a
-- recursive function instead, its summary must be a FIXPOINT, and reusing it is sound only
-- if that fixpoint soundly over-approximates the panic behavior at EVERY recursion depth.
-- This is the inductive-invariant argument PDR relies on, proven here in clean.
--
-- Model: a recursive function whose body, at each level, has a local panic possibility
-- `localPanic` and then either bottoms out or recurses. `panicWithin depth` is whether it
-- can panic within `depth` levels of unrolling; the true behavior is "panics at SOME
-- depth". The FIXPOINT summary reports `localPanic` (the inductive invariant: a no-panic
-- summary requires the local op to never panic, which is then preserved across the
-- recursive call). The theorem: the summary over-approximates `panicWithin` at every depth
-- — so a modular `summary says no-panic` proof is sound for the unbounded recursion.
-- Kernel-checked through clean; covered by the ouroboros gate.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
-- Implication matching the PREMISE first, so `bimplies false _` reduces to `true` and
-- `bimplies true b` reduces to `b` — both close by rfl after one `cases`.
def bimplies (a : Bool) (b : Bool) : Bool := match a with | true => b | false => true

-- Whether the recursive callee can panic within `depth` levels of unrolling. Each level
-- contributes the same local panic possibility `localPanic` (uniform body); depth 0 is the
-- base case (no recursive level entered, no local op).
def panicWithin (localPanic : Bool) (depth : Nat) : Bool :=
  match depth with
  | Nat.zero => false
  | Nat.succ d => bor localPanic (panicWithin localPanic d)

-- THE FIXPOINT SUMMARY: the least fixpoint of `S = localPanic ∨ S` is `localPanic` — the
-- inductive invariant carried across the recursive call.
def summaryPanic (localPanic : Bool) : Bool := localPanic

-- SOUNDNESS OF THE RECURSIVE FIXPOINT: the summary over-approximates the panic behavior at
-- EVERY recursion depth. Hence `summaryPanic = false` ⟹ the callee panics at no depth, so
-- reusing the summary in a caller is sound for the unbounded recursion.
theorem recursive_summary_sound (localPanic : Bool) (depth : Nat) :
    bimplies (panicWithin localPanic depth) (summaryPanic localPanic) = true := by
  cases localPanic with
  | true =>
    -- summaryPanic true = true, so `bimplies _ true` is true at every depth.
    induction depth with
    | zero => rfl
    | succ d ih => rfl
  | false =>
    -- summaryPanic false = false; with localPanic concretely false, `bor false PW` reduces
    -- to PW so the recursive step matches the induction hypothesis.
    induction depth with
    | zero => rfl
    | succ d ih => simp only [panicWithin, bor, ih]

------------------------------------------------------------------------------------
-- A summary that does NOT carry the invariant (e.g. always reports no-panic, ignoring the
-- local op) is UNSOUND: the callee panics at depth ≥ 1 when its local op can, while the
-- buggy summary says safe — a false proof through the call site.
------------------------------------------------------------------------------------

def buggySummaryPanic (_localPanic : Bool) : Bool := false

-- On a callee whose local op CAN panic, unrolled at least once:
theorem recursion_bug_says_safe : buggySummaryPanic true = false := rfl
theorem recursion_truth_can_panic : panicWithin true (Nat.succ Nat.zero) = true := rfl
-- ...so the buggy summary drops a real reachable panic (false PROVE); the fixpoint summary
-- does not: it equals the truth's over-approximation.
theorem fixpoint_summary_flags_it : summaryPanic true = true := rfl

------------------------------------------------------------------------------------
-- THE OBLIGATION-FREE COROLLARY — grounds the trust-mc recursion-fixpoint IMPLEMENTATION
-- (`try_direct_call_summary`, trust-mc-trust-bmc/src/translate_chc.rs, commit 681557917).
--
-- That implementation proves an obligation-free SELF-recursive callee panic-free instead of
-- fail-closing: it models the recursive call by the inductive hypothesis (assume safe, havoc the
-- result) and ACCEPTS the summary only when the callee carries NO per-level obligation — its
-- `self_recursion_seen && !error_conditions.is_empty() ⇒ return None` gate. The empty-obligation
-- case is exactly `localPanic = false` here, and the theorem below is the precise soundness that
-- justifies returning a no-panic summary: an obligation-free recursive callee panics at NO depth.
------------------------------------------------------------------------------------

-- `localPanic = false` (no per-level obligation) ⟹ the callee panics at no recursion depth.
theorem obligation_free_recursion_total (depth : Nat) :
    panicWithin false depth = false := by
  induction depth with
  | zero => rfl
  | succ d ih => simp only [panicWithin, bor, ih]

-- And it is exactly a corollary of the general fixpoint soundness: the summary of an
-- obligation-free callee is `false`, which over-approximates the (false) panic behavior at every
-- depth — so the implementation's accept-when-empty rule is sound, and its fail-close-when-
-- nonempty rule is necessary (a callee WITH a per-level op panics at depth ≥ 1, above).
theorem obligation_free_summary_is_safe : summaryPanic false = false := rfl
theorem obligation_free_sound_at_every_depth (depth : Nat) :
    bimplies (panicWithin false depth) (summaryPanic false) = true :=
  recursive_summary_sound false depth
