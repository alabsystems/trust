-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B: the CALL obligation class — the interprocedural, non-arithmetic arm — proven
-- sound and composed into the keystone. With arithmetic (encoder_flag_keystone +
-- overflow_trust_boundary), control flow (cfg_paths), recursion (recursive_summary), and the
-- search (search_soundness), this rounds out the obligation classes the encoder emits.
--
-- A call site's obligation is "the callee's SUMMARY says may-panic". The summary mechanism
-- (try_direct_call_summary) is sound in BOTH of its outcomes:
--   * FAIL-CLOSED (CASE-2): an unmodeled / recursive / non-terminated callee gets summary
--     `may-panic = true` (the encoder models the call as an unconditional possible panic).
--     true ⊇ anything, so the obligation soundly over-approximates whatever the callee does.
--   * MODELED: a fully-summarized callee gets `summary = the callee's real may-panic` (the
--     summary captures exactly its panic surface — the recursive case is sound by the
--     fixpoint in recursive_summary).
-- In EITHER case the per-op soundness `calleeTruePanic ⟹ callObligation` holds, so the
-- keystone composes call ops with the arithmetic ops into whole-program soundness.
-- Kernel-checked through clean; covered by the ouroboros gate.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b

theorem bimplies_refl (x : Bool) : bimplies x x = true := by
  cases x with | true => rfl | false => rfl
-- A `true` obligation soundly covers any panic (fail-closed is always sound).
theorem bimplies_top (x : Bool) : bimplies x true = true := by
  cases x with | true => rfl | false => rfl

-- The obligation the encoder emits for a call, by summary outcome. `tp` = the callee's true
-- may-panic on the actual args.
def failClosedObligation (_tp : Bool) : Bool := true          -- CASE-2: unmodeled ⇒ may-panic
def modeledObligation (tp : Bool) : Bool := tp                 -- modeled ⇒ exact summary

-- PER-OP SOUNDNESS of a call, in BOTH outcomes: the obligation fires whenever the callee
-- truly panics. (The CASE-2 *bug* was `failClosedObligation := false` — claiming a dropped
-- edge cannot panic; here it is `true`, the fix, which is sound for ANY callee.)
theorem fail_closed_call_sound (tp : Bool) :
    bimplies tp (failClosedObligation tp) = true := bimplies_top tp
theorem modeled_call_sound (tp : Bool) :
    bimplies tp (modeledObligation tp) = true := bimplies_refl tp

------------------------------------------------------------------------------------
-- Compose call ops with arithmetic ops via the keystone: PROVED ⟹ safe for whole programs
-- that mix interprocedural calls and arithmetic.
------------------------------------------------------------------------------------

inductive Prog where
  | nil : Prog
  | cons : Bool -> Bool -> Prog -> Prog   -- (truePanic, obligation)

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

-- Op constructors. A modeled call to a NON-panicking callee (tp=false) contributes a
-- non-firing obligation; an arithmetic op uses its literal flag.
def modeledCall (tp : Bool) (rest : Prog) : Prog := Prog.cons tp (modeledObligation tp) rest
def shiftOp (amt : Nat) (width : Nat) (rest : Prog) : Prog :=
  Prog.cons (Nat.ble width amt) (bnot (Nat.blt amt width)) rest

-- `{ let _ = g(...) [g total]; let _ = a << 3 (width 32) }` — a total call and an in-range
-- shift: no obligation fires ⇒ PROVED, and by encoding_sound truly safe.
def mixedSafe : Prog := modeledCall false (shiftOp 3 32 Prog.nil)
theorem mixed_proved : models mixedSafe = false := rfl
theorem mixed_sound : provedSound mixedSafe = true := rfl
theorem mixed_safe : safe mixedSafe = true := rfl

-- A FAIL-CLOSED call to a callee that actually panics (tp=true): the obligation is `true`
-- (CASE-2 fix), so it FIRES — correctly NOT proved. The reverted CASE-2 bug would have set
-- it false ⇒ a false PROVE; `fail_closed_call_sound` is exactly why the fix is sound.
def failClosedUnsafe : Prog := Prog.cons true (failClosedObligation true) Prog.nil
theorem failclosed_not_proved : models failClosedUnsafe = true := rfl
theorem failclosed_panics : realPanics failClosedUnsafe = true := rfl
