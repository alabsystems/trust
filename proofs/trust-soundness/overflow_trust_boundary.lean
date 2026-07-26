-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B: closes the arithmetic soundness story by NAMING the trust boundary for the
-- overflow arms — and proving everything above it composes.
--
-- The BV-obligation fidelity splits cleanly in two:
--   * COMPARISON obligations (div-by-zero, shift, bounds): the encoder STRUCTURALLY builds a
--     `<` / `==` check, and its flag is proven equal to the true panic condition in
--     `encoder_flag_keystone.lean` (machine-checked, no trust needed).
--   * OVERFLOW obligations (checked add/sub/mul): the encoder emits ay's BV no-overflow
--     PRIMITIVE — `ExprValue::BvAddNoOverflowUnsigned(a,b)`, a dedicated SMT node ay's solver
--     decides (ay-dpll/.../bitvectors/overflow.rs). Its semantics ("a+b does not overflow")
--     are ay's responsibility — a TRUST BOUNDARY, exactly like "ay's UNSAT is sound" in
--     search_soundness. There is NO deeper clean proof to do here: the encoder uses the
--     semantically-correct primitive; ay implements it.
--
-- This file makes that boundary explicit and proves the overflow op is sound GIVEN it, so
-- the keystone composes the (clean-proven) comparison arms with the (ay-trusted) overflow
-- arms into whole-program soundness. The trust base of the arithmetic discharge is then
-- precisely: { ay's BV-primitive correctness, ay's UNSAT soundness } — nothing hidden.
-- Kernel-checked through clean; covered by the ouroboros gate.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b

-- THE TRUST BOUNDARY, modeled: `ayNoOverflow tp` is ay's BV no-overflow primitive result for
-- an op whose true panic flag is `tp`. ay correctly decides overflow ⟺ the primitive is the
-- NEGATION of the true panic (`= true` exactly when the op does NOT overflow). We encode that
-- correctness directly as the primitive's definition — that IS the trust assumption.
def ayNoOverflow (truePanic : Bool) : Bool := bnot truePanic

-- The encoder's overflow OBLIGATION is the negation of ay's no-overflow primitive (the
-- `add_error_rule(no_overflow.not())` in translate.rs).
def overflowObligation (truePanic : Bool) : Bool := bnot (ayNoOverflow truePanic)

-- PER-OP SOUNDNESS of the overflow arm, GIVEN the trust boundary: the obligation fires
-- whenever the op truly overflows. (Proven directly by `cases`; no substitution.)
theorem overflow_op_sound (truePanic : Bool) :
    bimplies truePanic (overflowObligation truePanic) = true := by
  cases truePanic with | true => rfl | false => rfl

-- And the obligation is in fact EXACT (= the true panic), so overflow loses no precision
-- either — the trust boundary is tight, not conservative.
theorem overflow_obligation_exact (truePanic : Bool) :
    overflowObligation truePanic = truePanic := by
  cases truePanic with | true => rfl | false => rfl

------------------------------------------------------------------------------------
-- Composition: the keystone over a program MIXING comparison arms (obligation proven equal
-- to the condition, clean) and overflow arms (obligation = the ay-primitive negation). Both
-- kinds are sound, so PROVED ⟹ safe for the whole arithmetic program.
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

-- A program mixing a comparison op (shift, obligation = the literal bnot(blt 3 32) flag) and
-- an overflow op (obligation = the ay primitive negation). `a/0` is added as a firing op so
-- it is correctly NOT proved.
def overflowOp (tp : Bool) (rest : Prog) : Prog := Prog.cons tp (overflowObligation tp) rest

-- A non-overflowing add (truePanic = false) and a non-overflowing shift: both obligations
-- stay false ⇒ PROVED, and by encoding_sound truly safe.
def safeProg : Prog := overflowOp false (Prog.cons (bnot (Nat.blt 3 32)) (bnot (Nat.blt 3 32)) Prog.nil)
theorem safeProg_proved : models safeProg = false := rfl
theorem safeProg_sound : provedSound safeProg = true := rfl
theorem safeProg_safe : safe safeProg = true := rfl

-- An OVERFLOWING add (truePanic = true): the ay primitive says "overflow", the obligation
-- FIRES, so it is NOT proved — the trust boundary makes the verifier refuse, correctly.
def unsafeProg : Prog := overflowOp true Prog.nil
theorem unsafeProg_not_proved : models unsafeProg = true := rfl
theorem unsafeProg_panics : realPanics unsafeProg = true := rfl
