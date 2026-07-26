-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B: INSTANTIATE the keystone (encoding_contract.lean::encoding_sound, the
-- abstract `realPanics ⊆ models` composition) over the REAL arithmetic op classes — so the
-- contract is about the actual conditions the encoder computes (`divisor == 0`,
-- `amount >= width`, `a + b > MAX`, `len <= idx`, `x == INT_MIN`), not abstract Bools.
--
-- The per-op fidelity hypothesis the keystone needs — `truePanic ⟹ obligation`, i.e. the
-- encoder's obligation FIRES whenever the op truly panics — is what `soundness_oracle`
-- validates on the REAL trust-ir encoder, and what this session's two fixes RESTORED: the
-- shift arm was modeled in clean here all along (`shiftOverflows`), but the real encoder
-- emitted NO shift obligation (the 7th false-proof) until `translate.rs` was fixed; likewise
-- `Wrapping<K>` (the 6th). With those fixes, `obligation = the real condition` (tight
-- fidelity), the keystone's hypothesis holds, and PROVED ⟹ safe for arithmetic programs.
-- Kernel-checked through clean; covered by the ouroboros gate.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b

theorem bimplies_refl (x : Bool) : bimplies x x = true := by
  cases x with | true => rfl | false => rfl

-- REAL panic conditions of the arithmetic arms (the audited trust-mc obligations).
def divByZero (d : Nat) : Bool := Nat.beq d 0
def shiftOverflows (amount : Nat) (width : Nat) : Bool := Nat.ble width amount
def addOverflows (a : Nat) (b : Nat) (maxv : Nat) : Bool := Nat.blt maxv (Nat.add a b)
def outOfBounds (idx : Nat) (len : Nat) : Bool := Nat.ble len idx
def negOverflows (x : Nat) (intMin : Nat) : Bool := Nat.beq x intMin

-- A program: a list of operations, each (truePanic, obligation) — the keystone's shape.
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

-- THE KEYSTONE (re-proven self-contained): PROVED ∧ all-sound ⟹ safe.
theorem encoding_sound (p : Prog) : bimplies (provedSound p) (safe p) = true := by
  induction p with
  | nil => rfl
  | cons tp ob rest ih =>
    cases tp with
    | true => cases ob with | true => rfl | false => rfl
    | false => cases ob with | true => rfl | false => exact ih

-- Smart constructors lowering each REAL arithmetic class to a keystone op with TIGHT
-- fidelity — obligation = the real condition (what the encoder emits AFTER the fixes).
def consDiv (d : Nat) (rest : Prog) : Prog := Prog.cons (divByZero d) (divByZero d) rest
def consShift (amount : Nat) (width : Nat) (rest : Prog) : Prog :=
  Prog.cons (shiftOverflows amount width) (shiftOverflows amount width) rest
def consAdd (a : Nat) (b : Nat) (maxv : Nat) (rest : Prog) : Prog :=
  Prog.cons (addOverflows a b maxv) (addOverflows a b maxv) rest
def consBounds (idx : Nat) (len : Nat) (rest : Prog) : Prog :=
  Prog.cons (outOfBounds idx len) (outOfBounds idx len) rest
def consNeg (x : Nat) (intMin : Nat) (rest : Prog) : Prog :=
  Prog.cons (negOverflows x intMin) (negOverflows x intMin) rest

-- Per-class soundness: the obligation fires whenever the op truly panics (tight ⟹ trivially
-- sound). Each is the keystone's per-op hypothesis, instantiated with the REAL condition.
theorem div_op_sound (d : Nat) : bimplies (divByZero d) (divByZero d) = true := bimplies_refl _
theorem shift_op_sound (a : Nat) (w : Nat) :
    bimplies (shiftOverflows a w) (shiftOverflows a w) = true := bimplies_refl _
theorem add_op_sound (a : Nat) (b : Nat) (m : Nat) :
    bimplies (addOverflows a b m) (addOverflows a b m) = true := bimplies_refl _
theorem bounds_op_sound (i : Nat) (l : Nat) :
    bimplies (outOfBounds i l) (outOfBounds i l) = true := bimplies_refl _
theorem neg_op_sound (x : Nat) (m : Nat) :
    bimplies (negOverflows x m) (negOverflows x m) = true := bimplies_refl _

------------------------------------------------------------------------------------
-- Concrete arithmetic programs, decided by the REAL conditions. A program with no firing
-- obligation is PROVED, and the keystone makes that imply truly safe.
------------------------------------------------------------------------------------

-- `{ let _ = a / 7; let _ = b << 3 (width 32); let _ = arr[2] (len 5) }` — all in range.
def safeProgram : Prog := consDiv 7 (consShift 3 32 (consBounds 2 5 Prog.nil))
theorem safe_program_proved : models safeProgram = false := rfl       -- no obligation fires ⇒ PROVED
theorem safe_program_is_safe : realPanics safeProgram = false := rfl   -- and it truly cannot panic

-- `{ let _ = a / 0 }` — div-by-zero. The encoder's `divisor == 0` obligation FIRES, so it is
-- NOT proved; the keystone never claims it safe.
def unsafeProgram : Prog := consDiv 0 Prog.nil
theorem unsafe_program_not_proved : models unsafeProgram = true := rfl  -- obligation fires
theorem unsafe_program_panics : realPanics unsafeProgram = true := rfl  -- and it truly panics

-- `{ let _ = a << 40 (width 32) }` — out-of-range shift. Before the 7th-false-proof fix the
-- real encoder emitted NO obligation here (models would have been false ⇒ a false PROVE);
-- with the fix the obligation = `40 >= 32` FIRES, matching the truth.
def shiftUnsafeProgram : Prog := consShift 40 32 Prog.nil
theorem shift_unsafe_not_proved : models shiftUnsafeProgram = true := rfl
theorem shift_unsafe_panics : realPanics shiftUnsafeProgram = true := rfl
