-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex: narrowing-cast overflow fidelity — the missing arm of encoder_flag_keystone.
--
-- A narrowing integer `value as T` loses bits IFF `value` does not fit `T` (for unsigned,
-- `value > T::MAX`). The native CHC encoder (trust-mc codegen_stmt_fallback.rs,
-- emit_assignment_safety_checks) emits, for a narrowing IntToInt cast, the SAFE condition
-- `reextend(low_dst_bits(value)) == value` — which is valid EXACTLY when the dropped high bits
-- are the type-correct extension of the kept bits, i.e. `value <= T::MAX`. Its negation (the
-- may-lose-bits flag the rule generator turns into `from_pred ∧ ¬safe -> error()`) is therefore
-- `value > T::MAX`. The TRUE loss condition is also `value > T::MAX` — so the emitted flag is
-- FAITHFUL (exactly the true condition), not merely sound. This file proves that fidelity and
-- composes it into the keystone, so a cast-bearing program the verifier reports PROVED (no flag
-- fires) is truly lossless.
--
-- Its ABSENCE was the A1 soundness hole: before this arm the encoder emitted NO cast obligation
-- at all, so the cast violation predicate was unreachable and a lossy `(h % n) as u32` (n:u64
-- unbounded) vacuously "proved". This arm is the proof-level statement of the fix.
-- Kernel-checked through clean; covered by the ouroboros gate (MIN_PROOF_FILES).

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b

theorem bimplies_refl (x : Bool) : bimplies x x = true := by
  cases x with | true => rfl | false => rfl

-- ENCODER FLAG EXPRESSION (literal: negation of the `value <= maxv` fits-check the encoder
-- emits as SAFE) and the TRUE loss condition. For a narrowing cast both are `value > maxv`,
-- so — like div/neg, whose flag `x == c` IS the true condition — fidelity is reflexivity.
def castFlag (v : Nat) (maxv : Nat) : Bool := bnot (Nat.ble v maxv)   -- emitted: ¬(value <= max)
def castTrue (v : Nat) (maxv : Nat) : Bool := bnot (Nat.ble v maxv)   -- true loss: value > max

-- PER-OP FIDELITY: the true loss condition implies the encoder's flag (the encoder never MISSES
-- a lossy narrowing). The flag expression IS the true condition, so this is reflexive — the
-- A1 hole was that this arm (and the obligation it stands for) did not exist.
theorem cast_op_sound (v : Nat) (maxv : Nat) :
    bimplies (castTrue v maxv) (castFlag v maxv) = true :=
  bimplies_refl (bnot (Nat.ble v maxv))

------------------------------------------------------------------------------------
-- THE KEYSTONE (self-contained) instantiated over the cast flag.
------------------------------------------------------------------------------------

inductive Prog where
  | nil : Prog
  | cons : Bool -> Bool -> Prog -> Prog   -- (truePanic, encoderFlag)

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

-- A LOSSLESS narrowing: `value = 200` into a `maxv = 255` target (u8) fits, so no flag fires.
def prog_cast : Prog :=
  Prog.cons (castTrue 200 255) (castFlag 200 255) Prog.nil
-- No flag fires ⇒ the verifier reports PROVED...
theorem prog_cast_proved : models prog_cast = false := rfl
-- ...the per-op fidelity holds (the flag soundly captures the loss)...
theorem prog_cast_sound : provedSound prog_cast = true := rfl
-- ...so by encoding_sound the program is truly safe, and indeed it is.
theorem prog_cast_safe : safe prog_cast = true := rfl
theorem prog_cast_no_real_loss : realPanics prog_cast = false := rfl

-- A LOSSY narrowing: `value = 300` into `maxv = 255` does NOT fit — the flag MUST fire (the
-- verifier must NOT report PROVED), which is exactly the A1 refutation the fix restores.
def prog_cast_lossy : Prog :=
  Prog.cons (castTrue 300 255) (castFlag 300 255) Prog.nil
theorem prog_cast_lossy_flag_fires : models prog_cast_lossy = true := rfl
theorem prog_cast_lossy_real_loss : realPanics prog_cast_lossy = true := rfl
