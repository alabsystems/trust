-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B: the MEMORY-BOUNDS obligation (the non-arithmetic Load/Store/GEP class) lifted
-- to its literal `Expr` structure. The encoder, for a GEP/Load under `check_memory_bounds`,
-- emits the out-of-bounds obligation as `final_offset.bvuge(count)` (translate.rs:810) — i.e.
-- `BvUGe(offset, count)`, the SAME comparison shape as the array-bounds arm, now over the
-- COMPUTED gep offset (`base + Σ indices`, a `BvAdd` chain). This models that literal Expr
-- (extending the fragment with BvUGe and BvAdd) and proves it evaluates to the true
-- out-of-bounds condition `offset >= count`, so the memory-bounds obligation is sound.
--
-- SCOPE: the offset is modeled as a Nat magnitude (no wrap). A gep offset that WRAPPED past
-- 2^64 could fool the `bvuge` — but real allocations are far below that and the offset is a
-- monotone index sum; the wrapping case is a separate (BV-arithmetic) concern, like overflow,
-- not the bounds-comparison this proves. Kernel-checked; gated.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b
theorem bimplies_refl (x : Bool) : bimplies x x = true := by
  cases x with | true => rfl | false => rfl

-- Expr fragment incl. BvUGe (unsigned >=, the OOB check) and BvAdd (the gep offset sum).
inductive Expr where
  | bvConst : Nat -> Expr
  | bvVar : Nat -> Expr
  | bvAdd : Expr -> Expr -> Expr
  | bvUGe : Expr -> Expr -> Expr

def evalNat : Expr -> Nat
  | Expr.bvConst n => n
  | Expr.bvVar v => v
  | Expr.bvAdd a b => Nat.add (evalNat a) (evalNat b)
  | Expr.bvUGe _ _ => 0
def evalBool : Expr -> Bool
  | Expr.bvUGe a b => Nat.ble (evalNat b) (evalNat a)   -- a >= b  ⟺  b <= a
  | Expr.bvConst _ => false
  | Expr.bvVar _ => false
  | Expr.bvAdd _ _ => false

-- The literal GEP/Load out-of-bounds obligation the encoder builds:
-- `BvUGe(BvAdd(base, index), count)` — "(base + index) >= count".
def gepBoundsObligation (base : Nat) (index : Nat) (count : Nat) : Expr :=
  Expr.bvUGe (Expr.bvAdd (Expr.bvVar base) (Expr.bvVar index)) (Expr.bvConst count)

-- The true out-of-bounds condition: the accessed offset is at or past the region size.
def outOfBounds (base : Nat) (index : Nat) (count : Nat) : Bool :=
  Nat.ble count (Nat.add base index)

-- LIFT: the literal bounds-obligation Expr evaluates to the true OOB condition (exact).
theorem gep_bounds_obligation_exact (base : Nat) (index : Nat) (count : Nat) :
    evalBool (gepBoundsObligation base index count) = outOfBounds base index count := rfl

-- PER-OP SOUNDNESS: the obligation fires whenever the access is truly out of bounds.
theorem gep_bounds_op_sound (base : Nat) (index : Nat) (count : Nat) :
    bimplies (outOfBounds base index count) (evalBool (gepBoundsObligation base index count)) = true :=
  bimplies_refl (outOfBounds base index count)

-- Sanity, decided by the literal Expr: offset 5 into a region of 3 ⇒ OOB obligation fires;
-- offset 2 into 5 ⇒ clear.
theorem gep_oob_fires : evalBool (gepBoundsObligation 4 1 3) = true := rfl   -- 4+1=5 >= 3
theorem gep_in_bounds : evalBool (gepBoundsObligation 1 1 5) = false := rfl  -- 1+1=2 < 5

------------------------------------------------------------------------------------
-- BOUNDS FIDELITY, end-to-end for the trust-vcgen ARRAY/SLICE index VC (the one class
-- proven for real, against the live emitter — not just over a chosen predicate).
--
-- The real emitter (trust-vcgen rvalue_safety.rs:346-353, unsigned arm) builds the LITERAL
-- `Formula::Ge(index, len)` with VcKind::IndexOutOfBounds — a DIRECT comparison, no base offset
-- (distinct from the GEP/memory obligation above, which sums a base into the offset). Pinned on
-- the Rust side by the test `unsigned_index_bounds_vc_is_literal_index_ge_len` in trust-vcgen.
--
-- STATED FIDELITY ASSUMPTION (not kernel-proven; the same trust-boundary shape as
-- overflow_trust_boundary.lean's carry primitive): `index >= len` IS the real Rust/MIR panic
-- condition for `arr[i]` — rustc inserts `Assert { cond: Lt(index, len), expected: true, msg:
-- BoundsCheck }`, so the access panics iff the assert's negation `index >= len` holds. clean has
-- no MIR-semantics datatype, so this correspondence is definitional + test-backed, NOT a kernel
-- theorem through MIR. Everything BELOW this line is kernel-checked given that anchor.
------------------------------------------------------------------------------------

-- The faithful clean model of the trust-vcgen array/slice index obligation: BvUGe(index, len),
-- i.e. the literal `Formula::Ge(index, len)` the emitter builds (no base offset).
def indexBoundsObligation (index : Nat) (len : Nat) : Expr :=
  Expr.bvUGe (Expr.bvVar index) (Expr.bvConst len)

-- The real Rust array index-panic condition (the stated fidelity assumption above).
def rustIndexPanics (index : Nat) (len : Nat) : Bool := Nat.ble len index

-- (1) FIDELITY: the obligation Expr evaluates EXACTLY to the Rust panic condition `index >= len`.
theorem index_obligation_is_rust_panic (index : Nat) (len : Nat) :
    evalBool (indexBoundsObligation index len) = rustIndexPanics index len := rfl

-- (2) PER-OP SOUNDNESS: whenever the access truly panics, the obligation fires
--     (realPanics ⊆ models for this op). Reuses bimplies_refl.
theorem index_panic_sound (index : Nat) (len : Nat) :
    bimplies (rustIndexPanics index len) (evalBool (indexBoundsObligation index len)) = true :=
  bimplies_refl (rustIndexPanics index len)

-- (3) THE NO-PANIC HALF (the previously-missing direction, now a theorem): PROVED — the verifier
--     shows the obligation does NOT fire — implies the access does NOT panic. By defeq the
--     obligation-false IS rustIndexPanics-false. This is the end-to-end "PROVED ⟹ no OOB panic".
theorem index_proved_implies_no_panic (index : Nat) (len : Nat) :
    (evalBool (indexBoundsObligation index len) = false) -> (rustIndexPanics index len = false) := by
  intro h
  exact h

-- (4) Concrete witnesses, decided by reading the literal obligation Expr as the Rust condition:
--     index 6 into len 5 PANICS (obligation fires); index 2 into len 5 is SAFE (proved-no-panic).
theorem rust_index_6_5_oob : evalBool (indexBoundsObligation 6 5) = true := rfl
theorem rust_index_2_5_in_bounds : evalBool (indexBoundsObligation 2 5) = false := rfl
theorem rust_index_2_5_no_panic : rustIndexPanics 2 5 = false := rfl

------------------------------------------------------------------------------------
-- GROUNDING the panic condition in OPERATIONAL access semantics (so it is DERIVED, not a free
-- predicate). Array indexing is the standard bounds-checked PARTIAL function: `arr[i]` is defined
-- iff `i < len`, and "panics" in exactly the undefined case. We model that operationally and PROVE
-- the obligation fires precisely when the access is undefined — shrinking the fidelity assumption
-- from "this predicate IS the panic condition" to "Rust's `arr[i]` is the standard partial access"
-- (definitional). Everything here is kernel-checked, axiom-free (no PropExt/Choice — pure Nat/Bool).
------------------------------------------------------------------------------------

-- The access is in bounds iff `i < len`.
def inBounds (len : Nat) (i : Nat) : Bool := Nat.blt i len

-- The bounds-checked access PANICS exactly when NOT in bounds (the undefined case of the partial
-- access function). This is the operational definition of `arr[i]`'s panic.
def accessPanics (len : Nat) (i : Nat) : Bool := bnot (inBounds len i)

-- blt/ble duality (`len <= i  ⟺  ¬(i < len)`), by the compare_sound induction shape.
theorem ble_is_not_blt (i : Nat) : forall (len : Nat), Nat.ble len i = bnot (Nat.blt i len) := by
  induction i with
  | zero => intro len; cases len with | zero => rfl | succ k => rfl
  | succ j ih => intro len; cases len with | zero => rfl | succ k => exact ih k

-- DERIVED (not stipulated): the bounds-obligation Expr evaluates to EXACTLY the operational
-- access-panic condition. So `PROVED (obligation false) ⟹ the access does not panic` is now
-- grounded in the partial-access semantics of `arr[i]`, not in a chosen predicate.
theorem index_obligation_is_access_panic (index : Nat) (len : Nat) :
    evalBool (indexBoundsObligation index len) = accessPanics len index :=
  ble_is_not_blt index len

-- The previously-free `rustIndexPanics` IS the operational access-panic — closing that gap.
theorem rust_index_panics_is_access_panic (index : Nat) (len : Nat) :
    rustIndexPanics index len = accessPanics len index :=
  ble_is_not_blt index len

-- End-to-end, grounded: PROVED (obligation false) ⟹ the operational access does NOT panic.
-- `evalBool(...)` and `accessPanics` are only PROPOSITIONALLY equal (via ble_is_not_blt), so the
-- proof transports `h` across that equality with Eq.symm/Eq.trans (no rewrite tactic).
theorem index_proved_implies_access_in_bounds (index : Nat) (len : Nat) :
    (evalBool (indexBoundsObligation index len) = false) -> (accessPanics len index = false) := by
  intro h
  exact Eq.trans (Eq.symm (ble_is_not_blt index len)) h

-- Compose into the keystone with the other classes: a program of memory accesses (each
-- carrying its true OOB and the literal bounds-obligation Expr) is PROVED ⟹ truly safe.
inductive Prog where
  | nil : Prog
  | cons : Bool -> Bool -> Prog -> Prog

def consAccess (base : Nat) (index : Nat) (count : Nat) (rest : Prog) : Prog :=
  Prog.cons (outOfBounds base index count) (evalBool (gepBoundsObligation base index count)) rest

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

theorem memory_program_sound (p : Prog) : bimplies (provedSound p) (safe p) = true := by
  induction p with
  | nil => rfl
  | cons tp ob rest ih =>
    cases tp with
    | true => cases ob with | true => rfl | false => rfl
    | false => cases ob with | true => rfl | false => exact ih

-- Two in-bounds accesses ⇒ no bounds obligation fires ⇒ PROVED + truly safe.
def mem : Prog := consAccess 1 1 5 (consAccess 0 2 4 Prog.nil)
theorem mem_proved : models mem = false := rfl
theorem mem_safe : safe mem = true := rfl
theorem mem_sound : provedSound mem = true := rfl
-- An out-of-bounds access ⇒ obligation fires ⇒ correctly not proved.
def memBad : Prog := consAccess 4 1 3 Prog.nil
theorem memBad_not_proved : models memBad = true := rfl
theorem memBad_panics : realPanics memBad = true := rfl
