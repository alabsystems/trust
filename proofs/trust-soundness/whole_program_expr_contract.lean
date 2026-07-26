-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B: the whole-program contract `realPanics ⊆ models` over LITERAL obligation
-- EXPRESSIONS. whole_program_contract.lean composes obligation classes as abstract Bools;
-- expr_obligation_semantics.lean models the `ay_bindings::Expr` AST and proves each
-- obligation EXPRESSION evaluates to its condition. This unifies them: each op carries the
-- actual Expr the encoder builds, the program's `models` is the disjunction of those
-- expressions EVALUATED, and PROVED (no obligation Expr evaluates true) ⟹ truly safe — the
-- contract one level closer to the live encoder, where the obligation IS an AST node.
-- Kernel-checked through clean; covered by the ouroboros gate.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b
theorem bimplies_refl (x : Bool) : bimplies x x = true := by
  cases x with | true => rfl | false => rfl

-- comparison soundness: encoder flag `bnot(blt value bound)` implied by true `ble bound value`.
theorem compare_sound (value : Nat) :
    forall (bound : Nat), bimplies (Nat.ble bound value) (bnot (Nat.blt value bound)) = true := by
  induction value with
  | zero => intro bound; cases bound with | zero => rfl | succ k => rfl
  | succ j ihj => intro bound; cases bound with | zero => rfl | succ k => exact ihj k

-- The Expr AST fragment + evaluation (as in expr_obligation_semantics.lean).
inductive Expr where
  | bvConst : Nat -> Expr
  | bvVar : Nat -> Expr
  | bvUlt : Expr -> Expr -> Expr
  | bvEq : Expr -> Expr -> Expr
  | bvNot : Expr -> Expr

def evalNat : Expr -> Nat
  | Expr.bvConst n => n
  | Expr.bvVar v => v
  | Expr.bvUlt _ _ => 0
  | Expr.bvEq _ _ => 0
  | Expr.bvNot _ => 0
def evalBool : Expr -> Bool
  | Expr.bvUlt a b => Nat.blt (evalNat a) (evalNat b)
  | Expr.bvEq a b => Nat.beq (evalNat a) (evalNat b)
  | Expr.bvNot e => bnot (evalBool e)
  | Expr.bvConst _ => false
  | Expr.bvVar _ => false

-- An op kind, with its true panic and the LITERAL obligation Expr the encoder emits.
inductive Op where
  | shift : Nat -> Nat -> Op    -- amount, width
  | bounds : Nat -> Nat -> Op   -- idx, len
  | div : Nat -> Op             -- divisor

def opTrue : Op -> Bool
  | Op.shift amt width => Nat.ble width amt
  | Op.bounds idx len => Nat.ble len idx
  | Op.div d => Nat.beq d 0

def opObExpr : Op -> Expr
  | Op.shift amt width => Expr.bvNot (Expr.bvUlt (Expr.bvVar amt) (Expr.bvConst width))
  | Op.bounds idx len => Expr.bvNot (Expr.bvUlt (Expr.bvVar idx) (Expr.bvConst len))
  | Op.div d => Expr.bvEq (Expr.bvVar d) (Expr.bvConst 0)

-- The obligation Bool = the literal obligation EXPRESSION evaluated.
def opObligation (o : Op) : Bool := evalBool (opObExpr o)

-- PER-OP SOUNDNESS over the literal Expr: the obligation EXPRESSION fires whenever the op
-- truly panics. `opObligation` reduces (evalBool definitional) to the encoder flag, then the
-- comparison/refl lemmas close it.
theorem op_sound (o : Op) : bimplies (opTrue o) (opObligation o) = true := by
  cases o with
  | shift amt width => exact compare_sound amt width
  | bounds idx len => exact compare_sound idx len
  | div d => exact bimplies_refl (Nat.beq d 0)

-- A program of (truePanic, evaluated-obligation) pairs; ops embedded via consOp (which
-- EVALUATES the literal obligation Expr).
inductive Prog where
  | nil : Prog
  | cons : Bool -> Bool -> Prog -> Prog

def consOp (o : Op) (rest : Prog) : Prog := Prog.cons (opTrue o) (opObligation o) rest

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

-- THE CONTRACT over literal Expr obligations: PROVED (no obligation Expr evaluates true) and
-- every op sound ⟹ truly safe. realPanics ⊆ models, `models` = the disjunction of the
-- encoder's actual obligation EXPRESSIONS evaluated.
theorem whole_program_expr_sound (p : Prog) :
    bimplies (provedSound p) (safe p) = true := by
  induction p with
  | nil => rfl
  | cons tp ob rest ih =>
    cases tp with
    | true => cases ob with | true => rfl | false => rfl
    | false => cases ob with | true => rfl | false => exact ih

-- A concrete program whose obligations are LITERAL ASTs: `b << 3 (width 32); a / 7;
-- arr[2] (len 5)`. No obligation Expr evaluates true ⇒ PROVED, and by the contract safe.
def prog : Prog := consOp (Op.shift 3 32) (consOp (Op.div 7) (consOp (Op.bounds 2 5) Prog.nil))
theorem prog_proved : models prog = false := rfl
theorem prog_sound : provedSound prog = true := rfl
theorem prog_safe : safe prog = true := rfl
theorem prog_no_panic : realPanics prog = false := rfl

-- Flip the shift out-of-range: its obligation Expr `Not(BvUlt 40 32)` evaluates TRUE, so the
-- program is correctly NOT proved — decided by the literal AST.
def progUnsafe : Prog := consOp (Op.shift 40 32) prog
theorem progUnsafe_not_proved : models progUnsafe = true := rfl
theorem progUnsafe_panics : realPanics progUnsafe = true := rfl
