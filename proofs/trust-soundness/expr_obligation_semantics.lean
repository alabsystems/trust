-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B: LIFT the comparison-obligation fidelity from Bool/Nat models to the literal
-- obligation EXPRESSION the encoder builds. Earlier files prove `flag = condition` where the
-- flag is already a Bool (encoder_flag_keystone); this models the `ay_bindings::Expr` AST
-- itself — the BV comparison nodes (`bvUlt`/`bvEq`/`bvNot`, constants, operands) the encoder
-- assembles — with an evaluation semantics, and proves the obligation's LITERAL Expr
-- structure EVALUATES to the true panic condition. One level closer to the real datatype: the
-- remaining gap is only that the real encoder builds exactly this AST (the soundness oracle
-- validates that on the real `integer_binop_*_condition`).
--
-- The comparison fragment never wraps (the obligations compare an operand against a width /
-- length / zero directly), so a BV value is modeled by its Nat magnitude and `bvUlt` by the
-- unsigned Nat `<` — faithful for these obligations. (Carry-arithmetic overflow uses the ay
-- BvAddNoOverflow PRIMITIVE — a trust boundary, overflow_trust_boundary.lean — not this AST.)
-- Kernel-checked through clean; covered by the ouroboros gate.

def bnot (a : Bool) : Bool := match a with | true => false | false => true

theorem blt_neg_is_ble (x : Nat) : forall (m : Nat), bnot (Nat.blt x m) = Nat.ble m x := by
  induction x with
  | zero => intro m; cases m with | zero => rfl | succ k => rfl
  | succ j ihj => intro m; cases m with | zero => rfl | succ k => exact ihj k

-- A fragment of `ay_bindings::ExprValue`: exactly the nodes the comparison obligations use.
inductive Expr where
  | bvConst : Nat -> Expr          -- a literal width / length / zero
  | bvVar : Nat -> Expr            -- a runtime operand, modeled by its value
  | bvUlt : Expr -> Expr -> Expr   -- ExprValue::BvUlt (the `<` bounds check)
  | bvEq : Expr -> Expr -> Expr    -- ExprValue::BvEq  (the `== 0` div/neg check)
  | bvNot : Expr -> Expr           -- ExprValue::Not   (the obligation negates the check)

-- EVALUATION (the Expr's semantics): the BV-valued subterms to a Nat, the Bool-valued
-- obligation to a Bool. bvUlt = unsigned `<`; bvEq = `==`; bvNot = boolean negation.
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

-- The encoder's obligation EXPRESSIONS, as the literal AST it assembles.
-- SHIFT/BOUNDS/comparison-overflow: `Assert(operand < bound)` ⇒ obligation `Not(BvUlt op bnd)`.
def shiftObligationExpr (amount : Nat) (width : Nat) : Expr :=
  Expr.bvNot (Expr.bvUlt (Expr.bvVar amount) (Expr.bvConst width))
def boundsObligationExpr (idx : Nat) (len : Nat) : Expr :=
  Expr.bvNot (Expr.bvUlt (Expr.bvVar idx) (Expr.bvConst len))
-- DIV-BY-ZERO: `Assert(divisor != 0)` ⇒ may-panic obligation is `BvEq divisor 0`.
def divObligationExpr (divisor : Nat) : Expr :=
  Expr.bvEq (Expr.bvVar divisor) (Expr.bvConst 0)

-- THE LIFT: each obligation EXPRESSION, evaluated, equals the true panic condition.
theorem shift_obligation_expr_exact (amount : Nat) (width : Nat) :
    evalBool (shiftObligationExpr amount width) = Nat.ble width amount :=
  blt_neg_is_ble amount width
theorem bounds_obligation_expr_exact (idx : Nat) (len : Nat) :
    evalBool (boundsObligationExpr idx len) = Nat.ble len idx :=
  blt_neg_is_ble idx len
theorem div_obligation_expr_exact (divisor : Nat) :
    evalBool (divObligationExpr divisor) = Nat.beq divisor 0 := rfl

-- Sanity: the literal Expr decides concrete cases correctly.
theorem shift_expr_fires_at_32 : evalBool (shiftObligationExpr 40 32) = true := rfl    -- 40>=32 ⇒ overflow
theorem shift_expr_clear_at_3 : evalBool (shiftObligationExpr 3 32) = false := rfl     -- 3<32 ⇒ in range
theorem bounds_expr_fires : evalBool (boundsObligationExpr 5 3) = true := rfl          -- idx 5 >= len 3
theorem div_expr_fires_at_0 : evalBool (divObligationExpr 0) = true := rfl             -- divisor 0
theorem div_expr_clear_at_7 : evalBool (divObligationExpr 7) = false := rfl            -- divisor 7
