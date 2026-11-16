/-
SPDX-FileCopyrightText: Copyright 2022-2023 Arm Limited and/or its affiliates <open-source-office@arm.com>
SPDX-License-Identifier: BSD-3-Clause

Derived from herdtools7/asllib, ASLRefEAC1, ffad2692c4580538e8db7bf6631aa886edfc7423.
Retained source and full notice: ../reference/aslref; exact hashes: ../reference/SOURCE.json.
This is the closed, pure ADD/SUB leaf of CC1, not an AArch64 machine model.
The OCaml-to-Lean representation relation is reviewed source translation, not a
proved OCaml refinement or a completed ASL parser/typechecker/interpreter.
-/
import Init.Data.BitVec.Lemmas

namespace Asl1.Arithmetic

-- AST.mli: L_Int, L_BitVector, L_Bool; arithmetic binop constructors ADD/SUB.
inductive Op where | add | sub
  deriving DecidableEq

inductive Literal where
  | int (value : Int)
  | bits (width : Nat) (value : BitVec width)
  | bool (value : Bool)

inductive Ty where | int | bits (width : Nat) | bool
  deriving DecidableEq

def typeOf : Literal → Ty
  | .int _ => .int
  | .bits width _ => .bits width
  | .bool _ => .bool

-- The unconstrained integer and concretely known bit-width cases of
-- Typing.apply_binop_types (Typing.ml:682-684,697,710-716).
-- Named/parameterized/constrained types and all other operators are outside
-- this leaf; unsupported inputs cannot silently choose this interpretation.
def inferOp (_op : Op) : Ty → Ty → Option Ty
  | .int, .int => some .int
  | .bits n, .bits m => if n = m then some (.bits n) else none
  | .bits n, .int => some (.bits n)
  | _, _ => none

def intOp : Op → Int → Int → Int
  | .add, x, y => x + y
  | .sub, x, y => x - y

-- Operations.binop_values: Z.add/Z.sub followed by Bitvector.of_z at the
-- left width; bitvector/bitvector requires equal lengths. Bitvector.of_z's
-- low-bit extraction is represented by BitVec.ofInt (Euclidean modulus).
def execOp (op : Op) : Literal → Literal → Option Literal
  | .int x, .int y => some (.int (intOp op x y))
  | .bits n x, .bits m y =>
      if n = m then
        some (.bits n (BitVec.ofInt n (intOp op x.toNat y.toNat)))
      else none
  | .bits n x, .int y => some (.bits n (BitVec.ofInt n (intOp op x.toNat y)))
  | _, _ => none

inductive Expr where
  | literal (value : Literal)
  | binop (op : Op) (left right : Expr)

def infer : Expr → Option Ty
  | .literal value => some (typeOf value)
  | .binop op left right => do inferOp op (← infer left) (← infer right)

-- Interpreter.ml EvalELit and EvalBinop; Native.ml:102-108 delegates literal
-- operands to Operations.binop_values. This closed expression leaf has no
-- effects or environment, so it does not implement the general backend monad.
def eval : Expr → Option Literal
  | .literal value => some value
  | .binop op left right => do execOp op (← eval left) (← eval right)

theorem execOp_type (op : Op) (left right : Literal) :
    (execOp op left right).map typeOf = inferOp op (typeOf left) (typeOf right) := by
  cases left <;> cases right <;> simp [execOp, typeOf, inferOp]

theorem eval_type (expression : Expr) :
    (eval expression).map typeOf = infer expression := by
  induction expression with
  | literal value => rfl
  | binop op left right ihLeft ihRight =>
      simp only [infer]
      rw [← ihLeft, ← ihRight]
      cases hl : eval left <;> cases hr : eval right <;>
        simp [eval, hl, hr, execOp_type]

-- Every accepted type has an actual result. No successful evaluation premise.
theorem typed_progress (expression : Expr) (ty : Ty) (h : infer expression = some ty) :
    ∃ value, eval expression = some value ∧ typeOf value = ty := by
  have he := eval_type expression
  rw [h] at he
  cases hv : eval expression with
  | none => simp [hv] at he
  | some value => exact ⟨value, rfl, Option.some.inj (by simpa [hv] using he)⟩

-- Mathematical readout of ASLRef's bitvector/integer branch, including
-- negative offsets and underflow/overflow. This is not mapped-address validity.
theorem offset_modulus (op : Op) (width : Nat) (base : BitVec width) (offset : Int) :
    execOp op (.bits width base) (.int offset) =
      some (.bits width (BitVec.ofInt width (intOp op base.toNat offset))) := rfl

theorem offset_unsigned (op : Op) (width : Nat) (base : BitVec width) (offset : Int) :
    (BitVec.ofInt width (intOp op base.toNat offset)).toNat =
      (intOp op base.toNat offset % (2 ^ width : Nat)).toNat := by
  exact BitVec.toNat_ofInt _

theorem offset_no_wrap (op : Op) (width : Nat) (base : BitVec width) (offset : Int)
    (nonnegative : 0 ≤ intOp op base.toNat offset)
    (bounded : intOp op base.toNat offset < (2 ^ width : Nat)) :
    (BitVec.ofInt width (intOp op base.toNat offset)).toNat =
      (intOp op base.toNat offset).toNat := by
  rw [offset_unsigned, Int.emod_eq_of_lt nonnegative bounded]

end Asl1.Arithmetic
