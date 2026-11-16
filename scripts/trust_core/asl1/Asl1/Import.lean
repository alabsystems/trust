/-
SPDX-FileCopyrightText: Copyright 2022-2023 Arm Limited and/or its affiliates <open-source-office@arm.com>
SPDX-License-Identifier: BSD-3-Clause
ASLRefEAC1 provenance and full license: ../reference/SOURCE.json and aslref/LICENSE.txt.
-/
import Asl1.Arithmetic

namespace Asl1.Arithmetic

-- A structural mirror of the relevant AST.mli constructors, retaining the
-- version at EVERY annotated node. This is an explicit interchange boundary;
-- extraction from OCaml values / parsing ASL text is not yet implemented.
inductive Version where | V0 | V1
  deriving DecidableEq

inductive RawLiteral where
  | L_Int (value : Int)
  | L_BitVector (width unsigned : Nat)
  | L_Bool (value : Bool)
  | unsupported (constructor : String)

-- AST.mli's complete polymorphic-variant binop denominator. Preserve the real
-- constructor identity instead of passing operators through a String matcher.
inductive RawOp where
  | AND | BAND | BEQ | BOR | DIV | DIVRM | XOR | EQ | GT | GE | IMPL | LT | LE
  | MOD | SUB | MUL | NE | OR | ADD | POW | RDIV | SHL | SHR | BV_CONCAT
  | STR_CONCAT | BIC
  deriving DecidableEq

inductive RawExpr where
  | E_Literal (version : Version) (value : RawLiteral)
  | E_Binop (version : Version) (operator : RawOp) (left right : RawExpr)
  | unsupported (version : Version) (constructor : String)

inductive ImportError where
  | unsupportedVersion
  | unsupportedLiteral (constructor : String)
  | unsupportedOperator (operator : RawOp)
  | unsupportedExpression (constructor : String)
  | noncanonicalBitvector (width unsigned : Nat)
  deriving DecidableEq

def importOp : RawOp → Except ImportError Op
  | .ADD => .ok .add
  | .SUB => .ok .sub
  | other => .error (.unsupportedOperator other)

def importLiteral : RawLiteral → Except ImportError Literal
  | .L_Int value => .ok (.int value)
  | .L_Bool value => .ok (.bool value)
  | .L_BitVector width unsigned =>
      if h : unsigned < 2 ^ width then
        .ok (.bits width (BitVec.ofNatLT unsigned h))
      else .error (.noncanonicalBitvector width unsigned)
  | .unsupported name => .error (.unsupportedLiteral name)

def importExpr : RawExpr → Except ImportError Expr
  | .E_Literal .V1 value => do return .literal (← importLiteral value)
  | .E_Binop .V1 name left right => do
      let op ← importOp name
      let left ← importExpr left
      let right ← importExpr right
      return .binop op left right
  | .unsupported .V1 name => .error (.unsupportedExpression name)
  | _ => .error .unsupportedVersion

def exportOp : Op → RawOp | .add => .ADD | .sub => .SUB

def exportLiteral : Literal → RawLiteral
  | .int value => .L_Int value
  | .bool value => .L_Bool value
  | .bits width value => .L_BitVector width value.toNat

def exportExpr : Expr → RawExpr
  | .literal value => .E_Literal .V1 (exportLiteral value)
  | .binop op left right =>
      .E_Binop .V1 (exportOp op) (exportExpr left) (exportExpr right)

theorem import_export_op (op : Op) : importOp (exportOp op) = .ok op := by
  cases op <;> rfl

theorem import_export_literal (value : Literal) :
    importLiteral (exportLiteral value) = .ok value := by
  cases value with
  | int value => rfl
  | bool value => rfl
  | bits width value =>
      simp only [exportLiteral, importLiteral, value.isLt, dite_true]
      rfl

theorem import_export (expression : Expr) :
    importExpr (exportExpr expression) = .ok expression := by
  induction expression with
  | literal value =>
      simp only [exportExpr, importExpr, import_export_literal]
      rfl
  | binop op left right ihLeft ihRight =>
      simp only [exportExpr, importExpr, import_export_op, ihLeft, ihRight]
      rfl

-- Pure closed expressions only. No claim that a proprietary Arm model has
-- been parsed, imported, generated, or specialized is made by this boundary.
theorem imported_typed_progress (raw : RawExpr) (expression : Expr) (ty : Ty)
    (imported : importExpr raw = .ok expression) (typed : infer expression = some ty) :
    ∃ value, importExpr raw = .ok expression ∧
      eval expression = some value ∧ typeOf value = ty := by
  obtain ⟨value, result, resultType⟩ := typed_progress expression ty typed
  exact ⟨value, imported, result, resultType⟩

end Asl1.Arithmetic
