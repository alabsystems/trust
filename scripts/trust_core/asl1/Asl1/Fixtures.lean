/- SPDX-License-Identifier: BSD-3-Clause
Derived syntax/operations provenance: reference/SOURCE.json and reference/aslref/LICENSE.txt.
Only the CC1 closed arithmetic leaf is tested here. No physical frame/world claim.+-/
import Asl1.Import

namespace Asl1.Arithmetic.Fixtures

def rawBits (width unsigned : Nat) : RawExpr :=
  .E_Literal .V1 (.L_BitVector width unsigned)
def rawInt (value : Int) : RawExpr := .E_Literal .V1 (.L_Int value)
def bits (width unsigned : Nat) : Expr := .literal (.bits width (BitVec.ofNat width unsigned))
def int (value : Int) : Expr := .literal (.int value)

def saveRaw : RawExpr := .E_Binop .V1 .SUB (rawBits 64 4096) (rawInt 16)
def saveExpr : Expr := .binop .sub (bits 64 4096) (int 16)
def restoreRaw : RawExpr := .E_Binop .V1 .ADD saveRaw (rawInt 16)
def restoreExpr : Expr := .binop .add saveExpr (int 16)

def Save : Prop := importExpr saveRaw = .ok saveExpr ∧
  infer saveExpr = some (.bits 64) ∧
  eval saveExpr = some (.bits 64 (BitVec.ofNat 64 4080))
theorem save : Save := ⟨rfl, rfl, rfl⟩

def Restore : Prop := importExpr restoreRaw = .ok restoreExpr ∧
  infer restoreExpr = some (.bits 64) ∧
  eval restoreExpr = some (.bits 64 (BitVec.ofNat 64 4096))
theorem restore : Restore := ⟨rfl, rfl, rfl⟩

def Wrap : Prop :=
  eval (.binop .add (bits 64 18446744073709551615) (int 1)) =
    some (.bits 64 (BitVec.ofNat 64 0)) ∧
  eval (.binop .sub (bits 64 15) (int 16)) =
    some (.bits 64 (BitVec.ofNat 64 18446744073709551615))
theorem wrap : Wrap := ⟨rfl, rfl⟩

def WidthZeroAndNegative : Prop :=
  eval (.binop .add (bits 0 0) (int 1)) = some (.bits 0 (BitVec.ofNat 0 0)) ∧
  eval (.binop .add (bits 64 4096) (int (-16))) =
    some (.bits 64 (BitVec.ofNat 64 4080))
theorem widthZeroAndNegative : WidthZeroAndNegative := ⟨rfl, rfl⟩

def SameWidth : Prop :=
  eval (.binop .sub (bits 64 4096) (bits 64 16)) =
    some (.bits 64 (BitVec.ofNat 64 4080)) ∧
  eval (.binop .sub (int 0) (int 16)) = some (.int (-16))
theorem sameWidth : SameWidth := ⟨rfl, rfl⟩

def Refusals : Prop :=
  eval (.binop .sub (bits 64 4096) (bits 63 16)) = none ∧
  infer (.binop .sub (bits 64 4096) (bits 63 16)) = none ∧
  eval (.binop .add (int 16) (bits 64 4096)) = none ∧
  importExpr (.E_Binop .V1 .ADD (rawBits 64 4096)
    (.E_Literal .V0 (.L_Int 16))) = .error .unsupportedVersion ∧
  importExpr (rawBits 64 18446744073709551616) =
    .error (.noncanonicalBitvector 64 18446744073709551616)
theorem refusals : Refusals := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- AST.mli's complete binary-operator denominator is 26. All other 24 tags
-- refuse; the retained source census independently checks this exact list.
def unsupportedOps : List RawOp :=
  [.AND, .BAND, .BEQ, .BOR, .DIV, .DIVRM, .XOR, .EQ, .GT, .GE,
   .IMPL, .LT, .LE, .MOD, .MUL, .NE, .OR, .POW, .RDIV, .SHL,
   .SHR, .BV_CONCAT, .STR_CONCAT, .BIC]
theorem unsupported_ops_refuse :
    unsupportedOps.all (fun op => match importOp op with
      | .error (.unsupportedOperator name) => decide (name = op)
      | _ => false) = true := by decide

-- Closed false claims for independent Clean TypeMismatch controls. They stay
-- declarations with bodies of type Prop, never admitted as proofs.
def WrongLiteral : Prop := importExpr saveRaw = .ok saveExpr ∧
  infer saveExpr = some (.bits 64) ∧
  eval saveExpr = some (.bits 64 (BitVec.ofNat 64 4081))
def WrongWidth : Prop := importExpr saveRaw = .ok saveExpr ∧
  infer saveExpr = some (.bits 63) ∧
  eval saveExpr = some (.bits 64 (BitVec.ofNat 64 4080))
def WrongOperator : Prop := importExpr saveRaw = .ok
  (.binop .add (bits 64 4096) (int 16)) ∧
  infer saveExpr = some (.bits 64) ∧
  eval saveExpr = some (.bits 64 (BitVec.ofNat 64 4080))
def WrongNoWrap : Prop :=
  eval (.binop .add (bits 64 18446744073709551615) (int 1)) =
    some (.bits 64 (BitVec.ofNat 64 1)) ∧
  eval (.binop .sub (bits 64 15) (int 16)) =
    some (.bits 64 (BitVec.ofNat 64 18446744073709551615))

end Asl1.Arithmetic.Fixtures
