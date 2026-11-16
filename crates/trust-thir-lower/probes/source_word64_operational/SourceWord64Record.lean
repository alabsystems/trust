/- Copyright 2026 Andrew Yates. Apache-2.0.
   Decoder for untrusted THIR source claims. No source or compiler authority. -/
import SemR
namespace SourceWord64Record
open SemR
structure Definition where
  crateId : Nat
  localHash : Nat
  deriving Repr, BEq
inductive Operand where
  | parameter (index : Nat)
  | literal (value : Nat)
  deriving Repr, BEq
inductive Body where
  | operand (node : Nat) (value : Operand)
  | call (node : Nat) (definition : Definition) (registered genericU64 : Bool)
      (leftNode : Nat) (left : Operand) (rightNode : Nat) (right : Operand)
  deriving Repr, BEq
structure Record where
  owner : Definition
  parameters : List Nat
  expressions : Nat
  sourceHash : List Nat
  body : Body
  deriving Repr, BEq

def readDefinition : P Definition := do
  let crateId ← u64
  let localHash ← u64
  pure ⟨crateId, localHash⟩
def readOperand : P Operand := do
  match ← u8 with
  | 0 => return .parameter (← u32)
  | 1 => return .literal (← u64)
  | _ => bad "unknown source operand opcode"
def validOperand (r : Record) (node : Nat) (operand : Operand) : Bool :=
  node < r.expressions && match operand with
  | .parameter index => index < r.parameters.length
  | .literal _ => true
def valid (r : Record) : Bool :=
  (r.parameters.length == 1 || r.parameters.length == 2) &&
  (r.parameters.length != 2 || r.parameters[0]? != r.parameters[1]?) &&
  0 < r.expressions && r.expressions ≤ 64 &&
  0 < r.sourceHash.length && r.sourceHash.length ≤ 256 &&
  match r.body with
  | .operand node value => validOperand r node value
  | .call node _ registered generic leftNode left rightNode right =>
    node < r.expressions && leftNode != rightNode && leftNode != node &&
    rightNode != node && (!registered || generic) &&
    validOperand r leftNode left && validOperand r rightNode right

def readRecord : P Record := do
  let magic ← rep 8 u8
  if magic != [84, 82, 87, 54, 52, 83, 82, 67] then bad "source record magic" else do
  if (← u32) != 1 then bad "source record schema" else do
  let owner ← readDefinition
  let count ← u8
  if count != 1 && count != 2 then bad "source parameter population" else do
  let parameters ← rep count u32
  let expressions ← u32
  let length ← u32
  if length > 256 then bad "source hash representation budget" else do
  let sourceHash ← rep length u8
  if !utf8Ok sourceHash.length sourceHash then bad "source hash UTF8" else do
  let tag ← u8
  let node ← u32
  let body : Body ← match tag with
    | 0 => do
      let value ← readOperand
      pure (Body.operand node value)
    | 1 | 2 => do
      let definition ← readDefinition
      let generic ← boolB
      let leftNode ← u32
      let left ← readOperand
      let rightNode ← u32
      let right ← readOperand
      pure (.call node definition (tag == 2) generic leftNode left rightNode right)
    | _ => bad "unknown source body opcode"
  let record := Record.mk owner parameters expressions sourceHash body
  if valid record then pure record else bad "source record population"

def decode (bytes : List Nat) : Except DErr Record :=
  if bytes.length > 4096 || bytes.any (fun b => 255 < b) then
    .error (.malformed "source record byte budget or non-byte")
  else match readRecord 1 #[] bytes with
    | .ok record [] => .ok record
    | .ok _ (_ :: _) => .error (.malformed "trailing source record bytes")
    | .err error => .error error
end SourceWord64Record
