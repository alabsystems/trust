/- SPDX-License-Identifier: BSD-3-Clause
Actual pinned ASLRef extractor interchange; no ASL parser or ISA claim.
The OCaml producer is a declared source/AST TCB seam. This decoder checks the
complete packet, pin, node forms, literal bounds and caller-selected bindings.
-/
import Asl1.Import

namespace Asl1.Wire
open Arithmetic

inductive Error where
  | truncated | invalidByte | header | pin | name | type | expression | depth
  | negativeZero | trailing | importRejected | expectedName | expectedType | illTyped
  deriving DecidableEq

abbrev Parser (α : Type) := List Nat → Except Error (α × List Nat)

def byte : Parser Nat
  | [] => .error .truncated
  | value :: rest => if value < 256 then .ok (value, rest) else .error .invalidByte

def take : Nat → Parser (List Nat)
  | 0, bytes => .ok ([], bytes)
  | length + 1, bytes => do
      let (head, rest) ← byte bytes
      let (tail, rest) ← take length rest
      return (head :: tail, rest)

def unsigned : Parser Nat := fun bytes => do
  let (word, rest) ← take 8 bytes
  return (word.foldr (fun octet value => octet + 256 * value) 0, rest)

def name : Parser (List Nat) := fun bytes => do
  let (length, rest) ← byte bytes
  if length = 0 then .error .name else take length rest

def ty : Parser Ty := fun bytes => do
  let (tag, rest) ← byte bytes
  match tag with
  | 0 => return (.int, rest)
  | 1 =>
      let (width, rest) ← byte rest
      if width ≤ 64 then return (.bits width, rest) else .error .type
  | 2 => return (.bool, rest)
  | _ => .error .type

def expr : Nat → Parser RawExpr
  | 0, _ => .error .depth
  | fuel + 1, bytes => do
      let (tag, rest) ← byte bytes
      match tag with
      | 0 =>
          let (sign, rest) ← byte rest
          let (value, rest) ← unsigned rest
          if sign = 0 then return (.E_Literal .V1 (.L_Int value), rest)
          else if sign = 1 then
            if value = 0 then .error .negativeZero
            else return (.E_Literal .V1 (.L_Int (-(Int.ofNat value))), rest)
          else .error .expression
      | 1 =>
          let (width, rest) ← byte rest
          if width > 64 then .error .expression else do
            let (value, rest) ← unsigned rest
            return (.E_Literal .V1 (.L_BitVector width value), rest)
      | 2 =>
          let (value, rest) ← byte rest
          if value = 0 then return (.E_Literal .V1 (.L_Bool false), rest)
          else if value = 1 then return (.E_Literal .V1 (.L_Bool true), rest)
          else .error .expression
      | 3 =>
          let (operator, rest) ← byte rest
          let op ← if operator = 0 then .ok RawOp.ADD
                    else if operator = 1 then .ok RawOp.SUB else .error Error.expression
          let (left, rest) ← expr fuel rest
          let (right, rest) ← expr fuel rest
          return (.E_Binop .V1 op left right, rest)
      | _ => .error .expression

def magic : List Nat := [65, 83, 76, 49, 1]
-- ffad2692c4580538e8db7bf6631aa886edfc7423, ASLRefEAC1.
def sourcePin : List Nat :=
  [102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,
   55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51]

structure Profile where
  sourceName : List Nat
  typedName : List Nat
  resultType : Ty
  expression : Expr

def decode (bytes : List Nat) : Except Error Profile := do
  if bytes.length > 65536 then .error .header else do
    let (header, rest) ← take magic.length bytes
    if header ≠ magic then .error .header else do
      let (pin, rest) ← take sourcePin.length rest
      if pin ≠ sourcePin then .error .pin else do
        let (sourceName, rest) ← name rest
        let (typedName, rest) ← name rest
        let (resultType, rest) ← ty rest
        let (raw, rest) ← expr 65 rest
        if rest ≠ [] then .error .trailing else do
          match importExpr raw with
          | .error _ => .error .importRejected
          | .ok expression => return ⟨sourceName, typedName, resultType, expression⟩

-- Names and expected result type belong to the caller, not to the packet.
def checked (sourceName typedName : List Nat) (resultType : Ty) (bytes : List Nat) :
    Except Error Profile := do
  let profile ← decode bytes
  if profile.sourceName ≠ sourceName ∨ profile.typedName ≠ typedName then
    .error .expectedName
  else if profile.resultType ≠ resultType then .error .expectedType
  else if infer profile.expression ≠ some resultType then .error .illTyped
  else return profile

def evaluate (sourceName typedName : List Nat) (resultType : Ty) (bytes : List Nat) :
    Except Error (Option Literal) :=
  (checked sourceName typedName resultType bytes).map (fun profile => eval profile.expression)

def CheckedResult (sourceName typedName : List Nat) (resultType : Ty) :
    Except Error Profile → Prop
  | .error _ => True
  | .ok profile => profile.sourceName = sourceName ∧ profile.typedName = typedName ∧
      profile.resultType = resultType ∧
      ∃ value, eval profile.expression = some value ∧ typeOf value = resultType

-- Unconditional over every byte list. Acceptance is computed by the complete
-- decoder and caller binding checks; actual evaluation follows constructively
-- from typing rather than a successful-run or correspondence premise.
theorem checked_progress (sourceName typedName : List Nat) (resultType : Ty)
    (bytes : List Nat) :
    CheckedResult sourceName typedName resultType
      (checked sourceName typedName resultType bytes) := by
  unfold checked
  cases hd : decode bytes with
  | error error => trivial
  | ok profile =>
      simp only [Except.bind, bind, pure]
      split
      · trivial
      · rename_i sameNames
        split
        · trivial
        · rename_i sameType
          split
          · trivial
          · rename_i typed
            simp only [not_or, Decidable.not_not] at sameNames
            exact ⟨sameNames.1, sameNames.2, Decidable.not_not.mp sameType,
              typed_progress profile.expression resultType (Decidable.not_not.mp typed)⟩

end Asl1.Wire
