/- Copyright 2026 Andrew Yates. Apache-2.0.
   Interpretation of untrusted source CLAIMS, not authenticated Rust semantics. -/
import SourceWord64RecordOriginal
import SemRWord64Pair
namespace SourceWord64Evaluation
open SourceWord64Record

def operandValue (arguments : List Nat) : Operand → Option Nat
  | .parameter index => arguments[index]?
  | .literal value => if value < SemR.modulus 64 then some value else none

/-- The registered tag is interpreted as a CLAIM about a builtin. Decoding
    cannot authenticate that tag. An ordinary Rust call is never an intrinsic
    and needs a separate source/body refinement before it can be evaluated. -/
def evaluate (record : Record) (arguments : List Nat) : Option Nat := do
  if !valid record || arguments.length != record.parameters.length ||
      arguments.any (fun value => SemR.modulus 64 ≤ value) then none else do
  match record.body with
  | .operand _ value => operandValue arguments value
  | .call _ _ false _ _ _ _ _ => none
  | .call _ _ true false _ _ _ _ => none
  | .call _ _ true true _ left _ right =>
    let left ← operandValue arguments left
    let right ← operandValue arguments right
    pure ((left + right) % SemR.modulus 64)

theorem ordinary_call_unresolved (record : Record) (arguments : List Nat)
    (node : Nat) (definition : Definition) (generic : Bool)
    (leftNode rightNode : Nat) (left right : Operand)
    (body : record.body = .call node definition false generic leftNode left rightNode right) :
    evaluate record arguments = none := by
  simp [evaluate, body]

theorem retained_evaluates (left right : Nat)
    (leftValid : left < SemR.modulus 64) (rightValid : right < SemR.modulus 64) :
    evaluate SourceWord64RecordOriginal.original [left, right] =
      some ((left + right) % SemR.modulus 64) := by
  simp [evaluate, SourceWord64RecordOriginal.original, valid, validOperand,
    operandValue, Nat.not_le_of_lt leftValid,
    Nat.not_le_of_lt rightValid]

/-- Exact source-claim bytes and exact IR bytes, universally over both U64
    inputs. This is a record-to-IR agreement judgment. Source authenticity,
    Rust frontend correctness, ABI, world and machine code remain unproved. -/
theorem retained_agrees (left right depth : Nat)
    (leftValid : left < SemR.modulus 64) (rightValid : right < SemR.modulus 64) :
    SourceWord64Record.decode SourceWord64RecordOriginal.originalBytes =
      .ok SourceWord64RecordOriginal.original ∧
    evaluate SourceWord64RecordOriginal.original [left, right] =
      some ((left + right) % SemR.modulus 64) ∧
    SemR.runBlob SemRWord64Pair.originalBytes 0
      [.int .u64 left, .int .u64 right] 2 depth =
      .ok (.ret [.int .u64 ((left + right) % SemR.modulus 64)]) :=
  ⟨SourceWord64RecordOriginal.original_decodes,
    retained_evaluates left right leftValid rightValid,
    SemRWord64Pair.original_returns left right depth leftValid rightValid⟩

#print axioms ordinary_call_unresolved
#print axioms retained_evaluates
#print axioms retained_agrees
end SourceWord64Evaluation
