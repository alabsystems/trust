/- Original ordinary-call source claim; no source authentication or admission. -/
import SourceWord64Evaluation
namespace SourceWord64Call
open SourceWord64Record SourceWord64Evaluation
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
def callerBytes : List Nat := [84, 82, 87, 54, 52, 83, 82, 67, 1, 0, 0, 0, 54, 210, 232, 65, 126, 115, 181, 222, 59, 62, 71, 106, 64, 64, 236, 19, 2, 2, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 36, 0, 0, 0, 109, 100, 53, 61, 54, 98, 99, 55, 51, 52, 52, 97, 102, 98, 49, 53, 51, 50, 102, 52, 49, 98, 51, 55, 51, 52, 49, 49, 51, 98, 54, 101, 51, 54, 53, 55, 1, 5, 0, 0, 0, 78, 95, 187, 64, 234, 101, 239, 17, 200, 98, 214, 148, 77, 186, 118, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0]
def caller : Record := ⟨⟨16047859833313481270, 1435593026629484091⟩, [2, 4], 9, [109, 100, 53, 61, 54, 98, 99, 55, 51, 52, 52, 97, 102, 98, 49, 53, 51, 50, 102, 52, 49, 98, 51, 55, 51, 52, 49, 49, 51, 98, 54, 101, 51, 54, 53, 55], .call 5 ⟨1292363674861395790, 2627492274989589192⟩ false false 0 (.parameter 0) 2 (.parameter 1)⟩

/-- One ordinary, nongeneric call uses the exact named callee record. It may
    not substitute an arbitrary function or intrinsic interpretation. Generic
    ordinary calls still require instance evidence and remain unresolved. -/
def evaluateThrough (callee caller : Record) (arguments : List Nat) : Option Nat := do
  if !valid caller || arguments.length != caller.parameters.length ||
      arguments.any (fun value => SemR.modulus 64 ≤ value) then none else do
  match caller.body with
  | .call _ definition false false _ left _ right =>
    if definition != callee.owner then none else do
    let left ← operandValue arguments left
    let right ← operandValue arguments right
    evaluate callee [left, right]
  | _ => evaluate caller arguments

theorem caller_decodes : decode callerBytes = .ok caller := rfl

theorem wrong_owner_refused (callee caller : Record) (arguments : List Nat)
    (node : Nat) (definition : Definition) (leftNode rightNode : Nat)
    (left right : Operand)
    (body : caller.body = .call node definition false false leftNode left rightNode right)
    (different : (definition != callee.owner) = true) :
    evaluateThrough callee caller arguments = none := by
  simp [evaluateThrough, body, different]

theorem caller_evaluates (left right : Nat)
    (leftValid : left < SemR.modulus 64) (rightValid : right < SemR.modulus 64) :
    evaluateThrough SourceWord64RecordOriginal.original caller [left, right] =
      some ((left + right) % SemR.modulus 64) := by
  simp [evaluateThrough, caller, SourceWord64RecordOriginal.original,
    valid, validOperand, operandValue, Nat.not_le_of_lt leftValid,
    Nat.not_le_of_lt rightValid]
  exact ⟨by decide, retained_evaluates left right leftValid rightValid⟩

/-- Composition concerns the two exact source claims and the unchanged callee
    IR. It does not establish the caller IR, link relocation, Rust source
    semantics, physical ABI or compiler admission. -/
theorem call_claim_agrees_with_callee (left right depth : Nat)
    (leftValid : left < SemR.modulus 64) (rightValid : right < SemR.modulus 64) :
    decode callerBytes = .ok caller ∧
    evaluateThrough SourceWord64RecordOriginal.original caller [left, right] =
      some ((left + right) % SemR.modulus 64) ∧
    SemR.runBlob SemRWord64Pair.originalBytes 0
      [.int .u64 left, .int .u64 right] 2 depth =
      .ok (.ret [.int .u64 ((left + right) % SemR.modulus 64)]) :=
  ⟨caller_decodes, caller_evaluates left right leftValid rightValid,
    SemRWord64Pair.original_returns left right depth leftValid rightValid⟩

#print axioms caller_decodes
#print axioms wrong_owner_refused
#print axioms caller_evaluates
#print axioms call_claim_agrees_with_callee
end SourceWord64Call
