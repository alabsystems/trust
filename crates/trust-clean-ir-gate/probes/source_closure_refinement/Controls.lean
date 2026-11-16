/- Actual subjects for independent wrong-subject checks. They are definitions,
   never admitted theorems, axioms, or proof-registration receipts. -/
import SourceArrow
import ClosureU64Controls
namespace SourceArrowControls
open TrustIr ClosureU64

def CallerClaim (ctx : Nat → EvalContext) (source : UInt64 → UInt64 → UInt64 → UInt64) : Prop :=
  ∀ (depth : Nat) (world : MachineState) (a b x : UInt64),
    Sem.run (evalFunctionInContext (ctx depth) ⟨0⟩ [word a, word b, word x] 3 .abort)
      (entryState world) = .ok ([word (source a b x)], callerState world a b x)

def originalSubject : Prop := CallerClaim SourceProposal.context EscapingOriginal.useAffine

theorem original_subject_proved : originalSubject := SourceArrow.original_caller_refines

/-- The exact context and original source are indices of the proof. Its only
    constructor requires the real semantic refinement, not a structural receipt.
    Subject mismatch checks need not unfold the evaluator to compare indices. -/
inductive QuotationCertified (ctx : Nat → EvalContext)
    (source : UInt64 → UInt64 → UInt64 → UInt64) : Prop
  | checked (refinement : CallerClaim ctx source) : QuotationCertified ctx source

theorem original_certificate : QuotationCertified SourceProposal.context EscapingOriginal.useAffine :=
  .checked SourceArrow.original_caller_refines

def replaceFunction (ctx : EvalContext) (id : FuncId) (body : EvalFunction) : EvalContext :=
  {ctx with functions := fun index => if index == id then some body else ctx.functions index}

def wrongSource (a b x : UInt64) : UInt64 := EscapingOriginal.useAffine a b x + 1
def sourceSubject : Prop := QuotationCertified SourceProposal.context wrongSource

def wrongBody : EvalFunction := function [.U64, .U64, .U64] [.U64]
  [.BinOp .Add .U64 (valueId 0) (valueId 2),
   .BinOp .Add .U64 (valueId 3) (valueId 1)]
  [[valueId 3], [valueId 4]] (valueId 4)
def bodySubject : Prop := QuotationCertified
  (fun depth => replaceFunction (SourceProposal.context depth) ⟨3⟩ wrongBody)
  EscapingOriginal.useAffine

def wrongCode : EvalFunction := function [.U64, .U64] [.Closure ⟨0⟩]
  [.MakeClosure ⟨0⟩ ⟨2⟩ [valueId 0, valueId 1]] [[valueId 2]] (valueId 2)
def codeSubject : Prop := QuotationCertified
  (fun depth => replaceFunction (SourceProposal.context depth) ⟨1⟩ wrongCode)
  EscapingOriginal.useAffine

def wrongCaptureOrder : EvalFunction := function [.U64, .U64] [.Closure ⟨0⟩]
  [.MakeClosure ⟨0⟩ ⟨3⟩ [valueId 1, valueId 0]] [[valueId 2]] (valueId 2)
def captureSubject : Prop := QuotationCertified
  (fun depth => replaceFunction (SourceProposal.context depth) ⟨1⟩ wrongCaptureOrder)
  EscapingOriginal.useAffine

/-- A value binder is deleted from the physical signature while code and the
    original source still require it. It is not silently treated as a proof. -/
def wronglyErased : EvalFunction :=
  {SourceProposal.target with body := {SourceProposal.target.body with paramTys := [.U64, .U64]}}
def erasureSubject : Prop := QuotationCertified
  (fun depth => replaceFunction (SourceProposal.context depth) ⟨3⟩ wronglyErased)
  EscapingOriginal.useAffine

def wrongArity : EvalFunction :=
  {SourceProposal.application with
    body := {SourceProposal.application.body with paramTys := [.Closure ⟨0⟩]}}
def aritySubject : Prop := QuotationCertified
  (fun depth => replaceFunction (SourceProposal.context depth) ⟨2⟩ wrongArity)
  EscapingOriginal.useAffine

def wrongConvention : EvalFunction := {SourceProposal.target with callingConv := .C}
def conventionSubject : Prop := QuotationCertified
  (fun depth => replaceFunction (SourceProposal.context depth) ⟨3⟩ wrongConvention)
  EscapingOriginal.useAffine

theorem original_source_witness : EscapingOriginal.useAffine 2 3 5 = 13 ∧
    wrongSource 2 3 5 = 14 ∧ EscapingOriginal.useAffine 3 2 5 = 17 := by decide

/-- Populated surrounding memory is retained by the source-bound, generated
    caller proof. Fresh SSA entry deliberately replaces the old local frame. -/
theorem original_populated_world :
    Sem.run (evalFunctionInContext (SourceProposal.context 0) ⟨0⟩
      [word 2, word 3, word 5] 3 .abort) (entryState surroundingWorld) =
      .ok ([word (EscapingOriginal.useAffine 2 3 5)], callerState surroundingWorld 2 3 5) ∧
    (callerState surroundingWorld 2 3 5).memory = surroundingMemory ∧
    {callerState surroundingWorld 2 3 5 with
      locals := surroundingWorld.locals, nextValueId := surroundingWorld.nextValueId} =
      surroundingWorld := by
  exact ⟨SourceArrow.original_caller_refines 0 surroundingWorld 2 3 5,
    rfl, SourceArrow.caller_world_preserved surroundingWorld 2 3 5⟩

theorem original_low_fuel (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (SourceProposal.context depth) 2 (depth + 3)
      SourceProposal.caller.cfg ⟨0⟩ [word a, word b, word x]) (entryState world) =
      .error .outOfFuel := by
  rw [SourceArrow.generated_context, SourceArrow.generated_caller]
  exact caller_low_fuel depth world a b x

#print axioms original_subject_proved
#print axioms original_certificate
#print axioms original_source_witness
#print axioms original_populated_world
#print axioms original_low_fuel
end SourceArrowControls
