/- Exact refusals of the unchanged logical evaluator. These do not waive the
   physical environment, byte, boxed-runtime or machine-call obligations. -/
import ClosureU64Caller

namespace ClosureU64
open TrustIr
set_option maxRecDepth 8192

theorem wrong_nominal_refused (depth : Nat) (a b : UInt64) :
    makeClosureValue (context depth) ⟨1⟩ targetId [word a, word b] =
      .error (.unsupported .closureDefTable "closure definition is absent") := rfl

theorem missing_code_refused (depth : Nat) (a b : UInt64) :
    makeClosureValue (context depth) nominal ⟨4⟩ [word a, word b] =
      .error (.typeError "closure target is absent") := rfl

theorem wrong_capture_arity_refused (depth : Nat) (a : UInt64) :
    makeClosureValue (context depth) nominal targetId [word a] =
      .error (.typeError "MakeClosure: capture arity mismatch") := by
  unfold makeClosureValue
  rw [code_contract]
  rfl

theorem wrong_capture_type_refused (depth : Nat) (b : UInt64) :
    makeClosureValue (context depth) nominal targetId [.bool true, word b] =
      .error (.typeError "closure value does not match its declared type") := by
  unfold makeClosureValue
  rw [code_contract]
  rfl

/-- Equal apparent shapes cannot substitute another nominal signature id. -/
def sameShapeSignatures (depth : Nat) : EvalContext :=
  { context depth with
    funcTys := fun _ =>
      some {params := [.U64], returns := [.U64], isVararg := false} }

theorem wrong_signature_id_refused (depth : Nat) (a b x : UInt64) :
    closureCall (sameShapeSignatures depth) nominal targetId [word a, word b]
      ⟨1⟩ [word x] .Rust =
      .error (.typeError "CallIndirect: closure signature id mismatch") := rfl

theorem wrong_calling_convention_refused (depth : Nat) (a b x : UInt64) :
    closureCall (context depth) nominal targetId [word a, word b]
      apparent [word x] .C =
      .error (.typeError "CallIndirect: closure calling convention mismatch") := by
  unfold closureCall
  rw [code_contract]
  rfl

def wrongPhysicalSignature (depth : Nat) : EvalContext :=
  { context depth with
    functions := fun id =>
      if id == targetId then
        some {target with body := {target.body with paramTys := [.U64, .Bool, .U64]}}
      else (context depth).functions id }

theorem wrong_physical_signature_refused (depth : Nat) :
    closureContract (wrongPhysicalSignature depth) nominal targetId =
      .error (.typeError "closure target does not have captures ++ apparent signature") := rfl

/-- The source arithmetic distinguishes the two live environment positions. -/
theorem capture_order_source_witness :
    ClosureSource.useAffine 2 3 5 = 13 ∧
    ClosureSource.useAffine 3 2 5 = 17 ∧ (13 : UInt64) ≠ 17 := by decide

/-- These are actual executions with the two capture orders, rather than a
    comparison of a source-only calculation or a closure-shape receipt. -/
theorem capture_order_execution_witness (world : MachineState) :
    Sem.run (stepNWithContext (context 0) 2 2 application.cfg ⟨0⟩
      [closure 2 3, word 5]) (entryState world) =
        .ok ([word 13], applicationState world 2 3 5) ∧
    Sem.run (stepNWithContext (context 0) 2 2 application.cfg ⟨0⟩
      [closure 3 2, word 5]) (entryState world) =
        .ok ([word 17], applicationState world 3 2 5) := by
  constructor
  · exact application_body_evaluates 0 world 2 3 5
  · exact application_body_evaluates 0 world 3 2 5

/-- A populated surrounding world: a live allocation with sixteen sentinel
    bytes, a global binding, refcount/permission state, and independent ghost
    choice/frame fields. None is an input to the affine computation. -/
def surroundingMemory : Memory :=
  (Memory.empty.alloc 16 8 0 .rustHeap).2.writeImage 1024
    (ByteImage.fill 16 (some 165))

def surroundingWorld : MachineState :=
  { MachineState.empty with
    locals := ValueMap.empty.set (valueId 99) (word 42)
    nextValueId := 100
    memory := surroundingMemory
    permissions := PermissionMap.empty.set ⟨0⟩ .owned
    refCounts := fun id => if id == ⟨0⟩ then some 7 else none
    globals := [(⟨9⟩, 1024, ⟨0⟩)]
    floatZeroChoices := FloatZeroChoiceTape.ofList [true, false, true]
    floatZeroChoiceCursor := 2
    openFrameLineages := [7, 8]
    nextFrameLineage := 9 }

theorem surrounding_memory_live :
    surroundingMemory.lookup ⟨0⟩ =
      some {
        id := ⟨0⟩
        base := 1024
        size := 16
        alive := true
        origin := .rustHeap
        requested := 16 } := by rfl

theorem surrounding_sentinel_present : surroundingMemory.bytes 1027 = some 165 := by decide

/-- The full caller's exact final state retains the entire populated memory,
    not merely its one tested sentinel byte. -/
theorem surrounding_world_execution :
    Sem.run (evalFunctionInContext (context 0) callerId [word 2, word 3, word 5] 3 .abort)
      (entryState surroundingWorld) =
      .ok ([word 13], callerState surroundingWorld 2 3 5) ∧
    (callerState surroundingWorld 2 3 5).memory = surroundingMemory ∧
    (callerState surroundingWorld 2 3 5).memory.bytes 1027 = some 165 ∧
    {callerState surroundingWorld 2 3 5 with
      locals := surroundingWorld.locals, nextValueId := surroundingWorld.nextValueId} =
      surroundingWorld := by
  exact ⟨caller_evaluates 0 surroundingWorld 2 3 5,
    rfl, surrounding_sentinel_present, caller_world_restored surroundingWorld 2 3 5⟩

/-- A full-signature match never changes the selected nominal code identity. -/
theorem wrong_code_subject_distinct (a b : UInt64) :
    closure a b ≠ Value.typedClosure nominal callerId [word a, word b] := by
  intro equal
  cases equal

#print axioms capture_order_execution_witness
#print axioms surrounding_memory_live
#print axioms surrounding_sentinel_present
#print axioms surrounding_world_execution
#print axioms wrong_code_subject_distinct
#print axioms caller_low_fuel
#print axioms caller_low_depth

end ClosureU64
