/- Constructive non-call execution in the actual inferred canonical contexts.
   Only ordinary unchanged evaluator/state and full-range word lemmas are reused. -/
import CanonicalClosureContext

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64 TrustIr.GenericCoro.Prefix
set_option maxRecDepth 2048

theorem maker_contract (depth : Nat) :
    closureContract (makerContext depth) nominal targetId = .ok
      ({ func := apparent, captures := [.U64, .U64] },
       { params := [.U64], returns := [.U64], isVararg := false }, target) := by
  apply target_contract <;> rfl

theorem application_contract (depth : Nat) :
    closureContract (applicationContext depth) nominal targetId = .ok
      ({ func := apparent, captures := [.U64, .U64] },
       { params := [.U64], returns := [.U64], isVararg := false }, target) := by
  apply target_contract <;> rfl

theorem construction_exact (depth : Nat) (a b : UInt64) :
    makeClosureValue (makerContext depth) nominal targetId [word a, word b] =
      .ok (closure a b) := by
  apply makeClosureValue_of_checked
    (d := { func := apparent, captures := [.U64, .U64] })
    (s := { params := [.U64], returns := [.U64], isVararg := false }) (f := target)
  · exact maker_contract depth
  · rfl
  · exact pair_checked _ a b

theorem application_arguments_exact (depth : Nat) (a b x : UInt64) :
    closureCall (applicationContext depth) nominal targetId [word a, word b]
      apparent [word x] .Rust = .ok (targetId, [word a, word b, word x]) := by
  apply closureCall_of_checked
    (d := { func := apparent, captures := [.U64, .U64] })
    (s := { params := [.U64], returns := [.U64], isVararg := false }) (f := target)
  · exact application_contract depth
  · rfl
  · rfl
  · apply makeClosureValue_of_checked
      (d := { func := apparent, captures := [.U64, .U64] })
      (s := { params := [.U64], returns := [.U64], isVararg := false }) (f := target)
    · exact application_contract depth
    · rfl
    · exact pair_checked _ a b
  · rfl
  · exact argument_checked _ x

theorem maker_constructs (depth : Nat) (world : MachineState) (a b : UInt64) :
    Sem.run (stepInstWithContext (makerContext depth)
      (.MakeClosure nominal targetId [valueId 0, valueId 1])) (pairState world a b) =
      .ok (.value (some (valueId 2)), makerState world a b) := by
  rw [construction_action, lookup_pair_then, finish_construction_run,
    construction_exact depth a b]
  rfl

theorem maker_result_types (depth : Nat) :
    (makerContext depth).instructionResultTypes
      (.MakeClosure nominal targetId [valueId 0, valueId 1]) [valueId 2] 1 =
      .ok [.Closure nominal] := rfl

theorem target_multiply_types (depth : Nat) :
    (targetContext depth).instructionResultTypes
      (.BinOp .Mul .U64 (valueId 0) (valueId 2)) [valueId 3] 1 = .ok [.U64] := rfl

theorem target_add_types (depth : Nat) :
    (targetContext depth).instructionResultTypes
      (.BinOp .Add .U64 (valueId 3) (valueId 1)) [valueId 4] 1 = .ok [.U64] := rfl

/-- Reuse only the ordinary result-publication computation after the new
    context's actual source declaration association has been checked. -/
theorem maker_result_bound (depth : Nat) (world : MachineState) (a b : UInt64) :
    Sem.run ((makerContext depth).bindInstructionResults
      (.MakeClosure nominal targetId [valueId 0, valueId 1])
      (.value (some (valueId 2))) [valueId 2]) (makerState world a b) =
      .ok ((), makerState world a b) := by
  rw [bindInstructionResults_single_nonChar _ _ _ _ (.Closure nominal)
    (maker_result_types depth) (by intro impossible; cases impossible)]
  have original := ClosureU64.maker_result_bound 0 world a b
  rw [bindInstructionResults_single_nonChar _ _ _ _ (.Closure nominal)
    (by rfl) (by intro impossible; cases impossible)] at original
  exact original

theorem target_multiply_bound (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run ((targetContext depth).bindInstructionResults
      (.BinOp .Mul .U64 (valueId 0) (valueId 2))
      (.value (some (valueId 3))) [valueId 3]) (productState world a b x) =
      .ok ((), productState world a b x) := by
  rw [bindInstructionResults_single_nonChar _ _ _ _ .U64
    (target_multiply_types depth) (by intro impossible; cases impossible)]
  have original := ClosureU64.target_multiply_bound 0 world a b x
  rw [bindInstructionResults_single_nonChar _ _ _ _ .U64
    (by rfl) (by intro impossible; cases impossible)] at original
  exact original

theorem target_add_bound (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run ((targetContext depth).bindInstructionResults
      (.BinOp .Add .U64 (valueId 3) (valueId 1))
      (.value (some (valueId 4))) [valueId 4]) (targetState world a b x) =
      .ok ((), targetState world a b x) := by
  rw [bindInstructionResults_single_nonChar _ _ _ _ .U64
    (target_add_types depth) (by intro impossible; cases impossible)]
  have original := ClosureU64.target_add_bound 0 world a b x
  rw [bindInstructionResults_single_nonChar _ _ _ _ .U64
    (by rfl) (by intro impossible; cases impossible)] at original
  exact original

theorem maker_body_step (recurse : Recurse) (depth callDepth : Nat)
    (world : MachineState) (a b : UInt64) :
    Sem.run (evalBodyStep recurse (makerContext depth) callDepth .abort
      (.MakeClosure nominal targetId [valueId 0, valueId 1], [valueId 2]))
      (pairState world a b) = .ok (.yield (), makerState world a b) := by
  unfold evalBodyStep
  simp only [bind]
  rw [run_bind, maker_constructs]
  dsimp only [Except.bind]
  rw [run_bind, maker_result_bound]
  rfl

theorem maker_returns (depth callDepth : Nat) (world : MachineState) (a b : UInt64) :
    Sem.run (stepTermWithContext (makerContext depth) callDepth maker.cfg
      (.Return [valueId 2]) .abort) (makerState world a b) =
      .ok (.terminator (.Ret [closure a b]), makerState world a b) := by
  simp [stepTermWithContext, closureTermWithContext, stepInst, semReturn,
    Sem.run, Sem.lookupValue, Sem.getState, MachineState.lookupValue,
    makerState, ValueMap.get, ValueMap.set, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

theorem maker_body_evaluates (fuel depth callDepth : Nat) (world : MachineState)
    (a b : UInt64) :
    Sem.run (stepNWithContext (makerContext depth) (fuel + 1) callDepth maker.cfg ⟨0⟩
      [word a, word b]) (entryState world) = .ok ([closure a b], makerState world a b) := by
  rw [stepNWithContext_succ_layer]
  apply run_returning_layer (block := ClosureU64.makerBlock) (bound := pairState world a b)
    (bodyAfter := makerState world a b)
  · exact maker_block
  · rfl
  · exact maker_parameters world a b
  · unfold evalBody
    exact run_single_body _ _ _ _ (maker_body_step _ depth callDepth world a b)
  · exact maker_returns depth callDepth world a b

theorem target_multiply_instruction (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepInstWithContext (targetContext depth)
      (.BinOp .Mul .U64 (valueId 0) (valueId 2))) (tripleState world a b x) =
      .ok (.value (some (valueId 3)), productState world a b x) := by
  rw [binary_instruction_action, run_bind, multiplication_runs]
  rfl

theorem target_add_instruction (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepInstWithContext (targetContext depth)
      (.BinOp .Add .U64 (valueId 3) (valueId 1))) (productState world a b x) =
      .ok (.value (some (valueId 4)), targetState world a b x) := by
  rw [binary_instruction_action, run_bind, addition_runs]
  rfl

theorem target_multiply_step (recurse : Recurse) (depth callDepth : Nat)
    (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep recurse (targetContext depth) callDepth .abort
      (.BinOp .Mul .U64 (valueId 0) (valueId 2), [valueId 3])) (tripleState world a b x) =
      .ok (.yield (), productState world a b x) := by
  unfold evalBodyStep
  simp only [bind]
  rw [run_bind, target_multiply_instruction]
  dsimp only [Except.bind]
  rw [run_bind, target_multiply_bound]
  rfl

theorem target_add_step (recurse : Recurse) (depth callDepth : Nat)
    (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep recurse (targetContext depth) callDepth .abort
      (.BinOp .Add .U64 (valueId 3) (valueId 1), [valueId 4])) (productState world a b x) =
      .ok (.yield (), targetState world a b x) := by
  unfold evalBodyStep
  simp only [bind]
  rw [run_bind, target_add_instruction]
  dsimp only [Except.bind]
  rw [run_bind, target_add_bound]
  rfl

theorem target_returns (depth callDepth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepTermWithContext (targetContext depth) callDepth target.cfg
      (.Return [valueId 4]) .abort) (targetState world a b x) =
      .ok (.terminator (.Ret [word (a * x + b)]), targetState world a b x) := by
  simp [stepTermWithContext, closureTermWithContext, stepInst, semReturn,
    Sem.run, Sem.lookupValue, Sem.getState, MachineState.lookupValue,
    targetState, ValueMap.get, ValueMap.set, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

theorem target_body_evaluates (depth callDepth : Nat) (world : MachineState)
    (a b x : UInt64) :
    Sem.run (stepNWithContext (targetContext depth) 1 callDepth target.cfg ⟨0⟩
      [word a, word b, word x]) (entryState world) =
      .ok ([word (a * x + b)], targetState world a b x) := by
  rw [stepNWithContext_succ_layer]
  apply run_returning_layer (block := ClosureU64.targetBlock) (bound := tripleState world a b x)
    (bodyAfter := targetState world a b x)
  · exact target_block
  · rfl
  · exact target_parameters world a b x
  · unfold evalBody
    apply run_body_cons (middle := productState world a b x)
    · exact target_multiply_step _ depth callDepth world a b x
    · exact run_single_body _ _ _ _ (target_add_step _ depth callDepth world a b x)
  · exact target_returns depth callDepth world a b x

#print axioms maker_body_evaluates
#print axioms target_body_evaluates
end CanonicalClosure
