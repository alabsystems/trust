/- Application and caller composition in the complete canonical context.
   No returning recursive execution is assumed: each recursive premise below
   is supplied by the constructive maker/target/application theorem. -/
import CanonicalClosureSteps

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64 TrustIr.GenericCoro.Prefix
set_option maxRecDepth 2048

theorem call_results_single_nonChar (ctx : EvalContext) (inst : Inst)
    (dest : ValueId) (ty : Ty) (value : Value)
    (types : ctx.instructionResultTypes inst [dest] 1 = .ok [ty]) (notChar : ty ≠ .Char) :
    ctx.bindCallResults inst [dest] [value] = bindResultDests [dest] [value] := by
  change StateT.bind (ctx.checkInstructionResults inst [dest] [value])
    (fun _ => bindResultDests [dest] [value]) = _
  rw [checkInstructionResults_single_nonChar ctx inst dest ty value types notChar]
  rfl

theorem application_result_types (depth : Nat) :
    (applicationContext depth).instructionResultTypes
      (.CallIndirect (valueId 0) apparent [valueId 1] .Rust) [valueId 2] 1 = .ok [.U64] := rfl

theorem caller_maker_result_types (depth : Nat) :
    (callerContext depth).instructionResultTypes
      (.Call makerId [valueId 0, valueId 1]) [valueId 3] 1 = .ok [.Closure nominal] := rfl

theorem caller_apply_result_types (depth : Nat) :
    (callerContext depth).instructionResultTypes
      (.Call applyId [valueId 3, valueId 2]) [valueId 4] 1 = .ok [.U64] := rfl

theorem application_result_bound (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run ((applicationContext depth).bindCallResults
      (.CallIndirect (valueId 0) apparent [valueId 1] .Rust) [valueId 2] [word (a * x + b)])
      (applicationEntry world a b x) = .ok ((), applicationState world a b x) := by
  rw [call_results_single_nonChar _ _ _ .U64 _ (application_result_types depth)
    (by intro impossible; cases impossible)]
  have original := ClosureU64.application_result_bound 0 world a b x
  rw [call_results_single_nonChar _ _ _ .U64 _ (by rfl)
    (by intro impossible; cases impossible)] at original
  exact original

theorem caller_maker_bound (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run ((callerContext depth).bindCallResults (.Call makerId [valueId 0, valueId 1])
      [valueId 3] [closure a b]) (tripleState world a b x) =
      .ok ((), callerPartial world a b x) := by
  rw [call_results_single_nonChar _ _ _ (.Closure nominal) _ (caller_maker_result_types depth)
    (by intro impossible; cases impossible)]
  have original := ClosureU64.maker_call_bound 0 world a b x
  rw [call_results_single_nonChar _ _ _ (.Closure nominal) _ (by rfl)
    (by intro impossible; cases impossible)] at original
  exact original

theorem caller_apply_bound (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run ((callerContext depth).bindCallResults (.Call applyId [valueId 3, valueId 2])
      [valueId 4] [word (a * x + b)]) (callerPartial world a b x) =
      .ok ((), callerState world a b x) := by
  rw [call_results_single_nonChar _ _ _ .U64 _ (caller_apply_result_types depth)
    (by intro impossible; cases impossible)]
  have original := ClosureU64.apply_call_bound 0 world a b x
  rw [call_results_single_nonChar _ _ _ .U64 _ (by rfl)
    (by intro impossible; cases impossible)] at original
  exact original

/-- The concrete return check is supplied from word_checked, not assumed as
    the result of running the callee. The complete caller frame is restored. -/
theorem typed_return_word_runs (ctx : EvalContext) (callee : EvalFunction)
    (inst : Inst) (dest : ValueId) (value : UInt64) (frame : StackFrame)
    (before restored after : MachineState)
    (returns : callee.body.returnTys = [.U64])
    (restore : restoreFrame before frame [] = restored)
    (bound : Sem.run (ctx.bindCallResults inst [dest] [word value]) restored = .ok ((), after)) :
    Sem.run (returnToCaller ctx callee inst [dest] [word value] frame) before =
      .ok (.yield (), after) := by
  unfold returnToCaller
  rw [returns]
  have arity : checkReturnArity [word value] [.U64] = .ok () := rfl
  rw [arity, one_word_not_poison, after_return_checks_ok, checked_returns_one]
  rw [run_bind, checked_return_action_runs _ _ _ _ (word_checked ctx value)]
  dsimp only [Except.bind]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [run_bind, run_get]
  dsimp only [Except.bind]
  rw [restore, run_bind, run_set]
  dsimp only [Except.bind]
  rw [run_bind, bound]
  rfl

theorem application_indirect_step (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt 1) (applicationContext depth) (depth + 2) .abort
      (.CallIndirect (valueId 0) apparent [valueId 1] .Rust, [valueId 2]))
      (applicationEntry world a b x) = .ok (.yield (), applicationState world a b x) := by
  rw [typed_dispatch_runs (recurseAt 1) (applicationContext depth) (depth + 1) .abort
    (valueId 0) apparent [valueId 1] [valueId 2] .Rust nominal targetId
    [word a, word b] [word x] [word a, word b, word x] target
    (applicationEntry world a b x) (lookup_application_closure world a b x)
    (lookup_application_arguments world a b x) (application_arguments_exact depth a b x)
    (by rfl) (by rfl) (by rfl) (three_words_not_poison a b x "CallIndirect arguments")]
  apply invoke_closure_target_runs (calleeAfter := targetState world a b x)
    (retVals := [word (a * x + b)])
  · rfl
  · rw [for_target, reset_application]
    exact target_body_evaluates depth (depth + 1) world a b x
  · exact typed_return_word_runs _ _ _ _ _ _ _ (applicationEntry world a b x) _
      (by rfl) (restore_application world a b x) (application_result_bound depth world a b x)

theorem application_returns (depth callDepth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepTermWithContext (applicationContext depth) callDepth application.cfg
      (.Return [valueId 2]) .abort) (applicationState world a b x) =
      .ok (.terminator (.Ret [word (a * x + b)]), applicationState world a b x) := by
  simp [stepTermWithContext, closureTermWithContext, stepInst, semReturn,
    Sem.run, Sem.lookupValue, Sem.getState, MachineState.lookupValue,
    applicationState, ValueMap.get, ValueMap.set, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

theorem application_body_evaluates (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (applicationContext depth) 2 (depth + 2) application.cfg ⟨0⟩
      [closure a b, word x]) (entryState world) =
      .ok ([word (a * x + b)], applicationState world a b x) := by
  rw [stepNWithContext_succ_layer]
  apply run_returning_layer (block := ClosureU64.applicationBlock)
    (bound := applicationEntry world a b x) (bodyAfter := applicationState world a b x)
  · exact application_block
  · rfl
  · exact application_parameters world a b x
  · unfold evalBody
    exact run_single_body _ _ _ _ (application_indirect_step depth world a b x)
  · exact application_returns depth (depth + 2) world a b x

theorem maker_direct_lookup (depth : Nat) :
    (callerContext depth).lookupDirectCallee makerId
      "Call: callee is a bodyless declaration" "Call: undefined function" =
      (StateT.pure maker : Sem EvalFunction) := by
  unfold EvalContext.lookupDirectCallee
  rfl

theorem application_direct_lookup (depth : Nat) :
    (callerContext depth).lookupDirectCallee applyId
      "Call: callee is a bodyless declaration" "Call: undefined function" =
      (StateT.pure application : Sem EvalFunction) := by
  unfold EvalContext.lookupDirectCallee
  rfl

theorem caller_maker_step (fuel depth callDepth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt (fuel + 1)) (callerContext depth) (callDepth + 1) .abort
      (.Call makerId [valueId 0, valueId 1], [valueId 3]))
      (tripleState world a b x) = .ok (.yield (), callerPartial world a b x) := by
  rw [direct_dispatch_runs (recurseAt (fuel + 1)) (callerContext depth) callDepth .abort
    makerId [valueId 0, valueId 1] [valueId 3] [word a, word b] maker (tripleState world a b x)
    (lookup_caller_maker_arguments world a b x) (maker_direct_lookup depth)
    (by rfl) (by rfl) (two_words_not_poison a b "Call arguments")]
  apply invoke_direct_runs (retVals := [closure a b]) (calleeAfter := makerState world a b)
  · rfl
  · rw [for_maker, reset_caller_first]
    exact maker_body_evaluates fuel depth callDepth world a b
  · exact direct_finish_runs _ _ _ _ _ _ _ (tripleState world a b x) _
      (by rfl) (one_closure_not_poison a b "Call returns")
      (restore_caller_first world a b x) (caller_maker_bound depth world a b x)

theorem caller_application_step (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt 2) (callerContext depth) (depth + 3) .abort
      (.Call applyId [valueId 3, valueId 2], [valueId 4]))
      (callerPartial world a b x) = .ok (.yield (), callerState world a b x) := by
  rw [direct_dispatch_runs (recurseAt 2) (callerContext depth) (depth + 2) .abort
    applyId [valueId 3, valueId 2] [valueId 4] [closure a b, word x] application
    (callerPartial world a b x) (lookup_caller_apply_arguments world a b x)
    (application_direct_lookup depth) (by rfl) (by rfl)
    (closure_and_word_not_poison a b x "Call arguments")]
  apply invoke_direct_runs (retVals := [word (a * x + b)])
    (calleeAfter := applicationState world a b x)
  · rfl
  · rw [for_application, reset_caller_second]
    exact application_body_evaluates depth world a b x
  · exact direct_finish_runs _ _ _ _ _ _ _ (callerPartial world a b x) _
      (by rfl) (one_word_not_poison (a * x + b) "Call returns")
      (restore_caller_second world a b x) (caller_apply_bound depth world a b x)

theorem caller_returns (depth callDepth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepTermWithContext (callerContext depth) callDepth caller.cfg
      (.Return [valueId 4]) .abort) (callerState world a b x) =
      .ok (.terminator (.Ret [word (a * x + b)]), callerState world a b x) := by
  simp [stepTermWithContext, closureTermWithContext, stepInst, semReturn,
    Sem.run, Sem.lookupValue, Sem.getState, MachineState.lookupValue,
    callerState, ValueMap.get, ValueMap.set, valueId,
    ClosureSource.useAffine, ClosureSource.apply64, ClosureSource.makeAffine,
    StateT.run, StateT.bind, StateT.get, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

theorem caller_body_evaluates (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (callerContext depth) 3 (depth + 3) caller.cfg ⟨0⟩
      [word a, word b, word x]) (entryState world) =
      .ok ([word (a * x + b)], callerState world a b x) := by
  rw [stepNWithContext_succ_layer]
  apply run_returning_layer (block := ClosureU64.callerBlock) (bound := tripleState world a b x)
    (bodyAfter := callerState world a b x)
  · exact caller_block
  · rfl
  · exact caller_parameters world a b x
  · unfold evalBody
    apply run_body_cons (middle := callerPartial world a b x)
    · exact caller_maker_step 1 depth (depth + 2) world a b x
    · exact run_single_body _ _ _ _ (caller_application_step depth world a b x)
  · exact caller_returns depth (depth + 3) world a b x

/-- The unchanged public contextual evaluator, including original entry and
    return checks, performs genuine maker → returned closure → application →
    lifted-target execution. Every non-frame field of world remains arbitrary. -/
theorem caller_evaluates (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalFunctionInContext (context depth) callerId [word a, word b, word x] 3 .abort)
      (entryState world) = .ok ([word (a * x + b)], callerState world a b x) := by
  apply contextual_entry_runs (callee := caller)
  · exact caller_lookup depth
  · rfl
  · rfl
  · exact three_words_not_poison a b x "Call arguments"
  · change Sem.run (exitUnwinding .abort
      (stepNWithContext (callerContext depth) 3 (depth + 3) caller.cfg ⟨0⟩
        [word a, word b, word x] .abort)) (entryState world) = _
    simp only [exitUnwinding]
    exact caller_body_evaluates depth world a b x
  · exact one_word_not_poison (a * x + b) "Call returns"

theorem caller_world_restored (world : MachineState) (a b x : UInt64) :
    { callerState world a b x with locals := world.locals, nextValueId := world.nextValueId } =
      world := rfl

theorem caller_inputs_restored (world : MachineState) (a b x : UInt64) :
    (callerState world a b x).locals (valueId 0) = some (word a) ∧
    (callerState world a b x).locals (valueId 1) = some (word b) ∧
    (callerState world a b x).locals (valueId 2) = some (word x) ∧
    (callerState world a b x).locals (valueId 3) = some (closure a b) ∧
    (callerState world a b x).nextValueId = 5 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms application_body_evaluates
#print axioms caller_evaluates
end CanonicalClosure
