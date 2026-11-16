/- Constructive caller composition: maker → returned closure → application
   parameter → exact lifted target, with original call frame restoration. -/
import ClosureU64Application
namespace ClosureU64
open TrustIr
open TrustIr.GenericCoro.Prefix
set_option maxRecDepth 1024

theorem lookup_caller_maker_arguments (world : MachineState) (a b x : UInt64) :
    Sem.run ([valueId 0, valueId 1].mapM Sem.lookupValue) (tripleState world a b x) =
      .ok ([word a, word b], tripleState world a b x) := rfl

theorem lookup_caller_apply_arguments (world : MachineState) (a b x : UInt64) :
    Sem.run ([valueId 3, valueId 2].mapM Sem.lookupValue) (callerPartial world a b x) =
      .ok ([closure a b, word x], callerPartial world a b x) := rfl

theorem maker_abi_untyped : requireUntypedAbi maker.body.abi = (StateT.pure () : Sem Unit) := rfl

theorem application_abi_untyped :
    requireUntypedAbi application.body.abi = (StateT.pure () : Sem Unit) := rfl

theorem maker_arity (a b : UInt64) : checkCallArity [word a, word b] maker.body.paramTys = .ok () := rfl

theorem application_arity (a b x : UInt64) :
    checkCallArity [closure a b, word x] application.body.paramTys = .ok () := rfl

theorem maker_return_arity (a b : UInt64) :
    checkReturnArity [closure a b] maker.body.returnTys = .ok () := rfl

theorem application_return_arity (value : UInt64) :
    checkReturnArity [word value] application.body.returnTys = .ok () := rfl

theorem two_words_not_poison (a b : UInt64) (operation : String) :
    Sem.rejectPoisonValues [word a, word b] operation = (StateT.pure () : Sem Unit) := rfl

theorem closure_and_word_not_poison (a b x : UInt64) (operation : String) :
    Sem.rejectPoisonValues [closure a b, word x] operation = (StateT.pure () : Sem Unit) := rfl

theorem one_closure_not_poison (a b : UInt64) (operation : String) :
    Sem.rejectPoisonValues [closure a b] operation = (StateT.pure () : Sem Unit) := rfl

theorem restore_caller_first (world : MachineState) (a b x : UInt64) :
    restoreFrame (makerState world a b) (saveFrame (tripleState world a b x) none) [] =
      tripleState world a b x := rfl

theorem restore_caller_second (world : MachineState) (a b x : UInt64) :
    restoreFrame (applicationState world a b x) (saveFrame (callerPartial world a b x) none) [] =
      callerPartial world a b x := rfl

@[simp] theorem maker_return_types : maker.body.returnTys = [.Closure nominal] := rfl

@[simp] theorem application_return_types : application.body.returnTys = [.U64] := rfl

theorem maker_call_bound (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run ((context depth).bindCallResults (.Call makerId [valueId 0, valueId 1])
      [valueId 3] [closure a b]) (tripleState world a b x) =
      .ok ((), callerPartial world a b x) := by
  simp [EvalContext.bindCallResults, EvalContext.checkInstructionResults,
    EvalContext.instructionResultTypes, EvalContext.resultTypeHeaders,
    ssaInstructionResultTypes, ssaResultSourceType, localResultTypes,
    checkSSACharValues, checkSSACharValue, bindResultDests,
    Sem.run, Sem.getState, Sem.setState, tripleState, callerPartial, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

#print axioms maker_call_bound

theorem apply_call_bound (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run ((context depth).bindCallResults (.Call applyId [valueId 3, valueId 2])
      [valueId 4] [word (a * x + b)]) (callerPartial world a b x) =
      .ok ((), callerState world a b x) := by
  simp [EvalContext.bindCallResults, EvalContext.checkInstructionResults,
    EvalContext.instructionResultTypes, EvalContext.resultTypeHeaders,
    ssaInstructionResultTypes, ssaResultSourceType, localResultTypes,
    checkSSACharValues, checkSSACharValue, bindResultDests,
    Sem.run, Sem.getState, Sem.setState, callerPartial, callerState, valueId,
    ClosureSource.useAffine, ClosureSource.apply64, ClosureSource.makeAffine,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

#print axioms apply_call_bound

theorem maker_direct_lookup (depth : Nat) :
    (context depth).lookupDirectCallee makerId
      "Call: callee is a bodyless declaration" "Call: undefined function" =
      (StateT.pure maker : Sem EvalFunction) := by
  unfold EvalContext.lookupDirectCallee
  rw [maker_lookup]
  rfl

theorem application_direct_lookup (depth : Nat) :
    (context depth).lookupDirectCallee applyId
      "Call: callee is a bodyless declaration" "Call: undefined function" =
      (StateT.pure application : Sem EvalFunction) := by
  unfold EvalContext.lookupDirectCallee
  rw [application_lookup]
  rfl

theorem reset_caller_first (world : MachineState) (a b x : UInt64) :
    { tripleState world a b x with locals := ValueMap.empty, nextValueId := 0 } =
      entryState world := rfl

theorem reset_caller_second (world : MachineState) (a b x : UInt64) :
    { callerPartial world a b x with locals := ValueMap.empty, nextValueId := 0 } =
      entryState world := rfl

def directPrelude (callee : EvalFunction) (args : List Value) : Sem Unit := do
  requireUntypedAbi callee.body.abi
  match checkCallArity args callee.body.paramTys with
  | .ok () => pure ()
  | .error message => Sem.throwTypeError ("Call: " ++ message)
  Sem.rejectPoisonValues args "Call arguments"

theorem direct_prelude_pure (callee : EvalFunction) (args : List Value)
    (abi : requireUntypedAbi callee.body.abi = (StateT.pure () : Sem Unit))
    (arity : checkCallArity args callee.body.paramTys = .ok ())
    (poison : Sem.rejectPoisonValues args "Call arguments" = (StateT.pure () : Sem Unit)) :
    directPrelude callee args = (StateT.pure () : Sem Unit) := by
  unfold directPrelude
  rw [abi, arity, poison]
  rfl

def directFinish (ctx : EvalContext) (callee : EvalFunction) (inst : Inst)
    (destinations : List ValueId) (retVals : List Value) (frame : StackFrame) : Sem (ForInStep Unit) :=
  StateT.bind
    (match checkReturnArity retVals callee.body.returnTys with
      | .ok () => StateT.pure (() : Unit)
      | .error message => Sem.throwTypeError ("Call: " ++ message))
    (fun _ => StateT.bind (Sem.rejectPoisonValues retVals "Call returns") (fun _ =>
      StateT.bind Sem.getState (fun calleeState =>
        StateT.bind (Sem.setState (restoreFrame calleeState frame [])) (fun _ =>
          StateT.bind (ctx.bindCallResults inst destinations retVals)
            (fun _ => StateT.pure (.yield ()))))))

theorem direct_finish_runs (ctx : EvalContext) (callee : EvalFunction) (inst : Inst)
    (destinations : List ValueId) (retVals : List Value) (frame : StackFrame)
    (before restored after : MachineState)
    (arity : checkReturnArity retVals callee.body.returnTys = .ok ())
    (poison : Sem.rejectPoisonValues retVals "Call returns" = (StateT.pure () : Sem Unit))
    (restoredFrame : restoreFrame before frame [] = restored)
    (bound : Sem.run (ctx.bindCallResults inst destinations retVals) restored = .ok ((), after)) :
    Sem.run (directFinish ctx callee inst destinations retVals frame) before =
      .ok (.yield (), after) := by
  unfold directFinish
  rw [arity, poison, run_bind, run_pure]
  dsimp only [Except.bind]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [run_bind, run_get]
  dsimp only [Except.bind]
  rw [restoredFrame, run_bind, run_set]
  dsimp only [Except.bind]
  rw [run_bind, bound]
  rfl

def invokeDirect (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strategy : PanicStrategy) (callee : EvalFunction) (args : List Value)
    (inst : Inst) (destinations : List ValueId) : Sem (ForInStep Unit) := do
  directPrelude callee args
  let callerState ← Sem.getState
  let frame := saveFrame callerState none
  Sem.setState {callerState with locals := ValueMap.empty, nextValueId := 0}
  let retVals ← recurse (ctx.forFunction callee) callDepth callee.cfg callee.entryBlock args strategy
  directFinish ctx callee inst destinations retVals frame

theorem invoke_direct_runs (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strategy : PanicStrategy) (callee : EvalFunction) (args : List Value)
    (inst : Inst) (destinations : List ValueId) (before calleeAfter after : MachineState)
    (retVals : List Value)
    (prelude : directPrelude callee args = (StateT.pure () : Sem Unit))
    (computed : Sem.run (recurse (ctx.forFunction callee) callDepth callee.cfg callee.entryBlock args strategy)
      {before with locals := ValueMap.empty, nextValueId := 0} = .ok (retVals, calleeAfter))
    (returned : Sem.run (directFinish ctx callee inst destinations retVals (saveFrame before none))
      calleeAfter = .ok (.yield (), after)) :
    Sem.run (invokeDirect recurse ctx callDepth strategy callee args inst destinations) before =
      .ok (.yield (), after) := by
  unfold invokeDirect
  simp only [bind]
  rw [prelude, run_bind, run_pure]
  dsimp only [Except.bind]
  rw [run_bind, run_get]
  dsimp only [Except.bind]
  rw [run_bind, run_set]
  dsimp only [Except.bind]
  rw [run_bind, computed]
  dsimp only [Except.bind]
  exact returned

theorem invoke_direct_errors (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strategy : PanicStrategy) (callee : EvalFunction) (args : List Value)
    (inst : Inst) (destinations : List ValueId) (before : MachineState) (error : SemError)
    (prelude : directPrelude callee args = (StateT.pure () : Sem Unit))
    (computed : Sem.run (recurse (ctx.forFunction callee) callDepth callee.cfg callee.entryBlock args strategy)
      {before with locals := ValueMap.empty, nextValueId := 0} = .error error) :
    Sem.run (invokeDirect recurse ctx callDepth strategy callee args inst destinations) before =
      .error error := by
  unfold invokeDirect
  simp only [bind]
  rw [prelude, run_bind, run_pure]
  dsimp only [Except.bind]
  rw [run_bind, run_get]
  dsimp only [Except.bind]
  rw [run_bind, run_set]
  dsimp only [Except.bind]
  rw [run_bind, computed]
  rfl

theorem direct_dispatch_runs (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strategy : PanicStrategy) (code : FuncId) (argumentIds destinations : List ValueId)
    (args : List Value) (callee : EvalFunction) (world : MachineState)
    (lookedArguments : Sem.run (argumentIds.mapM Sem.lookupValue) world = .ok (args, world))
    (lookedCallee : ctx.lookupDirectCallee code
      "Call: callee is a bodyless declaration" "Call: undefined function" = (StateT.pure callee : Sem EvalFunction))
    (abi : requireUntypedAbi callee.body.abi = (StateT.pure () : Sem Unit))
    (arity : checkCallArity args callee.body.paramTys = .ok ())
    (poison : Sem.rejectPoisonValues args "Call arguments" = (StateT.pure () : Sem Unit)) :
    Sem.run (evalBodyStep recurse ctx (callDepth + 1) strategy (.Call code argumentIds, destinations)) world =
      Sem.run (invokeDirect recurse ctx callDepth strategy callee args (.Call code argumentIds) destinations) world := by
  conv =>
    rhs
    unfold invokeDirect
    simp only [bind]
    rw [direct_prelude_pure callee args abi arity poison, run_bind, run_pure]
    simp only [Except.bind]
  unfold evalBodyStep
  simp only [bind]
  rw [run_bind, lookedArguments]
  dsimp only [Except.bind]
  rw [lookedCallee, run_bind, run_pure]
  dsimp only [Except.bind]
  rw [abi, run_bind, run_pure]
  dsimp only [Except.bind]
  rw [arity]
  simp only [pure]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [poison, run_bind, run_pure]
  dsimp only [Except.bind]
  apply congrArg (fun action : Sem (ForInStep Unit) => Sem.run action world)
  apply congrArg (StateT.bind Sem.getState)
  funext callerState
  apply congrArg (StateT.bind (Sem.setState
    {callerState with locals := ValueMap.empty, nextValueId := 0}))
  funext ignored
  apply congrArg (StateT.bind (recurse (ctx.forFunction callee) callDepth
    callee.cfg callee.entryBlock args strategy))
  funext retVals
  unfold directFinish
  cases checked : checkReturnArity retVals callee.body.returnTys with
  | error message => rfl
  | ok returnedUnit => cases returnedUnit; rfl

#print axioms direct_dispatch_runs

theorem caller_maker_step (fuel depth callDepth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt (fuel + 1)) (context depth) (callDepth + 1) .abort
      (.Call makerId [valueId 0, valueId 1], [valueId 3]))
      (tripleState world a b x) = .ok (.yield (), callerPartial world a b x) := by
  rw [direct_dispatch_runs (recurseAt (fuel + 1)) (context depth) callDepth .abort
    makerId [valueId 0, valueId 1] [valueId 3] [word a, word b] maker (tripleState world a b x)
    (lookup_caller_maker_arguments world a b x) (maker_direct_lookup depth) maker_abi_untyped
    (maker_arity a b) (two_words_not_poison a b "Call arguments")]
  apply invoke_direct_runs (retVals := [closure a b]) (calleeAfter := makerState world a b)
  · exact direct_prelude_pure maker [word a, word b] maker_abi_untyped
      (maker_arity a b) (two_words_not_poison a b "Call arguments")
  · rw [for_maker, reset_caller_first]
    exact maker_body_evaluates_with_fuel fuel depth callDepth world a b
  · exact direct_finish_runs _ _ _ _ _ _ _ (tripleState world a b x) _
      (maker_return_arity a b) (one_closure_not_poison a b "Call returns")
      (restore_caller_first world a b x) (maker_call_bound depth world a b x)

#print axioms caller_maker_step

theorem caller_application_step (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt 2) (context depth) (depth + 3) .abort
      (.Call applyId [valueId 3, valueId 2], [valueId 4]))
      (callerPartial world a b x) = .ok (.yield (), callerState world a b x) := by
  rw [direct_dispatch_runs (recurseAt 2) (context depth) (depth + 2) .abort
    applyId [valueId 3, valueId 2] [valueId 4] [closure a b, word x] application (callerPartial world a b x)
    (lookup_caller_apply_arguments world a b x) (application_direct_lookup depth) application_abi_untyped
    (application_arity a b x) (closure_and_word_not_poison a b x "Call arguments")]
  apply invoke_direct_runs (retVals := [word (a * x + b)]) (calleeAfter := applicationState world a b x)
  · exact direct_prelude_pure application [closure a b, word x] application_abi_untyped
      (application_arity a b x) (closure_and_word_not_poison a b x "Call arguments")
  · rw [for_application, reset_caller_second]
    exact application_body_evaluates depth world a b x
  · exact direct_finish_runs _ _ _ _ _ _ _ (callerPartial world a b x) _
      (application_return_arity (a * x + b)) (one_word_not_poison (a * x + b) "Call returns")
      (restore_caller_second world a b x) (apply_call_bound depth world a b x)

#print axioms caller_application_step

def callerBlock : BasicBlock :=
  { params := [(valueId 0, .U64), (valueId 1, .U64), (valueId 2, .U64)]
    body := [.Call makerId [valueId 0, valueId 1], .Call applyId [valueId 3, valueId 2]]
    bodyResultDests := [[valueId 3], [valueId 4]]
    terminator := .Return [valueId 4] }

theorem caller_block_lookup : caller.cfg ⟨0⟩ = some callerBlock := rfl

theorem caller_block_resolved (depth : Nat) :
    (context depth).resolveBlock callerBlock = callerBlock := rfl

theorem caller_parameters (world : MachineState) (a b x : UInt64) :
    Sem.run (bindBlockParamsChecked callerBlock.params [word a, word b, word x])
      (entryState world) = .ok ((), tripleState world a b x) :=
  target_parameters world a b x

theorem caller_body_loop (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBody (recurseAt 2) (context depth) (depth + 3) .abort
      (bodyInstsWithResultDests callerBlock.body callerBlock.bodyResultDests))
      (tripleState world a b x) = .ok ((), callerState world a b x) := by
  unfold evalBody
  apply run_body_cons (middle := callerPartial world a b x)
  · exact caller_maker_step 1 depth (depth + 2) world a b x
  · exact run_single_body _ _ _ _ (caller_application_step depth world a b x)

theorem caller_returns (depth callDepth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepTermWithContext (context depth) callDepth caller.cfg
      (.Return [valueId 4]) .abort) (callerState world a b x) =
      .ok (.terminator (.Ret [word (ClosureSource.useAffine a b x)]), callerState world a b x) := by
  simp [stepTermWithContext, closureTermWithContext, stepInst, semReturn,
    Sem.run, Sem.lookupValue, Sem.getState, MachineState.lookupValue,
    callerState, ValueMap.get, ValueMap.set, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

/-- Constructive normal return of the escaping-closure caller: maker → returned
    closure → application parameter → exact target. The surrounding world is
    arbitrary and the caller's three inputs survive both restored call frames. -/
theorem caller_body_evaluates (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (context depth) 3 (depth + 3) caller.cfg ⟨0⟩
      [word a, word b, word x]) (entryState world) =
      .ok ([word (ClosureSource.useAffine a b x)], callerState world a b x) := by
  rw [stepNWithContext_succ_layer]
  apply run_returning_layer (block := callerBlock) (bound := tripleState world a b x)
    (bodyAfter := callerState world a b x)
  · exact caller_block_lookup
  · exact caller_block_resolved depth
  · exact caller_parameters world a b x
  · exact caller_body_loop depth world a b x
  · exact caller_returns depth (depth + 3) world a b x

#print axioms caller_body_evaluates

@[simp] theorem caller_entry : caller.entryBlock = ⟨0⟩ := rfl

theorem caller_abi_untyped : requireUntypedAbi caller.body.abi = (StateT.pure () : Sem Unit) := rfl

theorem caller_arity (a b x : UInt64) :
    checkCallArity [word a, word b, word x] caller.body.paramTys = .ok () := rfl

theorem context_call_depth (depth : Nat) : (context depth).maxCallDepth = depth + 3 := rfl

theorem contextual_entry_runs (ctx : EvalContext) (entry : FuncId) (callee : EvalFunction)
    (args retVals : List Value) (fuel : Nat) (strategy : PanicStrategy) (before after : MachineState)
    (found : ctx.functions entry = some callee)
    (abi : requireUntypedAbi callee.body.abi = (StateT.pure () : Sem Unit))
    (arity : checkCallArity args callee.body.paramTys = .ok ())
    (argumentsClean : Sem.rejectPoisonValues args "Call arguments" = (StateT.pure () : Sem Unit))
    (computed : Sem.run (exitUnwinding strategy
      (stepNWithContext (ctx.forFunction callee) fuel ctx.maxCallDepth callee.cfg callee.entryBlock args strategy))
      before = .ok (retVals, after))
    (returnsClean : Sem.rejectPoisonValues retVals "Call returns" = (StateT.pure () : Sem Unit)) :
    Sem.run (evalFunctionInContext ctx entry args fuel strategy) before = .ok (retVals, after) := by
  unfold evalFunctionInContext
  rw [found]
  simp only [bind, pure]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [abi, run_bind, run_pure]
  dsimp only [Except.bind]
  rw [arity]
  simp only [pure]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [argumentsClean, run_bind, run_pure]
  dsimp only [Except.bind]
  rw [run_bind, computed]
  dsimp only [Except.bind]
  rw [returnsClean, run_bind, run_pure]
  rfl

/-- The public contextual evaluator, including entry arity/poison checks and
    checked return, computes the actual source's wrapping UInt64 result. -/
theorem caller_evaluates (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalFunctionInContext (context depth) callerId [word a, word b, word x] 3 .abort)
      (entryState world) =
      .ok ([word (ClosureSource.useAffine a b x)], callerState world a b x) := by
  apply contextual_entry_runs (callee := caller)
  · exact caller_lookup depth
  · exact caller_abi_untyped
  · exact caller_arity a b x
  · exact three_words_not_poison a b x "Call arguments"
  · simp only [exitUnwinding, for_caller, context_call_depth, caller_entry]
    exact caller_body_evaluates depth world a b x
  · exact one_word_not_poison (ClosureSource.useAffine a b x) "Call returns"

#print axioms caller_evaluates

/-- Every non-frame field of the arbitrary initial world is preserved exactly. -/
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

theorem caller_application_low_fuel_step (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt 1) (context depth) (depth + 3) .abort
      (.Call applyId [valueId 3, valueId 2], [valueId 4]))
      (callerPartial world a b x) = .error .outOfFuel := by
  rw [direct_dispatch_runs (recurseAt 1) (context depth) (depth + 2) .abort
    applyId [valueId 3, valueId 2] [valueId 4] [closure a b, word x] application (callerPartial world a b x)
    (lookup_caller_apply_arguments world a b x) (application_direct_lookup depth) application_abi_untyped
    (application_arity a b x) (closure_and_word_not_poison a b x "Call arguments")]
  apply invoke_direct_errors
  · exact direct_prelude_pure application [closure a b, word x] application_abi_untyped
      (application_arity a b x) (closure_and_word_not_poison a b x "Call arguments")
  · rw [for_application, reset_caller_second]
    exact application_low_fuel depth world a b x

theorem caller_application_low_depth_step (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt 2) (context depth) 1 .abort
      (.Call applyId [valueId 3, valueId 2], [valueId 4]))
      (callerPartial world a b x) = .error .outOfFuel := by
  rw [direct_dispatch_runs (recurseAt 2) (context depth) (0) .abort
    applyId [valueId 3, valueId 2] [valueId 4] [closure a b, word x] application (callerPartial world a b x)
    (lookup_caller_apply_arguments world a b x) (application_direct_lookup depth) application_abi_untyped
    (application_arity a b x) (closure_and_word_not_poison a b x "Call arguments")]
  apply invoke_direct_errors
  · exact direct_prelude_pure application [closure a b, word x] application_abi_untyped
      (application_arity a b x) (closure_and_word_not_poison a b x "Call arguments")
  · rw [for_application, reset_caller_second]
    exact application_low_depth depth world a b x

/-- A positive caller block budget of two is insufficient for the actual
    maker → apply → target nesting; the successful theorem uses three. -/
theorem caller_low_fuel (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (context depth) 2 (depth + 3) caller.cfg ⟨0⟩
      [word a, word b, word x]) (entryState world) = .error .outOfFuel := by
  rw [stepNWithContext_succ_layer]
  apply run_failing_layer (block := callerBlock) (bound := tripleState world a b x)
  · exact caller_block_lookup
  · exact caller_block_resolved depth
  · exact caller_parameters world a b x
  · unfold evalBody
    apply run_body_tail_failure (middle := callerPartial world a b x)
    · exact caller_maker_step 0 depth (depth + 2) world a b x
    · exact run_body_head_failure _ _ _ _ _ (caller_application_low_fuel_step depth world a b x)

/-- A positive call-depth budget of one permits maker return, then refuses
    application before invoking the target; the successful caller uses three. -/
theorem caller_low_depth (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (context depth) 3 1 caller.cfg ⟨0⟩
      [word a, word b, word x]) (entryState world) = .error .outOfFuel := by
  rw [stepNWithContext_succ_layer]
  apply run_failing_layer (block := callerBlock) (bound := tripleState world a b x)
  · exact caller_block_lookup
  · exact caller_block_resolved depth
  · exact caller_parameters world a b x
  · unfold evalBody
    apply run_body_tail_failure (middle := callerPartial world a b x)
    · exact caller_maker_step 1 depth 0 world a b x
    · exact run_body_head_failure _ _ _ _ _ (caller_application_low_depth_step depth world a b x)


end ClosureU64
