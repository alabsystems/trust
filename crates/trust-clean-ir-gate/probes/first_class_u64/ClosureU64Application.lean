/- Exact nominal closure application in the pinned contextual evaluator. -/
import ClosureU64Execution
namespace ClosureU64
open TrustIr
open TrustIr.GenericCoro.Prefix
set_option maxRecDepth 1024

def recurseAt (fuel : Nat) : Recurse :=
  fun ctx depth cfg pc args strategy => stepNWithContext ctx fuel depth cfg pc args strategy

theorem lookup_application_closure (world : MachineState) (a b x : UInt64) :
    Sem.run (Sem.lookupValue (valueId 0)) (applicationEntry world a b x) =
      .ok (closure a b, applicationEntry world a b x) := rfl

theorem lookup_application_arguments (world : MachineState) (a b x : UInt64) :
    Sem.run ([valueId 1].mapM Sem.lookupValue) (applicationEntry world a b x) =
      .ok ([word x], applicationEntry world a b x) := rfl

theorem target_abi_untyped : requireUntypedAbi target.body.abi = (StateT.pure () : Sem Unit) := rfl

theorem target_arity (a b x : UInt64) :
    checkCallArity [word a, word b, word x] target.body.paramTys = .ok () := rfl

theorem target_return_arity (value : UInt64) :
    checkReturnArity [word value] target.body.returnTys = .ok () := rfl

theorem three_words_not_poison (a b x : UInt64) (operation : String) :
    Sem.rejectPoisonValues [word a, word b, word x] operation =
      (StateT.pure () : Sem Unit) := rfl

theorem one_word_not_poison (value : UInt64) (operation : String) :
    Sem.rejectPoisonValues [word value] operation = (StateT.pure () : Sem Unit) := rfl

theorem reset_application (world : MachineState) (a b x : UInt64) :
    { applicationEntry world a b x with locals := ValueMap.empty, nextValueId := 0 } =
      entryState world := rfl

theorem restore_application (world : MachineState) (a b x : UInt64) :
    restoreFrame (targetState world a b x) (saveFrame (applicationEntry world a b x) none) [] =
      applicationEntry world a b x := rfl

theorem application_result_bound (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run ((context depth).bindCallResults
      (.CallIndirect (valueId 0) apparent [valueId 1] .Rust) [valueId 2] [word (a * x + b)])
      (applicationEntry world a b x) = .ok ((), applicationState world a b x) := by
  simp [EvalContext.bindCallResults, EvalContext.checkInstructionResults,
    EvalContext.instructionResultTypes, ssaInstructionResultTypes, ssaResultSourceType,
    localResultTypes, checkSSACharValues, checkSSACharValue, bindResultDests,
    Sem.run, Sem.getState, Sem.setState, applicationEntry, applicationState, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

theorem state_bind_assoc {α β γ : Type} (first : Sem α) (next : α → Sem β)
    (last : β → Sem γ) :
    StateT.bind (StateT.bind first next) last =
      StateT.bind first (fun value => StateT.bind (next value) last) :=
  bind_assoc first next last

theorem target_return_types : target.body.returnTys = [.U64] := rfl


/-- The return checker remains an opaque mathematical input to this
    one-element loop lemma; its concrete success proof is supplied separately. -/
def checkedReturnAction (check : Ty → Value → Except SemError Unit) (ty : Ty) (value : Value) :
    Sem PUnit :=
  forIn [(ty, value)] PUnit.unit (fun pair _ =>
    match check pair.1 pair.2 with
    | .ok () => StateT.bind (StateT.pure (() : Unit)) (fun _ => StateT.pure (.yield PUnit.unit))
    | .error error => StateT.bind (throw error : Sem PUnit) (fun _ => StateT.pure (.yield PUnit.unit)))

theorem checked_return_action_runs (check : Ty → Value → Except SemError Unit) (ty : Ty)
    (value : Value) (world : MachineState) (valid : check ty value = .ok ()) :
    Sem.run (checkedReturnAction check ty value) world = .ok (PUnit.unit, world) := by
  unfold checkedReturnAction
  rw [List.forIn_cons]
  simp only [valid, List.forIn_nil, bind, pure]
  rfl

def checkedReturnsAction (check : Ty → Value → Except SemError Unit)
    (types : List Ty) (values : List Value) : Sem PUnit :=
  forIn (types.zip values) PUnit.unit (fun pair _ =>
    match check pair.1 pair.2 with
    | .ok () => StateT.bind (StateT.pure (() : Unit)) (fun _ => StateT.pure (.yield PUnit.unit))
    | .error error => StateT.bind (throw error : Sem PUnit) (fun _ => StateT.pure (.yield PUnit.unit)))

theorem checked_returns_one (check : Ty → Value → Except SemError Unit) (ty : Ty) (value : Value) :
    checkedReturnsAction check [ty] [value] = checkedReturnAction check ty value := rfl

/-- The checked return/restore suffix is separate so the proof never asks
    the kernel to normalize it through the entire indirect-call dispatch. -/
def applicationFinish (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem (ForInStep Unit) :=
  StateT.bind
    (checkedReturnAction (checkClosureValue (context depth)) .U64 (word (a * x + b)))
    (fun _ => StateT.bind (StateT.pure PUnit.unit) (fun _ =>
      StateT.bind Sem.getState (fun calleeState =>
        StateT.bind (Sem.setState
          (restoreFrame calleeState (saveFrame (applicationEntry world a b x) none) [])) (fun _ =>
          StateT.bind ((context depth).bindCallResults
            (.CallIndirect (valueId 0) apparent [valueId 1] .Rust) [valueId 2] [word (a * x + b)])
            (fun _ => StateT.pure (.yield ()))))))

theorem application_finish_runs (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (applicationFinish depth world a b x) (targetState world a b x) =
      .ok (.yield (), applicationState world a b x) := by
  unfold applicationFinish
  rw [run_bind, checked_return_action_runs _ _ _ _ (word_checked _ _)]
  dsimp only [Except.bind]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [run_bind, run_get]
  dsimp only [Except.bind]
  rw [restore_application, run_bind, run_set]
  dsimp only [Except.bind]
  rw [run_bind, application_result_bound]
  rfl

#print axioms application_finish_runs

def afterReturnChecks (arity : Except String Unit) (poisonGuard : Sem Unit)
    (validate : Sem PUnit) (next : Sem (ForInStep Unit)) : Sem (ForInStep Unit) :=
  StateT.bind
    (match arity with
      | .ok () => StateT.pure (() : Unit)
      | .error message => Sem.throwTypeError ("CallIndirect: " ++ message))
    (fun _ => StateT.bind poisonGuard (fun _ => StateT.bind validate (fun _ => next)))

theorem after_return_checks_ok (validate : Sem PUnit) (next : Sem (ForInStep Unit)) :
    afterReturnChecks (.ok ()) (StateT.pure ()) validate next =
      StateT.bind validate (fun _ => next) := rfl

def returnToCaller (ctx : EvalContext) (callee : EvalFunction) (inst : Inst)
    (destinations : List ValueId) (retVals : List Value) (frame : StackFrame) :
    Sem (ForInStep Unit) :=
  afterReturnChecks (checkReturnArity retVals callee.body.returnTys)
    (Sem.rejectPoisonValues retVals "Call returns")
    (checkedReturnsAction (checkClosureValue ctx) callee.body.returnTys retVals)
    (StateT.bind (StateT.pure PUnit.unit) (fun _ =>
      StateT.bind Sem.getState (fun calleeState =>
        StateT.bind (Sem.setState (restoreFrame calleeState frame [])) (fun _ =>
          StateT.bind (ctx.bindCallResults inst destinations retVals)
            (fun _ => StateT.pure (.yield ()))))))

def targetReturns (depth : Nat) (_a _b : UInt64) (retVals : List Value) (frame : StackFrame) :
    Sem (ForInStep Unit) :=
  returnToCaller (context depth) target
    (.CallIndirect (valueId 0) apparent [valueId 1] .Rust) [valueId 2] retVals frame

theorem target_returns_action (depth : Nat) (a b value : UInt64) (frame : StackFrame) :
    targetReturns depth a b [word value] frame =
      StateT.bind (checkedReturnAction (checkClosureValue (context depth)) .U64 (word value))
        (fun _ => StateT.bind (StateT.pure PUnit.unit) (fun _ =>
          StateT.bind Sem.getState (fun calleeState =>
            StateT.bind (Sem.setState (restoreFrame calleeState frame [])) (fun _ =>
              StateT.bind ((context depth).bindCallResults
                (.CallIndirect (valueId 0) apparent [valueId 1] .Rust) [valueId 2] [word value])
                (fun _ => StateT.pure (.yield ())))))) := by
  unfold targetReturns returnToCaller
  rw [target_return_arity, one_word_not_poison]
  rw [after_return_checks_ok]
  rw [target_return_types, checked_returns_one]

#print axioms target_returns_action

theorem target_returns_runs (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (targetReturns depth a b [word (a * x + b)]
      (saveFrame (applicationEntry world a b x) none)) (targetState world a b x) =
      .ok (.yield (), applicationState world a b x) := by
  rw [target_returns_action]
  change Sem.run (applicationFinish depth world a b x) (targetState world a b x) = _
  exact application_finish_runs depth world a b x

#print axioms target_returns_runs

def calleePrelude (callee : EvalFunction) (args : List Value) : Sem Unit := do
  requireUntypedAbi callee.body.abi
  match checkCallArity args callee.body.paramTys with
  | .ok () => pure ()
  | .error message => Sem.throwTypeError ("CallIndirect: " ++ message)
  Sem.rejectPoisonValues args "CallIndirect arguments"

theorem callee_prelude_pure (callee : EvalFunction) (args : List Value)
    (abi : requireUntypedAbi callee.body.abi = (StateT.pure () : Sem Unit))
    (arity : checkCallArity args callee.body.paramTys = .ok ())
    (poison : Sem.rejectPoisonValues args "CallIndirect arguments" = (StateT.pure () : Sem Unit)) :
    calleePrelude callee args = (StateT.pure () : Sem Unit) := by
  unfold calleePrelude
  rw [abi, arity, poison]
  rfl

theorem target_prelude_pure (a b x : UInt64) :
    calleePrelude target [word a, word b, word x] = (StateT.pure () : Sem Unit) := rfl

def invokeClosureTarget (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strategy : PanicStrategy) (callee : EvalFunction) (callArgs : List Value)
    (inst : Inst) (destinations : List ValueId) : Sem (ForInStep Unit) := do
  calleePrelude callee callArgs
  let callerState ← Sem.getState
  let frame := saveFrame callerState none
  Sem.setState {callerState with locals := ValueMap.empty, nextValueId := 0}
  let retVals ← recurse (ctx.forFunction callee) callDepth
    callee.cfg callee.entryBlock callArgs strategy
  returnToCaller ctx callee inst destinations retVals frame

def invokeTarget (fuel depth : Nat) (a b x : UInt64) : Sem (ForInStep Unit) :=
  invokeClosureTarget (recurseAt fuel) (context depth) (depth + 1) .abort target
    [word a, word b, word x] (.CallIndirect (valueId 0) apparent [valueId 1] .Rust) [valueId 2]

theorem invoke_closure_target_runs (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strategy : PanicStrategy) (callee : EvalFunction) (args : List Value)
    (inst : Inst) (destinations : List ValueId) (before calleeAfter after : MachineState)
    (retVals : List Value)
    (prelude : calleePrelude callee args = (StateT.pure () : Sem Unit))
    (computed : Sem.run (recurse (ctx.forFunction callee) callDepth callee.cfg callee.entryBlock args strategy)
      {before with locals := ValueMap.empty, nextValueId := 0} = .ok (retVals, calleeAfter))
    (returned : Sem.run (returnToCaller ctx callee inst destinations retVals (saveFrame before none))
      calleeAfter = .ok (.yield (), after)) :
    Sem.run (invokeClosureTarget recurse ctx callDepth strategy callee args inst destinations) before =
      .ok (.yield (), after) := by
  unfold invokeClosureTarget
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

theorem invoke_closure_target_errors (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strategy : PanicStrategy) (callee : EvalFunction) (args : List Value)
    (inst : Inst) (destinations : List ValueId) (before : MachineState) (error : SemError)
    (prelude : calleePrelude callee args = (StateT.pure () : Sem Unit))
    (computed : Sem.run (recurse (ctx.forFunction callee) callDepth callee.cfg callee.entryBlock args strategy)
      {before with locals := ValueMap.empty, nextValueId := 0} = .error error) :
    Sem.run (invokeClosureTarget recurse ctx callDepth strategy callee args inst destinations) before =
      .error error := by
  unfold invokeClosureTarget
  simp only [bind]
  rw [prelude, run_bind, run_pure]
  dsimp only [Except.bind]
  rw [run_bind, run_get]
  dsimp only [Except.bind]
  rw [run_bind, run_set]
  dsimp only [Except.bind]
  rw [run_bind, computed]
  rfl

theorem invoke_target_runs (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (invokeTarget 1 depth a b x) (applicationEntry world a b x) =
      .ok (.yield (), applicationState world a b x) := by
  unfold invokeTarget
  apply invoke_closure_target_runs (retVals := [word (a * x + b)])
    (calleeAfter := targetState world a b x)
  · exact target_prelude_pure a b x
  · rw [for_target, reset_application]
    exact target_body_evaluates depth (depth + 1) world a b x
  · exact target_returns_runs depth world a b x

#print axioms invoke_target_runs

/-- The dispatch conversion is proved once with an opaque context/callee.
    Every premise is a primitive lookup or the existing closure/ABI/argument
    validation; no successful recursive call is assumed. -/
theorem typed_dispatch_runs (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strategy : PanicStrategy) (calleeValueId : ValueId) (signature : FuncTyId)
    (argumentIds destinations : List ValueId) (convention : CallingConv)
    (cid : ClosureTyId) (code : FuncId) (captures args callArgs : List Value)
    (callee : EvalFunction) (world : MachineState)
    (lookedClosure : Sem.run (Sem.lookupValue calleeValueId) world =
      .ok (.typedClosure cid code captures, world))
    (lookedArguments : Sem.run (argumentIds.mapM Sem.lookupValue) world = .ok (args, world))
    (dispatched : closureCall ctx cid code captures signature args convention = .ok (code, callArgs))
    (found : ctx.functions code = some callee)
    (abi : requireUntypedAbi callee.body.abi = (StateT.pure () : Sem Unit))
    (arity : checkCallArity callArgs callee.body.paramTys = .ok ())
    (poison : Sem.rejectPoisonValues callArgs "CallIndirect arguments" = (StateT.pure () : Sem Unit)) :
    Sem.run (evalBodyStep recurse ctx (callDepth + 1) strategy
      (.CallIndirect calleeValueId signature argumentIds convention, destinations)) world =
      Sem.run (invokeClosureTarget recurse ctx callDepth strategy callee callArgs
        (.CallIndirect calleeValueId signature argumentIds convention) destinations) world := by
  conv =>
    rhs
    unfold invokeClosureTarget
    simp only [bind]
    rw [callee_prelude_pure callee callArgs abi arity poison, run_bind, run_pure]
    simp only [Except.bind]
  unfold evalBodyStep
  simp only [bind, state_bind_assoc]
  rw [run_bind, lookedClosure]
  dsimp only [Except.bind]
  simp only [pure]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [run_bind, lookedArguments]
  dsimp only [Except.bind]
  rw [dispatched]
  simp only [pure]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [found]
  simp only [pure]
  rw [run_bind, run_pure]
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
    callee.cfg callee.entryBlock callArgs strategy))
  funext retVals
  unfold returnToCaller afterReturnChecks checkedReturnsAction
  cases checked : checkReturnArity retVals callee.body.returnTys with
  | error message => rfl
  | ok returnedUnit => cases returnedUnit; rfl

#print axioms typed_dispatch_runs

theorem application_indirect_step (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt 1) (context depth) (depth + 2) .abort
      (.CallIndirect (valueId 0) apparent [valueId 1] .Rust, [valueId 2]))
      (applicationEntry world a b x) = .ok (.yield (), applicationState world a b x) := by
  rw [typed_dispatch_runs (recurseAt 1) (context depth) (depth + 1) .abort
    (valueId 0) apparent [valueId 1] [valueId 2] .Rust nominal targetId
    [word a, word b] [word x] [word a, word b, word x] target
    (applicationEntry world a b x) (lookup_application_closure world a b x)
    (lookup_application_arguments world a b x) (application_arguments_exact depth a b x)
    (target_lookup depth) target_abi_untyped (target_arity a b x)
    (three_words_not_poison a b x "CallIndirect arguments")]
  exact invoke_target_runs depth world a b x

#print axioms application_indirect_step

def applicationBlock : BasicBlock :=
  { params := [(valueId 0, .Closure nominal), (valueId 1, .U64)]
    body := [.CallIndirect (valueId 0) apparent [valueId 1] .Rust]
    bodyResultDests := [[valueId 2]]
    terminator := .Return [valueId 2] }

theorem application_block_lookup : application.cfg ⟨0⟩ = some applicationBlock := rfl

theorem application_block_resolved (depth : Nat) :
    (context depth).resolveBlock applicationBlock = applicationBlock := rfl

theorem application_parameters (world : MachineState) (a b x : UInt64) :
    Sem.run (bindBlockParamsChecked applicationBlock.params [closure a b, word x])
      (entryState world) = .ok ((), applicationEntry world a b x) := by
  simp [applicationBlock, bindBlockParamsChecked, checkSSACharValues, checkSSACharValue,
    bindBlockParams, Sem.run, Sem.getState, Sem.setState, entryState, applicationEntry, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

theorem application_body_loop (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBody (recurseAt 1) (context depth) (depth + 2) .abort
      (bodyInstsWithResultDests applicationBlock.body applicationBlock.bodyResultDests))
      (applicationEntry world a b x) = .ok ((), applicationState world a b x) := by
  unfold evalBody
  exact run_single_body _ _ _ _ (application_indirect_step depth world a b x)

theorem application_returns (depth callDepth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepTermWithContext (context depth) callDepth application.cfg
      (.Return [valueId 2]) .abort) (applicationState world a b x) =
      .ok (.terminator (.Ret [word (a * x + b)]), applicationState world a b x) := by
  simp [stepTermWithContext, closureTermWithContext, stepInst, semReturn,
    Sem.run, Sem.lookupValue, Sem.getState, MachineState.lookupValue,
    applicationState, ValueMap.get, ValueMap.set, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

/-- The function argument is a real nominal closure value. Application uses
    the checked code/capture/argument identity and restores the application
    frame after the selected target's normal return. -/
theorem application_body_evaluates (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (context depth) 2 (depth + 2) application.cfg ⟨0⟩
      [closure a b, word x]) (entryState world) =
      .ok ([word (a * x + b)], applicationState world a b x) := by
  rw [stepNWithContext_succ_layer]
  apply run_returning_layer (block := applicationBlock) (bound := applicationEntry world a b x)
    (bodyAfter := applicationState world a b x)
  · exact application_block_lookup
  · exact application_block_resolved depth
  · exact application_parameters world a b x
  · exact application_body_loop depth world a b x
  · exact application_returns depth (depth + 2) world a b x

#print axioms application_body_evaluates

theorem invoke_target_low_fuel (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (invokeTarget 0 depth a b x) (applicationEntry world a b x) = .error .outOfFuel := by
  unfold invokeTarget
  apply invoke_closure_target_errors
  · exact target_prelude_pure a b x
  · rfl

theorem application_indirect_low_fuel_step (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt 0) (context depth) (depth + 2) .abort
      (.CallIndirect (valueId 0) apparent [valueId 1] .Rust, [valueId 2]))
      (applicationEntry world a b x) = .error .outOfFuel := by
  rw [typed_dispatch_runs (recurseAt 0) (context depth) (depth + 1) .abort
    (valueId 0) apparent [valueId 1] [valueId 2] .Rust nominal targetId
    [word a, word b] [word x] [word a, word b, word x] target
    (applicationEntry world a b x) (lookup_application_closure world a b x)
    (lookup_application_arguments world a b x) (application_arguments_exact depth a b x)
    (target_lookup depth) target_abi_untyped (target_arity a b x)
    (three_words_not_poison a b x "CallIndirect arguments")]
  exact invoke_target_low_fuel depth world a b x

theorem application_low_fuel (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (context depth) 1 (depth + 2) application.cfg ⟨0⟩
      [closure a b, word x]) (entryState world) = .error .outOfFuel := by
  rw [stepNWithContext_succ_layer]
  apply run_failing_layer (block := applicationBlock) (bound := applicationEntry world a b x)
  · exact application_block_lookup
  · exact application_block_resolved depth
  · exact application_parameters world a b x
  · unfold evalBody
    exact run_body_head_failure _ _ _ _ _ (application_indirect_low_fuel_step depth world a b x)

theorem application_indirect_low_depth_step (fuel depth : Nat) (world : MachineState)
    (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt fuel) (context depth) 0 .abort
      (.CallIndirect (valueId 0) apparent [valueId 1] .Rust, [valueId 2]))
      (applicationEntry world a b x) = .error .outOfFuel := by
  unfold evalBodyStep
  simp only [bind]
  rw [run_bind, lookup_application_closure]
  dsimp only [Except.bind, closure]
  simp only [pure]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [run_bind, lookup_application_arguments]
  rfl

theorem application_low_depth (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (context depth) 2 0 application.cfg ⟨0⟩
      [closure a b, word x]) (entryState world) = .error .outOfFuel := by
  rw [stepNWithContext_succ_layer]
  apply run_failing_layer (block := applicationBlock) (bound := applicationEntry world a b x)
  · exact application_block_lookup
  · exact application_block_resolved depth
  · exact application_parameters world a b x
  · unfold evalBody
    exact run_body_head_failure _ _ _ _ _ (application_indirect_low_depth_step 1 depth world a b x)


end ClosureU64
