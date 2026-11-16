/- Actual Machine.new and five bounded Machine.step operations for the
   separate supported Exit program. It terminates with genuine MachineStop. -/
import MiniRustU64ExitStop
import MiniRustU64ProgramExecution
set_option autoImplicit false
noncomputable section
namespace MiniRustU64ExitExecution
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Step MiniRustU64Entry
  MiniRustU64AllocatedCall MiniRustU64ExitProgram MiniRustU64ExitStart MiniRustU64ExitRun
  MiniRustU64ExitCall MiniRustU64ExitStop MiniRustAllocate8Safety
open MiniRustU64ProgramStart (zeroSlot zeroTree zeroMemory)
open MiniRustU64ProgramRun (oneThreadRun finishStorage)
open MiniRustU64ProgramCall (one_thread_bind)
open MiniRustU64ProgramExecution (functionWorld choice_bind_selected chooseZero zero_tree_bind choose_zero_bind)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem initialized_storage_step (fuel literal input : Nat) (first second root : Int) :
    MRf.Machine.step (fuel + 50) (initialized literal input first second root) =
      oneThreadRun (selectedChoice (Int.ofNat (modulus 64))
        (allocationAllowed (functionWorld first second ++ [zeroSlot .Stack root]))
        (fun index => .ok (.ok (), callingState literal input first second root (ptr 2 root)
          (functionWorld first second ++ [zeroSlot .Stack root]) [] (address index) []))) := by
  change MRf.Machine.step (fuel + 50)
    (single (initialized literal input first second root) [entryFrame input (ptr 2 root)]
      ⟨⟨functionWorld first second ++ [zeroSlot .Stack root], ()⟩, []⟩) = _
  rw [entry_storage_step]
  change oneThreadRun ((MRf.ConcurrentMemory.allocate (fuel + 47)
    ⟨⟨functionWorld first second ++ [zeroSlot .Stack root], ()⟩, []⟩ .Stack 8 8).bind _) = _
  rw [concurrent8_exact (fuel + 41)]
  unfold concurrent8Tree
  rw [choice_bind_selected]
  apply congrArg oneThreadRun
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (functionWorld first second ++ [zeroSlot .Stack root])))
  funext index
  simp only [allocatedConcurrent8, finishStorageStep, callingState, memory, functionWorld,
    List.length_append, List.length_cons, List.length_nil, Nat.add_zero, candidate_nat, address,
    List.append_nil]

/-- Continue with four actual operations only after the previous real step
    returned ok; all actual errors are propagated without inventing a state. -/
def afterStorage (fuel : Nat) (result : SRes MR_TerminationInfo Unit × MR_Machine) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  match result with
  | (.err error, machine) => .ok (.err error, machine)
  | (.ok _, machine) => ((MRf.Machine.step (fuel + 50) machine).bind
      (MiniRustU64Correspondence.afterEntry (fuel + 50))).bind
        (MiniRustU64Run.nextStep (fuel + 50))

def fiveSteps (fuel : Nat) (machine : MR_Machine) :=
  (MRf.Machine.step (fuel + 50) machine).bind (afterStorage fuel)

def initializedTree (literal input : Nat) (first second root : Int) :=
  oneThreadRun (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (functionWorld first second ++ [zeroSlot .Stack root]))
    (fun index => stoppingTree literal input first second root (functionWorld first second) [] (address index)))

/-- Complete five-step initialized execution, full64 literal/input and eight
    exact scheduler/allocation choices. No successful step/run premise. -/
theorem initialized_five_steps (fuel literal input : Nat) (first second root : Int)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    fiveSteps fuel (initialized literal input first second root) =
      initializedTree literal input first second root := by
  unfold fiveSteps
  rw [initialized_storage_step, one_thread_bind, selected_bind]
  unfold initializedTree
  apply congrArg oneThreadRun
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (functionWorld first second ++ [zeroSlot .Stack root])))
  funext index
  simp only [SOut.bind_ok', afterStorage]
  change callCalleeExit fuel literal input first second root
    (functionWorld first second) [] (address index) [] = _
  exact call_callee_exit_exact fuel literal input first second root _ _ _ _
    (address_aligned index) inputValid literalValid

/-- Real startup errors have no machine state. The outer result preserves that
    distinction; the inner result is the actual bounded execution endpoint. -/
def continueNew (fuel : Nat) (result : SRes MR_TerminationInfo MR_Machine) :
    SOut (SRes MR_TerminationInfo (SRes MR_TerminationInfo Unit × MR_Machine)) :=
  match result with
  | .err error => .ok (.err error)
  | .ok machine => (fiveSteps fuel machine).bind (fun endpoint => .ok (.ok endpoint))

def executeExit (fuel literal input : Nat) :=
  (MRf.Machine.new (fuel + 81) (exitProgram literal input) () () ()).bind (continueNew fuel)

/-- Actual guarded zero-allocation distribution; only the continuation is
    exposed so source Machine.new choices are retained verbatim. -/
def executionTree (literal input : Nat) :
    SOut (SRes MR_TerminationInfo (SRes MR_TerminationInfo Unit × MR_Machine)) :=
  chooseZero [] (fun first => chooseZero [zeroSlot .Function first] (fun second =>
    chooseZero (functionWorld first second) (fun root =>
      (initializedTree literal input first second root).bind (fun endpoint => .ok (.ok endpoint)))))

theorem startup_shape (literal input : Nat) :
    startupTree literal input =
      chooseZero [] (fun first => chooseZero [zeroSlot .Function first] (fun second =>
        chooseZero (functionWorld first second) (fun root => .ok (.ok (initialized literal input first second root))))) := by
  unfold startupTree
  rw [zero_tree_bind]
  apply congrArg (chooseZero [])
  funext first
  rw [zero_tree_bind]
  apply congrArg (chooseZero [zeroSlot .Function first])
  funext second
  rw [zero_tree_bind]
  apply congrArg (chooseZero (functionWorld first second))
  funext root
  rfl

/-- Distribution is kept separate from the actual execution continuation. -/
theorem startup_bind {α : Type} (literal input : Nat)
    (failure : MR_TerminationInfo → SOut α) (next : MR_Machine → SOut α) :
    (startupTree literal input).bind (fun result => match result with
      | .err error => failure error | .ok machine => next machine) =
      chooseZero [] (fun first => chooseZero [zeroSlot .Function first] (fun second =>
        chooseZero (functionWorld first second) (fun root => next (initialized literal input first second root)))) := by
  rw [startup_shape, choose_zero_bind]
  apply congrArg (chooseZero [])
  funext first
  rw [choose_zero_bind]
  apply congrArg (chooseZero [zeroSlot .Function first])
  funext second
  rw [choose_zero_bind]
  rfl

attribute [local irreducible] fiveSteps

theorem startup_execution_tree (fuel literal input : Nat)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    (startupTree literal input).bind (continueNew fuel) = executionTree literal input := by
  unfold continueNew
  rw [startup_bind]
  unfold executionTree
  apply congrArg (chooseZero [])
  funext first
  apply congrArg (chooseZero [zeroSlot .Function first])
  funext second
  apply congrArg (chooseZero (functionWorld first second))
  funext root
  rw [initialized_five_steps fuel literal input first second root inputValid literalValid]

/-- Real complete validated Machine.new followed by five real Machine.step at
    one explicit bounded fuel. The exact eleven-choice tree ends in genuine
    actual MachineStop, with no assumed successful operation. -/
theorem execute_exit_exact (fuel literal input : Nat)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    executeExit fuel literal input = executionTree literal input := by
  unfold executeExit
  rw [startup_exact fuel literal input literalValid inputValid,
    startup_execution_tree fuel literal input inputValid literalValid]

/-- Pure original choice algebra, abstracting the bound and guard so no
    allocation implementation is unfolded by equality elaboration. -/
theorem pick_unit_shape {α : Type} (bound : Int) (guard : Int → Bool) (next : Int → SOut α) :
    ((SPick.choose ⟨1, bound, 1⟩ (fun addr (_ : Unit) => .ok (guard addr, ())) ()).bind
      (fun pair => next pair.1)) = .pick (fun index =>
        if SInt.blt ((1 + Int.ofNat index) * 1) bound then
          if guard ((1 + Int.ofNat index) * 1) then next ((1 + Int.ofNat index) * 1)
          else .reject else .reject) := by
  simp only [SPick.choose]
  rw [show SInt.div_ceil 1 1 = SOut.ok 1 from rfl]
  simp only [SOut.bind_ok']
  rw [MiniRustU64ProgramRun.pick_bind]
  apply congrArg SOut.pick
  funext index
  cases hb : SInt.blt ((1 + Int.ofNat index) * 1) bound <;>
    cases ha : guard ((1 + Int.ofNat index) * 1) <;> rfl

theorem choose_zero_shape {α : Type} (world : List MR_Allocation) (next : Int → SOut α) :
    chooseZero world next = .pick (fun index =>
      if SInt.blt ((1 + Int.ofNat index) * 1) (Int.ofNat (modulus 64)) then
        if MiniRustAllocate.allowed 0 1 world ((1 + Int.ofNat index) * 1) then
          next ((1 + Int.ofNat index) * 1) else .reject
      else .reject) := by
  unfold chooseZero
  exact pick_unit_shape _ _ _

theorem every_guarded_pick {α : Type} (p : α → Prop) (bound : Int) (guard : Int → Bool)
    (next : Int → SOut α) (h : ∀ addr, EveryResult p (next addr)) :
    EveryResult p (.pick (fun index =>
      if SInt.blt ((1 + Int.ofNat index) * 1) bound then
        if guard ((1 + Int.ofNat index) * 1) then next ((1 + Int.ofNat index) * 1)
        else .reject else .reject)) := by
  change ∀ index : Nat, _
  intro index
  dsimp only
  cases hb : SInt.blt ((1 + Int.ofNat index) * 1) bound with
  | false => trivial
  | true =>
    cases ha : guard ((1 + Int.ofNat index) * 1) with
    | false => trivial
    | true => exact h _

attribute [local irreducible] EveryResult

theorem every_zero {α : Type} (p : α → Prop) (world : List MR_Allocation)
    (next : Int → SOut α) (h : ∀ addr, EveryResult p (next addr)) :
    EveryResult p (chooseZero world next) := by
  rw [choose_zero_shape]
  exact every_guarded_pick p _ _ next h

theorem every_thread {α : Type} (p : α → Prop) (out : SOut α)
    (h : EveryResult p out) : EveryResult p (oneThreadRun out) :=
  MiniRustU64Run.every_scheduled p out h



def LocalObservation (literal input : Nat) (first second root : Int)
    (endpoint : SRes MR_TerminationInfo Unit × MR_Machine) : Prop :=
  ∃ callerIndex retIndex argIndex : Nat,
    endpoint = (.err .MachineStop, stoppedState literal input first second root
      (functionWorld first second) [] (address callerIndex) (address retIndex) (address argIndex))

theorem initialized_observed (literal input : Nat) (first second root : Int) :
    EveryResult (LocalObservation literal input first second root)
      (initializedTree literal input first second root) := by
  unfold initializedTree
  apply every_thread
  apply MiniRustU64Correspondence.every_selected
  intro callerIndex _ _
  unfold stoppingTree
  apply every_thread
  apply MiniRustU64Correspondence.every_selected
  intro retIndex _ _
  apply MiniRustU64Correspondence.every_selected
  intro argIndex _ _
  apply every_thread
  apply every_thread
  apply every_thread
  simp only [EveryResult]
  change LocalObservation literal input first second root _
  refine ⟨callerIndex, retIndex, argIndex, ?_⟩
  rfl

/-- Every admitted endpoint has actual normal model stop and the COMPLETE
    generated machine/world indexed by all six concrete allocation choices.
    Rejected choices are not successful observations; availability is separate. -/
def ExitObservation (literal input : Nat)
    (result : SRes MR_TerminationInfo (SRes MR_TerminationInfo Unit × MR_Machine)) : Prop :=
  ∃ first second root : Int, ∃ callerIndex retIndex argIndex : Nat,
    result = .ok (.err .MachineStop, stoppedState literal input first second root
      (functionWorld first second) [] (address callerIndex) (address retIndex) (address argIndex))

theorem execution_tree_observed (literal input : Nat) :
    EveryResult (ExitObservation literal input) (executionTree literal input) := by
  unfold executionTree
  apply every_zero
  intro first
  apply every_zero
  intro second
  apply every_zero
  intro root
  apply every_bind (LocalObservation literal input first second root)
  · exact initialized_observed literal input first second root
  · intro endpoint h
    rcases h with ⟨callerIndex, retIndex, argIndex, same⟩
    simp only [EveryResult]
    change ExitObservation literal input (.ok endpoint)
    exact ⟨first, second, root, callerIndex, retIndex, argIndex, congrArg SRes.ok same⟩

/-- Universal model safety/endpoint theorem for this explicit constructed
    program. No successful new/call/run, leak result or NoUB premise occurs. -/
theorem execute_exit_observed (fuel literal input : Nat)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    EveryResult (ExitObservation literal input) (executeExit fuel literal input) := by
  rw [execute_exit_exact fuel literal input inputValid literalValid]
  exact execution_tree_observed literal input

/-- One concrete branch of the complete tree: zero-sized allocations at
    1,2,3; caller result at8; callee cells at16,24; actual thread0 schedulers. -/
def executionOracle (history : List Nat) : Nat :=
  match history.length with
  | 0 => 0 | 1 => 1 | 2 => 2 | 6 => 1 | 7 => 2 | _ => 0

def normalState (literal input : Nat) : MR_Machine :=
  stoppedState literal input 1 2 3 (functionWorld 1 2) [] 8 16 24

/-- Constructive nonvacuity of the complete choice tree, for all data. This
    exhibits real MachineStop and a complete machine endpoint, with normal model termination. -/
theorem execution_tree_oracle (literal input : Nat) :
    SOut.runOracle executionOracle (fun _ => 0) (executionTree literal input) =
      .ok (.ok (.err .MachineStop, normalState literal input)) := by
  rfl

theorem exit_available (fuel literal input : Nat)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    SOut.runOracle executionOracle (fun _ => 0) (executeExit fuel literal input) =
      .ok (.ok (.err .MachineStop, normalState literal input)) := by
  rw [execute_exit_exact fuel literal input inputValid literalValid, execution_tree_oracle]


#print axioms execute_exit_exact
#print axioms execute_exit_observed
#print axioms exit_available
end MiniRustU64ExitExecution
