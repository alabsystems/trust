/- Actual Machine.new followed by five bounded Machine.step operations for the
   immutable Returning entry. Its terminal outcome is UB, never MachineStop. -/
import MiniRustU64ProgramReturn
set_option autoImplicit false
noncomputable section
namespace MiniRustU64ProgramExecution
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Step MiniRustU64Entry
  MiniRustU64AllocatedCall MiniRustU64Program MiniRustU64ProgramStart
  MiniRustU64ProgramRun MiniRustU64ProgramCall MiniRustU64ProgramReturn
  MiniRustAllocate8Safety
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def functionWorld (first second : Int) : List MR_Allocation :=
  [zeroSlot .Function first, zeroSlot .Function second]

theorem choice_bind_selected {α β : Type} (bound : Int) (allowed : Int → Bool)
    (make : Int → α) (next : α → SOut β) :
    (choiceTree bound allowed make).bind next =
      selectedChoice bound allowed (fun index => next (make (candidate index))) := by
  apply congrArg SOut.pick
  funext index
  dsimp only
  cases hb : SInt.blt (candidate index) bound <;>
    cases ha : allowed (candidate index) <;> rfl

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
    (fun index => returningTree literal input first second root (functionWorld first second) [] (address index)))

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
  change callCalleeRootReturn fuel literal input first second root
    (functionWorld first second) [] (address index) [] = _
  exact call_callee_root_return_exact fuel literal input first second root _ _ _ _
    (address_aligned index) inputValid literalValid

/-- Real startup errors have no machine state. The outer result preserves that
    distinction; the inner result is the actual bounded execution endpoint. -/
def continueNew (fuel : Nat) (result : SRes MR_TerminationInfo MR_Machine) :
    SOut (SRes MR_TerminationInfo (SRes MR_TerminationInfo Unit × MR_Machine)) :=
  match result with
  | .err error => .ok (.err error)
  | .ok machine => (fiveSteps fuel machine).bind (fun endpoint => .ok (.ok endpoint))

def executeReturning (fuel literal input : Nat) :=
  (MRf.Machine.new (fuel + 81) (program literal input) () () ()).bind (continueNew fuel)

/-- Actual guarded zero-allocation distribution; only the continuation is
    exposed so source Machine.new choices are retained verbatim. -/
def chooseZero {α : Type} (world : List MR_Allocation) (next : Int → SOut α) :=
  (SPick.choose ⟨1, Int.ofNat (modulus 64), 1⟩
    (fun addr (_ : Unit) => .ok (MiniRustAllocate.allowed 0 1 world addr, ())) ()).bind
      (fun pair => next pair.1)

def executionTree (literal input : Nat) :
    SOut (SRes MR_TerminationInfo (SRes MR_TerminationInfo Unit × MR_Machine)) :=
  chooseZero [] (fun first => chooseZero [zeroSlot .Function first] (fun second =>
    chooseZero (functionWorld first second) (fun root =>
      (initializedTree literal input first second root).bind (fun endpoint => .ok (.ok endpoint)))))

theorem zero_tree_bind {α : Type} (kind : MR_AllocationKind) (world : List MR_Allocation)
    (accesses : List MR_Access) (next : MR_ThinPointer × MR_ConcurrentMemory → SOut α) :
    (zeroTree kind world accesses).bind next =
      chooseZero world (fun addr => next (ptr world.length addr, zeroMemory kind world accesses addr)) := by
  unfold zeroTree chooseZero
  rw [bind_associative]
  rfl

theorem choose_zero_bind {α β : Type} (world : List MR_Allocation)
    (next : Int → SOut α) (finish : α → SOut β) :
    (chooseZero world next).bind finish = chooseZero world (fun addr => (next addr).bind finish) := by
  unfold chooseZero
  rw [bind_associative]

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
    start-thread Return UB, with no assumed successful operation. -/
theorem execute_returning_exact (fuel literal input : Nat)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    executeReturning fuel literal input = executionTree literal input := by
  unfold executeReturning
  rw [startup_exact fuel literal input literalValid inputValid,
    startup_execution_tree fuel literal input inputValid literalValid]

/-- One concrete branch of the complete tree: zero-sized allocations at
    1,2,3; caller result at8; callee cells at16,24; actual thread0 schedulers. -/
def executionOracle (history : List Nat) : Nat :=
  match history.length with
  | 0 => 0 | 1 => 1 | 2 => 2 | 6 => 1 | 7 => 2 | _ => 0

def returnedState (literal input : Nat) : MR_Machine :=
  single (initialized literal input 1 2 3) []
    (retiredRootMemory (functionWorld 1 2)
      [(slot 16 (u64bytes ((input + literal) % modulus 64))).set_live false,
       (slot 24 (u64bytes input)).set_live false]
      3 8 (u64bytes ((input + literal) % modulus 64)) [⟨.Load, .None, 3, 0⟩])

/-- Constructive nonvacuity of the complete choice tree, for all data. This
    exhibits real UB and a complete machine endpoint, not normal termination. -/
theorem execution_tree_oracle (literal input : Nat) :
    SOut.runOracle executionOracle (fun _ => 0) (executionTree literal input) =
      .ok (.ok (.err (.Ub "the start function must not return"), returnedState literal input)) := by
  rfl

theorem returning_available (fuel literal input : Nat)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    SOut.runOracle executionOracle (fun _ => 0) (executeReturning fuel literal input) =
      .ok (.ok (.err (.Ub "the start function must not return"), returnedState literal input)) := by
  rw [execute_returning_exact fuel literal input inputValid literalValid, execution_tree_oracle]

#print axioms initialized_five_steps
#print axioms returning_available
#print axioms execute_returning_exact
end MiniRustU64ProgramExecution
