/- Actual Call of the separately named Exit-exitEntry program, reusing the
   frozen generic Call algebra, allocator and complete callee execution. -/
import MiniRustU64ExitRun
set_option autoImplicit false
noncomputable section
namespace MiniRustU64ExitCall
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return
  MiniRustU64Step MiniRustU64Entry MiniRustU64Call MiniRustU64AllocatedCall
  MiniRustU64ExitProgram MiniRustU64ExitStart MiniRustU64ExitRun
  MiniRustProgramCall MiniRustProgramStep MiniRustAllocate8Safety
open MiniRustU64Program (callTerm callBlock)
open MiniRustU64ProgramRun (single_cur_frame oneThreadRun)
open MiniRustU64ProgramCall (lookup_single argument_value prepare_result call_generic
  raceAfterTerm race_after_call_tree memory_clear one_thread_bind)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem eval_result_place (fuel input : Nat) (base : MR_Machine)
    (ret result : MR_ThinPointer) (pc : Int) (mem : MR_ConcurrentMemory) :
    MRf.Machine.eval_place (fuel + 10)
      (single base [callerFrame input ret result pc] mem) (.Local ⟨1⟩) =
      .ok (.ok (place result, .Int (mrIntTy false .u64)),
        single base [callerFrame input ret result pc] mem) := by
  change MRf.Machine.eval_place_open (MR_rec_130.tie (fuel + 9)) (fuel + 10)
    (single base [callerFrame input ret result pc] mem) (.Local ⟨1⟩) = _
  simp only [MRf.Machine.eval_place_open]
  rw [single_cur_frame (fuel + 6)]
  simp only [SOut.bind_ok']
  simp [callerFrame, exitEntry, SMap.index_at, SMap.get, SMap.getL, MR_LocalName.beq,
    SInt.beq, SOption.unwrap, SOut.bind_ok', MRf.ThinPointer.widen, place]


theorem function_value (fuel literal input : Nat) (first second root : Int)
    (frame : MR_StackFrame) (mem : MR_ConcurrentMemory) :
    MRf.Machine.eval_value (fuel + 3)
      (single (initialized literal input first second root) [frame] mem)
      (.Constant (.FnPointer ⟨1⟩) (.Ptr .FnPtr)) =
      .ok (.ok (.Ptr ⟨ptr 1 second, none⟩, .Ptr .FnPtr),
        single (initialized literal input first second root) [frame] mem) := rfl


theorem function_lookup (fuel literal input : Nat) (first second root : Int)
    (frame : MR_StackFrame) (mem : MR_ConcurrentMemory) :
    MRf.Machine.fn_from_ptr (fuel + 2)
      (single (initialized literal input first second root) [frame] mem)
      (.Ptr ⟨ptr 1 second, none⟩) = .ok (.ok (function literal)) := by
  rw [lookup_single, initialized_function_lookup]


def callingState (literal input : Nat) (first second root : Int) (ret : MR_ThinPointer)
    (before after : List MR_Allocation) (addr : Nat) (accesses : List MR_Access) : MR_Machine :=
  single (initialized literal input first second root)
    [callerFrame input ret (ptr before.length (Int.ofNat addr)) 1]
    (memory before after addr uninit8 accesses)

/- Shared Call algebra is imported unchanged; actual Exit-entry primitives
   below instantiate its complete constructor law. -/

attribute [local irreducible] callWith MRf.Machine.eval_call

theorem entry_call (fuel literal input : Nat) (first second root : Int)
    (ret : MR_ThinPointer) (before after : List MR_Allocation) (addr : Nat)
    (accesses : List MR_Access) (aligned : addr % 8 = 0) :
    MRf.Machine.eval_terminator (fuel + 20)
      (callingState literal input first second root ret before after addr accesses) (callTerm input) =
      MRf.Machine.eval_call (fuel + 19)
        (callingState literal input first second root ret before after addr
          (accesses ++ [⟨.Store, .None, Int.ofNat addr, 8⟩]))
        (function literal) .Rust [(.Int (Int.ofNat input), .Int (mrIntTy false .u64))]
        (place (ptr before.length (Int.ofNat addr)), .Int (mrIntTy false .u64)) (some ⟨1⟩) none := by
  unfold callTerm
  rw [actual_call]
  refine call_generic MRf.Machine.eval_place MRf.Machine.prepare_for_inplace_passing
    MRf.Machine.eval_value MRf.Machine.fn_from_ptr MRf.Machine.eval_argument
    MRf.Machine.eval_call fuel literal input second
    (callingState literal input first second root ret before after addr accesses)
    (callingState literal input first second root ret before after addr
      (accesses ++ [⟨.Store, .None, Int.ofNat addr, 8⟩]))
    (ptr before.length (Int.ofNat addr)) ?_ ?_ ?_ ?_ ?_
  · exact eval_result_place (fuel + 9) input _ ret _ 1 _
  · exact prepare_result (fuel + 11) _ _ before after addr accesses aligned
  · exact function_value (fuel + 16) literal input first second root _ _
  · exact function_lookup (fuel + 17) literal input first second root _ _
  · exact argument_value (fuel + 16) input _


theorem caller_current_block (input : Nat) (ret result : MR_ThinPointer) (pc : Int) :
    SMap.index_at MR_BbName.beq (callerFrame input ret result pc).func.blocks
      (callerFrame input ret result pc).next_block = .ok (callBlock input) := rfl

/-- The original Machine.step scheduler wrapper selects the real Call at PC1.
    Its final race checker is retained as an actual operation over every result. -/

theorem call_step_shape
    (evalStatement : Nat → MR_Machine → MR_Statement →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (evalTerminator : Nat → MR_Machine → MR_Terminator →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (fuel input : Nat) (base : MR_Machine) (ret result : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    stepWith evalStatement evalTerminator (fuel + 50)
      (single base [callerFrame input ret result 1] mem) =
      oneThreadRun ((evalTerminator (fuel + 49)
        (single base [callerFrame input ret result 1] (mem.set_accesses [])) (callTerm input)).bind
          (raceAfterTerm (fuel + 49) (SSet.insert SInt.beq base.synchronized_threads 0, mem.accesses))) := by
  exact MiniRustU64ProgramReturn.terminator_step_shape evalStatement evalTerminator fuel base
    (callerFrame input ret result 1) mem (callBlock input)
    (caller_current_block input ret result 1) (by rfl)


theorem entry_call_step (fuel literal input : Nat) (first second root : Int)
    (ret : MR_ThinPointer) (before after : List MR_Allocation) (addr : Nat)
    (accesses : List MR_Access) (aligned : addr % 8 = 0) (inputValid : input < modulus 64) :
    MRf.Machine.step (fuel + 50)
      (callingState literal input first second root ret before after addr accesses) =
      oneThreadRun (callTree (MiniRustU64Step.callerWorld before after addr uninit8)
        [⟨.Store, .None, Int.ofNat addr, 8⟩] literal input
        (.BackToCaller (some ⟨1⟩) none (ptr before.length (Int.ofNat addr)))
        (initialized literal input first second root)
        (callerFrame input ret (ptr before.length (Int.ofNat addr)) 1)) := by
  rw [actual_step]
  unfold callingState
  rw [call_step_shape, memory_clear]
  have called := entry_call (fuel + 29) literal input first second root ret before after addr [] aligned
  unfold callingState at called
  rw [called]
  have callTreeLaw := call_tree_exact (fuel + 27) literal input
    (MiniRustU64Step.callerWorld before after addr uninit8)
    [⟨.Store, .None, Int.ofNat addr, 8⟩] (initialized literal input first second root)
    (callerFrame input ret (ptr before.length (Int.ofNat addr)) 1)
    (ptr before.length (Int.ofNat addr)) (some ⟨1⟩) none inputValid
  simp only [Nat.add_assoc, List.nil_append, memory, MiniRustU64Step.callerWorld] at callTreeLaw ⊢
  rw [callTreeLaw, race_after_call_tree]


def callStepThenCallee (fuel literal input : Nat) (first second root : Int)
    (ret : MR_ThinPointer) (before after : List MR_Allocation) (addr : Nat)
    (accesses : List MR_Access) : SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  (MRf.Machine.step (fuel + 50)
    (callingState literal input first second root ret before after addr accesses)).bind
      (MiniRustU64Correspondence.afterEntry (fuel + 50))

/-- THREE actual Machine.step operations at the same bounded fuel: the exitEntry
    Call, callee Assign, and callee Return. The complete choice tree ends at
    the real caller's return block with result bytes and both private cells
    retired. Every original call/body/scheduler branch remains. -/

theorem call_step_and_callee_exact (fuel literal input : Nat) (first second root : Int)
    (ret : MR_ThinPointer) (before after : List MR_Allocation) (addr : Nat)
    (accesses : List MR_Access) (aligned : addr % 8 = 0)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    callStepThenCallee fuel literal input first second root ret before after addr accesses =
      oneThreadRun (MiniRustU64Correspondence.fullTree literal input
        (initialized literal input first second root)
        (callerFrame input ret (ptr before.length (Int.ofNat addr)) 1) ⟨1⟩
        before after addr uninit8) := by
  unfold callStepThenCallee
  rw [entry_call_step fuel literal input first second root ret before after addr accesses aligned inputValid,
    one_thread_bind]
  apply congrArg oneThreadRun
  have body := MiniRustU64Correspondence.full_tree_exact fuel literal input
    (initialized literal input first second root)
    (callerFrame input ret (ptr before.length (Int.ofNat addr)) 1) ⟨1⟩ before after addr uninit8
    [⟨.Store, .None, Int.ofNat addr, 8⟩] MiniRustU64AllocatedCall.uninit8_length aligned inputValid literalValid
  unfold MiniRustU64Correspondence.enterAndRun at body
  rw [call_tree_exact fuel literal input _ _ _ _ _ _ _ inputValid] at body
  exact body


#print axioms entry_call_step
#print axioms call_step_and_callee_exact
end MiniRustU64ExitCall
