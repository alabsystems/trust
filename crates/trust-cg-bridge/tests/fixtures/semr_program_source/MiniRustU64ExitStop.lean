/- Actual final Exit step and complete Call/callee/Exit execution. The generated
   Exit keeps its caller frame/Stack allocations; it does not simulate Return. -/
import MiniRustU64ExitCall
set_option autoImplicit false
noncomputable section
namespace MiniRustU64ExitStop
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Entry MiniRustU64AllocatedCall MiniRustU64ExitProgram MiniRustU64ExitStart
  MiniRustU64ExitRun MiniRustU64ExitCall MiniRustProgramExit MiniRustAllocate8Safety
open MiniRustU64ProgramStart (zeroSlot)
open MiniRustU64ProgramRun (single_cur_frame oneThreadRun)
open MiniRustU64ProgramCall (one_thread_bind)
open MiniRustU64ProgramReturn (rootMemory terminator_step_shape)
open MiniRustProgramStep
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def exitFrame (input : Nat) (root result : MR_ThinPointer) : MR_StackFrame :=
  ⟨exitEntry input, [(⟨0⟩, root), (⟨1⟩, result)], .BottomOfStack, ⟨1⟩, 0, ()⟩

theorem eval_exit_place (fuel input : Nat) (base : MR_Machine)
    (root result : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    MRf.Machine.eval_place (fuel + 10) (single base [exitFrame input root result] mem) (.Local ⟨0⟩) =
      .ok (.ok (place root, MiniRustU64Program.unitTy), single base [exitFrame input root result] mem) := by
  change MRf.Machine.eval_place_open (MR_rec_130.tie (fuel + 9)) (fuel + 10)
    (single base [exitFrame input root result] mem) (.Local ⟨0⟩) = _
  simp only [MRf.Machine.eval_place_open]
  rw [single_cur_frame (fuel + 6)]
  simp only [SOut.bind_ok']
  simp [exitFrame, exitEntry, SMap.index_at, SMap.get, SMap.getL, MR_LocalName.beq,
    SOption.unwrap, SOut.bind_ok', MRf.ThinPointer.widen, place]

/-- Full actual Intrinsic terminator. No place_store/jump occurs because Exit
    produces its real termination-info result; exact memory and stack survive. -/
theorem exit_terminator (fuel input : Nat) (base : MR_Machine)
    (root result : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    MRf.Machine.eval_terminator (fuel + 20) (single base [exitFrame input root result] mem) exitTerm =
      .ok (.err (if anyLiveHeap mem.memory.allocations then .MemoryLeak else .MachineStop),
        single base [exitFrame input root result] mem) := by
  simp only [exitTerm, MRf.Machine.eval_terminator]
  rw [eval_exit_place (fuel + 9)]
  simp only [SOut.bind_ok', SList.tryMapResS]
  rw [intrinsic_exit_exact (fuel + 15)]
  rfl

theorem exit_current_block (input : Nat) (root result : MR_ThinPointer) :
    SMap.index_at MR_BbName.beq (exitFrame input root result).func.blocks
      (exitFrame input root result).next_block = .ok exitBlock := rfl

/-- Real scheduler/PC/reset wrapper. Both MachineStop and MemoryLeak skip the
    final data-race check, following the unchanged model error branch exactly. -/
theorem exit_step (fuel input : Nat) (base : MR_Machine)
    (root result : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    MRf.Machine.step (fuel + 50) (single base [exitFrame input root result] mem) =
      oneThreadRun (.ok (.err (if anyLiveHeap mem.memory.allocations then .MemoryLeak else .MachineStop),
        single base [exitFrame input root result] (mem.set_accesses []))) := by
  rw [actual_step, terminator_step_shape _ _ fuel base _ _ exitBlock
    (exit_current_block input root result) (by rfl)]
  simp only [exitBlock]
  rw [exit_terminator (fuel + 29)]
  rfl

theorem heap_append (before after : List MR_Allocation) :
    anyLiveHeap (before ++ after) = (anyLiveHeap before || anyLiveHeap after) := by
  induction before with
  | nil => rfl
  | cons allocation rest ih =>
    simp only [List.cons_append, anyLiveHeap, ih, Bool.or_assoc]

theorem root_memory_heap (before after : List MR_Allocation) (root : Int)
    (addr : Nat) (bytes : List MR_AbstractByte) (accesses : List MR_Access) :
    anyLiveHeap (rootMemory before after root addr bytes accesses).memory.allocations =
      (anyLiveHeap before || anyLiveHeap after) := by
  simp [rootMemory, heap_append, anyLiveHeap, liveHeap, zeroSlot, slot]

theorem retired_tail_heap (after : List MR_Allocation) (retAddr argAddr value input : Nat) :
    anyLiveHeap (after ++
      [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false,
       (slot (Int.ofNat argAddr) (u64bytes input)).set_live false]) = anyLiveHeap after := by
  simp [heap_append, anyLiveHeap, liveHeap, MR_Allocation.set_live]

theorem resumed_exit_exact (literal input : Nat) (first second root : Int)
    (before after : List MR_Allocation) (addr retAddr argAddr value : Nat) :
    MiniRustU64Run.exitState (initialized literal input first second root)
      (callerFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr)) 1) ⟨1⟩
      (before ++ [zeroSlot .Stack root]) after addr retAddr argAddr value input =
      single (initialized literal input first second root)
        [exitFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))]
        (rootMemory before (after ++
          [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false,
           (slot (Int.ofNat argAddr) (u64bytes input)).set_live false])
          root addr (u64bytes value)
          [⟨.Load, .None, Int.ofNat retAddr, 8⟩, ⟨.Store, .None, Int.ofNat addr, 8⟩]) := by
  simp only [MiniRustU64Run.exitState, callerFrame, exitFrame,
    MR_StackFrame.set_next_block, MR_StackFrame.set_next_stmt, retiredCells,
    MiniRustU64Step.callerWorld, rootMemory, List.append_assoc, List.cons_append, List.nil_append]

def stoppedState (literal input : Nat) (first second root : Int)
    (before after : List MR_Allocation) (addr retAddr argAddr : Nat) : MR_Machine :=
  single (initialized literal input first second root)
    [exitFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))]
    (rootMemory before (after ++
      [(slot (Int.ofNat retAddr) (u64bytes ((input + literal) % modulus 64))).set_live false,
       (slot (Int.ofNat argAddr) (u64bytes input)).set_live false])
      root addr (u64bytes ((input + literal) % modulus 64)) [])

def callCalleeExit (fuel literal input : Nat) (first second root : Int)
    (before after : List MR_Allocation) (addr : Nat) (accesses : List MR_Access) :=
  (callStepThenCallee fuel literal input first second root (ptr before.length root)
    (before ++ [zeroSlot .Stack root]) after addr accesses).bind (MiniRustU64Run.nextStep (fuel + 50))

/-- Outside live Heaps are retained and produce genuine MemoryLeak. In the
    actual complete startup program there are only Function/Stack allocations,
    so MachineStop is derived without a successful leak-check/NoUB premise. -/
def stoppingTree (literal input : Nat) (first second root : Int)
    (before after : List MR_Allocation) (addr : Nat) : SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  oneThreadRun (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (MiniRustU64Step.callerWorld (before ++ [zeroSlot .Stack root]) after addr uninit8))
    (fun retIndex => selectedChoice (Int.ofNat (modulus 64))
      (allocationAllowed (MiniRustU64Step.callerWorld (before ++ [zeroSlot .Stack root]) after addr uninit8 ++
        [slot (Int.ofNat (address retIndex)) uninit8])) (fun argIndex =>
      oneThreadRun (oneThreadRun (oneThreadRun (.ok
        (.err (if anyLiveHeap before || anyLiveHeap after then .MemoryLeak else .MachineStop),
          stoppedState literal input first second root before after addr (address retIndex) (address argIndex))))))))

theorem call_callee_exit_exact (fuel literal input : Nat) (first second root : Int)
    (before after : List MR_Allocation) (addr : Nat) (accesses : List MR_Access)
    (aligned : addr % 8 = 0) (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    callCalleeExit fuel literal input first second root before after addr accesses =
      stoppingTree literal input first second root before after addr := by
  unfold callCalleeExit
  rw [call_step_and_callee_exact fuel literal input first second root (ptr before.length root)
    (before ++ [zeroSlot .Stack root]) after addr accesses aligned inputValid literalValid, one_thread_bind]
  unfold stoppingTree
  apply congrArg oneThreadRun
  unfold MiniRustU64Correspondence.fullTree
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (MiniRustU64Step.callerWorld (before ++ [zeroSlot .Stack root]) after addr uninit8)))
  funext retIndex
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (MiniRustU64Step.callerWorld (before ++ [zeroSlot .Stack root]) after addr uninit8 ++
      [slot (Int.ofNat (address retIndex)) uninit8])))
  funext argIndex
  change (oneThreadRun (oneThreadChoice _)).bind _ = _
  rw [one_thread_bind, MiniRustU64Run.choice_bind]
  change oneThreadRun (oneThreadRun (MiniRustU64Run.nextStep (fuel + 50) (.ok (), _))) = _
  apply congrArg oneThreadRun
  apply congrArg oneThreadRun
  simp only [MiniRustU64Run.nextStep, List.length_append, List.length_singleton]
  rw [resumed_exit_exact, exit_step]
  simp only [root_memory_heap, retired_tail_heap]
  rfl

#print axioms exit_terminator
#print axioms call_callee_exit_exact
end MiniRustU64ExitStop
