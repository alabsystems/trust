/- Actual generated program startup and root caller construction.
   Only original operations are factored; no startup/frame/call success premise.
   All allocation choices, errors, complete memory and access logs are retained. -/
import MiniRustU64ProgramTyping
import MiniRustMachineNew

noncomputable section
namespace MiniRustU64ProgramStart
open SemR MiniRustU64Function MiniRustU64Entry MiniRustU64Call
  MiniRustU64Program MiniRustU64ProgramTyping MiniRustMachineNew
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def pendingEntry (input : Nat) : MR_StackFrame :=
  ⟨entry input, [], .BottomOfStack, ⟨0⟩, 0, ()⟩

def entryFrame (input : Nat) (ret : MR_ThinPointer) : MR_StackFrame :=
  ⟨entry input, [(⟨0⟩, ret)], .BottomOfStack, ⟨0⟩, 0, ()⟩

theorem concurrent_new (fuel : Nat) :
    MRf.ConcurrentMemory.new (fuel + 3) () = SOut.ok ⟨⟨[], ()⟩, []⟩ := rfl

theorem abi_unit (fuel : Nat) :
    MRf.fn.check_abi_compatibility (fuel + 3) unitTy unitTy = SOut.ok true := rfl

theorem dead_absent_unit (fuel input : Nat) (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_dead (fuel + 7) (pendingEntry input) mem ⟨0⟩ =
      .ok (.ok (), pendingEntry input, mem) := by
  simp only [MRf.StackFrame.storage_dead, pendingEntry, entry, SMap.index_at,
    SMap.get, SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false,
    SOption.unwrap, SOut.bind_ok', MiniRustU64Program.unit_layout,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align,
    SMap.remove, SMap.removeL]
  rfl

theorem continue_unit (fuel input : Nat) (mem : MR_ConcurrentMemory)
    (allocate : MR_ConcurrentMemory → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory)) :
    liveContinuation (fuel + 4) allocate ⟨0⟩ (.ok (), pendingEntry input, mem) =
      (allocate mem 0 1).bind (finishLive (pendingEntry input) ⟨0⟩) := by
  simp only [liveContinuation, pendingEntry, entry, SMap.index_at, SMap.get,
    SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false, SOption.unwrap,
    SOut.bind_ok', MiniRustU64Program.unit_layout,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align]

theorem live_unit (fuel input : Nat) (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_live (fuel + 9) (pendingEntry input) mem ⟨0⟩ =
      (MRf.ConcurrentMemory.allocate (fuel + 8) mem .Stack 0 1).bind
        (finishLive (pendingEntry input) ⟨0⟩) := by
  rw [live_unfold, dead_absent_unit (fuel + 1)]
  simp only [SOut.bind_ok']
  exact continue_unit (fuel + 4) input mem _

def finishEntry (machine : MR_Machine) (input : Nat)
    (result : SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory) :
    SOut (SRes MR_TerminationInfo MR_StackFrame × MR_Machine) :=
  match result with
  | (.err error, mem) => .ok (.err error, machine.set_mem mem)
  | (.ok ret, mem) => .ok (.ok (entryFrame input ret), machine.set_mem mem)

/-- Algebra over complete primitive results, instantiated with the actual
    storage law below. No primitive success is assumed. -/
theorem create_entry_generic
    (storageLive : Nat → MR_StackFrame → MR_ConcurrentMemory → MR_LocalName →
      SOut (SRes MR_TerminationInfo Unit × MR_StackFrame × MR_ConcurrentMemory))
    (typedStore : Nat → MR_Machine → MR_ThinPointer → MR_Value → MR_Type → Int → MR_Atomicity →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (allocate : Nat → MR_ConcurrentMemory → MR_AllocationKind → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory))
    (fuel input : Nat) (machine : MR_Machine)
    (retLaw : ∀ mem, storageLive (fuel + 10) (pendingEntry input) mem ⟨0⟩ =
      (allocate (fuel + 9) mem .Stack 0 1).bind (finishLive (pendingEntry input) ⟨0⟩)) :
    createWith storageLive typedStore (fuel + 11) machine (entry input) .BottomOfStack .C unitTy [] =
      (allocate (fuel + 9) machine.mem .Stack 0 1).bind (finishEntry machine input) := by
  simp only [createWith, MRf.BasicMemory.Memory.new_call, SOut.bind_ok',
    entry_start, entry_ret, entry_args, entry_convention, entry_locals]
  have live := retLaw machine.mem
  simp only [pendingEntry, Nat.add_assoc] at live
  rw [live, bind_associative]
  generalize ha : allocate (fuel + 9) machine.mem .Stack 0 1 = allocation
  apply congrArg (fun next => allocation.bind next)
  funext result
  rcases result with ⟨res, mem⟩
  cases res with
  | err error => rfl
  | ok ret =>
    simp only [finishLive, pendingEntry, entry, SMap.insert,
      MR_StackFrame.set_locals, SOut.bind_ok', MR_CallingConvention.beq,
      SBool.not, SLoop.forS, SList.zip, SList.len, SList.lenNat, SList.push,
      SList.appendL, SInt.beq, SMap.index_at, SMap.get, SMap.getL,
      MR_LocalName.beq, SOption.unwrap, abi_unit, finishEntry, entryFrame, decide_true]

theorem create_entry (fuel input : Nat) (machine : MR_Machine) :
    MRf.Machine.create_frame (fuel + 11) machine (entry input) .BottomOfStack .C unitTy [] =
      (MRf.ConcurrentMemory.allocate (fuel + 9) machine.mem .Stack 0 1).bind
        (finishEntry machine input) := by
  rw [actual_create]
  apply create_entry_generic
  intro mem
  exact live_unit (fuel + 1) input mem

def finishThread
    (result : SRes MR_TerminationInfo MR_StackFrame × MR_Machine) :
    SOut (SRes MR_TerminationInfo Int × MR_Machine) :=
  match result with
  | (.err error, machine) => .ok (.err error, machine)
  | (.ok frame, machine) =>
      .ok (.ok (SList.len machine.threads),
        machine.set_threads (SList.push machine.threads ⟨[frame], .Enabled, []⟩))

theorem new_thread_unfold (fuel : Nat) (machine : MR_Machine) (func : MR_Function) :
    MRf.Machine.new_thread (fuel + 2) machine func [] =
      (MRf.Machine.create_frame (fuel + 1) machine func .BottomOfStack .C unitTy []).bind
        finishThread := by
  simp only [MRf.Machine.new_thread, MiniRustU64Program.unit_type, SOut.bind_ok']
  apply congrArg (fun next =>
    (MRf.Machine.create_frame (fuel + 1) machine func .BottomOfStack .C unitTy []).bind next)
  funext result
  rcases result with ⟨res, nextMachine⟩
  cases res <;> rfl

def rootMachine (machine : MR_Machine) (input : Nat)
    (ret : MR_ThinPointer) (mem : MR_ConcurrentMemory) : MR_Machine :=
  (machine.set_mem mem).set_threads
    (SList.push machine.threads ⟨[entryFrame input ret], .Enabled, []⟩)

def finishRootThread (machine : MR_Machine) (input : Nat)
    (result : SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory) :
    SOut (SRes MR_TerminationInfo Int × MR_Machine) :=
  match result with
  | (.err error, mem) => .ok (.err error, machine.set_mem mem)
  | (.ok ret, mem) => .ok (.ok (SList.len machine.threads), rootMachine machine input ret mem)

/-- Actual caller thread construction over every complete allocation result.
    No new_thread/frame or allocation success is postulated. -/
theorem new_thread_entry (fuel input : Nat) (machine : MR_Machine) :
    MRf.Machine.new_thread (fuel + 12) machine (entry input) [] =
      (MRf.ConcurrentMemory.allocate (fuel + 9) machine.mem .Stack 0 1).bind
        (finishRootThread machine input) := by
  rw [new_thread_unfold (fuel + 10), create_entry, bind_associative]
  apply congrArg (fun next =>
    (MRf.ConcurrentMemory.allocate (fuel + 9) machine.mem .Stack 0 1).bind next)
  funext result
  rcases result with ⟨res, mem⟩
  cases res <;> cases machine <;> rfl

def beforeThread (literal input : Nat) (first second : MR_ThinPointer)
    (mem : MR_ConcurrentMemory) : MR_Machine :=
  ⟨program literal input, mem, ⟨[]⟩, [], 0, [], [], [],
    [(⟨0⟩, first), (⟨1⟩, second)], [], (), ()⟩

def finishNew (result : SRes MR_TerminationInfo Int × MR_Machine) :
    SOut (SRes MR_TerminationInfo MR_Machine) :=
  match result with
  | (.err error, _) => .ok (.err error)
  | (.ok _, machine) => .ok (.ok machine)

def functionPlanWith
    (allocate : Nat → MR_ConcurrentMemory → MR_AllocationKind → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory))
    (newThread : Nat → MR_Machine → MR_Function → List (MR_Value × MR_Type) →
      SOut (SRes MR_TerminationInfo Int × MR_Machine))
    (fuel literal input : Nat) : SOut (SRes MR_TerminationInfo MR_Machine) :=
  (allocate fuel ⟨⟨[], ()⟩, []⟩ .Function 0 1).bind (fun result => match result with
    | (.err error, _) => .ok (.err error)
    | (.ok first, mem) =>
      (allocate fuel mem .Function 0 1).bind (fun result => match result with
        | (.err error, _) => .ok (.err error)
        | (.ok second, mem) =>
          (newThread fuel (beforeThread literal input first second mem)
            (entry input) []).bind finishNew))

theorem new_shape_generic
    (checkWf : Nat → MR_Program → SOut (SRes MR_TerminationInfo Unit))
    (newMemory : Nat → Unit → SOut MR_ConcurrentMemory)
    (allocate : Nat → MR_ConcurrentMemory → MR_AllocationKind → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory))
    (newThread : Nat → MR_Machine → MR_Function → List (MR_Value × MR_Type) →
      SOut (SRes MR_TerminationInfo Int × MR_Machine))
    (fuel literal input : Nat)
    (checked : checkWf (fuel + 1) (program literal input) = .ok (.ok ()))
    (memory : newMemory (fuel + 1) () = .ok ⟨⟨[], ()⟩, []⟩) :
    newWith checkWf newMemory allocate newThread (fuel + 2) (program literal input) () () () =
      functionPlanWith allocate newThread (fuel + 1) literal input := by
  simp only [newWith, checked, memory, SOut.bind_ok',
    program_globals, program_functions, program_vtables, program_start,
    SLoop.forS, MRf.IntPtrCast.new]
  unfold functionPlanWith
  simp only [bind_associative]
  generalize ha : allocate (fuel + 1) ⟨⟨[], ()⟩, []⟩ .Function 0 1 = allocation
  apply congrArg (fun next => allocation.bind next)
  funext result
  rcases result with ⟨res, mem⟩
  cases res with
  | err error => rfl
  | ok first =>
    simp only [SOut.bind_ok', SMap.insert, SMap.get, SMap.getL,
      SList.push, SList.appendL, SLoop.forS, bind_associative]
    generalize hb : allocate (fuel + 1) mem .Function 0 1 = secondAllocation
    apply congrArg (fun next => secondAllocation.bind next)
    funext second
    rcases second with ⟨res, mem⟩
    cases res with
    | err error => rfl
    | ok last =>
      simp only [SOut.bind_ok', SMap.insert, SMap.get, SMap.getL,
        SMap.index_at, SOption.unwrap, MR_FnName.beq, SInt.beq, decide_true,
        decide_false, SList.push, SList.appendL, SLoop.forS, MRf.IntPtrCast.new,
        beforeThread]
      apply congrArg (fun next =>
        (newThread (fuel + 1) (beforeThread literal input first last mem) (entry input) []).bind next)
      funext result
      rcases result with ⟨res, machine⟩
      cases res <;> rfl

theorem new_shape (fuel literal input : Nat)
    (literalValid : literal < modulus 64) (inputValid : input < modulus 64) :
    MRf.Machine.new (fuel + 81) (program literal input) () () () =
      functionPlanWith MRf.ConcurrentMemory.allocate MRf.Machine.new_thread
        (fuel + 80) literal input := by
  rw [actual_new]
  apply new_shape_generic
  · exact program_wellformed fuel literal input literalValid inputValid
  · exact concurrent_new (fuel + 77)

def zeroSlot (kind : MR_AllocationKind) (addr : Int) : MR_Allocation :=
  ⟨[], addr, 1, kind, true, ()⟩

def zeroMemory (kind : MR_AllocationKind) (world : List MR_Allocation)
    (accesses : List MR_Access) (addr : Int) : MR_ConcurrentMemory :=
  ⟨⟨world ++ [zeroSlot kind addr], ()⟩, accesses⟩

/-- The full original guarded zero-size allocation. Equal start addresses
    still conflict, even though both allocation byte lists are empty. -/
def zeroTree (kind : MR_AllocationKind) (world : List MR_Allocation)
    (accesses : List MR_Access) : SOut (MR_ThinPointer × MR_ConcurrentMemory) :=
  (SPick.choose ⟨1, Int.ofNat (modulus 64), 1⟩
    (fun addr (_ : Unit) => .ok (MiniRustAllocate.allowed 0 1 world addr, ())) ()).bind
      (fun pair => .ok (ptr world.length pair.1, zeroMemory kind world accesses pair.1))

theorem concurrent_zero (fuel : Nat) (kind : MR_AllocationKind)
    (world : List MR_Allocation) (accesses : List MR_Access) :
    MRf.ConcurrentMemory.allocate (fuel + 6) ⟨⟨world, ()⟩, accesses⟩ kind 0 1 =
      (zeroTree kind world accesses).bind (fun pair => .ok (.ok pair.1, pair.2)) := by
  simp only [MRf.ConcurrentMemory.allocate, MRf.BasicMemory.Memory.allocate]
  have law : MRf.BasicMemory.allocate (fuel + 4) ⟨world, ()⟩ kind 0 1 () () =
      MiniRustAllocate.tree 0 1 world kind :=
    MiniRustAllocate.allocate_exact fuel 0 0 world kind
  rw [law]
  simp only [bind_associative]
  unfold MiniRustAllocate.tree zeroTree
  have zeroValid : inRange true 64 (0 : Int) = true := rfl
  have zeroCast : (((0 : Nat) : Int)) = 0 := rfl
  have oneCast : (((1 : Nat) : Int)) = 1 := rfl
  simp only [zeroCast, oneCast, zeroValid, ite_true, bind_associative]
  apply congrArg (fun next => (SPick.choose ⟨1, Int.ofNat (modulus 64), 1⟩
    (fun addr (_ : Unit) => .ok (MiniRustAllocate.allowed 0 1 world addr, ())) ()).bind next)
  funext result
  rcases result with ⟨addr, state⟩
  cases state
  rfl

def startupTree (literal input : Nat) : SOut (SRes MR_TerminationInfo MR_Machine) :=
  (zeroTree .Function [] []).bind (fun first =>
    (zeroTree .Function first.2.memory.allocations first.2.accesses).bind (fun second =>
      (zeroTree .Stack second.2.memory.allocations second.2.accesses).bind (fun root =>
        .ok (.ok (rootMachine (beforeThread literal input first.1 second.1 second.2)
          input root.1 root.2)))))

theorem new_thread_zero (fuel input : Nat) (machine : MR_Machine) :
    MRf.Machine.new_thread (fuel + 12) machine (entry input) [] =
      (zeroTree .Stack machine.mem.memory.allocations machine.mem.accesses).bind
        (fun pair => finishRootThread machine input (.ok pair.1, pair.2)) := by
  rw [new_thread_entry]
  generalize hm : machine.mem = mem
  rcases mem with ⟨⟨world, extra⟩, accesses⟩
  cases extra
  rw [concurrent_zero (fuel + 3), bind_associative]
  rfl

theorem startup_plan_generic
    (allocate : Nat → MR_ConcurrentMemory → MR_AllocationKind → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory))
    (newThread : Nat → MR_Machine → MR_Function → List (MR_Value × MR_Type) →
      SOut (SRes MR_TerminationInfo Int × MR_Machine))
    (fuel literal input : Nat)
    (functionLaw : ∀ world accesses,
      allocate fuel ⟨⟨world, ()⟩, accesses⟩ .Function 0 1 =
        (zeroTree .Function world accesses).bind (fun pair => .ok (.ok pair.1, pair.2)))
    (threadLaw : ∀ machine, newThread fuel machine (entry input) [] =
      (zeroTree .Stack machine.mem.memory.allocations machine.mem.accesses).bind
        (fun pair => finishRootThread machine input (.ok pair.1, pair.2))) :
    functionPlanWith allocate newThread fuel literal input = startupTree literal input := by
  unfold functionPlanWith startupTree
  rw [functionLaw, bind_associative]
  apply congrArg (fun next => (zeroTree .Function [] []).bind next)
  funext first
  rcases first with ⟨firstPtr, firstMem⟩
  simp only [SOut.bind_ok']
  rcases firstMem with ⟨⟨world, extra⟩, accesses⟩
  cases extra
  rw [functionLaw, bind_associative]
  apply congrArg (fun next => (zeroTree .Function world accesses).bind next)
  funext second
  rcases second with ⟨secondPtr, secondMem⟩
  simp only [SOut.bind_ok']
  rw [threadLaw, bind_associative]
  apply congrArg (fun next =>
    (zeroTree .Stack secondMem.memory.allocations secondMem.accesses).bind next)
  funext root
  rcases root with ⟨ret, mem⟩
  rfl

/-- Real Machine.new, including its full program validator, both Function
    allocations and zero-size root return allocation, then actual root thread
    creation. Every original demonic choice and rejected candidate remains. -/
theorem startup_exact (fuel literal input : Nat)
    (literalValid : literal < modulus 64) (inputValid : input < modulus 64) :
    MRf.Machine.new (fuel + 81) (program literal input) () () () =
      startupTree literal input := by
  rw [new_shape fuel literal input literalValid inputValid]
  apply startup_plan_generic
  · intro world accesses
    exact concurrent_zero (fuel + 74) .Function world accesses
  · intro machine
    exact new_thread_zero (fuel + 68) input machine

def initialized (literal input : Nat) (first second root : Int) : MR_Machine :=
  ⟨program literal input,
    ⟨⟨[zeroSlot .Function first, zeroSlot .Function second, zeroSlot .Stack root], ()⟩, []⟩,
    ⟨[]⟩, [⟨[entryFrame input (ptr 2 root)], .Enabled, []⟩], 0, [], [], [],
    [(⟨0⟩, ptr 0 first), (⟨1⟩, ptr 1 second)], [], (), ()⟩

def startupOracle (history : List Nat) : Nat := history.length

/-- Constructive nonvacuity, using the actual oracle interpreter on the exact
    guarded tree. Addresses 1, 2, 3 are distinct even for zero-sized objects. -/
theorem startup_oracle (literal input : Nat) :
    SOut.runOracle startupOracle (fun _ => 0) (startupTree literal input) =
      .ok (.ok (initialized literal input 1 2 3)) := by
  rfl

/-- A colliding second zero-size function allocation is genuinely rejected. -/
theorem colliding_oracle (literal input : Nat) :
    SOut.runOracle (fun _ => 0) (fun _ => 0) (startupTree literal input) = .reject := by
  rfl

theorem initialized_cur_frame (fuel literal input : Nat) (first second root : Int) :
    MRf.Machine.cur_frame (fuel + 3) (initialized literal input first second root) =
      .ok (entryFrame input (ptr 2 root)) := by
  simp only [MRf.Machine.cur_frame, MRf.Machine.active_thread, MRf.Thread.cur_frame,
    initialized, SList.index_at, SList.get, SList.getNat, SOut.bind_ok',
    SOption.unwrap, SList.last]

theorem initialized_function_constant (fuel literal input : Nat) (first second root : Int) :
    MRf.Machine.eval_constant (fuel + 2) (initialized literal input first second root)
      (.FnPointer ⟨1⟩) =
      .ok (.ok (.Ptr ⟨ptr 1 second, none⟩), initialized literal input first second root) := by
  rfl

theorem initialized_function_lookup (fuel literal input : Nat) (first second root : Int) :
    MRf.Machine.fn_from_ptr (fuel + 2) (initialized literal input first second root)
      (.Ptr ⟨ptr 1 second, none⟩) = .ok (.ok (function literal)) := by
  have different : decide (Int.ofNat 0 = Int.ofNat 1) = false := rfl
  simp only [MRf.Machine.fn_from_ptr, initialized, ptr, SOption.is_some,
    SList.findS, MR_ThinPointer.beq, MR_AllocId.beq, SOption.beq, SInt.beq, decide_true,
    decide_false, Bool.and_false, Bool.and_true, SOut.bind_ok', SMap.index_at,
    SMap.get, SMap.getL, MR_FnName.beq, SOption.unwrap, program_functions, different]
  all_goals rfl

theorem startup_result (fuel literal input : Nat)
    (literalValid : literal < modulus 64) (inputValid : input < modulus 64) :
    SOut.runOracle startupOracle (fun _ => 0)
      (MRf.Machine.new (fuel + 81) (program literal input) () () ()) =
      .ok (.ok (initialized literal input 1 2 3)) := by
  rw [startup_exact fuel literal input literalValid inputValid]
  exact startup_oracle literal input

/-- Actual startup and actual current-frame access for every full64 pair.
    Neither a successful startup nor an existing caller frame is a premise. -/
theorem startup_available (fuel literal input : Nat)
    (literalValid : literal < modulus 64) (inputValid : input < modulus 64) :
    ∃ machine,
      SOut.runOracle startupOracle (fun _ => 0)
        (MRf.Machine.new (fuel + 81) (program literal input) () () ()) = .ok (.ok machine) ∧
      MRf.Machine.cur_frame (fuel + 3) machine = .ok (entryFrame input (ptr 2 3)) := by
  refine ⟨initialized literal input 1 2 3, ?_, initialized_cur_frame fuel literal input 1 2 3⟩
  rw [startup_exact fuel literal input literalValid inputValid]
  exact startup_oracle literal input

namespace Controls

def Zero : Prop :=
  SOut.runOracle startupOracle (fun _ => 0) (MRf.Machine.new 81 (program 0 0) () () ()) =
    .ok (.ok (initialized 0 0 1 2 3))
theorem zero : Zero := startup_result 0 0 0 (by decide) (by decide)

def Eight : Prop :=
  SOut.runOracle startupOracle (fun _ => 0) (MRf.Machine.new 81 (program 8 0) () () ()) =
    .ok (.ok (initialized 8 0 1 2 3))
theorem eight : Eight := startup_result 0 8 0 (by decide) (by decide)

def Max : Prop :=
  SOut.runOracle startupOracle (fun _ => 0)
    (MRf.Machine.new 81 (program 18446744073709551615 18446744073709551615) () () ()) =
    .ok (.ok (initialized 18446744073709551615 18446744073709551615 1 2 3))
theorem max : Max :=
  startup_result 0 18446744073709551615 18446744073709551615 (by decide) (by decide)

def Collision : Prop :=
  SOut.runOracle (fun _ => 0) (fun _ => 0) (startupTree 8 0) = .reject
theorem collision : Collision := colliding_oracle 8 0

def RootFrame : Prop :=
  MRf.Machine.cur_frame 3 (initialized 8 0 1 2 3) = .ok (entryFrame 0 (ptr 2 3))
theorem rootFrame : RootFrame := initialized_cur_frame 0 8 0 1 2 3

def FunctionLookup : Prop :=
  MRf.Machine.fn_from_ptr 2 (initialized 8 0 1 2 3) (.Ptr ⟨ptr 1 2, none⟩) =
    .ok (.ok (function 8))
theorem functionLookup : FunctionLookup := initialized_function_lookup 0 8 0 1 2 3

-- Closed counterclaims for independent TypeMismatch controls. No proof is
-- supplied for these propositions and no resource refusal counts as rejection.
def WrongLiteral : Prop :=
  SOut.runOracle startupOracle (fun _ => 0) (MRf.Machine.new 81 (program 8 0) () () ()) =
    .ok (.ok (initialized 9 0 1 2 3))

def WrongRootKind : Prop :=
  SOut.runOracle startupOracle (fun _ => 0) (MRf.Machine.new 81 (program 8 0) () () ()) =
    .ok (.ok ((initialized 8 0 1 2 3).set_mem
      ⟨⟨[zeroSlot .Function 1, zeroSlot .Function 2, zeroSlot .Function 3], ()⟩, []⟩))

def MissingRootAllocation : Prop :=
  SOut.runOracle startupOracle (fun _ => 0) (MRf.Machine.new 81 (program 8 0) () () ()) =
    .ok (.ok ((initialized 8 0 1 2 3).set_mem
      ⟨⟨[zeroSlot .Function 1, zeroSlot .Function 2], ()⟩, []⟩))

def WrongCaller : Prop :=
  MRf.Machine.cur_frame 3 (initialized 8 0 1 2 3) = .ok (entryFrame 0 (ptr 1 2))

end Controls

#print axioms create_entry
#print axioms new_thread_entry
#print axioms new_shape
#print axioms startup_exact
#print axioms startup_available
#print axioms Controls.max

end MiniRustU64ProgramStart
