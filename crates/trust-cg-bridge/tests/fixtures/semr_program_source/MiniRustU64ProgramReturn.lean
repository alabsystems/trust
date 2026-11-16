/- Actual root Return operations. The frozen Returning entry cannot terminate
   normally: the generated model refuses return from active thread0. -/
import MiniRustU64ProgramCall

set_option autoImplicit false
noncomputable section
namespace MiniRustU64ProgramReturn
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return
  MiniRustU64Step MiniRustU64Entry MiniRustU64Call MiniRustU64AllocatedCall
  MiniRustU64Program MiniRustU64ProgramStart MiniRustU64ProgramRun MiniRustU64ProgramCall
  MiniRustAllocate8Safety MiniRustProgramStep
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem decode_unit (fuel : Nat) :
    MRf.Type.decode (fuel + 3) unitTy [] = .ok (some (.Tuple [])) := rfl

theorem check_unit (fuel : Nat) (machine : MR_Machine) :
    MRf.Machine.check_value (fuel + 3) machine (.Tuple []) unitTy = .ok (.ok ()) := rfl

/-- The actual model permits a zero-length load after checking alignment;
    it does not inspect provenance in this branch. The zero-byte Load log is
    nevertheless retained. This supplies no physical address-validity claim. -/
theorem load_zero (fuel idx : Nat) (addr : Int) (mem : MR_ConcurrentMemory) :
    MRf.ConcurrentMemory.load (fuel + 6) mem (ptr idx addr) 0 1 .None =
      .ok (.ok [], mem.set_accesses
        (mem.accesses ++ [⟨.Load, .None, addr, 0⟩])) := by
  have aligned : SAlign.is_aligned 1 addr = .ok true := by
    cases addr <;> simp [SAlign.is_aligned, SInt.rem, SInt.abs, SInt.isNeg,
      SInt.ofSignedNat, SInt.beq, SOut.bind_ok']
  cases mem with
  | mk memory accesses =>
    cases memory
    simp [MRf.ConcurrentMemory.load, MRf.BasicMemory.Memory.load, MRf.BasicMemory.load,
      MRf.BasicMemory.check_ptr, ptr, aligned, SSize.is_zero, SSize.from_bytes,
      SBool.not, SInt.blt, SInt.beq, SList.from_elem, SList.repeatNat,
      SOut.bind_ok', SOption.unwrap, MR_ConcurrentMemory.set_memory,
      MR_ConcurrentMemory.set_accesses, SList.push, MiniRustAllocate8Safety.append_model]

theorem typed_load_unit (fuel idx : Nat) (addr : Int) (machine : MR_Machine) :
    MRf.Machine.typed_load (fuel + 12) machine (ptr idx addr) unitTy 1 .None =
      .ok (.ok (.Tuple []), machine.set_mem (machine.mem.set_accesses
        (machine.mem.accesses ++ [⟨.Load, .None, addr, 0⟩]))) := by
  simp only [MRf.Machine.typed_load]
  rw [MiniRustU64Program.unit_layout (fuel + 7)]
  simp only [SOut.bind_ok', MRf.LayoutStrategy.expect_size]
  rw [load_zero (fuel + 5)]
  simp only [SOut.bind_ok']
  rw [decode_unit (fuel + 8)]
  simp only [SOut.bind_ok']
  rw [check_unit (fuel + 8)]
  rfl

private theorem get_at_prefix {α : Type} (xs : List α) (x : α) (ys : List α) :
    SList.getNat (xs ++ x :: ys) xs.length = some x := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact ih

private theorem set_at_prefix {α : Type} (xs : List α) (x y : α) (ys : List α) :
    SList.setNat (xs ++ x :: ys) xs.length y = some (xs ++ y :: ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa only [List.cons_append, List.length_cons, SList.setNat, ih]

/-- Real deallocation of a live zero-size Stack allocation. It is not erased
    just because its data is empty: the exact record is retired in place. -/
theorem deallocate_zero (fuel : Nat) (before after : List MR_Allocation) (addr : Int)
    (accesses : List MR_Access) :
    MRf.ConcurrentMemory.deallocate (fuel + 5)
      ⟨⟨before ++ zeroSlot .Stack addr :: after, ()⟩, accesses⟩
      (ptr before.length addr) .Stack 0 1 =
      .ok (.ok (), ⟨⟨before ++ (zeroSlot .Stack addr).set_live false :: after, ()⟩, accesses⟩) := by
  simp [MRf.ConcurrentMemory.deallocate, MRf.BasicMemory.Memory.deallocate,
    MRf.BasicMemory.deallocate, ptr, SList.index_at, SList.get, get_at_prefix,
    SOut.bind_ok', zeroSlot, SBool.not, SInt.beq, MR_AllocationKind.beq,
    MRf.Allocation.size, SSize.from_bytes, SInt.blt, SList.len, SemR.lenNat_eq,
    SOption.unwrap, MR_Allocation.set_extra, MR_Allocation.set_live,
    SList.set, set_at_prefix, MR_BasicMemory.set_allocations, MR_ConcurrentMemory.set_memory]

def returnFrame (input : Nat) (root result : MR_ThinPointer) : MR_StackFrame :=
  ⟨entry input, [(⟨0⟩, root), (⟨1⟩, result)], .BottomOfStack, ⟨1⟩, 0, ()⟩

def rootMemory (before after : List MR_Allocation) (root : Int) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) : MR_ConcurrentMemory :=
  ⟨⟨before ++ zeroSlot .Stack root :: slot (Int.ofNat addr) bytes :: after, ()⟩, accesses⟩

def deadRootMemory (before after : List MR_Allocation) (root : Int) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) : MR_ConcurrentMemory :=
  ⟨⟨before ++ (zeroSlot .Stack root).set_live false :: slot (Int.ofNat addr) bytes :: after, ()⟩, accesses⟩

def retiredRootMemory (before after : List MR_Allocation) (root : Int) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) : MR_ConcurrentMemory :=
  ⟨⟨before ++ (zeroSlot .Stack root).set_live false ::
    (slot (Int.ofNat addr) bytes).set_live false :: after, ()⟩, accesses⟩

theorem storage_dead_root (fuel input : Nat) (before after : List MR_Allocation)
    (root : Int) (addr : Nat) (bytes : List MR_AbstractByte) (accesses : List MR_Access) :
    MRf.StackFrame.storage_dead (fuel + 10)
      (returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr)))
      (rootMemory before after root addr bytes accesses) ⟨0⟩ =
      .ok (.ok (),
        (returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))).set_locals
          [(⟨1⟩, ptr (before.length + 1) (Int.ofNat addr))],
        deadRootMemory before after root addr bytes accesses) := by
  simp only [MRf.StackFrame.storage_dead, returnFrame, entry, SMap.index_at,
    SMap.get, SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false,
    SOption.unwrap, SOut.bind_ok', MiniRustU64Program.unit_layout,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align, SMap.remove, SMap.removeL]
  simp only [rootMemory]
  rw [deallocate_zero (fuel + 4) before (slot (Int.ofNat addr) bytes :: after) root accesses]
  rfl

theorem storage_dead_result (fuel input : Nat) (before after : List MR_Allocation)
    (root : Int) (addr : Nat) (bytes : List MR_AbstractByte) (accesses : List MR_Access)
    (length : bytes.length = 8) :
    MRf.StackFrame.storage_dead (fuel + 10)
      ((returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))).set_locals
        [(⟨1⟩, ptr (before.length + 1) (Int.ofNat addr))])
      (deadRootMemory before after root addr bytes accesses) ⟨1⟩ =
      .ok (.ok (),
        (returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))).set_locals [],
        retiredRootMemory before after root addr bytes accesses) := by
  have deallocated := concurrent_deallocate_private_slot (fuel + 4)
    (before ++ [(zeroSlot .Stack root).set_live false]) after addr bytes accesses length
  simp only [List.length_append, List.length_singleton, memory, List.append_assoc,
    List.cons_append, List.nil_append] at deallocated
  simp only [MRf.StackFrame.storage_dead, returnFrame, MR_StackFrame.set_locals,
    entry, SMap.index_at, SMap.get, SMap.getL, MR_LocalName.beq, SInt.beq,
    decide_true, decide_false, SOption.unwrap, SOut.bind_ok', layout_u64,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align, SMap.remove, SMap.removeL,
    deadRootMemory]
  rw [deallocated]
  rfl

theorem pop_single (fuel : Nat) (base : MR_Machine) (frame : MR_StackFrame)
    (mem : MR_ConcurrentMemory) :
    MRf.Machine.mutate_cur_stack MR_StackFrame Unit (fuel + 1) (single base [frame] mem)
      (fun stack (_ : Unit) => match SList.pop stack with
        | (popped, rest) => (SOption.unwrap popped).bind (fun frame => .ok (frame, rest, ()))) () =
      .ok (frame, single base [] mem, ()) := by
  simp [MRf.Machine.mutate_cur_stack, single, SList.mutateAtS, SList.mutateAtNat,
    SList.pop, SList.last, SList.dropLast, SOption.unwrap, SOut.bind_ok',
    MR_Thread.set_stack, MR_Machine.set_threads]

theorem root_single_mem (base : MR_Machine) (stack : List MR_StackFrame) (mem : MR_ConcurrentMemory) :
    (single base stack mem).mem = mem := rfl
theorem root_single_set_mem (base : MR_Machine) (stack : List MR_StackFrame)
    (first last : MR_ConcurrentMemory) :
    (single base stack first).set_mem last = single base stack last := rfl

theorem retire_root_first (fuel input : Nat) (base : MR_Machine)
    (before after : List MR_Allocation) (root : Int) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) :
    retireOne (fuel + 10)
      (returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr)),
        single base [] (rootMemory before after root addr bytes accesses)) =
      .ok (.next
        ((returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))).set_locals
          [(⟨1⟩, ptr (before.length + 1) (Int.ofNat addr))],
          single base [] (deadRootMemory before after root addr bytes accesses))) := by
  simp only [retireOne, root_single_mem]
  change (MRf.StackFrame.storage_dead (fuel + 10)
    (returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr)))
    (rootMemory before after root addr bytes accesses) ⟨0⟩).bind _ = _
  rw [storage_dead_root]
  rfl

theorem retire_root_second (fuel input : Nat) (base : MR_Machine)
    (before after : List MR_Allocation) (root : Int) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) (length : bytes.length = 8) :
    retireOne (fuel + 10)
      ((returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))).set_locals
        [(⟨1⟩, ptr (before.length + 1) (Int.ofNat addr))],
        single base [] (deadRootMemory before after root addr bytes accesses)) =
      .ok (.next
        ((returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))).set_locals [],
          single base [] (retiredRootMemory before after root addr bytes accesses))) := by
  simp only [retireOne, root_single_mem]
  change (MRf.StackFrame.storage_dead (fuel + 10)
    ((returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))).set_locals
      [(⟨1⟩, ptr (before.length + 1) (Int.ofNat addr))])
    (deadRootMemory before after root addr bytes accesses) ⟨1⟩).bind _ = _
  rw [storage_dead_result fuel input before after root addr bytes accesses length]
  rfl

theorem retire_root_loop (fuel spare input : Nat) (base : MR_Machine)
    (before after : List MR_Allocation) (root : Int) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) (length : bytes.length = 8) :
    SLoop.whileS (spare + 3)
      (returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr)),
        single base [] (rootMemory before after root addr bytes accesses)) (retireOne (fuel + 10)) =
      .ok (.brk
        ((returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))).set_locals [],
          single base [] (retiredRootMemory before after root addr bytes accesses))) := by
  rw [SLoop.whileS, retire_root_first]
  simp only [SOut.bind_ok']
  rw [SLoop.whileS, retire_root_second fuel input base before after root addr bytes accesses length]
  simp only [SOut.bind_ok']
  rw [SLoop.whileS]
  rfl

theorem root_return_type (input : Nat) (root result : MR_ThinPointer) :
    SMap.index_at MR_LocalName.beq (returnFrame input root result).func.locals
      (returnFrame input root result).func.ret = .ok unitTy := rfl
theorem root_return_pointer (input : Nat) (root result : MR_ThinPointer) :
    SMap.index_at MR_LocalName.beq (returnFrame input root result).locals
      (returnFrame input root result).func.ret = .ok root := rfl

/-- The frozen Returning entry has a real UB endpoint. The exact root/result
    allocations are retired, its stack is popped, and the actual model then
    refuses return from thread0. Nothing is labelled successful termination. -/
theorem root_return_ub (fuel input : Nat) (base : MR_Machine)
    (before after : List MR_Allocation) (root : Int) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) (length : bytes.length = 8) :
    MRf.Machine.eval_terminator (fuel + 30)
      (single base [returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))]
        (rootMemory before after root addr bytes accesses)) .Return =
      .ok (.err (.Ub "the start function must not return"),
        single base [] (retiredRootMemory before after root addr bytes
          (accesses ++ [⟨.Load, .None, root, 0⟩]))) := by
  have loaded := typed_load_unit (fuel + 17) before.length root
    (single base [] (rootMemory before after root addr bytes accesses))
  simp only [root_single_mem, root_single_set_mem] at loaded
  have retired := retire_root_loop (fuel + 19) (fuel + 26) input base before after root addr bytes
    (accesses ++ [⟨.Load, .None, root, 0⟩]) length
  unfold retireOne at retired
  simp only [Nat.add_assoc] at loaded retired
  simp only [MRf.Machine.eval_terminator]
  rw [pop_single (fuel + 28)]
  simp only [SOut.bind_ok']
  rw [root_return_type]
  simp only [SOut.bind_ok']
  rw [MiniRustU64Program.unit_layout (fuel + 25)]
  simp only [SOut.bind_ok', MRf.LayoutStrategy.expect_align]
  rw [root_return_pointer]
  simp only [SOut.bind_ok']
  rw [loaded]
  simp only [SOut.bind_ok']
  conv =>
    lhs
    arg 1
    tactic => exact retired
  simp only [SOut.bind_ok', MRf.ConcurrentMemory.end_call, MRf.BasicMemory.Memory.end_call,
    MR_ConcurrentMemory.set_memory, root_single_set_mem]
  rw [start_return_refused (fuel + 28)]
  rfl

theorem terminator_step_shape
    (evalStatement : Nat → MR_Machine → MR_Statement →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (evalTerminator : Nat → MR_Machine → MR_Terminator →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (fuel : Nat) (base : MR_Machine) (frame : MR_StackFrame) (mem : MR_ConcurrentMemory)
    (block : MR_BasicBlock)
    (blockLaw : SMap.index_at MR_BbName.beq frame.func.blocks frame.next_block = .ok block)
    (pcLaw : frame.next_stmt = SList.len block.statements) :
    stepWith evalStatement evalTerminator (fuel + 50) (single base [frame] mem) =
      oneThreadRun ((evalTerminator (fuel + 49) (single base [frame] (mem.set_accesses [])) block.terminator).bind
        (raceAfterTerm (fuel + 49) (SSet.insert SInt.beq base.synchronized_threads 0, mem.accesses))) := by
  simp only [stepWith]
  rw [enabled_single]
  simp only [SOut.bind_ok', SBool.not]
  rw [reset_single (fuel + 47)]
  simp only [SOut.bind_ok', SPick.choose, single_count]
  rw [show SInt.div_ceil 0 1 = SOut.ok 0 from rfl]
  simp only [SOut.bind_ok', pick_bind]
  unfold oneThreadRun
  congr 1
  funext index
  cases index with
  | succ index =>
    have hb : SInt.blt ((0 + Int.ofNat (index + 1)) * 1) 1 = false := by
      simp only [SInt.blt, Int.ofNat_eq_natCast, Int.zero_add, Int.mul_one, decide_eq_false_iff_not]
      omega
    rw [hb]
    rfl
  | zero =>
    rw [show (0 + Int.ofNat 0) * 1 = (0 : Int) from rfl]
    simp only [show SInt.blt 0 1 = true from rfl]
    rw [single_thread_at_zero]
    simp only [SOut.bind_ok', MR_ThreadState.beq]
    rw [single_set_zero, single_cur_frame (fuel + 46)]
    simp only [SOut.bind_ok']
    rw [blockLaw]
    simp only [SOut.bind_ok', pcLaw, SInt.beq, decide_true]
    apply congrArg (fun next => (evalTerminator (fuel + 49)
      (single base [frame] (mem.set_accesses [])) block.terminator).bind next)
    funext result
    rcases result with ⟨res, machine⟩
    cases res <;> rfl

theorem root_current_block (input : Nat) (root result : MR_ThinPointer) :
    SMap.index_at MR_BbName.beq (returnFrame input root result).func.blocks
      (returnFrame input root result).next_block = .ok returnBlock := rfl

theorem root_memory_clear (before after : List MR_Allocation) (root : Int) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) :
    (rootMemory before after root addr bytes accesses).set_accesses [] =
      rootMemory before after root addr bytes [] := rfl

/-- The real final Machine.step for the frozen Returning entry. It preserves
    the scheduler and actual UB; that error skips the final race-check branch
    exactly as the generated source specifies. Both caller allocations retire. -/
theorem root_return_step_ub (fuel input : Nat) (base : MR_Machine)
    (before after : List MR_Allocation) (root : Int) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) (length : bytes.length = 8) :
    MRf.Machine.step (fuel + 50)
      (single base [returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))]
        (rootMemory before after root addr bytes accesses)) =
      oneThreadRun (.ok (.err (.Ub "the start function must not return"),
        single base [] (retiredRootMemory before after root addr bytes [⟨.Load, .None, root, 0⟩]))) := by
  rw [actual_step, terminator_step_shape _ _ fuel base _ _ returnBlock
    (root_current_block input _ _) (by rfl), root_memory_clear]
  simp only [returnBlock]
  rw [root_return_ub (fuel + 19) input base before after root addr bytes [] length]
  rfl

/-- The actual callee endpoint is the real Returning-entry frame. All
    unrelated allocations, both retired callee cells and every access survive. -/
theorem resumed_root_exact (literal input : Nat) (first second root : Int)
    (before after : List MR_Allocation) (addr retAddr argAddr value : Nat) :
    MiniRustU64Run.exitState (initialized literal input first second root)
      (callerFrame input (ptr before.length root)
        (ptr (before.length + 1) (Int.ofNat addr)) 1) ⟨1⟩
      (before ++ [zeroSlot .Stack root]) after addr retAddr argAddr value input =
      single (initialized literal input first second root)
        [returnFrame input (ptr before.length root) (ptr (before.length + 1) (Int.ofNat addr))]
        (rootMemory before (after ++
          [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false,
           (slot (Int.ofNat argAddr) (u64bytes input)).set_live false])
          root addr (u64bytes value)
          [⟨.Load, .None, Int.ofNat retAddr, 8⟩, ⟨.Store, .None, Int.ofNat addr, 8⟩]) := by
  simp only [MiniRustU64Run.exitState, callerFrame, returnFrame,
    MR_StackFrame.set_next_block, MR_StackFrame.set_next_stmt,
    retiredCells, MiniRustU64Step.callerWorld, rootMemory,
    List.append_assoc, List.cons_append, List.nil_append]

/-- Four real Machine.step operations at one bounded fuel: Call, callee
    Assign, callee Return, then root Return. Actual errors propagate. -/
def callCalleeRootReturn (fuel literal input : Nat) (first second root : Int)
    (before after : List MR_Allocation) (addr : Nat) (accesses : List MR_Access) :=
  (callStepThenCallee fuel literal input first second root (ptr before.length root)
    (before ++ [zeroSlot .Stack root]) after addr accesses).bind
      (MiniRustU64Run.nextStep (fuel + 50))

/-- The complete six-choice tree. Rejected scheduler/allocation choices remain;
    every admitted leaf is the generated start-thread Return refusal, after
    exact root/result retirement and complete outside-world preservation. -/
def returningTree (literal input : Nat) (first second root : Int)
    (before after : List MR_Allocation) (addr : Nat) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  oneThreadRun (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (MiniRustU64Step.callerWorld (before ++ [zeroSlot .Stack root]) after addr uninit8))
    (fun retIndex => selectedChoice (Int.ofNat (modulus 64))
      (allocationAllowed (MiniRustU64Step.callerWorld (before ++ [zeroSlot .Stack root]) after addr uninit8 ++
        [slot (Int.ofNat (address retIndex)) uninit8])) (fun argIndex =>
        oneThreadRun (oneThreadRun (oneThreadRun (.ok
          (.err (.Ub "the start function must not return"),
            single (initialized literal input first second root) []
              (retiredRootMemory before (after ++
                [(slot (Int.ofNat (address retIndex)) (u64bytes ((input + literal) % modulus 64))).set_live false,
                 (slot (Int.ofNat (address argIndex)) (u64bytes input)).set_live false])
                root addr (u64bytes ((input + literal) % modulus 64)) [⟨.Load, .None, root, 0⟩]))))))))

theorem call_callee_root_return_exact (fuel literal input : Nat) (first second root : Int)
    (before after : List MR_Allocation) (addr : Nat) (accesses : List MR_Access)
    (aligned : addr % 8 = 0) (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    callCalleeRootReturn fuel literal input first second root before after addr accesses =
      returningTree literal input first second root before after addr := by
  unfold callCalleeRootReturn
  rw [call_step_and_callee_exact fuel literal input first second root (ptr before.length root)
    (before ++ [zeroSlot .Stack root]) after addr accesses aligned inputValid literalValid,
    one_thread_bind]
  unfold returningTree
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
  rw [resumed_root_exact, root_return_step_ub fuel input (initialized literal input first second root)
    before _ root addr _ _ (u64bytes_length _)]

#print axioms call_callee_root_return_exact
#print axioms typed_load_unit
#print axioms deallocate_zero
#print axioms storage_dead_result
#print axioms root_return_ub
#print axioms root_return_step_ub

end MiniRustU64ProgramReturn
