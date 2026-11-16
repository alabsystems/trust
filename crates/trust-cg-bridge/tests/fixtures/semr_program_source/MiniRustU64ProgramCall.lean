/- Actual entry Call evaluation, including its destination deinitialization,
   real function-pointer resolution, argument and full eval_call tree. -/
import MiniRustU64ProgramRun
import MiniRustProgramCall

set_option autoImplicit false
noncomputable section
namespace MiniRustU64ProgramCall
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return
  MiniRustU64Step MiniRustU64Entry MiniRustU64Call MiniRustU64AllocatedCall
  MiniRustU64Program MiniRustU64ProgramStart MiniRustU64ProgramRun MiniRustProgramCall MiniRustProgramStep
  MiniRustAllocate8Safety
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
  simp [callerFrame, entry, SMap.index_at, SMap.get, SMap.getL, MR_LocalName.beq,
    SInt.beq, SOption.unwrap, SOut.bind_ok', MRf.ThinPointer.widen, place]

theorem function_value (fuel literal input : Nat) (first second root : Int)
    (frame : MR_StackFrame) (mem : MR_ConcurrentMemory) :
    MRf.Machine.eval_value (fuel + 3)
      (single (initialized literal input first second root) [frame] mem)
      (.Constant (.FnPointer ⟨1⟩) (.Ptr .FnPtr)) =
      .ok (.ok (.Ptr ⟨ptr 1 second, none⟩, .Ptr .FnPtr),
        single (initialized literal input first second root) [frame] mem) := rfl

theorem lookup_single (fuel : Nat) (base : MR_Machine) (frame : MR_StackFrame)
    (mem : MR_ConcurrentMemory) (value : MR_Value) :
    MRf.Machine.fn_from_ptr fuel (single base [frame] mem) value =
      MRf.Machine.fn_from_ptr fuel base value := rfl

theorem function_lookup (fuel literal input : Nat) (first second root : Int)
    (frame : MR_StackFrame) (mem : MR_ConcurrentMemory) :
    MRf.Machine.fn_from_ptr (fuel + 2)
      (single (initialized literal input first second root) [frame] mem)
      (.Ptr ⟨ptr 1 second, none⟩) = .ok (.ok (function literal)) := by
  rw [lookup_single, initialized_function_lookup]

theorem argument_value (fuel input : Nat) (machine : MR_Machine) :
    MRf.Machine.eval_argument (fuel + 3) machine
      (.ByValue (.Constant (.Int (Int.ofNat input)) (.Int (mrIntTy false .u64)))) =
      .ok (.ok (.Int (Int.ofNat input), .Int (mrIntTy false .u64)), machine) := rfl

/-- The generated Call really deinitializes its result place before entry,
    including the actual Store access. This is not an assumed no-op. -/
theorem deinit_result (fuel : Nat) (before after : List MR_Allocation)
    (addr : Nat) (accesses : List MR_Access) (aligned : addr % 8 = 0) :
    MRf.ConcurrentMemory.deinit (fuel + 7) (memory before after addr uninit8 accesses)
      (ptr before.length (Int.ofNat addr)) 8 8 =
      .ok (.ok (), memory before after addr uninit8
        (accesses ++ [⟨.Store, .None, Int.ofNat addr, 8⟩])) := by
  simp only [MRf.ConcurrentMemory.deinit]
  rw [show SList.from_elem MR_AbstractByte.Uninit 8 = SOut.ok uninit8 from rfl]
  simp only [SOut.bind_ok']
  rw [concurrent_store_private_slot fuel before after addr uninit8 uninit8 accesses
    MiniRustU64AllocatedCall.uninit8_length MiniRustU64AllocatedCall.uninit8_length aligned]
  rfl

theorem prepare_result (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (before after : List MR_Allocation) (addr : Nat) (accesses : List MR_Access)
    (aligned : addr % 8 = 0) :
    MRf.Machine.prepare_for_inplace_passing (fuel + 8)
      (single base [caller] (memory before after addr uninit8 accesses))
      (place (ptr before.length (Int.ofNat addr))) (.Int (mrIntTy false .u64)) =
      .ok (.ok (), single base [caller] (memory before after addr uninit8
        (accesses ++ [⟨.Store, .None, Int.ofNat addr, 8⟩]))) := by
  simp only [MRf.Machine.prepare_for_inplace_passing, layout_u64,
    SOut.bind_ok', MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align]
  change ((MRf.ConcurrentMemory.deinit (fuel + 7)
    (memory before after addr uninit8 accesses) (ptr before.length (Int.ofNat addr)) 8 8).bind _) = _
  rw [deinit_result fuel before after addr accesses aligned]
  rfl

def callingState (literal input : Nat) (first second root : Int) (ret : MR_ThinPointer)
    (before after : List MR_Allocation) (addr : Nat) (accesses : List MR_Access) : MR_Machine :=
  single (initialized literal input first second root)
    [callerFrame input ret (ptr before.length (Int.ofNat addr)) 1]
    (memory before after addr uninit8 accesses)

/-- Algebra for the original Call constructor. Each primitive equality is
    independently derived from actual source operations at the final use. -/
theorem call_generic
    (evalPlace : Nat → MR_Machine → MR_PlaceExpr →
      SOut (SRes MR_TerminationInfo (MR_Place × MR_Type) × MR_Machine))
    (prepare : Nat → MR_Machine → MR_Place → MR_Type →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (evalValue : Nat → MR_Machine → MR_ValueExpr →
      SOut (SRes MR_TerminationInfo (MR_Value × MR_Type) × MR_Machine))
    (lookup : Nat → MR_Machine → MR_Value → SOut (SRes MR_TerminationInfo MR_Function))
    (evalArgument : Nat → MR_Machine → MR_ArgumentExpr →
      SOut (SRes MR_TerminationInfo (MR_Value × MR_Type) × MR_Machine))
    (evalCall : Nat → MR_Machine → MR_Function → MR_CallingConvention →
      List (MR_Value × MR_Type) → (MR_Place × MR_Type) → Option MR_BbName → Option MR_BbName →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (fuel literal input : Nat) (second : Int) (machine prepared : MR_Machine) (result : MR_ThinPointer)
    (placeLaw : evalPlace (fuel + 19) machine (.Local ⟨1⟩) =
      .ok (.ok (place result, .Int (mrIntTy false .u64)), machine))
    (prepareLaw : prepare (fuel + 19) machine (place result) (.Int (mrIntTy false .u64)) =
      .ok (.ok (), prepared))
    (valueLaw : evalValue (fuel + 19) prepared (.Constant (.FnPointer ⟨1⟩) (.Ptr .FnPtr)) =
      .ok (.ok (.Ptr ⟨ptr 1 second, none⟩, .Ptr .FnPtr), prepared))
    (lookupLaw : lookup (fuel + 19) prepared (.Ptr ⟨ptr 1 second, none⟩) =
      .ok (.ok (function literal)))
    (argumentLaw : evalArgument (fuel + 19) prepared
      (.ByValue (.Constant (.Int (Int.ofNat input)) (.Int (mrIntTy false .u64)))) =
      .ok (.ok (.Int (Int.ofNat input), .Int (mrIntTy false .u64)), prepared)) :
    callWith evalPlace prepare evalValue lookup evalArgument evalCall (fuel + 20) machine
      (.Constant (.FnPointer ⟨1⟩) (.Ptr .FnPtr)) .Rust
      [.ByValue (.Constant (.Int (Int.ofNat input)) (.Int (mrIntTy false .u64)))]
      (.Local ⟨1⟩) (some ⟨1⟩) none =
      evalCall (fuel + 19) prepared (function literal) .Rust
        [(.Int (Int.ofNat input), .Int (mrIntTy false .u64))]
        (place result, .Int (mrIntTy false .u64)) (some ⟨1⟩) none := by
  simp only [callWith, placeLaw, prepareLaw, valueLaw, lookupLaw,
    argumentLaw, SOut.bind_ok', SList.tryMapResS]
  change (evalCall (fuel + 19) prepared (function literal) .Rust
    [(.Int (Int.ofNat input), .Int (mrIntTy false .u64))]
    (place result, .Int (mrIntTy false .u64)) (some ⟨1⟩) none).bind SOut.ok = _
  exact bind_return _

attribute [local irreducible] callWith MRf.Machine.eval_call

/-- Actual Call terminator → real existing eval_call, with exact callee,
    argument, result destination and next block. The deinit Store is retained.
    There is no successful Call, frame, run or model correspondence premise. -/
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

def callThenCallee (fuel literal input : Nat) (first second root : Int)
    (ret : MR_ThinPointer) (before after : List MR_Allocation) (addr : Nat)
    (accesses : List MR_Access) : SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  (MRf.Machine.eval_terminator (fuel + 22)
    (callingState literal input first second root ret before after addr accesses) (callTerm input)).bind
      (MiniRustU64Correspondence.afterEntry (fuel + 50))

/-- The actual entry Call followed by the existing TWO actual callee
    Machine.step operations. Both allocator and callee scheduler choices,
    caller resumption, full-width result and private retirement stay exact. -/
theorem call_and_callee_exact (fuel literal input : Nat) (first second root : Int)
    (ret : MR_ThinPointer) (before after : List MR_Allocation) (addr : Nat)
    (accesses : List MR_Access) (aligned : addr % 8 = 0)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    callThenCallee fuel literal input first second root ret before after addr accesses =
      MiniRustU64Correspondence.fullTree literal input (initialized literal input first second root)
        (callerFrame input ret (ptr before.length (Int.ofNat addr)) 1) ⟨1⟩
        before after addr uninit8 := by
  unfold callThenCallee
  rw [entry_call (fuel + 2) literal input first second root ret before after addr accesses aligned]
  change MiniRustU64Correspondence.enterAndRun fuel literal input
    (initialized literal input first second root)
    (callerFrame input ret (ptr before.length (Int.ofNat addr)) 1) ⟨1⟩
    before after addr uninit8 (accesses ++ [⟨.Store, .None, Int.ofNat addr, 8⟩]) = _
  exact MiniRustU64Correspondence.full_tree_exact fuel literal input
    (initialized literal input first second root)
    (callerFrame input ret (ptr before.length (Int.ofNat addr)) 1) ⟨1⟩
    before after addr uninit8 _ MiniRustU64AllocatedCall.uninit8_length aligned inputValid literalValid

def raceAfterTerm (fuel : Nat) (old : List Int × List MR_Access)
    (result : SRes MR_TerminationInfo Unit × MR_Machine) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  match result with
  | (.err error, machine) => .ok (.err error, machine)
  | (.ok _, machine) =>
      (MRf.ConcurrentMemory.check_data_races fuel machine.mem machine.active_thread old).bind
        (fun checked => match checked with
          | .ok _ => .ok (.ok (), machine)
          | .err error => .ok (.err error, machine))

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
    rw [caller_current_block]
    simp only [SOut.bind_ok', caller_pc, callBlock]
    rw [show SList.len [MR_Statement.StorageLive ⟨1⟩] = 1 from rfl]
    simp only [show SInt.beq 1 1 = true from rfl]
    apply congrArg (fun next => (evalTerminator (fuel + 49)
      (single base [callerFrame input ret result 1] (mem.set_accesses [])) (callTerm input)).bind next)
    funext output
    rcases output with ⟨res, machine⟩
    cases res <;> rfl

theorem race_after_active_call (fuel : Nat) (base : MR_Machine)
    (caller callee : MR_StackFrame) (mem : MR_ConcurrentMemory) (accesses : List MR_Access) :
    raceAfterTerm (fuel + 1) (SSet.insert SInt.beq base.synchronized_threads 0, accesses)
      (.ok (), active base caller callee mem) = .ok (.ok (), active base caller callee mem) := by
  unfold raceAfterTerm
  change (MRf.ConcurrentMemory.check_data_races (fuel + 1) mem 0
    (SSet.insert SInt.beq base.synchronized_threads 0, accesses)).bind _ = _
  rw [current_thread_race_check]
  rfl

theorem race_after_call_tree (fuel literal input : Nat) (world : List MR_Allocation)
    (accesses oldAccesses : List MR_Access) (action : MR_StackPopAction)
    (base : MR_Machine) (caller : MR_StackFrame) :
    (callTree world accesses literal input action base caller).bind
      (raceAfterTerm (fuel + 1) (SSet.insert SInt.beq base.synchronized_threads 0, oldAccesses)) =
      callTree world accesses literal input action base caller := by
  unfold callTree
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64)) (allocationAllowed world))
  funext retIndex
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (world ++ [slot (Int.ofNat (address retIndex)) uninit8])))
  funext argIndex
  simp only [SOut.bind_ok', race_after_active_call]

theorem memory_clear (before after : List MR_Allocation) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) :
    (memory before after addr bytes accesses).set_accesses [] = memory before after addr bytes [] := rfl

/-- The complete actual Call Machine.step, including scheduler, destination
    Store, both allocations, argument initialization, stack push and real race
    check. No successful-call or admitted scheduler/allocation premise. -/
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

theorem start_return_refused (fuel : Nat) (base : MR_Machine) (mem : MR_ConcurrentMemory) :
    MRf.Machine.terminate_active_thread (fuel + 1) (single base [] mem) =
      .ok (.err (.Ub "the start function must not return"), single base [] mem) := rfl

theorem one_thread_bind {α β : Type} (out : SOut α) (next : α → SOut β) :
    (oneThreadRun out).bind next = oneThreadRun (out.bind next) := by
  apply congrArg SOut.pick
  funext index
  cases index <;> rfl

def callStepThenCallee (fuel literal input : Nat) (first second root : Int)
    (ret : MR_ThinPointer) (before after : List MR_Allocation) (addr : Nat)
    (accesses : List MR_Access) : SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  (MRf.Machine.step (fuel + 50)
    (callingState literal input first second root ret before after addr accesses)).bind
      (MiniRustU64Correspondence.afterEntry (fuel + 50))

/-- THREE actual Machine.step operations at the same bounded fuel: the entry
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

#print axioms prepare_result
#print axioms entry_call
#print axioms call_and_callee_exact
#print axioms entry_call_step
#print axioms call_step_and_callee_exact

end MiniRustU64ProgramCall
