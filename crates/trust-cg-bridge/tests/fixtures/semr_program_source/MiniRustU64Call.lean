/- Actual frame creation and call boundary for the existing MiniRust model.
   No compiler license, source elaboration, physical ABI or successful-run premise. -/
import MiniRustU64Entry
noncomputable section
namespace MiniRustU64Call
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def pending (literal : Nat) (locals : List (MR_LocalName × MR_ThinPointer))
    (action : MR_StackPopAction) : MR_StackFrame :=
  ⟨function literal, locals, action, ⟨0⟩, 0, ()⟩

theorem dead_absent_return (fuel literal : Nat) (action : MR_StackPopAction)
    (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_dead (fuel + 6) (pending literal [] action) mem ⟨0⟩ =
      .ok (.ok (), pending literal [] action, mem) := by
  simp only [MRf.StackFrame.storage_dead, pending, function, SMap.index_at,
    SMap.get, SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false,
    SOption.unwrap, SOut.bind_ok', layout_u64, MRf.LayoutStrategy.expect_size,
    MRf.LayoutStrategy.expect_align, SMap.remove, SMap.removeL]
  rfl

theorem dead_absent_argument (fuel literal : Nat) (action : MR_StackPopAction)
    (ret : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_dead (fuel + 6) (pending literal [(⟨0⟩, ret)] action) mem ⟨1⟩ =
      .ok (.ok (), pending literal [(⟨0⟩, ret)] action, mem) := by
  simp only [MRf.StackFrame.storage_dead, pending, function, SMap.index_at,
    SMap.get, SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false,
    SOption.unwrap, SOut.bind_ok', layout_u64, MRf.LayoutStrategy.expect_size,
    MRf.LayoutStrategy.expect_align, SMap.remove, SMap.removeL]
  rfl

def finishLive (frame : MR_StackFrame) (localName : MR_LocalName)
    (result : SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory) :
    SOut (SRes MR_TerminationInfo Unit × MR_StackFrame × MR_ConcurrentMemory) :=
  match result with
  | (res, mem) => match res with
    | .ok ptr => match SMap.insert MR_LocalName.beq frame.locals localName ptr with
      | (_, locals) => .ok (.ok (), frame.set_locals locals, mem)
    | .err error => .ok (.err error, frame, mem)

/-- The original continuation after StorageDead, parameterized only to keep
    allocator implementation expansion out of the proof term. Equality below
    checks the instantiation against the real generated operation. -/
def liveContinuation (fuel : Nat)
    (allocate : MR_ConcurrentMemory → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory))
    (localName : MR_LocalName)
    (result : SRes MR_TerminationInfo Unit × MR_StackFrame × MR_ConcurrentMemory) :
    SOut (SRes MR_TerminationInfo Unit × MR_StackFrame × MR_ConcurrentMemory) :=
  match result with
  | (res, frame, mem) => match res with
    | .err error => .ok (.err error, frame, mem)
    | .ok _ => (SMap.index_at MR_LocalName.beq frame.func.locals localName).bind (fun ty =>
      (MRf.Type.layout fuel ty).bind (fun layout =>
        (MRf.LayoutStrategy.expect_size fuel layout "WF ensures all locals are sized").bind
          (fun size => (SMap.index_at MR_LocalName.beq frame.func.locals localName).bind
            (fun ty => (MRf.Type.layout fuel ty).bind (fun layout =>
              (MRf.LayoutStrategy.expect_align fuel layout "WF ensures all locals are sized").bind
                (fun align => (allocate mem size align).bind (finishLive frame localName)))))))

theorem live_unfold (fuel : Nat) (frame : MR_StackFrame) (mem : MR_ConcurrentMemory)
    (localName : MR_LocalName) :
    MRf.StackFrame.storage_live (fuel + 1) frame mem localName =
      (MRf.StackFrame.storage_dead fuel frame mem localName).bind
        (liveContinuation fuel (fun mem size align =>
          MRf.ConcurrentMemory.allocate fuel mem .Stack size align) localName) := by
  simp only [MRf.StackFrame.storage_live]
  apply congrArg (fun continuation =>
    (MRf.StackFrame.storage_dead fuel frame mem localName).bind continuation)
  funext result
  rcases result with ⟨res, nextFrame, nextMem⟩
  cases res <;> simp only [liveContinuation, finishLive]
  all_goals rfl

theorem continue_return (fuel literal : Nat) (action : MR_StackPopAction)
    (mem : MR_ConcurrentMemory)
    (allocate : MR_ConcurrentMemory → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory)) :
    liveContinuation (fuel + 4) allocate ⟨0⟩ (.ok (), pending literal [] action, mem) =
      (allocate mem 8 8).bind (finishLive (pending literal [] action) ⟨0⟩) := by
  simp only [liveContinuation, pending, function, SMap.index_at, SMap.get,
    SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false, SOption.unwrap,
    SOut.bind_ok', layout_u64, MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align]

theorem continue_argument (fuel literal : Nat) (action : MR_StackPopAction)
    (ret : MR_ThinPointer) (mem : MR_ConcurrentMemory)
    (allocate : MR_ConcurrentMemory → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory)) :
    liveContinuation (fuel + 4) allocate ⟨1⟩ (.ok (), pending literal [(⟨0⟩, ret)] action, mem) =
      (allocate mem 8 8).bind (finishLive (pending literal [(⟨0⟩, ret)] action) ⟨1⟩) := by
  simp only [liveContinuation, pending, function, SMap.index_at, SMap.get,
    SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false, SOption.unwrap,
    SOut.bind_ok', layout_u64, MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align]

/-- Every allocator choice and error remains in the actual result tree. -/
theorem live_return (fuel literal : Nat) (action : MR_StackPopAction)
    (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_live (fuel + 8) (pending literal [] action) mem ⟨0⟩ =
      (MRf.ConcurrentMemory.allocate (fuel + 7) mem .Stack 8 8).bind
        (finishLive (pending literal [] action) ⟨0⟩) := by
  rw [live_unfold, dead_absent_return (fuel + 1)]
  simp only [SOut.bind_ok']
  exact continue_return (fuel + 3) literal action mem _

theorem live_argument (fuel literal : Nat) (action : MR_StackPopAction)
    (ret : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_live (fuel + 8) (pending literal [(⟨0⟩, ret)] action) mem ⟨1⟩ =
      (MRf.ConcurrentMemory.allocate (fuel + 7) mem .Stack 8 8).bind
        (finishLive (pending literal [(⟨0⟩, ret)] action) ⟨1⟩) := by
  rw [live_unfold, dead_absent_argument (fuel + 1)]
  simp only [SOut.bind_ok']
  exact continue_argument (fuel + 3) literal action ret mem _

theorem function_start (literal : Nat) : (function literal).start = ⟨0⟩ := rfl
theorem function_return (literal : Nat) : (function literal).ret = ⟨0⟩ := rfl
theorem function_arguments (literal : Nat) : (function literal).args = [⟨1⟩] := rfl
theorem function_convention (literal : Nat) : (function literal).calling_convention = .Rust := rfl
theorem function_local_types (literal : Nat) : (function literal).locals =
    [(⟨0⟩, .Int (mrIntTy false .u64)), (⟨1⟩, .Int (mrIntTy false .u64))] := rfl

theorem abi_u64 (fuel : Nat) :
    MRf.fn.check_abi_compatibility (fuel + 1)
      (.Int (mrIntTy false .u64)) (.Int (mrIntTy false .u64)) = .ok true := by
  change MRf.fn.check_abi_compatibility_open (MR_rec_106.tie fuel) (fuel + 1)
    (.Int (mrIntTy false .u64)) (.Int (mrIntTy false .u64)) = .ok true
  simp only [MRf.fn.check_abi_compatibility_open, MR_IntType.beq, mrIntTy,
    sgnOf, IntTy.bytes, SInt.beq, MR_Signedness.beq, Bool.and_self, decide_true]
  rfl

theorem memory_after_set (machine : MR_Machine) (mem : MR_ConcurrentMemory) :
    (machine.set_mem mem).mem = mem := by cases machine; rfl

theorem set_memory_last (machine : MR_Machine) (first last : MR_ConcurrentMemory) :
    (machine.set_mem first).set_mem last = machine.set_mem last := by cases machine; rfl

/-- Mechanical abstraction of ONLY two primitive constants in the exact
    generated create_frame body. The equality below checks the original
    instantiation definitionally; this supplies no new model axiom. -/
def createWith
    (storageLive : Nat → MR_StackFrame → MR_ConcurrentMemory → MR_LocalName →
      SOut (SRes MR_TerminationInfo Unit × MR_StackFrame × MR_ConcurrentMemory))
    (typedStore : Nat → MR_Machine → MR_ThinPointer → MR_Value → MR_Type → Int → MR_Atomicity →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (fuel : Nat) (self_6689 : MR_Machine) (func_6690 : MR_Function) (stack_pop_action_6691 : MR_StackPopAction) (caller_conv_6692 : MR_CallingConvention) (caller_ret_ty_6693 : MR_Type) (caller_args_6694 : List (MR_Value × MR_Type)) : SOut (SRes MR_TerminationInfo MR_StackFrame × MR_Machine) :=
  match fuel with | 0 => SOut.fuel | fuel + 1 => SOut.bind (α := Unit) (β := (SRes MR_TerminationInfo MR_StackFrame × MR_Machine)) (MRf.BasicMemory.Memory.new_call fuel) (fun (r_6695 : Unit) => let frame_6696 : MR_StackFrame := (MR_StackFrame.mk func_6690 ([] : List (MR_LocalName × MR_ThinPointer)) stack_pop_action_6691 (MR_Function.start func_6690) (0 : Int) r_6695); SOut.bind (α := (SRes MR_TerminationInfo Unit × MR_StackFrame × MR_ConcurrentMemory)) (β := (SRes MR_TerminationInfo MR_StackFrame × MR_Machine)) (storageLive fuel frame_6696 (MR_Machine.mem self_6689) (MR_Function.ret func_6690)) (fun (p_6700 : SRes MR_TerminationInfo Unit × MR_StackFrame × MR_ConcurrentMemory) => match p_6700 with | (r_6697, r_6698, r_6699) => let frame_6701 : MR_StackFrame := r_6698; let self_6702 : MR_Machine := (MR_Machine.set_mem self_6689 r_6699); (match r_6697 with | SRes.ok ok_6703 => let rest_6760 : MR_StackFrame × MR_Machine → SOut (SRes MR_TerminationInfo MR_StackFrame × MR_Machine) := (fun (st_6758 : MR_StackFrame × MR_Machine) => match st_6758 with | (frame_6718, self_6719) => let jp_6720 : Unit → SOut (SRes MR_TerminationInfo MR_StackFrame × MR_Machine) := (fun (jv_6721 : Unit) => let jp_6724 : Unit → SOut (SRes MR_TerminationInfo MR_StackFrame × MR_Machine) := (fun (jv_6725 : Unit) => let jp_6726 : Unit → SOut (SRes MR_TerminationInfo MR_StackFrame × MR_Machine) := (fun (jv_6727 : Unit) => let rest_6755 : MR_StackFrame × MR_Machine → SOut (SRes MR_TerminationInfo MR_StackFrame × MR_Machine) := (fun (st_6753 : MR_StackFrame × MR_Machine) => match st_6753 with | (frame_6751, self_6752) => SOut.ok ((SRes.ok frame_6751 : SRes MR_TerminationInfo MR_StackFrame), self_6752)); SOut.bind (α := (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) (β := (SRes MR_TerminationInfo MR_StackFrame × MR_Machine)) (SLoop.forS (α := (MR_LocalName × MR_Value × MR_Type)) (σ := (MR_StackFrame × MR_Machine)) (ρ := (SRes MR_TerminationInfo MR_StackFrame × MR_Machine)) (SList.zip (MR_Function.args func_6690) caller_args_6694) (frame_6718, self_6719) (fun (item_6731 : MR_LocalName × MR_Value × MR_Type) (st_6728 : MR_StackFrame × MR_Machine) => match st_6728 with | (frame_6729, self_6730) => (match item_6731 with | (c_6732, c_6733) => (match c_6733 with | (c_6734, c_6735) => let jp_6738 : Unit → SOut (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine)) := (fun (jv_6739 : Unit) => SOut.bind (α := MR_LayoutStrategy) (β := (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) (MRf.Type.layout fuel c_6735) (fun (r_6740 : MR_LayoutStrategy) => SOut.bind (α := Int) (β := (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) (MRf.LayoutStrategy.expect_align fuel r_6740 "WF ensures function arguments are sized") (fun (r_6741 : Int) => SOut.bind (α := MR_ThinPointer) (β := (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) (SMap.index_at MR_LocalName.beq (MR_StackFrame.locals frame_6729) c_6732) (fun (v_6742 : MR_ThinPointer) => SOut.bind (α := (SRes MR_TerminationInfo Unit × MR_Machine)) (β := (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) (typedStore fuel self_6730 v_6742 c_6734 c_6735 r_6741 MR_Atomicity.None) (fun (p_6745 : SRes MR_TerminationInfo Unit × MR_Machine) => match p_6745 with | (r_6743, r_6744) => let self_6746 : MR_Machine := r_6744; SOut.bind (α := Unit) (β := (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) (SRes.unwrap r_6743) (fun (v_6747 : Unit) => SOut.ok (SCtl.next (frame_6729, self_6746) : (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))))))))); SOut.bind (α := MR_Type) (β := (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) (SMap.index_at MR_LocalName.beq (MR_Function.locals func_6690) c_6732) (fun (v_6748 : MR_Type) => SOut.bind (α := Bool) (β := (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) (MRf.fn.check_abi_compatibility fuel c_6735 v_6748) (fun (r_6749 : Bool) => (match (SBool.not r_6749) with | true => SOut.ok (SCtl.ret ((SRes.err (MR_TerminationInfo.Ub "call ABI violation: argument types are not compatible") : SRes MR_TerminationInfo MR_StackFrame), self_6730)) | false => jp_6738 ()))))))) (fun (ctl_6750 : (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) => match ctl_6750 with | SCtl.next st_6753 => rest_6755 st_6753 | SCtl.brk st_6753 => rest_6755 st_6753 | SCtl.ret ret_6754 => SOut.ok ret_6754)); (match (SBool.not (SInt.beq (SList.len (MR_Function.args func_6690)) (SList.len caller_args_6694))) with | true => SOut.ok ((SRes.err (MR_TerminationInfo.Ub "call ABI violation: number of arguments does not agree") : SRes MR_TerminationInfo MR_StackFrame), self_6719) | false => jp_6726 ())); SOut.bind (α := MR_Type) (β := (SRes MR_TerminationInfo MR_StackFrame × MR_Machine)) (SMap.index_at MR_LocalName.beq (MR_Function.locals func_6690) (MR_Function.ret func_6690)) (fun (v_6756 : MR_Type) => SOut.bind (α := Bool) (β := (SRes MR_TerminationInfo MR_StackFrame × MR_Machine)) (MRf.fn.check_abi_compatibility fuel caller_ret_ty_6693 v_6756) (fun (r_6757 : Bool) => (match (SBool.not r_6757) with | true => SOut.ok ((SRes.err (MR_TerminationInfo.Ub "call ABI violation: return types are not compatible") : SRes MR_TerminationInfo MR_StackFrame), self_6719) | false => jp_6724 ())))); (match (SBool.not (MR_CallingConvention.beq caller_conv_6692 (MR_Function.calling_convention func_6690))) with | true => SOut.ok ((SRes.err (MR_TerminationInfo.Ub "call ABI violation: calling conventions are not the same") : SRes MR_TerminationInfo MR_StackFrame), self_6719) | false => jp_6720 ())); SOut.bind (α := (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) (β := (SRes MR_TerminationInfo MR_StackFrame × MR_Machine)) (SLoop.forS (α := MR_LocalName) (σ := (MR_StackFrame × MR_Machine)) (ρ := (SRes MR_TerminationInfo MR_StackFrame × MR_Machine)) (MR_Function.args func_6690) (frame_6701, self_6702) (fun (item_6708 : MR_LocalName) (st_6705 : MR_StackFrame × MR_Machine) => match st_6705 with | (frame_6706, self_6707) => SOut.bind (α := (SRes MR_TerminationInfo Unit × MR_StackFrame × MR_ConcurrentMemory)) (β := (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) (storageLive fuel frame_6706 (MR_Machine.mem self_6707) item_6708) (fun (p_6712 : SRes MR_TerminationInfo Unit × MR_StackFrame × MR_ConcurrentMemory) => match p_6712 with | (r_6709, r_6710, r_6711) => let frame_6713 : MR_StackFrame := r_6710; let self_6714 : MR_Machine := (MR_Machine.set_mem self_6707 r_6711); (match r_6709 with | SRes.ok ok_6715 => SOut.ok (SCtl.next (frame_6713, self_6714) : (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) | SRes.err err_6716 => SOut.ok (SCtl.ret ((SRes.err err_6716 : SRes MR_TerminationInfo MR_StackFrame), self_6714)))))) (fun (ctl_6717 : (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo MR_StackFrame × MR_Machine))) => match ctl_6717 with | SCtl.next st_6758 => rest_6760 st_6758 | SCtl.brk st_6758 => rest_6760 st_6758 | SCtl.ret ret_6759 => SOut.ok ret_6759) | SRes.err err_6704 => SOut.ok ((SRes.err err_6704 : SRes MR_TerminationInfo MR_StackFrame), self_6702))))

theorem actual_create (fuel : Nat) (machine : MR_Machine) (func : MR_Function)
    (action : MR_StackPopAction) (cc : MR_CallingConvention) (ret : MR_Type)
    (args : List (MR_Value × MR_Type)) :
    MRf.Machine.create_frame fuel machine func action cc ret args =
      createWith MRf.StackFrame.storage_live MRf.Machine.typed_store
        fuel machine func action cc ret args := rfl

def framePlanWith
    (allocate : Nat → MR_ConcurrentMemory → MR_AllocationKind → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory))
    (typedStore : Nat → MR_Machine → MR_ThinPointer → MR_Value → MR_Type → Int → MR_Atomicity →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (fuel literal : Nat) (action : MR_StackPopAction)
    (machine : MR_Machine) (value : MR_Value) :
    SOut (SRes MR_TerminationInfo MR_StackFrame × MR_Machine) :=
  (allocate fuel machine.mem .Stack 8 8).bind (fun first =>
    match first with
    | (.err error, retMem) => .ok (.err error, machine.set_mem retMem)
    | (.ok ret, retMem) =>
      (allocate fuel retMem .Stack 8 8).bind (fun second =>
        match second with
        | (.err error, argMem) => .ok (.err error, machine.set_mem argMem)
        | (.ok arg, argMem) =>
          (typedStore (fuel + 1) (machine.set_mem argMem) arg value
            (.Int (mrIntTy false .u64)) 8 .None).bind (fun stored =>
              match stored with
              | (res, resultMachine) => (SRes.unwrap res).bind (fun _ =>
                .ok (.ok (frame literal ret arg action 0), resultMachine)))))

/-- Pure equational calculation over primitive operations. Its hypotheses are
    full primitive equalities, supplied by checked actual laws below; no
    successful allocation, call, or execution is postulated. -/
theorem create_plan_generic
    (storageLive : Nat → MR_StackFrame → MR_ConcurrentMemory → MR_LocalName →
      SOut (SRes MR_TerminationInfo Unit × MR_StackFrame × MR_ConcurrentMemory))
    (typedStore : Nat → MR_Machine → MR_ThinPointer → MR_Value → MR_Type → Int → MR_Atomicity →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (allocate : Nat → MR_ConcurrentMemory → MR_AllocationKind → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory))
    (fuel literal : Nat) (action : MR_StackPopAction) (machine : MR_Machine) (value : MR_Value)
    (retLaw : ∀ mem, storageLive (fuel + 9) (pending literal [] action) mem ⟨0⟩ =
      (allocate (fuel + 8) mem .Stack 8 8).bind (finishLive (pending literal [] action) ⟨0⟩))
    (argLaw : ∀ ret mem, storageLive (fuel + 9) (pending literal [(⟨0⟩, ret)] action) mem ⟨1⟩ =
      (allocate (fuel + 8) mem .Stack 8 8).bind (finishLive (pending literal [(⟨0⟩, ret)] action) ⟨1⟩)) :
    createWith storageLive typedStore (fuel + 10) machine (function literal) action .Rust
      (.Int (mrIntTy false .u64)) [(value, .Int (mrIntTy false .u64))] =
      framePlanWith allocate typedStore (fuel + 8) literal action machine value := by
  simp only [createWith, MRf.BasicMemory.Memory.new_call, SOut.bind_ok',
    function_start, function_return, function_arguments, function_convention, function_local_types]
  have hl := retLaw machine.mem
  simp only [pending, Nat.add_assoc] at hl
  rw [hl]
  rw [MiniRustU64Entry.bind_associative]
  unfold framePlanWith
  generalize ha : allocate (fuel + 8) machine.mem .Stack 8 8 = allocation
  apply congrArg (fun continuation => allocation.bind continuation)
  funext first
  rcases first with ⟨res, retMem⟩
  cases res with
  | err error => simp only [finishLive, SOut.bind_ok']
  | ok ret =>
    simp only [finishLive, SMap.insert, SOut.bind_ok',
      pending, function, MR_StackFrame.set_locals, SLoop.forS, SMap.index_at,
      SMap.get, SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false,
      SOption.unwrap, MR_CallingConvention.beq, SBool.not, SList.len, SList.lenNat,
      SList.zip, SList.push, SList.appendL, memory_after_set, set_memory_last]
    have hl := argLaw ret retMem
    simp only [pending, function, Nat.add_assoc] at hl
    rw [hl]
    simp only [MiniRustU64Entry.bind_associative]
    generalize hb : allocate (fuel + 8) retMem .Stack 8 8 = secondAllocation
    apply congrArg (fun continuation => secondAllocation.bind continuation)
    funext second
    rcases second with ⟨res, argMem⟩
    cases res with
    | err error => simp only [finishLive, SOut.bind_ok']
    | ok arg =>
      simp only [finishLive, SMap.insert, pending, function,
        MR_StackFrame.set_locals, SOut.bind_ok', SLoop.forS, SMap.index_at, SMap.get,
        SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false, SOption.unwrap,
        MR_CallingConvention.beq, SBool.not, SList.len, SList.lenNat, SList.zip,
        abi_u64, layout_u64, MRf.LayoutStrategy.expect_align, SList.push, SList.appendL,
        memory_after_set, set_memory_last]
      simp only [MiniRustU64Entry.bind_associative]
      generalize hc : typedStore (fuel + 9) (machine.set_mem argMem) arg value
        (.Int (mrIntTy false .u64)) 8 .None = stored
      apply congrArg (fun continuation => stored.bind continuation)
      funext result
      rcases result with ⟨res, resultMachine⟩
      cases res <;> rfl

def framePlan (fuel literal : Nat) (action : MR_StackPopAction)
    (machine : MR_Machine) (value : MR_Value) :=
  framePlanWith MRf.ConcurrentMemory.allocate MRf.Machine.typed_store
    fuel literal action machine value

/-- Exact actual construction, with every original allocator/error/store path. -/
theorem create_frame_plan (fuel literal : Nat) (action : MR_StackPopAction)
    (machine : MR_Machine) (value : MR_Value) :
    MRf.Machine.create_frame (fuel + 10) machine (function literal) action .Rust
      (.Int (mrIntTy false .u64)) [(value, .Int (mrIntTy false .u64))] =
      framePlan (fuel + 8) literal action machine value := by
  rw [actual_create]
  apply create_plan_generic
  · intro mem
    exact live_return (fuel + 1) literal action mem
  · intro ret mem
    exact live_argument (fuel + 1) literal action ret mem

/-- The original call continuation, including all real stack-mutation errors. -/
def finishCall (fuel : Nat)
    (result : SRes MR_TerminationInfo MR_StackFrame × MR_Machine) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  match result with
  | (.err error, machine) => .ok (.err error, machine)
  | (.ok callee, machine) =>
    (MRf.Machine.mutate_cur_stack Unit Unit fuel machine
      (fun stack (_ : Unit) => .ok ((), SList.push stack callee, ())) ()).bind
      (fun result => match result with | (_, machine, _) => .ok (.ok (), machine))

theorem call_unfold (fuel : Nat) (machine : MR_Machine) (callee : MR_Function)
    (cc : MR_CallingConvention) (args : List (MR_Value × MR_Type))
    (ret : MR_Place × MR_Type) (next unwind : Option MR_BbName) :
    MRf.Machine.eval_call (fuel + 1) machine callee cc args ret next unwind =
      (MRf.Machine.create_frame fuel machine callee
        (.BackToCaller next unwind ret.1.ptr.thin_pointer) cc ret.2 args).bind (finishCall fuel) := by
  rcases ret with ⟨returnPlace, returnType⟩
  simp only [MRf.Machine.eval_call]
  apply congrArg (fun continuation =>
    (MRf.Machine.create_frame fuel machine callee
      (.BackToCaller next unwind returnPlace.ptr.thin_pointer) cc returnType args).bind continuation)
  funext result
  rcases result with ⟨res, nextMachine⟩
  cases res <;> rfl

theorem call_plan (fuel literal : Nat) (machine : MR_Machine) (value : MR_Value)
    (ret : MR_ThinPointer) (next unwind : Option MR_BbName) :
    MRf.Machine.eval_call (fuel + 11) machine (function literal) .Rust
      [(value, .Int (mrIntTy false .u64))]
      (place ret, .Int (mrIntTy false .u64)) next unwind =
      (framePlan (fuel + 8) literal (.BackToCaller next unwind ret) machine value).bind
        (finishCall (fuel + 10)) := by
  rw [call_unfold, create_frame_plan]
  rfl

/-- Actual stack push on the same enabled thread, retaining all base fields. -/
theorem push_active (fuel : Nat) (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) :
    MRf.Machine.mutate_cur_stack Unit Unit (fuel + 1) (single base [caller] mem)
      (fun stack (_ : Unit) => .ok ((), SList.push stack callee, ())) () =
      .ok ((), active base caller callee mem, ()) := by
  simp [MRf.Machine.mutate_cur_stack, active, single, SList.mutateAtS, SList.mutateAtNat,
    SList.push, SList.appendL, SOut.bind_ok', MR_Thread.set_stack, MR_Machine.set_threads]

theorem finish_call_active (fuel : Nat) (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) :
    finishCall (fuel + 1) (.ok callee, single base [caller] mem) =
      .ok (.ok (), active base caller callee mem) := by
  simp only [finishCall, push_active, SOut.bind_ok']

end MiniRustU64Call
