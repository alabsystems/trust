/- Exact generated frame creation for two runtime U64 arguments.
   This decomposition retains every allocator/error branch and both checked
   stores; it grants no Rust-source, physical ABI or compiler authority. -/
import MiniRustU64Call
import MiniRustWord64PairFunction
noncomputable section
namespace MiniRustWord64PairCall
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Call MiniRustU64Entry
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def pending (locals : List (MR_LocalName × MR_ThinPointer))
    (action : MR_StackPopAction) : MR_StackFrame :=
  ⟨MiniRustWord64PairFunction.function, locals, action, ⟨0⟩, 0, ()⟩

theorem dead_absent_return (fuel : Nat) (action : MR_StackPopAction)
    (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_dead (fuel + 6) (pending [] action) mem ⟨0⟩ =
      .ok (.ok (), pending [] action, mem) := by
  simp only [MRf.StackFrame.storage_dead, pending, MiniRustWord64PairFunction.function,
    SMap.index_at, SMap.get, SMap.getL, MR_LocalName.beq, SOption.unwrap, SOut.bind_ok', layout_u64,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align, SMap.remove, SMap.removeL]
  rfl

theorem continue_return (fuel : Nat) (action : MR_StackPopAction)
    (mem : MR_ConcurrentMemory)
    (allocate : MR_ConcurrentMemory → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory)) :
    liveContinuation (fuel + 4) allocate ⟨0⟩ (.ok (), pending [] action, mem) =
      (allocate mem 8 8).bind (finishLive (pending [] action) ⟨0⟩) := by
  simp only [liveContinuation, pending, MiniRustWord64PairFunction.function, SMap.index_at,
    SMap.get, SMap.getL, MR_LocalName.beq, SOption.unwrap, SOut.bind_ok', layout_u64,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align]

theorem live_return (fuel : Nat) (action : MR_StackPopAction)
    (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_live (fuel + 8) (pending [] action) mem ⟨0⟩ =
      (MRf.ConcurrentMemory.allocate (fuel + 7) mem .Stack 8 8).bind
        (finishLive (pending [] action) ⟨0⟩) := by
  rw [live_unfold, dead_absent_return (fuel + 1)]
  simp only [SOut.bind_ok']
  exact continue_return (fuel + 3) action mem _

theorem dead_absent_left (fuel : Nat) (action : MR_StackPopAction)
    (ret : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_dead (fuel + 6) (pending [(⟨0⟩, ret)] action) mem ⟨1⟩ =
      .ok (.ok (), pending [(⟨0⟩, ret)] action, mem) := by
  simp only [MRf.StackFrame.storage_dead, pending, MiniRustWord64PairFunction.function,
    SMap.index_at, SMap.get, SMap.getL, MR_LocalName.beq, SOption.unwrap, SOut.bind_ok', layout_u64,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align, SMap.remove, SMap.removeL]
  rfl

theorem continue_left (fuel : Nat) (action : MR_StackPopAction)
    (ret : MR_ThinPointer) (mem : MR_ConcurrentMemory)
    (allocate : MR_ConcurrentMemory → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory)) :
    liveContinuation (fuel + 4) allocate ⟨1⟩ (.ok (), pending [(⟨0⟩, ret)] action, mem) =
      (allocate mem 8 8).bind (finishLive (pending [(⟨0⟩, ret)] action) ⟨1⟩) := by
  simp only [liveContinuation, pending, MiniRustWord64PairFunction.function, SMap.index_at,
    SMap.get, SMap.getL, MR_LocalName.beq, SOption.unwrap, SOut.bind_ok', layout_u64,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align]

theorem live_left (fuel : Nat) (action : MR_StackPopAction)
    (ret : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_live (fuel + 8) (pending [(⟨0⟩, ret)] action) mem ⟨1⟩ =
      (MRf.ConcurrentMemory.allocate (fuel + 7) mem .Stack 8 8).bind
        (finishLive (pending [(⟨0⟩, ret)] action) ⟨1⟩) := by
  rw [live_unfold, dead_absent_left (fuel + 1)]
  simp only [SOut.bind_ok']
  exact continue_left (fuel + 3) action ret mem _

theorem dead_absent_right (fuel : Nat) (action : MR_StackPopAction)
    (ret left : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_dead (fuel + 6) (pending [(⟨0⟩, ret), (⟨1⟩, left)] action) mem ⟨2⟩ =
      .ok (.ok (), pending [(⟨0⟩, ret), (⟨1⟩, left)] action, mem) := by
  simp only [MRf.StackFrame.storage_dead, pending, MiniRustWord64PairFunction.function,
    SMap.index_at, SMap.get, SMap.getL, MR_LocalName.beq, SOption.unwrap, SOut.bind_ok', layout_u64,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align, SMap.remove, SMap.removeL]
  rfl

theorem continue_right (fuel : Nat) (action : MR_StackPopAction)
    (ret left : MR_ThinPointer) (mem : MR_ConcurrentMemory)
    (allocate : MR_ConcurrentMemory → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory)) :
    liveContinuation (fuel + 4) allocate ⟨2⟩ (.ok (), pending [(⟨0⟩, ret), (⟨1⟩, left)] action, mem) =
      (allocate mem 8 8).bind (finishLive (pending [(⟨0⟩, ret), (⟨1⟩, left)] action) ⟨2⟩) := by
  simp only [liveContinuation, pending, MiniRustWord64PairFunction.function, SMap.index_at,
    SMap.get, SMap.getL, MR_LocalName.beq, SOption.unwrap, SOut.bind_ok', layout_u64,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align]

theorem live_right (fuel : Nat) (action : MR_StackPopAction)
    (ret left : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_live (fuel + 8) (pending [(⟨0⟩, ret), (⟨1⟩, left)] action) mem ⟨2⟩ =
      (MRf.ConcurrentMemory.allocate (fuel + 7) mem .Stack 8 8).bind
        (finishLive (pending [(⟨0⟩, ret), (⟨1⟩, left)] action) ⟨2⟩) := by
  rw [live_unfold, dead_absent_right (fuel + 1)]
  simp only [SOut.bind_ok']
  exact continue_right (fuel + 3) action ret left mem _

def framePlanWith
    (allocate : Nat → MR_ConcurrentMemory → MR_AllocationKind → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory))
    (typedStore : Nat → MR_Machine → MR_ThinPointer → MR_Value → MR_Type → Int → MR_Atomicity →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (fuel : Nat) (action : MR_StackPopAction) (machine : MR_Machine)
    (leftValue rightValue : MR_Value) :
    SOut (SRes MR_TerminationInfo MR_StackFrame × MR_Machine) :=
  (allocate fuel machine.mem .Stack 8 8).bind (fun first =>
    match first with
    | (.err error, retMem) => .ok (.err error, machine.set_mem retMem)
    | (.ok ret, retMem) =>
      (allocate fuel retMem .Stack 8 8).bind (fun second =>
        match second with
        | (.err error, leftMem) => .ok (.err error, machine.set_mem leftMem)
        | (.ok left, leftMem) =>
          (allocate fuel leftMem .Stack 8 8).bind (fun third =>
            match third with
            | (.err error, rightMem) => .ok (.err error, machine.set_mem rightMem)
            | (.ok right, rightMem) =>
              (typedStore (fuel + 1) (machine.set_mem rightMem) left leftValue
                (.Int (mrIntTy false .u64)) 8 .None).bind (fun storedLeft =>
                match storedLeft with
                | (res, afterLeft) => (SRes.unwrap res).bind (fun _ =>
                  (typedStore (fuel + 1) afterLeft right rightValue
                    (.Int (mrIntTy false .u64)) 8 .None).bind (fun storedRight =>
                      match storedRight with
                      | (res, afterRight) => (SRes.unwrap res).bind (fun _ =>
                        .ok (.ok (MiniRustWord64PairFunction.frame ret left right action 0),
                          afterRight))))))))

/-- Equational expansion of the actual constructor. Primitive laws below
    are whole result equalities, not successful-operation assumptions. -/
theorem create_plan_generic
    (storageLive : Nat → MR_StackFrame → MR_ConcurrentMemory → MR_LocalName →
      SOut (SRes MR_TerminationInfo Unit × MR_StackFrame × MR_ConcurrentMemory))
    (typedStore : Nat → MR_Machine → MR_ThinPointer → MR_Value → MR_Type → Int → MR_Atomicity →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (allocate : Nat → MR_ConcurrentMemory → MR_AllocationKind → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory))
    (fuel : Nat) (action : MR_StackPopAction) (machine : MR_Machine)
    (leftValue rightValue : MR_Value)
    (retLaw : ∀ mem, storageLive (fuel + 9) (pending [] action) mem ⟨0⟩ =
      (allocate (fuel + 8) mem .Stack 8 8).bind (finishLive (pending [] action) ⟨0⟩))
    (leftLaw : ∀ ret mem, storageLive (fuel + 9) (pending [(⟨0⟩, ret)] action) mem ⟨1⟩ =
      (allocate (fuel + 8) mem .Stack 8 8).bind
        (finishLive (pending [(⟨0⟩, ret)] action) ⟨1⟩))
    (rightLaw : ∀ ret left mem,
      storageLive (fuel + 9) (pending [(⟨0⟩, ret), (⟨1⟩, left)] action) mem ⟨2⟩ =
      (allocate (fuel + 8) mem .Stack 8 8).bind
        (finishLive (pending [(⟨0⟩, ret), (⟨1⟩, left)] action) ⟨2⟩)) :
    createWith storageLive typedStore (fuel + 10) machine
      MiniRustWord64PairFunction.function action .Rust (.Int (mrIntTy false .u64))
      [(leftValue, .Int (mrIntTy false .u64)), (rightValue, .Int (mrIntTy false .u64))] =
      framePlanWith allocate typedStore (fuel + 8) action machine leftValue rightValue := by
  simp only [createWith, MRf.BasicMemory.Memory.new_call, SOut.bind_ok',
    MiniRustWord64PairFunction.function]
  have hl := retLaw machine.mem
  simp only [pending, MiniRustWord64PairFunction.function] at hl
  rw [hl]
  rw [bind_associative]
  unfold framePlanWith
  generalize ha : allocate (fuel + 8) machine.mem .Stack 8 8 = allocation
  apply congrArg (fun continuation => allocation.bind continuation)
  funext first
  rcases first with ⟨res, retMem⟩
  cases res with
  | err error => simp only [finishLive, SOut.bind_ok']
  | ok ret =>
    simp only [finishLive, SMap.insert, SOut.bind_ok', MR_StackFrame.set_locals, SLoop.forS,
      SMap.index_at, SMap.get, SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, SOption.unwrap,
      MR_CallingConvention.beq, SBool.not, SList.len, SList.lenNat, SList.zip, SList.push,
      SList.appendL, memory_after_set, set_memory_last]
    have hl := leftLaw ret retMem
    simp only [pending, MiniRustWord64PairFunction.function] at hl
    rw [hl]
    simp only [bind_associative]
    generalize hb : allocate (fuel + 8) retMem .Stack 8 8 = secondAllocation
    apply congrArg (fun continuation => secondAllocation.bind continuation)
    funext second
    rcases second with ⟨res, leftMem⟩
    cases res with
    | err error => simp only [finishLive, SOut.bind_ok']
    | ok left =>
      simp only [finishLive, SMap.insert, SOut.bind_ok', MR_StackFrame.set_locals, SMap.get,
        SMap.getL, MR_LocalName.beq, SList.push, SList.appendL, memory_after_set, set_memory_last]
      have hl := rightLaw ret left leftMem
      simp only [pending, MiniRustWord64PairFunction.function] at hl
      rw [hl]
      simp only [bind_associative]
      generalize hc : allocate (fuel + 8) leftMem .Stack 8 8 = thirdAllocation
      apply congrArg (fun continuation => thirdAllocation.bind continuation)
      funext third
      rcases third with ⟨res, rightMem⟩
      cases res with
      | err error => simp only [finishLive, SOut.bind_ok']
      | ok right =>
        simp only [finishLive, SMap.insert, MR_StackFrame.set_locals, SOut.bind_ok', SMap.get,
          SMap.getL, MR_LocalName.beq, abi_u64, layout_u64, MRf.LayoutStrategy.expect_align,
          SList.push, SList.appendL]
        simp only [bind_associative]
        generalize hd : typedStore (fuel + 9) (machine.set_mem rightMem) left leftValue
          (.Int (mrIntTy false .u64)) 8 .None = storedLeft
        apply congrArg (fun continuation => storedLeft.bind continuation)
        funext result
        rcases result with ⟨res, afterLeft⟩
        cases res with
        | err error => rfl
        | ok value =>
          simp only [SRes.unwrap, SOut.bind_ok', SMap.getL, MR_LocalName.beq]
          simp only [bind_associative]
          generalize he : typedStore (fuel + 9) afterLeft right rightValue
            (.Int (mrIntTy false .u64)) 8 .None = storedRight
          apply congrArg (fun continuation => storedRight.bind continuation)
          funext result
          rcases result with ⟨res, afterRight⟩
          cases res <;> rfl

def framePlan (fuel : Nat) (action : MR_StackPopAction)
    (machine : MR_Machine) (leftValue rightValue : MR_Value) :=
  framePlanWith MRf.ConcurrentMemory.allocate MRf.Machine.typed_store
    fuel action machine leftValue rightValue

/-- All three real allocations and both checked stores, including errors. -/
theorem create_frame_plan (fuel : Nat) (action : MR_StackPopAction)
    (machine : MR_Machine) (leftValue rightValue : MR_Value) :
    MRf.Machine.create_frame (fuel + 10) machine MiniRustWord64PairFunction.function action .Rust
      (.Int (mrIntTy false .u64))
      [(leftValue, .Int (mrIntTy false .u64)), (rightValue, .Int (mrIntTy false .u64))] =
      framePlan (fuel + 8) action machine leftValue rightValue := by
  rw [actual_create]
  apply create_plan_generic
  · intro mem
    exact live_return (fuel + 1) action mem
  · intro ret mem
    exact live_left (fuel + 1) action ret mem
  · intro ret left mem
    exact live_right (fuel + 1) action ret left mem

/-- Actual call continuation, including failures in the active-stack update. -/
theorem call_plan (fuel : Nat) (machine : MR_Machine) (leftValue rightValue : MR_Value)
    (ret : MR_ThinPointer) (next unwind : Option MR_BbName) :
    MRf.Machine.eval_call (fuel + 11) machine MiniRustWord64PairFunction.function .Rust
      [(leftValue, .Int (mrIntTy false .u64)), (rightValue, .Int (mrIntTy false .u64))]
      (place ret, .Int (mrIntTy false .u64)) next unwind =
      (framePlan (fuel + 8) (.BackToCaller next unwind ret) machine leftValue rightValue).bind
        (finishCall (fuel + 10)) := by
  rw [call_unfold, create_frame_plan]
  rfl

end MiniRustWord64PairCall

#print axioms MiniRustWord64PairCall.create_frame_plan
#print axioms MiniRustWord64PairCall.call_plan
