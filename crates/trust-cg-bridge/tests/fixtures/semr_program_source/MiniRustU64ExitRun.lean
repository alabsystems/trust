/- Entry execution in the actual generated MiniRust machine.
   Startup and function providers stay frozen. No successful operation,
   admitted allocation/scheduler branch or source/ABI/grade claim is assumed. -/
import MiniRustU64ExitStart
import MiniRustProgramStep

set_option autoImplicit false
noncomputable section
namespace MiniRustU64ExitRun
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return
  MiniRustU64Step MiniRustU64Entry MiniRustU64Call MiniRustU64AllocatedCall
  MiniRustU64ExitProgram MiniRustU64ExitStart MiniRustProgramStep
open MiniRustU64Program (unitTy callBlock callTerm)
open MiniRustU64ProgramRun
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Constructor-level law for the existing single enabled thread. The full
    callback result tree, including errors, is preserved. -/
theorem dead_absent_result (fuel input : Nat) (ret : MR_ThinPointer)
    (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_dead (fuel + 6) (entryFrame input ret) mem ⟨1⟩ =
      .ok (.ok (), entryFrame input ret, mem) := by
  simp only [MRf.StackFrame.storage_dead, entryFrame, exitEntry, SMap.index_at,
    SMap.get, SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false,
    SOption.unwrap, SOut.bind_ok', layout_u64, MRf.LayoutStrategy.expect_size,
    MRf.LayoutStrategy.expect_align, SMap.remove, SMap.removeL]
  rfl

theorem continue_result (fuel input : Nat) (ret : MR_ThinPointer)
    (mem : MR_ConcurrentMemory)
    (allocate : MR_ConcurrentMemory → Int → Int →
      SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory)) :
    liveContinuation (fuel + 4) allocate ⟨1⟩ (.ok (), entryFrame input ret, mem) =
      (allocate mem 8 8).bind (finishLive (entryFrame input ret) ⟨1⟩) := by
  simp only [liveContinuation, entryFrame, exitEntry, SMap.index_at, SMap.get,
    SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false, SOption.unwrap,
    SOut.bind_ok', layout_u64, MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align]

/-- The exitEntry's real local1 StorageLive operation is an actual guarded
    eight-byte allocation, with all errors and the complete world retained. -/
theorem live_result (fuel input : Nat) (ret : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    MRf.StackFrame.storage_live (fuel + 8) (entryFrame input ret) mem ⟨1⟩ =
      (MRf.ConcurrentMemory.allocate (fuel + 7) mem .Stack 8 8).bind
        (finishLive (entryFrame input ret) ⟨1⟩) := by
  rw [live_unfold, dead_absent_result (fuel + 1)]
  simp only [SOut.bind_ok']
  exact continue_result (fuel + 3) input ret mem _

def callerFrame (input : Nat) (ret result : MR_ThinPointer) (pc : Int) : MR_StackFrame :=
  ⟨exitEntry input, [(⟨0⟩, ret), (⟨1⟩, result)], .BottomOfStack, ⟨0⟩, pc, ()⟩

def finishResult (base : MR_Machine) (input : Nat) (ret : MR_ThinPointer)
    (result : SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  match result with
  | (.err error, mem) => .ok (.err error, single base [entryFrame input ret] mem)
  | (.ok result, mem) => .ok (.ok (), single base [callerFrame input ret result 0] mem)

/-- The real exitEntry statement, before the surrounding Machine.step increments
    its PC and performs its scheduler/race-tracking operations. -/
theorem eval_entry_storage (fuel input : Nat) (ret : MR_ThinPointer)
    (base : MR_Machine) (mem : MR_ConcurrentMemory) :
    MRf.Machine.eval_statement (fuel + 12) (single base [entryFrame input ret] mem)
      (.StorageLive ⟨1⟩) =
      (MRf.ConcurrentMemory.allocate (fuel + 10) mem .Stack 8 8).bind
        (finishResult base input ret) := by
  rw [storage_statement (fuel + 8), live_result (fuel + 3), bind_associative]
  apply congrArg (fun next =>
    (MRf.ConcurrentMemory.allocate (fuel + 10) mem .Stack 8 8).bind next)
  funext result
  rcases result with ⟨res, nextMem⟩
  cases res with
  | err error => rfl
  | ok ptr =>
    simp only [finishLive, entryFrame, SMap.insert, SMap.get, SMap.getL,
      SList.push, SList.appendL, MR_LocalName.beq, SInt.beq, decide_false,
      MR_StackFrame.set_locals, SOut.bind_ok', finishStorage, finishResult, callerFrame]

theorem entry_current_block (input : Nat) (ret : MR_ThinPointer) :
    SMap.index_at MR_BbName.beq (entryFrame input ret).func.blocks
      (entryFrame input ret).next_block = .ok (callBlock input) := rfl
theorem entry_pc (input : Nat) (ret : MR_ThinPointer) : (entryFrame input ret).next_stmt = 0 := rfl
theorem caller_pc (input : Nat) (ret result : MR_ThinPointer) (pc : Int) :
    (callerFrame input ret result pc).next_stmt = pc := rfl
theorem caller_set_pc (input : Nat) (ret result : MR_ThinPointer) (pc next : Int) :
    (callerFrame input ret result pc).set_next_stmt next = callerFrame input ret result next := rfl

def finishStorageStep (base : MR_Machine) (input : Nat) (ret : MR_ThinPointer)
    (result : SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  match result with
  | (.err error, mem) => .ok (.err error, single base [entryFrame input ret] mem)
  | (.ok ptr, mem) => .ok (.ok (), single base [callerFrame input ret ptr 1] mem)

/-- Exact scheduler/PC/race algebra. The primitive law concerns the complete
    result tree and is supplied by actual storage execution below. -/
theorem storage_step_generic
    (evalStatement : Nat → MR_Machine → MR_Statement →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (evalTerminator : Nat → MR_Machine → MR_Terminator →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (allocate : MR_ConcurrentMemory → SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory))
    (fuel input : Nat) (base : MR_Machine) (ret : MR_ThinPointer) (mem : MR_ConcurrentMemory)
    (statementLaw : ∀ mem,
      evalStatement (fuel + 49) (single base [entryFrame input ret] mem) (.StorageLive ⟨1⟩) =
        (allocate mem).bind (finishResult base input ret)) :
    stepWith evalStatement evalTerminator (fuel + 50) (single base [entryFrame input ret] mem) =
      oneThreadRun ((allocate (mem.set_accesses [])).bind (finishStorageStep base input ret)) := by
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
    rw [entry_current_block]
    simp only [SOut.bind_ok', entry_pc, callBlock]
    rw [show SList.len [MR_Statement.StorageLive ⟨1⟩] = 1 from rfl]
    simp only [show SInt.beq 0 1 = false from rfl]
    rw [show SList.index_at [MR_Statement.StorageLive ⟨1⟩] 0 = .ok (.StorageLive ⟨1⟩) from rfl]
    simp only [SOut.bind_ok']
    rw [statementLaw, bind_associative]
    apply congrArg (fun next => (allocate (mem.set_accesses [])).bind next)
    funext result
    rcases result with ⟨res, nextMem⟩
    cases res with
    | err error => rfl
    | ok ptr =>
      simp only [finishResult, SOut.bind_ok']
      rw [increment_single (fuel + 46)]
      simp only [SOut.bind_ok', caller_pc, caller_set_pc, single_active]
      rw [current_thread_race_check (fuel + 48)]
      rfl

/-- First REAL Machine.step from the exitEntry frame to its actual Call PC.
    Scheduler and allocation branches, including every reject/error, remain. -/
theorem entry_storage_step (fuel input : Nat) (base : MR_Machine)
    (ret : MR_ThinPointer) (mem : MR_ConcurrentMemory) :
    MRf.Machine.step (fuel + 50) (single base [entryFrame input ret] mem) =
      oneThreadRun ((MRf.ConcurrentMemory.allocate (fuel + 47) (mem.set_accesses []) .Stack 8 8).bind
        (finishStorageStep base input ret)) := by
  rw [actual_step]
  apply storage_step_generic _ _ (fun mem =>
    MRf.ConcurrentMemory.allocate (fuel + 47) mem .Stack 8 8) fuel input base ret mem
  intro mem
  exact eval_entry_storage (fuel + 37) input ret base mem

#print axioms eval_entry_storage
#print axioms entry_storage_step

end MiniRustU64ExitRun
