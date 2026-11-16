/- The actual generated Return path and its complete caller-memory endpoint. -/
import MiniRustU64Execution
noncomputable section
namespace MiniRustU64Return
open SemR MiniRustU64Function MiniRustU64Execution
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact remaining generated Return operations after retirement. Errors are
    retained, not replaced by a success predicate or a presumed caller license. -/
def finishReturn (fuel : Nat) (machine : MR_Machine) (value : Nat)
    (next : MR_BbName) (target : MR_ThinPointer) : SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  SOut.bind (MRf.Machine.typed_store fuel machine target (.Int (Int.ofNat value))
      (.Int (mrIntTy false .u64)) 8 .None)
    (fun result => match result.fst with
      | .ok _ => SOut.bind (MRf.Machine.jump_to_block fuel result.snd next)
        (fun resumed => match resumed.fst with
          | .ok _ => SOut.ok (.ok (), resumed.snd)
          | .err error => SOut.ok (.err error, resumed.snd))
      | .err error => SOut.ok (.err error, result.snd))

private theorem single_set_mem (base : MR_Machine) (stack : List MR_StackFrame)
    (a b : MR_ConcurrentMemory) :
    (single base stack a).set_mem b = single base stack b := rfl

/-- Real Return: pop, load the callee result, retire BOTH actual local slots,
    end_call, then the original checked caller store and continuation jump.
    The remaining caller operations are preserved even for an invalid target. -/
theorem return_to_boundary (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (pc : Int) (next : MR_BbName) (target : MR_ThinPointer)
    (world : List MR_Allocation) (retAddr argAddr value n : Nat) (accesses : List MR_Access)
    (retAligned : retAddr % 8 = 0) (valid : value < modulus 64) :
    MRf.Machine.eval_terminator (fuel + 30)
      (active base caller
        (frame literal (ptr world.length (Int.ofNat retAddr))
          (ptr (world.length + 1) (Int.ofNat argAddr)) (.BackToCaller (some next) none target) pc)
        (cells world retAddr argAddr (u64bytes value) n accesses)) .Return =
    finishReturn (fuel + 29)
      (single base [caller]
        (retiredCells world retAddr argAddr value n
          (accesses ++ [⟨.Load, .None, Int.ofNat retAddr, 8⟩]))) value next target := by
  have ht := typed_load_u64 (fuel + 19)
    (single base [caller] (cells world retAddr argAddr (u64bytes value) n accesses))
    world [slot (Int.ofNat argAddr) (u64bytes n)] retAddr value accesses retAligned valid
  simp only [single_set_mem] at ht
  have ht' : MRf.Machine.typed_load (fuel + 29)
      (single base [caller] (cells world retAddr argAddr (u64bytes value) n accesses))
      (ptr world.length (Int.ofNat retAddr)) (.Int (mrIntTy false .u64)) 8 .None =
    SOut.ok (.ok (.Int (Int.ofNat value)),
      single base [caller] (cells world retAddr argAddr (u64bytes value) n
        (accesses ++ [⟨.Load, .None, Int.ofNat retAddr, 8⟩]))) := by
    simpa only [cells] using ht
  have hl := retire_loop (fuel + 19) (fuel + 26) base caller literal
    (.BackToCaller (some next) none target) pc world retAddr argAddr value n
    (accesses ++ [⟨.Load, .None, Int.ofNat retAddr, 8⟩])
  unfold retireOne at hl
  simp [Nat.add_assoc] at hl
  simp only [MRf.Machine.eval_terminator]
  rw [pop_active (fuel + 28)]
  simp only [SOut.bind_ok']
  rw [frame_return_type]
  simp only [SOut.bind_ok']
  rw [layout_u64 (fuel + 26)]
  simp only [SOut.bind_ok', MRf.LayoutStrategy.expect_align]
  rw [frame_return_pointer]
  simp only [SOut.bind_ok']
  rw [ht']
  simp only [SOut.bind_ok']
  simp only [Int.ofNat_eq_natCast]
  conv =>
    lhs
    arg 1
    tactic => exact hl
  simp only [SOut.bind_ok']
  simp only [MRf.ConcurrentMemory.end_call, MRf.BasicMemory.Memory.end_call,
    SOut.bind_ok', MR_ConcurrentMemory.set_memory]
  simp [MRf.Machine.active_thread, single, SList.index_at, SList.get, SList.getNat,
    SOption.unwrap, SOut.bind_ok', SInt.blt, SList.len, SList.lenNat,
    MR_StackFrame.set_locals, MR_Machine.set_mem, retiredCells, frame, finishReturn]
  rfl
/-- The original checked caller store followed by the actual continuation jump.
    The complete outside memory and both dead private allocations are explicit. -/
theorem finish_exact (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr argAddr value n : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (valid : value < modulus 64) :
    finishReturn (fuel + 20)
      (single base [caller]
        (retiredCells (before ++ slot (Int.ofNat callerAddr) callerBytes :: after)
          retAddr argAddr value n accesses))
      value next (ptr before.length (Int.ofNat callerAddr)) =
    SOut.ok (.ok (), single base [(caller.set_next_block next).set_next_stmt 0]
      (retiredCells (before ++ slot (Int.ofNat callerAddr) (u64bytes value) :: after)
        retAddr argAddr value n
        (accesses ++ [⟨.Store, .None, Int.ofNat callerAddr, 8⟩]))) := by
  have hs := typed_store_u64 (fuel + 10)
    (single base [caller]
      (retiredCells (before ++ slot (Int.ofNat callerAddr) callerBytes :: after)
        retAddr argAddr value n accesses))
    before (after ++ [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false,
      (slot (Int.ofNat argAddr) (u64bytes n)).set_live false])
    callerAddr value callerBytes accesses callerLength callerAligned valid
  simp only [single_set_mem, memory, retiredCells, List.append_assoc, List.cons_append, List.nil_append] at hs
  unfold finishReturn
  simp only [memory, retiredCells, List.append_assoc, List.cons_append, List.nil_append]
  rw [hs]
  simp only [SOut.bind_ok']
  rw [jump_single (fuel + 17)]
  rfl

/-- Complete generated Return for a valid caller return cell, including full
    memory retirement, caller store and continuation. No execution-success
    premise or assumed frame/ABI equality appears in this model theorem. -/
theorem return_exact (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (pc : Int) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr retAddr argAddr value n : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (retAligned : retAddr % 8 = 0) (valid : value < modulus 64) :
    MRf.Machine.eval_terminator (fuel + 30)
      (active base caller
        (frame literal
          (ptr (before ++ slot (Int.ofNat callerAddr) callerBytes :: after).length (Int.ofNat retAddr))
          (ptr ((before ++ slot (Int.ofNat callerAddr) callerBytes :: after).length + 1) (Int.ofNat argAddr))
          (.BackToCaller (some next) none (ptr before.length (Int.ofNat callerAddr))) pc)
        (cells (before ++ slot (Int.ofNat callerAddr) callerBytes :: after)
          retAddr argAddr (u64bytes value) n accesses)) .Return =
    SOut.ok (.ok (), single base [(caller.set_next_block next).set_next_stmt 0]
      (retiredCells (before ++ slot (Int.ofNat callerAddr) (u64bytes value) :: after)
        retAddr argAddr value n
        ((accesses ++ [⟨.Load, .None, Int.ofNat retAddr, 8⟩]) ++
          [⟨.Store, .None, Int.ofNat callerAddr, 8⟩]))) := by
  rw [return_to_boundary fuel base caller literal pc next (ptr before.length (Int.ofNat callerAddr))
    (before ++ slot (Int.ofNat callerAddr) callerBytes :: after)
    retAddr argAddr value n accesses retAligned valid]
  exact finish_exact (fuel + 9) base caller next before after callerAddr retAddr argAddr value n
    callerBytes (accesses ++ [⟨.Load, .None, Int.ofNat retAddr, 8⟩]) callerLength callerAligned valid

end MiniRustU64Return
