/- Real scheduler steps for the pair function. Access history is reset by the
   generated step operation, rather than asserted unchanged across steps. -/
import MiniRustWord64PairReturn
import MiniRustU64Step

set_option autoImplicit false
noncomputable section
namespace MiniRustWord64PairStep
open SemR MiniRustU64Function MiniRustWord64PairFunction
  MiniRustWord64PairExecution MiniRustWord64PairReturn
  MiniRustU64Step
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem bind_pick {α β : Type} (k : Nat → SOut α) (f : α → SOut β) :
    (SOut.pick k).bind f = SOut.pick (fun j => (k j).bind f) := rfl
private theorem active_thread_count (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) : SList.len (active base caller callee mem).threads = 1 := rfl
private theorem active_thread_zero (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) : (active base caller callee mem).active_thread = 0 := rfl
private theorem active_set_thread_zero (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) : (active base caller callee mem).set_active_thread 0 =
      active base caller callee mem := rfl
private theorem active_thread_at_zero (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) : SList.get (active base caller callee mem).threads 0 =
      .ok (some ⟨[caller, callee], .Enabled, []⟩) := rfl
private theorem frame_pc (world : List MR_Allocation) (retAddr leftAddr rightAddr : Nat)
    (action : MR_StackPopAction) (pc : Int) :
    (localFrame world retAddr leftAddr rightAddr action pc).next_stmt = pc := rfl
private theorem frame_set_pc (world : List MR_Allocation) (retAddr leftAddr rightAddr : Nat)
    (action : MR_StackPopAction) (pc next : Int) :
    (localFrame world retAddr leftAddr rightAddr action pc).set_next_stmt next =
      localFrame world retAddr leftAddr rightAddr action next := rfl
private theorem cells_reset (world : List MR_Allocation) (retAddr leftAddr rightAddr : Nat)
    (bytes : List MR_AbstractByte) (left right : Nat) (accesses : List MR_Access) :
    (cells world retAddr leftAddr rightAddr bytes left right accesses).set_accesses [] =
      cells world retAddr leftAddr rightAddr bytes left right [] := rfl

theorem frame_current_block (world : List MR_Allocation) (retAddr leftAddr rightAddr : Nat)
    (action : MR_StackPopAction) (pc : Int) :
    SMap.index_at MR_BbName.beq
      (localFrame world retAddr leftAddr rightAddr action pc).func.blocks
      (localFrame world retAddr leftAddr rightAddr action pc).next_block =
      .ok ⟨[statement], .Return, .Regular⟩ := rfl

/-- Every scheduler choice is retained, including rejected indices. Both
    argument loads, the result write, PC advance and race check really run. -/
theorem assign_step (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (action : MR_StackPopAction) (world : List MR_Allocation)
    (retAddr leftAddr rightAddr left right : Nat)
    (retBytes : List MR_AbstractByte) (oldAccesses : List MR_Access)
    (retLength : retBytes.length = 8) (retAligned : retAddr % 8 = 0)
    (leftAligned : leftAddr % 8 = 0) (rightAligned : rightAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    MRf.Machine.step (fuel + 50)
      (active base caller (localFrame world retAddr leftAddr rightAddr action 0)
        (cells world retAddr leftAddr rightAddr retBytes left right oldAccesses)) =
    oneThreadChoice (.ok (), active base caller
      (localFrame world retAddr leftAddr rightAddr action 1)
      (cells world retAddr leftAddr rightAddr (u64bytes ((left + right) % modulus 64)) left right
        [⟨.Load, .None, Int.ofNat leftAddr, 8⟩, ⟨.Load, .None, Int.ofNat rightAddr, 8⟩,
          ⟨.Store, .None, Int.ofNat retAddr, 8⟩])) := by
  simp only [MRf.Machine.step]
  rw [enabled_active]
  simp only [SOut.bind_ok', SBool.not]
  rw [reset_active (fuel + 47)]
  simp only [SOut.bind_ok', cells_reset, SPick.choose, active_thread_count]
  rw [show SInt.div_ceil 0 1 = .ok 0 from rfl]
  simp only [SOut.bind_ok', bind_pick]
  unfold oneThreadChoice
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
    rw [active_thread_at_zero]
    simp only [SOut.bind_ok', MR_ThreadState.beq]
    rw [active_set_thread_zero, active_cur_frame (fuel + 46)]
    simp only [SOut.bind_ok']
    rw [frame_current_block]
    simp only [SOut.bind_ok', frame_pc]
    rw [show SList.len [statement] = 1 from rfl]
    simp only [show SInt.beq 0 1 = false from rfl]
    rw [show SList.index_at [statement] 0 = .ok statement from rfl]
    simp only [SOut.bind_ok']
    have ha := MiniRustWord64PairExecution.assign_exact (fuel + 27) base caller action 0 world
      retAddr leftAddr rightAddr retBytes left right [] retLength retAligned
      leftAligned rightAligned leftValid rightValid
    simp only [state] at ha
    change MRf.Machine.eval_statement (fuel + 49)
      (active base caller (localFrame world retAddr leftAddr rightAddr action 0)
        (cells world retAddr leftAddr rightAddr retBytes left right [])) statement = _ at ha
    rw [ha]
    simp only [SOut.bind_ok']
    rw [increment_active (fuel + 46)]
    simp only [SOut.bind_ok', frame_pc, frame_set_pc, active_thread_zero]
    rw [current_thread_race_check (fuel + 48)]
    rfl

private theorem single_thread_zero (base : MR_Machine) (stack : List MR_StackFrame)
    (mem : MR_ConcurrentMemory) : (MiniRustU64Execution.single base stack mem).active_thread = 0 := rfl

/-- The real Return step resets the previous statement log, reads the result,
    retires three locals, writes the caller cell and resumes the caller. -/
theorem return_step (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr leftAddr rightAddr value left right : Nat)
    (callerBytes : List MR_AbstractByte) (oldAccesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (retAligned : retAddr % 8 = 0) (valid : value < modulus 64) :
    MRf.Machine.step (fuel + 50)
      (active base caller
        (localFrame (callerWorld before after callerAddr callerBytes) retAddr leftAddr rightAddr
          (.BackToCaller (some next) none (ptr before.length (Int.ofNat callerAddr))) 1)
        (cells (callerWorld before after callerAddr callerBytes)
          retAddr leftAddr rightAddr (u64bytes value) left right oldAccesses)) =
    oneThreadChoice (.ok (), MiniRustU64Execution.single base [(caller.set_next_block next).set_next_stmt 0]
      (retiredCells (callerWorld before after callerAddr (u64bytes value))
        retAddr leftAddr rightAddr value left right
        [⟨.Load, .None, Int.ofNat retAddr, 8⟩, ⟨.Store, .None, Int.ofNat callerAddr, 8⟩])) := by
  simp only [MRf.Machine.step]
  rw [enabled_active]
  simp only [SOut.bind_ok', SBool.not]
  rw [reset_active (fuel + 47)]
  simp only [SOut.bind_ok', cells_reset, SPick.choose, active_thread_count]
  rw [show SInt.div_ceil 0 1 = .ok 0 from rfl]
  simp only [SOut.bind_ok', bind_pick]
  unfold oneThreadChoice
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
    rw [active_thread_at_zero]
    simp only [SOut.bind_ok', MR_ThreadState.beq]
    rw [active_set_thread_zero, active_cur_frame (fuel + 46)]
    simp only [SOut.bind_ok']
    rw [frame_current_block]
    simp only [SOut.bind_ok', frame_pc]
    rw [show SList.len [statement] = 1 from rfl]
    simp only [show SInt.beq 1 1 = true from rfl, callerWorld]
    rw [MiniRustWord64PairReturn.return_exact (fuel + 19) base caller 1 next before after
      callerAddr retAddr leftAddr rightAddr value left right callerBytes []
      callerLength callerAligned retAligned valid]
    simp only [SOut.bind_ok', single_thread_zero]
    rw [current_thread_race_check (fuel + 48)]
    rfl

end MiniRustWord64PairStep
