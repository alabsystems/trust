/- Actual scheduler/PC/race-tracking steps for the U64 function boundary. -/
import MiniRustU64Return
noncomputable section
namespace MiniRustU64Step
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The existing scheduler's one enabled-thread tree, including rejected indices. -/
def oneThreadChoice {α : Type} (result : α) : SOut α :=
  .pick (fun index => match index with | 0 => .ok result | _ + 1 => .reject)

theorem oneThread_oracle {α : Type} (result : α) (δ π : List Nat → Nat) :
    SOut.runOracle δ π (oneThreadChoice result) =
      match δ [] with | 0 => .ok result | _ + 1 => .reject := by
  simp only [oneThreadChoice, SOut.runOracle]
  cases h : δ [] <;> simp only [h] <;> rfl

private theorem contains_push_self (xs : List Int) (x : Int) :
    SSet.contains SInt.beq (SList.push xs x) x = true := by
  induction xs with
  | nil => simp [SSet.contains, SList.push, SList.appendL, SInt.beq]
  | cons a xs ih =>
    simp only [SList.push] at ih
    cases h : SInt.beq a x <;> simp [SList.push, SList.appendL, SSet.contains, h, ih]

theorem contains_insert_self (xs : List Int) (x : Int) :
    SSet.contains SInt.beq (SSet.insert SInt.beq xs x) x = true := by
  unfold SSet.insert
  cases h : SSet.contains SInt.beq xs x with
  | true => exact h
  | false => exact contains_push_self xs x

/-- The actual race checker uses its authenticated current-thread synchronization
    entry. No race-check call is removed or replaced by an assumption. -/
theorem current_thread_race_check (fuel : Nat) (mem : MR_ConcurrentMemory)
    (synchronized : List Int) (oldAccesses : List MR_Access) :
    MRf.ConcurrentMemory.check_data_races (fuel + 1) mem 0
      (SSet.insert SInt.beq synchronized 0, oldAccesses) = SOut.ok (.ok ()) := by
  simp only [MRf.ConcurrentMemory.check_data_races, contains_insert_self]

theorem reset_active (fuel : Nat) (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) :
    MRf.Machine.reset_data_race_tracking (fuel + 2) (active base caller callee mem) =
      SOut.ok ((SSet.insert SInt.beq base.synchronized_threads 0, mem.accesses),
        active base caller callee (mem.set_accesses [])) := by
  simp [MRf.Machine.reset_data_race_tracking, MRf.ConcurrentMemory.reset_accesses,
    active, MR_Machine.set_mem, SOut.bind_ok']

theorem enabled_active (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) :
    SList.anyS (active base caller callee mem).threads
      (fun thread (_ : Unit) => SOut.ok (MR_ThreadState.beq thread.state .Enabled, ())) () =
      SOut.ok (true, ()) := rfl

theorem frame_current_block (literal : Nat) (ret arg : MR_ThinPointer)
    (action : MR_StackPopAction) (pc : Int) :
    SMap.index_at MR_BbName.beq (frame literal ret arg action pc).func.blocks
      (frame literal ret arg action pc).next_block =
      SOut.ok ⟨[statement literal], .Return, .Regular⟩ := rfl

theorem increment_active (fuel : Nat) (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) :
    MRf.Machine.try_mutate_cur_frame Unit Unit (fuel + 3) (active base caller callee mem)
      (fun frame mem (_ : Unit) =>
        SOut.ok (.ok (), frame.set_next_stmt (frame.next_stmt + 1), mem, ())) () =
    SOut.ok (.ok (), active base caller (callee.set_next_stmt (callee.next_stmt + 1)) mem, ()) := by
  simp [MRf.Machine.try_mutate_cur_frame, MRf.Thread.try_mutate_cur_frame,
    active, SList.mutateAtS, SList.mutateAtNat, SList.is_empty, SList.len, SList.lenNat,
    SOut.bind_ok', MR_Thread.set_stack, MR_Machine.set_threads, MR_Machine.set_mem]

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
      SOut.ok (some ⟨[caller, callee], .Enabled, []⟩) := rfl
private theorem frame_pc (literal : Nat) (ret arg : MR_ThinPointer)
    (action : MR_StackPopAction) (pc : Int) : (frame literal ret arg action pc).next_stmt = pc := rfl
private theorem frame_set_pc (literal : Nat) (ret arg : MR_ThinPointer)
    (action : MR_StackPopAction) (pc next : Int) :
    (frame literal ret arg action pc).set_next_stmt next = frame literal ret arg action next := rfl
private theorem cells_reset (world : List MR_Allocation) (retAddr argAddr : Nat)
    (bytes : List MR_AbstractByte) (n : Nat) (accesses : List MR_Access) :
    (cells world retAddr argAddr bytes n accesses).set_accesses [] =
      cells world retAddr argAddr bytes n [] := rfl

/-- Actual Machine.step for Assign: all schedule indices are preserved, the
    statement really executes, the actual PC advances, and the real race check
    runs. No successful scheduling/statement premise is assumed. -/
theorem assign_step (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (action : MR_StackPopAction)
    (world : List MR_Allocation) (retAddr argAddr n : Nat)
    (retBytes : List MR_AbstractByte) (oldAccesses : List MR_Access)
    (retLength : retBytes.length = 8) (retAligned : retAddr % 8 = 0)
    (argAligned : argAddr % 8 = 0) (valid : n < modulus 64)
    (literalValid : literal < modulus 64) :
    MRf.Machine.step (fuel + 50)
      (active base caller
        (frame literal (ptr world.length (Int.ofNat retAddr))
          (ptr (world.length + 1) (Int.ofNat argAddr)) action 0)
        (cells world retAddr argAddr retBytes n oldAccesses)) =
    oneThreadChoice (.ok (), active base caller
      (frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action 1)
      (cells world retAddr argAddr (u64bytes ((n + literal) % modulus 64)) n
        [⟨.Load, .None, Int.ofNat argAddr, 8⟩, ⟨.Store, .None, Int.ofNat retAddr, 8⟩])) := by
  simp only [MRf.Machine.step]
  rw [enabled_active]
  simp only [SOut.bind_ok', SBool.not]
  rw [reset_active (fuel + 47)]
  simp only [SOut.bind_ok', cells_reset]
  simp only [SPick.choose, active_thread_count]
  rw [show SInt.div_ceil 0 1 = SOut.ok 0 from rfl]
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
    rw [show SList.len [statement literal] = 1 from rfl]
    simp only [show SInt.beq 0 1 = false from rfl]
    rw [show SList.index_at [statement literal] 0 = SOut.ok (statement literal) from rfl]
    simp only [SOut.bind_ok']
    rw [assign_exact (fuel + 27) base caller literal action 0 world retAddr argAddr n
      retBytes [] retLength retAligned argAligned valid literalValid]
    simp only [SOut.bind_ok']
    rw [increment_active (fuel + 46)]
    simp only [SOut.bind_ok', frame_pc, frame_set_pc, active_thread_zero]
    rw [current_thread_race_check (fuel + 48)]
    rfl

def callerWorld (before after : List MR_Allocation) (addr : Nat)
    (bytes : List MR_AbstractByte) : List MR_Allocation :=
  before ++ slot (Int.ofNat addr) bytes :: after

private theorem single_thread_zero (base : MR_Machine) (stack : List MR_StackFrame)
    (mem : MR_ConcurrentMemory) : (single base stack mem).active_thread = 0 := rfl

/-- Actual second machine step: PC1 selects the real Return, including its
    result load, both retirements, caller store/jump, and the actual race check.
    The original schedule tree and every rejected index remain explicit. -/
theorem return_step (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr argAddr value n : Nat)
    (callerBytes : List MR_AbstractByte) (oldAccesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (retAligned : retAddr % 8 = 0) (valid : value < modulus 64) :
    MRf.Machine.step (fuel + 50)
      (active base caller
        (frame literal
          (ptr (callerWorld before after callerAddr callerBytes).length (Int.ofNat retAddr))
          (ptr ((callerWorld before after callerAddr callerBytes).length + 1) (Int.ofNat argAddr))
          (.BackToCaller (some next) none (ptr before.length (Int.ofNat callerAddr))) 1)
        (cells (callerWorld before after callerAddr callerBytes)
          retAddr argAddr (u64bytes value) n oldAccesses)) =
    oneThreadChoice (.ok (), single base [(caller.set_next_block next).set_next_stmt 0]
      (retiredCells (callerWorld before after callerAddr (u64bytes value))
        retAddr argAddr value n
        [⟨.Load, .None, Int.ofNat retAddr, 8⟩, ⟨.Store, .None, Int.ofNat callerAddr, 8⟩])) := by
  simp only [MRf.Machine.step]
  rw [enabled_active]
  simp only [SOut.bind_ok', SBool.not]
  rw [reset_active (fuel + 47)]
  simp only [SOut.bind_ok', cells_reset]
  simp only [SPick.choose, active_thread_count]
  rw [show SInt.div_ceil 0 1 = SOut.ok 0 from rfl]
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
    rw [show SList.len [statement literal] = 1 from rfl]
    simp only [show SInt.beq 1 1 = true from rfl]
    simp only [callerWorld]
    rw [return_exact (fuel + 19) base caller literal 1 next before after
      callerAddr retAddr argAddr value n callerBytes [] callerLength callerAligned retAligned valid]
    simp only [SOut.bind_ok', single_thread_zero]
    rw [current_thread_race_check (fuel + 48)]
    rfl

end MiniRustU64Step
