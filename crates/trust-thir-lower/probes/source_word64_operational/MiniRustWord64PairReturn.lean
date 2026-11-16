/- Retirement primitives for the actual two-argument MiniRust frame.
   These do not postulate a successful return or grant source/ABI authority. -/
import MiniRustWord64PairExecution
import MiniRustU64Return

set_option autoImplicit false
noncomputable section
namespace MiniRustWord64PairReturn
open SemR MiniRustU64Function MiniRustWord64PairFunction MiniRustWord64PairExecution
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The hypotheses are finite map equalities over the actual frame, not a
    successful deallocation premise. The generated operation retires precisely
    the named private allocation and preserves its bytes and access history. -/
theorem storage_dead_local (fuel : Nat) (current : MR_StackFrame) (name : MR_LocalName)
    (remaining : List (MR_LocalName × MR_ThinPointer))
    (before after : List MR_Allocation) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access)
    (length : bytes.length = 8)
    (typed : SMap.index_at MR_LocalName.beq current.func.locals name =
      .ok (.Int (mrIntTy false .u64)))
    (removed : SMap.remove MR_LocalName.beq current.locals name =
      (some (ptr before.length (Int.ofNat addr)), remaining)) :
    MRf.StackFrame.storage_dead (fuel + 10) current
      (memory before after addr bytes accesses) name =
    .ok (.ok (), current.set_locals remaining,
      ⟨⟨before ++ (slot (Int.ofNat addr) bytes).set_live false :: after, ()⟩, accesses⟩) := by
  simp only [MRf.StackFrame.storage_dead]
  rw [typed]
  simp only [SOut.bind_ok', layout_u64,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align]
  rw [removed]
  dsimp only
  rw [concurrent_deallocate_private_slot (fuel + 4) before after addr bytes accesses length]
  rfl

theorem frame_local_type (ret left right : MR_ThinPointer) (action : MR_StackPopAction)
    (nextStatement : Int) (which : Local) :
    SMap.index_at MR_LocalName.beq
      (MiniRustWord64PairFunction.frame ret left right action nextStatement).func.locals
      which.name = .ok (.Int (mrIntTy false .u64)) := by
  cases which <;> rfl

private theorem single_memory (base : MR_Machine) (caller : MR_StackFrame)
    (mem : MR_ConcurrentMemory) :
    (MiniRustU64Execution.single base [caller] mem).mem = mem := rfl

/-- One actual generated Return-loop iteration. Its map premises are checked
    on the concrete three-local frame below; no successful iteration is assumed. -/
theorem retire_head (fuel : Nat) (base : MR_Machine) (caller current : MR_StackFrame)
    (name : MR_LocalName) (remaining : List (MR_LocalName × MR_ThinPointer))
    (before after : List MR_Allocation) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access)
    (length : bytes.length = 8)
    (typed : SMap.index_at MR_LocalName.beq current.func.locals name =
      .ok (.Int (mrIntTy false .u64)))
    (locals : current.locals = (name, ptr before.length (Int.ofNat addr)) :: remaining) :
    MiniRustU64Execution.retireOne (fuel + 10)
      (current, MiniRustU64Execution.single base [caller]
        (memory before after addr bytes accesses)) =
    .ok (.next (current.set_locals remaining,
      MiniRustU64Execution.single base [caller]
        ⟨⟨before ++ (slot (Int.ofNat addr) bytes).set_live false :: after, ()⟩, accesses⟩)) := by
  have removed : SMap.remove MR_LocalName.beq current.locals name =
      (some (ptr before.length (Int.ofNat addr)), remaining) := by
    rw [locals]
    cases name
    simp [SMap.remove, SMap.get, SMap.getL, SMap.removeL, MR_LocalName.beq]
  have hs := storage_dead_local fuel current name remaining before after addr bytes accesses
    length typed removed
  simp only [MiniRustU64Execution.retireOne, single_memory, locals, SMap.keys, SList.first]
  rw [hs]
  rfl

def localFrame (world : List MR_Allocation) (retAddr leftAddr rightAddr : Nat)
    (action : MR_StackPopAction) (pc : Int) : MR_StackFrame :=
  MiniRustWord64PairFunction.frame (ptr world.length (Int.ofNat retAddr))
    (ptr (world.length + 1) (Int.ofNat leftAddr))
    (ptr (world.length + 2) (Int.ofNat rightAddr)) action pc

def remainingLeft (world : List MR_Allocation) (leftAddr rightAddr : Nat) :
    List (MR_LocalName × MR_ThinPointer) :=
  [(⟨1⟩, ptr (world.length + 1) (Int.ofNat leftAddr)),
    (⟨2⟩, ptr (world.length + 2) (Int.ofNat rightAddr))]

def remainingRight (world : List MR_Allocation) (rightAddr : Nat) :
    List (MR_LocalName × MR_ThinPointer) :=
  [(⟨2⟩, ptr (world.length + 2) (Int.ofNat rightAddr))]

def afterReturn (world : List MR_Allocation) (retAddr leftAddr rightAddr value left right : Nat)
    (accesses : List MR_Access) : MR_ConcurrentMemory :=
  ⟨⟨world ++ [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false,
    slot (Int.ofNat leftAddr) (u64bytes left), slot (Int.ofNat rightAddr) (u64bytes right)], ()⟩,
    accesses⟩

def afterLeft (world : List MR_Allocation) (retAddr leftAddr rightAddr value left right : Nat)
    (accesses : List MR_Access) : MR_ConcurrentMemory :=
  ⟨⟨world ++ [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false,
    (slot (Int.ofNat leftAddr) (u64bytes left)).set_live false,
    slot (Int.ofNat rightAddr) (u64bytes right)], ()⟩, accesses⟩

def retiredCells (world : List MR_Allocation) (retAddr leftAddr rightAddr value left right : Nat)
    (accesses : List MR_Access) : MR_ConcurrentMemory :=
  ⟨⟨world ++ [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false,
    (slot (Int.ofNat leftAddr) (u64bytes left)).set_live false,
    (slot (Int.ofNat rightAddr) (u64bytes right)).set_live false], ()⟩, accesses⟩

theorem retire_first (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (action : MR_StackPopAction) (pc : Int) (world : List MR_Allocation)
    (retAddr leftAddr rightAddr value left right : Nat) (accesses : List MR_Access) :
    MiniRustU64Execution.retireOne (fuel + 10)
      (localFrame world retAddr leftAddr rightAddr action pc,
        MiniRustU64Execution.single base [caller]
          (cells world retAddr leftAddr rightAddr (u64bytes value) left right accesses)) =
    .ok (.next
      ((localFrame world retAddr leftAddr rightAddr action pc).set_locals
        (remainingLeft world leftAddr rightAddr),
       MiniRustU64Execution.single base [caller]
        (afterReturn world retAddr leftAddr rightAddr value left right accesses))) := by
  have h := retire_head fuel base caller
    (localFrame world retAddr leftAddr rightAddr action pc) ⟨0⟩
    (remainingLeft world leftAddr rightAddr)
    world [slot (Int.ofNat leftAddr) (u64bytes left), slot (Int.ofNat rightAddr) (u64bytes right)]
    retAddr (u64bytes value) accesses (u64bytes_length value) (by rfl) (by rfl)
  simpa only [cells, memory, afterReturn] using h

theorem retire_second (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (action : MR_StackPopAction) (pc : Int) (world : List MR_Allocation)
    (retAddr leftAddr rightAddr value left right : Nat) (accesses : List MR_Access) :
    MiniRustU64Execution.retireOne (fuel + 10)
      ((localFrame world retAddr leftAddr rightAddr action pc).set_locals
        (remainingLeft world leftAddr rightAddr),
       MiniRustU64Execution.single base [caller]
        (afterReturn world retAddr leftAddr rightAddr value left right accesses)) =
    .ok (.next
      ((localFrame world retAddr leftAddr rightAddr action pc).set_locals
        (remainingRight world rightAddr),
       MiniRustU64Execution.single base [caller]
        (afterLeft world retAddr leftAddr rightAddr value left right accesses))) := by
  have h := retire_head fuel base caller
    ((localFrame world retAddr leftAddr rightAddr action pc).set_locals
      (remainingLeft world leftAddr rightAddr)) ⟨1⟩ (remainingRight world rightAddr)
    (world ++ [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false])
    [slot (Int.ofNat rightAddr) (u64bytes right)] leftAddr (u64bytes left) accesses
    (u64bytes_length left) (by rfl)
    (by simp [localFrame, remainingLeft, remainingRight, MiniRustWord64PairFunction.frame,
      MR_StackFrame.set_locals])
  simpa [afterReturn, afterLeft, memory, List.append_assoc, localFrame,
    MiniRustWord64PairFunction.frame, MR_StackFrame.set_locals] using h

theorem retire_third (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (action : MR_StackPopAction) (pc : Int) (world : List MR_Allocation)
    (retAddr leftAddr rightAddr value left right : Nat) (accesses : List MR_Access) :
    MiniRustU64Execution.retireOne (fuel + 10)
      ((localFrame world retAddr leftAddr rightAddr action pc).set_locals
        (remainingRight world rightAddr),
       MiniRustU64Execution.single base [caller]
        (afterLeft world retAddr leftAddr rightAddr value left right accesses)) =
    .ok (.next
      ((localFrame world retAddr leftAddr rightAddr action pc).set_locals [],
       MiniRustU64Execution.single base [caller]
        (retiredCells world retAddr leftAddr rightAddr value left right accesses))) := by
  have h := retire_head fuel base caller
    ((localFrame world retAddr leftAddr rightAddr action pc).set_locals
      (remainingRight world rightAddr)) ⟨2⟩ []
    (world ++ [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false,
      (slot (Int.ofNat leftAddr) (u64bytes left)).set_live false])
    [] rightAddr (u64bytes right) accesses (u64bytes_length right) (by rfl)
    (by simp [localFrame, remainingRight, MiniRustWord64PairFunction.frame,
      MR_StackFrame.set_locals])
  simpa [afterLeft, retiredCells, memory, List.append_assoc, localFrame,
    MiniRustWord64PairFunction.frame, MR_StackFrame.set_locals] using h

/-- All three actual locals retire. The generated loop needs a final iteration
    to observe emptiness; no successful-retirement premise replaces these steps. -/
theorem retire_loop (fuel spare : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (action : MR_StackPopAction) (pc : Int) (world : List MR_Allocation)
    (retAddr leftAddr rightAddr value left right : Nat) (accesses : List MR_Access) :
    SLoop.whileS (spare + 4)
      (localFrame world retAddr leftAddr rightAddr action pc,
        MiniRustU64Execution.single base [caller]
          (cells world retAddr leftAddr rightAddr (u64bytes value) left right accesses))
      (MiniRustU64Execution.retireOne (fuel + 10)) =
    .ok (.brk
      ((localFrame world retAddr leftAddr rightAddr action pc).set_locals [],
       MiniRustU64Execution.single base [caller]
        (retiredCells world retAddr leftAddr rightAddr value left right accesses))) := by
  rw [SLoop.whileS, retire_first]
  simp only [SOut.bind_ok']
  rw [SLoop.whileS, retire_second]
  simp only [SOut.bind_ok']
  rw [SLoop.whileS, retire_third]
  simp only [SOut.bind_ok']
  rw [SLoop.whileS]
  rfl

private theorem single_set_memory (base : MR_Machine) (caller : MR_StackFrame)
    (before after : MR_ConcurrentMemory) :
    (MiniRustU64Execution.single base [caller] before).set_mem after =
      MiniRustU64Execution.single base [caller] after := rfl

theorem frame_return_type (world : List MR_Allocation) (retAddr leftAddr rightAddr : Nat)
    (action : MR_StackPopAction) (pc : Int) :
    SMap.index_at MR_LocalName.beq
      (localFrame world retAddr leftAddr rightAddr action pc).func.locals
      (localFrame world retAddr leftAddr rightAddr action pc).func.ret =
      .ok (.Int (mrIntTy false .u64)) := rfl

theorem frame_return_pointer (world : List MR_Allocation) (retAddr leftAddr rightAddr : Nat)
    (action : MR_StackPopAction) (pc : Int) :
    SMap.index_at MR_LocalName.beq
      (localFrame world retAddr leftAddr rightAddr action pc).locals
      (localFrame world retAddr leftAddr rightAddr action pc).func.ret =
      .ok (ptr world.length (Int.ofNat retAddr)) := rfl

/-- Actual Return pops the pair frame, reads its result before retirement,
    retires all three locals, and preserves the original checked caller store
    and continuation, including their error paths for an invalid target. -/
theorem return_to_boundary (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (pc : Int) (next : MR_BbName) (target : MR_ThinPointer)
    (world : List MR_Allocation) (retAddr leftAddr rightAddr value left right : Nat)
    (accesses : List MR_Access) (retAligned : retAddr % 8 = 0)
    (valid : value < modulus 64) :
    MRf.Machine.eval_terminator (fuel + 30)
      (active base caller
        (localFrame world retAddr leftAddr rightAddr (.BackToCaller (some next) none target) pc)
        (cells world retAddr leftAddr rightAddr (u64bytes value) left right accesses)) .Return =
    MiniRustU64Return.finishReturn (fuel + 29)
      (MiniRustU64Execution.single base [caller]
        (retiredCells world retAddr leftAddr rightAddr value left right
          (accesses ++ [⟨.Load, .None, Int.ofNat retAddr, 8⟩]))) value next target := by
  have ht := typed_load_u64 (fuel + 19)
    (MiniRustU64Execution.single base [caller]
      (cells world retAddr leftAddr rightAddr (u64bytes value) left right accesses))
    world [slot (Int.ofNat leftAddr) (u64bytes left), slot (Int.ofNat rightAddr) (u64bytes right)]
    retAddr value accesses retAligned valid
  simp only [cells, single_set_memory] at ht
  have hl := retire_loop (fuel + 19) (fuel + 25) base caller
    (.BackToCaller (some next) none target) pc world retAddr leftAddr rightAddr value left right
    (accesses ++ [⟨.Load, .None, Int.ofNat retAddr, 8⟩])
  unfold MiniRustU64Execution.retireOne at hl
  simp [Nat.add_assoc] at hl
  simp only [MRf.Machine.eval_terminator]
  rw [MiniRustU64Execution.pop_active (fuel + 28)]
  simp only [SOut.bind_ok']
  rw [frame_return_type]
  simp only [SOut.bind_ok']
  rw [layout_u64 (fuel + 26)]
  simp only [SOut.bind_ok', MRf.LayoutStrategy.expect_align]
  rw [frame_return_pointer]
  simp only [SOut.bind_ok', cells]
  rw [ht]
  simp only [SOut.bind_ok', Int.ofNat_eq_natCast]
  conv =>
    lhs
    arg 1
    tactic => exact hl
  simp only [SOut.bind_ok']
  simp only [MRf.ConcurrentMemory.end_call, MRf.BasicMemory.Memory.end_call,
    SOut.bind_ok', MR_ConcurrentMemory.set_memory]
  simp [MRf.Machine.active_thread, MiniRustU64Execution.single, SList.index_at,
    SList.get, SList.getNat, SOption.unwrap, SOut.bind_ok', SInt.blt,
    SList.len, SList.lenNat, MR_StackFrame.set_locals, MR_Machine.set_mem,
    retiredCells, localFrame, MiniRustWord64PairFunction.frame,
    MiniRustU64Return.finishReturn]
  rfl

/-- The actual caller-result store and resumption, retaining every surrounding
    allocation plus the three dead private objects and their exact bytes. -/
theorem finish_exact (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr leftAddr rightAddr value left right : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (valid : value < modulus 64) :
    MiniRustU64Return.finishReturn (fuel + 20)
      (MiniRustU64Execution.single base [caller]
        (retiredCells (before ++ slot (Int.ofNat callerAddr) callerBytes :: after)
          retAddr leftAddr rightAddr value left right accesses))
      value next (ptr before.length (Int.ofNat callerAddr)) =
    .ok (.ok (), MiniRustU64Execution.single base [(caller.set_next_block next).set_next_stmt 0]
      (retiredCells (before ++ slot (Int.ofNat callerAddr) (u64bytes value) :: after)
        retAddr leftAddr rightAddr value left right
        (accesses ++ [⟨.Store, .None, Int.ofNat callerAddr, 8⟩]))) := by
  have hs := typed_store_u64 (fuel + 10)
    (MiniRustU64Execution.single base [caller]
      (retiredCells (before ++ slot (Int.ofNat callerAddr) callerBytes :: after)
        retAddr leftAddr rightAddr value left right accesses))
    before (after ++ [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false,
      (slot (Int.ofNat leftAddr) (u64bytes left)).set_live false,
      (slot (Int.ofNat rightAddr) (u64bytes right)).set_live false])
    callerAddr value callerBytes accesses callerLength callerAligned valid
  simp only [single_set_memory, memory, retiredCells, List.append_assoc,
    List.cons_append, List.nil_append] at hs
  unfold MiniRustU64Return.finishReturn
  simp only [memory, retiredCells, List.append_assoc, List.cons_append, List.nil_append]
  rw [hs]
  simp only [SOut.bind_ok']
  rw [MiniRustU64Execution.jump_single (fuel + 17)]
  rfl

/-- Complete generated Return at a valid caller cell, with the full caller
    resumption and all three retired callee objects retained explicitly. -/
theorem return_exact (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (pc : Int) (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr leftAddr rightAddr value left right : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (retAligned : retAddr % 8 = 0) (valid : value < modulus 64) :
    MRf.Machine.eval_terminator (fuel + 30)
      (active base caller
        (localFrame (before ++ slot (Int.ofNat callerAddr) callerBytes :: after)
          retAddr leftAddr rightAddr
          (.BackToCaller (some next) none (ptr before.length (Int.ofNat callerAddr))) pc)
        (cells (before ++ slot (Int.ofNat callerAddr) callerBytes :: after)
          retAddr leftAddr rightAddr (u64bytes value) left right accesses)) .Return =
    .ok (.ok (), MiniRustU64Execution.single base [(caller.set_next_block next).set_next_stmt 0]
      (retiredCells (before ++ slot (Int.ofNat callerAddr) (u64bytes value) :: after)
        retAddr leftAddr rightAddr value left right
        ((accesses ++ [⟨.Load, .None, Int.ofNat retAddr, 8⟩]) ++
          [⟨.Store, .None, Int.ofNat callerAddr, 8⟩]))) := by
  rw [return_to_boundary fuel base caller pc next (ptr before.length (Int.ofNat callerAddr))
    (before ++ slot (Int.ofNat callerAddr) callerBytes :: after)
    retAddr leftAddr rightAddr value left right accesses retAligned valid]
  exact finish_exact (fuel + 9) base caller next before after callerAddr retAddr leftAddr rightAddr
    value left right callerBytes (accesses ++ [⟨.Load, .None, Int.ofNat retAddr, 8⟩])
    callerLength callerAligned valid

end MiniRustWord64PairReturn
