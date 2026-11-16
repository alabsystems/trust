/- Function-level execution proofs over the actual generated MiniRust machine.
   These do not prove frontend/Core elaboration, physical ABI or source admission. -/
import MiniRustU64Function
noncomputable section
namespace MiniRustU64Execution
open SemR MiniRustU64Function
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def expression (literal : Nat) : MR_ValueExpr :=
  .BinOp (.Int .Add) (.Load (.Local ⟨1⟩))
    (.Constant (.Int (Int.ofNat literal)) (.Int (mrIntTy false .u64)))

def statement (literal : Nat) : MR_Statement := .Assign (.Local ⟨0⟩) (expression literal)

/-- Actual generated local-load/constant/add execution, with no postulated
    successful-expression premise and with the complete memory/log endpoint. -/
theorem eval_add_expression (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (ret : MR_ThinPointer) (action : MR_StackPopAction) (nextStatement : Int)
    (before after : List MR_Allocation) (addr n : Nat) (accesses : List MR_Access)
    (aligned : addr % 8 = 0) (valid : n < modulus 64) (literalValid : literal < modulus 64) :
    MRf.Machine.eval_value (fuel + 20)
      (active base caller (frame literal ret (ptr before.length (Int.ofNat addr)) action nextStatement)
        (memory before after addr (u64bytes n) accesses)) (expression literal) =
    SOut.ok (.ok (.Int (Int.ofNat ((n + literal) % modulus 64)), .Int (mrIntTy false .u64)),
      active base caller (frame literal ret (ptr before.length (Int.ofNat addr)) action nextStatement)
        (memory before after addr (u64bytes n)
          (accesses ++ [⟨.Load, .None, Int.ofNat addr, 8⟩]))) := by
  rw [expression, eval_binop_eq (fuel + 18),
    load_argument (fuel + 4) base caller literal ret action nextStatement before after addr n accesses aligned valid]
  simp only [SOut.bind_ok']
  rw [eval_const_eq (fuel + 17)]
  simp only [SOut.bind_ok']
  have ha := add_minirust (fuel + 15)
    (active base caller (frame literal ret (ptr before.length (Int.ofNat addr)) action nextStatement)
      (memory before after addr (u64bytes n)
        (accesses ++ [⟨.Load, .None, Int.ofNat addr, 8⟩])))
    false .u64 n literal valid literalValid
  simp only [readAt_false] at ha
  rw [ha]
  rfl

def cells (world : List MR_Allocation) (retAddr argAddr : Nat)
    (retBytes : List MR_AbstractByte) (n : Nat) (accesses : List MR_Access) : MR_ConcurrentMemory :=
  memory world [slot (Int.ofNat argAddr) (u64bytes n)] retAddr retBytes accesses

private theorem active_set_mem (base : MR_Machine) (caller callee : MR_StackFrame)
    (a b : MR_ConcurrentMemory) :
    (active base caller callee a).set_mem b = active base caller callee b := rfl

/-- The actual Assign statement stores the modulo64 result into its allocated
    return local. Every surrounding allocation and the argument bytes remain. -/
theorem assign_exact (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (action : MR_StackPopAction) (nextStatement : Int)
    (world : List MR_Allocation) (retAddr argAddr n : Nat)
    (retBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (retLength : retBytes.length = 8) (retAligned : retAddr % 8 = 0)
    (argAligned : argAddr % 8 = 0) (valid : n < modulus 64)
    (literalValid : literal < modulus 64) :
    MRf.Machine.eval_statement (fuel + 22)
      (active base caller
        (frame literal (ptr world.length (Int.ofNat retAddr))
          (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement)
        (cells world retAddr argAddr retBytes n accesses)) (statement literal) =
    SOut.ok (.ok (), active base caller
      (frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement)
      (cells world retAddr argAddr (u64bytes ((n + literal) % modulus 64)) n
        ((accesses ++ [⟨.Load, .None, Int.ofNat argAddr, 8⟩]) ++
          [⟨.Store, .None, Int.ofNat retAddr, 8⟩]))) := by
  have he := eval_add_expression (fuel + 1) base caller literal
    (ptr world.length (Int.ofNat retAddr)) action nextStatement
    (world ++ [slot (Int.ofNat retAddr) retBytes]) [] argAddr n accesses argAligned valid literalValid
  simp only [List.length_append, List.length_singleton] at he
  have he' : MRf.Machine.eval_value (fuel + 21)
      (active base caller
        (frame literal (ptr world.length (Int.ofNat retAddr))
          (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement)
        (cells world retAddr argAddr retBytes n accesses)) (expression literal) =
    SOut.ok (.ok (.Int (Int.ofNat ((n + literal) % modulus 64)), .Int (mrIntTy false .u64)),
      active base caller
        (frame literal (ptr world.length (Int.ofNat retAddr))
          (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement)
        (cells world retAddr argAddr retBytes n
          (accesses ++ [⟨.Load, .None, Int.ofNat argAddr, 8⟩]))) := by
    simpa only [cells, memory, List.append_assoc, List.nil_append] using he
  simp only [statement, MRf.Machine.eval_statement]
  rw [eval_local_return (fuel + 11)]
  simp only [SOut.bind_ok']
  rw [he']
  simp only [SOut.bind_ok', MRf.Machine.place_store, place, SBool.not]
  rw [typed_store_alignment_one (fuel + 10) _ world.length retAddr _ _ retAligned]
  have hs := typed_store_u64 (fuel + 10)
    (active base caller
      (frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement)
      (cells world retAddr argAddr retBytes n
        (accesses ++ [⟨.Load, .None, Int.ofNat argAddr, 8⟩])))
    world [slot (Int.ofNat argAddr) (u64bytes n)] retAddr ((n + literal) % modulus 64)
    retBytes (accesses ++ [⟨.Load, .None, Int.ofNat argAddr, 8⟩]) retLength retAligned
    (Nat.mod_lt _ (by decide))
  simp only [active_set_mem] at hs
  simp only [cells] at hs ⊢
  rw [hs]
  rfl
/-- The real StorageDead path removes the return local and retires its exact
    allocation; it preserves its bytes and every surrounding allocation. -/
theorem storage_dead_return (fuel : Nat) (literal : Nat) (arg : MR_ThinPointer)
    (action : MR_StackPopAction) (nextStatement : Int)
    (before after : List MR_Allocation) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) (length : bytes.length = 8) :
    MRf.StackFrame.storage_dead (fuel + 10)
      (frame literal (ptr before.length (Int.ofNat addr)) arg action nextStatement)
      (memory before after addr bytes accesses) ⟨0⟩ =
    SOut.ok (.ok (),
      (frame literal (ptr before.length (Int.ofNat addr)) arg action nextStatement).set_locals [(⟨1⟩, arg)],
      ⟨⟨before ++ (slot (Int.ofNat addr) bytes).set_live false :: after, ()⟩, accesses⟩) := by
  simp only [MRf.StackFrame.storage_dead, frame, function, SMap.index_at, SMap.get,
    SMap.getL, MR_LocalName.beq, SInt.beq, decide_true, decide_false, SOption.unwrap,
    SOut.bind_ok', layout_u64, MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align,
    SMap.remove, SMap.removeL]
  rw [concurrent_deallocate_private_slot (fuel + 4) before after addr bytes accesses length]
  rfl

/-- The second and last local is retired through the same actual model path. -/
theorem storage_dead_argument (fuel : Nat) (literal : Nat) (ret : MR_ThinPointer)
    (action : MR_StackPopAction) (nextStatement : Int)
    (before after : List MR_Allocation) (addr n : Nat) (accesses : List MR_Access) :
    MRf.StackFrame.storage_dead (fuel + 10)
      ((frame literal ret (ptr before.length (Int.ofNat addr)) action nextStatement).set_locals
        [(⟨1⟩, ptr before.length (Int.ofNat addr))])
      (memory before after addr (u64bytes n) accesses) ⟨1⟩ =
    SOut.ok (.ok (),
      (frame literal ret (ptr before.length (Int.ofNat addr)) action nextStatement).set_locals [],
      ⟨⟨before ++ (slot (Int.ofNat addr) (u64bytes n)).set_live false :: after, ()⟩, accesses⟩) := by
  simp only [MRf.StackFrame.storage_dead, frame, function, MR_StackFrame.set_locals,
    SMap.index_at, SMap.get, SMap.getL, MR_LocalName.beq, SInt.beq,
    decide_true, decide_false, SOption.unwrap, SOut.bind_ok', layout_u64,
    MRf.LayoutStrategy.expect_size, MRf.LayoutStrategy.expect_align, SMap.remove, SMap.removeL]
  rw [concurrent_deallocate_private_slot (fuel + 4) before after addr (u64bytes n) accesses (u64bytes_length n)]
  rfl

/-- Explicit state of the same single enabled MiniRust thread. -/
def single (base : MR_Machine) (stack : List MR_StackFrame) (mem : MR_ConcurrentMemory) : MR_Machine :=
  { base with mem := mem, threads := [⟨stack, .Enabled, []⟩], active_thread := 0 }

private theorem single_mem (base : MR_Machine) (stack : List MR_StackFrame) (mem : MR_ConcurrentMemory) :
    (single base stack mem).mem = mem := rfl
private theorem single_set_mem (base : MR_Machine) (stack : List MR_StackFrame) (a b : MR_ConcurrentMemory) :
    (single base stack a).set_mem b = single base stack b := rfl

theorem pop_active (fuel : Nat) (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) :
    MRf.Machine.mutate_cur_stack MR_StackFrame Unit (fuel + 1) (active base caller callee mem)
      (fun stack (_ : Unit) => match SList.pop stack with
        | (popped, rest) => SOut.bind (SOption.unwrap popped)
          (fun frame => SOut.ok (frame, rest, ()))) () =
      SOut.ok (callee, single base [caller] mem, ()) := by
  simp [MRf.Machine.mutate_cur_stack, active, single, SList.mutateAtS, SList.mutateAtNat,
    SList.pop, SList.last, SList.dropLast, SOption.unwrap, SOut.bind_ok',
    MR_Thread.set_stack, MR_Machine.set_threads]

theorem jump_single (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (mem : MR_ConcurrentMemory) (next : MR_BbName) :
    MRf.Machine.jump_to_block (fuel + 3) (single base [caller] mem) next =
      SOut.ok (.ok (), single base [(caller.set_next_block next).set_next_stmt 0] mem) := by
  simp [MRf.Machine.jump_to_block, MRf.Machine.try_mutate_cur_frame, single,
    SList.mutateAtS, SList.mutateAtNat, MRf.Thread.try_mutate_cur_frame,
    SList.is_empty, SList.len, SList.lenNat, MRf.StackFrame.jump_to_block,
    SOut.bind_ok', MR_Thread.set_stack, MR_Machine.set_threads, MR_Machine.set_mem]

/-- A name for the EXACT monadic loop body inside generated Return. It calls
    the original StorageDead; it is not a replacement machine/value evaluator. -/
def retireOne (fuel : Nat) (state : MR_StackFrame × MR_Machine) :
    SOut (SCtl (MR_StackFrame × MR_Machine) (SRes MR_TerminationInfo Unit × MR_Machine)) :=
  match SList.first (SMap.keys state.fst.locals) with
  | some localName => SOut.bind (MRf.StackFrame.storage_dead fuel state.fst state.snd.mem localName)
    (fun result => match result.fst with
      | .ok _ => SOut.ok (.next (result.2.fst, state.snd.set_mem result.2.snd))
      | .err error => SOut.ok (.ret (.err error, state.snd.set_mem result.2.snd)))
  | none => SOut.ok (.brk (state.fst, state.snd))

def deadReturnCells (world : List MR_Allocation) (retAddr argAddr value n : Nat)
    (accesses : List MR_Access) : MR_ConcurrentMemory :=
  ⟨⟨world ++ [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false,
    slot (Int.ofNat argAddr) (u64bytes n)], ()⟩, accesses⟩

def retiredCells (world : List MR_Allocation) (retAddr argAddr value n : Nat)
    (accesses : List MR_Access) : MR_ConcurrentMemory :=
  ⟨⟨world ++ [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false,
    (slot (Int.ofNat argAddr) (u64bytes n)).set_live false], ()⟩, accesses⟩

theorem retire_first (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (action : MR_StackPopAction) (nextStatement : Int)
    (world : List MR_Allocation) (retAddr argAddr value n : Nat) (accesses : List MR_Access) :
    retireOne (fuel + 10)
      (frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement,
       single base [caller] (cells world retAddr argAddr (u64bytes value) n accesses)) =
    SOut.ok (.next
      ((frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement).set_locals
          [(⟨1⟩, ptr (world.length + 1) (Int.ofNat argAddr))],
       single base [caller] (deadReturnCells world retAddr argAddr value n accesses))) := by
  simp only [retireOne, single_mem]
  change SOut.bind (MRf.StackFrame.storage_dead (fuel + 10)
    (frame literal (ptr world.length (Int.ofNat retAddr))
      (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement)
    (cells world retAddr argAddr (u64bytes value) n accesses) ⟨0⟩) _ = _
  simp only [cells]
  rw [storage_dead_return fuel literal (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement world
    [slot (Int.ofNat argAddr) (u64bytes n)] retAddr (u64bytes value) accesses (u64bytes_length value)]
  rfl

theorem retire_second (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (action : MR_StackPopAction) (nextStatement : Int)
    (world : List MR_Allocation) (retAddr argAddr value n : Nat) (accesses : List MR_Access) :
    retireOne (fuel + 10)
      ((frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement).set_locals
          [(⟨1⟩, ptr (world.length + 1) (Int.ofNat argAddr))],
       single base [caller] (deadReturnCells world retAddr argAddr value n accesses)) =
    SOut.ok (.next
      ((frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement).set_locals [],
       single base [caller] (retiredCells world retAddr argAddr value n accesses))) := by
  have hs := storage_dead_argument fuel literal (ptr world.length (Int.ofNat retAddr))
    action nextStatement (world ++ [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false])
    [] argAddr n accesses
  simp only [List.length_append, List.length_singleton] at hs
  simp only [memory, deadReturnCells, List.append_assoc, List.cons_append, List.nil_append] at hs
  simp only [retireOne, single_mem]
  change SOut.bind (MRf.StackFrame.storage_dead (fuel + 10)
    ((frame literal (ptr world.length (Int.ofNat retAddr))
      (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement).set_locals
        [(⟨1⟩, ptr (world.length + 1) (Int.ofNat argAddr))])
    (deadReturnCells world retAddr argAddr value n accesses) ⟨1⟩) _ = _
  simp only [deadReturnCells] at ⊢
  rw [hs]
  rfl

/-- Exact two-local retirement loop from Return. The loop and body fuel are
    explicit; neither successful iteration nor final memory is a premise. -/
theorem retire_loop (fuel spare : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (action : MR_StackPopAction) (nextStatement : Int)
    (world : List MR_Allocation) (retAddr argAddr value n : Nat) (accesses : List MR_Access) :
    SLoop.whileS (spare + 3)
      (frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement,
       single base [caller] (cells world retAddr argAddr (u64bytes value) n accesses))
      (retireOne (fuel + 10)) =
    SOut.ok (.brk
      ((frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action nextStatement).set_locals [],
       single base [caller] (retiredCells world retAddr argAddr value n accesses))) := by
  rw [SLoop.whileS, retire_first]
  simp only [SOut.bind_ok']
  rw [SLoop.whileS, retire_second]
  simp only [SOut.bind_ok']
  rw [SLoop.whileS]
  rfl

theorem frame_return_type (literal : Nat) (ret arg : MR_ThinPointer)
    (action : MR_StackPopAction) (pc : Int) :
    SMap.index_at MR_LocalName.beq (frame literal ret arg action pc).func.locals
      (frame literal ret arg action pc).func.ret = SOut.ok (.Int (mrIntTy false .u64)) := rfl

theorem frame_return_pointer (literal : Nat) (ret arg : MR_ThinPointer)
    (action : MR_StackPopAction) (pc : Int) :
    SMap.index_at MR_LocalName.beq (frame literal ret arg action pc).locals
      (frame literal ret arg action pc).func.ret = SOut.ok ret := rfl

end MiniRustU64Execution
