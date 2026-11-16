/- Actual two-argument generated MiniRust expression execution.
   Complete entry, return, non-vacuity and reference replay remain separate. -/
import MiniRustWord64PairFunction

noncomputable section
namespace MiniRustWord64PairExecution
open SemR MiniRustU64Function MiniRustWord64PairFunction
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def cells (world : List MR_Allocation) (retAddr leftAddr rightAddr : Nat)
    (retBytes : List MR_AbstractByte) (left right : Nat)
    (accesses : List MR_Access) : MR_ConcurrentMemory :=
  memory world [slot (Int.ofNat leftAddr) (u64bytes left),
    slot (Int.ofNat rightAddr) (u64bytes right)] retAddr retBytes accesses

def state (base : MR_Machine) (caller : MR_StackFrame) (action : MR_StackPopAction)
    (nextStatement : Int) (world : List MR_Allocation) (retAddr leftAddr rightAddr : Nat)
    (retBytes : List MR_AbstractByte) (left right : Nat)
    (accesses : List MR_Access) : MR_Machine :=
  active base caller
    (MiniRustWord64PairFunction.frame
      (ptr world.length (Int.ofNat retAddr))
      (ptr (world.length + 1) (Int.ofNat leftAddr))
      (ptr (world.length + 2) (Int.ofNat rightAddr)) action nextStatement)
    (cells world retAddr leftAddr rightAddr retBytes left right accesses)

theorem load_left (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (action : MR_StackPopAction) (nextStatement : Int) (world : List MR_Allocation)
    (retAddr leftAddr rightAddr : Nat) (retBytes : List MR_AbstractByte)
    (left right : Nat) (accesses : List MR_Access)
    (aligned : leftAddr % 8 = 0) (valid : left < modulus 64) :
    MRf.Machine.eval_value (fuel + 15)
      (state base caller action nextStatement world retAddr leftAddr rightAddr
        retBytes left right accesses) (.Load (.Local ⟨1⟩)) =
    .ok (.ok (.Int (Int.ofNat left), .Int (mrIntTy false .u64)),
      state base caller action nextStatement world retAddr leftAddr rightAddr
        retBytes left right (accesses ++ [⟨.Load, .None, Int.ofNat leftAddr, 8⟩])) := by
  have h := MiniRustWord64PairFunction.load_argument fuel base caller .left
    (ptr world.length (Int.ofNat retAddr))
    (ptr (world.length + 2) (Int.ofNat rightAddr)) action nextStatement
    (world ++ [slot (Int.ofNat retAddr) retBytes])
    [slot (Int.ofNat rightAddr) (u64bytes right)] leftAddr left accesses aligned valid
  simpa [state, cells, memory, argumentFrame, Argument.local, Local.name,
    List.append_assoc] using h

theorem load_right (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (action : MR_StackPopAction) (nextStatement : Int) (world : List MR_Allocation)
    (retAddr leftAddr rightAddr : Nat) (retBytes : List MR_AbstractByte)
    (left right : Nat) (accesses : List MR_Access)
    (aligned : rightAddr % 8 = 0) (valid : right < modulus 64) :
    MRf.Machine.eval_value (fuel + 15)
      (state base caller action nextStatement world retAddr leftAddr rightAddr
        retBytes left right accesses) (.Load (.Local ⟨2⟩)) =
    .ok (.ok (.Int (Int.ofNat right), .Int (mrIntTy false .u64)),
      state base caller action nextStatement world retAddr leftAddr rightAddr
        retBytes left right (accesses ++ [⟨.Load, .None, Int.ofNat rightAddr, 8⟩])) := by
  have h := MiniRustWord64PairFunction.load_argument fuel base caller .right
    (ptr world.length (Int.ofNat retAddr))
    (ptr (world.length + 1) (Int.ofNat leftAddr)) action nextStatement
    (world ++ [slot (Int.ofNat retAddr) retBytes,
      slot (Int.ofNat leftAddr) (u64bytes left)]) [] rightAddr right accesses aligned valid
  simpa [state, cells, memory, argumentFrame, Argument.local, Local.name,
    List.append_assoc] using h

def expression : MR_ValueExpr :=
  .BinOp (.Int .Add) (.Load (.Local ⟨1⟩)) (.Load (.Local ⟨2⟩))

/-- Both distinct runtime arguments are loaded in order. Their real access
    records, the complete surrounding allocation world and every base-machine
    field retained by the explicit single-thread boundary remain in the result. -/
theorem eval_add_expression (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (action : MR_StackPopAction) (nextStatement : Int) (world : List MR_Allocation)
    (retAddr leftAddr rightAddr : Nat) (retBytes : List MR_AbstractByte)
    (left right : Nat) (accesses : List MR_Access)
    (leftAligned : leftAddr % 8 = 0) (rightAligned : rightAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    MRf.Machine.eval_value (fuel + 20)
      (state base caller action nextStatement world retAddr leftAddr rightAddr
        retBytes left right accesses) expression =
    .ok (.ok (.Int (Int.ofNat ((left + right) % modulus 64)), .Int (mrIntTy false .u64)),
      state base caller action nextStatement world retAddr leftAddr rightAddr
        retBytes left right
        ((accesses ++ [⟨.Load, .None, Int.ofNat leftAddr, 8⟩]) ++
          [⟨.Load, .None, Int.ofNat rightAddr, 8⟩])) := by
  rw [expression, eval_binop_eq (fuel + 18),
    load_left (fuel + 4) base caller action nextStatement world retAddr leftAddr rightAddr
      retBytes left right accesses leftAligned leftValid]
  simp only [SOut.bind_ok']
  have hr := load_right (fuel + 4) base caller action nextStatement world retAddr leftAddr rightAddr
    retBytes left right (accesses ++ [⟨.Load, .None, Int.ofNat leftAddr, 8⟩])
    rightAligned rightValid
  rw [hr]
  simp only [SOut.bind_ok']
  have h := add_minirust (fuel + 15)
    (state base caller action nextStatement world retAddr leftAddr rightAddr retBytes left right
      ((accesses ++ [⟨.Load, .None, Int.ofNat leftAddr, 8⟩]) ++
        [⟨.Load, .None, Int.ofNat rightAddr, 8⟩]))
    false .u64 left right leftValid rightValid
  simp only [readAt_false] at h
  rw [h]
  rfl

def statement : MR_Statement := .Assign (.Local ⟨0⟩) expression

private theorem active_set_memory (base : MR_Machine) (caller callee : MR_StackFrame)
    (before after : MR_ConcurrentMemory) :
    (active base caller callee before).set_mem after = active base caller callee after := rfl

theorem eval_return_place (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (action : MR_StackPopAction) (nextStatement : Int) (world : List MR_Allocation)
    (retAddr leftAddr rightAddr : Nat) (retBytes : List MR_AbstractByte)
    (left right : Nat) (accesses : List MR_Access) :
    MRf.Machine.eval_place (fuel + 10)
      (state base caller action nextStatement world retAddr leftAddr rightAddr
        retBytes left right accesses) (.Local ⟨0⟩) =
    .ok (.ok (place (ptr world.length (Int.ofNat retAddr)), .Int (mrIntTy false .u64)),
      state base caller action nextStatement world retAddr leftAddr rightAddr
        retBytes left right accesses) := by
  simpa only [state, Local.name, Local.pointer] using
    eval_local fuel base caller (ptr world.length (Int.ofNat retAddr))
      (ptr (world.length + 1) (Int.ofNat leftAddr))
      (ptr (world.length + 2) (Int.ofNat rightAddr)) action nextStatement
      (cells world retAddr leftAddr rightAddr retBytes left right accesses) .returned

/-- Actual Assign writes the full64 modular sum, preserving both argument
    objects and all earlier allocation records; two Loads precede its Store. -/
theorem assign_exact (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (action : MR_StackPopAction) (nextStatement : Int) (world : List MR_Allocation)
    (retAddr leftAddr rightAddr : Nat) (retBytes : List MR_AbstractByte)
    (left right : Nat) (accesses : List MR_Access) (retLength : retBytes.length = 8)
    (retAligned : retAddr % 8 = 0) (leftAligned : leftAddr % 8 = 0)
    (rightAligned : rightAddr % 8 = 0) (leftValid : left < modulus 64)
    (rightValid : right < modulus 64) :
    MRf.Machine.eval_statement (fuel + 22)
      (state base caller action nextStatement world retAddr leftAddr rightAddr
        retBytes left right accesses) statement =
    .ok (.ok (), state base caller action nextStatement world retAddr leftAddr rightAddr
      (u64bytes ((left + right) % modulus 64)) left right
      (((accesses ++ [⟨.Load, .None, Int.ofNat leftAddr, 8⟩]) ++
        [⟨.Load, .None, Int.ofNat rightAddr, 8⟩]) ++
          [⟨.Store, .None, Int.ofNat retAddr, 8⟩])) := by
  have he := eval_add_expression (fuel + 1) base caller action nextStatement world
    retAddr leftAddr rightAddr retBytes left right accesses
    leftAligned rightAligned leftValid rightValid
  simp only [statement, MRf.Machine.eval_statement]
  rw [eval_return_place (fuel + 11)]
  simp only [SOut.bind_ok']
  rw [he]
  simp only [SOut.bind_ok', MRf.Machine.place_store, place, SBool.not]
  rw [typed_store_alignment_one (fuel + 10) _ world.length retAddr _ _ retAligned]
  have hs := typed_store_u64 (fuel + 10)
    (state base caller action nextStatement world retAddr leftAddr rightAddr retBytes left right
      ((accesses ++ [⟨.Load, .None, Int.ofNat leftAddr, 8⟩]) ++
        [⟨.Load, .None, Int.ofNat rightAddr, 8⟩]))
    world [slot (Int.ofNat leftAddr) (u64bytes left),
      slot (Int.ofNat rightAddr) (u64bytes right)] retAddr ((left + right) % modulus 64)
    retBytes ((accesses ++ [⟨.Load, .None, Int.ofNat leftAddr, 8⟩]) ++
      [⟨.Load, .None, Int.ofNat rightAddr, 8⟩]) retLength retAligned
    (Nat.mod_lt _ (by decide))
  simp only [state, cells, active_set_memory] at hs ⊢
  rw [hs]
  rfl

end MiniRustWord64PairExecution
