/- Actual initialization of both runtime arguments after three allocations.
   Every old allocation and access is retained; no source or ABI authority. -/
import MiniRustWord64PairCall
import MiniRustWord64PairExecution
import MiniRustU64AllocatedCall
noncomputable section
namespace MiniRustWord64PairAllocatedCall
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64AllocatedCall
  MiniRustWord64PairExecution MiniRustAllocate8Safety
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def freshCells (world : List MR_Allocation) (retAddr leftAddr rightAddr : Nat)
    (leftBytes rightBytes : List MR_AbstractByte) (accesses : List MR_Access) :
    MR_ConcurrentMemory :=
  ⟨⟨world ++ [slot (Int.ofNat retAddr) uninit8,
    slot (Int.ofNat leftAddr) leftBytes, slot (Int.ofNat rightAddr) rightBytes], ()⟩, accesses⟩

theorem initialize_left (fuel : Nat) (machine : MR_Machine)
    (world : List MR_Allocation) (retAddr leftAddr rightAddr left : Nat)
    (accesses : List MR_Access) (aligned : leftAddr % 8 = 0)
    (valid : left < modulus 64) :
    MRf.Machine.typed_store (fuel + 10)
      (machine.set_mem (freshCells world retAddr leftAddr rightAddr uninit8 uninit8 accesses))
      (ptr (world.length + 1) (Int.ofNat leftAddr)) (.Int (Int.ofNat left))
      (.Int (mrIntTy false .u64)) 8 .None =
    .ok (.ok (), machine.set_mem
      (freshCells world retAddr leftAddr rightAddr (u64bytes left) uninit8
        (accesses ++ [⟨.Store, .None, Int.ofNat leftAddr, 8⟩]))) := by
  have h := typed_store_u64 fuel machine (world ++ [slot (Int.ofNat retAddr) uninit8])
    [slot (Int.ofNat rightAddr) uninit8] leftAddr left uninit8 accesses
    uninit8_length aligned valid
  simpa [freshCells, memory, List.append_assoc] using h

theorem initialize_right (fuel : Nat) (machine : MR_Machine)
    (world : List MR_Allocation) (retAddr leftAddr rightAddr left right : Nat)
    (accesses : List MR_Access) (aligned : rightAddr % 8 = 0)
    (valid : right < modulus 64) :
    MRf.Machine.typed_store (fuel + 10)
      (machine.set_mem (freshCells world retAddr leftAddr rightAddr (u64bytes left) uninit8 accesses))
      (ptr (world.length + 2) (Int.ofNat rightAddr)) (.Int (Int.ofNat right))
      (.Int (mrIntTy false .u64)) 8 .None =
    .ok (.ok (), machine.set_mem
      (MiniRustWord64PairExecution.cells world retAddr leftAddr rightAddr uninit8 left right
        (accesses ++ [⟨.Store, .None, Int.ofNat rightAddr, 8⟩]))) := by
  have h := typed_store_u64 fuel machine
    (world ++ [slot (Int.ofNat retAddr) uninit8, slot (Int.ofNat leftAddr) (u64bytes left)])
    [] rightAddr right uninit8 accesses uninit8_length aligned valid
  simpa [freshCells, MiniRustWord64PairExecution.cells, memory, List.append_assoc] using h

def frameTree (world : List MR_Allocation) (accesses : List MR_Access)
    (left right : Nat) (action : MR_StackPopAction) (machine : MR_Machine) :
    SOut (SRes MR_TerminationInfo MR_StackFrame × MR_Machine) :=
  selectedChoice (Int.ofNat (modulus 64)) (allocationAllowed world) (fun retIndex =>
    selectedChoice (Int.ofNat (modulus 64))
      (allocationAllowed (world ++ [slot (Int.ofNat (address retIndex)) uninit8])) (fun leftIndex =>
      selectedChoice (Int.ofNat (modulus 64))
        (allocationAllowed (world ++ [slot (Int.ofNat (address retIndex)) uninit8,
          slot (Int.ofNat (address leftIndex)) uninit8])) (fun rightIndex =>
        .ok (.ok (MiniRustWord64PairFunction.frame
          (ptr world.length (Int.ofNat (address retIndex)))
          (ptr (world.length + 1) (Int.ofNat (address leftIndex)))
          (ptr (world.length + 2) (Int.ofNat (address rightIndex))) action 0),
          machine.set_mem (MiniRustWord64PairExecution.cells world
            (address retIndex) (address leftIndex) (address rightIndex) uninit8 left right
            ((accesses ++ [⟨.Store, .None, Int.ofNat (address leftIndex), 8⟩]) ++
              [⟨.Store, .None, Int.ofNat (address rightIndex), 8⟩]))))))

/-- Exact three-choice allocator tree and ordered checked argument stores.
    Bounds and every overlap rejection are preserved. -/
theorem frame_plan_exact (fuel left right : Nat) (world : List MR_Allocation)
    (accesses : List MR_Access) (action : MR_StackPopAction) (machine : MR_Machine)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    MiniRustWord64PairCall.framePlan (fuel + 18) action
      (machine.set_mem ⟨⟨world, ()⟩, accesses⟩)
      (.Int (Int.ofNat left)) (.Int (Int.ofNat right)) =
      frameTree world accesses left right action machine := by
  unfold MiniRustWord64PairCall.framePlan MiniRustWord64PairCall.framePlanWith
  simp only [MiniRustU64Call.memory_after_set]
  rw [concurrent8_exact (fuel + 12)]
  unfold concurrent8Tree
  rw [choice_index_bind]
  unfold frameTree
  apply congrArg (selectedChoice (Int.ofNat (modulus 64)) (allocationAllowed world))
  funext retIndex
  simp only [allocatedConcurrent8, candidate_nat, address, SOut.bind_ok', MiniRustU64Call.set_memory_last]
  rw [concurrent8_exact (fuel + 12)]
  unfold concurrent8Tree
  rw [choice_index_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (world ++ [slot (Int.ofNat ((retIndex + 1) * 8)) uninit8])))
  funext leftIndex
  simp only [allocatedConcurrent8, candidate_nat, SOut.bind_ok', MiniRustU64Call.set_memory_last]
  rw [concurrent8_exact (fuel + 12)]
  unfold concurrent8Tree
  rw [choice_index_bind]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (world ++ [slot (Int.ofNat ((retIndex + 1) * 8)) uninit8,
      slot (Int.ofNat ((leftIndex + 1) * 8)) uninit8])))
  funext rightIndex
  simp only [allocatedConcurrent8, candidate_nat, SOut.bind_ok', MiniRustU64Call.set_memory_last,
    List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
  simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.add_assoc, Nat.zero_add]
  have hl := initialize_left (fuel + 9) machine world ((retIndex + 1) * 8)
    ((leftIndex + 1) * 8) ((rightIndex + 1) * 8) left accesses (by simp) leftValid
  change MRf.Machine.typed_store (fuel + 19) _ _ _ _ _ _ = _ at hl
  simp only [freshCells] at hl
  rw [hl]
  simp only [SOut.bind_ok', SRes.unwrap]
  have hr := initialize_right (fuel + 9) machine world ((retIndex + 1) * 8)
    ((leftIndex + 1) * 8) ((rightIndex + 1) * 8) left right
    (accesses ++ [⟨.Store, .None, Int.ofNat ((leftIndex + 1) * 8), 8⟩]) (by simp) rightValid
  simp only [freshCells] at hr
  rw [hr]
  simp only [SOut.bind_ok', SRes.unwrap, List.append_assoc, List.cons_append, List.nil_append]

def callTree (world : List MR_Allocation) (accesses : List MR_Access)
    (left right : Nat) (action : MR_StackPopAction) (base : MR_Machine) (caller : MR_StackFrame) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  selectedChoice (Int.ofNat (modulus 64)) (allocationAllowed world) (fun retIndex =>
    selectedChoice (Int.ofNat (modulus 64))
      (allocationAllowed (world ++ [slot (Int.ofNat (address retIndex)) uninit8])) (fun leftIndex =>
      selectedChoice (Int.ofNat (modulus 64))
        (allocationAllowed (world ++ [slot (Int.ofNat (address retIndex)) uninit8,
          slot (Int.ofNat (address leftIndex)) uninit8])) (fun rightIndex =>
        .ok (.ok (), active base caller (MiniRustWord64PairFunction.frame
          (ptr world.length (Int.ofNat (address retIndex)))
          (ptr (world.length + 1) (Int.ofNat (address leftIndex)))
          (ptr (world.length + 2) (Int.ofNat (address rightIndex))) action 0)
          (MiniRustWord64PairExecution.cells world
            (address retIndex) (address leftIndex) (address rightIndex) uninit8 left right
            ((accesses ++ [⟨.Store, .None, Int.ofNat (address leftIndex), 8⟩]) ++
              [⟨.Store, .None, Int.ofNat (address rightIndex), 8⟩]))))))

theorem call_tree_exact (fuel left right : Nat) (world : List MR_Allocation)
    (accesses : List MR_Access) (base : MR_Machine) (caller : MR_StackFrame)
    (ret : MR_ThinPointer) (next unwind : Option MR_BbName)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    MRf.Machine.eval_call (fuel + 21) (single base [caller] ⟨⟨world, ()⟩, accesses⟩)
      MiniRustWord64PairFunction.function .Rust
      [(.Int (Int.ofNat left), .Int (mrIntTy false .u64)),
       (.Int (Int.ofNat right), .Int (mrIntTy false .u64))]
      (place ret, .Int (mrIntTy false .u64)) next unwind =
      callTree world accesses left right (.BackToCaller next unwind ret) base caller := by
  have hc := MiniRustWord64PairCall.call_plan (fuel + 10)
    (single base [caller] ⟨⟨world, ()⟩, accesses⟩)
    (.Int (Int.ofNat left)) (.Int (Int.ofNat right)) ret next unwind
  simp only [Nat.add_assoc] at hc
  rw [hc]
  have hf := frame_plan_exact fuel left right world accesses (.BackToCaller next unwind ret)
    (single base [caller] ⟨⟨world, ()⟩, accesses⟩) leftValid rightValid
  simp only [single_memory_last] at hf
  rw [hf]
  unfold frameTree callTree
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64)) (allocationAllowed world))
  funext retIndex
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (world ++ [slot (Int.ofNat (address retIndex)) uninit8])))
  funext leftIndex
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (world ++ [slot (Int.ofNat (address retIndex)) uninit8,
      slot (Int.ofNat (address leftIndex)) uninit8])))
  funext rightIndex
  simp only [SOut.bind_ok', single_memory_last]
  rw [MiniRustU64Call.finish_call_active (fuel + 19)]

end MiniRustWord64PairAllocatedCall
