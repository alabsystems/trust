/- Actual concurrent allocator and frame-entry composition. -/
import MiniRustU64Call
import MiniRustAllocate8Safety
noncomputable section
namespace MiniRustU64AllocatedCall
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Call MiniRustU64Entry
open MiniRustAllocate8Safety
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem choice_map {α β : Type} (bound : Int) (allowed : Int → Bool)
    (make : Int → α) (next : α → SOut β) (other : Int → β)
    (law : ∀ addr, next (make addr) = .ok (other addr)) :
    (choiceTree bound allowed make).bind next = choiceTree bound allowed other := by
  change SOut.pick _ = SOut.pick _
  apply congrArg SOut.pick
  funext index
  dsimp only
  cases h1 : SInt.blt (candidate index) bound <;>
    cases h2 : allowed (candidate index) <;> simp only [h1, h2, SOut.bind_ok']
  exact law (candidate index)

def allocatedConcurrent8 (world : List MR_Allocation) (accesses : List MR_Access)
    (addr : Int) : SRes MR_TerminationInfo MR_ThinPointer × MR_ConcurrentMemory :=
  (.ok (ptr world.length addr), ⟨⟨world ++ [slot addr uninit8], ()⟩, accesses⟩)

def concurrent8Tree (world : List MR_Allocation) (accesses : List MR_Access) :=
  choiceTree (Int.ofNat (modulus 64)) (allocationAllowed world)
    (allocatedConcurrent8 world accesses)

/-- Full original concurrent allocator: no access-log or outside-world loss. -/
theorem concurrent8_exact (fuel : Nat) (world : List MR_Allocation)
    (accesses : List MR_Access) :
    MRf.ConcurrentMemory.allocate (fuel + 6) ⟨⟨world, ()⟩, accesses⟩ .Stack 8 8 =
      concurrent8Tree world accesses := by
  simp only [MRf.ConcurrentMemory.allocate, MRf.BasicMemory.Memory.allocate]
  rw [allocate8_exact fuel]
  simp only [MiniRustU64Entry.bind_associative]
  unfold allocate8Tree concurrent8Tree
  apply choice_map
  intro addr
  rfl

def address (index : Nat) : Nat := (index + 1) * 8

theorem address_aligned (index : Nat) : address index % 8 = 0 := by simp [address]

theorem uninit8_length : uninit8.length = 8 := rfl

/-- Actual full-width argument initialization after the two genuine appends. -/
theorem argument_initialized (fuel : Nat) (machine : MR_Machine)
    (world : List MR_Allocation) (retAddr argAddr input : Nat) (accesses : List MR_Access)
    (argAligned : argAddr % 8 = 0) (inputValid : input < modulus 64) :
    MRf.Machine.typed_store (fuel + 19)
      (machine.set_mem ⟨⟨world ++ [slot (Int.ofNat retAddr) uninit8,
        slot (Int.ofNat argAddr) uninit8], ()⟩, accesses⟩)
      (ptr (world.length + 1) (Int.ofNat argAddr)) (.Int (Int.ofNat input))
      (.Int (mrIntTy false .u64)) 8 .None =
      .ok (.ok (), machine.set_mem (cells world retAddr argAddr uninit8 input
        (accesses ++ [⟨.Store, .None, Int.ofNat argAddr, 8⟩]))) := by
  have h := typed_store_u64 (fuel + 9) machine (world ++ [slot (Int.ofNat retAddr) uninit8]) []
    argAddr input uninit8 accesses uninit8_length argAligned inputValid
  simpa [memory, cells, List.append_assoc] using h

/-- The SAME guarded choice, retaining its original index for later witnesses. -/
def selectedChoice {α : Type} (bound : Int) (allowed : Int → Bool)
    (next : Nat → SOut α) : SOut α :=
  .pick (fun index => match SInt.blt (candidate index) bound with
    | false => .reject
    | true => match allowed (candidate index) with
      | false => .reject
      | true => next index)

theorem choice_index_bind {α β : Type} (bound : Int) (allowed : Int → Bool)
    (make : Int → α) (next : α → SOut β) :
    (choiceTree bound allowed make).bind next =
      selectedChoice bound allowed (fun index => next (make (candidate index))) := by
  apply congrArg SOut.pick
  funext index
  dsimp only
  cases h1 : SInt.blt (candidate index) bound <;>
    cases h2 : allowed (candidate index) <;> rfl

/-- Two genuine allocation choices followed by the real typed argument store.
    No filter is erased, including ranges and live-allocation overlaps. -/
def frameTree (world : List MR_Allocation) (accesses : List MR_Access)
    (literal input : Nat) (action : MR_StackPopAction) (machine : MR_Machine) :
    SOut (SRes MR_TerminationInfo MR_StackFrame × MR_Machine) :=
  selectedChoice (Int.ofNat (modulus 64)) (allocationAllowed world) (fun retIndex =>
    selectedChoice (Int.ofNat (modulus 64))
      (allocationAllowed (world ++ [slot (Int.ofNat (address retIndex)) uninit8])) (fun argIndex =>
      .ok (.ok (frame literal
        (ptr world.length (Int.ofNat (address retIndex)))
        (ptr (world.length + 1) (Int.ofNat (address argIndex))) action 0),
        machine.set_mem (cells world (address retIndex) (address argIndex) uninit8 input
          (accesses ++ [⟨.Store, .None, Int.ofNat (address argIndex), 8⟩])))))

/-- Actual frame construction for the complete valid U64 input domain.
    The conclusion is the full original choice tree, not assumed success. -/
theorem frame_plan_exact (fuel literal input : Nat) (world : List MR_Allocation)
    (accesses : List MR_Access) (action : MR_StackPopAction) (machine : MR_Machine)
    (inputValid : input < modulus 64) :
    framePlan (fuel + 18) literal action
      (machine.set_mem ⟨⟨world, ()⟩, accesses⟩) (.Int (Int.ofNat input)) =
      frameTree world accesses literal input action machine := by
  unfold framePlan framePlanWith
  simp only [memory_after_set]
  rw [concurrent8_exact (fuel + 12)]
  unfold concurrent8Tree
  rw [choice_index_bind]
  unfold frameTree
  apply congrArg (selectedChoice (Int.ofNat (modulus 64)) (allocationAllowed world))
  funext retIndex
  simp only [allocatedConcurrent8, candidate_nat, address, SOut.bind_ok', set_memory_last]
  rw [concurrent8_exact (fuel + 12)]
  unfold concurrent8Tree
  rw [choice_index_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (world ++ [slot (Int.ofNat ((retIndex + 1) * 8)) uninit8])))
  funext argIndex
  simp only [allocatedConcurrent8, candidate_nat, SOut.bind_ok', set_memory_last,
    List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
  simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.add_assoc, Nat.zero_add]
  have hi := argument_initialized fuel machine world ((retIndex + 1) * 8) ((argIndex + 1) * 8)
    input accesses (by simp) inputValid
  rw [hi]
  rfl

theorem selected_bind {α β : Type} (bound : Int) (allowed : Int → Bool)
    (next : Nat → SOut α) (finish : α → SOut β) :
    (selectedChoice bound allowed next).bind finish =
      selectedChoice bound allowed (fun index => (next index).bind finish) := by
  apply congrArg SOut.pick
  funext index
  dsimp only
  cases h1 : SInt.blt (candidate index) bound <;>
    cases h2 : allowed (candidate index) <;> rfl

theorem single_memory_last (base : MR_Machine) (caller : MR_StackFrame)
    (first last : MR_ConcurrentMemory) :
    (single base [caller] first).set_mem last = single base [caller] last := rfl

def callTree (world : List MR_Allocation) (accesses : List MR_Access)
    (literal input : Nat) (action : MR_StackPopAction)
    (base : MR_Machine) (caller : MR_StackFrame) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  selectedChoice (Int.ofNat (modulus 64)) (allocationAllowed world) (fun retIndex =>
    selectedChoice (Int.ofNat (modulus 64))
      (allocationAllowed (world ++ [slot (Int.ofNat (address retIndex)) uninit8])) (fun argIndex =>
      .ok (.ok (), active base caller (frame literal
        (ptr world.length (Int.ofNat (address retIndex)))
        (ptr (world.length + 1) (Int.ofNat (address argIndex))) action 0)
        (cells world (address retIndex) (address argIndex) uninit8 input
          (accesses ++ [⟨.Store, .None, Int.ofNat (address argIndex), 8⟩])))))

/-- Real eval_call, two allocations, full argument initialization, and actual
    stack push. Both guarded choice layers remain, with no success premise. -/
theorem call_tree_exact (fuel literal input : Nat) (world : List MR_Allocation)
    (accesses : List MR_Access) (base : MR_Machine) (caller : MR_StackFrame)
    (ret : MR_ThinPointer) (next unwind : Option MR_BbName)
    (inputValid : input < modulus 64) :
    MRf.Machine.eval_call (fuel + 21) (single base [caller] ⟨⟨world, ()⟩, accesses⟩)
      (function literal) .Rust [(.Int (Int.ofNat input), .Int (mrIntTy false .u64))]
      (place ret, .Int (mrIntTy false .u64)) next unwind =
      callTree world accesses literal input (.BackToCaller next unwind ret) base caller := by
  have hc := call_plan (fuel + 10) literal (single base [caller] ⟨⟨world, ()⟩, accesses⟩)
    (.Int (Int.ofNat input)) ret next unwind
  simp only [Nat.add_assoc] at hc
  rw [hc]
  have hf := frame_plan_exact fuel literal input world accesses (.BackToCaller next unwind ret)
    (single base [caller] ⟨⟨world, ()⟩, accesses⟩) inputValid
  simp only [single_memory_last] at hf
  rw [hf]
  unfold frameTree callTree
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64)) (allocationAllowed world))
  funext retIndex
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (world ++ [slot (Int.ofNat (address retIndex)) uninit8])))
  funext argIndex
  simp only [SOut.bind_ok', single_memory_last]
  rw [finish_call_active (fuel + 19)]

end MiniRustU64AllocatedCall
