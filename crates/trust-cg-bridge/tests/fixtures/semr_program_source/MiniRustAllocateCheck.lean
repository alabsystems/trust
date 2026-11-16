/- Actual generated allocator controls for program startup. Wrong claims below
   are proposition definitions; the independent kernel must reject the real
   proof at each changed goal. No rejected branch is assumed successful. -/
import MiniRustAllocate

noncomputable section
namespace MiniRustAllocateCheck
open SemR MiniRustU64Function MiniRustAllocate
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def RightLaw : Prop :=
  ∀ (fuel size align : Nat) (world : List MR_Allocation) (kind : MR_AllocationKind),
    MRf.BasicMemory.allocate (fuel + 4) ⟨world, ()⟩ kind
      (size : Int) ((align + 1 : Nat) : Int) () () = tree size (align + 1) world kind

theorem right_law : RightLaw := allocate_exact

theorem existing_eight_preserved (world : List MR_Allocation) (kind : MR_AllocationKind) :
    tree 8 8 world kind = MiniRustAllocate8Safety.allocate8Tree world kind := by
  exact (allocate_exact 0 8 7 world kind).symm.trans
    (MiniRustAllocate8Safety.allocate8_exact 0 world kind)

def zeroSlot (live : Bool) : MR_Allocation := ⟨[], 1, 1, .Function, live, ()⟩
def first : List Nat → Nat := fun _ => 0

def RightZero : Prop := ∀ (fuel : Nat) (π : List Nat → Nat),
  SOut.runOracle first π
    (MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Function 0 1 () ()) =
      .ok (allocated 0 1 [] .Function 1)

theorem right_zero : RightZero := by
  intro fuel π
  rw [show MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Function 0 1 () () = tree 0 1 [] .Function by
    simpa only [Int.ofNat_eq_natCast] using allocate_exact fuel 0 0 [] .Function]
  rfl

def WrongZeroOmitted : Prop := ∀ (fuel : Nat) (π : List Nat → Nat),
  SOut.runOracle first π
    (MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Function 0 1 () ()) =
      .ok (.ok (ptr 0 1), ⟨[], ()⟩)

def RightLiveCollision : Prop := ∀ (fuel : Nat) (π : List Nat → Nat),
  SOut.runOracle first π
    (MRf.BasicMemory.allocate (fuel + 4) ⟨[zeroSlot true], ()⟩ .Function 0 1 () ()) = .reject

theorem right_live_collision : RightLiveCollision := by
  intro fuel π
  rw [show MRf.BasicMemory.allocate (fuel + 4) ⟨[zeroSlot true], ()⟩ .Function 0 1 () () = tree 0 1 [zeroSlot true] .Function by
    simpa only [Int.ofNat_eq_natCast] using allocate_exact fuel 0 0 [zeroSlot true] .Function]
  rfl

def WrongLiveReuse : Prop := ∀ (fuel : Nat) (π : List Nat → Nat),
  SOut.runOracle first π
    (MRf.BasicMemory.allocate (fuel + 4) ⟨[zeroSlot true], ()⟩ .Function 0 1 () ()) =
      .ok (allocated 0 1 [zeroSlot true] .Function 1)

def RightRetiredReuse : Prop := ∀ (fuel : Nat) (π : List Nat → Nat),
  SOut.runOracle first π
    (MRf.BasicMemory.allocate (fuel + 4) ⟨[zeroSlot false], ()⟩ .Function 0 1 () ()) =
      .ok (allocated 0 1 [zeroSlot false] .Function 1)

theorem right_retired_reuse : RightRetiredReuse := by
  intro fuel π
  rw [show MRf.BasicMemory.allocate (fuel + 4) ⟨[zeroSlot false], ()⟩ .Function 0 1 () () = tree 0 1 [zeroSlot false] .Function by
    simpa only [Int.ofNat_eq_natCast] using allocate_exact fuel 0 0 [zeroSlot false] .Function]
  rfl

def WrongRetiredBlocked : Prop := ∀ (fuel : Nat) (π : List Nat → Nat),
  SOut.runOracle first π
    (MRf.BasicMemory.allocate (fuel + 4) ⟨[zeroSlot false], ()⟩ .Function 0 1 () ()) = .reject

def RightOversize : Prop := ∀ (fuel : Nat),
  MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Stack (Int.ofNat (modulus 63)) 8 () () =
    SOut.ok (.err (.Ub "asking for a too large allocation"), ⟨[], ()⟩)

theorem right_oversize : RightOversize := by
  intro fuel
  rw [show MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Stack (Int.ofNat (modulus 63)) 8 () () = tree (modulus 63) 8 [] .Stack by
    simpa only [Int.ofNat_eq_natCast] using allocate_exact fuel (modulus 63) 7 [] .Stack]
  rfl

def WrongOversizeNoBehavior : Prop := ∀ (fuel : Nat),
  MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Stack (Int.ofNat (modulus 63)) 8 () () =
    SOut.reject

def lastCandidate : List Nat → Nat := fun _ => modulus 64 - 2

def RightStrictEnd : Prop := ∀ (fuel : Nat) (π : List Nat → Nat),
  SOut.runOracle lastCandidate π
    (MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Stack 1 1 () ()) = .reject

theorem right_strict_end : RightStrictEnd := by
  intro fuel π
  rw [show MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Stack 1 1 () () = tree 1 1 [] .Stack by
    simpa only [Int.ofNat_eq_natCast] using allocate_exact fuel 1 0 [] .Stack]
  rfl

def WrongEndInclusive : Prop := ∀ (fuel : Nat) (π : List Nat → Nat),
  SOut.runOracle lastCandidate π
    (MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Stack 1 1 () ()) =
      .ok (allocated 1 1 [] .Stack (Int.ofNat (modulus 64 - 1)))

def RightZeroAlignment : Prop := ∀ (fuel : Nat),
  MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Stack 8 0 () () =
    SOut.panic "attempt to divide by zero"

theorem right_zero_alignment : RightZeroAlignment := by
  intro fuel
  rfl

def WrongZeroAlignmentReject : Prop := ∀ (fuel : Nat),
  MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Stack 8 0 () () = SOut.reject

#print axioms right_law
#print axioms right_zero
#print axioms right_live_collision
#print axioms right_retired_reuse
#print axioms right_oversize
#print axioms right_strict_end
#print axioms right_zero_alignment

end MiniRustAllocateCheck
