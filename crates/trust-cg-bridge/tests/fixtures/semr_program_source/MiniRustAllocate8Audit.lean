/- Guard and axiom controls for the actual generated allocator facts. -/
import MiniRustAllocate8Room

noncomputable section
namespace MiniRustAllocate8Safety
open SemR MiniRustU64Function MiniRustU64Entry
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem candidate_natural_aligned (index : Nat) :
    ∃ addr : Nat, 0 < addr ∧ addr % 8 = 0 ∧ candidate index = Int.ofNat addr := by
  refine ⟨(index + 1) * 8, ?_, ?_, candidate_nat index⟩
  · omega
  · simp

theorem live_zero_same_address_overlaps (addr : Int) :
    overlap ⟨[], addr, 8, .Stack, true, ()⟩ addr = true := by
  simp [overlap, SInt.ble, SInt.beq]

theorem refused_of_overlap (world : List MR_Allocation) (addr : Int)
    (hs : anyOverlap world addr = true) : allocationAllowed world addr = false := by
  cases hp : SInt.ble addr 0 <;>
    cases hr : SInt.beq (rem8 addr) 0 <;>
    cases hb : inRange false 64 (addr + 8) <;>
    simp only [allocationAllowed, hp, hr, hb, hs, SBool.not, Bool.false_eq_true,
      ↓reduceIte]

attribute [local irreducible] allocationAllowed

theorem live_zero_same_address_refused (index : Nat) :
    allocationAllowed [⟨[], candidate index, 8, .Stack, true, ()⟩] (candidate index) = false := by
  apply refused_of_overlap
  simp only [anyOverlap, live_zero_same_address_overlaps]
  rfl

theorem adjacent_nonempty_does_not_overlap (addr : Int) :
    overlap ⟨uninit8, addr, 8, .Stack, true, ()⟩ (addr + 8) = false := by
  apply (overlap_false_iff _ _).mpr
  simp only [uninit8_length]
  change (addr + 8 ≤ addr + 8 ∨ (addr + 8) + 8 ≤ addr) ∧ addr ≠ addr + 8
  constructor
  · left; omega
  · omega

theorem upper_endpoint_out_of_range (width : Nat) :
    inRange false width (Int.ofNat (modulus width)) = false := by
  simp [inRange]

theorem refused_of_bound (world : List MR_Allocation) (addr : Int)
    (hb : inRange false 64 (addr + 8) = false) : allocationAllowed world addr = false := by
  unfold allocationAllowed
  cases hp : SInt.ble addr 0 <;> cases hr : SInt.beq (rem8 addr) 0 <;>
    simp only [hb, SBool.not, Bool.false_eq_true, ↓reduceIte]

theorem exact_end_boundary_refused (world : List MR_Allocation) (addr : Int)
    (atEnd : addr + 8 = Int.ofNat (modulus 64)) : allocationAllowed world addr = false := by
  apply refused_of_bound
  rw [atEnd]
  exact upper_endpoint_out_of_range 64

theorem dead_outside_record_does_not_block (index : Nat)
    (room : candidate index + 8 < Int.ofNat (modulus 64)) :
    allocationAllowed [⟨[], candidate index, 8, .Stack, false, ()⟩] (candidate index) = true := by
  apply allowed_of_interval _ index _ room
  intro old member live
  have same := List.mem_singleton.mp member
  subst old
  exact Bool.noConfusion live

/-- This checks a non-vacuous concrete room instance against the original
    operation through the ordinary oracle, rather than a success assumption. -/
theorem empty_world_constructive (fuel : Nat) (π : List Nat → Nat) :
    SOut.runOracle (fun _ => 0) π
      (MRf.BasicMemory.allocate (fuel + 4) ⟨[], ()⟩ .Stack 8 8 () ()) =
      .ok (allocated8 [] .Stack (candidate 0)) := by
  apply allocate8_room fuel [] .Stack 0 _ _ π
  · simp [Below]
  · decide

#print axioms allocate8_exact
#print axioms allocate8_every
#print axioms allocate8_room
#print axioms two_allowed_from_high_water
#print axioms live_zero_same_address_refused
#print axioms exact_end_boundary_refused
#print axioms empty_world_constructive

end MiniRustAllocate8Safety
