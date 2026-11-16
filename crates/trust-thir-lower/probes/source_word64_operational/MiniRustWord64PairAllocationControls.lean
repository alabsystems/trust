/- Concrete branch controls for the unchanged allocator, not allocation axioms. -/
import MiniRustWord64PairAllocatedCall
noncomputable section
namespace MiniRustWord64PairAllocationControls
open SemR MiniRustU64Function MiniRustU64AllocatedCall MiniRustAllocate8Safety
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem fresh_allocation_accepted (fuel : Nat) :
    SOut.runOracle (fun _ => 0) (fun _ => 0)
      (MRf.ConcurrentMemory.allocate (fuel + 6) ⟨⟨[], ()⟩, []⟩ .Stack 8 8) =
      .ok (.ok (ptr 0 8), ⟨⟨[slot 8 uninit8], ()⟩, []⟩) := by
  rw [concurrent8_exact]
  rfl

theorem live_overlap_rejected (fuel : Nat) :
    SOut.runOracle (fun _ => 0) (fun _ => 0)
      (MRf.ConcurrentMemory.allocate (fuel + 6) ⟨⟨[slot 8 uninit8], ()⟩, []⟩ .Stack 8 8) =
      .reject := by
  rw [concurrent8_exact]
  rfl

theorem out_of_range_rejected (fuel : Nat) :
    SOut.runOracle (fun _ => modulus 64) (fun _ => 0)
      (MRf.ConcurrentMemory.allocate (fuel + 6) ⟨⟨[], ()⟩, []⟩ .Stack 8 8) =
      .reject := by
  rw [concurrent8_exact]
  rfl

#print axioms fresh_allocation_accepted
#print axioms live_overlap_rejected
#print axioms out_of_range_rejected
end MiniRustWord64PairAllocationControls
