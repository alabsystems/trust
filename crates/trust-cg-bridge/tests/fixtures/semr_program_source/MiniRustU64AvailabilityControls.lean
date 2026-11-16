/- Inhabited actual full-function execution and an invalid scheduler control. -/
import MiniRustU64Availability
import MiniRustU64Controls
noncomputable section
namespace MiniRustU64AvailabilityControls
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Entry MiniRustU64Call MiniRustU64AllocatedCall MiniRustU64Run
  MiniRustU64Correspondence MiniRustU64Availability MiniRustAllocate8Safety
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def outside : List MR_Allocation := [slot 16 (u64bytes 0)]

theorem concrete_high_water : Below (callerWorld [] outside 8 uninit8) (8 * 3) := by
  intro old member _
  simp [callerWorld, outside] at member
  rcases member with rfl | rfl <;>
    simp [slot, MiniRustAllocate8Safety.uninit8_length, u64bytes_length]

/-- One real model state works for EVERY full64 input, not sampled agreement. -/
theorem concrete_full64_available (fuel input : Nat) (inputValid : input < modulus 64)
    (π : List Nat → Nat) :
    SOut.runOracle (entryOracle 3) π
      (enterAndRun fuel 7 input MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
        [] outside 8 uninit8 []) =
      .ok (.ok (), exitState MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
        [] outside 8 32 40 ((input + 7) % modulus 64) input) := by
  exact full_function_available fuel 7 input MiniRustU64Controls.base MiniRustU64Controls.caller
    ⟨0⟩ [] outside 8 uninit8 [] (by rfl) (by decide) inputValid (by decide) 3
    concrete_high_water (by decide) π

theorem actual_maximum_input_wrap (fuel : Nat) (π : List Nat → Nat) :
    SOut.runOracle (entryOracle 3) π
      (enterAndRun fuel 7 (modulus 64 - 1) MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
        [] outside 8 uninit8 []) =
      .ok (.ok (), exitState MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
        [] outside 8 32 40 6 (modulus 64 - 1)) := by
  have h := concrete_full64_available fuel (modulus 64 - 1) (by decide) π
  rw [MiniRustU64Controls.full64_wrap_boundary] at h
  exact h

def invalidThreadOracle (k : Nat) : List Nat → Nat
  | [] => k
  | [_] => k + 1
  | _ => 1

/-- The original scheduler rejects index1; it is not silently forced to0. -/
theorem invalid_scheduler_refuses (fuel input : Nat) (inputValid : input < modulus 64)
    (π : List Nat → Nat) :
    SOut.runOracle (invalidThreadOracle 3) π
      (enterAndRun fuel 7 input MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
        [] outside 8 uninit8 []) = .reject := by
  rw [full_tree_exact fuel 7 input MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
    [] outside 8 uninit8 [] (by rfl) (by decide) inputValid (by decide)]
  have firstUpper := candidate_upper 3 (by decide)
  have secondUpper := candidate_upper 4 (by decide)
  have gates := two_allowed_from_high_water (callerWorld [] outside 8 uninit8) .Stack 3
    concrete_high_water (by decide)
  have secondAllowed : allocationAllowed (callerWorld [] outside 8 uninit8 ++
      [slot (Int.ofNat (address 3)) uninit8]) (candidate 4) = true := by
    simpa only [candidate_nat, slot, address] using gates.2
  unfold fullTree
  rw [selected_run _ _ _ (invalidThreadOracle 3) π firstUpper gates.1]
  rw [show invalidThreadOracle 3 [] = 3 from rfl]
  rw [selected_run _ _ _ (fun history => invalidThreadOracle 3 (3 :: history))
    (fun history => π (3 :: history)) secondUpper secondAllowed]
  simp only [invalidThreadOracle, scheduled, oneThreadChoice, SOut.runOracle]

end MiniRustU64AvailabilityControls
