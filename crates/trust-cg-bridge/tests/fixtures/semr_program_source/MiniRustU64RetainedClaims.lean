/- Closed ORIGINAL claims and semantically false expected subjects for replay.
   No new evaluator, axiom, guessed result or source/ABI admission is supplied. -/
import MiniRustU64AvailabilityControls
noncomputable section
namespace MiniRustU64RetainedClaims
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64AllocatedCall MiniRustU64Run MiniRustU64Correspondence MiniRustU64Availability
  MiniRustU64AvailabilityControls MiniRustAllocate8Safety
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def OriginalBlobClaim : Prop :=
  runBlob SemRU64Addition.originalBytes 0 [.int .u64 0] 3 0 = .ok (.ret [.int .u64 7])

theorem original_blob_zero : OriginalBlobClaim := by
  unfold OriginalBlobClaim
  simp only [runBlob, SemRU64Addition.original_decodes]
  exact congrArg Except.ok (SemRU64Addition.original_return 0 0 (by decide))

def WrongBlobClaim : Prop :=
  runBlob MiniRustU64Controls.wrongBytes 0 [.int .u64 0] 3 0 = .ok (.ret [.int .u64 7])

def actualZero := SOut.runOracle (entryOracle 3) (fun _ => 0)
  (enterAndRun 0 7 0 MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
    [] outside 8 uninit8 [])

def CompleteZeroClaim : Prop := actualZero =
  .ok (.ok (), exitState MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
    [] outside 8 32 40 7 0)

theorem complete_zero : CompleteZeroClaim := by
  exact concrete_full64_available 0 0 (by decide) (fun _ => 0)

def DroppedZeroClaim : Prop := actualZero =
  .ok (.ok (), MiniRustU64Controls.droppedArgument MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
    [] outside 8 32 40 7 0)

def WrongScalarZeroClaim : Prop := actualZero =
  .ok (.ok (), exitState MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
    [] outside 8 32 40 8 0)

end MiniRustU64RetainedClaims
