/- Constructive availability of the actual full function, separate from safety. -/
import MiniRustU64Correspondence
import MiniRustAllocate8Room
noncomputable section
namespace MiniRustU64Availability
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Entry MiniRustU64Call MiniRustU64AllocatedCall MiniRustU64Run
  MiniRustU64Correspondence MiniRustAllocate8Safety
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The real oracle picks two fresh high-water candidates then current thread0.
    It does not manufacture a model result or remove any branch from safety. -/
def entryOracle (k : Nat) : List Nat → Nat
  | [] => k
  | [_] => k + 1
  | _ => 0

theorem selected_run {α : Type} (bound : Int) (allowed : Int → Bool)
    (next : Nat → SOut α) (δ π : List Nat → Nat)
    (upper : SInt.blt (candidate (δ [])) bound = true)
    (accepted : allowed (candidate (δ [])) = true) :
    SOut.runOracle δ π (selectedChoice bound allowed next) =
      SOut.runOracle (fun history => δ (δ [] :: history))
        (fun history => π (δ [] :: history)) (next (δ [])) := by
  unfold selectedChoice SOut.runOracle
  dsimp only
  rw [upper, accepted]

theorem candidate_upper (index : Nat) (room : 8 * (index + 2) < modulus 64) :
    SInt.blt (candidate index) (Int.ofNat (modulus 64)) = true := by
  have endRoom := candidate_end_room index room
  have : candidate index < Int.ofNat (modulus 64) := by omega
  simpa [SInt.blt] using this

/-- Explicit sufficient room; no successful allocation/call/run is a premise.
    Full or fragmented address spaces are NOT declared available by this law. -/
theorem full_function_available (fuel literal input : Nat) (base : MR_Machine)
    (caller : MR_StackFrame) (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr : Nat) (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64)
    (k : Nat) (below : Below (callerWorld before after callerAddr callerBytes) (8 * k))
    (room : 8 * (k + 3) < modulus 64) (π : List Nat → Nat) :
    SOut.runOracle (entryOracle k) π
      (enterAndRun fuel literal input base caller next before after callerAddr callerBytes accesses) =
      .ok (.ok (), exitState base caller next before after callerAddr (address k) (address (k + 1))
        ((input + literal) % modulus 64) input) := by
  rw [full_tree_exact fuel literal input base caller next before after callerAddr callerBytes accesses
    callerLength callerAligned inputValid literalValid]
  have gates := two_allowed_from_high_water (callerWorld before after callerAddr callerBytes) .Stack k below room
  have firstUpper := candidate_upper k (by omega : 8 * (k + 2) < modulus 64)
  have secondUpper := candidate_upper (k + 1) (by simpa [Nat.add_assoc] using room)
  have secondAllowed : allocationAllowed (callerWorld before after callerAddr callerBytes ++
      [slot (Int.ofNat (address k)) uninit8]) (candidate (k + 1)) = true := by
    simpa only [candidate_nat, slot, address] using gates.2
  unfold fullTree
  rw [selected_run _ _ _ (entryOracle k) π firstUpper gates.1]
  rw [show entryOracle k [] = k from rfl]
  rw [selected_run _ _ _ (fun history => entryOracle k (k :: history))
    (fun history => π (k :: history)) secondUpper secondAllowed]
  simp only [entryOracle, scheduled, oneThreadChoice, SOut.runOracle]

end MiniRustU64Availability
