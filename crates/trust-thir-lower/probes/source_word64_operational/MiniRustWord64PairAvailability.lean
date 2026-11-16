/- Constructive availability, independently of every-success safety. -/
import MiniRustWord64PairEntryRun
import MiniRustAllocate8Room
noncomputable section
namespace MiniRustWord64PairAvailability
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64AllocatedCall MiniRustAllocate8Safety MiniRustWord64PairRun MiniRustWord64PairEntryRun
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def entryOracle (k : Nat) : List Nat → Nat
  | [] => k
  | [_] => k + 1
  | [_, _] => k + 2
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

theorem third_allowed (world : List MR_Allocation) (k : Nat)
    (below : Below world (8 * k)) (room : 8 * (k + 4) < modulus 64) :
    allocationAllowed (world ++ [slot (Int.ofNat (address k)) uninit8,
      slot (Int.ofNat (address (k + 1))) uninit8]) (candidate (k + 2)) = true := by
  apply allowed_of_interval
  · intro old member live
    rcases List.mem_append.mp member with prior | fresh
    · exact high_water_separate world k (k + 2) below (by omega) old prior live
    · simp at fresh
      rcases fresh with h | h <;> subst old <;>
        simp only [slot, MiniRustAllocate8Safety.uninit8_length, MiniRustU64AllocatedCall.address, candidate_nat,
          Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add, Int.natCast_one]
      all_goals constructor
      all_goals first | left; omega | omega
  · exact candidate_end_room (k + 2) (by omega)

/-- A concrete allocation/scheduler oracle reaches the complete normal return.
    Room is explicit; no successful call, initialization or step is assumed. -/
theorem full_function_available (fuel left right : Nat) (base : MR_Machine)
    (caller : MR_StackFrame) (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr : Nat) (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64)
    (k : Nat) (below : Below (callerWorld before after callerAddr callerBytes) (8 * k))
    (room : 8 * (k + 4) < modulus 64) (π : List Nat → Nat) :
    SOut.runOracle (entryOracle k) π
      (enterAndRun fuel left right base caller next before after callerAddr callerBytes accesses) =
      .ok (.ok (), exitState base caller next before after callerAddr
        (address k) (address (k + 1)) (address (k + 2))
        ((left + right) % modulus 64) left right) := by
  rw [full_tree_exact fuel left right base caller next before after callerAddr callerBytes accesses
    callerLength callerAligned leftValid rightValid]
  have gates := two_allowed_from_high_water (callerWorld before after callerAddr callerBytes)
    .Stack k below (by omega : 8 * (k + 3) < modulus 64)
  have secondAllowed : allocationAllowed (callerWorld before after callerAddr callerBytes ++
      [slot (Int.ofNat (address k)) uninit8]) (candidate (k + 1)) = true := by
    simpa only [candidate_nat, slot, address] using gates.2
  have thirdAllowed := third_allowed (callerWorld before after callerAddr callerBytes) k below room
  unfold fullTree
  rw [selected_run _ _ _ (entryOracle k) π (candidate_upper k (by omega)) gates.1]
  rw [show entryOracle k [] = k from rfl]
  rw [selected_run _ _ _ (fun history => entryOracle k (k :: history))
    (fun history => π (k :: history)) (candidate_upper (k + 1) (by omega)) secondAllowed]
  rw [show entryOracle k [k] = k + 1 from rfl]
  rw [selected_run _ _ _ (fun history => entryOracle k (k :: (k + 1) :: history))
    (fun history => π (k :: (k + 1) :: history))
    (candidate_upper (k + 2) (by omega)) thirdAllowed]
  simp only [entryOracle, scheduled, oneThreadChoice, SOut.runOracle]

#print axioms full_function_available
end MiniRustWord64PairAvailability
