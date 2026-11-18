-- Copyright 2026 Andrew Yates | Apache-2.0
import BoxedWord64ARC

/-!
The mathematical pre-Dec ordering of the retained untrusted adapter: read both
payloads, then consume two supplied references. This file does not execute or
interpret C, reconstruct header bytes, or establish source ownership/ABI/NoUB.
The reference budget is explicit. A single fresh reference is not two owned
arguments merely because two SSA operands have the same pointer value.
-/
namespace BoxedWord64
open TrustIr

/-- Alias of the existing fixed canonical UInt64 payload read. -/
def loadPayload (cell : Allocation) : Sem Value :=
  semLoadValueUsing (fun m bs => decodeMemoryAt .le64 m .U64 bs)
    .U64 (.ptr (cell.base + 8) (some cell.id)) true none .le64

theorem loadPayload_runs (s : MachineState) (cell : Allocation) (word : Nat)
    (rep : Payload s cell word) :
    Sem.run (loadPayload cell) s = .ok (.int 64 (Int.ofNat word), s) :=
  payload_load s cell word rep

theorem setRefCount_replace (counts : RefCountMap) (id : AllocId) (before after : Nat) :
    setRefCount (setRefCount counts id before) id after = setRefCount counts id after := by
  funext other
  by_cases same : other = id <;> simp [setRefCount, same]

theorem countState_replace (s : MachineState) (id : AllocId) (before after : Nat) :
    countState (countState s id before) id after = countState s id after := by
  simp only [countState, setRefCount_replace]

theorem lastRelease_after_count (s : MachineState) (id : AllocId) (n : Nat) :
    lastReleaseState (countState s id n) id = lastReleaseState s id := by
  simp only [countState, lastReleaseState, setRefCount_replace]

/-- At canonical count two, the first Release leaves one live reference and
the second is final. Source ownership of both arguments is a separate calling
contract obligation, not inferred from these equal pointer operands. -/
theorem alias_two_releases (s : MachineState) (left right : ValueId)
    (cell : Allocation) (word : Nat)
    (leftRep : ArcPayload s left cell word 2)
    (rightRep : ArcPayload s right cell word 2) :
    Sem.run (do semRelease left; semRelease right) s =
      .ok ((), lastReleaseState s cell.id) := by
  have first := release_shared_runs s left cell word 0 leftRep
  have remaining := countState_arcPayload s right cell word 2 1 rightRep
  have second := release_last_runs (countState s cell.id 1) right cell word remaining
  simp only [Sem.run_bind, first, Except.bind]
  simpa only [lastRelease_after_count] using second

/-- Exact retained wrapper order for aliased operands with supplied count two, before
any callable/result boxing is considered. Saved scalar values survive release;
the allocation itself has the exact dead-state result, not a live Payload. -/
theorem alias_reads_then_releases (s : MachineState) (left right : ValueId)
    (cell : Allocation) (word : Nat)
    (leftRep : ArcPayload s left cell word 2)
    (rightRep : ArcPayload s right cell word 2) :
    Sem.run (do
      let a ← loadPayload cell
      let b ← loadPayload cell
      semRelease left
      semRelease right
      pure (a, b)) s =
      .ok ((.int 64 (Int.ofNat word), .int 64 (Int.ofNat word)),
        lastReleaseState s cell.id) := by
  have first := release_shared_runs s left cell word 0 leftRep
  have remaining := countState_arcPayload s right cell word 2 1 rightRep
  have last := release_last_runs (countState s cell.id 1) right cell word remaining
  simp only [Sem.run_bind, loadPayload_runs s cell word leftRep.payload,
    Except.bind, first, last, Sem.run_pure, lastRelease_after_count]

/-- Canonical count two also permits this interleaving in the canonical
model: the first Release leaves one live reference for the second read. The
retained adapter order is proved above; no claim that this alternative is
inherently unsafe, or permission to change generated C, follows. -/
theorem alias_interleaved_two_references (s : MachineState) (left right : ValueId)
    (cell : Allocation) (word : Nat)
    (leftRep : ArcPayload s left cell word 2)
    (rightRep : ArcPayload s right cell word 2) :
    Sem.run (do
      let a ← loadPayload cell
      semRelease left
      let b ← loadPayload cell
      semRelease right
      pure (a, b)) s =
      .ok ((.int 64 (Int.ofNat word), .int 64 (Int.ofNat word)),
        lastReleaseState s cell.id) := by
  have first := release_shared_runs s left cell word 0 leftRep
  have remaining := countState_arcPayload s right cell word 2 1 rightRep
  have last := release_last_runs (countState s cell.id 1) right cell word remaining
  simp only [Sem.run_bind, loadPayload_runs s cell word leftRep.payload,
    Except.bind, first, loadPayload_runs (countState s cell.id 1) cell word remaining.payload,
    last, Sem.run_pure, lastRelease_after_count]

/-- Constructive sidecar state for every bounded raw word. The unchanged
qualified payload witness provides bytes; these are logical ARC inputs, not C
header bytes. The two SSA arguments retain one exact object-base pointer. -/
def arcWitnessState (word references : Nat) : MachineState :=
  { witnessState word with
    locals := (ValueMap.empty.set ⟨0⟩ (.ptr witnessCell.base (some witnessCell.id))).set
      ⟨1⟩ (.ptr witnessCell.base (some witnessCell.id))
    permissions := PermissionMap.empty.set witnessCell.id .arcRef
    refCounts := setRefCount RefCountMap.empty witnessCell.id references
    nextValueId := 2 }

theorem arc_witness_represents (word references : Nat) (bounded : word < 2^64) :
    ArcPayload (arcWitnessState word references) ⟨0⟩ witnessCell word references ∧
    ArcPayload (arcWitnessState word references) ⟨1⟩ witnessCell word references := by
  have rep := witness_represents word bounded
  have payload : Payload (arcWitnessState word references) witnessCell word :=
    ⟨rep.lookup, rep.live, rep.origin, rep.room, rep.aligned, rep.initialized, rep.bounded⟩
  constructor <;> refine ⟨payload, ?_, ?_, ?_⟩ <;>
    simp [arcWitnessState, witnessCell, ValueMap.get, ValueMap.set, ValueMap.empty,
      PermissionMap.get, PermissionMap.set, getRefCount, setRefCount]

/-- Canonical Retain constructs the second reference from a supplied first
reference. There is no successful-operation premise and no C-counter equation. -/
theorem retain_constructs_second_reference (s : MachineState) (left right : ValueId)
    (cell : Allocation) (word : Nat)
    (leftRep : ArcPayload s left cell word 1)
    (rightRep : ArcPayload s right cell word 1) :
    Sem.run (semRetain left) s = .ok ((), countState s cell.id 2) ∧
      ArcPayload (countState s cell.id 2) left cell word 2 ∧
      ArcPayload (countState s cell.id 2) right cell word 2 := by
  exact ⟨retain_runs s left cell word 0 leftRep,
    countState_arcPayload s left cell word 1 2 leftRep,
    countState_arcPayload s right cell word 1 2 rightRep⟩

/-- If other owners remain, the two supplied references are consumed while
that residual ownership budget and the payload stay live. The whole ambient
state is retained except for the named sidecar update. -/
theorem alias_reads_leave_other_owners (s : MachineState) (left right : ValueId)
    (cell : Allocation) (word n : Nat)
    (leftRep : ArcPayload s left cell word (n + 3))
    (rightRep : ArcPayload s right cell word (n + 3)) :
    Sem.run (do
      let a ← loadPayload cell
      let b ← loadPayload cell
      semRelease left
      semRelease right
      pure (a, b)) s =
      .ok ((.int 64 (Int.ofNat word), .int 64 (Int.ofNat word)),
        countState s cell.id (n + 1)) ∧
      Payload (countState s cell.id (n + 1)) cell word := by
  have first := release_shared_runs s left cell word (n + 1) leftRep
  have remaining := countState_arcPayload s right cell word (n + 3) (n + 2) rightRep
  have last := release_shared_runs (countState s cell.id (n + 2)) right cell word n remaining
  constructor
  · simp only [Sem.run_bind, loadPayload_runs s cell word leftRep.payload,
      Except.bind, first, last, Sem.run_pure, countState_replace]
  · exact countState_payload s cell word (n + 1) leftRep.payload

/-- The actual canonical Retain supplies the additional reference before the
exact alias wrapper order is run. No successful-retain or successful-wrapper
premise is introduced. -/
theorem retain_then_alias_reads_releases (s : MachineState) (left right : ValueId)
    (cell : Allocation) (word : Nat)
    (leftRep : ArcPayload s left cell word 1)
    (rightRep : ArcPayload s right cell word 1) :
    Sem.run (do
      semRetain left
      let a ← loadPayload cell
      let b ← loadPayload cell
      semRelease left
      semRelease right
      pure (a, b)) s =
      .ok ((.int 64 (Int.ofNat word), .int 64 (Int.ofNat word)),
        lastReleaseState s cell.id) := by
  have retained := retain_runs s left cell word 0 leftRep
  have a := countState_arcPayload s left cell word 1 2 leftRep
  have b := countState_arcPayload s right cell word 1 2 rightRep
  have rest := alias_reads_then_releases (countState s cell.id 2) left right cell word a b
  simp only [Sem.run_bind, retained, Except.bind]
  simpa only [lastRelease_after_count] using rest

#print axioms alias_interleaved_two_references
#print axioms alias_reads_leave_other_owners
#print axioms retain_then_alias_reads_releases

#print axioms loadPayload_runs
#print axioms setRefCount_replace
#print axioms countState_replace
#print axioms lastRelease_after_count
#print axioms alias_two_releases
#print axioms alias_reads_then_releases
#print axioms arc_witness_represents
#print axioms retain_constructs_second_reference
end BoxedWord64
