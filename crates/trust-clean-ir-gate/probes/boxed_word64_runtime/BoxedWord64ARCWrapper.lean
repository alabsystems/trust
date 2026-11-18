-- Copyright 2026 Andrew Yates | Apache-2.0
import BoxedWord64ARCFrame
import BoxedWord64ARCOrder

/-!
Canonical memory/sidecar composition for the pre-call read/read/release/release
pattern. This is not execution of the generated Clean wrapper, its C runtime,
its scalar call or its result boxing. Source ownership supplies the reference
budgets; identical pointer values alone do not supply two owned arguments.
-/
namespace BoxedWord64
open TrustIr

theorem lastRelease_other_arcPayload (s : MachineState) (id : AllocId)
    (operand : ValueId) (cell : Allocation) (word n : Nat)
    (rep : ArcPayload s operand cell word n) (different : cell.id ≠ id) :
    ArcPayload (lastReleaseState s id) operand cell word n := by
  refine ⟨lastRelease_other_payload s id cell word rep.payload different,
    rep.argument, ?_, ?_⟩
  · change (lastReleaseState s id).permissions cell.id = some .arcRef
    rw [lastRelease_other_permission s id cell.id different]
    exact rep.permission
  · change getRefCount (lastReleaseState s id).refCounts cell.id = n
    unfold getRefCount
    rw [lastRelease_other_count s id cell.id different]
    exact rep.references

/-- Distinct count-one arguments have the exact canonical two-deallocation
poststate. This complements, rather than imposing disjointness on, the separate
count-two alias theorem. -/
theorem distinct_reads_then_releases (s : MachineState) (left right : ValueId)
    (leftCell rightCell : Allocation) (a b : Nat)
    (leftRep : ArcPayload s left leftCell a 1)
    (rightRep : ArcPayload s right rightCell b 1)
    (different : rightCell.id ≠ leftCell.id) :
    Sem.run (do
      let a' ← loadPayload leftCell
      let b' ← loadPayload rightCell
      semRelease left
      semRelease right
      pure (a', b')) s =
      .ok ((.int 64 (Int.ofNat a), .int 64 (Int.ofNat b)),
        lastReleaseState (lastReleaseState s leftCell.id) rightCell.id) := by
  have first := release_last_runs s left leftCell a leftRep
  have remaining := lastRelease_other_arcPayload s leftCell.id right rightCell b 1
    rightRep different
  have last := release_last_runs (lastReleaseState s leftCell.id) right rightCell b remaining
  simp only [Sem.run_bind, loadPayload_runs s leftCell a leftRep.payload,
    loadPayload_runs s rightCell b rightRep.payload, Except.bind, first, last, Sem.run_pure]

/-- A nonempty surrounding allocation and retained scalar/global/frame
inputs. This constructs a nontrivial instance of the arbitrary-state theorems;
none of these records is identified with a physical C allocation/header. -/
def ambientCell : Allocation :=
  { id := ⟨7⟩, base := 64, size := 16, alive := true,
    origin := .cleanHeap, requested := 16 }

def ambientWitnessState (word references : Nat) : MachineState :=
  { arcWitnessState word references with
    memory := { (arcWitnessState word references).memory with
      allocations := [witnessCell, ambientCell]
      nextAddr := 128
      nextAllocId := 8 }
    locals := (arcWitnessState word references).locals.set ⟨99⟩ (.int 64 123)
    permissions := (arcWitnessState word references).permissions.set ambientCell.id .owned
    refCounts := setRefCount (arcWitnessState word references).refCounts ambientCell.id 7
    globals := [(⟨5⟩, 64, ambientCell.id)]
    openFrameLineages := [11, 13]
    nextFrameLineage := 14
    nextValueId := 100 }

theorem ambient_witness_represents (word references : Nat) (bounded : word < 2^64) :
    ArcPayload (ambientWitnessState word references) ⟨0⟩ witnessCell word references ∧
    ArcPayload (ambientWitnessState word references) ⟨1⟩ witnessCell word references := by
  have rep := witness_represents word bounded
  have payload : Payload (ambientWitnessState word references) witnessCell word := by
    refine ⟨?_, rep.live, rep.origin, rep.room, rep.aligned, rep.initialized, rep.bounded⟩
    simp [ambientWitnessState, witnessCell, ambientCell, Memory.lookup]
  constructor <;> refine ⟨payload, ?_, ?_, ?_⟩ <;>
    simp [ambientWitnessState, arcWitnessState, witnessCell, ambientCell,
      ValueMap.get, ValueMap.set, ValueMap.empty,
      PermissionMap.get, PermissionMap.set, PermissionMap.empty, getRefCount, setRefCount]

/-- Every bounded word executes the exact alias order in a nontrivial world,
with arbitrary-state framing instantiated rather than assumed successful. -/
theorem ambient_alias_witness_executes (word : Nat) (bounded : word < 2^64) :
    Sem.run (do
      let a ← loadPayload witnessCell
      let b ← loadPayload witnessCell
      semRelease ⟨0⟩
      semRelease ⟨1⟩
      pure (a, b)) (ambientWitnessState word 2) =
      .ok ((.int 64 (Int.ofNat word), .int 64 (Int.ofNat word)),
        lastReleaseState (ambientWitnessState word 2) witnessCell.id) := by
  have rep := ambient_witness_represents word 2 bounded
  exact alias_reads_then_releases _ _ _ _ _ rep.1 rep.2

/-- Concrete surrounding allocation/SSA/frame inputs survive final release.
The general frame and lookup theorems quantify over arbitrary ambient states. -/
theorem ambient_survives_release (word : Nat) :
    (lastReleaseState (ambientWitnessState word 2) witnessCell.id).memory.lookup
      ambientCell.id = some ambientCell ∧
    (lastReleaseState (ambientWitnessState word 2) witnessCell.id).permissions
      ambientCell.id = some .owned ∧
    (lastReleaseState (ambientWitnessState word 2) witnessCell.id).refCounts
      ambientCell.id = some 7 ∧
    (lastReleaseState (ambientWitnessState word 2) witnessCell.id).locals.get
      ⟨99⟩ = some (.int 64 123) ∧
    (lastReleaseState (ambientWitnessState word 2) witnessCell.id).globals =
      [(⟨5⟩, 64, ambientCell.id)] ∧
    (lastReleaseState (ambientWitnessState word 2) witnessCell.id).openFrameLineages =
      [11, 13] := by
  have other : ambientCell.id ≠ witnessCell.id := by decide
  have found : (ambientWitnessState word 2).memory.lookup ambientCell.id = some ambientCell := by
    simp [ambientWitnessState, witnessCell, ambientCell, Memory.lookup]
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simpa [other] using lastRelease_lookup (ambientWitnessState word 2)
      witnessCell.id ambientCell found
  · rw [lastRelease_other_permission _ _ _ other]
    simp [ambientWitnessState, PermissionMap.set]
  · rw [lastRelease_other_count _ _ _ other]
    simp [ambientWitnessState, setRefCount]
  · simp [lastReleaseState, ambientWitnessState, ValueMap.get, ValueMap.set]

#print axioms lastRelease_other_arcPayload
#print axioms distinct_reads_then_releases
#print axioms ambient_witness_represents
#print axioms ambient_alias_witness_executes
#print axioms ambient_survives_release
end BoxedWord64
