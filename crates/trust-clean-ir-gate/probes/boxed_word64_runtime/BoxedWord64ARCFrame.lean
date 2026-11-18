-- Copyright 2026 Andrew Yates | Apache-2.0
import BoxedWord64ARC

namespace BoxedWord64
open TrustIr

/-- Exact state framing: count-only operations retain every field except the
named sidecar. These are projections of expected canonical poststates, not C. -/
theorem countState_frame (s : MachineState) (id : AllocId) (n : Nat) :
    { countState s id n with refCounts := s.refCounts } = s := rfl

theorem countState_other (s : MachineState) (id other : AllocId) (n : Nat)
    (different : other ≠ id) :
    (countState s id n).refCounts other = s.refCounts other := by
  simp [countState, setRefCount, different]

/-- Only allocation liveness, permissions and reference counts may change at
last release. All other MachineState fields are preserved exactly. -/
theorem lastRelease_frame (s : MachineState) (id : AllocId) :
    { lastReleaseState s id with
      memory := s.memory
      permissions := s.permissions
      refCounts := s.refCounts } = s := rfl

/-- Canonical deallocation preserves all memory components except allocation
liveness. This does not say a physical header/write/free preserves C bytes. -/
theorem lastRelease_memory_frame (s : MachineState) (id : AllocId) :
    { (lastReleaseState s id).memory with allocations := s.memory.allocations } =
      s.memory := rfl

theorem lastRelease_other_count (s : MachineState) (id other : AllocId)
    (different : other ≠ id) :
    (lastReleaseState s id).refCounts other = s.refCounts other := by
  simp [lastReleaseState, setRefCount, different]

theorem lastRelease_other_permission (s : MachineState) (id other : AllocId)
    (different : other ≠ id) :
    (lastReleaseState s id).permissions other = s.permissions other := by
  simp [lastReleaseState, clearPermission, different]

private theorem readBytes_from_same_bytes (before after : Memory) (addr size : Nat)
    (same : ∀ address, before.bytes address = after.bytes address) :
    before.readBytes addr size = after.readBytes addr size := by
  unfold Memory.readBytes
  induction size generalizing addr with
  | zero => rfl
  | succ n ih =>
    simp only [Memory.readBytes.go]
    rw [same addr]
    cases after.bytes addr with
    | none => rfl
    | some byte => rw [ih (addr + 1)]

theorem lastRelease_readBytes (s : MachineState) (id : AllocId) (addr size : Nat) :
    (lastReleaseState s id).memory.readBytes addr size = s.memory.readBytes addr size := by
  exact readBytes_from_same_bytes _ _ addr size (fun _ => rfl)

/-- Every actual allocation record is retained; only matching ids become dead.
No allocation-list uniqueness or surrounding-memory emptiness is assumed. -/
theorem lastRelease_lookup (s : MachineState) (id : AllocId) (cell : Allocation)
    (found : s.memory.lookup cell.id = some cell) :
    (lastReleaseState s id).memory.lookup cell.id =
      some (if cell.id == id then { cell with alive := false } else cell) := by
  let mark := fun a : Allocation => if a.id == id then { a with alive := false } else a
  have keepId (a : Allocation) : (mark a).id = a.id := by
    dsimp [mark]
    split <;> rfl
  have predicate : (fun a => (mark a).id == cell.id) = (fun a => a.id == cell.id) := by
    funext a
    rw [keepId]
  change (s.memory.allocations.map mark).find? (fun a => a.id == cell.id) = _
  rw [List.find?_map]
  change (s.memory.allocations.find? (fun a => (mark a).id == cell.id)).map mark = _
  rw [predicate]
  change (s.memory.lookup cell.id).map mark = _
  rw [found]
  rfl

/-- Last release of another allocation preserves this complete live Payload,
including initialized storage and allocation identity. -/
theorem lastRelease_other_payload (s : MachineState) (id : AllocId)
    (cell : Allocation) (word : Nat) (rep : Payload s cell word)
    (different : cell.id ≠ id) :
    Payload (lastReleaseState s id) cell word := by
  refine ⟨?_, rep.live, rep.origin, rep.room, rep.aligned, ?_, rep.bounded⟩
  · simpa [different] using lastRelease_lookup s id cell rep.lookup
  · exact rep.initialized

/-- Preserved raw storage is not permission to read a released object. -/
theorem lastRelease_not_payload (s : MachineState) (cell : Allocation) (word : Nat)
    (rep : Payload s cell word) : ¬ Payload (lastReleaseState s cell.id) cell word := by
  intro bad
  have found := lastRelease_lookup s cell.id cell rep.lookup
  simp only [beq_self_eq_true, ite_true] at found
  have equal : { cell with alive := false } = cell := Option.some.inj (found.symm.trans bad.lookup)
  have contradiction := congrArg Allocation.alive equal
  rw [rep.live] at contradiction
  cases contradiction

#print axioms countState_frame
#print axioms countState_other
#print axioms lastRelease_frame
#print axioms lastRelease_memory_frame
#print axioms lastRelease_other_count
#print axioms lastRelease_other_permission
#print axioms lastRelease_readBytes
#print axioms lastRelease_lookup
#print axioms lastRelease_other_payload
#print axioms lastRelease_not_payload
end BoxedWord64
