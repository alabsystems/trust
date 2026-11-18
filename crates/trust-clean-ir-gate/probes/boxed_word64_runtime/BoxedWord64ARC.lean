-- Copyright 2026 Andrew Yates | Apache-2.0
import BoxedWord64Payload

/-!
Canonical ARC sidecar ownership groundwork for the retained UInt64 adapter.
The C runtime stores refs-minus-one in header bytes and has sticky/atomic/drop
rules. None of those bytes or C effects is identified with this logical Nat
sidecar. These theorems execute existing TrustIR ARC/memory operations only.
The supplied ownership budget is an explicit calling-contract premise; a
refcount observed in arbitrary source code does not establish ownership.
-/
namespace BoxedWord64
open TrustIr

/-- An object-base SSA operand, payload and explicitly supplied sidecar count.
No successful execution or physical header relation is assumed. This predicate
does not derive individual source ownership rights from an observed count. -/
structure ArcPayload (s : MachineState) (operand : ValueId) (cell : Allocation)
    (word references : Nat) : Prop where
  payload : Payload s cell word
  argument : s.locals.get operand = some (.ptr cell.base (some cell.id))
  permission : s.permissions.get cell.id = some .arcRef
  references : getRefCount s.refCounts cell.id = references

/-- Exact expected poststate of a nonfinal sidecar count update. -/
def countState (s : MachineState) (id : AllocId) (references : Nat) : MachineState :=
  { s with refCounts := setRefCount s.refCounts id references }

/-- Exact expected poststate of canonical last release, not a C header write. -/
def lastReleaseState (s : MachineState) (id : AllocId) : MachineState :=
  { s with
    memory := { s.memory with allocations := (s.memory.allocations.map
      (fun a => if a.id == id then { a with alive := false } else a)) }
    permissions := clearPermission s.permissions id
    refCounts := setRefCount s.refCounts id 0 }

private theorem get_run (s : MachineState) : Sem.run Sem.getState s = .ok (s, s) := rfl
private theorem set_run (s t : MachineState) : Sem.run (Sem.setState t) s = .ok ((), t) := rfl

private theorem lookup_run (s : MachineState) (operand : ValueId) (value : Value)
    (found : s.locals.get operand = some value) :
    Sem.run (Sem.lookupValue operand) s = .ok (value, s) := by
  simp [Sem.lookupValue, Sem.run_bind, get_run, MachineState.lookupValue, found,
    Except.bind, Sem.run_pure]

theorem countState_payload (s : MachineState) (cell : Allocation) (word n : Nat)
    (rep : Payload s cell word) : Payload (countState s cell.id n) cell word := by
  exact ⟨rep.lookup, rep.live, rep.origin, rep.room, rep.aligned, rep.initialized, rep.bounded⟩

theorem countState_arcPayload (s : MachineState) (operand : ValueId) (cell : Allocation)
    (word before after : Nat) (rep : ArcPayload s operand cell word before) :
    ArcPayload (countState s cell.id after) operand cell word after := by
  refine ⟨countState_payload s cell word after rep.payload, rep.argument, rep.permission, ?_⟩
  simp [countState, getRefCount, setRefCount]

/-- Retaining a live operand with a positive sidecar budget preserves payload/ambient
state and adds exactly one logical reference. Zero-budget resurrection is not
used as a calling-contract witness. -/
theorem retain_runs (s : MachineState) (operand : ValueId) (cell : Allocation)
    (word n : Nat) (rep : ArcPayload s operand cell word (n + 1)) :
    Sem.run (semRetain operand) s = .ok ((), countState s cell.id (n + 2)) := by
  simp [semRetain, Sem.run_bind, lookup_run s operand _ rep.argument,
    getAllocIdFromPtrARC, get_run, rep.payload.lookup, rep.payload.live,
    requireArcRef, rep.permission, requireObjectBase, rep.references,
    set_run, countState, Except.bind, Nat.add_assoc]

/-- With at least two supplied references, one release leaves a live payload
and every ambient field intact except this allocation's sidecar count. -/
theorem release_shared_runs (s : MachineState) (operand : ValueId) (cell : Allocation)
    (word n : Nat) (rep : ArcPayload s operand cell word (n + 2)) :
    Sem.run (semRelease operand) s = .ok ((), countState s cell.id (n + 1)) := by
  simp [semRelease, Sem.run_bind, lookup_run s operand _ rep.argument,
    getAllocIdFromPtrARC, get_run, rep.payload.lookup, rep.payload.live,
    requireArcRef, rep.permission, requireObjectBase, rep.references,
    set_run, countState, Except.bind]

private theorem live_allocation_found (s : MachineState) (cell : Allocation)
    (found : s.memory.lookup cell.id = some cell) (live : cell.alive = true) :
    s.memory.allocations.any (fun a => a.id == cell.id && a.alive) = true := by
  have member : cell ∈ s.memory.allocations := List.mem_of_find?_eq_some found
  exact List.any_eq_true.mpr ⟨cell, member, by simp [live]⟩

private theorem dealloc_runs (s : MachineState) (cell : Allocation)
    (found : s.memory.allocations.any (fun a => a.id == cell.id && a.alive) = true) :
    Sem.run (deallocARC cell.id) s = .ok ((), lastReleaseState s cell.id) := by
  simp only [deallocARC, Sem.run_bind, get_run, Except.bind]
  rw [found]
  rfl

/-- Last release has the exact canonical deallocation state. Payload bytes
are not overwritten by this model, but the cell is no longer live/readable. -/
theorem release_last_runs (s : MachineState) (operand : ValueId) (cell : Allocation)
    (word : Nat) (rep : ArcPayload s operand cell word 1) :
    Sem.run (semRelease operand) s = .ok ((), lastReleaseState s cell.id) := by
  have found := live_allocation_found s cell rep.payload.lookup rep.payload.live
  simp [semRelease, Sem.run_bind, lookup_run s operand _ rep.argument,
    getAllocIdFromPtrARC, get_run, rep.payload.lookup, rep.payload.live,
    requireArcRef, rep.permission, requireObjectBase, rep.references,
    dealloc_runs s cell found, Except.bind]

#print axioms countState_payload
#print axioms countState_arcPayload
#print axioms retain_runs
#print axioms release_shared_runs
#print axioms release_last_runs
end BoxedWord64
