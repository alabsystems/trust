-- Copyright 2026 Andrew Yates | Apache-2.0
import BoxedWord64ARCFrame
import BoxedWord64ARCOrder

namespace BoxedWord64
open TrustIr

private theorem get_runs (s : MachineState) : Sem.run Sem.getState s = .ok (s, s) := rfl
private theorem throw_runs {α : Type} (s : MachineState) (fault : SemError) :
    Sem.run (throw fault : Sem α) s = .error fault := rfl
private theorem lookup_runs (s : MachineState) (operand : ValueId) (value : Value)
    (found : s.locals.get operand = some value) :
    Sem.run (Sem.lookupValue operand) s = .ok (value, s) := by
  simp [Sem.lookupValue, Sem.run_bind, get_runs, MachineState.lookupValue, found,
    Except.bind, Sem.run_pure]

/-- Canonical release refuses a live ARC object with no supplied count. -/
theorem zero_budget_refuses (s : MachineState) (operand : ValueId)
    (cell : Allocation) (word : Nat) (rep : ArcPayload s operand cell word 0) :
    Sem.run (semRelease operand) s = .error (.ub
      (trustIrStringBuild s!"Release on zero refcount (double free): {repr cell.id}")) := by
  simp [semRelease, Sem.run_bind, lookup_runs s operand _ rep.argument,
    getAllocIdFromPtrARC, get_runs, rep.payload.lookup, rep.payload.live,
    requireArcRef, rep.permission, requireObjectBase, rep.references,
    Sem.throwUB, throw_runs, Except.bind]

/-- Provenance/liveness is checked before the permission/count operations. -/
theorem dead_object_refuses (s : MachineState) (operand : ValueId)
    (cell : Allocation)
    (argument : s.locals.get operand = some (.ptr cell.base (some cell.id)))
    (found : s.memory.lookup cell.id = some cell) (dead : cell.alive = false) :
    Sem.run (semRelease operand) s = .error (.ub
      (trustIrStringBuild s!"ARC pointer references a freed allocation: {cell.base}")) := by
  simp [semRelease, Sem.run_bind, lookup_runs s operand _ argument,
    getAllocIdFromPtrARC, get_runs, found, dead, Sem.throwUB, throw_runs,
    Except.bind]

/-- A payload address is not the object-base pointer consumed by Release,
even though it is aligned and points to readable initialized storage. -/
theorem interior_pointer_refuses (s : MachineState) (operand : ValueId)
    (cell : Allocation) (word : Nat) (rep : Payload s cell word)
    (argument : s.locals.get operand = some (.ptr (cell.base + 8) (some cell.id)))
    (permission : s.permissions.get cell.id = some .arcRef) :
    Sem.run (semRelease operand) s = .error (.ub
      "Release: pointer is at offset 8 of its cell, not at the object base a runtime object pointer names") := by
  simp [semRelease, Sem.run_bind, lookup_runs s operand _ argument,
    getAllocIdFromPtrARC, get_runs, rep.lookup, rep.live,
    requireArcRef, permission, requireObjectBase, Sem.throwUB, throw_runs,
    Except.bind] <;> rfl

/-- Bytes/liveness do not manufacture ARC permission. -/
theorem missing_permission_refuses (s : MachineState) (operand : ValueId)
    (cell : Allocation) (word : Nat) (rep : Payload s cell word)
    (argument : s.locals.get operand = some (.ptr cell.base (some cell.id)))
    (permission : s.permissions.get cell.id = none) :
    Sem.run (semRelease operand) s = .error (.ub
      (trustIrStringBuild s!"ARC operation on allocation without permission: {repr cell.id}")) := by
  simp [semRelease, Sem.run_bind, lookup_runs s operand _ argument,
    getAllocIdFromPtrARC, get_runs, rep.lookup, rep.live,
    requireArcRef, permission, Sem.throwUB, throw_runs, Except.bind]

/-- Two equal pointer operands do not turn the one supplied reference into two.
The retained all-reads-first ordering still refuses the second Release. -/
theorem single_reference_alias_refuses (s : MachineState) (left right : ValueId)
    (cell : Allocation) (word : Nat)
    (leftRep : ArcPayload s left cell word 1)
    (rightRep : ArcPayload s right cell word 1) :
    Sem.run (do
      let a ← loadPayload cell
      let b ← loadPayload cell
      semRelease left
      semRelease right
      pure (a, b)) s = .error (.ub
        (trustIrStringBuild s!"ARC pointer references a freed allocation: {cell.base}")) := by
  have final := release_last_runs s left cell word leftRep
  have deadLookup := lastRelease_lookup s cell.id cell leftRep.payload.lookup
  simp only [beq_self_eq_true, ite_true] at deadLookup
  have bad := dead_object_refuses (lastReleaseState s cell.id) right
    { cell with alive := false } rightRep.argument deadLookup rfl
  simp only [Sem.run_bind, loadPayload_runs s cell word leftRep.payload,
    Except.bind, final, bad]

/-- Every bounded raw word has a constructive two-reference alias success
witness, not only a representation assumed to exist in an arbitrary world. -/
theorem alias_witness_executes (word : Nat) (bounded : word < 2^64) :
    Sem.run (do
      let a ← loadPayload witnessCell
      let b ← loadPayload witnessCell
      semRelease ⟨0⟩
      semRelease ⟨1⟩
      pure (a, b)) (arcWitnessState word 2) =
        .ok ((.int 64 (Int.ofNat word), .int 64 (Int.ofNat word)),
          lastReleaseState (arcWitnessState word 2) witnessCell.id) := by
  have rep := arc_witness_represents word 2 bounded
  exact alias_reads_then_releases _ _ _ _ _ rep.1 rep.2

/-- The hostile one-reference alias case is inhabited for every bounded word,
including the same initialized bytes and two valid object-base SSA arguments. -/
theorem single_reference_witness_refuses (word : Nat) (bounded : word < 2^64) :
    Sem.run (do
      let a ← loadPayload witnessCell
      let b ← loadPayload witnessCell
      semRelease ⟨0⟩
      semRelease ⟨1⟩
      pure (a, b)) (arcWitnessState word 1) = .error (.ub
        (trustIrStringBuild s!"ARC pointer references a freed allocation: {witnessCell.base}")) := by
  have rep := arc_witness_represents word 1 bounded
  exact single_reference_alias_refuses _ _ _ _ _ rep.1 rep.2

/-- The successful one-to-two ownership construction is inhabited for every
bounded word, without a successful-Retain or returning-run premise. -/
theorem retain_witness_executes (word : Nat) (bounded : word < 2^64) :
    Sem.run (do
      semRetain ⟨0⟩
      let a ← loadPayload witnessCell
      let b ← loadPayload witnessCell
      semRelease ⟨0⟩
      semRelease ⟨1⟩
      pure (a, b)) (arcWitnessState word 1) =
      .ok ((.int 64 (Int.ofNat word), .int 64 (Int.ofNat word)),
        lastReleaseState (arcWitnessState word 1) witnessCell.id) := by
  have rep := arc_witness_represents word 1 bounded
  exact retain_then_alias_reads_releases _ _ _ _ _ rep.1 rep.2

#print axioms single_reference_witness_refuses
#print axioms retain_witness_executes

#print axioms zero_budget_refuses
#print axioms dead_object_refuses
#print axioms interior_pointer_refuses
#print axioms missing_permission_refuses
#print axioms single_reference_alias_refuses
#print axioms alias_witness_executes
end BoxedWord64
