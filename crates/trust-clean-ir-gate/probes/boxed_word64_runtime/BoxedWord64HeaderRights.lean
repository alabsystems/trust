-- Copyright 2026 Andrew Yates | Apache-2.0
import BoxedWord64HeaderEncoding

/-! Constructive canonical hostile controls: encoding arithmetic cannot supply
permissions or turn one supplied reference into two. No physical C rights are
inferred from these states or counts. -/
namespace BoxedWord64.HeaderEncoding
open TrustIr

def noPermissionState (word : Nat) : MachineState :=
  { ambientWitnessState word 2 with
    permissions := clearPermission (ambientWitnessState word 2).permissions witnessCell.id }

theorem positive_count_without_permission (word : Nat) (bounded : word < 2^64) :
    getRefCount (noPermissionState word).refCounts witnessCell.id = references 1 ∧
    (noPermissionState word).permissions.get witnessCell.id = none := by
  have rep := (ambient_witness_represents word 2 bounded).1
  constructor
  · exact rep.references
  · simp [noPermissionState, clearPermission, PermissionMap.get]

theorem positive_header_does_not_bypass_permission (word : Nat) (bounded : word < 2^64) :
    Sem.run (semRelease ⟨0⟩) (noPermissionState word) = .error (.ub
      (trustIrStringBuild s!"ARC operation on allocation without permission: {repr witnessCell.id}")) := by
  have rep := (ambient_witness_represents word 2 bounded).1
  have payload : Payload (noPermissionState word) witnessCell word :=
    ⟨rep.payload.lookup, rep.payload.live, rep.payload.origin, rep.payload.room,
      rep.payload.aligned, rep.payload.initialized, rep.payload.bounded⟩
  exact missing_permission_refuses _ _ _ _ payload rep.argument
    (positive_count_without_permission word bounded).2

theorem zero_budget_is_not_header_zero (s : MachineState) (operand : ValueId)
    (cell : Allocation) (word : Nat)
    (empty : getRefCount s.refCounts cell.id = 0) :
    ¬ Ordinary s operand cell word 0 := by
  intro rep
  have contradiction := rep.canonical.references
  rw [empty] at contradiction
  cases contradiction

#print axioms positive_count_without_permission
#print axioms positive_header_does_not_bypass_permission
#print axioms zero_budget_is_not_header_zero
end BoxedWord64.HeaderEncoding
