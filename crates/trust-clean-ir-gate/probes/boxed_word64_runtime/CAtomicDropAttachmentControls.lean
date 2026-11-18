-- Copyright 2026 Andrew Yates | Apache-2.0
import CAtomicDropSource
import CAtomicDropCandidate

/-! Closed fragment-to-candidate association only. Macro/type/source-context and
C11 execution-to-canonical simulation are not conclusions of these statements. -/
namespace CAtomicDropAttachmentControls
open TrustIr

theorem actual_fragment_proposes (threshold : Nat) (pointer : ValueId) :
    CAtomicDropCandidate.propose CAtomicDropSource.actualSource
      CAtomicDropSource.proposal threshold pointer =
      some (CAtomicDropCandidate.program threshold pointer) :=
  CAtomicDropCandidate.checked_source_proposes _ _ _ _ CAtomicDropSource.actual_syntax

theorem actual_changed_guard_refuses (threshold : Nat) (pointer : ValueId) :
    CAtomicDropCandidate.propose CAtomicDropSource.changed_guard
      CAtomicDropSource.proposal threshold pointer = none :=
  CAtomicDropCandidate.unsupported_source_refuses _ _ _ _
    CAtomicDropSource.changed_guard_refuses

/-- Existing canonical operand lookup remains mandatory; source syntax does
not invent a pointer/provenance/permission from an unbound name. -/
theorem undefined_operand_refuses (threshold : Nat) :
    (Sem.run (CAtomicDropCandidate.program threshold ⟨0⟩) MachineState.empty).toOption = none := by
  rfl

#print axioms actual_fragment_proposes
#print axioms actual_changed_guard_refuses
#print axioms undefined_operand_refuses
end CAtomicDropAttachmentControls
