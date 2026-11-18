-- Copyright 2026 Andrew Yates | Apache-2.0
import CAtomicDropCandidate
import BoxedWord64HeaderRights

/-! Limitation controls for the actual canonical byte operations. A successful
byte-atomic candidate has no ARC-permission or source-ownership conclusion.
This header-only state is not a constructed physical C object/lifetime witness.
The helper's true return is a request to its caller to free, not deallocation.
-/
namespace CAtomicHeaderBoundaryControls
open TrustIr BoxedWord64

def headerOnlyState (header : Nat) : MachineState :=
  { witnessState 7 with
    memory := (witnessState 7).memory.writeBytes witnessCell.base
      (encodeIntBytes (Int.ofNat header) 4)
    locals := ValueMap.empty.set ⟨0⟩ (.ptr witnessCell.base (some witnessCell.id))
    nextValueId := 1 }

theorem header_only_has_no_arc_permission (header : Nat) :
    (headerOnlyState header).permissions.get witnessCell.id = none ∧
    getRefCount (headerOnlyState header).refCounts witnessCell.id = 0 := by
  constructor <;> rfl

/-- Existing strict byte atomics can execute with no ARC permission. Therefore
that execution alone cannot justify the separately checked ownership gate. -/
theorem raw_atomic_success_does_not_supply_rights :
    (Sem.run (CAtomicDropCandidate.program 0xE0000000 ⟨0⟩) (headerOnlyState 1)).map
      (fun (last, s) => (last, s.memory.readBytes witnessCell.base 4,
        s.permissions.get witnessCell.id, getRefCount s.refCounts witnessCell.id)) =
      .ok (false, some [0, 0, 0, 0], none, 0) := by cbv

/-- The OLD-zero RMW wraps u32 in header bytes and returns true but does NOT
free. clean_dec/clean_dec_release and their actual C proof remain required. -/
theorem last_signal_is_not_deallocation :
    (Sem.run (CAtomicDropCandidate.program 0xE0000000 ⟨0⟩) (headerOnlyState 0)).map
      (fun (last, s) => (last, s.memory.readBytes witnessCell.base 4,
        (s.memory.lookup witnessCell.id).map (fun a => a.alive))) =
      .ok (true, some [255, 255, 255, 255], some true) := by cbv

#print axioms header_only_has_no_arc_permission
#print axioms raw_atomic_success_does_not_supply_rights
#print axioms last_signal_is_not_deallocation
end CAtomicHeaderBoundaryControls
