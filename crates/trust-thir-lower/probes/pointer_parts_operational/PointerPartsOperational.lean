/- Copyright 2026 Andrew Yates. Apache-2.0.
   Conditional canonical IR semantics only: no source authority or admission. -/
import TrustIr.Semantics.Memory

namespace PointerPartsOperational
open TrustIr

private theorem lookup_run (state : MachineState) (id : ValueId) :
    Sem.run (Sem.lookupValue id) state =
      match state.lookupValue id with
      | some value => .ok (value, state)
      | none => .error (.typeError s!"undefined SSA value: {repr id}") := by
  cases found : state.lookupValue id <;>
    simp [Sem.lookupValue, found, Sem.getState, Sem.throwTypeError,
      Sem.run, bind, StateT.bind, StateT.get, StateT.run, pure, StateT.pure,
      throw, throwThe, MonadExceptOf.throw, Except.bind, Except.pure, StateT.lift]

/-- With actual thin pointer operands, construction only binds its result.
    The hypotheses must be derived for an original input before this theorem
    can justify eliminating an unused construction. They are not certificates
    for arbitrary Undef operands or for the Rust coercion. -/
theorem construct_trait_pointer (state : MachineState) (dataId metadataId : ValueId)
    (traitId : UInt32) (data metadata : Nat) (dataProv metadataProv : Option AllocId)
    (dataFound : state.lookupValue dataId = some (.ptr data dataProv))
    (metadataFound : state.lookupValue metadataId = some (.ptr metadata metadataProv)) :
    Sem.run (semPtrFromParts (.FatPtr (.TraitObject traitId)) .Ptr dataId metadataId)
      state = .ok (state.bindValue (.fatPtr data dataProv (.ptr metadata metadataProv))) := by
  simp [semPtrFromParts, Sem.run_bind, lookup_run, Sem.rejectPartial, Sem.run_pure,
    dataFound, metadataFound, metadataTyMatchesFor, metadataTyMatches,
    metadataInhabitsFor, metadataInhabits, FatPtrKind.metadataTy,
    fatPtrFromPartsValue, Except.bind]
  rfl

/-- A dead result does not make poison inspection safe. This is why an
    unconditional dead-instruction deletion would not follow from the positive
    theorem, even though the captured native bundle never uses the result. -/
theorem undef_data_refused (state : MachineState) (dataId metadataId : ValueId)
    (traitId : UInt32) (metadata : Value)
    (dataFound : state.lookupValue dataId = some (.undef .Ptr))
    (metadataFound : state.lookupValue metadataId = some metadata) :
    ∃ error, Sem.run
      (semPtrFromParts (.FatPtr (.TraitObject traitId)) .Ptr dataId metadataId)
      state = .error error := by
  unfold semPtrFromParts
  simp only [Sem.run_bind, lookup_run, dataFound, metadataFound, Except.bind]
  simp [Sem.rejectPartial, Except.bind, Sem.throwUB, Sem.run, bind, StateT.bind,
    StateT.run, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw,
    Except.pure, StateT.lift]

/-- A defined data pointer does not make poisoned metadata safe. Both lanes
    must be derived before the construction theorem can apply. -/
theorem undef_metadata_refused (state : MachineState) (dataId metadataId : ValueId)
    (traitId : UInt32) (data : Nat) (dataProv : Option AllocId)
    (dataFound : state.lookupValue dataId = some (.ptr data dataProv))
    (metadataFound : state.lookupValue metadataId = some (.undef .Ptr)) :
    ∃ error, Sem.run
      (semPtrFromParts (.FatPtr (.TraitObject traitId)) .Ptr dataId metadataId)
      state = .error error := by
  unfold semPtrFromParts
  simp only [Sem.run_bind, lookup_run, dataFound, metadataFound, Except.bind]
  simp [Sem.rejectPartial, Except.bind, Sem.throwUB, Sem.run, bind, StateT.bind,
    StateT.run, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw,
    Except.pure, StateT.lift]

#print axioms construct_trait_pointer
#print axioms undef_data_refused
#print axioms undef_metadata_refused

end PointerPartsOperational
