
-- Hand-written vectors for the generated slice's one angelic prediction,
-- `MRf.IntPtrCast.int2ptr` (MiniRust mem/intptrcast.md: `predict` the provenance
-- among the exposed allocations, or none). No minitest of the slice reaches
-- int2ptr, so these are its semantic tests: K8's least candidate is `none`; an
-- oracle naming an exposed allocation gets that provenance; one naming an
-- allocation that was not exposed is rejected (not a behaviour); and the decoder
-- reaches far allocations (index 1000 names AllocId 999).
-- Checked after SpecrPrelude.lean, PreludeVectors.lean and the slice by
-- `regen.py check --clean`.
theorem v_int2ptr_least : SOut.runLeast 100 (MRf.IntPtrCast.int2ptr 5 (MR_IntPtrCast.mk [(MR_AllocId.mk 3, ())]) 4096) = SOut.ok (SRes.ok (MR_ThinPointer.mk 4096 none) : SRes MR_TerminationInfo MR_ThinPointer) := rfl
theorem v_int2ptr_exposed : SOut.runOracle (fun (_ : List Nat) => 0) (fun (_ : List Nat) => 4) (MRf.IntPtrCast.int2ptr 5 (MR_IntPtrCast.mk [(MR_AllocId.mk 3, ())]) 4096) = SOut.ok (SRes.ok (MR_ThinPointer.mk 4096 (some (MR_AllocId.mk 3, ()))) : SRes MR_TerminationInfo MR_ThinPointer) := rfl
theorem v_int2ptr_unexposed : SOut.runOracle (fun (_ : List Nat) => 0) (fun (_ : List Nat) => 2) (MRf.IntPtrCast.int2ptr 5 (MR_IntPtrCast.mk [(MR_AllocId.mk 3, ())]) 4096) = SOut.reject := rfl
theorem v_int2ptr_far : SOut.runOracle (fun (_ : List Nat) => 0) (fun (_ : List Nat) => 1000) (MRf.IntPtrCast.int2ptr 5 (MR_IntPtrCast.mk [(MR_AllocId.mk 999, ())]) 4096) = SOut.ok (SRes.ok (MR_ThinPointer.mk 4096 (some (MR_AllocId.mk 999, ()))) : SRes MR_TerminationInfo MR_ThinPointer) := rfl
theorem v_int2ptr_none : SOut.runOracle (fun (_ : List Nat) => 0) (fun (_ : List Nat) => 0) (MRf.IntPtrCast.int2ptr 5 (MR_IntPtrCast.mk []) 4096) = SOut.ok (SRes.ok (MR_ThinPointer.mk 4096 none) : SRes MR_TerminationInfo MR_ThinPointer) := rfl
