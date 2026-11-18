-- Copyright 2026 Andrew Yates | Apache-2.0
import C11FragmentPhases
import CAtomicDropSource
import CAtomicIncrementSource

/-! Actual accepted byte fragments need no trigraph/splicing transformation.
This is an input-phase fact only, NOT source execution/TU/ABI/NoUB authority. -/
namespace C11ActualFragmentPhases

theorem drop_phase12_identity :
    C11FragmentPhases.mechanical12 CAtomicDropSource.actualSource =
      CAtomicDropSource.actualSource :=
  C11FragmentPhases.tokenized_phases_identity _ _ CAtomicDropSource.actual_tokens

theorem increment_phase12_identity :
    C11FragmentPhases.mechanical12 CAtomicIncrementSource.actualSource =
      CAtomicIncrementSource.actualSource :=
  C11FragmentPhases.tokenized_phases_identity _ _ CAtomicIncrementSource.actual_tokens

#print axioms drop_phase12_identity
#print axioms increment_phase12_identity
end C11ActualFragmentPhases
