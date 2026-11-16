/- Actual original-source-fixed packet02 Module mutations. These are precise
   observations of the unchanged evaluator at stated inputs/budgets, not a
   claim that every code mutation is rejected or that DATA has source authority.
   Fixed pretty-wire equations for these same constants are separate. -/
import CanonicalClosureObservation
import Lean.Elab.Tactic.Cbv

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64
set_option maxRecDepth 2048

theorem original_observation : observe ActualClosureModuleData.proposedModule =
    .ok (.ok [word 13]) := by cbv

theorem changed_operator_observation : observe ActualClosureMutantData.targetMulToAdd =
    .ok (.ok [word 10]) := by cbv

/-- This wrong target is the same-shaped original caller. It is accepted by
    the shape contract and recurses; this stated finite budget is exhausted.
    This is not a generic code-identity rejection or divergence theorem. -/
theorem wrong_target_observation : observe ActualClosureMutantData.wrongTarget =
    .ok (.error .outOfFuel) := by cbv

theorem swapped_captures_observation : observe ActualClosureMutantData.swappedCaptures =
    .ok (.ok [word 17]) := by cbv

theorem erased_parameter_observation : observe ActualClosureMutantData.erasedTargetParam =
    .ok (.error (.typeError "closure target does not have captures ++ apparent signature")) := by cbv

theorem application_arity_observation : observe ActualClosureMutantData.applyArity =
    .ok (.error (.typeError "CallIndirect: closure argument arity mismatch")) := by cbv

theorem target_convention_observation : observe ActualClosureMutantData.targetConventionC =
    .ok (.error (.typeError "CallIndirect: closure calling convention mismatch")) := by cbv

/-- The omitted application's header also prevents the original caller's
    result declarations from being constructed. It remains in functionErrors. -/
theorem omitted_original_observation : observe ActualClosureMutantData.omittedOriginal =
    .ok (.error (.typeError "evalFunctionInContext: undefined entry function")) := by cbv

theorem omitted_original_error_retained :
    (contextOf ActualClosureMutantData.omittedOriginal 3).map
      (fun ctx => (ctx.functionErrors callerId).isSome) = .ok true := rfl

theorem omitted_original_roster : ActualClosureMutantData.omittedOriginal.functions.map (·.id) =
    [callerId, makerId, targetId] := rfl

theorem omitted_roster_differs :
    ActualClosureMutantData.omittedOriginal.functions.map (·.id) ≠
      ActualClosureModuleData.proposedModule.functions.map (·.id) := by decide

theorem observations_differ_of_eq (left right first second : D (Except SemError (List Value)))
    (leftEq : left = first) (rightEq : right = second) (different : first ≠ second) : left ≠ right :=
  fun same => different (leftEq.symm.trans (same.trans rightEq))

theorem all_seven_observations_differ :
    observe ActualClosureMutantData.targetMulToAdd ≠ observe ActualClosureModuleData.proposedModule ∧
    observe ActualClosureMutantData.wrongTarget ≠ observe ActualClosureModuleData.proposedModule ∧
    observe ActualClosureMutantData.swappedCaptures ≠ observe ActualClosureModuleData.proposedModule ∧
    observe ActualClosureMutantData.erasedTargetParam ≠ observe ActualClosureModuleData.proposedModule ∧
    observe ActualClosureMutantData.applyArity ≠ observe ActualClosureModuleData.proposedModule ∧
    observe ActualClosureMutantData.targetConventionC ≠ observe ActualClosureModuleData.proposedModule ∧
    observe ActualClosureMutantData.omittedOriginal ≠ observe ActualClosureModuleData.proposedModule := by
  exact ⟨observations_differ_of_eq _ _ _ _ changed_operator_observation original_observation
      (by intro impossible; cases impossible),
    observations_differ_of_eq _ _ _ _ wrong_target_observation original_observation
      (by intro impossible; cases impossible),
    observations_differ_of_eq _ _ _ _ swapped_captures_observation original_observation
      (by intro impossible; cases impossible),
    observations_differ_of_eq _ _ _ _ erased_parameter_observation original_observation
      (by intro impossible; cases impossible),
    observations_differ_of_eq _ _ _ _ application_arity_observation original_observation
      (by intro impossible; cases impossible),
    observations_differ_of_eq _ _ _ _ target_convention_observation original_observation
      (by intro impossible; cases impossible),
    observations_differ_of_eq _ _ _ _ omitted_original_observation original_observation
      (by intro impossible; cases impossible)⟩

#print axioms changed_operator_observation
#print axioms swapped_captures_observation
#print axioms all_seven_observations_differ
end CanonicalClosure
