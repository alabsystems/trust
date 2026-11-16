/- Composition interface for the separate fixed-wire decoder proof. A concrete
   final wire theorem must supply the module equation; no wire association is
   inferred here from a digest, DATA label or successful native producer. -/
import CanonicalClosureControls
import CanonicalClosureMutants

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64

noncomputable def runDecoded (decoded : D Module) (depth : Nat) (world : MachineState)
    (a b x : UInt64) : D (Except SemError (List Value × MachineState)) := do
  let source ← decoded
  let ctx ← contextOf source (depth + 3)
  pure (Sem.run (evalFunctionInContext ctx callerId [word a, word b, word x] 3 .abort)
    (entryState world))

/-- The premise is an exact decoder/Module equation, not returning execution.
    The caller execution itself is supplied constructively by caller_evaluates.
    This generic composition alone does not authenticate any concrete wire. -/
theorem run_decoded_caller (decoded : D Module)
    (moduleEquation : decoded = .ok ActualClosureModuleData.proposedModule)
    (depth : Nat) (world : MachineState) (a b x : UInt64) :
    runDecoded decoded depth world a b x =
      .ok (.ok ([word (a * x + b)], callerState world a b x)) := by
  unfold runDecoded
  rw [moduleEquation]
  simp only [bind, pure, Except.bind, Except.pure]
  rw [context_exact]
  simp only [bind, pure, Except.bind, Except.pure]
  rw [caller_evaluates]

noncomputable def observeDecoded (decoded : D Module) : D (Except SemError (List Value)) :=
  decoded.bind observe

theorem observe_decoded_exact (decoded : D Module) (source : Module)
    (moduleEquation : decoded = .ok source) : observeDecoded decoded = observe source := by
  unfold observeDecoded
  rw [moduleEquation]
  rfl

#print axioms run_decoded_caller
end CanonicalClosure
