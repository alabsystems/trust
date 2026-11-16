/- A projection of the existing evaluator result, keeping context failure,
   evaluator failure and successful values distinct. No new program syntax,
   evaluator or admission rule is introduced. -/
import CanonicalClosurePublic
import ActualClosureMutantData

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64

noncomputable def observe (source : Module) : D (Except SemError (List Value)) :=
  (contextOf source 3).map (fun ctx =>
    (Sem.run (evalFunctionInContext ctx callerId [word 2, word 3, word 5] 3 .abort)
      (entryState MachineState.empty)).map (·.1))

end CanonicalClosure
