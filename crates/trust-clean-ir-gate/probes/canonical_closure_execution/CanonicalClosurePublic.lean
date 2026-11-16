/- Each original/lifted function executes through the unchanged public
   contextual evaluator, with its own actual inferred local declarations. -/
import CanonicalClosureCalls

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64 TrustIr.GenericCoro.Prefix
set_option maxRecDepth 2048

theorem application_step_with_depth (depth remaining : Nat) (world : MachineState)
    (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt 1) (applicationContext depth) (remaining + 1) .abort
      (.CallIndirect (valueId 0) apparent [valueId 1] .Rust, [valueId 2]))
      (applicationEntry world a b x) = .ok (.yield (), applicationState world a b x) := by
  rw [typed_dispatch_runs (recurseAt 1) (applicationContext depth) remaining .abort
    (valueId 0) apparent [valueId 1] [valueId 2] .Rust nominal targetId
    [word a, word b] [word x] [word a, word b, word x] target
    (applicationEntry world a b x) (lookup_application_closure world a b x)
    (lookup_application_arguments world a b x) (application_arguments_exact depth a b x)
    (by rfl) (by rfl) (by rfl) (three_words_not_poison a b x "CallIndirect arguments")]
  apply invoke_closure_target_runs (calleeAfter := targetState world a b x)
    (retVals := [word (a * x + b)])
  · rfl
  · rw [for_target, reset_application]
    exact target_body_evaluates depth remaining world a b x
  · exact typed_return_word_runs _ _ _ _ _ _ _ (applicationEntry world a b x) _
      (by rfl) (restore_application world a b x) (application_result_bound depth world a b x)

theorem application_body_with_depth (depth remaining : Nat) (world : MachineState)
    (a b x : UInt64) :
    Sem.run (stepNWithContext (applicationContext depth) 2 (remaining + 1) application.cfg ⟨0⟩
      [closure a b, word x]) (entryState world) =
      .ok ([word (a * x + b)], applicationState world a b x) := by
  rw [stepNWithContext_succ_layer]
  apply run_returning_layer (block := ClosureU64.applicationBlock)
    (bound := applicationEntry world a b x) (bodyAfter := applicationState world a b x)
  · exact application_block
  · rfl
  · exact application_parameters world a b x
  · unfold evalBody
    exact run_single_body _ _ _ _ (application_step_with_depth depth remaining world a b x)
  · exact application_returns depth (remaining + 1) world a b x

theorem maker_evaluates (depth : Nat) (world : MachineState) (a b : UInt64) :
    Sem.run (evalFunctionInContext (context depth) makerId [word a, word b] 1 .abort)
      (entryState world) = .ok ([closure a b], makerState world a b) := by
  apply contextual_entry_runs (callee := maker)
  · exact maker_lookup depth
  · rfl
  · rfl
  · exact two_words_not_poison a b "Call arguments"
  · change Sem.run (exitUnwinding .abort
      (stepNWithContext (makerContext depth) 1 (depth + 3) maker.cfg ⟨0⟩
        [word a, word b] .abort)) (entryState world) = _
    simp only [exitUnwinding]
    exact maker_body_evaluates 0 depth (depth + 3) world a b
  · exact one_closure_not_poison a b "Call returns"

theorem target_evaluates (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalFunctionInContext (context depth) targetId [word a, word b, word x] 1 .abort)
      (entryState world) = .ok ([word (a * x + b)], targetState world a b x) := by
  apply contextual_entry_runs (callee := target)
  · exact target_lookup depth
  · rfl
  · rfl
  · exact three_words_not_poison a b x "Call arguments"
  · change Sem.run (exitUnwinding .abort
      (stepNWithContext (targetContext depth) 1 (depth + 3) target.cfg ⟨0⟩
        [word a, word b, word x] .abort)) (entryState world) = _
    simp only [exitUnwinding]
    exact target_body_evaluates depth (depth + 3) world a b x
  · exact one_word_not_poison (a * x + b) "Call returns"

theorem application_evaluates (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalFunctionInContext (context depth) applyId [closure a b, word x] 2 .abort)
      (entryState world) = .ok ([word (a * x + b)], applicationState world a b x) := by
  apply contextual_entry_runs (callee := application)
  · exact application_lookup depth
  · rfl
  · rfl
  · exact closure_and_word_not_poison a b x "Call arguments"
  · change Sem.run (exitUnwinding .abort
      (stepNWithContext (applicationContext depth) 2 (depth + 3) application.cfg ⟨0⟩
        [closure a b, word x] .abort)) (entryState world) = _
    simp only [exitUnwinding]
    exact application_body_with_depth depth (depth + 2) world a b x
  · exact one_word_not_poison (a * x + b) "Call returns"

#print axioms maker_evaluates
#print axioms target_evaluates
#print axioms application_evaluates
end CanonicalClosure
