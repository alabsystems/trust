/- Budget and surrounding-world controls for the actual canonical context.
   A successful run is never a premise of these execution conclusions. -/
import CanonicalClosurePublic
import ClosureU64Controls

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64 TrustIr.GenericCoro.Prefix
set_option maxRecDepth 2048

theorem all_five_signature_rows (depth : Nat) :
    (context depth).funcTys ⟨0⟩ = some
      { params := [.U64], returns := [.U64], isVararg := false } ∧
    (context depth).funcTys ⟨1⟩ = some
      { params := [.U64, .U64, .U64], returns := [.U64], isVararg := false } ∧
    (context depth).funcTys ⟨2⟩ = some
      { params := [.U64, .U64], returns := [.Closure nominal], isVararg := false } ∧
    (context depth).funcTys ⟨3⟩ = some
      { params := [.Closure nominal, .U64], returns := [.U64], isVararg := false } ∧
    (context depth).funcTys ⟨4⟩ = some
      { params := [.U64, .U64, .U64], returns := [.U64], isVararg := false } := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nominal_closure_table (depth : Nat) : (context depth).closures nominal =
    some { func := apparent, captures := [.U64, .U64] } := rfl

theorem application_indirect_low_fuel_step (depth : Nat) (world : MachineState)
    (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt 0) (applicationContext depth) (depth + 2) .abort
      (.CallIndirect (valueId 0) apparent [valueId 1] .Rust, [valueId 2]))
      (applicationEntry world a b x) = .error .outOfFuel := by
  rw [typed_dispatch_runs (recurseAt 0) (applicationContext depth) (depth + 1) .abort
    (valueId 0) apparent [valueId 1] [valueId 2] .Rust nominal targetId
    [word a, word b] [word x] [word a, word b, word x] target
    (applicationEntry world a b x) (lookup_application_closure world a b x)
    (lookup_application_arguments world a b x) (application_arguments_exact depth a b x)
    (by rfl) (by rfl) (by rfl) (three_words_not_poison a b x "CallIndirect arguments")]
  apply invoke_closure_target_errors
  · rfl
  · rfl

theorem application_low_fuel (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (applicationContext depth) 1 (depth + 2) application.cfg ⟨0⟩
      [closure a b, word x]) (entryState world) = .error .outOfFuel := by
  rw [stepNWithContext_succ_layer]
  apply run_failing_layer (block := ClosureU64.applicationBlock)
    (bound := applicationEntry world a b x)
  · exact application_block
  · rfl
  · exact application_parameters world a b x
  · unfold evalBody
    exact run_body_head_failure _ _ _ _ _ (application_indirect_low_fuel_step depth world a b x)

theorem application_indirect_low_depth_step (fuel depth : Nat) (world : MachineState)
    (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt fuel) (applicationContext depth) 0 .abort
      (.CallIndirect (valueId 0) apparent [valueId 1] .Rust, [valueId 2]))
      (applicationEntry world a b x) = .error .outOfFuel := by
  unfold evalBodyStep
  simp only [bind]
  rw [run_bind, lookup_application_closure]
  dsimp only [Except.bind, closure]
  simp only [pure]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [run_bind, lookup_application_arguments]
  rfl

theorem application_low_depth (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (applicationContext depth) 2 0 application.cfg ⟨0⟩
      [closure a b, word x]) (entryState world) = .error .outOfFuel := by
  rw [stepNWithContext_succ_layer]
  apply run_failing_layer (block := ClosureU64.applicationBlock)
    (bound := applicationEntry world a b x)
  · exact application_block
  · rfl
  · exact application_parameters world a b x
  · unfold evalBody
    exact run_body_head_failure _ _ _ _ _ (application_indirect_low_depth_step 1 depth world a b x)

theorem caller_application_low_fuel_step (depth : Nat) (world : MachineState)
    (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt 1) (callerContext depth) (depth + 3) .abort
      (.Call applyId [valueId 3, valueId 2], [valueId 4]))
      (callerPartial world a b x) = .error .outOfFuel := by
  rw [direct_dispatch_runs (recurseAt 1) (callerContext depth) (depth + 2) .abort
    applyId [valueId 3, valueId 2] [valueId 4] [closure a b, word x] application
    (callerPartial world a b x) (lookup_caller_apply_arguments world a b x)
    (application_direct_lookup depth) (by rfl) (by rfl)
    (closure_and_word_not_poison a b x "Call arguments")]
  apply invoke_direct_errors
  · rfl
  · rw [for_application, reset_caller_second]
    exact application_low_fuel depth world a b x

theorem caller_application_low_depth_step (depth : Nat) (world : MachineState)
    (a b x : UInt64) :
    Sem.run (evalBodyStep (recurseAt 2) (callerContext depth) 1 .abort
      (.Call applyId [valueId 3, valueId 2], [valueId 4]))
      (callerPartial world a b x) = .error .outOfFuel := by
  rw [direct_dispatch_runs (recurseAt 2) (callerContext depth) 0 .abort
    applyId [valueId 3, valueId 2] [valueId 4] [closure a b, word x] application
    (callerPartial world a b x) (lookup_caller_apply_arguments world a b x)
    (application_direct_lookup depth) (by rfl) (by rfl)
    (closure_and_word_not_poison a b x "Call arguments")]
  apply invoke_direct_errors
  · rfl
  · rw [for_application, reset_caller_second]
    exact application_low_depth depth world a b x

theorem caller_low_fuel (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (callerContext depth) 2 (depth + 3) caller.cfg ⟨0⟩
      [word a, word b, word x]) (entryState world) = .error .outOfFuel := by
  rw [stepNWithContext_succ_layer]
  apply run_failing_layer (block := ClosureU64.callerBlock) (bound := tripleState world a b x)
  · exact caller_block
  · rfl
  · exact caller_parameters world a b x
  · unfold evalBody
    apply run_body_tail_failure (middle := callerPartial world a b x)
    · exact caller_maker_step 0 depth (depth + 2) world a b x
    · exact run_body_head_failure _ _ _ _ _ (caller_application_low_fuel_step depth world a b x)

theorem caller_low_depth (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (callerContext depth) 3 1 caller.cfg ⟨0⟩
      [word a, word b, word x]) (entryState world) = .error .outOfFuel := by
  rw [stepNWithContext_succ_layer]
  apply run_failing_layer (block := ClosureU64.callerBlock) (bound := tripleState world a b x)
  · exact caller_block
  · rfl
  · exact caller_parameters world a b x
  · unfold evalBody
    apply run_body_tail_failure (middle := callerPartial world a b x)
    · exact caller_maker_step 1 depth 0 world a b x
    · exact run_body_head_failure _ _ _ _ _ (caller_application_low_depth_step depth world a b x)

theorem surrounding_world_execution :
    Sem.run (evalFunctionInContext (context 0) callerId [word 2, word 3, word 5] 3 .abort)
      (entryState surroundingWorld) =
      .ok ([word 13], callerState surroundingWorld 2 3 5) ∧
    (callerState surroundingWorld 2 3 5).memory = surroundingMemory ∧
    (callerState surroundingWorld 2 3 5).memory.bytes 1027 = some 165 ∧
    { callerState surroundingWorld 2 3 5 with
      locals := surroundingWorld.locals, nextValueId := surroundingWorld.nextValueId } =
      surroundingWorld := by
  exact ⟨caller_evaluates 0 surroundingWorld 2 3 5, rfl,
    surrounding_sentinel_present, caller_world_restored surroundingWorld 2 3 5⟩

#print axioms caller_low_fuel
#print axioms caller_low_depth
#print axioms surrounding_world_execution
end CanonicalClosure
