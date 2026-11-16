/- Complete decoded scalar bytes → actual generated MiniRust Exit program.
   This closes the byte/model construction step, not Rust frontend refinement. -/
import MiniRustU64ExitExecution
set_option autoImplicit false
noncomputable section
namespace MiniRustU64ProgramFromBytes
open SemR MiniRustU64ExitProgram MiniRustU64ExitExecution
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A total fail-closed constructor over the actual complete decoder result.
    The original decoded view retains the actual function name and target.
    The C/unit Exit entry is an explicit model harness around that callee;
    it is not claimed to be a Rust frontend-generated process entry. -/
def construct (bytes : List Nat) (input : Nat) :
    Option (SemRU64ScalarProfile.View × MR_Program) :=
  match decode bytes with
  | .error _ => none
  | .ok module =>
    if module.executableTarget then
      match SemRU64ScalarProfile.classify module with
      | none => none
      | some view =>
        if view.literal < modulus 64 ∧ input < modulus 64 then
          some (view, exitProgram view.literal input)
        else none
    else none

/-- The host supplies a closed proof of this decision, not a range flag. -/
theorem literal_valid (literal : Nat)
    (checked : decide (literal < modulus 64) = true) : literal < modulus 64 :=
  of_decide_eq_true checked

theorem refuses_decode (bytes : List Nat) (input : Nat) (failure : DErr)
    (failed : decode bytes = .error failure) : construct bytes input = none := by
  simp only [construct, failed]

theorem refuses_target (bytes : List Nat) (input : Nat) (module : Module)
    (decoded : decode bytes = .ok module) (rejected : module.executableTarget = false) :
    construct bytes input = none := by
  simp only [construct, decoded, rejected, Bool.false_eq_true, ite_false]

theorem refuses_shape (bytes : List Nat) (input : Nat) (module : Module)
    (decoded : decode bytes = .ok module)
    (rejected : SemRU64ScalarProfile.classify module = none) :
    construct bytes input = none := by
  simp [construct, decoded, rejected]

theorem refuses_input (bytes : List Nat) (input : Nat)
    (outside : ¬ input < modulus 64) : construct bytes input = none := by
  cases decoded : decode bytes with
  | error failure => simp [construct, decoded]
  | ok module =>
    cases target : module.executableTarget with
    | false => simp [construct, decoded, target]
    | true =>
      cases shape : SemRU64ScalarProfile.classify module with
      | none => simp [construct, decoded, target, shape]
      | some view => simp [construct, decoded, target, shape, outside]

/-- Exact initial IR Core and complete actual constructed program, derived
    from the same bytes. No successful machine startup/execution is a premise. -/
def Construction (bytes : List Nat) (literal : Nat) : Prop :=
  literal < modulus 64 ∧
  ∀ input depth : Nat, input < modulus 64 →
    ∃ view : SemRU64ScalarProfile.View,
      decode bytes = .ok (SemRU64ScalarProfile.module view) ∧
      view.literal = literal ∧
      (SemRU64ScalarProfile.module view).executableTarget = true ∧
      construct bytes input = some (view, exitProgram literal input) ∧
      start (SemRU64ScalarProfile.module view) 0 [.int .u64 input] depth =
        .ok (SemRU64ScalarProfile.initial view input depth Mem.empty)

theorem construction (bytes : List Nat) (literal : Nat)
    (decoded : SemRU64ScalarProfile.Decodes bytes literal)
    (literalValid : literal < modulus 64) : Construction bytes literal := by
  refine ⟨literalValid, ?_⟩
  intro input depth inputValid
  obtain ⟨view, exactDecode, sameLiteral, executable⟩ :=
    SemRU64ScalarProfile.decoded_module bytes literal decoded
  refine ⟨view, exactDecode, sameLiteral, executable, ?_, ?_⟩
  · simp only [construct, exactDecode, executable, ite_true,
      MiniRustU64ScalarCorrespondence.classified_module, sameLiteral]
    rw [if_pos ⟨literalValid, inputValid⟩]
  · exact SemRU64ScalarProfile.start_exact view input depth executable inputValid

theorem construct_exact (bytes : List Nat) (literal input : Nat)
    (decoded : SemRU64ScalarProfile.Decodes bytes literal)
    (literalValid : literal < modulus 64) (inputValid : input < modulus 64) :
    ∃ view : SemRU64ScalarProfile.View,
      construct bytes input = some (view, exitProgram literal input) := by
  obtain ⟨view, _, _, _, constructed, _⟩ :=
    (construction bytes literal decoded literalValid).2 input 0 inputValid
  exact ⟨view, constructed⟩

/-- Execute precisely the program produced by the byte constructor. Decoder,
    target, shape and full64 failures reject before Machine.new. Actual startup
    and all five generated steps/error/scheduler/allocation choices are retained. -/
def execute (fuel : Nat) (bytes : List Nat) (input : Nat) :=
  match construct bytes input with
  | none => SOut.reject
  | some bound =>
    (MRf.Machine.new (fuel + 81) bound.2 () () ()).bind (continueNew fuel)

theorem execute_exact (fuel literal input : Nat) (bytes : List Nat)
    (decoded : SemRU64ScalarProfile.Decodes bytes literal)
    (literalValid : literal < modulus 64) (inputValid : input < modulus 64) :
    execute fuel bytes input = executeExit fuel literal input := by
  obtain ⟨view, constructed⟩ := construct_exact bytes literal input decoded literalValid inputValid
  simp only [execute, constructed]
  rfl

/-- The same full bytes have their actual IR Core execution and a real complete
    generated-machine endpoint. ExitObservation retains all machine/world data;
    no new frame, successful call, run or NoUB premise replaces the theorem. -/
def Correspondence (bytes : List Nat) (literal : Nat) : Prop :=
  ∀ fuel input depth : Nat, input < modulus 64 →
    runBlob bytes 0 [.int .u64 input] 3 depth =
      .ok (.ret [.int .u64 ((input + literal) % modulus 64)]) ∧
    MiniRustU64Entry.EveryResult (ExitObservation literal input)
      (execute fuel bytes input)

theorem correspondence (bytes : List Nat) (literal : Nat)
    (decoded : SemRU64ScalarProfile.Decodes bytes literal)
    (literalValid : literal < modulus 64) : Correspondence bytes literal := by
  intro fuel input depth inputValid
  refine ⟨SemRU64ScalarProfile.returns bytes literal decoded input depth inputValid, ?_⟩
  rw [execute_exact fuel literal input bytes decoded literalValid inputValid]
  exact execute_exit_observed fuel literal input inputValid literalValid

/-- Constructive availability is required separately from the all-branches
    observation, so rejected choices cannot make the model fact vacuous. -/
def Available (bytes : List Nat) (literal : Nat) : Prop :=
  ∀ fuel input : Nat, input < modulus 64 →
    SOut.runOracle executionOracle (fun _ => 0) (execute fuel bytes input) =
      .ok (.ok (.err .MachineStop, normalState literal input))

theorem available (bytes : List Nat) (literal : Nat)
    (decoded : SemRU64ScalarProfile.Decodes bytes literal)
    (literalValid : literal < modulus 64) : Available bytes literal := by
  intro fuel input inputValid
  rw [execute_exact fuel literal input bytes decoded literalValid inputValid]
  exact exit_available fuel literal input inputValid literalValid

/-- Generated well-formedness concerns the actual constructed program, before
    startup. This is not a different validator or a caller success flag. -/
theorem constructed_wellformed (fuel literal input : Nat) (bytes : List Nat)
    (decoded : SemRU64ScalarProfile.Decodes bytes literal)
    (literalValid : literal < modulus 64) (inputValid : input < modulus 64) :
    ∃ view : SemRU64ScalarProfile.View,
      construct bytes input = some (view, exitProgram literal input) ∧
      MRf.Program.check_wf (fuel + 80) (exitProgram literal input) = .ok (.ok ()) := by
  obtain ⟨view, constructed⟩ := construct_exact bytes literal input decoded literalValid inputValid
  exact ⟨view, constructed, program_wellformed fuel literal input literalValid inputValid⟩

#print axioms construction
#print axioms correspondence
#print axioms available
end MiniRustU64ProgramFromBytes
