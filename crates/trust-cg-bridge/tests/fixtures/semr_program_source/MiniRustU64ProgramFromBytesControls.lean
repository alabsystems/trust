/- Closed controls for the actual complete-byte construction. False goals
   deliberately have no proof; the independent checker must report TypeMismatch. -/
import MiniRustU64ProgramFromBytes
import MiniRustU64ScalarFixtures
import MiniRustU64ExitControls
set_option autoImplicit false
noncomputable section
namespace MiniRustU64ProgramFromBytesControls
open SemR MiniRustU64ProgramFromBytes MiniRustU64ScalarFixtures
  MiniRustU64ExitProgram MiniRustU64ExitExecution
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def ThreeClaims (bytes : List Nat) (literal : Nat) : Prop :=
  Construction bytes literal ∧ Correspondence bytes literal ∧ Available bytes literal

theorem three_claims (bytes : List Nat) (literal : Nat)
    (decoded : SemRU64ScalarProfile.Decodes bytes literal)
    (valid : literal < modulus 64) : ThreeClaims bytes literal :=
  ⟨construction bytes literal decoded valid,
    correspondence bytes literal decoded valid, available bytes literal decoded valid⟩

def Zero : Prop := ThreeClaims zeroBytes 0
theorem zero : Zero := three_claims zeroBytes 0 zero_decodes (by decide)

/-- This actual fixture also renames the module and function. -/
def Eight : Prop := ThreeClaims fresh8Bytes 8
theorem eight : Eight := three_claims fresh8Bytes 8 fresh8_decodes (by decide)

def Max : Prop := ThreeClaims maxBytes 18446744073709551615
theorem max : Max := three_claims maxBytes _ max_decodes (by decide)

def Current63 : Prop := ThreeClaims current63Bytes 7
theorem current63 : Current63 := three_claims current63Bytes 7 current63_decodes (by decide)

def SemanticSubRefused : Prop := construct subBytes 0 = none
theorem semanticSubRefused : SemanticSubRefused := by rfl

def OutOfRangeRefused : Prop := construct zeroBytes (modulus 64) = none
theorem outOfRangeRefused : OutOfRangeRefused := refuses_input zeroBytes _ (by decide)

def ModelZero : Prop := (construct zeroBytes 0).map Prod.snd = some (exitProgram 0 0)
theorem modelZero : ModelZero := by rfl

def EndpointZero : Prop :=
  SOut.runOracle executionOracle (fun _ => 0) (execute 0 zeroBytes 0) =
    .ok (.ok (.err .MachineStop, normalState 0 0))
theorem endpointZero : EndpointZero :=
  available zeroBytes 0 zero_decodes (by decide) 0 0 (by decide)

def WrongConstructor : Prop :=
  (construct zeroBytes 0).map Prod.snd = some (exitProgram 8 0)

def WrongLiteral : Prop :=
  SOut.runOracle executionOracle (fun _ => 0) (execute 0 zeroBytes 0) =
    .ok (.ok (.err .MachineStop, normalState 8 0))

def WrongWorld : Prop :=
  SOut.runOracle executionOracle (fun _ => 0) (execute 0 zeroBytes 0) =
    .ok (.ok (.err .MachineStop, MiniRustU64ExitControls.deadRootState))

def WrongStop : Prop :=
  SOut.runOracle executionOracle (fun _ => 0) (execute 0 zeroBytes 0) =
    .ok (.ok (.err (.Ub "the start function must not return"), normalState 0 0))

#print axioms zero
#print axioms eight
#print axioms max
#print axioms endpointZero
end MiniRustU64ProgramFromBytesControls
