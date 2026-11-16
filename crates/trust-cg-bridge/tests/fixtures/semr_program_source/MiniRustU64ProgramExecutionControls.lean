/- Closed controls for the real Returning program. Wrong claims below have no
   proof; the maintained independent Clean reader must reject their rebinding. -/
import MiniRustU64ProgramExecution
set_option autoImplicit false
noncomputable section
namespace MiniRustU64ProgramExecutionControls
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64ProgramStart
  MiniRustU64ProgramReturn MiniRustU64ProgramExecution
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def Zero : Prop := SOut.runOracle executionOracle (fun _ => 0) (executeReturning 0 0 0) =
  .ok (.ok (.err (.Ub "the start function must not return"), returnedState 0 0))
theorem zero : Zero := returning_available 0 0 0 (by decide) (by decide)

def Eight : Prop := SOut.runOracle executionOracle (fun _ => 0) (executeReturning 0 8 8) =
  .ok (.ok (.err (.Ub "the start function must not return"), returnedState 8 8))
theorem eight : Eight := returning_available 0 8 8 (by decide) (by decide)

def Max : Prop := SOut.runOracle executionOracle (fun _ => 0)
    (executeReturning 0 (modulus 64 - 1) (modulus 64 - 1)) =
  .ok (.ok (.err (.Ub "the start function must not return"), returnedState (modulus 64 - 1) (modulus 64 - 1)))
theorem max : Max := returning_available 0 _ _ (by decide) (by decide)

def Colliding : Prop := SOut.runOracle (fun _ => 0) (fun _ => 0) (executeReturning 0 8 8) = .reject
theorem colliding : Colliding := by
  unfold Colliding
  rw [execute_returning_exact 0 8 8 (by decide) (by decide)]
  rfl

/-- Wrong semantic literal: the executed program is unchanged, but every
    claimed field of its result is rebound to the different literal. -/
def WrongLiteral : Prop := SOut.runOracle executionOracle (fun _ => 0) (executeReturning 0 0 0) =
  .ok (.ok (.err (.Ub "the start function must not return"), returnedState 8 0))

/-- Wrong complete world: the root allocation is resurrected in place. -/
def liveRootState : MR_Machine :=
  single (initialized 0 0 1 2 3) []
    ⟨⟨functionWorld 1 2 ++
      [zeroSlot .Stack 3, (slot 8 (u64bytes 0)).set_live false,
       (slot 16 (u64bytes 0)).set_live false, (slot 24 (u64bytes 0)).set_live false], ()⟩,
      [⟨.Load, .None, 3, 0⟩]⟩
def WrongWorld : Prop := SOut.runOracle executionOracle (fun _ => 0) (executeReturning 0 0 0) =
  .ok (.ok (.err (.Ub "the start function must not return"), liveRootState))

/-- Normal MachineStop is not the actual Returning-entry outcome. -/
def WrongMachineStop : Prop := SOut.runOracle executionOracle (fun _ => 0) (executeReturning 0 0 0) =
  .ok (.ok (.err .MachineStop, returnedState 0 0))

def WrongSuccess : Prop := SOut.runOracle executionOracle (fun _ => 0) (executeReturning 0 0 0) =
  .ok (.ok (.ok (), returnedState 0 0))

#print axioms zero
#print axioms eight
#print axioms max
#print axioms colliding
end MiniRustU64ProgramExecutionControls
