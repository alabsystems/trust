/- Closed controls for the separately constructed real Exit program. False
   claims have no proofs and must produce genuine independent TypeMismatch. -/
import MiniRustU64ExitExecution
set_option autoImplicit false
noncomputable section
namespace MiniRustU64ExitControls
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64ExitStart
  MiniRustU64ExitStop MiniRustU64ExitExecution MiniRustProgramExit MiniRustAllocate8Safety
open MiniRustU64ProgramExecution (functionWorld)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def Zero : Prop := SOut.runOracle executionOracle (fun _ => 0) (executeExit 0 0 0) =
  .ok (.ok (.err .MachineStop, normalState 0 0))
theorem zero : Zero := exit_available 0 0 0 (by decide) (by decide)

def Eight : Prop := SOut.runOracle executionOracle (fun _ => 0) (executeExit 0 8 8) =
  .ok (.ok (.err .MachineStop, normalState 8 8))
theorem eight : Eight := exit_available 0 8 8 (by decide) (by decide)

def Max : Prop := SOut.runOracle executionOracle (fun _ => 0)
    (executeExit 0 (modulus 64 - 1) (modulus 64 - 1)) =
  .ok (.ok (.err .MachineStop, normalState (modulus 64 - 1) (modulus 64 - 1)))
theorem max : Max := exit_available 0 _ _ (by decide) (by decide)

def Colliding : Prop := SOut.runOracle (fun _ => 0) (fun _ => 0) (executeExit 0 8 8) = .reject
theorem colliding : Colliding := by
  unfold Colliding
  rw [execute_exit_exact 0 8 8 (by decide) (by decide)]
  rfl

def heapAllocation (live : Bool) : MR_Allocation := ⟨uninit8, 32, 8, .Heap, live, ()⟩
def heapMachine (live : Bool) : MR_Machine :=
  (normalState 0 0).set_mem ⟨⟨[heapAllocation live], ()⟩, []⟩

/-- Primitive control, not a claim that this changed raw state was produced
    by startup. The actual leak checker must not discard a live outside Heap. -/
def HeapLeak : Prop := MRf.Machine.exit 3 (heapMachine true) = .ok (.err .MemoryLeak)
theorem heapLeak : HeapLeak := machine_exit_exact 0 (heapMachine true)

def DeadHeap : Prop := MRf.Machine.exit 3 (heapMachine false) = .ok (.err .MachineStop)
theorem deadHeap : DeadHeap := machine_exit_exact 0 (heapMachine false)

def WrongLiteral : Prop := SOut.runOracle executionOracle (fun _ => 0) (executeExit 0 0 0) =
  .ok (.ok (.err .MachineStop, normalState 8 0))

/-- False world conversion: Exit does not retire the root Stack allocation. -/
def deadRootState : MR_Machine :=
  single (initialized 0 0 1 2 3) [exitFrame 0 (MiniRustU64Function.ptr 2 3) (MiniRustU64Function.ptr 3 8)]
    (MiniRustU64ProgramReturn.deadRootMemory (functionWorld 1 2)
      [(slot 16 (u64bytes 0)).set_live false, (slot 24 (u64bytes 0)).set_live false]
      3 8 (u64bytes 0) [])
def WrongWorld : Prop := SOut.runOracle executionOracle (fun _ => 0) (executeExit 0 0 0) =
  .ok (.ok (.err .MachineStop, deadRootState))

def WrongStop : Prop := SOut.runOracle executionOracle (fun _ => 0) (executeExit 0 0 0) =
  .ok (.ok (.err (.Ub "the start function must not return"), normalState 0 0))

def WrongLeak : Prop := MRf.Machine.exit 3 (heapMachine true) = .ok (.err .MachineStop)

#print axioms zero
#print axioms eight
#print axioms max
#print axioms colliding
#print axioms heapLeak
#print axioms deadHeap
end MiniRustU64ExitControls
