/- Exact generated leak/Exit semantics. This classifies all allocation kinds
   and both live flags; no successful leak check or normal-stop premise. -/
import MiniRustU64ProgramReturn
set_option autoImplicit false
noncomputable section
namespace MiniRustProgramExit
open SemR
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def liveHeap (allocation : MR_Allocation) : Bool :=
  allocation.live && match allocation.kind with | .Heap => true | _ => false

def anyLiveHeap : List MR_Allocation → Bool
  | [] => false
  | allocation :: rest => liveHeap allocation || anyLiveHeap rest

/-- The exact original per-allocation loop body, retained mechanically. -/
def leakOne (allocation : MR_Allocation) (_ : Unit) : SOut (SCtl Unit (SRes MR_TerminationInfo Unit)) :=
  match allocation.live with
  | false => .ok (.next ())
  | true => match allocation.kind with
    | .Heap => .ok (.ret (.err .MemoryLeak))
    | .Stack | .Global | .Function | .VTable => .ok (.next ())

theorem leak_one (allocation : MR_Allocation) :
    leakOne allocation () =
      .ok (if liveHeap allocation then .ret (.err .MemoryLeak) else .next ()) := by
  rcases allocation with ⟨data, addr, align, kind, live, extra⟩
  cases live <;> cases kind <;> rfl

theorem leak_loop (world : List MR_Allocation) :
    SLoop.forS world () leakOne =
      .ok (if anyLiveHeap world then .ret (.err .MemoryLeak) else .next ()) := by
  induction world with
  | nil => rfl
  | cons allocation rest ih =>
    rw [SLoop.forS, leak_one]
    cases h : liveHeap allocation <;>
      simp only [h, Bool.false_eq_true, ite_false, ite_true, SOut.bind_ok', anyLiveHeap,
        Bool.false_or, Bool.true_or] <;> first | exact ih | rfl

/-- Definitional connection to the complete original generated loop. This
    is not an independent evaluator or an assumed leak-check result. -/
theorem actual_leak (fuel : Nat) (world : List MR_Allocation) (extra : Unit) :
    MRf.BasicMemory.leak_check (fuel + 1) ⟨world, extra⟩ =
      (SLoop.forS world () leakOne).bind (fun control => match control with
        | .next _ | .brk _ => .ok (.ok ()) | .ret result => .ok result) := by
  simp only [MRf.BasicMemory.leak_check]
  apply congrArg (fun (body : MR_Allocation → Unit → SOut (SCtl Unit (SRes MR_TerminationInfo Unit))) => (SLoop.forS world () body).bind
    (fun control => match control with
      | .next _ | .brk _ => .ok (.ok ()) | .ret result => .ok result))
  funext allocation state
  rcases allocation with ⟨data, addr, align, kind, live, extra⟩
  cases live <;> cases kind <;> rfl

theorem leak_check_exact (fuel : Nat) (mem : MR_BasicMemory) :
    MRf.BasicMemory.leak_check (fuel + 1) mem =
      .ok (if anyLiveHeap mem.allocations then .err .MemoryLeak else .ok ()) := by
  cases mem with
  | mk world extra =>
    rw [actual_leak, leak_loop]
    cases h : anyLiveHeap world <;> rfl

theorem concurrent_leak_exact (fuel : Nat) (mem : MR_ConcurrentMemory) :
    MRf.ConcurrentMemory.leak_check (fuel + 2) mem =
      .ok (if anyLiveHeap mem.memory.allocations then .err .MemoryLeak else .ok ()) := by
  simp only [MRf.ConcurrentMemory.leak_check]
  rw [leak_check_exact]
  rfl

/-- MachineStop is the original model's termination-info constructor, carried
    by SRes.err. Live Heap allocations instead produce actual MemoryLeak. -/
theorem machine_exit_exact (fuel : Nat) (machine : MR_Machine) :
    MRf.Machine.exit (fuel + 3) machine =
      .ok (.err (if anyLiveHeap machine.mem.memory.allocations then .MemoryLeak else .MachineStop)) := by
  simp only [MRf.Machine.exit]
  rw [concurrent_leak_exact]
  cases h : anyLiveHeap machine.mem.memory.allocations <;> rfl

/-- Full original Exit intrinsic constructor for arbitrary arguments/type.
    Exit does not return a value; its error/stop path preserves the machine. -/
theorem intrinsic_exit_shape (fuel : Nat) (machine : MR_Machine)
    (arguments : List (MR_Value × MR_Type)) (retTy : MR_Type) :
    MRf.Machine.eval_intrinsic (fuel + 1) machine .Exit arguments retTy =
      (MRf.Machine.exit fuel machine).bind (fun result => match result with
        | .ok _ => .panic "value of the never type"
        | .err error => .ok (.err error, machine)) := rfl

theorem intrinsic_exit_exact (fuel : Nat) (machine : MR_Machine)
    (arguments : List (MR_Value × MR_Type)) (retTy : MR_Type) :
    MRf.Machine.eval_intrinsic (fuel + 4) machine .Exit arguments retTy =
      .ok (.err (if anyLiveHeap machine.mem.memory.allocations then .MemoryLeak else .MachineStop), machine) := by
  rw [intrinsic_exit_shape, machine_exit_exact]
  rfl

#print axioms leak_check_exact
#print axioms machine_exit_exact
#print axioms intrinsic_exit_exact
end MiniRustProgramExit
