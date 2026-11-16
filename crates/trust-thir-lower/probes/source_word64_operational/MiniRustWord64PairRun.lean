/- Actual pair Assign and Return scheduler composition. No source/ABI admission. -/
import MiniRustWord64PairStep
noncomputable section
namespace MiniRustWord64PairRun
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return
  MiniRustWord64PairFunction MiniRustWord64PairExecution MiniRustWord64PairReturn MiniRustU64Step
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- One actual single-thread scheduler layer around a continuation tree. -/
def scheduled {α : Type} (out : SOut α) : SOut α :=
  .pick (fun index => match index with | 0 => out | _ + 1 => .reject)

theorem choice_bind {α β : Type} (value : α) (next : α → SOut β) :
    (oneThreadChoice value).bind next = scheduled (next value) := by
  change SOut.pick _ = SOut.pick _
  apply congrArg SOut.pick
  funext index
  cases index <;> rfl

def nextStep (fuel : Nat) (result : SRes MR_TerminationInfo Unit × MR_Machine) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  match result with
  | (.ok _, machine) => MRf.Machine.step fuel machine
  | (.err error, machine) => .ok (.err error, machine)

/-- Two calls of the REAL scheduler/step operation; no alternate evaluator. -/
def twoSteps (fuel : Nat) (machine : MR_Machine) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  (MRf.Machine.step fuel machine).bind (nextStep fuel)

def exitState (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr retAddr leftAddr rightAddr value left right : Nat) : MR_Machine :=
  single base [(caller.set_next_block next).set_next_stmt 0]
    (retiredCells (callerWorld before after callerAddr (u64bytes value))
      retAddr leftAddr rightAddr value left right
      [⟨.Load, .None, Int.ofNat retAddr, 8⟩, ⟨.Store, .None, Int.ofNat callerAddr, 8⟩])

/-- Complete function BODY execution: genuine Assign and genuine Return,
    preserving both original scheduler choices and the complete final world. -/
theorem two_steps_exact (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (left right : Nat) (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr leftAddr rightAddr : Nat) (callerBytes retBytes : List MR_AbstractByte)
    (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (retLength : retBytes.length = 8)
    (callerAligned : callerAddr % 8 = 0) (retAligned : retAddr % 8 = 0)
    (leftAligned : leftAddr % 8 = 0) (rightAligned : rightAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    twoSteps (fuel + 50)
      (active base caller
        (localFrame (callerWorld before after callerAddr callerBytes) retAddr leftAddr rightAddr
          (.BackToCaller (some next) none (ptr before.length (Int.ofNat callerAddr))) 0)
        (cells (callerWorld before after callerAddr callerBytes)
          retAddr leftAddr rightAddr retBytes left right accesses)) =
      scheduled (oneThreadChoice (.ok (), exitState base caller next before after
        callerAddr retAddr leftAddr rightAddr ((left + right) % modulus 64) left right)) := by
  unfold twoSteps
  rw [MiniRustWord64PairStep.assign_step fuel base caller _ _ retAddr leftAddr rightAddr
    left right retBytes accesses retLength retAligned leftAligned rightAligned leftValid rightValid]
  rw [choice_bind]
  simp only [nextStep]
  rw [MiniRustWord64PairStep.return_step fuel base caller next before after
    callerAddr retAddr leftAddr rightAddr ((left + right) % modulus 64) left right callerBytes _
    callerLength callerAligned retAligned (Nat.mod_lt _ (by decide))]
  rfl

/-- An explicit scheduler oracle reaches a normal endpoint. This prevents the
    preallocated-body result from being only a vacuous every-success claim.
    Entry allocation availability is a separate obligation. -/
theorem body_available (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (left right : Nat) (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr leftAddr rightAddr : Nat) (callerBytes retBytes : List MR_AbstractByte)
    (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (retLength : retBytes.length = 8)
    (callerAligned : callerAddr % 8 = 0) (retAligned : retAddr % 8 = 0)
    (leftAligned : leftAddr % 8 = 0) (rightAligned : rightAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    SOut.runOracle (fun _ => 0) (fun _ => 0)
      (twoSteps (fuel + 50)
      (active base caller
        (localFrame (callerWorld before after callerAddr callerBytes) retAddr leftAddr rightAddr
          (.BackToCaller (some next) none (ptr before.length (Int.ofNat callerAddr))) 0)
        (cells (callerWorld before after callerAddr callerBytes)
          retAddr leftAddr rightAddr retBytes left right accesses))) = .ok (.ok (), exitState base caller next before after
        callerAddr retAddr leftAddr rightAddr ((left + right) % modulus 64) left right) := by
  rw [two_steps_exact fuel base caller left right next before after
    callerAddr retAddr leftAddr rightAddr callerBytes retBytes accesses callerLength retLength
    callerAligned retAligned leftAligned rightAligned leftValid rightValid]
  rfl

end MiniRustWord64PairRun
