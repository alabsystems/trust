/- Function execution over the original generated Machine.step operation. -/
import MiniRustU64Call
import U64Addition
noncomputable section
namespace MiniRustU64Run
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Call MiniRustU64Entry
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
    (before after : List MR_Allocation) (callerAddr retAddr argAddr value input : Nat) : MR_Machine :=
  single base [(caller.set_next_block next).set_next_stmt 0]
    (retiredCells (callerWorld before after callerAddr (u64bytes value))
      retAddr argAddr value input
      [⟨.Load, .None, Int.ofNat retAddr, 8⟩, ⟨.Store, .None, Int.ofNat callerAddr, 8⟩])

/-- Complete function BODY execution: genuine Assign and genuine Return,
    preserving both original scheduler choices and the complete final world. -/
theorem two_steps_exact (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal input : Nat) (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr argAddr : Nat) (callerBytes retBytes : List MR_AbstractByte)
    (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (retLength : retBytes.length = 8)
    (callerAligned : callerAddr % 8 = 0) (retAligned : retAddr % 8 = 0)
    (argAligned : argAddr % 8 = 0) (inputValid : input < modulus 64)
    (literalValid : literal < modulus 64) :
    twoSteps (fuel + 50)
      (active base caller
        (frame literal
          (ptr (callerWorld before after callerAddr callerBytes).length (Int.ofNat retAddr))
          (ptr ((callerWorld before after callerAddr callerBytes).length + 1) (Int.ofNat argAddr))
          (.BackToCaller (some next) none (ptr before.length (Int.ofNat callerAddr))) 0)
        (cells (callerWorld before after callerAddr callerBytes)
          retAddr argAddr retBytes input accesses)) =
      scheduled (oneThreadChoice (.ok (), exitState base caller next before after
        callerAddr retAddr argAddr ((input + literal) % modulus 64) input)) := by
  unfold twoSteps
  rw [assign_step fuel base caller literal _ _ retAddr argAddr input retBytes accesses
    retLength retAligned argAligned inputValid literalValid]
  rw [choice_bind]
  simp only [nextStep]
  rw [return_step fuel base caller literal next before after callerAddr retAddr argAddr
    ((input + literal) % modulus 64) input callerBytes _ callerLength callerAligned retAligned
    (Nat.mod_lt _ (by decide))]
  rfl

/-- Canonical SSA states BEFORE root Return. These retain the actual SemR
    memory/world rather than pretending the terminal `Out.ret` stores it. -/
def irAfterConstant (literal input depth : Nat) (memory : Mem) : Core :=
  { SemRU64Addition.initial literal input depth memory with
    pc := 1, env := [(1, .int .u64 literal), (0, .int .u64 input)] }

def irBeforeReturn (literal input depth : Nat) (memory : Mem) : Core :=
  { SemRU64Addition.initial literal input depth memory with
    pc := 2, env := [(2, .int .u64 ((input + literal) % modulus 64)),
      (1, .int .u64 literal), (0, .int .u64 input)] }

private theorem pure_ok {α : Type} (value : α) : (pure value : R α) = .ok value := rfl

theorem ir_const_step (literal input depth : Nat) (memory : Mem)
    (literalValid : literal < modulus 64) :
    stepCore (SemRU64Addition.module literal) (SemRU64Addition.initial literal input depth memory) =
      .cont (irAfterConstant literal input depth memory) := by
  simp [stepCore, SemRU64Addition.module, SemRU64Addition.initial, SemRU64Addition.function,
    SemRU64Addition.signature, SemRU64Addition.body, irAfterConstant, nth?, execNode,
    constStep, constVal, bindResults, next, ofR, ok_bind, pure_ok,
    IntTy.bits, Module.pointerBits, Nat.mod_eq_of_lt literalValid]

theorem ir_add_step (literal input depth : Nat) (memory : Mem)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    stepCore (SemRU64Addition.module literal) (irAfterConstant literal input depth memory) =
      .cont (irBeforeReturn literal input depth memory) := by
  simp [stepCore, SemRU64Addition.module, SemRU64Addition.initial, SemRU64Addition.function,
    SemRU64Addition.signature, SemRU64Addition.body, irAfterConstant, irBeforeReturn, nth?, execNode,
    binopStep, evalBinop, intBin, liftOp, pure_ok, ok_bind, getV, lookupEnv, expectTy,
    rejectPoison, expectInt, isBoolTy, Val.ty, Ty.beq, IntTy.code, IntTy.bits,
    Module.pointerBits, bindResults, next, ofR, inputValid, literalValid]

theorem ir_root_return (literal input depth : Nat) (memory : Mem) :
    stepCore (SemRU64Addition.module literal) (irBeforeReturn literal input depth memory) =
      .done (.ret [.int .u64 ((input + literal) % modulus 64)]) := by
  simp [stepCore, SemRU64Addition.module, SemRU64Addition.initial, SemRU64Addition.function,
    SemRU64Addition.signature, SemRU64Addition.body, irBeforeReturn, nth?, execNode,
    retStep, returnTo, getV, getVs, lookupEnv, pure_ok, ok_bind, rejectPoison, ofR,
    checkSig, expectTy, Val.ty, Ty.beq, IntTy.code, IntTy.bits, Module.pointerBits,
    Nat.mod_lt _ (by decide : 0 < modulus 64)]

theorem ir_world_retained (literal input depth : Nat) (memory : Mem) :
    (irBeforeReturn literal input depth memory).mem = memory := rfl

/-- The observed scalar from the actual SemR result indexes the COMPLETE
    MiniRust endpoint, including caller bytes and both retired private slots.
    This is mathematical observation only, not source/ABI/admission evidence. -/
def ReturnObservation (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr retAddr argAddr input : Nat)
    (irResult : Out) (modelResult : SRes MR_TerminationInfo Unit × MR_Machine) : Prop :=
  match irResult, modelResult with
  | .ret [.int .u64 value], (.ok (), machine) =>
    machine = exitState base caller next before after callerAddr retAddr argAddr value input
  | _, _ => False

theorem every_scheduled {α : Type} (p : α → Prop) (out : SOut α)
    (h : EveryResult p out) : EveryResult p (scheduled out) := by
  change ∀ index, _
  intro index
  cases index with
  | zero => exact h
  | succ index => trivial

theorem every_choice {α : Type} (p : α → Prop) (value : α)
    (h : p value) : EveryResult p (oneThreadChoice value) := by
  change ∀ index, _
  intro index
  cases index with
  | zero => exact h
  | succ index => trivial

theorem body_correspondence (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal input depth : Nat) (irMemory : Mem) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr retAddr argAddr : Nat)
    (callerBytes retBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (retLength : retBytes.length = 8)
    (callerAligned : callerAddr % 8 = 0) (retAligned : retAddr % 8 = 0)
    (argAligned : argAddr % 8 = 0) (inputValid : input < modulus 64)
    (literalValid : literal < modulus 64) :
    EveryResult
      (ReturnObservation base caller next before after callerAddr retAddr argAddr input
        (run (SemRU64Addition.module literal) 3
          (SemRU64Addition.initial literal input depth irMemory)))
      (twoSteps (fuel + 50)
        (active base caller
          (frame literal
            (ptr (callerWorld before after callerAddr callerBytes).length (Int.ofNat retAddr))
            (ptr ((callerWorld before after callerAddr callerBytes).length + 1) (Int.ofNat argAddr))
            (.BackToCaller (some next) none (ptr before.length (Int.ofNat callerAddr))) 0)
          (cells (callerWorld before after callerAddr callerBytes)
            retAddr argAddr retBytes input accesses))) := by
  rw [two_steps_exact fuel base caller literal input next before after
    callerAddr retAddr argAddr callerBytes retBytes accesses callerLength retLength
    callerAligned retAligned argAligned inputValid literalValid]
  apply every_scheduled
  apply every_choice
  rw [SemRU64Addition.run_exact literal input depth irMemory inputValid]
  rfl

end MiniRustU64Run
