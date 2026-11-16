/- Actual generated function entry/execution → canonical SemR result.
   This is a model theorem, not TCX/source/physical-ABI/admission authority. -/
import MiniRustU64AllocatedCall
import MiniRustU64Run
noncomputable section
namespace MiniRustU64Correspondence
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Entry MiniRustU64Call MiniRustU64AllocatedCall MiniRustU64Run
open MiniRustAllocate8Safety
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def afterEntry (fuel : Nat) (result : SRes MR_TerminationInfo Unit × MR_Machine) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  match result with
  | (.ok _, machine) => twoSteps fuel machine
  | (.err error, machine) => .ok (.err error, machine)

/-- Calls existing eval_call then existing Machine.step twice, preserving
    every error and scheduler/allocator choice of those original operations. -/
def enterAndRun (fuel literal input : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access) :=
  (MRf.Machine.eval_call (fuel + 21)
    (single base [caller] ⟨⟨callerWorld before after callerAddr callerBytes, ()⟩, accesses⟩)
    (function literal) .Rust [(.Int (Int.ofNat input), .Int (mrIntTy false .u64))]
    (place (ptr before.length (Int.ofNat callerAddr)), .Int (mrIntTy false .u64))
    (some next) none).bind (afterEntry (fuel + 50))

def fullTree (literal input : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) : SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (callerWorld before after callerAddr callerBytes)) (fun retIndex =>
    selectedChoice (Int.ofNat (modulus 64))
      (allocationAllowed (callerWorld before after callerAddr callerBytes ++
        [slot (Int.ofNat (address retIndex)) uninit8])) (fun argIndex =>
      scheduled (oneThreadChoice (.ok (), exitState base caller next before after
        callerAddr (address retIndex) (address argIndex) ((input + literal) % modulus 64) input))))

/-- Complete actual ENTRY and BODY, not an assumed initialized frame.
    The exact original four choice layers and every raw world field remain. -/
theorem full_tree_exact (fuel literal input : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    enterAndRun fuel literal input base caller next before after callerAddr callerBytes accesses =
      fullTree literal input base caller next before after callerAddr callerBytes := by
  unfold enterAndRun
  rw [call_tree_exact fuel literal input _ accesses base caller _ _ _ inputValid]
  unfold callTree fullTree
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (callerWorld before after callerAddr callerBytes)))
  funext retIndex
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (callerWorld before after callerAddr callerBytes ++
      [slot (Int.ofNat (address retIndex)) uninit8])))
  funext argIndex
  simp only [SOut.bind_ok', afterEntry]
  rw [two_steps_exact fuel base caller literal input next before after callerAddr
    (address retIndex) (address argIndex) callerBytes uninit8 _ callerLength uninit8_length
    callerAligned (address_aligned _) (address_aligned _) inputValid literalValid]

theorem every_selected {α : Type} (p : α → Prop) (bound : Int) (allowed : Int → Bool)
    (next : Nat → SOut α)
    (h : ∀ index, SInt.blt (candidate index) bound = true →
      allowed (candidate index) = true → EveryResult p (next index)) :
    EveryResult p (selectedChoice bound allowed next) := by
  change ∀ index, _
  intro index
  dsimp only
  cases hb : SInt.blt (candidate index) bound with
  | false => trivial
  | true =>
    cases ha : allowed (candidate index) with
    | false => trivial
    | true => exact h index hb ha

/-- Chosen addresses and COMPLETE endpoint tied to the actual SemR result.
    Gate facts are derived from the original choice tree, never supplied by
    callers as admission booleans. This proposition confers no compiler capability. -/
def FunctionObservation (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr input : Nat)
    (callerBytes : List MR_AbstractByte) (irResult : Out)
    (result : SRes MR_TerminationInfo Unit × MR_Machine) : Prop :=
  ∃ retIndex argIndex,
    SInt.blt (candidate retIndex) (Int.ofNat (modulus 64)) = true ∧
    allocationAllowed (callerWorld before after callerAddr callerBytes) (candidate retIndex) = true ∧
    SInt.blt (candidate argIndex) (Int.ofNat (modulus 64)) = true ∧
    allocationAllowed (callerWorld before after callerAddr callerBytes ++
      [slot (Int.ofNat (address retIndex)) uninit8]) (candidate argIndex) = true ∧
    ReturnObservation base caller next before after callerAddr (address retIndex) (address argIndex)
      input irResult result

/-- Universal full64 function-boundary correspondence, including actual entry,
    actual execution, memory framing and exact caller return/retirement. -/
theorem function_correspondence (fuel literal input depth : Nat)
    (irMemory : Mem) (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr : Nat) (callerBytes : List MR_AbstractByte)
    (accesses : List MR_Access) (callerLength : callerBytes.length = 8)
    (callerAligned : callerAddr % 8 = 0) (inputValid : input < modulus 64)
    (literalValid : literal < modulus 64) :
    EveryResult
      (FunctionObservation base caller next before after callerAddr input callerBytes
        (run (SemRU64Addition.module literal) 3
          (SemRU64Addition.initial literal input depth irMemory)))
      (enterAndRun fuel literal input base caller next before after callerAddr callerBytes accesses) := by
  rw [full_tree_exact fuel literal input base caller next before after callerAddr callerBytes accesses
    callerLength callerAligned inputValid literalValid]
  let p := FunctionObservation base caller next before after callerAddr input callerBytes
    (run (SemRU64Addition.module literal) 3 (SemRU64Addition.initial literal input depth irMemory))
  change EveryResult p (fullTree literal input base caller next before after callerAddr callerBytes)
  unfold fullTree
  refine every_selected p _ _ _ ?_
  intro retIndex retBound retAllowed
  refine every_selected p _ _ _ ?_
  intro argIndex argBound argAllowed
  refine every_scheduled p _ ?_
  refine every_choice p _ ?_
  change FunctionObservation base caller next before after callerAddr input callerBytes
    (run (SemRU64Addition.module literal) 3 (SemRU64Addition.initial literal input depth irMemory)) _
  refine ⟨retIndex, argIndex, retBound, retAllowed, argBound, argAllowed, ?_⟩
  rw [SemRU64Addition.run_exact literal input depth irMemory inputValid]
  rfl

-- Keep proof-predicate transport from unfolding the complete execution tree
-- during elaboration. The final kernel still checks the original statements.
attribute [local irreducible] EveryResult enterAndRun

/-- The COMPLETE original serialized compiler Module goes through the real
    decoder and function entry. No module is synthesized from the source. -/
def OriginalObservation (input depth : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte)
    (result : SRes MR_TerminationInfo Unit × MR_Machine) : Prop :=
  match runBlob SemRU64Addition.originalBytes 0 [.int .u64 input] 3 depth with
  | .error _ => False
  | .ok irResult => FunctionObservation base caller next before after callerAddr input callerBytes irResult result

theorem original_function_correspondence (fuel input depth : Nat)
    (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr : Nat) (callerBytes : List MR_AbstractByte)
    (accesses : List MR_Access) (callerLength : callerBytes.length = 8)
    (callerAligned : callerAddr % 8 = 0) (inputValid : input < modulus 64) :
    EveryResult (OriginalObservation input depth base caller next before after callerAddr callerBytes)
      (enterAndRun fuel 7 input base caller next before after callerAddr callerBytes accesses) := by
  have original : runBlob SemRU64Addition.originalBytes 0 [.int .u64 input] 3 depth =
      .ok (run (SemRU64Addition.module 7) 3
        (SemRU64Addition.initial 7 input depth Mem.empty)) := by
    simp only [runBlob, SemRU64Addition.original_decodes, runFunction,
      SemRU64Addition.start_exact 7 input depth inputValid]
  have predicate : OriginalObservation input depth base caller next before after callerAddr callerBytes =
      FunctionObservation base caller next before after callerAddr input callerBytes
        (run (SemRU64Addition.module 7) 3 (SemRU64Addition.initial 7 input depth Mem.empty)) := by
    funext result
    simp only [OriginalObservation, original]
  rw [predicate]
  exact function_correspondence fuel 7 input depth Mem.empty base caller next before after callerAddr
    callerBytes accesses callerLength callerAligned inputValid (by decide)

/-- Canonical relational NoBad for that SAME decoded function and full64 input.
    This is not a Rust SourceNoUB or physical-machine assertion. -/
theorem original_canonical_no_bad (input depth : Nat) (inputValid : input < modulus 64) :
    ¬ BodyViolation (SemRU64Addition.module 7)
      (SemRU64Addition.initial 7 input depth Mem.empty) :=
  SemRU64Addition.no_body_violation 7 input depth Mem.empty inputValid

def ModelResultOk (result : SRes MR_TerminationInfo Unit × MR_Machine) : Prop :=
  result.1 = .ok ()

/-- Actual model error/fuel/panic/refusal is excluded from every admitted leaf.
    Rejected choices are preserved; constructive availability is separate. -/
theorem original_model_no_error (fuel input : Nat)
    (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr : Nat) (callerBytes : List MR_AbstractByte)
    (accesses : List MR_Access) (callerLength : callerBytes.length = 8)
    (callerAligned : callerAddr % 8 = 0) (inputValid : input < modulus 64) :
    EveryResult ModelResultOk
      (enterAndRun fuel 7 input base caller next before after callerAddr callerBytes accesses) := by
  rw [full_tree_exact fuel 7 input base caller next before after callerAddr callerBytes accesses
    callerLength callerAligned inputValid (by decide)]
  unfold fullTree
  refine every_selected ModelResultOk _ _ _ ?_
  intro retIndex _ _
  refine every_selected ModelResultOk _ _ _ ?_
  intro argIndex _ _
  refine every_scheduled ModelResultOk _ ?_
  refine every_choice ModelResultOk _ ?_
  rfl

end MiniRustU64Correspondence
