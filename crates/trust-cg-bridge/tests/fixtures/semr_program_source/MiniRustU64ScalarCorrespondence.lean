/- Actual decoded scalar profile → constructed generated-MiniRust function.
   This is an explicit bounded model relation, not a source/codec/ABI theorem. -/
import U64ScalarProfile
import MiniRustU64Availability

noncomputable section
namespace MiniRustU64ScalarCorrespondence
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Entry MiniRustU64Call MiniRustU64AllocatedCall MiniRustU64Run
  MiniRustU64Correspondence MiniRustU64Availability MiniRustAllocate8Safety
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The bounded model construction inspects the REAL decoded Module. MiniRust
    has no module/function-name or TargetInfo field in MR_Function: those stay
    in the decoded View and byte subject, not in a claimed frontend refinement.
    The selected body is the existing actual MR_Function Const/Add/Return
    construction, which executes the unchanged generated machine operations. -/
def modelOfBytes (bytes : List Nat) : Option MR_Function :=
  match decode bytes with
  | .error _ => none
  | .ok module =>
    if module.executableTarget then
      match SemRU64ScalarProfile.classify module with
      | none => none
      | some view => some (function view.literal)
    else none

/-- Exact structural relation at the two existing model representations. This
    proposition is proved from decoding below, never assumed as a conversion
    premise. The complete decoded name and target remain in view. -/
def ModelRelation (bytes : List Nat) (literal : Nat) (callee : MR_Function) : Prop :=
  ∃ view : SemRU64ScalarProfile.View,
    decode bytes = .ok (SemRU64ScalarProfile.module view) ∧
    view.literal = literal ∧
    (SemRU64ScalarProfile.module view).executableTarget = true ∧
    callee = function view.literal

theorem classified_module (view : SemRU64ScalarProfile.View) :
    SemRU64ScalarProfile.classify (SemRU64ScalarProfile.module view) = some view := by
  cases view
  rfl

theorem decoded_model_relation (bytes : List Nat) (literal : Nat)
    (checked : SemRU64ScalarProfile.Decodes bytes literal) :
    ModelRelation bytes literal (function literal) := by
  obtain ⟨view, decoded, sameLiteral, accepted⟩ :=
    SemRU64ScalarProfile.decoded_module bytes literal checked
  exact ⟨view, decoded, sameLiteral, accepted, by rw [sameLiteral]⟩

theorem decoded_model_exact (bytes : List Nat) (literal : Nat)
    (checked : SemRU64ScalarProfile.Decodes bytes literal) :
    modelOfBytes bytes = some (function literal) := by
  obtain ⟨view, decoded, sameLiteral, accepted⟩ :=
    SemRU64ScalarProfile.decoded_module bytes literal checked
  simp only [modelOfBytes, decoded, accepted, ite_true, classified_module, sameLiteral]

/-- The actual callee is constructed from the complete byte subject. Invalid
    decoding/profile returns reject; no successful call/run/frame or admitted
    allocator/scheduler branch is a premise. Two original Machine.step calls
    follow the original eval_call, with all its allocation/init/push choices. -/
def enterFromBytes (fuel input : Nat) (bytes : List Nat)
    (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access) :=
  match modelOfBytes bytes with
  | none => SOut.reject
  | some callee =>
    (MRf.Machine.eval_call (fuel + 21)
      (single base [caller] ⟨⟨callerWorld before after callerAddr callerBytes, ()⟩, accesses⟩)
      callee .Rust [(.Int (Int.ofNat input), .Int (mrIntTy false .u64))]
      (place (ptr before.length (Int.ofNat callerAddr)), .Int (mrIntTy false .u64))
      (some next) none).bind (afterEntry (fuel + 50))

theorem enter_from_bytes_exact (fuel literal input : Nat) (bytes : List Nat)
    (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (checked : SemRU64ScalarProfile.Decodes bytes literal) :
    enterFromBytes fuel input bytes base caller next before after callerAddr callerBytes accesses =
      enterAndRun fuel literal input base caller next before after callerAddr callerBytes accesses := by
  simp only [enterFromBytes, decoded_model_exact bytes literal checked]
  rfl

/-- Complete actual allocator and scheduler tree, not an initialized-frame law.
    Both guarded demonic allocations retain their strict end-address bound and
    overlap/alignment guards; every rejected branch is still rejected. -/
theorem profile_full_tree_exact (fuel literal input : Nat) (bytes : List Nat)
    (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (checked : SemRU64ScalarProfile.Decodes bytes literal)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    enterFromBytes fuel input bytes base caller next before after callerAddr callerBytes accesses =
      fullTree literal input base caller next before after callerAddr callerBytes := by
  rw [enter_from_bytes_exact fuel literal input bytes base caller next before after callerAddr
    callerBytes accesses checked]
  exact full_tree_exact fuel literal input base caller next before after callerAddr callerBytes
    accesses callerLength callerAligned inputValid literalValid

/-- The endpoint refers to runBlob on the SAME complete actual bytes, not a
    relabelled historical 262-byte blob or a guessed normalized IR Module. -/
def ProfileObservation (bytes : List Nat) (input depth : Nat)
    (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte)
    (result : SRes MR_TerminationInfo Unit × MR_Machine) : Prop :=
  match runBlob bytes 0 [.int .u64 input] 3 depth with
  | .error _ => False
  | .ok irResult =>
    FunctionObservation base caller next before after callerAddr input callerBytes irResult result

attribute [local irreducible] EveryResult enterAndRun enterFromBytes

/-- Full function-boundary correspondence for every full64 literal/input and
    actual decoded canonical profile. Complete outside world, caller resumption,
    argument initialization, both private retirements and real step logs are
    retained by FunctionObservation/exitState, as in the original theorem. -/
theorem profile_function_correspondence (fuel literal input depth : Nat) (bytes : List Nat)
    (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (checked : SemRU64ScalarProfile.Decodes bytes literal)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    EveryResult
      (ProfileObservation bytes input depth base caller next before after callerAddr callerBytes)
      (enterFromBytes fuel input bytes base caller next before after callerAddr callerBytes accesses) := by
  have actual := SemRU64ScalarProfile.returns bytes literal checked input depth inputValid
  have predicate :
      ProfileObservation bytes input depth base caller next before after callerAddr callerBytes =
        FunctionObservation base caller next before after callerAddr input callerBytes
          (run (SemRU64Addition.module literal) 3
            (SemRU64Addition.initial literal input depth Mem.empty)) := by
    funext result
    simp only [ProfileObservation, actual,
      SemRU64Addition.run_exact literal input depth Mem.empty inputValid]
  rw [predicate, enter_from_bytes_exact fuel literal input bytes base caller next before after
    callerAddr callerBytes accesses checked]
  exact function_correspondence fuel literal input depth Mem.empty base caller next before after
    callerAddr callerBytes accesses callerLength callerAligned inputValid literalValid

theorem profile_canonical_no_bad (bytes : List Nat) (literal : Nat)
    (checked : SemRU64ScalarProfile.Decodes bytes literal) :
    SemRU64ScalarProfile.NoBad bytes :=
  SemRU64ScalarProfile.no_bad bytes literal checked

/-- Error/fuel/panic results are excluded at every admitted leaf of the real
    tree. Rejected choices remain separate; availability is proved below. -/
theorem profile_model_no_error (fuel literal input : Nat) (bytes : List Nat)
    (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (checked : SemRU64ScalarProfile.Decodes bytes literal)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64) :
    EveryResult ModelResultOk
      (enterFromBytes fuel input bytes base caller next before after callerAddr callerBytes accesses) := by
  rw [profile_full_tree_exact fuel literal input bytes base caller next before after callerAddr
    callerBytes accesses checked callerLength callerAligned inputValid literalValid]
  unfold fullTree
  refine every_selected ModelResultOk _ _ _ ?_
  intro retIndex _ _
  refine every_selected ModelResultOk _ _ _ ?_
  intro argIndex _ _
  refine every_scheduled ModelResultOk _ ?_
  refine every_choice ModelResultOk _ ?_
  rfl

/-- Constructive nonvacuity under explicit sufficient high-water room. No
    successful allocation, allowed-branch flag, call or run is assumed. The
    whole generated machine/world endpoint remains the actual returned value. -/
theorem profile_function_available (fuel literal input : Nat) (bytes : List Nat)
    (base : MR_Machine) (caller : MR_StackFrame) (next : MR_BbName)
    (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (checked : SemRU64ScalarProfile.Decodes bytes literal)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (inputValid : input < modulus 64) (literalValid : literal < modulus 64)
    (k : Nat) (below : Below (callerWorld before after callerAddr callerBytes) (8 * k))
    (room : 8 * (k + 3) < modulus 64) (π : List Nat → Nat) :
    SOut.runOracle (entryOracle k) π
      (enterFromBytes fuel input bytes base caller next before after callerAddr callerBytes accesses) =
      .ok (.ok (), exitState base caller next before after callerAddr (address k) (address (k + 1))
        ((input + literal) % modulus 64) input) := by
  rw [enter_from_bytes_exact fuel literal input bytes base caller next before after callerAddr
    callerBytes accesses checked]
  exact full_function_available fuel literal input base caller next before after callerAddr callerBytes
    accesses callerLength callerAligned inputValid literalValid k below room π

end MiniRustU64ScalarCorrespondence
