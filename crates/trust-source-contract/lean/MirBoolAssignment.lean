/- Copyright 2026 Andrew Yates. Apache-2.0.
   Owning-compiler typed MIR fragment, not a source certificate. Original Rust
   AST-to-this-quotation fidelity remains a separate obligation. The target is
   the canonical independently decoded original wire artifact, not a new lowerer.
-/
import SemRSourceBodyCheck
namespace TrustMirBoolAssignment
open SemR
open SemR.SourceBodyCheck (original mutant)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

structure Place where
  «local» : Nat
  projections : List Nat
  deriving DecidableEq
inductive Operand where
  | constantBool (value : Bool)
  | copy (place : Place)
  deriving DecidableEq
inductive Rvalue where
  | use (operand : Operand)
  | discriminant (place : Place)
  deriving DecidableEq
inductive Statement where
  | assign (place : Place) (value : Rvalue)
  deriving DecidableEq

inductive Terminator where
  | switchInt (operand : Operand) (targets : List (Nat × Nat)) (otherwise : Nat)
  | goto (destination : Nat)
  | return
  deriving DecidableEq

/-- A WORD VIEW of the captured original nominal input. This is neither a
    valid Rust enum value nor an identification with SemR.Enum. -/
def originalNominalName : String := "trust_ir::proof::obligations::ObligationKindShape"
structure NominalWordView (nominalName : String) where
  tagWord : Nat
abbrev OriginalInputView := NominalWordView originalNominalName

/-- The original frame's Bool locals 0 and 2; nominal local 1 stays separate.
    Local 3's already-read tag is preserved in the target environment. -/
structure SourceFrame where
  input : OriginalInputView
  local0 : Option Bool
  local2 : Option Bool

/-- Exactly the Bool-constant assignment fragment with original local identity.
    This is a statement relation, not an interpreter for unsupported MIR. -/
inductive SourceStep : Statement → SourceFrame → SourceFrame → Prop where
  | assignLocal2 (s : SourceFrame) (b : Bool) :
      SourceStep (.assign ⟨2, []⟩ (.use (.constantBool b))) s {s with local2 := some b}
  | copyLocal2ToReturn (s : SourceFrame) (b : Bool) :
      SourceStep (.assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩)))
        {s with local2 := some b} {s with local2 := some b, local0 := some b}

structure SourceLocation where
  block : Nat
  statement : Nat
inductive SourceGoto : Terminator → SourceLocation → SourceLocation → Prop where
  | toReturn (origin : SourceLocation) : SourceGoto (.goto 10) origin ⟨10,0⟩
inductive SourceReturn : Terminator → SourceFrame → Bool → Prop where
  | returned (s : SourceFrame) (b : Bool) : SourceReturn .return {s with local0 := some b} b

def originalAssignment : Statement := .assign ⟨2, []⟩ (.use (.constantBool true))
def mutantAssignment : Statement := .assign ⟨2, []⟩ (.use (.constantBool false))
def program (b : Bool) : Module := if b then original else mutant
def function (b : Bool) : Func := match nth? (program b).functions 0 with
  | some f => f
  | none => {id := 0, ty := 0, entry := 0, blocks := [], name := []}
def block (b : Bool) (id : Nat) : Block := match findBlock (function b).blocks id with
  | some k => k
  | none => {id := id, params := [], body := []}
def image : Option Bool → List AByte
  | none => []
  | some b => [.init (b2n b)]
def slot (value : Option Bool) : Alloc :=
  {base := 1024, size := 1, align := 1, live := true, data := image value}
def memory (value : Option Bool) : Mem :=
  {allocs := [slot value], nextAddr := 1025}
/-- Explicit mapping of original local 1 to STRUCT0[original I64 word].
    No nominal Enum constructor or native pointer is substituted. -/
def before (b : Bool) (s : SourceFrame) : Core :=
  {fn := function b, sig := {params := [.struct 0], returns := [.bool], vararg := false},
   block := block b 1, pc := 0,
   env := [(5, .int .i64 s.input.tagWord), (4, .ptr 0 0),
           (0, .struct 0 [.int .i64 s.input.tagWord])], depth := 4,
   stack := [], openFrames := [], nextFrame := 0, mem := memory s.local2}
def first (b : Bool) (s : SourceFrame) : Core :=
  {next (before b s) with env := (6, .bool b) :: (before b s).env}
def second (b : Bool) (s : SourceFrame) : Core :=
  {next (first b s) with env := (7, .bool b) :: (first b s).env}
def after (b : Bool) (s : SourceFrame) : Core :=
  {next (second b s) with mem := (written (memory s.local2) 0 0 (slot s.local2) [.init (b2n b)])}

/-- Three REAL operational steps, using the existing relation unchanged. -/
def ThreeSteps (m : Module) (a z : Core) : Prop :=
  ∃ middle1 middle2, Step m a (.cont middle1) ∧
    Step m middle1 (.cont middle2) ∧ Step m middle2 (.cont z)

/-- No successful-store premise: the actual allocation, bounds, alignment,
    SSA operands, declaration and byte image are reduced and checked here.
    Arbitrary prior initialized/uninitialized local 2 is overwritten. -/
theorem const_step (b : Bool) (s : SourceFrame) :
    stepCore (program b) (before b s) = .cont (first b s) := by cases b <;> rfl
theorem copy_step (b : Bool) (s : SourceFrame) :
    stepCore (program b) (first b s) = .cont (second b s) := by cases b <;> rfl
private theorem pointer_lookup (b : Bool) (s : SourceFrame) :
    getV (second b s) 4 = .ok (.ptr 0 0) := rfl
private theorem value_lookup (b : Bool) (s : SourceFrame) :
    getV (second b s) 7 = .ok (.bool b) := rfl
private theorem access_slot (old : Option Bool) (op : String) :
    accessAt (memory old) op 0 0 1 1 = .ok (slot old) := by
  simp [accessAt, memory, slot, accessAlloc, addrSpace, nth?]
private theorem store_node (b : Bool) (s : SourceFrame) :
    nth? (second b s).block.body (second b s).pc =
      some ⟨.store .bool 4 7 false none, []⟩ := by cases b <;> rfl
private theorem pure_ok {α : Type} (value : α) : (pure value : R α) = .ok value := rfl
private theorem pointer_bits (b : Bool) : (program b).pointerBits = 64 := by cases b <;> rfl

theorem store_step (b : Bool) (s : SourceFrame) :
    stepCore (program b) (second b s) = .cont (after b s) := by
  rw [stepCore, store_node]
  change ofR (storeStep (program b).pointerBits (second b s)
    ⟨.store .bool 4 7 false none, []⟩ .bool 4 7 false none) = _
  simp only [storeStep, pointer_bits, pointer_lookup, value_lookup, ok_bind]
  cases b <;> simp [storeImage, expectTy, Val.ty, Ty.beq, encodeVal, scalarLayout,
    checkAlign, isPow2, expectPtr, rejectPoison, pure_ok, ok_bind, access_slot, after,
    second, first, before, bindResults, next, ofR]

theorem write_image (old : Option Bool) (b : Bool) :
    writeBytes (image old) 0 [.init (b2n b)] = image (some b) := by cases old <;> rfl

theorem after_memory (b : Bool) (s : SourceFrame) :
    (after b s).mem = memory (some b) := by
  simp only [after, written, memory, slot, setNth, write_image]

/-- The independently specified source assignment and the exact original
    byte-store slice commute. The relation includes the original source local
    identity and byte image; it does not grant source-quotation authority. -/
theorem assignment_simulates (b : Bool) (s : SourceFrame) :
    SourceStep (.assign ⟨2, []⟩ (.use (.constantBool b))) s {s with local2 := some b} ∧
    ThreeSteps (program b) (before b s) (after b s) ∧
    (after b s).mem = memory ({s with local2 := some b} : SourceFrame).local2 ∧
    getV (after b s) 0 = .ok (.struct 0 [.int .i64 s.input.tagWord]) := by
  refine ⟨SourceStep.assignLocal2 s b, ?_, after_memory b s, ?_⟩
  · exact ⟨first b s, second b s,
      (const_step b s) ▸ step_complete (program b) (before b s),
      (copy_step b s) ▸ step_complete (program b) (first b s),
      (store_step b s) ▸ step_complete (program b) (second b s)⟩
  · rfl

def returnStart (b : Bool) (s : SourceFrame) : Core :=
  {after b s with block := block b 10, pc := 0}
def loaded (b : Bool) (s : SourceFrame) : Core :=
  {next (returnStart b s) with env := (24, .bool b) :: (returnStart b s).env}
def copied (b : Bool) (s : SourceFrame) : Core :=
  {next (loaded b s) with env := (25, .bool b) :: (loaded b s).env}
private theorem branch_step (b : Bool) (s : SourceFrame) :
    stepCore (program b) (after b s) = .cont (returnStart b s) := by cases b <;> rfl
private theorem load_node (b : Bool) (s : SourceFrame) :
    nth? (returnStart b s).block.body (returnStart b s).pc =
      some ⟨.load .bool 4 false none, [24]⟩ := by cases b <;> rfl
private theorem return_pointer (b : Bool) (s : SourceFrame) :
    getV (returnStart b s) 4 = .ok (.ptr 0 0) := rfl
private theorem load_step (b : Bool) (s : SourceFrame) :
    stepCore (program b) (returnStart b s) = .cont (loaded b s) := by
  rw [stepCore, load_node]
  change ofR (loadStep (program b).pointerBits (returnStart b s)
    ⟨.load .bool 4 false none, [24]⟩ .bool 4 false none) = _
  simp only [loadStep, pointer_bits, return_pointer, ok_bind]
  have hm : (returnStart b s).mem = memory (some b) := after_memory b s
  cases b <;> simp [scalarLayout, checkAlign, isPow2, expectPtr, rejectPoison,
    pure_ok, ok_bind, hm, access_slot, readOut, readBytes, byteAt, slot, image,
    firstUninit, decodeVal, b2n, nth?, loaded, bindResults, next, ofR]
private theorem copy_return_step (b : Bool) (s : SourceFrame) :
    stepCore (program b) (loaded b s) = .cont (copied b s) := by cases b <;> rfl
private theorem return_step (b : Bool) (s : SourceFrame) :
    stepCore (program b) (copied b s) = .done (.ret [.bool b]) := by cases b <;> rfl
/-- Actual original Goto10/Load24/Copy25/Return25 continuation. This retains
    the byte-load and output custody rather than replacing the tail by a flag. -/
theorem actual_return_tail (b : Bool) (s : SourceFrame) :
    run (program b) 4 (after b s) = .ret [.bool b] := by
  simp only [run, branch_step, load_step, copy_return_step, return_step]

def rootFrame : SourceFrame := ⟨⟨0⟩, none, none⟩
def entry (b : Bool) : Core :=
  {before b rootFrame with
    block := block b 0
    pc := 0
    env := [(0, .struct 0 [.int .i64 0])]
    mem := Mem.empty}
def allocated (b : Bool) : Core :=
  {next (entry b) with
    env := [(4, .ptr 0 0), (0, .struct 0 [.int .i64 0])]
    mem := memory none}
def discriminated (b : Bool) : Core :=
  {next (allocated b) with env := (5, .int .i64 0) :: (allocated b).env}
private theorem entry_start (b : Bool) :
    start (program b) 0 [.struct 0 [.int .i64 0]] 4 = .ok (entry b) := by cases b <;> rfl
private theorem allocated_step (b : Bool) :
    stepCore (program b) (entry b) = .cont (allocated b) := by cases b <;> rfl
private theorem discriminated_step (b : Bool) :
    stepCore (program b) (allocated b) = .cont (discriminated b) := by cases b <;> rfl
private theorem selected_step (b : Bool) :
    stepCore (program b) (discriminated b) = .cont (before b rootFrame) := by cases b <;> rfl
/-- An actual target-root witness, not a postulated entry at an arbitrary
    block. The source discriminant/branch quotation itself is not proved here. -/
theorem actual_root_prefix (b : Bool) :
    start (program b) 0 [.struct 0 [.int .i64 0]] 4 = .ok (entry b) ∧
    ThreeSteps (program b) (entry b) (before b rootFrame) := by
  refine ⟨entry_start b, allocated b, discriminated b, ?_, ?_, ?_⟩
  · exact (allocated_step b) ▸ step_complete (program b) (entry b)
  · exact (discriminated_step b) ▸ step_complete (program b) (allocated b)
  · exact (selected_step b) ▸ step_complete (program b) (discriminated b)

/-- Closed actual input/root/return composition for this source fragment.
    This is not a theorem authenticating the external Rust AST quotation. -/
theorem actual_root_assignment (b : Bool) :
    SourceStep (.assign ⟨2, []⟩ (.use (.constantBool b))) rootFrame
      {rootFrame with local2 := some b} ∧
    runFunction (program b) 0 [.struct 0 [.int .i64 0]] 10 4 = .ret [.bool b] := by
  refine ⟨SourceStep.assignLocal2 rootFrame b, ?_⟩
  simp only [runFunction, entry_start]
  simp only [run, allocated_step, discriminated_step, selected_step,
    const_step, copy_step, store_step, branch_step, load_step, copy_return_step, return_step]

/-- The reflected source view retains the nominal metadata index. This still
    does not prove Rust DefId/source-capture fidelity or enum validity. -/
example : True := by
  fail_if_success
    have wrong : OriginalInputView := (⟨0⟩ : NominalWordView "another nominal type")
  trivial

/-- Equal numeric IDs do not identify the legacy Struct carrier with Enum. -/
example : start (program true) 0 [.enum 0 [.int .i64 0]] 4 =
    .stop (.typeError "SignatureMismatch: type mismatch") := rfl

/-- Wrong original destination is not silently mapped to ptr4. -/
example (s : SourceFrame) : True := by
  fail_if_success
    have wrong : SourceStep (.assign ⟨0, []⟩ (.use (.constantBool true))) s
      {s with local2 := some true} := SourceStep.assignLocal2 s true
  trivial
/-- A changed body cannot reuse the old true return theorem. -/
example (s : SourceFrame) : True := by
  fail_if_success
    have wrong : run (program false) 4 (after false s) = .ret [.bool true] :=
      actual_return_tail true s
  trivial
end TrustMirBoolAssignment
