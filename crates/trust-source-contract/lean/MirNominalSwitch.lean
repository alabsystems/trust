/- Copyright 2026 Andrew Yates. Apache-2.0.
   Valid constructors of the reflected original declaration, NOT an authenticated
   Rust AST quotation or physical enum representation. No source grade changes.
-/
import MirBoolAssignment
namespace TrustMirNominalSwitch
open SemR TrustMirBoolAssignment
set_option maxRecDepth 30000
set_option maxHeartbeats 0

structure DeclaredVariant where
  name : String
  discriminant : Int
/-- Exact original fieldless declaration. Payloads are absent by construction;
    the compiler observer refuses any payload before producing this view. -/
def variants : List DeclaredVariant :=
  [⟨"Precondition",0⟩, ⟨"Postcondition",1⟩, ⟨"LoopInvariant",2⟩,
   ⟨"TypeInvariant",3⟩, ⟨"RefinementType",4⟩, ⟨"TranslationValidation",5⟩,
   ⟨"MemorySafety",6⟩, ⟨"PanicFreedom",7⟩, ⟨"TemporalSafety",8⟩,
   ⟨"Liveness",9⟩, ⟨"ArithmeticSafety",10⟩, ⟨"BoundsCheck",11⟩,
   ⟨"GiveBackRefinement",12⟩, ⟨"Termination",13⟩, ⟨"Ownership",14⟩, ⟨"Custom",15⟩]
/-- Constructor custody is declaration membership, not an authored tag bound.
    There is deliberately NO caller-provided integer tag or payload. -/
structure Constructor (nominalName : String) where
  variant : Fin variants.length
abbrev OriginalConstructor := Constructor originalNominalName

def declared (c : OriginalConstructor) : DeclaredVariant := variants.get c.variant
def discriminant (c : OriginalConstructor) : Int := (declared c).discriminant
def word (c : OriginalConstructor) : Nat := resid 64 (discriminant c)
/-- Explicit logical legacy embedding. Struct0 is never treated as Enum0. -/
def embed (c : OriginalConstructor) : Val := .struct 0 [.int .i64 (word c)]

private theorem constructor_cases (c : OriginalConstructor) :
    c.variant.val = 0 ∨ c.variant.val = 1 ∨ c.variant.val = 2 ∨ c.variant.val = 3 ∨
    c.variant.val = 4 ∨ c.variant.val = 5 ∨ c.variant.val = 6 ∨ c.variant.val = 7 ∨
    c.variant.val = 8 ∨ c.variant.val = 9 ∨ c.variant.val = 10 ∨ c.variant.val = 11 ∨
    c.variant.val = 12 ∨ c.variant.val = 13 ∨ c.variant.val = 14 ∨ c.variant.val = 15 := by
  have h := c.variant.isLt
  change c.variant.val < 16 at h
  omega

theorem declaration_discriminant (c : OriginalConstructor) :
    discriminant c = (c.variant.val : Int) := by
  rcases c with ⟨⟨n, hn⟩⟩
  have h := constructor_cases (⟨⟨n,hn⟩⟩ : OriginalConstructor)
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp only at h <;> subst n <;> rfl

theorem declared_tag_bounds (c : OriginalConstructor) :
    0 ≤ discriminant c ∧ discriminant c < 16 := by
  rw [declaration_discriminant]
  have h := c.variant.isLt
  change c.variant.val < 16 at h
  omega

theorem declared_i64_bounds (c : OriginalConstructor) :
    (-9223372036854775808 : Int) ≤ discriminant c ∧
      discriminant c < 9223372036854775808 := by
  obtain ⟨lo,hi⟩ := declared_tag_bounds c
  omega

structure Signed64 where
  value : Int
  bounds : (-9223372036854775808 : Int) ≤ value ∧ value < 9223372036854775808

def readValue (c : OriginalConstructor) : Signed64 := ⟨discriminant c, declared_i64_bounds c⟩

theorem word_exact (c : OriginalConstructor) : word c = c.variant.val := by
  rw [word, declaration_discriminant]
  change c.variant.val % modulus 64 = c.variant.val
  apply Nat.mod_eq_of_lt
  have h := c.variant.isLt
  change c.variant.val < 16 at h
  have hb : 16 < modulus 64 := by decide
  omega

theorem embedded_word_bounds (c : OriginalConstructor) : word c < modulus 64 := by
  rw [word_exact]
  have h := c.variant.isLt
  change c.variant.val < 16 at h
  have hb : 16 < modulus 64 := by decide
  omega

theorem signed_discriminant_preserved (c : OriginalConstructor) :
    readInt true 64 (word c) = discriminant c := by
  rcases c with ⟨⟨n, hn⟩⟩
  have h := constructor_cases (⟨⟨n,hn⟩⟩ : OriginalConstructor)
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp only at h <;> subst n <;> rfl

/-- Original source SwitchInt order and otherwise are retained, not a set. -/
def targets : List (Nat × Nat) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(8,7),(9,8)]
def select : List (Nat × Nat) → Nat → Nat
  | [], _ => 9
  | (tag,destination) :: rest, value => if tag == value then destination else select rest value
def sourceBlock (c : OriginalConstructor) : Nat := select targets (word c)
def sourceStatement : Statement := .assign ⟨3,[]⟩ (.discriminant ⟨1,[]⟩)
def sourceTerminator : Terminator := .switchInt (.copy ⟨3,[]⟩) targets 9
structure SourceFrame where
  input : OriginalConstructor
  local3 : Option Signed64
  selected : Option Nat
inductive SourceDiscriminantStep : Statement → SourceFrame → SourceFrame → Prop where
  | read (s : SourceFrame) : SourceDiscriminantStep sourceStatement s
      {s with local3 := some (readValue s.input)}
inductive SourceSwitchStep : Terminator → SourceFrame → SourceFrame → Prop where
  | select (s : SourceFrame) (d : Signed64) : SourceSwitchStep sourceTerminator
      {s with local3 := some d} {s with local3 := some d, selected := some (select targets (resid 64 d.value))}

def entry (b : Bool) (c : OriginalConstructor) : Core :=
  {TrustMirBoolAssignment.entry b with env := [(0, embed c)]}
def allocated (b : Bool) (c : OriginalConstructor) : Core :=
  {next (entry b c) with env := [(4,.ptr 0 0),(0,embed c)], mem := memory none}
def discriminated (b : Bool) (c : OriginalConstructor) : Core :=
  {next (allocated b c) with env := (5,.int .i64 (word c)) :: (allocated b c).env}
def selected (b : Bool) (c : OriginalConstructor) : Core :=
  {discriminated b c with block := block b (sourceBlock c), pc := 0}

private theorem start_constructor (b : Bool) (c : OriginalConstructor) :
    start (program b) 0 [embed c] 4 = .ok (entry b c) := by cases b <;> rfl
private theorem pure_ok {α : Type} (x : α) : (pure x : R α) = .ok x := rfl
private theorem pointer_bits (b : Bool) : (program b).pointerBits = 64 := by cases b <;> rfl
private theorem allocation_node (b : Bool) (c : OriginalConstructor) :
    nth? (entry b c).block.body (entry b c).pc = some ⟨.alloca .bool none none, [4]⟩ := by cases b <;> rfl
private theorem allocate_constructor (b : Bool) (c : OriginalConstructor) :
    stepCore (program b) (entry b c) = .cont (allocated b c) := by
  rw [stepCore, allocation_node]
  change ofR (allocaStep (program b).pointerBits (entry b c)
    ⟨.alloca .bool none none, [4]⟩ .bool none none) = _
  simp [allocaStep, pointer_bits, getCount, layoutOf, allocSize,
    checkAlign, isPow2, allocAt, alignUp, addrSpace, pure_ok, ok_bind, bindResults,
    entry, TrustMirBoolAssignment.entry, before, rootFrame, Mem.empty, memory,
    slot, image, allocated, next, ofR]
private theorem extract_constructor (b : Bool) (c : OriginalConstructor) :
    stepCore (program b) (allocated b c) = .cont (discriminated b c) := by
  rcases c with ⟨⟨n,hn⟩⟩
  have h := constructor_cases (⟨⟨n,hn⟩⟩ : OriginalConstructor)
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp only at h <;> subst n <;> cases b <;> rfl
private theorem switch_constructor (b : Bool) (c : OriginalConstructor) :
    stepCore (program b) (discriminated b c) = .cont (selected b c) := by
  rcases c with ⟨⟨n,hn⟩⟩
  have h := constructor_cases (⟨⟨n,hn⟩⟩ : OriginalConstructor)
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp only at h <;> subst n <;> cases b <;> rfl

private theorem selected_identity (b : Bool) (c : OriginalConstructor) :
    (selected b c).block.id = sourceBlock c := by
  rcases c with ⟨⟨n,hn⟩⟩
  have h := constructor_cases (⟨⟨n,hn⟩⟩ : OriginalConstructor)
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp only at h <;> subst n <;> cases b <;> rfl

/-- Two source-prefix steps versus real target allocation stutter, ExtractField
    and Switch. Bounds are derived, never supplied as successful-run premises. -/
theorem prefix_simulates (b : Bool) (c : OriginalConstructor) :
    SourceDiscriminantStep sourceStatement ⟨c,none,none⟩ ⟨c,some (readValue c),none⟩ ∧
    SourceSwitchStep sourceTerminator ⟨c,some (readValue c),none⟩
      ⟨c,some (readValue c),some (sourceBlock c)⟩ ∧
    start (program b) 0 [embed c] 4 = .ok (entry b c) ∧
    ThreeSteps (program b) (entry b c) (selected b c) ∧
    getV (discriminated b c) 5 = .ok (.int .i64 (word c)) ∧
    readInt true 64 (word c) = (readValue c).value ∧
    (selected b c).block.id = sourceBlock c ∧
    getV (selected b c) 0 = .ok (embed c) ∧ word c < modulus 64 := by
  refine ⟨SourceDiscriminantStep.read _,
    SourceSwitchStep.select (⟨c,none,none⟩ : SourceFrame) (readValue c),
    start_constructor b c, ?_, rfl, signed_discriminant_preserved c,
    selected_identity b c, rfl, embedded_word_bounds c⟩
  exact ⟨allocated b c, discriminated b c,
    (allocate_constructor b c) ▸ step_complete (program b) (entry b c),
    (extract_constructor b c) ▸ step_complete (program b) (allocated b c),
    (switch_constructor b c) ▸ step_complete (program b) (discriminated b c)⟩

def precondition : OriginalConstructor := ⟨⟨0, by decide⟩⟩
theorem published_assignment_consumed (b : Bool) :
    selected b precondition = TrustMirBoolAssignment.before b rootFrame ∧
    runFunction (program b) 0 [embed precondition] 10 4 = .ret [.bool b] := by
  exact ⟨by cases b <;> rfl, actual_root_assignment b |>.2⟩

example : True := by
  fail_if_success
    have bad : OriginalConstructor := ⟨⟨16, by decide⟩⟩
  trivial
example : True := by
  fail_if_success
    have bad : OriginalConstructor := (⟨⟨0, by decide⟩⟩ : Constructor "foreign")
  trivial
example : sourceBlock (⟨⟨8, by decide⟩⟩ : OriginalConstructor) = 7 := rfl
example : select [(0,7),(0,8)] 0 = 7 := rfl
example : True := by
  fail_if_success
    have bad : embed precondition = .struct 0 [.int .i64 1] := rfl
  trivial
example : True := by
  fail_if_success
    have bad : sourceBlock (⟨⟨8, by decide⟩⟩ : OriginalConstructor) = 1 := rfl
  trivial
end TrustMirNominalSwitch
