/- Exact observed three-local/four-block body DATA and its finite path relation.
   Not an interpreter, MIR quotation theorem, or source authority. Rust checker
   correctness and actual compiler semantics remain explicit TCB boundaries. -/
import LiveHelperEnumWire
namespace TrustLiveHelperBodyView
open SemR TrustMirBoolAssignment TrustMirNominalSwitch TrustMirHelperReturn
set_option maxRecDepth 40000
set_option maxHeartbeats 0

inductive ObservedLocalType where | bool | nominal | isize deriving DecidableEq
/-- Move is retained explicitly; no Copy substitution is admitted. -/
inductive ObservedExit where
  | moveSwitch (movedLocal : Nat) (cases : List (Nat × Nat)) (otherwise : Nat)
  | goto (block : Nat)
  | ret
  deriving DecidableEq
structure ObservedBlock where
  id : Nat
  statements : List Statement
  /-- Runtime MIR Use retag flags, parallel to the statement population.
      Discriminant has no Use flag. No retag semantic theorem is inferred. -/
  useRetags : List (Option Bool)
  exit : ObservedExit
  deriving DecidableEq
structure ObservedBody where
  arguments : Nat
  locals : List (Nat × ObservedLocalType)
  blocks : List ObservedBlock
  deriving DecidableEq

def trueTags : List Nat := [0,1,2,3,4,5,8,9]
def cases : List (Nat × Nat) := trueTags.map (fun n => (n,2))
def liveEntry : ObservedBlock := ⟨0,[.assign ⟨2,[]⟩ (.discriminant ⟨1,[]⟩)],
  [none],.moveSwitch 2 cases 1⟩
def liveBranch (id : Nat) (value : Bool) : ObservedBlock :=
  ⟨id,[.assign ⟨0,[]⟩ (.use (.constantBool value))],[some true],.goto 3⟩
def liveReturnBlock : ObservedBlock := ⟨3,[],[],.ret⟩
/-- Complete observed body; no historical eleven-block reconstruction. -/
def liveBody : ObservedBody := ⟨1,[(0,.bool),(1,.nominal),(2,.isize)],
  [liveEntry,liveBranch 1 false,liveBranch 2 true,liveReturnBlock]⟩
/-- Data selection for this exact table, whose every case targets block2.
    This is not a general MIR execution function. -/
def selectedBlock (c : OriginalConstructor) : Nat :=
  if trueTags.contains c.variant.val then 2 else 1

private theorem constructor_cases (c : OriginalConstructor) :
    c.variant.val = 0 ∨ c.variant.val = 1 ∨ c.variant.val = 2 ∨ c.variant.val = 3 ∨
    c.variant.val = 4 ∨ c.variant.val = 5 ∨ c.variant.val = 6 ∨ c.variant.val = 7 ∨
    c.variant.val = 8 ∨ c.variant.val = 9 ∨ c.variant.val = 10 ∨ c.variant.val = 11 ∨
    c.variant.val = 12 ∨ c.variant.val = 13 ∨ c.variant.val = 14 ∨ c.variant.val = 15 := by
  have h := c.variant.isLt
  change c.variant.val < 16 at h
  omega

theorem exact_population : liveBody.arguments = 1 ∧
    liveBody.locals = [(0,.bool),(1,.nominal),(2,.isize)] ∧
    liveBody.blocks.length = 4 ∧ liveBody.blocks.map (fun b => b.statements.length) = [1,1,1,0] :=
  ⟨rfl,rfl,rfl,rfl⟩
theorem exact_move_entry : liveBody.blocks[0]? = some
    ⟨0,[.assign ⟨2,[]⟩ (.discriminant ⟨1,[]⟩)],[none],
      .moveSwitch 2 [(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(8,2),(9,2)] 1⟩ := rfl
theorem declared_branch (c : OriginalConstructor) : liveBody.blocks[selectedBlock c]? =
    some (liveBranch (selectedBlock c) (sourceValue true c)) := by
  rcases c with ⟨⟨n,hn⟩⟩
  have h := constructor_cases (⟨⟨n,hn⟩⟩ : OriginalConstructor)
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp only at h <;> subst n <;> rfl
theorem exact_return : liveBody.blocks[3]? = some ⟨3,[],[],.ret⟩ := rfl
/-- Finite structural path and independently decoded Enum byte outcome agree.
    There is no premise claiming the Rustc snapshot quoted itself faithfully. -/
theorem body_path_and_byte_outcome (c : OriginalConstructor) :
    liveBody.blocks[0]? = some liveEntry ∧
    liveBody.blocks[selectedBlock c]? = some (liveBranch (selectedBlock c) (sourceValue true c)) ∧
    liveBody.blocks[3]? = some liveReturnBlock ∧
    runFunction TrustLiveHelperEnumWire.original 0 [TrustLiveHelperEnumWire.embed c] 128 4 =
      .ret [.bool (sourceValue true c)] :=
  ⟨rfl,declared_branch c,rfl,TrustLiveHelperEnumWire.declared_return c⟩
/-- Exact source edit removes tag0, so its structural destination is the false
    block and its actually produced byte image returns false too. -/
theorem source_arm_mutant :
    ((trueTags.drop 1).contains 0) = false ∧
    liveBody.blocks[1]? = some (liveBranch 1 false) ∧
    runFunction TrustLiveHelperEnumWire.mutant 0
      [TrustLiveHelperEnumWire.embed ⟨⟨0,by decide⟩⟩] 128 4 = .ret [.bool false] :=
  ⟨rfl,rfl,TrustLiveHelperEnumWire.source_mutant_changes_first⟩
/-- The exact body view cannot silently admit changed target ownership. -/
theorem wrong_destination_not_entry :
    (⟨0,[.assign ⟨2,[]⟩ (.discriminant ⟨1,[]⟩)],[none],
      .moveSwitch 2 [(0,1),(1,2),(2,2),(3,2),(4,2),(5,2),(8,2),(9,2)] 1⟩ : ObservedBlock) ≠ liveEntry := by decide
end TrustLiveHelperBodyView
