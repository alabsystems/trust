/- Copyright 2026 Andrew Yates. Apache-2.0.
   Complete SAME-helper reflected-body composition; AST quotation remains OPEN.
   This extends the owning typed-view rules and uses actual SemR steps unchanged.
-/
import MirNominalSwitch
namespace TrustMirHelperReturn
open SemR TrustMirBoolAssignment TrustMirNominalSwitch
set_option maxRecDepth 40000
set_option maxHeartbeats 0
private theorem constructor_cases (c : OriginalConstructor) :
    c.variant.val = 0 ∨ c.variant.val = 1 ∨ c.variant.val = 2 ∨ c.variant.val = 3 ∨
    c.variant.val = 4 ∨ c.variant.val = 5 ∨ c.variant.val = 6 ∨ c.variant.val = 7 ∨
    c.variant.val = 8 ∨ c.variant.val = 9 ∨ c.variant.val = 10 ∨ c.variant.val = 11 ∨
    c.variant.val = 12 ∨ c.variant.val = 13 ∨ c.variant.val = 14 ∨ c.variant.val = 15 := by
  have h := c.variant.isLt
  change c.variant.val < 16 at h
  omega
private theorem branch_bounds (c : OriginalConstructor) : 1 ≤ sourceBlock c ∧ sourceBlock c ≤ 9 := by
  rcases c with ⟨⟨n,hn⟩⟩
  have h := constructor_cases (⟨⟨n,hn⟩⟩ : OriginalConstructor)
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp only at h <;> subst n <;> decide +revert

def branchIndex (c : OriginalConstructor) : Fin 9 :=
  ⟨sourceBlock c - 1, by have h := branch_bounds c; omega⟩
/-- Exact original MIR blocks1..9. Only block1 changes in the retained mutant. -/
def constants (originalBody : Bool) : List Bool :=
  [originalBody,true,true,true,true,true,true,true,false]
def sourceValue (b : Bool) (c : OriginalConstructor) : Bool :=
  constants b |>.get (branchIndex c)
def assignment (b : Bool) (c : OriginalConstructor) : Statement :=
  .assign ⟨2,[]⟩ (.use (.constantBool (sourceValue b c)))
def copyToReturn : Statement := .assign ⟨0,[]⟩ (.use (.copy ⟨2,[]⟩))
def initialSource (c : OriginalConstructor) : TrustMirBoolAssignment.SourceFrame :=
  ⟨⟨word c⟩,none,none⟩
def assignedSource (b : Bool) (c : OriginalConstructor) : TrustMirBoolAssignment.SourceFrame :=
  {initialSource c with local2 := some (sourceValue b c)}
def returnedSource (b : Bool) (c : OriginalConstructor) : TrustMirBoolAssignment.SourceFrame :=
  {assignedSource b c with local0 := some (sourceValue b c)}

def constId (c : OriginalConstructor) : Nat := 4 + 2 * sourceBlock c
def afterConst (b : Bool) (c : OriginalConstructor) : Core :=
  {next (selected b c) with env := (constId c,.bool (sourceValue b c)) :: (selected b c).env}
def afterCopy (b : Bool) (c : OriginalConstructor) : Core :=
  {next (afterConst b c) with env := (constId c + 1,.bool (sourceValue b c)) :: (afterConst b c).env}
def afterStore (b : Bool) (c : OriginalConstructor) : Core :=
  {next (afterCopy b c) with mem := memory (some (sourceValue b c))}
def afterGoto (b : Bool) (c : OriginalConstructor) : Core :=
  {afterStore b c with block := block b 10, pc := 0}
def afterLoad (b : Bool) (c : OriginalConstructor) : Core :=
  {next (afterGoto b c) with env := (24,.bool (sourceValue b c)) :: (afterGoto b c).env}
def afterReturnCopy (b : Bool) (c : OriginalConstructor) : Core :=
  {next (afterLoad b c) with env := (25,.bool (sourceValue b c)) :: (afterLoad b c).env}

private theorem pure_ok {α : Type} (x : α) : (pure x : R α) = .ok x := rfl
private theorem pointer_bits (b : Bool) : (program b).pointerBits = 64 := by cases b <;> rfl
private theorem load_node (b : Bool) (c : OriginalConstructor) :
    nth? (afterGoto b c).block.body (afterGoto b c).pc =
      some ⟨.load .bool 4 false none,[24]⟩ := by cases b <;> rfl
private theorem load_pointer (b : Bool) (c : OriginalConstructor) :
    getV (afterGoto b c) 4 = .ok (.ptr 0 0) := by
  rcases c with ⟨⟨n,hn⟩⟩
  have h := constructor_cases (⟨⟨n,hn⟩⟩ : OriginalConstructor)
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp only at h <;> subst n <;> cases b <;> rfl
private theorem access_slot (v : Bool) :
    accessAt (memory (some v)) "Load" 0 0 1 1 = .ok (slot (some v)) := by
  simp [accessAt,memory,slot,accessAlloc,addrSpace,nth?]
private theorem load_tail (b : Bool) (c : OriginalConstructor) :
    stepCore (program b) (afterGoto b c) = .cont (afterLoad b c) := by
  rw [stepCore,load_node]
  change ofR (loadStep (program b).pointerBits (afterGoto b c)
    ⟨.load .bool 4 false none,[24]⟩ .bool 4 false none) = _
  simp only [loadStep,pointer_bits,load_pointer,ok_bind]
  have hm : (afterGoto b c).mem = memory (some (sourceValue b c)) := rfl
  cases hv : sourceValue b c <;> simp [scalarLayout,checkAlign,isPow2,expectPtr,
    rejectPoison,pure_ok,ok_bind,hm,hv,access_slot,readOut,readBytes,byteAt,
    slot,image,firstUninit,decodeVal,b2n,nth?,afterLoad,bindResults,next,ofR]

/-- All seven ACTUAL remaining byte steps; no successful-run/store premises. -/
def TargetTail (b : Bool) (c : OriginalConstructor) : Prop :=
    stepCore (program b) (selected b c) = .cont (afterConst b c) ∧
    stepCore (program b) (afterConst b c) = .cont (afterCopy b c) ∧
    stepCore (program b) (afterCopy b c) = .cont (afterStore b c) ∧
    stepCore (program b) (afterStore b c) = .cont (afterGoto b c) ∧
    stepCore (program b) (afterGoto b c) = .cont (afterLoad b c) ∧
    stepCore (program b) (afterLoad b c) = .cont (afterReturnCopy b c) ∧
    stepCore (program b) (afterReturnCopy b c) = .done (.ret [.bool (sourceValue b c)])

theorem target_tail_steps (b : Bool) (c : OriginalConstructor) : TargetTail b c := by
  rcases c with ⟨⟨n,hn⟩⟩
  have h := constructor_cases (⟨⟨n,hn⟩⟩ : OriginalConstructor)
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp only at h <;> subst n <;> cases b <;> exact ⟨rfl,rfl,rfl,rfl,load_tail _ _,rfl,rfl⟩

theorem source_tail_steps (b : Bool) (c : OriginalConstructor) :
    SourceStep (assignment b c) (initialSource c) (assignedSource b c) ∧
    SourceGoto (.goto 10) ⟨sourceBlock c,1⟩ ⟨10,0⟩ ∧
    SourceStep copyToReturn (assignedSource b c) (returnedSource b c) ∧
    SourceReturn .return (returnedSource b c) (sourceValue b c) := by
  exact ⟨SourceStep.assignLocal2 _ _, SourceGoto.toReturn _,
    SourceStep.copyLocal2ToReturn _ _, SourceReturn.returned _ _⟩

private theorem run_three (m : Module) (a z : Core) (h : ThreeSteps m a z) (fuel : Nat) :
    run m (fuel+3) a = run m fuel z := by
  rcases h with ⟨x,y,hx,hy,hz⟩
  simp only [run, step_sound m a _ hx, step_sound m x _ hy, step_sound m y _ hz]

theorem target_tail_return (b : Bool) (c : OriginalConstructor) :
    run (program b) 7 (selected b c) = .ret [.bool (sourceValue b c)] := by
  obtain ⟨hc,hcopy,hs,hg,hl,hretcopy,hr⟩ := target_tail_steps b c
  simp only [run,hc,hcopy,hs,hg,hl,hretcopy,hr]

def TailCorrespondence (b : Bool) (c : OriginalConstructor) : Prop :=
    (afterStore b c).mem = memory (assignedSource b c).local2 ∧
    (assignedSource b c).local2 = some (sourceValue b c) ∧
    (returnedSource b c).local0 = some (sourceValue b c) ∧
    (afterGoto b c).block.id = 10 ∧ (afterGoto b c).pc = 0 ∧
    getV (afterLoad b c) 24 = .ok (.bool (sourceValue b c)) ∧
    getV (afterReturnCopy b c) 25 = .ok (.bool (sourceValue b c)) ∧
    getV (afterReturnCopy b c) 0 = .ok (embed c)

theorem tail_correspondence (b : Bool) (c : OriginalConstructor) : TailCorrespondence b c := by
  rcases c with ⟨⟨n,hn⟩⟩
  have h := constructor_cases (⟨⟨n,hn⟩⟩ : OriginalConstructor)
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp only at h <;> subst n <;> cases b <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Whole reflected helper for EVERY valid declared constructor, both original
    and retained body mutant. This does NOT authenticate the external AST view. -/
theorem helper_view_return (b : Bool) (c : OriginalConstructor) :
    SourceDiscriminantStep sourceStatement ⟨c,none,none⟩ ⟨c,some (readValue c),none⟩ ∧
    SourceSwitchStep sourceTerminator ⟨c,some (readValue c),none⟩
      ⟨c,some (readValue c),some (sourceBlock c)⟩ ∧
    SourceStep (assignment b c) (initialSource c) (assignedSource b c) ∧
    SourceGoto (.goto 10) ⟨sourceBlock c,1⟩ ⟨10,0⟩ ∧
    SourceStep copyToReturn (assignedSource b c) (returnedSource b c) ∧
    SourceReturn .return (returnedSource b c) (sourceValue b c) ∧
    start (program b) 0 [embed c] 4 = .ok (TrustMirNominalSwitch.entry b c) ∧
    ThreeSteps (program b) (TrustMirNominalSwitch.entry b c) (selected b c) ∧
    TargetTail b c ∧ TailCorrespondence b c ∧
    runFunction (program b) 0 [embed c] 10 4 = .ret [.bool (sourceValue b c)] := by
  obtain ⟨sd,ss,hs,hprefix,_⟩ := prefix_simulates b c
  obtain ⟨sa,sg,sc,sr⟩ := source_tail_steps b c
  refine ⟨sd,ss,sa,sg,sc,sr,hs,hprefix,target_tail_steps b c,tail_correspondence b c,?_⟩
  simp only [runFunction,hs]
  rw [show 10 = 7+3 from rfl, run_three _ _ _ hprefix 7]
  exact target_tail_return b c

example (c : OriginalConstructor) : True := by
  fail_if_success
    have bad : SourceStep copyToReturn (initialSource c) (returnedSource true c) :=
      SourceStep.copyLocal2ToReturn _ _
  trivial
example (c : OriginalConstructor) : True := by
  fail_if_success
    have bad : SourceReturn .return (initialSource c) false := SourceReturn.returned _ _
  trivial
example : True := by
  fail_if_success
    have bad : SourceGoto (.goto 11) ⟨1,1⟩ ⟨11,0⟩ := SourceGoto.toReturn _
  trivial
end TrustMirHelperReturn
