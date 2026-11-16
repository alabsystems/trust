/- Source-bound logical refinement for the generated evaluator quotation.
   The producer is untrusted. These goals mention the actual Original module,
   generated functions and all original/lifted bodies. They do not authenticate
   a canonical Rust Module, runtime environment, ABI, bytes or admission token. -/
import Proposal
import ClosureU64Caller

namespace SourceArrow
open TrustIr ClosureU64
set_option maxRecDepth 1024

/-- A source function's application observes its generated closure value.
    The fresh SSA frame is explicit; every other world field is unchanged. -/
def applicationExit (world : MachineState) (held : Value) (x result : UInt64) : MachineState :=
  { world with
    locals := ((ValueMap.empty.set (valueId 0) held).set (valueId 1) (word x)).set
      (valueId 2) (word result)
    nextValueId := 3 }

/-- Bounded logical arrow relation for this proposed context. It grants no
    total carrier for arbitrary Lean functions. A witness must establish real
    checked construction and normal application for every input and world;
    the maker theorem below constructs that witness without a success premise. -/
structure Represents (depth : Nat) (source : UInt64 → UInt64) (held : Value) : Prop where
  constructed : ∃ captures, makeClosureValue (SourceProposal.context depth) ⟨0⟩ ⟨3⟩ captures = .ok held
  application : ∀ (world : MachineState) (x : UInt64),
    Sem.run (stepNWithContext (SourceProposal.context depth) 2 (depth + 2)
      SourceProposal.application.cfg ⟨0⟩ [held, word x]) (entryState world) =
      .ok ([word (source x)], applicationExit world held x (source x))

/- These equalities are checked about the actual generated quotation. Reusing
   existing execution lemmas through them does not assert generator correctness. -/
theorem generated_target : SourceProposal.target = ClosureU64.target := rfl
theorem generated_maker : SourceProposal.maker = ClosureU64.maker := rfl
theorem generated_application : SourceProposal.application = ClosureU64.application := rfl
theorem generated_caller : SourceProposal.caller = ClosureU64.caller := rfl
theorem generated_context (depth : Nat) : SourceProposal.context depth = ClosureU64.context depth := rfl

theorem original_roster : SourceProposal.originalRoster =
    [("EscapingOriginal.useAffine", ⟨0⟩), ("EscapingOriginal.makeAffine", ⟨1⟩),
     ("EscapingOriginal.apply64", ⟨2⟩)] := rfl

theorem lifted_roster : SourceProposal.liftedRoster =
    [("EscapingOriginal.makeAffine.__closure_target", ⟨3⟩)] := rfl

/-- All four generated code bodies are present and every other identity is
    absent. Roster custody with an actual canonical Module remains separate. -/
theorem complete_context (depth : Nat) (id : FuncId) :
    (SourceProposal.context depth).functions id =
      if id == (⟨0⟩ : FuncId) then some SourceProposal.caller
      else if id == (⟨1⟩ : FuncId) then some SourceProposal.maker
      else if id == (⟨2⟩ : FuncId) then some SourceProposal.application
      else if id == (⟨3⟩ : FuncId) then some SourceProposal.target else none := rfl

theorem original_arrow_represented (depth : Nat) (a b : UInt64) :
    Represents depth (EscapingOriginal.makeAffine a b) (closure a b) := by
  constructor
  · refine ⟨[word a, word b], ?_⟩
    rw [generated_context]
    exact construction_exact depth a b
  · intro world x
    rw [generated_context, generated_application]
    exact application_body_evaluates depth world a b x

/-- Actual generated maker normal execution returns a representation of the
    actual original arrow, for arbitrary captures and surrounding worlds. -/
theorem original_maker_refines (depth callDepth : Nat) (world : MachineState) (a b : UInt64) :
    Sem.run (stepNWithContext (SourceProposal.context depth) 2 callDepth
      SourceProposal.maker.cfg ⟨0⟩ [word a, word b]) (entryState world) =
        .ok ([closure a b], makerState world a b) ∧
      Represents depth (EscapingOriginal.makeAffine a b) (closure a b) := by
  constructor
  · rw [generated_context, generated_maker]
    exact maker_body_evaluates depth callDepth world a b
  · exact original_arrow_represented depth a b

theorem original_application_refines (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepNWithContext (SourceProposal.context depth) 2 (depth + 2)
      SourceProposal.application.cfg ⟨0⟩ [closure a b, word x]) (entryState world) =
      .ok ([word (EscapingOriginal.apply64 (EscapingOriginal.makeAffine a b) x)],
        applicationExit world (closure a b) x
          (EscapingOriginal.apply64 (EscapingOriginal.makeAffine a b) x)) :=
  (original_arrow_represented depth a b).application world x

theorem original_lifted_target_refines (depth callDepth : Nat) (world : MachineState)
    (a b x : UInt64) :
    Sem.run (stepNWithContext (SourceProposal.context depth) 1 callDepth
      SourceProposal.target.cfg ⟨0⟩ [word a, word b, word x]) (entryState world) =
      .ok ([word (EscapingOriginal.makeAffine a b x)], targetState world a b x) := by
  rw [generated_context, generated_target]
  exact target_body_evaluates depth callDepth world a b x

/-- No successful execution or representation is assumed. The actual generated
    maker, returned function parameter, application and lifted target compose. -/
theorem original_caller_refines (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (evalFunctionInContext (SourceProposal.context depth) ⟨0⟩
      [word a, word b, word x] 3 .abort) (entryState world) =
      .ok ([word (EscapingOriginal.useAffine a b x)], callerState world a b x) := by
  rw [generated_context]
  exact caller_evaluates depth world a b x

theorem application_world_preserved (world : MachineState) (held : Value) (x result : UInt64) :
    { applicationExit world held x result with
      locals := world.locals, nextValueId := world.nextValueId } = world := rfl

theorem caller_world_preserved (world : MachineState) (a b x : UInt64) :
    { callerState world a b x with locals := world.locals, nextValueId := world.nextValueId } =
      world := caller_world_restored world a b x

/-- One constructive subject covers every original body and the lifted target
    in this quotation. Canonical source/module custody is not asserted here. -/
theorem quotation_refinement (depth : Nat) (world : MachineState) (a b x : UInt64) :
    (Sem.run (stepNWithContext (SourceProposal.context depth) 2 (depth + 3)
      SourceProposal.maker.cfg ⟨0⟩ [word a, word b]) (entryState world) =
        .ok ([closure a b], makerState world a b) ∧
      Represents depth (EscapingOriginal.makeAffine a b) (closure a b)) ∧
    (Sem.run (stepNWithContext (SourceProposal.context depth) 2 (depth + 2)
      SourceProposal.application.cfg ⟨0⟩ [closure a b, word x]) (entryState world) =
        .ok ([word (EscapingOriginal.apply64 (EscapingOriginal.makeAffine a b) x)],
          applicationExit world (closure a b) x (EscapingOriginal.makeAffine a b x))) ∧
    (Sem.run (stepNWithContext (SourceProposal.context depth) 1 (depth + 3)
      SourceProposal.target.cfg ⟨0⟩ [word a, word b, word x]) (entryState world) =
        .ok ([word (EscapingOriginal.makeAffine a b x)], targetState world a b x)) ∧
    (Sem.run (evalFunctionInContext (SourceProposal.context depth) ⟨0⟩
      [word a, word b, word x] 3 .abort) (entryState world) =
        .ok ([word (EscapingOriginal.useAffine a b x)], callerState world a b x)) := by
  exact ⟨original_maker_refines depth (depth + 3) world a b,
    original_application_refines depth world a b x,
    original_lifted_target_refines depth (depth + 3) world a b x,
    original_caller_refines depth world a b x⟩

#print axioms original_arrow_represented
#print axioms original_maker_refines
#print axioms original_application_refines
#print axioms original_lifted_target_refines
#print axioms original_caller_refines
#print axioms application_world_preserved
#print axioms caller_world_preserved
#print axioms quotation_refinement
end SourceArrow
