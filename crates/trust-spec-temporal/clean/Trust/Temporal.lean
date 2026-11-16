-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- Trust's primary temporal proposition vocabulary. This is Clean source, not
-- TLA+ and not a Rust macro facade. ty may use TLA+ internally when it searches
-- for a certificate, but a user-authored proposition has this denotation.

namespace Trust
namespace Temporal

def Behavior (State : Type) := Nat → State
def Formula (State : Type) := Behavior State → Prop

def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
  fun k => b (n + k)

def Always {State : Type} (F : Formula State) : Formula State :=
  fun b => ∀ n, F (drop b n)

def Eventually {State : Type} (F : Formula State) : Formula State :=
  fun b => ∃ n, F (drop b n)

def LeadsTo {State : Type} (F G : Formula State) : Formula State :=
  Always (fun b => F b → Eventually G b)

-- A temporal proposition ranges over an authored transition system, not an
-- unbound formula.  `Runs` has TLA+'s stutter-permissive `[Next]_vars`
-- semantics; liveness claims therefore state their weak-fairness assumption
-- explicitly.
structure StateMachine (State : Type) where
  init : State → Prop
  next : State → State → Prop

def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
  M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

def Lift {State : Type} (P : State → Prop) : Formula State :=
  fun b => P (b 0)

def NonStuttering {State : Type} (A : State → State → Prop)
    (s s' : State) : Prop :=
  A s s' ∧ ¬ (s' = s)

def Enabled {State : Type} (A : State → State → Prop) (s : State) : Prop :=
  ∃ s', NonStuttering A s s'

def LiftAction {State : Type} (A : State → State → Prop) : Formula State :=
  fun b => NonStuttering A (b 0) (b 1)

def WeakFair {State : Type} (A : State → State → Prop) : Formula State :=
  Always (fun b =>
    Eventually (Always (Lift (Enabled A))) b → Eventually (LiftAction A) b)

-- Strong fairness is the complementary, recurring-enablement obligation:
-- whenever a non-stuttering action remains enabled infinitely often, that
-- action must eventually occur.  Both notions are formulas so they compose
-- with the same suffix semantics as `□`, `◇`, and `~>`.
def StrongFair {State : Type} (A : State → State → Prop) : Formula State :=
  Always (fun b =>
    Always (Eventually (Lift (Enabled A))) b → Eventually (LiftAction A) b)

-- Fairness assumptions are action-scoped.  An indexed family is deliberately
-- more general than a `List`: it expresses any finite authored action list,
-- named action families, and proof-oriented infinite families without adding a
-- second temporal semantics.
inductive FairnessConstraint (State : Type) where
  | weak : (State → State → Prop) → FairnessConstraint State
  | strong : (State → State → Prop) → FairnessConstraint State

def HoldsFairness {State : Type} (constraint : FairnessConstraint State) :
    Formula State :=
  match constraint with
  | FairnessConstraint.weak action => WeakFair action
  | FairnessConstraint.strong action => StrongFair action

def FairFamily {State Index : Type}
    (constraints : Index → FairnessConstraint State) : Formula State :=
  fun b => ∀ index, HoldsFairness (constraints index) b

def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
  ∀ b, Runs M b → F b

def SatisfiesUnderWeakFairness {State : Type}
    (M : StateMachine State) (F : Formula State) : Prop :=
  ∀ b, Runs M b → WeakFair M.next b → F b

def SatisfiesUnderFairness {State Index : Type}
    (M : StateMachine State)
    (constraints : Index → FairnessConstraint State)
    (F : Formula State) : Prop :=
  ∀ b, Runs M b → FairFamily constraints b → F b

-- A proof-carrying forward simulation connects an actual program transition
-- system to an authored abstraction.  A concrete step may map either to an
-- abstract step or to abstract stuttering, matching `Runs`' stutter-permissive
-- semantics.  This is deliberately a proposition, not an unchecked adapter:
-- every model/program pairing must provide a kernel-checked inhabitant.
structure ForwardRefinement {Concrete Abstract : Type}
    (concrete : StateMachine Concrete)
    (abstractModel : StateMachine Abstract)
    (project : Concrete → Abstract) : Prop where
  init : ∀ state : Concrete,
    concrete.init state → abstractModel.init (project state)
  next : ∀ before after : Concrete,
    concrete.next before after →
      abstractModel.next (project before) (project after) ∨
        project after = project before

theorem forwardRefinementRuns {Concrete Abstract : Type}
    (concrete : StateMachine Concrete)
    (abstractModel : StateMachine Abstract)
    (project : Concrete → Abstract)
    (refinement : ForwardRefinement concrete abstractModel project)
    (behavior : Behavior Concrete)
    (runs : Runs concrete behavior) :
    Runs abstractModel (fun n => project (behavior n)) :=
  And.intro
    (refinement.init (behavior 0) runs.1)
    (fun n =>
      Or.elim (runs.2 n)
        (fun step => refinement.next (behavior n) (behavior (Nat.succ n)) step)
        (fun stutter => Or.inr (congrArg project stutter)))

-- Pull an abstract temporal proposition back to concrete executions through
-- the same projection used by the refinement proof.
def Pullback {Concrete Abstract : Type}
    (project : Concrete → Abstract) (F : Formula Abstract) : Formula Concrete :=
  fun behavior => F (fun n => project (behavior n))

theorem forwardRefinementSatisfies {Concrete Abstract : Type}
    (concrete : StateMachine Concrete)
    (abstractModel : StateMachine Abstract)
    (project : Concrete → Abstract)
    (refinement : ForwardRefinement concrete abstractModel project)
    (F : Formula Abstract)
    (holds : Satisfies abstractModel F) :
    Satisfies concrete (Pullback project F) :=
  fun behavior runs =>
    holds (fun n => project (behavior n))
      (forwardRefinementRuns concrete abstractModel project refinement behavior runs)

-- Fairness does not automatically survive abstraction: a projection can hide
-- the very non-stuttering step whose scheduling assumption matters.  Transport
-- is therefore explicit about the honest premise—the projected concrete run
-- must satisfy the abstract model's exact authored fairness family.
theorem forwardRefinementSatisfiesUnderFairness
    {Concrete Abstract Index : Type}
    (concrete : StateMachine Concrete)
    (abstractModel : StateMachine Abstract)
    (project : Concrete → Abstract)
    (refinement : ForwardRefinement concrete abstractModel project)
    (constraints : Index → FairnessConstraint Abstract)
    (F : Formula Abstract)
    (holds : SatisfiesUnderFairness abstractModel constraints F) :
    ∀ behavior : Behavior Concrete,
      Runs concrete behavior →
      FairFamily constraints (fun n => project (behavior n)) →
      Pullback project F behavior :=
  fun behavior runs fair =>
    holds (fun n => project (behavior n))
      (forwardRefinementRuns concrete abstractModel project refinement behavior runs)
      fair

-- A reachable-state simulation keeps the original concrete transition relation.
-- The invariant is evidence to establish along actual runs, not a filter that
-- removes concrete steps from the machine being refined.
structure InvariantForwardRefinement {Concrete Abstract : Type}
    (concrete : StateMachine Concrete)
    (abstractModel : StateMachine Abstract)
    (project : Concrete → Abstract)
    (invariant : Concrete → Prop) : Prop where
  init_invariant : ∀ state : Concrete, concrete.init state → invariant state
  preserve_invariant : ∀ before after : Concrete,
    invariant before → concrete.next before after → invariant after
  init : ∀ state : Concrete,
    concrete.init state → abstractModel.init (project state)
  next : ∀ before after : Concrete,
    invariant before → concrete.next before after →
      abstractModel.next (project before) (project after) ∨
        project after = project before

theorem invariantForwardRefinementInvariant {Concrete Abstract : Type}
    (concrete : StateMachine Concrete)
    (abstractModel : StateMachine Abstract)
    (project : Concrete → Abstract)
    (invariant : Concrete → Prop)
    (refinement : InvariantForwardRefinement concrete abstractModel project invariant)
    (behavior : Behavior Concrete)
    (runs : Runs concrete behavior) :
    ∀ n : Nat, invariant (behavior n) :=
  Nat.rec
    (refinement.init_invariant (behavior 0) runs.1)
    (fun n previous =>
      Or.elim (runs.2 n)
        (fun step =>
          refinement.preserve_invariant (behavior n) (behavior (Nat.succ n)) previous step)
        (fun stutter => Eq.mpr (congrArg invariant stutter) previous))

theorem invariantForwardRefinementRuns {Concrete Abstract : Type}
    (concrete : StateMachine Concrete)
    (abstractModel : StateMachine Abstract)
    (project : Concrete → Abstract)
    (invariant : Concrete → Prop)
    (refinement : InvariantForwardRefinement concrete abstractModel project invariant)
    (behavior : Behavior Concrete)
    (runs : Runs concrete behavior) :
    Runs abstractModel (fun n => project (behavior n)) :=
  And.intro
    (refinement.init (behavior 0) runs.1)
    (fun n =>
      Or.elim (runs.2 n)
        (fun step => refinement.next (behavior n) (behavior (Nat.succ n))
          (invariantForwardRefinementInvariant concrete abstractModel project invariant
            refinement behavior runs n) step)
        (fun stutter => Or.inr (congrArg project stutter)))

theorem invariantForwardRefinementSatisfies {Concrete Abstract : Type}
    (concrete : StateMachine Concrete)
    (abstractModel : StateMachine Abstract)
    (project : Concrete → Abstract)
    (invariant : Concrete → Prop)
    (refinement : InvariantForwardRefinement concrete abstractModel project invariant)
    (F : Formula Abstract)
    (holds : Satisfies abstractModel F) :
    Satisfies concrete (Pullback project F) :=
  fun behavior runs =>
    holds (fun n => project (behavior n))
      (invariantForwardRefinementRuns concrete abstractModel project invariant
        refinement behavior runs)

-- Fairness is still an explicit premise about the projected concrete run.
theorem invariantForwardRefinementSatisfiesUnderFairness
    {Concrete Abstract Index : Type}
    (concrete : StateMachine Concrete)
    (abstractModel : StateMachine Abstract)
    (project : Concrete → Abstract)
    (invariant : Concrete → Prop)
    (refinement : InvariantForwardRefinement concrete abstractModel project invariant)
    (constraints : Index → FairnessConstraint Abstract)
    (F : Formula Abstract)
    (holds : SatisfiesUnderFairness abstractModel constraints F) :
    ∀ behavior : Behavior Concrete,
      Runs concrete behavior →
      FairFamily constraints (fun n => project (behavior n)) →
      Pullback project F behavior :=
  fun behavior runs fair =>
    holds (fun n => project (behavior n))
      (invariantForwardRefinementRuns concrete abstractModel project invariant
        refinement behavior runs)
      fair

-- Notation expansion happens at the use site, so force every expansion target
-- through Clean's root-namespace escape.  A merely dotted name such as
-- `Trust.Temporal.Always` is still namespace-relative: inside `namespace N`,
-- `N.Trust.Temporal.Always` wins when it exists.
prefix:100 "□" => _root_.Trust.Temporal.Always
prefix:100 "◇" => _root_.Trust.Temporal.Eventually
infixl:50 " ~> " => _root_.Trust.Temporal.LeadsTo
infixl:45 " ⊨ " => _root_.Trust.Temporal.Satisfies

-- These pins make the exported notation executable evidence: the full Clean
-- file pipeline elaborates each pretty proposition to its ordinary definition,
-- and the kernel checks the resulting proof term.
theorem box_unfolds {State : Type} (F : Formula State) : (□ F) = Always F := rfl
theorem diamond_unfolds {State : Type} (F : Formula State) : (◇ F) = Eventually F := rfl
theorem leadsto_unfolds {State : Type} (F G : Formula State) :
    (F ~> G) = LeadsTo F G := rfl

theorem box_implies_diamond {State : Type} (F : Formula State) (b : Behavior State)
    (h : (□ F) b) : (◇ F) b :=
  ⟨0, h 0⟩

theorem drop_zero {State : Type} (b : Behavior State) : drop b 0 = b :=
  by
    funext k
    exact congrArg b (Nat.zero_add k)

theorem leadsto_refl {State : Type} (F : Formula State) (b : Behavior State) :
    (F ~> F) b :=
  fun n h => ⟨0, Eq.mpr (congrArg F (drop_zero (drop b n))) h⟩

theorem always_implies_leadsto {State : Type} (F G : Formula State)
    (b : Behavior State) (h : (□ G) b) : (F ~> G) b :=
  fun n _ => ⟨0, Eq.mpr (congrArg G (drop_zero (drop b n))) (h n)⟩

end Temporal
end Trust
