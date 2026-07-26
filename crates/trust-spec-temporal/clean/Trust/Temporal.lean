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

def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
  ∀ b, Runs M b → F b

def SatisfiesUnderWeakFairness {State : Type}
    (M : StateMachine State) (F : Formula State) : Prop :=
  ∀ b, Runs M b → WeakFair M.next b → F b

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

end Temporal
end Trust
