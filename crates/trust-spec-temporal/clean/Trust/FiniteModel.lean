-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- A kernel-elaborated, user-authored finite-model vocabulary.  The scalar
-- compatibility structure remains source-compatible with the old migration
-- lane; `Model` adds finite Boolean-function state.  The definitions below also
-- give the data an ordinary Clean transition semantics.  The Rust bridge
-- decodes the same kernel-checked value and derives ty's private TLA+ image;
-- that reviewed cross-language translation remains in the TCB, while the
-- proposition to which evidence is bound is now an actual applied
-- `Trust.Temporal.StateMachine`.

namespace Trust
namespace Temporal
namespace FiniteModel

-- The scalar expression union accepted by the old model value.  Arithmetic is
-- over the nonnegative fragment used by the macro surface.  References are
-- names, just as they were in `trust_model!`; the consumer rejects missing,
-- duplicate, or cross-sort names before generating a model. `ite` preserves the
-- common scalar sort of its branches; the bridge rejects mixed-sort branches.
inductive ScalarExpr where
  | int : Nat → ScalarExpr
  | var : String → ScalarExpr
  | constRef : String → ScalarExpr
  | add : ScalarExpr → ScalarExpr → ScalarExpr
  | sub : ScalarExpr → ScalarExpr → ScalarExpr
  | gt : ScalarExpr → ScalarExpr → ScalarExpr
  | le : ScalarExpr → ScalarExpr → ScalarExpr
  | eq : ScalarExpr → ScalarExpr → ScalarExpr
  | neq : ScalarExpr → ScalarExpr → ScalarExpr
  | or : ScalarExpr → ScalarExpr → ScalarExpr
  | and : ScalarExpr → ScalarExpr → ScalarExpr
  | ite : ScalarExpr → ScalarExpr → ScalarExpr → ScalarExpr
  | iff : ScalarExpr → ScalarExpr → ScalarExpr
  | forallIn : String → ScalarExpr → ScalarExpr → ScalarExpr → ScalarExpr
  | fnAccess : String → ScalarExpr → ScalarExpr
  | except : String → ScalarExpr → ScalarExpr → ScalarExpr
  | comprehension : String → ScalarExpr → ScalarExpr → ScalarExpr → ScalarExpr
  | bool : Bool → ScalarExpr

structure Constant where
  name : String
  value : Nat

structure StateVar where
  name : String
  init : Nat

structure FunctionVar where
  name : String
  rangeConstant : String

structure Update where
  var : String
  value : ScalarExpr

inductive Guard where
  | always
  | when : ScalarExpr → Guard

structure Action where
  name : String
  guard : Guard
  updates : List Update

structure Invariant where
  name : String
  value : ScalarExpr

structure ScalarModel where
  name : String
  constants : List Constant
  variables : List StateVar
  actions : List Action
  invariants : List Invariant

-- Full finite Model ABI.  `ScalarModel` is retained as the compatibility
-- constructor so existing authored migration sources do not change arity.
structure Model where
  name : String
  constants : List Constant
  variables : List StateVar
  functionVariables : List FunctionVar
  actions : List Action
  invariants : List Invariant

def ScalarModel.asModel (model : ScalarModel) : Model :=
  Model.mk model.name model.constants model.variables [] model.actions model.invariants

-- Membership is defined locally so the semantic vocabulary depends only on
-- Clean's foundational `List` constructors, not on a library search/import.
inductive Member {α : Type} (value : α) : List α → Prop where
  | head (tail : List α) : Member value (value :: tail)
  | tail (head : α) (tail : List α) :
      Member value tail → Member value (head :: tail)

-- A total carrier makes state equality extensional and keeps stuttering
-- semantics ordinary.  Well-formed applied states canonicalize every
-- undeclared scalar/function coordinate to zero/false.
structure State where
  scalar : String → Nat
  function : String → Nat → Bool

inductive Value where
  | nat : Nat → Value
  | bool : Bool → Value
  | function : String → (Nat → Bool) → Value

def DeclaresScalar (model : Model) (name : String) : Prop :=
  ∃ entry : StateVar,
    Member entry model.variables ∧ entry.name = name

def DeclaresFunction (model : Model) (name : String) : Prop :=
  ∃ entry : FunctionVar,
    Member entry model.functionVariables ∧ entry.name = name

def FunctionRange (model : Model) (name range : String) : Prop :=
  ∃ entry : FunctionVar,
    Member entry model.functionVariables ∧
    entry.name = name ∧ entry.rangeConstant = range

def ConstantValue (model : Model) (name : String) (value : Nat) : Prop :=
  ∃ entry : Constant, Member entry model.constants ∧
    entry.name = name ∧ entry.value = value

def FunctionDomain (model : Model) (range : String) (index : Nat) : Prop :=
  ∃ high : Nat,
    ConstantValue model range high ∧ Nat.le 1 index ∧ Nat.le index high

def DeclaresFunctionAt (model : Model) (name : String) (index : Nat) : Prop :=
  ∃ range : String,
    FunctionRange model name range ∧ FunctionDomain model range index

def LocalValue (locals : List (String × Nat)) (name : String) (value : Nat) : Prop :=
  ∃ binding : String × Nat,
    Member binding locals ∧ binding.1 = name ∧ binding.2 = value

-- Relational evaluation avoids hiding partiality behind a default value.  A
-- malformed or ill-sorted expression simply has no derivation; Rust performs
-- the matching deterministic well-formedness check before certification.
inductive Evaluates (model : Model) :
    List (String × Nat) → State → ScalarExpr → Value → Prop where
  | int (value : Nat) :
      Evaluates model locals state (ScalarExpr.int value) (Value.nat value)
  | stateVar (name : String) :
      DeclaresScalar model name →
      Evaluates model locals state (ScalarExpr.var name) (Value.nat (state.scalar name))
  | localVar (name : String) (value : Nat) :
      LocalValue locals name value →
      Evaluates model locals state (ScalarExpr.var name) (Value.nat value)
  | functionVar (name range : String) :
      FunctionRange model name range →
      Evaluates model locals state (ScalarExpr.var name)
        (Value.function range (state.function name))
  | constRef (name : String) (value : Nat) :
      ConstantValue model name value →
      Evaluates model locals state (ScalarExpr.constRef name) (Value.nat value)
  | add (left right : ScalarExpr) (leftValue rightValue : Nat) :
      Evaluates model locals state left (Value.nat leftValue) →
      Evaluates model locals state right (Value.nat rightValue) →
      Evaluates model locals state (ScalarExpr.add left right)
        (Value.nat (leftValue + rightValue))
  | sub (left right : ScalarExpr) (leftValue rightValue : Nat) :
      Evaluates model locals state left (Value.nat leftValue) →
      Evaluates model locals state right (Value.nat rightValue) →
      Evaluates model locals state (ScalarExpr.sub left right)
        (Value.nat (leftValue - rightValue))
  | gtTrue (left right : ScalarExpr) (leftValue rightValue : Nat) :
      Evaluates model locals state left (Value.nat leftValue) →
      Evaluates model locals state right (Value.nat rightValue) →
      Nat.lt rightValue leftValue →
      Evaluates model locals state (ScalarExpr.gt left right) (Value.bool true)
  | gtFalse (left right : ScalarExpr) (leftValue rightValue : Nat) :
      Evaluates model locals state left (Value.nat leftValue) →
      Evaluates model locals state right (Value.nat rightValue) →
      Nat.le leftValue rightValue →
      Evaluates model locals state (ScalarExpr.gt left right) (Value.bool false)
  | leTrue (left right : ScalarExpr) (leftValue rightValue : Nat) :
      Evaluates model locals state left (Value.nat leftValue) →
      Evaluates model locals state right (Value.nat rightValue) →
      Nat.le leftValue rightValue →
      Evaluates model locals state (ScalarExpr.le left right) (Value.bool true)
  | leFalse (left right : ScalarExpr) (leftValue rightValue : Nat) :
      Evaluates model locals state left (Value.nat leftValue) →
      Evaluates model locals state right (Value.nat rightValue) →
      Nat.lt rightValue leftValue →
      Evaluates model locals state (ScalarExpr.le left right) (Value.bool false)
  | eqTrue (left right : ScalarExpr) (leftValue rightValue : Nat) :
      Evaluates model locals state left (Value.nat leftValue) →
      Evaluates model locals state right (Value.nat rightValue) →
      leftValue = rightValue →
      Evaluates model locals state (ScalarExpr.eq left right) (Value.bool true)
  | eqFalse (left right : ScalarExpr) (leftValue rightValue : Nat) :
      Evaluates model locals state left (Value.nat leftValue) →
      Evaluates model locals state right (Value.nat rightValue) →
      (¬ (leftValue = rightValue)) →
      Evaluates model locals state (ScalarExpr.eq left right) (Value.bool false)
  | neqTrue (left right : ScalarExpr) (leftValue rightValue : Nat) :
      Evaluates model locals state left (Value.nat leftValue) →
      Evaluates model locals state right (Value.nat rightValue) →
      (¬ (leftValue = rightValue)) →
      Evaluates model locals state (ScalarExpr.neq left right) (Value.bool true)
  | neqFalse (left right : ScalarExpr) (leftValue rightValue : Nat) :
      Evaluates model locals state left (Value.nat leftValue) →
      Evaluates model locals state right (Value.nat rightValue) →
      leftValue = rightValue →
      Evaluates model locals state (ScalarExpr.neq left right) (Value.bool false)
  | orFalse (left right : ScalarExpr) :
      Evaluates model locals state left (Value.bool false) →
      Evaluates model locals state right (Value.bool false) →
      Evaluates model locals state (ScalarExpr.or left right) (Value.bool false)
  | orLeft (left right : ScalarExpr) (rightValue : Bool) :
      Evaluates model locals state left (Value.bool true) →
      Evaluates model locals state right (Value.bool rightValue) →
      Evaluates model locals state (ScalarExpr.or left right) (Value.bool true)
  | orRight (left right : ScalarExpr) :
      Evaluates model locals state left (Value.bool false) →
      Evaluates model locals state right (Value.bool true) →
      Evaluates model locals state (ScalarExpr.or left right) (Value.bool true)
  | andTrue (left right : ScalarExpr) :
      Evaluates model locals state left (Value.bool true) →
      Evaluates model locals state right (Value.bool true) →
      Evaluates model locals state (ScalarExpr.and left right) (Value.bool true)
  | andLeftFalse (left right : ScalarExpr) (rightValue : Bool) :
      Evaluates model locals state left (Value.bool false) →
      Evaluates model locals state right (Value.bool rightValue) →
      Evaluates model locals state (ScalarExpr.and left right) (Value.bool false)
  | andRightFalse (left right : ScalarExpr) :
      Evaluates model locals state left (Value.bool true) →
      Evaluates model locals state right (Value.bool false) →
      Evaluates model locals state (ScalarExpr.and left right) (Value.bool false)
  | iteTrue (condition thenValue elseValue : ScalarExpr) (value : Value) :
      Evaluates model locals state condition (Value.bool true) →
      Evaluates model locals state thenValue value →
      Evaluates model locals state (ScalarExpr.ite condition thenValue elseValue) value
  | iteFalse (condition thenValue elseValue : ScalarExpr) (value : Value) :
      Evaluates model locals state condition (Value.bool false) →
      Evaluates model locals state elseValue value →
      Evaluates model locals state (ScalarExpr.ite condition thenValue elseValue) value
  | iffTrue (left right : ScalarExpr) (value : Bool) :
      Evaluates model locals state left (Value.bool value) →
      Evaluates model locals state right (Value.bool value) →
      Evaluates model locals state (ScalarExpr.iff left right) (Value.bool true)
  | iffFalseTrue (left right : ScalarExpr) :
      Evaluates model locals state left (Value.bool false) →
      Evaluates model locals state right (Value.bool true) →
      Evaluates model locals state (ScalarExpr.iff left right) (Value.bool false)
  | iffTrueFalse (left right : ScalarExpr) :
      Evaluates model locals state left (Value.bool true) →
      Evaluates model locals state right (Value.bool false) →
      Evaluates model locals state (ScalarExpr.iff left right) (Value.bool false)
  | forallTrue (index : String) (low high body : ScalarExpr)
      (lowValue highValue : Nat) :
      Evaluates model locals state low (Value.nat lowValue) →
      Evaluates model locals state high (Value.nat highValue) →
      (∀ value : Nat, Nat.le lowValue value → Nat.le value highValue →
        Evaluates model ((index, value) :: locals) state body (Value.bool true)) →
      Evaluates model locals state (ScalarExpr.forallIn index low high body) (Value.bool true)
  | forallFalse (index : String) (low high body : ScalarExpr)
      (lowValue highValue witness : Nat) :
      Evaluates model locals state low (Value.nat lowValue) →
      Evaluates model locals state high (Value.nat highValue) →
      Nat.le lowValue witness → Nat.le witness highValue →
      Evaluates model ((index, witness) :: locals) state body (Value.bool false) →
      Evaluates model locals state (ScalarExpr.forallIn index low high body) (Value.bool false)
  | fnAccess (name range : String) (index : ScalarExpr) (value : Nat) :
      FunctionRange model name range →
      Evaluates model locals state index (Value.nat value) →
      FunctionDomain model range value →
      Evaluates model locals state (ScalarExpr.fnAccess name index)
        (Value.bool (state.function name value))
  | except (name range : String) (index value : ScalarExpr)
      (indexValue : Nat) (boolValue : Bool) (result : Nat → Bool) :
      FunctionRange model name range →
      Evaluates model locals state index (Value.nat indexValue) →
      FunctionDomain model range indexValue →
      Evaluates model locals state value (Value.bool boolValue) →
      result indexValue = boolValue →
      (∀ other : Nat, FunctionDomain model range other →
        (¬ (other = indexValue)) →
        result other = state.function name other) →
      (∀ other : Nat, (¬ (FunctionDomain model range other)) →
        result other = false) →
      Evaluates model locals state (ScalarExpr.except name index value)
        (Value.function range result)
  | comprehension (index range : String) (low high body : ScalarExpr)
      (lowValue highValue : Nat) (result : Nat → Bool) :
      low = ScalarExpr.int 1 →
      high = ScalarExpr.constRef range →
      lowValue = 1 →
      ConstantValue model range highValue →
      Evaluates model locals state low (Value.nat lowValue) →
      Evaluates model locals state high (Value.nat highValue) →
      (∀ value : Nat, Nat.le lowValue value → Nat.le value highValue →
        Evaluates model ((index, value) :: locals) state body
          (Value.bool (result value))) →
      (∀ value : Nat, (¬ (Nat.le lowValue value ∧ Nat.le value highValue)) →
        result value = false) →
      Evaluates model locals state
        (ScalarExpr.comprehension index low high body) (Value.function range result)
  | bool (value : Bool) :
      Evaluates model locals state (ScalarExpr.bool value) (Value.bool value)

def CanonicalState (model : Model) (state : State) : Prop :=
  (∀ name : String, (¬ DeclaresScalar model name) → state.scalar name = 0) ∧
  (∀ name : String, ∀ value : Nat, (¬ (DeclaresFunctionAt model name value)) →
    state.function name value = false)

def Initial (model : Model) (state : State) : Prop :=
  CanonicalState model state ∧
  (∀ entry : StateVar, Member entry model.variables →
    state.scalar entry.name = entry.init) ∧
  (∀ entry : FunctionVar, Member entry model.functionVariables →
    ∀ index : Nat, state.function entry.name index = false)

def GuardHolds (model : Model) (state : State) (guard : Guard) : Prop :=
  match guard with
  | Guard.always => True
  | Guard.when expression => Evaluates model [] state expression (Value.bool true)

def NoUpdate (action : Action) (name : String) : Prop :=
  ∀ update : Update, Member update action.updates → ¬ (update.var = name)

def ActionHolds (model : Model) (action : Action) (before after : State) : Prop :=
  GuardHolds model before action.guard ∧
  CanonicalState model after ∧
  (∀ entry : StateVar, Member entry model.variables →
    ((∃ update : Update, Member update action.updates ∧
        update.var = entry.name ∧
        Evaluates model [] before update.value
          (Value.nat (after.scalar entry.name))) ∨
     (NoUpdate action entry.name ∧
        after.scalar entry.name = before.scalar entry.name))) ∧
  (∀ entry : FunctionVar, Member entry model.functionVariables →
    ((∃ update : Update, Member update action.updates ∧
        update.var = entry.name ∧
        Evaluates model [] before update.value
          (Value.function entry.rangeConstant (after.function entry.name))) ∨
     (NoUpdate action entry.name ∧
        after.function entry.name = before.function entry.name)))

def Next (model : Model) (before after : State) : Prop :=
  ∃ action : Action,
    Member action model.actions ∧ ActionHolds model action before after

def StateMachine (model : Model) : _root_.Trust.Temporal.StateMachine State :=
  { init := Initial model, next := Next model }

def InvariantHolds (model : Model) (invariant : Invariant) (state : State) : Prop :=
  Evaluates model [] state invariant.value (Value.bool true)

def SafetyFormula (model : Model) : _root_.Trust.Temporal.Formula State :=
  □ (_root_.Trust.Temporal.Lift (fun state =>
    ∀ invariant : Invariant, Member invariant model.invariants →
      InvariantHolds model invariant state))

def SafetyClaim (model : Model) : Prop :=
  StateMachine model ⊨ SafetyFormula model

def AllInvariantsHold (model : Model) (state : State) : Prop :=
  ∀ invariant : Invariant, Member invariant model.invariants →
    InvariantHolds model invariant state

-- The proposition-level bridge needed by a reachable-set certificate or a
-- stronger authored inductive invariant.  The strengthening need not equal the
-- authored safety predicate: safe unreachable states may have unsafe
-- successors, so authored safety is not necessarily inductive even when the
-- model is safe.  This theorem carries no decision authority; the caller must
-- construct exact initiation, consecution, and safety-preservation judgments
-- for the same model and strengthening.  Stuttering is handled here once.
theorem safetyClaimOfStrengthening
    (model : Model)
    (strengthening : State → Prop)
    (initiation :
      ∀ state : State, Initial model state → strengthening state)
    (consecution :
      ∀ before after : State,
        strengthening before →
        Next model before after →
        strengthening after)
    (preservation :
      ∀ state : State,
        strengthening state →
        AllInvariantsHold model state) :
    SafetyClaim model :=
  fun behavior run index =>
    preservation (behavior index)
      (@Nat.rec
        (fun n => strengthening (behavior n))
        (initiation (behavior 0) run.1)
        (fun n previous =>
          match run.2 n with
          | Or.inl step =>
              consecution (behavior n) (behavior (Nat.succ n)) previous step
          | Or.inr stutter =>
              Eq.mpr
                (congrArg strengthening stutter)
                previous)
        index)

-- Convenience corollary for the narrower case where the authored safety
-- predicate is itself inductive.
theorem safetyClaimOfInductive
    (model : Model)
    (initiation :
      ∀ state : State, Initial model state → AllInvariantsHold model state)
    (consecution :
      ∀ before after : State,
        AllInvariantsHold model before →
        Next model before after →
        AllInvariantsHold model after) :
    SafetyClaim model :=
  safetyClaimOfStrengthening model
    (AllInvariantsHold model)
    initiation
    consecution
    (fun _ holds => holds)

def ScalarModel.stateMachine (model : ScalarModel) :
    _root_.Trust.Temporal.StateMachine State :=
  StateMachine model.asModel

def ScalarModel.safetyClaim (model : ScalarModel) : Prop :=
  SafetyClaim model.asModel

end FiniteModel
end Temporal
end Trust
