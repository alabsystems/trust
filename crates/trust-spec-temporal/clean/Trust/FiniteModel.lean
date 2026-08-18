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
-- names, as in the retired scalar DSL; the consumer rejects missing,
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

-- A reducible all-elements predicate lets generated certificates discharge
-- arbitrary `Member` witnesses without trusting a producer-selected index.
-- `everyMember` consumes the actual inductive membership derivation, while a
-- quoted list reduces `Every` to nested conjunctions in the kernel.
def Every {α : Type} (predicate : α → Prop) (values : List α) : Prop :=
  @List.rec α (fun _ => Prop)
    True
    (fun head _ previous => predicate head ∧ previous)
    values

theorem everyMember {α : Type} (predicate : α → Prop)
    (value : α) (values : List α)
    (every : Every predicate values) (member : Member value values) :
    predicate value :=
  @Member.rec α value
    (fun list _ => Every predicate list → predicate value)
    (fun _ all => all.1)
    (fun _ _ _ previous all => previous all.2)
    values member every

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

-- A first-order inversion view for the owner-ratified scalar macro grammar.
-- Clean's ordinary dependent-pattern elaborator does not yet accept a direct
-- match on Evaluates (the authenticated constructor indices are more
-- general than that surface matcher).  This definition plus the explicit
-- recursor theorem below is the kernel-side replacement: every fact retained
-- by the view is copied from the exact relational derivation, and unsupported
-- expression constructors deliberately reveal only True.
def MacroEvaluationView (model : Model) (locals : List (String × Nat))
    (state : State) (expression : ScalarExpr) (value : Value) : Prop :=
  match expression with
  | ScalarExpr.int literal =>
      value = Value.nat literal
  | ScalarExpr.var name =>
      (DeclaresScalar model name ∧
        value = Value.nat (state.scalar name)) ∨
      (∃ local : Nat,
        LocalValue locals name local ∧ value = Value.nat local) ∨
      (∃ range : String,
        FunctionRange model name range ∧
          value = Value.function range (state.function name))
  | ScalarExpr.constRef name =>
      ∃ constant : Nat,
        ConstantValue model name constant ∧ value = Value.nat constant
  | ScalarExpr.add left right =>
      ∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        value = Value.nat (leftValue + rightValue)
  | ScalarExpr.sub left right =>
      ∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        value = Value.nat (leftValue - rightValue)
  | ScalarExpr.gt left right =>
      (∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        Nat.lt rightValue leftValue ∧ value = Value.bool true) ∨
      (∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        Nat.le leftValue rightValue ∧ value = Value.bool false)
  | ScalarExpr.le left right =>
      (∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        Nat.le leftValue rightValue ∧ value = Value.bool true) ∨
      (∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        Nat.lt rightValue leftValue ∧ value = Value.bool false)
  | ScalarExpr.eq left right =>
      (∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        leftValue = rightValue ∧ value = Value.bool true) ∨
      (∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        (¬ (leftValue = rightValue)) ∧ value = Value.bool false)
  | ScalarExpr.ite condition thenValue elseValue =>
      (Evaluates model locals state condition (Value.bool true) ∧
        Evaluates model locals state thenValue value) ∨
      (Evaluates model locals state condition (Value.bool false) ∧
        Evaluates model locals state elseValue value)
  | _ => True

-- Explicit use of the authenticated recursor avoids assigning any trust to
-- source-level dependent pattern compilation.  This theorem is intentionally
-- proved once in the canonical prelude and is rechecked in every fresh replay
-- environment.
theorem macroEvaluationViewOfEvaluates
    (model : Model) (locals : List (String × Nat)) (state : State)
    (expression : ScalarExpr) (value : Value)
    (evaluation : Evaluates model locals state expression value) :
    MacroEvaluationView model locals state expression value :=
  @Evaluates.rec model
    (fun locals state expression value _ =>
      MacroEvaluationView model locals state expression value)
    (fun _ _ literal => rfl)
    (fun _ _ name declared => Or.inl ⟨declared, rfl⟩)
    (fun _ _ name local found => Or.inr (Or.inl ⟨local, found, rfl⟩))
    (fun _ _ name range found =>
      Or.inr (Or.inr ⟨range, found, rfl⟩))
    (fun _ _ name constant found => ⟨constant, found, rfl⟩)
    (fun _ _ left right leftValue rightValue
        leftProof rightProof _ _ =>
      ⟨leftValue, rightValue, leftProof, rightProof, rfl⟩)
    (fun _ _ left right leftValue rightValue
        leftProof rightProof _ _ =>
      ⟨leftValue, rightValue, leftProof, rightProof, rfl⟩)
    (fun _ _ left right leftValue rightValue
        leftProof rightProof order _ _ =>
      Or.inl ⟨leftValue, rightValue, leftProof, rightProof, order, rfl⟩)
    (fun _ _ left right leftValue rightValue
        leftProof rightProof order _ _ =>
      Or.inr ⟨leftValue, rightValue, leftProof, rightProof, order, rfl⟩)
    (fun _ _ left right leftValue rightValue
        leftProof rightProof order _ _ =>
      Or.inl ⟨leftValue, rightValue, leftProof, rightProof, order, rfl⟩)
    (fun _ _ left right leftValue rightValue
        leftProof rightProof order _ _ =>
      Or.inr ⟨leftValue, rightValue, leftProof, rightProof, order, rfl⟩)
    (fun _ _ left right leftValue rightValue
        leftProof rightProof same _ _ =>
      Or.inl ⟨leftValue, rightValue, leftProof, rightProof, same, rfl⟩)
    (fun _ _ left right leftValue rightValue
        leftProof rightProof different _ _ =>
      Or.inr ⟨leftValue, rightValue, leftProof, rightProof, different, rfl⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ condition thenValue elseValue result
        conditionProof branchProof _ _ =>
      Or.inl ⟨conditionProof, branchProof⟩)
    (fun _ _ condition thenValue elseValue result
        conditionProof branchProof _ _ =>
      Or.inr ⟨conditionProof, branchProof⟩)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
    locals state expression value evaluation

-- A second inversion view covers the function-valued finite ABI.  It is kept
-- separate from `MacroEvaluationView`: the latter is the deliberately narrow
-- compatibility theorem used by the retired scalar grammar, while this view
-- retains exactly the premises needed to construct and compare evaluations of
-- access, EXCEPT, comprehension, bounded forall, and their Boolean glue.
def FunctionEvaluationView (model : Model) (locals : List (String × Nat))
    (state : State) (expression : ScalarExpr) (value : Value) : Prop :=
  match expression with
  | ScalarExpr.int literal => value = Value.nat literal
  | ScalarExpr.var name =>
      (DeclaresScalar model name ∧
        value = Value.nat (state.scalar name)) ∨
      (∃ local : Nat,
        LocalValue locals name local ∧ value = Value.nat local) ∨
      (∃ range : String,
        FunctionRange model name range ∧
          value = Value.function range (state.function name))
  | ScalarExpr.constRef name =>
      ∃ constant : Nat,
        ConstantValue model name constant ∧ value = Value.nat constant
  | ScalarExpr.eq left right =>
      (∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        leftValue = rightValue ∧ value = Value.bool true) ∨
      (∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        (¬ (leftValue = rightValue)) ∧ value = Value.bool false)
  | ScalarExpr.and left right =>
      (Evaluates model locals state left (Value.bool true) ∧
        Evaluates model locals state right (Value.bool true) ∧
        value = Value.bool true) ∨
      (∃ rightValue : Bool,
        Evaluates model locals state left (Value.bool false) ∧
        Evaluates model locals state right (Value.bool rightValue) ∧
        value = Value.bool false) ∨
      (Evaluates model locals state left (Value.bool true) ∧
        Evaluates model locals state right (Value.bool false) ∧
        value = Value.bool false)
  | ScalarExpr.iff left right =>
      (∃ truth : Bool,
        Evaluates model locals state left (Value.bool truth) ∧
        Evaluates model locals state right (Value.bool truth) ∧
        value = Value.bool true) ∨
      (Evaluates model locals state left (Value.bool false) ∧
        Evaluates model locals state right (Value.bool true) ∧
        value = Value.bool false) ∨
      (Evaluates model locals state left (Value.bool true) ∧
        Evaluates model locals state right (Value.bool false) ∧
        value = Value.bool false)
  | ScalarExpr.forallIn index low high body =>
      (∃ lowValue : Nat, ∃ highValue : Nat,
        Evaluates model locals state low (Value.nat lowValue) ∧
        Evaluates model locals state high (Value.nat highValue) ∧
        (∀ candidate : Nat,
          Nat.le lowValue candidate → Nat.le candidate highValue →
          Evaluates model ((index, candidate) :: locals) state body
            (Value.bool true)) ∧
        value = Value.bool true) ∨
      (∃ lowValue : Nat, ∃ highValue : Nat, ∃ witness : Nat,
        Evaluates model locals state low (Value.nat lowValue) ∧
        Evaluates model locals state high (Value.nat highValue) ∧
        Nat.le lowValue witness ∧ Nat.le witness highValue ∧
        Evaluates model ((index, witness) :: locals) state body
          (Value.bool false) ∧
        value = Value.bool false)
  | ScalarExpr.fnAccess name index =>
      ∃ range : String, ∃ indexValue : Nat,
        FunctionRange model name range ∧
        Evaluates model locals state index (Value.nat indexValue) ∧
        FunctionDomain model range indexValue ∧
        value = Value.bool (state.function name indexValue)
  | ScalarExpr.except name index newValue =>
      ∃ range : String, ∃ indexValue : Nat, ∃ boolValue : Bool,
      ∃ result : Nat → Bool,
        FunctionRange model name range ∧
        Evaluates model locals state index (Value.nat indexValue) ∧
        FunctionDomain model range indexValue ∧
        Evaluates model locals state newValue (Value.bool boolValue) ∧
        result indexValue = boolValue ∧
        (∀ other : Nat, FunctionDomain model range other →
          (¬ (other = indexValue)) →
          result other = state.function name other) ∧
        (∀ other : Nat, (¬ (FunctionDomain model range other)) →
          result other = false) ∧
        value = Value.function range result
  | ScalarExpr.comprehension index low high body =>
      ∃ range : String, ∃ lowValue : Nat, ∃ highValue : Nat,
      ∃ result : Nat → Bool,
        low = ScalarExpr.int 1 ∧
        high = ScalarExpr.constRef range ∧
        lowValue = 1 ∧
        ConstantValue model range highValue ∧
        Evaluates model locals state low (Value.nat lowValue) ∧
        Evaluates model locals state high (Value.nat highValue) ∧
        (∀ candidate : Nat,
          Nat.le lowValue candidate → Nat.le candidate highValue →
          Evaluates model ((index, candidate) :: locals) state body
            (Value.bool (result candidate))) ∧
        (∀ candidate : Nat,
          (¬ (Nat.le lowValue candidate ∧ Nat.le candidate highValue)) →
          result candidate = false) ∧
        value = Value.function range result
  | ScalarExpr.bool truth => value = Value.bool truth
  | _ => True

theorem functionEvaluationViewOfEvaluates
    (model : Model) (locals : List (String × Nat)) (state : State)
    (expression : ScalarExpr) (value : Value)
    (evaluation : Evaluates model locals state expression value) :
    FunctionEvaluationView model locals state expression value :=
  @Evaluates.rec model
    (fun locals state expression value _ =>
      FunctionEvaluationView model locals state expression value)
    (fun _ _ literal => rfl)
    (fun _ _ _ declared => Or.inl ⟨declared, rfl⟩)
    (fun _ _ _ local found => Or.inr (Or.inl ⟨local, found, rfl⟩))
    (fun _ _ _ range found => Or.inr (Or.inr ⟨range, found, rfl⟩))
    (fun _ _ _ constant found => ⟨constant, found, rfl⟩)
    (fun _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ leftValue rightValue leftProof rightProof same _ _ =>
      Or.inl ⟨leftValue, rightValue, leftProof, rightProof, same, rfl⟩)
    (fun _ _ _ _ leftValue rightValue leftProof rightProof different _ _ =>
      Or.inr ⟨leftValue, rightValue, leftProof, rightProof, different, rfl⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ leftProof rightProof _ _ =>
      Or.inl ⟨leftProof, rightProof, rfl⟩)
    (fun _ _ _ _ rightValue leftProof rightProof _ _ =>
      Or.inr (Or.inl ⟨rightValue, leftProof, rightProof, rfl⟩))
    (fun _ _ _ _ leftProof rightProof _ _ =>
      Or.inr (Or.inr ⟨leftProof, rightProof, rfl⟩))
    (fun _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ truth leftProof rightProof _ _ =>
      Or.inl ⟨truth, leftProof, rightProof, rfl⟩)
    (fun _ _ _ _ leftProof rightProof _ _ =>
      Or.inr (Or.inl ⟨leftProof, rightProof, rfl⟩))
    (fun _ _ _ _ leftProof rightProof _ _ =>
      Or.inr (Or.inr ⟨leftProof, rightProof, rfl⟩))
    (fun _ _ _ _ _ _ lowValue highValue lowProof highProof bodyProof _ _ _ =>
      Or.inl ⟨lowValue, highValue, lowProof, highProof, bodyProof, rfl⟩)
    (fun _ _ _ _ _ _ lowValue highValue witness
        lowProof highProof lower upper bodyProof _ _ _ =>
      Or.inr ⟨lowValue, highValue, witness, lowProof, highProof,
        lower, upper, bodyProof, rfl⟩)
    (fun _ _ _ range _ indexValue found indexProof domain _ =>
      ⟨range, indexValue, found, indexProof, domain, rfl⟩)
    (fun _ _ _ range _ _ indexValue boolValue result
        found indexProof domain valueProof atIndex others outside _ _ =>
      ⟨range, indexValue, boolValue, result, found, indexProof, domain,
        valueProof, atIndex, others, outside, rfl⟩)
    (fun _ _ _ range low high _ lowValue highValue result
        lowShape highShape lowIsOne found lowProof highProof bodyProof outside _ _ _ =>
      ⟨range, lowValue, highValue, result, lowShape, highShape, lowIsOne,
        found, lowProof, highProof, bodyProof, outside, rfl⟩)
    (fun _ _ _ => rfl)
    locals state expression value evaluation

theorem memberNilFalse {alpha : Type} {value : alpha}
    (member : Member value []) : False :=
  @Member.rec alpha value
    (fun list _ =>
      match list with
      | [] => False
      | _ :: _ => True)
    (fun _ => True.intro)
    (fun _ _ _ _ => True.intro)
    [] member

theorem localValueNilFalse (name : String) (value : Nat)
    (found : LocalValue [] name value) : False :=
  match found with
  | ⟨_, member, _, _⟩ => memberNilFalse member

theorem scalarModelNoFunctionRange (model : ScalarModel)
    (name range : String) (found : FunctionRange model.asModel name range) :
    False :=
  Exists.elim found (fun _ facts => memberNilFalse facts.1)

theorem uniqueConstantValueOfEvery (model : Model)
    (name : String) (value : Nat)
    (allConstants :
      Every
        (fun entry : Constant =>
          entry.name = name → entry.value = value)
        model.constants)
    (other : Nat) (found : ConstantValue model name other) :
    other = value :=
  Exists.elim found (fun entry facts =>
    Eq.trans (Eq.symm facts.2.2)
      ((everyMember
        (fun candidate : Constant =>
          candidate.name = name → candidate.value = value)
        entry model.constants allConstants facts.1) facts.2.1))

theorem uniqueFunctionRangeOfEvery (model : Model)
    (name range : String)
    (allFunctions :
      Every
        (fun entry : FunctionVar =>
          entry.name = name → entry.rangeConstant = range)
        model.functionVariables)
    (other : String) (found : FunctionRange model name other) :
    other = range :=
  Exists.elim found (fun entry facts =>
    Eq.trans (Eq.symm facts.2.2)
      ((everyMember
        (fun candidate : FunctionVar =>
          candidate.name = name → candidate.rangeConstant = range)
        entry model.functionVariables allFunctions facts.1) facts.2.1))

theorem uniqueLocalValueOfEvery (locals : List (String × Nat))
    (name : String) (value : Nat)
    (allLocals :
      Every
        (fun binding : String × Nat =>
          binding.1 = name → binding.2 = value)
        locals)
    (other : Nat) (found : LocalValue locals name other) :
    other = value :=
  Exists.elim found (fun binding facts =>
    Eq.trans (Eq.symm facts.2.2)
      ((everyMember
        (fun candidate : String × Nat =>
          candidate.1 = name → candidate.2 = value)
        binding locals allLocals facts.1) facts.2.1))

theorem noDeclaredScalarOfEvery (model : Model) (name : String)
    (allScalars :
      Every (fun entry : StateVar => ¬ (entry.name = name)) model.variables) :
    ¬ (DeclaresScalar model name) :=
  fun declared =>
    Exists.elim declared (fun entry facts =>
      (everyMember (fun candidate : StateVar => ¬ (candidate.name = name))
        entry model.variables allScalars facts.1) facts.2)

theorem noFunctionRangeOfEvery (model : Model) (name : String)
    (allFunctions :
      Every
        (fun entry : FunctionVar => ¬ (entry.name = name))
        model.functionVariables)
    (range : String) (found : FunctionRange model name range) : False :=
  Exists.elim found (fun entry facts =>
    (everyMember
      (fun candidate : FunctionVar => ¬ (candidate.name = name))
      entry model.functionVariables allFunctions facts.1) facts.2.1)

theorem noLocalValueOfEvery (locals : List (String × Nat))
    (name : String)
    (allLocals :
      Every (fun binding : String × Nat => ¬ (binding.1 = name)) locals)
    (value : Nat) (found : LocalValue locals name value) : False :=
  Exists.elim found (fun binding facts =>
    (everyMember
      (fun candidate : String × Nat => ¬ (candidate.1 = name))
      binding locals allLocals facts.1) facts.2.1)

-- A compositional proof object for the exact macro evaluator.  The forward
-- field constructs the relational semantics; the uniqueness field consumes
-- an arbitrary relational derivation through MacroEvaluationView.  Thus a
-- producer-computed value has no authority unless both fields kernel-check.
structure ExactScalarEvaluation (model : Model) (state : State)
    (expression : ScalarExpr) (value : Value) : Prop where
  derives : Evaluates model [] state expression value
  unique :
    ∀ other : Value,
      Evaluates model [] state expression other → other = value

theorem exactScalarInt (model : Model) (state : State) (literal : Nat) :
    ExactScalarEvaluation model state (ScalarExpr.int literal)
      (Value.nat literal) :=
  { derives := Evaluates.int literal
    unique := fun other evaluation =>
      macroEvaluationViewOfEvaluates model [] state
        (ScalarExpr.int literal) other evaluation }

theorem exactScalarVar (model : Model) (state : State)
    (name : String) (value : Nat)
    (declared : DeclaresScalar model name)
    (coordinate : state.scalar name = value)
    (noFunction :
      ∀ range : String, FunctionRange model name range → False) :
    ExactScalarEvaluation model state (ScalarExpr.var name)
      (Value.nat value) :=
  { derives :=
      Eq.mp
        (congrArg
          (fun output =>
            Evaluates model [] state (ScalarExpr.var name)
              (Value.nat output))
          coordinate)
        (Evaluates.stateVar name declared)
    unique := fun other evaluation =>
      Or.elim
        (macroEvaluationViewOfEvaluates model [] state
          (ScalarExpr.var name) other evaluation)
        (fun scalar =>
          Eq.trans scalar.2 (congrArg Value.nat coordinate))
        (fun localOrFunction =>
          Or.elim localOrFunction
            (fun localCase =>
              Exists.elim localCase (fun local foundAndSame =>
                False.elim
                  (localValueNilFalse name local foundAndSame.1)))
            (fun functionCase =>
              Exists.elim functionCase (fun range foundAndSame =>
                False.elim (noFunction range foundAndSame.1)))) }

theorem exactScalarConst (model : Model) (state : State)
    (name : String) (value : Nat)
    (found : ConstantValue model name value)
    (uniqueConstant :
      ∀ other : Nat, ConstantValue model name other → other = value) :
    ExactScalarEvaluation model state (ScalarExpr.constRef name)
      (Value.nat value) :=
  { derives := Evaluates.constRef name value found
    unique := fun other evaluation =>
      Exists.elim
        (macroEvaluationViewOfEvaluates model [] state
          (ScalarExpr.constRef name) other evaluation)
        (fun otherValue foundAndSame =>
          Eq.trans foundAndSame.2
            (congrArg Value.nat
              (uniqueConstant otherValue foundAndSame.1))) }

def valueNatProjection (value : Value) : Nat :=
  match value with
  | Value.nat number => number
  | _ => 0

theorem exactScalarAdd (model : Model) (state : State)
    (left right : ScalarExpr) (leftValue rightValue : Nat)
    (leftExact :
      ExactScalarEvaluation model state left (Value.nat leftValue))
    (rightExact :
      ExactScalarEvaluation model state right (Value.nat rightValue)) :
    ExactScalarEvaluation model state (ScalarExpr.add left right)
      (Value.nat (leftValue + rightValue)) :=
  { derives :=
      Evaluates.add left right leftValue rightValue
        leftExact.derives rightExact.derives
    unique := by
      intro other evaluation
      have view := macroEvaluationViewOfEvaluates model [] state
        (ScalarExpr.add left right) other evaluation
      rcases view with ⟨actualLeft, actualRight,
        actualLeftProof, actualRightProof, same⟩
      have leftSame : actualLeft = leftValue :=
        congrArg valueNatProjection
          (leftExact.unique (Value.nat actualLeft) actualLeftProof)
      have rightSame : actualRight = rightValue :=
        congrArg valueNatProjection
          (rightExact.unique (Value.nat actualRight) actualRightProof)
      rw [leftSame, rightSame] at same
      exact same }

theorem exactScalarSub (model : Model) (state : State)
    (left right : ScalarExpr) (leftValue rightValue : Nat)
    (leftExact :
      ExactScalarEvaluation model state left (Value.nat leftValue))
    (rightExact :
      ExactScalarEvaluation model state right (Value.nat rightValue)) :
    ExactScalarEvaluation model state (ScalarExpr.sub left right)
      (Value.nat (leftValue - rightValue)) :=
  { derives :=
      Evaluates.sub left right leftValue rightValue
        leftExact.derives rightExact.derives
    unique := by
      intro other evaluation
      have view := macroEvaluationViewOfEvaluates model [] state
        (ScalarExpr.sub left right) other evaluation
      rcases view with ⟨actualLeft, actualRight,
        actualLeftProof, actualRightProof, same⟩
      have leftSame : actualLeft = leftValue :=
        congrArg valueNatProjection
          (leftExact.unique (Value.nat actualLeft) actualLeftProof)
      have rightSame : actualRight = rightValue :=
        congrArg valueNatProjection
          (rightExact.unique (Value.nat actualRight) actualRightProof)
      rw [leftSame, rightSame] at same
      exact same }

def valueBoolProjection (value : Value) : Bool :=
  match value with
  | Value.bool truth => truth
  | _ => false

def valueFunctionProjection (value : Value) : Nat → Bool :=
  match value with
  | Value.function _ contents => contents
  | _ => fun _ => false

def scalarExprNameProjection (expression : ScalarExpr) : String :=
  match expression with
  | ScalarExpr.var name => name
  | ScalarExpr.constRef name => name
  | _ => ""

theorem natLtLeConflict (high low : Nat)
    (strict : Nat.lt low high) (opposite : Nat.le high low) : False :=
  Nat.lt_irrefl high
    (Nat.lt_of_le_of_lt high low high opposite strict)

theorem alignedNatLtLeConflict
    (actualHigh actualLow expectedHigh expectedLow : Nat)
    (sameHigh : actualHigh = expectedHigh)
    (sameLow : actualLow = expectedLow)
    (strict : Nat.lt expectedLow expectedHigh)
    (opposite : Nat.le actualHigh actualLow) : False := by
  rw [sameHigh, sameLow] at opposite
  exact natLtLeConflict expectedHigh expectedLow strict opposite

theorem alignedNatEqNeConflict
    (actualLeft actualRight expectedLeft expectedRight : Nat)
    (sameLeft : actualLeft = expectedLeft)
    (sameRight : actualRight = expectedRight)
    (expectedSame : expectedLeft = expectedRight)
    (actualDifferent : ¬ (actualLeft = actualRight)) : False :=
  actualDifferent
    (Eq.trans sameLeft
      (Eq.trans expectedSame (Eq.symm sameRight)))

theorem alignedNatNeEqConflict
    (actualLeft actualRight expectedLeft expectedRight : Nat)
    (sameLeft : actualLeft = expectedLeft)
    (sameRight : actualRight = expectedRight)
    (expectedDifferent : ¬ (expectedLeft = expectedRight))
    (actualSame : actualLeft = actualRight) : False :=
  expectedDifferent
    (Eq.trans (Eq.symm sameLeft)
      (Eq.trans actualSame sameRight))

theorem exactScalarGtTrue (model : Model) (state : State)
    (left right : ScalarExpr) (leftValue rightValue : Nat)
    (leftExact :
      ExactScalarEvaluation model state left (Value.nat leftValue))
    (rightExact :
      ExactScalarEvaluation model state right (Value.nat rightValue))
    (order : Nat.lt rightValue leftValue) :
    ExactScalarEvaluation model state (ScalarExpr.gt left right)
      (Value.bool true) :=
  { derives := Evaluates.gtTrue left right leftValue rightValue
      leftExact.derives rightExact.derives order
    unique := fun other evaluation =>
      Or.elim
        (macroEvaluationViewOfEvaluates model [] state
          (ScalarExpr.gt left right) other evaluation)
        (fun trueCase =>
          Exists.elim trueCase (fun _ rightCase =>
            Exists.elim rightCase (fun _ facts => facts.2.2.2)))
        (fun falseCase =>
          Exists.elim falseCase (fun actualLeft rightCase =>
            Exists.elim rightCase (fun actualRight facts =>
              False.elim
                (alignedNatLtLeConflict actualLeft actualRight
                  leftValue rightValue
                  (congrArg valueNatProjection
                    (leftExact.unique (Value.nat actualLeft) facts.1))
                  (congrArg valueNatProjection
                    (rightExact.unique (Value.nat actualRight) facts.2.1))
                  order facts.2.2.1)))) }

theorem exactScalarGtFalse (model : Model) (state : State)
    (left right : ScalarExpr) (leftValue rightValue : Nat)
    (leftExact :
      ExactScalarEvaluation model state left (Value.nat leftValue))
    (rightExact :
      ExactScalarEvaluation model state right (Value.nat rightValue))
    (order : Nat.le leftValue rightValue) :
    ExactScalarEvaluation model state (ScalarExpr.gt left right)
      (Value.bool false) :=
  { derives := Evaluates.gtFalse left right leftValue rightValue
      leftExact.derives rightExact.derives order
    unique := fun other evaluation =>
      Or.elim
        (macroEvaluationViewOfEvaluates model [] state
          (ScalarExpr.gt left right) other evaluation)
        (fun trueCase =>
          Exists.elim trueCase (fun actualLeft rightCase =>
            Exists.elim rightCase (fun actualRight facts =>
              False.elim
                (alignedNatLtLeConflict leftValue rightValue
                  actualLeft actualRight
                  (Eq.symm (congrArg valueNatProjection
                    (leftExact.unique (Value.nat actualLeft) facts.1)))
                  (Eq.symm (congrArg valueNatProjection
                    (rightExact.unique (Value.nat actualRight) facts.2.1)))
                  facts.2.2.1 order))))
        (fun falseCase =>
          Exists.elim falseCase (fun _ rightCase =>
            Exists.elim rightCase (fun _ facts => facts.2.2.2))) }

theorem exactScalarLeTrue (model : Model) (state : State)
    (left right : ScalarExpr) (leftValue rightValue : Nat)
    (leftExact :
      ExactScalarEvaluation model state left (Value.nat leftValue))
    (rightExact :
      ExactScalarEvaluation model state right (Value.nat rightValue))
    (order : Nat.le leftValue rightValue) :
    ExactScalarEvaluation model state (ScalarExpr.le left right)
      (Value.bool true) :=
  { derives := Evaluates.leTrue left right leftValue rightValue
      leftExact.derives rightExact.derives order
    unique := fun other evaluation =>
      Or.elim
        (macroEvaluationViewOfEvaluates model [] state
          (ScalarExpr.le left right) other evaluation)
        (fun trueCase =>
          Exists.elim trueCase (fun _ rightCase =>
            Exists.elim rightCase (fun _ facts => facts.2.2.2)))
        (fun falseCase =>
          Exists.elim falseCase (fun actualLeft rightCase =>
            Exists.elim rightCase (fun actualRight facts =>
              False.elim
                (alignedNatLtLeConflict leftValue rightValue
                  actualLeft actualRight
                  (Eq.symm (congrArg valueNatProjection
                    (leftExact.unique (Value.nat actualLeft) facts.1)))
                  (Eq.symm (congrArg valueNatProjection
                    (rightExact.unique (Value.nat actualRight) facts.2.1)))
                  facts.2.2.1 order)))) }

theorem exactScalarLeFalse (model : Model) (state : State)
    (left right : ScalarExpr) (leftValue rightValue : Nat)
    (leftExact :
      ExactScalarEvaluation model state left (Value.nat leftValue))
    (rightExact :
      ExactScalarEvaluation model state right (Value.nat rightValue))
    (order : Nat.lt rightValue leftValue) :
    ExactScalarEvaluation model state (ScalarExpr.le left right)
      (Value.bool false) :=
  { derives := Evaluates.leFalse left right leftValue rightValue
      leftExact.derives rightExact.derives order
    unique := fun other evaluation =>
      Or.elim
        (macroEvaluationViewOfEvaluates model [] state
          (ScalarExpr.le left right) other evaluation)
        (fun trueCase =>
          Exists.elim trueCase (fun actualLeft rightCase =>
            Exists.elim rightCase (fun actualRight facts =>
              False.elim
                (alignedNatLtLeConflict actualLeft actualRight
                  leftValue rightValue
                  (congrArg valueNatProjection
                    (leftExact.unique (Value.nat actualLeft) facts.1))
                  (congrArg valueNatProjection
                    (rightExact.unique (Value.nat actualRight) facts.2.1))
                  order facts.2.2.1))))
        (fun falseCase =>
          Exists.elim falseCase (fun _ rightCase =>
            Exists.elim rightCase (fun _ facts => facts.2.2.2))) }

theorem exactScalarEqTrue (model : Model) (state : State)
    (left right : ScalarExpr) (leftValue rightValue : Nat)
    (leftExact :
      ExactScalarEvaluation model state left (Value.nat leftValue))
    (rightExact :
      ExactScalarEvaluation model state right (Value.nat rightValue))
    (same : leftValue = rightValue) :
    ExactScalarEvaluation model state (ScalarExpr.eq left right)
      (Value.bool true) :=
  { derives := Evaluates.eqTrue left right leftValue rightValue
      leftExact.derives rightExact.derives same
    unique := fun other evaluation =>
      Or.elim
        (macroEvaluationViewOfEvaluates model [] state
          (ScalarExpr.eq left right) other evaluation)
        (fun trueCase =>
          Exists.elim trueCase (fun _ rightCase =>
            Exists.elim rightCase (fun _ facts => facts.2.2.2)))
        (fun falseCase =>
          Exists.elim falseCase (fun actualLeft rightCase =>
            Exists.elim rightCase (fun actualRight facts =>
              False.elim
                (alignedNatEqNeConflict actualLeft actualRight
                  leftValue rightValue
                  (congrArg valueNatProjection
                    (leftExact.unique (Value.nat actualLeft) facts.1))
                  (congrArg valueNatProjection
                    (rightExact.unique (Value.nat actualRight) facts.2.1))
                  same facts.2.2.1)))) }

theorem exactScalarEqFalse (model : Model) (state : State)
    (left right : ScalarExpr) (leftValue rightValue : Nat)
    (leftExact :
      ExactScalarEvaluation model state left (Value.nat leftValue))
    (rightExact :
      ExactScalarEvaluation model state right (Value.nat rightValue))
    (different : ¬ (leftValue = rightValue)) :
    ExactScalarEvaluation model state (ScalarExpr.eq left right)
      (Value.bool false) :=
  { derives := Evaluates.eqFalse left right leftValue rightValue
      leftExact.derives rightExact.derives different
    unique := fun other evaluation =>
      Or.elim
        (macroEvaluationViewOfEvaluates model [] state
          (ScalarExpr.eq left right) other evaluation)
        (fun trueCase =>
          Exists.elim trueCase (fun actualLeft rightCase =>
            Exists.elim rightCase (fun actualRight facts =>
              False.elim
                (alignedNatNeEqConflict actualLeft actualRight
                  leftValue rightValue
                  (congrArg valueNatProjection
                    (leftExact.unique (Value.nat actualLeft) facts.1))
                  (congrArg valueNatProjection
                    (rightExact.unique (Value.nat actualRight) facts.2.1))
                  different facts.2.2.1))))
        (fun falseCase =>
          Exists.elim falseCase (fun _ rightCase =>
            Exists.elim rightCase (fun _ facts => facts.2.2.2))) }

theorem exactScalarIteTrue (model : Model) (state : State)
    (condition thenValue elseValue : ScalarExpr) (value : Value)
    (conditionExact :
      ExactScalarEvaluation model state condition (Value.bool true))
    (branchExact :
      ExactScalarEvaluation model state thenValue value) :
    ExactScalarEvaluation model state
      (ScalarExpr.ite condition thenValue elseValue) value :=
  { derives := Evaluates.iteTrue condition thenValue elseValue value
      conditionExact.derives branchExact.derives
    unique := fun other evaluation =>
      Or.elim
        (macroEvaluationViewOfEvaluates model [] state
          (ScalarExpr.ite condition thenValue elseValue) other evaluation)
        (fun trueCase => branchExact.unique other trueCase.2)
        (fun falseCase =>
          False.elim
            (Bool.noConfusion
              (congrArg valueBoolProjection
                (conditionExact.unique (Value.bool false) falseCase.1)))) }

theorem exactScalarIteFalse (model : Model) (state : State)
    (condition thenValue elseValue : ScalarExpr) (value : Value)
    (conditionExact :
      ExactScalarEvaluation model state condition (Value.bool false))
    (branchExact :
      ExactScalarEvaluation model state elseValue value) :
    ExactScalarEvaluation model state
      (ScalarExpr.ite condition thenValue elseValue) value :=
  { derives := Evaluates.iteFalse condition thenValue elseValue value
      conditionExact.derives branchExact.derives
    unique := fun other evaluation =>
      Or.elim
        (macroEvaluationViewOfEvaluates model [] state
          (ScalarExpr.ite condition thenValue elseValue) other evaluation)
        (fun trueCase =>
          False.elim
            (Bool.noConfusion
              (congrArg valueBoolProjection
                (conditionExact.unique (Value.bool true) trueCase.1))))
        (fun falseCase => branchExact.unique other falseCase.2) }

theorem falseOfExactFalseEvaluatesTrue
    (model : Model) (state : State) (expression : ScalarExpr)
    (exact :
      ExactScalarEvaluation model state expression (Value.bool false))
    (evaluatesTrue :
      Evaluates model [] state expression (Value.bool true)) : False :=
  Bool.noConfusion
    (congrArg valueBoolProjection
      (exact.unique (Value.bool true) evaluatesTrue))

-- Exact evaluation for the full finite ABI.  The local environment is
-- explicit because bounded forall and comprehension evaluate their body under
-- a freshly bound index.  As in the scalar reflector, a generated value has no
-- authority unless the forward derivation and the uniqueness consumer both
-- kernel-check.
structure ExactFunctionEvaluation (model : Model)
    (locals : List (String × Nat)) (state : State)
    (expression : ScalarExpr) (value : Value) : Prop where
  derives : Evaluates model locals state expression value
  unique :
    ∀ other : Value,
      Evaluates model locals state expression other → other = value

theorem exactFunctionInt (model : Model)
    (locals : List (String × Nat)) (state : State) (literal : Nat) :
    ExactFunctionEvaluation model locals state (ScalarExpr.int literal)
      (Value.nat literal) :=
  { derives := Evaluates.int literal
    unique := fun other evaluation =>
      functionEvaluationViewOfEvaluates model locals state
        (ScalarExpr.int literal) other evaluation }

theorem exactFunctionBool (model : Model)
    (locals : List (String × Nat)) (state : State) (truth : Bool) :
    ExactFunctionEvaluation model locals state (ScalarExpr.bool truth)
      (Value.bool truth) :=
  { derives := Evaluates.bool truth
    unique := fun other evaluation =>
      functionEvaluationViewOfEvaluates model locals state
        (ScalarExpr.bool truth) other evaluation }

theorem exactFunctionLocalVar (model : Model)
    (locals : List (String × Nat)) (state : State)
    (name : String) (value : Nat)
    (found : LocalValue locals name value)
    (uniqueLocal :
      ∀ other : Nat, LocalValue locals name other → other = value)
    (noScalar : ¬ DeclaresScalar model name)
    (noFunction :
      ∀ range : String, FunctionRange model name range → False) :
    ExactFunctionEvaluation model locals state (ScalarExpr.var name)
      (Value.nat value) :=
  { derives := Evaluates.localVar name value found
    unique := fun other evaluation =>
      Or.elim
        (functionEvaluationViewOfEvaluates model locals state
          (ScalarExpr.var name) other evaluation)
        (fun scalar => False.elim (noScalar scalar.1))
        (fun localOrFunction =>
          Or.elim localOrFunction
            (fun localCase =>
              Exists.elim localCase (fun actual foundAndSame =>
                Eq.trans foundAndSame.2
                  (congrArg Value.nat
                    (uniqueLocal actual foundAndSame.1))))
            (fun functionCase =>
              Exists.elim functionCase (fun actualRange foundAndSame =>
                False.elim
                  (noFunction actualRange foundAndSame.1)))) }

theorem exactFunctionVar (model : Model)
    (locals : List (String × Nat)) (state : State)
    (name range : String)
    (found : FunctionRange model name range)
    (uniqueRange :
      ∀ other : String, FunctionRange model name other → other = range)
    (noScalar : ¬ DeclaresScalar model name)
    (noLocal : ∀ value : Nat, LocalValue locals name value → False) :
    ExactFunctionEvaluation model locals state (ScalarExpr.var name)
      (Value.function range (state.function name)) :=
  { derives := Evaluates.functionVar name range found
    unique := fun other evaluation =>
      Or.elim
        (functionEvaluationViewOfEvaluates model locals state
          (ScalarExpr.var name) other evaluation)
        (fun scalar => False.elim (noScalar scalar.1))
        (fun localOrFunction =>
          Or.elim localOrFunction
            (fun localCase =>
              Exists.elim localCase (fun actual foundAndSame =>
                False.elim (noLocal actual foundAndSame.1)))
            (fun functionCase =>
              Exists.elim functionCase (fun actualRange foundAndSame =>
                Eq.trans foundAndSame.2
                  (congrArg
                    (fun selected : String =>
                      Value.function selected (state.function name))
                    (uniqueRange actualRange foundAndSame.1))))) }

theorem exactFunctionVarValue (model : Model)
    (locals : List (String × Nat)) (state : State)
    (name range : String) (contents : Nat → Bool)
    (found : FunctionRange model name range)
    (uniqueRange :
      ∀ other : String, FunctionRange model name other → other = range)
    (noScalar : ¬ DeclaresScalar model name)
    (noLocal : ∀ value : Nat, LocalValue locals name value → False)
    (coordinate : state.function name = contents) :
    ExactFunctionEvaluation model locals state (ScalarExpr.var name)
      (Value.function range contents) :=
  { derives :=
      Eq.mp
        (congrArg
          (fun selected : Nat → Bool =>
            Evaluates model locals state (ScalarExpr.var name)
              (Value.function range selected))
          coordinate)
        (Evaluates.functionVar name range found)
    unique := fun other evaluation =>
      Eq.trans
        ((exactFunctionVar model locals state name range found uniqueRange
          noScalar noLocal).unique other evaluation)
        (congrArg (fun selected : Nat → Bool => Value.function range selected)
          coordinate) }

theorem exactFunctionConst (model : Model)
    (locals : List (String × Nat)) (state : State)
    (name : String) (value : Nat)
    (found : ConstantValue model name value)
    (uniqueConstant :
      ∀ other : Nat, ConstantValue model name other → other = value) :
    ExactFunctionEvaluation model locals state (ScalarExpr.constRef name)
      (Value.nat value) :=
  { derives := Evaluates.constRef name value found
    unique := by
      intro other evaluation
      have view := functionEvaluationViewOfEvaluates model locals state
        (ScalarExpr.constRef name) other evaluation
      rcases view with ⟨actual, actualFound, same⟩
      exact Eq.trans same
        (congrArg Value.nat (uniqueConstant actual actualFound)) }

theorem exactFunctionEqTrue (model : Model)
    (locals : List (String × Nat)) (state : State)
    (left right : ScalarExpr) (leftValue rightValue : Nat)
    (leftExact :
      ExactFunctionEvaluation model locals state left (Value.nat leftValue))
    (rightExact :
      ExactFunctionEvaluation model locals state right (Value.nat rightValue))
    (same : leftValue = rightValue) :
    ExactFunctionEvaluation model locals state (ScalarExpr.eq left right)
      (Value.bool true) :=
  { derives := Evaluates.eqTrue left right leftValue rightValue
      leftExact.derives rightExact.derives same
    unique := by
      intro other evaluation
      have view := functionEvaluationViewOfEvaluates model locals state
        (ScalarExpr.eq left right) other evaluation
      rcases view with trueCase | falseCase
      · rcases trueCase with ⟨_, _, _, _, _, output⟩
        exact output
      · rcases falseCase with
          ⟨actualLeft, actualRight, actualLeftProof, actualRightProof,
            different, _⟩
        exact False.elim
          (alignedNatEqNeConflict actualLeft actualRight leftValue rightValue
            (congrArg valueNatProjection
              (leftExact.unique (Value.nat actualLeft) actualLeftProof))
            (congrArg valueNatProjection
              (rightExact.unique (Value.nat actualRight) actualRightProof))
            same different) }

theorem exactFunctionAndTrue (model : Model)
    (locals : List (String × Nat)) (state : State)
    (left right : ScalarExpr)
    (leftExact :
      ExactFunctionEvaluation model locals state left (Value.bool true))
    (rightExact :
      ExactFunctionEvaluation model locals state right (Value.bool true)) :
    ExactFunctionEvaluation model locals state (ScalarExpr.and left right)
      (Value.bool true) :=
  { derives := Evaluates.andTrue left right leftExact.derives rightExact.derives
    unique := fun other evaluation =>
      Or.elim
        (functionEvaluationViewOfEvaluates model locals state
          (ScalarExpr.and left right) other evaluation)
        (fun trueCase => trueCase.2.2)
        (fun falseCases =>
          Or.elim falseCases
            (fun leftFalse =>
              Exists.elim leftFalse (fun _ facts =>
                False.elim
                  (Bool.noConfusion
                    (congrArg valueBoolProjection
                      (leftExact.unique (Value.bool false) facts.1)))))
            (fun rightFalse =>
              False.elim
                (Bool.noConfusion
                  (congrArg valueBoolProjection
                    (rightExact.unique
                      (Value.bool false) rightFalse.2.1))))) }

theorem exactFunctionIffFalseFalse (model : Model)
    (locals : List (String × Nat)) (state : State)
    (left right : ScalarExpr)
    (leftExact :
      ExactFunctionEvaluation model locals state left (Value.bool false))
    (rightExact :
      ExactFunctionEvaluation model locals state right (Value.bool false)) :
    ExactFunctionEvaluation model locals state (ScalarExpr.iff left right)
      (Value.bool true) :=
  { derives := Evaluates.iffTrue left right false
      leftExact.derives rightExact.derives
    unique := fun other evaluation =>
      Or.elim
        (functionEvaluationViewOfEvaluates model locals state
          (ScalarExpr.iff left right) other evaluation)
        (fun trueCase =>
          Exists.elim trueCase (fun _ facts => facts.2.2))
        (fun falseCases =>
          Or.elim falseCases
            (fun leftFalse =>
              False.elim
                (Bool.noConfusion
                  (congrArg valueBoolProjection
                    (rightExact.unique (Value.bool true) leftFalse.2.1))))
            (fun rightFalse =>
              False.elim
                (Bool.noConfusion
                  (congrArg valueBoolProjection
                    (leftExact.unique (Value.bool true) rightFalse.1))))) }

theorem exactFunctionAccess (model : Model)
    (locals : List (String × Nat)) (state : State)
    (name range : String) (index : ScalarExpr) (indexValue : Nat)
    (found : FunctionRange model name range)
    (indexExact :
      ExactFunctionEvaluation model locals state index (Value.nat indexValue))
    (domain : FunctionDomain model range indexValue) :
    ExactFunctionEvaluation model locals state (ScalarExpr.fnAccess name index)
      (Value.bool (state.function name indexValue)) :=
  { derives := Evaluates.fnAccess name range index indexValue
      found indexExact.derives domain
    unique := by
      intro other evaluation
      have view := functionEvaluationViewOfEvaluates model locals state
        (ScalarExpr.fnAccess name index) other evaluation
      rcases view with ⟨_, actualIndex, _, actualIndexProof, _, output⟩
      have indexSame : actualIndex = indexValue :=
        congrArg valueNatProjection
          (indexExact.unique (Value.nat actualIndex) actualIndexProof)
      exact Eq.trans output
        (congrArg
          (fun selected : Nat => Value.bool (state.function name selected))
          indexSame) }

theorem exactFunctionAccessValue (model : Model)
    (locals : List (String × Nat)) (state : State)
    (name range : String) (index : ScalarExpr) (indexValue : Nat)
    (truth : Bool)
    (found : FunctionRange model name range)
    (indexExact :
      ExactFunctionEvaluation model locals state index (Value.nat indexValue))
    (domain : FunctionDomain model range indexValue)
    (coordinate : state.function name indexValue = truth) :
    ExactFunctionEvaluation model locals state (ScalarExpr.fnAccess name index)
      (Value.bool truth) :=
  { derives :=
      Eq.mp
        (congrArg
          (fun selected : Bool =>
            Evaluates model locals state (ScalarExpr.fnAccess name index)
              (Value.bool selected))
          coordinate)
        (Evaluates.fnAccess name range index indexValue
          found indexExact.derives domain)
    unique := fun other evaluation =>
      Eq.trans
        ((exactFunctionAccess model locals state name range index indexValue
          found indexExact domain).unique other evaluation)
        (congrArg Value.bool coordinate) }

theorem natLeLeftTransport (actual expected witness : Nat)
    (same : actual = expected) (lower : Nat.le actual witness) :
    Nat.le expected witness :=
  Eq.mp
    (congrArg (fun selected : Nat => Nat.le selected witness) same)
    lower

theorem natLeRightTransport (actual expected witness : Nat)
    (same : actual = expected) (upper : Nat.le witness actual) :
    Nat.le witness expected :=
  Eq.mp
    (congrArg (fun selected : Nat => Nat.le witness selected) same)
    upper

theorem exactFunctionForallTrue (model : Model)
    (locals : List (String × Nat)) (state : State)
    (index : String) (low high body : ScalarExpr)
    (lowValue highValue : Nat)
    (lowExact :
      ExactFunctionEvaluation model locals state low (Value.nat lowValue))
    (highExact :
      ExactFunctionEvaluation model locals state high (Value.nat highValue))
    (bodyExact :
      ∀ candidate : Nat,
        Nat.le lowValue candidate → Nat.le candidate highValue →
        ExactFunctionEvaluation model ((index, candidate) :: locals) state body
          (Value.bool true)) :
    ExactFunctionEvaluation model locals state
      (ScalarExpr.forallIn index low high body) (Value.bool true) :=
  { derives := Evaluates.forallTrue index low high body lowValue highValue
      lowExact.derives highExact.derives
      (fun candidate lower upper => (bodyExact candidate lower upper).derives)
    unique := fun other evaluation =>
      Or.elim
        (functionEvaluationViewOfEvaluates model locals state
          (ScalarExpr.forallIn index low high body) other evaluation)
        (fun trueCase =>
          Exists.elim trueCase (fun _ highCase =>
            Exists.elim highCase (fun _ facts => facts.2.2.2)))
        (fun falseCase =>
          Exists.elim falseCase (fun actualLow highCase =>
            Exists.elim highCase (fun actualHigh witnessCase =>
              Exists.elim witnessCase (fun witness facts =>
                False.elim
                  (Bool.noConfusion
                    (congrArg valueBoolProjection
                      ((bodyExact witness
                        (natLeLeftTransport actualLow lowValue witness
                          (congrArg valueNatProjection
                            (lowExact.unique
                              (Value.nat actualLow) facts.1))
                          facts.2.2.1)
                        (natLeRightTransport actualHigh highValue witness
                          (congrArg valueNatProjection
                            (highExact.unique
                              (Value.nat actualHigh) facts.2.1))
                          facts.2.2.2.1)).unique
                        (Value.bool false) facts.2.2.2.2.1))))))) }

theorem exceptResultsSame (model : Model) (state : State)
    (name range : String) (indexValue : Nat) (boolValue : Bool)
    (actualResult result : Nat → Bool)
    (actualAtIndex : actualResult indexValue = boolValue)
    (atIndex : result indexValue = boolValue)
    (actualOthers :
      ∀ other : Nat, FunctionDomain model range other →
        (¬ (other = indexValue)) →
        actualResult other = state.function name other)
    (others :
      ∀ other : Nat, FunctionDomain model range other →
        (¬ (other = indexValue)) →
        result other = state.function name other)
    (actualOutside :
      ∀ other : Nat, (¬ (FunctionDomain model range other)) →
        actualResult other = false)
    (outside :
      ∀ other : Nat, (¬ (FunctionDomain model range other)) →
        result other = false)
    (classify :
      ∀ candidate : Nat,
        candidate = indexValue ∨
        (FunctionDomain model range candidate ∧
          (¬ (candidate = indexValue))) ∨
        (¬ (FunctionDomain model range candidate))) :
    actualResult = result := by
  funext candidate
  exact Or.elim (classify candidate)
    (fun sameIndex =>
      Eq.trans (congrArg actualResult sameIndex)
        (Eq.trans actualAtIndex
          (Eq.trans (Eq.symm atIndex)
            (congrArg result (Eq.symm sameIndex)))))
    (fun remaining =>
      Or.elim remaining
        (fun inside =>
          Eq.trans
            (actualOthers candidate inside.1 inside.2)
            (Eq.symm (others candidate inside.1 inside.2)))
        (fun beyond =>
          Eq.trans
            (actualOutside candidate beyond)
            (Eq.symm (outside candidate beyond))))

theorem comprehensionResultsSame (model : Model)
    (locals : List (String × Nat)) (state : State)
    (index : String) (body : ScalarExpr)
    (lowValue highValue : Nat) (actualResult result : Nat → Bool)
    (bodyExact :
      ∀ candidate : Nat,
        Nat.le lowValue candidate → Nat.le candidate highValue →
        ExactFunctionEvaluation model ((index, candidate) :: locals) state body
          (Value.bool (result candidate)))
    (actualBody :
      ∀ candidate : Nat,
        Nat.le lowValue candidate → Nat.le candidate highValue →
        Evaluates model ((index, candidate) :: locals) state body
          (Value.bool (actualResult candidate)))
    (actualOutside :
      ∀ candidate : Nat,
        (¬ (Nat.le lowValue candidate ∧ Nat.le candidate highValue)) →
        actualResult candidate = false)
    (outside :
      ∀ candidate : Nat,
        (¬ (Nat.le lowValue candidate ∧ Nat.le candidate highValue)) →
        result candidate = false)
    (classify :
      ∀ candidate : Nat,
        (Nat.le lowValue candidate ∧ Nat.le candidate highValue) ∨
        (¬ (Nat.le lowValue candidate ∧ Nat.le candidate highValue))) :
    actualResult = result := by
  funext candidate
  exact Or.elim (classify candidate)
    (fun inside =>
      congrArg valueBoolProjection
        ((bodyExact candidate inside.1 inside.2).unique
          (Value.bool (actualResult candidate))
          (actualBody candidate inside.1 inside.2)))
    (fun beyond =>
      Eq.trans
        (actualOutside candidate beyond)
        (Eq.symm (outside candidate beyond)))

theorem natIntervalClassify (low high candidate : Nat) :
    (Nat.le low candidate ∧ Nat.le candidate high) ∨
    (¬ (Nat.le low candidate ∧ Nat.le candidate high)) :=
  match Nat.decLe low candidate with
  | Decidable.isTrue lower =>
      match Nat.decLe candidate high with
      | Decidable.isTrue upper => Or.inl ⟨lower, upper⟩
      | Decidable.isFalse notUpper =>
          Or.inr (fun inside => notUpper inside.2)
  | Decidable.isFalse notLower =>
      Or.inr (fun inside => notLower inside.1)

theorem functionDomainClassify (model : Model) (range : String)
    (high index candidate : Nat)
    (found : ConstantValue model range high)
    (uniqueConstant :
      ∀ other : Nat, ConstantValue model range other → other = high) :
    candidate = index ∨
    (FunctionDomain model range candidate ∧ (¬ (candidate = index))) ∨
    (¬ (FunctionDomain model range candidate)) :=
  match Nat.decEq candidate index with
  | Decidable.isTrue same => Or.inl same
  | Decidable.isFalse different =>
      match Nat.decLe 1 candidate with
      | Decidable.isTrue lower =>
          match Nat.decLe candidate high with
          | Decidable.isTrue upper =>
              Or.inr (Or.inl ⟨⟨high, found, lower, upper⟩, different⟩)
          | Decidable.isFalse notUpper =>
              Or.inr (Or.inr (fun domain =>
                Exists.elim domain (fun actual facts =>
                  notUpper
                    (Eq.mp
                      (congrArg (fun bound : Nat => Nat.le candidate bound)
                        (uniqueConstant actual facts.1))
                      facts.2.2))))
      | Decidable.isFalse notLower =>
          Or.inr (Or.inr (fun domain =>
            Exists.elim domain (fun _ facts => notLower facts.2.1)))

theorem exactFunctionExcept (model : Model)
    (locals : List (String × Nat)) (state : State)
    (name range : String) (index newValue : ScalarExpr)
    (indexValue : Nat) (boolValue : Bool) (result : Nat → Bool)
    (found : FunctionRange model name range)
    (uniqueRange :
      ∀ other : String, FunctionRange model name other → other = range)
    (indexExact :
      ExactFunctionEvaluation model locals state index (Value.nat indexValue))
    (domain : FunctionDomain model range indexValue)
    (valueExact :
      ExactFunctionEvaluation model locals state newValue (Value.bool boolValue))
    (atIndex : result indexValue = boolValue)
    (others :
      ∀ other : Nat, FunctionDomain model range other →
        (¬ (other = indexValue)) →
        result other = state.function name other)
    (outside :
      ∀ other : Nat, (¬ (FunctionDomain model range other)) →
        result other = false)
    (classify :
      ∀ candidate : Nat,
        candidate = indexValue ∨
        (FunctionDomain model range candidate ∧
          (¬ (candidate = indexValue))) ∨
        (¬ (FunctionDomain model range candidate))) :
    ExactFunctionEvaluation model locals state
      (ScalarExpr.except name index newValue) (Value.function range result) :=
  { derives := Evaluates.except name range index newValue indexValue boolValue result
      found indexExact.derives domain valueExact.derives atIndex others outside
    unique := by
      intro other evaluation
      have view := functionEvaluationViewOfEvaluates model locals state
        (ScalarExpr.except name index newValue) other evaluation
      rcases view with
        ⟨actualRange, actualIndex, actualBool, actualResult,
          actualFound, actualIndexProof, actualDomain, actualValueProof,
          actualAtIndex, actualOthers, actualOutside, output⟩
      have rangeSame : actualRange = range :=
        uniqueRange actualRange actualFound
      have indexSame : actualIndex = indexValue :=
        congrArg valueNatProjection
          (indexExact.unique (Value.nat actualIndex) actualIndexProof)
      have boolSame : actualBool = boolValue :=
        congrArg valueBoolProjection
          (valueExact.unique (Value.bool actualBool) actualValueProof)
      rw [rangeSame, indexSame] at actualDomain actualOthers
      rw [rangeSame] at actualOutside output
      rw [indexSame, boolSame] at actualAtIndex
      exact Eq.trans output
        (congrArg (fun contents : Nat → Bool => Value.function range contents)
          (exceptResultsSame model state name range indexValue boolValue
            actualResult result actualAtIndex atIndex actualOthers others
            actualOutside outside classify)) }

theorem exactFunctionComprehension (model : Model)
    (locals : List (String × Nat)) (state : State)
    (index range : String) (low high body : ScalarExpr)
    (lowValue highValue : Nat) (result : Nat → Bool)
    (lowShape : low = ScalarExpr.int 1)
    (highShape : high = ScalarExpr.constRef range)
    (lowIsOne : lowValue = 1)
    (found : ConstantValue model range highValue)
    (lowExact :
      ExactFunctionEvaluation model locals state low (Value.nat lowValue))
    (highExact :
      ExactFunctionEvaluation model locals state high (Value.nat highValue))
    (bodyExact :
      ∀ candidate : Nat,
        Nat.le lowValue candidate → Nat.le candidate highValue →
        ExactFunctionEvaluation model ((index, candidate) :: locals) state body
          (Value.bool (result candidate)))
    (outside :
      ∀ candidate : Nat,
        (¬ (Nat.le lowValue candidate ∧ Nat.le candidate highValue)) →
        result candidate = false)
    (classify :
      ∀ candidate : Nat,
        (Nat.le lowValue candidate ∧ Nat.le candidate highValue) ∨
        (¬ (Nat.le lowValue candidate ∧ Nat.le candidate highValue))) :
    ExactFunctionEvaluation model locals state
      (ScalarExpr.comprehension index low high body)
      (Value.function range result) :=
  { derives := Evaluates.comprehension index range low high body
      lowValue highValue result lowShape highShape lowIsOne found
      lowExact.derives highExact.derives
      (fun candidate lower upper =>
        (bodyExact candidate lower upper).derives)
      outside
    unique := by
      intro other evaluation
      have view := functionEvaluationViewOfEvaluates model locals state
        (ScalarExpr.comprehension index low high body) other evaluation
      rcases view with
        ⟨actualRange, actualLow, actualHigh, actualResult,
          actualLowShape, actualHighShape, actualLowIsOne, actualFound,
          actualLowProof, actualHighProof, actualBody, actualOutside, output⟩
      have rangeSame : actualRange = range :=
        congrArg scalarExprNameProjection
          (Eq.trans (Eq.symm actualHighShape) highShape)
      have lowSame : actualLow = lowValue :=
        congrArg valueNatProjection
          (lowExact.unique (Value.nat actualLow) actualLowProof)
      have highSame : actualHigh = highValue :=
        congrArg valueNatProjection
          (highExact.unique (Value.nat actualHigh) actualHighProof)
      rw [rangeSame] at actualFound output
      rw [lowSame, highSame] at actualBody actualOutside
      exact Eq.trans output
        (congrArg (fun contents : Nat → Bool => Value.function range contents)
          (comprehensionResultsSame model locals state index body
            lowValue highValue actualResult result bodyExact actualBody
            actualOutside outside classify)) }

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

-- Project an initial scalar coordinate through the exact quoted entry.  The
-- explicit name/init equalities normalize the result to the user's scalar
-- projection, rather than leaving a reducible `StateVar` projection that a
-- generated rewrite tactic would have to guess how to unfold.
theorem scalarCoordinateOfInitial
    (model : Model) (state : State) (entry : StateVar)
    (name : String) (expected : Nat)
    (entryMember : Member entry model.variables)
    (entryName : entry.name = name) (entryInit : entry.init = expected)
    (initial : Initial model state) :
    state.scalar name = expected :=
  Eq.trans
    (congrArg state.scalar (Eq.symm entryName))
    (Eq.trans (initial.2.1 entry entryMember) entryInit)

theorem scalarLowerBoundOfInitial
    (model : Model) (state : State) (entry : StateVar)
    (name : String) (expected bound : Nat)
    (entryMember : Member entry model.variables)
    (entryName : entry.name = name) (entryInit : entry.init = expected)
    (lower : Nat.le bound expected)
    (initial : Initial model state) :
    Nat.le bound (state.scalar name) :=
  Eq.mpr
    (congrArg
      (fun value : Nat => Nat.le bound value)
      (scalarCoordinateOfInitial model state entry name expected
        entryMember entryName entryInit initial))
    lower

theorem functionsEqualOfPointwise
    (left right : Nat → Bool)
    (same : ∀ index : Nat, left index = right index) : left = right := by
  funext index
  exact same index

theorem functionCoordinateOfInitial
    (model : Model) (state : State) (entry : FunctionVar)
    (expected : Nat → Bool)
    (entryMember : Member entry model.functionVariables)
    (expectedFalse : ∀ index : Nat, expected index = false)
    (initial : Initial model state) :
    state.function entry.name = expected :=
  functionsEqualOfPointwise (state.function entry.name) expected
    (fun index =>
      Eq.trans (initial.2.2 entry entryMember index)
        (Eq.symm (expectedFalse index)))

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

-- Generated finite certificates classify the actual update-membership proof
-- with `Every`; a producer-supplied update index has no authority.  The two
-- helpers below then project the exact post-coordinate from ActionHolds for an
-- updated or an omitted scalar variable respectively.
theorem scalarCoordinateOfUpdatedAction
    (model : Model) (action : Action) (before after : State)
    (entry : StateVar) (expected : Nat)
    (entryMember : Member entry model.variables)
    (allUpdates :
      Every
        (fun update : Update =>
          update.var = entry.name →
          Evaluates model [] before update.value
            (Value.nat (after.scalar entry.name)) →
          after.scalar entry.name = expected)
        action.updates)
    (hasMatching :
      ∃ update : Update,
        Member update action.updates ∧ update.var = entry.name)
    (holds : ActionHolds model action before after) :
    after.scalar entry.name = expected :=
  Or.elim (holds.2.2.1 entry entryMember)
    (fun updated =>
      Exists.elim updated (fun update facts =>
        everyMember
          (fun candidate : Update =>
            candidate.var = entry.name →
            Evaluates model [] before candidate.value
              (Value.nat (after.scalar entry.name)) →
            after.scalar entry.name = expected)
          update action.updates allUpdates facts.1 facts.2.1 facts.2.2))
    (fun unchanged =>
      Exists.elim hasMatching (fun update facts =>
        False.elim (unchanged.1 update facts.1 facts.2)))

theorem namedScalarCoordinateOfUpdatedAction
    (model : Model) (action : Action) (before after : State)
    (entry : StateVar) (name : String) (expected : Nat)
    (entryMember : Member entry model.variables)
    (entryName : entry.name = name)
    (allUpdates :
      Every
        (fun update : Update =>
          update.var = entry.name →
          Evaluates model [] before update.value
            (Value.nat (after.scalar entry.name)) →
          after.scalar entry.name = expected)
        action.updates)
    (hasMatching :
      ∃ update : Update,
        Member update action.updates ∧ update.var = entry.name)
    (holds : ActionHolds model action before after) :
    after.scalar name = expected :=
  Eq.trans
    (congrArg after.scalar (Eq.symm entryName))
    (scalarCoordinateOfUpdatedAction model action before after entry expected
      entryMember allUpdates hasMatching holds)

theorem scalarCoordinateOfUnchangedAction
    (model : Model) (action : Action) (before after : State)
    (entry : StateVar) (expected : Nat)
    (entryMember : Member entry model.variables)
    (beforeCoordinate : before.scalar entry.name = expected)
    (noMatching :
      Every (fun update : Update => ¬ (update.var = entry.name))
        action.updates)
    (holds : ActionHolds model action before after) :
    after.scalar entry.name = expected :=
  Or.elim (holds.2.2.1 entry entryMember)
    (fun updated =>
      Exists.elim updated (fun update facts =>
        False.elim
          ((everyMember
            (fun candidate : Update => ¬ (candidate.var = entry.name))
            update action.updates noMatching facts.1) facts.2.1)))
    (fun unchanged => Eq.trans unchanged.2 beforeCoordinate)

theorem functionCoordinateOfUpdatedAction
    (model : Model) (action : Action) (before after : State)
    (entry : FunctionVar) (expected : Nat → Bool)
    (entryMember : Member entry model.functionVariables)
    (allUpdates :
      Every
        (fun update : Update =>
          update.var = entry.name →
          Evaluates model [] before update.value
            (Value.function entry.rangeConstant (after.function entry.name)) →
          after.function entry.name = expected)
        action.updates)
    (hasMatching :
      ∃ update : Update,
        Member update action.updates ∧ update.var = entry.name)
    (holds : ActionHolds model action before after) :
    after.function entry.name = expected :=
  Or.elim (holds.2.2.2 entry entryMember)
    (fun updated =>
      Exists.elim updated (fun update facts =>
        everyMember
          (fun candidate : Update =>
            candidate.var = entry.name →
            Evaluates model [] before candidate.value
              (Value.function entry.rangeConstant
                (after.function entry.name)) →
            after.function entry.name = expected)
          update action.updates allUpdates facts.1 facts.2.1 facts.2.2))
    (fun unchanged =>
      Exists.elim hasMatching (fun update facts =>
        False.elim (unchanged.1 update facts.1 facts.2)))

theorem functionCoordinateOfUnchangedAction
    (model : Model) (action : Action) (before after : State)
    (entry : FunctionVar) (expected : Nat → Bool)
    (entryMember : Member entry model.functionVariables)
    (beforeCoordinate : before.function entry.name = expected)
    (noMatching :
      Every (fun update : Update => ¬ (update.var = entry.name))
        action.updates)
    (holds : ActionHolds model action before after) :
    after.function entry.name = expected :=
  Or.elim (holds.2.2.2 entry entryMember)
    (fun updated =>
      Exists.elim updated (fun update facts =>
        False.elim
          ((everyMember
            (fun candidate : Update => ¬ (candidate.var = entry.name))
            update action.updates noMatching facts.1) facts.2.1)))
    (fun unchanged => Eq.trans unchanged.2 beforeCoordinate)

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

-- A scalar reachable row is ordered exactly like `ScalarModel.variables`.
-- Keeping names in the model, rather than duplicating them in certificate
-- data, makes a reordered/renamed model change the proposition the kernel
-- checks.  `ScalarCoordinatesDenote` is length-exact: neither a missing nor an
-- extra coordinate has a constructor.
def ScalarCoordinatesDenote (state : State)
    (entries : List StateVar) (values : List Nat) : Prop :=
  (@List.rec StateVar (fun _ => List Nat → Prop)
    (fun remaining =>
      match remaining with
      | [] => True
      | _ :: _ => False)
    (fun entry _ previous remaining =>
      match remaining with
      | [] => False
      | value :: tail =>
          state.scalar entry.name = value ∧ previous tail)
    entries) values

def ScalarRowDenotes (model : ScalarModel) (row : List Nat)
    (state : State) : Prop :=
  CanonicalState model.asModel state ∧
  ScalarCoordinatesDenote state model.variables row

def ScalarRowsStrengthening (model : ScalarModel) (rows : List (List Nat))
    (state : State) : Prop :=
  ∃ row : List Nat, Member row rows ∧ ScalarRowDenotes model row state

structure FiniteRow where
  scalarValues : List Nat
  functionValues : List (Nat → Bool)

def FunctionCoordinatesDenote (state : State)
    (entries : List FunctionVar) (values : List (Nat → Bool)) : Prop :=
  (@List.rec FunctionVar (fun _ => List (Nat → Bool) → Prop)
    (fun remaining =>
      match remaining with
      | [] => True
      | _ :: _ => False)
    (fun entry _ previous remaining =>
      match remaining with
      | [] => False
      | value :: tail =>
          state.function entry.name = value ∧ previous tail)
    entries) values

def FiniteRowDenotes (model : Model) (row : FiniteRow)
    (state : State) : Prop :=
  CanonicalState model state ∧
  ScalarCoordinatesDenote state model.variables row.scalarValues ∧
  FunctionCoordinatesDenote state model.functionVariables row.functionValues

def FiniteRowsStrengthening (model : Model) (rows : List FiniteRow)
    (state : State) : Prop :=
  ∃ row : FiniteRow, Member row rows ∧ FiniteRowDenotes model row state

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

-- The proposition-level target of the automatic scalar fixpoint reflector.
-- The row producer has no authority here: callers must supply exact
-- initiation, closure, and preservation proofs for the same model and quoted
-- rows.  The reflected checker discharges these three premises and this
-- theorem performs only the generic temporal induction/stutter step.
theorem scalarSafetyClaimOfRows
    (model : ScalarModel)
    (rows : List (List Nat))
    (initiation :
      ∀ state : State, Initial model.asModel state →
        ScalarRowsStrengthening model rows state)
    (consecution :
      ∀ before after : State,
        ScalarRowsStrengthening model rows before →
        Next model.asModel before after →
        ScalarRowsStrengthening model rows after)
    (preservation :
      ∀ state : State,
        ScalarRowsStrengthening model rows state →
        AllInvariantsHold model.asModel state) :
    SafetyClaim model.asModel :=
  safetyClaimOfStrengthening model.asModel
    (ScalarRowsStrengthening model rows)
    initiation consecution preservation

theorem finiteSafetyClaimOfRows
    (model : Model)
    (rows : List FiniteRow)
    (initiation :
      ∀ state : State, Initial model state →
        FiniteRowsStrengthening model rows state)
    (consecution :
      ∀ before after : State,
        FiniteRowsStrengthening model rows before →
        Next model before after →
        FiniteRowsStrengthening model rows after)
    (preservation :
      ∀ state : State,
        FiniteRowsStrengthening model rows state →
        AllInvariantsHold model state) :
    SafetyClaim model :=
  safetyClaimOfStrengthening model
    (FiniteRowsStrengthening model rows)
    initiation consecution preservation

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
