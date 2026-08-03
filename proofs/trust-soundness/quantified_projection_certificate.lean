-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- First non-circular soundness slice for AY's quantified projection certificate.
--
-- This file is checked by Trust's pinned `clean` CIC kernel. It deliberately
-- does NOT use trust-vc's AY-backed SMT discharge: using AY to justify the
-- checker that licenses AY's SAT verdict would be circular.
--
-- Scope of the theorem:
--   * a selected uninterpreted function is interpreted as a TOTAL projection
--     from its application arguments;
--   * rewriting that application to the selected argument preserves value;
--   * an equality supplied by an implication premise may be substituted in an
--     arbitrary Boolean context;
--   * complementary guarded equalities merge to a same-typed ITE and that
--     equality composes with premise substitution;
--   * the Boolean/ITE reducer preserves its denotation; and
--   * if the reduced rewritten conclusion is checked true whenever the premise
--     is true, the resulting total projection model satisfies the quantified
--     implication for every argument tuple.
--
-- The authority layer below lifts that semantic argument to an exact finite
-- multi-head projection map and indexes it by source/query provenance. It is
-- still a model: no claim below establishes live-Rust/MIR refinement.
--
-- This is a semantic theorem, not yet a proof that the current Rust checker is
-- a faithful implementation of every definition below. The live-Rust
-- conformance/dispatch obligations remain separate and fail-closed in AY.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def bite (c : Bool) (onTrue : Bool) (onFalse : Bool) : Bool :=
  match c with | true => onTrue | false => onFalse
def bimplies (premise : Bool) (conclusion : Bool) : Bool :=
  bor (bnot premise) conclusion

--------------------------------------------------------------------------------
-- Total projection semantics and rewrite fidelity.
--------------------------------------------------------------------------------

-- A small, kernel-owned list avoids importing either AY's term store or
-- Trust's Rust IR. `T` is arbitrary, so the theorem is independent of BV width
-- and also applies to Bool-valued heads.
inductive Args (T : Type) where
  | nil : Args T
  | cons : T -> Args T -> Args T

-- A projection definition must be total. The Rust checker rejects an
-- out-of-range selector; the fallback here gives the semantic function a value
-- on every input even before that well-formedness fact is connected.
def nthOr (T : Type) (fallback : T) : Nat -> Args T -> T
  | Nat.zero, Args.nil => fallback
  | Nat.zero, Args.cons head _ => head
  | Nat.succ _, Args.nil => fallback
  | Nat.succ index, Args.cons _ tail => nthOr T fallback index tail

-- Denotation of the UF head in the certified model.
def evalUfUnderProjection (T : Type) (fallback : T) (selector : Nat) (args : Args T) : T :=
  nthOr T fallback selector args

-- Value produced by rewriting `f(args)` to `args[selector]`.
def rewriteUfApplication (T : Type) (fallback : T) (selector : Nat) (args : Args T) : T :=
  nthOr T fallback selector args

-- PROJECTION_REWRITE_EVAL: the model interpretation and the checked rewrite
-- agree for every carrier, selector, and argument tuple. This first semantic
-- anchor is intentionally definitional: both sides name the same `nthOr`, so
-- the proof is `rfl`. It does not by itself establish that AY's live Rust
-- evaluator and rewriter refine these definitions.
theorem projection_rewrite_eval
    (T : Type) (fallback : T) (selector : Nat) (args : Args T) :
    evalUfUnderProjection T fallback selector args =
      rewriteUfApplication T fallback selector args := rfl

--------------------------------------------------------------------------------
-- Premise substitution.
--------------------------------------------------------------------------------

-- If the premise establishes `selected = rhs`, replacing `selected` by `rhs`
-- in an arbitrary Boolean context preserves its value. This is the semantic
-- core of each acyclic premise-substitution step; applying it repeatedly gives
-- the checked topological substitution chain.
theorem premise_substitution
    (T : Type) (selected : T) (rhs : T) (established : selected = rhs)
    (context : T -> Bool) :
    context selected = context rhs :=
  congrArg context established

-- Two checked substitutions compose without strengthening the premise.
theorem premise_substitution_two_steps
    (T : Type) (first : T) (second : T) (third : T)
    (firstEq : first = second) (secondEq : second = third)
    (context : T -> Bool) :
    context first = context third :=
  Eq.trans (congrArg context firstEq) (congrArg context secondEq)

-- A type-indexed ITE. Both branches inhabit the same arbitrary carrier `T`, so
-- an accepted conditional definition cannot silently cross Bool/BV sorts.
def typedIte (T : Type) (guard : Bool) (onTrue : T) (onFalse : T) : T :=
  match guard with | true => onTrue | false => onFalse

-- CONDITIONAL PREMISE MERGE. If complementary premise branches establish the
-- selected value as `rhsTrue` under a true guard and `rhsFalse` under a false
-- guard, then the selected value equals the total, same-typed ITE. This proof
-- performs Boolean elimination in the Clean kernel; it does not assume an AY
-- simplifier or solver result.
theorem conditional_premise_merge
    (T : Type) (selected : T) (guard : Bool)
    (rhsTrue : T) (rhsFalse : T)
    (selectedWhenTrue : guard = true -> selected = rhsTrue)
    (selectedWhenFalse : guard = false -> selected = rhsFalse) :
    selected = typedIte T guard rhsTrue rhsFalse :=
  @Bool.rec
    (fun value =>
      (value = true -> selected = rhsTrue) ->
      (value = false -> selected = rhsFalse) ->
        selected = typedIte T value rhsTrue rhsFalse)
    (fun _ falseBranch => falseBranch rfl)
    (fun trueBranch _ => trueBranch rfl)
    guard
    selectedWhenTrue
    selectedWhenFalse

-- The conditional equality is admissible by the existing substitution theorem
-- in every Boolean context; no special, stronger substitution rule is needed.
theorem conditional_premise_substitution
    (T : Type) (selected : T) (guard : Bool)
    (rhsTrue : T) (rhsFalse : T)
    (selectedWhenTrue : guard = true -> selected = rhsTrue)
    (selectedWhenFalse : guard = false -> selected = rhsFalse)
    (context : T -> Bool) :
    context selected = context (typedIte T guard rhsTrue rhsFalse) :=
  premise_substitution
    T selected (typedIte T guard rhsTrue rhsFalse)
    (conditional_premise_merge
      T selected guard rhsTrue rhsFalse selectedWhenTrue selectedWhenFalse)
    context

--------------------------------------------------------------------------------
-- Boolean/ITE reducer soundness.
--------------------------------------------------------------------------------

-- Exactly the independent reducer fragment used after projection and premise
-- substitution: Boolean leaves, negation, conjunction, disjunction, and ITE.
-- Equality/congruence checks produce `atom` leaves; their semantic authority is
-- supplied by `premise_substitution` and reflexive equality, not by this reducer.
inductive BoolExpr where
  | atom : Bool -> BoolExpr
  | lit : Bool -> BoolExpr
  | notNode : BoolExpr -> BoolExpr
  | andNode : BoolExpr -> BoolExpr -> BoolExpr
  | orNode : BoolExpr -> BoolExpr -> BoolExpr
  | iteNode : BoolExpr -> BoolExpr -> BoolExpr -> BoolExpr

def evalBoolExpr : BoolExpr -> Bool
  | BoolExpr.atom value => value
  | BoolExpr.lit value => value
  | BoolExpr.notNode arg => bnot (evalBoolExpr arg)
  | BoolExpr.andNode left right => band (evalBoolExpr left) (evalBoolExpr right)
  | BoolExpr.orNode left right => bor (evalBoolExpr left) (evalBoolExpr right)
  | BoolExpr.iteNode guard onTrue onFalse =>
      bite (evalBoolExpr guard) (evalBoolExpr onTrue) (evalBoolExpr onFalse)

-- The reducer is intentionally written independently from `evalBoolExpr`: it
-- pattern-matches directly on recursively reduced results, mirroring the small
-- constant-folding kernel rather than calling the denotational evaluator.
def reduceBool : BoolExpr -> Bool
  | BoolExpr.atom value => value
  | BoolExpr.lit value => value
  | BoolExpr.notNode arg =>
      match reduceBool arg with | true => false | false => true
  | BoolExpr.andNode left right =>
      match reduceBool left with | true => reduceBool right | false => false
  | BoolExpr.orNode left right =>
      match reduceBool left with | true => true | false => reduceBool right
  | BoolExpr.iteNode guard onTrue onFalse =>
      match reduceBool guard with
      | true => reduceBool onTrue
      | false => reduceBool onFalse

-- BOOLEAN_ITE_NORMALIZER_SOUND: reduction never changes the formula value.
theorem boolean_ite_normalizer_sound (expr : BoolExpr) :
    reduceBool expr = evalBoolExpr expr :=
  @BoolExpr.rec
    (fun item => reduceBool item = evalBoolExpr item)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ ih => congrArg bnot ih)
    (fun left right ihLeft ihRight =>
      Eq.trans
        (congrArg (fun value => band value (reduceBool right)) ihLeft)
        (congrArg (fun value => band (evalBoolExpr left) value) ihRight))
    (fun left right ihLeft ihRight =>
      Eq.trans
        (congrArg (fun value => bor value (reduceBool right)) ihLeft)
        (congrArg (fun value => bor (evalBoolExpr left) value) ihRight))
    (fun guard onTrue onFalse ihGuard ihTrue ihFalse =>
      Eq.trans
        (congrArg
          (fun value => bite value (reduceBool onTrue) (reduceBool onFalse))
          ihGuard)
        (Eq.trans
          (congrArg
            (fun value => bite (evalBoolExpr guard) value (reduceBool onFalse))
            ihTrue)
          (congrArg
            (fun value => bite (evalBoolExpr guard) (evalBoolExpr onTrue) value)
            ihFalse)))
    expr

--------------------------------------------------------------------------------
-- Accepted certificate implies a total model of the quantified implication.
--------------------------------------------------------------------------------

-- Boolean bridge used by both composition theorems: a checked conclusion under
-- a true premise is exactly what is needed to satisfy implication semantics.
theorem implication_of_checked_conclusion
    (premise : Bool) (conclusion : Bool)
    (checked : premise = true -> conclusion = true) :
    bimplies premise conclusion = true :=
  @Bool.rec
    (fun value =>
      (value = true -> conclusion = true) ->
        bimplies value conclusion = true)
    (fun _ => rfl)
    (fun trueCase =>
      Eq.trans
        (congrArg (fun value => bimplies true value) (trueCase rfl))
        rfl)
    premise
    checked

-- ACCEPTED=>MODEL, without premise substitution. `checked` is the runtime
-- checker's acceptance obligation: for every argument tuple on which the
-- premise holds, the independently reduced rewritten conclusion is true.
-- The conclusion is evaluated using the TOTAL projection interpretation.
theorem accepted_projection_implies_model
    (T : Type) (fallback : T) (selector : Nat)
    (premise : Args T -> Bool) (context : T -> BoolExpr)
    (checked : (args : Args T) -> premise args = true ->
      reduceBool (context (rewriteUfApplication T fallback selector args)) = true) :
    (args : Args T) ->
      bimplies
        (premise args)
        (evalBoolExpr (context (evalUfUnderProjection T fallback selector args))) = true :=
  fun args =>
    implication_of_checked_conclusion
      (premise args)
      (evalBoolExpr (context (evalUfUnderProjection T fallback selector args)))
      (fun premiseTrue =>
        Eq.trans
          (congrArg evalBoolExpr
            (congrArg context
              (projection_rewrite_eval T fallback selector args)))
          (Eq.trans
            (Eq.symm
              (boolean_ite_normalizer_sound
                (context (rewriteUfApplication T fallback selector args))))
            (checked args premiseTrue)))

-- ACCEPTED=>MODEL with the acyclic premise-substitution step made explicit.
-- Under a true premise, `established` proves that the projected value equals
-- `rhs`; the checker may reduce `context rhs`. Rewrite fidelity, equality
-- substitution, and reducer soundness compose to show that the original body
-- under the total UF model is true for every argument tuple.
theorem accepted_projection_with_premise_substitution_implies_model
    (T : Type) (fallback : T) (selector : Nat)
    (premise : Args T -> Bool) (rhs : Args T -> T)
    (context : T -> BoolExpr)
    (established : (args : Args T) -> premise args = true ->
      rewriteUfApplication T fallback selector args = rhs args)
    (checked : (args : Args T) -> premise args = true ->
      reduceBool (context (rhs args)) = true) :
    (args : Args T) ->
      bimplies
        (premise args)
        (evalBoolExpr (context (evalUfUnderProjection T fallback selector args))) = true :=
  fun args =>
    implication_of_checked_conclusion
      (premise args)
      (evalBoolExpr (context (evalUfUnderProjection T fallback selector args)))
      (fun premiseTrue =>
        Eq.trans
          (congrArg evalBoolExpr
            (congrArg context
              (projection_rewrite_eval T fallback selector args)))
          (Eq.trans
            (congrArg evalBoolExpr
              (congrArg context (established args premiseTrue)))
            (Eq.trans
              (Eq.symm (boolean_ite_normalizer_sound (context (rhs args))))
              (checked args premiseTrue))))

-- ACCEPTED=>MODEL for the conditional-premise rule. The two guarded branch
-- equalities are first merged by `conditional_premise_merge`; the resulting
-- typed ITE equality is then passed to the already-proven ordinary premise-
-- substitution composition theorem. This adds no new SAT authority.
theorem accepted_projection_with_conditional_premise_implies_model
    (T : Type) (fallback : T) (selector : Nat)
    (premise : Args T -> Bool) (guard : Args T -> Bool)
    (rhsTrue : Args T -> T) (rhsFalse : Args T -> T)
    (context : T -> BoolExpr)
    (establishedTrue : (args : Args T) -> premise args = true ->
      guard args = true ->
        rewriteUfApplication T fallback selector args = rhsTrue args)
    (establishedFalse : (args : Args T) -> premise args = true ->
      guard args = false ->
        rewriteUfApplication T fallback selector args = rhsFalse args)
    (checked : (args : Args T) -> premise args = true ->
      reduceBool
        (context (typedIte T (guard args) (rhsTrue args) (rhsFalse args))) = true) :
    (args : Args T) ->
      bimplies
        (premise args)
        (evalBoolExpr (context (evalUfUnderProjection T fallback selector args))) = true :=
  accepted_projection_with_premise_substitution_implies_model
    T fallback selector premise
    (fun args => typedIte T (guard args) (rhsTrue args) (rhsFalse args))
    context
    (fun args premiseTrue =>
      conditional_premise_merge
        T
        (rewriteUfApplication T fallback selector args)
        (guard args)
        (rhsTrue args)
        (rhsFalse args)
        (fun guardTrue => establishedTrue args premiseTrue guardTrue)
        (fun guardFalse => establishedFalse args premiseTrue guardFalse))
    checked

-- Concrete sanity witness: `f(a,b)` projects to `b`; when the premise is true,
-- the checked conclusion is `ite true true false`, hence the quantified body is
-- satisfied. This exercises projection and ITE reduction in one closed term.
def twoBoolArgs : Args Bool := Args.cons false (Args.cons true Args.nil)
def trueContext (_ : Bool) : BoolExpr :=
  BoolExpr.iteNode (BoolExpr.lit true) (BoolExpr.lit true) (BoolExpr.lit false)
theorem projection_ite_witness :
    bimplies true
      (evalBoolExpr (trueContext
        (evalUfUnderProjection Bool false (Nat.succ Nat.zero) twoBoolArgs))) = true :=
  accepted_projection_implies_model
    Bool false (Nat.succ Nat.zero)
    (fun _ => true)
    trueContext
    (fun _ _ => rfl)
    twoBoolArgs

--------------------------------------------------------------------------------
-- Exact finite-map subject, source binding, and authored-query SAT authority.
--------------------------------------------------------------------------------

-- The finite map is modeled below with exact stable declaration/signature,
-- application-pattern, and selector identities plus nonempty/uniqueness
-- evidence. Nothing below proves that live Rust constructs the same map.

-- Opaque frontend identity plus source/elaboration epoch. Equal printed names
-- are irrelevant; redeclaration receives a different `DeclarationId`.
inductive SourceContextStamp where
  | capture : Nat -> Nat -> SourceContextStamp

-- A public decision attempt has a separate epoch. Repeating `check-sat` at an
-- otherwise identical source stamp and root vector must not reuse a permit.
inductive QueryAuthorityEpoch where
  | capture : Nat -> QueryAuthorityEpoch

inductive DeclarationId where
  | declaration : Nat -> DeclarationId

-- Signature identities are opaque modeled sort identities, not source text.
-- The declaration reference contains both stable identity and full signature.
inductive SortIdentity where
  | sort : Nat -> SortIdentity

inductive SortIdentities where
  | nil : SortIdentities
  | cons : SortIdentity -> SortIdentities -> SortIdentities

inductive DeclarationSignature where
  | function : SortIdentities -> SortIdentity -> DeclarationSignature

inductive DeclarationRef where
  | declaration : DeclarationId -> DeclarationSignature -> DeclarationRef

-- Ordered roots model the exact frozen assertion vector, never a digest.
inductive AssertionRoots where
  | nil : AssertionRoots
  | cons : Nat -> AssertionRoots -> AssertionRoots

-- Mirrors every production `ay_frontend::DeclarationKind` variant.
inductive DeclarationKind where
  | freeUninterpreted : DeclarationKind
  | defined : DeclarationKind
  | adoptedDefinition : DeclarationKind
  | datatypeConstructor : DeclarationKind
  | datatypeSelector : DeclarationKind
  | datatypeTester : DeclarationKind
  | theory : DeclarationKind
  | solverInternal : DeclarationKind

-- Empty `check-sat-assuming` remains a distinct, ineligible origin.
inductive QueryDispatch where
  | authoredCheckSat : QueryDispatch
  | authoredCheckSatAssuming : QueryDispatch
  | genericExecutor : QueryDispatch
  | internalSolver : QueryDispatch

def sameSourceContext : SourceContextStamp -> SourceContextStamp -> Bool
  | SourceContextStamp.capture leftContext leftEpoch,
      SourceContextStamp.capture rightContext rightEpoch =>
    band (Nat.beq leftContext rightContext) (Nat.beq leftEpoch rightEpoch)

def sameQueryAuthorityEpoch : QueryAuthorityEpoch -> QueryAuthorityEpoch -> Bool
  | QueryAuthorityEpoch.capture left, QueryAuthorityEpoch.capture right =>
    Nat.beq left right

def sameDeclarationId : DeclarationId -> DeclarationId -> Bool
  | DeclarationId.declaration left, DeclarationId.declaration right =>
    Nat.beq left right

def sameSortIdentity : SortIdentity -> SortIdentity -> Bool
  | SortIdentity.sort left, SortIdentity.sort right => Nat.beq left right

def sameSortIdentities : SortIdentities -> SortIdentities -> Bool
  | SortIdentities.nil, SortIdentities.nil => true
  | SortIdentities.cons leftHead leftTail,
      SortIdentities.cons rightHead rightTail =>
    band (sameSortIdentity leftHead rightHead)
      (sameSortIdentities leftTail rightTail)
  | SortIdentities.nil, SortIdentities.cons _ _ => false
  | SortIdentities.cons _ _, SortIdentities.nil => false

def sameDeclarationSignature : DeclarationSignature -> DeclarationSignature -> Bool
  | DeclarationSignature.function leftArgs leftResult,
      DeclarationSignature.function rightArgs rightResult =>
    band (sameSortIdentities leftArgs rightArgs)
      (sameSortIdentity leftResult rightResult)

def sameDeclarationRef : DeclarationRef -> DeclarationRef -> Bool
  | DeclarationRef.declaration leftId leftSignature,
      DeclarationRef.declaration rightId rightSignature =>
    band (sameDeclarationId leftId rightId)
      (sameDeclarationSignature leftSignature rightSignature)

def sameAssertionRoots : AssertionRoots -> AssertionRoots -> Bool
  | AssertionRoots.nil, AssertionRoots.nil => true
  | AssertionRoots.cons leftHead leftTail,
      AssertionRoots.cons rightHead rightTail =>
    band (Nat.beq leftHead rightHead) (sameAssertionRoots leftTail rightTail)
  | AssertionRoots.nil, AssertionRoots.cons _ _ => false
  | AssertionRoots.cons _ _, AssertionRoots.nil => false

def isFreeUninterpreted : DeclarationKind -> Bool
  | DeclarationKind.freeUninterpreted => true
  | DeclarationKind.defined => false
  | DeclarationKind.adoptedDefinition => false
  | DeclarationKind.datatypeConstructor => false
  | DeclarationKind.datatypeSelector => false
  | DeclarationKind.datatypeTester => false
  | DeclarationKind.theory => false
  | DeclarationKind.solverInternal => false

def isAuthoredPlainHard : QueryDispatch -> Bool
  | QueryDispatch.authoredCheckSat => true
  | QueryDispatch.authoredCheckSatAssuming => false
  | QueryDispatch.genericExecutor => false
  | QueryDispatch.internalSolver => false

-- A projection head records the exact stable declaration, an opaque identity
-- for its checked application pattern, its total fallback/selector pair, and
-- the application arguments computed from the quantified binder tuple.
inductive ApplicationPatternId where
  | pattern : Nat -> ApplicationPatternId

def sameApplicationPatternId : ApplicationPatternId -> ApplicationPatternId -> Bool
  | ApplicationPatternId.pattern left, ApplicationPatternId.pattern right =>
    Nat.beq left right

inductive ProjectionHead (T : Type) where
  | exact :
    DeclarationRef -> ApplicationPatternId -> T -> Nat ->
    (Args T -> Args T) -> ProjectionHead T

-- `ProjectionMap` is an ordered finite representation of the production
-- declaration-to-projection map. `projectionMapUnique` below upgrades the raw
-- list to map semantics by rejecting duplicate stable declaration references.
inductive ProjectionMap (T : Type) where
  | nil : ProjectionMap T
  | cons : ProjectionHead T -> ProjectionMap T -> ProjectionMap T

inductive ProjectionValues (T : Type) where
  | nil : ProjectionValues T
  | cons : T -> ProjectionValues T -> ProjectionValues T

inductive ProjectionBindingRef where
  | binding : DeclarationRef -> ApplicationPatternId -> Nat -> ProjectionBindingRef

inductive ProjectionMapIdentity where
  | nil : ProjectionMapIdentity
  | cons : ProjectionBindingRef -> ProjectionMapIdentity -> ProjectionMapIdentity

def projectionHeadDeclaration (T : Type) : ProjectionHead T -> DeclarationRef
  | ProjectionHead.exact declaration _ _ _ _ => declaration

def projectionHeadBindingRef (T : Type) : ProjectionHead T -> ProjectionBindingRef
  | ProjectionHead.exact declaration patternId _ selector _ =>
    ProjectionBindingRef.binding declaration patternId selector

def sameProjectionBindingRef : ProjectionBindingRef -> ProjectionBindingRef -> Bool
  | ProjectionBindingRef.binding leftDeclaration leftPattern leftSelector,
      ProjectionBindingRef.binding rightDeclaration rightPattern rightSelector =>
    band (sameDeclarationRef leftDeclaration rightDeclaration)
      (band (sameApplicationPatternId leftPattern rightPattern)
        (Nat.beq leftSelector rightSelector))

def sameProjectionMapIdentity : ProjectionMapIdentity -> ProjectionMapIdentity -> Bool
  | ProjectionMapIdentity.nil, ProjectionMapIdentity.nil => true
  | ProjectionMapIdentity.cons leftHead leftTail,
      ProjectionMapIdentity.cons rightHead rightTail =>
    band (sameProjectionBindingRef leftHead rightHead)
      (sameProjectionMapIdentity leftTail rightTail)
  | ProjectionMapIdentity.nil, ProjectionMapIdentity.cons _ _ => false
  | ProjectionMapIdentity.cons _ _, ProjectionMapIdentity.nil => false

def projectionMapIdentity (T : Type)
    (projections : ProjectionMap T) : ProjectionMapIdentity :=
  @ProjectionMap.rec
    T
    (fun _ => ProjectionMapIdentity)
    ProjectionMapIdentity.nil
    (fun head _ tailIdentity =>
      ProjectionMapIdentity.cons
        (projectionHeadBindingRef T head) tailIdentity)
    projections

def projectionMapContainsDeclaration (T : Type)
    (requested : DeclarationRef) (projections : ProjectionMap T) : Bool :=
  @ProjectionMap.rec
    T
    (fun _ => Bool)
    false
    (fun head _ tailContains =>
      match sameDeclarationRef requested (projectionHeadDeclaration T head) with
      | true => true
      | false => tailContains)
    projections

def projectionMapUnique (T : Type) (projections : ProjectionMap T) : Bool :=
  @ProjectionMap.rec
    T
    (fun _ => Bool)
    true
    (fun head tail tailUnique =>
      band
        (bnot
          (projectionMapContainsDeclaration T
            (projectionHeadDeclaration T head) tail))
        tailUnique)
    projections

def projectionMapNonempty (T : Type) : ProjectionMap T -> Bool
  | ProjectionMap.nil => false
  | ProjectionMap.cons _ _ => true

def rewriteProjectionHead (T : Type) (binderArgs : Args T) : ProjectionHead T -> T
  | ProjectionHead.exact _ _ fallback selector applicationArgs =>
    rewriteUfApplication T fallback selector (applicationArgs binderArgs)

def evalProjectionHead (T : Type) (binderArgs : Args T) : ProjectionHead T -> T
  | ProjectionHead.exact _ _ fallback selector applicationArgs =>
    evalUfUnderProjection T fallback selector (applicationArgs binderArgs)

def rewriteProjectionMap (T : Type) (binderArgs : Args T)
    (projections : ProjectionMap T) : ProjectionValues T :=
  @ProjectionMap.rec
    T
    (fun _ => ProjectionValues T)
    ProjectionValues.nil
    (fun head _ tailValues =>
      ProjectionValues.cons
        (rewriteProjectionHead T binderArgs head) tailValues)
    projections

def evalProjectionMap (T : Type) (binderArgs : Args T)
    (projections : ProjectionMap T) : ProjectionValues T :=
  @ProjectionMap.rec
    T
    (fun _ => ProjectionValues T)
    ProjectionValues.nil
    (fun head _ tailValues =>
      ProjectionValues.cons
        (evalProjectionHead T binderArgs head) tailValues)
    projections

-- Exact finite-map lifting of PROJECTION_REWRITE_EVAL. Every map entry is
-- evaluated at its own checked application-argument function, and the ordered
-- value vector agrees with simultaneous rewriting for every binder tuple.
theorem projection_map_rewrite_eval
    (T : Type) (binderArgs : Args T) (projections : ProjectionMap T) :
    evalProjectionMap T binderArgs projections =
      rewriteProjectionMap T binderArgs projections := rfl

-- ACCEPTED=>MODEL for an exact finite projection map. This is the multi-head
-- semantic composition theorem used by the authority eliminator below.
theorem accepted_projection_map_implies_model
    (T : Type)
    (projections : ProjectionMap T)
    (premise : Args T -> Bool)
    (context : ProjectionValues T -> BoolExpr)
    (checked : (args : Args T) -> premise args = true ->
      reduceBool (context (rewriteProjectionMap T args projections)) = true) :
    (args : Args T) ->
      bimplies
        (premise args)
        (evalBoolExpr (context (evalProjectionMap T args projections))) = true :=
  fun args =>
    implication_of_checked_conclusion
      (premise args)
      (evalBoolExpr (context (evalProjectionMap T args projections)))
      (fun premiseTrue =>
        Eq.trans
          (congrArg evalBoolExpr
            (congrArg context
              (projection_map_rewrite_eval T args projections)))
          (Eq.trans
            (Eq.symm
              (boolean_ite_normalizer_sound
                (context (rewriteProjectionMap T args projections))))
            (checked args premiseTrue)))

-- The exact multi-head subject shared by semantic, source, and query evidence.
-- The complete finite projection map and semantic functions are part of the
-- subject, rather than arbitrary Boolean indices.
inductive ProjectionSubject (T : Type) where
  | exact :
    SourceContextStamp -> QueryAuthorityEpoch -> AssertionRoots ->
    ProjectionMap T -> Nat -> Nat ->
    (Args T -> Bool) -> (ProjectionValues T -> BoolExpr) -> ProjectionSubject T

-- Evidence that this exact subject has the stated total projection model. The
-- constructor repeats every subject field in its result index, so the model
-- theorem cannot be transported to another context/root/declaration record.
inductive SubjectHasModel (T : Type) : ProjectionSubject T -> Type where
  | establish :
    (capturedStamp : SourceContextStamp) ->
    (queryEpoch : QueryAuthorityEpoch) ->
    (roots : AssertionRoots) ->
    (projections : ProjectionMap T) ->
    (scopeDepth : Nat) ->
    (termCount : Nat) ->
    (premise : Args T -> Bool) ->
    (context : ProjectionValues T -> BoolExpr) ->
    ((args : Args T) ->
      bimplies
        (premise args)
        (evalBoolExpr
          (context (evalProjectionMap T args projections))) = true) ->
    SubjectHasModel T
      (ProjectionSubject.exact capturedStamp queryEpoch roots projections
        scopeDepth termCount premise context)

inductive LiveDeclarationInventory where
  | nil : LiveDeclarationInventory
  | cons :
    DeclarationRef -> DeclarationKind -> LiveDeclarationInventory ->
    LiveDeclarationInventory

inductive LiveSourceState where
  | snapshot :
    SourceContextStamp -> AssertionRoots -> LiveDeclarationInventory -> LiveSourceState

inductive AuthoredQueryState where
  | capture :
    QueryAuthorityEpoch -> SourceContextStamp -> AssertionRoots ->
    ProjectionMapIdentity -> Nat -> Nat -> QueryDispatch ->
    Nat -> Nat -> Nat -> Nat -> AuthoredQueryState

def liveDeclarationIsFree
    (requested : DeclarationRef) (inventory : LiveDeclarationInventory) : Bool :=
  @LiveDeclarationInventory.rec
    (fun _ => Bool)
    false
    (fun actual actualKind _ tailResult =>
      match sameDeclarationRef requested actual with
      | true => isFreeUninterpreted actualKind
      | false => tailResult)
    inventory

def projectionMapBoundToFreeDeclarations (T : Type)
    (inventory : LiveDeclarationInventory) (projections : ProjectionMap T) : Bool :=
  @ProjectionMap.rec
    T
    (fun _ => Bool)
    true
    (fun head _ tailBound =>
      band
        (liveDeclarationIsFree (projectionHeadDeclaration T head) inventory)
        tailBound)
    projections

-- Positive live-source check over the exact subject record. Every head in the
-- exact map must resolve by stable ID/full signature to a currently present
-- free-UF declaration. Absence, stale provenance, or any non-free kind rejects.
def sourceProjectionBindingAccepted (T : Type) :
    ProjectionSubject T -> LiveSourceState -> Bool
  | ProjectionSubject.exact capturedStamp _ capturedRoots projections
      _ _ _ _,
      LiveSourceState.snapshot currentStamp currentRoots inventory =>
    band (sameSourceContext capturedStamp currentStamp)
      (band (sameAssertionRoots capturedRoots currentRoots)
        (projectionMapBoundToFreeDeclarations T inventory projections))

-- Exact query check over the SAME subject. Besides source/root/declaration,
-- scope-depth, and term-count agreement, the fresh public query epoch and
-- explicit `check-sat` origin are load-bearing. Parser-owned softs and
-- API-owned softs are tracked separately.
def plainHardQueryAccepted (T : Type) :
    ProjectionSubject T -> AuthoredQueryState -> Bool
  | ProjectionSubject.exact certificateStamp certificateQueryEpoch
      certificateRoots certificateProjections certificateScopeDepth
      certificateTermCount _ _,
      AuthoredQueryState.capture queryEpoch queryStamp queryRoots queryProjections
        queryScopeDepth queryTermCount dispatch assumptionCount parsedSoftCount
        nativeSoftCount objectiveCount =>
    band (sameQueryAuthorityEpoch certificateQueryEpoch queryEpoch)
      (band (sameSourceContext certificateStamp queryStamp)
        (band (sameAssertionRoots certificateRoots queryRoots)
          (band
            (sameProjectionMapIdentity
              (projectionMapIdentity T certificateProjections) queryProjections)
            (band (Nat.beq certificateScopeDepth queryScopeDepth)
              (band (Nat.beq certificateTermCount queryTermCount)
                (band (isAuthoredPlainHard dispatch)
                  (band (Nat.beq assumptionCount Nat.zero)
                    (band (Nat.beq parsedSoftCount Nat.zero)
                      (band (Nat.beq nativeSoftCount Nat.zero)
                        (Nat.beq objectiveCount Nat.zero))))))))))

-- Three distinct dependent evidence families. A literal Bool has none of these
-- types, and evidence for subject B cannot be substituted into subject A. The
-- semantic constructor carries the checker's exact accepted-conclusion
-- obligation; it does not accept a Boolean verdict or a prepackaged model.
inductive CheckedProjectionSemantics
    (T : Type) : ProjectionSubject T -> Type where
  | certify :
    (capturedStamp : SourceContextStamp) ->
    (queryEpoch : QueryAuthorityEpoch) ->
    (roots : AssertionRoots) ->
    (projections : ProjectionMap T) ->
    (scopeDepth : Nat) ->
    (termCount : Nat) ->
    (premise : Args T -> Bool) ->
    (context : ProjectionValues T -> BoolExpr) ->
    projectionMapNonempty T projections = true ->
    projectionMapUnique T projections = true ->
    ((args : Args T) -> premise args = true ->
      reduceBool (context (rewriteProjectionMap T args projections)) = true) ->
    CheckedProjectionSemantics T
      (ProjectionSubject.exact capturedStamp queryEpoch roots projections
        scopeDepth termCount premise context)

inductive CheckedSourceBinding
    (T : Type) (subject : ProjectionSubject T) (live : LiveSourceState) where
  | certify : sourceProjectionBindingAccepted T subject live = true ->
    CheckedSourceBinding T subject live

inductive CheckedAuthoredPlainHardQuery
    (T : Type) (subject : ProjectionSubject T) (query : AuthoredQueryState) where
  | certify : plainHardQueryAccepted T subject query = true ->
    CheckedAuthoredPlainHardQuery T subject query

-- Stopped and deterministic resource-limit outcomes are deliberately outside
-- `CheckedProjectionSemantics`; neither can be supplied to the SAT constructor.
inductive ProjectionCheckOutcome
    (T : Type) (subject : ProjectionSubject T) where
  | checked : CheckedProjectionSemantics T subject -> ProjectionCheckOutcome T subject
  | stopped : ProjectionCheckOutcome T subject
  | resourceLimit : ProjectionCheckOutcome T subject

-- SAT authority is indexed by one exact subject/live-source/query triple and
-- accepts only the three typed evidence objects for those same records.
inductive ProjectionSatAuthority
    (T : Type)
    (subject : ProjectionSubject T)
    (live : LiveSourceState)
    (query : AuthoredQueryState) where
  | mint :
    CheckedProjectionSemantics T subject ->
    CheckedSourceBinding T subject live ->
    CheckedAuthoredPlainHardQuery T subject query ->
    ProjectionSatAuthority T subject live query

def checked_projection_semantics_has_model
    (T : Type) (subject : ProjectionSubject T)
    (evidence : CheckedProjectionSemantics T subject) :
    SubjectHasModel T subject :=
  match evidence with
  | CheckedProjectionSemantics.certify capturedStamp queryEpoch roots projections
      scopeDepth termCount premise context _ _ checked =>
    SubjectHasModel.establish
      capturedStamp queryEpoch roots projections scopeDepth termCount
      premise context
      (accepted_projection_map_implies_model
        T projections premise context checked)

-- Eliminating authority yields a model theorem for the exact subject, not a
-- proof about an independently chosen Bool.
def projection_sat_authority_has_model
    (T : Type)
    (subject : ProjectionSubject T)
    (live : LiveSourceState)
    (query : AuthoredQueryState)
    (authority : ProjectionSatAuthority T subject live query) :
    SubjectHasModel T subject :=
  match authority with
  | ProjectionSatAuthority.mint semanticEvidence _ _ =>
    checked_projection_semantics_has_model T subject semanticEvidence

def projection_sat_authority_has_source_binding
    (T : Type)
    (subject : ProjectionSubject T)
    (live : LiveSourceState)
    (query : AuthoredQueryState)
    (authority : ProjectionSatAuthority T subject live query) :
    CheckedSourceBinding T subject live :=
  match authority with
  | ProjectionSatAuthority.mint _ bindingEvidence _ => bindingEvidence

def projection_sat_authority_has_exact_query
    (T : Type)
    (subject : ProjectionSubject T)
    (live : LiveSourceState)
    (query : AuthoredQueryState)
    (authority : ProjectionSatAuthority T subject live query) :
    CheckedAuthoredPlainHardQuery T subject query :=
  match authority with
  | ProjectionSatAuthority.mint _ _ queryEvidence => queryEvidence

def semantic_projection_with_bound_authored_query_mints_sat
    (T : Type)
    (subject : ProjectionSubject T)
    (live : LiveSourceState)
    (query : AuthoredQueryState)
    (semanticEvidence : CheckedProjectionSemantics T subject)
    (bindingEvidence : CheckedSourceBinding T subject live)
    (queryEvidence : CheckedAuthoredPlainHardQuery T subject query) :
    ProjectionSatAuthority T subject live query :=
  ProjectionSatAuthority.mint semanticEvidence bindingEvidence queryEvidence

--------------------------------------------------------------------------------
-- Closed green witness and executable rejection sentinels.
--------------------------------------------------------------------------------

def authorityCurrentStamp : SourceContextStamp :=
  SourceContextStamp.capture (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero))
def authorityStaleStamp : SourceContextStamp :=
  SourceContextStamp.capture (Nat.succ Nat.zero) (Nat.succ Nat.zero)
def authorityForeignStamp : SourceContextStamp :=
  SourceContextStamp.capture (Nat.succ (Nat.succ Nat.zero))
    (Nat.succ (Nat.succ Nat.zero))

def authorityCurrentQueryEpoch : QueryAuthorityEpoch :=
  QueryAuthorityEpoch.capture (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
def authorityPreviousQueryEpoch : QueryAuthorityEpoch :=
  QueryAuthorityEpoch.capture (Nat.succ (Nat.succ Nat.zero))

def authorityScopeDepth : Nat := Nat.succ Nat.zero
def authorityChangedScopeDepth : Nat := Nat.succ (Nat.succ Nat.zero)
def authorityTermCount : Nat := Nat.succ (Nat.succ Nat.zero)
def authorityChangedTermCount : Nat :=
  Nat.succ (Nat.succ (Nat.succ Nat.zero))

def authorityRoots : AssertionRoots :=
  AssertionRoots.cons (Nat.succ Nat.zero)
    (AssertionRoots.cons (Nat.succ (Nat.succ Nat.zero)) AssertionRoots.nil)
def authorityChangedRoots : AssertionRoots :=
  AssertionRoots.cons (Nat.succ Nat.zero)
    (AssertionRoots.cons
      (Nat.succ (Nat.succ (Nat.succ Nat.zero))) AssertionRoots.nil)
def authorityReorderedRoots : AssertionRoots :=
  AssertionRoots.cons (Nat.succ (Nat.succ Nat.zero))
    (AssertionRoots.cons (Nat.succ Nat.zero) AssertionRoots.nil)
def authorityShortRoots : AssertionRoots :=
  AssertionRoots.cons (Nat.succ Nat.zero) AssertionRoots.nil
def authorityLongRoots : AssertionRoots :=
  AssertionRoots.cons (Nat.succ Nat.zero)
    (AssertionRoots.cons (Nat.succ (Nat.succ Nat.zero))
      (AssertionRoots.cons
        (Nat.succ (Nat.succ (Nat.succ Nat.zero))) AssertionRoots.nil))

def authorityBoolSort : SortIdentity := SortIdentity.sort (Nat.succ Nat.zero)
def authorityOtherSort : SortIdentity :=
  SortIdentity.sort (Nat.succ (Nat.succ Nat.zero))
def authorityArgumentSorts : SortIdentities :=
  SortIdentities.cons authorityBoolSort
    (SortIdentities.cons authorityOtherSort SortIdentities.nil)
def authorityChangedArgumentSorts : SortIdentities :=
  SortIdentities.cons authorityBoolSort
    (SortIdentities.cons authorityBoolSort SortIdentities.nil)
def authorityReorderedArgumentSorts : SortIdentities :=
  SortIdentities.cons authorityOtherSort
    (SortIdentities.cons authorityBoolSort SortIdentities.nil)
def authorityShortArgumentSorts : SortIdentities :=
  SortIdentities.cons authorityBoolSort SortIdentities.nil
def authoritySignature : DeclarationSignature :=
  DeclarationSignature.function authorityArgumentSorts authorityBoolSort
def authorityChangedResultSignature : DeclarationSignature :=
  DeclarationSignature.function authorityArgumentSorts authorityOtherSort
def authorityChangedArgumentSignature : DeclarationSignature :=
  DeclarationSignature.function authorityChangedArgumentSorts authorityBoolSort
def authorityReorderedArgumentSignature : DeclarationSignature :=
  DeclarationSignature.function authorityReorderedArgumentSorts authorityBoolSort
def authorityChangedAritySignature : DeclarationSignature :=
  DeclarationSignature.function authorityShortArgumentSorts authorityBoolSort
def authorityDeclarationId : DeclarationId :=
  DeclarationId.declaration (Nat.succ Nat.zero)
def authorityReplacementDeclarationId : DeclarationId :=
  DeclarationId.declaration (Nat.succ (Nat.succ Nat.zero))
def authoritySecondDeclarationId : DeclarationId :=
  DeclarationId.declaration (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
def authorityDeclaration : DeclarationRef :=
  DeclarationRef.declaration authorityDeclarationId authoritySignature
def authorityReplacementDeclaration : DeclarationRef :=
  DeclarationRef.declaration authorityReplacementDeclarationId authoritySignature
def authorityWrongSignatureDeclaration : DeclarationRef :=
  DeclarationRef.declaration authorityDeclarationId authorityChangedResultSignature
def authorityWrongArgumentDeclaration : DeclarationRef :=
  DeclarationRef.declaration authorityDeclarationId authorityChangedArgumentSignature
def authorityWrongArgumentOrderDeclaration : DeclarationRef :=
  DeclarationRef.declaration authorityDeclarationId authorityReorderedArgumentSignature
def authorityWrongArityDeclaration : DeclarationRef :=
  DeclarationRef.declaration authorityDeclarationId authorityChangedAritySignature
def authoritySecondDeclaration : DeclarationRef :=
  DeclarationRef.declaration authoritySecondDeclarationId authoritySignature

def authorityFirstPattern : ApplicationPatternId :=
  ApplicationPatternId.pattern (Nat.succ Nat.zero)
def authoritySecondPattern : ApplicationPatternId :=
  ApplicationPatternId.pattern (Nat.succ (Nat.succ Nat.zero))
def authorityOtherPattern : ApplicationPatternId :=
  ApplicationPatternId.pattern (Nat.succ (Nat.succ (Nat.succ Nat.zero)))

def authorityIdentityArguments (args : Args Bool) : Args Bool := args

def authorityFirstHead : ProjectionHead Bool :=
  ProjectionHead.exact authorityDeclaration authorityFirstPattern
    false (Nat.succ Nat.zero) authorityIdentityArguments
def authoritySecondHead : ProjectionHead Bool :=
  ProjectionHead.exact authoritySecondDeclaration authoritySecondPattern
    true Nat.zero authorityIdentityArguments

def authorityProjectionMap : ProjectionMap Bool :=
  ProjectionMap.cons authorityFirstHead
    (ProjectionMap.cons authoritySecondHead ProjectionMap.nil)
def authorityDuplicateProjectionMap : ProjectionMap Bool :=
  ProjectionMap.cons authorityFirstHead
    (ProjectionMap.cons authorityFirstHead ProjectionMap.nil)

def authorityProjectionMapIdentity : ProjectionMapIdentity :=
  projectionMapIdentity Bool authorityProjectionMap

def authorityProjectionIdentityWithFirst
    (declaration : DeclarationRef)
    (patternId : ApplicationPatternId)
    (selector : Nat) : ProjectionMapIdentity :=
  ProjectionMapIdentity.cons
    (ProjectionBindingRef.binding declaration patternId selector)
    (ProjectionMapIdentity.cons
      (ProjectionBindingRef.binding
        authoritySecondDeclaration authoritySecondPattern Nat.zero)
      ProjectionMapIdentity.nil)

def trueProjectionMapContext (_ : ProjectionValues Bool) : BoolExpr :=
  BoolExpr.iteNode (BoolExpr.lit true) (BoolExpr.lit true) (BoolExpr.lit false)
def falseProjectionMapContext (_ : ProjectionValues Bool) : BoolExpr :=
  BoolExpr.lit false

def authoritySubject : ProjectionSubject Bool :=
  ProjectionSubject.exact
    authorityCurrentStamp authorityCurrentQueryEpoch authorityRoots
    authorityProjectionMap authorityScopeDepth authorityTermCount
    (fun _ => true) trueProjectionMapContext

def authorityOtherSubject : ProjectionSubject Bool :=
  ProjectionSubject.exact
    authorityCurrentStamp authorityCurrentQueryEpoch authorityChangedRoots
    authorityProjectionMap authorityScopeDepth authorityTermCount
    (fun _ => true) trueProjectionMapContext

def falseSemanticSubject : ProjectionSubject Bool :=
  ProjectionSubject.exact
    authorityCurrentStamp authorityCurrentQueryEpoch authorityRoots
    authorityProjectionMap authorityScopeDepth authorityTermCount
    (fun _ => true) falseProjectionMapContext

def duplicateMapSubject : ProjectionSubject Bool :=
  ProjectionSubject.exact
    authorityCurrentStamp authorityCurrentQueryEpoch authorityRoots
    authorityDuplicateProjectionMap authorityScopeDepth authorityTermCount
    (fun _ => true) trueProjectionMapContext

def emptyMapSubject : ProjectionSubject Bool :=
  ProjectionSubject.exact
    authorityCurrentStamp authorityCurrentQueryEpoch authorityRoots
    ProjectionMap.nil authorityScopeDepth authorityTermCount
    (fun _ => true) trueProjectionMapContext

def authorityFreeInventory : LiveDeclarationInventory :=
  LiveDeclarationInventory.cons
    authorityDeclaration DeclarationKind.freeUninterpreted
    (LiveDeclarationInventory.cons
      authoritySecondDeclaration DeclarationKind.freeUninterpreted
      LiveDeclarationInventory.nil)

def authorityInventoryWithFirst
    (declaration : DeclarationRef)
    (kind : DeclarationKind) : LiveDeclarationInventory :=
  LiveDeclarationInventory.cons declaration kind
    (LiveDeclarationInventory.cons
      authoritySecondDeclaration DeclarationKind.freeUninterpreted
      LiveDeclarationInventory.nil)

def currentFreeSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityRoots
    authorityFreeInventory

def exactAuthoredQuery : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero

def authoritySemanticEvidence : CheckedProjectionSemantics Bool authoritySubject :=
  CheckedProjectionSemantics.certify
    authorityCurrentStamp authorityCurrentQueryEpoch authorityRoots
    authorityProjectionMap authorityScopeDepth authorityTermCount
    (fun _ => true) trueProjectionMapContext rfl rfl
    (fun _ _ => rfl)

def authorityOtherSemanticEvidence :
    CheckedProjectionSemantics Bool authorityOtherSubject :=
  CheckedProjectionSemantics.certify
    authorityCurrentStamp authorityCurrentQueryEpoch authorityChangedRoots
    authorityProjectionMap authorityScopeDepth authorityTermCount
    (fun _ => true) trueProjectionMapContext rfl rfl
    (fun _ _ => rfl)

def currentFreeBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject currentFreeSource
def exactAuthoredPlainHardQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject exactAuthoredQuery

theorem current_free_binding_accepts : currentFreeBinding = true := rfl
theorem exact_authored_plain_hard_query_accepts :
    exactAuthoredPlainHardQuery = true := rfl

def currentFreeBindingEvidence :
    CheckedSourceBinding Bool authoritySubject currentFreeSource :=
  CheckedSourceBinding.certify current_free_binding_accepts

def exactAuthoredQueryEvidence :
    CheckedAuthoredPlainHardQuery Bool authoritySubject exactAuthoredQuery :=
  CheckedAuthoredPlainHardQuery.certify exact_authored_plain_hard_query_accepts

def projection_ite_authority_witness :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource exactAuthoredQuery
    authoritySemanticEvidence currentFreeBindingEvidence exactAuthoredQueryEvidence

def projection_ite_authority_witness_has_model :
    SubjectHasModel Bool authoritySubject :=
  projection_sat_authority_has_model
    Bool authoritySubject currentFreeSource exactAuthoredQuery
    projection_ite_authority_witness

-- Invalid live-source states.
def missingSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityRoots
    LiveDeclarationInventory.nil
def staleSource : LiveSourceState :=
  LiveSourceState.snapshot authorityStaleStamp authorityRoots
    authorityFreeInventory
def foreignSource : LiveSourceState :=
  LiveSourceState.snapshot authorityForeignStamp authorityRoots
    authorityFreeInventory
def changedRootSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityChangedRoots
    authorityFreeInventory
def replacementDeclarationSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityRoots
    (authorityInventoryWithFirst
      authorityReplacementDeclaration DeclarationKind.freeUninterpreted)
def changedSignatureSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityRoots
    (authorityInventoryWithFirst
      authorityWrongSignatureDeclaration DeclarationKind.freeUninterpreted)
def definedDeclarationSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityRoots
    (authorityInventoryWithFirst authorityDeclaration DeclarationKind.defined)
def adoptedDeclarationSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityRoots
    (authorityInventoryWithFirst
      authorityDeclaration DeclarationKind.adoptedDefinition)
def datatypeConstructorSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityRoots
    (authorityInventoryWithFirst
      authorityDeclaration DeclarationKind.datatypeConstructor)
def datatypeSelectorSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityRoots
    (authorityInventoryWithFirst
      authorityDeclaration DeclarationKind.datatypeSelector)
def datatypeTesterSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityRoots
    (authorityInventoryWithFirst
      authorityDeclaration DeclarationKind.datatypeTester)
def theoryDeclarationSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityRoots
    (authorityInventoryWithFirst authorityDeclaration DeclarationKind.theory)
def internalDeclarationSource : LiveSourceState :=
  LiveSourceState.snapshot authorityCurrentStamp authorityRoots
    (authorityInventoryWithFirst
      authorityDeclaration DeclarationKind.solverInternal)

def missingSourceBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject missingSource
def staleSourceBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject staleSource
def foreignSourceBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject foreignSource
def changedRootBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject changedRootSource
def replacementDeclarationBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject replacementDeclarationSource
def changedSignatureBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject changedSignatureSource
def definedDeclarationBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject definedDeclarationSource
def adoptedDeclarationBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject adoptedDeclarationSource
def datatypeConstructorBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject datatypeConstructorSource
def datatypeSelectorBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject datatypeSelectorSource
def datatypeTesterBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject datatypeTesterSource
def theoryDeclarationBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject theoryDeclarationSource
def internalDeclarationBinding : Bool :=
  sourceProjectionBindingAccepted Bool authoritySubject internalDeclarationSource

theorem missing_source_binding_rejected : missingSourceBinding = false := rfl
theorem stale_source_binding_rejected : staleSourceBinding = false := rfl
theorem foreign_source_binding_rejected : foreignSourceBinding = false := rfl
theorem changed_root_binding_rejected : changedRootBinding = false := rfl
theorem replacement_declaration_binding_rejected :
    replacementDeclarationBinding = false := rfl
theorem changed_signature_binding_rejected : changedSignatureBinding = false := rfl
theorem defined_declaration_binding_rejected :
    definedDeclarationBinding = false := rfl
theorem adopted_declaration_binding_rejected :
    adoptedDeclarationBinding = false := rfl
theorem datatype_constructor_binding_rejected :
    datatypeConstructorBinding = false := rfl
theorem datatype_selector_binding_rejected : datatypeSelectorBinding = false := rfl
theorem datatype_tester_binding_rejected : datatypeTesterBinding = false := rfl
theorem theory_declaration_binding_rejected : theoryDeclarationBinding = false := rfl
theorem internal_declaration_binding_rejected :
    internalDeclarationBinding = false := rfl

-- Invalid query states preserve the visible formula while changing independent
-- authenticated records. The repeated-query case changes only
-- `QueryAuthorityEpoch`; scope-depth and term-count cases each change one field.
def authorityReplacementProjectionMapIdentity : ProjectionMapIdentity :=
  authorityProjectionIdentityWithFirst
    authorityReplacementDeclaration authorityFirstPattern (Nat.succ Nat.zero)
def authorityWrongResultProjectionMapIdentity : ProjectionMapIdentity :=
  authorityProjectionIdentityWithFirst
    authorityWrongSignatureDeclaration authorityFirstPattern (Nat.succ Nat.zero)
def authorityWrongArgumentProjectionMapIdentity : ProjectionMapIdentity :=
  authorityProjectionIdentityWithFirst
    authorityWrongArgumentDeclaration authorityFirstPattern (Nat.succ Nat.zero)
def authorityWrongArgumentOrderProjectionMapIdentity : ProjectionMapIdentity :=
  authorityProjectionIdentityWithFirst
    authorityWrongArgumentOrderDeclaration authorityFirstPattern (Nat.succ Nat.zero)
def authorityWrongArityProjectionMapIdentity : ProjectionMapIdentity :=
  authorityProjectionIdentityWithFirst
    authorityWrongArityDeclaration authorityFirstPattern (Nat.succ Nat.zero)
def authorityWrongSelectorProjectionMapIdentity : ProjectionMapIdentity :=
  authorityProjectionIdentityWithFirst
    authorityDeclaration authorityFirstPattern Nat.zero
def authorityWrongPatternProjectionMapIdentity : ProjectionMapIdentity :=
  authorityProjectionIdentityWithFirst
    authorityDeclaration authorityOtherPattern (Nat.succ Nat.zero)

def staleSourceEpochQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityStaleStamp authorityRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def repeatedQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityPreviousQueryEpoch authorityCurrentStamp authorityRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def changedRootsQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityChangedRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def reorderedRootsQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityReorderedRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def shortRootsQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityShortRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def longRootsQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityLongRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def replacementDeclarationQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityReplacementProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def changedResultSignatureQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityWrongResultProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def changedArgumentSignatureQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityWrongArgumentProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def reorderedArgumentSignatureQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityWrongArgumentOrderProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def changedAritySignatureQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityWrongArityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def changedSelectorQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityWrongSelectorProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def changedPatternQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityWrongPatternProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def changedScopeDepthQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityProjectionMapIdentity authorityChangedScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def changedTermCountQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityChangedTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero Nat.zero
def assumptionQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    (Nat.succ Nat.zero) Nat.zero Nat.zero Nat.zero
def parsedSoftQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero (Nat.succ Nat.zero) Nat.zero Nat.zero
def nativeSoftQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero (Nat.succ Nat.zero) Nat.zero
def objectiveQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSat
    Nat.zero Nat.zero Nat.zero (Nat.succ Nat.zero)
def emptyAssumingQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.authoredCheckSatAssuming
    Nat.zero Nat.zero Nat.zero Nat.zero
def genericExecutorQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.genericExecutor
    Nat.zero Nat.zero Nat.zero Nat.zero
def internalSolverQueryState : AuthoredQueryState :=
  AuthoredQueryState.capture
    authorityCurrentQueryEpoch authorityCurrentStamp authorityRoots
    authorityProjectionMapIdentity authorityScopeDepth authorityTermCount
    QueryDispatch.internalSolver
    Nat.zero Nat.zero Nat.zero Nat.zero

def staleSourceEpochQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject staleSourceEpochQueryState
def repeatedQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject repeatedQueryState
def changedRootsQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject changedRootsQueryState
def reorderedRootsQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject reorderedRootsQueryState
def shortRootsQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject shortRootsQueryState
def longRootsQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject longRootsQueryState
def replacementDeclarationQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject replacementDeclarationQueryState
def changedResultSignatureQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject changedResultSignatureQueryState
def changedArgumentSignatureQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject changedArgumentSignatureQueryState
def reorderedArgumentSignatureQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject reorderedArgumentSignatureQueryState
def changedAritySignatureQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject changedAritySignatureQueryState
def changedSelectorQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject changedSelectorQueryState
def changedPatternQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject changedPatternQueryState
def changedScopeDepthQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject changedScopeDepthQueryState
def changedTermCountQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject changedTermCountQueryState
def assumptionQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject assumptionQueryState
def parsedSoftQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject parsedSoftQueryState
def nativeSoftQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject nativeSoftQueryState
def objectiveQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject objectiveQueryState
def emptyAssumingQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject emptyAssumingQueryState
def genericExecutorQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject genericExecutorQueryState
def internalSolverQuery : Bool :=
  plainHardQueryAccepted Bool authoritySubject internalSolverQueryState

theorem stale_source_epoch_query_rejected : staleSourceEpochQuery = false := rfl
theorem repeated_identical_query_epoch_rejected : repeatedQuery = false := rfl
theorem changed_roots_query_rejected : changedRootsQuery = false := rfl
theorem reordered_roots_query_rejected : reorderedRootsQuery = false := rfl
theorem short_roots_query_rejected : shortRootsQuery = false := rfl
theorem long_roots_query_rejected : longRootsQuery = false := rfl
theorem replacement_declaration_query_rejected :
    replacementDeclarationQuery = false := rfl
theorem changed_result_signature_query_rejected :
    changedResultSignatureQuery = false := rfl
theorem changed_argument_signature_query_rejected :
    changedArgumentSignatureQuery = false := rfl
theorem reordered_argument_signature_query_rejected :
    reorderedArgumentSignatureQuery = false := rfl
theorem changed_arity_signature_query_rejected :
    changedAritySignatureQuery = false := rfl
theorem changed_selector_query_rejected : changedSelectorQuery = false := rfl
theorem changed_pattern_query_rejected : changedPatternQuery = false := rfl
theorem changed_scope_depth_query_rejected : changedScopeDepthQuery = false := rfl
theorem changed_term_count_query_rejected : changedTermCountQuery = false := rfl
theorem assumption_query_rejected : assumptionQuery = false := rfl
theorem parsed_soft_query_rejected : parsedSoftQuery = false := rfl
theorem native_soft_query_rejected : nativeSoftQuery = false := rfl
theorem objective_query_rejected : objectiveQuery = false := rfl
theorem empty_assuming_query_rejected : emptyAssumingQuery = false := rfl
theorem generic_executor_query_rejected : genericExecutorQuery = false := rfl
theorem internal_solver_query_rejected : internalSolverQuery = false := rfl
