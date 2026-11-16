-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- Trust.Model.Tlc: THE semantics, TLC's item machine, written once (Beyond-TLA design
-- 10-executable-semantics.md, "Executable values" 10:219-257 and "The item machine and its
-- three evaluation modes" 10:259-310). Clean source, served to ty by
-- crates/trust-model-prelude and kernel-checked by crates/trust-spec-temporal.
--
-- This revision (lane row B1A-14a) is the skeleton:
--   * the executable values Ctx, SetGen and XVal (10:230-249) in one mutual block, Ctx the
--     single-constructor fallback with projection definitions (B1A-D21: Clean refuses a
--     structure in a mutual block), and `abbrev Frame` after the block (B1A-02a);
--   * their well-formedness, XVal.Wf, SetGen.Wf and Ctx.Wf (10:250-256), with Bool
--     deciders beside them;
--   * the block of B1A-D07: the tagged `Job` and `Out`, the non-recursive `Tlc.step`, which
--     reaches every recursive call through its `go` binder, and `Tlc.run`, a `Nat.rec` over
--     fuel; the nine design functions are wrappers with exactly the signatures of
--     10:285-298 (`evalX`, `force`, `applyX`, `memX`, `enumNext`, `enumAll`, `tlcEnumF`,
--     `tlcEnabledF`, `tlcHoldsF`);
--   * the six forcing rules `Tlc.rule.*`, each implementing only TLC's behaviour (B1A-D36):
--     no Bool flag, no alternative branch. The variant preludes of FX-prelude-variants
--     (B1A-46) replace one rule's definition each, so each rule's signature takes what its
--     wrong alternative needs (a forcing callback) and its real body ignores it.
-- Every case of the block's steps returns `Tlc.todo` (`Fail.unmodeled Code.todo`) until
-- the rows that fill it (B1A-14b core evaluation, 15 PrimOps, 16-17b laziness, 18 generate
-- mode, 19 enabled and pair modes); B1A-19 leaves no `Code.todo` in this file.
--
-- Row B1A-15 fills the `op` case: the operands left to right, then `PrimOp.evalV` over
-- their values (B1A-D12, B1A-D44, B1A-D96, B1A-D97; a lazy operand stays `Tlc.todo` for
-- B1A-16/17), and makes a quantifier with no binder `Tlc.illFormed` (B1A-D95 amended).
--
-- Row B1A-16 fills forcing-table rows 1-6 (10:612-617; the laziness I section below): the
-- quant qFn case (`Tlc.qFnX`), `Tlc.stepForce` on a `lazyFn` and an `fnX`, `Tlc.stepApplyX`,
-- `Tlc.stepMemX` on a forced set (the lazy sets are B1A-17a's), `Tlc.rhsX` (keepLazy's reset),
-- and the operand rows of func.apply, seq.index, tuple.get, func.domain, func.except,
-- rec.get, rec.with, tuple.new, rec.new, seq.head and seq.tail (`Tlc.opLazyX`).
--
-- Row B1A-14b fills `Tlc.stepEvalX`'s core cases (lit, cur, nxt, bvar, pool, ite, caseOf,
-- letLazy, app, and quant over `val` sets: qEx, qAll, qChoose, qFilter, qMap) and
-- `Tlc.stepForce` on a forced `val`, and defines `Frame.ofState` and `evalE` (10:299-302).
-- Still `Tlc.todo` after B1A-16: a lazy binder domain and a filter over a non-Reducible
-- base (B1A-17a), forcing or enumerating a lazy set and every other PrimOp on a lazy operand
-- (B1A-17a/17b), `enabled` (B1A-19), and the item machine's steps (B1A-18, B1A-19).
--
-- Recursors (B1A-D70): Ctx, SetGen and XVal share one recursor family of ten motives, one
-- per block type and one per distinct nested instantiation, in Clean's discovery order:
-- Ctx, SetGen, XVal, List (Option XVal), List SetGen, List (Nat × SetGen),
-- List (Value × XVal), Option XVal, Nat × SetGen, Value × XVal (measured by B1A-14a: the
-- count by `model_prelude_kernel::syntax_recursor_motives`, the order by sanity
-- tlc_skeleton.lean's `motive_order`, which gives each motive its own type). Their casesOn
-- takes every motive too, then the major premise, then every
-- constructor's minor of all ten types. Job and Out are plain inductives (one motive).

namespace Trust
namespace Model

-- ---- Executable values (10:230-249) ----
--
-- Only the evaluator, a lazy closure and the item machine's partial successor hold these;
-- states, literals, SpecDigest, the Shape codecs and every claim hold `Value` only (10:224).
--   Ctx      quantifier-bound values (canonical) and the partial successor at capture time.
--   SetGen   a set TLC does not normalize (a non-`Reducible` set value) over lazy operands;
--            there is no set-of-all generator (TLC builds SetOfAll eagerly, 10:236).
--   XVal     a forced canonical `val`, an unforced function constructor `lazyFn` (one
--            unforced domain per binder, the body, its captured Ctx), a tuple or record
--            `fnX` holding lazy entries, or a `lazySet`.
mutual
inductive Ctx where
  | mk : List Value → List (Option XVal) → Ctx
inductive SetGen where
  | ofVal  : Value → SetGen
  | subset : SetGen → SetGen
  | fnSet  : SetGen → SetGen → SetGen
  | prod   : List SetGen → SetGen
  | rcdSet : List (Nat × SetGen) → SetGen
  | filter : SetGen → Expr → Ctx → SetGen
inductive XVal where
  | val     : Value → XVal
  | lazyFn  : List SetGen → Expr → Ctx → XVal
  | fnX     : List (Value × XVal) → XVal
  | lazySet : SetGen → XVal
end

-- The primed slots of the partial successor (10:230): `none` = unassigned; length
-- `sp.vars`. Declared after the block it names (B1A-02a, frame_after_mutual.lean).
abbrev Frame := List (Option XVal)

-- ---- One-type dispatch on the block (every motive, B1A-D70) ----

-- `Ctx.elim c mk`: c's two fields.
def Ctx.elim {α : Type} (c : Ctx) (mk : List Value → List (Option XVal) → α) : α :=
  @Ctx.casesOn (fun _ => α) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) c
    mk
    (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ _ => 0)
    (fun _ => 0) (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ => 0)
    (fun _ _ => 0)
    (fun _ _ => 0)

-- `SetGen.elim g ...`: one minor per SetGen constructor.
def SetGen.elim {α : Type} (g : SetGen) (ofVal : Value → α) (subset : SetGen → α)
    (fnSet : SetGen → SetGen → α) (prod : List SetGen → α)
    (rcdSet : List (Prod Nat SetGen) → α) (filter : SetGen → Expr → Ctx → α) : α :=
  @SetGen.casesOn (fun _ => Nat) (fun _ => α) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) g
    (fun _ _ => 0)
    ofVal subset fnSet prod rcdSet filter
    (fun _ => 0) (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ => 0)
    (fun _ _ => 0)
    (fun _ _ => 0)

-- `XVal.elim x ...`: one minor per XVal constructor.
def XVal.elim {α : Type} (x : XVal) (val : Value → α) (lazyFn : List SetGen → Expr → Ctx → α)
    (fnX : List (Prod Value XVal) → α) (lazySet : SetGen → α) : α :=
  @XVal.casesOn (fun _ => Nat) (fun _ => Nat) (fun _ => α)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) x
    (fun _ _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ _ => 0)
    val lazyFn fnX lazySet
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ => 0)
    (fun _ _ => 0)
    (fun _ _ => 0)

-- The fields of the single-constructor Ctx (B1A-D21): the bound values and the frame.
def Ctx.env (c : Ctx) : List Value := Ctx.elim c (fun env _ => env)
def Ctx.post (c : Ctx) : Frame := Ctx.elim c (fun _ post => post)

-- `XVal.isReducible x`: x is a `val` holding a finite set, TLC's `Reducible` (a
-- SetEnumValue or an IntervalValue; 10:590). An `infSet` is not one, nor is anything lazy.
def XVal.isReducible (x : XVal) : Bool :=
  XVal.elim x
    (fun v => @Option.casesOn (List Value) (fun _ => Bool) (Value.asSet v) false (fun _ => true))
    (fun _ _ _ => false) (fun _ => false) (fun _ => false)

-- ---- Well-formedness of executable values (10:250-256) ----
--
-- The premise of every value lemma (10:562). `XVal.wfB`, `SetGen.wfB` and `Ctx.wfB` decide
-- it, structurally through the block's recursor (all ten motives, Bool):
--   val v                every value canonical (`Value.Canon`);
--   fnX ps               every key canonical, the keys strictly increasing in TLC's order,
--                        every entry well formed;
--   lazyFn ds e c        every domain well formed, c well formed, and e's indices in range
--                        with one binder per domain around c's bound values
--                        (`Spec.exprWf`: slots, bound variables, pool, definitions);
--   lazySet g            g well formed;
--   ofVal v              v canonical; subset, fnSet, prod, rcdSet: every operand well
--                        formed; filter g e c: g and c well formed, e's indices in range
--                        with one binder around c's bound values;
--   Ctx.mk env post      every bound value canonical, `post` of length `sp.vars`, every
--                        assigned slot well formed.
-- The Props are the deciders' `= true`, except `Ctx.Wf`, which is the design's text
-- (10:254-256, `Value.Canon v = true` for the design's coerced Bool, as Spec.StateWf);
-- `Ctx.wfB sp c = true` is equivalent to it (a B1b lemma), and it is what `XVal.wfB` reads
-- for a captured context.

-- `keysOfX ps`: the keys of an `fnX`, in order.
def keysOfX (ps : List (Prod Value XVal)) : List Value :=
  @List.rec (Prod Value XVal) (fun _ => List Value) []
    (fun p _ rest => List.cons (Prod.fst p) rest) ps

-- `XVal.wfB sp x`.
def XVal.wfB (sp : Spec) (x : XVal) : Bool :=
  @XVal.rec (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
    (fun _ => Bool) (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
    (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
    -- Ctx.mk
    (fun env post ihpost => Bool.and (Temporal.allB Value.Canon env)
      (Bool.and (Nat.beq (List.length post) sp.vars) ihpost))
    -- SetGen
    (fun v => Value.Canon v)
    (fun _ ih => ih)
    (fun _ _ iha ihb => Bool.and iha ihb)
    (fun _ ih => ih)
    (fun _ ih => ih)
    (fun _ e c ihg ihc => Bool.and ihg
      (Bool.and ihc (Spec.exprWf sp (Nat.succ (List.length (Ctx.env c))) e)))
    -- XVal
    (fun v => Value.Canon v)
    (fun ds e c ihds ihc => Bool.and ihds
      (Bool.and ihc (Spec.exprWf sp (Nat.add (List.length ds) (List.length (Ctx.env c))) e)))
    (fun ps ih => Bool.and ih (strictInc (keysOfX ps)))
    (fun _ ih => ih)
    -- List (Option XVal), List SetGen, List (Nat × SetGen), List (Value × XVal)
    true (fun _ _ ih ihs => Bool.and ih ihs)
    true (fun _ _ ih ihs => Bool.and ih ihs)
    true (fun _ _ ih ihs => Bool.and ih ihs)
    true (fun _ _ ih ihs => Bool.and ih ihs)
    -- Option XVal
    true (fun _ ih => ih)
    -- Nat × SetGen, Value × XVal
    (fun _ _ ih => ih)
    (fun k _ ih => Bool.and (Value.Canon k) ih)
    x

-- `SetGen.wfB sp g`: a lazy set is well formed exactly when its generator is (the
-- `lazySet` minor of `XVal.wfB` is its generator's).
def SetGen.wfB (sp : Spec) (g : SetGen) : Bool := XVal.wfB sp (XVal.lazySet g)

-- `Ctx.wfB sp c`: the same minors as `XVal.wfB`, through Ctx's recursor.
def Ctx.wfB (sp : Spec) (c : Ctx) : Bool :=
  @Ctx.rec (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
    (fun _ => Bool) (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
    (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
    (fun env post ihpost => Bool.and (Temporal.allB Value.Canon env)
      (Bool.and (Nat.beq (List.length post) sp.vars) ihpost))
    (fun v => Value.Canon v)
    (fun _ ih => ih)
    (fun _ _ iha ihb => Bool.and iha ihb)
    (fun _ ih => ih)
    (fun _ ih => ih)
    (fun _ e c ihg ihc => Bool.and ihg
      (Bool.and ihc (Spec.exprWf sp (Nat.succ (List.length (Ctx.env c))) e)))
    (fun v => Value.Canon v)
    (fun ds e c ihds ihc => Bool.and ihds
      (Bool.and ihc (Spec.exprWf sp (Nat.add (List.length ds) (List.length (Ctx.env c))) e)))
    (fun ps ih => Bool.and ih (strictInc (keysOfX ps)))
    (fun _ ih => ih)
    true (fun _ _ ih ihs => Bool.and ih ihs)
    true (fun _ _ ih ihs => Bool.and ih ihs)
    true (fun _ _ ih ihs => Bool.and ih ihs)
    true (fun _ _ ih ihs => Bool.and ih ihs)
    true (fun _ ih => ih)
    (fun _ _ ih => ih)
    (fun k _ ih => Bool.and (Value.Canon k) ih)
    c

-- `XVal.Wf sp x` (10:251-252).
def XVal.Wf (sp : Spec) (x : XVal) : Prop := XVal.wfB sp x = true

-- `SetGen.Wf sp g` (10:253).
def SetGen.Wf (sp : Spec) (g : SetGen) : Prop := SetGen.wfB sp g = true

-- `Ctx.Wf sp c` (10:254-256), the design's text.
def Ctx.Wf (sp : Spec) (c : Ctx) : Prop :=
  (∀ v, Temporal.Member v (Ctx.env c) → Value.Canon v = true) ∧
    List.length (Ctx.post c) = sp.vars ∧
    ∀ o, Temporal.Member o (Ctx.post c) → ∀ x, o = Option.some x → XVal.Wf sp x

-- ---- The forcing rules (B1A-D36) ----
--
-- Each implements ONLY TLC's behaviour (the forcing table, 10:612-632; how TLC decides
-- laziness, 10:586-594). A variant prelude of FX-prelude-variants (LEDGER) replaces one of
-- these definitions, same name and type, by its wrong alternative (B1A-46); the real
-- definitions carry no flag and no branch that only a variant takes. A callback parameter
-- (`frc`, the block's `force` at the caller's fuel; `memV`, membership in a forced set) is
-- there for that alternative: the real body never calls it. The rows that call a rule
-- (16, 17a, 18) may refine its signature before B1A-29b type-pins it.

-- Row 1 (10:590, 10:614): `[x \in S |-> e]` is materialized at construction exactly when
-- the control is not KeepLazy and every domain is `Reducible`; otherwise it is a `lazyFn`
-- over the unforced domains. `k` is the evaluation's keepLazy, `ds` the evaluated domains.
def Tlc.rule.materializeQFn (k : Bool) (ds : List XVal) : Bool :=
  Bool.and (Bool.not k) (Temporal.allB XVal.isReducible ds)

-- Row 1 (10:590, 10:614): a function constructor's domains are evaluated to XVals and
-- never forced or enumerated at construction (FcnLambdaValue keeps them, Tool.java
-- 2363-2367): the domains are kept as evaluated.
def Tlc.rule.forceCtorDomains (_frc : XVal → Res Value) (ds : List XVal) : Res (List XVal) :=
  Res.ok ds

-- Row 2 (10:591, 10:615): KeepLazy is reset to `Clear` at an item's right-hand side
-- (Tool.java:1361, 1366), whatever control the item machine was entered with.
def Tlc.rule.keepLazyReset (_k : Bool) : Bool := false

-- Generate mode (10:592, 10:620): a slot assignment binds its value into the frame
-- unforced; the frame is forced when the branch emits, never at the assignment.
def Tlc.rule.forceAtAssign (_frc : XVal → Res Value) (x : XVal) : Res XVal := Res.ok x

-- 10:628: a filter `{x \in S : P}` over a `Reducible` base is built eagerly, as a `val`;
-- over any other base it stays `SetGen.filter`, its predicate run per element reached.
def Tlc.rule.eagerFilter (base : XVal) : Bool := XVal.isReducible base

-- 10:622: `v \in S` for a non-filter `lazySet` S is answered pointwise by kind (SUBSET
-- elementwise, `[S -> T]` domain then values, `\X` componentwise, a record set fieldwise),
-- never by forcing S: the answer is the pointwise one, `pointwise`.
def Tlc.rule.memByForcing (_frc : XVal → Res Value) (_memV : Value → Value → Res Bool)
    (pointwise : Res Bool) (_x : XVal) (_v : Value) : Res Bool :=
  pointwise

-- ---- The block (B1A-D07; 10:264-298) ----
--
-- One tagged job per design function, its arguments after the Spec and the fuel, and one
-- answer per result type. `Tlc.run sp n` is the block at fuel n: a `Nat.rec` whose step is
-- the non-recursive `Tlc.step sp go`, `go` being the block at fuel n - 1; fuel 0 answers
-- `Fail.fuel`, a resource result, never a verdict (10:98). Fuel decreases per nesting
-- depth of calls, not per element (B1A-D07).
inductive Job where
  | evalX       : Bool → List Value → State → Frame → Expr → Job
  | force       : State → XVal → Job
  | applyX      : Bool → State → XVal → Value → Job
  | memX        : State → XVal → Value → Job
  | enumNext    : State → SetGen → Nat → Job
  | enumAll     : State → SetGen → Job
  | tlcEnumF    : List Value → Act → State → Job
  | tlcEnabledF : List Value → Act → State → Job
  | tlcHoldsF   : List Value → Act → State → State → Job

inductive Out where
  | xval   : XVal → Out
  | value  : Value → Out
  | bool   : Bool → Out
  | next   : Option (Value × Nat) → Out
  | values : List Value → Out
  | states : List State → Out

-- `Tlc.mismatch`: the answer of a projection below to an `Out` of another result type.
-- `Tlc.step` answers each job with its own result type, so this is unreachable; were it
-- reached (a prelude defect), it is `Fail.fuel`: a resource result, never a TLC error or a
-- verdict, and excluded by every fuel-monotonicity statement (TH-evalX_mono) (B1A-D92).
def Tlc.mismatch {α : Type} : Res α := Res.error Fail.fuel

-- `Tlc.todo`: a case of the block not yet filled (B1A-14a's skeleton). B1A-19 leaves no
-- `Code.todo` in this file and B1A-25 none in the prelude.
def Tlc.todo {α : Type} : Res α := Res.error (Fail.unmodeled Code.todo)

-- The answer of each result type, else `Tlc.mismatch`.
def Out.asXVal (o : Out) : Res XVal :=
  @Out.casesOn (fun _ => Res XVal) o (fun x => Res.ok x) (fun _ => Tlc.mismatch)
    (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch)
def Out.asValue (o : Out) : Res Value :=
  @Out.casesOn (fun _ => Res Value) o (fun _ => Tlc.mismatch) (fun v => Res.ok v)
    (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch)
def Out.asBool (o : Out) : Res Bool :=
  @Out.casesOn (fun _ => Res Bool) o (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch)
    (fun b => Res.ok b) (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch)
def Out.asNext (o : Out) : Res (Option (Prod Value Nat)) :=
  @Out.casesOn (fun _ => Res (Option (Prod Value Nat))) o (fun _ => Tlc.mismatch)
    (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch) (fun n => Res.ok n) (fun _ => Tlc.mismatch)
    (fun _ => Tlc.mismatch)
def Out.asValues (o : Out) : Res (List Value) :=
  @Out.casesOn (fun _ => Res (List Value)) o (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch)
    (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch) (fun vs => Res.ok vs) (fun _ => Tlc.mismatch)
def Out.asStates (o : Out) : Res (List State) :=
  @Out.casesOn (fun _ => Res (List State)) o (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch)
    (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch) (fun _ => Tlc.mismatch) (fun ss => Res.ok ss)

-- The block's recursive calls: `go` on the tagged job, then the answer's projection. The
-- steps below call each other only through these.
def Tlc.goEvalX (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (e : Expr) : Res XVal :=
  Res.bind (go (Job.evalX k env s p e)) Out.asXVal
def Tlc.goForce (go : Job → Res Out) (s : State) (x : XVal) : Res Value :=
  Res.bind (go (Job.force s x)) Out.asValue
def Tlc.goApplyX (go : Job → Res Out) (k : Bool) (s : State) (f : XVal) (a : Value) : Res XVal :=
  Res.bind (go (Job.applyX k s f a)) Out.asXVal
def Tlc.goMemX (go : Job → Res Out) (s : State) (x : XVal) (v : Value) : Res Bool :=
  Res.bind (go (Job.memX s x v)) Out.asBool
def Tlc.goEnumNext (go : Job → Res Out) (s : State) (g : SetGen) (i : Nat) :
    Res (Option (Prod Value Nat)) :=
  Res.bind (go (Job.enumNext s g i)) Out.asNext
def Tlc.goEnumAll (go : Job → Res Out) (s : State) (g : SetGen) : Res (List Value) :=
  Res.bind (go (Job.enumAll s g)) Out.asValues
def Tlc.goEnumF (go : Job → Res Out) (env : List Value) (a : Act) (s : State) :
    Res (List State) :=
  Res.bind (go (Job.tlcEnumF env a s)) Out.asStates
def Tlc.goEnabledF (go : Job → Res Out) (env : List Value) (a : Act) (s : State) : Res Bool :=
  Res.bind (go (Job.tlcEnabledF env a s)) Out.asBool
def Tlc.goHoldsF (go : Job → Res Out) (env : List Value) (a : Act) (s t : State) : Res Bool :=
  Res.bind (go (Job.tlcHoldsF env a s t)) Out.asBool

-- ---- Core evaluation (B1A-14b; 10:130-145, 10:264-302, 10:586-632) ----
--
-- What each core case of `evalX` does, with the TLC 94d0c50 behaviour it follows (the
-- probes are ty reports/perf/2026-10-09-beyond-tla-b1a/core-probes/, run on the jar of
-- record; sanity tlc_core.lean cites each one):
--   lit v          the forced value v.
--   cur n          slot n of the state s, forced.
--   nxt n          slot n of the primed frame, as bound (possibly lazy); an unassigned slot
--                  raises `unassignedPrime` (10:275, 10:97).
--   bvar j         the quantifier-bound value j (`env`, innermost first; B1A-D15).
--   pool i         pool entry i, evaluated at use (10:135), in a closed environment (env
--                  []; the pool is constant-level, B1A-D90), keepLazy inherited (10:615).
--   ite c t e      c's value must be a forced Boolean, else `typeErr` (TLC's IF); then
--                  the chosen arm only, keepLazy inherited.
--   caseOf as o    the guards in order, each a forced Boolean or `typeErr`; the first TRUE
--                  guard's arm; none: OTHER if present, else `caseNoMatch`. No guard after
--                  the first TRUE one is read.
--   letLazy e b    by substitution (10:168, 10:276-277): `Expr.subst [e] b`, so an unread
--                  definition is never evaluated (TLC's LET is by need).
--   app i as       by-name substitution of the actuals into definition i's body
--                  (`Expr.subst as body`), so an unread actual is never evaluated (TLC binds
--                  an operator's arguments as LazyValues).
--   quant          TLC's ContextEnumerator (10:142, Tool.contexts): EVERY domain is
--                  evaluated (keepLazy inherited: contexts passes its control to eval) and
--                  converted to its elements in TLC's normalized order (Enumerable.elements
--                  (NORMALIZED); a `val` set's elements are already canonical), in binder
--                  order, before any body runs, even after an empty one; the contexts are
--                  the product of the element lists, FIRST binder fastest; a context's
--                  values are bound so that the last binder is `bvar 0` (B1A-D15). A domain
--                  that is not a set is `notEnumerable`: only TLC's set values are
--                  Enumerable (javap of the jar of record), so a scalar, a model value, a
--                  function (forced or lazy) and an infinite `infSet` all raise there.
--                  qEx: the first context whose body is TRUE gives TRUE, else FALSE.
--                  qAll: the first FALSE gives FALSE, else TRUE.
--                  qChoose: one binder; the first element (canonical order) whose body is
--                  TRUE, else `chooseFailed`.
--                  qFilter: one binder; over a Reducible base (`Tlc.rule.eagerFilter`) the
--                  predicate runs at every element in order and the kept elements are the
--                  result set (a subsequence of a canonical list is canonical); any other
--                  base is a lazy `SetGen.filter` (B1A-17a).
--                  qMap: the body at every context in order, each a forced value, then
--                  TLC's normalization (`normSet`, so its first comparison error is TLC's);
--                  a lazy element is `unmodeled lazy.soa-elem` (10:629, B1A-D22).
--                  A body or predicate that is not a forced Boolean is `typeErr` (TLC: "TLC
--                  expected a boolean value", and the filter's own text).
-- A term outside the presentation's well-formedness is `Tlc.illFormed` (B1A-D95).

-- `Tlc.illFormed`: what a term the design's well-formedness excludes evaluates to (B1A-D95):
-- an index outside its list (a slot outside the state or the frame, a bound variable outside
-- `env`, a pool entry or definition the Spec lacks), a call with other than its definition's
-- number of actuals, a CHOOSE or set filter with other than one binder. `Fail.fuel`, as
-- `Tlc.mismatch` (B1A-D92): never a TLC class or a verdict, and `Spec.wf` (with
-- `Spec.StateWf` for the state and the frame) excludes every case (its site tag 8 the
-- binder count).
def Tlc.illFormed {α : Type} : Res α := Res.error Fail.fuel

-- `Tlc.nth xs i`: the i-th element of xs (from 0), or `none` past the end.
def Tlc.nth {α : Type} (xs : List α) : Nat → Option α :=
  @List.rec α (fun _ => Nat → Option α)
    (fun _ => Option.none)
    (fun x _ go i => @Nat.rec (fun _ => Option α) (Option.some x) (fun i' _ => go i') i)
    xs

-- `Tlc.at xs i k`: k on the i-th element of xs; `Tlc.illFormed` past the end.
def Tlc.at {α β : Type} (xs : List α) (i : Nat) (k : α → Res β) : Res β :=
  @Option.casesOn α (fun _ => Res β) (Tlc.nth xs i) Tlc.illFormed k

-- `XVal.asBool x`: the Boolean of a forced `val (bool b)`; `none` for anything else.
def XVal.asBool (x : XVal) : Option Bool :=
  XVal.elim x (fun v => Value.asBool v) (fun _ _ _ => Option.none) (fun _ => Option.none)
    (fun _ => Option.none)

-- `Tlc.truth x`: TLC's Boolean test of an evaluated condition, guard, body or predicate: a
-- forced Boolean, else `typeErr`.
def Tlc.truth (x : XVal) : Res Bool :=
  @Option.casesOn Bool (fun _ => Res Bool) (XVal.asBool x) (Res.error Fail.typeErr)
    (fun b => Res.ok b)

-- `Tlc.ifB r yes no`: yes when r is TRUE, no when FALSE, r's error otherwise; the branch
-- not taken is never read.
def Tlc.ifB {α : Type} (r : Res Bool) (yes no : Res α) : Res α :=
  Res.bind r (fun b => @Bool.rec (fun _ => Res α) no yes b)

-- `Tlc.domainOf x`: the elements of an evaluated binder domain, in TLC's normalized order:
-- a `val` set's own (canonical) list; `notEnumerable` for any other `val` (Nat, Int, STRING
-- and Seq(S), which are UserValues, not Enumerable, included) and for a lazy or tuple
-- function; an `infSet fnSet` ([S -> T] with an infinite operand) is a SetOfFcnsValue, which
-- TLC enumerates ([PSetExFnSetEmptyDom]: `\E f \in [{} -> Nat] : f = <<>>` is TRUE), so it
-- is `Tlc.todo` with the lazy sets, which B1A-17a converts (B1A-15 repair round 1).
def Tlc.domainOf (x : XVal) : Res (List Value) :=
  XVal.elim x
    (fun v => @Option.casesOn (List Value) (fun _ => Res (List Value)) (Value.asSet v)
      (@Option.casesOn (Prod InfKind (List Value)) (fun _ => Res (List Value)) (Value.asInfSet v)
        (Res.error Fail.notEnumerable)
        (fun p => @Bool.rec (fun _ => Res (List Value)) (Res.error Fail.notEnumerable) Tlc.todo
          (Nat.beq (InfKind.tag (Prod.fst p)) 4)))
      (fun xs => Res.ok xs))
    (fun _ _ _ => Res.error Fail.notEnumerable)
    (fun _ => Res.error Fail.notEnumerable)
    (fun _ => Tlc.todo)

-- `Tlc.consEach d r`: a :: r for every a of d, in d's order.
def Tlc.consEach (d r : List Value) : List (List Value) :=
  @List.rec Value (fun _ => List (List Value)) []
    (fun a _ acc => List.cons (List.cons a r) acc) d

-- `Tlc.contexts ds`: TLC's contexts over the element lists ds = [d0, ..., dn-1], each a list
-- [x0, ..., xn-1] of one value per binder in binder order, FIRST binder fastest
-- (ContextEnumerator.nextElement advances enumerator 0 first); none when any di is empty.
def Tlc.contexts (ds : List (List Value)) : List (List Value) :=
  @List.rec (List Value) (fun _ => List (List Value))
    [[]]
    (fun d _ rest => @List.rec (List Value) (fun _ => List (List Value)) []
      (fun r _ acc => List.append (Tlc.consEach d r) acc) rest)
    ds

-- `Tlc.pushAll xs env`: the context values xs = [x0, ..., xn-1] bound over env, the last
-- binder innermost (`bvar 0` is xn-1, B1A-D15).
def Tlc.pushAll (xs env : List Value) : List Value :=
  @List.rec Value (fun _ => List Value → List Value)
    (fun acc => acc)
    (fun x _ go acc => go (List.cons x acc))
    xs env

-- `Tlc.evalDomains go k env s p ds`: every domain evaluated and converted, in order; the
-- first error wins.
def Tlc.evalDomains (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (ds : List Expr) : Res (List (List Value)) :=
  @List.rec Expr (fun _ => Res (List (List Value))) (Res.ok [])
    (fun d _ rest =>
      Res.bind (Res.bind (Tlc.goEvalX go k env s p d) Tlc.domainOf)
        (fun xs => Res.map (fun xss => List.cons xs xss) rest))
    ds

-- `Tlc.oneBinder ds k`: k on the only domain of a one-binder form (CHOOSE, a set filter);
-- `Tlc.illFormed` for any other number (B1A-D95).
def Tlc.oneBinder {α : Type} (ds : List Expr) (k : Expr → Res α) : Res α :=
  @List.casesOn Expr (fun _ => Res α) ds Tlc.illFormed
    (fun d rest => @List.casesOn Expr (fun _ => Res α) rest (k d) (fun _ _ => Tlc.illFormed))

-- `Tlc.bodyAt go k env s p body xs`: the Boolean value of a quantifier body at the context
-- values xs.
def Tlc.bodyAt (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (body : Expr) (xs : List Value) : Res Bool :=
  Res.bind (Tlc.goEvalX go k (Tlc.pushAll xs env) s p body) Tlc.truth

-- `Tlc.exLoop`: \E over the contexts, in order: TRUE at the first TRUE body, else FALSE.
def Tlc.exLoop (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (body : Expr) (cs : List (List Value)) : Res Bool :=
  @List.rec (List Value) (fun _ => Res Bool) (Res.ok false)
    (fun xs _ rest => Tlc.ifB (Tlc.bodyAt go k env s p body xs) (Res.ok true) rest)
    cs

-- `Tlc.allLoop`: \A over the contexts, in order: FALSE at the first FALSE body, else TRUE.
def Tlc.allLoop (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (body : Expr) (cs : List (List Value)) : Res Bool :=
  @List.rec (List Value) (fun _ => Res Bool) (Res.ok true)
    (fun xs _ rest => Tlc.ifB (Tlc.bodyAt go k env s p body xs) rest (Res.ok false))
    cs

-- `Tlc.chooseLoop`: CHOOSE over one binder's elements, in order: the first whose body is
-- TRUE, else `chooseFailed`.
def Tlc.chooseLoop (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (body : Expr) (xs : List Value) : Res Value :=
  @List.rec Value (fun _ => Res Value) (Res.error Fail.chooseFailed)
    (fun x _ rest => Tlc.ifB (Tlc.bodyAt go k env s p body [x]) (Res.ok x) rest)
    xs

-- `Tlc.filterLoop`: an eager filter's kept elements, the predicate run at every element in
-- order (the first error wins).
def Tlc.filterLoop (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (body : Expr) (xs : List Value) : Res (List Value) :=
  @List.rec Value (fun _ => Res (List Value)) (Res.ok [])
    (fun x _ rest => Res.bind (Tlc.bodyAt go k env s p body [x])
      (fun b => Res.map (fun ys => @Bool.rec (fun _ => List Value) ys (List.cons x ys) b) rest))
    xs

-- `Tlc.forcedElem x`: a set-of-all element must be a forced value (10:629): a lazy one is
-- `unmodeled lazy.soa-elem`.
def Tlc.forcedElem (x : XVal) : Res Value :=
  XVal.elim x (fun v => Res.ok v)
    (fun _ _ _ => Res.error (Fail.unmodeled Code.lazySoaElem))
    (fun _ => Res.error (Fail.unmodeled Code.lazySoaElem))
    (fun _ => Res.error (Fail.unmodeled Code.lazySoaElem))

-- `Tlc.mapLoop`: a set-of-all's elements before normalization, the body at every context in
-- order (the first error wins).
def Tlc.mapLoop (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (body : Expr) (cs : List (List Value)) : Res (List Value) :=
  @List.rec (List Value) (fun _ => Res (List Value)) (Res.ok [])
    (fun xs _ rest =>
      Res.bind (Res.bind (Tlc.goEvalX go k (Tlc.pushAll xs env) s p body) Tlc.forcedElem)
        (fun v => Res.map (fun vs => List.cons v vs) rest))
    cs

-- `Tlc.boolX b`: a forced Boolean as an executable value.
def Tlc.boolX (b : Bool) : XVal := XVal.val (Value.bool b)

-- `Fail.deferCmp f` (B1A-D96): a comparison error met while the EP normalizes a set it has
-- just built, or while it searches a set for a member, as the EP may report it: TLC's class
-- `incomparable` becomes the named refusal `unmodeled cmp.unpinned`; every other Fail is
-- unchanged. TLC builds a set enumeration, a set-of-all and `\cup` unnormalized and
-- normalizes them only when something sorts them (fingerprinting, `=`, enumeration,
-- Cardinality), and it searches an unnormalized set in source order with `equals` (the
-- element as receiver) but a normalized one by binary search with `compareTo` (the value
-- as receiver; ValueVec.search, javap of the jar of record). The EP holds every set
-- canonical (10:84) and so cannot tell which comparisons TLC makes: on the probes
-- primop-probes/ PSetInTmvFirst (`T \in {T, 1}` is TRUE) and PSoaTmv (TRUE) TLC answers
-- where an eager normalization raises `incomparable` (PSetEnumTmv raises it only at
-- fingerprinting), so a TLC class there would be a wrong outcome and the refusal never is.
def Fail.deferCmp (f : Fail) : Fail :=
  @Fail.casesOn (fun _ => Fail) f Fail.overflow Fail.notInDomain Fail.chooseFailed
    Fail.divZero Fail.typeErr Fail.caseNoMatch Fail.notCompletelySpecified
    Fail.notEnumerable Fail.assumeFalse (fun _ => f)
    (Fail.unmodeled Code.cmpUnpinned) Fail.unassignedPrime Fail.fuel (fun _ => f)

-- `Tlc.normDefer xs`: TLC's normalized set of xs (`normSet`), its comparison errors as the
-- EP reports them at construction (`Fail.deferCmp`, B1A-D96).
def Tlc.normDefer (xs : List Value) : Res (List Value) :=
  @Res.rec (List Value) (fun _ => Res (List Value)) (fun ys => Res.ok ys)
    (fun f => Res.error (Fail.deferCmp f)) (normSet xs)

-- `Tlc.someBinders ds r`: r, unless the binder list ds is empty, which is `Tlc.illFormed`:
-- no TLA+ quantifier, set-of-all or function constructor has zero binders, and `Spec.wf`
-- refuses one (site tag 8; B1A-D95 amended by B1A-15).
def Tlc.someBinders {α : Type} (ds : List Expr) (r : Res α) : Res α :=
  @List.casesOn Expr (fun _ => Res α) ds Tlc.illFormed (fun _ _ => r)

-- `Tlc.caseX`: CASE's arms in order, then OTHER, else `caseNoMatch`.
def Tlc.caseX (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (arms : List (Prod Expr Expr)) (other : Option Expr) : Res XVal :=
  @List.rec (Prod Expr Expr) (fun _ => Res XVal)
    (@Option.casesOn Expr (fun _ => Res XVal) other (Res.error Fail.caseNoMatch)
      (fun o => Tlc.goEvalX go k env s p o))
    (fun arm _ rest =>
      Tlc.ifB (Res.bind (Tlc.goEvalX go k env s p (Prod.fst arm)) Tlc.truth)
        (Tlc.goEvalX go k env s p (Prod.snd arm)) rest)
    arms

-- `Tlc.appX`: definition i applied by name to the actuals (B1A-D15).
def Tlc.appX (sp : Spec) (go : Job → Res Out) (k : Bool) (env : List Value) (s : State)
    (p : Frame) (i : Nat) (args : List Expr) : Res XVal :=
  Tlc.at sp.defs i (fun d =>
    @Bool.rec (fun _ => Res XVal) Tlc.illFormed
      (Tlc.goEvalX go k env s p (Expr.subst args (Prod.snd d)))
      (Nat.beq (Prod.fst d) (List.length args)))

-- ---- The PrimOp evaluator over materialized values (B1A-15) ----
--
-- `PrimOp.evalV m vs o` (design 10:156, 10:166; TASKS B1A-15) is the value of the PrimOp o
-- at the operand values vs, which `Tlc.stepEvalX`'s `op` case has evaluated left to right
-- with the inherited keepLazy (TLC evaluates every operand of a built-in or a Java override
-- before it applies it). The PrimOps that read a function have their lazy-operand rows in
-- `Tlc.opLazyX` (B1A-16); any other PrimOp with an operand that is not a forced `val` is
-- B1A-17a/17b's (`Tlc.todo` until then). A wrong number of operands is `Tlc.illFormed` (B1A-D95; Spec.wf
-- refuses it, site tag 9). The classes are TLC 94d0c50's, read from the probes of ty
-- reports/perf/2026-10-09-beyond-tla-b1a/primop-probes/ (`[Name]` below; their classes by
-- ../tools/causes.tsv, the row number given) and the batch-B integer probes (`probes/`).
-- Where a class is stated for an operand kind no probe ran, it rests on bytecode (javap of
-- the jar of record): a type test TLC applies alike to every kind it lists (BoolValue,
-- IntValue, StringValue and ModelValue implement neither FunctionValue nor Enumerable), or
-- the method named with it; an operand kind with neither is `Tlc.todo`. (B1A-15 repair
-- round 1: IsFiniteSet of a function, UNION of a non-SetEnum element and Cardinality of
-- [S -> T] had been carried from one probed kind to others; they are probed now.)
--   int.add/sub/mul/div/mod/neg, ^   the integer result ([PArithValues], [PIntPow]) of two
--          integer operands, else `typeErr` (TLC applies the
--          Naturals/Integers Java method only to IntValues: [PIntAddNonInt], [PIntAddFirst],
--          [PIntSubNonInt], [PIntMulNonInt], [PIntDivNonInt] (before the zero check),
--          [PIntModNonInt], [PIntNegNonInt], [PIntPowNonInt], row 160); then Value.lean's
--          arithmetic under the Spec's IntMode; 0^0 is `typeErr` ([PIntPowZeroZero], row
--          153; B1A-D85).
--   <, <=, >, >=   integers ([PIntCmp]), else `typeErr` ([PIntLtNonInt] ..., row 161).
--   natSuccU [a] = a + 1, natSatU [a, cap] = if a < cap then a + 1 else cap, both unbounded
--          whatever the IntMode (B1A-D12); a non-integer operand is `typeErr`, the class of
--          every other integer operator's (no TLA+ syntax produces them, 10:166).
--   value.eq, value.ne   `valueEq` with the left operand as receiver ([PNe]; [PNeStrInt],
--          row 200); value.as_bool   a Boolean, else `typeErr` (Q-K2-14).
--   assert [p, m]   TRUE when p is TRUE; any other p, a non-Boolean included, is
--          `assertFailed` ([PAssertTrue]; [PAssertNonBool], [PAssertFalseNonStr], row 50),
--          whose argument is m's token rank when m is a string and 0 otherwise (B1A-D97).
--   func.apply [f, a], seq.index, tuple.get i, rec.get fld   f a function: the value at the
--          key equal to a ([PFnApply], [PFnApplyRec], [PRecGet]); none: `notInDomain`
--          ([PFnApplyOut], [PFnApplyZero], [PFnApplyRecMissing], [PRecGetMissing], rows
--          101-103); a key of another kind than a: the named refusal (`keyEqWith`: TLC's
--          class depends on how it holds the function, [PFnApplyKind], [PRecGetTuple], rows
--          104, 105); f not a function: `typeErr` ([PFnApplyNonFn], [PRecGetNonFn], rows
--          163, 167).
--   func.except [f, x, v], rec.with fld [r, v]   the value at x replaced; x not a key: f
--          unchanged ([PFnExcept], [PFnExceptOut], [PRecWith], [PRecWithMissing]); f not a
--          function: `typeErr` ([PFnExceptNonFn], row 166).
--   func.domain   the keys as a set ([PFnDomain]); not a function: `typeErr` (row 164).
--   set.in [x, S]   `Prim.mem` below; set.enum: normalized ([PSetEnumNorm]); \cup, S \cup
--          {x}: both operands sets, normalized ([PSetUnion], [PSetInsert]), an operand that
--          is not a set `Tlc.todo` (TLC builds a lazy SetCupValue: [PSetUnionNonSetMem] is
--          TRUE, the error comes when it is enumerated, [PSetUnionNonSet], row 128; B1A-17b's
--          lazy.<op> code, B1A-D22); \cap, \: the first set filtered by membership in the
--          other ([PSetInter], [PSetDiff]; the other not a set: `typeErr`, [PSetInterNonSet],
--          [PSetDiffNonSet], row 162; \cap of a non-set first operand filters the second;
--          \ of one, and \cap of two, `Tlc.todo`: lazy SetDiffValue/SetCapValue); every
--          normalization through `Tlc.normDefer` (B1A-D96).
--   set.card   a set's size ([PSetCard]); Nat, Int, STRING, Seq(S) or a value that is not
--          a set: `notEnumerable` ([PSetCardInf], [PSetCardNonSet], row 126; FiniteSets.Cardinality
--          tests `instanceof Enumerable`, javap); [S -> T] with an infinite operand: TLC's
--          SetOfFcnsValue.size() (`Prim.cardFnSet`: 1 for an empty domain, 0 for an empty
--          range, 1 for a one-element range, else an infinite operand's size() raises `typeErr`,
--          row 160).
--   set.subseteq [S, T]   every element of S in T, the first FALSE deciding ([PSetSubseteq]).
--          TLC's opcode raises row 127's `notEnumerable` exactly when S is not Enumerable
--          (javap), and else calls S.isSubsetEq(T), which enumerates S and tests T.member:
--          so Nat, Int, STRING, Seq(S) (UserValues), a function and a scalar or model value
--          are `notEnumerable` ([PSetSubseteqNonSet] `3`, [PSetSubseteqNat], [PSetSubseteqInt],
--          [PSetSubseteqStr], [PSetSubseteqSeq], [PSetSubseteqTuple], [PSetSubseteqRec],
--          [PSetSubseteqMv]); [S -> T] with an infinite operand is a SetOfFcnsValue, which is
--          Enumerable, so it is `Tlc.todo` with the finite SetOfFcnsValue (B1A-17a/17b; TLC
--          enumerates it: [PSetSubseteqFnSetEmptyDom] `[{} -> Nat] \subseteq {<<>>}` TRUE,
--          [PSetSubseteqFnSetEmpty] FALSE, [PSetSubseteqFnSetEmptyRng] `[Nat -> {}] \subseteq
--          {}` TRUE, [PSetSubseteqFnSetEmptyDomInt] `incomparable` (row 200),
--          [PSetSubseteqFnSetNatRng] `notEnumerable` (row 119); B1A-15 repair round 2).
--   a..b   the integers from a to b, empty when a > b ([PSetRange]); not integers: `typeErr`
--          ([PSetRangeNonInt], row 160).
--   UNION S   S a set whose every element is a finite set: the union, normalized
--          ([PSetBigUnion]). TLC's UnionValue.union is eager only when S and every element
--          are SetEnumValues; `Value.set` also stands for TLC's IntervalValue, which TLC
--          keeps as a lazy UnionValue (`UNION {1..2}`): the values agree, and the EP's only
--          error on that path is `Tlc.normDefer`'s refusal (B1A-D96). An element that is
--          not a finite set, or S not a set: `Tlc.todo` (TLC builds a lazy UnionValue, whose
--          membership asks each element's member(): [PSetBigUnionNatMem] `0 \in UNION {Nat}`
--          is TRUE, [PSetBigUnionIntMem] `1 \in UNION {1}` raises row 162's typeErr, and
--          enumerating it raises [PSetBigUnionNonSet] row 129, [PSetBigUnionOfNonSet] row
--          124; B1A-17b's lazy.<op>).
--   IsFiniteSet   a set TRUE; a function TRUE ([PSetIsFiniteFn]: a tuple, a record, <<>>, a
--          FcnRcdValue); Nat, Int, STRING FALSE; Seq(S) TRUE exactly when S is the empty set
--          ([PSetIsFinite], [PSetIsFiniteInt], [PSetIsFiniteSeq], [PSetIsFiniteSeqOne]); a
--          Boolean, an integer, a string or a model value: `typeErr` ([PSetIsFiniteNonSet],
--          [PSetIsFiniteBool], [PSetIsFiniteStr], [PSetIsFiniteMv], [PSetIsFiniteTmv], row
--          160); Seq of an infinite set and [S -> T] with an infinite operand: `Tlc.todo`
--          (unprobed, B1A-15b). A function constructor is TRUE as well ([PSetIsFiniteLambda]
--          `IsFiniteSet([x \in {1, 2} |-> x])`), although FcnLambdaValue.isFinite raises
--          (javap): under Clear it is materialized at construction (B1A-16) and reaches
--          `PrimOp.evalV` as a forced function; a lazy one is a lazy operand (B1A-17b).
--   SUBSET, \X, [S -> T] over finite sets, record sets   lazy sets (SetGen), B1A-17a: `Tlc.todo`;
--          [S -> T] with an infinite operand is `infSet fnSet [S, T]` and Seq(S) is
--          `infSet seqOf [S]` (B1A-D44; Seq(3) is built without error, [PSeqSetNonSet]); a
--          quantifier over an `infSet fnSet` is `Tlc.todo` (`Tlc.domainOf`: TLC enumerates a
--          SetOfFcnsValue, [PSetExFnSetEmptyDom]; B1A-17a).
--   tuple.new, rec.new   `mkTuple`, `mkRecord` ([PArithValues], [PRecNew]).
--   Len, Head, Tail, Append, \o, SubSeq   on sequences (functions on 1..n: [PSeqLen],
--          [PSeqHeadTail], [PSeqAppend], [PSeqConcat], [PSeqSubSeq]); Head or Tail of <<>>:
--          `notInDomain` (row 110; [PSeqTailEmpty], row 111); SubSeq(s, m, n) is <<>> when
--          m > n, else m and n must lie in 1..Len(s), `notInDomain` ([PSeqSubSeqLow],
--          [PSeqSubSeqHigh], row 112); an operand that is not a sequence, or a bound that is
--          not an integer, `typeErr` ([PSeqLenNonSeq], [PSeqLenRec], [PSeqHeadNonSeq],
--          [PSeqTailNonSeq], [PSeqAppendNonSeq], [PSeqConcatNonSeq], [PSeqConcatFirstNonSeq],
--          [PSeqSubSeqNonSeq], [PSeqSubSeqNonInt], rows 154, 168, 169). A string operand is
--          `Tlc.todo`: TLC treats a string as a sequence of characters (Len, SubSeq, \o), which
--          mints runtime strings (refused by the front end, model.runtime-string, 10:678).
--   RemoveAt(s, i)   CommunityModules' SequencesExt definition, `SubSeq(s, 1, i-1) \o
--          SubSeq(s, i+1, Len(s))`, evaluated as TLC evaluates it ([PSeqRemoveAt],
--          [PSeqRemoveAtOut] (an index just outside leaves s unchanged), [PSeqRemoveAtNonSeq],
--          [PSeqRemoveAtNonInt]); K2's "i outside 1..Len(s) is an error" is not TLC's.
--   membership (`Prim.mem`, B1A-D44)   x \in S for a set S: an element equal to x
--          (`valueEq`, the element as receiver: TLC's search of a set enumeration); a
--          comparison error is the named refusal (`Fail.deferCmp`; whether TLC compares x
--          with that element at all depends on whether S is normalized, B1A-D96). Nat: an
--          integer >= 0; Int: an integer; STRING: a string; an untyped model value is in none
--          of them ([PSetInInf], [PSetInNatMv], [PSetInIntKinds]), a typed one raises
--          `incomparable` ([PSetInNatTmv], [PSetInIntTmv], [PSetInStringTmv], row 203), any
--          other value `typeErr` ([PSetInNatStr], [PSetInIntStr], [PSetInStringInt], row
--          162). Seq(S): a sequence whose every element is in S ([PSetInSeq]; [PSetInSeqNonSetBase]
--          raises at an element), an untyped model value FALSE ([PSetInSeqMv]), any other
--          value `typeErr` ([PSetInSeqRec], [PSetInSeqNonSeq], row 162), a typed model value
--          `Tlc.todo` (unprobed). [S -> T]: a function whose domain equals S (`valueEq S
--          (DOMAIN f)`, S the receiver; a comparison error refused, [PFnSetInfRecMem],
--          [PFnSetInfDomMem]) and whose every value is in T ([PFnSetInfMem]). SetOfFcnsValue.member
--          (javap) takes S as the receiver only for a function without an interval domain
--          (`S.equals(SetEnumValue(DOMAIN f))`); for a tuple or sequence (TupleValue.toFcnRcd
--          builds an IntervalValue domain) it calls `fcn.intv.equals(S)`, the interval 1..n as
--          receiver (IntervalValue.equals: toSetEnum().equals(S)). The two orders agree or both
--          raise, and every such error is the refusal above, so the EP keeps one order;
--          a value that is not a function `typeErr` ([PFnSetInfNonFn], row 157); a model value
--          `Tlc.todo` (unprobed). A value that is not a set: `typeErr` (an integer
--          [PSetInNonSet], a Boolean [PSetInBool], a string [PSetInStr], a model value
--          [PSetInMv], [PSetInTmv], row 162; a tuple [PSetInTuple], row 142; a record
--          [PSetInRec], row 143; a FcnRcdValue [PSetInFcnRcd], row 162; also as the second
--          operand of \cap and \: [PSetInterTuple], [PSetDiffRec]).

-- `Prim.typeErr`: TLC's operand-kind error class.
def Prim.typeErr {α : Type} : Res α := Res.error Fail.typeErr

-- `Prim.args1 vs k` .. `Prim.args3`: k on exactly one, two or three operands; any other
-- number is `Tlc.illFormed` (B1A-D95).
def Prim.args1 {α : Type} (vs : List Value) (k : Value → Res α) : Res α :=
  @List.casesOn Value (fun _ => Res α) vs Tlc.illFormed
    (fun a r => @List.casesOn Value (fun _ => Res α) r (k a) (fun _ _ => Tlc.illFormed))
def Prim.args2 {α : Type} (vs : List Value) (k : Value → Value → Res α) : Res α :=
  @List.casesOn Value (fun _ => Res α) vs Tlc.illFormed (fun a r => Prim.args1 r (fun b => k a b))
def Prim.args3 {α : Type} (vs : List Value) (k : Value → Value → Value → Res α) : Res α :=
  @List.casesOn Value (fun _ => Res α) vs Tlc.illFormed
    (fun a r => Prim.args2 r (fun b c => k a b c))

-- `Prim.int v k`: k on v's integer, else `typeErr`.
def Prim.int {α : Type} (v : Value) (k : Int → Res α) : Res α :=
  @Option.casesOn Int (fun _ => Res α) (Value.asInt v) Prim.typeErr k

-- `Prim.arith f vs`: an integer operator of two integer operands.
def Prim.arith (f : Int → Int → Res Int) (vs : List Value) : Res Value :=
  Prim.args2 vs (fun a b => Prim.int a (fun x => Prim.int b (fun y => Res.map Value.int (f x y))))

-- `Prim.cmp p vs`: an integer comparison; p reads `intCmp` (0 before, 1 equal, 2 after).
def Prim.cmp (p : Nat → Bool) (vs : List Value) : Res Value :=
  Prim.args2 vs (fun a b => Prim.int a (fun x => Prim.int b (fun y =>
    Res.ok (Value.bool (p (intCmp x y))))))

-- `Prim.lookup ps a`: the value at the key equal to a, `none` when there is none; a key of
-- another kind than a is the named refusal (`keyEqWith`, B1A-D86/D87).
def Prim.lookup (ps : List (Prod Value Value)) (a : Value) : Res (Option Value) :=
  @List.rec (Prod Value Value) (fun _ => Res (Option Value)) (Res.ok Option.none)
    (fun p _ rest => Res.bind (keyEqWith valueEq (Prod.fst p) a)
      (fun b => @Bool.rec (fun _ => Res (Option Value)) rest (Res.ok (Option.some (Prod.snd p))) b))
    ps

-- `Prim.apply f a`: f[a].
def Prim.apply (f a : Value) : Res Value :=
  @Option.casesOn (List (Prod Value Value)) (fun _ => Res Value) (Value.asFn f) Prim.typeErr
    (fun ps => Res.bind (Prim.lookup ps a) (fun o =>
      @Option.casesOn Value (fun _ => Res Value) o (Res.error Fail.notInDomain) (fun v => Res.ok v)))

-- `Prim.replace ps x v`: ps with the value at the key equal to x replaced by v; unchanged
-- when no key is (TLC's EXCEPT ignores a point outside the domain).
def Prim.replace (ps : List (Prod Value Value)) (x v : Value) : Res (List (Prod Value Value)) :=
  @List.rec (Prod Value Value) (fun _ => Res (List (Prod Value Value))) (Res.ok [])
    (fun p tl rest => Res.bind (keyEqWith valueEq (Prod.fst p) x)
      (fun b => @Bool.rec (fun _ => Res (List (Prod Value Value)))
        (Res.map (fun r => List.cons p r) rest)
        (Res.ok (List.cons (Prod.mk (Prod.fst p) v) tl)) b))
    ps

-- `Prim.except f x v`: [f EXCEPT ![x] = v].
def Prim.except (f x v : Value) : Res Value :=
  @Option.casesOn (List (Prod Value Value)) (fun _ => Res Value) (Value.asFn f) Prim.typeErr
    (fun ps => Res.map Value.fn (Prim.replace ps x v))

-- `Prim.seqFrom ps i`: the values of ps when its keys are exactly i, i+1, ... in order.
def Prim.seqFrom (ps : List (Prod Value Value)) : Nat → Option (List Value) :=
  @List.rec (Prod Value Value) (fun _ => Nat → Option (List Value)) (fun _ => Option.some [])
    (fun p _ go i => @Option.casesOn Int (fun _ => Option (List Value)) (Value.asInt (Prod.fst p))
      Option.none
      (fun n => @Bool.rec (fun _ => Option (List Value)) Option.none
        (@Option.casesOn (List Value) (fun _ => Option (List Value)) (go (Nat.succ i)) Option.none
          (fun vs => Option.some (List.cons (Prod.snd p) vs)))
        (intBeq n (Int.ofNat i))))
    ps

-- `Prim.seq v k`: k on the elements of the sequence v (a function on 1..n); a string is
-- `Tlc.todo` (TLC reads it as a sequence of characters, see above); anything else `typeErr`.
def Prim.seq {α : Type} (v : Value) (k : List Value → Res α) : Res α :=
  @Option.casesOn Nat (fun _ => Res α) (Value.asStr v)
    (@Option.casesOn (List (Prod Value Value)) (fun _ => Res α) (Value.asFn v) Prim.typeErr
      (fun ps => @Option.casesOn (List Value) (fun _ => Res α) (Prim.seqFrom ps 1) Prim.typeErr k))
    (fun _ => Tlc.todo)

-- `Prim.drop n xs` / `Prim.take n xs`.
def Prim.drop (n : Nat) (xs : List Value) : List Value :=
  @Nat.rec (fun _ => List Value → List Value) (fun ys => ys)
    (fun _ go ys => go (@List.casesOn Value (fun _ => List Value) ys [] (fun _ t => t))) n xs
def Prim.take (n : Nat) (xs : List Value) : List Value :=
  @List.rec Value (fun _ => Nat → List Value) (fun _ => [])
    (fun x _ go k => @Nat.casesOn (fun _ => List Value) k [] (fun k' => List.cons x (go k'))) xs n

-- `Prim.inRange xs i`: 1 <= i <= Len(xs).
def Prim.inRange (xs : List Value) (i : Int) : Bool :=
  @Int.casesOn (fun _ => Bool) i
    (fun n => Bool.and (Nat.blt 0 n) (Nat.ble n (List.length xs))) (fun _ => false)

-- `Prim.subSeq xs m n`: Sequences.SubSeq on the elements xs: <<>> when m > n, else m and n in
-- 1..Len, `notInDomain` otherwise (m first), and the elements m..n.
def Prim.subSeq (xs : List Value) (m n : Int) : Res Value :=
  @Bool.rec (fun _ => Res Value)
    (@Bool.rec (fun _ => Res Value) (Res.error Fail.notInDomain)
      (@Bool.rec (fun _ => Res Value) (Res.error Fail.notInDomain)
        (Res.ok (mkSeq (Prim.take (Nat.succ (Nat.sub (natAbs n) (natAbs m)))
          (Prim.drop (Nat.pred (natAbs m)) xs))))
        (Prim.inRange xs n))
      (Prim.inRange xs m))
    (Res.ok (mkSeq []))
    (Nat.beq (intCmp m n) 2)

-- `Prim.subSeqV s a b`: SubSeq(s, a, b) on values: s a sequence, a and b integers.
def Prim.subSeqV (s a b : Value) : Res Value :=
  Prim.seq s (fun xs => Prim.int a (fun m => Prim.int b (fun n => Prim.subSeq xs m n)))

-- `Prim.concat s t`: s \o t.
def Prim.concat (s t : Value) : Res Value :=
  Prim.seq s (fun xs => Prim.seq t (fun ys => Res.ok (mkSeq (List.append xs ys))))

-- `Prim.removeAt m s i`: RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s)), in
-- TLC's order: i-1, the left SubSeq, i+1, Len(s), the right SubSeq, then \o.
def Prim.removeAt (m : IntMode) (s i : Value) : Res Value :=
  Prim.int i (fun n =>
    Res.bind (intSub m n 1) (fun n1 =>
      Res.bind (Prim.subSeqV s (Value.int 1) (Value.int n1)) (fun l =>
        Res.bind (intAdd m n 1) (fun n2 =>
          Prim.seq s (fun xs =>
            Res.bind (Prim.subSeqV s (Value.int n2) (Value.int (Int.ofNat (List.length xs))))
              (fun r => Prim.concat l r))))))

-- `Prim.setOf v k`: k on the elements of the finite set v, else `other`.
def Prim.setOf {α : Type} (v : Value) (other : Res α) (k : List Value → Res α) : Res α :=
  @Option.casesOn (List Value) (fun _ => Res α) (Value.asSet v) other k

-- `Prim.defer r`: r, a comparison error as the EP reports it in a membership search
-- (`Fail.deferCmp`, B1A-D96).
def Prim.defer {α : Type} (r : Res α) : Res α :=
  @Res.rec α (fun _ => Res α) (fun a => Res.ok a) (fun f => Res.error (Fail.deferCmp f)) r

-- `Prim.memSet x xs`: x equal to an element of xs, each element `valueEq`'s receiver, in
-- order (TLC's search of an unnormalized set); a comparison error is the named refusal
-- (B1A-D96).
def Prim.memSet (x : Value) (xs : List Value) : Res Bool :=
  @List.rec Value (fun _ => Res Bool) (Res.ok false)
    (fun e _ rest => Res.bind (Prim.defer (valueEq e x))
      (fun b => @Bool.rec (fun _ => Res Bool) rest (Res.ok true) b))
    xs

-- `Prim.allB xs p`: p at every element in order, the first FALSE or error deciding.
def Prim.allB (xs : List Value) (p : Value → Res Bool) : Res Bool :=
  @List.rec Value (fun _ => Res Bool) (Res.ok true)
    (fun x _ rest => Res.bind (p x) (fun b => @Bool.rec (fun _ => Res Bool) (Res.ok false) rest b))
    xs

-- `Prim.mvOr x mvAns tmvAns other`: x an untyped model value: mvAns; a typed one: tmvAns;
-- else other.
def Prim.mvOr (x : Value) (mvAns tmvAns other : Res Bool) : Res Bool :=
  @Option.casesOn Nat (fun _ => Res Bool) (Value.asMv x)
    (@Bool.rec (fun _ => Res Bool) other tmvAns (Value.isTmv x)) (fun _ => mvAns)

-- `Prim.memF fuel x S`: x \in S (membership by kind, B1A-D44), fuel-by-size of S.
def Prim.memF (fuel : Nat) : Value → Value → Res Bool :=
  @Nat.rec (fun _ => Value → Value → Res Bool)
    (fun _ _ => Res.error Fail.fuel)
    (fun _ go x S =>
      @Value.elim (Res Bool) S
        (fun _ => Prim.typeErr) (fun _ => Prim.typeErr) (fun _ => Prim.typeErr)
        (fun _ => Prim.typeErr) (fun _ _ => Prim.typeErr)
        (fun xs => Prim.memSet x xs)
        (fun _ => Prim.typeErr)
        (fun k args => @InfKind.casesOn (fun _ => Res Bool) k
          -- Nat
          (Prim.mvOr x (Res.ok false) (Res.error Fail.incomparable)
            (@Option.casesOn Int (fun _ => Res Bool) (Value.asInt x) Prim.typeErr
              (fun n => Res.ok (Bool.not (isNeg n)))))
          -- Int
          (Prim.mvOr x (Res.ok false) (Res.error Fail.incomparable)
            (@Option.casesOn Int (fun _ => Res Bool) (Value.asInt x) Prim.typeErr
              (fun _ => Res.ok true)))
          -- STRING
          (Prim.mvOr x (Res.ok false) (Res.error Fail.incomparable)
            (@Option.casesOn Nat (fun _ => Res Bool) (Value.asStr x) Prim.typeErr
              (fun _ => Res.ok true)))
          -- Seq(B)
          (Prim.args1 args (fun B => Prim.mvOr x (Res.ok false) Tlc.todo
            (@Option.casesOn (List (Prod Value Value)) (fun _ => Res Bool) (Value.asFn x)
              Prim.typeErr
              (fun ps => @Option.casesOn (List Value) (fun _ => Res Bool) (Prim.seqFrom ps 1)
                Prim.typeErr (fun xs => Prim.allB xs (fun e => go e B))))))
          -- [D -> C]
          (Prim.args2 args (fun D C => Prim.mvOr x Tlc.todo Tlc.todo
            (@Option.casesOn (List (Prod Value Value)) (fun _ => Res Bool) (Value.asFn x)
              Prim.typeErr
              (fun ps => Res.bind (Prim.defer (valueEq D (Value.set (keysOf ps))))
                (fun b => @Bool.rec (fun _ => Res Bool) (Res.ok false)
                  (Prim.allB (List.map (@Prod.snd Value Value) ps) (fun e => go e C)) b)))))))
    fuel

-- `Prim.mem x S`: x \in S, with fuel that never runs out (each recursive call tests an
-- element against a proper part of S).
def Prim.mem (x S : Value) : Res Bool := Prim.memF (Nat.succ (Value.size S)) x S

-- `Prim.filterM xs p`: the elements of xs at which p is TRUE, in order; the first error wins.
def Prim.filterM (xs : List Value) (p : Value → Res Bool) : Res (List Value) :=
  @List.rec Value (fun _ => Res (List Value)) (Res.ok [])
    (fun x _ rest => Res.bind (p x) (fun b =>
      Res.map (fun ys => @Bool.rec (fun _ => List Value) ys (List.cons x ys) b) rest))
    xs

-- `Prim.setV r`: a list of elements as a set value.
def Prim.setV (r : Res (List Value)) : Res Value := Res.map Value.set r

-- `Prim.allSets xs`: every element of xs is a finite set (`Value.set`): TLC's UnionValue.union
-- builds UNION S eagerly only when S and its every element are SetEnumValues, and lazily (a
-- UnionValue) otherwise (javap, B1A-15 repair round 1; [PSetBigUnionNatMem], [PSetBigUnionIntMem]).
-- `Value.set` also stands for an IntervalValue, which TLC keeps lazy: the EP builds that union
-- eagerly, with the same value, its only error `Tlc.normDefer`'s refusal (B1A-15 repair round 2).
def Prim.allSets (xs : List Value) : Bool :=
  @List.rec Value (fun _ => Bool) true
    (fun x _ rest => @Option.casesOn (List Value) (fun _ => Bool) (Value.asSet x) false
      (fun _ => rest))
    xs

-- `Prim.unions xs`: the elements of the finite sets xs, in order (an element that is not one
-- contributes nothing: `PrimOp.evalV` calls this only when `Prim.allSets xs`).
def Prim.unions (xs : List Value) : List Value :=
  @List.rec Value (fun _ => List Value) []
    (fun x _ rest => @Option.casesOn (List Value) (fun _ => List Value) (Value.asSet x) rest
      (fun ys => List.append ys rest))
    xs

-- `Prim.rangeFrom a n`: the n integers a, a+1, ...; `Prim.range a b`: a..b, empty when a > b.
def Prim.rangeFrom (a : Int) (n : Nat) : List Value :=
  @Nat.rec (fun _ => Int → List Value) (fun _ => [])
    (fun _ go x => List.cons (Value.int x) (go (x + 1))) n a
def Prim.range (a b : Int) : List Value :=
  @Bool.rec (fun _ => List Value) (Prim.rangeFrom a (Nat.succ (natAbs (b - a)))) []
    (Nat.beq (intCmp a b) 2)

-- `Prim.isInf v`: v is an `infSet`.
def Prim.isInf (v : Value) : Bool :=
  @Option.casesOn (Prod InfKind (List Value)) (fun _ => Bool) (Value.asInfSet v) false
    (fun _ => true)

-- `Prim.isFnSet v`: v is an `infSet fnSet` ([S -> T] with an infinite operand, TLC's
-- SetOfFcnsValue, which is Enumerable; B1A-15 repair round 2).
def Prim.isFnSet (v : Value) : Bool :=
  @Option.casesOn (Prod InfKind (List Value)) (fun _ => Bool) (Value.asInfSet v) false
    (fun p => Nat.beq (InfKind.tag (Prod.fst p)) 4)

-- `Prim.fnOpK v`: TLC's isEmpty() and size() of an operand of [S -> T], where pinned, from one
-- lookup (so either both are pinned or neither is): a finite set's emptiness and size; Nat,
-- Int, STRING (kinds nat, int, string) isEmpty() FALSE without error ([PSetCardFnSetOneRng],
-- [PSetCardFnSetInf], [PSetCardFnSetIntRng], [PSetCardFnSetIntDom], [PSetCardFnSetStrRng],
-- [PSetCardFnSetStrDom] each pass it) and size() raising "Attempted to compute the number of
-- elements in the overridden value", `typeErr` (row 160: [PSetCardFnSetInf],
-- [PSetCardFnSetNatDom], [PSetCardFnSetIntRng], [PSetCardFnSetIntDom], [PSetCardFnSetStrRng],
-- [PSetCardFnSetStrDom]); any other operand `none` (unprobed: B1A-15b). (B1A-15 repair round 2:
-- this replaces `Prim.isEmptyK` and `Prim.sizeK`, which were `some` for the same operands, so
-- `Prim.cardFnSet`'s two `none` branches of `Prim.sizeK` could not be reached.)
def Prim.fnOpK (v : Value) : Option (Prod Bool (Res Nat)) :=
  @Option.casesOn (List Value) (fun _ => Option (Prod Bool (Res Nat))) (Value.asSet v)
    (@Option.casesOn (Prod InfKind (List Value)) (fun _ => Option (Prod Bool (Res Nat)))
      (Value.asInfSet v) Option.none
      (fun p => @Bool.rec (fun _ => Option (Prod Bool (Res Nat))) Option.none
        (Option.some (Prod.mk false (@Prim.typeErr Nat))) (Nat.blt (InfKind.tag (Prod.fst p)) 3)))
    (fun xs => Option.some (Prod.mk (@List.casesOn Value (fun _ => Bool) xs true (fun _ _ => false))
      (Res.ok (List.length xs))))

-- `Prim.cardFnSet D C`: Cardinality([D -> C]) for an infinite operand, TLC's
-- SetOfFcnsValue.size() step by step (javap, B1A-15 repair round 1): D empty 1
-- ([PSetCardFnSetEmptyDom]); else C empty 0 ([PSetCardFnSetEmptyRng]); else C of size 1 1
-- ([PSetCardFnSetOneRng]); else D's size, which for an infinite D raises ([PSetCardFnSetNatDom]).
-- An operand whose isEmpty() and size() are unprobed (`Prim.fnOpK` `none`) is `Tlc.todo`
-- (B1A-15b); two finite operands never make an `infSet fnSet` (`PrimOp.evalV`'s funcSet), and
-- are B1A-17a's finite SetOfFcnsValue.
def Prim.cardFnSet (D C : Value) : Res Value :=
  @Option.casesOn (Prod Bool (Res Nat)) (fun _ => Res Value) (Prim.fnOpK D) Tlc.todo
    (fun d => @Bool.rec (fun _ => Res Value)
      (@Option.casesOn (Prod Bool (Res Nat)) (fun _ => Res Value) (Prim.fnOpK C) Tlc.todo
        (fun c => @Bool.rec (fun _ => Res Value)
          (Res.bind (Prod.snd c) (fun n => @Bool.rec (fun _ => Res Value)
            (Res.bind (Prod.snd d) (fun _ => Tlc.todo)) -- two finite operands: B1A-17a
            (Res.ok (Value.int 1)) (Nat.beq n 1)))
          (Res.ok (Value.int 0)) (Prod.fst c)))
      (Res.ok (Value.int 1)) (Prod.fst d))

-- `Prim.card S`: Cardinality(S): a finite set's size; [D -> C] with an infinite operand
-- `Prim.cardFnSet`; any other value, Nat, Int, STRING and Seq(S) included, `notEnumerable`
-- (FiniteSets.Cardinality answers size() for an Enumerable and the row-126 text otherwise:
-- [PSetCardNonSet], [PSetCardInf]; Nat, Int, STRING and Seq(S) are UserValues, not Enumerable).
def Prim.card (S : Value) : Res Value :=
  Prim.setOf S
    (@Option.casesOn (Prod InfKind (List Value)) (fun _ => Res Value) (Value.asInfSet S)
      (Res.error Fail.notEnumerable)
      (fun p => @Bool.rec (fun _ => Res Value) (Res.error Fail.notEnumerable)
        (Prim.args2 (Prod.snd p) Prim.cardFnSet)
        (Nat.beq (InfKind.tag (Prod.fst p)) 4)))
    (fun xs => Res.ok (Value.int (Int.ofNat (List.length xs))))

-- `Prim.isFinite S`: IsFiniteSet(S), TLC's `S.isFinite()`: a finite set TRUE; a function
-- TRUE (FcnRcdValue, TupleValue and RecordValue.isFinite are the constant TRUE, javap;
-- [PSetIsFiniteFn]); Nat, Int, STRING FALSE; Seq(B) TRUE exactly when B is the empty set; a
-- Boolean, an integer, a string or a model value `typeErr` ([PSetIsFiniteNonSet],
-- [PSetIsFiniteBool], [PSetIsFiniteStr], [PSetIsFiniteMv], [PSetIsFiniteTmv], row 160).
def Prim.isFinite (S : Value) : Res Value :=
  Prim.setOf S
    (@Option.casesOn (Prod InfKind (List Value)) (fun _ => Res Value) (Value.asInfSet S)
      (@Option.casesOn (List (Prod Value Value)) (fun _ => Res Value) (Value.asFn S) Prim.typeErr
        (fun _ => Res.ok (Value.bool true)))
      (fun p => @InfKind.casesOn (fun _ => Res Value) (Prod.fst p)
        (Res.ok (Value.bool false)) (Res.ok (Value.bool false)) (Res.ok (Value.bool false))
        (Prim.args1 (Prod.snd p) (fun B => Prim.setOf B Tlc.todo
          (fun bs => Res.ok (Value.bool (@List.casesOn Value (fun _ => Bool) bs true
            (fun _ _ => false))))))
        Tlc.todo))
    (fun _ => Res.ok (Value.bool true))

-- `Prim.fields fs vs`: the record fields (name rank, value), in source order.
def Prim.fields (fs : List Nat) (vs : List Value) : List (Prod Nat Value) :=
  @List.rec Nat (fun _ => List Value → List (Prod Nat Value)) (fun _ => [])
    (fun f _ go ws => @List.casesOn Value (fun _ => List (Prod Nat Value)) ws []
      (fun w r => List.cons (Prod.mk f w) (go r)))
    fs vs

-- `Prim.assertMsg m`: the argument of `assertFailed`: m's token rank when m is a string,
-- else 0 (B1A-D97).
def Prim.assertMsg (m : Value) : Nat :=
  @Option.casesOn Nat (fun _ => Nat) (Value.asStr m) 0 (fun r => r)

-- `PrimOp.evalV m vs o` (TASKS B1A-15): the PrimOp o at the operand values vs, under the
-- Spec's IntMode m; one minor per constructor, in declaration order (Syntax.lean).
def PrimOp.evalV (m : IntMode) (vs : List Value) (o : PrimOp) : Res Value :=
  @PrimOp.casesOn (fun _ => Res Value) o
    -- intAdd intSub intMul intDiv intMod
    (Prim.arith (intAdd m) vs) (Prim.arith (intSub m) vs) (Prim.arith (intMul m) vs)
    (Prim.arith (intDiv m) vs) (Prim.arith (intMod m) vs)
    -- intNeg
    (Prim.args1 vs (fun a => Prim.int a (fun x => Res.map Value.int (intNeg m x))))
    -- intLt intLe
    (Prim.cmp (fun c => Nat.beq c 0) vs) (Prim.cmp (fun c => Bool.not (Nat.beq c 2)) vs)
    -- recGet field, recWith field
    (fun f => Prim.args1 vs (fun r => Prim.apply r (Value.str f)))
    (fun f => Prim.args2 vs (fun r v => Prim.except r (Value.str f) v))
    -- funcApply funcExcept funcDomain
    (Prim.args2 vs (fun f a => Prim.apply f a))
    (Prim.args3 vs (fun f x v => Prim.except f x v))
    (Prim.args1 vs (fun f =>
      @Option.casesOn (List (Prod Value Value)) (fun _ => Res Value) (Value.asFn f) Prim.typeErr
        (fun ps => Res.ok (Value.set (keysOf ps)))))
    -- setIn
    (Prim.args2 vs (fun x S => Res.map Value.bool (Prim.mem x S)))
    -- setInsert
    (Prim.args2 vs (fun S x => Prim.setOf S Tlc.todo
      (fun xs => Prim.setV (Tlc.normDefer (List.append xs [x])))))
    -- setUnion
    (Prim.args2 vs (fun S T => Prim.setOf S Tlc.todo (fun xs => Prim.setOf T Tlc.todo
      (fun ys => Prim.setV (Tlc.normDefer (List.append xs ys))))))
    -- setDiff
    (Prim.args2 vs (fun S T => Prim.setOf S Tlc.todo
      (fun xs => Prim.setV (Prim.filterM xs (fun e => Res.map Bool.not (Prim.mem e T))))))
    -- setCard
    (Prim.args1 vs Prim.card)
    -- setSubseteq: S not Enumerable `notEnumerable`; an infSet fnSet (Enumerable) B1A-17a/17b
    (Prim.args2 vs (fun S T => Prim.setOf S
      (@Bool.rec (fun _ => Res Value) (Res.error Fail.notEnumerable) Tlc.todo (Prim.isFnSet S))
      (fun xs => Res.map Value.bool (Prim.allB xs (fun e => Prim.mem e T)))))
    -- seqLen
    (Prim.args1 vs (fun s => Prim.seq s (fun xs =>
      Res.ok (Value.int (Int.ofNat (List.length xs))))))
    -- seqIndex
    (Prim.args2 vs (fun s i => Prim.apply s i))
    -- seqAppend
    (Prim.args2 vs (fun s x => Prim.seq s (fun xs => Res.ok (mkSeq (List.append xs [x])))))
    -- seqHead
    (Prim.args1 vs (fun s => Prim.seq s (fun xs =>
      @List.casesOn Value (fun _ => Res Value) xs (Res.error Fail.notInDomain)
        (fun h _ => Res.ok h))))
    -- seqTail
    (Prim.args1 vs (fun s => Prim.seq s (fun xs =>
      @List.casesOn Value (fun _ => Res Value) xs (Res.error Fail.notInDomain)
        (fun _ t => Res.ok (mkSeq t)))))
    -- seqSubseq
    (Prim.args3 vs (fun s a b => Prim.subSeqV s a b))
    -- valueEq valueNe
    (Prim.args2 vs (fun a b => Res.map Value.bool (valueEq a b)))
    (Prim.args2 vs (fun a b => Res.map (fun c => Value.bool (Bool.not c)) (valueEq a b)))
    -- setEnum
    (Prim.setV (Tlc.normDefer vs))
    -- setRange
    (Prim.args2 vs (fun a b => Prim.int a (fun x => Prim.int b (fun y =>
      Res.ok (Value.set (Prim.range x y))))))
    -- setIntersect
    (Prim.args2 vs (fun S T => Prim.setOf S
      (Prim.setOf T Tlc.todo (fun ys => Prim.setV (Prim.filterM ys (fun e => Prim.mem e S))))
      (fun xs => Prim.setV (Prim.filterM xs (fun e => Prim.mem e T)))))
    -- setBigUnion: eager when every element is a finite set, else a lazy UnionValue (B1A-17b)
    (Prim.args1 vs (fun S => Prim.setOf S Tlc.todo
      (fun xs => @Bool.rec (fun _ => Res Value) Tlc.todo
        (Prim.setV (Tlc.normDefer (Prim.unions xs))) (Prim.allSets xs))))
    -- setPowerset setProduct: lazy sets, B1A-17a
    Tlc.todo Tlc.todo
    -- setIsFinite
    (Prim.args1 vs Prim.isFinite)
    -- funcSet: [S -> T] with an infinite operand is `infSet fnSet` (B1A-D44); else B1A-17a
    (Prim.args2 vs (fun S T => @Bool.rec (fun _ => Res Value) Tlc.todo
      (Res.ok (Value.infSet InfKind.fnSet [S, T])) (Bool.or (Prim.isInf S) (Prim.isInf T))))
    -- recNew fields
    (fun fs => @Bool.rec (fun _ => Res Value) Tlc.illFormed (mkRecord (Prim.fields fs vs))
      (Nat.beq (List.length fs) (List.length vs)))
    -- recSetOf: a lazy set, B1A-17a
    (fun _ => Tlc.todo)
    -- tupleNew
    (Res.ok (mkTuple vs))
    -- tupleGet index
    (fun i => Prim.args1 vs (fun t => Prim.apply t (Value.int (Int.ofNat i))))
    -- seqConcat
    (Prim.args2 vs (fun s t => Prim.concat s t))
    -- seqSet: Seq(S) (B1A-D44)
    (Prim.args1 vs (fun S => Res.ok (Value.infSet InfKind.seqOf [S])))
    -- seqRemoveAt
    (Prim.args2 vs (fun s i => Prim.removeAt m s i))
    -- valueAsBool
    (Prim.args1 vs (fun a => @Option.casesOn Bool (fun _ => Res Value) (Value.asBool a)
      Prim.typeErr (fun b => Res.ok (Value.bool b))))
    -- intPow
    (Prim.arith (intPow m) vs)
    -- intGt intGe
    (Prim.cmp (fun c => Nat.beq c 2) vs) (Prim.cmp (fun c => Bool.not (Nat.beq c 0)) vs)
    -- natSuccU, natSatU (B1A-D12): unbounded whatever the IntMode
    (Prim.args1 vs (fun a => Prim.int a (fun x => Res.ok (Value.int (x + 1)))))
    (Prim.args2 vs (fun a c => Prim.int a (fun x => Prim.int c (fun y =>
      Res.ok (Value.int (@Bool.rec (fun _ => Int) y (x + 1) (Nat.beq (intCmp x y) 0)))))))
    -- assert
    (Prim.args2 vs (fun p msg => @Bool.rec (fun _ => Res Value)
      (Res.error (Fail.assertFailed (Prim.assertMsg msg))) (Res.ok (Value.bool true))
      (@Option.casesOn Bool (fun _ => Bool) (Value.asBool p) false (fun b => b))))

-- `Tlc.evalOps go k env s p args`: the operands, left to right with the inherited keepLazy;
-- the first error wins.
def Tlc.evalOps (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (args : List Expr) : Res (List XVal) :=
  @List.rec Expr (fun _ => Res (List XVal)) (Res.ok [])
    (fun d _ rest => Res.bind (Tlc.goEvalX go k env s p d)
      (fun x => Res.map (fun xs => List.cons x xs) rest))
    args

-- `Tlc.allVals xs`: the values when every operand is a forced `val`.
def Tlc.allVals (xs : List XVal) : Option (List Value) :=
  @List.rec XVal (fun _ => Option (List Value)) (Option.some [])
    (fun x _ rest => XVal.elim x
      (fun v => @Option.casesOn (List Value) (fun _ => Option (List Value)) rest Option.none
        (fun vs => Option.some (List.cons v vs)))
      (fun _ _ _ => Option.none) (fun _ => Option.none) (fun _ => Option.none))
    xs

-- `Tlc.opX`: an `op` node: the operands, then `PrimOp.evalV` when all are forced; a lazy
-- operand of a PrimOp `Tlc.opLazyX` does not route elsewhere is a forcing row of B1A-17a/17b
-- (`Tlc.todo` until then).
def Tlc.opX (sp : Spec) (go : Job → Res Out) (k : Bool) (env : List Value) (s : State)
    (p : Frame) (o : PrimOp) (args : List Expr) : Res XVal :=
  Res.bind (Tlc.evalOps go k env s p args) (fun xs =>
    @Option.casesOn (List Value) (fun _ => Res XVal) (Tlc.allVals xs) Tlc.todo
      (fun vs => Res.map XVal.val (PrimOp.evalV sp.intMode vs o)))

-- ---- Laziness I: function constructors, keepLazy, applyX, DOMAIN, EXCEPT, force (B1A-16) ----
--
-- Forcing-table rows 1-6 (design 10:612-617) and the operand rows of the PrimOps that read a
-- function (TASKS B1A-16). Read from the jar of record (javap of Tool.evalApplImpl,
-- FcnLambdaValue, FcnParams, Sequences) and pinned by the probes of ty
-- reports/perf/2026-10-09-beyond-tla-b1a/lazy-probes/ (`[Name]`) and batch C (probes/):
--   construction   `[x \in S |-> e]`: the domains are evaluated to XVals with the inherited
--                  keepLazy, in binder order, never enumerated (`Tlc.rule.forceCtorDomains`);
--                  when `Tlc.rule.materializeQFn` holds (keepLazy off and every domain
--                  Reducible) the body runs at every context, FIRST binder fastest (FcnParams'
--                  enumerator advances binder 0 first, over each domain normalized:
--                  [PLazyCtorOrder], [PLazyCtorSetOrder]), under the same keepLazy, and the
--                  result is the function of those values (`Tlc.mkFnX`: a `val` when every
--                  value is forced, else an `fnX`); otherwise a `lazyFn` over the unforced
--                  domains, capturing env and the primed frame ([LazyTupleClear],
--                  [LazyTupleKeep], [LazyNatDomain]).
--   keepLazy       set on the function operand of `f[a]` only (OPCODE_fa evaluates it under
--                  setKeepLazy(control)), inherited everywhere else (tuple and record
--                  elements, IF/CASE arms, LET bodies, pool entries, operator bodies, a
--                  Java override's operands: [PLazyHeadKeep], [PLazyTailKeep],
--                  [PLazyRecGetKeep], [PLazyExceptKeep]); reset at an item's right-hand side
--                  (`Tlc.rhsX`, `Tlc.rule.keepLazyReset`; the item machine is B1A-18's).
--   f[a]           f under keepLazy on; a function value (a `val` function, a `lazyFn`, an
--                  `fnX`) is then applied, anything else is `typeErr` BEFORE a is evaluated
--                  ([PLazyApplyNonFnFirst], row 163); a is evaluated with the inherited
--                  keepLazy and must be forced: a lazy argument is `unmodeled lazy.arg`
--                  (10:615); then `applyX` under the inherited keepLazy (FunctionValue.apply
--                  (arg, control)). seq.index and tuple.get are the same TLA+ form.
--   applyX         a `lazyFn`: the domain test is `memX` of a, pointwise (one binder: its
--                  domain; several: a must be a tuple, each of its first n components
--                  tested against its binder's domain in order, TLC ignoring any further
--                  component ([PLazyApplyTwo], [PLazyApplyTwoLong]); a non-tuple or a shorter
--                  one is `Tlc.todo`, B1A-17b); FALSE is `notInDomain` ([PLazyNotInDomain],
--                  [PLazyApplyTwoOut], row 106); TRUE: the body at this point only, under the
--                  APPLICATION's keepLazy (FcnLambdaValue.apply passes its control to
--                  evalBody: [PLazyApplyCtl] divZero, [PLazyApplyKeep] 2), in the captured
--                  env and frame. An `fnX`: the entry at a, unforced ([LazyTuple]). A `val`
--                  function: `Prim.apply`.
--   memX           (this row's part) a forced set or `ofVal`: `Prim.mem`; a function, lazy or
--                  not, is not a set: `typeErr` (FcnLambdaValue/TupleValue/RecordValue.member
--                  raise, rows 162, 142, 143); every other lazy set is B1A-17a's.
--   DOMAIN         the operand with the inherited keepLazy; a `lazyFn`'s domain unforced: the
--                  one binder's (`val` when it is one), several binders' product as a lazy
--                  set (FcnLambdaValue.getDomain; [PLazyDomainNat], [LazyDomainNonReducible]);
--                  an `fnX`'s keys; not a function `typeErr` (row 164).
--   r.fld          the operand with the inherited keepLazy (OPCODE_rs sets no KeepLazy); a
--                  record `fnX`'s entry unforced ([PLazyRecGetKeep]); a `lazyFn` is FORCED
--                  (toFcnRcd) and then selected ([PLazyRecGetForces]); a lazy set `typeErr`
--                  (toFcnRcd is null, row 167).
--   EXCEPT         f, then the point x, both with the inherited keepLazy; a `lazyFn` is
--                  `unmodeled lazy.except` (10:617; TLC keeps an excepts list and reads the
--                  old value at x: [LazyExcept], [LazyExceptOtherPoint]); a value that is not
--                  a function `typeErr` after x ([PLazyExceptNonFnPath], row 166); a lazy x is
--                  `Tlc.todo` (B1A-17b); x not a point of f: f unchanged and the new value
--                  never evaluated ([PLazyExceptOut]: TLC warns and skips the clause); else
--                  the new value (inherited keepLazy) at x, the other entries untouched.
--   <<...>>, [f |-> e, ...]   the elements with the inherited keepLazy; a tuple or record
--                  holding a lazy element is an `fnX` ([LazyTuple], [LazyTupleKeep],
--                  [PLazyRecGetKeep]); a record in `mkRecord`'s order and with its refusal.
--   Head, Tail     the operand with the inherited keepLazy; an `fnX` tuple: the first entry,
--                  or the others renumbered, unforced; a `lazyFn` over exactly 1..n: TLC's
--                  toTuple runs the body at EVERY index first ([PLazyHeadFn] divZero); any
--                  other function `typeErr` (toTuple is null, row 168); a lazy domain
--                  `Tlc.todo` (B1A-17b).
--   force          a `val` is itself; an `fnX` forces its entries in key order (TupleValue and
--                  RecordValue fingerprint their entries in order); a `lazyFn` (toFcnRcd):
--                  FcnParams.size() first, so a Nat, Int or STRING domain is `typeErr`
--                  ([PLazyForceNat], row 144) and any other domain that is not a finite set
--                  `Tlc.todo` (B1A-17b's enumAll); then the body at every context, first
--                  binder fastest, under keepLazy ON, and only then each value forced in key
--                  order ([PLazyForceOrder]: chooseFailed at the second point before the
--                  first point's lazy value raises). KeepLazy ON is the captured control
--                  exactly: a `lazyFn` all of whose domains are finite sets was built under
--                  KeepLazy (else `Tlc.rule.materializeQFn` would have materialized it).
-- Every other PrimOp with a lazy operand is still `Tlc.opX`'s `Tlc.todo` (B1A-17a/17b).

-- `Tlc.rhsX go k env s p e`: an item's right-hand side: e under `Tlc.rule.keepLazyReset k`
-- (TLC evaluates it under Clear, Tool.java:1361, 1366); the item machine (B1A-18) calls it.
def Tlc.rhsX (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (e : Expr) : Res XVal :=
  Tlc.goEvalX go (Tlc.rule.keepLazyReset k) env s p e

-- `Tlc.xOfGen g`: a domain as an executable value: `ofVal v` is `val v`, else a lazy set.
def Tlc.xOfGen (g : SetGen) : XVal :=
  SetGen.elim g (fun v => XVal.val v) (fun _ => XVal.lazySet g) (fun _ _ => XVal.lazySet g)
    (fun _ => XVal.lazySet g) (fun _ => XVal.lazySet g) (fun _ _ _ => XVal.lazySet g)

-- `Tlc.genOf x`: an evaluated constructor domain as a SetGen: a `val` is `ofVal`, a lazy set
-- its generator; a function used as a domain is `Tlc.todo` (B1A-17b).
def Tlc.genOf (x : XVal) : Res SetGen :=
  XVal.elim x (fun v => Res.ok (SetGen.ofVal v)) (fun _ _ _ => Tlc.todo) (fun _ => Tlc.todo)
    (fun g => Res.ok g)

-- `Tlc.gensOf xs`: every domain's generator, in order.
def Tlc.gensOf (xs : List XVal) : Res (List SetGen) :=
  @List.rec XVal (fun _ => Res (List SetGen)) (Res.ok [])
    (fun x _ rest => Res.bind (Tlc.genOf x) (fun g => Res.map (fun gs => List.cons g gs) rest))
    xs

-- `Tlc.entryVals ps`: the entries as values when every one is forced.
def Tlc.entryVals (ps : List (Prod Value XVal)) : Option (List (Prod Value Value)) :=
  @List.rec (Prod Value XVal) (fun _ => Option (List (Prod Value Value))) (Option.some [])
    (fun q _ rest => XVal.elim (Prod.snd q)
      (fun v => @Option.casesOn (List (Prod Value Value)) (fun _ => Option (List (Prod Value Value)))
        rest Option.none (fun qs => Option.some (List.cons (Prod.mk (Prod.fst q) v) qs)))
      (fun _ _ _ => Option.none) (fun _ => Option.none) (fun _ => Option.none))
    ps

-- `Tlc.mkFnX ps`: the function with the canonical keys of ps: a `val` when every entry is
-- forced, else an `fnX` (TLC holds both as one FcnRcdValue/TupleValue/RecordValue).
def Tlc.mkFnX (ps : List (Prod Value XVal)) : XVal :=
  @Option.casesOn (List (Prod Value Value)) (fun _ => XVal) (Tlc.entryVals ps) (XVal.fnX ps)
    (fun qs => XVal.val (Value.fn qs))

-- `Tlc.indexX xs i`: (i, x1), (i+1, x2), ...: the entries of a tuple.
def Tlc.indexX (xs : List XVal) : Nat → List (Prod Value XVal) :=
  @List.rec XVal (fun _ => Nat → List (Prod Value XVal)) (fun _ => [])
    (fun x _ next i => List.cons (Prod.mk (Value.int (Int.ofNat i)) x) (next (Nat.succ i))) xs

-- `Tlc.ctxKey one xs`: a context's key: the element itself for one binder, else the tuple.
def Tlc.ctxKey (one : Bool) (xs : List Value) : Value :=
  @Bool.rec (fun _ => Value) (mkTuple xs)
    (@List.casesOn Value (fun _ => Value) xs (mkTuple xs) (fun x _ => x)) one

-- `Tlc.bodiesAt go k env s p body one cs`: the body at every context of cs in order, under
-- keepLazy k, each value kept as evaluated; the first error wins.
def Tlc.bodiesAt (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (body : Expr) (one : Bool) (cs : List (List Value)) : Res (List (Prod Value XVal)) :=
  @List.rec (List Value) (fun _ => Res (List (Prod Value XVal))) (Res.ok [])
    (fun xs _ rest => Res.bind (Tlc.goEvalX go k (Tlc.pushAll xs env) s p body)
      (fun x => Res.map (fun ps => List.cons (Prod.mk (Tlc.ctxKey one xs) x) ps) rest))
    cs

-- `Tlc.insertKey q ps`: q inserted into ps, ascending by key in TLC's order (a comparison
-- error is the named refusal, B1A-D96).
def Tlc.insertKey (q : Prod Value XVal) (ps : List (Prod Value XVal)) :
    Res (List (Prod Value XVal)) :=
  @List.rec (Prod Value XVal) (fun _ => Res (List (Prod Value XVal))) (Res.ok [q])
    (fun r rs next => Res.bind (Prim.defer (tlcLt (Prod.fst q) (Prod.fst r)))
      (fun b => @Bool.rec (fun _ => Res (List (Prod Value XVal)))
        (Res.map (fun t => List.cons r t) next) (Res.ok (List.cons q (List.cons r rs))) b))
    ps

-- `Tlc.keyed one ps`: the entries in key order: as they are for one binder (the contexts run
-- in the domain's canonical order), sorted for several (first binder fastest is not TLC's
-- tuple order).
def Tlc.keyed (one : Bool) (ps : List (Prod Value XVal)) : Res (List (Prod Value XVal)) :=
  @Bool.rec (fun _ => Res (List (Prod Value XVal)))
    (@List.rec (Prod Value XVal) (fun _ => Res (List (Prod Value XVal))) (Res.ok [])
      (fun q _ rest => Res.bind rest (fun t => Tlc.insertKey q t)) ps)
    (Res.ok ps) one

-- `Tlc.setElems x`: the elements of a `val` finite set (empty for anything else; called only
-- when every domain is Reducible).
def Tlc.setElems (x : XVal) : List Value :=
  XVal.elim x (fun v => @Option.casesOn (List Value) (fun _ => List Value) (Value.asSet v) []
    (fun ys => ys)) (fun _ _ _ => []) (fun _ => []) (fun _ => [])

-- `Tlc.materialize go k env s p body xs`: a constructor materialized at construction (row 1).
def Tlc.materialize (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (body : Expr) (xs : List XVal) : Res XVal :=
  Res.bind (Tlc.bodiesAt go k env s p body (Nat.beq (List.length xs) 1)
      (Tlc.contexts (List.map Tlc.setElems xs)))
    (fun ps => Res.map Tlc.mkFnX (Tlc.keyed (Nat.beq (List.length xs) 1) ps))

-- `Tlc.qFnX go k env s p ds body`: `[x \in S, ... |-> body]` (row 1).
def Tlc.qFnX (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (ds : List Expr) (body : Expr) : Res XVal :=
  Res.bind (Tlc.evalOps go k env s p ds) (fun xs0 =>
    Res.bind (Tlc.rule.forceCtorDomains (Tlc.goForce go s) xs0) (fun xs =>
      @Bool.rec (fun _ => Res XVal)
        (Res.map (fun gs => XVal.lazyFn gs body (Ctx.mk env p)) (Tlc.gensOf xs))
        (Tlc.materialize go k env s p body xs)
        (Tlc.rule.materializeQFn k xs)))

-- `Tlc.lookupX ps a`: the entry at the key equal to a, `none` when there is none; a key of
-- another kind than a is the named refusal (`keyEqWith`, as `Prim.lookup`).
def Tlc.lookupX (ps : List (Prod Value XVal)) (a : Value) : Res (Option XVal) :=
  @List.rec (Prod Value XVal) (fun _ => Res (Option XVal)) (Res.ok Option.none)
    (fun q _ rest => Res.bind (keyEqWith valueEq (Prod.fst q) a)
      (fun b => @Bool.rec (fun _ => Res (Option XVal)) rest (Res.ok (Option.some (Prod.snd q))) b))
    ps

-- `Tlc.replaceX ps x v`: ps with the entry at the key equal to x replaced by v.
def Tlc.replaceX (ps : List (Prod Value XVal)) (x : Value) (v : XVal) :
    Res (List (Prod Value XVal)) :=
  @List.rec (Prod Value XVal) (fun _ => Res (List (Prod Value XVal))) (Res.ok [])
    (fun q tl rest => Res.bind (keyEqWith valueEq (Prod.fst q) x)
      (fun b => @Bool.rec (fun _ => Res (List (Prod Value XVal)))
        (Res.map (fun r => List.cons q r) rest)
        (Res.ok (List.cons (Prod.mk (Prod.fst q) v) tl)) b))
    ps

-- `Tlc.seqFromX ps i`: the entries of ps when its keys are exactly i, i+1, ... in order.
def Tlc.seqFromX (ps : List (Prod Value XVal)) : Nat → Option (List XVal) :=
  @List.rec (Prod Value XVal) (fun _ => Nat → Option (List XVal)) (fun _ => Option.some [])
    (fun q _ next i => @Option.casesOn Int (fun _ => Option (List XVal)) (Value.asInt (Prod.fst q))
      Option.none
      (fun n => @Bool.rec (fun _ => Option (List XVal)) Option.none
        (@Option.casesOn (List XVal) (fun _ => Option (List XVal)) (next (Nat.succ i)) Option.none
          (fun xs => Option.some (List.cons (Prod.snd q) xs)))
        (intBeq n (Int.ofNat i))))
    ps

-- `Tlc.oneToN ys i`: ys are exactly the integers i, i+1, ... in order.
def Tlc.oneToN (ys : List Value) : Nat → Bool :=
  @List.rec Value (fun _ => Nat → Bool) (fun _ => true)
    (fun y _ next i => @Option.casesOn Int (fun _ => Bool) (Value.asInt y) false
      (fun n => Bool.and (intBeq n (Int.ofNat i)) (next (Nat.succ i))))
    ys

-- `Tlc.memAll go s ds xs`: each value of xs in its domain of ds, in order, the first FALSE
-- deciding (xs at least as long as ds).
def Tlc.memAll (go : Job → Res Out) (s : State) (ds : List SetGen) : List Value → Res Bool :=
  @List.rec SetGen (fun _ => List Value → Res Bool) (fun _ => Res.ok true)
    (fun d _ next xs => @List.casesOn Value (fun _ => Res Bool) xs (Res.ok false)
      (fun x rest => Res.bind (Tlc.goMemX go s (Tlc.xOfGen d) x)
        (fun b => @Bool.rec (fun _ => Res Bool) (Res.ok false) (next rest) b)))
    ds

-- `Tlc.inDomains go s ds a`: the binder values when a is in the domain of a `lazyFn` over ds,
-- `none` when it is not (FcnLambdaValue.apply's test).
def Tlc.inDomains (go : Job → Res Out) (s : State) (ds : List SetGen) (a : Value) :
    Res (Option (List Value)) :=
  @List.casesOn SetGen (fun _ => Res (Option (List Value))) ds Tlc.illFormed
    (fun d rest => @List.casesOn SetGen (fun _ => Res (Option (List Value))) rest
      -- one binder: memX of a in its domain
      (Res.map (fun b => @Bool.rec (fun _ => Option (List Value)) Option.none (Option.some [a]) b)
        (Tlc.goMemX go s (Tlc.xOfGen d) a))
      -- several: a tuple with at least as many components, each tested in order
      (fun _ _ => @Option.casesOn (List (Prod Value Value)) (fun _ => Res (Option (List Value)))
        (Value.asFn a) Tlc.todo
        (fun ps => @Option.casesOn (List Value) (fun _ => Res (Option (List Value)))
          (Prim.seqFrom ps 1) Tlc.todo
          (fun xs => @Bool.rec (fun _ => Res (Option (List Value))) Tlc.todo
            (Res.map (fun b => @Bool.rec (fun _ => Option (List Value)) Option.none
                (Option.some (Prim.take (List.length ds) xs)) b)
              (Tlc.memAll go s ds xs))
            (Nat.ble (List.length ds) (List.length xs))))))

-- `Tlc.forceDomain g`: a lazy function's domain enumerated for forcing: a finite set's
-- elements; Nat, Int or STRING `typeErr` (their size() raises, [PLazyForceNat], row 144);
-- anything else `Tlc.todo` (B1A-17b).
def Tlc.forceDomain (g : SetGen) : Res (List Value) :=
  SetGen.elim g
    (fun v => @Option.casesOn (List Value) (fun _ => Res (List Value)) (Value.asSet v)
      (@Option.casesOn (Prod InfKind (List Value)) (fun _ => Res (List Value)) (Value.asInfSet v)
        Tlc.todo
        (fun q => @Bool.rec (fun _ => Res (List Value)) Tlc.todo (Res.error Fail.typeErr)
          (Nat.blt (InfKind.tag (Prod.fst q)) 3)))
      (fun ys => Res.ok ys))
    (fun _ => Tlc.todo) (fun _ _ => Tlc.todo) (fun _ => Tlc.todo) (fun _ => Tlc.todo)
    (fun _ _ _ => Tlc.todo)

-- `Tlc.forceDomains gs`: every domain's elements, in binder order; the first error wins.
def Tlc.forceDomains (gs : List SetGen) : Res (List (List Value)) :=
  @List.rec SetGen (fun _ => Res (List (List Value))) (Res.ok [])
    (fun g _ rest => Res.bind (Tlc.forceDomain g) (fun ys => Res.map (fun yss => List.cons ys yss) rest))
    gs

-- `Tlc.forceVals go s ps`: every entry forced, in order.
def Tlc.forceVals (go : Job → Res Out) (s : State) (ps : List (Prod Value XVal)) :
    Res (List (Prod Value Value)) :=
  @List.rec (Prod Value XVal) (fun _ => Res (List (Prod Value Value))) (Res.ok [])
    (fun q _ rest => Res.bind (Tlc.goForce go s (Prod.snd q))
      (fun v => Res.map (fun qs => List.cons (Prod.mk (Prod.fst q) v) qs) rest))
    ps

-- `Tlc.lazyTuple go s ds e c`: a `lazyFn` as a tuple (FcnLambdaValue.toTuple): one binder
-- over exactly 1..n, the body at every index under keepLazy on (captured, see `force`);
-- another function `typeErr`; a domain that is not a finite set `Tlc.todo` (B1A-17b).
def Tlc.lazyTuple (go : Job → Res Out) (s : State) (ds : List SetGen) (e : Expr) (c : Ctx) :
    Res (List XVal) :=
  @List.casesOn SetGen (fun _ => Res (List XVal)) ds Tlc.illFormed
    (fun d rest => @List.casesOn SetGen (fun _ => Res (List XVal)) rest
      (SetGen.elim d
        (fun v => @Option.casesOn (List Value) (fun _ => Res (List XVal)) (Value.asSet v) Tlc.todo
          (fun ys => @Bool.rec (fun _ => Res (List XVal)) (Res.error Fail.typeErr)
            (Res.map (fun ps => List.map (@Prod.snd Value XVal) ps)
              (Tlc.bodiesAt go true (Ctx.env c) s (Ctx.post c) e true
                (List.map (fun y => [y]) ys)))
            (Tlc.oneToN ys 1)))
        (fun _ => Tlc.todo) (fun _ _ => Tlc.todo) (fun _ => Tlc.todo) (fun _ => Tlc.todo)
        (fun _ _ _ => Tlc.todo))
      (fun _ _ => Res.error Fail.typeErr))

-- `Tlc.headTail isHead xs`: Head (the first element, unforced) or Tail (the others,
-- renumbered from 1) of the tuple's elements xs; empty `notInDomain` (rows 110, 111).
def Tlc.headTail (isHead : Bool) (xs : List XVal) : Res XVal :=
  @List.casesOn XVal (fun _ => Res XVal) xs (Res.error Fail.notInDomain)
    (fun h t => @Bool.rec (fun _ => Res XVal) (Res.ok (Tlc.mkFnX (Tlc.indexX t 1))) (Res.ok h)
      isHead)

-- `Tlc.isFnX f`: f is a value TLC applies (a FunctionValue): a `val` function, a `lazyFn`,
-- an `fnX`.
def Tlc.isFnX (f : XVal) : Bool :=
  XVal.elim f
    (fun v => @Option.casesOn (List (Prod Value Value)) (fun _ => Bool) (Value.asFn v) false
      (fun _ => true))
    (fun _ _ _ => true) (fun _ => true) (fun _ => false)

-- `Tlc.argVal x k`: k on a forced argument; a lazy one is `unmodeled lazy.arg` (10:615).
def Tlc.argVal {α : Type} (x : XVal) (k : Value → Res α) : Res α :=
  XVal.elim x k (fun _ _ _ => Res.error (Fail.unmodeled Code.lazyArg))
    (fun _ => Res.error (Fail.unmodeled Code.lazyArg))
    (fun _ => Res.error (Fail.unmodeled Code.lazyArg))

-- `Tlc.argE1 args k` .. `Tlc.argE3`: k on exactly one, two or three operand expressions; any
-- other number is `Tlc.illFormed` (B1A-D95, as `Prim.args1`).
def Tlc.argE1 {α : Type} (args : List Expr) (k : Expr → Res α) : Res α :=
  @List.casesOn Expr (fun _ => Res α) args Tlc.illFormed
    (fun a r => @List.casesOn Expr (fun _ => Res α) r (k a) (fun _ _ => Tlc.illFormed))
def Tlc.argE2 {α : Type} (args : List Expr) (k : Expr → Expr → Res α) : Res α :=
  @List.casesOn Expr (fun _ => Res α) args Tlc.illFormed (fun a r => Tlc.argE1 r (fun b => k a b))
def Tlc.argE3 {α : Type} (args : List Expr) (k : Expr → Expr → Expr → Res α) : Res α :=
  @List.casesOn Expr (fun _ => Res α) args Tlc.illFormed
    (fun a r => Tlc.argE2 r (fun b c => k a b c))

-- `Tlc.applyOpX go k env s p fE aE`: `fE[aE]` (func.apply, seq.index, tuple.get).
def Tlc.applyOpX (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (fE aE : Expr) : Res XVal :=
  Res.bind (Tlc.goEvalX go true env s p fE) (fun f =>
    @Bool.rec (fun _ => Res XVal) (Res.error Fail.typeErr)
      (Res.bind (Tlc.goEvalX go k env s p aE)
        (fun ax => Tlc.argVal ax (fun a => Tlc.goApplyX go k s f a)))
      (Tlc.isFnX f))

-- `Tlc.okEntry o`: a looked-up entry, `notInDomain` when there is none.
def Tlc.okEntry (o : Option XVal) : Res XVal :=
  @Option.casesOn XVal (fun _ => Res XVal) o (Res.error Fail.notInDomain) (fun x => Res.ok x)

-- `Tlc.recGetX go k env s p fld rE`: `rE.fld` (rec.get).
def Tlc.recGetX (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (fld : Nat) (rE : Expr) : Res XVal :=
  Res.bind (Tlc.goEvalX go k env s p rE) (fun r => XVal.elim r
    (fun v => Res.map XVal.val (Prim.apply v (Value.str fld)))
    (fun _ _ _ => Res.bind (Tlc.goForce go s r)
      (fun v => Res.map XVal.val (Prim.apply v (Value.str fld))))
    (fun ps => Res.bind (Tlc.lookupX ps (Value.str fld)) Tlc.okEntry)
    (fun _ => Res.error Fail.typeErr))

-- `Tlc.domainX go k env s p fE`: `DOMAIN fE` (func.domain).
def Tlc.domainX (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (fE : Expr) : Res XVal :=
  Res.bind (Tlc.goEvalX go k env s p fE) (fun f => XVal.elim f
    (fun v => @Option.casesOn (List (Prod Value Value)) (fun _ => Res XVal) (Value.asFn v)
      Prim.typeErr (fun ps => Res.ok (XVal.val (Value.set (keysOf ps)))))
    (fun ds _ _ => @List.casesOn SetGen (fun _ => Res XVal) ds Tlc.illFormed
      (fun d rest => @List.casesOn SetGen (fun _ => Res XVal) rest (Res.ok (Tlc.xOfGen d))
        (fun _ _ => Res.ok (XVal.lazySet (SetGen.prod ds)))))
    (fun ps => Res.ok (XVal.val (Value.set (keysOfX ps))))
    (fun _ => Prim.typeErr))

-- `Tlc.exceptAt go k env s p ps xx vE`: the EXCEPT clause at the point xx on the entries ps.
def Tlc.exceptAt (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (ps : List (Prod Value XVal)) (xx : XVal) (vE : Expr) : Res XVal :=
  XVal.elim xx
    (fun x => Res.bind (Tlc.lookupX ps x) (fun o =>
      @Option.casesOn XVal (fun _ => Res XVal) o (Res.ok (Tlc.mkFnX ps))
        (fun _ => Res.bind (Tlc.goEvalX go k env s p vE)
          (fun vx => Res.map Tlc.mkFnX (Tlc.replaceX ps x vx)))))
    (fun _ _ _ => Tlc.todo) (fun _ => Tlc.todo) (fun _ => Tlc.todo)

-- `Tlc.exceptX go k env s p fE xE vE`: `[fE EXCEPT ![xE] = vE]` (func.except, rec.with).
def Tlc.exceptX (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (fE xE vE : Expr) : Res XVal :=
  Res.bind (Tlc.goEvalX go k env s p fE) (fun f =>
    Res.bind (Tlc.goEvalX go k env s p xE) (fun xx => XVal.elim f
      (fun fv => @Option.casesOn (List (Prod Value Value)) (fun _ => Res XVal) (Value.asFn fv)
        Prim.typeErr
        (fun ps => Tlc.exceptAt go k env s p
          (@List.map (Prod Value Value) (Prod Value XVal)
            (fun q => Prod.mk (Prod.fst q) (XVal.val (Prod.snd q))) ps) xx vE))
      (fun _ _ _ => Res.error (Fail.unmodeled Code.lazyExcept))
      (fun ps => Tlc.exceptAt go k env s p ps xx vE)
      (fun _ => Prim.typeErr)))

-- `Tlc.headTailX sp go k env s p o isHead sE`: Head(sE) or Tail(sE); a forced operand is
-- `PrimOp.evalV`'s (o is seq.head or seq.tail).
def Tlc.headTailX (sp : Spec) (go : Job → Res Out) (k : Bool) (env : List Value) (s : State)
    (p : Frame) (o : PrimOp) (isHead : Bool) (sE : Expr) : Res XVal :=
  Res.bind (Tlc.goEvalX go k env s p sE) (fun sx => XVal.elim sx
    (fun v => Res.map XVal.val (PrimOp.evalV sp.intMode [v] o))
    (fun ds e c => Res.bind (Tlc.lazyTuple go s ds e c) (Tlc.headTail isHead))
    (fun ps => @Option.casesOn (List XVal) (fun _ => Res XVal) (Tlc.seqFromX ps 1) Prim.typeErr
      (Tlc.headTail isHead))
    (fun _ => Prim.typeErr))

-- `Tlc.atPositions xs ps`: each pair (key, position i) of ps as (key, the i-th of xs).
def Tlc.atPositions (xs : List XVal) (ps : List (Prod Value Value)) :
    Res (List (Prod Value XVal)) :=
  @List.rec (Prod Value Value) (fun _ => Res (List (Prod Value XVal))) (Res.ok [])
    (fun q _ rest => @Option.casesOn Int (fun _ => Res (List (Prod Value XVal)))
      (Value.asInt (Prod.snd q)) Tlc.illFormed
      (fun i => Tlc.at xs (natAbs i)
        (fun x => Res.map (fun r => List.cons (Prod.mk (Prod.fst q) x) r) rest)))
    ps

-- `Tlc.recordX fs xs`: the record of the fields fs (name ranks, source order) holding xs,
-- in `mkRecord`'s order and with its refusal (B1A-D93): mkRecord over the positions, which
-- are then replaced by the elements.
def Tlc.recordX (fs : List Nat) (xs : List XVal) : Res XVal :=
  Res.bind (mkRecord (Prim.fields fs (Prim.rangeFrom 0 (List.length xs)))) (fun r =>
    @Option.casesOn (List (Prod Value Value)) (fun _ => Res XVal) (Value.asFn r) Tlc.illFormed
      (fun ps => Res.map Tlc.mkFnX (Tlc.atPositions xs ps)))

-- `Tlc.opLazyX sp go k env s p o args`: an `op` node: the PrimOps that read a function have
-- their own operand rows above; every other one is `Tlc.opX`.
def Tlc.opLazyX (sp : Spec) (go : Job → Res Out) (k : Bool) (env : List Value) (s : State)
    (p : Frame) (o : PrimOp) (args : List Expr) : Res XVal :=
  @PrimOp.casesOn (fun _ => Res XVal) o
    -- intAdd intSub intMul intDiv intMod intNeg intLt intLe
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    -- recGet field, recWith field
    (fun f => Tlc.argE1 args (fun rE => Tlc.recGetX go k env s p f rE))
    (fun f => Tlc.argE2 args (fun rE vE =>
      Tlc.exceptX go k env s p rE (Expr.lit (Value.str f)) vE))
    -- funcApply funcExcept funcDomain
    (Tlc.argE2 args (fun fE aE => Tlc.applyOpX go k env s p fE aE))
    (Tlc.argE3 args (fun fE xE vE => Tlc.exceptX go k env s p fE xE vE))
    (Tlc.argE1 args (fun fE => Tlc.domainX go k env s p fE))
    -- setIn setInsert setUnion setDiff setCard setSubseteq
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    -- seqLen seqIndex seqAppend seqHead seqTail seqSubseq
    (Tlc.opX sp go k env s p o args)
    (Tlc.argE2 args (fun sE iE => Tlc.applyOpX go k env s p sE iE))
    (Tlc.opX sp go k env s p o args)
    (Tlc.argE1 args (fun sE => Tlc.headTailX sp go k env s p o true sE))
    (Tlc.argE1 args (fun sE => Tlc.headTailX sp go k env s p o false sE))
    (Tlc.opX sp go k env s p o args)
    -- valueEq valueNe
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    -- setEnum setRange setIntersect setBigUnion setPowerset setProduct setIsFinite
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    (Tlc.opX sp go k env s p o args)
    -- funcSet
    (Tlc.opX sp go k env s p o args)
    -- recNew fields: the fields with the inherited keepLazy, lazy ones kept; recSetOf fields
    (fun fs => Res.bind (Tlc.evalOps go k env s p args) (fun xs =>
      @Bool.rec (fun _ => Res XVal) Tlc.illFormed (Tlc.recordX fs xs)
        (Nat.beq (List.length fs) (List.length xs))))
    (fun _ => Tlc.opX sp go k env s p o args)
    -- tupleNew: the elements with the inherited keepLazy, lazy ones kept
    (Res.map (fun xs => Tlc.mkFnX (Tlc.indexX xs 1)) (Tlc.evalOps go k env s p args))
    -- tupleGet index
    (fun i => Tlc.argE1 args (fun tE =>
      Tlc.applyOpX go k env s p tE (Expr.lit (Value.int (Int.ofNat i)))))
    -- seqConcat seqSet seqRemoveAt
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    (Tlc.opX sp go k env s p o args)
    -- valueAsBool
    (Tlc.opX sp go k env s p o args)
    -- intPow intGt intGe natSuccU natSatU assert
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)
    (Tlc.opX sp go k env s p o args) (Tlc.opX sp go k env s p o args)

-- `Tlc.quantX`: the quantifier forms (10:128, 10:142); qFn is `Tlc.qFnX` (B1A-16).
def Tlc.quantX (go : Job → Res Out) (k : Bool) (env : List Value) (s : State) (p : Frame)
    (q : QKind) (ds : List Expr) (body : Expr) : Res XVal :=
  @QKind.casesOn (fun _ => Res XVal) q
    -- qEx
    (Tlc.someBinders ds (Res.bind (Tlc.evalDomains go k env s p ds)
      (fun dss => Res.map Tlc.boolX (Tlc.exLoop go k env s p body (Tlc.contexts dss)))))
    -- qAll
    (Tlc.someBinders ds (Res.bind (Tlc.evalDomains go k env s p ds)
      (fun dss => Res.map Tlc.boolX (Tlc.allLoop go k env s p body (Tlc.contexts dss)))))
    -- qChoose
    (Tlc.oneBinder ds (fun d =>
      Res.bind (Res.bind (Tlc.goEvalX go k env s p d) Tlc.domainOf)
        (fun xs => Res.map XVal.val (Tlc.chooseLoop go k env s p body xs))))
    -- qFilter
    (Tlc.oneBinder ds (fun d =>
      Res.bind (Tlc.goEvalX go k env s p d)
        (fun base => @Bool.rec (fun _ => Res XVal)
          Tlc.todo
          (Res.bind (Tlc.domainOf base)
            (fun xs => Res.map (fun ys => XVal.val (Value.set ys))
              (Tlc.filterLoop go k env s p body xs)))
          (Tlc.rule.eagerFilter base))))
    -- qMap (normalized as the EP reports it, B1A-D96)
    (Tlc.someBinders ds (Res.bind (Tlc.evalDomains go k env s p ds)
      (fun dss => Res.bind (Tlc.mapLoop go k env s p body (Tlc.contexts dss))
        (fun vs => Res.map (fun ys => XVal.val (Value.set ys)) (Tlc.normDefer vs)))))
    -- qFn (B1A-16)
    (Tlc.someBinders ds (Tlc.qFnX go k env s p ds body))

-- One step of each design function, given the block at the next lower fuel as `go`.
-- `Tlc.stepEvalX` (B1A-14b): the core cases above, one-type dispatch on Expr through
-- `Expr.casesOn` (every motive, B1A-D70).
def Tlc.stepEvalX (sp : Spec) (go : Job → Res Out) (k : Bool) (env : List Value)
    (s : State) (p : Frame) (e : Expr) : Res XVal :=
  @Expr.casesOn
    (fun _ => Res XVal) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat)
    e
    -- lit, cur, nxt, bvar, pool
    (fun v => Res.ok (XVal.val v))
    (fun n => Tlc.at s n (fun v => Res.ok (XVal.val v)))
    (fun n => Tlc.at p n (fun o =>
      @Option.casesOn XVal (fun _ => Res XVal) o (Res.error Fail.unassignedPrime)
        (fun x => Res.ok x)))
    (fun j => Tlc.at env j (fun v => Res.ok (XVal.val v)))
    (fun i => Tlc.at sp.pool i (fun d => Tlc.goEvalX go k [] s p d))
    -- op (B1A-15; the operand rows of B1A-16)
    (fun o args => Tlc.opLazyX sp go k env s p o args)
    -- ite
    (fun c t f => Tlc.ifB (Res.bind (Tlc.goEvalX go k env s p c) Tlc.truth)
      (Tlc.goEvalX go k env s p t) (Tlc.goEvalX go k env s p f))
    -- caseOf
    (fun arms other => Tlc.caseX go k env s p arms other)
    -- letLazy
    (fun d b => Tlc.goEvalX go k env s p (Expr.subst [d] b))
    -- quant
    (fun q ds body => Tlc.quantX go k env s p q ds body)
    -- app
    (fun i args => Tlc.appX sp go k env s p i args)
    -- enabled: B1A-19
    (fun _ => Tlc.todo)
    -- the other eleven types' minors: unused
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ => 0)
    0 (fun _ _ => 0)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)

-- `Tlc.stepForce` (B1A-14b, B1A-16): materialize, in TLC's order (see the laziness section
-- above): a `val` is itself; an `fnX` its entries forced in key order; a `lazyFn` the body at
-- every context under keepLazy on, then every value forced in key order; a lazy set is
-- B1A-17b's (its `ofVal` generator is its value).
def Tlc.stepForce (_sp : Spec) (go : Job → Res Out) (s : State) (x : XVal) : Res Value :=
  XVal.elim x (fun v => Res.ok v)
    (fun ds e c => Res.bind (Tlc.forceDomains ds) (fun dss =>
      Res.bind (Tlc.bodiesAt go true (Ctx.env c) s (Ctx.post c) e (Nat.beq (List.length ds) 1)
          (Tlc.contexts dss))
        (fun ps => Res.bind (Tlc.keyed (Nat.beq (List.length ds) 1) ps)
          (fun qs => Res.map Value.fn (Tlc.forceVals go s qs)))))
    (fun ps => Res.map Value.fn (Tlc.forceVals go s ps))
    (fun g => SetGen.elim g (fun v => Res.ok v) (fun _ => Tlc.todo) (fun _ _ => Tlc.todo)
      (fun _ => Tlc.todo) (fun _ => Tlc.todo) (fun _ _ _ => Tlc.todo))
-- `Tlc.stepApplyX` (B1A-16): `f[a]`, pointwise (forcing-table rows 3 and 4).
def Tlc.stepApplyX (_sp : Spec) (go : Job → Res Out) (k : Bool) (s : State) (f : XVal)
    (a : Value) : Res XVal :=
  XVal.elim f
    (fun v => Res.map XVal.val (Prim.apply v a))
    (fun ds e c => Res.bind (Tlc.inDomains go s ds a) (fun o =>
      @Option.casesOn (List Value) (fun _ => Res XVal) o (Res.error Fail.notInDomain)
        (fun xs => Tlc.goEvalX go k (Tlc.pushAll xs (Ctx.env c)) s (Ctx.post c) e)))
    (fun ps => Res.bind (Tlc.lookupX ps a) Tlc.okEntry)
    (fun _ => Prim.typeErr)
-- `Tlc.stepMemX` (B1A-16's part): `v \in x` for a forced set or an `ofVal` generator
-- (`Prim.mem`); a function is not a set (`typeErr`); the other lazy sets are B1A-17a's.
def Tlc.stepMemX (_sp : Spec) (_go : Job → Res Out) (_s : State) (x : XVal) (v : Value) :
    Res Bool :=
  XVal.elim x (fun S => Prim.mem v S) (fun _ _ _ => Prim.typeErr) (fun _ => Prim.typeErr)
    (fun g => SetGen.elim g (fun S => Prim.mem v S) (fun _ => Tlc.todo) (fun _ _ => Tlc.todo)
      (fun _ => Tlc.todo) (fun _ => Tlc.todo) (fun _ _ _ => Tlc.todo))
def Tlc.stepEnumNext (_sp : Spec) (_go : Job → Res Out) (_s : State) (_g : SetGen) (_i : Nat) :
    Res (Option (Prod Value Nat)) :=
  Tlc.todo
def Tlc.stepEnumAll (_sp : Spec) (_go : Job → Res Out) (_s : State) (_g : SetGen) :
    Res (List Value) :=
  Tlc.todo
def Tlc.stepEnumF (_sp : Spec) (_go : Job → Res Out) (_env : List Value) (_a : Act)
    (_s : State) : Res (List State) :=
  Tlc.todo
def Tlc.stepEnabledF (_sp : Spec) (_go : Job → Res Out) (_env : List Value) (_a : Act)
    (_s : State) : Res Bool :=
  Tlc.todo
def Tlc.stepHoldsF (_sp : Spec) (_go : Job → Res Out) (_env : List Value) (_a : Act)
    (_s _t : State) : Res Bool :=
  Tlc.todo

-- `Tlc.step sp go`: the non-recursive step (B1A-D07): the job's own step, its answer
-- tagged with the job's result type.
def Tlc.step (sp : Spec) (go : Job → Res Out) : Job → Res Out :=
  fun j => @Job.casesOn (fun _ => Res Out) j
    (fun k env s p e => Res.map Out.xval (Tlc.stepEvalX sp go k env s p e))
    (fun s x => Res.map Out.value (Tlc.stepForce sp go s x))
    (fun k s f a => Res.map Out.xval (Tlc.stepApplyX sp go k s f a))
    (fun s x v => Res.map Out.bool (Tlc.stepMemX sp go s x v))
    (fun s g i => Res.map Out.next (Tlc.stepEnumNext sp go s g i))
    (fun s g => Res.map Out.values (Tlc.stepEnumAll sp go s g))
    (fun env a s => Res.map Out.states (Tlc.stepEnumF sp go env a s))
    (fun env a s => Res.map Out.bool (Tlc.stepEnabledF sp go env a s))
    (fun env a s t => Res.map Out.bool (Tlc.stepHoldsF sp go env a s t))

-- `Tlc.run sp n`: the block at fuel n, a `Nat.rec` over fuel (B1A-D07).
def Tlc.run (sp : Spec) (n : Nat) : Job → Res Out :=
  @Nat.rec (fun _ => Job → Res Out) (fun _ => Res.error Fail.fuel) (fun _ go => Tlc.step sp go) n

-- ---- The nine design functions (10:285-298), exactly their signatures ----

-- `evalX sp n k env s p e` (10:286): fuel, keepLazy (TLC's EvalControl.KeepLazy), the
-- quantifier-bound values, the state, the primed frame.
def evalX (sp : Spec) : Nat → Bool → List Value → State → Frame → Expr → Res XVal :=
  fun n k env s p e => Tlc.goEvalX (Tlc.run sp n) k env s p e

-- `force sp n s x` (10:288): materialize, in TLC's order.
def force (sp : Spec) : Nat → State → XVal → Res Value :=
  fun n s x => Tlc.goForce (Tlc.run sp n) s x

-- `applyX sp n k s f a` (10:289): `f[a]`, pointwise.
def applyX (sp : Spec) : Nat → Bool → State → XVal → Value → Res XVal :=
  fun n k s f a => Tlc.goApplyX (Tlc.run sp n) k s f a

-- `memX sp n s x v` (10:290): `v \in x`, pointwise.
def memX (sp : Spec) : Nat → State → XVal → Value → Res Bool :=
  fun n s x v => Tlc.goMemX (Tlc.run sp n) s x v

-- `enumNext sp n s g i` (10:291-293): the next member at or after position i, in TLC's
-- order; predicates run only up to the member returned.
def enumNext (sp : Spec) : Nat → State → SetGen → Nat → Res (Option (Value × Nat)) :=
  fun n s g i => Tlc.goEnumNext (Tlc.run sp n) s g i

-- `enumAll sp n s g` (10:294): `enumNext` to exhaustion.
def enumAll (sp : Spec) : Nat → State → SetGen → Res (List Value) :=
  fun n s g => Tlc.goEnumAll (Tlc.run sp n) s g

-- `tlcEnumF sp n env a s` (10:295): generate mode.
def tlcEnumF (sp : Spec) : Nat → List Value → Act → State → Res (List State) :=
  fun n env a s => Tlc.goEnumF (Tlc.run sp n) env a s

-- `tlcEnabledF sp n env a s` (10:296): enabled mode.
def tlcEnabledF (sp : Spec) : Nat → List Value → Act → State → Res Bool :=
  fun n env a s => Tlc.goEnabledF (Tlc.run sp n) env a s

-- `tlcHoldsF sp n env a s t` (10:297): pair mode.
def tlcHoldsF (sp : Spec) : Nat → List Value → Act → State → State → Res Bool :=
  fun n env a s t => Tlc.goHoldsF (Tlc.run sp n) env a s t

-- ---- Evaluate, then force (10:299-302; B1A-14b) ----

-- `Frame.ofState t` (10:300): a whole state as a primed frame, every slot assigned and
-- forced (pair mode, an atom, `Act.denote`).
def Frame.ofState (t : State) : Frame := List.map (fun v => Option.some (XVal.val v)) t

-- `evalE sp n env s t e` (10:301-302): evaluate e with keepLazy off (TLC's `Clear`) at the
-- state s and the successor t, then force the result: what an atom, an ASSUME and
-- `Act.denote` read.
def evalE (sp : Spec) (n : Nat) (env : List Value) (s t : State) (e : Expr) : Res Value :=
  Res.bind (evalX sp n false env s (Frame.ofState t) e) (force sp n s)

end Model
end Trust
