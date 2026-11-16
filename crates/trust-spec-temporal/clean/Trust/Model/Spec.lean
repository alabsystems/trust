-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- Trust.Model.Spec: the executable presentation's specification record and its static
-- checks (Beyond-TLA design 10-executable-semantics.md, "Spec", 10:174-216, and "Actions,
-- derived from next", 10:312-327): FairEntry, ChoiceMode, Spec, Spec.StateWf, Spec.fuel,
-- Spec.wf, Action, Act.split, Spec.actions and Action.toAct. Clean source, served to ty by
-- crates/trust-model-prelude and kernel-checked by crates/trust-spec-temporal. Lane row
-- B1A-13.
--
-- Verbatim: FairEntry (10:180-184), ChoiceMode (10:186-188), Spec (10:190-205, fifteen
-- fields; `tokens` stays `List String`, B1A-D43), Spec.StateWf (10:213-214) and Action
-- (10:318-320) have the design's names and field order; the statement pins of B1A-26a/26b
-- enforce it. `Spec.StateWf` writes the design's `Value.Canon v` (a Bool read as a Prop)
-- as `Value.Canon v = true`, which is what that coercion elaborates to.
--
-- Cost discipline (TASK-STATE 4.8): control is raw recursors with explicit motives, never
-- `match`, `if` or `&&`.

namespace Trust
namespace Model

-- ---- The record (10:180-205), verbatim ----

-- One WF/SF conjunct (10:180-184): `\A p \in D1, ... : WF_sub(act)`. `binders` are the
-- constant-level index domains ([] = one constraint), read outside the binders; `act`
-- is A(p) with the binders as de Bruijn variables (binder k of n is `bvar (n-1-k)`,
-- B1A-D15); `sub` is the subscript, read with no binder in scope (`FairEntry.angle`,
-- 10:357, instantiates `act` only).
structure FairEntry where
  strong  : Bool
  binders : List Expr
  act     : Act
  sub     : Expr

-- PROB's choice discipline (10:186-188).
inductive ChoiceMode where
  | none
  | uniformStates

-- The specification (10:190-205). Not in Spec, so not in SpecDigest: sorts and fuel
-- (computed, `Spec.fuel`).
structure Spec where
  vars              : Nat
  intMode           : IntMode
  tokens            : List String
  pool              : List Expr
  defs              : List (Nat × Expr)
  actDefs           : List (Nat × Act)
  assumes           : List Expr
  init              : Act
  next              : Act
  fairness          : List FairEntry
  invariants        : List Expr
  constraints       : List Expr
  actionConstraints : List Expr
  checkDeadlock     : Bool
  choice            : ChoiceMode

-- `Spec.StateWf sp s` (10:213-214): the carrier of every adequacy and codec statement: one
-- value per slot, every one canonical.
def Spec.StateWf (sp : Spec) (s : State) : Prop :=
  List.length s = sp.vars ∧ ∀ v, Temporal.Member v s → Value.Canon v = true

-- `Spec.stateWfB sp s`: the Bool decider beside `Spec.StateWf` (B1A-D29).
def Spec.stateWfB (sp : Spec) (s : State) : Bool :=
  Bool.and (Nat.beq (List.length s) sp.vars) (Temporal.allB Value.Canon s)

-- ---- Sites: one traversal for every static check (B1A-D17) ----
--
-- `QKind.oneBinder q`: 1 for the forms TLA+ writes with exactly one bound variable (CHOOSE
-- x \in S : P and {x \in S : P}), 0 for the others (\E, \A, {e : x \in S, ...},
-- [x \in S, ... |-> e]).
def QKind.oneBinder (q : QKind) : Nat := @QKind.casesOn (fun _ => Nat) q 0 0 1 1 0 0

-- `PrimOp.arityOk o n` (B1A-15): n operands are the PrimOp's number (ty ops.rs `OPS`
-- operand arity at K2 v2.4 for the K2 rows; the additions as Syntax.lean states them):
-- set.enum and tuple.new take any number, set.product at least two, rec.new and
-- rec.set_of one per field name (at least one), every other its fixed number.
def PrimOp.arityOk (o : PrimOp) (n : Nat) : Bool :=
  @PrimOp.casesOn (fun _ => Bool) o
    (Nat.beq n 2) (Nat.beq n 2) (Nat.beq n 2) (Nat.beq n 2) (Nat.beq n 2) (Nat.beq n 1)
    (Nat.beq n 2) (Nat.beq n 2)
    (fun _ => Nat.beq n 1) (fun _ => Nat.beq n 2)
    (Nat.beq n 2) (Nat.beq n 3) (Nat.beq n 1)
    (Nat.beq n 2) (Nat.beq n 2) (Nat.beq n 2) (Nat.beq n 2) (Nat.beq n 1) (Nat.beq n 2)
    (Nat.beq n 1) (Nat.beq n 2) (Nat.beq n 2) (Nat.beq n 1) (Nat.beq n 1) (Nat.beq n 3)
    (Nat.beq n 2) (Nat.beq n 2)
    true (Nat.beq n 2) (Nat.beq n 2) (Nat.beq n 1) (Nat.beq n 1) (Nat.blt 1 n) (Nat.beq n 1)
    (Nat.beq n 2)
    (fun fs => Bool.and (Nat.blt 0 n) (Nat.beq n (List.length fs)))
    (fun fs => Bool.and (Nat.blt 0 n) (Nat.beq n (List.length fs)))
    true
    (fun _ => Nat.beq n 1)
    (Nat.beq n 2) (Nat.beq n 1) (Nat.beq n 2)
    (Nat.beq n 1)
    (Nat.beq n 2) (Nat.beq n 2) (Nat.beq n 2) (Nat.beq n 1) (Nat.beq n 2) (Nat.beq n 2)

-- `boolNat b`: 1 for true, 0 for false.
def boolNat (b : Bool) : Nat := @Bool.rec (fun _ => Nat) 0 1 b

-- `Expr.foldSites z both site litF e k` folds every node of e that a static check reads,
-- with k binders around e (B1A-D15: `letLazy`/`letA` bind one, a binder list of n binds n
-- in its body and none in its domains). Each such node is one `site tag a b`:
--   tag 0  `cur n`              a = n
--   tag 1  `nxt n`              a = n
--   tag 2  `bvar j`             a = the binders around it (k at the root), b = j
--   tag 3  `pool i`             a = i
--   tag 4  `app i args`         a = i, b = the number of actuals
--   tag 5  `Act.prime n e`      a = n
--   tag 6  `Act.primeIn n e`    a = n
--   tag 7  `Act.call i args`    a = i, b = the number of actuals
--   tag 8  `quant q ds body`    a = 1 when q binds exactly one variable in TLA+ (CHOOSE, a set
--                               filter; `QKind.oneBinder`), else 0; b = the number of domains
--                               (B1A-14b, B1A-D95)
--   tag 9  `op o args`          a = 1 when o takes that number of operands
--                               (`PrimOp.arityOk`), else 0 (B1A-15, B1A-D95 amended)
-- and every literal is one `litF v`; `both` combines the parts in source order, `z` is the
-- empty part. The traversal enters `Expr.enabled`'s action (it adds no site of its own),
-- so `Act.foldSites` is `Expr.foldSites` on `Expr.enabled a`. Structural through the
-- block's recursor, all twelve motives (B1A-D70, B1A-D89).
def Expr.foldSites {α : Type} (z : α) (both : α → α → α) (site : Nat → Nat → Nat → α)
    (litF : Value → α) (e : Expr) : Nat → α :=
  @Expr.rec
    (fun _ => Nat → α) (fun _ => Nat → α) (fun _ => Nat → α) (fun _ => Nat → α)
    (fun _ => Nat → α) (fun _ => Nat → α) (fun _ => Nat → α) (fun _ => Nat → α)
    (fun _ => Nat → α) (fun _ => Nat → α) (fun _ => Nat → α) (fun _ => Nat → α)
    -- Expr
    (fun v _ => litF v)
    (fun n _ => site 0 n 0)
    (fun n _ => site 1 n 0)
    (fun j k => site 2 k j)
    (fun i _ => site 3 i 0)
    (fun o xs rs k => both (site 9 (boolNat (PrimOp.arityOk o (List.length xs))) 0) (rs k))
    (fun _ _ _ rc rt re k => both (rc k) (both (rt k) (re k)))
    (fun _ _ rs rd k => both (rs k) (rd k))
    (fun _ _ re rb k => both (re k) (rb (Nat.succ k)))
    (fun q ds _ rds rb k => both (site 8 (QKind.oneBinder q) (List.length ds))
      (both (rds k) (rb (Nat.add k (List.length ds)))))
    (fun i xs rs k => both (site 4 i (List.length xs)) (rs k))
    (fun _ ra k => ra k)
    -- Act
    (fun _ rs k => rs k)
    (fun _ rs k => rs k)
    (fun _ re k => re k)
    (fun n _ re k => both (site 5 n 0) (re k))
    (fun n _ re k => both (site 6 n 0) (re k))
    (fun _ re k => re k)
    (fun _ re k => re k)
    (fun ds _ rds ra k => both (rds k) (ra (Nat.add k (List.length ds))))
    (fun ds _ rds ra k => both (rds k) (ra (Nat.add k (List.length ds))))
    (fun _ _ _ rc rt re k => both (rc k) (both (rt k) (re k)))
    (fun _ _ rs rd k => both (rs k) (rd k))
    (fun _ _ re ra k => both (re k) (ra (Nat.succ k)))
    (fun i xs rs k => both (site 7 i (List.length xs)) (rs k))
    (fun _ rs k => rs k)
    -- List Expr
    (fun _ => z) (fun _ _ rh rt k => both (rh k) (rt k))
    -- List (Expr × Expr)
    (fun _ => z) (fun _ _ rh rt k => both (rh k) (rt k))
    -- Option Expr
    (fun _ => z) (fun _ rx k => rx k)
    -- List Act
    (fun _ => z) (fun _ _ rh rt k => both (rh k) (rt k))
    -- List (Expr × Act)
    (fun _ => z) (fun _ _ rh rt k => both (rh k) (rt k))
    -- Option Act
    (fun _ => z) (fun _ rx k => rx k)
    -- List (Nat × Act)
    (fun _ => z) (fun _ _ rh rt k => both (rh k) (rt k))
    -- Expr × Expr, Expr × Act, Nat × Act
    (fun _ _ ra rb k => both (ra k) (rb k))
    (fun _ _ ra rb k => both (ra k) (rb k))
    (fun _ _ ra k => ra k)
    e

-- `Act.foldSites`: `Expr.foldSites` on an Act.
def Act.foldSites {α : Type} (z : α) (both : α → α → α) (site : Nat → Nat → Nat → α)
    (litF : Value → α) (a : Act) (k : Nat) : α :=
  Expr.foldSites z both site litF (Expr.enabled a) k

-- `Expr.allSites p e k`: every site of e (at k binders) passes p; literals are not read.
def Expr.allSites (p : Nat → Nat → Nat → Bool) (e : Expr) (k : Nat) : Bool :=
  Expr.foldSites true Bool.and p (fun _ => true) e k

-- `Act.allSites p a k`: `Expr.allSites` on an Act.
def Act.allSites (p : Nat → Nat → Nat → Bool) (a : Act) (k : Nat) : Bool :=
  Act.foldSites true Bool.and p (fun _ => true) a k

-- `tagIn tags tag`: tag is one of tags (a list of eight flags, tag 0 first).
def tagIn (tags : List Bool) (tag : Nat) : Bool := Temporal.nthD tags tag false

-- `noTag tags`: a site predicate refusing exactly the tags flagged in tags.
def noTag (tags : List Bool) (tag _a _b : Nat) : Bool := Bool.not (tagIn tags tag)

-- The site classes the checks below refuse: a read of the current state (`cur`), and any
-- read or assignment of a state slot (`cur`, `nxt`, `prime`, `primeIn`).
def curTags : List Bool := [true, false, false, false, false, false, false, false]
def stateTags : List Bool := [true, true, false, false, false, true, true, false]

-- ---- Spec.wf (10:209-210; B1A-D15, B1A-D17) ----

-- `Value.ints32 v`: every integer inside v is in TLC's range (`inRange32`), recursively.
def Value.ints32 (v : Value) : Bool :=
  @Value.rec (fun _ => Bool) (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
    (fun _ => true) (fun n => inRange32 n) (fun _ => true) (fun _ => true) (fun _ _ => true)
    (fun _ c => c) (fun _ c => c) (fun _ _ c => c)
    true (fun _ _ cx cxs => Bool.and cx cxs)
    true (fun _ _ cp cps => Bool.and cp cps)
    (fun _ _ ca cb => Bool.and ca cb)
    v

-- `litOk m v`: a literal is canonical (`Value.Canon`) and, under `tlc32`, holds no integer
-- outside TLC's range (`model.int-literal-range`, design 10:678, B1A-D08), at any depth.
def litOk (m : IntMode) (v : Value) : Bool :=
  Bool.and (Value.Canon v) (@IntMode.casesOn (fun _ => Bool) m (Value.ints32 v) true)

-- `arityAt ds i`: the arity of the i-th definition of ds (from 0), or none past the end.
def arityAt {β : Type} (ds : List (Prod Nat β)) : Nat → Option Nat :=
  @List.rec (Prod Nat β) (fun _ => Nat → Option Nat)
    (fun _ => Option.none)
    (fun d _ go i =>
      @Nat.rec (fun _ => Option Nat) (Option.some (Prod.fst d)) (fun i' _ => go i') i)
    ds

-- `arityIs ds i n`: ds has an i-th definition and its arity is n.
def arityIs {β : Type} (ds : List (Prod Nat β)) (i n : Nat) : Bool :=
  @Option.casesOn Nat (fun _ => Bool) (arityAt ds i) false (fun m => Nat.beq m n)

-- `Spec.siteOk sp tag a b`: one site is in range: a slot below `vars` (tags 0, 1, 5, 6), a
-- bound variable below the binders around it (tag 2), a pool entry that exists (tag 3), a
-- value or action operator that exists, applied to exactly its arity of actuals (tags 4
-- and 7; a by-name call substitutes one actual per parameter, B1A-D15), a CHOOSE or set
-- filter with exactly one domain, and any quantifier with at least one (tag 8; B1A-D95, its
-- empty case added by B1A-15), a PrimOp with its number of operands (tag 9; B1A-15).
def Spec.siteOk (sp : Spec) (tag a b : Nat) : Bool :=
  Temporal.nthD
    [Nat.blt a sp.vars, Nat.blt a sp.vars, Nat.blt b a, Nat.blt a (List.length sp.pool),
      arityIs sp.defs a b, Nat.blt a sp.vars, Nat.blt a sp.vars, arityIs sp.actDefs a b,
      Bool.and (Nat.blt 0 b) (Bool.or (Nat.beq a 0) (Nat.beq b 1)), Nat.beq a 1]
    tag false

-- `Spec.exprWf sp k e` / `Spec.actWf sp k a`: every site of the term (with k binders
-- around it) in range, every literal `litOk`.
def Spec.exprWf (sp : Spec) (k : Nat) (e : Expr) : Bool :=
  Expr.foldSites true Bool.and (Spec.siteOk sp) (litOk sp.intMode) e k

def Spec.actWf (sp : Spec) (k : Nat) (a : Act) : Bool :=
  Act.foldSites true Bool.and (Spec.siteOk sp) (litOk sp.intMode) a k

-- `FairEntry.wfIn sp f`: the binder domains at no binder (read outside the binders), the
-- action under the binders, the subscript at no binder (10:357 instantiates `act` only).
def FairEntry.wfIn (sp : Spec) (f : FairEntry) : Bool :=
  Bool.and (Temporal.allB (Spec.exprWf sp 0) f.binders)
    (Bool.and (Spec.actWf sp (List.length f.binders) f.act) (Spec.exprWf sp 0 f.sub))

-- `Spec.termsWf sp`: every term of the record in range with its literals `litOk`: pool
-- entries, assumptions, init, next, invariants and constraints at no binder; a
-- definition's body under its arity's parameters.
def Spec.termsWf (sp : Spec) : Bool :=
  Bool.and (Temporal.allB (Spec.exprWf sp 0) sp.pool)
  (Bool.and
    (Temporal.allB (fun (d : Prod Nat Expr) => Spec.exprWf sp (Prod.fst d) (Prod.snd d)) sp.defs)
  (Bool.and
    (Temporal.allB (fun (d : Prod Nat Act) => Spec.actWf sp (Prod.fst d) (Prod.snd d)) sp.actDefs)
  (Bool.and (Temporal.allB (Spec.exprWf sp 0) sp.assumes)
  (Bool.and (Spec.actWf sp 0 sp.init)
  (Bool.and (Spec.actWf sp 0 sp.next)
  (Bool.and (Temporal.allB (FairEntry.wfIn sp) sp.fairness)
  (Bool.and (Temporal.allB (Spec.exprWf sp 0) sp.invariants)
  (Bool.and (Temporal.allB (Spec.exprWf sp 0) sp.constraints)
    (Temporal.allB (Spec.exprWf sp 0) sp.actionConstraints)))))))))

-- ---- The call graph over pool, defs and actDefs together (B1A-D17) ----
--
-- Node ids: pool entry i is i, definition i is P + i, action definition i is P + D + i
-- (P, D, A the three lengths). A node's edges are the in-range `pool`, `app` and `call`
-- sites of its body, in source order (an out-of-range one is `Spec.termsWf`'s refusal and
-- no edge, so it cannot alias another node).

-- `Spec.refSite sp tag a b`: the node a site refers to, as a list of at most one id.
def Spec.refSite (sp : Spec) (tag a _b : Nat) : List Nat :=
  Temporal.nthD
    [[], [], [], @Bool.rec (fun _ => List Nat) [] [a] (Nat.blt a (List.length sp.pool)),
      @Bool.rec (fun _ => List Nat) []
        [Nat.add (List.length sp.pool) a] (Nat.blt a (List.length sp.defs)),
      [], [],
      @Bool.rec (fun _ => List Nat) []
        [Nat.add (Nat.add (List.length sp.pool) (List.length sp.defs)) a]
        (Nat.blt a (List.length sp.actDefs))]
    tag []

def Spec.exprRefs (sp : Spec) (e : Expr) : List Nat :=
  Expr.foldSites [] List.append (Spec.refSite sp) (fun _ => []) e 0

def Spec.actRefs (sp : Spec) (a : Act) : List Nat :=
  Act.foldSites [] List.append (Spec.refSite sp) (fun _ => []) a 0

-- `Spec.nodeCount sp`: P + D + A.
def Spec.nodeCount (sp : Spec) : Nat :=
  Nat.add (Nat.add (List.length sp.pool) (List.length sp.defs)) (List.length sp.actDefs)

-- `Spec.nodeMap sp fe fa`: one entry per node, in id order: fe on each pool entry and each
-- definition's body, fa on each action definition's body.
def Spec.nodeMap {β : Type} (sp : Spec) (fe : Expr → β) (fa : Act → β) : List β :=
  List.append (List.map fe sp.pool)
    (List.append (List.map (fun (d : Prod Nat Expr) => fe (Prod.snd d)) sp.defs)
      (List.map (fun (d : Prod Nat Act) => fa (Prod.snd d)) sp.actDefs))

-- `Spec.adj sp`: every node's edges.
def Spec.adj (sp : Spec) : List (List Nat) := Spec.nodeMap sp (Spec.exprRefs sp) (Spec.actRefs sp)

-- `natMax a b`, `depthIn done n`: the larger of two; the recorded depth of n (0 if none).
def natMax (a b : Nat) : Nat := @Bool.rec (fun _ => Nat) a b (Nat.blt a b)

def depthIn (done : List (Prod Nat Nat)) (n : Nat) : Nat :=
  @Option.casesOn Nat (fun _ => Nat) (Temporal.lookupBy Nat.beq n done) 0 (fun d => d)

-- `dfsChildren go path n cs done`: visit the children cs of n in order with `go` (the DFS
-- at one less fuel, n already on the path), threading the finished list, then record n
-- with its depth: one more than its deepest child's (1 for a node with no child). none
-- as soon as a child's visit is none.
def dfsChildren (go : List Nat → List (Prod Nat Nat) → Nat → Option (List (Prod Nat Nat)))
    (path : List Nat) (n : Nat) (cs : List Nat) (done : List (Prod Nat Nat)) :
    Option (List (Prod Nat Nat)) :=
  @List.rec Nat (fun _ => List (Prod Nat Nat) → Nat → Option (List (Prod Nat Nat)))
    (fun done d => Option.some (List.cons (Prod.mk n (Nat.succ d)) done))
    (fun c _ rest done d =>
      @Option.casesOn (List (Prod Nat Nat)) (fun _ => Option (List (Prod Nat Nat)))
        (go path done c)
        Option.none
        (fun done' => rest done' (natMax d (depthIn done' c))))
    cs done 0

-- `dfsF adj fuel path done n` (B1A-D17): the depth-first search from node n over the edges
-- adj, with `path` the nodes on the way to n and `done` the finished nodes with their
-- depths (each visited once). none when n is on the path (a cycle) or the fuel runs out;
-- otherwise `done` extended by every node reachable from n, in post-order. Fuel one more
-- than the number of nodes never runs out on an acyclic graph (a path holds each node at
-- most once).
def dfsF (adj : List (List Nat)) (fuel : Nat) :
    List Nat → List (Prod Nat Nat) → Nat → Option (List (Prod Nat Nat)) :=
  @Nat.rec (fun _ => List Nat → List (Prod Nat Nat) → Nat → Option (List (Prod Nat Nat)))
    (fun _ _ _ => Option.none)
    (fun _ go path done n =>
      @Option.casesOn Nat (fun _ => Option (List (Prod Nat Nat)))
        (Temporal.lookupBy Nat.beq n done)
        (@Bool.rec (fun _ => Option (List (Prod Nat Nat)))
          (dfsChildren go (List.cons n path) n (Temporal.nthD adj n []) done)
          Option.none
          (Temporal.memBy Nat.beq n path))
        (fun _ => Option.some done))
    fuel

-- `dfsFrom adj fuel roots done`: `dfsF` from each root in order, threading `done`.
def dfsFrom (adj : List (List Nat)) (fuel : Nat) (roots : List Nat)
    (done : List (Prod Nat Nat)) : Option (List (Prod Nat Nat)) :=
  @List.rec Nat (fun _ => List (Prod Nat Nat) → Option (List (Prod Nat Nat)))
    (fun done => Option.some done)
    (fun r _ rest done =>
      @Option.casesOn (List (Prod Nat Nat)) (fun _ => Option (List (Prod Nat Nat)))
        (dfsF adj fuel [] done r) Option.none (fun done' => rest done'))
    roots done

-- `natRange n`: [0, 1, ..., n-1].
def natRange (n : Nat) : List Nat :=
  @Nat.rec (fun _ => List Nat) [] (fun k acc => List.append acc [k]) n

-- `Spec.dfs sp roots`: the search from roots over the whole graph, fuel nodeCount + 1.
def Spec.dfs (sp : Spec) (roots : List Nat) : Option (List (Prod Nat Nat)) :=
  dfsFrom (Spec.adj sp) (Nat.succ (Spec.nodeCount sp)) roots []

-- `Spec.acyclic sp`: the search from every node finds no cycle.
def Spec.acyclic (sp : Spec) : Bool :=
  @Option.casesOn (List (Prod Nat Nat)) (fun _ => Bool)
    (Spec.dfs sp (natRange (Spec.nodeCount sp))) false (fun _ => true)

-- `Spec.callDepth sp` (B1A-D16): the number of nodes on the longest call chain (0 with no
-- definition), so `callDepth + 1` counts the bodies on the longest evaluation nesting,
-- the top-level term included. 0 on a cyclic graph (`Spec.wf` refuses it).
def Spec.callDepth (sp : Spec) : Nat :=
  @Option.casesOn (List (Prod Nat Nat)) (fun _ => Nat)
    (Spec.dfs sp (natRange (Spec.nodeCount sp))) 0
    (fun done =>
      @List.rec (Prod Nat Nat) (fun _ => Nat) 0 (fun p _ m => natMax (Prod.snd p) m) done)

-- `allFlagged flags found`: found is some list of nodes, each flagged in flags (by id).
def allFlagged (flags : List Bool) (found : Option (List (Prod Nat Nat))) : Bool :=
  @Option.casesOn (List (Prod Nat Nat)) (fun _ => Bool) found false
    (fun done =>
      Temporal.allB (fun (p : Prod Nat Nat) => Temporal.nthD flags (Prod.fst p) false) done)

-- `Spec.reachFree sp roots tags`: every node reachable from roots (roots included) has no
-- site whose tag is flagged in tags; false on a cycle.
def Spec.reachFree (sp : Spec) (roots : List Nat) (tags : List Bool) : Bool :=
  allFlagged
    (Spec.nodeMap sp (fun e => Expr.allSites (noTag tags) e 0)
      (fun a => Act.allSites (noTag tags) a 0))
    (Spec.dfs sp roots)

-- `Spec.initPrimed sp` (B1A-D15: Init is in primed form, `tlcInit` runs it on the empty
-- state): no `cur` in init, nor in any node init reaches.
def Spec.initPrimed (sp : Spec) : Bool :=
  Bool.and (Act.allSites (noTag curTags) sp.init 0)
    (Spec.reachFree sp (Spec.actRefs sp sp.init) curTags)

-- `Spec.poolConstant sp`: the pool is constant-level (10:194): no pool entry, nor any node
-- one reaches, reads or assigns a state slot.
def Spec.poolConstant (sp : Spec) : Bool :=
  Spec.reachFree sp (natRange (List.length sp.pool)) stateTags

-- `strBeq a b`: String equality (the kernel's `String.decEq`).
def strBeq (a b : String) : Bool := decide (a = b)

-- `distinctBy eq xs`: no element of xs occurs again after itself.
def distinctBy {α : Type} (eq : α → α → Bool) (xs : List α) : Bool :=
  @List.rec α (fun _ => Bool) true
    (fun x rest ih => Bool.and (Bool.not (Temporal.memBy eq x rest)) ih)
    xs

-- `Spec.wf sp` (10:209-210, kernel-checked): canonical literals, and under `tlc32` integer
-- literals in TLC's range; slot, bound-variable, pool and definition indices in range,
-- each call with its definition's arity, each CHOOSE and set filter with one binder
-- (B1A-D95); the call graph over pool, defs and actDefs acyclic (B1A-D17); no `cur` in init
-- (B1A-D15); a constant-level pool; distinct tokens.
def Spec.wf (sp : Spec) : Bool :=
  Bool.and (Spec.termsWf sp)
    (Bool.and (Spec.acyclic sp)
      (Bool.and (Spec.initPrimed sp)
        (Bool.and (Spec.poolConstant sp) (distinctBy strBeq sp.tokens))))

-- ---- Spec.fuel (B1A-D16) ----

-- `sumNat xs`: the sum of xs.
def sumNat (xs : List Nat) : Nat :=
  @List.rec Nat (fun _ => Nat) 0 (fun n _ s => Nat.add n s) xs

-- `Spec.size sp`: the total term size of the record (`Expr.size`, `Act.size`): every pool
-- entry, definition body, assumption, init, next, every fairness entry's binder domains,
-- action and subscript, every invariant and constraint.
def Spec.size (sp : Spec) : Nat :=
  sumNat
    (List.append (Spec.nodeMap sp Expr.size Act.size)
      (List.append (List.map Expr.size sp.assumes)
        (List.append [Act.size sp.init, Act.size sp.next]
          (List.append
            (List.map
              (fun (f : FairEntry) => Nat.add (sumNat (List.map Expr.size f.binders))
                (Nat.add (Act.size f.act) (Expr.size f.sub)))
              sp.fairness)
            (List.map Expr.size
              (List.append sp.invariants (List.append sp.constraints sp.actionConstraints)))))))

-- `Spec.fuel sp` (10:208, B1A-D16): 1 + (call-graph depth + 1) * (total term size + vars +
-- 1). `Fail.fuel` is a resource result: a probe that runs out is fixed here, never in its
-- expectation.
def Spec.fuel (sp : Spec) : Nat :=
  Nat.succ (Nat.mul (Nat.succ (Spec.callDepth sp)) (Nat.succ (Nat.add (Spec.size sp) sp.vars)))

-- ---- Actions, derived from next (10:312-325) ----

structure Action where
  binders : List Expr
  body    : Act

-- `Action.toAct a` (10:324).
def Action.toAct (a : Action) : Act := Act.ex a.binders a.body

-- `Action.flat a`: the action as a conjunct: its body when it has no binder, else
-- `Action.toAct a`.
def Action.flat (a : Action) : Act :=
  @List.casesOn Expr (fun _ => Act) a.binders a.body (fun _ _ => Action.toAct a)

-- `Expr.primeFree e`: e is a guard Act.split may copy into every action (B1A-D18): it
-- reads no primed slot, calls no value operator (an `app` body is not looked into) and
-- holds no action site (an `Expr.enabled` whose action assigns or calls). A pool entry is
-- constant-level (`Spec.poolConstant`).
def Expr.primeFree (e : Expr) : Bool :=
  Expr.allSites (noTag [false, true, false, false, true, true, true, true]) e 0

-- `Act.isGuard a`: a is `pred e` with e prime-free.
def Act.isGuard (a : Act) : Bool :=
  @Act.casesOn
    (fun _ => Nat) (fun _ => Bool) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    a
    -- Expr: unused
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
    (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0)
    (fun _ => 0)
    -- Act
    (fun _ => false) (fun _ => false) (fun e => Expr.primeFree e) (fun _ _ => false)
    (fun _ _ => false) (fun _ => false) (fun _ => false) (fun _ _ => false)
    (fun _ _ => false) (fun _ _ _ => false) (fun _ _ => false) (fun _ _ => false)
    (fun _ _ => false) (fun _ => false)
    -- the other ten types' minors: unused
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ => 0)
    0 (fun _ _ => 0)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)

-- `nonGuardSplits ps`: the splits of the conjuncts that are not guards, in order.
def nonGuardSplits (ps : List (Prod Act (List Action))) : List (List Action) :=
  @List.rec (Prod Act (List Action)) (fun _ => List (List Action)) []
    (fun p _ rest =>
      @Bool.rec (fun _ => List (List Action)) (List.cons (Prod.snd p) rest) rest
        (Act.isGuard (Prod.fst p)))
    ps

-- `conjWith ps b`: the conjunction with its one non-guard conjunct replaced by `b.flat`.
def conjWith (ps : List (Prod Act (List Action))) (b : Action) : Action :=
  Action.mk []
    (Act.conj
      (List.map
        (fun (p : Prod Act (List Action)) =>
          @Bool.rec (fun _ => Act) (Action.flat b) (Prod.fst p) (Act.isGuard (Prod.fst p)))
        ps))

-- `splitConj ps`: `Act.conj cs` (ps = each conjunct with its split). When exactly one
-- conjunct is not a guard and it splits into at least one action, one action per action of
-- that conjunct, the guards copied in place (TLC evaluates the guards in each branch, in
-- the same order, with the same first error); otherwise the conjunction is one action.
def splitConj (ps : List (Prod Act (List Action))) : List Action :=
  @List.casesOn (List Action) (fun _ => List Action) (nonGuardSplits ps)
    [Action.mk [] (Act.conj (List.map (@Prod.fst Act (List Action)) ps))]
    (fun bs more =>
      @List.casesOn (List Action) (fun _ => List Action) more
        (@List.casesOn Action (fun _ => List Action) bs
          [Action.mk [] (Act.conj (List.map (@Prod.fst Act (List Action)) ps))]
          (fun _ _ => List.map (conjWith ps) bs))
        (fun _ _ => [Action.mk [] (Act.conj (List.map (@Prod.fst Act (List Action)) ps))]))

-- `splitLet e a bs`: `Act.letA e a` (bs = a's split). LET is substitution (10:168), so it
-- distributes over the actions of a; split only when e is a prime-free guard and a splits
-- into at least one action.
def splitLet (e : Expr) (a : Act) (bs : List Action) : List Action :=
  @Bool.rec (fun _ => List Action)
    [Action.mk [] (Act.letA e a)]
    (@List.casesOn Action (fun _ => List Action) bs
      [Action.mk [] (Act.letA e a)]
      (fun _ _ => List.map (fun b => Action.mk [] (Act.letA e (Action.flat b))) bs))
    (Expr.primeFree e)

-- `Act.split a` (10:321-322, B1A-D18): the actions of a, in source order. It descends
-- through `disj` (each disjunct's actions, concatenated), through `conj` whose other
-- conjuncts are prime-free guards, and through `letA` with a prime-free definition; a
-- leading `ex` is one action with its binders exposed (`\E x : (A \/ B)` stays ONE
-- action); `call` (an action operator) and a conjunct holding `app` are never descended
-- into; every other form is one action. So `Res.concat` of the actions' generation is the
-- generation of a (TH-tlcEnum_split), and a net's `disj` of transitions splits into one
-- action per transition, in transition order (DR-13).
def Act.split (a : Act) : List Action :=
  @Act.rec
    (fun _ => Nat) (fun _ => List Action) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => List (Prod Act (List Action))) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    -- Expr: unused
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ _ => 0)
    (fun _ _ _ _ _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ _ _ _ => 0)
    (fun _ _ _ => 0) (fun _ _ => 0)
    -- Act
    (fun _ ps => splitConj ps)
    (fun _ ps =>
      @List.rec (Prod Act (List Action)) (fun _ => List Action) []
        (fun p _ rest => List.append (Prod.snd p) rest) ps)
    (fun e _ => [Action.mk [] (Act.pred e)])
    (fun n e _ => [Action.mk [] (Act.prime n e)])
    (fun n e _ => [Action.mk [] (Act.primeIn n e)])
    (fun e _ => [Action.mk [] (Act.unchanged e)])
    (fun e _ => [Action.mk [] (Act.changed e)])
    (fun ds b _ _ => [Action.mk ds b])
    (fun ds b _ _ => [Action.mk [] (Act.fa ds b)])
    (fun c t f _ _ _ => [Action.mk [] (Act.ite c t f)])
    (fun arms d _ _ => [Action.mk [] (Act.caseOf arms d)])
    (fun e b _ bs => splitLet e b bs)
    (fun i args _ => [Action.mk [] (Act.call i args)])
    (fun arms _ => [Action.mk [] (Act.pchoice arms)])
    -- List Expr, List (Expr × Expr), Option Expr: unused
    0 (fun _ _ _ _ => 0)
    0 (fun _ _ _ _ => 0)
    0 (fun _ _ => 0)
    -- List Act: each conjunct or disjunct with its split
    [] (fun h _ bh rest => List.cons (Prod.mk h bh) rest)
    -- List (Expr × Act), Option Act, List (Nat × Act), Expr × Expr, Expr × Act, Nat × Act:
    -- unused
    0 (fun _ _ _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ _ _ => 0)
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ _ => 0)
    a

-- `Spec.actions sp` (10:323): the actions of `next`, derived, never stored.
def Spec.actions (sp : Spec) : List Action := Act.split sp.next

end Model
end Trust
