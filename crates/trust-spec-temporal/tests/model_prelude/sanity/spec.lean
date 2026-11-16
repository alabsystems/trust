-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-13 sanity facts for Trust.Model.Spec (model_prelude_kernel.rs, sanity_files):
-- Act.split (B1A-D18; design 10:321-322) including the Petri image of ty DR-13 (one action
-- per transition, in transition order), Spec.wf (10:209-210; B1A-D15, B1A-D17) on
-- well-formed controls and on a cyclic call graph, an out-of-range literal, a `cur` in
-- init and the index checks, Spec.fuel (B1A-D16), and Spec.stateWfB. Elaborated after the
-- whole model prelude; every theorem is accepted by check_model_theorem (kernel re-check,
-- constructive, axiom-free, audited) and is a Bool door closed by rfl (B1A-D54); the
-- mutated-literal doors of SANITY_MUTANTS must each be refuted (class Definite).
--
-- The expectations are the design's rules, applied by hand: which forms split
-- (10:321-322, D18), what wf refuses (10:209-210, D15, D17), and the fuel formula
-- 1 + (call-graph depth + 1) * (total term size + vars + 1) (D16) with the sizes counted
-- by Expr.size's rule (one per constructor). Actions are compared through `actionV`, an
-- injective encoding as a `Value` tree (B1A-12's `exprV`), with the structural
-- `Value.beq`.

namespace Trust
namespace Model
namespace Sanity

def int (n : Int) : Value := Value.int n

-- ---- Comparing terms and actions ----

-- `opCode o`: the constructor's position in PrimOp (from 0), with its attribute.
def opCode (o : PrimOp) : Value :=
  @PrimOp.casesOn (fun _ => Value) o
    (int 0) (int 1) (int 2) (int 3) (int 4) (int 5) (int 6) (int 7)
    (fun f => Value.set [int 8, int f])
    (fun f => Value.set [int 9, int f])
    (int 10) (int 11) (int 12)
    (int 13) (int 14) (int 15) (int 16) (int 17) (int 18)
    (int 19) (int 20) (int 21) (int 22) (int 23) (int 24)
    (int 25) (int 26)
    (int 27) (int 28) (int 29) (int 30) (int 31) (int 32) (int 33)
    (int 34)
    (fun fs => Value.set [int 35, Value.set (List.map (fun f => Value.int (Int.ofNat f)) fs)])
    (fun fs => Value.set [int 36, Value.set (List.map (fun f => Value.int (Int.ofNat f)) fs)])
    (int 37)
    (fun i => Value.set [int 38, int i])
    (int 39) (int 40) (int 41)
    (int 42)
    (int 43) (int 44) (int 45) (int 46) (int 47) (int 48)

def qkCode (q : QKind) : Value :=
  @QKind.casesOn (fun _ => Value) q (int 0) (int 1) (int 2) (int 3) (int 4) (int 5)

-- `exprV e`: e as a Value tree (B1A-12's encoding).
def exprV (e : Expr) : Value :=
  @Expr.rec
    (fun _ => Value) (fun _ => Value) (fun _ => List Value) (fun _ => List Value)
    (fun _ => List Value) (fun _ => List Value) (fun _ => List Value) (fun _ => List Value)
    (fun _ => List Value) (fun _ => Value) (fun _ => Value) (fun _ => Value)
    -- Expr
    (fun v => Value.set [int 0, v])
    (fun n => Value.set [int 1, int n])
    (fun n => Value.set [int 2, int n])
    (fun n => Value.set [int 3, int n])
    (fun n => Value.set [int 4, int n])
    (fun o _ vs => Value.set [int 5, opCode o, Value.set vs])
    (fun _ _ _ c t f => Value.set [int 6, c, t, f])
    (fun _ _ arms d => Value.set [int 7, Value.set arms, Value.set d])
    (fun _ _ x b => Value.set [int 8, x, b])
    (fun q _ _ ds b => Value.set [int 9, qkCode q, Value.set ds, b])
    (fun i _ vs => Value.set [int 10, int i, Value.set vs])
    (fun _ a => Value.set [int 11, a])
    -- Act
    (fun _ vs => Value.set [int 20, Value.set vs])
    (fun _ vs => Value.set [int 21, Value.set vs])
    (fun _ x => Value.set [int 22, x])
    (fun n _ x => Value.set [int 23, int n, x])
    (fun n _ x => Value.set [int 24, int n, x])
    (fun _ x => Value.set [int 25, x])
    (fun _ x => Value.set [int 26, x])
    (fun _ _ ds a => Value.set [int 27, Value.set ds, a])
    (fun _ _ ds a => Value.set [int 28, Value.set ds, a])
    (fun _ _ _ c t f => Value.set [int 29, c, t, f])
    (fun _ _ arms d => Value.set [int 30, Value.set arms, Value.set d])
    (fun _ _ x a => Value.set [int 31, x, a])
    (fun i _ vs => Value.set [int 32, int i, Value.set vs])
    (fun _ arms => Value.set [int 33, Value.set arms])
    -- List Expr, List (Expr × Expr), Option Expr, List Act, List (Expr × Act), Option Act,
    -- List (Nat × Act)
    [] (fun _ _ h t => List.cons h t)
    [] (fun _ _ h t => List.cons h t)
    [] (fun _ x => [x])
    [] (fun _ _ h t => List.cons h t)
    [] (fun _ _ h t => List.cons h t)
    [] (fun _ x => [x])
    [] (fun _ _ h t => List.cons h t)
    -- Expr × Expr, Expr × Act, Nat × Act
    (fun _ _ a b => Value.set [a, b])
    (fun _ _ a b => Value.set [a, b])
    (fun n _ a => Value.set [int n, a])
    e

def actV (a : Act) : Value := exprV (Expr.enabled a)
def actEq (a b : Act) : Bool := Value.beq (actV a) (actV b)

-- `actionV a`: an action as its binders' terms and its body's.
def actionV (a : Action) : Value :=
  Value.set [Value.set (List.map exprV a.binders), actV a.body]

-- `actionsEq xs ys`: the same actions, in the same order.
def actionsEq (xs ys : List Action) : Bool :=
  Value.beq (Value.set (List.map actionV xs)) (Value.set (List.map actionV ys))

def one (a : Act) : Action := Action.mk [] a

-- ---- Terms ----

def lit (n : Int) : Expr := Expr.lit (int n)
def le (a b : Expr) : Expr := Expr.op PrimOp.intLe [a, b]
def add (a b : Expr) : Expr := Expr.op PrimOp.intAdd [a, b]
def sub (a b : Expr) : Expr := Expr.op PrimOp.intSub [a, b]
def eq (a b : Expr) : Expr := Expr.op PrimOp.valueEq [a, b]

-- A Petri net over two places (slots 0 and 1), in the image of ty DR-13: one transition per
-- disjunct, each `pre <= m` as a guard, then the firing `m - pre + post`.
def t0 : Act :=
  Act.conj [Act.pred (le (lit 1) (Expr.cur 0)), Act.prime 0 (sub (Expr.cur 0) (lit 1)),
    Act.prime 1 (add (Expr.cur 1) (lit 1))]
def t1 : Act :=
  Act.conj [Act.pred (le (lit 1) (Expr.cur 1)), Act.prime 1 (sub (Expr.cur 1) (lit 1)),
    Act.prime 0 (add (Expr.cur 0) (lit 1))]

-- `spec vars m tokens pool defs actDefs init next invs`: a Spec with no assumption, no
-- fairness, no constraint, deadlock checked, no PROB choice.
def spec (vars : Nat) (m : IntMode) (tokens : List String) (pool : List Expr)
    (defs : List (Prod Nat Expr)) (actDefs : List (Prod Nat Act)) (init next : Act)
    (invs : List Expr) : Spec :=
  Spec.mk vars m tokens pool defs actDefs [] init next [] invs [] [] true ChoiceMode.none

def petriInit : Act := Act.conj [Act.prime 0 (lit 1), Act.prime 1 (lit 0)]
def petri : Spec :=
  spec 2 IntMode.tlc32 [] [] [] [] petriInit (Act.disj [t0, t1]) [le (lit 0) (Expr.cur 0)]

-- ---- Act.split (B1A-D18) ----

-- The net's `disj` of two transitions splits into two actions, in transition order (DR-13).
theorem petri_two_actions_in_order :
    actionsEq (Spec.actions petri) [one t0, one t1] = true := rfl
theorem petri_toAct :
    Bool.and (actEq (Action.toAct (one t0)) (Act.ex [] t0))
      (actEq (Action.toAct (Action.mk [Expr.lit (Value.set [int 1])] t1))
        (Act.ex [Expr.lit (Value.set [int 1])] t1)) = true := rfl

def dom : Expr := Expr.lit (Value.set [int 1, int 2])
def aA : Act := Act.prime 0 (Expr.bvar 0)
def aB : Act := Act.prime 1 (lit 7)

-- `\E x \in S : (A \/ B)` stays ONE action, its binder exposed (10:321-322).
theorem ex_over_disj_one_action :
    actionsEq (Act.split (Act.ex [dom] (Act.disj [aA, aB]))) [Action.mk [dom] (Act.disj [aA, aB])]
      = true := rfl
-- A leading \E inside a disjunct keeps its binders; nested disjunctions are flattened in
-- order; an empty disjunction has no action.
theorem disj_flattens_in_order :
    Bool.and
      (actionsEq (Act.split (Act.disj [Act.ex [dom] aA, Act.disj [aB, t0], t1]))
        [Action.mk [dom] aA, one aB, one t0, one t1])
      (actionsEq (Act.split (Act.disj [])) []) = true := rfl
-- A conjunction whose other conjuncts are prime-free guards is descended, before or after
-- the split conjunct, the guards copied in place.
theorem conj_guard_descends :
    Bool.and
      (actionsEq (Act.split (Act.conj [Act.pred (le (lit 1) (Expr.cur 0)), Act.disj [aB, t1]]))
        [one (Act.conj [Act.pred (le (lit 1) (Expr.cur 0)), aB]),
          one (Act.conj [Act.pred (le (lit 1) (Expr.cur 0)), t1])])
      (actionsEq (Act.split (Act.conj [Act.disj [aB, t1], Act.pred (Expr.pool 0)]))
        [one (Act.conj [aB, Act.pred (Expr.pool 0)]), one (Act.conj [t1, Act.pred (Expr.pool 0)])])
      = true := rfl
-- A split conjunct that is a leading \E stays under the conjunction (its binders are not
-- hoisted over the guard, which TLC evaluates first).
theorem conj_keeps_inner_ex :
    actionsEq (Act.split (Act.conj [Act.pred (le (lit 1) (Expr.cur 0)),
        Act.disj [Act.ex [dom] aA, aB]]))
      [one (Act.conj [Act.pred (le (lit 1) (Expr.cur 0)), Act.ex [dom] aA]),
        one (Act.conj [Act.pred (le (lit 1) (Expr.cur 0)), aB])] = true := rfl
-- D18: a conjunct holding a value-operator call (`app`) or an action-operator call (`call`)
-- is never descended through, and `call` is never unfolded.
def appGuarded : Act := Act.conj [Act.pred (Expr.app 0 []), Act.disj [aA, aB]]
theorem no_descent_through_app_or_call :
    Bool.and (actionsEq (Act.split appGuarded) [one appGuarded])
      (Bool.and
        (actionsEq (Act.split (Act.disj [Act.call 0 [], aB])) [one (Act.call 0 []), one aB])
        (actionsEq (Act.split (Act.conj [Act.call 0 [], Act.disj [aA, aB]]))
          [one (Act.conj [Act.call 0 [], Act.disj [aA, aB]])])) = true := rfl
-- A guard that reads a primed slot is not prime-free, and two split conjuncts are not
-- descended: each conjunction stays one action.
theorem conj_no_descent :
    Bool.and
      (actionsEq (Act.split (Act.conj [Act.pred (eq (Expr.nxt 0) (lit 1)), Act.disj [aA, aB]]))
        [one (Act.conj [Act.pred (eq (Expr.nxt 0) (lit 1)), Act.disj [aA, aB]])])
      (actionsEq (Act.split (Act.conj [Act.disj [aA, aB], Act.disj [t0, t1]]))
        [one (Act.conj [Act.disj [aA, aB], Act.disj [t0, t1]])]) = true := rfl
-- A guard with no action to split into: the conjunction stays (its guard may raise).
theorem conj_empty_disj_stays :
    actionsEq (Act.split (Act.conj [Act.pred (le (lit 1) (Expr.cur 0)), Act.disj []]))
      [one (Act.conj [Act.pred (le (lit 1) (Expr.cur 0)), Act.disj []])] = true := rfl
-- LET distributes (substitution, 10:168).
theorem letA_descends :
    actionsEq (Act.split (Act.letA (lit 3) (Act.disj [aA, aB])))
      [one (Act.letA (lit 3) aA), one (Act.letA (lit 3) aB)] = true := rfl
-- Every other form is one action.
theorem other_forms_one_action :
    Bool.and (actionsEq (Act.split (Act.fa [dom] (Act.disj [aA, aB])))
        [one (Act.fa [dom] (Act.disj [aA, aB]))])
      (Bool.and (actionsEq (Act.split (Act.ite (Expr.cur 0) (Act.disj [aA, aB]) aB))
          [one (Act.ite (Expr.cur 0) (Act.disj [aA, aB]) aB)])
        (actionsEq (Act.split (Act.pchoice [(1, aA), (2, aB)]))
          [one (Act.pchoice [(1, aA), (2, aB)])]))
      = true := rfl

-- ---- Spec.wf (B1A-D15, B1A-D17) ----

-- `rejects sp`: Spec.wf refuses sp. `allT bs`: every one of bs is true.
def rejects (sp : Spec) : Bool := Bool.not (Spec.wf sp)
def allT (bs : List Bool) : Bool := Temporal.allB (fun (b : Bool) => b) bs

-- Well-formed controls: the net, and a spec with a constant pool entry calling a
-- constant-level definition, a parametrised definition, an action definition with a
-- parameter, a fairness entry over one binder and distinct tokens.
def rich : Spec :=
  Spec.mk 2 IntMode.tlc32 ["a", "b"]
    [Expr.app 1 [lit 4]]
    [(0, eq (Expr.cur 0) (Expr.pool 0)), (1, add (Expr.bvar 0) (lit 1))]
    [(1, Act.prime 0 (Expr.bvar 0))]
    [le (lit 0) (Expr.pool 0)]
    (Act.conj [Act.prime 0 (lit 0), Act.prime 1 (Expr.nxt 0)])
    (Act.ex [Expr.lit (Value.set [int 1, int 2])]
      (Act.conj [Act.pred (Expr.app 0 []), Act.call 0 [Expr.bvar 0], Act.unchanged (Expr.cur 1)]))
    [FairEntry.mk false [dom] (Act.call 0 [Expr.bvar 0]) (Expr.cur 0)]
    [le (lit (-2147483648)) (Expr.cur 0)] [] [] true ChoiceMode.none
theorem wf_controls : Bool.and (Spec.wf petri) (Spec.wf rich) = true := rfl

-- A cyclic call graph, over defs, over pool and defs together, over actDefs, or a
-- self-loop, is refused, reached or not; the acyclic chain is accepted.
def withDefs (defs : List (Prod Nat Expr)) : Spec :=
  spec 1 IntMode.tlc32 [] [] defs [] (Act.prime 0 (lit 0)) (Act.prime 0 (lit 1)) []
theorem wf_rejects_cyclic_defs :
    allT [rejects (withDefs [(0, Expr.app 1 []), (0, Expr.app 0 [])]),
      rejects (withDefs [(0, Expr.app 0 [])]),
      Spec.wf (withDefs [(0, Expr.app 1 []), (0, lit 1)])] = true := rfl
theorem wf_rejects_cycles_across_kinds :
    allT [rejects (spec 1 IntMode.tlc32 [] [Expr.app 0 []] [(0, Expr.pool 0)] []
        (Act.prime 0 (lit 0)) (Act.prime 0 (lit 1)) []),
      rejects (spec 1 IntMode.tlc32 [] [] [] [(0, Act.call 0 [])]
        (Act.prime 0 (lit 0)) (Act.prime 0 (lit 1)) [])] = true := rfl

-- An integer literal outside TLC's range is refused under tlc32 (model.int-literal-range,
-- 10:678), at any depth of the literal; accepted unbounded; -2^31 is in range. A
-- non-canonical literal is refused.
def withNext (m : IntMode) (e : Expr) : Spec :=
  spec 1 m [] [] [] [] (Act.prime 0 (lit 0)) (Act.prime 0 e) []
theorem wf_rejects_out_of_range_literal :
    allT [rejects (withNext IntMode.tlc32 (lit 2147483648)),
      rejects (withNext IntMode.tlc32 (Expr.lit (Value.set [int 1, int 2147483648]))),
      Spec.wf (withNext IntMode.unbounded (lit 2147483648)),
      Spec.wf (withNext IntMode.tlc32 (lit (-2147483648))),
      rejects (withNext IntMode.tlc32 (lit (-2147483649)))] = true := rfl
theorem wf_rejects_noncanonical_literal :
    rejects (withNext IntMode.tlc32 (Expr.lit (Value.set [int 2, int 1]))) = true := rfl

-- Init is in primed form (B1A-D15): a `cur` in init, or in a definition init reaches, is
-- refused; the same definition reached only from next is accepted; a primed read in init
-- is accepted.
def curDef : List (Prod Nat Expr) := [(0, eq (Expr.cur 0) (lit 0))]
theorem wf_rejects_cur_in_init :
    allT [rejects (spec 1 IntMode.tlc32 [] [] [] []
        (Act.conj [Act.prime 0 (lit 0), Act.pred (eq (Expr.cur 0) (lit 0))])
        (Act.prime 0 (lit 1)) []),
      rejects (spec 1 IntMode.tlc32 [] [] curDef []
        (Act.conj [Act.prime 0 (lit 0), Act.pred (Expr.app 0 [])]) (Act.prime 0 (lit 1)) []),
      Spec.wf (spec 1 IntMode.tlc32 [] [] curDef [] (Act.prime 0 (lit 0))
        (Act.conj [Act.pred (Expr.app 0 []), Act.prime 0 (lit 1)]) []),
      Spec.wf (spec 1 IntMode.tlc32 [] [] [] []
        (Act.conj [Act.prime 0 (lit 0), Act.pred (eq (Expr.nxt 0) (lit 0))])
        (Act.prime 0 (lit 1)) [])] = true := rfl

-- Indices: a slot at or past `vars`, a free bound variable, a definition's body beyond its
-- parameters, a call with the wrong number of actuals, a pool entry or definition that does
-- not exist, are refused; a bound variable under its binder is accepted.
theorem wf_rejects_bad_indices :
    allT [rejects (withNext IntMode.tlc32 (Expr.cur 1)),
      rejects (withNext IntMode.tlc32 (Expr.bvar 0)),
      rejects (withNext IntMode.tlc32 (Expr.pool 0)),
      rejects (withNext IntMode.tlc32 (Expr.app 0 [])),
      rejects (spec 1 IntMode.tlc32 [] [] [(0, Expr.bvar 0)] []
        (Act.prime 0 (lit 0)) (Act.prime 0 (Expr.app 0 [])) []),
      rejects (spec 1 IntMode.tlc32 [] [] [(1, Expr.bvar 0)] []
        (Act.prime 0 (lit 0)) (Act.prime 0 (Expr.app 0 [])) []),
      Spec.wf (spec 1 IntMode.tlc32 [] [] [(1, Expr.bvar 0)] []
        (Act.prime 0 (lit 0)) (Act.prime 0 (Expr.app 0 [lit 1])) []),
      rejects (spec 1 IntMode.tlc32 [] [] [] [] (Act.prime 0 (lit 0)) (Act.prime 1 (lit 1)) []),
      rejects (spec 1 IntMode.tlc32 [] [] [] [] (Act.prime 0 (lit 0)) (Act.call 0 []) []),
      Spec.wf (spec 1 IntMode.tlc32 [] [] [] [] (Act.prime 0 (lit 0))
        (Act.ex [dom] (Act.prime 0 (Expr.bvar 0))) [])] = true := rfl

-- The pool is constant-level: an entry reading a state slot, directly or through a
-- definition, is refused.
theorem wf_rejects_state_in_pool :
    allT [rejects (spec 1 IntMode.tlc32 [] [Expr.cur 0] [] [] (Act.prime 0 (lit 0))
        (Act.prime 0 (lit 1)) []),
      rejects (spec 1 IntMode.tlc32 [] [Expr.app 0 []] curDef [] (Act.prime 0 (lit 0))
        (Act.prime 0 (lit 1)) [])] = true := rfl

-- Fairness: the action is read under the entry's binders, the subscript under none.
def fairSpec (f : FairEntry) : Spec :=
  Spec.mk 1 IntMode.tlc32 [] [] [] [] [] (Act.prime 0 (lit 0)) (Act.prime 0 (lit 1)) [f] [] []
    [] true ChoiceMode.none
theorem wf_fairness_scopes :
    allT [Spec.wf (fairSpec (FairEntry.mk true [dom] (Act.prime 0 (Expr.bvar 0)) (Expr.cur 0))),
      rejects (fairSpec (FairEntry.mk true [dom] (Act.prime 0 (Expr.bvar 0)) (Expr.bvar 0)))]
      = true := rfl

-- Tokens are distinct.
theorem wf_rejects_duplicate_tokens :
    allT [Spec.wf (spec 1 IntMode.tlc32 ["a", "b", "c"] [] [] [] (Act.prime 0 (lit 0))
        (Act.prime 0 (lit 1)) []),
      rejects (spec 1 IntMode.tlc32 ["a", "b", "a"] [] [] [] (Act.prime 0 (lit 0))
        (Act.prime 0 (lit 1)) [])] = true := rfl

-- ---- Spec.fuel (B1A-D16) ----

-- The net: no definition (depth 0); sizes by Expr.size's rule: init `conj [prime, prime]`
-- 1 + 2 + 2 = 5; each transition `conj [pred (op [lit, cur]), prime (op ..), prime (op ..)]`
-- 1 + 4 + 4 + 4 = 13, next 1 + 13 + 13 = 27; the invariant `op [lit, cur]` 3; total 35.
-- fuel = 1 + (0 + 1) * (35 + 2 + 1) = 39.
theorem fuel_petri :
    Bool.and (Nat.beq (Spec.callDepth petri) 0)
      (Bool.and (Nat.beq (Spec.size petri) 35) (Nat.beq (Spec.fuel petri) 39)) = true := rfl
-- A chain def0 -> def1: depth 2 (nodes on the longest chain); sizes init 2, next
-- `prime 0 (app 0 [])` 2, bodies 1 and 1: total 6; fuel = 1 + (2 + 1) * (6 + 1 + 1) = 25.
def chain : Spec :=
  spec 1 IntMode.tlc32 [] [] [(0, Expr.app 1 []), (0, lit 1)] [] (Act.prime 0 (lit 0))
    (Act.prime 0 (Expr.app 0 [])) []
theorem fuel_chain :
    Bool.and (Nat.beq (Spec.callDepth chain) 2)
      (Bool.and (Nat.beq (Spec.size chain) 6) (Nat.beq (Spec.fuel chain) 25)) = true := rfl
-- A diamond pool0 -> def0 -> def1, pool0 -> def1, plus an action definition calling def0:
-- the longest chain has 3 nodes (pool0, def0, def1; or actDef0, def0, def1).
def diamond : Spec :=
  spec 1 IntMode.tlc32 [] [add (Expr.app 0 []) (Expr.app 1 [])]
    [(0, add (Expr.app 1 []) (lit 1)), (0, lit 2)]
    [(0, Act.pred (eq (Expr.app 0 []) (lit 3)))] (Act.prime 0 (lit 0)) (Act.call 0 []) []
theorem fuel_diamond_depth :
    Bool.and (Nat.beq (Spec.callDepth diamond) 3) (Spec.wf diamond) = true := rfl

-- ---- Spec.StateWf's decider ----

theorem stateWf_decider :
    Bool.and (Spec.stateWfB petri [int 1, int 0])
      (Bool.and (Bool.not (Spec.stateWfB petri [int 1]))
        (Bool.not (Spec.stateWfB petri [int 1, Value.set [int 2, int 1]]))) = true := rfl

end Sanity
end Model
end Trust
