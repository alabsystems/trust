-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-12 sanity facts for Trust.Model.Syntax (model_prelude_kernel.rs, sanity_files):
-- de Bruijn shifting and substitution (B1A-D15) including the capture case of design
-- 10:675, `Act.inst`, term size, every recursor case of `Expr.mapVar`, and the truth
-- tables of the Boolean encoding definitions (B1A-D11). Elaborated after the whole model
-- prelude; every theorem is accepted by check_model_theorem (kernel re-check,
-- constructive, axiom-free, audited) and is a Bool door closed by rfl (B1A-D54); the
-- mutated-literal doors of SANITY_MUTANTS must each be refuted (class Definite).
--
-- Terms are compared through `exprV`, an injective encoding of a term as a
-- `Value` tree (every constructor a `Value.set` headed by its own tag, lists and options
-- as `Value.set`s of their elements), with the structural `Value.beq`.
--
-- The truth tables run the encodings through `evalB`, a reference evaluator of exactly the
-- fragment they use (lit, ite, letLazy as substitution, and the ops value.as_bool,
-- value.eq, tuple.new, seq.head, seq.tail, plus int.div as an operand that raises), written
-- here as TLC 94d0c50 evaluates those forms: operands left to right, the first error
-- winning; IF raises typeErr on a non-Boolean condition. The expected rows are TLC's
-- (Tool.evalApplImpl, read with `javap -c`: opcodes lnot 27, land 36, lor 37, implies 38,
-- equiv 39), never the encoding's: inputs TRUE, FALSE, a non-Boolean (1) and an operand
-- that raises (1 \div 0, divZero). B1A-14b's `evalE` takes over from `evalB`.

namespace Trust
namespace Model
namespace Sanity

def int (n : Int) : Value := Value.int n

-- ---- Comparing terms: exprV ----

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

-- `exprV e`: e as a Value tree. Motives: a term is a Value, a list or option of
-- terms a List Value, a pair a Value.
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

def exprEq (a b : Expr) : Bool := Value.beq (exprV a) (exprV b)
def actEq (a b : Act) : Bool := Value.beq (actV a) (actV b)

-- ---- The capture case of 10:675 ----
--
-- `Op(c) == \A x \in {1} : c = 0`: the parameter c is `bvar 0` in Op's body, so `bvar 1`
-- under the quantifier's binder x.
def opBody : Expr :=
  Expr.quant QKind.qAll [Expr.lit (Value.set [int 1])]
    (Expr.op PrimOp.valueEq [Expr.bvar 1, Expr.lit (int 0)])

-- `Op(x)` with x the state variable at slot 3: exactly 10:675's term,
-- `quant .qAll [lit (.set [.int 1])] (op .eq [cur iₓ, lit (.int 0)])`, ...
theorem capture_state_var :
    exprEq (Expr.subst [Expr.cur 3] opBody)
      (Expr.quant QKind.qAll [Expr.lit (Value.set [int 1])]
        (Expr.op PrimOp.valueEq [Expr.cur 3, Expr.lit (int 0)])) = true := rfl
-- ... not `op .eq [bvar 0, …]`, the captured reading.
theorem capture_not_bvar0 :
    exprEq (Expr.subst [Expr.cur 3] opBody)
      (Expr.quant QKind.qAll [Expr.lit (Value.set [int 1])]
        (Expr.op PrimOp.valueEq [Expr.bvar 0, Expr.lit (int 0)])) = false := rfl
-- `\E x \in S : Op(x)` with x bound outside: the actual `bvar 0` is shifted under the
-- inner binder to `bvar 1`, the outer x, never the inner one.
theorem capture_bound_actual :
    exprEq (Expr.subst [Expr.bvar 0] opBody)
      (Expr.quant QKind.qAll [Expr.lit (Value.set [int 1])]
        (Expr.op PrimOp.valueEq [Expr.bvar 1, Expr.lit (int 0)])) = true := rfl

-- ---- Substitution (B1A-D15: parameter k of n is bvar (n-1-k)) ----

-- `Sub(a, b) == a - b`: a is `bvar 1`, b is `bvar 0`; `Sub(7, 2)` is `7 - 2`.
theorem subst_parameter_order :
    exprEq (Expr.subst [Expr.lit (int 7), Expr.lit (int 2)]
        (Expr.op PrimOp.intSub [Expr.bvar 1, Expr.bvar 0]))
      (Expr.op PrimOp.intSub [Expr.lit (int 7), Expr.lit (int 2)]) = true := rfl
-- LET y == 5 IN y + z, with z the enclosing scope's `bvar 0` (`bvar 1` in the LET body):
-- y becomes 5 and z is lowered back to `bvar 0`.
theorem subst_lowers_outer :
    exprEq (Expr.subst [Expr.lit (int 5)] (Expr.op PrimOp.intAdd [Expr.bvar 0, Expr.bvar 1]))
      (Expr.op PrimOp.intAdd [Expr.lit (int 5), Expr.bvar 0]) = true := rfl
-- An actual crossing a two-binder list is shifted by two, and the list's domains are read
-- outside it (the domain's `bvar 0` is the parameter).
theorem subst_under_two_binders :
    exprEq (Expr.subst [Expr.cur 1]
        (Expr.quant QKind.qEx [Expr.bvar 0, Expr.bvar 0]
          (Expr.op PrimOp.setEnum [Expr.bvar 0, Expr.bvar 1, Expr.bvar 2])))
      (Expr.quant QKind.qEx [Expr.cur 1, Expr.cur 1]
        (Expr.op PrimOp.setEnum [Expr.bvar 0, Expr.bvar 1, Expr.cur 1])) = true := rfl
theorem subst_bound_actual_under_let :
    exprEq (Expr.subst [Expr.bvar 4]
        (Expr.letLazy (Expr.bvar 0) (Expr.op PrimOp.intAdd [Expr.bvar 0, Expr.bvar 1])))
      (Expr.letLazy (Expr.bvar 4) (Expr.op PrimOp.intAdd [Expr.bvar 0, Expr.bvar 5])) = true :=
  rfl

-- ---- Shifting ----

-- shift 0 2: the domain's free `bvar 0` (outside the binder) and the body's free `bvar 1`
-- rise by 2; the body's local `bvar 0` stays.
theorem shift_free_only :
    exprEq (Expr.shift 0 2
        (Expr.quant QKind.qEx [Expr.bvar 0] (Expr.op PrimOp.valueEq [Expr.bvar 0, Expr.bvar 1])))
      (Expr.quant QKind.qEx [Expr.bvar 2] (Expr.op PrimOp.valueEq [Expr.bvar 0, Expr.bvar 3]))
      = true := rfl
-- The cutoff: shift 1 1 leaves `bvar 0` and raises `bvar 1`.
theorem shift_cutoff :
    exprEq (Expr.shift 1 1 (Expr.op PrimOp.setEnum [Expr.bvar 0, Expr.bvar 1, Expr.cur 0]))
      (Expr.op PrimOp.setEnum [Expr.bvar 0, Expr.bvar 2, Expr.cur 0]) = true := rfl

-- Every constructor of Expr and Act, every list, option and pair case of the recursor
-- (`Expr.mapVar`), under nested binders of every kind: shift 0 1 raises exactly the free
-- variables.
def everyCtor (d fb1 fb2 fb3 fb4 fb5 fb9 : Nat) : Expr :=
  Expr.quant QKind.qFn [Expr.bvar d]
    (Expr.caseOf [(Expr.bvar 0, Expr.bvar fb1)]
      (some (Expr.letLazy (Expr.bvar fb2)
        (Expr.app 0
          [Expr.bvar 0, Expr.bvar fb3, Expr.caseOf [] none,
            Expr.enabled
              (Act.ex [Expr.bvar fb2]
                (Act.conj
                  [Act.pred (Expr.bvar 0), Act.prime 0 (Expr.bvar fb3),
                    Act.primeIn 1 (Expr.bvar 1), Act.unchanged (Expr.cur 0),
                    Act.changed (Expr.bvar 2),
                    Act.disj [Act.fa [Expr.bvar 1, Expr.bvar 0] (Act.pred (Expr.bvar 2))],
                    Act.ite (Expr.bvar fb4) (Act.call 0 [Expr.bvar 0])
                      (Act.letA (Expr.bvar fb3) (Act.pred (Expr.bvar 0))),
                    Act.caseOf [(Expr.bvar fb3, Act.pchoice [(2, Act.pred (Expr.bvar fb4))])]
                      (some (Act.pred (Expr.bvar fb9))),
                    Act.caseOf [] none])),
            Expr.op PrimOp.setEnum [Expr.cur 0, Expr.nxt 1, Expr.pool 2, Expr.lit (int 7)],
            Expr.ite (Expr.bvar 0) (Expr.bvar 1) (Expr.bvar fb5)]))))

-- In `everyCtor 0 1 2 3 4 3 9` the free variables are the outer domain's `bvar 0` and
-- every `fb*` position: fb1 = 1 at depth 1, fb2 = 2 at depths 1 and 2 (the LET's value and
-- the \E's domain), fb3 = 3 at depths 2 and 3, fb4 = 4 at depth 3, fb5 = 3 at depth 2 and
-- fb9 = 9 at depth 4; every other variable is local. shift 0 1 raises exactly the free
-- ones, so the image is `everyCtor 1 2 3 4 5 4 10`.
theorem mapVar_every_constructor :
    exprEq (Expr.shift 0 1 (everyCtor 0 1 2 3 4 3 9)) (everyCtor 1 2 3 4 5 4 10) = true := rfl
-- With every `fb*` at 0 they are all local: only the outer domain moves.
theorem mapVar_locals_stay :
    exprEq (Expr.shift 0 5 (everyCtor 0 0 0 0 0 0 0)) (everyCtor 5 0 0 0 0 0 0) = true := rfl

-- ---- Act.subst and Act.inst ----

-- One binder: x' = p + 1 with p := 5.
theorem inst_one :
    actEq (Act.inst [int 5] (Act.prime 0 (Expr.op PrimOp.intAdd [Expr.bvar 0, Expr.lit (int 1)])))
      (Act.prime 0 (Expr.op PrimOp.intAdd [Expr.lit (int 5), Expr.lit (int 1)])) = true := rfl
-- Two binders, in order: binder 0 is `bvar 1`, binder 1 is `bvar 0`.
theorem inst_two :
    actEq (Act.inst [int 1, int 2] (Act.pred (Expr.op PrimOp.intSub [Expr.bvar 1, Expr.bvar 0])))
      (Act.pred (Expr.op PrimOp.intSub [Expr.lit (int 1), Expr.lit (int 2)])) = true := rfl
-- Under the action's own \E binder the instantiated binder is `bvar 1`; the \E's own
-- variable stays.
theorem inst_under_ex :
    actEq (Act.inst [int 5]
        (Act.ex [Expr.lit (Value.set [int 1])]
          (Act.prime 0 (Expr.op PrimOp.intAdd [Expr.bvar 0, Expr.bvar 1]))))
      (Act.ex [Expr.lit (Value.set [int 1])]
        (Act.prime 0 (Expr.op PrimOp.intAdd [Expr.bvar 0, Expr.lit (int 5)]))) = true := rfl
-- Act.subst through letA: the actual `cur 0` is placed under the LET's binder.
theorem act_subst_letA :
    actEq (Act.subst [Expr.cur 0]
        (Act.letA (Expr.lit (int 1)) (Act.pred (Expr.op PrimOp.valueEq [Expr.bvar 0, Expr.bvar 1]))))
      (Act.letA (Expr.lit (int 1)) (Act.pred (Expr.op PrimOp.valueEq [Expr.bvar 0, Expr.cur 0])))
      = true := rfl

-- ---- Size ----

theorem size_facts :
    Bool.and (Nat.beq (Expr.size (Expr.op PrimOp.intAdd [Expr.lit (int 1), Expr.bvar 0])) 3)
      (Bool.and (Nat.beq (Expr.size opBody) 5)
        (Bool.and (Nat.beq (Expr.size (Expr.caseOf [(Expr.lit (int 1), Expr.lit (int 2))]
            (some (Expr.lit (int 3))))) 4)
          (Bool.and (Nat.beq (Act.size (Act.prime 0 (Expr.lit (int 1)))) 2)
            (Bool.and (Nat.beq (Act.size (Act.pchoice [(1, Act.conj [])])) 2)
              (Nat.beq (Expr.size (Expr.enabled (Act.ex [Expr.cur 0] (Act.pred (Expr.bvar 0)))))
                5))))) = true := rfl
-- A literal counts 1 whatever its value.
theorem size_literal :
    Nat.beq (Expr.size (Expr.lit (Value.set [int 1, int 2, int 3]))) 1 = true := rfl

-- ---- The Boolean encodings (B1A-D11) against TLC's rules ----

-- `evalAll go es`: es evaluated left to right; the first error wins.
def evalAll (go : Expr → Res Value) (es : List Expr) : Res (List Value) :=
  @List.rec Expr (fun _ => Res (List Value))
    (Res.ok [])
    (fun e _ rest => Res.bind (go e) (fun v => Res.map (List.cons v) rest))
    es

-- `asBoolV v`: v when it is a Boolean, else typeErr (value.as_bool, IF's condition).
def asBoolV (v : Value) : Res Value :=
  @Option.casesOn Bool (fun _ => Res Value) (Value.asBool v) (Res.error Fail.typeErr)
    (fun b => Res.ok (Value.bool b))

-- Head and Tail of a tuple (TLC's Sequences.Head returns the element; Tail re-numbers).
def headV (v : Value) : Res Value :=
  @Option.casesOn (List (Prod Value Value)) (fun _ => Res Value) (Value.asFn v)
    (Res.error Fail.typeErr)
    (fun ps => @List.casesOn (Prod Value Value) (fun _ => Res Value) ps
      (Res.error Fail.notInDomain) (fun p _ => Res.ok (Prod.snd p)))
def tailV (v : Value) : Res Value :=
  @Option.casesOn (List (Prod Value Value)) (fun _ => Res Value) (Value.asFn v)
    (Res.error Fail.typeErr)
    (fun ps => @List.casesOn (Prod Value Value) (fun _ => Res Value) ps
      (Res.error Fail.notInDomain)
      (fun _ rest => Res.ok (mkTuple (List.map (@Prod.snd Value Value) rest))))

def isOp (o p : PrimOp) : Bool := Value.beq (opCode o) (opCode p)

-- `applyOp o vs`: the fragment's ops on evaluated operands.
def applyOp (o : PrimOp) (vs : List Value) : Res Value :=
  @Bool.rec (fun _ => Res Value)
    (@Bool.rec (fun _ => Res Value)
      (@Bool.rec (fun _ => Res Value)
        (@Bool.rec (fun _ => Res Value)
          (@Bool.rec (fun _ => Res Value)
            (@Bool.rec (fun _ => Res Value)
              (Res.error Fail.fuel)
              (@Option.casesOn Int (fun _ => Res Value) (Value.asInt (listGetD vs 0))
                (Res.error Fail.typeErr)
                (fun a => @Option.casesOn Int (fun _ => Res Value) (Value.asInt (listGetD vs 1))
                  (Res.error Fail.typeErr)
                  (fun b => Res.map Value.int (intDiv IntMode.tlc32 a b))))
              (isOp o PrimOp.intDiv))
            (tailV (listGetD vs 0))
            (isOp o PrimOp.seqTail))
          (headV (listGetD vs 0))
          (isOp o PrimOp.seqHead))
        (Res.ok (mkTuple vs))
        (isOp o PrimOp.tupleNew))
      (Res.map Value.bool (valueEq (listGetD vs 0) (listGetD vs 1)))
      (isOp o PrimOp.valueEq))
    (asBoolV (listGetD vs 0))
    (isOp o PrimOp.valueAsBool)

-- `evalB fuel e`: the reference evaluator of the encodings' fragment; any other form is
-- `fuel` (never expected below).
def evalB (fuel : Nat) : Expr → Res Value :=
  @Nat.rec (fun _ => Expr → Res Value)
    (fun _ => Res.error Fail.fuel)
    (fun _ go e =>
      @Expr.casesOn
        (fun _ => Res Value) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
        (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
        (fun _ => Nat) (fun _ => Nat)
        e
        (fun v => Res.ok v)
        (fun _ => Res.error Fail.fuel) (fun _ => Res.error Fail.fuel)
        (fun _ => Res.error Fail.fuel) (fun _ => Res.error Fail.fuel)
        (fun o args => Res.bind (evalAll go args) (fun vs => applyOp o vs))
        (fun c t f => Res.bind (go c) (fun v =>
          @Option.casesOn Bool (fun _ => Res Value) (Value.asBool v) (Res.error Fail.typeErr)
            (fun b => @Bool.rec (fun _ => Res Value) (go f) (go t) b)))
        (fun _ _ => Res.error Fail.fuel)
        (fun x b => go (Expr.subst [x] b))
        (fun _ _ _ => Res.error Fail.fuel)
        (fun _ _ => Res.error Fail.fuel)
        (fun _ => Res.error Fail.fuel)
        (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0)
        (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0)
        (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0)
        0 (fun _ _ => 0)
        0 (fun _ _ => 0)
        0 (fun _ => 0)
        0 (fun _ _ => 0)
        0 (fun _ _ => 0)
        0 (fun _ => 0)
        0 (fun _ _ => 0)
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0))
    fuel

def failTag (f : Fail) : Nat :=
  @Fail.casesOn (fun _ => Nat) f 0 1 2 3 4 5 6 7 8 (fun _ => 9) 10 11 12 (fun _ => 13)

-- `resIs r s`: the same value (structurally) or an error of the same class.
def resIs (r s : Res Value) : Bool :=
  @Res.rec Value (fun _ => Bool)
    (fun v => @Res.rec Value (fun _ => Bool) (fun w => Value.beq v w) (fun _ => false) s)
    (fun e => @Res.rec Value (fun _ => Bool) (fun _ => false)
      (fun f => Nat.beq (failTag e) (failTag f)) s)
    r

-- Inputs and outputs.
def inT : Expr := Expr.lit (Value.bool true)
def inF : Expr := Expr.lit (Value.bool false)
def inN : Expr := Expr.lit (int 1)
def inE : Expr := Expr.op PrimOp.intDiv [Expr.lit (int 1), Expr.lit (int 0)]
def oT : Res Value := Res.ok (Value.bool true)
def oF : Res Value := Res.ok (Value.bool false)
def oTE : Res Value := Res.error Fail.typeErr
def oDZ : Res Value := Res.error Fail.divZero

-- `row con a b r`: the encoding `con a b` evaluates to r.
def row (con : Expr → Expr → Expr) (a b : Expr) (r : Res Value) : Bool :=
  resIs (evalB 40 (con a b)) r

-- `table con rows`: every row (a, b, r) holds.
def table (con : Expr → Expr → Expr) (rows : List (Prod Expr (Prod Expr (Res Value)))) :
    Bool :=
  @List.rec (Prod Expr (Prod Expr (Res Value))) (fun _ => Bool) true
    (fun x _ rest =>
      Bool.and (row con (Prod.fst x) (Prod.fst (Prod.snd x)) (Prod.snd (Prod.snd x))) rest)
    rows

-- ~a (lnot): the operand checked, then negated.
theorem not_truth_table :
    table (fun a _ => Expr.not_ a)
      [(inT, inT, oF), (inF, inT, oT), (inN, inT, oTE), (inE, inT, oDZ)] = true := rfl
-- a /\ b (land): FALSE short-circuits; b checked only after a TRUE a.
theorem and_truth_table :
    table Expr.and_
      [(inT, inT, oT), (inT, inF, oF), (inT, inN, oTE), (inT, inE, oDZ),
        (inF, inT, oF), (inF, inF, oF), (inF, inN, oF), (inF, inE, oF),
        (inN, inT, oTE), (inN, inF, oTE), (inN, inN, oTE), (inN, inE, oTE),
        (inE, inT, oDZ), (inE, inF, oDZ), (inE, inN, oDZ), (inE, inE, oDZ)] = true := rfl
-- a \/ b (lor): TRUE short-circuits.
theorem or_truth_table :
    table Expr.or_
      [(inT, inT, oT), (inT, inF, oT), (inT, inN, oT), (inT, inE, oT),
        (inF, inT, oT), (inF, inF, oF), (inF, inN, oTE), (inF, inE, oDZ),
        (inN, inT, oTE), (inN, inF, oTE), (inN, inN, oTE), (inN, inE, oTE),
        (inE, inT, oDZ), (inE, inF, oDZ), (inE, inN, oDZ), (inE, inE, oDZ)] = true := rfl
-- a => b (implies): FALSE short-circuits to TRUE.
theorem implies_truth_table :
    table Expr.implies_
      [(inT, inT, oT), (inT, inF, oF), (inT, inN, oTE), (inT, inE, oDZ),
        (inF, inT, oT), (inF, inF, oT), (inF, inN, oT), (inF, inE, oT),
        (inN, inT, oTE), (inN, inF, oTE), (inN, inN, oTE), (inN, inE, oTE),
        (inE, inT, oDZ), (inE, inF, oDZ), (inE, inN, oDZ), (inE, inE, oDZ)] = true := rfl
-- a <=> b (equiv): both operands evaluated, then both checked; so a non-Boolean a with a
-- raising b gives b's error (the row (inN, inE)).
theorem equiv_truth_table :
    table Expr.equiv_
      [(inT, inT, oT), (inT, inF, oF), (inT, inN, oTE), (inT, inE, oDZ),
        (inF, inT, oF), (inF, inF, oT), (inF, inN, oTE), (inF, inE, oDZ),
        (inN, inT, oTE), (inN, inF, oTE), (inN, inN, oTE), (inN, inE, oDZ),
        (inE, inT, oDZ), (inE, inF, oDZ), (inE, inN, oDZ), (inE, inE, oDZ)] = true := rfl
-- Why `Expr.equiv_` binds a tuple: the direct form `value.eq` of the two checked operands
-- checks a before evaluating b, so it gives typeErr on that row where TLC gives b's error.
def naiveEquiv (a b : Expr) : Expr :=
  Expr.op PrimOp.valueEq [Expr.op PrimOp.valueAsBool [a], Expr.op PrimOp.valueAsBool [b]]
theorem naive_equiv_differs :
    Bool.and (row naiveEquiv inN inE oTE) (row Expr.equiv_ inN inE oDZ) = true := rfl

end Sanity
end Model
end Trust
