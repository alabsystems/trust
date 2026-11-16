-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-16 sanity facts for Trust.Model.Tlc's laziness I (model_prelude_kernel.rs,
-- sanity_files): forcing-table rows 1-6 (design 10:612-617) at value level: function
-- constructors (materialized or a `lazyFn`), keepLazy (set on a function operand, inherited,
-- reset at an item's right-hand side by `Tlc.rhsX`), `applyX` on a `lazyFn`, an `fnX` and a
-- `val`, DOMAIN unforced, EXCEPT, record select, Head and Tail, and `force` in TLC's order.
-- Elaborated after the whole model prelude; every theorem is accepted by
-- check_model_theorem and is a Bool door closed by rfl (B1A-D54); the mutated-literal doors
-- of SANITY_MUTANTS must each be refuted (class Definite).
--
-- Where the expectations come from. The batch-C facts are the recorded outcomes of the
-- TY-PROBE track's batch C (B1A-06; ty reports/perf/2026-10-09-beyond-tla-b1a/probes/,
-- `[Name]` = probes/tlc-Name.txt; the outcomes are probes/INDEX.tsv's), restated at value
-- level: each probe's next-state right-hand side evaluated and forced (`evalE`, keepLazy off,
-- as TLC evaluates an assignment's right-hand side under Clear and fingerprints the
-- successor). The other facts are this row's probes on the jar of record (TLC 94d0c50),
-- `[lazy-probes/Name]` = ty reports/perf/2026-10-09-beyond-tla-b1a/lazy-probes/tlc-Name.txt:
-- each binds `s'` to the expression, a value probe's invariant `Pin` is violated exactly when
-- `s'` is the stated value, an error probe's log names the error (class by ../tools/causes.tsv).
-- The W1-committed probes PR-LazyPool3/-Domain/-Forced are cited by their LEDGER rows. A fact
-- with no TLA+ counterpart cites the design. Never the encoding itself.

namespace Trust
namespace Model
namespace Sanity

def int (n : Int) : Value := Value.int n
def num (n : Int) : Expr := Expr.lit (Value.int n)
def tt : Expr := Expr.lit (Value.bool true)
def op (o : PrimOp) (xs : List Expr) : Expr := Expr.op o xs
def setE (xs : List Expr) : Expr := op PrimOp.setEnum xs
def tupE (xs : List Expr) : Expr := op PrimOp.tupleNew xs
def strE (r : Nat) : Expr := Expr.lit (Value.str r)
def natE : Expr := Expr.lit (Value.infSet InfKind.nat [])
def neg (e : Expr) : Expr := op PrimOp.intNeg [e]
def dv (a b : Expr) : Expr := op PrimOp.intDiv [a, b]
def add (a b : Expr) : Expr := op PrimOp.intAdd [a, b]
def sub (a b : Expr) : Expr := op PrimOp.intSub [a, b]
def mul (a b : Expr) : Expr := op PrimOp.intMul [a, b]
def eqE (a b : Expr) : Expr := op PrimOp.valueEq [a, b]
def qfn (ds : List Expr) (b : Expr) : Expr := Expr.quant QKind.qFn ds b
def app (f a : Expr) : Expr := op PrimOp.funcApply [f, a]
def dom (f : Expr) : Expr := op PrimOp.funcDomain [f]
def exc (f x v : Expr) : Expr := op PrimOp.funcExcept [f, x, v]
def hd (s : Expr) : Expr := op PrimOp.seqHead [s]
def tl (s : Expr) : Expr := op PrimOp.seqTail [s]
def tup (vs : List Value) : Value := mkTuple vs
-- CHOOSE z \in {} : TRUE: raises `chooseFailed` wherever it is evaluated.
def bad : Expr := Expr.quant QKind.qChoose [setE []] tt
-- [y \in {0, 1} |-> 1 \div y]: raises `divZero` at 0 when the body runs there.
def ctor : Expr := qfn [setE [num 0, num 1]] (dv (num 1) (Expr.bvar 0))

-- The spec of the facts: one variable; pool entries `S == {0, 1}` (0),
-- `F == [y \in S |-> 1 \div y]` (1), `Dbl == [n \in Nat |-> 2 * n]` (2), as batch C writes
-- them (constant-level definitions are pool entries, evaluated at use, 10:135).
def spL : Spec :=
  Spec.mk 1 IntMode.tlc32 [] [setE [num 0, num 1], qfn [Expr.pool 0] (dv (num 1) (Expr.bvar 0)),
      qfn [natE] (mul (num 2) (Expr.bvar 0))]
    [] [] [] (Act.conj []) (Act.conj []) [] [] [] [] true ChoiceMode.none

-- `evS s e`: e evaluated and forced (`evalE`, 10:301-302) at fuel 64 (every term below nests
-- far less), keepLazy off, at the state s (successor s); `ev e` at the state [0].
def evS (s : State) (e : Expr) : Res Value := evalE spL 64 [] s s e
def ev (e : Expr) : Res Value := evS [int 0] e

-- `evX k e`: `evalX` itself, unforced, keepLazy k, at the state [0] and frame [none].
def evX (k : Bool) (e : Expr) : Res XVal := evalX spL 64 k [] [int 0] [Option.none] e

-- ---- Reading results ----

-- The constructor of a Fail, in declaration order (10:93-100): notInDomain 1, chooseFailed
-- 2, divZero 3, typeErr 4, unmodeled 13.
def failTag (f : Fail) : Nat :=
  @Fail.casesOn (fun _ => Nat) f 0 1 2 3 4 5 6 7 8 (fun _ => 9) 10 11 12 (fun _ => 13)
def errTag {α : Type} (r : Res α) (t : Nat) : Bool :=
  @Res.rec α (fun _ => Bool) (fun _ => false) (fun f => Nat.beq (failTag f) t) r
def isNotInDomain {α : Type} (r : Res α) : Bool := errTag r 1
def isChooseFailed {α : Type} (r : Res α) : Bool := errTag r 2
def isDivZero {α : Type} (r : Res α) : Bool := errTag r 3
def isTypeErr {α : Type} (r : Res α) : Bool := errTag r 4
def isUnmodeled {α : Type} (r : Res α) (code : Nat) : Bool :=
  @Res.rec α (fun _ => Bool) (fun _ => false)
    (fun f => @Fail.casesOn (fun _ => Bool) f false false false false false false false false
      false (fun _ => false) false false false (fun c => Nat.beq c code))
    r
def isPending {α : Type} (r : Res α) : Bool := isUnmodeled r Code.todo
def isOkWith {α : Type} (r : Res α) (p : α → Bool) : Bool :=
  @Res.rec α (fun _ => Bool) (fun a => p a) (fun _ => false) r
def okV (r : Res Value) (v : Value) : Bool := isOkWith r (fun a => Value.beq a v)
-- The constructor of an XVal: 0 val, 1 lazyFn, 2 fnX, 3 lazySet.
def xTag (x : XVal) : Nat := XVal.elim x (fun _ => 0) (fun _ _ _ => 1) (fun _ => 2) (fun _ => 3)
def isX (r : Res XVal) (t : Nat) : Bool := isOkWith r (fun x => Nat.beq (xTag x) t)
def allT (bs : List Bool) : Bool := @List.rec Bool (fun _ => Bool) true (fun b _ r => Bool.and b r) bs

-- ---- Batch C (B1A-06), at value level ----

-- [PointwiseDemand] `x' = F[x]` from x = 1 and [LazyPoolInit] `Init == x = F[1]` (with
-- LEDGER PR-LazyPool3): F is applied at 1 only, its unused point 0 never raises: F[x] at
-- x = 1 and F[1] are 1. F read whole under Clear is materialized at its construction
-- and raises there (LEDGER PR-LazyPoolForced, `x' = F`; PR-LazyPoolDomain, `DOMAIN F`).
theorem lazy_pool :
    allT [okV (evS [int 1] (app (Expr.pool 1) (Expr.cur 0))) (int 1),
      okV (ev (app (Expr.pool 1) (num 1))) (int 1),
      isDivZero (ev (Expr.pool 1)),
      isDivZero (ev (dom (Expr.pool 1)))] = true := rfl

-- [LazyTuple] `<<F, 1>>[2]` is 1: keepLazy is inherited through the tuple, which holds F
-- unforced (an `fnX`), and its entry 2 is returned.
theorem lazy_tuple :
    allT [okV (ev (app (tupE [Expr.pool 1, num 1]) (num 2))) (int 1),
      isX (evX true (tupE [Expr.pool 1, num 1])) 2] = true := rfl

-- [LazyTupleKeep] `<<[y \in {0, 1} |-> 1 \div y], 1>>[2]` is 1: the in-place constructor,
-- a function operand's element, is kept lazy (10:614-615).
theorem lazy_tuple_keep :
    okV (ev (app (tupE [ctor, num 1]) (num 2))) (int 1) = true := rfl

-- [LazyTupleClear] `x' = <<[y \in {0, 1} |-> 1 \div y], CHOOSE z \in {} : TRUE>>` raises
-- divZero, not chooseFailed: under Clear the constructor is materialized at construction,
-- before the second element. keepLazy is reset at an item's right-hand side (`Tlc.rhsX`,
-- `Tlc.rule.keepLazyReset`, 10:615): evaluated from keepLazy on, the same tuple keeps the
-- constructor lazy and raises chooseFailed; as a right-hand side it raises divZero.
theorem lazy_tuple_clear :
    allT [isDivZero (ev (tupE [ctor, bad])),
      isChooseFailed (evX true (tupE [ctor, bad])),
      isDivZero (Tlc.rhsX (Tlc.run spL 64) true [] [int 0] [Option.none] (tupE [ctor, bad]))]
      = true := rfl

-- [LazyNatDomain] `x' = Dbl[x + 1]` with `Dbl == [n \in Nat |-> 2 * n]` completes: Dbl
-- stays a `lazyFn` even under Clear (Nat is not Reducible), applied pointwise: 2, 4, 6.
theorem lazy_nat_domain :
    allT [okV (evS [int 0] (app (Expr.pool 2) (add (Expr.cur 0) (num 1)))) (int 2),
      okV (evS [int 2] (app (Expr.pool 2) (add (Expr.cur 0) (num 1)))) (int 6),
      isX (evX false (Expr.pool 2)) 1] = true := rfl

-- [LazyDeadBranchTuple] the right-hand side `<<[y \in {0, 1} |-> 1 \div y], 1>>[1]` is
-- evaluated without error, to a `lazyFn` (bound unforced, 10:620); [LazyDeadBranchTupleLive]
-- forcing it when the successor is emitted raises divZero.
theorem lazy_dead_branch_tuple :
    allT [isX (evX false (app (tupE [ctor, num 1]) (num 1))) 1,
      isDivZero (ev (app (tupE [ctor, num 1]) (num 1)))] = true := rfl

-- [LazyExcept] and [LazyExceptOtherPoint]: EXCEPT on a lazy function is the named refusal
-- `unmodeled lazy.except` (10:617; ALLOWED_NONEXACT, TASK-STATE 7.5): shown here on a lazy
-- function over Nat; their own G is over SUBSET {0} (B1A-17a, `lazy_pending`).
theorem lazy_except_refused :
    isUnmodeled (ev (exc (qfn [natE] (Expr.bvar 0)) (num 0) (num 7))) Code.lazyExcept = true := rfl

-- Still pending: batch C's other probes build SUBSET, a lazy set (B1A-17a): [LazyFilterDomain]
-- (F over a filter over SUBSET {1, 2}), [LazyDomainNonReducible], [LazyExcept] and
-- [LazyDeadBranchSubset] (G over SUBSET {0}); [LazyEmitOrder*] and [LazyRefusedForce*] also
-- need generate mode (B1A-18). These facts change with those rows.
def gSub : Expr := qfn [op PrimOp.setPowerset [setE [num 0]]]
  (dv (num 1) (op PrimOp.setCard [Expr.bvar 0]))
theorem lazy_pending :
    allT [isPending (ev gSub),
      isPending (ev (app (exc gSub (setE []) (num 7)) (setE []))),
      isPending (ev (op PrimOp.setCard [dom gSub]))] = true := rfl

-- ---- Construction (forcing-table row 1) ----

-- [lazy-probes/PLazyCtorOrder] a two-binder constructor materialized at construction runs its
-- body FIRST binder fastest: (2, 1) raises chooseFailed before (1, 2) would raise divZero;
-- [lazy-probes/PLazyCtorSetOrder] over `{2, 1}`, the domain normalized: 1 (chooseFailed)
-- before 2 (divZero). Materialized, `[x \in {FALSE, TRUE} |-> x]` is the function of its
-- values (10:614; B1A-14b's `core_pending` qFn door, restated), and with two binders its keys
-- are the tuples in TLC's order.
def ctorOrder : Expr :=
  qfn [setE [num 1, num 2], setE [num 1, num 2]]
    (Expr.ite (Expr.and_ (eqE (Expr.bvar 1) (num 2)) (eqE (Expr.bvar 0) (num 1))) bad
      (Expr.ite (Expr.and_ (eqE (Expr.bvar 1) (num 1)) (eqE (Expr.bvar 0) (num 2)))
        (dv (num 1) (num 0)) (num 0)))
theorem lazy_ctor :
    allT [isChooseFailed (ev ctorOrder),
      isChooseFailed (ev (qfn [setE [num 2, num 1]]
        (Expr.ite (eqE (Expr.bvar 0) (num 2)) (dv (num 1) (num 0)) bad))),
      okV (ev (qfn [setE [Expr.lit (Value.bool false), tt]] (Expr.bvar 0)))
        (Value.fn [(Value.bool false, Value.bool false), (Value.bool true, Value.bool true)]),
      okV (ev (qfn [setE [num 2, num 1], setE [num 3, num 4]] (sub (Expr.bvar 1) (Expr.bvar 0))))
        (Value.fn [(tup [int 1, int 3], int (-2)), (tup [int 1, int 4], int (-3)),
          (tup [int 2, int 3], int (-1)), (tup [int 2, int 4], int (-2))])] = true := rfl

-- ---- Application (rows 2-4) ----

-- [lazy-probes/PLazyApplyCtl] `DOMAIN ([x \in {1} |-> <<[y \in {0, 1} |-> 1 \div y], 2>>][1])`
-- raises divZero: the lazy function's body runs under the APPLICATION's keepLazy (off here),
-- so the inner constructor is materialized; [lazy-probes/PLazyApplyKeep] as a function
-- operand itself, `(...[1])[2]`, the body runs under keepLazy on and gives 2.
def fTup : Expr := qfn [setE [num 1]] (tupE [ctor, num 2])
theorem lazy_apply_control :
    allT [isDivZero (ev (dom (app fTup (num 1)))),
      okV (ev (app (app fTup (num 1)) (num 2))) (int 2)] = true := rfl

-- [lazy-probes/PLazyNotInDomain] `[n \in Nat |-> n][-1]` is notInDomain (row 106);
-- [lazy-probes/PLazyApplyNonFnFirst] `3[1 \div 0]` is typeErr: a value that is not a
-- function raises before the argument is evaluated (row 163); [lazy-probes/PLazyApplyTwo]
-- `[x, y \in Nat |-> x - y][<<5, 2>>]` is 3; [lazy-probes/PLazyApplyTwoOut] with `<<5, -2>>`
-- notInDomain; [lazy-probes/PLazyApplyTwoLong] with `<<5, 2, 9>>` 3 (TLC ignores the third
-- component). A lazy argument is `unmodeled lazy.arg` (10:615): `[x \in Nat |-> 0]` applied
-- to `[n \in Nat |-> n]`, which is lazy even under Clear.
def fTwo : Expr := qfn [natE, natE] (sub (Expr.bvar 1) (Expr.bvar 0))
theorem lazy_apply :
    allT [isNotInDomain (ev (app (qfn [natE] (Expr.bvar 0)) (neg (num 1)))),
      isTypeErr (ev (app (num 3) (dv (num 1) (num 0)))),
      okV (ev (app fTwo (tupE [num 5, num 2]))) (int 3),
      isNotInDomain (ev (app fTwo (tupE [num 5, neg (num 2)]))),
      okV (ev (app fTwo (tupE [num 5, num 2, num 9]))) (int 3),
      isUnmodeled (ev (app (qfn [natE] (num 0)) (qfn [natE] (Expr.bvar 0)))) Code.lazyArg]
      = true := rfl

-- ---- DOMAIN (row 5), record select, EXCEPT (row 6) ----

-- [lazy-probes/PLazyDomainNat] `0 \in DOMAIN [n \in Nat |-> 1 \div n]` is TRUE: DOMAIN
-- returns the unforced domain, the body never runs. With two binders it is their product,
-- a lazy set (10:616).
theorem lazy_domain :
    allT [okV (ev (op PrimOp.setIn [num 0, dom (qfn [natE] (dv (num 1) (Expr.bvar 0)))]))
        (Value.bool true),
      isX (evX false (dom fTwo)) 3] = true := rfl

-- [lazy-probes/PLazyRecGetForces] `<<[x \in {"a", "b"} |-> IF x = "b" THEN 1 \div 0 ELSE
-- 1].a>>[1]` raises divZero: record select forces a lazy function; [lazy-probes/PLazyRecGetKeep]
-- `([a |-> [y \in {0, 1} |-> 1 \div y], b |-> 2].a)[1]` is 1: a record's lazy entry is
-- returned unforced. ("a", "b" are string ranks 378, 380.)
theorem lazy_rec_get :
    allT [isDivZero (ev (app (tupE [op (PrimOp.recGet 378)
          [qfn [setE [strE 378, strE 380]]
            (Expr.ite (eqE (Expr.bvar 0) (strE 380)) (dv (num 1) (num 0)) (num 1))]])
        (num 1))),
      okV (ev (app (op (PrimOp.recGet 378) [op (PrimOp.recNew [378, 380]) [ctor, num 2]])
        (num 1))) (int 1)] = true := rfl

-- [lazy-probes/PLazyExceptOut] `[<<1>> EXCEPT ![5] = 1 \div 0]` is <<1>>: a point outside the
-- domain leaves the function unchanged and the new value is never evaluated;
-- [lazy-probes/PLazyExceptNonFnPath] `[3 EXCEPT ![1 \div 0] = 2]` raises divZero (the point
-- before the base's kind); [lazy-probes/PLazyExceptKeep]
-- `([<<[y \in {0, 1} |-> 1 \div y], 2>> EXCEPT ![2] = 3][1])[1]` is 1: the other entry stays
-- lazy.
theorem lazy_except :
    allT [okV (ev (exc (tupE [num 1]) (num 5) (dv (num 1) (num 0)))) (tup [int 1]),
      isDivZero (ev (exc (num 3) (dv (num 1) (num 0)) (num 2))),
      okV (ev (app (app (exc (tupE [ctor, num 2]) (num 2) (num 3)) (num 1)) (num 1))) (int 1)]
      = true := rfl

-- ---- Head and Tail ----

-- [lazy-probes/PLazyHeadKeep] `Head(<<<<[y \in {0, 1} |-> 1 \div y], 2>>, 1>>)[2]` is 2 and
-- [lazy-probes/PLazyTailKeep] `Tail(<<[y \in {0, 1} |-> 1 \div y], 1>>)[1]` is 1: a Java
-- override's operand inherits keepLazy, and the entries stay unforced;
-- [lazy-probes/PLazyHeadFn] `Head([i \in 1..2 |-> IF i = 1 THEN <<5>> ELSE 1 \div 0])[1]`
-- raises divZero: toTuple runs the body at every index.
theorem lazy_head_tail :
    allT [okV (ev (app (hd (tupE [tupE [ctor, num 2], num 1])) (num 2))) (int 2),
      okV (ev (app (tl (tupE [ctor, num 1])) (num 1))) (int 1),
      isDivZero (ev (app (hd (qfn [op PrimOp.setRange [num 1, num 2]]
        (Expr.ite (eqE (Expr.bvar 0) (num 1)) (tupE [num 5]) (dv (num 1) (num 0))))) (num 1)))]
      = true := rfl

-- ---- force ----

-- [lazy-probes/PLazyForceNat] `[n \in Nat |-> n]` forced raises typeErr (the domain's
-- size(), row 144); [lazy-probes/PLazyForceOrder] a lazy function whose point 1 holds a
-- raising lazy constructor and whose point 2 raises chooseFailed, forced: chooseFailed (every
-- body first, then the values forced); an `fnX` is forced entry by entry, so
-- `<<[n \in Nat |-> n], 1>>` forced raises its first entry's typeErr (PLazyForceNat's class).
theorem lazy_force :
    allT [isTypeErr (ev (qfn [natE] (Expr.bvar 0))),
      isChooseFailed (ev (app (tupE [qfn [setE [num 1, num 2]]
        (Expr.ite (eqE (Expr.bvar 0) (num 1)) (qfn [setE [num 0]] (dv (num 1) (Expr.bvar 0))) bad)])
        (num 1))),
      isTypeErr (ev (app (tupE [tupE [qfn [natE] (Expr.bvar 0), num 1]]) (num 1)))] = true := rfl

end Sanity
end Model
end Trust
