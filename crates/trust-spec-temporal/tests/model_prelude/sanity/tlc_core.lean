-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-14b sanity facts for Trust.Model.Tlc's core evaluation (model_prelude_kernel.rs,
-- sanity_files): the core cases of `evalX` (lit, cur, nxt, bvar, pool, ite, caseOf, letLazy,
-- app, and quant over `val` sets), `Frame.ofState` and `evalE` (design 10:299-302).
-- Elaborated after the whole model prelude; every theorem is accepted by
-- check_model_theorem and is a Bool door closed by rfl (B1A-D54); the mutated-literal doors
-- of SANITY_MUTANTS must each be refuted (class Definite).
--
-- Where the expectations come from. Every TLA+ fact below is the recorded outcome of a TLC
-- probe on the jar of record (TLC 94d0c50, sha256 7beec0f0...ea78d), run by this row with
-- `b1a_ttlc --dir $B1A_TREC/core-probes` and committed in ty
-- reports/perf/2026-10-09-beyond-tla-b1a/core-probes/ (each probe binds `s'` to the
-- expression; a value probe's invariant `Pin` is violated exactly when `s'` is the stated
-- value; an error probe's log names the error, its class by ../tools/causes.tsv). The
-- citation `[Name]` is the log `core-probes/tlc-Name.txt`; `[cause-probes/Name]` is
-- ../tools/cause-probes/tlc-Name.txt. Facts with no TLA+ counterpart (an index outside its
-- list, the fuel) cite the design or a decision. Never the encoding itself.

namespace Trust
namespace Model
namespace Sanity

def int (n : Int) : Value := Value.int n
def num (n : Int) : Expr := Expr.lit (Value.int n)
def tt : Expr := Expr.lit (Value.bool true)
def ff : Expr := Expr.lit (Value.bool false)
def setOf (vs : List Value) : Expr := Expr.lit (Value.set vs)
-- {FALSE, TRUE}, canonical (TLC orders FALSE first: BoolValue.compareTo).
def bools : Expr := setOf [Value.bool false, Value.bool true]
def empty : Expr := setOf []
-- CHOOSE z \in {} : TRUE: raises `chooseFailed` wherever it is evaluated.
def bad : Expr := Expr.quant QKind.qChoose [empty] tt

-- The spec of the facts: pool entries `Bad == CHOOSE z \in {} : TRUE` (0) and
-- `K == IF TRUE THEN 3 ELSE 4` (1); definitions `G(a) == 5` (0), `H(a, b) == IF a THEN b
-- ELSE 0` (1, parameter a is `bvar 1`, b is `bvar 0`, B1A-D15), `G2(a) == IF a THEN 1 ELSE 2`
-- (2). One variable; no actions.
def spC : Spec :=
  Spec.mk 1 IntMode.tlc32 [] [bad, Expr.ite tt (num 3) (num 4)]
    [(1, num 5), (2, Expr.ite (Expr.bvar 1) (Expr.bvar 0) (num 0)),
      (1, Expr.ite (Expr.bvar 0) (num 1) (num 2))]
    [] [] (Act.conj []) (Act.conj []) [] [] [] [] true ChoiceMode.none

-- ---- Reading results ----

-- The constructor of a Fail, in declaration order (10:93-100): chooseFailed 2, typeErr 4,
-- caseNoMatch 5, notEnumerable 7, unassignedPrime 11, fuel 12, unmodeled 13.
def failTag (f : Fail) : Nat :=
  @Fail.casesOn (fun _ => Nat) f 0 1 2 3 4 5 6 7 8 (fun _ => 9) 10 11 12 (fun _ => 13)

def errTag {α : Type} (r : Res α) (t : Nat) : Bool :=
  @Res.rec α (fun _ => Bool) (fun _ => false) (fun f => Nat.beq (failTag f) t) r

def isChooseFailed {α : Type} (r : Res α) : Bool := errTag r 2
def isTypeErr {α : Type} (r : Res α) : Bool := errTag r 4
def isCaseNoMatch {α : Type} (r : Res α) : Bool := errTag r 5
def isNotEnumerable {α : Type} (r : Res α) : Bool := errTag r 7
def isUnassignedPrime {α : Type} (r : Res α) : Bool := errTag r 11
def isFuel {α : Type} (r : Res α) : Bool := errTag r 12

def isUnmodeled {α : Type} (r : Res α) (code : Nat) : Bool :=
  @Res.rec α (fun _ => Bool) (fun _ => false)
    (fun f => @Fail.casesOn (fun _ => Bool) f false false false false false false false false
      false (fun _ => false) false false false (fun c => Nat.beq c code))
    r

def isOkWith {α : Type} (r : Res α) (p : α → Bool) : Bool :=
  @Res.rec α (fun _ => Bool) (fun a => p a) (fun _ => false) r

-- `okV r v`: r is the value v.
def okV (r : Res Value) (v : Value) : Bool := isOkWith r (fun a => Value.beq a v)

-- The constructor of an XVal: 0 val, 1 lazyFn, 2 fnX, 3 lazySet.
def xTag (x : XVal) : Nat := XVal.elim x (fun _ => 0) (fun _ _ _ => 1) (fun _ => 2) (fun _ => 3)

-- `ev e`: e at the design's fuel, keepLazy off, forced (`evalE`, 10:301-302), at the state
-- [0] with successor [0], no bound values.
def ev (e : Expr) : Res Value := evalE spC (Spec.fuel spC) [] [int 0] [int 0] e

-- `evX env s p e`: `evalX` itself at the design's fuel, keepLazy off.
def evX (env : List Value) (s : State) (p : Frame) (e : Expr) : Res XVal :=
  evalX spC (Spec.fuel spC) false env s p e

def gSet : SetGen := SetGen.ofVal (Value.set [int 1, int 2])

-- ---- Leaves (10:131-135) ----

-- A literal is its value; a slot reads the state; a bound variable reads env, innermost
-- first (B1A-D15). Design 10:131-134 (no TLA+ probe: these are the encoding's leaves).
theorem core_leaves :
    Bool.and (okV (ev (setOf [int 1, int 2])) (Value.set [int 1, int 2]))
    (Bool.and (isOkWith (evX [] [int 7, int 8] [] (Expr.cur 1))
      (fun x => isOkWith (force spC 1 [] x) (fun v => Value.beq v (int 8))))
      (isOkWith (evX [int 4, int 5] [] [] (Expr.bvar 1))
        (fun x => isOkWith (force spC 1 [] x) (fun v => Value.beq v (int 5))))) = true := rfl

-- A primed read of an assigned slot is its value AS BOUND, lazy or not (10:620: bound
-- unforced); of an unassigned slot, `unassignedPrime` (10:275, 10:97; TLC's text for it is
-- causes.tsv row 190, tlc-XeqReversed.txt:29).
theorem core_nxt :
    Bool.and (isOkWith (evX [] [int 0] [Option.some (XVal.val (int 9))] (Expr.nxt 0))
      (fun x => Nat.beq (xTag x) 0))
    (Bool.and (isOkWith (evX [] [int 0] [Option.some (XVal.lazySet gSet)] (Expr.nxt 0))
      (fun x => Nat.beq (xTag x) 3))
      (isUnassignedPrime (evX [] [int 0] [Option.none] (Expr.nxt 0)))) = true := rfl

-- An index outside its list is `Tlc.illFormed` = `Fail.fuel` (B1A-D95): a slot, a primed
-- slot, a bound variable, a pool entry, a definition; a call with the wrong number of
-- actuals; a CHOOSE or a filter with other than one binder.
theorem core_ill_formed :
    Bool.and (isFuel (evX [] [int 0] [Option.none] (Expr.cur 1)))
    (Bool.and (isFuel (evX [] [int 0] [Option.none] (Expr.nxt 1)))
    (Bool.and (isFuel (evX [int 4] [int 0] [Option.none] (Expr.bvar 1)))
    (Bool.and (isFuel (ev (Expr.pool 2)))
    (Bool.and (isFuel (ev (Expr.app 3 [])))
    (Bool.and (isFuel (ev (Expr.app 1 [tt])))
    (Bool.and (isFuel (ev (Expr.quant QKind.qChoose [bools, bools] tt)))
      (isFuel (ev (Expr.quant QKind.qFilter [] tt))))))))) = true := rfl

-- Spec.wf refuses a CHOOSE or a set filter with other than one binder (B1A-D95), so every
-- `Tlc.illFormed` case above is outside a well-formed Spec; \E keeps any positive number
-- (none is refused too, B1A-D95 amended by B1A-15, which states it in primops.lean's
-- `prim_ill_formed`); spC is well formed.
def spWith (inv : Expr) : Spec :=
  Spec.mk 1 IntMode.tlc32 [] [] [] [] [] (Act.conj []) (Act.conj []) [] [inv] [] [] true
    ChoiceMode.none
theorem core_wf_one_binder :
    Bool.and (Spec.wf spC)
    (Bool.and (Spec.wf (spWith (Expr.quant QKind.qChoose [bools] tt)))
    (Bool.and (Bool.not (Spec.wf (spWith (Expr.quant QKind.qChoose [bools, bools] tt))))
    (Bool.and (Bool.not (Spec.wf (spWith (Expr.quant QKind.qFilter [] tt))))
      (Spec.wf (spWith (Expr.quant QKind.qEx [bools, bools] tt)))))) = true := rfl

-- ---- Pool entries: evaluated at use (10:135) ----

-- [CorePoolValue] `K` is 3; [CorePoolUnused] an unread raising entry never raises;
-- [CorePoolUsed] a read one raises where it is read (chooseFailed, causes.tsv row 170).
theorem core_pool :
    Bool.and (okV (ev (Expr.pool 1)) (int 3))
    (Bool.and (okV (ev (Expr.ite tt (num 1) (Expr.pool 0))) (int 1))
      (isChooseFailed (ev (Expr.pool 0)))) = true := rfl

-- ---- IF and CASE ----

-- [CoreIfElse] IF FALSE THEN 1 ELSE 2 is 2; [cause-probes/CIfNonBool] a non-Boolean
-- condition is typeErr (causes.tsv row 150).
theorem core_ite :
    Bool.and (okV (ev (Expr.ite ff (num 1) (num 2))) (int 2))
      (isTypeErr (ev (Expr.ite (num 1) (num 2) (num 3)))) = true := rfl

-- [CoreCaseFirst] CASE TRUE -> 1 [] TRUE -> 2 is 1; [CoreCaseOther] CASE FALSE -> 1 []
-- OTHER -> 2 is 2; [CoreCaseLaterUnread] CASE TRUE -> 1 [] 3 -> 2 is 1 (no guard after the
-- first TRUE one is read).
theorem core_case :
    Bool.and (okV (ev (Expr.caseOf [(tt, num 1), (tt, num 2)] Option.none)) (int 1))
    (Bool.and (okV (ev (Expr.caseOf [(ff, num 1)] (Option.some (num 2)))) (int 2))
      (okV (ev (Expr.caseOf [(tt, num 1), (num 3, num 2)] Option.none)) (int 1))) = true := rfl

-- [CoreCaseGuardOrder] CASE FALSE -> 1 [] 3 -> 2 [] TRUE -> 4 raises typeErr at the second
-- guard before the TRUE third; [CoreCaseNoMatch] CASE FALSE -> 1 [] FALSE -> 2 is
-- caseNoMatch.
theorem core_case_errors :
    Bool.and (isTypeErr (ev (Expr.caseOf [(ff, num 1), (num 3, num 2), (tt, num 4)] Option.none)))
      (isCaseNoMatch (ev (Expr.caseOf [(ff, num 1), (ff, num 2)] Option.none))) = true := rfl

-- ---- LET and operator application: by substitution (10:168, 10:276-277) ----

-- [CoreLetUnused] LET y == CHOOSE z \in {} : TRUE IN 5 is 5; [CoreLetUsed] LET y == TRUE IN
-- IF y THEN 1 ELSE 2 is 1; [CoreLetUsedRaises] reading the raising definition raises
-- chooseFailed.
theorem core_let :
    Bool.and (okV (ev (Expr.letLazy bad (num 5))) (int 5))
    (Bool.and (okV (ev (Expr.letLazy tt (Expr.ite (Expr.bvar 0) (num 1) (num 2)))) (int 1))
      (isChooseFailed (ev (Expr.letLazy bad (Expr.ite (Expr.bvar 0) (num 1) (num 2))))))
      = true := rfl

-- [CoreLetCapture] \E x \in {TRUE} : LET y == x IN \A z \in {FALSE} : y is TRUE: the
-- definition's bound variable is shifted under the \A binder it crosses (10:168: capture-
-- avoiding), so y still reads x, not z.
theorem core_let_capture :
    okV (ev (Expr.quant QKind.qEx [setOf [Value.bool true]]
      (Expr.letLazy (Expr.bvar 0)
        (Expr.quant QKind.qAll [setOf [Value.bool false]] (Expr.bvar 1)))))
      (Value.bool true) = true := rfl

-- [CoreAppByName] G(CHOOSE z \in {} : TRUE) is 5 with G(a) == 5 (an unread actual is never
-- evaluated); [CoreAppOrder] H(TRUE, 7) is 7 with H(a, b) == IF a THEN b ELSE 0;
-- [CoreAppRaises] G2(CHOOSE z \in {} : TRUE) raises chooseFailed with G2(a) == IF a THEN 1
-- ELSE 2.
theorem core_app :
    Bool.and (okV (ev (Expr.app 0 [bad])) (int 5))
    (Bool.and (okV (ev (Expr.app 1 [tt, num 7])) (int 7))
      (isChooseFailed (ev (Expr.app 2 [bad])))) = true := rfl

-- ---- Quantifiers over val sets (10:142; ContextEnumerator) ----

-- [CoreExTrue] \E x \in {FALSE, TRUE} : x is TRUE; [CoreExEmpty] \E x \in {} : TRUE is
-- FALSE; [CoreAllFalse] \A x \in {FALSE, TRUE} : x is FALSE; [CoreAllEmpty]
-- \A x \in {} : FALSE is TRUE.
theorem core_ex_all :
    Bool.and (okV (ev (Expr.quant QKind.qEx [bools] (Expr.bvar 0))) (Value.bool true))
    (Bool.and (okV (ev (Expr.quant QKind.qEx [empty] tt)) (Value.bool false))
    (Bool.and (okV (ev (Expr.quant QKind.qAll [bools] (Expr.bvar 0))) (Value.bool false))
      (okV (ev (Expr.quant QKind.qAll [empty] ff)) (Value.bool true)))) = true := rfl

-- [CoreExOrder] \E x \in {FALSE, TRUE}, y \in {FALSE, TRUE} : IF y THEN 1 ELSE x is TRUE,
-- and [CoreAllOrder] \A x, y \in ... : IF y THEN 1 ELSE ~x is FALSE: one context loop, the
-- FIRST binder fastest, so (x = TRUE, y = FALSE) is reached before (x = FALSE, y = TRUE),
-- whose body would raise. (x is `bvar 1`, y `bvar 0`.)
theorem core_context_order :
    Bool.and
      (okV (ev (Expr.quant QKind.qEx [bools, bools] (Expr.ite (Expr.bvar 0) (num 1) (Expr.bvar 1))))
        (Value.bool true))
      (okV (ev (Expr.quant QKind.qAll [bools, bools]
          (Expr.ite (Expr.bvar 0) (num 1) (Expr.ite (Expr.bvar 1) ff tt))))
        (Value.bool false)) = true := rfl

-- [CoreExDomainsFirst] \E x \in {}, y \in 3 : TRUE raises notEnumerable: every domain is
-- evaluated and converted before any body runs, even after an empty one.
theorem core_domains_first :
    isNotEnumerable (ev (Expr.quant QKind.qEx [empty, num 3] tt)) = true := rfl

-- A domain that is not a set is notEnumerable: [CoreExBoundNonSet] \E x \in 3,
-- [CoreExBoundNat] \E x \in Nat, [CoreChooseBoundNonSet] CHOOSE x \in 3,
-- [CoreMapBoundNonSet] {1 : x \in 3}.
theorem core_bound_not_a_set :
    Bool.and (isNotEnumerable (ev (Expr.quant QKind.qEx [num 3] tt)))
    (Bool.and (isNotEnumerable (ev (Expr.quant QKind.qEx [Expr.lit (Value.infSet InfKind.nat [])] tt)))
    (Bool.and (isNotEnumerable (ev (Expr.quant QKind.qChoose [num 3] tt)))
      (isNotEnumerable (ev (Expr.quant QKind.qMap [num 3] (num 1)))))) = true := rfl

-- A body that is not a forced Boolean is typeErr: [CoreExBodyNonBool] \E x \in {1} : x,
-- [CoreAllBodyNonBool] \A x \in {1} : x, [CoreChooseBodyNonBool] CHOOSE x \in {1} : x,
-- [CoreFilterNonBool] {x \in {1, 2} : x}.
theorem core_body_not_boolean :
    Bool.and (isTypeErr (ev (Expr.quant QKind.qEx [setOf [int 1]] (Expr.bvar 0))))
    (Bool.and (isTypeErr (ev (Expr.quant QKind.qAll [setOf [int 1]] (Expr.bvar 0))))
    (Bool.and (isTypeErr (ev (Expr.quant QKind.qChoose [setOf [int 1]] (Expr.bvar 0))))
      (isTypeErr (ev (Expr.quant QKind.qFilter [setOf [int 1, int 2]] (Expr.bvar 0))))))
      = true := rfl

-- ---- CHOOSE: the first element in TLC's normalized order ----

-- [CoreChooseFirst] CHOOSE x \in {3, 1, 2} : TRUE is 1 (the literal is canonical: 1, 2, 3);
-- [CoreChooseSkip] CHOOSE x \in {FALSE, TRUE} : x is TRUE; [CoreChooseNone]
-- CHOOSE x \in {FALSE} : x raises chooseFailed.
theorem core_choose :
    Bool.and (okV (ev (Expr.quant QKind.qChoose [setOf [int 1, int 2, int 3]] tt)) (int 1))
    (Bool.and (okV (ev (Expr.quant QKind.qChoose [bools] (Expr.bvar 0))) (Value.bool true))
      (isChooseFailed (ev (Expr.quant QKind.qChoose [setOf [Value.bool false]] (Expr.bvar 0)))))
      = true := rfl

-- ---- Set filter and set-of-all ----

-- [CoreFilter] {x \in {FALSE, TRUE} : x} is {TRUE}: eager over a Reducible base (10:628).
-- [CoreFilterBoundNonSet] {x \in 3 : TRUE}: TLC builds it lazily (its error comes when the
-- set is enumerated), so it is not eager here either: a lazy filter is B1A-17a's, todo
-- until then (this fact changes with that row).
theorem core_filter :
    Bool.and (okV (ev (Expr.quant QKind.qFilter [bools] (Expr.bvar 0)))
      (Value.set [Value.bool true]))
      (isUnmodeled (ev (Expr.quant QKind.qFilter [num 3] tt)) Code.todo) = true := rfl

-- [CoreMap] {IF x THEN 1 ELSE 2 : x \in {FALSE, TRUE}} is {1, 2}; [CoreMapDup] {IF x THEN 1
-- ELSE 1 : x \in {FALSE, TRUE}} is {1}; [CoreMapTwo] {IF x THEN y ELSE 0 : x \in {FALSE,
-- TRUE}, y \in {1, 2}} is {0, 1, 2}.
theorem core_map :
    Bool.and (okV (ev (Expr.quant QKind.qMap [bools] (Expr.ite (Expr.bvar 0) (num 1) (num 2))))
      (Value.set [int 1, int 2]))
    (Bool.and (okV (ev (Expr.quant QKind.qMap [bools] (Expr.ite (Expr.bvar 0) (num 1) (num 1))))
      (Value.set [int 1]))
      (okV (ev (Expr.quant QKind.qMap [bools, setOf [int 1, int 2]]
          (Expr.ite (Expr.bvar 1) (Expr.bvar 0) (num 0))))
        (Value.set [int 0, int 1, int 2]))) = true := rfl

-- A set-of-all element that is not a forced value is `unmodeled lazy.soa-elem` (10:629):
-- here the body reads a primed slot bound to a lazy set.
theorem core_map_lazy_element :
    isUnmodeled (evX [] [int 0] [Option.some (XVal.lazySet gSet)]
      (Expr.quant QKind.qMap [bools] (Expr.nxt 0))) Code.lazySoaElem = true := rfl

-- ---- Not yet filled (their rows change these facts) ----

-- A lazy set constructor (SUBSET, B1A-17a) and ENABLED (B1A-19) are still `Tlc.todo`;
-- B1A-15 filled `op` (sanity primops.lean), so this fact's first door now reads SUBSET
-- instead of `value.eq`; B1A-16 filled `[x \in S |-> e]`, so its qFn door now reads the
-- materialized function (sanity lazy_fn.lean `lazy_ctor` has the constructor facts).
theorem core_pending :
    Bool.and (isUnmodeled (ev (Expr.op PrimOp.setPowerset [bools])) Code.todo)
    (Bool.and (okV (ev (Expr.quant QKind.qFn [bools] (Expr.bvar 0)))
        (Value.fn [(Value.bool false, Value.bool false), (Value.bool true, Value.bool true)]))
      (isUnmodeled (ev (Expr.enabled (Act.conj []))) Code.todo)) = true := rfl

-- ---- Frame.ofState, evalE and fuel (10:299-302, B1A-D07) ----

-- `Frame.ofState t` assigns every slot, forced: a primed read under `evalE` reads the
-- successor t (pair mode); `evalE` forces what `evalX` returns.
theorem core_evalE :
    Bool.and (okV (evalE spC (Spec.fuel spC) [] [int 0, int 0] [int 7, int 8] (Expr.nxt 1)) (int 8))
    (Bool.and (Nat.beq (List.length (Frame.ofState [int 1, int 2])) 2)
      (@Option.casesOn (Option XVal) (fun _ => Bool) (Tlc.nth (Frame.ofState [int 1, int 2]) 1)
        false
        (fun o => @Option.casesOn XVal (fun _ => Bool) o false (fun x => Nat.beq (xTag x) 0))))
      = true := rfl

-- Each recursive evaluation costs one unit of fuel (B1A-D07: per nesting depth, not per
-- element): IF TRUE THEN 1 ELSE 2 needs fuel 2; at fuel 1 its arm's evaluation answers
-- `Fail.fuel` (10:98); \E over three elements needs only fuel 2 as well.
theorem core_fuel :
    Bool.and (isFuel (evalX spC 1 false [] [int 0] [] (Expr.ite tt (num 1) (num 2))))
    (Bool.and (isOkWith (evalX spC 2 false [] [int 0] [] (Expr.ite tt (num 1) (num 2)))
      (fun x => Nat.beq (xTag x) 0))
      (isOkWith (evalX spC 2 false [] [int 0] []
          (Expr.quant QKind.qEx [setOf [int 1, int 2, int 3]] ff))
        (fun x => Nat.beq (xTag x) 0))) = true := rfl

end Sanity
end Model
end Trust
