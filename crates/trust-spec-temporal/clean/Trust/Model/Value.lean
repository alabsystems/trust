-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- Trust.Model.Value: the executable presentation's values (Beyond-TLA design
-- 10-executable-semantics.md, "Values", 10:67-119). Clean source, served to ty by
-- crates/trust-model-prelude and kernel-checked by crates/trust-spec-temporal.
--
-- This revision (lane row B1A-10) holds the value core: InfKind, Value, IntMode, Fail,
-- Res and State verbatim from 10:71-107 (names and constructor order are the design's;
-- the statement pins of B1A-26a/26b enforce it), Res's plain combinators (B1A-D09: no
-- Monad instance), the `Fail.unmodeled` code table (B1A-D13), TLC's 32-bit integer
-- arithmetic (B1A-D08) and `epVersion`. Row B1A-11a adds TLC's order (`tlcCmp`, `tlcLt`)
-- and the structural `Value.beq` (B1A-D86); row B1A-11b adds TLC's `=` (`valueEq`,
-- B1A-D14, B1A-D87) and the canonical forms (`Value.Canon`, `normSet`, the builders).
-- Row B1A-14a (the M0 review's findings 4, 5 and 14) pins the untyped model value's order,
-- refuses an infSet receiver against a typed model value, and refuses two function keys of
-- different kinds.
--
-- Cost discipline (TASK-STATE 4.8, FiniteModelCheck.lean:94-130): control is raw
-- recursors (`Int.casesOn`, `Bool.rec`, `Res.rec`, `List.rec`, `Nat.rec`), never
-- `match`, `if` or `&&`; a recursor's motive is explicit.

namespace Trust
namespace Model

-- Sets TLC can test but cannot enumerate (10:75-76).
inductive InfKind where
  | nat | int | string | seqOf | fnSet

-- The presentation's values (10:78-86), nested through List and Prod: `Value.casesOn`
-- and `Value.rec` take four motives (Value, List Value, List (Value × Value),
-- Value × Value) and then every constructor's minor (B1A-02a, B1A-D70).
inductive Value where
  | bool   : Bool → Value
  | int    : Int → Value
  | str    : Nat → Value
  | mv     : Nat → Value
  | tmv    : Nat → Nat → Value
  | set    : List Value → Value
  | fn     : List (Value × Value) → Value
  | infSet : InfKind → List Value → Value

-- `tlc32`: a result outside [-2^31, 2^31) raises `overflow`, except an operand pair TLC
-- wraps, which is `unmodeled`. `unbounded`: Clean's Int, not TLC-exact (10:88-91).
inductive IntMode where
  | tlc32
  | unbounded

-- TLC's error classes, plus two results that are never a verdict: `fuel` (a resource
-- result) and `unmodeled` (a named refusal whose code is in the `Code` table below)
-- (10:93-100).
inductive Fail where
  | overflow | notInDomain | chooseFailed | divZero | typeErr | caseNoMatch
  | notCompletelySpecified | notEnumerable | assumeFalse | assertFailed (msg : Nat)
  | incomparable
  | unassignedPrime
  | fuel
  | unmodeled (code : Nat)

-- The local result type (10:102-104); no dependence on the prelude's Except.
inductive Res (α : Type) where
  | ok    : α → Res α
  | error : Fail → Res α

-- One Value per slot (10:106).
abbrev State := List Value

-- ---- Res combinators: plain definitions, no Monad instance (B1A-D09) ----

-- `Res.bind r f`: `f` on the value of `r`; an error passes through unchanged.
def Res.bind {α β : Type} (r : Res α) (f : α → Res β) : Res β :=
  @Res.rec α (fun _ => Res β) f (fun e => Res.error e) r

-- `Res.map f r`: `f` applied to the value of `r`; an error passes through unchanged.
def Res.map {α β : Type} (f : α → β) (r : Res α) : Res β :=
  @Res.rec α (fun _ => Res β) (fun a => Res.ok (f a)) (fun e => Res.error e) r

-- `Res.concat rs` (10:327, `def-res-concat`): the result lists appended in source
-- order; the first error in source order wins (TLC's error order), so nothing after an
-- erroring element is read.
def Res.concat {α : Type} (rs : List (Res (List α))) : Res (List α) :=
  @List.rec (Res (List α)) (fun _ => Res (List α))
    (Res.ok [])
    (fun head _ rest =>
      @Res.rec (List α) (fun _ => Res (List α))
        (fun xs =>
          @Res.rec (List α) (fun _ => Res (List α))
            (fun ys => Res.ok (List.append xs ys))
            (fun e => Res.error e)
            rest)
        (fun e => Res.error e)
        head)
    rs

-- ---- The `Fail.unmodeled` code table (B1A-D13) ----
--
-- Codes come only from the design: the 10:109 codes (B1A-D13), `int.<op>-wrap` for a
-- further operand pair TLC is found to wrap (none on the TLC of record 94d0c50,
-- DR-B1A-D26 (5)), and `cmp.unpinned` (B1A-D14; added by B1A-11a for `tlcCmp`'s
-- unpinned cross-kind orders, B1A-D86). The `lazy.<op>`
-- family of 10:109 gets one code per operator when a forcing row needs it (B1A-D22,
-- B1A-17b). `todo` is the development placeholder; it is deleted by B1A-25.
-- trust-model-prelude's UNMODELED_CODES mirrors this table line by line: every line
-- `def Code.<name> : Nat := <n>  -- <code> <registry refusal>` (B1A-10's unit test
-- parses exactly this form and fails on any other `def Code.` line).
def Code.intDivWrap : Nat := 0  -- int.div-wrap model.int-div-wrap
def Code.lazyArg : Nat := 1  -- lazy.arg model.lazy-unpinned
def Code.lazyExcept : Nat := 2  -- lazy.except model.lazy-unpinned
def Code.lazyRefusedForce : Nat := 3  -- lazy.refused-force model.lazy-unpinned
def Code.lazyMemKind : Nat := 4  -- lazy.mem-kind model.lazy-unpinned
def Code.lazySoaElem : Nat := 5  -- lazy.soa-elem model.lazy-unpinned
def Code.lazyEnabledAssign : Nat := 6  -- lazy.enabled-assign model.lazy-unpinned
def Code.cmpUnpinned : Nat := 7  -- cmp.unpinned model.cmp-unpinned
def Code.todo : Nat := 999  -- todo -

-- ---- TLC's integers (B1A-D08) ----
--
-- Hand-written over Nat.div / Nat.mod and the sign cases of `Int` (`ofNat n` is n,
-- `negSucc n` is -(n+1)): Clean's Int division truncates and is stuck on negative
-- operands at trust's pin. Every class below is the one TLC raised on the batch-B
-- probes of PR-int-probes (ty reports/perf/2026-10-09-beyond-tla-b1a/probes,
-- INDEX.tsv; DR-B1A-D26 (5), DR-B1A-D30).

-- `intBeq a b`: integer equality as a Bool.
def intBeq (a b : Int) : Bool :=
  @Int.casesOn (fun _ => Bool) a
    (fun n => @Int.casesOn (fun _ => Bool) b (fun m => Nat.beq n m) (fun _ => false))
    (fun n => @Int.casesOn (fun _ => Bool) b (fun _ => false) (fun m => Nat.beq n m))

-- `natAbs a`: |a|.
def natAbs (a : Int) : Nat :=
  @Int.casesOn (fun _ => Nat) a (fun n => n) (fun n => Nat.succ n)

-- `isNeg a`: a < 0.
def isNeg (a : Int) : Bool :=
  @Int.casesOn (fun _ => Bool) a (fun _ => false) (fun _ => true)

-- `inRange32 a`: -2^31 <= a < 2^31, TLC's int range (Java int). Also the range of an
-- integer literal under `tlc32` (`model.int-literal-range`, design 10:678).
def inRange32 (a : Int) : Bool :=
  @Int.casesOn (fun _ => Bool) a
    (fun n => Nat.blt n 2147483648)
    (fun n => Nat.blt n 2147483648)

-- `IntMode.check m a`: under `tlc32`, `a` if it is in range, else `overflow`; under
-- `unbounded`, `a`.
def IntMode.check (m : IntMode) (a : Int) : Res Int :=
  @IntMode.casesOn (fun _ => Res Int) m
    (@Bool.rec (fun _ => Res Int) (Res.error Fail.overflow) (Res.ok a) (inRange32 a))
    (Res.ok a)

-- `a + b`, `a - b`, `a * b`, `-a`: the mathematical result, then the mode's range check
-- (TLC raises `Overflow when computing`; IntAddMax, IntSubMin, IntMulPosOverflow,
-- IntMulMinNegOne, IntNegMin and their in-range controls).
def intAdd (m : IntMode) (a b : Int) : Res Int := IntMode.check m (a + b)
def intSub (m : IntMode) (a b : Int) : Res Int := IntMode.check m (a - b)
def intMul (m : IntMode) (a b : Int) : Res Int := IntMode.check m (a * b)
def intNeg (m : IntMode) (a : Int) : Res Int := IntMode.check m (Int.neg a)

-- `floorDiv a b`: floor(a / b) for b ≠ 0 (TLC's `\div`), by the four sign cases;
-- `floorDiv a 0` is 0 or -1 and is never read (`intDiv` checks the divisor first).
--   a = n >= 0,  b = m > 0:       n / m
--   a = n >= 0,  b = -(m+1) < 0:  -ceil(n / (m+1)) = -((n + m) / (m+1))
--   a = -(n+1),  b = m > 0:       -ceil((n+1) / m) = -(n / m) - 1
--   a = -(n+1),  b = -(m+1):      (n+1) / (m+1)
def floorDiv (a b : Int) : Int :=
  @Int.casesOn (fun _ => Int) a
    (fun n => @Int.casesOn (fun _ => Int) b
      (fun m => Int.ofNat (Nat.div n m))
      (fun m => Int.neg (Int.ofNat (Nat.div (Nat.add n m) (Nat.succ m)))))
    (fun n => @Int.casesOn (fun _ => Int) b
      (fun m => Int.negSucc (Nat.div n m))
      (fun m => Int.ofNat (Nat.div (Nat.succ n) (Nat.succ m))))

-- `floorMod a m`: a mod m in 0..m-1 for m > 0 (TLC's `%`): for a = -(n+1) it is
-- m - 1 - (n mod m).
def floorMod (a : Int) (m : Nat) : Int :=
  @Int.casesOn (fun _ => Int) a
    (fun n => Int.ofNat (Nat.mod n m))
    (fun n => Int.ofNat (Nat.sub (Nat.sub m 1) (Nat.mod n m)))

-- `isIntMinByNegOne a b`: a = -2^31 and b = -1, the one `\div` pair W1 recorded TLC
-- wrapping (TLC 9787e65) where TLC 94d0c50 raises overflow (IntDivMinNegOne).
def isIntMinByNegOne (a b : Int) : Bool :=
  @Int.casesOn (fun _ => Bool) a
    (fun _ => false)
    (fun n => Bool.and (Nat.beq n 2147483647)
      (@Int.casesOn (fun _ => Bool) b (fun _ => false) (fun k => Nat.beq k 0)))

-- `a \div b`: `divZero` for b = 0 (IntDivZero); under `tlc32`, the pair (-2^31, -1) is
-- `unmodeled int.div-wrap` (design 10:678; the two TLC revisions disagree, DR-B1A-D26
-- (5)), and any other result goes through the range check; floor semantics
-- (IntDivNegPos, IntDivPosNeg, IntDivNegNeg, IntDivMin*).
def intDiv (m : IntMode) (a b : Int) : Res Int :=
  @Bool.rec (fun _ => Res Int)
    (@IntMode.casesOn (fun _ => Res Int) m
      (@Bool.rec (fun _ => Res Int)
        (IntMode.check m (floorDiv a b))
        (Res.error (Fail.unmodeled Code.intDivWrap))
        (isIntMinByNegOne a b))
      (Res.ok (floorDiv a b)))
    (Res.error Fail.divZero)
    (intBeq b 0)

-- `a % b`: `divZero` for b <= 0 (TLC: "The second argument of % should be a positive
-- number", IntModZeroDivisor, IntModNegDivisor, IntModMinNegTwo, IntModMinNegOne;
-- ops.rs int.mod "b <= 0 is an error"), else the result in 0..b-1 (IntModNeg,
-- IntModMin*), always in range.
def intMod (m : IntMode) (a b : Int) : Res Int :=
  @Int.casesOn (fun _ => Res Int) b
    (fun k => @Bool.rec (fun _ => Res Int)
      (IntMode.check m (floorMod a k))
      (Res.error Fail.divZero)
      (Nat.beq k 0))
    (fun _ => Res.error Fail.divZero)

-- `powNat a e`: a^e by e multiplications.
def powNat (a : Int) (e : Nat) : Int :=
  @Nat.rec (fun _ => Int) 1 (fun _ acc => acc * a) e

-- `a ^ b`: `typeErr` for b < 0 (TLC: "The second argument of ^ should be a natural
-- number", IntPowNegExp); 0^0 is `typeErr` too (TLC: "0^0 is undefined.", probe
-- primop-probes/PIntPowZeroZero, cause row 153: an argument pair outside the domain of ^,
-- the module-argument class of IntPowNegExp; B1A-D85, resolved by B1A-15); a^0 = 1 otherwise. For
-- b >= 1: 0, 1 and -1 never leave the range and are computed without a loop; for
-- |a| >= 2 under `tlc32`, b >= 32 gives |a^b| >= 2^32, so `overflow` (IntPowOverflow),
-- and b <= 31 is computed and range-checked; under `unbounded`, a^b exactly. TLC checks
-- the range after every multiplication; |a^k| grows with k for |a| >= 2, so checking
-- the final value gives the same class.
def intPow (m : IntMode) (a b : Int) : Res Int :=
  @Int.casesOn (fun _ => Res Int) b
    (fun e => @Bool.rec (fun _ => Res Int)
      (@Bool.rec (fun _ => Res Int)
        (@IntMode.casesOn (fun _ => Res Int) m
          (@Bool.rec (fun _ => Res Int)
            (Res.error Fail.overflow)
            (IntMode.check m (powNat a e))
            (Nat.blt e 32))
          (Res.ok (powNat a e)))
        (Res.ok (@Bool.rec (fun _ => Int) a 1
          (Bool.and (isNeg a) (Nat.beq (Nat.mod e 2) 0))))
        (Nat.ble (natAbs a) 1))
      (@Bool.rec (fun _ => Res Int)
        (Res.ok 1)
        (Res.error Fail.typeErr)
        (intBeq a 0))
      (Nat.beq e 0))
    (fun _ => Res.error Fail.typeErr)

-- ---- TLC's order: tlcCmp, tlcLt and the structural Value.beq (B1A-11a, B1A-D86) ----
--
-- `tlcCmp a b` is TLC's `a.compareTo(b)` on canonical values (design 10:111,
-- `def-tlclt`; TLC 94d0c50's `compareTo` of BoolValue, IntValue, StringValue,
-- ModelValue, SetEnumValue, FcnRcdValue, TupleValue and RecordValue): `Res.ok 0` when a
-- comes first, `Res.ok 1` when they are equal, `Res.ok 2` when b comes first.
--   bool:   false before true.
--   int:    numerically.
--   str:    by token rank (UniqueString order: ChooseOrderStr).
--   mv:     untyped model values by token rank (ModelValueMvSetOrder); an untyped model value
--           comes BEFORE every value that is not a model value, in either order (TLC 94d0c50's
--           ModelValue.compareTo answers -1 for an untyped receiver and a non-model argument,
--           and every other kind's compareTo hands a model-value argument to
--           `modelValueCompareTo`, which answers 1 for an untyped one; the lane record's
--           m0-review-probes/ Mv{Int,Str,Bool,Set,Tup,Rcd,Fcn,Nat,IntSet,String,Seq}{A,B}: CHOOSE
--           takes the model value whichever literal comes first); and an untyped against a typed
--           model value goes by token rank in either order (ModelValue.compareTo accepts an
--           untyped operand; MvTmvA/B, TmvMvA/B, where whichever was minted first is taken).
--   tmv:    same type tag by rank (ModelValueTmvSameType); another tag, or any value that
--           is not a model value, raises `incomparable` in either order (design 10:116; TLC
--           94d0c50's ModelValue.compareTo and modelValueCompareTo raise "Attempted to
--           compare the differently-typed model values" / "the typed model value ... and
--           (the) non-model value" there: TmvTmvDiff, TmvIntA, TmvIntB, TmvNatB, cause rows
--           201 and 202). The probes ModelValueTmvDiffType, -TmvVsInt, -IntVsTmv, -StrVsTmv
--           and -TmvVsStr exercise `=`: they are the equality analogue (`valueEq`).
--           One exception, refused: an infSet receiver of kind nat, int, string or seqOf (a
--           TLC UserValue) against a typed model value: UserValue.compareTo answers 1 without
--           raising (TmvNatA) where design 10:116 says `incomparable`, so that pair is the
--           named refusal until the design owner rules, as its equality analogue is
--           (K2-REQUESTS-B1A.md R1 item 7; M0 review finding 4).
--   set:    cardinality first, then element by element in canonical order.
--   fn:     a record (a non-empty function whose keys are all strings) against a function
--           that is not one (a non-empty one with a non-string key: a tuple, a sequence,
--           an integer-domain function; or the empty function) is the named refusal
--           `unmodeled cmp.unpinned` in either order (B1A-D86 as corrected): at 94d0c50
--           RecordValue.compareTo raises when the other operand has no record form
--           (`toRcd` null: a non-empty TupleValue, any interval-domain FcnRcdValue, the
--           empty one included, a FcnRcdValue with a non-string key), while TupleValue's
--           and FcnRcdValue's compareTo order the same pair by size, so TLC's outcome
--           depends on which operand holds the record (the lane record's order-probes/:
--           RecTupA/B, RecFcnC/D, RecEmpIntvA/B). `<<>>` and
--           `[x \in {} |-> e]` have a record form and `[i \in 1..0 |-> e]` has none
--           (RecEmpTupA/B, RecEmpDomA/B ordered, RecEmpIntvB raises), but all three are
--           `fn []`, so the empty function against a record refuses too. Any other two
--           functions: domain size first, then the keys in canonical order, then the
--           values (FcnRcdValue's, TupleValue's and RecordValue's common rule there). Two
--           keys of different kinds are the named refusal (M0 review finding 5): TLC compares
--           an interval-domain function's keys as integers ("Attempted to compare integer
--           with non-integer", the RecTupSameA text, a class no probe pins) and a
--           list-domain function's keys with compareTo, so the outcome depends on how TLC
--           holds the domain (the order analogue of `valueEq`'s `keyEqWith`).
--   infSet: against an untyped model value, after it for kinds nat, int, string and seqOf
--           (UserValue.compareTo; MvNatA/B, MvIntSetA/B, MvStringA/B, MvSeqA/B); fnSet
--           (SetOfFcnsValue) converts and enumerates itself first, so it refuses; against a
--           typed model value, refused (above); against anything else, refused.
-- Every other pair is a cross-kind order that neither a probe nor the design pins, so it
-- is the named refusal `unmodeled cmp.unpinned` (B1A-D14): two different kinds neither of
-- which is a model value (TLC raises an unpinned class). The first error in comparison
-- order wins, as in TLC, and nothing after it is compared.
--
-- All three are fuel-by-size through `Nat.rec` (B1A-D86): every recursive call compares
-- a proper part of the left operand, so `Nat.succ (Value.size a)` never runs out, and
-- `Fail.fuel` (for `tlcCmpF`) and `false` (for `Value.beqF`) are reached only with a
-- smaller explicit fuel.

-- `natCmp a b`: 0, 1 or 2 as a < b, a = b, a > b.
def natCmp (a b : Nat) : Nat :=
  @Bool.rec (fun _ => Nat) (@Bool.rec (fun _ => Nat) 2 1 (Nat.beq a b)) 0 (Nat.blt a b)

-- `intCmp a b`: numeric order, by the sign cases (`negSucc n` is -(n+1)).
def intCmp (a b : Int) : Nat :=
  @Int.casesOn (fun _ => Nat) a
    (fun n => @Int.casesOn (fun _ => Nat) b (fun m => natCmp n m) (fun _ => 2))
    (fun n => @Int.casesOn (fun _ => Nat) b (fun _ => 0) (fun m => natCmp m n))

-- `boolCmp a b`: false before true.
def boolCmp (a b : Bool) : Nat :=
  @Bool.rec (fun _ => Nat)
    (@Bool.rec (fun _ => Nat) 1 0 b)
    (@Bool.rec (fun _ => Nat) 2 1 b)
    a

-- `boolBeq a b`: a = b.
def boolBeq (a b : Bool) : Bool :=
  @Bool.rec (fun _ => Bool) (@Bool.rec (fun _ => Bool) true false b) b a

-- `InfKind.tag k`: the constructor index of k.
def InfKind.tag (k : InfKind) : Nat :=
  @InfKind.casesOn (fun _ => Nat) k 0 1 2 3 4

-- `Value.size v`: one per constructor, plus the sizes of the parts (structural, by
-- `Value.rec`: motives Value, List Value, List (Value × Value), Value × Value).
def Value.size (v : Value) : Nat :=
  @Value.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 1)
    (fun _ s => Nat.succ s)
    (fun _ s => Nat.succ s)
    (fun _ _ s => Nat.succ s)
    0 (fun _ _ sx sxs => Nat.add sx sxs)
    0 (fun _ _ sp sps => Nat.add sp sps)
    (fun _ _ sa sb => Nat.add sa sb)
    v

-- `Value.elim v ...`: one-type dispatch on v (the three auxiliary motives are unused).
def Value.elim {α : Type} (v : Value) (bool : Bool → α) (int : Int → α) (str : Nat → α)
    (mv : Nat → α) (tmv : Nat → Nat → α) (set : List Value → α)
    (fn : List (Prod Value Value) → α) (infSet : InfKind → List Value → α) : α :=
  @Value.casesOn (fun _ => α) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) v
    bool int str mv tmv set fn infSet
    0 (fun _ _ => 0) 0 (fun _ _ => 0) (fun _ _ => 0)

-- The fields of v when it is of one constructor, else `none`.
def Value.asBool (v : Value) : Option Bool :=
  @Value.elim (Option Bool) v (fun x => Option.some x) (fun _ => Option.none)
    (fun _ => Option.none) (fun _ => Option.none) (fun _ _ => Option.none)
    (fun _ => Option.none) (fun _ => Option.none) (fun _ _ => Option.none)
def Value.asInt (v : Value) : Option Int :=
  @Value.elim (Option Int) v (fun _ => Option.none) (fun x => Option.some x)
    (fun _ => Option.none) (fun _ => Option.none) (fun _ _ => Option.none)
    (fun _ => Option.none) (fun _ => Option.none) (fun _ _ => Option.none)
def Value.asStr (v : Value) : Option Nat :=
  @Value.elim (Option Nat) v (fun _ => Option.none) (fun _ => Option.none)
    (fun r => Option.some r) (fun _ => Option.none) (fun _ _ => Option.none)
    (fun _ => Option.none) (fun _ => Option.none) (fun _ _ => Option.none)
def Value.asMv (v : Value) : Option Nat :=
  @Value.elim (Option Nat) v (fun _ => Option.none) (fun _ => Option.none)
    (fun _ => Option.none) (fun r => Option.some r) (fun _ _ => Option.none)
    (fun _ => Option.none) (fun _ => Option.none) (fun _ _ => Option.none)
def Value.asTmv (v : Value) : Option (Prod Nat Nat) :=
  @Value.elim (Option (Prod Nat Nat)) v (fun _ => Option.none) (fun _ => Option.none)
    (fun _ => Option.none) (fun _ => Option.none) (fun t r => Option.some (Prod.mk t r))
    (fun _ => Option.none) (fun _ => Option.none) (fun _ _ => Option.none)
def Value.asSet (v : Value) : Option (List Value) :=
  @Value.elim (Option (List Value)) v (fun _ => Option.none) (fun _ => Option.none)
    (fun _ => Option.none) (fun _ => Option.none) (fun _ _ => Option.none)
    (fun xs => Option.some xs) (fun _ => Option.none) (fun _ _ => Option.none)
def Value.asFn (v : Value) : Option (List (Prod Value Value)) :=
  @Value.elim (Option (List (Prod Value Value))) v (fun _ => Option.none)
    (fun _ => Option.none) (fun _ => Option.none) (fun _ => Option.none)
    (fun _ _ => Option.none) (fun _ => Option.none) (fun ps => Option.some ps)
    (fun _ _ => Option.none)
def Value.asInfSet (v : Value) : Option (Prod InfKind (List Value)) :=
  @Value.elim (Option (Prod InfKind (List Value))) v (fun _ => Option.none)
    (fun _ => Option.none) (fun _ => Option.none) (fun _ => Option.none)
    (fun _ _ => Option.none) (fun _ => Option.none) (fun _ => Option.none)
    (fun k xs => Option.some (Prod.mk k xs))

-- `Value.isTmv v`: v is a typed model value.
def Value.isTmv (v : Value) : Bool :=
  @Option.casesOn (Prod Nat Nat) (fun _ => Bool) (Value.asTmv v) false (fun _ => true)

-- `Value.isStr v`: v is a string.
def Value.isStr (v : Value) : Bool :=
  @Option.casesOn Nat (fun _ => Bool) (Value.asStr v) false (fun _ => true)

-- `strKeys ps`: every key of ps is a string (true when there is none).
def strKeys (ps : List (Prod Value Value)) : Bool :=
  @List.rec (Prod Value Value) (fun _ => Bool) true
    (fun p _ rest => Bool.and (Value.isStr (Prod.fst p)) rest) ps

-- `fnIsRecord ps`: ps is non-empty and every key is a string, so whatever object TLC
-- holds it in has a record form (`toRcd` not null). The empty function is not one: TLC's
-- `[i \in 1..0 |-> e]` has no record form (see tlcCmp above).
def fnIsRecord (ps : List (Prod Value Value)) : Bool :=
  @List.casesOn (Prod Value Value) (fun _ => Bool) ps false (fun _ _ => strKeys ps)

-- The named refusal of an unpinned cross-kind order (B1A-D14).
def unpinnedCmp : Res Nat := Res.error (Fail.unmodeled Code.cmpUnpinned)

-- `Value.tag v`: the constructor index of v.
def Value.tag (v : Value) : Nat :=
  @Value.elim Nat v (fun _ => 0) (fun _ => 1) (fun _ => 2) (fun _ => 3) (fun _ _ => 4)
    (fun _ => 5) (fun _ => 6) (fun _ _ => 7)

-- `crossCmp b`: a value that is neither a model value nor of b's kind, against b: after
-- b when b is an untyped model value (`modelValueCompareTo` answers 1), `incomparable`
-- when b is a typed one (design 10:116), else unpinned.
def crossCmp (b : Value) : Res Nat :=
  @Option.casesOn Nat (fun _ => Res Nat) (Value.asMv b)
    (@Bool.rec (fun _ => Res Nat) unpinnedCmp (Res.error Fail.incomparable) (Value.isTmv b))
    (fun _ => Res.ok 2)

-- `infSetCmp k b`: an infSet of kind k against b: after an untyped model value for the
-- UserValue kinds (nat, int, string, seqOf; not fnSet, tag 4), else the named refusal.
def infSetCmp (k : InfKind) (b : Value) : Res Nat :=
  @Option.casesOn Nat (fun _ => Res Nat) (Value.asMv b) unpinnedCmp
    (fun _ => @Bool.rec (fun _ => Res Nat) (Res.ok 2) unpinnedCmp (Nat.beq (InfKind.tag k) 4))

-- `keyCmpWith go k l`: two function keys: `go` when they are of one kind, else the named
-- refusal (M0 review finding 5; see tlcCmp above).
def keyCmpWith (go : Value → Value → Res Nat) (k l : Value) : Res Nat :=
  @Bool.rec (fun _ => Res Nat) unpinnedCmp (go k l) (Nat.beq (Value.tag k) (Value.tag l))

-- `cmpThen r k`: r, unless r is `ok 1` (equal), in which case k (read only then).
def cmpThen (r k : Res Nat) : Res Nat :=
  Res.bind r (fun c => @Bool.rec (fun _ => Res Nat) (Res.ok c) k (Nat.beq c 1))

-- `cmpListWith go xs ys`: xs and ys element by element by `go`, the first unequal pair
-- or error deciding; a shorter list first (not reached by `tlcCmpF`, which compares the
-- lengths before).
def cmpListWith (go : Value → Value → Res Nat) (xs ys : List Value) : Res Nat :=
  @List.rec Value (fun _ => List Value → Res Nat)
    (fun rest => @List.casesOn Value (fun _ => Res Nat) rest (Res.ok 1) (fun _ _ => Res.ok 0))
    (fun x _ next rest => @List.casesOn Value (fun _ => Res Nat) rest (Res.ok 2)
      (fun y tail => cmpThen (go x y) (next tail)))
    xs ys

-- `cmpPairsWith go sel ps qs`: `cmpListWith` over the `sel` component of each pair.
def cmpPairsWith (go : Value → Value → Res Nat) (sel : Prod Value Value → Value)
    (ps qs : List (Prod Value Value)) : Res Nat :=
  @List.rec (Prod Value Value) (fun _ => List (Prod Value Value) → Res Nat)
    (fun rest => @List.casesOn (Prod Value Value) (fun _ => Res Nat) rest (Res.ok 1)
      (fun _ _ => Res.ok 0))
    (fun p _ next rest => @List.casesOn (Prod Value Value) (fun _ => Res Nat) rest (Res.ok 2)
      (fun q tail => cmpThen (go (sel p) (sel q)) (next tail)))
    ps qs

-- `tlcCmpF fuel a b`: TLC's order with explicit fuel; `Fail.fuel` when it runs out.
def tlcCmpF (fuel : Nat) : Value → Value → Res Nat :=
  @Nat.rec (fun _ => Value → Value → Res Nat)
    (fun _ _ => Res.error Fail.fuel)
    (fun _ go a b =>
      @Value.elim (Res Nat) a
        (fun x => @Option.casesOn Bool (fun _ => Res Nat) (Value.asBool b) (crossCmp b)
          (fun y => Res.ok (boolCmp x y)))
        (fun x => @Option.casesOn Int (fun _ => Res Nat) (Value.asInt b) (crossCmp b)
          (fun y => Res.ok (intCmp x y)))
        (fun r => @Option.casesOn Nat (fun _ => Res Nat) (Value.asStr b) (crossCmp b)
          (fun s => Res.ok (natCmp r s)))
        (fun r => @Option.casesOn Nat (fun _ => Res Nat) (Value.asMv b)
          (@Option.casesOn (Prod Nat Nat) (fun _ => Res Nat) (Value.asTmv b) (Res.ok 0)
            (fun p => Res.ok (natCmp r (Prod.snd p))))
          (fun s => Res.ok (natCmp r s)))
        (fun t r => @Option.casesOn (Prod Nat Nat) (fun _ => Res Nat) (Value.asTmv b)
          (@Option.casesOn Nat (fun _ => Res Nat) (Value.asMv b)
            (Res.error Fail.incomparable) (fun s => Res.ok (natCmp r s)))
          (fun p => @Bool.rec (fun _ => Res Nat)
            (Res.error Fail.incomparable)
            (Res.ok (natCmp r (Prod.snd p)))
            (Nat.beq t (Prod.fst p))))
        (fun xs => @Option.casesOn (List Value) (fun _ => Res Nat) (Value.asSet b) (crossCmp b)
          (fun ys => cmpThen (Res.ok (natCmp (List.length xs) (List.length ys)))
            (cmpListWith go xs ys)))
        (fun ps => @Option.casesOn (List (Prod Value Value)) (fun _ => Res Nat) (Value.asFn b)
          (crossCmp b)
          (fun qs => @Bool.rec (fun _ => Res Nat)
            unpinnedCmp
            (cmpThen (Res.ok (natCmp (List.length ps) (List.length qs)))
              (cmpThen (cmpPairsWith (keyCmpWith go) (@Prod.fst Value Value) ps qs)
                (cmpPairsWith go (@Prod.snd Value Value) ps qs)))
            (boolBeq (fnIsRecord ps) (fnIsRecord qs))))
        (fun k _ => infSetCmp k b))
    fuel

-- `tlcCmp a b`: TLC's order, with fuel that never runs out (see above).
def tlcCmp (a b : Value) : Res Nat :=
  tlcCmpF (Nat.succ (Value.size a)) a b

-- `tlcLt a b` (design 10:111): a comes strictly before b in TLC's order.
def tlcLt (a b : Value) : Res Bool :=
  Res.map (fun c => Nat.beq c 0) (tlcCmp a b)

-- `beqListWith go xs ys`: same length and `go` true at every position.
def beqListWith (go : Value → Value → Bool) (xs ys : List Value) : Bool :=
  @List.rec Value (fun _ => List Value → Bool)
    (fun rest => @List.casesOn Value (fun _ => Bool) rest true (fun _ _ => false))
    (fun x _ next rest => @List.casesOn Value (fun _ => Bool) rest false
      (fun y tail => @Bool.rec (fun _ => Bool) false (next tail) (go x y)))
    xs ys

-- `beqPairsWith go ps qs`: same length, and `go` true on both components at every position.
def beqPairsWith (go : Value → Value → Bool) (ps qs : List (Prod Value Value)) : Bool :=
  @List.rec (Prod Value Value) (fun _ => List (Prod Value Value) → Bool)
    (fun rest => @List.casesOn (Prod Value Value) (fun _ => Bool) rest true (fun _ _ => false))
    (fun p _ next rest => @List.casesOn (Prod Value Value) (fun _ => Bool) rest false
      (fun q tail =>
        @Bool.rec (fun _ => Bool) false
          (@Bool.rec (fun _ => Bool) false (next tail) (go (Prod.snd p) (Prod.snd q)))
          (go (Prod.fst p) (Prod.fst q))))
    ps qs

-- `Value.beqF fuel a b`: structural equality with explicit fuel; `false` when it runs out.
def Value.beqF (fuel : Nat) : Value → Value → Bool :=
  @Nat.rec (fun _ => Value → Value → Bool)
    (fun _ _ => false)
    (fun _ go a b =>
      @Value.elim Bool a
        (fun x => @Option.casesOn Bool (fun _ => Bool) (Value.asBool b) false
          (fun y => boolBeq x y))
        (fun x => @Option.casesOn Int (fun _ => Bool) (Value.asInt b) false
          (fun y => intBeq x y))
        (fun r => @Option.casesOn Nat (fun _ => Bool) (Value.asStr b) false
          (fun s => Nat.beq r s))
        (fun r => @Option.casesOn Nat (fun _ => Bool) (Value.asMv b) false
          (fun s => Nat.beq r s))
        (fun t r => @Option.casesOn (Prod Nat Nat) (fun _ => Bool) (Value.asTmv b) false
          (fun p => Bool.and (Nat.beq t (Prod.fst p)) (Nat.beq r (Prod.snd p))))
        (fun xs => @Option.casesOn (List Value) (fun _ => Bool) (Value.asSet b) false
          (fun ys => beqListWith go xs ys))
        (fun ps => @Option.casesOn (List (Prod Value Value)) (fun _ => Bool) (Value.asFn b) false
          (fun qs => beqPairsWith go ps qs))
        (fun k xs => @Option.casesOn (Prod InfKind (List Value)) (fun _ => Bool)
          (Value.asInfSet b) false
          (fun p => Bool.and (Nat.beq (InfKind.tag k) (InfKind.tag (Prod.fst p)))
            (beqListWith go xs (Prod.snd p)))))
    fuel

-- `Value.beq a b`: structural equality, the proof-carrying equality of seen-lists and
-- indexes (same constructor, equal fields; it is not TLC's `=`, which is `valueEq`,
-- B1A-11b). With the size fuel it never runs out.
def Value.beq (a b : Value) : Bool :=
  Value.beqF (Nat.succ (Value.size a)) a b

-- ---- TLC's `=`: valueEq (B1A-11b, B1A-D14, B1A-D87) ----
--
-- `valueEq a b` is TLC's `a.equals(b)` on canonical values (design 10:113-116, the
-- comparison rules; TLC 94d0c50's `equals` of BoolValue, IntValue, StringValue,
-- ModelValue, SetEnumValue, IntervalValue, FcnRcdValue, TupleValue and RecordValue, read
-- from the jar of record with `javap -c`): `Res.ok` of the answer, or the error TLC
-- raises. a is TLC's receiver (`this`), b its argument; the order matters where TLC's does.
--   model values (design 10:114-116; ModelValue.equals and modelValueEquals): an untyped
--           model value equals only an untyped one of the same rank, and is `false` against
--           anything else, a typed one included (ModelValueStrVsMv, -MvVsStr, -MvVsInt,
--           -IntVsMv, -MvVsTmv, -TmvVsMv). A typed model value equals one of its own tag by
--           rank, raises `incomparable` against another tag or a value that is not a model
--           value, in either order (ModelValueTmvDiffType, -TmvVsInt, -IntVsTmv, -StrVsTmv,
--           -TmvVsStr), and is `false` against an untyped one. Every non-model receiver
--           hands a model-value argument to `modelValueEquals`: `false` when untyped,
--           `incomparable` when typed.
--   bool, int, str: equal values of their own kind. A string against an integer raises
--           `incomparable` (cause probe CStrEqInt: "Attempted to check equality of string",
--           the `incomparable` class of the lane's cause table, DR-B1A-D30).
--   set:    a different cardinality is `false`, with no element compared; then element by
--           element in canonical order, the first `false` or error deciding (SetEnumValue:
--           both normalized, sizes, then `elementAt(i).equals(elementAt(i))`).
--   fn:     a record (`fnIsRecord`) against a function with no record form is the named
--           refusal in either order, before the sizes: TLC's RecordValue.equals raises
--           ("Attempted to check equality of record ... with non-record") when the other
--           operand's `toRcd` is null while TupleValue/FcnRcdValue answer by size or raise
--           another text, so the outcome depends on the representation and operand order
--           (as for `tlcCmp`, B1A-D86). Otherwise a different size is `false`; then every
--           key, then every value (FcnRcdValue.equals: sizes, all of the domain, then all
--           of the values; RecordValue: names, then values; TupleValue: values). Two keys of
--           different kinds are the named refusal: TLC compares an interval-domain key
--           against a non-integer one with "Attempted to compare integer with non-integer"
--           (an order-error text no cause row maps) and two list-domain keys with `equals`,
--           so the outcome depends on how TLC holds the domain. A function against an
--           integer raises `incomparable` (EnMemberBoundErr: "Attempted to check equality
--           of the function <<1>> with the value: 1"; RecordValue, TupleValue and
--           FcnRcdValue all reach an "Attempted to check equality of" text there).
--   infSet: Nat, Int, STRING and Seq(S) (kinds nat, int, string, seqOf) are TLC
--           UserValues (Naturals/Integers/Strings static initializers, Sequences.Seq), whose
--           `equals` is `compareTo(other) == 0`, and UserValue.compareTo returns 1 for ANY
--           ModelValue argument without raising (javap -c, the jar of record 94d0c50). So
--           against an untyped model value TLC answers `false`, which is design 10:115's rule:
--           `ok false` here. Against a typed model value TLC also answers `false` while design
--           10:116 says `incomparable`; the two disagree, so that pair stays the named refusal
--           until the design owner rules (K2-REQUESTS-B1A.md R1, item 7). fnSet ([S -> T],
--           SetOfFcnsValue.equals) converts and enumerates instead, so it refuses against a
--           model value too. Against any other argument an infSet receiver refuses (UserValue
--           delegates to its UserObj's compareTo, which no probe pins). Where the receiver is
--           a model value, its own rule above decides (untyped: `false`; typed:
--           `incomparable`).
-- Every other pair of kinds is an equality neither a probe nor the design pins, so it is
-- the named refusal `unmodeled cmp.unpinned` (B1A-D14): TLC raises there, with a text
-- whose class no probe records (a boolean's text, "Attempted to compare equality of
-- boolean", matches no cause row at all). Fuel is `Nat.succ (Value.size a)` through
-- `Nat.rec`, as for `tlcCmp`: every recursive call compares a proper part of a.

-- The named refusal of an unpinned cross-kind equality (B1A-D14).
def unpinnedEq : Res Bool := Res.error (Fail.unmodeled Code.cmpUnpinned)

-- `mvArgEq b other`: a receiver that is not a model value against b: `false` when b is an
-- untyped model value, `incomparable` when b is a typed one (modelValueEquals), else
-- `other` (b is of another kind than the receiver).
def mvArgEq (b : Value) (other : Res Bool) : Res Bool :=
  @Option.casesOn Nat (fun _ => Res Bool) (Value.asMv b)
    (@Bool.rec (fun _ => Res Bool) other (Res.error Fail.incomparable) (Value.isTmv b))
    (fun _ => Res.ok false)

-- `intArgIncomparable b`: `incomparable` when b is an integer (the pinned receivers: a
-- string, CStrEqInt; a function, EnMemberBoundErr), else the named refusal.
def intArgIncomparable (b : Value) : Res Bool :=
  @Option.casesOn Int (fun _ => Res Bool) (Value.asInt b) unpinnedEq
    (fun _ => Res.error Fail.incomparable)

-- `eqThen r k`: `ok false` and errors pass through; `ok true` continues with k (read only
-- then).
def eqThen (r k : Res Bool) : Res Bool :=
  Res.bind r (fun c => @Bool.rec (fun _ => Res Bool) (Res.ok false) k c)

-- `eqListWith go xs ys`: element by element by `go`, the first `false` or error deciding; a
-- length difference is `false` (not reached by `valueEqF`, which compares sizes before).
def eqListWith (go : Value → Value → Res Bool) (xs ys : List Value) : Res Bool :=
  @List.rec Value (fun _ => List Value → Res Bool)
    (fun rest => @List.casesOn Value (fun _ => Res Bool) rest (Res.ok true)
      (fun _ _ => Res.ok false))
    (fun x _ next rest => @List.casesOn Value (fun _ => Res Bool) rest (Res.ok false)
      (fun y tail => eqThen (go x y) (next tail)))
    xs ys

-- `eqPairsWith go sel ps qs`: `eqListWith` over the `sel` component of each pair.
def eqPairsWith (go : Value → Value → Res Bool) (sel : Prod Value Value → Value)
    (ps qs : List (Prod Value Value)) : Res Bool :=
  @List.rec (Prod Value Value) (fun _ => List (Prod Value Value) → Res Bool)
    (fun rest => @List.casesOn (Prod Value Value) (fun _ => Res Bool) rest (Res.ok true)
      (fun _ _ => Res.ok false))
    (fun p _ next rest => @List.casesOn (Prod Value Value) (fun _ => Res Bool) rest
      (Res.ok false)
      (fun q tail => eqThen (go (sel p) (sel q)) (next tail)))
    ps qs

-- `keyEqWith go k l`: two function keys: `go` when they are of one kind, else the named
-- refusal (see valueEq above).
def keyEqWith (go : Value → Value → Res Bool) (k l : Value) : Res Bool :=
  @Bool.rec (fun _ => Res Bool) unpinnedEq (go k l) (Nat.beq (Value.tag k) (Value.tag l))

-- `valueEqF fuel a b`: TLC's `=` with explicit fuel; `Fail.fuel` when it runs out.
def valueEqF (fuel : Nat) : Value → Value → Res Bool :=
  @Nat.rec (fun _ => Value → Value → Res Bool)
    (fun _ _ => Res.error Fail.fuel)
    (fun _ go a b =>
      @Value.elim (Res Bool) a
        (fun x => @Option.casesOn Bool (fun _ => Res Bool) (Value.asBool b)
          (mvArgEq b unpinnedEq) (fun y => Res.ok (boolBeq x y)))
        (fun x => @Option.casesOn Int (fun _ => Res Bool) (Value.asInt b)
          (mvArgEq b unpinnedEq) (fun y => Res.ok (intBeq x y)))
        (fun r => @Option.casesOn Nat (fun _ => Res Bool) (Value.asStr b)
          (mvArgEq b (intArgIncomparable b)) (fun s => Res.ok (Nat.beq r s)))
        (fun r => @Option.casesOn Nat (fun _ => Res Bool) (Value.asMv b) (Res.ok false)
          (fun s => Res.ok (Nat.beq r s)))
        (fun t r => @Option.casesOn (Prod Nat Nat) (fun _ => Res Bool) (Value.asTmv b)
          (@Option.casesOn Nat (fun _ => Res Bool) (Value.asMv b)
            (Res.error Fail.incomparable) (fun _ => Res.ok false))
          (fun p => @Bool.rec (fun _ => Res Bool)
            (Res.error Fail.incomparable)
            (Res.ok (Nat.beq r (Prod.snd p)))
            (Nat.beq t (Prod.fst p))))
        (fun xs => @Option.casesOn (List Value) (fun _ => Res Bool) (Value.asSet b)
          (mvArgEq b unpinnedEq)
          (fun ys => @Bool.rec (fun _ => Res Bool)
            (Res.ok false)
            (eqListWith go xs ys)
            (Nat.beq (List.length xs) (List.length ys))))
        (fun ps => @Option.casesOn (List (Prod Value Value)) (fun _ => Res Bool) (Value.asFn b)
          (mvArgEq b (intArgIncomparable b))
          (fun qs => @Bool.rec (fun _ => Res Bool)
            unpinnedEq
            (@Bool.rec (fun _ => Res Bool)
              (Res.ok false)
              (eqThen (eqPairsWith (keyEqWith go) (@Prod.fst Value Value) ps qs)
                (eqPairsWith go (@Prod.snd Value Value) ps qs))
              (Nat.beq (List.length ps) (List.length qs)))
            (boolBeq (fnIsRecord ps) (fnIsRecord qs))))
        (fun k _ => @Option.casesOn Nat (fun _ => Res Bool) (Value.asMv b) unpinnedEq
          (fun _ => @Bool.rec (fun _ => Res Bool) (Res.ok false) unpinnedEq
            (Nat.beq (InfKind.tag k) 4))))
    fuel

-- `valueEq a b`: TLC's `=`, with fuel that never runs out (see above).
def valueEq (a b : Value) : Res Bool :=
  valueEqF (Nat.succ (Value.size a)) a b

-- ---- Canonical forms: Value.Canon, normSet, builders (B1A-11b, B1A-D87) ----
--
-- `Value.Canon v` (design 10:211-212, `def-value-canon`): every set's elements and every
-- function's keys strictly increasing in `tlcLt`, recursively (keys and values of a
-- function, elements of a set, the arguments of an infSet); an order error is not
-- canonical; no tlc32 range bound (Decision K, 10:52).
--
-- `normSet xs` is TLC's `SetEnumValue.normalize` (ValueVec.sort with dropping of
-- duplicates, read from the jar of record): xs is the element list in TLC's order before
-- normalization; each element after the first is placed by binary search in the sorted
-- prefix, comparing it (as receiver) with the middle element `lo + (hi - lo) / 2`; an equal
-- element is dropped, otherwise it is inserted where the search ends. The comparisons are
-- TLC's own, in TLC's order, so the first error is the one TLC raises (or the named
-- refusal where `tlcCmp` refuses), and a set of one element compares nothing.
--
-- Builders (canonical when their inputs are): `mkTuple`/`mkSeq` (keys 1..n, design 10:85),
-- `mkFn dom vals` (`[x \in S |-> e]`: dom a canonical domain, `normSet`'s output, and the
-- values in its order), and `mkRecord` (fields as (name token rank, value) in source
-- order; sorted by rank as RecordValue.normalize sorts its names; a repeated name, where
-- TLC raises "Field name ... occurs multiple times in record." (a class no probe pins), is
-- the named refusal). That refusal is `cmp.unpinned`: RecordValue.normalize finds the
-- repetition by comparing two names equal, so it is a comparison whose TLC class is
-- unpinned, and D13 allows no code the design does not name (B1A-D93; the registry request
-- K2-REQUESTS-B1A.md R1 names this use; M0 review finding 20).

-- `ltOk a b`: `tlcLt a b` is `ok true` (an error is not).
def ltOk (a b : Value) : Bool :=
  @Res.rec Bool (fun _ => Bool) (fun x => x) (fun _ => false) (tlcLt a b)

-- `strictInc xs`: every element strictly before the next in TLC's order.
def strictInc (xs : List Value) : Bool :=
  @List.rec Value (fun _ => Bool) true
    (fun x rest ih =>
      Bool.and (@List.casesOn Value (fun _ => Bool) rest true (fun y _ => ltOk x y)) ih)
    xs

-- `keysOf ps`: the keys of ps, in order.
def keysOf (ps : List (Prod Value Value)) : List Value :=
  @List.rec (Prod Value Value) (fun _ => List Value) []
    (fun p _ rest => List.cons (Prod.fst p) rest) ps

-- `Value.Canon v`: v is canonical (structural, by `Value.rec`: motives Value, List Value,
-- List (Value × Value), Value × Value).
def Value.Canon (v : Value) : Bool :=
  @Value.rec (fun _ => Bool) (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
    (fun _ => true) (fun _ => true) (fun _ => true) (fun _ => true) (fun _ _ => true)
    (fun xs cxs => Bool.and cxs (strictInc xs))
    (fun ps cps => Bool.and cps (strictInc (keysOf ps)))
    (fun _ _ cxs => cxs)
    true (fun _ _ cx cxs => Bool.and cx cxs)
    true (fun _ _ cp cps => Bool.and cp cps)
    (fun _ _ ca cb => Bool.and ca cb)
    v

-- `listGetD xs i`: the i-th element of xs (from 0); `bool false` past the end (never read
-- by `normSet`, whose indices are in range).
def listGetD (xs : List Value) : Nat → Value :=
  @List.rec Value (fun _ => Nat → Value)
    (fun _ => Value.bool false)
    (fun x _ next i => @Bool.rec (fun _ => Value) (next (Nat.sub i 1)) x (Nat.beq i 0))
    xs

-- `listInsertAt x xs i`: xs with x inserted before position i (at the end when i is past it).
def listInsertAt (x : Value) (xs : List Value) : Nat → List Value :=
  @List.rec Value (fun _ => Nat → List Value)
    (fun _ => [x])
    (fun y ys next i => @Bool.rec (fun _ => List Value)
      (List.cons y (next (Nat.sub i 1)))
      (List.cons x (List.cons y ys))
      (Nat.beq i 0))
    xs

-- `midOf lo hi`: TLC's `lo + ((hi - lo) >> 1)`.
def midOf (lo hi : Nat) : Nat := Nat.add lo (Nat.div (Nat.sub hi lo) 2)

-- `normSearchF x sorted fuel lo hi`: TLC's binary search for x in sorted[lo, hi):
-- `ok none` when an equal element is found (x is dropped), `ok (some pos)` with the
-- insertion position, or the comparison's error. Each step shrinks hi - lo, so
-- `Nat.succ (List.length sorted)` never runs out.
def normSearchF (x : Value) (sorted : List Value) (fuel : Nat) : Nat → Nat → Res (Option Nat) :=
  @Nat.rec (fun _ => Nat → Nat → Res (Option Nat))
    (fun _ _ => Res.error Fail.fuel)
    (fun _ go lo hi =>
      @Bool.rec (fun _ => Res (Option Nat))
        (Res.ok (Option.some lo))
        (Res.bind (tlcCmp x (listGetD sorted (midOf lo hi)))
          (fun c => @Bool.rec (fun _ => Res (Option Nat))
            (@Bool.rec (fun _ => Res (Option Nat))
              (go (Nat.succ (midOf lo hi)) hi)
              (Res.ok Option.none)
              (Nat.beq c 1))
            (go lo (midOf lo hi))
            (Nat.beq c 0)))
        (Nat.blt lo hi))
    fuel

-- `normInsert acc x`: one step of TLC's sort: x placed into the sorted prefix acc.
def normInsert (acc : Res (List Value)) (x : Value) : Res (List Value) :=
  Res.bind acc (fun sorted =>
    Res.map (fun o => @Option.casesOn Nat (fun _ => List Value) o sorted
        (fun pos => listInsertAt x sorted pos))
      (normSearchF x sorted (Nat.succ (List.length sorted)) 0 (List.length sorted)))

-- `normSet xs`: TLC's normalized set of the elements xs (in TLC's pre-normalization
-- order): sorted by `tlcCmp`, duplicates dropped; the first comparison error wins.
def normSet (xs : List Value) : Res (List Value) :=
  @List.rec Value (fun _ => Res (List Value) → Res (List Value))
    (fun acc => acc)
    (fun x _ next acc => next (normInsert acc x))
    xs (Res.ok [])

-- `tupleFrom vs i`: the pairs (i, v1), (i+1, v2), ...
def tupleFrom (vs : List Value) : Nat → List (Prod Value Value) :=
  @List.rec Value (fun _ => Nat → List (Prod Value Value))
    (fun _ => [])
    (fun v _ next i => List.cons (Prod.mk (Value.int (Int.ofNat i)) v) (next (Nat.succ i)))
    vs

-- `mkTuple vs`: <<v1, ..., vn>>, the function on 1..n.
def mkTuple (vs : List Value) : Value := Value.fn (tupleFrom vs 1)

-- `mkSeq vs`: the sequence of vs (a sequence is a tuple, design 10:85).
def mkSeq (vs : List Value) : Value := mkTuple vs

-- `zipPairs ks vs`: (k1, v1), (k2, v2), ..., as long as the shorter list.
def zipPairs (ks : List Value) : List Value → List (Prod Value Value) :=
  @List.rec Value (fun _ => List Value → List (Prod Value Value))
    (fun _ => [])
    (fun k _ next vs => @List.casesOn Value (fun _ => List (Prod Value Value)) vs []
      (fun v rest => List.cons (Prod.mk k v) (next rest)))
    ks

-- `mkFn dom vals`: the function on the canonical domain dom with the values vals, in
-- dom's order (`[x \in S |-> e]`, S normalized by `normSet`).
def mkFn (dom vals : List Value) : Value := Value.fn (zipPairs dom vals)

-- `rcdInsert f fs`: the field f = (rank, value) inserted into fs, ascending by rank; a
-- repeated rank is the named refusal.
def rcdInsert (f : Prod Nat Value) (fs : List (Prod Nat Value)) : Res (List (Prod Nat Value)) :=
  @List.rec (Prod Nat Value) (fun _ => Res (List (Prod Nat Value)))
    (Res.ok [f])
    (fun q qs next =>
      @Bool.rec (fun _ => Res (List (Prod Nat Value)))
        (@Bool.rec (fun _ => Res (List (Prod Nat Value)))
          (Res.map (fun rest => List.cons q rest) next)
          (Res.error (Fail.unmodeled Code.cmpUnpinned))
          (Nat.beq (Prod.fst f) (Prod.fst q)))
        (Res.ok (List.cons f (List.cons q qs)))
        (Nat.blt (Prod.fst f) (Prod.fst q)))
    fs

-- `rcdPairs fs`: the record's (str name, value) pairs.
def rcdPairs (fs : List (Prod Nat Value)) : List (Prod Value Value) :=
  @List.rec (Prod Nat Value) (fun _ => List (Prod Value Value)) []
    (fun f _ rest => List.cons (Prod.mk (Value.str (Prod.fst f)) (Prod.snd f)) rest) fs

-- `mkRecord fs`: the record [n1 |-> v1, ...] of the fields fs = (name rank, value), in
-- source order.
def mkRecord (fs : List (Prod Nat Value)) : Res Value :=
  Res.map (fun sorted => Value.fn (rcdPairs sorted))
    (@List.rec (Prod Nat Value) (fun _ => Res (List (Prod Nat Value)) → Res (List (Prod Nat Value)))
      (fun acc => acc)
      (fun f _ next acc => next (Res.bind acc (fun sorted => rcdInsert f sorted)))
      fs (Res.ok []))

-- The executable presentation's version (design 10:526, `def-epversion`). A Rust
-- consumer refuses a presentation it was not built against with
-- `model.ep-version`; trust-model-prelude's `EP_VERSION` mirrors this number.
def epVersion : Nat := 1

end Model
end Trust
