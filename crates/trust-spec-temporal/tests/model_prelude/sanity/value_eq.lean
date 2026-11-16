-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-11b sanity facts for Trust.Model.Value's equality and canonical forms
-- (model_prelude_kernel.rs, sanity_files): `valueEq` (TLC's `=`), `Value.Canon`, `normSet`
-- and the builders `mkTuple`, `mkSeq`, `mkFn`, `mkRecord`. Elaborated after the whole
-- model prelude; every theorem below is accepted by check_model_theorem (kernel re-check,
-- constructive, axiom-free, audited). Every fact is a Bool door closed by rfl (B1A-D54,
-- TASK-STATE 4.8); the mutated-literal doors of SANITY_MUTANTS must each be refuted (class
-- Definite).
--
-- `probe_<Name>` states, for each ModelValue* probe of batch A (ty
-- reports/perf/2026-10-09-beyond-tla-b1a/probes/batch-A.txt, PR-model-value), the `=`
-- outcome TLC 94d0c50 recorded (INDEX.tsv: `counts 2 2` with the probe's Result invariant
-- holding is a value, `error incomparable` the cause row "Attempted to check equality of",
-- DR-B1A-D30), at value level, over the probe's own values: a string or model value is its
-- token rank in the probe's dump (`tokens-<Name>.txt`: "a" 1, "x" 465, a 1, A_a 1,
-- A_b 2; a string's rank is its RUNTIME StringValue rank, the unquoted token, not the
-- lexer's quoted image: "a" is the UniqueString of the model value a, B1A-14a, M0 review
-- finding 6), a typed model value `X_n` is `Value.tmv <char code of X> <rank>` (A = 65,
-- B = 66), the receiver is the left operand of the probe's `=`. ModelValueMvSetOrder, which
-- records an order, is stated through `normSet` over its literal `{C, B, A}` = {mid 3,
-- alpha 2, zeta 1}: the canonical set starts with zeta, which CHOOSE takes (`violated
-- ChoseZeta`); `probe_ChooseOrder{Str,Int}` do the same for batch B's CHOOSE probes.
-- `probe_C*` and `probe_EnMemberBoundErr` state the cross-kind equalities other committed
-- TLC logs pin (the cause probes ty reports/perf/2026-10-09-beyond-tla-b1a/tools/
-- cause-probes/: "a" is 378 in tokens-CStrEqInt.txt, and the str arm reads no rank, so it
-- is stated at 0 too; oracle_enabled's EnMemberBoundErr: "Attempted to check
-- equality of the function <<1>> with the value: 1"). Every other cross-kind equality is
-- B1A-D14's named refusal `unmodeled cmp.unpinned`.

namespace Trust
namespace Model
namespace Sanity

-- Doors. `isTrue`/`isFalse`: a Res Bool is `ok true`/`ok false`. `failTag`: a Fail's
-- constructor index. `isErrB r f`: r is an error of f's constructor. `isUnmodeledB r c`: r
-- is `unmodeled c`. `isOkList r ys`: r is `ok xs` with xs structurally ys. `isErrL`,
-- `isUnmodeledL`: the same for a Res (List Value). `isOkVal r v`: r is `ok v'`, v'
-- structurally v.
def isTrue (r : Res Bool) : Bool :=
  @Res.rec Bool (fun _ => Bool) (fun b => b) (fun _ => false) r
def isFalse (r : Res Bool) : Bool :=
  @Res.rec Bool (fun _ => Bool) (fun b => @Bool.rec (fun _ => Bool) true false b) (fun _ => false) r
def failTag (f : Fail) : Nat :=
  @Fail.casesOn (fun _ => Nat) f 0 1 2 3 4 5 6 7 8 (fun _ => 9) 10 11 12 (fun _ => 13)
def isErrB (r : Res Bool) (f : Fail) : Bool :=
  @Res.rec Bool (fun _ => Bool) (fun _ => false) (fun e => Nat.beq (failTag e) (failTag f)) r
def unmodeledIs (e : Fail) (c : Nat) : Bool :=
  @Fail.casesOn (fun _ => Bool) e false false false false false false false false
    false (fun _ => false) false false false (fun k => Nat.beq k c)
def isUnmodeledB (r : Res Bool) (c : Nat) : Bool :=
  @Res.rec Bool (fun _ => Bool) (fun _ => false) (fun e => unmodeledIs e c) r
def isOkList (r : Res (List Value)) (ys : List Value) : Bool :=
  @Res.rec (List Value) (fun _ => Bool) (fun xs => Value.beq (Value.set xs) (Value.set ys))
    (fun _ => false) r
def isErrL (r : Res (List Value)) (f : Fail) : Bool :=
  @Res.rec (List Value) (fun _ => Bool) (fun _ => false)
    (fun e => Nat.beq (failTag e) (failTag f)) r
def isUnmodeledL (r : Res (List Value)) (c : Nat) : Bool :=
  @Res.rec (List Value) (fun _ => Bool) (fun _ => false) (fun e => unmodeledIs e c) r
def isOkVal (r : Res Value) (v : Value) : Bool :=
  @Res.rec Value (fun _ => Bool) (fun x => Value.beq x v) (fun _ => false) r
def isUnmodeledV (r : Res Value) (c : Nat) : Bool :=
  @Res.rec Value (fun _ => Bool) (fun _ => false) (fun e => unmodeledIs e c) r
def notB (b : Bool) : Bool := @Bool.rec (fun _ => Bool) true false b
-- `eqBothWays a b f`: `valueEq` raises f's class in both orders.
def eqBothWays (a b : Value) (f : Fail) : Bool :=
  Bool.and (isErrB (valueEq a b) f) (isErrB (valueEq b a) f)
-- `unpinnedBothWays a b`: `valueEq` is `unmodeled cmp.unpinned` in both orders.
def unpinnedBothWays (a b : Value) : Bool :=
  Bool.and (isUnmodeledB (valueEq a b) Code.cmpUnpinned)
    (isUnmodeledB (valueEq b a) Code.cmpUnpinned)
-- `falseBothWays a b`: `valueEq` is `ok false` in both orders.
def falseBothWays (a b : Value) : Bool :=
  Bool.and (isFalse (valueEq a b)) (isFalse (valueEq b a))

-- Values used below.
def int (n : Int) : Value := Value.int n
def fn1 (k v : Value) : Value := Value.fn [(k, v)]
def fn2 (k1 v1 k2 v2 : Value) : Value := Value.fn [(k1, v1), (k2, v2)]
def tup1 : Value := fn1 (int 1) (int 1)
def tup12 : Value := fn2 (int 1) (int 1) (int 2) (int 2)
def rcdA (a : Nat) : Value := fn1 (Value.str a) (int 1)
def deep : Value :=
  Value.set [int 1, Value.set [int 2, Value.tmv 65 3],
    fn2 (Value.str 10) (Value.bool true) (Value.str 11) (Value.set [])]

-- ---- Batch A, PR-model-value: the ModelValue* probes' `=` outcomes ----

-- "a" = a, and its mirror a = "a": FALSE (a string never equals a model value, 10:114).
theorem probe_ModelValueStrVsMv : isFalse (valueEq (Value.str 1) (Value.mv 1)) = true := rfl
theorem probe_ModelValueMvVsStr : isFalse (valueEq (Value.mv 1) (Value.str 1)) = true := rfl
-- a = 1 and 1 = a: FALSE (an untyped model value against a non-model value, 10:115).
theorem probe_ModelValueMvVsInt : isFalse (valueEq (Value.mv 1) (int 1)) = true := rfl
theorem probe_ModelValueIntVsMv : isFalse (valueEq (int 1) (Value.mv 1)) = true := rfl
-- A_a = 1 and 1 = A_a: `incomparable` (10:116).
theorem probe_ModelValueTmvVsInt :
    isErrB (valueEq (Value.tmv 65 1) (int 1)) Fail.incomparable = true := rfl
theorem probe_ModelValueIntVsTmv :
    isErrB (valueEq (int 1) (Value.tmv 65 1)) Fail.incomparable = true := rfl
-- A_a = A_b FALSE, A_a = A_a TRUE, no error.
theorem probe_ModelValueTmvSameType :
    Bool.and (isFalse (valueEq (Value.tmv 65 1) (Value.tmv 65 2)))
      (isTrue (valueEq (Value.tmv 65 1) (Value.tmv 65 1))) = true := rfl
-- A_a = B_b: `incomparable`.
theorem probe_ModelValueTmvDiffType :
    isErrB (valueEq (Value.tmv 65 1) (Value.tmv 66 2)) Fail.incomparable = true := rfl
-- a = A_b and A_b = a: FALSE (TLC's ModelValue.equals accepts an untyped operand; 10:116's
-- "different type" excludes untyped model values).
theorem probe_ModelValueMvVsTmv : isFalse (valueEq (Value.mv 1) (Value.tmv 65 2)) = true := rfl
theorem probe_ModelValueTmvVsMv : isFalse (valueEq (Value.tmv 65 2) (Value.mv 1)) = true := rfl
-- "x" = A_b and A_b = "x": `incomparable`.
theorem probe_ModelValueStrVsTmv :
    isErrB (valueEq (Value.str 465) (Value.tmv 65 2)) Fail.incomparable = true := rfl
theorem probe_ModelValueTmvVsStr :
    isErrB (valueEq (Value.tmv 65 2) (Value.str 465)) Fail.incomparable = true := rfl
-- {C, B, A} = {mid 3, alpha 2, zeta 1} normalizes to zeta, alpha, mid: CHOOSE takes zeta.
theorem probe_ModelValueMvSetOrder :
    isOkList (normSet [Value.mv 3, Value.mv 2, Value.mv 1])
      [Value.mv 1, Value.mv 2, Value.mv 3] = true := rfl

-- ---- Batch B, PR-choose: the CHOOSE domains normalized ----

-- {"mid", "alpha", "zeta"} with "zeta" 547, "alpha" 548, "mid" 549 (the runtime ranks):
-- zeta first.
theorem probe_ChooseOrderStr :
    isOkList (normSet [Value.str 549, Value.str 548, Value.str 547])
      [Value.str 547, Value.str 548, Value.str 549] = true := rfl
-- {4, 1, 3, 2}: 1, 2, 3, 4, so the first element above 1 is 2.
theorem probe_ChooseOrderInt :
    isOkList (normSet [int 4, int 1, int 3, int 2]) [int 1, int 2, int 3, int 4] = true := rfl

-- ---- Other committed TLC logs that pin a cross-kind `=` ----

-- CStrEqInt: "a" = 1 raises "Attempted to check equality of string" (`incomparable`); "a"
-- is 378 in its dump (tokens-CStrEqInt.txt), and the str arm reads no rank (0 too).
theorem probe_CStrEqInt :
    Bool.and (isErrB (valueEq (Value.str 378) (int 1)) Fail.incomparable)
      (isErrB (valueEq (Value.str 0) (int 1)) Fail.incomparable) = true := rfl
-- CTmvInt: a = 1 with a = A_a (`incomparable`).
theorem probe_CTmvInt : isErrB (valueEq (Value.tmv 65 1) (int 1)) Fail.incomparable = true := rfl
-- EnMemberBoundErr: <<1>> = 1 raises "Attempted to check equality of the function"; the
-- same class for a record and an empty function (RecordValue, FcnRcdValue).
theorem probe_EnMemberBoundErr :
    Bool.and (isErrB (valueEq (mkTuple [int 1]) (int 1)) Fail.incomparable)
      (Bool.and (isErrB (valueEq (rcdA 372) (int 1)) Fail.incomparable)
        (isErrB (valueEq (Value.fn []) (int 1)) Fail.incomparable)) = true := rfl

-- ---- Scalars and model values ----

theorem scalars_equal :
    Bool.and (isTrue (valueEq (Value.bool true) (Value.bool true)))
      (Bool.and (isFalse (valueEq (Value.bool true) (Value.bool false)))
        (Bool.and (isTrue (valueEq (int (-5)) (int (-5))))
          (Bool.and (isFalse (valueEq (int 5) (int (-5))))
            (Bool.and (isTrue (valueEq (Value.str 7) (Value.str 7)))
              (Bool.and (isFalse (valueEq (Value.str 7) (Value.str 8)))
                (Bool.and (isTrue (valueEq (Value.mv 4) (Value.mv 4)))
                  (isFalse (valueEq (Value.mv 4) (Value.mv 5))))))))) = true := rfl
-- A string never equals a model value, even of the same rank (10:113).
theorem str_never_mv : falseBothWays (Value.str 5) (Value.mv 5) = true := rfl
-- An untyped model value is FALSE against every other kind, in both orders (10:115;
-- ModelValue.equals, and every non-model receiver's modelValueEquals).
theorem mv_against_other_kinds :
    Bool.and (falseBothWays (Value.mv 1) (Value.bool true))
      (Bool.and (falseBothWays (Value.mv 1) (Value.set [int 1]))
        (Bool.and (falseBothWays (Value.mv 1) tup12)
          (Bool.and (falseBothWays (Value.mv 1) (rcdA 2))
            (isFalse (valueEq (Value.mv 1) (Value.infSet InfKind.nat [])))))) = true := rfl
-- A typed model value raises `incomparable` against every value that is not a model value,
-- in both orders (10:116), and against an infSet as the receiver.
theorem tmv_against_non_model :
    Bool.and (eqBothWays (Value.tmv 65 1) (Value.bool false) Fail.incomparable)
      (Bool.and (eqBothWays (Value.tmv 65 1) (Value.set []) Fail.incomparable)
        (Bool.and (eqBothWays (Value.tmv 65 1) tup12 Fail.incomparable)
          (Bool.and (eqBothWays (Value.tmv 65 1) (rcdA 2) Fail.incomparable)
            (isErrB (valueEq (Value.tmv 65 1) (Value.infSet InfKind.int [])) Fail.incomparable))))
      = true := rfl

-- ---- Cross-kind equalities no probe pins (B1A-D14) ----

-- Including the mirrors of the pinned ones: 1 = "a" and 1 = <<1>> (TLC raises "Attempted
-- to check equality of integer", unprobed), and a boolean receiver (TLC's text
-- "Attempted to compare equality of boolean" matches no cause row).
theorem cross_kind_unpinned :
    Bool.and (isUnmodeledB (valueEq (int 1) (Value.str 378)) Code.cmpUnpinned)
      (Bool.and (isUnmodeledB (valueEq (int 1) tup1) Code.cmpUnpinned)
        (Bool.and (unpinnedBothWays (Value.bool true) (int 1))
          (Bool.and (unpinnedBothWays (Value.set []) (Value.fn []))
            (Bool.and (unpinnedBothWays (Value.str 1) (Value.bool false))
              (Bool.and (unpinnedBothWays (Value.set [int 1]) (int 1))
                (unpinnedBothWays (Value.str 1) tup1)))))) = true := rfl
-- An infSet receiver (B1A-D87 as amended by B1A-12). Nat, Int, STRING and Seq(S) are TLC
-- UserValues, whose `equals` is `compareTo(other) == 0`, and UserValue.compareTo returns 1
-- for any ModelValue argument without raising (javap -c, TLC 94d0c50): against an untyped
-- model value TLC answers FALSE, as design 10:115 says.
theorem infSet_vs_mv :
    Bool.and (isFalse (valueEq (Value.infSet InfKind.nat []) (Value.mv 1)))
      (Bool.and (isFalse (valueEq (Value.infSet InfKind.int []) (Value.mv 2)))
        (Bool.and (isFalse (valueEq (Value.infSet InfKind.string []) (Value.mv 1)))
          (isFalse (valueEq (Value.infSet InfKind.seqOf [Value.set [int 1]]) (Value.mv 1)))))
      = true := rfl
-- Everything else an infSet receiver meets refuses: a typed model value (TLC answers
-- FALSE, design 10:116 says `incomparable`: the conflict is filed for the design owner,
-- K2-REQUESTS-B1A.md R1 item 7), fnSet against a model value (SetOfFcnsValue.equals
-- converts and enumerates instead), and any other argument (UserValue delegates to its
-- UserObj's compareTo, which no probe pins).
theorem infSet_unpinned :
    Bool.and (isUnmodeledB (valueEq (Value.infSet InfKind.nat []) (Value.infSet InfKind.nat []))
        Code.cmpUnpinned)
      (Bool.and (isUnmodeledB (valueEq (Value.infSet InfKind.int []) (Value.tmv 65 1))
          Code.cmpUnpinned)
        (Bool.and (isUnmodeledB (valueEq (Value.infSet InfKind.nat []) (Value.tmv 65 1))
            Code.cmpUnpinned)
          (Bool.and (isUnmodeledB (valueEq (Value.infSet InfKind.fnSet
                [Value.set [int 1], Value.set [int 2]]) (Value.mv 1)) Code.cmpUnpinned)
            (unpinnedBothWays (Value.infSet InfKind.string []) (int 0))))) = true := rfl

-- ---- Sets: cardinality first, then element by element ----

-- {1} = {"a", "b"}: FALSE, no element compared (an int against a str would refuse).
theorem set_size_first :
    falseBothWays (Value.set [int 1]) (Value.set [Value.str 1, Value.str 2]) = true := rfl
theorem set_elementwise :
    Bool.and (isTrue (valueEq (Value.set [int 1, int 2]) (Value.set [int 1, int 2])))
      (Bool.and (isFalse (valueEq (Value.set [int 1, int 2]) (Value.set [int 1, int 3])))
        (isTrue (valueEq (Value.set []) (Value.set [])))) = true := rfl
-- The first FALSE decides; the typed model value in the second position raises nothing.
-- This is a fact about the encoding on an input outside the carrier, not a TLC outcome:
-- `{0, A_a}` is not canonical (`tlcCmp` raises `incomparable` between its elements), and
-- TLC's SetEnumValue.equals normalizes both operands before comparing sizes, so on that
-- TLA+ input TLC would raise `incomparable` during normalization. The fact states only
-- that `valueEq` reads no element after the first FALSE.
theorem set_first_false_wins :
    isFalse (valueEq (Value.set [int 0, Value.tmv 65 1]) (Value.set [int 1, int 2])) = true := rfl
theorem set_element_errors :
    Bool.and (isErrB (valueEq (Value.set [tup1]) (Value.set [int 1])) Fail.incomparable)
      (isUnmodeledB (valueEq (Value.set [int 1]) (Value.set [Value.str 1])) Code.cmpUnpinned)
      = true := rfl

-- ---- Functions: size, then every key, then every value ----

theorem fn_size_first :
    falseBothWays (fn1 (int 1) (Value.str 0)) (fn2 (int 1) (int 0) (int 2) (int 0)) = true := rfl
-- Keys 1 = 1, 3 /= 2: FALSE before any value is compared ("a" against 1 would raise).
theorem fn_keys_before_values :
    falseBothWays (fn2 (int 1) (Value.str 5) (int 3) (int 1)) (fn2 (int 1) (int 1) (int 2) (int 1))
      = true := rfl
theorem fn_values :
    Bool.and (isTrue (valueEq tup12 (mkTuple [int 1, int 2])))
      (Bool.and (isFalse (valueEq tup12 (mkTuple [int 1, int 3])))
        (isErrB (valueEq (fn1 (int 1) tup1) (fn1 (int 1) (int 1))) Fail.incomparable)) = true :=
  rfl
-- Keys of different kinds refuse: `[x \in {A_a} |-> 1] = <<1>>` (TLC: "Attempted to
-- compare integer with non-integer" against an interval domain), and a set key against an
-- integer key.
theorem fn_key_kinds_unpinned :
    Bool.and (unpinnedBothWays (fn1 (Value.tmv 65 1) (int 1)) tup1)
      (unpinnedBothWays (fn1 (Value.set [int 1]) (int 1)) tup1) = true := rfl
-- A record against a function with no record form refuses, in both orders, before the
-- sizes: `[a |-> 1]` against `<<1>>`, `<<1, 2>>`, the empty function, and a function with
-- one non-string key.
theorem fn_record_guard :
    Bool.and (unpinnedBothWays (rcdA 372) tup1)
      (Bool.and (unpinnedBothWays (rcdA 372) tup12)
        (Bool.and (unpinnedBothWays (rcdA 372) (Value.fn []))
          (unpinnedBothWays (rcdA 372) (fn2 (Value.str 372) (int 1) (int 5) (int 1))))) = true :=
  rfl
-- Two records, two non-record functions and two empty functions are still compared.
theorem fn_kinds_still_compared :
    Bool.and (isTrue (valueEq (rcdA 372) (rcdA 372)))
      (Bool.and (isFalse (valueEq (rcdA 372) (rcdA 373)))
        (Bool.and (isFalse (valueEq (rcdA 372) (fn1 (Value.str 372) (int 2))))
          (Bool.and (isTrue (valueEq (Value.fn []) (Value.fn [])))
            (falseBothWays (Value.fn []) tup12)))) = true := rfl
theorem fn_deep_equal : isTrue (valueEq deep deep) = true := rfl

-- ---- Fuel: by size, so it runs out only when given less ----

theorem eq_fuel_runs_out_only_below_size :
    Bool.and (isErrB (valueEqF 1 (Value.set [int 1]) (Value.set [int 1])) Fail.fuel)
      (isTrue (valueEqF 2 (Value.set [int 1]) (Value.set [int 1]))) = true := rfl

-- ---- normSet: TLC's normalize (binary insertion, duplicates dropped) ----

theorem normSet_sorts_and_dedupes :
    Bool.and (isOkList (normSet []) [])
      (Bool.and (isOkList (normSet [int 2, int 1, int 2, int 1]) [int 1, int 2])
        (Bool.and (isOkList (normSet [int 5, int (-3), int 0, int 9, int (-3)])
            [int (-3), int 0, int 5, int 9])
          (isOkList (normSet [Value.set [int 2], Value.set [], Value.set [int 1]])
            [Value.set [], Value.set [int 1], Value.set [int 2]]))) = true := rfl
-- A set of one element compares nothing, so nothing in it can raise.
theorem normSet_singleton :
    isOkList (normSet [Value.set [Value.tmv 65 1, int 1]]) [Value.set [Value.tmv 65 1, int 1]]
      = true := rfl
-- The first comparison error in TLC's order wins: "a" is placed before A_a here, so the
-- refusal of str against int comes first; in the other order, A_a's `incomparable`.
theorem normSet_errors :
    Bool.and (isUnmodeledL (normSet [int 1, Value.str 5]) Code.cmpUnpinned)
      (Bool.and (isErrL (normSet [Value.tmv 65 1, int 1]) Fail.incomparable)
        (Bool.and (isUnmodeledL (normSet [int 1, Value.str 5, Value.tmv 65 1]) Code.cmpUnpinned)
          (Bool.and (isErrL (normSet [int 1, Value.tmv 65 1, Value.str 5]) Fail.incomparable)
            (isUnmodeledL (normSet [rcdA 372, tup12]) Code.cmpUnpinned)))) = true := rfl

-- ---- Value.Canon ----

theorem canon_sets :
    Bool.and (Value.Canon (Value.set [int 1, int 2]))
      (Bool.and (notB (Value.Canon (Value.set [int 2, int 1])))
        (Bool.and (notB (Value.Canon (Value.set [int 1, int 1])))
          (Bool.and (notB (Value.Canon (Value.set [int 1, Value.str 2])))
            (Bool.and (notB (Value.Canon (Value.set [Value.tmv 65 1, Value.tmv 66 2])))
              (Bool.and (Value.Canon (Value.set []))
                (Bool.and (Value.Canon (Value.set [Value.set [int 1], Value.set [int 1, int 2]]))
                  (notB (Value.Canon deep)))))))) = true := rfl
-- Recursively: a non-canonical set inside a set, a key, a value or an infSet argument.
theorem canon_recursive :
    Bool.and (notB (Value.Canon (Value.set [Value.set [int 2, int 1]])))
      (Bool.and (notB (Value.Canon (fn1 (Value.set [int 2, int 1]) (int 0))))
        (Bool.and (notB (Value.Canon (fn1 (int 0) (Value.set [int 2, int 1]))))
          (notB (Value.Canon (Value.infSet InfKind.seqOf [Value.set [int 2, int 1]]))))) = true :=
  rfl
theorem canon_fn_keys :
    Bool.and (Value.Canon tup12)
      (Bool.and (notB (Value.Canon (fn2 (int 2) (int 0) (int 1) (int 0))))
        (Bool.and (notB (Value.Canon (fn2 (int 1) (int 0) (int 1) (int 5))))
          (Bool.and (Value.Canon (fn2 (Value.str 3) (int 0) (Value.str 9) (int 0)))
            (Value.Canon (Value.fn []))))) = true := rfl
-- No tlc32 range bound (Decision K, 10:52).
theorem canon_no_range_bound :
    Bool.and (Value.Canon (int 1099511627776)) (Value.Canon (Value.set [int (-1099511627776), int 0]))
      = true := rfl
theorem canon_of_normSet :
    @Res.rec (List Value) (fun _ => Bool) (fun xs => Value.Canon (Value.set xs)) (fun _ => false)
      (normSet [int 3, int 1, int 2, int 1]) = true := rfl

-- ---- Builders ----

theorem builders_tuple_seq :
    Bool.and (Value.beq (mkTuple [Value.str 1, Value.bool true])
        (fn2 (int 1) (Value.str 1) (int 2) (Value.bool true)))
      (Bool.and (Value.beq (mkSeq []) (Value.fn []))
        (Bool.and (Value.beq (mkSeq [int 7]) (fn1 (int 1) (int 7)))
          (Value.Canon (mkTuple [int 3, int 2, int 1])))) = true := rfl
theorem builders_fn :
    Bool.and (Value.beq (mkFn [int 1, int 4] [Value.str 2, Value.str 3])
        (fn2 (int 1) (Value.str 2) (int 4) (Value.str 3)))
      (Value.Canon (mkFn [Value.str 3, Value.str 9] [int 0, int 0])) = true := rfl
-- Fields in source order are sorted by name rank; a repeated name refuses (TLC raises
-- "Field name ... occurs multiple times in record.", a class no probe pins).
theorem builders_record :
    Bool.and (isOkVal (mkRecord [(5, int 1), (3, int 2)]) (fn2 (Value.str 3) (int 2) (Value.str 5) (int 1)))
      (Bool.and (isOkVal (mkRecord []) (Value.fn []))
        (Bool.and (isUnmodeledV (mkRecord [(5, int 1), (3, int 2), (5, int 3)]) Code.cmpUnpinned)
          (@Res.rec Value (fun _ => Bool) Value.Canon (fun _ => false)
            (mkRecord [(9, int 0), (2, int 0), (4, int 0)])))) = true := rfl

end Sanity
end Model
end Trust
