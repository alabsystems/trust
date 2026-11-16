-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-11a sanity facts for Trust.Model.Value's order (model_prelude_kernel.rs,
-- sanity_files): `tlcCmp`, `tlcLt` and the structural `Value.beq`. Elaborated after the
-- whole model prelude; every theorem below is accepted by check_model_theorem (kernel
-- re-check, constructive, axiom-free, audited). Every fact is a Bool door closed by rfl
-- (B1A-D54, TASK-STATE 4.8); the mutated-literal doors of SANITY_MUTANTS must each be
-- refuted (class Definite).
--
-- `probe_<Name>` states, for each ModelValue* probe of batch A (ty
-- reports/perf/2026-10-09-beyond-tla-b1a/probes/batch-A.txt, PR-model-value), the order
-- fact over the probe's own values, and `probe_ChooseOrder{Int,Str}` the two CHOOSE order
-- probes of batch B. A string or model value is its token rank in the probe's TLC dump
-- (`tokens-<Name>.txt`, TLC 94d0c50; e.g. ModelValueMvSetOrder mints zeta 1, alpha 2,
-- mid 3); a typed model value `X_n` is `Value.tmv <char code of X> <rank>` (A = 65,
-- B = 66). Where TLC's recorded outcome is an order (MvSetOrder: CHOOSE takes zeta;
-- ChooseOrderStr: zeta; ChooseOrderInt: 2) the fact is that order. The other eleven
-- probes record `=`, so their order fact is pinned elsewhere, and each such fact names its
-- evidence: a typed model value against another type tag or a value that is not a model
-- value raises `incomparable` in either order (design 10:116; TLC 94d0c50's order texts
-- "Attempted to compare the differently-typed model values" / "the typed model value ...
-- and (the) non-model value", the order probes TmvTmvDiff, TmvIntA/B and TmvNatB of ty
-- reports/perf/2026-10-09-beyond-tla-b1a/m0-review-probes/, cause rows 201 and 202;
-- TmvDiffType, TmvVsInt, IntVsTmv, StrVsTmv and TmvVsStr are the equality analogue,
-- stated by valueEq in value_eq.lean); an untyped model value comes before every value
-- that is not a model value, in either order, and against a typed one goes by rank (B1A-14a,
-- the M0 review's finding 14: m0-review-probes/ Mv*{A,B}, MvTmvA/B, TmvMvA/B, where CHOOSE
-- takes the untyped value, or the one minted first, whichever literal comes first). String
-- ranks are the RUNTIME StringValue ranks of each dump (B1A-14a, M0 review finding 6): the
-- unquoted token, e.g. "a" is 1 in ModelValueStrVsMv (the same UniqueString as the model
-- value a) and "x" is 465 in ModelValueStrVsTmv; the quoted `"a"` image is the lexer's.
-- `beq_<Name>` states `Value.beq` on the seven probes whose TLC `=` outcome is a value,
-- not an error: structural equality agrees with it there (TmvSameType TRUE and FALSE,
-- the six others FALSE; `notBeq` checks both orders, so beq_ModelValueStrVsMv,
-- beq_ModelValueMvVsInt and beq_ModelValueMvVsTmv also cover the mirrors MvVsStr, IntVsMv
-- and TmvVsMv). `Value.beq` is not TLC's `=` (that is valueEq, B1A-11b), so
-- the five `incomparable` probes get no beq fact.
-- `probe_Rec*` (B1A-11a repair round 1, B1A-D86 as corrected) state that a record against
-- a function with no record form is the named refusal in both orders, over the values of
-- the order probes in ty reports/perf/2026-10-09-beyond-tla-b1a/order-probes/, where TLC
-- raises in one order or both.
-- `probe_Mv*`, `probe_TmvMv`, `probe_TmvNat` (B1A-14a, the M0 review's findings 4 and 14)
-- state the order the m0-review-probes/ logs record, over each probe's values (N is the
-- untyped model value nv, rank 1 where the cfg mints it first; T is the typed A_t, rank 2;
-- "s" is 365 and the record field v 375, the dumps' runtime ranks).

namespace Trust
namespace Model
namespace Sanity

-- Doors. `isOrd r c`: r is `ok c` (0 before, 1 equal, 2 after). `isTrue`/`isFalse`:
-- a Res Bool is `ok true`/`ok false`. `failTag`: a Fail's constructor index. `isErrN r f`:
-- r is an error of f's constructor. `isUnmodeledN r c`: r is `unmodeled c`.
def isOrd (r : Res Nat) (c : Nat) : Bool :=
  @Res.rec Nat (fun _ => Bool) (fun x => Nat.beq x c) (fun _ => false) r
def isTrue (r : Res Bool) : Bool :=
  @Res.rec Bool (fun _ => Bool) (fun b => b) (fun _ => false) r
def isFalse (r : Res Bool) : Bool :=
  @Res.rec Bool (fun _ => Bool) (fun b => @Bool.rec (fun _ => Bool) true false b) (fun _ => false) r
def failTag (f : Fail) : Nat :=
  @Fail.casesOn (fun _ => Nat) f 0 1 2 3 4 5 6 7 8 (fun _ => 9) 10 11 12 (fun _ => 13)
def isErrN (r : Res Nat) (f : Fail) : Bool :=
  @Res.rec Nat (fun _ => Bool) (fun _ => false) (fun e => Nat.beq (failTag e) (failTag f)) r
def isErrB (r : Res Bool) (f : Fail) : Bool :=
  @Res.rec Bool (fun _ => Bool) (fun _ => false) (fun e => Nat.beq (failTag e) (failTag f)) r
def isUnmodeledN (r : Res Nat) (c : Nat) : Bool :=
  @Res.rec Nat (fun _ => Bool) (fun _ => false)
    (fun e => @Fail.casesOn (fun _ => Bool) e false false false false false false false false
      false (fun _ => false) false false false (fun k => Nat.beq k c))
    r
-- `bothWays a b f`: `tlcCmp` raises f's class in both orders.
def bothWays (a b : Value) (f : Fail) : Bool :=
  Bool.and (isErrN (tlcCmp a b) f) (isErrN (tlcCmp b a) f)
-- `unpinnedBothWays a b`: `tlcCmp` is `unmodeled cmp.unpinned` in both orders.
def unpinnedBothWays (a b : Value) : Bool :=
  Bool.and (isUnmodeledN (tlcCmp a b) Code.cmpUnpinned)
    (isUnmodeledN (tlcCmp b a) Code.cmpUnpinned)
-- `notB b`: b is false. `notBeq a b`: `Value.beq` is false in both orders.
def notB (b : Bool) : Bool := @Bool.rec (fun _ => Bool) true false b
def notBeq (a b : Value) : Bool :=
  Bool.and (@Bool.rec (fun _ => Bool) true false (Value.beq a b))
    (@Bool.rec (fun _ => Bool) true false (Value.beq b a))

-- Values used below. `deep` nests sets, a record-like function and a typed model value.
def int (n : Int) : Value := Value.int n
def fn1 (k v : Value) : Value := Value.fn [(k, v)]
def fn2 (k1 v1 k2 v2 : Value) : Value := Value.fn [(k1, v1), (k2, v2)]
def deep : Value :=
  Value.set [int 1, Value.set [int 2, Value.tmv 65 3],
    fn2 (Value.str 10) (Value.bool true) (Value.str 11) (Value.set [])]

-- ---- Batch A, PR-model-value: the ModelValue* probes ----

-- zeta 1, alpha 2, mid 3: zeta comes first (CHOOSE takes zeta, `violated ChoseZeta`),
-- not alpha (lexical) or mid (the literal's first element).
theorem probe_ModelValueMvSetOrder :
    Bool.and (isTrue (tlcLt (Value.mv 1) (Value.mv 2)))
      (isTrue (tlcLt (Value.mv 1) (Value.mv 3))) = true := rfl
-- A_a 1, A_b 2: one type tag, ordered by rank, no error (TLC: a = b FALSE, a = a TRUE).
theorem probe_ModelValueTmvSameType :
    Bool.and (isOrd (tlcCmp (Value.tmv 65 1) (Value.tmv 65 2)) 0)
      (Bool.and (isOrd (tlcCmp (Value.tmv 65 2) (Value.tmv 65 1)) 2)
        (isOrd (tlcCmp (Value.tmv 65 1) (Value.tmv 65 1)) 1)) = true := rfl
-- A_a 1, B_b 2: `incomparable` (design 10:116 and ModelValue.compareTo; the probe's
-- recorded `error incomparable` is the outcome of `=`, the equality analogue).
theorem probe_ModelValueTmvDiffType :
    bothWays (Value.tmv 65 1) (Value.tmv 66 2) Fail.incomparable = true := rfl
-- A_a 1 and the integer 1, in the probe's order and its mirror (TmvVsInt, IntVsTmv).
theorem probe_ModelValueTmvVsInt :
    isErrN (tlcCmp (Value.tmv 65 1) (int 1)) Fail.incomparable = true := rfl
theorem probe_ModelValueIntVsTmv :
    isErrN (tlcCmp (int 1) (Value.tmv 65 1)) Fail.incomparable = true := rfl
-- "x" 465 and A_b 2 (StrVsTmv, TmvVsStr): `incomparable` (design 10:116; the order text
-- is StringValue.compareTo's `modelValueCompareTo`, as IntValue's in TmvIntA).
theorem probe_ModelValueStrVsTmv :
    isErrN (tlcCmp (Value.str 465) (Value.tmv 65 2)) Fail.incomparable = true := rfl
theorem probe_ModelValueTmvVsStr :
    isErrN (tlcCmp (Value.tmv 65 2) (Value.str 465)) Fail.incomparable = true := rfl
-- a 1 and A_b 2 (MvVsTmv, TmvVsMv): by rank in either order (MvTmvA/B, TmvMvA/B).
theorem probe_ModelValueMvVsTmv :
    isOrd (tlcCmp (Value.mv 1) (Value.tmv 65 2)) 0 = true := rfl
theorem probe_ModelValueTmvVsMv :
    isOrd (tlcCmp (Value.tmv 65 2) (Value.mv 1)) 2 = true := rfl
-- "a" 1 and a 1 (StrVsMv, MvVsStr; one rank, two constructors); a 1 and the integer 1
-- (MvVsInt, IntVsMv): the untyped model value first, in either order (MvStrA/B, MvIntA/B).
theorem probe_ModelValueStrVsMv :
    isOrd (tlcCmp (Value.str 1) (Value.mv 1)) 2 = true := rfl
theorem probe_ModelValueMvVsStr :
    isOrd (tlcCmp (Value.mv 1) (Value.str 1)) 0 = true := rfl
theorem probe_ModelValueMvVsInt :
    isOrd (tlcCmp (Value.mv 1) (int 1)) 0 = true := rfl
theorem probe_ModelValueIntVsMv :
    isOrd (tlcCmp (int 1) (Value.mv 1)) 2 = true := rfl

-- `Value.beq` agrees with TLC's `=` where that is a value: TmvSameType (a = b FALSE,
-- a = a TRUE) and the FALSE of StrVsMv, MvVsStr, MvVsInt, IntVsMv, MvVsTmv, TmvVsMv.
theorem beq_ModelValueTmvSameType :
    Bool.and (Value.beq (Value.tmv 65 1) (Value.tmv 65 1))
      (notBeq (Value.tmv 65 1) (Value.tmv 65 2)) = true := rfl
theorem beq_ModelValueStrVsMv : notBeq (Value.str 1) (Value.mv 1) = true := rfl
theorem beq_ModelValueMvVsInt : notBeq (Value.mv 1) (int 1) = true := rfl
theorem beq_ModelValueMvVsTmv : notBeq (Value.mv 1) (Value.tmv 65 2) = true := rfl

-- ---- Batch B, PR-choose: CHOOSE takes the first element in TLC's order ----

-- "zeta" 547, "alpha" 548, "mid" 549 (the runtime ranks; 364, 366 and 367 are the quoted
-- lexer images, ty EVIDENCE.md B1A-05): token rank, so zeta (`violated ChoseZeta`).
theorem probe_ChooseOrderStr :
    Bool.and (isTrue (tlcLt (Value.str 547) (Value.str 548)))
      (isTrue (tlcLt (Value.str 547) (Value.str 549))) = true := rfl
-- {4, 1, 3, 2}: numeric, so the first element above 1 is 2 (`violated Chose2`).
theorem probe_ChooseOrderInt :
    Bool.and (isTrue (tlcLt (int 1) (int 2)))
      (Bool.and (isTrue (tlcLt (int 2) (int 3))) (isTrue (tlcLt (int 2) (int 4)))) = true :=
  rfl

-- ---- The M0 review's order probes (m0-review-probes/; findings 4 and 14) ----

-- `mvFirst m x`: m before x, x after m (the A probe inserts x as the receiver, the B probe m).
def mvFirst (m x : Value) : Bool := Bool.and (isOrd (tlcCmp m x) 0) (isOrd (tlcCmp x m) 2)
def nv : Value := Value.mv 1
theorem probe_MvScalars :
    Bool.and (mvFirst nv (int 1))
      (Bool.and (mvFirst nv (Value.str 365)) (mvFirst nv (Value.bool true))) = true := rfl
theorem probe_MvCompound :
    Bool.and (mvFirst nv (Value.set [int 1]))
      (Bool.and (mvFirst nv (fn2 (int 1) (int 1) (int 2) (int 2)))
        (Bool.and (mvFirst nv (fn1 (Value.str 375) (int 1)))
          (mvFirst nv (fn2 (int 2) (int 2) (int 3) (int 3))))) = true := rfl
-- Nat, Int, STRING and Seq({1}) are TLC UserValues, whose compareTo answers 1 for any model
-- value (MvNatA/B, MvIntSetA/B, MvStringA/B, MvSeqA/B).
theorem probe_MvInfSets :
    Bool.and (mvFirst nv (Value.infSet InfKind.nat []))
      (Bool.and (mvFirst nv (Value.infSet InfKind.int []))
        (Bool.and (mvFirst nv (Value.infSet InfKind.string []))
          (mvFirst nv (Value.infSet InfKind.seqOf [Value.set [int 1]])))) = true := rfl
-- Untyped against typed: by rank whichever was minted first (MvTmvA/B: nv 1, A_t 2;
-- TmvMvA/B: A_t 1, nv 2).
theorem probe_TmvMv :
    Bool.and (mvFirst nv (Value.tmv 65 2))
      (Bool.and (isOrd (tlcCmp (Value.tmv 65 1) (Value.mv 2)) 0)
        (isOrd (tlcCmp (Value.mv 2) (Value.tmv 65 1)) 2)) = true := rfl
-- A typed model value and Nat (finding 4): TLC orders them when Nat is the receiver
-- (TmvNatA: UserValue.compareTo answers 1) and raises when the typed value is (TmvNatB,
-- cause row 201). Design 10:116 says `incomparable` for both, so the first is the named
-- refusal until the design owner rules (K2-REQUESTS-B1A.md R1 item 7), the second TLC's
-- class; the same for every UserValue kind.
theorem probe_TmvNat :
    Bool.and (isUnmodeledN (tlcCmp (Value.infSet InfKind.nat []) (Value.tmv 65 2)) Code.cmpUnpinned)
      (Bool.and (isErrN (tlcCmp (Value.tmv 65 2) (Value.infSet InfKind.nat [])) Fail.incomparable)
        (Bool.and (isUnmodeledN (tlcCmp (Value.infSet InfKind.int []) (Value.tmv 65 2)) Code.cmpUnpinned)
          (Bool.and (isUnmodeledN (tlcCmp (Value.infSet InfKind.string []) (Value.tmv 65 2))
              Code.cmpUnpinned)
            (isUnmodeledN (tlcCmp (Value.infSet InfKind.seqOf []) (Value.tmv 65 2)) Code.cmpUnpinned))))
      = true := rfl
-- A typed model value against an integer, either receiver, and two type tags (TmvIntA/B,
-- TmvTmvDiff): `incomparable`.
theorem probe_TmvInt :
    Bool.and (bothWays (Value.tmv 65 2) (int 1) Fail.incomparable)
      (bothWays (Value.tmv 65 2) (Value.tmv 66 3) Fail.incomparable) = true := rfl

-- ---- Scalars ----

theorem bool_order :
    Bool.and (isOrd (tlcCmp (Value.bool false) (Value.bool true)) 0)
      (Bool.and (isOrd (tlcCmp (Value.bool true) (Value.bool false)) 2)
        (isOrd (tlcCmp (Value.bool true) (Value.bool true)) 1)) = true := rfl
theorem int_order :
    Bool.and (isOrd (tlcCmp (int (-3)) (int 2)) 0)
      (Bool.and (isOrd (tlcCmp (int (-3)) (int (-2))) 0)
        (Bool.and (isOrd (tlcCmp (int 5) (int (-1))) 2)
          (Bool.and (isOrd (tlcCmp (int 0) (int 0)) 1)
            (isOrd (tlcCmp (int (-2147483648)) (int 2147483647)) 0)))) = true := rfl
theorem str_mv_rank_order :
    Bool.and (isOrd (tlcCmp (Value.str 3) (Value.str 5)) 0)
      (Bool.and (isOrd (tlcCmp (Value.mv 5) (Value.mv 3)) 2)
        (isOrd (tlcCmp (Value.str 4) (Value.str 4)) 1)) = true := rfl
theorem tlcLt_values :
    Bool.and (isTrue (tlcLt (int 1) (int 2)))
      (Bool.and (isFalse (tlcLt (int 2) (int 2))) (isFalse (tlcLt (int 3) (int 2)))) = true :=
  rfl
theorem tlcLt_error :
    isErrB (tlcLt (Value.tmv 65 1) (int 1)) Fail.incomparable = true := rfl

-- ---- Sets: cardinality first, then element by element ----

theorem set_cardinality_first :
    isOrd (tlcCmp (Value.set [int 5]) (Value.set [int 1, int 2])) 0 = true := rfl
theorem set_elementwise :
    Bool.and (isOrd (tlcCmp (Value.set [int 1, int 3]) (Value.set [int 1, int 2])) 2)
      (isOrd (tlcCmp (Value.set [int 1, int 2]) (Value.set [int 1, int 3])) 0) = true := rfl
theorem set_empty :
    Bool.and (isOrd (tlcCmp (Value.set []) (Value.set [int 0])) 0)
      (isOrd (tlcCmp (Value.set []) (Value.set [])) 1) = true := rfl
theorem set_nested :
    isOrd (tlcCmp (Value.set [Value.set [int 1], Value.set [int 2]])
      (Value.set [Value.set [int 1], Value.set [int 3]])) 0 = true := rfl
-- The first unequal pair decides; nothing after it is compared, so the typed model value
-- in the second position raises nothing. This is a fact about the encoding on an input
-- outside the carrier, not a TLC outcome: `{0, A_a}` is not canonical (`tlcCmp` raises
-- `incomparable` between its elements), and TLC normalizes a set before comparing it, so
-- on that TLA+ input TLC would raise during normalization. The fact states only that
-- `tlcCmp` reads no element after the first unequal pair.
theorem set_first_difference_wins :
    isOrd (tlcCmp (Value.set [int 0, Value.tmv 65 1]) (Value.set [int 1, int 2])) 0 = true :=
  rfl
theorem set_element_error :
    isErrN (tlcCmp (Value.set [Value.tmv 65 1]) (Value.set [int 1])) Fail.incomparable = true :=
  rfl

-- ---- Functions: domain size first, then every key, then every value ----

theorem fn_size_first :
    isOrd (tlcCmp (fn1 (int 1) (int 9)) (fn2 (int 1) (int 0) (int 2) (int 0))) 0 = true := rfl
-- Keys 1 = 1, 2 < 3: before, although the first value 9 is above 0.
theorem fn_keys_before_values :
    isOrd (tlcCmp (fn2 (int 1) (int 9) (int 2) (int 0)) (fn2 (int 1) (int 0) (int 3) (int 0))) 0
      = true := rfl
theorem fn_values :
    Bool.and
      (isOrd (tlcCmp (fn2 (int 1) (int 0) (int 2) (int 5)) (fn2 (int 1) (int 0) (int 2) (int 3))) 2)
      (isOrd (tlcCmp (fn2 (int 1) (int 0) (int 2) (int 5)) (fn2 (int 1) (int 0) (int 2) (int 5))) 1)
      = true := rfl
-- A record's field names are strings, ordered by token rank, before its values.
theorem record_names_by_rank :
    isOrd (tlcCmp (fn1 (Value.str 10) (int 0)) (fn1 (Value.str 9) (int 5))) 2 = true := rfl
theorem fn_deep_equal : isOrd (tlcCmp deep deep) 1 = true := rfl

-- ---- A record against a function with no record form (B1A-D86 as corrected) ----
--
-- TLC 94d0c50's RecordValue.compareTo raises ("Attempted to compare record ... with
-- non-record") when the other operand has no record form (`toRcd` null: a non-empty
-- tuple, an interval-domain or non-string-domain function), while TupleValue's and
-- FcnRcdValue's compareTo order the same pair by size: the outcome depends on which
-- operand TLC holds the record in. The verifier's probes, re-run and committed in ty
-- reports/perf/2026-10-09-beyond-tla-b1a/order-probes/, put `[a |-> 1]` in one set with
-- `<<1, 2>>` (RecTupA: the record is chosen, `violated ChoseRec`; RecTupB: raises) and
-- with `[i \in {2, 3} |-> i]` (RecFcnC: chosen; RecFcnD: raises). The empty function
-- (B1A-D86's empty case): `<<>>` (RecEmpTupA/B) and `[i \in {} |-> i]` (RecEmpDomA/B)
-- come first in both orders, but `[i \in 1..0 |-> i]` raises in one (RecEmpIntvB; its
-- mirror RecEmpIntvA does not), and all three are `fn []`, so a record against `fn []`
-- refuses too. `"a"` is each probe's dump rank (372 in the A probes, 375 in RecTupB and
-- RecEmpIntvB, 378 in RecFcnD, 374 in RecTupSameB).
def rcdA (a : Nat) : Value := fn1 (Value.str a) (int 1)
def tup12 : Value := fn2 (int 1) (int 1) (int 2) (int 2)
def fn23 : Value := fn2 (int 2) (int 2) (int 3) (int 3)
theorem probe_RecTup :
    Bool.and (unpinnedBothWays (rcdA 372) tup12) (unpinnedBothWays (rcdA 375) tup12) = true :=
  rfl
theorem probe_RecFcn :
    Bool.and (unpinnedBothWays (rcdA 372) fn23) (unpinnedBothWays (rcdA 378) fn23) = true :=
  rfl
theorem probe_RecEmpty :
    Bool.and (unpinnedBothWays (rcdA 372) (Value.fn [])) (unpinnedBothWays (rcdA 375) (Value.fn []))
      = true := rfl
-- Of one size too: `[a |-> 1]` and `<<1>>` raise in both orders, with two different
-- messages, neither a pinned class (RecTupSameA: "Attempted to compare integer with
-- non-integer", "a" 372; RecTupSameB: "Attempted to compare record", "a" 374); and
-- against a function with one non-string key among string ones.
theorem probe_RecTupSame :
    Bool.and (unpinnedBothWays (rcdA 372) (fn1 (int 1) (int 1)))
      (Bool.and (unpinnedBothWays (rcdA 374) (fn1 (int 1) (int 1)))
        (unpinnedBothWays (rcdA 372) (fn2 (Value.str 372) (int 1) (int 5) (int 1)))) = true :=
  rfl
-- The guard is narrow: two records, two non-record functions, and the empty function
-- against a non-record are still ordered by size, keys, then values.
theorem fn_kinds_still_ordered :
    Bool.and (isOrd (tlcCmp (rcdA 372) (fn2 (Value.str 372) (int 1) (Value.str 373) (int 2))) 0)
      (Bool.and (isOrd (tlcCmp tup12 fn23) 0)
        (Bool.and (isOrd (tlcCmp fn23 tup12) 2)
          (Bool.and (isOrd (tlcCmp (Value.fn []) tup12) 0)
            (Bool.and (isOrd (tlcCmp tup12 (Value.fn [])) 2)
              (isOrd (tlcCmp (Value.fn []) (Value.fn [])) 1))))) = true := rfl

-- ---- Cross-kind (B1A-D14) ----

theorem cross_kind_unpinned :
    Bool.and (unpinnedBothWays (Value.bool true) (int 1))
      (Bool.and (unpinnedBothWays (int 1) (Value.str 1))
        (Bool.and (unpinnedBothWays (Value.set []) (Value.fn []))
          (Bool.and (unpinnedBothWays (Value.str 1) (Value.bool false))
            (unpinnedBothWays (Value.set []) (Value.infSet InfKind.nat []))))) = true := rfl
theorem tmv_against_other_kinds :
    Bool.and (bothWays (Value.tmv 65 1) (Value.set []) Fail.incomparable)
      (Bool.and (bothWays (Value.tmv 65 1) (Value.fn []) Fail.incomparable)
        (Bool.and (bothWays (Value.tmv 65 1) (Value.bool true) Fail.incomparable)
          (isErrN (tlcCmp (Value.tmv 65 1) (Value.infSet InfKind.fnSet [])) Fail.incomparable)))
      = true := rfl
theorem infSet_unpinned :
    Bool.and (unpinnedBothWays (Value.infSet InfKind.nat []) (Value.infSet InfKind.nat []))
      (Bool.and (unpinnedBothWays (Value.infSet InfKind.int []) (int 0))
        (Bool.and (unpinnedBothWays (Value.infSet InfKind.fnSet []) (Value.bool true))
          -- fnSet ([S -> T], SetOfFcnsValue) converts itself before comparing: refused
          -- against an untyped model value as the receiver; as the argument it comes after.
          (Bool.and (isUnmodeledN (tlcCmp (Value.infSet InfKind.fnSet []) (Value.mv 1)) Code.cmpUnpinned)
            (isOrd (tlcCmp (Value.mv 1) (Value.infSet InfKind.fnSet [])) 0)))) = true := rfl

-- Two function keys of different kinds (finding 5): the named refusal in either order, as
-- for `=` (TLC's interval-domain compare raises "Attempted to compare integer with
-- non-integer", a list-domain one calls compareTo). Keys of one kind still order.
theorem fn_keys_of_two_kinds :
    Bool.and (unpinnedBothWays (fn1 (int 1) (int 0)) (fn1 (Value.tmv 65 1) (int 0)))
      (Bool.and (unpinnedBothWays (fn1 (int 1) (int 0)) (fn1 (Value.mv 1) (int 0)))
        (Bool.and (unpinnedBothWays (fn1 (Value.mv 1) (int 0)) (fn1 (Value.tmv 65 2) (int 0)))
          (isOrd (tlcCmp (fn1 (Value.mv 1) (int 0)) (fn1 (Value.mv 2) (int 0))) 0))) = true := rfl

-- ---- Fuel: by size, so it runs out only when given less ----

theorem size_counts_parts :
    Bool.and (Nat.beq (Value.size (Value.set [int 1, fn1 (int 1) (Value.bool true)])) 5)
      (Nat.beq (Value.size deep) 10) = true := rfl
theorem fuel_runs_out_only_below_size :
    Bool.and (isErrN (tlcCmpF 1 (Value.set [int 1]) (Value.set [int 1])) Fail.fuel)
      (isOrd (tlcCmpF 2 (Value.set [int 1]) (Value.set [int 1])) 1) = true := rfl

-- ---- Value.beq: structural ----

theorem beq_deep_reflexive : Value.beq deep deep = true := rfl
theorem beq_deep_leaf_differs :
    notBeq deep
      (Value.set [int 1, Value.set [int 2, Value.tmv 65 3],
        fn2 (Value.str 10) (Value.bool true) (Value.str 11) (Value.set [int 0])]) = true := rfl
theorem beq_shapes :
    Bool.and (notBeq (Value.set [int 1]) (Value.set [int 1, int 2]))
      (Bool.and (notBeq (Value.str 1) (Value.mv 1))
        (Bool.and (notBeq (Value.tmv 65 1) (Value.tmv 66 1))
          (Bool.and (notBeq (Value.infSet InfKind.nat []) (Value.infSet InfKind.int []))
            (Bool.and (Value.beq (Value.infSet InfKind.seqOf [int 1]) (Value.infSet InfKind.seqOf [int 1]))
              (notBeq (fn1 (int 1) (int 2)) (fn1 (int 2) (int 1))))))) = true := rfl
theorem beq_fuel_zero :
    Bool.and (notB (Value.beqF 0 (int 1) (int 1))) (Value.beqF 2 (int 1) (int 1)) = true := rfl

end Sanity
end Model
end Trust
