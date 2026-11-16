-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-15 sanity facts for Trust.Model.Tlc's PrimOp evaluator (model_prelude_kernel.rs,
-- sanity_files): one fact per PrimOp constructor (`op_<constructor>`), every batch-B integer
-- row of PR-int-probes (`probe_Int*`), the five truth tables of the Boolean encodings
-- (B1A-D11) restated through the presentation's own `evalE`, the operand-count and
-- binder-count refusals (B1A-D95 as amended) and the set-normalization timing refusal
-- (B1A-D96). Elaborated after the whole model prelude; every theorem is accepted by
-- check_model_theorem and is a Bool door closed by rfl (B1A-D54); the mutated-literal doors
-- of SANITY_MUTANTS must each be refuted (class Definite).
--
-- Where the expectations come from. Every TLA+ fact is the recorded outcome of a TLC probe
-- on the jar of record (TLC 94d0c50, sha256 7beec0f0...ea78d), never the encoding: `[Name]`
-- is ty reports/perf/2026-10-09-beyond-tla-b1a/primop-probes/tlc-Name.txt (run by this row
-- with `b1a_ttlc --dir $B1A_TREC/primop-probes`; a value probe's `Pin` is violated exactly
-- when `s'` is the stated value; an error probe's class is ../tools/causes.tsv's), and
-- `[probes/Name]` the batch-B log of B1A-05. Token ranks are the probes' dumps
-- (tokens-Name.txt): the model value `m` is 1 and `A_t` 2 in every probe; "a" is 378 and "b"
-- 380 in PRecGet/PRecWith, "b" 378 and "a" 380 in PRecNew; the facts use those ranks. The
-- truth tables' rows are TLC's Tool.evalApplImpl (javap, opcodes 27, 36-39), as in
-- syntax.lean. Facts with no TLA+ counterpart (natSuccU/natSatU, an operand count, the
-- lazy rows still pending) cite the design or a decision. The plain integer, seq.index and
-- tuple.new values are [PArithValues] (B1A-15 repair round 1, which also probed IsFiniteSet of
-- a function, UNION of a non-SetEnum element, Cardinality of [S -> T] with an infinite operand,
-- a quantifier over it, and set.in against every non-set kind; repair round 2 probed
-- set.subseteq over [S -> T] with an infinite operand and over every non-Enumerable kind).

namespace Trust
namespace Model
namespace Sanity

def int (n : Int) : Value := Value.int n
def num (n : Int) : Expr := Expr.lit (Value.int n)
def tt : Expr := Expr.lit (Value.bool true)
def ff : Expr := Expr.lit (Value.bool false)
def vT : Value := Value.bool true
def vF : Value := Value.bool false
def strE (r : Nat) : Expr := Expr.lit (Value.str r)
def op (o : PrimOp) (xs : List Expr) : Expr := Expr.op o xs
def setE (xs : List Expr) : Expr := op PrimOp.setEnum xs
def tupE (xs : List Expr) : Expr := op PrimOp.tupleNew xs
def neg (e : Expr) : Expr := op PrimOp.intNeg [e]
-- The probes' model values: M (untyped, `m`, rank 1) and T (typed, `A_t`: tag 65, rank 2).
def vM : Value := Value.mv 1
def vTm : Value := Value.tmv 65 2
def mE : Expr := Expr.lit vM
def tE : Expr := Expr.lit vTm
def natE : Expr := Expr.lit (Value.infSet InfKind.nat [])
def intE : Expr := Expr.lit (Value.infSet InfKind.int [])
def strSetE : Expr := Expr.lit (Value.infSet InfKind.string [])
def seqOfE (e : Expr) : Expr := op PrimOp.seqSet [e]
def fnSetE (a b : Expr) : Expr := op PrimOp.funcSet [a, b]
def tup (vs : List Value) : Value := mkTuple vs
def setV (vs : List Value) : Value := Value.set vs

-- The spec of the facts: one variable, nothing else (the facts evaluate closed terms).
def spP : Spec :=
  Spec.mk 1 IntMode.tlc32 [] [] [] [] [] (Act.conj []) (Act.conj []) [] [] [] [] true
    ChoiceMode.none

-- `ev e`: e evaluated and forced (`evalE`, 10:301-302) at fuel 64 (every term below nests
-- far less), keepLazy off, at the state [0] with successor [0].
def ev (e : Expr) : Res Value := evalE spP 64 [] [int 0] [int 0] e

-- ---- Reading results ----

-- The constructor of a Fail (10:93-100): overflow 0, notInDomain 1, divZero 3, typeErr 4,
-- notEnumerable 7, assertFailed 9, incomparable 10, fuel 12, unmodeled 13.
def failTag (f : Fail) : Nat :=
  @Fail.casesOn (fun _ => Nat) f 0 1 2 3 4 5 6 7 8 (fun _ => 9) 10 11 12 (fun _ => 13)
def errTag (r : Res Value) (t : Nat) : Bool :=
  @Res.rec Value (fun _ => Bool) (fun _ => false) (fun f => Nat.beq (failTag f) t) r
def isOverflow (r : Res Value) : Bool := errTag r 0
def isNotInDomain (r : Res Value) : Bool := errTag r 1
def isDivZero (r : Res Value) : Bool := errTag r 3
def isTypeErr (r : Res Value) : Bool := errTag r 4
def isNotEnumerable (r : Res Value) : Bool := errTag r 7
def isIncomparable (r : Res Value) : Bool := errTag r 10
def isFuel (r : Res Value) : Bool := errTag r 12
def isUnmodeled (r : Res Value) (code : Nat) : Bool :=
  @Res.rec Value (fun _ => Bool) (fun _ => false)
    (fun f => @Fail.casesOn (fun _ => Bool) f false false false false false false false false
      false (fun _ => false) false false false (fun c => Nat.beq c code))
    r
def isAssertFailed (r : Res Value) (msg : Nat) : Bool :=
  @Res.rec Value (fun _ => Bool) (fun _ => false)
    (fun f => @Fail.casesOn (fun _ => Bool) f false false false false false false false false
      false (fun m => Nat.beq m msg) false false false (fun _ => false))
    r
-- The refusals: cmp.unpinned (B1A-D14, B1A-D96) and a row still pending (Tlc.todo).
def isRefused (r : Res Value) : Bool := isUnmodeled r Code.cmpUnpinned
def isPending (r : Res Value) : Bool := isUnmodeled r Code.todo
-- `okV r v`: r is the value v (structurally, `Value.beq`).
def okV (r : Res Value) (v : Value) : Bool :=
  @Res.rec Value (fun _ => Bool) (fun a => Value.beq a v) (fun _ => false) r
-- `allT bs`: every door holds.
def allT (bs : List Bool) : Bool := @List.rec Bool (fun _ => Bool) true (fun b _ r => Bool.and b r) bs

-- ---- Integers (Naturals/Integers; B1A-D08, B1A-D85) ----

-- [PArithValues] `<<2 + 3, 2 - 3, 2 * 3, -3, 7 \div 2, 7 % 3, <<5, 6>>[1], <<5, TRUE>>, <<>>>>`
-- = <<5, -1, 6, -3, 3, 1, 5, <<5, TRUE>>, <<>>>>: the value parts of op_intAdd .. op_intMod,
-- op_seqIndex and op_tupleNew.
-- [PIntAddNonInt] `1 + "a"`, [PIntAddFirst] `"a" + TRUE`: typeErr (row 160).
theorem op_intAdd :
    allT [okV (ev (op PrimOp.intAdd [num 2, num 3])) (int 5),
      isTypeErr (ev (op PrimOp.intAdd [num 1, strE 378])),
      isTypeErr (ev (op PrimOp.intAdd [strE 378, tt]))] = true := rfl
-- [PIntSubNonInt] `TRUE - 1`.
theorem op_intSub :
    allT [okV (ev (op PrimOp.intSub [num 2, num 3])) (int (-1)),
      isTypeErr (ev (op PrimOp.intSub [tt, num 1]))] = true := rfl
-- [PIntMulNonInt] `2 * {1}`.
theorem op_intMul :
    allT [okV (ev (op PrimOp.intMul [num 2, num 3])) (int 6),
      isTypeErr (ev (op PrimOp.intMul [num 2, setE [num 1]]))] = true := rfl
-- [PIntDivNonInt] `"a" \div 0`: the operand kind is checked before the zero divisor.
theorem op_intDiv :
    allT [okV (ev (op PrimOp.intDiv [num 7, num 2])) (int 3),
      isTypeErr (ev (op PrimOp.intDiv [strE 378, num 0]))] = true := rfl
-- [PIntModNonInt] `5 % "a"`.
theorem op_intMod :
    allT [okV (ev (op PrimOp.intMod [num 7, num 3])) (int 1),
      isTypeErr (ev (op PrimOp.intMod [num 5, strE 378]))] = true := rfl
-- [PIntNegNonInt] `-"a"`.
theorem op_intNeg :
    allT [okV (ev (neg (num 3))) (int (-3)), isTypeErr (ev (neg (strE 378)))] = true := rfl
-- [PIntCmp] `<<1 < 2, 2 <= 2, 3 > 2, 2 >= 3, -1 < -2>>` = <<TRUE, TRUE, TRUE, FALSE, FALSE>>;
-- [PIntLtNonInt] `1 < "a"`, [PIntLeNonInt] `"a" <= 1`, [PIntGtNonInt] `TRUE > 1`,
-- [PIntGeNonInt] `1 >= {}`: typeErr (row 161).
theorem op_intLt :
    allT [okV (ev (op PrimOp.intLt [num 1, num 2])) vT,
      okV (ev (op PrimOp.intLt [neg (num 1), neg (num 2)])) vF,
      isTypeErr (ev (op PrimOp.intLt [num 1, strE 378]))] = true := rfl
theorem op_intLe :
    allT [okV (ev (op PrimOp.intLe [num 2, num 2])) vT,
      isTypeErr (ev (op PrimOp.intLe [strE 378, num 1]))] = true := rfl
theorem op_intGt :
    allT [okV (ev (op PrimOp.intGt [num 3, num 2])) vT,
      isTypeErr (ev (op PrimOp.intGt [tt, num 1]))] = true := rfl
theorem op_intGe :
    allT [okV (ev (op PrimOp.intGe [num 2, num 3])) vF,
      isTypeErr (ev (op PrimOp.intGe [num 1, setE []]))] = true := rfl
-- [PIntCmp] as one tuple, the probe's own expression.
theorem probe_PIntCmp :
    okV (ev (tupE [op PrimOp.intLt [num 1, num 2], op PrimOp.intLe [num 2, num 2],
      op PrimOp.intGt [num 3, num 2], op PrimOp.intGe [num 2, num 3],
      op PrimOp.intLt [neg (num 1), neg (num 2)]])) (tup [vT, vT, vT, vF, vF]) = true := rfl
-- [PIntPow] `<<2 ^ 10, (-2) ^ 3, 0 ^ 3, 5 ^ 0>>` = <<1024, -8, 0, 1>>; [PIntPowZeroZero]
-- `0 ^ 0` typeErr (row 153, B1A-D85); [PIntPowNonInt] `"a" ^ 2` typeErr (row 160).
theorem op_intPow :
    allT [okV (ev (tupE [op PrimOp.intPow [num 2, num 10], op PrimOp.intPow [neg (num 2), num 3],
        op PrimOp.intPow [num 0, num 3], op PrimOp.intPow [num 5, num 0]]))
        (tup [int 1024, int (-8), int 0, int 1]),
      isTypeErr (ev (op PrimOp.intPow [num 0, num 0])),
      isTypeErr (ev (op PrimOp.intPow [strE 378, num 2]))] = true := rfl
-- natSuccU and natSatU (B1A-D12): unbounded in a tlc32 Spec (no TLA+ syntax maps to them,
-- 10:166); a non-integer operand typeErr (B1A-D12's reading).
theorem op_natSuccU :
    allT [okV (ev (op PrimOp.natSuccU [num 2147483647])) (int 2147483648),
      isTypeErr (ev (op PrimOp.natSuccU [tt]))] = true := rfl
theorem op_natSatU :
    allT [okV (ev (op PrimOp.natSatU [num 2, num 5])) (int 3),
      okV (ev (op PrimOp.natSatU [num 5, num 5])) (int 5),
      okV (ev (op PrimOp.natSatU [num 7, num 5])) (int 5),
      isTypeErr (ev (op PrimOp.natSatU [num 1, tt]))] = true := rfl

-- ---- Batch B, PR-int-probes, through the evaluator: one fact per INDEX row ----

-- `-2147483647 - 1`, the probes' INT_MIN.
def intMin : Expr := op PrimOp.intSub [neg (num 2147483647), num 1]
def dv (a b : Expr) : Expr := op PrimOp.intDiv [a, b]
def md (a b : Expr) : Expr := op PrimOp.intMod [a, b]

theorem probe_IntDivMinNegOne : isUnmodeled (ev (dv intMin (neg (num 1)))) Code.intDivWrap = true := rfl
theorem probe_IntDivNegPos : okV (ev (dv (neg (num 7)) (num 2))) (int (-4)) = true := rfl
theorem probe_IntDivPosNeg : okV (ev (dv (num 7) (neg (num 2)))) (int (-4)) = true := rfl
theorem probe_IntDivNegNeg : okV (ev (dv (neg (num 7)) (neg (num 2)))) (int 3) = true := rfl
theorem probe_IntDivMinTwo : okV (ev (dv intMin (num 2))) (int (-1073741824)) = true := rfl
theorem probe_IntDivMinNegTwo : okV (ev (dv intMin (neg (num 2)))) (int 1073741824) = true := rfl
theorem probe_IntDivMinThree : okV (ev (dv intMin (num 3))) (int (-715827883)) = true := rfl
theorem probe_IntDivZero : isDivZero (ev (dv (num 7) (num 0))) = true := rfl
theorem probe_IntModNeg : okV (ev (md (neg (num 7)) (num 2))) (int 1) = true := rfl
theorem probe_IntModZeroDivisor : isDivZero (ev (md (num 7) (num 0))) = true := rfl
theorem probe_IntModNegDivisor : isDivZero (ev (md (num 7) (neg (num 2)))) = true := rfl
theorem probe_IntModMinTwo : okV (ev (md intMin (num 2))) (int 0) = true := rfl
theorem probe_IntModMinThree : okV (ev (md intMin (num 3))) (int 1) = true := rfl
theorem probe_IntModMinNegTwo : isDivZero (ev (md intMin (neg (num 2)))) = true := rfl
theorem probe_IntModMinNegOne : isDivZero (ev (md intMin (neg (num 1)))) = true := rfl
theorem probe_IntNegMin : isOverflow (ev (neg intMin)) = true := rfl
theorem probe_IntAddMax : isOverflow (ev (op PrimOp.intAdd [num 2147483647, num 1])) = true := rfl
theorem probe_IntAddMin : isOverflow (ev (op PrimOp.intAdd [intMin, neg (num 1)])) = true := rfl
theorem probe_IntAddMaxExact :
    okV (ev (op PrimOp.intAdd [num 2147483646, num 1])) (int 2147483647) = true := rfl
theorem probe_IntSubMin : isOverflow (ev (op PrimOp.intSub [intMin, num 1])) = true := rfl
theorem probe_IntSubMaxNegOne :
    isOverflow (ev (op PrimOp.intSub [num 2147483647, neg (num 1)])) = true := rfl
theorem probe_IntSubMinExact : okV (ev intMin) (int (-2147483648)) = true := rfl
theorem probe_IntMulPosOverflow : isOverflow (ev (op PrimOp.intMul [num 46341, num 46341])) = true := rfl
theorem probe_IntMulNegOverflow :
    isOverflow (ev (op PrimOp.intMul [num 46341, neg (num 46341)])) = true := rfl
theorem probe_IntMulMinNegOne : isOverflow (ev (op PrimOp.intMul [intMin, neg (num 1)])) = true := rfl
theorem probe_IntMulMinExact :
    okV (ev (op PrimOp.intMul [neg (num 65536), num 32768])) (int (-2147483648)) = true := rfl
theorem probe_IntPowOverflow : isOverflow (ev (op PrimOp.intPow [num 2, num 31])) = true := rfl
theorem probe_IntPowNegExp : isTypeErr (ev (op PrimOp.intPow [num 2, neg (num 1)])) = true := rfl
-- IntLitOutOfRange `2147483648` and IntLitNegMin `-2147483648` (the unary minus of that
-- literal): TLC refuses the literal (overflow, row 70); the EP's Spec.wf refuses it
-- (model.int-literal-range, 10:678, B1A-D90), and the negation of an in-range INT_MIN is
-- INT_MIN's own value.
def spInv (inv : Expr) : Spec :=
  Spec.mk 1 IntMode.tlc32 [] [] [] [] [] (Act.conj []) (Act.conj []) [] [inv] [] [] true
    ChoiceMode.none
theorem probe_IntLitOutOfRange :
    allT [Bool.not (Spec.wf (spInv (num 2147483648))), Spec.wf (spInv (num 2147483647))] = true := rfl
theorem probe_IntLitNegMin :
    allT [Bool.not (Spec.wf (spInv (neg (num 2147483648)))), Spec.wf (spInv intMin)] = true := rfl

-- ---- Equality, IF's test, Assert (B1A-D87, B1A-D97) ----

-- [PNe] `<<1 # 2, {1} # {1}>>` = <<TRUE, FALSE>>; [PNeStrInt] `"a" # 1` incomparable (row 200).
theorem op_valueEq :
    allT [okV (ev (op PrimOp.valueEq [setE [num 1], setE [num 1]])) vT,
      okV (ev (op PrimOp.valueEq [num 1, num 2])) vF,
      isIncomparable (ev (op PrimOp.valueEq [strE 378, num 1]))] = true := rfl
theorem op_valueNe :
    allT [okV (ev (tupE [op PrimOp.valueNe [num 1, num 2], op PrimOp.valueNe [setE [num 1], setE [num 1]]]))
        (tup [vT, vF]),
      isIncomparable (ev (op PrimOp.valueNe [strE 378, num 1]))] = true := rfl
-- value.as_bool: a Boolean, else typeErr (K2 v2.1 Q-K2-14; TLC's land/lor/implies on a
-- non-Boolean second operand, the truth tables below).
theorem op_valueAsBool :
    allT [okV (ev (op PrimOp.valueAsBool [ff])) vF,
      isTypeErr (ev (op PrimOp.valueAsBool [num 1]))] = true := rfl
-- [PAssertTrue] `Assert(TRUE, "m")` TRUE ("m" is the token `m`, rank 1); [PAssertNonBool]
-- `Assert(1, "m")` and [PAssertFalseNonStr] `Assert(FALSE, 3)` raise assertFailed (row 50;
-- TLC treats any non-TRUE first argument as FALSE); the argument is the message's rank, 0
-- for a non-string message (B1A-D97).
theorem op_assert :
    allT [okV (ev (op PrimOp.assert [tt, strE 1])) vT,
      isAssertFailed (ev (op PrimOp.assert [num 1, strE 1])) 1,
      isAssertFailed (ev (op PrimOp.assert [ff, num 3])) 0] = true := rfl

-- ---- Records and functions ----

-- [PRecGet] `[a |-> 1, b |-> 2].b` = 2 (a 378, b 380); [PRecGetMissing] `[a |-> 1].b`
-- notInDomain (row 103); [PRecGetNonFn] `r.a` with r = 3 typeErr (row 167); [PRecGetTuple]
-- `<<1, 2>>.a` refused (row 105: TLC's class depends on how it holds the function).
theorem op_recGet :
    allT [okV (ev (op (PrimOp.recGet 380) [op (PrimOp.recNew [378, 380]) [num 1, num 2]])) (int 2),
      isNotInDomain (ev (op (PrimOp.recGet 380) [op (PrimOp.recNew [378]) [num 1]])),
      isTypeErr (ev (op (PrimOp.recGet 378) [num 3])),
      isRefused (ev (op (PrimOp.recGet 378) [tupE [num 1, num 2]]))] = true := rfl
-- [PRecWith] `[[a |-> 1, b |-> 2] EXCEPT !.a = 5]` = [a |-> 5, b |-> 2]; [PRecWithMissing]
-- `[[a |-> 1] EXCEPT !.b = 5]` = [a |-> 1] (TLC warns and leaves it unchanged).
theorem op_recWith :
    allT [okV (ev (op (PrimOp.recWith 378) [op (PrimOp.recNew [378, 380]) [num 1, num 2], num 5]))
        (Value.fn [(Value.str 378, int 5), (Value.str 380, int 2)]),
      okV (ev (op (PrimOp.recWith 380) [op (PrimOp.recNew [378]) [num 1], num 5]))
        (Value.fn [(Value.str 378, int 1)])] = true := rfl
-- [PRecNew] `[b |-> 1, a |-> 2]` = [a |-> 2, b |-> 1]: fields ordered by rank (b 378, a 380).
theorem op_recNew :
    allT [okV (ev (op (PrimOp.recNew [378, 380]) [num 1, num 2]))
        (Value.fn [(Value.str 378, int 1), (Value.str 380, int 2)]),
      okV (ev (op (PrimOp.recNew [380, 378]) [num 2, num 1]))
        (Value.fn [(Value.str 378, int 1), (Value.str 380, int 2)])] = true := rfl
-- [PFnApply] `<<5, 6>>[2]` = 6; [PFnApplyOut] `<<5, 6>>[3]`, [PFnApplyZero] `<<5, 6>>[0]`
-- notInDomain (row 101); [PFnApplyNonFn] `f[1]` with f = 3 typeErr (row 163); [PFnApplyRec]
-- `[a |-> 1]["a"]` = 1; [PFnApplyRecMissing] `[a |-> 1]["b"]` notInDomain (row 102);
-- [PFnApplyKind] `<<5>>["a"]` refused (row 104).
theorem op_funcApply :
    allT [okV (ev (op PrimOp.funcApply [tupE [num 5, num 6], num 2])) (int 6),
      isNotInDomain (ev (op PrimOp.funcApply [tupE [num 5, num 6], num 3])),
      isNotInDomain (ev (op PrimOp.funcApply [tupE [num 5, num 6], num 0])),
      isTypeErr (ev (op PrimOp.funcApply [num 3, num 1])),
      okV (ev (op PrimOp.funcApply [op (PrimOp.recNew [378]) [num 1], strE 378])) (int 1),
      isNotInDomain (ev (op PrimOp.funcApply [op (PrimOp.recNew [378]) [num 1], strE 380])),
      isRefused (ev (op PrimOp.funcApply [tupE [num 5], strE 378]))] = true := rfl
-- seq.index and tuple.get are `s[i]` (TLC's function application): as [PFnApply],
-- [PFnApplyOut]; [PArithValues] `<<5, 6>>[1]` = 5.
theorem op_seqIndex :
    allT [okV (ev (op PrimOp.seqIndex [tupE [num 5, num 6], num 1])) (int 5),
      isNotInDomain (ev (op PrimOp.seqIndex [tupE [num 5, num 6], num 3]))] = true := rfl
theorem op_tupleGet :
    allT [okV (ev (op (PrimOp.tupleGet 2) [tupE [num 5, num 6]])) (int 6),
      isNotInDomain (ev (op (PrimOp.tupleGet 3) [tupE [num 5, num 6]]))] = true := rfl
-- [PFnExcept] `[<<5, 6>> EXCEPT ![1] = 7]` = <<7, 6>>; [PFnExceptOut] `![3]` leaves it
-- unchanged; [PFnExceptNonFn] EXCEPT on 3 typeErr (row 166).
theorem op_funcExcept :
    allT [okV (ev (op PrimOp.funcExcept [tupE [num 5, num 6], num 1, num 7])) (tup [int 7, int 6]),
      okV (ev (op PrimOp.funcExcept [tupE [num 5, num 6], num 3, num 7])) (tup [int 5, int 6]),
      isTypeErr (ev (op PrimOp.funcExcept [num 3, num 1, num 7]))] = true := rfl
-- [PFnDomain] `<<DOMAIN <<5, 6>>, DOMAIN [b |-> 1, a |-> 2], DOMAIN <<>>>>` =
-- <<{1, 2}, {"a", "b"}, {}>> (b 382, a 384 in its dump); [PFnDomainNonFn] `DOMAIN 3`
-- typeErr (row 164).
theorem op_funcDomain :
    allT [okV (ev (tupE [op PrimOp.funcDomain [tupE [num 5, num 6]],
        op PrimOp.funcDomain [op (PrimOp.recNew [382, 384]) [num 1, num 2]],
        op PrimOp.funcDomain [tupE []]]))
        (tup [setV [int 1, int 2], setV [Value.str 382, Value.str 384], setV []]),
      isTypeErr (ev (op PrimOp.funcDomain [num 3]))] = true := rfl
-- tuple.new: <<a, b>> is the function on 1..2 ([PArithValues]: <<5, TRUE>>, <<>>).
theorem op_tupleNew :
    allT [okV (ev (tupE [num 5, tt])) (Value.fn [(int 1, int 5), (int 2, vT)]),
      okV (ev (tupE [])) (Value.fn [])] = true := rfl

-- ---- Sets ----

-- [PSetIn] `<<2 \in {1, 2}, 3 \in {1, 2}, {} \in {{}}>>` = <<TRUE, FALSE, TRUE>>;
-- [PSetInNonSet] `1 \in 3`, [PSetInBool] `1 \in TRUE`, [PSetInStr] `1 \in "a"`, [PSetInMv]
-- `1 \in M`, [PSetInTmv] `1 \in T`, [PSetInFcnRcd] `1 \in (2 :> 3)` typeErr (row 162);
-- [PSetInTuple] `1 \in <<1>>` (row 142), [PSetInRec] `1 \in [a |-> 1]` (row 143) typeErr.
theorem op_setIn :
    allT [okV (ev (tupE [op PrimOp.setIn [num 2, setE [num 1, num 2]],
        op PrimOp.setIn [num 3, setE [num 1, num 2]], op PrimOp.setIn [setE [], setE [setE []]]]))
        (tup [vT, vF, vT]),
      isTypeErr (ev (op PrimOp.setIn [num 1, num 3])),
      isTypeErr (ev (op PrimOp.setIn [num 1, tt])),
      isTypeErr (ev (op PrimOp.setIn [num 1, strE 378])),
      isTypeErr (ev (op PrimOp.setIn [num 1, mE])),
      isTypeErr (ev (op PrimOp.setIn [num 1, tE])),
      isTypeErr (ev (op PrimOp.setIn [num 1, Expr.lit (Value.fn [(int 2, int 3)])])),
      isTypeErr (ev (op PrimOp.setIn [num 1, tupE [num 1]])),
      isTypeErr (ev (op PrimOp.setIn [num 1, op (PrimOp.recNew [378]) [num 1]]))] = true := rfl
-- [PSetEnumNorm] `{3, 1, 2, 1}` = {1, 2, 3}; [PSetEnumTmv] `{T, 1}` raises incomparable when
-- TLC normalizes it (at fingerprinting, row 201), but [PSetInTmvFirst] `T \in {T, 1}` is TRUE
-- (TLC searches the literal unnormalized) and [PSetInTmvSecond] `T \in {1, T}` raises: the
-- EP, whose sets are canonical, refuses all three (B1A-D96).
theorem op_setEnum :
    allT [okV (ev (setE [num 3, num 1, num 2, num 1])) (setV [int 1, int 2, int 3]),
      isRefused (ev (setE [tE, num 1])),
      isRefused (ev (op PrimOp.setIn [tE, setE [tE, num 1]])),
      isRefused (ev (op PrimOp.setIn [tE, setE [num 1, tE]]))] = true := rfl
-- [PSoaTmv] `T \in {IF b THEN 1 ELSE T : b \in BOOLEAN}` is TRUE in TLC (the set-of-all is
-- built unnormalized); the EP refuses it (B1A-D96).
theorem set_of_all_defers :
    isRefused (ev (op PrimOp.setIn [tE, Expr.quant QKind.qMap
      [Expr.lit (setV [vF, vT])] (Expr.ite (Expr.bvar 0) (num 1) tE)])) = true := rfl
-- [PSetUnion] `{3, 1} \cup {2, 1}` = {1, 2, 3}; [PSetUnionTmv] `T \in ({T} \cup {1})`
-- (incomparable in TLC) refused (B1A-D96); [PSetUnionNonSet] `{1} \cup 3` raises only when
-- enumerated ([PSetUnionNonSetMem] `1 \in ({1} \cup 3)` is TRUE: a lazy SetCupValue), so
-- the EP's union of a non-set is pending (B1A-17b's lazy.<op>, B1A-D22).
theorem op_setUnion :
    allT [okV (ev (op PrimOp.setUnion [setE [num 3, num 1], setE [num 2, num 1]]))
        (setV [int 1, int 2, int 3]),
      isRefused (ev (op PrimOp.setIn [tE, op PrimOp.setUnion [setE [tE], setE [num 1]]])),
      isPending (ev (op PrimOp.setUnion [setE [num 1], num 3]))] = true := rfl
-- [PSetInsert] `{3, 1} \cup {2}` = {1, 2, 3}.
theorem op_setInsert :
    allT [okV (ev (op PrimOp.setInsert [setE [num 3, num 1], num 2])) (setV [int 1, int 2, int 3]),
      isPending (ev (op PrimOp.setInsert [num 3, num 2]))] = true := rfl
-- [PSetInter] `{3, 1, 2} \cap {2, 4, 3}` = {2, 3}; [PSetInterNonSet] `{1} \cap 3` typeErr
-- (row 162); [PSetInterTuple] `{1} \cap <<1>>` typeErr (row 142).
theorem op_setIntersect :
    allT [okV (ev (op PrimOp.setIntersect [setE [num 3, num 1, num 2], setE [num 2, num 4, num 3]]))
        (setV [int 2, int 3]),
      isTypeErr (ev (op PrimOp.setIntersect [setE [num 1], num 3])),
      isTypeErr (ev (op PrimOp.setIntersect [setE [num 1], tupE [num 1]]))] = true := rfl
-- [PSetDiff] `{3, 1, 2} \ {2}` = {1, 3}; [PSetDiffNonSet] `{1} \ 3` typeErr (row 162);
-- [PSetDiffRec] `{1} \ [a |-> 1]` typeErr (row 143).
theorem op_setDiff :
    allT [okV (ev (op PrimOp.setDiff [setE [num 3, num 1, num 2], setE [num 2]])) (setV [int 1, int 3]),
      isTypeErr (ev (op PrimOp.setDiff [setE [num 1], num 3])),
      isTypeErr (ev (op PrimOp.setDiff [setE [num 1], op (PrimOp.recNew [378]) [num 1]]))] = true := rfl
-- [PSetCard] `Cardinality({3, 1, 3})` = 2; [PSetCardNonSet] `Cardinality(3)` and
-- [PSetCardInf] `Cardinality(Nat)` notEnumerable (row 126). [S -> T] with an infinite operand,
-- TLC's SetOfFcnsValue.size(): [PSetCardFnSetEmptyDom] `Cardinality([{} -> Nat])` = 1,
-- [PSetCardFnSetOneRng] `Cardinality([Nat -> {7}])` = 1, [PSetCardFnSetEmptyRng]
-- `Cardinality([Nat -> {}])` = 0; an infinite operand's size() typeErr (row 160):
-- [PSetCardFnSetInf] `[{1} -> Nat]`, [PSetCardFnSetNatDom] `[Nat -> {1, 2}]`,
-- [PSetCardFnSetIntRng] `[{1} -> Int]`, [PSetCardFnSetIntDom] `[Int -> {1, 2}]`,
-- [PSetCardFnSetStrRng] `[{1} -> STRING]`, [PSetCardFnSetStrDom] `[STRING -> {1, 2}]`.
theorem op_setCard :
    allT [okV (ev (op PrimOp.setCard [setE [num 3, num 1, num 3]])) (int 2),
      isNotEnumerable (ev (op PrimOp.setCard [num 3])),
      isNotEnumerable (ev (op PrimOp.setCard [natE])),
      okV (ev (op PrimOp.setCard [fnSetE (setE []) natE])) (int 1),
      okV (ev (op PrimOp.setCard [fnSetE natE (setE [num 7])])) (int 1),
      okV (ev (op PrimOp.setCard [fnSetE natE (setE [])])) (int 0),
      isTypeErr (ev (op PrimOp.setCard [fnSetE (setE [num 1]) natE])),
      isTypeErr (ev (op PrimOp.setCard [fnSetE natE (setE [num 1, num 2])])),
      isTypeErr (ev (op PrimOp.setCard [fnSetE (setE [num 1]) intE])),
      isTypeErr (ev (op PrimOp.setCard [fnSetE intE (setE [num 1, num 2])])),
      isTypeErr (ev (op PrimOp.setCard [fnSetE (setE [num 1]) strSetE])),
      isTypeErr (ev (op PrimOp.setCard [fnSetE strSetE (setE [num 1, num 2])]))] = true := rfl
-- [PSetSubseteq] `<<{1} \subseteq {1, 2}, {3} \subseteq {1, 2}>>` = <<TRUE, FALSE>>.
-- S not Enumerable is notEnumerable (row 127): [PSetSubseteqNonSet] `3 \subseteq {1}`,
-- [PSetSubseteqNat] `Nat \subseteq Int`, [PSetSubseteqInt] `Int \subseteq {}`,
-- [PSetSubseteqStr] `STRING \subseteq {}`, [PSetSubseteqSeq] `Seq({1}) \subseteq {}`,
-- [PSetSubseteqTuple] `<<1>> \subseteq {}`, [PSetSubseteqRec] `[a |-> 1] \subseteq {}` ("a"
-- is 378), [PSetSubseteqMv] `M \subseteq {}`. [S -> T] with an infinite operand is a
-- SetOfFcnsValue, which is Enumerable, and TLC enumerates it: [PSetSubseteqFnSetEmptyDom]
-- `[{} -> Nat] \subseteq {<<>>}` TRUE, [PSetSubseteqFnSetEmpty] `[{} -> Nat] \subseteq {}`
-- FALSE, [PSetSubseteqFnSetEmptyRng] `[Nat -> {}] \subseteq {}` TRUE,
-- [PSetSubseteqFnSetEmptyDomInt] `[{} -> Nat] \subseteq {1}` incomparable (row 200),
-- [PSetSubseteqFnSetNatRng] `[{1} -> Nat] \subseteq {<<1>>}` notEnumerable (row 119); the EP
-- answers each pending until B1A-17a/17b (B1A-D44 as amended by B1A-15 repair round 2).
theorem op_setSubseteq :
    allT [okV (ev (tupE [op PrimOp.setSubseteq [setE [num 1], setE [num 1, num 2]],
        op PrimOp.setSubseteq [setE [num 3], setE [num 1, num 2]]])) (tup [vT, vF]),
      isNotEnumerable (ev (op PrimOp.setSubseteq [num 3, setE [num 1]])),
      isNotEnumerable (ev (op PrimOp.setSubseteq [natE, intE])),
      isNotEnumerable (ev (op PrimOp.setSubseteq [intE, setE []])),
      isNotEnumerable (ev (op PrimOp.setSubseteq [strSetE, setE []])),
      isNotEnumerable (ev (op PrimOp.setSubseteq [seqOfE (setE [num 1]), setE []])),
      isNotEnumerable (ev (op PrimOp.setSubseteq [tupE [num 1], setE []])),
      isNotEnumerable (ev (op PrimOp.setSubseteq [op (PrimOp.recNew [378]) [num 1], setE []])),
      isNotEnumerable (ev (op PrimOp.setSubseteq [mE, setE []])),
      isPending (ev (op PrimOp.setSubseteq [fnSetE (setE []) natE, setE [tupE []]])),
      isPending (ev (op PrimOp.setSubseteq [fnSetE (setE []) natE, setE []])),
      isPending (ev (op PrimOp.setSubseteq [fnSetE (setE []) natE, setE [num 1]])),
      isPending (ev (op PrimOp.setSubseteq [fnSetE (setE [num 1]) natE, setE [tupE [num 1]]])),
      isPending (ev (op PrimOp.setSubseteq [fnSetE natE (setE []), setE []]))] = true := rfl
-- [PSetRange] `<<2..4, 3..1>>` = <<{2, 3, 4}, {}>>; [PSetRangeNonInt] `1.."a"` typeErr.
theorem op_setRange :
    allT [okV (ev (tupE [op PrimOp.setRange [num 2, num 4], op PrimOp.setRange [num 3, num 1]]))
        (tup [setV [int 2, int 3, int 4], setV []]),
      isTypeErr (ev (op PrimOp.setRange [num 1, strE 378]))] = true := rfl
-- [PSetBigUnion] `UNION {{1, 2}, {3}, {}}` = {1, 2, 3}. TLC builds UNION S lazily (a
-- UnionValue) unless S and its every element are SetEnumValues: [PSetBigUnionNatMem]
-- `0 \in UNION {Nat}` is TRUE and [PSetBigUnionIntMem] `1 \in UNION {1}` typeErr (row 162,
-- the element's own member()); enumerating one raises ([PSetBigUnionNonSet] `UNION {1}`, row
-- 129; [PSetBigUnionOfNonSet] `UNION 3`, row 124): all pending (B1A-17b's lazy.<op>).
theorem op_setBigUnion :
    allT [okV (ev (op PrimOp.setBigUnion [setE [setE [num 1, num 2], setE [num 3], setE []]]))
        (setV [int 1, int 2, int 3]),
      isPending (ev (op PrimOp.setBigUnion [setE [num 1]])),
      isPending (ev (op PrimOp.setIn [num 0, op PrimOp.setBigUnion [setE [natE]]])),
      isPending (ev (op PrimOp.setIn [num 1, op PrimOp.setBigUnion [setE [num 1]]])),
      isPending (ev (op PrimOp.setBigUnion [num 3]))] = true := rfl
-- [PSetIsFinite] `<<IsFiniteSet({1}), IsFiniteSet(Nat)>>` = <<TRUE, FALSE>>;
-- [PSetIsFiniteInt] Int and STRING FALSE; [PSetIsFiniteSeq] `Seq({})` TRUE;
-- [PSetIsFiniteSeqOne] `Seq({1})` FALSE; [PSetIsFiniteFn] `<<IsFiniteSet(<<1>>),
-- IsFiniteSet([a |-> 1]), IsFiniteSet(<<>>), IsFiniteSet(2 :> 3)>>` = <<TRUE, TRUE, TRUE,
-- TRUE>>; [PSetIsFiniteNonSet] `IsFiniteSet(3)`, [PSetIsFiniteBool] `TRUE`, [PSetIsFiniteStr]
-- `"a"`, [PSetIsFiniteMv] `M`, [PSetIsFiniteTmv] `T` typeErr (row 160).
theorem op_setIsFinite :
    allT [okV (ev (tupE [op PrimOp.setIsFinite [setE [num 1]], op PrimOp.setIsFinite [natE],
        op PrimOp.setIsFinite [intE], op PrimOp.setIsFinite [strSetE],
        op PrimOp.setIsFinite [seqOfE (setE [])], op PrimOp.setIsFinite [seqOfE (setE [num 1])]]))
        (tup [vT, vF, vF, vF, vT, vF]),
      okV (ev (tupE [op PrimOp.setIsFinite [tupE [num 1]],
        op PrimOp.setIsFinite [op (PrimOp.recNew [378]) [num 1]], op PrimOp.setIsFinite [tupE []],
        op PrimOp.setIsFinite [Expr.lit (Value.fn [(int 2, int 3)])]])) (tup [vT, vT, vT, vT]),
      isTypeErr (ev (op PrimOp.setIsFinite [num 3])),
      isTypeErr (ev (op PrimOp.setIsFinite [tt])),
      isTypeErr (ev (op PrimOp.setIsFinite [strE 378])),
      isTypeErr (ev (op PrimOp.setIsFinite [mE])),
      isTypeErr (ev (op PrimOp.setIsFinite [tE]))] = true := rfl
-- SUBSET, \X, record sets and [S -> T] over finite sets are lazy sets (SetGen), B1A-17a;
-- [S -> T] with an infinite operand is `infSet fnSet [S, T]` (B1A-D44).
theorem op_setPowerset : isPending (ev (op PrimOp.setPowerset [setE [num 1]])) = true := rfl
theorem op_setProduct :
    isPending (ev (op PrimOp.setProduct [setE [num 1], setE [num 2]])) = true := rfl
theorem op_recSetOf : isPending (ev (op (PrimOp.recSetOf [378]) [setE [num 1]])) = true := rfl
-- [PSetExFnSetEmptyDom] `\E f \in [{} -> Nat] : f = <<>>` is TRUE: TLC enumerates a
-- SetOfFcnsValue whatever its operands, so a quantifier over an `infSet fnSet` is pending
-- with the lazy sets (`Tlc.domainOf`, B1A-17a).
theorem quant_fn_set_pending :
    isPending (ev (Expr.quant QKind.qEx [fnSetE (setE []) natE]
      (op PrimOp.valueEq [Expr.bvar 0, tupE []]))) = true := rfl
theorem op_funcSet :
    allT [okV (ev (fnSetE (setE [num 1]) natE))
        (Value.infSet InfKind.fnSet [setV [int 1], Value.infSet InfKind.nat []]),
      isPending (ev (fnSetE (setE [num 1]) (setE [num 2])))] = true := rfl
-- Seq(S) is `infSet seqOf [S]` (B1A-D44), built without error whatever S is ([PSeqSetNonSet]
-- `Seq(3) = Seq(3)`).
theorem op_seqSet :
    allT [okV (ev (seqOfE (setE [num 1]))) (Value.infSet InfKind.seqOf [setV [int 1]]),
      okV (ev (seqOfE (num 3))) (Value.infSet InfKind.seqOf [int 3])] = true := rfl

-- ---- Membership by kind (B1A-D44) ----

-- [PSetInInf] `<<3 \in Nat, -1 \in Nat, -1 \in Int, "a" \in STRING>>` = <<TRUE, FALSE, TRUE,
-- TRUE>>; [PSetInNatMv] `M \in Nat` FALSE; [PSetInIntKinds] `<<M \in Int, M \in STRING>>`
-- = <<FALSE, FALSE>>; [PSetInNatTmv], [PSetInIntTmv], [PSetInStringTmv] a typed model value
-- incomparable (row 203); [PSetInNatStr] `"a" \in Nat`, [PSetInIntStr] `"a" \in Int`,
-- [PSetInStringInt] `1 \in STRING` typeErr (row 162).
theorem mem_nat_int_string :
    allT [okV (ev (tupE [op PrimOp.setIn [num 3, natE], op PrimOp.setIn [neg (num 1), natE],
        op PrimOp.setIn [neg (num 1), intE], op PrimOp.setIn [strE 378, strSetE]]))
        (tup [vT, vF, vT, vT]),
      okV (ev (tupE [op PrimOp.setIn [mE, natE], op PrimOp.setIn [mE, intE],
        op PrimOp.setIn [mE, strSetE]])) (tup [vF, vF, vF]),
      isIncomparable (ev (op PrimOp.setIn [tE, natE])),
      isIncomparable (ev (op PrimOp.setIn [tE, intE])),
      isIncomparable (ev (op PrimOp.setIn [tE, strSetE])),
      isTypeErr (ev (op PrimOp.setIn [strE 378, natE])),
      isTypeErr (ev (op PrimOp.setIn [strE 378, intE])),
      isTypeErr (ev (op PrimOp.setIn [num 1, strSetE]))] = true := rfl
-- [PSetInSeq] `<<<<1>> \in Seq({1}), <<1, 2>> \in Seq({1}), <<>> \in Seq({1})>>` = <<TRUE,
-- FALSE, TRUE>>; [PSetInSeqMv] `M \in Seq({1})` FALSE; [PSetInSeqRec] `[a |-> 1] \in
-- Seq({1})`, [PSetInSeqNonSeq] `3 \in Seq({1})`, [PSetInSeqNonSetBase] `<<1>> \in Seq(3)`
-- typeErr (row 162).
theorem mem_seq :
    allT [okV (ev (tupE [op PrimOp.setIn [tupE [num 1], seqOfE (setE [num 1])],
        op PrimOp.setIn [tupE [num 1, num 2], seqOfE (setE [num 1])],
        op PrimOp.setIn [tupE [], seqOfE (setE [num 1])]])) (tup [vT, vF, vT]),
      okV (ev (op PrimOp.setIn [mE, seqOfE (setE [num 1])])) vF,
      isTypeErr (ev (op PrimOp.setIn [op (PrimOp.recNew [378]) [num 1], seqOfE (setE [num 1])])),
      isTypeErr (ev (op PrimOp.setIn [num 3, seqOfE (setE [num 1])])),
      isTypeErr (ev (op PrimOp.setIn [tupE [num 1], seqOfE (num 3)]))] = true := rfl
-- [PFnSetInfMem] `<<<<1>> \in [{1} -> Nat], <<-1>> \in [{1} -> Nat]>>` = <<TRUE, FALSE>>;
-- [PFnSetInfRecMem] `[a |-> 1] \in [{1} -> Nat]` and [PFnSetInfDomMem] `<<1>> \in [Nat ->
-- Nat]` raise incomparable comparing the domains (row 200): refused (B1A-D96);
-- [PFnSetInfNonFn] `3 \in [{1} -> Nat]` typeErr (row 157).
theorem mem_fn_set :
    allT [okV (ev (tupE [op PrimOp.setIn [tupE [num 1], fnSetE (setE [num 1]) natE],
        op PrimOp.setIn [tupE [neg (num 1)], fnSetE (setE [num 1]) natE]])) (tup [vT, vF]),
      isRefused (ev (op PrimOp.setIn [op (PrimOp.recNew [378]) [num 1], fnSetE (setE [num 1]) natE])),
      isRefused (ev (op PrimOp.setIn [tupE [num 1], fnSetE natE natE])),
      isTypeErr (ev (op PrimOp.setIn [num 3, fnSetE (setE [num 1]) natE]))] = true := rfl

-- ---- Sequences ----

-- [PSeqLen] `<<Len(<<5, 6>>), Len(<<>>)>>` = <<2, 0>>; [PSeqLenNonSeq] `Len(3)`,
-- [PSeqLenRec] `Len([a |-> 1])` typeErr (row 168). A string operand is pending (TLC reads a
-- string as a sequence of characters: runtime strings, 10:678).
theorem op_seqLen :
    allT [okV (ev (tupE [op PrimOp.seqLen [tupE [num 5, num 6]], op PrimOp.seqLen [tupE []]]))
        (tup [int 2, int 0]),
      isTypeErr (ev (op PrimOp.seqLen [num 3])),
      isTypeErr (ev (op PrimOp.seqLen [op (PrimOp.recNew [378]) [num 1]])),
      isPending (ev (op PrimOp.seqLen [strE 378]))] = true := rfl
-- [PSeqHeadTail] `<<Head(<<5, 6>>), Tail(<<5, 6>>)>>` = <<5, <<6>>>>; Head(<<>>) notInDomain
-- (row 110, w1-review-fixes VExceptLaterPoolKeyHead); [PSeqTailEmpty] `Tail(<<>>)` notInDomain
-- (row 111); [PSeqHeadNonSeq] `Head(3)`, [PSeqTailNonSeq] `Tail(3)` typeErr (row 168).
theorem op_seqHead :
    allT [okV (ev (op PrimOp.seqHead [tupE [num 5, num 6]])) (int 5),
      isNotInDomain (ev (op PrimOp.seqHead [tupE []])),
      isTypeErr (ev (op PrimOp.seqHead [num 3]))] = true := rfl
theorem op_seqTail :
    allT [okV (ev (op PrimOp.seqTail [tupE [num 5, num 6]])) (tup [int 6]),
      isNotInDomain (ev (op PrimOp.seqTail [tupE []])),
      isTypeErr (ev (op PrimOp.seqTail [num 3]))] = true := rfl
-- [PSeqAppend] `Append(<<5>>, 6)` = <<5, 6>>; [PSeqAppendNonSeq] `Append(3, 6)` typeErr
-- (row 169).
theorem op_seqAppend :
    allT [okV (ev (op PrimOp.seqAppend [tupE [num 5], num 6])) (tup [int 5, int 6]),
      isTypeErr (ev (op PrimOp.seqAppend [num 3, num 6]))] = true := rfl
-- [PSeqConcat] `<<5>> \o <<6, 7>>` = <<5, 6, 7>>; [PSeqConcatNonSeq] `<<5>> \o 3`,
-- [PSeqConcatFirstNonSeq] `3 \o <<5>>` typeErr (row 169).
theorem op_seqConcat :
    allT [okV (ev (op PrimOp.seqConcat [tupE [num 5], tupE [num 6, num 7]])) (tup [int 5, int 6, int 7]),
      isTypeErr (ev (op PrimOp.seqConcat [tupE [num 5], num 3])),
      isTypeErr (ev (op PrimOp.seqConcat [num 3, tupE [num 5]]))] = true := rfl
-- [PSeqSubSeq] `<<SubSeq(<<5, 6, 7>>, 2, 3), SubSeq(<<5, 6, 7>>, 3, 2)>>` = <<<<6, 7>>, <<>>>>;
-- [PSeqSubSeqLow] `SubSeq(<<5, 6, 7>>, 0, 2)`, [PSeqSubSeqHigh] `SubSeq(<<5, 6, 7>>, 2, 4)`
-- notInDomain (row 112); [PSeqSubSeqNonSeq] `SubSeq(3, 1, 1)`, [PSeqSubSeqNonInt]
-- `SubSeq(<<5>>, "a", 1)` typeErr (row 154).
def s567 : Expr := tupE [num 5, num 6, num 7]
theorem op_seqSubseq :
    allT [okV (ev (tupE [op PrimOp.seqSubseq [s567, num 2, num 3], op PrimOp.seqSubseq [s567, num 3, num 2]]))
        (tup [tup [int 6, int 7], tup []]),
      isNotInDomain (ev (op PrimOp.seqSubseq [s567, num 0, num 2])),
      isNotInDomain (ev (op PrimOp.seqSubseq [s567, num 2, num 4])),
      isTypeErr (ev (op PrimOp.seqSubseq [num 3, num 1, num 1])),
      isTypeErr (ev (op PrimOp.seqSubseq [tupE [num 5], strE 378, num 1]))] = true := rfl
-- [PSeqRemoveAt] `RemoveAt(<<5, 6, 7>>, 2)` = <<5, 7>>; [PSeqRemoveAtOut] `<<RemoveAt(<<5, 6,
-- 7>>, 4), RemoveAt(<<5, 6, 7>>, 0)>>` leaves s unchanged; [PSeqRemoveAtNonSeq]
-- `RemoveAt(3, 1)` typeErr (row 154, through SubSeq); [PSeqRemoveAtNonInt] `RemoveAt(<<5>>,
-- "a")` typeErr (row 160, `i-1`). Two past the end reaches SubSeq's own check (SequencesExt's
-- definition): notInDomain.
theorem op_seqRemoveAt :
    allT [okV (ev (op PrimOp.seqRemoveAt [s567, num 2])) (tup [int 5, int 7]),
      okV (ev (tupE [op PrimOp.seqRemoveAt [s567, num 4], op PrimOp.seqRemoveAt [s567, num 0]]))
        (tup [tup [int 5, int 6, int 7], tup [int 5, int 6, int 7]]),
      isTypeErr (ev (op PrimOp.seqRemoveAt [num 3, num 1])),
      isTypeErr (ev (op PrimOp.seqRemoveAt [tupE [num 5], strE 378])),
      isNotInDomain (ev (op PrimOp.seqRemoveAt [s567, num 5]))] = true := rfl

-- ---- Operand counts, binders, lazy operands (B1A-D95 amended) ----

-- A PrimOp with another number of operands than its own is `Tlc.illFormed` (fuel), and
-- Spec.wf refuses it (site tag 9); so is a quantifier with no binder (site tag 8; the B1A-14b
-- verifier's item 1). A lazy operand is a forcing row of B1A-16/17 (pending).
theorem prim_ill_formed :
    allT [isFuel (ev (op PrimOp.intAdd [num 1])),
      isFuel (ev (op PrimOp.valueEq [])),
      isFuel (ev (op (PrimOp.recNew [378, 380]) [num 1])),
      Bool.not (Spec.wf (spInv (op PrimOp.intAdd [num 1]))),
      Bool.not (Spec.wf (spInv (op PrimOp.setProduct [setE [num 1]]))),
      Spec.wf (spInv (op PrimOp.valueEq [num 1, num 1])),
      Spec.wf (spInv (setE [])),
      isFuel (ev (Expr.quant QKind.qEx [] tt)),
      isFuel (ev (Expr.quant QKind.qMap [] (num 1))),
      Bool.not (Spec.wf (spInv (Expr.quant QKind.qEx [] tt))),
      Bool.not (Spec.wf (spInv (Expr.quant QKind.qAll [] tt)))] = true := rfl
def isPendingX (r : Res XVal) : Bool :=
  @Res.rec XVal (fun _ => Bool) (fun _ => false)
    (fun f => @Fail.casesOn (fun _ => Bool) f false false false false false false false false
      false (fun _ => false) false false false (fun c => Nat.beq c Code.todo))
    r
theorem prim_lazy_operand_pending :
    isPendingX (evalX spP 64 false [] [int 0] [Option.some (XVal.lazySet (SetGen.ofVal (setV [int 1])))]
      (op PrimOp.setCard [Expr.nxt 0])) = true := rfl

-- ---- The truth tables of the Boolean encodings, through evalE (B1A-D11) ----
--
-- The rows of sanity/syntax.lean, unchanged: inputs TRUE, FALSE, a non-Boolean (1) and an
-- operand that raises (1 \div 0, divZero); expected outcomes TLC's (Tool.evalApplImpl,
-- opcodes 27, 36, 37, 38, 39), never the encoding's.

-- `resIs r s`: the same value (structurally) or an error of the same class.
def resIs (r s : Res Value) : Bool :=
  @Res.rec Value (fun _ => Bool)
    (fun v => @Res.rec Value (fun _ => Bool) (fun w => Value.beq v w) (fun _ => false) s)
    (fun e => @Res.rec Value (fun _ => Bool) (fun _ => false)
      (fun f => Nat.beq (failTag e) (failTag f)) s)
    r

def inT : Expr := tt
def inF : Expr := ff
def inN : Expr := num 1
def inE : Expr := op PrimOp.intDiv [num 1, num 0]
def oT : Res Value := Res.ok vT
def oF : Res Value := Res.ok vF
def oTE : Res Value := Res.error Fail.typeErr
def oDZ : Res Value := Res.error Fail.divZero

-- `row con a b r`: the encoding `con a b` evaluates (evalE) to r.
def row (con : Expr → Expr → Expr) (a b : Expr) (r : Res Value) : Bool := resIs (ev (con a b)) r

-- `table con rows`: every row (a, b, r) holds.
def table (con : Expr → Expr → Expr) (rows : List (Prod Expr (Prod Expr (Res Value)))) : Bool :=
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
  op PrimOp.valueEq [op PrimOp.valueAsBool [a], op PrimOp.valueAsBool [b]]
theorem naive_equiv_differs :
    Bool.and (row naiveEquiv inN inE oTE) (row Expr.equiv_ inN inE oDZ) = true := rfl

end Sanity
end Model
end Trust
