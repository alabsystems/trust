-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-10 sanity facts for Trust.Model.Value's core (model_prelude_kernel.rs,
-- sanity_files): elaborated after the whole model prelude, and every theorem below is
-- accepted by check_model_theorem (kernel re-check, constructive, axiom-free, audited).
-- Every fact is a Bool door closed by rfl (B1A-D54, TASK-STATE 4.8); the mutated-literal
-- doors of SANITY_MUTANTS must each be refuted (class Definite).
--
-- `probe_<Name>` states, for each integer probe of batch B (ty
-- reports/perf/2026-10-09-beyond-tla-b1a/probes/batch-B.txt, PR-int-probes), the EP's
-- value of the probe's own `x'` expression, built from the probe's TLA+ text operator by
-- operator (a literal is non-negative; `-e` is `intNeg`; `-2147483647 - 1` is how the
-- probes reach INT_MIN), under `IntMode.tlc32`. The expected value or class is TLC
-- 94d0c50's outcome in that row of INDEX.tsv: `counts 2 2` with the probe's MathResult
-- invariant pins the value, `error <class>` the class. That is TLC's class on 27 of the
-- 30; the other three are not TLC's outcome, each by a recorded ruling (DR-B1A-D26 (5) /
-- model.int-literal-range; corrected by B1A-11a): IntDivMinNegOne is the named refusal `unmodeled int.div-wrap`
-- (design 10:678; DR-B1A-D26 (5)), and IntLitOutOfRange / IntLitNegMin are refused
-- before evaluation (`model.int-literal-range`, a Spec.wf check of `inRange32`, design
-- 10:678), so their fact is that the literal 2147483648 is out of range.

namespace Trust
namespace Model
namespace Sanity

-- The probes' TLA+ integer syntax, evaluated by the EP's tlc32 operations.
def lit (n : Nat) : Res Int := Res.ok (Int.ofNat n)
def neg (r : Res Int) : Res Int := Res.bind r (fun a => intNeg IntMode.tlc32 a)
def op2 (f : Int → Int → Res Int) (r s : Res Int) : Res Int :=
  Res.bind r (fun a => Res.bind s (fun b => f a b))
def add (r s : Res Int) : Res Int := op2 (intAdd IntMode.tlc32) r s
def sub (r s : Res Int) : Res Int := op2 (intSub IntMode.tlc32) r s
def mul (r s : Res Int) : Res Int := op2 (intMul IntMode.tlc32) r s
def div (r s : Res Int) : Res Int := op2 (intDiv IntMode.tlc32) r s
def mod (r s : Res Int) : Res Int := op2 (intMod IntMode.tlc32) r s
def pow (r s : Res Int) : Res Int := op2 (intPow IntMode.tlc32) r s
-- `-2147483647 - 1`, the probes' INT_MIN.
def intMin : Res Int := sub (neg (lit 2147483647)) (lit 1)

-- Doors. `isOk r v`: r is `ok v`. `failTag`: a Fail's constructor index.
-- `isErr r f`: r is an error of f's constructor. `isUnmodeled r c`: r is
-- `unmodeled c`.
def isOk (r : Res Int) (v : Int) : Bool :=
  @Res.rec Int (fun _ => Bool) (fun a => intBeq a v) (fun _ => false) r
def failTag (f : Fail) : Nat :=
  @Fail.casesOn (fun _ => Nat) f 0 1 2 3 4 5 6 7 8 (fun _ => 9) 10 11 12 (fun _ => 13)
def isErr (r : Res Int) (f : Fail) : Bool :=
  @Res.rec Int (fun _ => Bool) (fun _ => false) (fun e => Nat.beq (failTag e) (failTag f)) r
def isUnmodeled (r : Res Int) (c : Nat) : Bool :=
  @Res.rec Int (fun _ => Bool) (fun _ => false)
    (fun e => @Fail.casesOn (fun _ => Bool) e false false false false false false false false
      false (fun _ => false) false false false (fun k => Nat.beq k c))
    r

-- ---- Batch B, PR-int-probes: one fact per INDEX row ----

theorem probe_IntDivMinNegOne : isUnmodeled (div intMin (neg (lit 1))) Code.intDivWrap = true := rfl
theorem probe_IntDivNegPos : isOk (div (neg (lit 7)) (lit 2)) (-4) = true := rfl
theorem probe_IntDivPosNeg : isOk (div (lit 7) (neg (lit 2))) (-4) = true := rfl
theorem probe_IntDivNegNeg : isOk (div (neg (lit 7)) (neg (lit 2))) 3 = true := rfl
theorem probe_IntDivMinTwo : isOk (div intMin (lit 2)) (-1073741824) = true := rfl
theorem probe_IntDivMinNegTwo : isOk (div intMin (neg (lit 2))) 1073741824 = true := rfl
theorem probe_IntDivMinThree : isOk (div intMin (lit 3)) (-715827883) = true := rfl
theorem probe_IntDivZero : isErr (div (lit 7) (lit 0)) Fail.divZero = true := rfl
theorem probe_IntModNeg : isOk (mod (neg (lit 7)) (lit 2)) 1 = true := rfl
theorem probe_IntModZeroDivisor : isErr (mod (lit 7) (lit 0)) Fail.divZero = true := rfl
theorem probe_IntModNegDivisor : isErr (mod (lit 7) (neg (lit 2))) Fail.divZero = true := rfl
theorem probe_IntModMinTwo : isOk (mod intMin (lit 2)) 0 = true := rfl
theorem probe_IntModMinThree : isOk (mod intMin (lit 3)) 1 = true := rfl
theorem probe_IntModMinNegTwo : isErr (mod intMin (neg (lit 2))) Fail.divZero = true := rfl
theorem probe_IntModMinNegOne : isErr (mod intMin (neg (lit 1))) Fail.divZero = true := rfl
theorem probe_IntNegMin : isErr (neg intMin) Fail.overflow = true := rfl
theorem probe_IntAddMax : isErr (add (lit 2147483647) (lit 1)) Fail.overflow = true := rfl
theorem probe_IntAddMin : isErr (add intMin (neg (lit 1))) Fail.overflow = true := rfl
theorem probe_IntAddMaxExact : isOk (add (lit 2147483646) (lit 1)) 2147483647 = true := rfl
theorem probe_IntSubMin : isErr (sub intMin (lit 1)) Fail.overflow = true := rfl
theorem probe_IntSubMaxNegOne : isErr (sub (lit 2147483647) (neg (lit 1))) Fail.overflow = true := rfl
theorem probe_IntSubMinExact : isOk (sub (neg (lit 2147483647)) (lit 1)) (-2147483648) = true := rfl
theorem probe_IntMulPosOverflow : isErr (mul (lit 46341) (lit 46341)) Fail.overflow = true := rfl
theorem probe_IntMulNegOverflow : isErr (mul (lit 46341) (neg (lit 46341))) Fail.overflow = true := rfl
theorem probe_IntMulMinNegOne : isErr (mul intMin (neg (lit 1))) Fail.overflow = true := rfl
theorem probe_IntMulMinExact : isOk (mul (neg (lit 65536)) (lit 32768)) (-2147483648) = true := rfl
theorem probe_IntPowOverflow : isErr (pow (lit 2) (lit 31)) Fail.overflow = true := rfl
theorem probe_IntPowNegExp : isErr (pow (lit 2) (neg (lit 1))) Fail.typeErr = true := rfl
theorem probe_IntLitOutOfRange : Bool.not (inRange32 2147483648) = true := rfl
-- IntLitNegMin's `-2147483648` is TLA+'s unary minus applied to the literal 2147483648 (TLC
-- raises "TLC can't handle a number this big" on the literal, before the negation), so its
-- refusal is the same literal check as IntLitOutOfRange's; the two facts are one statement
-- on purpose, and the negated value itself is in range (`range_min`).
theorem probe_IntLitNegMin : Bool.not (inRange32 2147483648) = true := rfl

-- ---- Range edges and the mode switch ----

theorem range_max : inRange32 2147483647 = true := rfl
theorem range_min : inRange32 (-2147483648) = true := rfl
theorem range_below_min : Bool.not (inRange32 (-2147483649)) = true := rfl
-- Unbounded mode is Clean's Int: no overflow, and INT_MIN \div -1 is 2^31.
theorem unbounded_add : isOk (intAdd IntMode.unbounded 2147483647 1) 2147483648 = true := rfl
theorem unbounded_div_min : isOk (intDiv IntMode.unbounded (-2147483648) (-1)) 2147483648 = true := rfl
theorem unbounded_div_zero : isErr (intDiv IntMode.unbounded 7 0) Fail.divZero = true := rfl
theorem unbounded_mod_neg : isErr (intMod IntMode.unbounded 7 (-2)) Fail.divZero = true := rfl
theorem unbounded_pow : isOk (intPow IntMode.unbounded 2 40) 1099511627776 = true := rfl

-- ---- Floor division and modulus away from the probes ----
--
-- TLC's values for these (and the powers below) are recorded by ty reports/perf/
-- 2026-10-09-beyond-tla-b1a/m0-review-probes/ (B1A-14a, the M0 review's finding 18):
-- RvIntFacts (one invariant per fact, `counts 2 2`: every one holds on TLC 94d0c50),
-- RvPowOneLarge (1^2147483647, (-1)^2147483647, (-1)^2147483646, `counts 2 2`) and
-- RvPowLarge (3^2147483647, `error overflow`). The `unbounded` facts have no TLC outcome
-- (IntMode.unbounded is not TLC-exact, 10:91); 0^0's is primop-probes/PIntPowZeroZero (B1A-15).

theorem div_exact_neg : isOk (div (neg (lit 6)) (lit 3)) (-2) = true := rfl
theorem div_zero_dividend_neg_divisor : isOk (div (lit 0) (neg (lit 5))) 0 = true := rfl
theorem div_pos_pos : isOk (div (lit 7) (lit 2)) 3 = true := rfl
theorem div_pos_neg_exact : isOk (div (lit 6) (neg (lit 2))) (-3) = true := rfl
theorem div_min_neg_one_unbounded_is_not_the_refusal :
    isUnmodeled (intDiv IntMode.unbounded (-2147483648) (-1)) Code.intDivWrap = false := rfl
theorem mod_exact_neg : isOk (mod (neg (lit 6)) (lit 3)) 0 = true := rfl
theorem mod_pos : isOk (mod (lit 7) (lit 3)) 1 = true := rfl

-- ---- Powers: 0, 1, -1 bases, the range edge, and 0^0 ----

theorem pow_neg_two_31 : isOk (pow (neg (lit 2)) (lit 31)) (-2147483648) = true := rfl
theorem pow_two_30 : isOk (pow (lit 2) (lit 30)) 1073741824 = true := rfl
theorem pow_large_exponent : isErr (pow (lit 3) (lit 2147483647)) Fail.overflow = true := rfl
theorem pow_one_large : isOk (pow (lit 1) (lit 2147483647)) 1 = true := rfl
theorem pow_neg_one_odd : isOk (pow (neg (lit 1)) (lit 2147483647)) (-1) = true := rfl
theorem pow_neg_one_even : isOk (pow (neg (lit 1)) (lit 2147483646)) 1 = true := rfl
theorem pow_zero_pos : isOk (pow (lit 0) (lit 5)) 0 = true := rfl
theorem pow_zero_exponent : isOk (pow (neg (lit 5)) (lit 0)) 1 = true := rfl
-- 0^0: TLC raises "0^0 is undefined." (ty reports/perf/2026-10-09-beyond-tla-b1a/
-- primop-probes/tlc-PIntPowZeroZero.txt, cause row 153: typeErr; B1A-D85 resolved by B1A-15).
theorem pow_zero_zero : isErr (pow (lit 0) (lit 0)) Fail.typeErr = true := rfl

-- ---- Res combinators (B1A-D09, 10:327) ----

def rList (r : Res (List Nat)) : List Nat :=
  @Res.rec (List Nat) (fun _ => List Nat) (fun xs => xs) (fun _ => []) r
def rErrTag (r : Res (List Nat)) : Nat :=
  @Res.rec (List Nat) (fun _ => Nat) (fun _ => 100) (fun e => failTag e) r

theorem concat_order :
    Nat.beq (Temporal.nthD (rList (Res.concat [Res.ok [1, 2], Res.ok [], Res.ok [3]])) 2 0) 3 = true := rfl
theorem concat_length :
    Nat.beq (List.length (rList (Res.concat [Res.ok [1, 2], Res.ok [], Res.ok [3]]))) 3 = true := rfl
theorem concat_nil : Nat.beq (rErrTag (Res.concat ([] : List (Res (List Nat))))) 100 = true := rfl
-- The first error in source order wins, whatever follows it.
theorem concat_first_error :
    Nat.beq (rErrTag (Res.concat [Res.ok [1], Res.error Fail.divZero, Res.error Fail.overflow]))
      (failTag Fail.divZero) = true := rfl
theorem bind_error : isErr (Res.bind (Res.error Fail.typeErr) (fun (a : Int) => Res.ok a)) Fail.typeErr = true := rfl
theorem map_ok : isOk (Res.map (fun a => a + 1) (lit 41)) 42 = true := rfl
theorem map_error : isErr (Res.map (fun a => a + 1) (Res.error Fail.fuel)) Fail.fuel = true := rfl

-- ---- The code table and the version ----

-- No two codes share a number (trust-model-prelude's mirror test checks the same on the
-- source text).
def distinctB (xs : List Nat) : Bool :=
  @List.rec Nat (fun _ => Bool) true
    (fun head tail rest => Bool.and (Bool.not (Temporal.memBy Nat.beq head tail)) rest) xs
theorem codes_distinct :
    distinctB [Code.intDivWrap, Code.lazyArg, Code.lazyExcept, Code.lazyRefusedForce,
      Code.lazyMemKind, Code.lazySoaElem, Code.lazyEnabledAssign, Code.cmpUnpinned, Code.todo]
      = true := rfl
theorem epVersion_one : Nat.beq epVersion 1 = true := rfl

end Sanity
end Model
end Trust
