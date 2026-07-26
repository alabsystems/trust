// real-spec-corpus — a corpus with MEANINGFUL specifications, written to measure
// the TRUE verification depth of Trust (NOT contract inhabitation on spec-free
// one-liners). Every function here either (a) carries a real source-level
// postcondition via the native Rust `#[core::contracts::ensures(...)]` attribute,
// (b) exercises an auto safety VC (overflow / bounds / div-by-zero) for a
// NON-OBVIOUS reason, or (c) is a deliberately-UNSAFE negative control whose
// obligation MUST NOT be discharged (an honest corpus needs functions that fail).
//
// Dump with:
//   trustc -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//     --crate-type=lib SOURCE.rs
//
// Source contract mechanism (STEP 1 finding): Trust recognizes the upstream Rust
// contracts feature. `#[core::contracts::requires(pred)]` lowers to a typed
// precondition Formula; `#[core::contracts::ensures(move |ret: &T| pred)]` lowers
// to a typed postcondition Formula in the dumped VerifiableFunction. Bare
// `#[requires]`/`#[ensures]` are NOT recognized — the native attribute path is.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#![feature(contracts)]
#![allow(internal_features)]
#![allow(incomplete_features)]
#![allow(unused)]

// ===========================================================================
// GROUP A — real POSTCONDITIONS (the depth that the spec-free corpora lack)
// ===========================================================================

// A1. Identity is provably >= its input. The simplest honest postcondition.
#[core::contracts::ensures(move |ret: &i32| *ret >= x)]
pub fn id_ge(x: i32) -> i32 {
    x
}

// A2. Increment is provably strictly greater than input — given no overflow.
//     The precondition rules out the wrap; the postcondition is then real.
#[core::contracts::requires(x < 2147483647)]
#[core::contracts::ensures(move |ret: &i32| *ret > x)]
pub fn inc_gt(x: i32) -> i32 {
    x + 1
}

// A3. abs is provably non-negative (guarded against i32::MIN negation overflow).
//     Branch + negation: a genuine correctness argument, not a one-liner.
#[core::contracts::requires(x > -2147483648)]
#[core::contracts::ensures(move |ret: &i32| *ret >= 0)]
pub fn abs_nonneg(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

// A4. max(a,b) is provably >= a. A real branch-dependent postcondition.
#[core::contracts::ensures(move |ret: &i32| *ret >= a)]
pub fn max_ge_a(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}

// A5. min(a,b) is provably <= a.
#[core::contracts::ensures(move |ret: &i32| *ret <= a)]
pub fn min_le_a(a: i32, b: i32) -> i32 {
    if a <= b { a } else { b }
}

// A6. A saturating-style clamp: result provably stays >= 0.
#[core::contracts::ensures(move |ret: &i32| *ret >= 0)]
pub fn clamp_lo(x: i32) -> i32 {
    if x < 0 { 0 } else { x }
}

// A7. CONJUNCTIVE GUARD (the multi-condition depth frontier). The guard
//     `a >= 0 && b >= 0` is a short-circuit `&&` — lowered as TWO chained
//     SwitchInts — so the return reflects to `Ite(And(a>=0, b>=0), a, 0)`. The
//     postcondition `ret >= 0` is proven by a NESTED kernel case-split on the
//     conjoined decidable: the then arm `a` needs the FIRST conjunct `a >= 0`; the
//     else arm `0` is trivially >= 0. Fully faithful (no arithmetic ⇒ no safety VC).
#[core::contracts::ensures(move |ret: &i32| *ret >= 0)]
pub fn conj_guard(a: i32, b: i32) -> i32 {
    if a >= 0 && b >= 0 { a } else { 0 }
}

// ===========================================================================
// GROUP B — non-trivial AUTO SAFETY VCs (overflow / bounds / div-by-zero)
//           that are safe for a NON-OBVIOUS reason
// ===========================================================================

// B1. Unsigned add that is overflow-free BECAUSE the precondition bounds inputs.
//     Without the contract this would raise an unprovable overflow VC.
#[core::contracts::requires(a < 1000)]
#[core::contracts::requires(b < 1000)]
pub fn bounded_add(a: u32, b: u32) -> u32 {
    a + b
}

// B2. Division that is div-by-zero-free BECAUSE the precondition excludes 0.
#[core::contracts::requires(b != 0)]
pub fn checked_div(a: u32, b: u32) -> u32 {
    a / b
}

// B3. Unsigned subtraction that is underflow-free BECAUSE a >= b is required.
#[core::contracts::requires(a >= b)]
pub fn checked_sub(a: u32, b: u32) -> u32 {
    a - b
}

// B4. In-source guarded index: bounds-safe by the `if i < len` guard, NO contract.
//     Exercises the bounds VC + branch reasoning purely from the body.
pub fn guarded_index(s: &[u32], i: usize) -> u32 {
    if i < s.len() { s[i] } else { 0 }
}

// B5. In-source guarded division: div-by-zero-safe by the body guard, NO contract.
pub fn guarded_div(a: u32, b: u32) -> u32 {
    if b != 0 { a / b } else { 0 }
}

// B6. In-source guarded subtraction: underflow-safe by the body guard, NO contract.
pub fn guarded_sub(a: u32, b: u32) -> u32 {
    if a >= b { a - b } else { 0 }
}

// ===========================================================================
// GROUP C — NEGATIVE CONTROLS: genuinely UNSAFE / UNPROVABLE.
//           An honest verifier must NOT discharge these.
// ===========================================================================

// C1. Unguarded unsigned add: a real, unbounded overflow obligation. MUST fail.
pub fn unsafe_add(a: u32, b: u32) -> u32 {
    a + b
}

// C2. Unguarded division: a real div-by-zero obligation. MUST fail.
pub fn unsafe_div(a: u32, b: u32) -> u32 {
    a / b
}

// C3. Unguarded slice index: a real out-of-bounds obligation. MUST fail.
pub fn unsafe_index(s: &[u32], i: usize) -> u32 {
    s[i]
}

// C4. A FALSE postcondition: `id` cannot satisfy `ret > x`. MUST NOT be proven.
//     This is the load-bearing honesty test: if the verifier "proves" this, the
//     whole pipeline is vacuous.
#[core::contracts::ensures(move |ret: &i32| *ret > x)]
pub fn false_post(x: i32) -> i32 {
    x
}

// ===========================================================================
// GROUP D — a LOOP with a LOOP-CARRIED postcondition (the per-function loop
//           instantiation of the Hoare while-rule).
// ===========================================================================

// D1. A bounded counting loop whose postcondition `ret == 0` is a loop-carried
//     INVARIANT: the local `r` is set to 0 before the loop and the loop body
//     NEVER writes it (it only increments the counter `i`), so `r == 0` is
//     maintained for an ARBITRARY iteration count and holds at the exit. This is
//     the function the per-function loop instantiation discharges: the Hoare
//     while-rule `loopInvariantRule` is INSTANTIATED at this loop's concrete
//     guard `i < n`, body `i = i + 1`, and the PROVIDED invariant `I := λ e.
//     e[r] = 0`; the preservation `I e → guard → I (exec e body)` is DEFINITIONAL
//     (the body leaves `r` untouched), so the per-function partial-correctness
//     instance `∀ n e, I e → I (exec_loop e (i<n) [i:=i+1] n)` kernel-checks
//     modulo 3 and the postcondition `ret == 0` is its corollary.
//
//     HONEST SCOPE: the invariant `r == 0` is PROVIDED (a trivially-derived
//     untouched-local fact), NOT inferred. Automatic invariant inference for
//     arbitrary loops remains DEFERRED. The certificate is PARTIAL correctness
//     (invariant survives every iteration); arithmetic-decrease TERMINATION is
//     not part of this certificate.
#[core::contracts::ensures(move |ret: &u32| *ret == 0)]
pub fn loop_keep_zero(n: u32) -> u32 {
    let r: u32 = 0;
    let mut i: u32 = 0;
    while i < n {
        i = i + 1;
    }
    r
}

// ===========================================================================
// GROUP E — a LOOP whose postcondition needs a SYNTHESIZED (inferred) invariant.
// ===========================================================================

// E1. A counting loop that RETURNS the counter. The postcondition `ret >= 0` is a
//     REAL (non-vacuous, SIGNED) loop-carried fact — it does NOT follow from the
//     body alone, it follows from the LOOP INVARIANT `0 <= i`. That invariant is
//     NOT hand-provided: trust-strengthen's INTERVAL abstract domain SYNTHESIZES it
//     by abstract interpretation of the init `i = 0` and the body `i = i + 1`
//     (lower bound 0 held, upper bound widened to +inf). The clean kernel then
//     CHECKS the synthesized invariant's preservation `0 <= i -> 0 <= i + 1`
//     GENUINELY — `loopInvariantRule`/`loopTotalCorrect` INSTANTIATE at the
//     SYNTHESIZED `I := lambda e. Int.le 0 (e i)` modulo 3, using the constructive
//     prelude lemmas `Int.le_trans` + `Int.le_self_add_one` and the loop-carried
//     hypothesis. The SMT backend FAILS this postcondition (it has no loop
//     invariant); the synthesized-invariant kernel path is exactly what closes the
//     gap. A WRONG synthesized invariant (e.g. a lower bound on a decrement body)
//     is ill-typed and KernelRejected — fail-closed. This is the FIRST loop class
//     in the corpus whose invariant is INFERRED, not provided.
//
//     HONEST SCOPE: the SYNTHESIZED fact is the interval LOWER bound `0 <= i`. The
//     upper bound `i <= n` (which needs the guard, not just the init+body) and
//     other abstract domains (octagon, congruence) / loop shapes are DEFERRED.
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret >= 0)]
pub fn count_up(n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        i = i + 1;
    }
    i
}

// ===========================================================================
// GROUP F — ADDITIONAL LOOP SHAPES whose postcondition needs a SYNTHESIZED
//           invariant: `<=`-guard, COUNTDOWN, positive STRIDE. The `<` + `+1`
//           shape (count_to / count_up) is generalized here.
// ===========================================================================

// F1. `<=`-GUARDED counter that RETURNS the counter. The loop `while i <= n` exits
//     at `i = n + 1` (one past the `<` case). The postcondition `ret <= n + 1` is
//     DISCHARGED by the SYNTHESIZED guard-aware upper bound `i <= n + 1`: a `<=`
//     guard re-establishes only `i <= n + 1` (NOT `i <= n` — that is FALSE after the
//     last iteration), proved `i <= n => i + 1 <= n + 1` via `Int.add_le_add_right`.
//     Fully faithful via the synthesized `i <= n + 1`.
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret <= n + 1)]
pub fn count_le(n: i32) -> i32 {
    let mut i: i32 = 0;
    while i <= n {
        i = i + 1;
    }
    i
}

// F2. COUNTDOWN that RETURNS the counter. The loop `while i > 0 { i = i - 1 }` exits
//     at `i = 0`. The postcondition `ret >= 0` is DISCHARGED by the SYNTHESIZED lower
//     bound `0 <= i`, preserved BECAUSE of the guard `i > 0` (`0 < i => 0 <= i - 1`,
//     the kernel-checked `countdownGe0`). Termination is the SYNTHESIZED ranking
//     `toNat(i)` (i decreases to 0). Fully faithful.
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret >= 0)]
pub fn countdown(n: i32) -> i32 {
    let mut i: i32 = n;
    while i > 0 {
        i = i - 1;
    }
    i
}

// F3. POSITIVE-STRIDE counter that RETURNS the counter. The body advances by stride
//     `k = 2`. The SYNTHESIZED lower bound `0 <= i` is preserved for ANY positive
//     stride (`0 <= i => 0 <= i + 2`, via `Int.le_trans` + `strideSelfLe`). TERMINATION
//     is now TOTAL: the ranking `toNat(n - i)` STRICTLY decreases each `+k` step, proved
//     by the kernel-checked `strideRankDecrease` lemma — built on the new `toNat`
//     MONOTONICITY lemma `toNatMono : Int.le a b -> Nat.le (toNat a)(toNat b)` (proven by
//     `Int.NonNeg` case-split, constructive, modulo 3): from `i < n` and `1 <= k`,
//     `toNat(n-(i+k)) < toNat(n-i)`. So `stride_up` is now FULLY FAITHFUL — its `+2` raises
//     a MODELED signed-add overflow VC (Lemma 5), and the postcondition `ret >= 0` is
//     discharged by the synthesized lower bound `0 <= i` at the halting state. DEFERRED for
//     a stride k > 1: the guard-aware UPPER bound `i <= n` (a stride can overshoot it).
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret >= 0)]
pub fn stride_up(n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        i = i + 2;
    }
    i
}

// ===========================================================================
// GROUP G — a MULTI-STATEMENT loop body (ACCUMULATOR). The body updates TWO
//           distinct mutable locals; the synthesized invariant is an interval
//           fact on the ACCUMULATOR (a SECOND local), not the guard counter.
// ===========================================================================

// G1. ACCUMULATOR with a TWO-ASSIGNMENT loop body. The body updates BOTH the
//     accumulator `s` and the guard counter `i`. The postcondition `ret >= 0` is a
//     loop-carried fact about the ACCUMULATOR `s` (the return), discharged by the
//     SYNTHESIZED interval lower bound `0 <= s` (an interval fact on a SECOND mutable
//     local). The synthesis HANDLES the multi-statement body: it collects BOTH the
//     `s = s + 1` and `i = i + 1` updates (split across blocks by the per-update overflow
//     asserts), drives TERMINATION via the GUARD counter `i` (ranking `toNat(n - i)`) and
//     the INVARIANT via the accumulator `s` (`0 <= s`, preserved by `s := s + 1` through
//     the kernel-checked `Int.le_trans` + `Int.le_self_add_one` step — which reduces
//     correctly through the 2-statement `exec` because the `i := i + 1` statement leaves
//     `s` untouched). Fully faithful via the synthesized `0 <= s`. DEFERRED: non-`+1`
//     accumulator strides, relational invariants between `s` and `i` (e.g. `s <= i`), and
//     >2-statement bodies.
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret >= 0)]
pub fn accum(n: i32) -> i32 {
    let mut s: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        s = s + 1;
        i = i + 1;
    }
    s
}

// ===========================================================================
// GROUP H — a RELATIONAL loop invariant (PART 1). The SAME lockstep accumulator
//           body as `accum`, but the postcondition is the STRONGER `ret <= n`,
//           which needs a RELATIONAL fact BETWEEN the two locals (`s == i`), not
//           just an interval fact on one of them.
// ===========================================================================

// H1. RELATIONAL ACCUMULATOR. `s` and the guard counter `i` increment in LOCKSTEP from
//     equal inits (`s = 0`, `i = 0`), so `s == i` holds throughout. The postcondition
//     `ret <= n` is DISCHARGED by the SYNTHESIZED RELATIONAL invariant `s == i ∧ i <= n`:
//     at exit `i <= n` (the guard-aware upper bound) AND `s == i`, so `s <= n`. The bare
//     interval lower bound `0 <= s` (which `accum` uses) only proves `ret >= 0` — it CANNOT
//     prove `ret <= n`. The synthesis PROPOSES `s == i` by CONSUMING trust-strengthen's
//     OCTAGON relational domain (the difference `s - i` is pinned at 0 by the equal inits +
//     identical `+1` strides); the clean kernel VERIFIES preservation by CONGRUENCE
//     (`s == i → s + 1 == i + 1` via `congrArg (·+1)`) and discharges `ret <= n` via `Eq.subst`
//     along `i = s`. Fully faithful via the relational invariant. DEFERRED: non-`+1` lockstep
//     strides, relational facts over >2 locals (general octagon), and `s == i + k` offsets.
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret <= n)]
pub fn accum_eq(n: i32) -> i32 {
    let mut s: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        s = s + 1;
        i = i + 1;
    }
    s
}

// ===========================================================================
// GROUP I — GENERAL RELATIONAL loop invariants (PART 1: GENERAL OCTAGON over
//           >2 variables). The lockstep accumulator is GENERALIZED from TWO
//           locals (`s == i`) to a SET of ≥ 2 accumulators all locked to the
//           counter (`a == i ∧ b == i ∧ … ∧ i <= n`) — a fact the 2-var
//           relational domain CANNOT express. Plus a precondition-bounded
//           counter and two HONESTLY-DEFERRED shapes.
// ===========================================================================

// I1. THREE interacting locals (TWO accumulators a, b + the guard counter i), all
//     incrementing in LOCKSTEP from equal inits. The postcondition `ret <= n` needs the
//     RELATIONAL fact `a == i ∧ b == i` over THREE distinct locals — the 2-var domain
//     (`s == i`) cannot express it. The synthesis CONSUMES trust-strengthen's GENERAL
//     OCTAGON over the FULL set {a, b, i} (ONE difference-bound matrix over ≥ 4 dimensions,
//     NOT a sequence of 2-var octagons): the joint `+1` translation pins EVERY difference
//     `a - i` and `b - i` at 0, so the closed DBM proves `a == i ∧ b == i`. The clean kernel
//     VERIFIES preservation by a NESTED right-folded `And.intro` of one congruence step per
//     accumulator (`a == i -> a+1 == i+1` via `congrArg (·+1)`) capped by the guard upper
//     bound, and discharges `ret <= n` via `Eq.subst` along `i = a` (the return reads `a`).
//     FULLY FAITHFUL via the general octagon (>2 vars). A WRONG relation (some `ak == i + d`,
//     d != 0, or a non-lockstep stride) is ill-typed and KernelRejected — fail-closed.
//     DEFERRED: non-`+1` lockstep strides, non-equal-init offsets (`ak == i + k`), returning
//     a non-first accumulator, and conditional (non-lockstep) updates.
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret <= n)]
pub fn three(n: i32) -> i32 {
    let mut a: i32 = 0;
    let mut b: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        a = a + 1;
        b = b + 1;
        i = i + 1;
    }
    a
}

// I2. FOUR interacting locals (THREE accumulators a, b, c + the counter i). The general
//     octagon scales to a wider DBM (over {a, b, c, i}, ≥ 5 dimensions): `a == i ∧ b == i ∧
//     c == i ∧ i <= n` discharges `ret <= n`. Same general path as `three`, one more
//     congruence conjunct. FULLY FAITHFUL via the general octagon.
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret <= n)]
pub fn four(n: i32) -> i32 {
    let mut a: i32 = 0;
    let mut b: i32 = 0;
    let mut c: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        a = a + 1;
        b = b + 1;
        c = c + 1;
        i = i + 1;
    }
    a
}

// I3. PRECONDITION-bounded counter. The precondition `n >= 0` bounds the loop; the
//     postcondition `ret <= n` is discharged by the EXISTING synthesized conjoined range
//     `0 <= i ∧ i <= n` (the `count_to` shape, exercised on a precondition-fed function).
//     FULLY FAITHFUL via the synthesized `i <= n`.
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret <= n)]
pub fn bounded_iter(n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        i = i + 1;
    }
    i
}

// I4. HONEST not-yet-faithful — a 3-var LOCKSTEP loop that RETURNS the SECOND accumulator `b`
//     (not the first). The general relational discharge of `ret <= n` is wired only for a
//     return reading the FIRST accumulator `a0` (`ret = a0 == i <= n`). Returning any `ak`
//     (here `b`) is the DEFERRED "return any accumulator" generalization. The SMT backend
//     fails the postcondition and the synthesis does NOT close it — included as an honest
//     coverage boundary, NOT forced. (Supporting it is a small extension: project the k-th
//     equality instead of the 0-th.)
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret <= n)]
pub fn three_ret_b(n: i32) -> i32 {
    let mut a: i32 = 0;
    let mut b: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        a = a + 1;
        b = b + 1;
        i = i + 1;
    }
    b
}

// I5. HONEST not-yet-faithful — a MAX-scanning loop with a CONDITIONAL accumulator update
//     `if i > m { m = i }`. The invariant `0 <= m` (and `m <= i`) needs CONDITIONAL-update
//     transfer the lockstep `+1` synthesis does not model (the body branch is not a
//     straight-line increment). DEFERRED, honestly documented — the SMT backend fails the
//     postcondition and synthesis declines (no WRONG invariant is forced). Conditional /
//     max-min loop invariants are a future shape.
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret >= 0)]
pub fn max_scan(n: i32) -> i32 {
    let mut m: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if i > m {
            m = i;
        }
        i = i + 1;
    }
    m
}
