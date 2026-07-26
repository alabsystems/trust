// call-spine-corpus — the CALL-SPINE increment's fixture corpus (the fourth
// return shape: a caller whose return value flows out of a `Terminator::Call`
// to a same-crate callee). Measures the smallest honest step past the
// "Call-spine ceiling" (reports/call-spine-scoping-2026-07-02.md): the §6
// Clean-kernel lane certifies a function WITH A REAL CALL when — and only when
// — the callee is ITSELF already fully-faithful-certified (callees-first) AND
// (call-requires establishment, residue #2 closed) the caller ESTABLISHES the
// callee's `#[requires]` at the call site with the actual args substituted.
//
// DELIBERATELY SEPARATE from fixtures/real-spec-corpus (the depth corpus): the
// switchover test pins the depth corpus's MirSem fallback population at 0, and
// this corpus carries the call shapes (both call lanes — the MirSem witness and
// the trust-ir Call denotation — certify/decline in lockstep here).
//
// The corpus (positives + the mandatory negative controls):
//   * helper                        — the certified callee: the depth corpus's
//     `bounded_add` shape (its overflow VC discharges from the `#[requires]`
//     bounds ⇒ fully faithful) — becomes an assumable CalleeFact CARRYING its
//     parsed requires conjuncts (`a < 1000`, `b < 1000`).
//   * caller(x) = helper(x, 1)      — the ORIGINAL thin dispatcher. UNDER THE
//     ESTABLISHMENT CLAUSE IT NO LONGER CERTIFIES (expectation FLIPPED, on
//     purpose): helper's requires needs `a < 1000` at the call site, but
//     `caller` passes its UNCONSTRAINED `x` as `a` — `caller(2000)` panics
//     inside `helper`. This WAS the named epistemic hole (call-spine report
//     §residues #2); the flip is the closure's primary evidence.
//   * caller_establishes            — POSITIVE: its own `#[requires(x < 1000)]`
//     implies helper's `a < 1000` (and the const `1` establishes `b < 1000`
//     as a ground fact), so every violation refutes modulo 3 under the
//     caller's own precondition + type bounds ⇒ fully faithful.
//   * caller_const_ok               — POSITIVE: constant args `helper(3, 4)`
//     satisfy both bounds as ground facts ⇒ established ⇒ fully faithful.
//   * caller_violates               — NEGATIVE CONTROL (the epistemic-hole
//     REGRESSION TEST, named so): an unconstrained arg to the requires-carrying
//     helper. `caller_violates(2000)` panics inside `helper`; it MUST NOT
//     count as fully faithful on ANY lane, ever again.
//   * wild_helper / caller_uncertified — NEGATIVE CONTROL: `wild_helper` has NO
//     precondition, so its overflow VC stays satisfiable ⇒ NOT fully faithful ⇒
//     never registered ⇒ `caller_uncertified` must stay uncounted (fail-closed).
//   * self_loop                     — NEGATIVE CONTROL: a self-recursive caller.
//     Its callee is itself, whose certificate cannot precede its own — the
//     recognizer fails closed on the self edge.
//
// Dump with (see regenerate.sh):
//   trustc -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//     --edition 2021 --crate-type=lib SOURCE.rs
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#![feature(contracts)]
#![allow(internal_features)]
#![allow(incomplete_features)]
#![allow(unused)]
#![allow(unconditional_recursion)]

// The SAFE straight-line callee — the depth corpus's `bounded_add` shape: the
// unsigned-add overflow VC discharges from the precondition bounds, so the
// callee is fully faithful and becomes an assumable CalleeFact (carrying the
// two parsed requires conjuncts callers must establish).
#[core::contracts::requires(a < 1000)]
#[core::contracts::requires(b < 1000)]
pub fn helper(a: u32, b: u32) -> u32 {
    a + b
}

// The ORIGINAL thin dispatcher: the sole non-trivial step is one
// `Terminator::Call` to `helper`, dest `_0`, args a parameter copy + a constant.
// NOTE the file name sorts BEFORE helper's ("caller" < "helper"), so the
// callees-first reorder in `prove_dump_dir` is genuinely load-bearing.
// EXPECTATION (flipped by the call-requires establishment increment): `x` is
// UNCONSTRAINED, so helper's `a < 1000` is NOT established — `caller` must NOT
// count as fully faithful (`caller(2000)` panics inside `helper`).
pub fn caller(x: u32) -> u32 {
    helper(x, 1)
}

// POSITIVE (establishment) — the caller's own `#[requires]` implies helper's:
// `x < 1000 ⊢ ¬(x ≥ 1000)` and the const `1` grounds `¬(1 ≥ 1000)`, both
// refuted modulo 3 by the consumed vc_refute lane ⇒ certifies on BOTH call
// lanes (trust-ir primary).
#[core::contracts::requires(x < 1000)]
pub fn caller_establishes(x: u32) -> u32 {
    helper(x, 1)
}

// POSITIVE (establishment, ground) — constant args satisfy helper's bounds as
// ground facts (`¬(3 ≥ 1000)`, `¬(4 ≥ 1000)`) ⇒ established ⇒ certifies.
pub fn caller_const_ok() -> u32 {
    helper(3, 4)
}

// NEGATIVE CONTROL — THE EPISTEMIC-HOLE REGRESSION TEST (named so): an
// unconstrained arg to the requires-carrying helper. Before the establishment
// clause this shape certified fully faithful while `caller_violates(2000)`
// panics inside `helper`; it must NEVER count again (fail-closed on both
// call lanes).
pub fn caller_violates(y: u32) -> u32 {
    helper(y, 2)
}

// NEGATIVE CONTROL (b) — an UNCERTIFIED callee: no precondition, so the
// unsigned-add overflow VC does not discharge ⇒ wild_helper is NOT fully
// faithful ⇒ it never enters the certified registry.
pub fn wild_helper(a: u32, b: u32) -> u32 {
    a + b
}

// NEGATIVE CONTROL (b) caller — must stay UNCOUNTED: its callee is never
// certified, so the call-return shape fails closed.
pub fn caller_uncertified(x: u32) -> u32 {
    wild_helper(x, 7)
}

// NEGATIVE CONTROL (c) — a SELF-RECURSIVE caller: must fail closed (the
// #[decreases] recursion lane is NOT this increment).
pub fn self_loop(x: u32) -> u32 {
    self_loop(x)
}
