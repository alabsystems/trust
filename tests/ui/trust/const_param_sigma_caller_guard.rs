//@ revisions: ok bad r1 r1_bad
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[ok] check-pass
//@[r1] check-fail
//@[bad] check-fail
//@[r1_bad] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! CONSTPARAM-SIGMA-FRESHEN-1: the σ call-site pass split a generic caller's OWN
//! const parameter into one fresh symbol per occurrence, so a correct guard on it
//! could not discharge the callee's precondition.
//!
//! A const parameter `K` is ONE symbol, `__trust_constparam_0_K`, keyed on its
//! identity (piece #7a); it is the same term as the array length of `a: &[u32; K]`.
//! The σ post-pass `freshen_aliasing_opaque_occurrences` still listed the family as
//! alias-prone and renamed every occurrence to an independent
//! `__trust_constparam_0_K__r1occ{n}`. That detached the guard `n < K` from σ's
//! rendering of `buf.len()` as `K` and from the unsize fact `slice_len == K`. Correct
//! callers were refuted with the counterexample `n = 0, ...occ4 = 1, ...occ0..7 = 0`
//! (eight copies of one `K`), and the default policy failed the build. Through R1, a
//! private `idx(a, i)` called only behind such a guard was refused its caller-
//! propagation flip, and its own bounds row failed the crate. Concrete twins
//! (`a: &[u32; 4]` with `n < 4`) were proved.
//!
//! The fix drops the family from the freshen set (one symbol is one value of the
//! caller) and, as defence in depth, renames a CALLEE's own const-param leaves out of
//! the family before σ, so a callee's `M` can never be read as a caller's `M`
//! (`trust_vcgen` `const_param_fold_tests`).
//!
//! BEFORE (the stage 1 of `5911b1325f`, origin/main after wave 22, at
//! `scratchpad/stage1-w23base`; each revision's flags plus `--cfg <revision>
//! --emit=metadata`; measured 2026-10-11):
//! - `ok` exits 1 with `[precond] FAILED (ay-in-process)` and a counterexample over
//!   `__trust_constparam_0_K__r1occ*`.
//! - `r1` exits 1: `idx`'s `[slice]` row is FAILED (no flip is admitted), and `idx`
//!   gets the two errors `r1_bad` annotates.
//! - `bad` and `r1_bad` exit 1 with exactly the errors annotated below (`bad`'s
//!   counterexample splits both `K` and `M` into `__r1occ` copies).
//! The concrete twins of `ok` and `r1` (scout probes `fx_c.rs`, `r8.rs`, on the stage 1
//! of `2bf0ad72e3`) exit 0 with warnings only.
//!
//! AFTER (measured on the stage 1 of `999b006b87`): `ok` and `r1` exit 0 like their twins.
//! `ok`'s precondition row is proved, and `r1` admits the flip, so `idx`'s row is
//! proved by caller propagation. `bad` and `r1_bad` stay refused with the same
//! errors, because each is a real bug for some instantiation:
//! - `bad` guards on `M` but the array has length `K`.
//! - `r1_bad` guards on `M` while `idx` reads `a: &[u32; N]`, and `entry`
//!   instantiates `N = 6`, `M = 7`.
//! There is no UI revision for a generic CALLEE whose own `M` shares the caller's
//! spelling, because no producer puts a callee's const-param symbol into `P` today.
//! For example, a call `pickg::<2>(b, n)` to `pickg<const M>(buf: &[u32; M], n) requires
//! n < buf.len()` gets `P = n < buf__slice_len` (`TRUST_PRECOND_DEBUG`, same compiler),
//! which σ renders from the actual `b`. That collision is pinned at the crate level by
//! `const_param_fold_tests::callee_const_param_cannot_meet_the_callers_symbol`.

// ---- ok: a correct guard on the caller's own `K` ----

#[cfg(any(ok, bad))]
pub fn pick(buf: &[u32], n: usize) -> u32
    requires n < buf.len()
{
    buf[n]
}

#[cfg(ok)]
pub fn caller_ok<const K: usize>(a: &[u32; K], n: usize) -> u32 {
    if n < K { pick(a, n) } else { 0 }
}

// ---- bad: guards on `M`, the array has length `K` ----

#[cfg(bad)]
pub fn caller_bad<const K: usize, const M: usize>(a: &[u32; K], n: usize) -> u32 {
    //[bad]~^ ERROR strict verification failed for `const_param_sigma_caller_guard::caller_bad`
    if n < M { pick(a, n) } else { 0 }
}

// ---- r1: a private callee reached only behind a correct generic guard ----

#[cfg(any(r1, r1_bad))]
fn idx(a: &[u32], i: usize) -> u32 {
    //[r1,r1_bad]~^ ERROR safety verification incomplete for `const_param_sigma_caller_guard::idx`
    //[r1,r1_bad]~| ERROR strict verification failed for `const_param_sigma_caller_guard::idx`
    // `r1`: CAPABILITY LOSS, re-pinned 2026-10-15 (the merge of 2026-10-14; docs/KNOWN_HAZARDS.md
    // "OPEN 2026-10-15 — correct programs the merge of 2026-10-14 refuses", DECISION_QUEUE
    // D103(i)). `idx`'s R1 caller-propagation flip is not admitted: its strengthened VC
    // (`i < a.len()` assumed) is not kernel-certified (`TRUST_R1_TRACE`: "strengthened VC NOT
    // kernel-certified"), so its `[slice]` row stays FAILED exactly as in `r1_bad`. Fail-closed:
    // refused, never proved. Flip `r1` back to `check-pass` when the capability returns.
    a[i]
}

#[cfg(r1)]
fn caller<const N: usize>(a: &[u32; N], i: usize) -> u32 {
    if i < N { idx(a, i) } else { 0 }
}

#[cfg(r1)]
pub fn entry(i: usize) -> u32 {
    let a = [3u32; 6];
    caller(&a, i)
}

// ---- r1_bad: the guard reads a DIFFERENT const param ----

#[cfg(r1_bad)]
fn caller<const N: usize, const M: usize>(a: &[u32; N], i: usize) -> u32 {
    if i < M { idx(a, i) } else { 0 }
}

#[cfg(r1_bad)]
pub fn entry(i: usize) -> u32 {
    let a = [3u32; 6];
    caller::<6, 7>(&a, i)
}
