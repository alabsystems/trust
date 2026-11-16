//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! I0 (ref-self design §4.0) — a clause identifier that RUST BINDS is that
//! binding, never a same-named admitted item.
//!
//! `e9_cited_island_def_param_shadow.rs` already pins the half
//! `admit_clause_island_definitions` closes: a PARAMETER PATTERN shadows a
//! Clean island DEFINITION. This file pins the two holes that guard left open.
//! Both were measured on a stage-1 `trustc` built from this tree, and BOTH
//! CERTIFIED A FALSE CONTRACT before the fix — the negative control is in the
//! commit message.
//!
//! 1. CONST GENERICS were in no shadow set at all, so `ensures result == N`
//!    beside `clean { def N … }` discharged: measured goal
//!    `trust_import_…__pick = N`, `DEFEQ-DISCHARGED`, 2 proved. The Rust
//!    reading is FALSE — `pick::<7>()` returns 3 — while the island reading is
//!    `3 = 3`. `pick_ctl` is the same program with the collision removed
//!    (definition `n`, const generic `M`) and still discharges, so what
//!    refuses `pick` is the collision and not the shape.
//!
//! 2. PROGRAM FUNCTIONS are admitted UPSTREAM of that seam —
//!    `trust_mint_program_admissions` and the in-walk mint key every recognized
//!    crate function under its def-path AND every `spec_spellings` suffix, the
//!    BARE last segment first — with no parameter-name filter anywhere. A
//!    by-value struct parameter contributes the rows `p.field` and NO bare `p`,
//!    so the bare name fell through to that admission: `cap`'s goal was
//!    `trust_import_…__limit = eighty`, byte-identical to the unshadowed
//!    control `ctl`'s, and `DEFEQ-DISCHARGED`. `cap` returns 80 whatever `C` it
//!    is handed, so the clause is a statement about the crate function `limit`
//!    while its text names the parameter. Both spellings are pinned: bare
//!    `limit` and the call `limit()`. `ctl` must stay green.
//!
//! The refusals come from `trust_spec_elab::ambient_bare_admission` /
//! `ambient_call_admission`, reading the shadow set
//! `admit_clause_island_definitions` installs on the clause-local facet table.
//! They are pure REMOVALS of a name resolution: this file can only lose a
//! discharge, never create one.
//!
//! `dont-require-annotations: ERROR` tolerates the secondary
//! strict-verification errors; the refusals themselves are pinned on their
//! REASON text below, not on the generic headline.

// The shadowing bindings exist to SHADOW; the bodies deliberately ignore them.
#![allow(unused_variables)]

clean {
    def N : UInt64 := 3
    def n : UInt64 := 3
    def eighty : UInt64 := 80
}

pub struct C {
    pub a: u64,
    pub b: u64,
}

fn limit() -> u64 {
    80
}

// ---------------------------------------------------------------------------
// 1. a const generic vs an island definition of the same name
// ---------------------------------------------------------------------------

// CONTROL: no collision (`M` vs `n`), so the uncited island-defeq route still
// discharges both obligations. No annotations: this function must stay GREEN.
fn pick_ctl<const M: usize>() -> u64
    ensures result == n
{
    3
}

// NEGATIVE: the const generic `N` and the island definition `N` collide.
fn pick<const N: usize>() -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures result == N
{
    3
}

// ---------------------------------------------------------------------------
// 2. a program-function admission vs a by-value struct parameter
// ---------------------------------------------------------------------------

// CONTROL: the admitted crate function `limit` still resolves under an
// unshadowed spelling, and the clause still discharges. No annotations: GREEN.
fn ctl(bound: C) -> u64
    ensures limit == eighty
{
    80
}

// NEGATIVE, BARE ARM.
fn cap(limit: C) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures limit == eighty
    //~^ ERROR a clause names VALUES: `limit` is bound by this function's signature and has no clause binder of its own
{
    80
}

// NEGATIVE, CALL ARM. The native lane already records this rule in
// `tests/ui/trust/contract_inlined_call_scope_stays_closed.rs`; the citing lane
// must not be looser about the same identifier.
fn cap_call(limit: C) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures limit() == eighty
    //~^ ERROR is a call of that binding in Rust
{
    80
}

fn main() {
    let _ = (pick_ctl::<1>(), pick::<7>());
    let _ = (ctl(C { a: 1, b: 2 }), cap(C { a: 1, b: 2 }), cap_call(C { a: 1, b: 2 }));
}
