//@ revisions: nonlinear_div nonlinear_div_two_divisors linear_control
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Ztrust-verify-timeout-ms=1
//@[nonlinear_div] check-pass
//@[nonlinear_div_two_divisors] check-fail
//@[linear_control] check-pass
//@ edition: 2021
//@ dont-check-compiler-stderr
#![crate_type = "lib"]
//! **A true `ensures` whose only prover runs out of time is REFUSED, never
//! accepted — and only that row is refused.**
//!
//! `nonlinear_div` is the shape `ensures_adt_param_json_wire_no_ice.rs
//! #trait_impl_called` first had: a trait impl method whose clause
//! `result <= 100` holds over `if x != 0 { 100 / x } else { 0 }`, plus a caller
//! that reaches it through the trait. The division branch's body row is
//! nonlinear (`100 / x` by a variable): the Clean kernel does not certify it, so
//! its only prover is ay-chc, which needs SECONDS of wall clock for it, and under
//! suite load that lapses. MEASURED 2026-09-30 on m16 (stage 1 of origin/main
//! `486460dbe77`, std with debug assertions), the compile exactly as compiletest
//! runs it: at the default 20 s budget 36 concurrent copies red 36 of 36, 18
//! concurrent green 18 of 18; at 120 s, 36 concurrent still red 36 of 36;
//! serially red at 3000 ms and green at 5000 ms. The red is always the same two
//! `unknown` rows — the division branch's body row (`postcondition:2`) and the
//! clause marker, which names it as the one body row that did not qualify — and
//! nothing in it depends on the std build (the native bundle and request digests
//! are identical under a release-like std). Every red run at a budget of 500 ms
//! or more also prints a refutation that strict certification withdrew ("strict
//! UNSAT proof validation failed: step t0 uses unverified trust rule"); no green
//! run does.
//!
//! This file makes that lapse DETERMINISTIC with `-Ztrust-verify-timeout-ms=1`
//! and pins the refusal: strict verification fails `<S as Td>::m` on exactly
//! those 2 rows, while its other rows (the guarded division's `divzero` row
//! and the constant branch's body row) and the caller `p` stay proved
//! (crate summary 2 analyzed, 1 verified, 3 proved, 0 failed, 2 unknown), and
//! the marker names the division row as the one that did not qualify. A starved
//! solver must never turn into a proof: had the budget path published the
//! candidate, this revision would build and the test would fail. The error is
//! pinned without its count: at 1 ms the native lane lapses on the `divzero` and
//! constant-branch rows too, the Clean kernel then certifies both, and the error
//! counts 4 obligations where the published rows show 2 unknown (at 1000 ms it
//! counts 2). That count over-reports; it never under-reports.
//!
//! `linear_control` is the same method, the same caller and the same 1 ms budget
//! with a linear body (`if x <= 100 { x } else { 100 }`): both body rows are
//! certified by the Clean kernel, which no solver budget gates, so it builds with
//! everything proved. Together the two say the refusal is the nonlinear row's
//! and nothing else's. `linear_control` emits no diagnostic, so it also guards
//! the JSON-wire ICE fix of `ensures_adt_param_json_wire_no_ice.rs`: with that
//! fix reverted it exits 101 with the `trimmed_def_paths` panic, while
//! `nonlinear_div` exits 1 either way (its error satisfies `must_produce_diag`).
//!
//! If `nonlinear_div` ever builds, the division row became provable without the
//! solver budget (a kernel route for it, or an ay-chc proof inside 1 ms):
//! re-measure it at the default budget under load before moving the pin, and
//! say which.
//!
//! IT DID, on the merged tree (the merge of 2026-10-14; measured on its stage 1,
//! 2026-10-15): at 1 ms every row of `nonlinear_div`'s `m` is proved, the body rows
//! and the `divzero` row by `clean-kernel-certified` and the clause by
//! `trust-exact-source-clause-discharge` — a KERNEL route for `100 / x <= 100`, which
//! no solver budget gates. So `nonlinear_div` is now `check-pass` and pins that
//! route. The refusal this file exists for moved to `nonlinear_div_two_divisors`:
//! `if x != 0 { 100 / x / (x % 5 + 1) } else { 0 }` with the same clause is just as
//! true, the kernel certifies its other body row but not the nested division's, and
//! at 1 ms that row times out: strict fails `m` on it, every other row (two `divzero`,
//! one `overflow:add`, the constant branch) proved.
//!
//! Flags as in `ensures_adt_param_json_wire_no_ice.rs` (the raw JSON wire with a
//! human error format), so every stderr line is a RAW diagnostic and the pins are
//! RAW substrings.

pub struct S;

pub trait Td {
    fn m(&self, x: u32) -> u32;
}

#[cfg(nonlinear_div_two_divisors)]
impl Td for S {
    fn m(&self, x: u32) -> u32
        ensures result <= 100
    {
        if x != 0 { 100 / x / (x % 5 + 1) } else { 0 }
    }
}

#[cfg(nonlinear_div)]
impl Td for S {
    fn m(&self, x: u32) -> u32
        ensures result <= 100
    {
        if x != 0 { 100 / x } else { 0 }
    }
}

#[cfg(linear_control)]
impl Td for S {
    fn m(&self, x: u32) -> u32
        ensures result <= 100
    {
        if x <= 100 { x } else { 100 }
    }
}

pub fn p(y: u32) -> u32 {
    S.m(y)
}

//[nonlinear_div_two_divisors]~? RAW Trust strict verification failed for `<ensures_nonlinear_div_solver_starved_stays_refused::S as ensures_nonlinear_div_solver_starved_stays_refused::Td>::m`
//[nonlinear_div_two_divisors]~? RAW was not discharged because 1 of its 2 body row(s) did not qualify: `vc:h0__x3censures_unonlinear_udiv_usolver_ustarved_ustays_urefused__S_x20as_x20ensures_unonlinear_udiv_usolver_ustarved_ustays_urefused__Td_x3e__m:postcondition:4`
//[nonlinear_div_two_divisors]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_nonlinear_div_solver_starved_stays_refused","functions_analyzed":2,"functions_verified":1,"total_proved":5,"total_failed":0,"total_unknown":2
//[nonlinear_div]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_nonlinear_div_solver_starved_stays_refused","functions_analyzed":2,"functions_verified":2,"total_proved":5,"total_failed":0,"total_unknown":0
//[linear_control]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_nonlinear_div_solver_starved_stays_refused","functions_analyzed":2,"functions_verified":2,"total_proved":4,"total_failed":0,"total_unknown":0
