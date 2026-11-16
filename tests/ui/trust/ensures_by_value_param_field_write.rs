//@ revisions: certify default
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ edition: 2021
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! KNOWN_HAZARDS R-c: a write to a FIELD of a by-value parameter must fail-close an
//! `ensures` that names that field, exactly as a whole-parameter rebind already does.
//!
//! A parameter name in an `ensures` denotes its ENTRY value (E2/D2,
//! docs/design/2026-07-09-two-language-spec-surface.md §3). The postcondition VC reads
//! every name at the return block, where a written place is bound to its FINAL value.
//! vcgen guards that with `postcondition_references_mutated_param`, which fail-closes a
//! clause over a rebound parameter to a bare `Not(post)` with the parameter free; the
//! scalar `fn f4(mut x: u8) ensures x == 0 { x = 0; x }` has read FAILED since hunt-6.
//! The guard saw only WHOLE-local writes, so every shape below was PROVED.
//!
//! Before (stage 1 of `782780ea0d` plus the wave-7 fix, measured 2026-10-03, both
//! revisions of this file): exit 0. `z` read "2 proved" under certify, its
//! `vc:..:postcondition:0` row `ay-in-process`, Certified / KernelRechecked, and its
//! `obligation:..:postcondition:0` row credited from it. Every clause marked ERROR is
//! FALSE under E2: `z` claims every input has `a == 0`; `two`, `tup`, `callw`,
//! `viaref` and `neg` relate the result to a field value the body overwrote.
//!
//! After: the written places come from `trust_vcgen::rebound_parameter_places`, which
//! the compiler's typed-CHC attestation (`typed_chc_rebound_parameters`) also asks. Each
//! false clause is fail-closed and the build is an error in both revisions. The split
//! between `failed` and `unknown` is not pinned here: either refuses the build.
//! (`7f118dfc1f` closed the same hole in vcgen by asking the `local_defs` seam, pinned
//! by `ensures_field_of_reassigned_by_value_param.rs`; the predicate is now the union of
//! both.)
//!
//! `unrel` writes the OTHER field. Its clause is true under E2, and the predicate's
//! channel walk names only `s.b`, which would keep it proved; the seam half names a
//! non-SSA parameter WHOLE, so it is fail-closed too: a capability cost, DECISION_QUEUE
//! R-c. When per-place precision returns, re-bless it to the `ok` control's NOTE.
//!
//! Controls, each pinned by its per-function report NOTE:
//!  * `ok` writes nothing; its clause is true under E2 and must stay proved.
//!  * `mref` writes through a `&mut` parameter. Its unprimed pointee name reads the
//!    pointee at EXIT on purpose until the PD-15 flip (docs/DECISION_QUEUE.md PD-15;
//!    `tests/ui/trust/d2-primes/wedge_primed.rs`). This fix must not touch it; when PD-15
//!    flips, re-bless this row with it.
//! `k` (`let old = s.a; s.a = 0; old` under `ensures result == s.a`, true under E2) is
//! left out: it read `unknown` before the fix because the lane read the field at exit,
//! and it stays unproved after it (MEASURED on the stage 1 of `6011b74bad`; the
//! fail-closed `Not(post)` is satisfiable): a capability cost, DECISION_QUEUE R-c.

pub struct S {
    pub a: u8,
    pub b: u8,
}

#[inline(never)]
pub fn id(x: u8) -> u8 {
    x
}

pub fn z(mut s: S) -> u8
//~^ ERROR Trust strict verification failed for `ensures_by_value_param_field_write::z`
    ensures s.a == 0
{
    s.a = 0;
    1
}

pub fn two(mut s: S) -> u8
//~^ ERROR Trust strict verification failed for `ensures_by_value_param_field_write::two`
    ensures result == s.a
{
    s.a = s.b;
    s.a
}

pub fn tup(mut t: (u8, u8)) -> u8
//~^ ERROR Trust strict verification failed for `ensures_by_value_param_field_write::tup`
    ensures result == t.0
{
    t.0 = t.1;
    t.0
}

pub fn callw(mut s: S) -> u8
//~^ ERROR Trust strict verification failed for `ensures_by_value_param_field_write::callw`
    ensures s.a == 4
{
    s.a = id(4);
    0
}

pub fn viaref(mut s: S) -> u8
//~^ ERROR Trust strict verification failed for `ensures_by_value_param_field_write::viaref`
    ensures result == s.a
{
    let p = &mut s.a;
    *p = 9;
    s.a
}

pub fn neg(mut s: S) -> bool
//~^ ERROR Trust strict verification failed for `ensures_by_value_param_field_write::neg`
    ensures result == !(s.a == 0)
{
    s.a = 0;
    s.a != 0
}

pub fn ok(s: S) -> u8
//~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
    ensures result == s.a
{
    s.a
}

pub fn unrel(mut s: S) -> u8
//~^ ERROR Trust strict verification failed for `ensures_by_value_param_field_write::unrel`
    ensures result == s.a
{
    s.b = 0;
    s.a
}

pub fn mref(s: &mut S) -> u8
//~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
    ensures s.a == 0
{
    s.a = 0;
    1
}
