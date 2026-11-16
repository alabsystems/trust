//[json]~ NOTE "proved":1,"failed":0,"unknown":2,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":4}
//@ revisions: human json
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib -Ztrust-policy=advisory
//@[human] compile-flags: -Ztrust-verify-output=human
//@[json] compile-flags: -Ztrust-verify-output=both
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-pass
//! Regression `discharge-cycle` (2026-10-05): the measured shape, reduced from ty's
//! `cvw::same_representation` / `cvw::all_same` (`tla-shapes-families`, four
//! `failed` rows on main `c797f90c1`). `all_same` dispatches `Iterator::zip` on its
//! `impl Iterator` parameter (an admitted site) and calls `same` back through the
//! `all` closure; `same` names `all_same::<slice::Iter<V>, slice::Iter<V>>`. The
//! discharge row used to be `failed` with "unresolvable: the definition's MIR is
//! being computed up this stack" (`same` pinned `"failed":1,"unknown":1`). It now
//! reads `all_same`'s completed body and resolves the site to core's
//! `Iterator::zip`, a sysroot body this compilation has no verdict for: `unknown`
//! (not established; the pin, `"failed":0,"unknown":2`), with that reason.
//!
//! Two revisions. `json` pins `same`'s counts on its TRUST_JSON row; `human` (43 KB of stderr)
//! pins the discharge warning and the same counts through the human summary line, which reads
//! the published-row tally the JSON reads. They were split (2026-10-09) because compiletest then
//! kept only the first 512 KiB of a compile's stderr (`read2.rs`, `MAX_OUT_LEN`) and `same`'s
//! TRUST_JSON row (its inline native verification bundle, with the message repeated in
//! `rendered`) alone is ~546 KB: by 2026-10-13 that row itself crossed the cap (681,005 bytes of
//! stderr, the row starting ~123 KB in), so `json` failed with the verdict unchanged. compiletest
//! now captures 16 MiB and refuses a truncated capture instead of checking a prefix
//! (DECISION_QUEUE COMPILETEST-CAPTURE-CAP-1).
pub enum V {
    Leaf(u8),
    Node(Vec<V>),
}

pub fn same(a: &V, b: &V) -> bool {
    //[human]~^ WARN Trust instance discharge not established for `mutual_recursion_discharge_through_closure_callee::same`: 1 instance(s)
    //[human]~| NOTE Trust verification: 1 proved, 0 failed, 2 unknown, 0 timed out, 1 runtime-checked out of 4 obligation(s)
    match (a, b) {
        (V::Leaf(x), V::Leaf(y)) => x == y,
        (V::Node(x), V::Node(y)) => all_same(x.iter(), y.iter()),
        _ => false,
    }
}

fn all_same<'a, 'b>(l: impl Iterator<Item = &'a V>, r: impl Iterator<Item = &'b V>) -> bool {
    l.zip(r).all(|(p, q)| same(p, q))
}
