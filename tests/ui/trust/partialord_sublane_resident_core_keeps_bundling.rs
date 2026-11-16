//@ needs-trust-verify
//@ edition: 2021
//@ revisions: certify strict
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[strict] compile-flags: -Ztrust-policy=strict
//@ rustc-env:TRUST_PARTIALORD_SUBLANE=1
//@ rustc-env:TRUST_BUNDLE_MEMBERS=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[certify] check-fail
//@[strict] check-fail
//~? RAW [BUNDLE_MEMBER] root=partialord_sublane_resident_core_keeps_bundling::good_lt name=lt def_path=<partialord_sublane_resident_core_keeps_bundling::Good as core::cmp::PartialOrd>::lt
//~? RAW [BUNDLE_MEMBER] root=partialord_sublane_resident_core_keeps_bundling::good_max name=max def_path=<partialord_sublane_resident_core_keeps_bundling::Good as core::cmp::Ord>::max
//! HONEST CONTROL for the 2026-09-28 authentic-core conjunct in
//! `native_trust_ir_partialord_default_comparator_instances` (see
//! `partialord_sublane_no_core_lang_item_impostor_refuted.rs`).
//!
//! The same shapes on this compiler's own resident `core`: a local ADT whose
//! `lt` and `max` are core's UN-OVERRIDDEN defaults. The sub-lane must still
//! bundle both default bodies (the `RAW` pins), and the verdicts are pinned too.
//! `good_lt` builds under both policies. `good_max`'s bundle leaves one
//! runtime-checked row, which `certify` refuses and `strict` reports; that is
//! unrelated to the conjunct.
#![no_std]

use core::cmp::Ordering;

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct Good(pub u8);

impl PartialOrd for Good {
    fn partial_cmp(&self, o: &Good) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for Good {
    fn cmp(&self, o: &Good) -> Ordering {
        if self.0 < o.0 {
            Ordering::Less
        } else if self.0 > o.0 {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(e)): still refused, but no
// longer zero-row. The call into the bundled body now carries the counted panic-freedom
// aggregate (one unproved `runtime_checked` row), so ZERO-ROW-GATE's note is gone and the
// body is refused on that row instead.
//[certify,strict]~vv ERROR Trust strict verification failed for `partialord_sublane_resident_core_keeps_bundling::good_lt`
//[certify]~v ERROR Trust Level 0 safety verification incomplete for `partialord_sublane_resident_core_keeps_bundling::good_lt`
pub fn good_lt(a: &Good, b: &Good) -> bool {
    a.lt(b)
}

pub fn good_max(a: Good, b: Good) -> Good {
    // Re-pinned 2026-10-15 (the merge of 2026-10-14): `strict` refuses too. The bundle's one
    // runtime-checked row is now the counted aggregate, and beside it the bundle keeps a
    // generic absent callee (core's default `max` dispatches into `Good`'s own `cmp`), the
    // assumption-panic shape no policy tolerates. Before, the runtime-checked std-member
    // disposition carried the row and `strict` reported it. Fail-closed (D103(e)).
    //[certify,strict]~^^^^^^ ERROR Trust strict verification failed for `partialord_sublane_resident_core_keeps_bundling::good_max`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `partialord_sublane_resident_core_keeps_bundling::good_max`
    a.max(b)
}
