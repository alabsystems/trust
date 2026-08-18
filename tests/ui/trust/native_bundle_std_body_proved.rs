//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! A std/core callee's REAL body is lowered into the verification bundle, so the
//! caller's panic-freedom obligation is discharged by PROOF — not by a totality
//! model asserting the callee cannot panic.
//!
//! Before the monomorphic foreign-callee lane
//! (`native_trust_ir_monomorphic_foreign_callees`), every one of these calls hit
//! the fail-closed absent-callee arm:
//!
//! ```text
//! error: an unproven panic-freedom obligation for a call to an absent callee
//!        (a std/extern function whose body is not in the lowered bundle) ...
//! error: Trust strict verification failed for `probe_reverse`:
//!        1 obligation(s) were not fully verified
//! ```
//!
//! The bundle assembler excluded std/core/alloc by crate name because it keys
//! callees by bare `DefId` and bundles the GENERIC body — one entry would serve
//! every instantiation, and the bridge matches callees by rendered name. The new
//! lane instead instantiates the callee at its call site and names the bundled
//! body by its PER-INSTANCE path, admitting it only when the caller's own
//! call-site spelling (`func_operand_name`) is byte-equal to that path.
//!
//! `-Ztrust-dump=native-bundle` on this file shows the real bodies alongside the
//! callers, e.g. `["probe_reverse", "core::cmp::Ordering::reverse"]` and
//! `["probe_max_i32", "core::cmp::max::<i32>"]`.

use std::cmp::Ordering;

pub fn probe_reverse(o: Ordering) -> Ordering {
    o.reverse()
}

pub fn probe_is_lt(o: Ordering) -> bool {
    o.is_lt()
}

pub fn probe_then(a: Ordering, b: Ordering) -> Ordering {
    a.then(b)
}

pub fn probe_max_i32(a: i32, b: i32) -> i32 {
    std::cmp::max(a, b)
}

pub fn probe_is_some(o: Option<i32>) -> bool {
    o.is_some()
}

pub fn probe_len(s: &[u8]) -> usize {
    s.len()
}

fn main() {}
