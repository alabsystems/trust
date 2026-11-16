//@ needs-trust-verify
//@ revisions: direct transitive unused_island
//@ compile-flags: -Z trust-verify=off
//@[direct] check-pass
//@[transitive] check-pass
//@[unused_island] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **The `dead_code` lint follows a live island `def` to the Rust `fn` it calls
//! (Trust, 2026-09-28).**
//!
//! A Rust `fn` whose only caller is an island `def` was reported "function is
//! never used", so `#![deny(dead_code)]` (or `deny(warnings)`) refused a valid
//! program. The lint walks HIR, and the call exists only in the Clean-origin
//! MIR, which is synthesized after the lint runs. The fixture
//! `clean_origin_rust_call.rs` masked the warning with `allow(dead_code)` and
//! recorded it as "increment 4 work". The resolver now records, from the
//! kernel's own terms, which Rust `fn`s and which other island `def`s each island
//! `def` names. The lint pushes those onto its worklist when the island `def` is
//! live.
//!
//! * `direct`: `main` calls `twice_inc`, which calls `inc`.
//! * `transitive`: `main` calls `outer`, which calls the island `def` `middle`,
//!   which calls `dbl`.
//! * `unused_island`: nothing live calls the island `def` (it sits in a private
//!   module), so its callee is still dead, and the lint still says so. An edge is
//!   a naming, not a reachability claim.

#![deny(dead_code)]

#[cfg(direct)]
fn inc(x: u64) -> u64 {
    x.wrapping_add(1)
}

#[cfg(direct)]
clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
}

#[cfg(transitive)]
fn dbl(x: u64) -> u64 {
    x.wrapping_mul(2)
}

#[cfg(transitive)]
clean {
    def middle (x : UInt64) : UInt64 := dbl x
    def outer (x : UInt64) : UInt64 := middle x
}

// In a PRIVATE module: an island `def` at the crate root is planted `pub`, and
// the lint seeds it as reachable, so its callee would be live, as it is for a
// `pub fn`.
#[cfg(unused_island)]
mod hidden {
    fn orphan(x: u64) -> u64 {
        //[unused_island]~^ ERROR function `orphan` is never used
        x.wrapping_add(3)
    }

    clean {
        def calls_orphan (x : UInt64) : UInt64 := orphan x
    }
}

#[cfg(direct)]
fn main() {
    let _ = twice_inc(5);
}

#[cfg(transitive)]
fn main() {
    let _ = outer(5);
}

#[cfg(unused_island)]
fn main() {}
