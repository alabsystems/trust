//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A verify-off dependency with three `Drop` impls, compiled exactly the way
//! `targo` compiles every dependency unit: `-Ztrust-verify=off` (so NOTHING in
//! this file is verified) and `-Zalways-encode-mir` (so its bodies are readable
//! by a caller). Consumed by
//! `xcrate_drop_glue_dep_destructor_not_credited.rs`; see that file for the
//! defect this pins (X1, 2026-09-23).
//!
//! The crate name is deliberately NOT `trust_`-prefixed: it classifies as an
//! ordinary external dependency. `trust_xcrate_drop_glue_dep.rs` is its
//! byte-identical `trust_`-named twin for the declared-scope revision.
//!
//! `Boom` IS THE ASSERTION — its `drop` panics on 7. Do not make it total.
#![crate_name = "xcdrop_dep"]

/// Panics when dropped holding 7.
pub struct Boom(pub u32);
impl Drop for Boom {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("boom");
        }
    }
}

/// A `Drop` whose body is EMPTY. Panic-free in fact; still unverified.
pub struct Hollow(pub u32);
impl Drop for Hollow {
    fn drop(&mut self) {}
}

/// A `Drop` that writes a field and cannot panic. Panic-free in fact; still
/// unverified.
pub struct Quiet(pub u32);
impl Drop for Quiet {
    fn drop(&mut self) {
        self.0 = 0;
    }
}
