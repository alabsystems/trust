//@ needs-trust-verify
//@ edition: 2021
//@ revisions: guarded nonempty guarded_write unguarded cleared
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[guarded] check-pass
//@[nonempty] check-pass
//@[guarded_write] check-pass
//@[unguarded] check-fail
//@[cleared] check-fail
//! **A `Vec` scalar index `v[i]` verifies again on a `Ty::Seq` receiver (Trust,
//! 2026-09-28).**
//!
//! Since a std `Vec` has been extracted as `Ty::Seq`, every owned-`Vec` gate that matched
//! only the `Vec` ADT name went blind. vcgen stopped emitting the `i >= len` bounds row,
//! the bridge's audited scalar-index arm stopped firing, and the B-lane bundled
//! `<Vec<T> as Index<usize>>::index` instead, whose `SliceIndex` member no root call can
//! carry. Measured: a guarded `if i < v.len() { v[i] }` over `&Vec<u32>` did not build even
//! under the DEFAULT policy ("native typed-TrustIr lowering did not complete").
//!
//! The fix is one shape predicate, `trust_vcgen`'s `ty_is_owned_vec` (`Seq`, or the legacy
//! `Vec` ADT name), asked by every owned-`Vec` gate, plus the bridge's
//! `ty_is_owned_vec_container`, plus a B-lane decline that returns `Vec` scalar
//! `Index`/`IndexMut` to the audited arm.
//!
//! * `guarded`, `nonempty`, `guarded_write`: POSITIVE. The bounds row is proved from the
//!   guard.
//! * `unguarded`: an unguarded `v[i]` is refuted. The abstract length is unconstrained,
//!   so `i >= len` is satisfiable.
//! * `cleared`: `v.clear()` then `v[0]` really panics. The `&mut` resize makes the length
//!   unrecoverable, so the fail-honest backstop reports it Unknown and `certify` refuses
//!   it. It must never pass.

#[cfg(guarded)]
pub fn at(v: &Vec<u32>, i: usize) -> u32 {
    if i < v.len() { v[i] } else { 0 }
}

#[cfg(nonempty)]
pub fn first(v: &Vec<u32>) -> u32 {
    if v.is_empty() { 0 } else { v[0] }
}

#[cfg(guarded_write)]
pub fn set(v: &mut Vec<u32>, i: usize, x: u32) {
    if i < v.len() {
        v[i] = x;
    }
}

#[cfg(unguarded)]
pub fn at(v: &Vec<u32>, i: usize) -> u32 {
    //[unguarded]~^ ERROR Trust Level 0 safety verification incomplete for `vec_scalar_index_on_seq_receiver::at`
    v[i]
}

#[cfg(cleared)]
pub fn first_after_clear(v: &mut Vec<u32>) -> u32 {
    //[cleared]~^ ERROR Trust Level 0 safety verification incomplete for `vec_scalar_index_on_seq_receiver::first_after_clear`
    v.clear();
    v[0]
}
