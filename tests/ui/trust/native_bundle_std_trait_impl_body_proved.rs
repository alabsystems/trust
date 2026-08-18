//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! A call through a std TRAIT whose receiver is CONCRETE resolves to exactly one
//! impl body, and that body is lowered into the bundle — so the caller's
//! panic-freedom obligation is discharged by PROOF, not by a model asserting
//! that some trait method cannot panic.
//!
//! rustc keeps the TRAIT method's `DefId` in the MIR call terminator and
//! devirtualizes at monomorphization, so `needle.as_ref()` on a `&[u8]` is a
//! call to `core::convert::AsRef::as_ref` — a trait-DECLARATION callee — that
//! merely RENDERS as `<[u8] as AsRef<[u8]>>::as_ref`.
//! `native_trust_ir_monomorphic_foreign_callees` excluded trait callees
//! outright, so before this lane covered them a call through a std trait landed
//! on the fail-closed absent-callee arm no matter how trivial the impl was
//! (`impl<T> AsRef<[T]> for [T] { fn as_ref(&self) -> &[T] { self } }` is a
//! reborrow and nothing else):
//!
//! ```text
//! note: Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out,
//!       1 runtime-checked out of 1 obligation(s)
//! error: an unproven panic-freedom obligation for a call to an absent callee
//!        `<[u8] as core::convert::AsRef<[u8]>>::as_ref` ...
//! error: Trust strict verification failed for `probe_slice_as_ref`:
//!        1 obligation(s) were not fully verified
//! ```
//!
//! That reached well past `AsRef`: it is why first-party memchr's `Finder`
//! constructors could not verify (`needle.as_ref()`), and it is the same shape
//! every crate hits calling through any std trait.
//!
//! The admission rule is RESOLUTION, not naming. `Instance::try_resolve` under a
//! fully-concrete argument vector runs the same trait selection rustc's own
//! monomorphization collector and codegen run, so when it yields
//! `InstanceKind::Item` the body it names is the body that will actually
//! execute, and coherence admits at most one impl for a concrete `Self`. The
//! body then comes from the resolved instance while the bundled NAME stays the
//! syntactic `<Concrete as Trait<..>>::m` spelling, because that is what
//! `func_operand_name` renders at the call site; the identity gate compares the
//! two and declines on any mismatch. Everything resolution cannot pin down stays
//! fail-closed — see `native_bundle_std_trait_impl_stays_fail_closed.rs`.
//!
//! `-Ztrust-dump=native-bundle` on this file shows the impl bodies alongside
//! their callers, e.g. `["probe_slice_as_ref",
//! "<[u8] as core::convert::AsRef<[u8]>>::as_ref"]`.

use std::num::Wrapping;

pub fn probe_slice_as_ref(needle: &[u8]) -> &[u8] {
    needle.as_ref()
}

pub fn probe_slice_as_ref_len(needle: &[u8]) -> usize {
    let bytes: &[u8] = needle.as_ref();
    bytes.len()
}

// `impl AsRef<[u8]> for str` is NOT generic, so its body is cross-crate only
// because it is `cross_crate_inlinable` (`str::as_bytes` makes no calls). This
// probe is what notices if that stops holding.
pub fn probe_str_as_ref_bytes(needle: &str) -> &[u8] {
    needle.as_ref()
}

pub fn probe_str_as_ref_str(needle: &str) -> &str {
    needle.as_ref()
}

// An operator is a trait call too: `Add::add` on `Wrapping<u8>` is
// `Wrapping(self.0.wrapping_add(other.0))` — total, and provable once its body
// is in the bundle rather than assumed away.
pub fn probe_wrapping_add(a: Wrapping<u8>, b: Wrapping<u8>) -> Wrapping<u8> {
    a + b
}

fn main() {}
