//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! The guard for the trait-impl arm of
//! `native_trust_ir_monomorphic_foreign_callees`.
//!
//! Admitting resolved std trait calls (see
//! `native_bundle_std_trait_impl_body_proved.rs`) is sound only because the
//! admission is keyed on RESOLUTION. A trait method is user-implementable, so
//! the tempting shortcut — "`AsRef::as_ref` is trivial, model it as total" —
//! becomes a lie the moment any crate writes the impl below, and it would
//! launder that lie into every caller in the graph. `Boom` is that crate,
//! written here on purpose.
//!
//!   * `probe_generic_as_ref` — the receiver is the bare type parameter `B`, so
//!     trait selection cannot pick an impl and `Instance::try_resolve` returns
//!     `Ok(None)`. `B = Boom` is a legal instantiation and it panics, so the
//!     R3/T5 refusal is not conservatism, it is the correct answer. This is the
//!     shape that shows up as `<B as core::convert::AsRef<[u8]>>::as_ref` in
//!     first-party memchr's generic `Finder` constructors, and it stays open
//!     until the frontier is closed by a contract, never by a blanket model.
//!   * `probe_dyn_as_ref` — a `dyn` receiver resolves to `InstanceKind::Virtual`.
//!     There is no source body behind a vtable slot, so it is the irreducible
//!     floor no amount of body-lowering reaches.
//!   * `probe_slice_index_range` — a std trait call (`SliceIndex::index`) that
//!     DOES resolve, so the new arm bundles its body. It must still fail,
//!     because the body it bundles is the real one and the real one panics on an
//!     out-of-range index. Bundling can only ADD a callee's obligations to the
//!     caller's verdict; if this probe ever passes, a body-lowering path has
//!     started discarding the obligations of the body it lowered.
//!
//! Note what is deliberately NOT probed here: a call to a LOCAL panicking impl
//! with a concrete receiver. Verification is modular, so the error lands on
//! `<Boom as AsRef<[u8]>>::as_ref` itself (below) and the caller is entitled to
//! assume a separately-verified callee. The crate still fails; the obligation is
//! just booked against the body that owns it.
//!
//! If this fixture ever compiles clean, read it as a soundness regression: some
//! trait method became total without a resolved body behind it.

pub struct Boom;

impl AsRef<[u8]> for Boom {
    fn as_ref(&self) -> &[u8] { //~ ERROR Trust strict verification failed
        panic!("a trait method is user code, and user code panics")
    }
}

pub fn probe_generic_as_ref<B: AsRef<[u8]>>(b: &B) -> usize { //~ ERROR Trust strict verification failed
    b.as_ref().len()
}

pub fn probe_dyn_as_ref(b: &dyn AsRef<[u8]>) -> usize { //~ ERROR Trust strict verification failed
    b.as_ref().len()
}

pub fn probe_slice_index_range(a: &[u8]) -> &[u8] { //~ ERROR Trust strict verification failed
    &a[1..2]
}

fn main() {}
