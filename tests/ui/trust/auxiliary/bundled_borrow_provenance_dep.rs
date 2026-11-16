//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency compiled the way `targo` compiles every dependency unit
//! (`-Ztrust-verify=off -Zalways-encode-mir`), so a caller that declares it with
//! `-Ztrust-bundle-foreign-crate=bpdep` bundles these bodies through the
//! monomorphic foreign drain (the B-lane).
//!
//! `load_ref` and `load_transmuted_ref` both load through a `&u32` and have no
//! `Assert`, so the only thing that separates them is where that reference comes
//! from. `pass_through` and `pass_transmuted` do not load at all. Each hands a
//! reference to `load_ref`, which is clean, so the only thing that separates
//! those two is who made the reference.
//!
//! Non-generic on purpose: the declared arm admits only callees with empty
//! generic arguments.
#![crate_name = "bpdep"]

/// The reference is the parameter itself, supplied by the verifying caller.
pub fn load_ref(x: &u32) -> u32 {
    *x
}

/// The reference is fabricated from an integer by `transmute`. Unsound on
/// purpose. `function_is_borrow_provenance_clean` refuses it, because the cast
/// target is a reference and the cast is not a pointer coercion.
#[allow(integer_to_ptr_transmutes)]
pub fn load_transmuted_ref(a: usize) -> u32 {
    let r: &u32 = unsafe { core::mem::transmute(a) };
    *r
}

/// Clean, and loads nothing itself: it passes its own parameter on to `load_ref`.
pub fn pass_through(x: &u32) -> u32 {
    load_ref(x)
}

/// Fabricates the reference (refused by the classifier) but loads nothing
/// itself. The load happens in `load_ref`, which is clean, so a per-function stamp
/// would put `ValidBorrow` on a load from address `a`.
#[allow(integer_to_ptr_transmutes)]
pub fn pass_transmuted(a: usize) -> u32 {
    let r: &u32 = unsafe { core::mem::transmute(a) };
    load_ref(r)
}
