//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (2026-09-23): **an extern generic instantiated at an unsized type LINKS when its
//! signed declaration spells each parameter the way the operand is spelled.**
//!
//! The companion of `trust_ir_lower_extern_dst_instantiation_declines.rs`, pinning the other
//! direction. An extern declaration is signed from the INSTANTIATED signature, so an identity
//! `&T` read at `T = str` is `&str` — `fatptr<str>`, exactly the operand — and nothing about
//! the identity signature's thin `&T` reaches the module. Each call below is therefore linked
//! against a faithful declaration, and under `strict` a body that is declined OR refused at
//! crate assembly is an error, so every body here must stay fully lowered and spliced.
//!
//! MEASURED 2026-09-23: all of these link with a valid module on the trustc without the
//! extern-callee fat/thin gate; with it (`sig_shapes_coherent` minus its `!is_local()` early
//! return, tried 2026-09-22) `str_to_string`, `str_size`, `deref_str_assert`,
//! `container_ptr_eq`, `container_size` and `raw_dyn_is_null` were declined as
//! `Call(DST-incoherent instantiation)` — and `assert_eq!(String::from("a"), "a".to_string())`
//! in `trust_ir_lower_borrow_snapshot_wide.rs` with them. Covered: `&str` (`fatptr<str>`),
//! a raw pointer and a reference to a container with a `[u8]` TAIL (both
//! `fatptr<container-len>`, one `map_ty` rule for both), `&mut [u8]` / `&mut str` (thin on
//! both sides), a typed `*const dyn Tr` (`fatptr<trait-object>` on both sides), and a thin
//! control.

use std::fmt::Debug;

pub struct W<T: ?Sized> {
    pub h: u32,
    pub t: T,
}

pub fn thin_ptr_eq(a: &u32, b: &u32) -> bool {
    std::ptr::eq(a, b)
}

pub fn str_to_string() -> String {
    "a".to_string()
}

pub fn str_size(s: &str) -> usize {
    std::mem::size_of_val(s)
}

pub fn deref_str_assert(s: &str) {
    assert_eq!(*s, *"a");
}

pub fn container_ptr_eq(a: *const W<[u8]>, b: *const W<[u8]>) -> bool {
    std::ptr::eq(a, b)
}

pub fn container_size(a: &W<[u8]>) -> usize {
    std::mem::size_of_val(a)
}

pub fn mut_slice_utf8(a: &mut [u8]) -> bool {
    std::str::from_utf8_mut(a).is_ok()
}

pub fn mut_str_upper(s: &mut str) {
    s.make_ascii_uppercase()
}

pub fn raw_dyn_is_null(a: *const dyn Debug) -> bool {
    a.is_null()
}
