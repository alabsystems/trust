//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on --crate-type=lib
//! Trust (2026-09-23): **a raw pointer to a DST is never signed onto an extern declaration,
//! because no single spelling of it agrees with every operand a call site can pass.**
//!
//! `recover_callee_param_tys` signs an extern callee's declaration from the INSTANTIATED
//! signature, so `std::ptr::eq::<[u8]>` is read as `fn(*const [u8], *const [u8]) -> bool`. It
//! used to spell that `*const [u8]` as the thin `ptr` — the spelling `map_ty` gives `&mut [u8]`
//! — while the operands are spelled by whatever produced them: a `&[u8]` coerced at the site
//! keeps `fatptr<slice ..>`, a `&str` keeps `fatptr<str>`, and a typed `*const [u8]` /
//! `*const str` value is `map_ty`'s raw arm, `(ptr, i64)`. Every body below except `same_thin`
//! made the validator refuse the WHOLE crate module, e.g.
//!
//!     CallArgTypeMismatch { callee: "std::ptr::eq", arg_index: 0, expected: "ptr",
//!     actual: "fatptr<slice ty.0>", .. }
//!
//! (MEASURED 2026-09-22 in ay-sat's test target, and on each body here on 2026-09-23). The
//! reader now DECLINES such a parameter: the declaration stays unsigned, crate assembly refuses
//! each calling body as `UnsignableRustAbiDeclaration` (lowered for coverage, never spliced),
//! and the rest of the module is assembled and validates. `same_thin` still links: `*const u32`
//! is thin on every route.
//!
//! The three `len` bodies are the reason the fix lives in the reader and not in the fat/thin
//! CLASS gate `sig_shapes_coherent`: `<*const [T]>::len`'s identity parameter is already
//! `*const [T]`, so no class moves under instantiation and a gate has nothing to refuse (an
//! extern-callee gate tried on 2026-09-22 left all three failing, and declined extern generics
//! the reader signs faithfully — see `trust_ir_lower_extern_dst_faithful_signings_link.rs`).
//!
//! No `.stderr` and no `dont-check-compiler-stderr`: the pin is that this lane prints NOTHING,
//! so the finalization warning fails this file on a producer that signs any of these.

pub fn same_slice(a: &[u8], b: &[u8]) -> bool {
    std::ptr::eq(a, b)
}

pub fn same_str(a: &str, b: &str) -> bool {
    std::ptr::eq(a, b)
}

pub fn same_typed_raw_slice(a: *const [u8], b: *const [u8]) -> bool {
    std::ptr::eq(a, b)
}

pub fn same_typed_raw_str(a: *const str, b: *const str) -> bool {
    std::ptr::eq(a, b)
}

pub fn coerced_raw_slice_len(a: &[u8]) -> usize {
    (a as *const [u8]).len()
}

pub fn typed_raw_slice_len(p: *const [u8]) -> usize {
    p.len()
}

pub fn typed_raw_mut_slice_len(p: *mut [u8]) -> usize {
    p.len()
}

pub fn typed_raw_str_is_null(p: *const str) -> bool {
    p.is_null()
}

pub fn same_thin(a: &u32, b: &u32) -> bool {
    std::ptr::eq(a, b)
}
