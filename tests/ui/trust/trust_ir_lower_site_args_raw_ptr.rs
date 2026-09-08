//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
// wave-RP: `encode_site_args` could not spell a RAW POINTER, so any call
// whose generic args mention one failed the callee identity closed with
// `Callee(MIR site args unencodable)` / `Callee(concrete instance args
// unencodable)` — the two classes that cost the population 671 clean
// bodies when the concrete-callee-identity work landed
// (reports/encode-site-args-vocabulary-2026-09-01.md sizes the whole
// vocabulary gap; `TRUST_ENCTY_TRACE=1` names the refused TyKind).
//
// A raw pointer is the CHEAPEST row in that table and the only one whose
// encoding is EXACT: `SiteTy::Ref` already drops a region and rebuilds at
// `ReErased` (sound because the comparator erases regions on both sides),
// whereas `*const T` carries no region at all, so pointee + mutability
// reconstructs the identical interned type. `SiteTy::RawPtr` therefore
// mirrors the `Ref` arm across all four sites that must agree: the
// encoder, `rebuild_site_ty`, `stable_ty`, and both lineage byte
// encoders — where it takes tag 11, APPENDED on the wave-CRT discipline
// so every digest that mentions no raw pointer stays byte-identical, and
// kept DISTINCT from `Ref`'s tag 10 so `*const T` and `&T` can never
// digest equal.

pub fn takes_ptr<T>(p: *const T) -> usize {
    p as usize
}

pub fn takes_mut_ptr<T>(p: *mut T) -> usize {
    p as usize
}

// Calls whose generic args ARE raw pointers: these are the sites whose
// identity could not be pinned before. Spelled with null pointers so the
// body depends on nothing but the encoder (an address-of-a-local would
// bring in the unrelated `Borrow(non-scalar pointee)` lane).
pub fn call_with_ptr_args() -> usize {
    takes_ptr::<*const u8>(core::ptr::null())
        + takes_mut_ptr::<*mut i64>(core::ptr::null_mut())
}

// A raw pointer nested inside another encodable shape — the recursion
// must carry through tuples and references alike.
pub fn call_with_nested_ptr(t: (*const u8, bool)) -> usize {
    takes_ptr::<(*const u8, bool)>(&t)
}

fn main() {}
