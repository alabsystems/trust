//@ check-fail
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
// Re-pinned 2026-10-15 (the merge of 2026-10-14 brought WS5.2, 87388a9d3ec and aa2f22aa306):
// `Function.name` is now the link-time symbol, and a GENERIC definition has none until
// per-instance lowering (B8), so `-Ztrust-ir-lower=strict` refuses each one by name at crate
// assembly ("lowered for coverage, never spliced"). Those refusals are pinned below; every
// other body must still lower, and any other strict error fails this test.
//! Trust (2026-09-14): the two leaf kinds the site-args encoder never spelled.
//!
//! A concrete callee is admitted only when `encode_site_args` can spell every
//! generic arg of the call site and of the resolved instance; anything it cannot
//! spell fails closed as `Callee(MIR site args unencodable)` +
//! `Callee(concrete instance args unencodable)`. After the 2026-09-01 tiers were
//! closed, the content-pinned census of 2026-09-14 still had 33 bodies blocked by
//! EXACTLY that pair and nothing else, and `TRUST_ENCTY_TRACE=1` named two kinds
//! for all of them: `Never` (every `thread_local!` desugaring closure, the
//! never-type corpus) and `Foreign` (the extern-types corpus). Both are leaves
//! with no args — intern-equal by construction on rebuild (`tcx.types.never`,
//! `Ty::new_foreign`) — so they take digest tags 18 and 19, APPENDED after the
//! highest tag in use. These two bodies pin the pair; each carried only the
//! encoder refusal before and must lower clean under `strict` now.
#![feature(never_type, extern_types, sized_hierarchy)]

use std::marker::PointeeSized;

unsafe extern "C" {
    pub type Opaque;
}

// `PointeeSized`, not `?Sized`: under `sized_hierarchy` a bare `?Sized` still
// implies `MetaSized`, which an extern type does not implement (E0277).
fn thin<T: PointeeSized>() -> u8 {
    //~^ ERROR NoLinkTimeSymbol(thin): no link-time symbol for `thin`
    1
}

fn pick<T>(x: u8) -> u8 {
    //~^ ERROR NoLinkTimeSymbol(pick): no link-time symbol for `pick`
    x
}

// The instantiated callee's args carry an extern type.
pub fn call_with_foreign() -> u8 {
    thin::<Opaque>()
}

// The instantiated callee's args carry `!`.
pub fn call_with_never() -> u8 {
    pick::<!>(3)
}
