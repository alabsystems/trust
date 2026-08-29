//@ needs-trust-verify
//@ build-pass
//@ compile-flags: -Z trust-verify=on -Z mir-opt-level=2 -Z inline-mir=yes -Z trust-policy=advisory
//@ dont-check-compiler-stderr
// The advisory lane reports unproved obligations here. WHICH obligations those
// are is not what this test pins — it pins that the compiler SURVIVES a body
// carrying inlined FOREIGN source scopes — and pinning their exact wording
// would make an unrelated verifier improvement look like a regression in this
// guard.
//@ dont-require-annotations: WARN

//! **Regression: a local body may contain FOREIGN source scopes.**
//!
//! `rustc_mir_transform::inline` integrates a callee by APPENDING the callee's
//! `source_scopes` verbatim into the caller. When that callee was decoded from
//! another crate's metadata, every one of those scopes carries
//! `local_data: ClearCrossCrate::Clear` — crate-local scope data is never
//! encoded cross-crate (`Decodable for ClearCrossCrate` returns `Clear`
//! whenever `D::CLEAR_CROSS_CRATE`, which the metadata decoder sets). So "the
//! body is local" does NOT imply "every scope in the body is readable here".
//!
//! No auxiliary crate is needed to arrange that: `core` is the foreign crate.
//! `iter_mut()` pulls `core::slice::IterMut::next` into this crate's MIR, and
//! that callee brings its own loop — so this body owns a dominator-proved
//! backedge whose endpoint scopes it never had.
//!
//! `stamp_loop_header_provenance` walks EVERY dominator-proved backedge of the
//! body it is handed. Until 2026-08-28 the endpoint lookup called
//! `unwrap_crate_local()`, which is `bug!("unwrapping cross-crate data")`, so
//! this file ICEd the compiler:
//!
//! ```text
//! error: internal compiler error: compiler/rustc_middle/src/mir/mod.rs:794:39:
//!        unwrapping cross-crate data
//! ```
//!
//! That took down the whole third-party verification lane. `Inline::is_enabled`
//! needs mir-opt-level >= 2 with `OptLevel::More` and no incremental, which is
//! exactly what a `[profile.dev.package."*"] opt-level = 2` gives a dependency
//! crate — while first-party units at opt-level 1 have the inliner off and
//! looked healthy. The flags above reproduce that configuration directly rather
//! than depending on a Cargo profile.
//!
//! A cleared scope is now a MISS: no HIR-loop identity, so such a backedge can
//! neither nominate a header nor be nominated as one, and the drop is counted
//! into a distinct blocker code rather than passed off as an ordinary
//! unstamped scope. Nothing here authors a loop contract, so nothing is
//! claimed and the build passes.

pub unsafe fn fd_zero(bits: *mut [i32; 32]) {
    for slot in (*bits).iter_mut() {
        *slot = 0;
    }
}

fn main() {
    let mut bits = [1i32; 32];
    unsafe { fd_zero(&mut bits) };
    std::hint::black_box(bits[0]);
}
