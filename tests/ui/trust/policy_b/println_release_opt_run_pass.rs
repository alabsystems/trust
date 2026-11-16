//@ needs-trust-verify
//@ revisions: o2plain
//@ compile-flags: -Ztrust-verify=on -Copt-level=2
//@ run-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! The OPTIMIZED twin of `println_default_run_pass.rs` — `--release`-shaped.
//!
//! At `-Copt-level>=2` rustc inlines std's `format_args!` machinery into the
//! caller, and its MIR carries three casts that previously had no arm in the
//! cast accept-lists: `*const str -> *const u8` (a fat->thin metadata drop),
//! `&str -> &[u8]` on the literal, and `usize -> NonNull<Argument>` (the
//! fmt-packing transmute the extractor already admits). Each minted an
//! `unsupported_mir` row from TWO refusing lanes — measured: six `unknown`
//! obligations — poisoning the whole function, so every printing program failed
//! its release verification even after the policy-B print-backend restoration
//! greened the debug build.
//!
//! All three are DEFINED operations that design principle 9 says to MODEL, so
//! they are (identity / fresh unconstrained value; nothing is asserted, so no
//! value-dependent obligation can be falsely proved). This fixture is the
//! end-to-end pin that the release build now verifies. Its fail-closed twins
//! live beside it: `absent_dep_callee_stays_closed_opt2.rs` proves the
//! optimized lane still refuses an unverified dependency's raw deref, and the
//! per-direction refusals are unit-pinned in `trust-vcgen`'s `tests.rs`.
fn main() {
    println!("hello from an optimized trust build");
}
