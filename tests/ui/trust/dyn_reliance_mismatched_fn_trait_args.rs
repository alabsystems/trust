//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! REGRESSION: C-FLOW's case split must not hand `Instance::try_resolve` a trait
//! reference that no impl can satisfy.
//!
//! `DynDispatchBundleFacts::coerced` is keyed by trait `DefId` ALONE, and
//! `record` files each coerced type under every SUPERTRAIT `DefId` as well.
//! Both are deliberate. Together they make the bucket an OVER-approximation for
//! any GENERIC trait: `dyn Fn(&CStr)` and `dyn FnMut(&OnceState)` are different
//! trait objects that share the `FnMut` `DefId`, so a closure coerced to the
//! first lands in the bucket the second enumerates.
//!
//! `resolve_virtual_target` then substituted that closure as `Self` while
//! KEEPING the site's own trait arguments, building
//! `<{closure ..(&CStr)} as FnMut<(&OnceState,)>>` — and `Instance::try_resolve`
//! is a codegen query with codegen's precondition, so instead of declining it
//! reached `bug!` in `codegen_select_candidate`:
//!
//! ```text
//! error: internal compiler error: compiler/rustc_traits/src/codegen.rs:45:13:
//!   Encountered error `SignatureMismatch(SignatureMismatchData {
//!     found_trait_ref: <{closure@std::sys::env::unix::getenv::{closure#0}}
//!                        as std::ops::FnMut<(&std::ffi::CStr,)>>,
//!     expected_trait_ref: <{closure@std::sys::env::unix::getenv::{closure#0}}
//!                        as std::ops::FnMut<(&std::sync::OnceState,)>>,
//!     terr: Sorts(ExpectedFound { expected: std::sync::OnceState,
//!                                 found: std::ffi::CStr }) })`
//!   selecting ... during codegen
//! ```
//!
//! ## Why THIS body, and why it is not exotic
//!
//! The two coercions have to be in one bundle, and this five-line `main` is the
//! smallest thing that puts them there — through std, not through anything this
//! file writes:
//!
//! * `env::var_os` reaches `std::sys::env::unix::getenv`, which hands a closure
//!   to `run_with_cstr` as `&dyn Fn(&CStr) -> io::Result<T>`. Principal `Fn`,
//!   so `record` files it under `FnMut` and `FnOnce` too.
//! * `process::exit` reaches `rt::cleanup`, whose `Once::call_once` hands its
//!   closure to `Once::call` as `&mut dyn FnMut(&OnceState)` — the virtual site
//!   whose case split then enumerated the wrong bucket.
//!
//! Neither call is unusual: this is the shape of essentially every build
//! script, and it is where the ICE was found (`proc-macro2`'s `build.rs`,
//! compiling the workspace of a real crate under `-Ztrust-policy=advisory`).
//! Either call ALONE compiles fine; it is the pair that builds the bucket.
//!
//! ## What the fix must NOT be
//!
//! Not "skip the branch and keep discharging". A case split is a proof only if
//! EVERY branch is checked, so a branch that is silently dropped is a
//! fail-OPEN. `resolve_virtual_target` proves the branch is well typed before
//! resolving it, and every uncertain answer declines — which declines the whole
//! site, exactly as an unresolvable target already did.
fn main() {
    let v = std::env::var_os("PATH");
    if v.is_none() {
        std::process::exit(1);
    }
    println!("{:?}", v);
}
