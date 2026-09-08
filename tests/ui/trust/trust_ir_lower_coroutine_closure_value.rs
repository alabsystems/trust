//@ edition: 2021
//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-CCV): a COROUTINE-CLOSURE (`async || ..`) literal joins the
//! opaque-symbol family, both halves at once:
//!
//!   * `map_ty` gains a `ty::CoroutineClosure` arm mirroring the
//!     `ty::Coroutine` arm (the shared zero-field opaque-alias sort,
//!     `param_opaque` set) — without it the `let` binding's declared type
//!     pushes a fresh `Ty` tag and the body trades one tag for another;
//!   * the PO2b value arm's `UpvarArgs::Coroutine` match widens to include
//!     `UpvarArgs::CoroutineClosure`, with `contains_call` FORCED on the new
//!     half — the differential's real NotRun mechanisms are `contains_call`
//!     and the opaque walk, not the `symbolic` flag, so the confinement is
//!     stated where it is enforced.
//!
//! The value is fact-free (a zero-field aggregate of the opaque sort): the
//! body never splices, never samples, and a CALL through the value still
//! fails closed (`AsyncFn*` methods are not `Fn`-trait methods —
//! `Call(rust-call ABI)`).

pub struct S {
    pub path: String,
}

/// The corpus shape: an async move closure bound to a local, capturing a ref.
pub fn bind_async_closure(s: &S) -> usize {
    let c = async move || {
        let _path = &s.path;
    };
    let _keep = &c;
    s.path.len()
}

fn main() {
    let s = S { path: "abc".to_string() };
    assert_eq!(bind_async_closure(&s), 3);
}
