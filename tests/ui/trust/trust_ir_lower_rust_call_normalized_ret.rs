//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-RCN): the rust-call havoc return fence NORMALIZES before it
//! judges. The signature is built with `.skip_normalization()`, so calling
//! through a `Box<dyn FnMut() -> T>` presents the return as the unresolved
//! projection `<Box<dyn FnMut()> as FnOnce<()>>::Output` — which the fence,
//! written to accept unit/scalar/thin-sized-ref, was rejecting on SPELLING
//! rather than on shape.
//!
//! `cycle_safe_normalize` is fail-closed by construction (it returns the type
//! unchanged whenever a param, infer var, placeholder, opaque or escaping bound
//! var is present), and it is the CYCLE-SAFE spelling deliberately: a raw
//! `try_normalize_erasing_regions` inside `mir_built` is the documented E0391
//! hazard, because revealing a TAIT re-enters `type_of_opaque` -> borrowck ->
//! the in-flight `mir_built`.

pub fn call_boxed_unit(mut f: Box<dyn FnMut()>) {
    f();
}

pub fn call_boxed_u32(mut f: Box<dyn FnMut() -> u32>) -> u32 {
    f()
}

fn main() {
    let mut n = 0u32;
    call_boxed_unit(Box::new(|| {}));
    let r = call_boxed_u32(Box::new(move || {
        n += 5;
        n
    }));
    assert_eq!(r, 5);
}
