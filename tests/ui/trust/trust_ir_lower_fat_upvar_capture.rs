//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-FUC): a SINGLETON `&str` upvar capture.
//!
//! rustc TRUNCATES the capture of a variable that is itself a shared reference
//! to `v[Deref]` — a non-empty projection whose value is nonetheless the WHOLE
//! variable. The wave-UD sub-lane exists for exactly that, and its G5/G6 gates
//! already establish the truncation; only the THINNESS gates stood in the way,
//! and they were written for a lane that hands out an ADDRESS.
//!
//! Here the env field IS the value handed out, so no address is synthesised and
//! no pointee is read — this is exactly as much a by-REF capture as its thin
//! twin. `upvar_is_thin` is deliberately NOT widened: it is also read by
//! `closure_first_class_ty` and by the caller's whole-variable gate, where a
//! change would move shapes this lane has not analysed.

pub fn capture_str(s: &str) -> usize {
    let c = || s;
    c().len()
}

pub fn capture_str_indirect() -> usize {
    let s: &str = "hello";
    let c = || s;
    c().len()
}

fn main() {
    assert_eq!(capture_str("abcd"), 4);
    assert_eq!(capture_str_indirect(), 5);
}
