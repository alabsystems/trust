//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off --crate-type=lib
// wave-PO3: a CAPTURING closure literal at the body's DIRECT TAIL, when the
// declared return maps to the opaque-alias sort (`-> impl Fn*`), takes the
// wave-PO2b posture: the value is the fact-free opaque-alias const (the
// SAME StructId the return position minted, so the implicit Return types),
// the capture operands are deliberately NOT lowered, and `param_opaque`
// marks the body SYMBOLIC — never spliced, never sampled — so every channel
// that could observe the elided captures is structurally closed. The
// re-sort is position-exact (the ONE tail literal); every other capturing
// value position keeps the fail-closed `Closure(value position)` tag. The
// closure BODIES keep their own honest tags at their own sites.

// The measured shape (auto-trait-leak-rpass's `before`/`after`): a move
// closure capturing a Box, returned as `impl FnMut`.
pub fn counter() -> impl FnMut(i32) {
    let mut p = Box::new(0);
    move |x| *p = x
}

// A by-ref capture, returned as `impl Fn`.
pub fn reader(s: String) -> impl Fn() -> usize {
    move || s.len()
}

// NEGATIVE-shaped control: the same capturing literal NOT at an opaque
// tail (stored in a let first) keeps failing closed at its own site; this
// body must NOT lower.
pub fn stored() -> i64 {
    let mut n = Box::new(1i64);
    let f = move |x: i64| *n = x;
    let _ = f;
    9
}
