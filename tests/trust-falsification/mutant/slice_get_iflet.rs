#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard: assert the get'd value is 0, which CAN FAIL (`x` is
// an unconstrained u32 from a fresh `Option<&u32>`). MUST be refused (exit 1). If
// `slice::get`'s result were mis-modeled (e.g. the payload aliased to a constant),
// `assert!(x == 0)` could falsely prove — so this guards the get'd value stays free.
pub fn slice_get_iflet(s: &[u32], i: usize) -> u32 {
    if let Some(&x) = s.get(i) {
        assert!(x == 0);
        x
    } else {
        0
    }
}
