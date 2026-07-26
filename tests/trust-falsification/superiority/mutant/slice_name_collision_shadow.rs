#![crate_type = "lib"]
// SOUNDNESS REGRESSION (name-collision false proof, found by the adversarial false-proof
// hunt). The guard `i < a.len()` bounds the index against the ORIGINAL slice `a`, but
// `let a = b` shadows `a` with a DISTINCT, possibly-shorter slice. If the slice-length
// guard were threaded by the non-unique source name "a" (the bug), `a[i]` would read the
// shadow `b` while the bound came from the original `a` — a FALSE PROOF of the bounds check
// (b can be shorter than i, an out-of-bounds read). place_to_var_name now disambiguates the
// two `a` locals, so the length guard cannot attach to the shadow: this stays NOT fully
// discharged (the `a[i]` bounds check is correctly retained).
pub fn f(a: &[u32], b: &[u32], i: usize) -> u32 {
    if i < a.len() {
        let a = b;
        return a[i];
    }
    0
}
