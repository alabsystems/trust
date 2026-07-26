#![crate_type = "lib"]
// MUTANT (soundness regression guard, adversarial-audit 2026-06-16): two DISTINCT
// slices `outer` and `inner` that copy-prop debug-names identically (`let s = outer;
// { let s = inner; ... }`). The `i < g` guard bounds `g = len(outer)`, but the access
// indexes `inner`. When len(inner) <= i < len(outer) this is a real OUT-OF-BOUNDS read,
// so the bounds obligation is SAT and MUST be refused (exit 1). A name-keyed slice-length
// canonical var that conflates the two `s__slice_len`s would FALSELY prove it (the hole
// `reconstruct_slice_len_formula` re-opened; closed by the `collision_safe_local_name`
// guard mirroring `trust_vcgen::place_to_var_name`).
pub fn slice_shadow_name_collision(outer: &[u32], inner: &[u32], i: usize) -> u32 {
    let s = outer;
    let g = s.len();
    {
        let s = inner;
        if i < g { s[i] } else { 0 }
    }
}
