#![crate_type = "lib"]
// SOUNDNESS LOCK (conditional-merge mis-tie). `v` is one of two Vecs depending on `c`,
// but the only length guard is on `a`. If the length tie resolved `v`'s base to `a`
// (a naive first-found trace), the guard `k <= a.len()` would discharge `&v[..k]` even
// when `v == b` is the SHORTER vec — a false-PROVE. `base_collection_local_unique`
// returns `None` for `v` (it has two whole-local definitions, one per branch), so the
// slice bound fails closed: the verifier MUST refuse this.
pub fn cond_merge_mistie<'r>(a: &'r Vec<u8>, b: &'r Vec<u8>, c: bool, k: usize) -> &'r [u8] {
    let v = if c { a } else { b };
    if k <= a.len() { &v[..k] } else { &v[..] }
}
