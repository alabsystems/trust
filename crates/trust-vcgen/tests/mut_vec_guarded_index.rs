// Regression (over-refutation, 2026-07-06): the EXTREMELY common idiom
// `if i < v.len() { v[i] }` over a `&mut Vec` FALSELY REFUTED, while the identical
// `&Vec` (shared) case proved. Root cause: for a `&mut Vec`, `.len()` and `v[i]` are
// each called on a distinct `&(*v)` reborrow temp, and `base_collection_step` did not
// trace those reborrow-of-deref temps back to the param, so the guard's length and the
// index obligation's length resolved to DIFFERENT `coll_len` symbols and never unified.
//
// Fix: (a) `base_collection_step` traces `_dst = &(*_src)` through to `_src`, so both
// `.len()` and `v[i]` resolve to the SAME base (the param `v`); (b) the abstract-len
// recovery peels a `&mut Vec` receiver. BOTH are gated by `local_is_mutably_borrowed`:
// every Vec resize/write reborrows `&mut *v`, tripping the gate → the length tie declines
// → a resized/mutated Vec's index stays REFUTABLE (no false-PROVE). Validated end-to-end:
// guarded read PROVES; `n=len; push; v[n]`, `clear(); v[i]`, `truncate(0); v[i]`, and
// unguarded `v[i]` all REFUTE.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn bounds_formula(name: &str) -> String {
    let json = std::fs::read_to_string(format!("tests/fixtures/{name}.json")).unwrap();
    let f: VerifiableFunction = serde_json::from_str(&json).unwrap();
    let v = generate_vcs(&f);
    let b: Vec<String> = v
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .map(|vc| format!("{:?}", vc.formula))
        .collect();
    assert!(!b.is_empty(), "{name}: expected a bounds obligation");
    b.join(" ")
}

#[test]
fn guarded_mut_vec_index_length_is_canonicalized_and_provable() {
    // The FIX: the guard's `v.len()` is tied to `coll_len(v)` (== `Var("v")`) AND the
    // index obligation is `i >= v` — so the chain `i < v ∧ i >= v` is UNSAT (proved).
    // The canonical `v` length var appears on BOTH the tie and the obligation.
    let dbg = bounds_formula("mv_guarded");
    assert!(
        dbg.matches("Var(\"v\", Int)").count() >= 2,
        "the `&mut Vec` guard length and index obligation must both resolve to the \
         canonical coll_len `v` (>=2 occurrences), unifying so the guarded index proves: {dbg}"
    );
    assert!(
        dbg.contains("Eq(Var(\"_4\", Int), Var(\"v\", Int))")
            && dbg.contains("Ge(Var(\"i\", Int), Var(\"v\", Int))"),
        "must contain the len tie `_4 == v` AND the obligation `i >= v` (contradicted by \
         the guard `i < _4`): {dbg}"
    );
}

#[test]
fn resized_mut_vec_index_stays_refutable() {
    // SOUNDNESS: `let n = v.len(); v.push(9); v[n]` — the push reborrows `&mut *v`, so
    // the length tie DECLINES: there is NO `n == v` equality, so the obligation `n >= v`
    // is satisfiable (refutable) — never a vacuous false-PROVE.
    let dbg = bounds_formula("mv_resized");
    assert!(
        !dbg.contains("Eq(Var(\"n\", Int), Var(\"v\", Int))"),
        "a RESIZED `&mut Vec` must NOT tie the stored length `n` to `coll_len` `v` (that \
         would false-PROVE an out-of-bounds index): {dbg}"
    );
}

#[test]
fn unguarded_mut_vec_index_stays_refutable() {
    // No guard: the obligation `i >= v` has `i` unconstrained → refutable.
    let dbg = bounds_formula("mv_unguarded");
    assert!(
        dbg.contains("Ge(Var(\"i\", Int), Var(\"v\", Int))")
            && !dbg.contains("Lt(Var(\"i\", Int), Var(\"v\""),
        "unguarded `v[i]` must carry the refutable obligation `i >= v` with no discharging \
         `i < v` guard: {dbg}"
    );
}
