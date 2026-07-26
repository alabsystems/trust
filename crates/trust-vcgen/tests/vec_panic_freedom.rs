// Regression (Vec panic-freedom soundness, 2026-07-07): `Vec::remove(i)`,
// `swap_remove(i)`, and `insert(i, x)` PANIC when the index is out of range
// (`i >= len` for remove/swap_remove, `i > len` for insert). That panic path was
// unmodeled, so a genuinely-unsafe `v.remove(i)` compiled clean — a hole in
// pillar-1 panic-freedom.
//
// The DANGER in modeling it: recovering the abstract `coll_len(v)` for the
// receiver lets a `.len()` tie (`let n = v.len()`) reach the obligation. But the
// tie-killer does NOT recognize remove/insert/swap_remove as resizes, so a tie
// minted BEFORE an intervening resize SURVIVES it and can discharge a genuinely
// out-of-bounds later access:
//
//     let n = v.len();   // n == coll_len(v)
//     v.remove(0);       // (unmodeled resize — tie NOT killed)
//     v.remove(n - 1);   // obligation (n-1) >= coll_len(v), with n == coll_len
//                        // → UNSAT → PROVED → FALSE-ACCEPT (v may now be empty!)
//
// So the lane is deliberately fail-honest: every Vec panic-method index emits an
// `UnsupportedMir { kind: "vec-panic-method-index-unmodeled" }` VC — preclassified
// Unknown, NEVER proved — and never a dischargeable `SliceBoundsCheck`. This
// over-refuses (conservative, acceptable); it can never false-accept. The
// completeness follow-up (a version-aware coll_len that treats remove/insert/
// swap_remove as resizes) is tracked separately.
//
// Non-Vec receivers whose `remove`/`insert` do NOT panic on an out-of-range index
// (HashMap/BTreeMap/HashSet return Option; VecDeque/String have different
// signatures) must NOT match this lane and must compile clean w.r.t. it.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn vcs(name: &str) -> Vec<VerificationCondition> {
    let json = std::fs::read_to_string(format!("tests/fixtures/{name}.json")).unwrap();
    let f: VerifiableFunction = serde_json::from_str(&json).unwrap();
    generate_vcs(&f)
}

fn vec_panic_unknowns(vcs: &[VerificationCondition]) -> usize {
    vcs.iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "vec-panic-method-index-unmodeled")
        })
        .count()
}

fn slice_bounds_checks(vcs: &[VerificationCondition]) -> usize {
    vcs.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).count()
}

#[test]
fn unconstrained_vec_remove_reports_unknown_never_proved() {
    // `fn rm(v: Vec<u8>, i: usize) { v.remove(i); }` — genuinely unsafe (i unbounded).
    let v = vcs("vp_rm");
    assert_eq!(
        vec_panic_unknowns(&v), 1,
        "Vec::remove must emit exactly one fail-honest vec-panic-method Unknown"
    );
    assert_eq!(
        slice_bounds_checks(&v), 0,
        "Vec::remove must NOT mint a dischargeable SliceBoundsCheck (that path could false-accept)"
    );
}

#[test]
fn unconstrained_vec_swap_remove_reports_unknown() {
    let v = vcs("vp_srm");
    assert_eq!(vec_panic_unknowns(&v), 1, "Vec::swap_remove must emit one vec-panic-method Unknown");
    assert_eq!(slice_bounds_checks(&v), 0, "swap_remove must not mint a dischargeable bounds check");
}

#[test]
fn unconstrained_vec_insert_reports_unknown() {
    let v = vcs("vp_ins");
    assert_eq!(vec_panic_unknowns(&v), 1, "Vec::insert must emit one vec-panic-method Unknown");
    assert_eq!(slice_bounds_checks(&v), 0, "insert must not mint a dischargeable bounds check");
}

#[test]
fn hashmap_remove_is_not_a_panic_method() {
    // `HashMap::remove` returns `Option<V>` — it never panics on a missing key, so
    // it must NOT match the Vec panic lane (compiles clean w.r.t. it).
    let v = vcs("vp_hm");
    assert_eq!(
        vec_panic_unknowns(&v), 0,
        "HashMap::remove returns Option and must not be treated as a panicking Vec method"
    );
}

#[test]
fn vec_pop_is_not_a_panic_method() {
    // `Vec::pop` is total (returns `Option<T>`, no index) — no panic obligation.
    let v = vcs("vp_pp");
    assert_eq!(
        vec_panic_unknowns(&v), 0,
        "Vec::pop takes no index and never panics — it must not match the panic lane"
    );
}

#[test]
fn len_tie_across_intervening_remove_never_false_accepts() {
    // THE regression anchor. `let n = v.len(); v.remove(0); v.remove(n - 1);` is
    // genuinely unsafe (if v has 1 element: remove(0) empties it, then remove(0)
    // panics). An earlier design recovered coll_len(v) and let the `n == coll_len`
    // tie survive the first (unmodeled) remove, discharging the second remove's
    // bound → FALSE-ACCEPT. The fix makes BOTH removes fail-honest Unknowns.
    let v = vcs("bat_rmrm");
    assert_eq!(
        vec_panic_unknowns(&v), 2,
        "both removes must be fail-honest vec-panic-method Unknowns"
    );
    assert_eq!(
        slice_bounds_checks(&v), 0,
        "SOUNDNESS: no dischargeable SliceBoundsCheck may exist — the surviving \
         .len() tie must never prove the second (genuinely OOB) remove safe"
    );
}
