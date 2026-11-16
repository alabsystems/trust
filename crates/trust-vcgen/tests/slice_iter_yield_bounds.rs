// Regression: `for w in s.windows(n) { w[k] }` and `for c in s.chunks(n) { c[k] }`
// must PROVE their sub-slice index bounds. `windows(n)` yields sub-slices of
// length EXACTLY n; `chunks(n)` of length in [1, n]. vcgen models the yielded
// slice's length (build_slice_iter_yield_guard_map) and conjoins it onto the
// `w[k]`/`c[k]` bounds VC — `len == n` (windows) or `1 <= len <= n` (chunks) —
// so the index obligation discharges instead of being false-refuted (the yielded
// sub-slice's length is otherwise havoc'd).
//
// Fixtures are the REAL extracted MIR of the loops (via -Ztrust-dump=mir:<dir>).
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn bounds_vc_formula(mir: &str) -> String {
    let func: VerifiableFunction = serde_json::from_str(mir).expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds))
        .expect("sub-slice indexing should produce a bounds VC");
    format!("{:?}", vc.formula)
}

#[test]
fn windows_index_vc_carries_exact_length() {
    // windows(2): the yielded slice length is modeled `== 2`, so its `__slice_len`
    // term is equated to the window size; the index bound then discharges.
    let dbg = bounds_vc_formula(include_str!("fixtures/windows_index_mir.json"));
    assert!(
        dbg.contains("__slice_len"),
        "windows bounds VC should reference the yielded slice length: {dbg}"
    );
    assert!(
        dbg.contains("Eq"),
        "windows yields exactly-n slices, so the length must be EQUATED (== n): {dbg}"
    );
}

#[test]
fn chunks_index_vc_carries_nonempty_length() {
    // chunks(4): the yielded slice length is modeled in [1, 4]; the `c[0]` bound
    // discharges from `len >= 1`.
    let dbg = bounds_vc_formula(include_str!("fixtures/chunks_index_mir.json"));
    assert!(
        dbg.contains("__slice_len"),
        "chunks bounds VC should reference the yielded slice length: {dbg}"
    );
}

// ── CHUNKS-MUT-PAYLOAD-1 (2026-10-12): the `_mut` chunk payload's length licence ──
//
// `for w in a.chunks_exact_mut(4) { w[3] = 1 }` was refuted with `w__slice_len = 0`, a
// length `chunks_exact_mut` never yields. Indexing through `&mut [T]` makes rustc read
// the length through its own `&raw const (*w)`, and the payload gate
// (`iterator_yield::payload_carries_global_fact`, plain `is_single_static_assignment`)
// counted that Deref-first borrow as an escape of `w`, so no `len(w) == 4` fact was
// minted. The gate is now the `{s}__slice_len` name licence
// (`slice_len_licence::licensed_slice_len_formula`), which ignores what is strictly
// inside the fat pointer (a reborrow of `*w`, an element store) and still refuses a
// reseat of `w` and a mutable borrow of `w` itself.
//
// Fixtures: the REAL extracted MIR of each function below (`-Ztrust-dump=mir:<dir>`,
// `--edition 2021 -Ztrust-verify=on --crate-type lib`, the stage 1 of `46e9afaf95`; the
// span file is the relative `chex.rs`, so there is no path to scrub).

fn fixture(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("the captured MIR fixture must deserialize")
}

/// Strip `#<token>` version suffixes so the fact reads the same on every version.
fn strip_versions(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '#' {
            while chars.peek().is_some_and(|n| n.is_ascii_alphanumeric() || *n == '_') {
                chars.next();
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// The yield fact this lane mints for a `chunks_exact_mut(4)` payload bound to `w`.
const W_LEN_IS_4: &str = "Eq(Var(\"w__slice_len\", Int), Int(4))";

fn is_bounds(kind: &VcKind) -> bool {
    matches!(kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds)
}

/// Every bounds row of `name` with its in-process `ay` verdict and whether
/// `trust-certify` certifies it.
fn bounds_rows(name: &str) -> Vec<(VerificationCondition, VerificationResult, bool)> {
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs: Vec<VerificationCondition> =
                generate_vcs(&func).into_iter().filter(|vc| is_bounds(&vc.kind)).collect();
            let router = test_router::deterministic_test_router();
            router
                .verify_all(&vcs)
                .into_iter()
                .map(|(vc, r)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    (vc, r, certified)
                })
                .collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn assert_payload_length_proves(name: &str) {
    let rows = bounds_rows(name);
    assert!(!rows.is_empty(), "{name}: the `w[3]` bounds row must be generated");
    for (vc, verdict, certified) in &rows {
        let dbg = strip_versions(&format!("{:?}", vc.formula));
        assert!(
            dbg.contains(W_LEN_IS_4),
            "{name}: the bounds row must carry the payload's `len(w) == 4` yield fact: {dbg}"
        );
        assert!(
            matches!(verdict, VerificationResult::Proved { .. }),
            "{name}: `w[3]` on a chunk of length 4 must prove; got {verdict:?}"
        );
        // The read-only `chunks_exact` twin's rows are kernel-certified on the compiler
        // (`certify` exits 0); the `_mut` rows must be too, or `certify` still refuses.
        assert!(*certified, "{name}: the proved bounds row is not kernel-certified");
    }
}

fn assert_reseated_payload_gets_no_length(name: &str) {
    let rows = bounds_rows(name);
    assert!(!rows.is_empty(), "{name}: the `w[3]` bounds row must be generated");
    for (vc, verdict, certified) in &rows {
        let dbg = strip_versions(&format!("{:?}", vc.formula));
        assert!(
            !dbg.contains(W_LEN_IS_4),
            "{name}: a reseated payload may not carry the chunk length `len(w) == 4`: {dbg}"
        );
        assert!(
            !(matches!(verdict, VerificationResult::Failed { .. }) && *certified),
            "{name}: a refuted row may not also be kernel-certified"
        );
    }
    assert!(
        rows.iter().any(|(_, r, _)| !matches!(r, VerificationResult::Proved { .. })),
        "{name}: `w[3]` on a reseated `w` (any length) is PROVED: {:?}",
        rows.iter().map(|(vc, r, _)| (vc.kind.clone(), r.clone())).collect::<Vec<_>>()
    );
}

/// `pub fn chex_mut(a: &mut [u8]) { for w in a.chunks_exact_mut(4) { w[3] = 1; } }`.
/// Before: `[bounds] FAILED`, counterexample `w__slice_len#s6_0 = 0` (no yield fact).
#[test]
fn chunks_exact_mut_payload_carries_its_exact_length() {
    assert_payload_length_proves("chunks_exact_mut_index");
}

/// `let mut it = a.chunks_exact_mut(4); while let Some(w) = it.next() { w[3] = 1; }`.
/// Before: `[bounds] FAILED`, counterexample `w__slice_len#s3_0 = 0`.
#[test]
fn chunks_exact_mut_while_let_payload_carries_its_exact_length() {
    assert_payload_length_proves("chunks_exact_mut_whilelet");
}

/// `for mut w in a.chunks_exact_mut(4) { w = &mut other[..]; w[3] = 1; }` panics for a
/// short `other`. `w` has a second whole definition, so its length name has two
/// values and no fact may be keyed on it.
#[test]
fn a_reseated_chunks_exact_mut_payload_gets_no_length() {
    assert_reseated_payload_gets_no_length("chunks_exact_mut_reseat");
}

/// `for mut w in a.chunks_exact_mut(4) { let p = &mut w; *p = &mut other[..]; w[3] = 1;
/// }` reseats `w` through a mutable borrow of the payload itself (not of `*w`).
#[test]
fn a_chunks_exact_mut_payload_reseated_through_a_borrow_gets_no_length() {
    assert_reseated_payload_gets_no_length("chunks_exact_mut_reseat_via_ref");
}
