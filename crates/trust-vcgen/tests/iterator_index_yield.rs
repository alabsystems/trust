// Regression (task #29): two default-mode index idioms must carry their yield /
// loop-invariant bound on the bounds VC.
//
//  * enumerate: `for (i, _) in s.iter().enumerate() { s[i] }` — the index payload
//    (the tuple's `.0` of the `Some` from `next`) satisfies `0 <= i < s.len()`,
//    traced through next -> into_iter -> enumerate -> <[T]>::iter -> slice.
//  * chained min: `n = a.len().min(b.len()).min(c.len())` — the outer min's
//    inner-result argument resolves to a stable symbol so `n <= a.len()`,
//    `n <= b.len()`, `n <= c.len()` all hold; with `i < n` every index closes.
//
// Fixtures are the REAL extracted MIR (via -Ztrust-dump=mir:<dir>).
use trust_types::*;
use trust_vcgen::generate_vcs;

/// Strip `#<token>` version suffixes (S2c flip renames `n` -> `n#token`) so these
/// structural assertions test semantic content, not the encoding.
fn strip_v(s: &str) -> String {
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

fn bounds_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .collect()
}

#[test]
fn enumerate_index_carries_slice_length_yield_fact() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/enumerate_index_mir.json"))
            .expect("fixture MIR must deserialize");
    let bounds = bounds_vcs(&func);
    assert!(!bounds.is_empty(), "enumerate indexing must produce a bounds VC");
    for vc in &bounds {
        let dbg = strip_v(&format!("{:?}", vc.formula));
        // The yield fact `i < s.len()` (a `Lt` over the index var against a
        // `__slice_len`) must be present — not just the bounds check's own length.
        assert!(
            dbg.contains("__slice_len") && dbg.contains("Lt(Var(\"i\""),
            "enumerate index bounds VC must carry the `0 <= i < s.len()` yield fact: {dbg}"
        );
    }
}

#[test]
fn chunks_exact_yields_exact_length_chunks() {
    // `for c in s.chunks_exact(4) { c[k] }` — each yielded chunk has length EXACTLY
    // 4, so the chunk's modeled `__slice_len` must be constrained `== 4`, letting
    // c[0]..c[3] discharge. The bounds VC must carry that `len == 4` fact.
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/chunks_exact_index_mir.json"))
            .expect("fixture MIR must deserialize");
    let bounds = bounds_vcs(&func);
    assert!(!bounds.is_empty(), "chunks_exact indexing must produce bounds VCs");
    assert!(
        bounds.iter().any(|vc| {
            let dbg = strip_v(&format!("{:?}", vc.formula));
            dbg.contains("__slice_len") && dbg.contains("Int(4)")
        }),
        "a chunks_exact bounds VC must carry the `len == 4` yield fact"
    );
}

#[test]
fn chained_min_bounds_all_three_slices() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/min_three_mir.json"))
            .expect("fixture MIR must deserialize");
    let bounds = bounds_vcs(&func);
    assert!(
        bounds.len() >= 3,
        "min_three must produce a[i], b[i], c[i] bounds VCs, got {}",
        bounds.len()
    );
    for vc in &bounds {
        let dbg = strip_v(&format!("{:?}", vc.formula));
        assert!(
            dbg.contains("__slice_len") && dbg.contains("\"n\""),
            "chained-min bounds VC must carry the loop-invariant `n <= len` bound: {dbg}"
        );
    }
}
