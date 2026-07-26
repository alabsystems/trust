// Regression (task #28): the bounded-copy idiom
//   let n = src.len().min(dst.len());
//   for i in 0..n { dst[i] = src[i]; }
// must verify. Three modeled facts combine to discharge both index checks:
//   1. range-yield invariant:        0 <= i < n
//   2. loop-invariant Ord::min bound: n <= src.len()  AND  n <= dst.len()
//   3. the `&mut [T]` metadata slice-length tie (dst.len() via FakeForPtrMetadata)
// The min bound (2) is the load-bearing addition here: it is a PATH guard that the
// loop-header join weakens away, so it must be emitted as a GLOBAL fact
// (build_min_max_facts) to reach the loop body. Without it, `i < n` alone leaves
// `n <= dst.len()` unknown and the `dst[i]`/`src[i]` checks false-refute.
//
// The fixture is the REAL extracted MIR (via -Ztrust-dump=mir:<dir>).
use trust_types::*;
use trust_vcgen::generate_vcs;

/// Strip `#<token>` version suffixes (S2c flip renames `n` -> `n#token`) so these
/// structural assertions test semantic content, not the encoding. The flip renames
/// consistently (verdict-equivalent, proven by `flip_matches_kill_stmt`).
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

#[test]
fn bounded_copy_min_bound_reaches_loop_body() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/bounded_copy_min_mir.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);

    let bounds: Vec<&VerificationCondition> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .collect();
    assert!(
        bounds.len() >= 2,
        "bounded-copy must produce both src[i] and dst[i] bounds VCs, got {}",
        bounds.len()
    );

    // Every loop-body bounds VC must carry the global `Ord::min` bound `n <= len`
    // (so the loop-header join cannot have weakened it away). Both `n` and a
    // `__slice_len` term must appear, tying the loop bound to the slice length.
    for vc in &bounds {
        let dbg = strip_v(&format!("{:?}", vc.formula));
        assert!(dbg.contains("__slice_len"), "bounds VC must reference a slice length: {dbg}");
        assert!(
            dbg.contains("\"n\""),
            "bounds VC must carry the loop-invariant min bound over `n`: {dbg}"
        );
    }
}

#[test]
fn partial_min_resolution_bounds_the_outer_index() {
    // `let m = n.min(g.len());` — one arg (`n`, a bare param) does NOT resolve, but
    // `g.len()` does. `min(n, g.len()) <= g.len()` holds regardless, so the fact
    // `m <= g.len()` must still be emitted (per-arg, not all-or-nothing) and reach
    // the outer `g[i]` bounds VC. Fixture: `fn(g: &[[u8;4]], n) 2D iteration`.
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/nested_2d_min_mir.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let outer = vcs.iter().find(|vc| {
        matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
            && format!("{:?}", vc.formula).contains("g__slice_len")
    });
    let vc = outer.expect("must produce a `g[i]` outer bounds VC");
    let dbg = strip_v(&format!("{:?}", vc.formula));
    assert!(
        dbg.contains("Le(Var(\"m\"") && dbg.contains("g__slice_len"),
        "outer index VC must carry the partial min bound `m <= g.len()`: {dbg}"
    );
}
