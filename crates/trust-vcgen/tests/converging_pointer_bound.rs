// Regression (task #31): the converging two-pointer idiom
//   let mut lo=0; let mut hi=s.len(); while lo<hi { hi-=1; swap(s[lo],s[hi]); lo+=1; }
// must verify. `s[hi]` rides the downward-induction fact; `s[lo]` rides the
// converging fact `lo < s.len()` — sound because at the lo-stable body blocks
// `lo < hi <= s.len()`. The fact is per-block (only where `lo` is unchanged since
// the guard), so it never reaches a post-increment `lo`.
//
// Fixture is the REAL extracted MIR (via -Ztrust-dump=mir:<dir>).
use trust_types::*;
use trust_vcgen::generate_vcs;

/// Strip `#<token>` version suffixes (the S2c flip renames `lo` -> `lo#token`) so
/// these structural assertions test semantic content, not the encoding.
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
fn converging_loop_bounds_both_indices() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/two_pointer_mir.json"))
            .expect("fixture MIR must deserialize");
    let bounds: Vec<_> = generate_vcs(&func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .collect();
    assert!(bounds.len() >= 2, "two-pointer swap must produce s[lo] and s[hi] bounds VCs");
    // Every bounds VC must carry the `lo < s.len()` converging fact (so the s[lo]
    // accesses discharge; s[hi] additionally carries the downward decrement fact).
    for vc in &bounds {
        let dbg = strip_v(&format!("{:?}", vc.formula));
        assert!(
            dbg.contains("Lt(Var(\"lo\"") && dbg.contains("s__slice_len"),
            "converging bounds VC must carry `lo < s.len()`: {dbg}"
        );
    }
}
