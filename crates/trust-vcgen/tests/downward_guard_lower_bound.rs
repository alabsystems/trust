// Regression (task #31 follow-up): a downward loop guarded by `j > K` proves a
// SECONDARY index subtraction `s[j-1]` — the guard gives the decrement result
// `j - c >= (K+1) - c` (here `j >= 1`), discharging the `j - 1` underflow.
//
// Fixture: REAL MIR of the insertion-sort inner loop
//   let mut j = s.len(); while j > 1 { j -= 1; if s[j] < s[j-1] { s.swap(j, j-1); } }
use trust_types::*;
use trust_vcgen::generate_vcs;

#[test]
fn downward_loop_carries_guard_lower_bound() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/insertion_inner_mir.json"))
            .expect("fixture MIR must deserialize");
    let has_lower = generate_vcs(&func).iter().any(|vc| {
        let d = format!("{:?}", vc.formula);
        // `Ge(_t.0, 1)` — the guard-derived lower bound on the decrement result.
        d.contains("Ge(Var(") && d.contains(".0\"") && d.contains("Int(1)")
    });
    assert!(has_lower, "downward loop with `j > 1` guard must emit the `_t.0 >= 1` lower bound");
}
