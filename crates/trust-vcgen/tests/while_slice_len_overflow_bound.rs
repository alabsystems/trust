// Regression: a `while i < s.len() { s[i]; i += 1 }` loop must PROVE that the
// `i += 1` increment cannot overflow. The only counterexample to no-overflow
// needs `i == usize::MAX` together with the loop guard `i < s.len()`, i.e.
// `s.len() == 2^64` — an IMPOSSIBLE slice length (a slice's length is always
// `<= isize::MAX`). vcgen conjoins that language invariant onto the overflow VC
// (conjoin_slice_len_bounds: every `*__slice_len` term is bounded
// `0 <= len <= isize::MAX`), removing the spurious model so the increment proves.
// Without it the SMT lane FALSE-REFUTES this safe loop ([overflow:add] FAILED).
//
// The fixture is the REAL extracted MIR of the while-loop (via -Ztrust-dump=mir:<dir>).
use trust_types::*;
use trust_vcgen::generate_vcs;

#[test]
fn while_increment_overflow_vc_bounds_slice_len() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/while_range_index_mir.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
        .expect("the `i += 1` increment should produce an ArithmeticOverflow VC");
    let dbg = format!("{:?}", vc.formula);
    // The slice-length term must be referenced AND bounded by isize::MAX
    // (9223372036854775807). The bound is what makes the no-overflow obligation
    // provable, so both must be present in the overflow VC's formula.
    assert!(
        dbg.contains("__slice_len"),
        "overflow VC should reference the loop-bounding slice length: {dbg}"
    );
    assert!(
        dbg.contains("9223372036854775807"),
        "overflow VC must conjoin the `len <= isize::MAX` language invariant: {dbg}"
    );
}
