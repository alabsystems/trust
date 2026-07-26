// Regression (over-refutation #11 / owner drop-in decision 2026-07-06): a plain
// integer→integer `as` cast is DEFINED behavior in Rust (truncate / sign-extend /
// reinterpret — never UB), so Trust does NOT restrict the programmer with a
// CastOverflow safety obligation. Instead it TYPE-TRACKS the result to its
// target-type range so downstream bounds/overflow stay sound AND precise.
//
// Fixtures are real MIR extracted with `-Ztrust-dump=mir:<dir>`:
//   trunc:            fn(x:u32)->u8  { x as u8 }
//   trunc_then_widen: fn(x:u32)->u32 { (x as u8) as u32 + 1 }
//   oob_from_cast:    fn(..,x:u32)   { let arr=[..8..]; arr[(x as u8) as usize] }
use trust_types::*;
use trust_vcgen::generate_vcs;

fn vcs_of(name: &str) -> Vec<VerificationCondition> {
    let json = std::fs::read_to_string(format!("tests/fixtures/{name}.json")).unwrap();
    let f: VerifiableFunction = serde_json::from_str(&json).unwrap();
    generate_vcs(&f)
}

#[test]
fn truncating_cast_emits_no_overflow_obligation() {
    // `x as u8` — no CastOverflow, no UnsupportedMir → compiles.
    let vcs = vcs_of("cast_trunc");
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::CastOverflow { .. })),
        "`x as u8` is defined and must not emit CastOverflow: {vcs:#?}"
    );
    assert!(
        !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { .. })),
        "`x as u8` must not fail closed as unsupported: {vcs:#?}"
    );
}

#[test]
fn widened_cast_result_is_type_tracked_and_provable() {
    // `(x as u8) as u32 + 1`: the u8 cast result is bounded to [0,255], so the
    // Add obligation is UNSAT (proved). Assert the ≤255 type-track fact is present
    // and no CastOverflow fires.
    let vcs = vcs_of("cast_trunc_then_widen");
    assert!(!vcs.iter().any(|vc| matches!(vc.kind, VcKind::CastOverflow { .. })));
    let add = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
        .expect("the `+ 1` must still produce an ArithmeticOverflow obligation");
    let dbg = format!("{:?}", add.formula);
    // The narrowing type-track fact bounds the cast result by the target-type max.
    assert!(
        dbg.contains("Int(255)"),
        "the cast result must be type-tracked to its target-type range (<=255) so the \
         widened `+1` proves: {dbg}"
    );
}

#[test]
fn oob_index_built_from_cast_is_still_caught() {
    // SOUNDNESS: `arr[(x as u8) as usize]` over a len-8 array — the index ranges
    // 0..=255, so it can exceed 8. The bounds obligation MUST remain (and be
    // refutable), never dropped along with the cast obligation.
    let vcs = vcs_of("cast_oob_from_cast");
    let idx = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .expect("the index-from-cast must still produce a bounds obligation");
    let dbg = format!("{:?}", idx.formula);
    // The violation `index >= 8` is reachable because the cast result reaches 255 —
    // so the obligation is genuinely refutable (OOB caught), not vacuously proved.
    assert!(
        dbg.contains("Int(8)") && dbg.contains("Int(255)"),
        "bounds obligation must relate the type-tracked index (<=255) to the array \
         length (8), keeping the genuine OOB refutable: {dbg}"
    );
}
