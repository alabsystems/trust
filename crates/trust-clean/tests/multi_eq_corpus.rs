// multi_eq_corpus — pinning regression for the MULTI-VALUE SwitchInt
// disjunctive-equality guard gap closure (2026-07-08): the REAL `core`
// stdlib `is_ascii_whitespace` MIR dumps (never hand-transcribed — see
// fixtures/multi-eq-corpus/PROVENANCE.md) now certify FULLY-FAITHFUL through
// the real production `prove_dump_dir` pipeline.
//
// Before this gap closure: `census-core-m5-2026-07-07/VERDICTS.tsv`'s own row
// for `num::<impl u8>::is_ascii_whitespace` ("multi-value SwitchInt on
// (*self) + GAP-BOOL") named this shape unclosed — a SINGLE `SwitchInt` whose
// five explicit targets all converge on one arm, which NO existing
// recognizer modeled (`sem_cf_return_of_mir`'s `switch_leaf` only handles a
// comparison-derived Bool discriminant, never a direct multi-target integer
// switch). This test is the honest, run-the-real-pipeline pin: does NOT
// touch prove.rs/mirsem.rs/trustir_multieq.rs from here — it only measures.
//
// Run with:
//   RUSTC_BOOTSTRAP=1 cargo test -p trust-clean --manifest-path crates/Cargo.toml \
//       --test multi_eq_corpus -- --nocapture

use std::path::Path;

use trust_clean::prove_dump_dir;

#[test]
fn is_ascii_whitespace_fully_faithful_real_mir() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/multi-eq-corpus");
    if !dir.exists() {
        panic!("multi-eq-corpus fixtures missing at {}", dir.display());
    }
    let sc = prove_dump_dir(&dir).expect("read multi-eq-corpus dumps");

    println!("\n============ multi-eq-corpus scorecard ============");
    println!("total                       : {}", sc.total);
    println!("inhabited                   : {}", sc.inhabited);
    println!("fully_faithful              : {}", sc.fully_faithful);
    println!("  via_trustir               : {}", sc.fully_faithful_via_trustir);
    println!("  mirsem_fallback           : {}", sc.fully_faithful_mirsem_fallback);
    println!("kernel_rejected             : {}", sc.kernel_rejected);
    println!("proven                      : {:?}", sc.proven);
    println!("=======================================================\n");

    assert_eq!(sc.kernel_rejected, 0, "UNSOUND kernel acceptance: {:?}", sc.rejections);
    assert_eq!(sc.total, 2, "expected both multi-eq-corpus dumps to load");
    assert_eq!(
        sc.fully_faithful, 2,
        "both `is_ascii_whitespace` impls (u8 + char) must be fully-faithful now \
         (the multi-value SwitchInt gap closure) — got {}",
        sc.fully_faithful
    );
    assert_eq!(
        sc.fully_faithful_via_trustir, 2,
        "both must certify via the trust-ir multi-eq lane — got {}",
        sc.fully_faithful_via_trustir
    );
}
