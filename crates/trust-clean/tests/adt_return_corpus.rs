// adt_return_corpus — pinning regression for the ADT-return gap closure
// (reports/honesty-and-ladder-2026-07-07.md, gap-queue #2): the REAL `cast`
// 0.3.0 fallible-impl MIR dumps (never hand-transcribed — see
// fixtures/adt-return-corpus/PROVENANCE.md) now certify FULLY-FAITHFUL through
// the real production `prove_dump_dir` pipeline.
//
// Before this gap closure: every one of these functions' arms construct a
// `Result<$dst, Error>` variant via `Rvalue::Aggregate(AggregateKind::Adt{..},
// ..)`, which NO recognizer modeled at all (`arm_value_rvalue_for` declines an
// `Aggregate` rvalue outright) — so each measured `inhabited=0,
// fully_faithful=0` (confirmed against the census's own VERDICTS.tsv row for
// `_64::<impl From<i16> for u16>::cast`: all-zero). This is the CONSTRUCTION
// dual of the discriminant-guard CONSUMPTION shape `either_discriminant_guard.rs`
// pins.
//
// This test is the honest, run-the-real-pipeline pin: does NOT touch
// prove.rs/mirsem.rs/trustir_adt.rs from here — it only measures.
//
// Run with:
//   RUSTC_BOOTSTRAP=1 cargo test -p trust-clean --manifest-path crates/Cargo.toml \
//       --test adt_return_corpus -- --nocapture

use std::path::Path;

use trust_clean::prove_dump_dir;

#[test]
fn cast_fallible_impls_are_fully_faithful_real_mir() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/adt-return-corpus");
    if !dir.exists() {
        panic!("adt-return-corpus fixtures missing at {}", dir.display());
    }
    let sc = prove_dump_dir(&dir).expect("read adt-return-corpus dumps");

    println!("\n============ adt-return-corpus scorecard ============");
    println!("total                       : {}", sc.total);
    println!("inhabited                   : {}", sc.inhabited);
    println!("fully_faithful              : {}", sc.fully_faithful);
    println!("  via_trustir               : {}", sc.fully_faithful_via_trustir);
    println!("  mirsem_fallback           : {}", sc.fully_faithful_mirsem_fallback);
    println!("kernel_rejected             : {}", sc.kernel_rejected);
    println!("proven                      : {:?}", sc.proven);
    println!("=======================================================\n");

    // Soundness: the kernel must never reject a constructed inhabitant.
    assert_eq!(sc.kernel_rejected, 0, "UNSOUND kernel acceptance: {:?}", sc.rejections);
    // All ten real fixtures deserialize and load.
    assert_eq!(sc.total, 10, "expected all ten adt-return-corpus dumps to load");

    // THE HEADLINE: all ten real, unmodified `cast` 0.3.0 fallible-cast impls
    // (5 `half_promotion!` direct-const-guard + 5 `from_unsigned!` temp-cast-const-guard,
    // spanning every source integer width the crate ships) now reach FULLY FAITHFUL via
    // the new trust-ir ADT-return witness — the mission's "spot-check 10" gate.
    assert_eq!(
        sc.fully_faithful, 10,
        "all ten cast-crate fallible impls must be fully-faithful now (the ADT-return \
         gap closure) — got {}",
        sc.fully_faithful
    );
    // Every one of these ten certifies via the NEW trust-ir ADT-return witness (there
    // is no MirSem lane for an ADT-typed return at all — `ground_int` cannot represent
    // one), so via_trustir must equal fully_faithful exactly (not the partial-partition
    // invariant `via_trustir + mirsem_fallback == fully_faithful` other corpora pin —
    // here mirsem_fallback is EXPECTED to be 0).
    assert_eq!(
        sc.fully_faithful_via_trustir, 10,
        "every cast fallible-impl must certify via the trust-ir ADT-return lane (no \
         MirSem lane exists for an ADT-typed return) — got {}",
        sc.fully_faithful_via_trustir
    );
    assert_eq!(sc.fully_faithful_mirsem_fallback, 0, "no MirSem lane exists for an ADT-typed return");
}
