// from_signed_corpus — pinning regression for the ADT-return 3-outcome
// GUARD-CHAIN gap closure (reports/honesty-and-ladder-2026-07-07.md, gap-queue
// #2 follow-up #1): the REAL `cast` 0.3.0 `from_signed!`-class fallible-impl
// MIR dumps (never hand-transcribed — see
// fixtures/from-signed-corpus/PROVENANCE.md) now certify FULLY-FAITHFUL
// through the real production `prove_dump_dir` pipeline.
//
// Before this gap closure: every one of these functions' guard is a CHAINED
// if/else-if/else (two sequential `SwitchInt`s), which `sem_adt_return_shape_of`
// (the flat 2-arm recognizer the ORIGINAL `adt-return-corpus` gap closure
// lands) declines outright — confirmed against `adt-return-corpus/PROVENANCE.md`'s
// own accounting: these 28 functions are exactly the "genuinely 3-outcome
// `from_signed!` shapes... OUT OF SCOPE" residue that gap closure named as a
// follow-up. This test is the honest, run-the-real-pipeline pin for THAT
// follow-up: does NOT touch prove.rs/mirsem.rs/trustir_adt.rs from here — it
// only measures.
//
// Run with:
//   RUSTC_BOOTSTRAP=1 cargo test -p trust-clean --manifest-path crates/Cargo.toml \
//       --test from_signed_corpus -- --nocapture

use std::path::Path;

use trust_clean::prove_dump_dir;

#[test]
fn from_signed_fallible_impls_are_fully_faithful_real_mir() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/from-signed-corpus");
    if !dir.exists() {
        panic!("from-signed-corpus fixtures missing at {}", dir.display());
    }
    let sc = prove_dump_dir(&dir).expect("read from-signed-corpus dumps");

    println!("\n============ from-signed-corpus scorecard ============");
    println!("total                       : {}", sc.total);
    println!("inhabited                   : {}", sc.inhabited);
    println!("fully_faithful              : {}", sc.fully_faithful);
    println!("  via_trustir               : {}", sc.fully_faithful_via_trustir);
    println!("  mirsem_fallback           : {}", sc.fully_faithful_mirsem_fallback);
    println!("kernel_rejected             : {}", sc.kernel_rejected);
    println!("proven                      : {:?}", sc.proven);
    println!("=========================================================\n");

    // Soundness: the kernel must never reject a constructed inhabitant.
    assert_eq!(sc.kernel_rejected, 0, "UNSOUND kernel acceptance: {:?}", sc.rejections);
    // All twenty-eight real fixtures deserialize and load.
    assert_eq!(sc.total, 28, "expected all twenty-eight from-signed-corpus dumps to load");

    // THE HEADLINE: all 28 real, unmodified `cast` 0.3.0 `from_signed!` fallible
    // impls (the genuinely 3-outcome guard-chain shape, spanning every
    // (src,dst) width pair the crate ships) now reach FULLY FAITHFUL via the
    // new trust-ir 3-outcome ADT-return-chain witness.
    assert_eq!(
        sc.fully_faithful, 28,
        "all 28 cast-crate from_signed! fallible impls must be fully-faithful now (the \
         3-outcome guard-chain gap closure) — got {}",
        sc.fully_faithful
    );
    // Every one of these certifies via the NEW trust-ir ADT-return-chain witness
    // (there is no MirSem lane for an ADT-typed return at all).
    assert_eq!(
        sc.fully_faithful_via_trustir, 28,
        "every from_signed! fallible-impl must certify via the trust-ir ADT-return-chain \
         lane (no MirSem lane exists for an ADT-typed return) — got {}",
        sc.fully_faithful_via_trustir
    );
    assert_eq!(sc.fully_faithful_mirsem_fallback, 0, "no MirSem lane exists for an ADT-typed return");
}
