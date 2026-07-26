// either_discriminant_guard — pinning regression for the M1 discriminant-guard
// gap closure (reports/flagship-crate-census-2026-07-06.md, THE PICK): the REAL
// `either` 1.15.0 `Either::<L, R>::is_left`/`is_right` MIR dumps (never hand-
// transcribed — see fixtures/either-discriminant-corpus/PROVENANCE.md) now
// certify FULLY-FAITHFUL through the real production `prove_dump_dir` pipeline.
//
// Before this gap closure: `is_left`'s `SwitchInt` guard is `Rvalue::Discriminant`
// (an enum-tag read), which `mirsem::switch_leaf`/`clean_ground::switch_cond`
// only recognized for `Rvalue::BinaryOp` (scalar comparisons) — so `is_left`
// measured `inhabited=1, fully_faithful=0` (PARTIAL, per the census). `is_right`
// (`!is_left(self)`) was blocked transitively AND by its own gap (a
// `Call-then-UnaryOp(Not)` shape the `CallThenOp` recognizer did not admit).
//
// This test is the honest, run-the-real-pipeline pin: does NOT touch
// prove.rs/mirsem.rs/clean_ground.rs from here — it only measures.
//
// Run with:
//   RUSTC_BOOTSTRAP=1 cargo test -p trust-clean --manifest-path crates/Cargo.toml \
//       --test either_discriminant_guard -- --nocapture

use std::path::Path;

use trust_clean::prove_dump_dir;

#[test]
fn either_is_left_and_is_right_are_fully_faithful_real_mir() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/either-discriminant-corpus");
    if !dir.exists() {
        panic!("either-discriminant-corpus fixtures missing at {}", dir.display());
    }
    let sc = prove_dump_dir(&dir).expect("read either-discriminant-corpus dumps");

    println!("\n============ either-discriminant-corpus scorecard ============");
    println!("total                       : {}", sc.total);
    println!("inhabited                   : {}", sc.inhabited);
    println!("fully_faithful              : {}", sc.fully_faithful);
    println!("  via_trustir               : {}", sc.fully_faithful_via_trustir);
    println!("  mirsem_fallback           : {}", sc.fully_faithful_mirsem_fallback);
    println!("kernel_rejected             : {}", sc.kernel_rejected);
    println!("proven                      : {:?}", sc.proven);
    println!("================================================================\n");

    // Soundness: the kernel must never reject a constructed inhabitant.
    assert_eq!(sc.kernel_rejected, 0, "UNSOUND kernel acceptance: {:?}", sc.rejections);
    // Both real fixtures deserialize and load.
    assert_eq!(sc.total, 2, "expected both is_left.json and is_right.json to load");

    // THE HEADLINE: both is_left AND is_right now reach FULLY FAITHFUL — is_right
    // consuming is_left's certified-callee registry entry, exactly as the real
    // `prove_dump_dir` callees-first composition does over the whole corpus.
    assert_eq!(
        sc.fully_faithful, 2,
        "either::is_left and either::is_right must BOTH be fully-faithful now \
         (the discriminant-guard + Call-then-UnaryOp gap closures) — got {}",
        sc.fully_faithful
    );
    // Post-flip partition invariant (mirrors the real-spec-corpus switchover
    // test): every fully-faithful function is EITHER via-trustir OR MirSem-
    // fallback, never both, never neither.
    assert_eq!(
        sc.fully_faithful_via_trustir + sc.fully_faithful_mirsem_fallback,
        sc.fully_faithful,
        "post-flip partition: fully_faithful == via_trustir + mirsem_fallback"
    );
}
