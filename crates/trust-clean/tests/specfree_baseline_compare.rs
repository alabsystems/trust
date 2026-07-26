// specfree_baseline_compare — run the SAME kernel prover over the EXISTING
// spec-free corpora (real-corpus, guarded-real-corpus) so the real-spec-corpus
// depth numbers can be compared apples-to-apples against the spec-free baseline
// the adversarial audit critiques. Measurement only; touches no prover logic.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::path::Path;
use trust_clean::prove_dump_dir;

fn report(label: &str, rel: &str) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures").join(rel);
    if !dir.exists() {
        println!("[{label}] MISSING: {}", dir.display());
        return;
    }
    let sc = prove_dump_dir(&dir).expect("read dumps");
    let spec_free = sc.total.saturating_sub(sc.postcondition_obligations);
    println!(
        "[{label}] total={} inhabited={} | postcond_obls={} safety_obls={} safety_kernel_discharged={} safety_smt_only={} | fully_faithful={} | spec_free>={} kernel_rejected={}",
        sc.total,
        sc.inhabited,
        sc.postcondition_obligations,
        sc.safety_obligations,
        sc.safety_discharged,
        sc.safety_obligations.saturating_sub(sc.safety_discharged),
        sc.fully_faithful,
        spec_free,
        sc.kernel_rejected,
    );
    assert_eq!(sc.kernel_rejected, 0, "UNSOUND in {label}: {:?}", sc.rejections);
}

#[test]
fn compare_specfree_vs_realspec() {
    println!("\n========== SPEC-FREE BASELINE vs REAL-SPEC CORPUS ==========");
    report("real-corpus (spec-free)", "real-corpus");
    report("guarded-real-corpus (spec-free)", "guarded-real-corpus");
    report("safe-corpus", "safe-corpus");
    report("real-spec-corpus (REAL SPECS)", "real-spec-corpus");
    println!("============================================================\n");
}
