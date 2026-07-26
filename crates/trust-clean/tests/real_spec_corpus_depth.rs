// real_spec_corpus_depth — measure the TRUE verification depth of the kernel
// prover (`prove_dump_dir`) over the real-spec corpus (functions with MEANINGFUL
// postconditions + non-trivial safety VCs + negative controls), and print the
// honest scorecard so the numbers are reproducible. This test ADDS measurement;
// it does not touch prove.rs / mirsem.rs / any prover logic.
//
// Run with:
//   RUSTC_BOOTSTRAP=1 cargo test -p trust-clean --manifest-path crates/Cargo.toml \
//       --test real_spec_corpus_depth -- --nocapture
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::path::Path;

use trust_clean::vc_refute::{StructParams, check_refute_vc_with};
use trust_clean::{RefuteOutcome, prove_dump_dir};
use trust_types::VerifiableFunction;

/// Per-function honest breakdown: for each dumped function, how many safety VCs
/// and postcondition VCs does vcgen raise, and how many does the KERNEL refute
/// modulo 3 (vs left SMT-only / not-discharged). This is the load-bearing
/// negative-control evidence: the unsafe controls must show their safety VC
/// NOT discharged, and `false_post` must show its postcondition NOT discharged.
#[test]
fn real_spec_corpus_per_function_breakdown() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures").join("real-spec-corpus");
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .expect("read dir")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("json"))
        .collect();
    entries.sort();

    println!("\n========== PER-FUNCTION SAFETY/POSTCOND DISCHARGE BREAKDOWN ==========");
    println!(
        "{:<16} {:>5} {:>5} {:>6} {:>5} {:>5} {:>6}",
        "function", "safe", "sDis", "sSMT", "post", "pDis", "pSMT"
    );
    for path in entries {
        let bytes = std::fs::read(&path).unwrap();
        let Ok(func) = serde_json::from_slice::<VerifiableFunction>(&bytes) else { continue };
        // Re-create the same registry/struct-param context prove_dump_dir uses, so
        // the discharge verdict matches the scorecard exactly.
        let carriers = trust_clean::clean_ground::reachable_adt_carriers(&func);
        let mut adt_env = clean_kernel::Environment::with_prelude();
        let registry = trust_clean::clean_ground::register_adt_carriers(&mut adt_env, &carriers);
        let struct_params = StructParams::from_function(&func, &registry);

        // NOTE: this raw breakdown calls the kernel refuter WITHOUT prove.rs's
        // private `augment_with_type_bounds` (we must not touch prove.rs), so the
        // discharged counts here are a LOWER BOUND vs the authoritative scorecard.
        // The negative-control conclusion is robust either way: an unsafe VC is
        // NEVER refuted, augmentation or not.
        let (mut safe_n, mut safe_dis, mut post_n, mut post_dis) = (0, 0, 0, 0);
        for vc in trust_vcgen::generate_vcs(&func) {
            let refuted = matches!(
                check_refute_vc_with(&vc.formula, &struct_params),
                Some(RefuteOutcome::RefutedModulo3)
            );
            if matches!(vc.kind, trust_types::VcKind::Postcondition) {
                post_n += 1;
                if refuted {
                    post_dis += 1;
                }
            } else {
                safe_n += 1;
                if refuted {
                    safe_dis += 1;
                }
            }
        }
        println!(
            "{:<16} {:>5} {:>5} {:>6} {:>5} {:>5} {:>6}",
            func.def_path,
            safe_n,
            safe_dis,
            safe_n - safe_dis,
            post_n,
            post_dis,
            post_n - post_dis
        );
    }
    println!("=====================================================================");
    println!("(safe=safety VCs, sDis=kernel-discharged, sSMT=not-kernel-discharged;");
    println!(" post=postcond VCs, pDis=kernel-discharged, pSMT=not-discharged)\n");
}

#[test]
fn real_spec_corpus_true_depth_report() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures").join("real-spec-corpus");
    if !dir.exists() {
        panic!("real-spec-corpus fixtures missing at {}", dir.display());
    }
    let sc = prove_dump_dir(&dir).expect("read real-spec-corpus dumps");

    println!("\n================ REAL-SPEC CORPUS TRUE-DEPTH SCORECARD ================");
    println!("total functions loaded          : {}", sc.total);
    println!();
    println!("--- contract INHABITATION / grounding (NOT depth) ---");
    println!("inhabited (contract PROVEN)     : {}", sc.inhabited);
    println!("type-grounded, not inhabited    : {}", sc.type_grounded_not_inhabited);
    println!("not grounded                    : {}", sc.not_grounded);
    println!();
    println!("--- obligation accounting ---");
    println!("total obligations               : {}", sc.total_obligations);
    println!("postcondition obligations       : {}", sc.postcondition_obligations);
    println!("safety obligations              : {}", sc.safety_obligations);
    println!("safety KERNEL-discharged (mod 3): {}", sc.safety_discharged);
    println!(
        "safety SMT-only / not-discharged: {}",
        sc.safety_obligations.saturating_sub(sc.safety_discharged)
    );
    println!();
    println!("--- verification DEPTH (faithfulness, modulo 3) ---");
    println!("FULLY FAITHFUL (capstone)       : {}", sc.fully_faithful);
    println!("whole-function faithful         : {}", sc.faithfulness_full);
    println!("operand-certified (Lemma 1A)    : {}", sc.faithfulness_certified);
    println!("safety-VC faithful              : {}", sc.safety_vc_faithful);
    println!(
        "  overflow / usub / signed-ovf  : {} / {} / {}",
        sc.safety_vc_faithful_overflow,
        sc.safety_vc_faithful_usub,
        sc.safety_vc_faithful_signed_overflow
    );
    println!(
        "  bounds / div / rem            : {} / {} / {}",
        sc.safety_vc_faithful_bounds, sc.safety_vc_faithful_div, sc.safety_vc_faithful_rem
    );
    println!("mirsem refinement proven        : {}", sc.mirsem_refinement_proven);
    println!("mirsem branch-refinement proven : {}", sc.mirsem_branch_refinement_proven);
    println!("per-function LOOP cert (6LF)    : {}", sc.loop_refinement_proven);
    println!("per-function TOTAL cert (6LT)   : {}", sc.loop_total_correct_proven);
    println!();
    println!("--- SOUNDNESS (MUST be 0) ---");
    println!("kernel_rejected                 : {}", sc.kernel_rejected);
    if !sc.rejections.is_empty() {
        println!("rejections                      : {:?}", sc.rejections);
    }
    println!();
    println!("proven set                      : {:?}", sc.proven);
    println!();
    println!("HEADLINE       : {}", sc.headline());
    println!("DEPTH HEADLINE : {}", sc.depth_headline());
    println!("DEPTH LINE     : {}", sc.depth_line());
    println!("=======================================================================\n");

    // The only HARD assertion is soundness: the kernel must never accept a
    // constructed inhabitant that is wrong. Everything else is measured + printed,
    // not asserted — the honest number is the deliverable, whatever it is.
    assert_eq!(sc.kernel_rejected, 0, "UNSOUND kernel acceptance: {:?}", sc.rejections);
    assert!(sc.total > 0, "expected the corpus to load");
    // STEP 6LF — the per-function loop instantiation is WIRED: at least one function
    // (`loop_keep_zero`) carries a kernel-checked per-function loop certificate. The
    // prior fully-faithful depth (>= 11) must NOT regress.
    assert!(
        sc.loop_refinement_proven >= 1,
        "at least one function must carry a per-function loop certificate (6LF), got {}",
        sc.loop_refinement_proven
    );
    // STEP 6LT — the per-function TOTAL-correctness instantiation is WIRED: `loop_keep_zero`
    // carries a kernel-checked total-correctness certificate (invariant-at-halt AND
    // termination, with a PROVIDED ranking, modulo 3).
    assert!(
        sc.loop_total_correct_proven >= 1,
        "at least one function must carry a per-function TOTAL-correctness certificate (6LT), got {}",
        sc.loop_total_correct_proven
    );
    // The fully-faithful depth has RISEN to 19 with the COMPLETED stride termination and the
    // MULTI-STATEMENT accumulator: `stride_up` (`while i<n { i=i+2 }`) is now FULLY FAITHFUL
    // (its termination is TOTAL via the synthesized stride ranking `toNat(n-i)` + the
    // kernel-checked `strideRankDecrease`/`toNatMono` lemmas — the `+2` overflow VC is a
    // MODELED signed-add overflow), and `accum` (`while i<n { s=s+1; i=i+1 }`) is FULLY
    // FAITHFUL via the synthesized accumulator invariant `0 <= s` (interval lower bound on a
    // SECOND mutable local, preserved across a two-assignment body). This is a NON-REGRESSION
    // floor — it must not drop below 19.
    assert!(
        sc.fully_faithful >= 19,
        "the fully-faithful depth (>= 19, with TOTAL stride termination + the multi-statement \
         accumulator) must not regress, got {}",
        sc.fully_faithful
    );
}

/// REGRESSION (PART 1 + PART 2): the REAL `stride_up` and `accum` fixtures extract to the
/// expected SYNTHESIZED loop shapes and carry BOTH a partial AND a TOTAL kernel certificate
/// modulo 3. This pins, from the actual MIR dumps (not hand-built `SemLoopFunction`s):
///   * `stride_up` (`while i<n { i=i+2 }`) → `StrideGeConst { k: 2 }`, TOTAL (termination
///     COMPLETED via `strideRankDecrease`/`toNatMono`); and
///   * `accum` (`while i<n { s=s+1; i=i+1 }`) → `AccumGeConst` (a MULTI-STATEMENT body whose
///     invariant `0<=s` is on the accumulator, a SECOND mutable local), TOTAL.
#[test]
fn stride_and_accum_extract_to_total_certificates_modulo_3() {
    use trust_clean::mirsem::{self, SynthInvariant};
    let dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures").join("real-spec-corpus");

    let load = |name: &str| -> VerifiableFunction {
        serde_json::from_slice(&std::fs::read(dir.join(format!("{name}.json"))).unwrap())
            .unwrap_or_else(|_| panic!("parse {name}.json"))
    };

    // stride_up → StrideGeConst, partial + TOTAL modulo 3.
    let su = load("stride_up");
    let su_lf = trust_clean::prove::extract_synth_loop_function_pub(&su)
        .expect("stride_up extracts to a synthesized loop");
    assert!(
        matches!(su_lf.synth_inv, Some(SynthInvariant::StrideGeConst { k: 2, .. })),
        "stride_up must extract to StrideGeConst{{k:2}}, got {:?}",
        su_lf.synth_inv
    );
    assert!(mirsem::loop_refinement_witness(&su_lf).is_some_and(|c| c.is_modulo_3()));
    assert!(
        mirsem::loop_total_correct_witness(&su_lf).is_some_and(|c| c.is_modulo_3()),
        "stride_up TERMINATION must now be TOTAL (modulo 3)"
    );

    // accum → AccumGeConst (multi-statement body), partial + TOTAL modulo 3.
    let ac = load("accum");
    let ac_lf = trust_clean::prove::extract_accum_loop_function_pub(&ac)
        .expect("accum extracts to a multi-statement accumulator loop");
    assert!(
        matches!(ac_lf.synth_inv, Some(SynthInvariant::AccumGeConst { c: 0, .. })),
        "accum must extract to AccumGeConst{{c:0}}, got {:?}",
        ac_lf.synth_inv
    );
    assert_eq!(ac_lf.body.len(), 2, "accum's body is the TWO-statement `s=s+1; i=i+1`");
    assert!(mirsem::loop_refinement_witness(&ac_lf).is_some_and(|c| c.is_modulo_3()));
    assert!(
        mirsem::loop_total_correct_witness(&ac_lf).is_some_and(|c| c.is_modulo_3()),
        "accum TOTAL correctness (invariant-over-`s`, termination-over-`i`) must be modulo 3"
    );

    // Neither emits an UNMODELED safety VC (the `+k`/`+1` overflows are MODELED), so the
    // fully-faithful gate's safety clause is satisfied for both.
    assert!(!mirsem::function_emits_unmodeled_safety_vc_pub(&su));
    assert!(!mirsem::function_emits_unmodeled_safety_vc_pub(&ac));
}
