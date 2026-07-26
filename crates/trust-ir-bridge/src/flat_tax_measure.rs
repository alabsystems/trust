//! Per-phase flat-tax measurement over the committed VerifiableFunction
//! fixtures: how long the LOWER (`lower_to_trust_ir`) and VCGEN
//! (`trust_vcgen::generate_vcs`) phases take on the common, cheap functions
//! that dominate a build. Their combined cost measures the potential upside of
//! a future complete, authenticated artifact design. The current VC-artifact
//! container is telemetry/population-only: it cannot skip either phase because
//! its key and stored vector do not prove obligation completeness, and
//! re-solving a truncated vector would not restore omitted VCs.
//!
//! This is a measurement, not a functional test: it asserts only that the two
//! phases run without panicking (a cheap smoke test), and prints a per-fixture
//! table to stderr ONLY when `TRUST_FLAT_TAX_MEASURE=1`. Run it with:
//!   TRUST_FLAT_TAX_MEASURE=1 cargo test -p trust-ir-bridge \
//!       flat_tax_measure -- --nocapture --test-threads=1

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use trust_types::VerifiableFunction;

    use crate::lower_to_trust_ir;

    /// Repetitions per phase per fixture — enough to average out scheduler
    /// noise on sub-millisecond phases without making the run slow.
    const REPS: u32 = 200;

    fn load_fixtures() -> Vec<(String, VerifiableFunction)> {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures");
        let mut out = Vec::new();
        for entry in std::fs::read_dir(dir).expect("fixtures dir readable") {
            let path = entry.expect("dir entry").path();
            if path.extension().and_then(|e| e.to_str()) != Some("json") {
                continue;
            }
            let name = path.file_stem().unwrap().to_string_lossy().into_owned();
            let json = std::fs::read_to_string(&path).expect("fixture readable");
            // Some fixtures may predate a schema field; skip unparseable ones
            // rather than fail the smoke test.
            if let Ok(func) = serde_json::from_str::<VerifiableFunction>(&json) {
                out.push((name, func));
            }
        }
        out.sort_by(|a, b| a.0.cmp(&b.0));
        out
    }

    #[test]
    fn flat_tax_phase_costs() {
        let fixtures = load_fixtures();
        assert!(!fixtures.is_empty(), "expected committed VerifiableFunction fixtures");

        let trace = std::env::var_os("TRUST_FLAT_TAX_MEASURE").is_some();
        // Under a plain `cargo test` run this stays a fast smoke test (1 pass
        // per fixture, no timing loop); the REPS-averaged timing only runs when
        // explicitly measuring, so CI never pays for it.
        let reps = if trace { REPS } else { 1 };
        if trace {
            eprintln!(
                "\n{:<18} {:>6} {:>12} {:>12} {:>12}",
                "fixture", "vcs", "lower_us", "vcgen_us", "sum_us"
            );
        }

        let (mut tot_lower, mut tot_vcgen, mut tot_vcs) = (0u128, 0u128, 0usize);
        for (name, func) in &fixtures {
            // Smoke: both phases must run. `lower_to_trust_ir` may legitimately
            // return Err for a not-yet-lowerable fixture — that is the `None`
            // fallback the cache key path already handles, so we still MEASURE
            // vcgen for it but record lowering as the failing cost.
            let lowered_ok = lower_to_trust_ir(func).is_ok();

            let t = Instant::now();
            for _ in 0..reps {
                let _ = std::hint::black_box(lower_to_trust_ir(std::hint::black_box(func)));
            }
            let lower_us = t.elapsed().as_nanos() / u128::from(reps) / 1000;

            let t = Instant::now();
            for _ in 0..reps {
                let _ = std::hint::black_box(trust_vcgen::generate_vcs(std::hint::black_box(func)));
            }
            let vcgen_us = t.elapsed().as_nanos() / u128::from(reps) / 1000;

            // Discharge-inclusive cost (fixpoint + interval discharge + augment)
            // — what the compiler actually runs. `raw_walk` = generate_vcs (the
            // raw generation walk); `discharge_delta` = the remaining work.
            // This is cost measurement only; the quarantined artifact cache
            // always reruns both paths regardless of an observed hit.
            let t = Instant::now();
            for _ in 0..reps {
                let _ = std::hint::black_box(trust_vcgen::generate_vcs_with_discharge(
                    std::hint::black_box(func),
                ));
            }
            let discharge_us = t.elapsed().as_nanos() / u128::from(reps) / 1000;
            let discharge_delta = discharge_us.saturating_sub(vcgen_us);

            let nvcs = trust_vcgen::generate_vcs(func).len();
            tot_lower += lower_us;
            tot_vcgen += vcgen_us;
            tot_vcs += nvcs;

            if trace {
                eprintln!(
                    "{:<14} {:>4} raw_walk={:>7} discharge_delta={:>7} full={:>7}",
                    name, nvcs, vcgen_us, discharge_delta, discharge_us,
                );
                eprintln!(
                    "{:<18} {:>6} {:>12} {:>12} {:>12}{}",
                    name,
                    nvcs,
                    lower_us,
                    vcgen_us,
                    lower_us + vcgen_us,
                    if lowered_ok { "" } else { "  (lower=Err)" }
                );
            }
        }

        if trace {
            let n = fixtures.len() as u128;
            eprintln!(
                "{:<18} {:>6} {:>12} {:>12} {:>12}",
                "TOTAL",
                tot_vcs,
                tot_lower,
                tot_vcgen,
                tot_lower + tot_vcgen
            );
            eprintln!(
                "{:<18} {:>6} {:>12} {:>12} {:>12}",
                "MEAN/fixture",
                tot_vcs / fixtures.len(),
                tot_lower / n,
                tot_vcgen / n,
                (tot_lower + tot_vcgen) / n
            );
            eprintln!(
                "\nInterpretation: MEAN (lower+vcgen)/fixture is the maximum \
                 prospective warm-rebuild saving. The current cache remains \
                 observation-only; no skip is authorized without a complete, \
                 collision-resistant input envelope and authenticated \
                 obligation-completeness commitment.\n"
            );
        }
    }

    /// The load-bearing SOUNDNESS test for the VC-artifact-cache raw/discharge
    /// split (task #37): for every fixture, prove that
    ///   (a) the CAPTURING cold variant is verdict-identical to the combined fn, and
    ///   (b) measurement-only re-discharge of the captured raw reproduces the
    ///       same result.
    /// This tests a prospective split only. The compiler does not use this
    /// helper as a cache-hit verdict path and still performs fresh generation;
    /// parity here grants no authority to skip that work. Compared via serde
    /// (VC has no PartialEq); deterministic for a fixed input.
    #[test]
    fn split_capturing_and_rehydrate_match_combined() {
        use trust_vcgen::VcgenContext;
        type GenResult = (
            Vec<trust_types::VerificationCondition>,
            Vec<(trust_types::VerificationCondition, trust_types::VerificationResult)>,
        );
        fn key(r: &GenResult) -> String {
            serde_json::to_string(r).expect("gen result serializes")
        }

        let fixtures = load_fixtures();
        assert!(!fixtures.is_empty());
        let empty_spans: std::collections::HashSet<trust_types::SourceSpan> =
            std::collections::HashSet::new();
        let mut checked_raw = 0usize;

        for (name, func) in &fixtures {
            let summaries = trust_vcgen::SummaryDatabase::new();
            let ctx = VcgenContext::for_function(func.def_path.clone());

            // Combined reference (the function the compiler's cold path mirrors).
            let combined: GenResult =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context(
                    func,
                    &summaries,
                    false,
                    &ctx,
                );
            let combined_key = key(&combined);

            // (a) capturing cold variant == combined (byte-for-byte result).
            let (cap_solver, cap_discharged, raw) =
                trust_vcgen::generate_vcs_capturing_raw_body_with_context(
                    func,
                    &summaries,
                    false,
                    &ctx,
                    &empty_spans,
                );
            assert_eq!(
                key(&(cap_solver, cap_discharged)),
                combined_key,
                "capturing variant diverged from combined for `{name}`"
            );

            // (b) prospective measurement-only re-discharge == combined. This
            // is not the compiler cache path and authorizes no generation skip.
            if let Some(raw_body) = raw {
                let rehydrated = trust_vcgen::discharge_captured_raw_body_with_context(
                    func,
                    raw_body,
                    &ctx,
                );
                assert_eq!(
                    key(&rehydrated),
                    combined_key,
                    "measurement-only raw re-discharge diverged from combined for `{name}`"
                );
                checked_raw += 1;
            }
        }
        // The fixtures must exercise the cacheable (Some-raw) path, or the test
        // proves nothing about the prospective rehydration split.
        assert!(checked_raw > 0, "no fixture produced a cacheable raw set");
    }
}
