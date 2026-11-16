//! The real CLI boundary for the native loop. There is no fallback to prompts,
//! scripts, shell strings, a saved graph report or an agent's claimed success.
use std::process::ExitCode;

// This is an implementation prerequisite inventory, never negotiated support or
// a constructed owner. Add a transition only when the genuine operation consumes
// the SAME original source, graph, resource and result owners.
const MISSING: &[&str] = &[
    "original-protected-graph-and-build-input-custody",
    "authenticated-native-agent-proposed-source-connection",
    "same-graph-build-verify-test-and-measured-comparison",
    "ordinary-development-main-publication-owner",
];

#[cfg(unix)]
pub(super) fn timing_report(
    measurements: trust_qualification::improvement::Measurements,
) -> serde_json::Value {
    let observations = measurements.observations().clone();
    let selected = measurements.select();
    serde_json::json!({
        "scope":"actual synchronous live-verifier reduction intervals, including delivery/capture overhead; diagnostic selection only, not CPU cause or graph/proof success",
        "observed_elapsed_ns":observations,
        "complete":selected.is_ok(),
        "measured_bottleneck_candidate":selected.ok().map(|s| serde_json::json!({"crate":s.name(),"elapsed_ns":s.elapsed_ns()})),
    })
}

pub(super) fn run(json: bool) -> ExitCode {
    if json {
        println!(
            "{}",
            serde_json::json!({
                "schema":"trust.self-improve.native.v1",
                "status":"could-not-run",
                "stage":"native-prerequisites",
                "missing":MISSING,
                "source_mutation_started":false,
                "scope":"no native execution, SDK, proof, qualification or publication grant"
            })
        );
    } else {
        eprintln!(
            "targo trust self-improve: native loop could not run; original graph/SDK, authenticated agent and development publication owners are unavailable; no project work started"
        );
    }
    ExitCode::from(3)
}
