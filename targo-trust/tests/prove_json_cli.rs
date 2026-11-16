//! Producer-level contract for `targo trust prove --format=json`.
//!
//! The coverage collector consumes this exact subprocess surface. A parser-only
//! test or fake JSON emitter cannot establish that the real binary publishes a
//! complete scorecard and couples its exit status to kernel/bridge acceptance.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

/// Hard outer bound on one `prove --budget-secs=1` run over a one-function
/// dump. `--budget-secs` bounds every unit of proof work — the function (1 s)
/// AND each Lean↔Clean bridge-gate step (`BRIDGE_STEP_BUDGET_SCALE` x 1 s) —
/// so a debug build stops at the first gate step that outlives its 20 s.
/// Before the gate was budgeted this same run took more than 8 minutes in a
/// debug build (killed unfinished, 2026-09-25); the bound sits well above the
/// budgeted cost and well below that.
const PROVE_DEADLINE: Duration = Duration::from_secs(300);

#[test]
fn real_producer_emits_status_bound_json_with_exact_loop_denominator() {
    let (_dump, output) = prove_count_to_with_one_second_budget();

    let stdout = String::from_utf8(output.stdout.clone()).expect("prove stdout is UTF-8 JSON");
    let document: serde_json::Value = serde_json::from_str(&stdout).unwrap_or_else(|error| {
        panic!(
            "real prove producer did not emit JSON: {error}\nstdout:\n{stdout}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    });
    assert_eq!(document["schema"], "trust.prove-scorecard.v1");
    assert_eq!(document["budget_secs_per_function"], 1);
    assert_eq!(document["bridge_gate_budget_secs_per_step"], 20);
    assert_eq!(document["scorecard"]["total"], 1);
    assert_eq!(document["scorecard"]["loop_headers_detected"], 1);
    assert_eq!(document["scorecard"]["loop_headers_recognized"], 1);
    let scorecard = &document["scorecard"];
    assert_eq!(
        scorecard["fully_faithful"].as_u64(),
        Some(
            scorecard["fully_faithful_via_trustir"].as_u64().expect("via-trustir tally")
                + scorecard["fully_faithful_mirsem_fallback"]
                    .as_u64()
                    .expect("MirSem fallback tally")
        )
    );
    let safety_faithful = scorecard["safety_vc_faithful"].as_u64().expect("safety-faithful tally");
    for field in [
        "safety_vc_faithful_overflow",
        "safety_vc_faithful_usub",
        "safety_vc_faithful_signed_overflow",
        "safety_vc_faithful_bounds",
        "safety_vc_faithful_div",
        "safety_vc_faithful_rem",
        "safety_vc_faithful_negation",
        "safety_vc_faithful_shift",
    ] {
        assert!(
            scorecard[field].as_u64().expect("safety-faithful subtype tally") <= safety_faithful,
            "{field} must be bounded by safety_vc_faithful"
        );
    }
    let proven: std::collections::BTreeSet<_> = scorecard["proven"]
        .as_array()
        .expect("proven paths")
        .iter()
        .map(|path| path.as_str().expect("proven path"))
        .collect();
    let declined: std::collections::BTreeSet<_> = scorecard["declined_paths"]
        .as_array()
        .expect("declined paths")
        .iter()
        .map(|path| path.as_str().expect("declined path"))
        .collect();
    assert!(proven.is_disjoint(&declined));

    let kernel_rejected =
        document["scorecard"]["kernel_rejected"].as_u64().expect("kernel_rejected is an integer");
    let bridge_rejected = !document["bridge_gate_error"].is_null();
    match document["status"].as_str() {
        Some("measured") => {
            assert_eq!(kernel_rejected, 0);
            assert!(!bridge_rejected);
            assert!(output.status.success(), "an accepted measured scorecard must return success");
        }
        Some("rejected") => {
            assert!(kernel_rejected > 0 || bridge_rejected);
            assert!(!output.status.success(), "a rejected scorecard must return a nonzero status");
        }
        Some("incomplete") => {
            assert_eq!(kernel_rejected, 0, "a kernel rejection outranks an incomplete gate");
            assert!(bridge_rejected, "an incomplete scorecard must name what did not finish");
            assert!(
                !output.status.success(),
                "an incomplete scorecard must return a nonzero status"
            );
        }
        status => panic!("unexpected real producer status: {status:?}"),
    }
}

/// `--budget-secs` must bound the WHOLE invocation's proof work, not just the
/// per-function phase: the Lean↔Clean bridge gate that runs after it is
/// budgeted per step too. A unit that spends the budget earns nothing — the
/// function is declined, a timed-out gate leaves the scorecard `incomplete`
/// with no bridge agreement attached — and nothing exhausted is reported
/// proven or accepted.
#[test]
fn budget_secs_bounds_the_bridge_gate_and_exhaustion_is_never_credit() {
    let started = Instant::now();
    let (_dump, output) = prove_count_to_with_one_second_budget();
    let elapsed = started.elapsed();
    let stderr = String::from_utf8_lossy(&output.stderr);
    let document: serde_json::Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("prove did not emit JSON: {error}\nstderr:\n{stderr}"));
    let scorecard = &document["scorecard"];

    // A declined (budget-exhausted) function is never proven.
    let declined_paths = scorecard["declined_paths"].as_array().expect("declined paths");
    assert_eq!(scorecard["declined"].as_u64(), Some(declined_paths.len() as u64));
    let proven = scorecard["proven"].as_array().expect("proven paths");
    for path in declined_paths {
        assert!(!proven.contains(path), "budget-exhausted {path} was reported proven");
    }

    match document["status"].as_str() {
        Some("incomplete") => {
            let error = document["bridge_gate_error"].as_str().expect("incomplete names its cause");
            assert!(
                error.starts_with("TIMEOUT")
                    && error.contains("within its 20s wall-clock step budget"),
                "an incomplete gate must report its spent step budget as a TIMEOUT, got: {error}"
            );
            assert!(
                scorecard["bridge_agreement"].is_null(),
                "a timed-out gate must attach no bridge agreement"
            );
            assert!(!output.status.success(), "a timed-out gate must not return success");
        }
        // The gate finished inside the per-step budget (a fast optimized
        // build): then it must carry its full evidence.
        Some("measured") => {
            assert!(scorecard["bridge_agreement"].is_object());
            assert!(output.status.success());
        }
        status => panic!(
            "a one-function budgeted run must be measured or incomplete, got {status:?} after \
             {elapsed:?}\nstderr:\n{stderr}"
        ),
    }
}

/// Run the real producer over one copy of the `count_to` dump with
/// `--budget-secs=1`, killing it and failing if it outlives
/// [`PROVE_DEADLINE`]. Returns the dump directory so it outlives the run.
fn prove_count_to_with_one_second_budget() -> (tempfile::TempDir, Output) {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("targo-trust is inside the repository");
    let fixture = repo.join("crates/trust-clean/fixtures/real-spec-corpus/count_to.json");
    let temporary = tempfile::tempdir().expect("create isolated dump directory");
    std::fs::copy(&fixture, temporary.path().join("count_to.json"))
        .expect("copy one real VerifiableFunction dump");

    let mut command = Command::new(targo_trust_binary());
    command
        .args([
            "trust",
            "prove",
            "--dump-dir",
            temporary.path().to_str().expect("UTF-8 temporary path"),
            "--budget-secs=1",
            "--format=json",
        ])
        .current_dir(repo);
    let output = output_within(command, PROVE_DEADLINE);
    (temporary, output)
}

/// [`Command::output`] with a hard wall-clock deadline: on expiry the child is
/// killed and the test FAILS, instead of hanging the suite for as long as the
/// child cares to run.
fn output_within(mut command: Command, deadline: Duration) -> Output {
    let started = Instant::now();
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn the real targo-trust producer");
    // Drain both pipes concurrently so a chatty child cannot block on a full
    // pipe and be misreported as a hang.
    let drain = |mut pipe: Box<dyn Read + Send>| {
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            let _ = pipe.read_to_end(&mut bytes);
            bytes
        })
    };
    let stdout = drain(Box::new(child.stdout.take().expect("piped stdout")));
    let stderr = drain(Box::new(child.stderr.take().expect("piped stderr")));
    let status = loop {
        if let Some(status) = child.try_wait().expect("poll the producer") {
            break status;
        }
        if started.elapsed() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            let stderr = stderr.join().unwrap_or_default();
            panic!(
                "`targo trust prove --budget-secs=1` did not finish within {deadline:?}: the \
                 budget is not bounding the run. stderr so far:\n{}",
                String::from_utf8_lossy(&stderr)
            );
        }
        std::thread::sleep(Duration::from_millis(50));
    };
    Output {
        status,
        stdout: stdout.join().expect("stdout drain"),
        stderr: stderr.join().expect("stderr drain"),
    }
}

fn targo_trust_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_targo-trust") {
        return PathBuf::from(path);
    }
    let mut path = std::env::current_exe().expect("current test executable path");
    path.pop();
    if path.ends_with("deps") {
        path.pop();
    }
    path.push(format!("targo-trust{}", std::env::consts::EXE_SUFFIX));
    path
}
