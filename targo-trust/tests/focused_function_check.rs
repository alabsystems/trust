#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

#[path = "support/compiler_overrides.rs"]
mod compiler_overrides;
#[path = "support/fake_trustd.rs"]
mod fake_trustd;
#[path = "support/publication_transport.rs"]
mod publication_transport;

#[test]
fn focused_check_passes_when_selected_function_is_proved_despite_nonfocused_runtime_rows() {
    let run = run_focused_check("trust-focused-check-proved", "safe_target", "proved");
    let stdout = String::from_utf8_lossy(&run.output.stdout);
    let stderr = String::from_utf8_lossy(&run.output.stderr);

    assert_eq!(
        run.output.status.code(),
        Some(0),
        "focused check should return the focused query exit code\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_no_forwarded_function_flag(&run.capture);

    let json = focused_json(&run.output);
    assert_eq!(json["query"]["function"], "safe_target");
    assert_eq!(json["focused_exit_code"], 0);
    assert_eq!(json["focused_summary"]["functions"], 1);
    assert_eq!(json["focused_summary"]["total_obligations"], 1);
    assert_eq!(json["focused_summary"]["proved"], 1);
    assert_eq!(json["focused_summary"]["runtime_checked"], 0);
    assert!(
        stderr.contains("focused exit code"),
        "terminal diagnostics should explain that focused semantics drove the exit\nstderr:\n{stderr}"
    );
    cleanup_report_path(&json);
}

#[test]
fn focused_check_fails_when_selected_function_failed() {
    let run = run_focused_check("trust-focused-check-failed", "safe_target", "failed");
    let stdout = String::from_utf8_lossy(&run.output.stdout);
    let stderr = String::from_utf8_lossy(&run.output.stderr);

    assert_eq!(
        run.output.status.code(),
        Some(1),
        "failed focused function should fail the focused entrypoint\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_no_forwarded_function_flag(&run.capture);

    let json = focused_json(&run.output);
    assert_eq!(json["focused_exit_code"], 1);
    assert_eq!(json["focused_summary"]["failed"], 1);
    cleanup_report_path(&json);
}

#[test]
fn focused_check_fails_when_selected_function_is_runtime_checked() {
    let run = run_focused_check("trust-focused-check-runtime", "safe_target", "runtime_checked");
    let stdout = String::from_utf8_lossy(&run.output.stdout);
    let stderr = String::from_utf8_lossy(&run.output.stderr);

    assert_eq!(
        run.output.status.code(),
        Some(1),
        "runtime-checked focused rows must not satisfy --require proved\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let json = focused_json(&run.output);
    assert_eq!(json["focused_exit_code"], 1);
    assert_eq!(json["focused_summary"]["total_obligations"], 1);
    assert_eq!(json["focused_summary"]["proved"], 0);
    cleanup_report_path(&json);
}

#[test]
fn focused_check_reports_no_match_as_usage_error() {
    let run = run_focused_check("trust-focused-check-no-match", "missing_target", "proved");
    let stdout = String::from_utf8_lossy(&run.output.stdout);
    let stderr = String::from_utf8_lossy(&run.output.stderr);

    assert_eq!(
        run.output.status.code(),
        Some(2),
        "missing focused selector should fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "no-match should not emit misleading JSON: {stdout}");
    assert!(
        stderr.contains("no functions matched `missing_target`"),
        "stderr should identify the missing selector\nstderr:\n{stderr}"
    );
}

#[test]
fn focused_check_live_report_downgrades_unbound_proved_before_persistence_failure() {
    let run = run_focused_check_with_blocked_report_dir(
        "trust-focused-check-blocked-report",
        "safe_target",
        "proved",
    );
    let stdout = String::from_utf8_lossy(&run.output.stdout);
    let stderr = String::from_utf8_lossy(&run.output.stderr);

    assert_eq!(
        run.output.status.code(),
        Some(2),
        "the explicitly requested report artifact must still fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_no_forwarded_function_flag(&run.capture);
    let json = focused_json(&run.output);
    assert_eq!(json["report_path"], "<live sealed compiler report>");
    assert_eq!(json["focused_exit_code"], 1);
    assert_eq!(json["focused_summary"]["proved"], 0);
    assert_eq!(json["focused_summary"]["unknown"], 1);
    assert!(
        stdout.contains("claimed a favorable outcome without an exact canonical claim digest")
            && stdout.contains("downgraded before publication"),
        "the live report must expose the safe downgrade rather than false proof credit\nstdout:\n{stdout}"
    );
    assert!(
        stderr.contains("report artifact evidence gate failed")
            && stderr.contains("focused function `safe_target` skipped"),
        "stderr should explain the fail-closed artifact gate\nstderr:\n{stderr}"
    );
}

struct FocusedRun {
    output: Output,
    capture: String,
}

fn run_focused_check(prefix: &str, selector: &str, target_outcome: &str) -> FocusedRun {
    run_focused_check_inner(prefix, selector, target_outcome, false, None)
}

fn run_focused_check_with_blocked_report_dir(
    prefix: &str,
    selector: &str,
    target_outcome: &str,
) -> FocusedRun {
    run_focused_check_inner(prefix, selector, target_outcome, true, None)
}

/// S9, revised for T14a: probe I's inherited RUSTFLAGS (an external trust-mc
/// backend, the Kani cfg and tool registration, and engine `-Cllvm-args`)
/// reach the child Cargo as the caller set them, where the sibling Targo drops
/// the backend and the LLVM arguments under the lane (its
/// `lane_inheritance_tests`); none of it enters the lane, and `targo trust
/// check` discloses the Kani surface instead of printing a silent strict PASS.
#[test]
fn inherited_trust_mc_backend_rustflags_stay_out_of_the_lane_and_are_disclosed() {
    let rustflags = "-Zcodegen-backend=/abs/librustc_codegen_trust_mc.dylib --cfg=kani \
                     -Zcrate-attr=feature(register_tool) -Zcrate-attr=register_tool(kanitool) \
                     -Cllvm-args=--reachability=harnesses";
    let run = run_focused_check_inner(
        "trust-focused-check-kani-surface",
        "safe_target",
        "proved",
        false,
        Some(rustflags),
    );
    let stdout = String::from_utf8_lossy(&run.output.stdout);
    let stderr = String::from_utf8_lossy(&run.output.stderr);

    assert!(
        stderr.contains("UNEXAMINED_KANI_SURFACE") && stderr.contains("NOT examined"),
        "an inherited trust-mc backend must be disclosed, not silently replaced\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("librustc_codegen_trust_mc.dylib"),
        "the disclosure must name the stripped flag\nstderr:\n{stderr}"
    );
    let child_rustflags = run
        .capture
        .lines()
        .filter_map(|line| line.strip_prefix("env_rustflags="))
        .collect::<Vec<_>>();
    assert_eq!(child_rustflags, [rustflags], "capture:\n{}", run.capture);
    let lane =
        run.capture.lines().filter_map(|line| line.strip_prefix("env_lane=")).collect::<Vec<_>>();
    assert_eq!(lane.len(), 1, "capture:\n{}", run.capture);
    assert!(
        !lane[0].contains("trust_mc")
            && !lane[0].contains("llvm-args")
            && !lane[0].contains("kani"),
        "an inherited flag entered the lane: {}",
        lane[0]
    );
    assert!(lane[0].contains("trust-verify-session="), "the lane carries the session: {}", lane[0]);
    if let Ok(json) = serde_json::from_slice::<Value>(&run.output.stdout) {
        cleanup_report_path(&json);
    }
}

/// TRUST-26: `targo trust check` must print the same Kani and Creusot
/// zero-authority disclosures that `targo trust build` prints. Before the fix
/// only the build arm ran those boundaries, so the two verbs disagreed about
/// what a green run covered: `check` passed a crate carrying `kani` harnesses
/// and Creusot specs without saying either had been ignored.
#[test]
fn check_discloses_kani_and_creusot_zero_authority_lanes_like_build() {
    let run = run_focused_check_with_manifest_tail(
        "trust-focused-check-ingestion-disclosure",
        "safe_target",
        "proved",
        false,
        None,
        "\n[dependencies]\nkani = \"0.1\"\ncreusot-contracts = \"0.2\"\n",
    );
    let stdout = String::from_utf8_lossy(&run.output.stdout);
    let stderr = String::from_utf8_lossy(&run.output.stderr);

    assert_eq!(
        run.output.status.code(),
        Some(0),
        "a disclosure must not change a passing check's exit code\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("targo trust check: warning:")
            && stderr.contains("declares a `kani` dependency")
            && stderr.contains("NOT examined"),
        "check must disclose the Kani zero-authority lane\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("declares a Creusot-family dependency")
            && stderr.contains("carry NO proof authority"),
        "check must disclose the Creusot zero-authority lane\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("targo trust build: warning:"),
        "the disclosure must name the verb that ran\nstderr:\n{stderr}"
    );
    if let Ok(json) = serde_json::from_slice::<Value>(&run.output.stdout) {
        cleanup_report_path(&json);
    }
}

fn run_focused_check_inner(
    prefix: &str,
    selector: &str,
    target_outcome: &str,
    block_report_dir: bool,
    inherited_rustflags: Option<&str>,
) -> FocusedRun {
    run_focused_check_with_manifest_tail(
        prefix,
        selector,
        target_outcome,
        block_report_dir,
        inherited_rustflags,
        "",
    )
}

fn run_focused_check_with_manifest_tail(
    prefix: &str,
    selector: &str,
    target_outcome: &str,
    block_report_dir: bool,
    inherited_rustflags: Option<&str>,
    manifest_tail: &str,
) -> FocusedRun {
    let temp = TempDir::new(prefix);
    let crate_dir = temp.path().join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = temp.path().join("toolchain").join("bin");
    fs::create_dir_all(&src_dir).expect("create fixture src dir");
    fs::create_dir_all(&bin_dir).expect("create fake toolchain bin dir");

    fs::write(
        crate_dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"focused-check-fixture\"\nversion = \"0.0.0\"\nedition = \"2021\"\n{manifest_tail}"
        ),
    )
    .expect("write fixture manifest");
    fs::write(
        src_dir.join("lib.rs"),
        "pub fn safe_target(x: usize) -> usize { x }\npub fn support_main(x: usize) -> usize { x }\n",
    )
    .expect("write fixture source");

    let capture_path = temp.path().join("capture.txt");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    write_executable(&bin_dir.join("trustc"), fake_trustc_script());
    write_executable(&bin_dir.join("targo"), &fake_targo_script(target_outcome, !block_report_dir));
    let _trustd = fake_trustd::install(&bin_dir);
    let report_dir = temp.path().join("focused-report");
    if block_report_dir {
        fs::write(&report_dir, "not a directory").expect("block report-dir with a file");
    }

    let mut command = Command::new(targo_trust);
    // The fixture selects its own sibling trustc. The compiler settings this
    // test was built or run with (bootstrap's `RUSTC` and `RUSTC_WRAPPER`, a
    // developer's `sccache`) must not reach the check: it would refuse them,
    // correctly, before the fake targo ever ran, and every test here would
    // fail on its capture file instead of reaching what it asserts.
    compiler_overrides::remove_inherited_compiler_overrides(&mut command);
    let output = command
        .arg("check")
        .arg("--function")
        .arg(selector)
        .arg("--format")
        .arg("json")
        .arg("--report-dir")
        .arg(&report_dir)
        .current_dir(&crate_dir)
        .env(fake_trustd::RUNTIME_DIR_ENV, _trustd.runtime_dir())
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env_remove("CARGO")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .envs(inherited_rustflags.map(|flags| ("RUSTFLAGS", flags)))
        .output()
        .expect("run focused targo-trust check with fake toolchain");

    let capture = fs::read_to_string(&capture_path).unwrap_or_else(|error| {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!(
            "fake targo should write capture file at {}\nerror: {error}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            capture_path.display()
        )
    });

    FocusedRun { output, capture }
}

fn fake_trustc_script() -> &'static str {
    r#"#!/bin/sh
verification_session=
for arg in "$@"; do
  case "$arg" in
    trust-verify-session=*) verification_session=${arg#trust-verify-session=} ;;
  esac
done
printf 'TRUST_JSON:{"type":"function_result","function":"trust_verify_probe::trust_verify_probe","package_name":null,"crate_name":"trust_verify_probe","primary_package":false,"verification_session":"%s","results":[],"proved":0,"failed":0,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":0,"cached":0,"total":0}\n' "$verification_session" >&2
printf 'TRUST_JSON:{"type":"coverage_summary","crate_name":"trust_verify_probe","package_name":"","primary_package":false,"verification_session":"%s","eligible":1,"processed":1,"function_identities":{"schema":"trustc.coverage-function-identities.v1","eligible_functions":["trust_verify_probe::trust_verify_probe"],"processed_functions":["trust_verify_probe::trust_verify_probe"]},"memory":{"schema":"trust-memory-summary/v1","counters":{}}}\n' "$verification_session" >&2
exit 0
"#
}

fn fake_targo_script(target_outcome: &str, bind_proved: bool) -> String {
    let (proved, failed, runtime_checked) = match target_outcome {
        "proved" => (1, 0, 0),
        "failed" => (0, 1, 0),
        "runtime_checked" => (0, 0, 1),
        other => panic!("unsupported fake outcome: {other}"),
    };
    let function = "focused_check_fixture::safe_target";
    let selected_payload = if target_outcome == "proved" && bind_proved {
        let result = publication_transport::proved_result(
            trust_types::VcKind::Assertion { message: "selected function".to_string() },
            function,
            "focused-check-req-1",
            "1",
        );
        serde_json::to_string(&trust_types::TransportMessage::FunctionResult(
            trust_types::FunctionTransportResult {
                stable_ids: vec!["00000000000000a1".to_string()],
                source_sha256: None,
                expanded_function_identity: None,
                modeled_facts: Vec::new(),
                function: function.to_string(),
                package_name: Some("focused-check-fixture".to_string()),
                crate_name: Some("focused_check_fixture".to_string()),
                primary_package: true,
                verification_session: "__TRUST_VERIFICATION_SESSION__".to_string(),
                runtime_checks: None,
                results: vec![result],
                proved: 1,
                failed: 0,
                unknown: 0,
                timed_out: 0,
                skipped: 0,
                runtime_checked: 0,
                cached: 0,
                total: 1,
                transport_budget: None,
            },
        ))
        .expect("serialize bound focused Proved transport")
    } else {
        serde_json::json!({
            "type": "function_result",
            "function": function,
            "package_name": "focused-check-fixture",
            "crate_name": "focused_check_fixture",
            "primary_package": true,
            "verification_session": "__TRUST_VERIFICATION_SESSION__",
            "stable_ids": ["00000000000000a1"],
            "results": [{
                "kind": "postcondition",
                "description": "selected function",
                "outcome": target_outcome,
                "solver": "fake",
                "time_ms": 1,
                // A reproducible stop, so the run is a measurement (T7b): an
                // unstamped non-proved row is `unclassified`, which exits 3.
                "reason": "fixture search ended [stop:solver-incomplete]",
            }],
            "proved": proved,
            "failed": failed,
            "unknown": 0,
            "timed_out": 0,
            "skipped": 0,
            "runtime_checked": runtime_checked,
            "cached": 0,
            "total": 1,
        })
        .to_string()
    };
    assert!(
        !selected_payload.contains('\''),
        "focused payload must remain safe for the shell single-quoted literal"
    );

    // What the native producer
    // (`src/tools/targo/src/cargo/core/compiler/build_context/project_policy.rs`,
    // `ProjectTrustPolicy::default()`) prints for a project without Trust
    // requirements. The consumer parses it with `deny_unknown_fields`.
    let empty_project_policy = r#"{"schema":"trust.project-policy.v1","policy":null,"level":null,"profile":null,"include_dependencies":null,"ir_lower":null,"verification_required":false}"#;
    format!(
        r#"#!/bin/sh
mode=build
previous_arg=
for arg in "$@"; do
  if [ "$arg" = "metadata" ]; then
    mode=metadata
  elif [ "$arg" = "trust-policy" ] && [ "$previous_arg" = "config" ]; then
    mode=trust-policy
  fi
  previous_arg="$arg"
done
# The authenticated project-policy query (`targo -Zunstable-options config
# trust-policy`) precedes lane selection and compiles nothing: answer with the
# native producer's `trust.project-policy.v1` shape for a project with no
# configured Trust requirements, and keep it out of the compile capture.
if [ "$mode" = "trust-policy" ]; then
  printf '%s\n' '{empty_project_policy}'
  exit 0
fi
# Capture the compile invocation only: `check` also runs `targo metadata`
# probes (package selection, and the post-check Kani/Creusot disclosure), and
# those must not overwrite the record of what the compile was handed.
if [ "$mode" != "metadata" ]; then
{{
  echo "program=$(basename "$0")"
  printf 'arg=%s\n' "$@"
  printf 'env_rustflags=%s\n' "$RUSTFLAGS"
  printf 'env_lane=%s\n' "$(printf '%s' "${{TRUST_TARGO_LANE_RUSTFLAGS-}}" | tr '\037' ' ')"
}} > "$TRUST_CAPTURE_FILE"
fi
package_name="focused-check-fixture"
crate_name="focused_check_fixture"
verification_session=$(printf '%s\n' "${{TRUST_TARGO_LANE_RUSTFLAGS-}}" | tr '\037' ' ' | sed -n 's/.*trust-verify-session=\([^ ]*\).*/\1/p' | head -n 1)
package_id="path+file://$PWD#$package_name@0.0.0"
manifest="$PWD/Cargo.toml"
source="$PWD/src/lib.rs"
compile_target="test-host"
compile_mode="build"
compile_kind="target"
unit_identity_sha256="cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
unit_semantics='{{"schema":"targo.trust-unit-semantics.v1","features":[],"target_cfg":["unix"],"cfg_test":false,"target_edition":"2024","target_crate_types":["rlib"],"target_harness":false,"target_proc_macro":false,"profile":{{"opt_level":"0","requested_lto":"false","effective_lto":"only-object","debuginfo":"0","debug_assertions":false,"overflow_checks":false,"rpath":false,"incremental":false,"panic":"unwind","strip":"none","rustflags":[]}},"compiler":{{"frontend":"rustc","codegen_backend":"trust-cg","rustc_release":"1.99.0-nightly","rustc_host":"test-host","rustc_verbose_version_sha256":"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"}},"unit_rustflags":["-Zcodegen-backend=trust-cg"],"manifest_lint_rustflags":[],"extra_compiler_args":[]}}'
semantics_sha256="67fbdb2e7e098b6c27117b599ec42fc343d9b18b8a040b3f570e03e6da417f94"
proof_unit="{{\"schema\":\"targo.trust-proof-unit.v2\",\"index\":0,\"mode\":\"$compile_mode\",\"role\":\"primary\",\"package_name\":\"$package_name\",\"semantics_sha256\":\"$semantics_sha256\"}}"
if [ "$mode" = "metadata" ]; then
  printf '{{"packages":[{{"id":"%s","name":"%s","version":"0.0.0","manifest_path":"%s","targets":[{{"kind":["lib"],"crate_types":["lib"],"name":"%s","src_path":"%s","edition":"2021","doc":true,"doctest":true,"test":true}}]}}],"workspace_members":["%s"],"workspace_default_members":["%s"],"workspace_root":"%s","target_directory":"%s/target","version":1}}\n' \
    "$package_id" "$package_name" "$manifest" "$crate_name" "$source" \
    "$package_id" "$package_id" "$PWD" "$PWD"
  exit 0
fi
emit_transport() {{
  escaped=$(printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g')
  printf '{{"reason":"compiler-message","package_id":"%s","trust_compile_target":"%s","trust_compile_mode":"%s","trust_compile_kind":"%s","trust_unit_identity_sha256":"%s","trust_proof_unit":%s,"target":{{"name":"%s","kind":["lib"]}},"message":{{"message":"TRUST_JSON:%s","level":"note","code":{{"code":"trust_verification_transport_v1","explanation":null}},"rendered":null,"spans":[],"children":[]}}}}\n' \
    "$package_id" "$compile_target" "$compile_mode" "$compile_kind" "$unit_identity_sha256" "$proof_unit" "$crate_name" "$escaped"
}}
printf '{{"reason":"trust-proof-inventory","schema":"targo.trust-proof-inventory.v2","include_dependencies":true,"units":[{{"trust_proof_unit":%s,"semantics":%s,"package_id":"%s","target_name":"%s","target_kinds":["lib"],"compile_target":"%s","trust_compile_mode":"%s","trust_compile_kind":"%s","trust_unit_identity_sha256":"%s"}}],"excluded_units":[]}}\n' \
  "$proof_unit" "$unit_semantics" "$package_id" "$crate_name" "$compile_target" "$compile_mode" "$compile_kind" "$unit_identity_sha256"
selected=$(printf '%s' '{selected_payload}' | sed "s/__TRUST_VERIFICATION_SESSION__/$verification_session/g")
support=$(printf '{{"type":"function_result","function":"%s::support_main","package_name":"%s","crate_name":"%s","primary_package":true,"verification_session":"%s","stable_ids":["00000000000000b2"],"results":[{{"kind":"formatting","description":"nonfocused support row","outcome":"runtime_checked","solver":"fake","time_ms":1,"reason":"fixture search ended [stop:solver-incomplete]"}}],"proved":0,"failed":0,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":1}}' \
  "$crate_name" "$package_name" "$crate_name" "$verification_session")
summary=$(printf '{{"type":"crate_summary","package_name":"%s","crate_name":"%s","primary_package":true,"verification_session":"%s","functions_analyzed":2,"functions_verified":{proved},"total_proved":{proved},"total_failed":{failed},"total_unknown":0,"total_timed_out":0,"total_skipped":0,"total_runtime_checked":%s,"total_obligations":2}}' \
  "$package_name" "$crate_name" "$verification_session" "$(({runtime_checked} + 1))")
coverage=$(printf '{{"type":"coverage_summary","crate_name":"%s","package_name":"%s","primary_package":true,"verification_session":"%s","eligible":2,"processed":2,"function_identities":{{"schema":"trustc.coverage-function-identities.v1","eligible_functions":["%s::safe_target","%s::support_main"],"processed_functions":["%s::safe_target","%s::support_main"]}},"memory":{{"schema":"trust-memory-summary/v1","counters":{{}}}}}}' \
  "$crate_name" "$package_name" "$verification_session" "$crate_name" "$crate_name" "$crate_name" "$crate_name")
emit_transport "$selected"
emit_transport "$support"
emit_transport "$coverage"
emit_transport "$summary"
printf '{{"reason":"compiler-artifact","package_id":"%s","trust_compile_target":"%s","trust_compile_mode":"%s","trust_compile_kind":"%s","trust_unit_identity_sha256":"%s","trust_proof_unit":%s,"target":{{"name":"%s","kind":["lib"]}},"profile":{{"opt_level":"0","debuginfo":0,"debug_assertions":false,"overflow_checks":false,"test":false}},"features":[],"fresh":false}}\n' \
  "$package_id" "$compile_target" "$compile_mode" "$compile_kind" "$unit_identity_sha256" "$proof_unit" "$crate_name"
printf '{{"reason":"build-finished","success":true}}\n'
exit 0
"#
    )
}

fn focused_json(output: &Output) -> Value {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!("focused check should emit JSON: {error}\nstdout:\n{stdout}\nstderr:\n{stderr}")
    })
}

fn cleanup_report_path(json: &Value) {
    let Some(report_path) = json["report_path"].as_str() else {
        return;
    };
    let Some(report_dir) = Path::new(report_path).parent() else {
        return;
    };
    let _ = fs::remove_dir_all(report_dir);
}

fn assert_no_forwarded_function_flag(capture: &str) {
    assert!(
        !capture
            .lines()
            .any(|line| line == "arg=--function" || line.starts_with("arg=--function=")),
        "--function is a targo-trust focus selector and must not be forwarded to targo: {capture}"
    );
}

/// Write a fake executable and execute it once, before the test hands it to
/// `targo-trust`.
///
/// macOS assesses a freshly written executable on its FIRST `execve`, and that
/// assessment is serialized system-wide (measured 2026-10-04: thirty new
/// two-line scripts exec'd concurrently finished 0.16 s apart, 4.8 s for the
/// last; a second exec of each took no measurable time). With the suite's
/// tests running in parallel, each copying a fresh `targo-trust` and writing
/// fresh fakes, that queue reached tens of seconds — and the first exec of the
/// fake `trustc`/`targo` now happens inside `targo-trust`'s fixed 30 s
/// project-policy setup allowance, which then expired on OS latency the
/// product never sees with an installed toolchain. Paying the first exec here,
/// outside every product deadline, leaves each deadline measuring only what
/// the fixture does. The prewarm line exits before any side effect, so a fake
/// that "must not run" still records nothing.
fn write_executable(path: &Path, contents: &str) {
    let contents = contents.as_bytes();
    let shebang: &[u8] = b"#!/bin/sh\n";
    let contents = match contents.strip_prefix(shebang) {
        Some(body) => [shebang, PREWARM_EXIT, body].concat(),
        None => panic!("fake executables are /bin/sh scripts: {}", path.display()),
    };
    fs::write(path, contents).expect("write fake executable");
    let mut permissions = fs::metadata(path).expect("fake executable metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("chmod fake executable");
    let status = Command::new(path)
        .env("TRUST_FIXTURE_PREWARM", "1")
        .status()
        .expect("prewarm fake executable");
    assert!(status.success(), "prewarm of {} failed: {status}", path.display());
}

const PREWARM_EXIT: &[u8] = b"[ \"${TRUST_FIXTURE_PREWARM:-}\" = 1 ] && exit 0\n";

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

fn install_targo_trust_binary(bin_dir: &Path) -> PathBuf {
    let path = bin_dir.join(format!("targo-trust{}", std::env::consts::EXE_SUFFIX));
    fs::copy(targo_trust_binary(), &path).expect("copy targo-trust into fake Trust root");
    let mut permissions = fs::metadata(&path).expect("targo-trust metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&path, permissions).expect("chmod targo-trust");
    path
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> Self {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock after Unix epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()));
        fs::create_dir_all(&path).expect("create temp dir");
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
