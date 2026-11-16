//! Exact compiler-unit coverage for build scripts and their support closure.

use super::*;

const ROOT_PACKAGE: &str = "path+file:///fixture#demo@0.1.0";

fn complete_compiler_scope() -> (BTreeMap<String, String>, Vec<serde_json::Value>) {
    let selected = [(ROOT_PACKAGE.to_string(), "demo".to_string())].into_iter().collect();
    let mut lines = Vec::new();
    for (index, package_id, package, target, kind, role) in [
        (0, ROOT_PACKAGE, "demo", "demo", "lib", "primary"),
        (1, ROOT_PACKAGE, "demo", "build-script-build", "custom-build", "dependency"),
        (
            2,
            "path+file:///fixture/support#support@1.0.0",
            "support",
            "support",
            "lib",
            "dependency",
        ),
        (
            3,
            "path+file:///fixture/ny-contracts#ny-contracts@0.2.0",
            "ny-contracts",
            "trust",
            "proc-macro",
            "dependency",
        ),
    ] {
        append_complete_proof_unit(
            &mut lines, package_id, package, target, kind, index, "build", role, true,
        );
    }
    let values = successful_cargo_input(lines)
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    (selected, values)
}

fn render(values: &[serde_json::Value]) -> String {
    values.iter().map(|line| format!("{line}\n")).collect()
}

#[test]
fn compiler_dependencies_require_and_retain_their_own_evidence() {
    let (selected, values) = complete_compiler_scope();
    let evidence =
        parse_cargo_json_stdout(Cursor::new(render(&values)), &selected, TEST_SESSION, true)
            .expect("build-script, support and spec-provider compiles carry ordinary evidence");
    evidence.require_successful_selected_roots(&selected, true).unwrap();
    let inventory = evidence.declared_inventory.as_ref().unwrap();
    assert!(inventory.include_dependencies);
    assert_eq!(inventory.proof_targets.len(), 4);
    assert!(inventory.excluded_targets.is_empty());
    assert_eq!(evidence.parsed.completed_proof_targets, inventory.proof_targets);
    assert_eq!(evidence.parsed.coverage_proof_targets, inventory.proof_targets);
    assert_eq!(evidence.parsed.verification_results.len(), 4);
    // Successful transport admission is not proof success. Unknown obligations
    // from these compiles must reach the ordinary result gate unchanged.
    assert!(
        evidence
            .parsed
            .verification_results
            .iter()
            .all(|result| result.outcome == VerificationOutcome::Unknown)
    );
}

#[test]
fn compiler_dependency_evidence_cannot_be_omitted_or_reused_fresh() {
    let (selected, baseline) = complete_compiler_scope();
    for index in 1..=3 {
        for missing in ["all", "coverage_summary", "crate_summary", "compiler-artifact", "fresh"] {
            let mut values = baseline.clone();
            values.retain_mut(|line| {
                if line.pointer("/trust_proof_unit/index").and_then(serde_json::Value::as_u64)
                    != Some(index)
                {
                    return true;
                }
                let artifact = line["reason"] == "compiler-artifact";
                if missing == "fresh" && artifact {
                    line["fresh"] = serde_json::json!(true);
                }
                missing != "all"
                    && !(missing == "compiler-artifact" && artifact)
                    && !line
                        .pointer("/message/message")
                        .and_then(serde_json::Value::as_str)
                        .is_some_and(|message| missing != "fresh" && message.contains(missing))
            });
            let error = parse_cargo_json_stdout(
                Cursor::new(render(&values)),
                &selected,
                TEST_SESSION,
                true,
            )
            .err()
            .expect("every declared compiler unit requires fresh complete evidence");
            assert!(!error.is_empty(), "unit {index}, missing {missing}");
        }
    }
}

#[test]
fn build_script_execution_stays_a_distinct_control_unit() {
    let (selected, mut values) = complete_compiler_scope();
    let mut execution = serde_json::json!({
        "index": 4,
        "mode": "run-custom-build",
        "package_id": ROOT_PACKAGE,
        "package_name": "demo",
        "target_name": "build-script-build",
        "target_kinds": ["custom-build"],
        "compile_target": TEST_COMPILE_TARGET,
        "exclusion_reason": TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION,
        "graph_role": "control",
    });
    set_excluded_unit_semantics(&mut execution, "run-custom-build");
    values[0]["excluded_units"] = serde_json::json!([execution]);
    let evidence =
        parse_cargo_json_stdout(Cursor::new(render(&values)), &selected, TEST_SESSION, true)
            .expect("execution is recorded independently of the verified build-script compilation");
    evidence.require_successful_selected_roots(&selected, true).unwrap();
    let inventory = evidence.declared_inventory.unwrap();
    assert_eq!(inventory.proof_targets.len(), 4);
    assert_eq!(inventory.excluded_targets.len(), 1);
    let execution = inventory.excluded_targets.iter().next().unwrap();
    assert_eq!(execution.proof_unit_mode, "run-custom-build");
    assert_eq!(inventory.excluded_graph_roles[execution], "control");
    assert!(!evidence.parsed.completed_proof_targets.contains(execution));
}
