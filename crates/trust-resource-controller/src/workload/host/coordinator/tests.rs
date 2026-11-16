// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;
fn plan() -> Plan {
    Plan {
        sources: vec![
            Source {
                root: b"/work/app".to_vec(),
                sha256: [1; 32],
            },
            Source {
                root: b"/work/leaf".to_vec(),
                sha256: [2; 32],
            },
        ],
        manifest: InputFile {
            path: b"/work/app/Cargo.toml".to_vec(),
            sha256: [3; 32],
        },
        package: "app".into(),
        binary: "app".into(),
        features: vec![],
        output_root: b"/output".to_vec(),
        cargo_home: b"/cargo-home".to_vec(),
        sdk_root: b"/sdk".to_vec(),
        compiler: InputFile {
            path: b"/sdk/bin/trustc".to_vec(),
            sha256: [4; 32],
        },
        mode: Mode::Build,
        timeout_ns: 1_000_000_000,
    }
}
#[test]
fn selected_native_features_are_bound_before_exec_and_source_output_overlap_refuses() {
    let base = plan();
    let mut changed = base.clone();
    changed.features.push("offset".into());
    assert_ne!(
        base.startup_args().unwrap(),
        changed.startup_args().unwrap()
    );
    assert_eq!(
        Plan::from_startup_args(&changed.startup_args().unwrap()).unwrap(),
        changed
    );
    let mut duplicate = changed.clone();
    duplicate.features.push("offset".into());
    assert!(duplicate.encode().is_err());
    let mut overlap = base;
    overlap.output_root = b"/work/app/target".to_vec();
    assert!(overlap.encode().is_err());
    let mut trailing = changed.encode().unwrap();
    trailing.push(0);
    assert!(Plan::decode(&trailing).is_err());
}
#[test]
fn selection_data_cannot_decode_as_an_execution_plan() {
    let selection = SemanticSelection {
        root_attempt: [1; 16],
        member_attempt: [2; 16],
        prepared_sha256: [3; 32],
        configuration_sha256: [4; 32],
        coverage_sha256: [5; 32],
    };
    let bytes = selection.encode().unwrap();
    assert!(Plan::decode(&bytes).is_err());
    assert_eq!(SemanticSelection::decode(&bytes).unwrap(), selection);
}
