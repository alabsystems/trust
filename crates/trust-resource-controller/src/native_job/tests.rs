// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Pure graph/protocol controls. These fixtures construct no native Root,
//! CPU description, SDK, materialization, command eligibility or proof grade.
use super::*;
pub(crate) fn plan() -> Plan {
    let input = |path: &[u8]| InputFile {
        path: path.to_vec(),
        sha256: [3; 32],
    };
    let program = input(b"/sdk/bin/targo");
    let compiler = input(b"/sdk/bin/trustc");
    let unit = |kind| UnitSelector {
        package: "fixture".into(),
        target: "fixture".into(),
        kind,
    };
    let artifact = |id, kind| Artifact {
        producer: NodeId(id),
        unit: unit(kind),
    };
    let edge = |id| Dependency {
        node: NodeId(id),
        condition: EdgeCondition::Succeeded,
    };
    let compile = |name: &str, source, output, kind| Node {
        name: name.into(),
        dependencies: vec![],
        timeout_ns: 1_000_000,
        kind: Kind::Compile {
            source,
            output,
            unit: unit(kind),
            mode: CompileMode::Build,
            features: vec![],
            frontend: Frontend::OriginalSdk,
        },
    };
    Plan {
        invocation: [9; 16],
        inputs: RootInputs {
            sdk_root: b"/sdk".to_vec(),
            program: program.clone(),
            compiler: compiler.clone(),
            cwd: b"/source".to_vec(),
            cargo_home: b"/cargo-home".to_vec(),
            output_root: b"/output".to_vec(),
            environment: vec![
                (b"LANG".to_vec(), b"C".to_vec()),
                (b"LC_ALL".to_vec(), b"C".to_vec()),
                (b"CARGO".to_vec(), program.path),
                (b"RUSTC".to_vec(), compiler.path),
                (b"CARGO_HOME".to_vec(), b"/cargo-home".to_vec()),
                (b"CARGO_CACHE_RUSTC_INFO".to_vec(), b"0".to_vec()),
            ],
            observed_host_store: None,
        },
        sources: vec![
            Source {
                root: b"/source".to_vec(),
                manifest: input(b"/source/Cargo.toml"),
                namespace_sha256: [4; 32],
            },
            Source {
                root: b"/candidate-source".to_vec(),
                manifest: input(b"/candidate-source/Cargo.toml"),
                namespace_sha256: [5; 32],
            },
        ],
        outputs: vec![
            Output {
                name: "baseline".into(),
                root: b"/output/baseline".to_vec(),
            },
            Output {
                name: "candidate".into(),
                root: b"/output/candidate".to_vec(),
            },
            Output {
                name: "tests".into(),
                root: b"/output/tests".to_vec(),
            },
        ],
        nodes: vec![
            compile("baseline", 0, 0, TargetKind::Binary),
            compile("candidate", 1, 1, TargetKind::Binary),
            compile("test-build", 0, 2, TargetKind::Test),
            Node {
                name: "verify".into(),
                dependencies: vec![edge(0)],
                timeout_ns: 1_000_000,
                kind: Kind::Verify {
                    artifact: artifact(0, TargetKind::Binary),
                    policy: ProofPolicy::Certify,
                },
            },
            Node {
                name: "candidate-verify".into(),
                dependencies: vec![edge(1)],
                timeout_ns: 1_000_000,
                kind: Kind::Verify {
                    artifact: artifact(1, TargetKind::Binary),
                    policy: ProofPolicy::Certify,
                },
            },
            Node {
                name: "tests".into(),
                dependencies: vec![edge(2)],
                timeout_ns: 1_000_000,
                kind: Kind::Tests {
                    artifact: artifact(2, TargetKind::Test),
                    arguments: vec![],
                },
            },
            Node {
                name: "run".into(),
                dependencies: vec![edge(0)],
                timeout_ns: 1_000_000,
                kind: Kind::Run {
                    artifact: artifact(0, TargetKind::Binary),
                    arguments: vec![vec![0xff, 0xfe]],
                },
            },
            Node {
                name: "candidate-run".into(),
                dependencies: vec![edge(1)],
                timeout_ns: 1_000_000,
                kind: Kind::Run {
                    artifact: artifact(1, TargetKind::Binary),
                    arguments: vec![vec![0xff, 0xfe]],
                },
            },
            Node {
                name: "compare".into(),
                dependencies: vec![
                    edge(0),
                    edge(1),
                    edge(3),
                    edge(4),
                    edge(5),
                    edge(6),
                    edge(7),
                ],
                timeout_ns: 1_000_000,
                kind: Kind::Compare {
                    baseline: artifact(0, TargetKind::Binary),
                    candidate: artifact(1, TargetKind::Binary),
                    selection: comparison::Selection {
                        workload_sources: vec![0],
                        pairs: vec![
                            comparison::ActionPair {
                                action: "verify".into(),
                                repetition: 0,
                                baseline: NodeId(3),
                                candidate: NodeId(4),
                            },
                            comparison::ActionPair {
                                action: "run".into(),
                                repetition: 0,
                                baseline: NodeId(6),
                                candidate: NodeId(7),
                            },
                        ],
                        repetitions: 1,
                        focus: "run".into(),
                        metric: comparison::Metric::ParentActionIntervalV1,
                    },
                },
            },
            Node {
                name: "land".into(),
                dependencies: vec![edge(8)],
                timeout_ns: 1_000_000,
                kind: Kind::Land {
                    source: 1,
                    comparison: NodeId(8),
                    selection: comparison::LandSelection {
                        sources: vec![comparison::SourcePair {
                            baseline: 0,
                            candidate: 1,
                        }],
                    },
                },
            },
        ],
        timeout_ns: 60_000_000_000,
    }
}
#[test]
fn whole_job_roundtrips_all_nodes_and_rejects_every_incomplete_prefix() {
    let p = plan();
    let bytes = p.encode().unwrap();
    assert_eq!(Plan::decode(&bytes).unwrap(), p);
    for end in 0..bytes.len() {
        assert!(Plan::decode(&bytes[..end]).is_err(), "prefix {end}");
    }
    let mut extended = bytes;
    extended.push(0);
    assert!(Plan::decode(&extended).is_err());
}
#[test]
fn graph_rejects_cycles_failed_artifact_edges_and_selector_grafts() {
    let p = plan();
    p.validate().unwrap();
    let mut changed = p.clone();
    changed.nodes[0].dependencies.push(Dependency {
        node: NodeId(9),
        condition: EdgeCondition::Retired,
    });
    assert!(changed.validate().is_err());
    let mut changed = p.clone();
    changed.nodes[4].dependencies[0].condition = EdgeCondition::Retired;
    assert!(changed.validate().is_err());
    let mut changed = p.clone();
    if let Kind::Run { artifact, .. } = &mut changed.nodes[6].kind {
        artifact.unit.target = "another".into();
    }
    assert!(changed.validate().is_err());
    let mut changed = p.clone();
    if let Kind::Compile { mode, .. } = &mut changed.nodes[0].kind {
        *mode = CompileMode::Check;
    }
    assert!(changed.validate().is_err());
    let mut changed = p.clone();
    changed.outputs[1].root = b"/output/baseline/nested".to_vec();
    assert!(changed.validate().is_err());
}
#[test]
fn plan_binding_preserves_environment_proof_policy_and_complete_denominator() {
    let p = plan();
    let original = p.binding_preimage().unwrap();
    let mut changed = p.clone();
    changed
        .inputs
        .environment
        .push((b"RUSTFLAGS".to_vec(), b"-Copt-level=3".to_vec()));
    assert_ne!(changed.binding_preimage().unwrap(), original);
    let mut changed = p.clone();
    if let Kind::Verify { policy, .. } = &mut changed.nodes[3].kind {
        *policy = ProofPolicy::Advisory;
    }
    if let Kind::Verify { policy, .. } = &mut changed.nodes[4].kind {
        *policy = ProofPolicy::Advisory;
    }
    assert_ne!(changed.binding_preimage().unwrap(), original);
    let mut changed = p;
    changed.nodes.pop();
    assert_ne!(changed.binding_preimage().unwrap(), original);
}
#[test]
fn root_and_field_bounds_precede_serialization_or_native_adoption() {
    let mut p = plan();
    p.timeout_ns = MAX_ROOT_NS + 1;
    assert!(p.encode().is_err());
    let mut p = plan();
    p.inputs
        .environment
        .push((b"RUSTFLAGS".to_vec(), vec![b'x'; 65537]));
    assert!(p.encode().is_err());
    let mut p = plan();
    p.invocation = [0; 16];
    assert!(p.encode().is_err());
    let mut p = plan();
    p.nodes.resize(MAX_NODES + 1, p.nodes[0].clone());
    assert!(p.encode().is_err());
}

#[test]
fn native_ready_and_queries_never_decode_as_workload_or_paired_protocols() {
    let mut original = crate::paired_qualification::query::tests::query();
    original.member.command.program = plan().inputs.compiler.path;
    original.member.command.environment = plan().inputs.environment;
    original.member.command.cwd = plan().inputs.cwd;
    let request = host::ReadyRequest {
        query: crate::ContextQuery {
            binding: original.member.binding.clone(),
            call_attempt: [8; 16],
        },
        plan: plan(),
    };
    let bytes = request.encode().unwrap();
    assert!(host::ReadyRequest::decode(&bytes).unwrap() == request);
    assert!(crate::workload::host::ReadyRequest::decode(&bytes).is_err());
    assert!(crate::paired_qualification::host::ReadyRequest::decode(&bytes).is_err());
    let q = query::CompilerQuery {
        member: original.member,
        plan_sha256: [7; 32],
        sdk_root: request.plan.inputs.sdk_root.clone(),
        compiler: request.plan.inputs.compiler.clone(),
    };
    let bytes = q.encode().unwrap();
    assert!(query::CompilerQuery::decode(&bytes).unwrap() == q);
    assert!(crate::workload::host::CompilerQuery::decode(&bytes).is_err());
    assert!(crate::paired_qualification::query::CompilerQuery::decode(&bytes).is_err());
    for end in 0..bytes.len() {
        assert!(query::CompilerQuery::decode(&bytes[..end]).is_err());
    }
    for args in [
        vec![b"--emit=link".to_vec()],
        vec![b"@source.rsp".to_vec()],
        vec![b"/source/main.rs".to_vec()],
    ] {
        let mut invalid = q.clone();
        invalid.member.command.args = args;
        assert!(invalid.encode().is_err());
    }
}
