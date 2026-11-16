use trust_resource_controller::paired_qualification::AySubject;
use trust_resource_controller::workload::{InputFile, WorkloadInvocation};
use trust_resource_controller::{BirthKind, FileIdentity, Identity};

use super::*;

pub(in crate::paired_qualification) fn plan() -> PairedInvocation {
    let file = |path: &str| InputFile { path: path.as_bytes().to_vec(), sha256: [2; 32] };
    PairedInvocation {
        consumer: WorkloadInvocation {
            invocation: [1; 16],
            observed_host_store: None,
            root: b"/sdk".to_vec(),
            program: file("/sdk/bin/targo"),
            compiler: file("/sdk/bin/trustc"),
            cwd: b"/consumer".to_vec(),
            cargo_home: b"/cargo-home".to_vec(),
            output_root: b"/outputs".to_vec(),
            refutation_step: file("/fixtures/step.rs"),
            refutation_loop: file("/fixtures/loop.rs"),
            trust_spec_source: file("/fixtures/spec.rs"),
            repetitions: 1,
            timeout_ns: 3_600_000_000_000,
        },
        ay: AySubject {
            root: b"/ay".to_vec(),
            workspace_manifest: file("/ay/Cargo.toml"),
            crate_manifest: file("/ay/crates/ay-proof-common/Cargo.toml"),
            lockfile: file("/ay/Cargo.lock"),
            cargo_config: file("/ay/.cargo/config.toml"),
            toolchain_config: file("/ay/rust-toolchain.toml"),
            source_commit: [3; 20],
            crate_tree: [4; 20],
        },
    }
}
fn protocol() -> Protocol {
    let mut p = Protocol::new(plan()).unwrap();
    let ready = service::Ready {
        binding: service::Binding { root_attempt: [9; 16], invocation_sha256: p.digest },
        original_root: Identity { pid: 2, birth: 3, birth_kind: BirthKind::MacosWallMicroseconds },
        native_manifest: FileIdentity { device: 4, inode: 5 },
        reserved_domain: 28,
        dispatch_ceiling: 7,
        memory_bytes: 15_032_385_536,
        repetitions: 1,
    };
    let bytes = service::compiler_observation::Ready { original: ready }.encode().unwrap();
    assert!(matches!(p.frame(&bytes).unwrap(), Some(Event::Ready(_))));
    p
}
fn register(p: &mut Protocol, node: Node, unit: bool) {
    let row = service::Registered {
        binding: p.binding().unwrap().clone(),
        node,
        original_compile_unit: unit.then(|| service::CompileUnit {
            index: 7,
            unit_hash: "actual-cargo-unit".into(),
            package: "ay-proof-common".into(),
            target: "ay_proof_common".into(),
            source: b"/ay/crates/ay-proof-common/src/lib.rs".to_vec(),
        }),
    };
    p.frame(&row.encode(1).unwrap()).unwrap();
}
fn blocked(p: &mut Protocol, node: Node) -> service::Finished {
    register(p, node, false);
    service::Finished {
        binding: p.binding().unwrap().clone(),
        node,
        result: service::Result::Blocked { reason: "retained original prerequisite failed".into() },
        lengths: [0; 2],
        ends: [service::StreamEnd::Unobserved; 2],
        truncated: [false; 2],
    }
}
fn finish(p: &mut Protocol, row: &service::Finished) -> service::Checkpoint {
    let bytes = row.encode(1).unwrap();
    p.frame(&bytes).unwrap();
    let checkpoint = service::Checkpoint {
        binding: p.binding().unwrap().clone(),
        sequence: p.next,
        node: row.node,
        outcome_sha256: Sha256::digest(&bytes).into(),
    };
    p.frame(&checkpoint.encode(1).unwrap()).unwrap();
    checkpoint
}
fn closed(p: &mut Protocol, node: Node) {
    for (scope, stream) in [
        (OutputScope::Diagnostics, Stream::Stdout),
        (OutputScope::Diagnostics, Stream::Stderr),
        (OutputScope::CompilerReport, Stream::Stdout),
    ] {
        p.frame(
            &service::DiagnosticEnd {
                binding: p.binding().unwrap().clone(),
                node,
                scope,
                stream,
                length: 0,
                writer_closed: false,
                truncated: false,
            }
            .encode(1)
            .unwrap(),
        )
        .unwrap();
    }
    let observation = service::compiler_observation::Observation {
        binding: p.binding().unwrap().clone(),
        node,
        run_id: None,
        report_bytes: 0,
        report_sha256: Sha256::digest([]).into(),
        counts: None,
        unavailable: Some("original stage preparation failed".into()),
    };
    p.frame(&observation.encode().unwrap()).unwrap();
}

#[test]
fn old_ready_refuses_before_configuration_and_projection_requires_original_closed_bytes() {
    let original = protocol().ready.unwrap();
    let mut p = Protocol::new(plan()).unwrap();
    assert!(p.frame(&original.encode().unwrap()).is_err());
    let new = service::compiler_observation::Ready { original };
    assert!(p.frame(&new.encode().unwrap()).is_err(), "old Ready failure is permanent");
    let mut p = protocol();
    let row = service::compiler_observation::Observation {
        binding: p.binding().unwrap().clone(),
        node: Node::AyCompile,
        run_id: None,
        report_bytes: 0,
        report_sha256: Sha256::digest([]).into(),
        counts: None,
        unavailable: Some("not initialized".into()),
    };
    assert!(p.frame(&row.encode().unwrap()).is_err(), "no projection before original writer end");
}

#[test]
fn projection_cannot_replace_raw_report_bytes_or_turn_unavailable_into_zero() {
    let mut p = protocol();
    register(&mut p, Node::AyCompile, false);
    let bytes = b"actual original report prefix\n".to_vec();
    p.frame(
        &service::Chunk {
            binding: p.binding().unwrap().clone(),
            node: Node::AyCompile,
            scope: OutputScope::CompilerReport,
            stream: Stream::Stdout,
            offset: 0,
            bytes: bytes.clone(),
        }
        .encode(1)
        .unwrap(),
    )
    .unwrap();
    p.frame(
        &service::DiagnosticEnd {
            binding: p.binding().unwrap().clone(),
            node: Node::AyCompile,
            scope: OutputScope::CompilerReport,
            stream: Stream::Stdout,
            length: bytes.len() as u64,
            writer_closed: true,
            truncated: false,
        }
        .encode(1)
        .unwrap(),
    )
    .unwrap();
    let mut observation = service::compiler_observation::Observation {
        binding: p.binding().unwrap().clone(),
        node: Node::AyCompile,
        run_id: Some("original-run".into()),
        report_bytes: bytes.len() as u64,
        report_sha256: Sha256::digest(&bytes).into(),
        counts: None,
        unavailable: Some("actual malformed report".into()),
    };
    p.frame(&observation.encode().unwrap()).unwrap();
    assert!(p.nodes[&Node::AyCompile].compiler_observation.as_ref().unwrap().counts.is_none());
    observation.report_sha256[0] ^= 1;
    assert!(p.frame(&observation.encode().unwrap()).is_err());
    assert!(!p.measured());
}

#[test]
fn projection_hash_and_length_cannot_substitute_the_actual_empty_report_prefix() {
    for wrong_length in [false, true] {
        let mut p = protocol();
        let binding = p.binding().unwrap().clone();
        p.frame(
            &service::DiagnosticEnd {
                binding: binding.clone(),
                node: Node::AyCompile,
                scope: OutputScope::CompilerReport,
                stream: Stream::Stdout,
                length: 0,
                writer_closed: false,
                truncated: false,
            }
            .encode(1)
            .unwrap(),
        )
        .unwrap();
        let row = service::compiler_observation::Observation {
            binding,
            node: Node::AyCompile,
            run_id: None,
            report_bytes: u64::from(wrong_length),
            report_sha256: if wrong_length { Sha256::digest([]).into() } else { [9; 32] },
            counts: None,
            unavailable: Some("original report did not initialize".into()),
        };
        assert!(p.frame(&row.encode().unwrap()).is_err());
        assert!(p.failure.is_some());
    }
}
fn empty_census(p: &mut Protocol) -> service::Final {
    let binding = p.binding().unwrap().clone();
    p.frame(
        &service::encode_census(&trust_resource_controller::workload::host::census::Page {
            request: trust_resource_controller::workload::host::census::Request {
                root_attempt: binding.root_attempt,
                invocation_sha256: binding.invocation_sha256,
                snapshot: [5; 16],
                offset: 0,
            },
            total: 0,
            entries: Vec::new(),
        })
        .unwrap(),
    )
    .unwrap();
    service::Final {
        binding,
        repetitions: 1,
        finished: 0,
        blocked: 8,
        inputs_unchanged: true,
        snapshot: [5; 16],
        members: 0,
    }
}

#[test]
fn complete_blocked_population_is_retained_and_never_measured_as_zero() {
    let mut p = protocol();
    // Actual preparation failures close pre-created unused writers first.
    closed(&mut p, Node::AyCompile);
    closed(&mut p, Node::ConsumerCompile);
    for node in Node::population(1).unwrap() {
        let row = blocked(&mut p, node);
        let checkpoint = finish(&mut p, &row);
        p.continued(&checkpoint).unwrap();
    }
    let final_observation = empty_census(&mut p);
    assert!(matches!(
        p.frame(&final_observation.encode().unwrap()).unwrap(),
        Some(Event::Final(_))
    ));
    assert!(!p.measured());
    assert_eq!(p.nodes.values().filter(|state| state.terminal.is_some()).count(), 8);
    assert!(p.frame(&final_observation.encode().unwrap()).is_err());
    assert!(
        p.final_observation.is_some(),
        "actual earlier final observation survives trailing failure"
    );
    assert!(p.failure.is_some());
}
#[test]
fn checkpoint_hash_is_exact_and_failed_protocol_cannot_recover_from_a_valid_retry() {
    let mut p = protocol();
    let row = blocked(&mut p, Node::AyCompile);
    let bytes = row.encode(1).unwrap();
    p.frame(&bytes).unwrap();
    let checkpoint = service::Checkpoint {
        binding: p.binding().unwrap().clone(),
        sequence: 1,
        node: row.node,
        outcome_sha256: [8; 32],
    };
    assert!(p.frame(&checkpoint.encode(1).unwrap()).is_err());
    let correct =
        service::Checkpoint { outcome_sha256: Sha256::digest(bytes).into(), ..checkpoint };
    assert!(p.frame(&correct.encode(1).unwrap()).is_err());
    assert!(p.nodes[&Node::AyCompile].terminal.is_some());
    assert!(!p.nodes[&Node::AyCompile].continued);
}
#[test]
fn only_actual_matching_ack_write_advances_the_same_original_checkpoint() {
    let mut p = protocol();
    let row = blocked(&mut p, Node::AyCompile);
    let checkpoint = finish(&mut p, &row);
    assert!(!p.nodes[&Node::AyCompile].continued);
    let mut wrong = checkpoint.clone();
    wrong.outcome_sha256[0] ^= 1;
    assert!(p.continued(&wrong).is_err());
    assert!(p.continued(&checkpoint).is_err());
    let mut p = protocol();
    let row = blocked(&mut p, Node::AyCompile);
    let checkpoint = finish(&mut p, &row);
    p.continued(&checkpoint).unwrap();
    assert!(p.nodes[&Node::AyCompile].continued);
    assert!(p.continued(&checkpoint).is_err());
}
#[test]
fn compiler_diagnostics_may_follow_retirement_until_the_original_writer_closes() {
    let mut p = protocol();
    register(&mut p, Node::AyCompile, false);
    let row = service::Finished {
        binding: p.binding().unwrap().clone(),
        node: Node::AyCompile,
        result: service::Result::Compiled {
            succeeded: true,
            local_workers_joined: true,
            failure: None,
        },
        lengths: [0; 2],
        ends: [service::StreamEnd::Unobserved; 2],
        truncated: [false; 2],
    };
    let checkpoint = finish(&mut p, &row);
    p.continued(&checkpoint).unwrap();
    let chunk = service::Chunk {
        binding: p.binding().unwrap().clone(),
        node: Node::AyCompile,
        scope: OutputScope::Diagnostics,
        stream: Stream::Stderr,
        offset: 0,
        bytes: b"actual verification diagnostic".to_vec(),
    };
    p.frame(&chunk.encode(1).unwrap()).unwrap();
    let end = service::DiagnosticEnd {
        binding: chunk.binding.clone(),
        node: chunk.node,
        scope: chunk.scope,
        stream: chunk.stream,
        length: chunk.bytes.len() as u64,
        writer_closed: true,
        truncated: false,
    };
    p.frame(&end.encode(1).unwrap()).unwrap();
    assert!(
        p.frame(&service::Chunk { offset: chunk.bytes.len() as u64, ..chunk }.encode(1).unwrap())
            .is_err()
    );
}
#[test]
fn native_failed_exit_and_unavailable_accounting_remain_distinct_from_unknown() {
    let row = service::Finished {
        binding: service::Binding { root_attempt: [9; 16], invocation_sha256: [8; 32] },
        node: Node::Strict,
        result: service::Result::Captured {
            capture: service::Capture {
                started: true,
                outcome: Some(Outcome::Exit(7)),
                cause: Some(CompletionCause::Exited),
                runtime_ns: Some(0),
                retirement_confirmed: true,
                accounting: None,
                member_attempt: Some([6; 16]),
                failure: None,
            },
            elapsed_ns: 0,
            input_failure: None,
        },
        lengths: [0; 2],
        ends: [service::StreamEnd::Eof; 2],
        truncated: [false; 2],
    };
    assert!(Protocol::native_complete(&row), "nonzero native exit is a known semantic observation");
    assert!(!Protocol::native_complete(&service::Finished {
        ends: [service::StreamEnd::Unobserved; 2],
        ..row.clone()
    }));
    let mut unknown = row.clone();
    if let service::Result::Captured { capture, .. } = &mut unknown.result {
        capture.outcome = None;
    }
    assert!(!Protocol::native_complete(&unknown));
    if let service::Result::Captured { capture, .. } = &row.result {
        assert_eq!(capture.accounting, None);
    }
}
#[test]
fn native_samples_cannot_replace_the_complete_all_target_inventory_barrier() {
    let mut p = protocol();
    register(&mut p, Node::Sample { target: 0, repetition: 0 }, false);
    let row = service::Finished {
        binding: p.binding().unwrap().clone(),
        node: Node::Sample { target: 0, repetition: 0 },
        result: service::Result::Captured {
            capture: service::Capture {
                started: false,
                outcome: None,
                cause: None,
                runtime_ns: None,
                retirement_confirmed: false,
                accounting: None,
                member_attempt: None,
                failure: Some("no admission".into()),
            },
            elapsed_ns: 0,
            input_failure: None,
        },
        lengths: [0; 2],
        ends: [service::StreamEnd::Unobserved; 2],
        truncated: [false; 2],
    };
    assert!(p.frame(&row.encode(1).unwrap()).is_err());
}
#[test]
fn full_plan_readiness_and_verifier_subject_are_not_substitutable() {
    let mut p = protocol();
    let mut wrong = p.ready.clone().unwrap();
    wrong.binding.invocation_sha256 = Sha256::digest(plan().consumer.encode().unwrap()).into();
    assert!(Protocol::new(plan()).unwrap().frame(&wrong.encode().unwrap()).is_err());
    let mut registered = service::Registered {
        binding: p.binding().unwrap().clone(),
        node: Node::Advisory,
        original_compile_unit: Some(service::CompileUnit {
            index: 7,
            unit_hash: "actual-cargo-unit".into(),
            package: "ay-proof-common".into(),
            target: "ay_proof_common".into(),
            source: b"/other/ay/crates/ay-proof-common/src/lib.rs".to_vec(),
        }),
    };
    assert!(p.frame(&registered.encode(1).unwrap()).is_err());
    registered.original_compile_unit.as_mut().unwrap().source =
        b"/ay/crates/ay-proof-common/src/lib.rs".to_vec();
    assert!(
        p.frame(&registered.encode(1).unwrap()).is_err(),
        "subject substitution poisons permanently"
    );
}

pub(in crate::paired_qualification) fn complete_graph(metrics: bool) -> Protocol {
    complete_graph_with_projection(metrics, true)
}
fn complete_graph_with_projection(metrics: bool, project: bool) -> Protocol {
    use trust_resource_controller::accounting::{CpuTimes, Observation, Scope};
    use trust_resource_controller::workload::host::census;
    let mut p = protocol();
    let observation = Observation {
        scope: Scope::ChildAndWaitedDescendantsV1,
        cpu_times: metrics.then_some(CpuTimes { user_ns: 0, system_ns: 0 }),
        peak_rss_bytes: metrics.then_some(0),
    };
    let mut members = Vec::new();
    for (index, node) in Node::population(1).unwrap().into_iter().enumerate() {
        register(&mut p, node, node.is_verification());
        if node == Node::ConsumerCompile {
            for target in 0..2 {
                let artifact = service::Artifact {
                    binding: p.binding().unwrap().clone(),
                    target,
                    executable: trust_resource_controller::MetadataFile {
                        path: format!("/outputs/debug/deps/target-{target}").into_bytes(),
                        sha256: [4 + target as u8; 32],
                        bytes: 7,
                        device: 8,
                        inode: 9 + target as u64,
                    },
                };
                p.frame(&artifact.encode(b"/outputs").unwrap()).unwrap();
            }
        }
        let result = if node.is_compile() {
            service::Result::Compiled { succeeded: true, local_workers_joined: true, failure: None }
        } else {
            let identity = Identity {
                pid: 100 + index as u32,
                birth: 7,
                birth_kind: BirthKind::MacosWallMicroseconds,
            };
            let member_attempt = [20 + index as u8; 16];
            members.push(census::Entry {
                member_attempt,
                kind: if node.is_verification() {
                    SourceKind::Compiler
                } else if matches!(node, Node::Inventory { .. }) {
                    SourceKind::Inventory
                } else {
                    SourceKind::Sample
                },
                identity: Some(identity),
                started: Some(trust_resource_controller::Started {
                    identity,
                    monotonic_ns: 5,
                    unix_ns: 6,
                }),
                terminal: Status::Finished {
                    outcome: Outcome::Exit(0),
                    cause: CompletionCause::Exited,
                    runtime_ns: 0,
                },
                accounting: observation,
                retired: true,
                drained: true,
            });
            service::Result::Captured {
                capture: service::Capture {
                    started: true,
                    outcome: Some(Outcome::Exit(0)),
                    cause: Some(CompletionCause::Exited),
                    runtime_ns: Some(0),
                    retirement_confirmed: true,
                    accounting: Some(observation),
                    member_attempt: Some(member_attempt),
                    failure: None,
                },
                elapsed_ns: 0,
                input_failure: None,
            }
        };
        let row = service::Finished {
            binding: p.binding().unwrap().clone(),
            node,
            result,
            lengths: [0; 2],
            ends: if node.is_compile() {
                [service::StreamEnd::Unobserved; 2]
            } else {
                [service::StreamEnd::Eof; 2]
            },
            truncated: [false; 2],
        };
        let checkpoint = finish(&mut p, &row);
        p.continued(&checkpoint).unwrap();
    }
    for node in [Node::AyCompile, Node::ConsumerCompile] {
        // Serialized DATA consistency fixture, never an actual candidate or
        // execution owner. Keep a valid, explicitly declared zero-unit report
        // so zero comes from a closed report contract, not absent bytes.
        let mut report = Vec::new();
        for mut value in [
            serde_json::json!({"reason":"input-work-enabled","version":1}),
            serde_json::json!({"reason":"build-started","command":[],"cwd":"/fixture","host":"fixture","jobs":1,
                "num_cpus":null,"profile":"dev","rustc_version":"fixture","rustc_version_verbose":"fixture",
                "target_dir":"/outputs","workspace_root":"/fixture"}),
            serde_json::json!({"reason":"unit-graph-finished","elapsed":0.0}),
            serde_json::json!({"reason":"execution-enabled","version":1}),
            serde_json::json!({"reason":"compiler-observations-enabled","version":1,"rusage_requested":metrics}),
            serde_json::json!({"reason":"execution-graph-finished","elapsed":0.0,"outcome":"succeeded","scheduled":0,"completed":0,"not_executed":0}),
            serde_json::json!({"reason":"input-work-closed","version":1,"started":0,"finished":0}),
        ] {
            value["run_id"] = serde_json::json!("serialized-consistency-fixture");
            value["timestamp"] = serde_json::json!("2026-11-07T01:02:03Z");
            serde_json::to_writer(&mut report, &value).unwrap();
            report.push(b'\n');
        }
        p.frame(
            &service::Chunk {
                binding: p.binding().unwrap().clone(),
                node,
                scope: OutputScope::CompilerReport,
                stream: Stream::Stdout,
                offset: 0,
                bytes: report.clone(),
            }
            .encode(1)
            .unwrap(),
        )
        .unwrap();
        for (scope, stream) in [
            (OutputScope::Diagnostics, Stream::Stdout),
            (OutputScope::Diagnostics, Stream::Stderr),
            (OutputScope::CompilerReport, Stream::Stdout),
        ] {
            p.frame(
                &service::DiagnosticEnd {
                    binding: p.binding().unwrap().clone(),
                    node,
                    scope,
                    stream,
                    length: if scope == OutputScope::CompilerReport {
                        report.len() as u64
                    } else {
                        0
                    },
                    writer_closed: true,
                    truncated: false,
                }
                .encode(1)
                .unwrap(),
            )
            .unwrap();
        }
        if project {
            use service::compiler_observation::{Counts, GraphOutcome, Observation};
            p.frame(
                &Observation {
                    binding: p.binding().unwrap().clone(),
                    node,
                    run_id: Some("serialized-consistency-fixture".into()),
                    report_bytes: report.len() as u64,
                    report_sha256: Sha256::digest(&report).into(),
                    unavailable: None,
                    counts: Some(Counts {
                        graph_outcome: GraphOutcome::Succeeded,
                        registered: 0,
                        scheduled: 0,
                        scheduled_fresh: 0,
                        completed: 0,
                        succeeded: 0,
                        failed: 0,
                        tolerated_failure: 0,
                        cancelled: 0,
                        not_executed: 0,
                        rusage_requested: Some(metrics),
                        successful_primary_processes: Some(0),
                        observed_successful_units: 0,
                        unmeasured_starts: 0,
                        completed_without_start: 0,
                    }),
                }
                .encode()
                .unwrap(),
            )
            .unwrap();
        }
    }
    let binding = p.binding().unwrap().clone();
    p.frame(
        &service::encode_census(&census::Page {
            request: census::Request {
                root_attempt: binding.root_attempt,
                invocation_sha256: binding.invocation_sha256,
                snapshot: [5; 16],
                offset: 0,
            },
            total: members.len() as u32,
            entries: members,
        })
        .unwrap(),
    )
    .unwrap();
    p
}
#[test]
fn revision2_final_cannot_silently_omit_its_declared_compiler_projection() {
    let mut p = complete_graph_with_projection(true, false);
    let final_observation = service::Final {
        binding: p.binding().unwrap().clone(),
        repetitions: 1,
        finished: 8,
        blocked: 0,
        inputs_unchanged: true,
        snapshot: [5; 16],
        members: 6,
    };
    let error = p.frame(&final_observation.encode().unwrap()).err().unwrap();
    assert!(error.0.contains("omitted declared compiler observation"));
    assert!(!p.measured());
}
#[test]
fn complete_original_census_preserves_some_zero_and_missing_metrics_independently() {
    // Serialized consistency fixtures only, never live execution grants.
    for metrics in [true, false] {
        let mut p = complete_graph(metrics);
        let final_observation = service::Final {
            binding: p.binding().unwrap().clone(),
            repetitions: 1,
            finished: 8,
            blocked: 0,
            inputs_unchanged: true,
            snapshot: [5; 16],
            members: 6,
        };
        p.frame(&final_observation.encode().unwrap()).unwrap();
        assert_eq!(p.measured(), metrics);
        assert_eq!(p.census.as_ref().unwrap().entries().len(), 6);
        assert_eq!(p.census.as_ref().unwrap().entries()[0].accounting.cpu_times.is_some(), metrics);
    }
}
#[test]
fn final_census_must_bind_every_original_member_and_final_input_recheck() {
    let mut p = complete_graph(true);
    let binding = p.binding().unwrap().clone();
    let mut final_observation = service::Final {
        binding,
        repetitions: 1,
        finished: 8,
        blocked: 0,
        inputs_unchanged: false,
        snapshot: [5; 16],
        members: 6,
    };
    p.frame(&final_observation.encode().unwrap()).unwrap();
    assert!(!p.measured());
    let mut p = complete_graph(true);
    final_observation.inputs_unchanged = true;
    final_observation.members = 5;
    assert!(p.frame(&final_observation.encode().unwrap()).is_err());
    assert!(p.failure.is_some());
}
