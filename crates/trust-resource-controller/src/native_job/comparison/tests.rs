//! Graph controls preserve requested obligations and the declared experimental
//! cases. They construct no executions, current proof or publication owner.
use super::*;

fn fixture() -> (Plan, Artifact, Artifact, Selection) {
    let mut plan = super::super::tests::plan();
    plan.nodes.truncate(2);
    plan.sources = (0..3)
        .map(|i| Source {
            root: format!("/source{i}").into_bytes(),
            manifest: InputFile {
                path: format!("/source{i}/Cargo.toml").into_bytes(),
                sha256: [i + 1; 32],
            },
            namespace_sha256: [i + 1; 32],
        })
        .collect();
    plan.inputs.cwd = b"/source0".to_vec();
    for (index, node) in plan.nodes.iter_mut().enumerate() {
        let Kind::Compile { source, .. } = &mut node.kind else {
            panic!()
        };
        *source = index as u32;
    }
    plan.outputs = (0..4)
        .map(|i| Output {
            name: format!("cache{i}"),
            root: format!("/output/cache{i}").into_bytes(),
        })
        .collect();
    let unit = UnitSelector {
        package: "workload".into(),
        target: "app".into(),
        kind: TargetKind::Binary,
    };
    let programs = [0, 1].map(|id| Artifact {
        producer: NodeId(id),
        unit: match &plan.nodes[id as usize].kind {
            Kind::Compile { unit, .. } => unit.clone(),
            _ => panic!(),
        },
    });
    let edge = |id| Dependency {
        node: NodeId(id),
        condition: EdgeCondition::Succeeded,
    };
    let mut pairs = Vec::new();
    let mut preceding_runs = None;
    for temperature in ["cold", "warm"] {
        let start = plan.nodes.len() as u32;
        for side in 0..2 {
            let mut dependencies = vec![edge(side)];
            if let Some(previous) = preceding_runs {
                dependencies.push(edge(previous + side));
            }
            plan.nodes.push(Node {
                name: format!("{temperature}-compile-{side}"),
                dependencies,
                timeout_ns: 1_000_000,
                kind: Kind::Compile {
                    source: 2,
                    output: side + 2,
                    unit: unit.clone(),
                    mode: CompileMode::Build,
                    features: vec![],
                    frontend: Frontend::Produced(programs[side as usize].clone()),
                },
            });
        }
        for side in 0..2 {
            plan.nodes.push(Node {
                name: format!("{temperature}-verify-{side}"),
                dependencies: vec![edge(start + side)],
                timeout_ns: 1_000_000,
                kind: Kind::Verify {
                    artifact: Artifact {
                        producer: NodeId(start + side),
                        unit: unit.clone(),
                    },
                    policy: ProofPolicy::Certify,
                },
            });
        }
        for side in 0..2 {
            plan.nodes.push(Node {
                name: format!("{temperature}-run-{side}"),
                dependencies: vec![edge(start + side), edge(start + 2 + side)],
                timeout_ns: 1_000_000,
                kind: Kind::Run {
                    artifact: Artifact {
                        producer: NodeId(start + side),
                        unit: unit.clone(),
                    },
                    arguments: vec![b"42".to_vec()],
                },
            });
        }
        for (offset, action) in [(0, "compile"), (2, "verify"), (4, "run")] {
            pairs.push(ActionPair {
                action: format!("{temperature}-{action}"),
                repetition: 0,
                baseline: NodeId(start + offset),
                candidate: NodeId(start + offset + 1),
            });
        }
        preceding_runs = Some(start + 4);
    }
    let selection = Selection {
        workload_sources: vec![2],
        pairs,
        repetitions: 1,
        focus: "warm-compile".into(),
        metric: Metric::ParentActionIntervalV1,
    };
    let comparison = plan.nodes.len() as u32;
    plan.nodes.push(Node {
        name: "comparison".into(),
        dependencies: vec![edge(comparison - 2), edge(comparison - 1)],
        timeout_ns: 1_000_000,
        kind: Kind::Compare {
            baseline: programs[0].clone(),
            candidate: programs[1].clone(),
            selection: selection.clone(),
        },
    });
    (plan, programs[0].clone(), programs[1].clone(), selection)
}

fn valid(plan: &Plan, a: &Artifact, b: &Artifact, selection: &Selection) -> io::Result<()> {
    selection.validate(plan, a, b, NodeId(plan.nodes.len() as u32 - 1))
}

#[test]
fn complete_cold_warm_obligations_survive_native_plan_round_trip() {
    let (plan, a, b, selection) = fixture();
    valid(&plan, &a, &b, &selection).unwrap();
    let mut e = Encoder::new(106);
    selection.write(&mut e).unwrap();
    let bytes = e.finish().unwrap();
    let mut d = header(&bytes, 106).unwrap();
    assert_eq!(Selection::read(&mut d).unwrap(), selection);
    d.done().unwrap();
}

#[test]
fn omitted_failed_or_unsupported_verifier_stays_in_requested_population() {
    let (plan, a, b, mut selection) = fixture();
    selection.pairs.retain(|pair| pair.action != "cold-verify");
    assert!(valid(&plan, &a, &b, &selection).is_err());
}

#[test]
fn candidate_flags_cache_domains_and_real_argument_cases_must_match() {
    let (plan, a, b, selection) = fixture();
    let mut flags = plan.clone();
    let Kind::Compile { features, .. } = &mut flags.nodes[9].kind else {
        panic!()
    };
    features.push("offset".into());
    assert!(valid(&flags, &a, &b, &selection).is_err());
    let mut shared = plan.clone();
    let Kind::Compile { output, .. } = &mut shared.nodes[3].kind else {
        panic!()
    };
    *output = 2;
    assert!(valid(&shared, &a, &b, &selection).is_err());
    let mut args = plan;
    let Kind::Run { arguments, .. } = &mut args.nodes[13].kind else {
        panic!()
    };
    arguments[0] = b"43".to_vec();
    assert!(valid(&args, &a, &b, &selection).is_err());
}

#[test]
fn cold_and_warm_cannot_be_relabelled_as_repetitions_or_reordered() {
    let (plan, a, b, selection) = fixture();
    let mut mixed = selection.clone();
    mixed.repetitions = 2;
    mixed.focus = "compile".into();
    for pair in &mut mixed.pairs {
        let (temperature, action) = pair.action.split_once('-').unwrap();
        pair.repetition = u32::from(temperature == "warm");
        pair.action = action.to_owned();
    }
    assert!(valid(&plan, &a, &b, &mixed).is_err());
    let mut swapped = selection;
    let cold = swapped.pairs[0].candidate;
    swapped.pairs[0].candidate = swapped.pairs[3].candidate;
    swapped.pairs[3].candidate = cold;
    assert!(valid(&plan, &a, &b, &swapped).is_err());
}

#[test]
fn retained_dependency_order_and_declared_timeout_cannot_be_omitted() {
    let (plan, a, b, selection) = fixture();
    let mut deps = plan.clone();
    deps.nodes[9]
        .dependencies
        .retain(|edge| edge.node != NodeId(7));
    assert!(valid(&deps, &a, &b, &selection).is_err());
    let mut timeout = plan;
    timeout.nodes[9].timeout_ns += 1;
    assert!(valid(&timeout, &a, &b, &selection).is_err());
}

#[test]
fn land_source_population_binds_compared_programs_and_round_trips_explicit_pairs() {
    let (plan, _, _, _) = fixture();
    let selection = LandSelection {
        sources: vec![SourcePair {
            baseline: 0,
            candidate: 1,
        }],
    };
    let comparison = NodeId(plan.nodes.len() as u32 - 1);
    selection.validate(&plan, 1, comparison).unwrap();
    let mut e = Encoder::new(106);
    selection.write(&mut e).unwrap();
    let bytes = e.finish().unwrap();
    let mut d = header(&bytes, 106).unwrap();
    assert_eq!(LandSelection::read(&mut d).unwrap(), selection);
    d.done().unwrap();
    assert!(selection.validate(&plan, 2, comparison).is_err());
    assert!(selection.validate(&plan, 1, NodeId(0)).is_err());
}

#[test]
fn land_cannot_duplicate_or_cross_graft_original_source_endpoints() {
    let (plan, _, _, _) = fixture();
    let comparison = NodeId(plan.nodes.len() as u32 - 1);
    for sources in [
        vec![],
        vec![SourcePair {
            baseline: 0,
            candidate: 0,
        }],
        vec![
            SourcePair {
                baseline: 0,
                candidate: 1,
            },
            SourcePair {
                baseline: 2,
                candidate: 1,
            },
        ],
        vec![
            SourcePair {
                baseline: 0,
                candidate: 1,
            },
            SourcePair {
                baseline: 1,
                candidate: 2,
            },
        ],
        vec![SourcePair {
            baseline: 0,
            candidate: 3,
        }],
        vec![SourcePair {
            baseline: 2,
            candidate: 1,
        }],
    ] {
        assert!(
            LandSelection { sources }
                .validate(&plan, 1, comparison)
                .is_err()
        );
    }
}
