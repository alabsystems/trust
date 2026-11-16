use std::collections::BTreeSet;

use clean_kernel::expr::BinderInfo;

use super::*;

fn captures(parts: &[Vec<u8>]) -> Vec<Captured> {
    (0..4).map(|index| {
        let bytes = parts.get(index).cloned();
        let record = match &bytes {
            Some(bytes) => json!({"status":"captured", "sha256":super::super::hash(bytes), "path":{"display":format!("part-{index}")}}),
            None => json!({"status":"absent"}),
        };
        Captured {bytes,record}
    }).collect()
}

fn graph(expr: &Result<Expr, String>, bounds: Bounds) -> (Value, Graph<'_>) {
    let mut graph = Graph::new(bounds);
    let root = graph.root(expr);
    (root, graph)
}

#[test]
fn core_graph_keeps_shared_children_large_nats_and_nondep() {
    let huge = Expr::bignat_lit(BigNat::Big(vec![7, 0, 1]));
    let shared = Arc::new(huge);
    let app = Expr::app_arc(shared.clone(), shared);
    let expr = Ok(Expr::let_named(
        Name::str(Name::anon(), "x.y"),
        Expr::sort(Level::zero()),
        app,
        Expr::bvar(0),
        true,
    ));
    let (root, dag) = graph(&expr, Bounds::default());
    assert_eq!(root["status"], "projected");
    let node = &dag.expressions[root["root"].as_u64().unwrap() as usize];
    assert_eq!(node["kind"], "let");
    assert_eq!(node["nondep"], true);
    assert_eq!(node["name"], json!([{"kind":"str","value":"x.y"}]));
    assert!(dag.expressions.iter().any(|n| n["limbs_le_u64"] == json!([7, 0, 1])));
    let app = dag.expressions.iter().find(|n| n["kind"] == "app").unwrap();
    assert_eq!(app["fun"], app["arg"]);
}

#[test]
fn structural_levels_names_binders_and_projection_are_retained() {
    let quoted = Name::str(Name::anon(), "u.v");
    let level = Level::IMax(
        Level::Param(quoted.clone()).into(),
        Level::Max(Level::Zero.into(), Level::Succ(Level::Zero.into()).into()).into(),
    );
    let value = Expr::const_(Name::num(Name::str(Name::anon(), "Family"), 7), vec![level]);
    let expr = Ok(Expr::lam(
        BinderInfo::Implicit,
        Expr::sort(Level::zero()),
        Expr::proj(quoted, 2, value),
    ));
    let (root, dag) = graph(&expr, Bounds::default());
    assert_eq!(root["status"], "projected");
    assert!(dag.expressions.iter().any(|n| n["kind"] == "proj" && n["index"] == 2));
    for kind in ["zero", "succ", "max", "imax", "param"] {
        assert!(dag.levels.iter().any(|n| n["kind"] == kind), "{kind}");
    }
    assert!(dag.expressions.iter().any(|n| n["binder"]["info"] == "Implicit"));
}

#[test]
fn projection_bounds_and_repeated_failed_root_stay_partial() {
    let expr = Ok(Expr::app(Expr::bvar(0), Expr::bvar(1)));
    let mut graph = Graph::new(Bounds { nodes: 1, scalar_bytes: 100 });
    assert_eq!(graph.root(&expr)["status"], "partial");
    assert_eq!(graph.root(&expr)["status"], "partial");
    assert_eq!(graph.expressions.len(), 1);
    assert_eq!(graph.expressions[0]["kind"], "unrepresented");
    let expr = Ok(Expr::bignat_lit(BigNat::Big(vec![1, 2, 3])));
    let (root, _) = self::graph(&expr, Bounds { nodes: 10, scalar_bytes: 8 });
    assert_eq!(root["status"], "partial");
}

#[test]
fn captures_missing_base_malformed_parts_and_ir_are_not_empty_successes() {
    let captured = captures(&[vec![0; 160], vec![0; 160], vec![0; 160], vec![0; 160]]);
    let observed = observe(&captured);
    for part in &observed[..3] {
        assert_eq!(part["status"], "part-decode-failed");
        assert!(part["source_row_count"].is_null());
        assert!(part["part_error"].is_string());
    }
    assert_eq!(observed[3]["status"], "not-a-kernel-module-part");
    let mut captured = captured;
    captured[0].bytes = None;
    assert_eq!(observe(&captured)[1]["status"], "missing-captured-base");
}

#[test]
fn reconciliation_never_joins_by_dotted_spelling_or_ignores_kind() {
    let name = names::ModuleName(vec![names::Segment::Str("a.b".into())]);
    let raw = names::NameRow {
        index: 0,
        name: Some(name.clone()),
        error: None,
        constant_tag: Some(1),
        runtime_only: None,
        import_flags: None,
    };
    let witness = names::Witness { constants: vec![raw], ..Default::default() };
    let mut report = json!({"source_row_count":1,"rows":[{"index":0,"decoded_name":name,"declaration":{"kind":"definition"}}]});
    reconcile(&mut report, &witness);
    assert_eq!(report["raw_witness_reconciliation"]["status"], "exact-row-identities-agree");
    let original = report.clone();
    report["rows"]
        .as_array_mut()
        .unwrap()
        .push(json!({"index":1,"decoded_name":name,"declaration":{"kind":"definition"}}));
    reconcile(&mut report, &witness);
    assert_eq!(report["raw_witness_reconciliation"]["status"], "incomplete-or-disagrees");
    report = original;
    report["rows"][0]["decoded_name"] =
        json!([{"kind":"str","value":"a"},{"kind":"str","value":"b"}]);
    reconcile(&mut report, &witness);
    assert_eq!(report["raw_witness_reconciliation"]["status"], "incomplete-or-disagrees");
    report["rows"][0]["decoded_name"] = json!(name);
    report["rows"][0]["declaration"]["kind"] = json!("axiom");
    reconcile(&mut report, &witness);
    assert_eq!(report["raw_witness_reconciliation"]["status"], "incomplete-or-disagrees");
}

fn fixture() -> (Vec<Captured>, Value) {
    let root = std::path::PathBuf::from(std::env::var_os("TRUST_RUNTIME_CONTENT_FIXTURE").expect(
        "TRUST_RUNTIME_CONTENT_FIXTURE must name the captured pinned-Lean fixture directory",
    ));
    let parts = ["RuntimeProbe.olean", "RuntimeProbe.olean.server", "RuntimeProbe.olean.private"]
        .map(|p| std::fs::read(root.join(p)).unwrap());
    let oracle =
        serde_json::from_str(&std::fs::read_to_string(root.join("oracle.stdout")).unwrap())
            .unwrap();
    (captures(&parts), oracle)
}

#[test]
#[ignore = "requires actual pinned runtime fixture"]
fn actual_cumulative_rows_names_stubs_and_partial_body_are_retained() {
    let (captured, _) = fixture();
    let observed = observe(&captured);
    let mut unique = BTreeSet::new();
    for (index, count) in [24, 24, 25].into_iter().enumerate() {
        let part = &observed[index];
        assert_eq!(part["source_row_count"], count);
        assert_eq!(part["rows"].as_array().unwrap().len(), count);
        assert!(part["part_error"].is_null());
        assert_eq!(part["borrowed_prefix"].as_array().unwrap().len(), index);
        for row in part["rows"].as_array().unwrap() {
            assert!(row["projection_error"].is_null(), "{row}");
            assert_eq!(row["projection_graph_complete"], true);
            unique.insert(row["decoded_name"].to_string());
        }
    }
    assert_eq!(unique.len(), 25);
    let find = |part: usize, components: &[&str]| {
        observed[part]["rows"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| {
                row["decoded_name"]
                    == json!(
                        components
                            .iter()
                            .map(|s| json!({"kind":"str","value":s}))
                            .collect::<Vec<_>>()
                    )
            })
            .unwrap()
    };
    let generated = &["RuntimeProbe", "count", "_unsafe_rec"];
    assert_eq!(find(0, generated)["declaration"]["body"]["status"], "no-stored-value-for-kind");
    assert_eq!(find(2, generated)["declaration"]["body"]["status"], "stored");
    assert_eq!(find(2, generated)["declaration"]["safety"], "partial");
    assert_eq!(find(2, &["RuntimeProbe", "count._unsafe_rec"])["declaration"]["safety"], "safe");
    assert_eq!(observed[2]["runtime_body_universe"], "unmeasured");
}

fn compare_level(graph: &Value, id: &Value, oracle: &Value, depth: usize) {
    assert!(depth < 256);
    let node = &graph["levels"][id.as_u64().expect("level reference") as usize];
    assert_eq!(node["kind"], oracle["tag"]);
    match oracle["tag"].as_str().unwrap() {
        "zero" => (),
        "param" => assert_eq!(node["name"], oracle["name"]),
        "succ" => compare_level(graph, &node["inner"], &oracle["inner"], depth + 1),
        "max" | "imax" => {
            for child in ["left", "right"] {
                compare_level(graph, &node[child], &oracle[child], depth + 1)
            }
        }
        other => panic!("oracle Level {other}"),
    }
}

fn compare_core(graph: &Value, id: &Value, oracle: &Value, depth: usize) {
    assert!(depth < 512);
    let node = &graph["expressions"][id.as_u64().expect("expression reference") as usize];
    assert_eq!(node["kind"], oracle["tag"]);
    let mut children = Vec::new();
    match oracle["tag"].as_str().unwrap() {
        "bvar" => assert_eq!(node["index"], oracle["index"]),
        "sort" => compare_level(graph, &node["level"], &oracle["level"], 0),
        "const" => {
            assert_eq!(node["name"], oracle["name"]);
            let actual = node["levels"].as_array().unwrap();
            let expected = oracle["levels"].as_array().unwrap();
            assert_eq!(actual.len(), expected.len());
            for (actual, expected) in actual.iter().zip(expected) {
                compare_level(graph, actual, expected, 0)
            }
        }
        "app" => children.extend(["fun", "arg"]),
        "lam" | "pi" => {
            let binder = ["Default", "Implicit", "StrictImplicit", "InstImplicit"]
                [oracle["binder"].as_u64().unwrap() as usize];
            assert_eq!(node["binder"]["info"], binder);
            assert_eq!(node["binder"]["mult"], "Many");
            children.extend(["type", "body"]);
        }
        "let" => {
            assert_eq!(node["name"], oracle["name"]);
            assert_eq!(node["nondep"], oracle["nondep"]);
            children.extend(["type", "value", "body"]);
        }
        "proj" => {
            assert_eq!(node["name"], oracle["name"]);
            assert_eq!(node["index"], oracle["index"]);
            children.push("value");
        }
        "nat" => assert_eq!(
            node["limbs_le_u64"],
            json!([oracle["value"]
                .as_u64()
                .expect("fixture Nat is small; separate arbitrary-limb control")])
        ),
        "str" => assert_eq!(node["value"], oracle["value"]),
        "mdata-unmeasured" => children.push("value"),
        other => panic!("oracle Expr {other}"),
    }
    for child in children {
        compare_core(graph, &node[child], &oracle[child], depth + 1);
    }
}

#[test]
#[ignore = "requires actual pinned runtime fixture"]
fn actual_every_core_type_body_rule_and_family_matches_independent_oracle() {
    let (captured, oracle) = fixture();
    let observed = observe(&captured);
    let mut count = 0;
    for (part, expected) in observed[..3].iter().zip(oracle["parts"].as_array().unwrap()) {
        let rows = part["rows"].as_array().unwrap();
        let expected = expected["constants"].as_array().unwrap();
        assert_eq!(rows.len(), expected.len());
        for (actual, expected) in rows.iter().zip(expected) {
            count += 1;
            let actual = &actual["declaration"];
            assert_eq!(actual["name"], expected["name"]);
            assert_eq!(actual["kind"], expected["kind"]);
            match expected["kind"].as_str().unwrap() {
                "definition" | "axiom" | "opaque" => {
                    assert_eq!(actual["safety"], expected["safety"])
                }
                "inductive" | "constructor" | "recursor" => {
                    assert!(actual["safety"].is_null());
                    assert_eq!(actual["family"]["is_unsafe"], expected["family"]["is_unsafe"]);
                }
                "theorem" => {
                    assert!(actual["safety"].is_null());
                    assert_eq!(expected["safety"], "none");
                }
                other => panic!("unmeasured fixture kind {other}"),
            }
            assert_eq!(actual["level_params"], expected["levels"]);
            assert_eq!(actual["type"]["status"], "projected");
            compare_core(&part["core_graph"], &actual["type"]["root"], &expected["type_core"], 0);
            if !expected["value_core"].is_null() {
                assert_eq!(actual["body"]["status"], "stored");
                assert_eq!(actual["body"]["expression"]["status"], "projected");
                compare_core(
                    &part["core_graph"],
                    &actual["body"]["expression"]["root"],
                    &expected["value_core"],
                    0,
                );
            } else {
                assert_eq!(actual["body"]["status"], "no-stored-value-for-kind");
            }
            let family = &expected["family"];
            if family.is_null() {
                assert_eq!(actual["family"]["kind"], "none");
                continue;
            }
            for (key, value) in family.as_object().unwrap() {
                if key == "rules" {
                    let rules = actual["family"]["rules"].as_array().unwrap();
                    assert_eq!(rules.len(), value.as_array().unwrap().len());
                    for (rule, expected) in rules.iter().zip(value.as_array().unwrap()) {
                        assert_eq!(rule["constructor"], expected["constructor"]);
                        assert_eq!(rule["num_fields"], expected["num_fields"]);
                        compare_core(
                            &part["core_graph"],
                            &rule["rhs"]["root"],
                            &expected["rhs"],
                            0,
                        );
                    }
                } else if key == "all"
                    && matches!(
                        expected["kind"].as_str(),
                        Some("definition" | "theorem" | "opaque")
                    )
                {
                    assert_eq!(&actual["mutual_declarations"], value);
                } else {
                    assert_eq!(&actual["family"][key], value, "family {key}");
                }
            }
        }
    }
    assert_eq!(count, 73);
}

fn raw_word(parts: &[Vec<u8>], pointer: u64) -> u64 {
    for part in parts {
        let base = clean_olean::OleanHeader::parse(part).unwrap().base_addr;
        if let Some(offset) = pointer.checked_sub(base).and_then(|o| usize::try_from(o).ok()) {
            if let Some(bytes) = part.get(offset..offset.saturating_add(8)) {
                return u64::from_le_bytes(bytes.try_into().unwrap());
            }
        }
    }
    panic!("uncaptured test word");
}

fn change_word(parts: &mut [Vec<u8>], pointer: u64, value: u64) {
    for part in parts {
        let base = clean_olean::OleanHeader::parse(part).unwrap().base_addr;
        if let Some(offset) = pointer.checked_sub(base).and_then(|o| usize::try_from(o).ok()) {
            if let Some(bytes) = part.get_mut(offset..offset.saturating_add(8)) {
                bytes.copy_from_slice(&value.to_le_bytes());
                return;
            }
        }
    }
    panic!("uncaptured test mutation");
}

#[test]
#[ignore = "requires actual pinned runtime fixture"]
fn actual_malformed_row_and_borrowed_prefix_changes_retain_population() {
    let (captured, _) = fixture();
    let original = observe(&captured);
    let mut parts: Vec<_> = captured[..3].iter().map(|c| c.bytes.clone().unwrap()).collect();
    let base_header = clean_olean::OleanHeader::parse(&parts[0]).unwrap();
    let root = raw_word(&parts, base_header.base_addr + clean_olean::header::HEADER_SIZE_V2 as u64);
    let constants = raw_word(&parts, root + 24);
    let first = raw_word(&parts, constants + 24);
    // Preserve the slot; make only this ConstantInfo tag unsupported.
    let header = raw_word(&parts, first);
    change_word(&mut parts, first, (header & !(0xff << 56)) | (255u64 << 56));
    let changed = observe(&captures(&parts));
    assert_eq!(changed[0]["source_row_count"], 24);
    assert_eq!(changed[0]["rows"].as_array().unwrap().len(), 24);
    assert!(changed[0]["rows"][0]["projection_error"].is_string());
    assert!(changed[0]["rows"][1]["projection_error"].is_null());
    assert_eq!(original[2]["identity"]["capture_sha256"], changed[2]["identity"]["capture_sha256"]);
    assert_ne!(original[2]["borrowed_prefix"], changed[2]["borrowed_prefix"]);
    assert_ne!(original[0]["identity"], changed[0]["identity"]);
}

#[test]
#[ignore = "requires actual pinned runtime fixture"]
fn actual_changed_body_missing_value_and_valid_borrowed_name_are_observed() {
    let (captured, oracle) = fixture();
    let original = observe(&captured);
    let mut parts: Vec<_> = captured[..3].iter().map(|c| c.bytes.clone().unwrap()).collect();
    let rows = original[2]["rows"].as_array().unwrap();
    let target=rows.iter().position(|r|r["decoded_name"]==json!([
        {"kind":"str","value":"RuntimeProbe"},{"kind":"str","value":"count"},{"kind":"str","value":"_unsafe_rec"}])).unwrap();
    let other = rows
        .iter()
        .position(|r| {
            r["decoded_name"]
                == json!([
        {"kind":"str","value":"RuntimeProbe"},{"kind":"str","value":"count._unsafe_rec"}])
        })
        .unwrap();
    let header = clean_olean::OleanHeader::parse(&parts[2]).unwrap();
    let root = raw_word(&parts, header.base_addr + clean_olean::header::HEADER_SIZE_V2 as u64);
    let array = raw_word(&parts, root + 24);
    let value = |parts: &[Vec<u8>], index: usize| {
        raw_word(parts, raw_word(parts, array + 24 + index as u64 * 8) + 8)
    };
    let target_value = value(&parts, target);
    let replacement = raw_word(&parts, value(&parts, other) + 16);
    change_word(&mut parts, target_value + 16, replacement);
    let changed = observe(&captures(&parts));
    let body = &changed[2]["rows"][target]["declaration"]["body"]["expression"];
    compare_core(
        &changed[2]["core_graph"],
        &body["root"],
        &oracle["parts"][2]["constants"][other]["value_core"],
        0,
    );
    assert_eq!(changed[2]["rows"][target]["declaration"]["safety"], "partial");
    assert_ne!(original[2]["identity"], changed[2]["identity"]);
    change_word(&mut parts, target_value + 16, 0);
    let missing = observe(&captures(&parts));
    assert_eq!(
        missing[2]["rows"][target]["declaration"]["body"]["status"],
        "missing-required-value"
    );
    assert_eq!(missing[2]["source_row_count"], 25);
    // A valid borrowed string change changes typed content despite identical
    // private bytes. Prefix hashes are therefore part of every observation.
    let mut parts: Vec<_> = captured[..3].iter().map(|c| c.bytes.clone().unwrap()).collect();
    let positions: Vec<_> = parts[0]
        .windows(6)
        .enumerate()
        .filter_map(|(i, b)| (b == b"Unary\0").then_some(i))
        .collect();
    assert!(!positions.is_empty());
    for index in positions {
        parts[0][index] = b'V';
    }
    let borrowed = observe(&captures(&parts));
    assert_eq!(original[2]["identity"], borrowed[2]["identity"]);
    assert_ne!(original[2]["borrowed_prefix"], borrowed[2]["borrowed_prefix"]);
    assert_ne!(original[2]["rows"], borrowed[2]["rows"]);
    assert_eq!(borrowed[2]["source_row_count"], 25);
}

#[test]
#[ignore = "requires actual pinned runtime fixture"]
fn actual_frontdoor_preserves_independent_raw_parser_and_ir_observations() {
    use super::super::{
        OleanCensusLimits, OleanCensusSource, observe_olean_closure, part_dependencies,
    };
    let root = std::path::PathBuf::from(
        std::env::var_os("TRUST_RUNTIME_CONTENT_FIXTURE").expect("explicit fixture required"),
    );
    let (captured, _) = fixture();
    let report = observe_olean_closure(
        &[OleanCensusSource {
            module: "Main".into(),
            path: root.join("MissingSource.lean"),
            source: Ok("import RuntimeProbe\n".into()),
        }],
        &[root],
        OleanCensusLimits::default(),
    );
    let module = report
        .modules
        .iter()
        .find(|m| m["name"] == json!([{"kind":"str","value":"RuntimeProbe"}]))
        .unwrap();
    let parts = module["candidates"][0]["parts"].as_array().unwrap();
    for index in 0..3 {
        let bytes = captured[index].bytes.as_ref().unwrap();
        let indices = part_dependencies(
            bytes,
            captured[0].bytes.as_deref(),
            captured[1].bytes.as_deref(),
            index,
        )
        .unwrap();
        let dependencies: Vec<_> =
            indices.iter().map(|&i| captured[i].bytes.as_deref().unwrap()).collect();
        let witness = names::witness(bytes, &dependencies, 1_000_000);
        assert_eq!(parts[index]["raw_name_witness"], json!(witness));
        let ir = super::super::ir::observe(bytes, &dependencies, 1_000_000, 200_000);
        assert_eq!(parts[index]["runtime_ir"], ir.report);
        if witness.errors.is_empty() {
            let parsed = if indices.is_empty() {
                clean_olean::parse_module(bytes)
            } else {
                clean_olean::parse_module_incremental(
                    captured[0].bytes.as_deref().unwrap(),
                    if indices.len() == 2 { captured[1].bytes.as_deref() } else { None },
                    bytes,
                )
            };
            if let Ok(parsed) = parsed {
                let mut issues = Vec::new();
                assert_eq!(
                    parts[index]["declarations"],
                    json!(super::super::parsed_rows(&parsed, &witness, &mut issues))
                );
                assert_eq!(
                    parts[index]["clean_payload"],
                    parsed
                        .clean_payload
                        .map(|p| serde_json::to_value(p).unwrap())
                        .unwrap_or(Value::Null)
                );
            } else {
                assert_eq!(parts[index]["parse_status"], "malformed-or-unresolved-part");
            }
        }
        assert_eq!(parts[index]["declaration_content"]["source_row_count"], [24, 24, 25][index]);
    }
    assert_eq!(report.runtime_body_universe, "unmeasured");
    assert_eq!(report.denominator_status, "denominator_unverified");
}

#[test]
fn decode_failures_and_unsupported_exprs_never_become_projected_roots() {
    let failed = Err("retained direct reader failure".to_string());
    let (root, dag) = graph(&failed, Bounds::default());
    assert_eq!(root["status"], "unrepresented");
    assert_eq!(root["error"], "retained direct reader failure");
    assert!(dag.expressions.is_empty());
    assert_eq!(dag.errors.len(), 1);
    let non_imported = Ok(Expr::from_kind(ExprKind::SProp));
    let (root, dag) = graph(&non_imported, Bounds::default());
    assert_eq!(root["status"], "partial");
    assert_eq!(root["graph_error_count"], 1);
    assert!(root["errors"].is_null());
    assert_eq!(dag.expressions[0]["kind"], "unrepresented");
}

#[test]
fn zero_capacity_and_direct_reader_root_error_mark_row_graph_incomplete() {
    let declaration = |type_| RuntimeDeclaration {
        name: Name::anon().str("Root"),
        kind: ConstantKind::Axiom,
        level_params: vec![],
        declaration_safety: Some(DefinitionSafety::Safe),
        hints: None,
        mutual_declarations: None,
        type_,
        body: RuntimeBody::NoStoredValueForKind,
        family: RuntimeFamily::None,
        dependencies: BTreeSet::new(),
        represented_fields_complete: false,
        issues: vec!["test direct-reader boundary".into()],
    };
    for (root, bounds) in [
        (Ok(Expr::sort(Level::zero())), Bounds { nodes: 0, scalar_bytes: 100 }),
        (Err("actual root error retained".into()), Bounds::default()),
    ] {
        let part = RuntimePartExtraction {
            identity: RuntimePartIdentity {
                part: RuntimeOleanPart::Base,
                label: "test".into(),
                byte_count: 0,
                blake3: [0; 32],
            },
            captured: RuntimeOleanInput { label: "test".into(), bytes: Arc::from([]) },
            borrowed_prefix: vec![],
            source_row_count: Some(1),
            rows: vec![clean_olean::RuntimeDeclarationRow {
                index: 0,
                declaration: Ok(declaration(root)),
            }],
            error: None,
        };
        let report = part_report(&part, &captures(&[vec![]]), bounds);
        assert_eq!(report["source_row_count"], 1);
        assert_eq!(report["rows"][0]["projection_graph_complete"], false);
        assert_eq!(report["rows"][0]["declaration"]["type"]["status"], "unrepresented");
        assert!(!report["core_graph"]["errors"].as_array().unwrap().is_empty());
        let identity_bound =
            part_report(&part, &captures(&[vec![]]), Bounds { nodes: 100, scalar_bytes: 0 });
        assert_eq!(identity_bound["source_row_count"], 1);
        assert_eq!(identity_bound["rows"][0]["index"], 0);
        assert_eq!(identity_bound["identity"], report["identity"]);
        assert!(identity_bound["rows"][0]["decoded_name"].is_null());
        assert!(identity_bound["rows"][0]["identity_projection_error"].is_string());
        assert_eq!(identity_bound["rows"][0]["projection_graph_complete"], false);
    }
}
