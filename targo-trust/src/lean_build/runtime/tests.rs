use super::*;

const SOURCE: &str = "inductive Data where\n  | make : Data\ndef identity (x : Data) : Data := x\ndef twice (x : Data) : Data := identity (identity x)\n";

// This is the unchanged complete original source of the separate logical
// quotation prerequisite. Its accepted payload is not that quotation, and the
// existing Object/RC diagnostic emitter is allowed to refuse it.
const ESCAPING_ORIGINAL: &str = include_str!(
    "../../../../crates/trust-clean-ir-gate/probes/source_closure_refinement/Original.lean"
);

fn request(dir: &Path, source: &str, entry: &str) -> Request {
    std::fs::write(dir.join("Main.lean"), source).unwrap();
    parse(&[
        dir.join("Main.lean").display().to_string(),
        "--emit=diagnostic-runtime-trust-ir".into(),
        "--entry".into(),
        entry.into(),
        "--out".into(),
        dir.join("new.tmbc").display().to_string(),
        "--census".into(),
        dir.join("new.json").display().to_string(),
    ])
    .unwrap()
}
fn report(request: &Request) -> Value {
    serde_json::from_slice(&std::fs::read(request.build.census_output.as_ref().unwrap()).unwrap())
        .unwrap()
}

fn original_payload<'a>(receipt: &'a Value, name: &str) -> &'a Value {
    receipt["accepted_original"]["owned_payloads"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["name"] == json!(Name::from_string(name)))
        .unwrap()
}

#[test]
fn accepted_original_attachment_retains_all_three_real_bodies_on_refusal() {
    let dir = tempfile::tempdir().unwrap();
    let request = request(dir.path(), ESCAPING_ORIGINAL, "EscapingOriginal.useAffine");
    let checked =
        crate::lean_cli::check_batch_for_runtime(std::slice::from_ref(&request.build.input));
    let accepted = checked.accepted_context().expect("actual original source is accepted");
    assert_eq!(accepted.owned_declarations().len(), 3);
    let error = build(&request).expect_err("logical quotation does not authorize runtime emission");
    assert!(!error.is_empty());
    assert!(!request.build.output.exists());
    let observed = report(&request);
    let receipt = &observed["diagnostic_runtime"];
    assert_eq!(receipt["status"], "refused-no-artifact");
    assert!(receipt["module_attachment"].is_null());
    let original = &receipt["accepted_original"];
    assert_eq!(original["authority"], "none-data-only-not-source-refinement");
    assert_eq!(original["capture_delta_complete"], true);
    assert_eq!(original["sources"][0]["source"], ESCAPING_ORIGINAL);
    assert_eq!(original["source_closure_sha256"], accepted.source_closure_sha256());
    assert_eq!(original["owned_declarations_sha256"], accepted.owned_declarations_sha256());
    assert_eq!(original["owned_payloads"].as_array().unwrap().len(), 3);
    for name in
        ["EscapingOriginal.makeAffine", "EscapingOriginal.apply64", "EscapingOriginal.useAffine"]
    {
        let row = original_payload(receipt, name);
        let info = accepted.environment().get_const(&Name::from_string(name)).unwrap();
        assert_eq!(row["constant"], serde_json::to_value(info).unwrap());
        assert!(!row["constant"]["value"].is_null(), "full original body retained");
        assert!(!row["constant"]["type_"].is_null(), "full original type retained");
        for role in ["inductive", "constructor", "recursor", "quotient"] {
            assert!(row.as_object().unwrap().contains_key(role), "complete represented roles");
        }
    }
}

#[test]
fn typed_closure_candidate_retains_real_module_without_runtime_or_object_permission() {
    let dir = tempfile::tempdir().unwrap();
    let request = request(dir.path(), ESCAPING_ORIGINAL, "EscapingOriginal.useAffine");
    assert!(build(&request).is_err());
    assert!(!request.build.output.exists());
    let receipt = report(&request);
    let runtime = &receipt["diagnostic_runtime"];
    assert_eq!(runtime["status"], "refused-no-artifact");
    assert!(runtime["module_attachment"].is_null());
    let candidate = &runtime["typed_closure_candidate"];
    assert_eq!(candidate["status"], "candidate-data", "{candidate}");
    assert_eq!(candidate["authority"], "none-data-only-not-source-refinement");
    assert_eq!(
        candidate["environment_snapshot_blake3"],
        runtime["context"]["source"]["snapshot_blake3"]
    );
    assert!(!candidate["environment_snapshot_blake3"].is_null());
    assert_eq!(candidate["complete_owned_roster"].as_array().unwrap().len(), 3);
    assert_eq!(candidate["originals"].as_array().unwrap().len(), 3);
    for row in candidate["originals"].as_array().unwrap() {
        let original = runtime["accepted_original"]["owned_payloads"]
            .as_array()
            .unwrap()
            .iter()
            .find(|original| original["name"] == row["constant"]["name"])
            .unwrap();
        assert_eq!(original["constant"], row["constant"]);
    }
    let module: trust_ir::Module = serde_json::from_value(candidate["module"].clone()).unwrap();
    assert_eq!(module.functions.len(), 4);
    assert!(module.functions.iter().all(|f| !f.blocks.is_empty()
        && f.body_gate == Some(trust_ir::BodyGate::Ungated)
        && f.calling_conv == trust_ir::CallingConv::Rust));
    let bytes: Vec<u8> = serde_json::from_value(candidate["wire_bytes"].clone()).unwrap();
    assert_eq!(trust_ir::binary::deserialize_module(&bytes).unwrap(), module);
    assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(), bytes);
    assert_eq!(candidate["wire_sha256"], format!("{:x}", Sha256::digest(&bytes)));

    // The ordinary full-source library and strict object paths still refuse
    // their original missing function carrier. Candidate DATA is not consulted.
    for object in [false, true] {
        let ordinary = super::super::Request {
            input: request.build.input.clone(),
            output: dir.path().join(if object { "strict.o" } else { "library.json" }),
            verbose: false,
            census_output: None,
            olean_paths: Vec::new(),
        };
        let error = super::super::build_artifact(&ordinary, object).unwrap_err().render(true);
        assert!(error.contains("carrier"), "{error}");
        assert!(!ordinary.output.exists());
    }
}

#[test]
fn typed_closure_candidate_tracks_actual_body_capture_and_complete_roster_changes() {
    let mut modules = Vec::new();
    for source in [
        ESCAPING_ORIGINAL.to_owned(),
        ESCAPING_ORIGINAL.replace("a * x + b", "a + x + b"),
        ESCAPING_ORIGINAL.replace("makeAffine a b\n", "makeAffine b a\n"),
    ] {
        let dir = tempfile::tempdir().unwrap();
        let request = request(dir.path(), &source, "EscapingOriginal.useAffine");
        assert!(build(&request).is_err());
        assert!(!request.build.output.exists());
        let receipt = report(&request);
        let candidate = &receipt["diagnostic_runtime"]["typed_closure_candidate"];
        assert_eq!(candidate["status"], "candidate-data", "{candidate}");
        modules.push(candidate["module"].clone());
    }
    assert_ne!(modules[0], modules[1]);
    assert_ne!(modules[0], modules[2]);

    let dir = tempfile::tempdir().unwrap();
    let source = format!("{ESCAPING_ORIGINAL}\ndef unselected (x : UInt64) : UInt64 := x\n");
    let request = request(dir.path(), &source, "EscapingOriginal.useAffine");
    assert!(build(&request).is_err());
    assert!(!request.build.output.exists());
    let receipt = report(&request);
    let runtime = &receipt["diagnostic_runtime"];
    assert_eq!(runtime["typed_closure_candidate"]["status"], "refused-no-candidate");
    assert!(runtime["typed_closure_candidate"]["module"].is_null());
    assert_eq!(runtime["accepted_original"]["owned_payloads"].as_array().unwrap().len(), 4);
}

#[test]
fn accepted_original_attachment_observes_a_real_source_body_mutation() {
    let original_dir = tempfile::tempdir().unwrap();
    let changed_dir = tempfile::tempdir().unwrap();
    let changed = ESCAPING_ORIGINAL.replace("a * x + b", "a + x + b");
    assert_ne!(changed, ESCAPING_ORIGINAL);
    let original = request(original_dir.path(), ESCAPING_ORIGINAL, "EscapingOriginal.useAffine");
    let mutated = request(changed_dir.path(), &changed, "EscapingOriginal.useAffine");
    for request in [&original, &mutated] {
        assert!(build(request).is_err());
        assert!(!request.build.output.exists());
    }
    let a = report(&original);
    let b = report(&mutated);
    let a = &a["diagnostic_runtime"];
    let b = &b["diagnostic_runtime"];
    assert_ne!(
        a["accepted_original"]["source_closure_sha256"],
        b["accepted_original"]["source_closure_sha256"]
    );
    assert_ne!(
        a["accepted_original"]["owned_declarations_sha256"],
        b["accepted_original"]["owned_declarations_sha256"]
    );
    assert_ne!(
        original_payload(a, "EscapingOriginal.makeAffine")["constant"]["value"],
        original_payload(b, "EscapingOriginal.makeAffine")["constant"]["value"]
    );
    assert!(a["module_attachment"].is_null() && b["module_attachment"].is_null());
}

#[test]
fn accepted_original_attachment_retains_the_known_uint64_metadata_refusal() {
    let dir = tempfile::tempdir().unwrap();
    let source = "def scalar (x : UInt64) : UInt64 := x\n";
    let request = request(dir.path(), source, "scalar");
    let error = build(&request).expect_err("UInt64 runtime metadata remains unsupported");
    assert!(
        error.contains("OfNat") && error.contains("constructor header and field metadata disagree"),
        "{error}"
    );
    assert!(!request.build.output.exists());
    let observed = report(&request);
    let receipt = &observed["diagnostic_runtime"];
    assert_eq!(receipt["accepted_original"]["sources"][0]["source"], source);
    assert_eq!(receipt["accepted_original"]["owned_payloads"].as_array().unwrap().len(), 1);
    assert!(!original_payload(receipt, "scalar")["constant"]["value"].is_null());
    assert!(receipt["module_attachment"].is_null());
}

#[test]
fn accepted_original_attachment_keeps_unselected_siblings_and_exact_produced_wire() {
    use clean_compiler::emit_trust_ir::deserialize_module_bytes;
    let with_sibling = "def scalar (x : Bool) : Bool := x\ndef sibling (x y : Bool) : Bool := x\n";
    let changed_body = with_sibling.replace(":= x\n", ":= y\n");
    // Only mutate the sibling; the selected root remains the same original.
    let changed_body = changed_body.replacen(
        "def scalar (x : Bool) : Bool := y",
        "def scalar (x : Bool) : Bool := x",
        1,
    );
    let no_sibling = "def scalar (x : Bool) : Bool := x\n";
    let mut receipts = Vec::new();
    for source in [with_sibling, changed_body.as_str(), no_sibling] {
        let dir = tempfile::tempdir().unwrap();
        let request = request(dir.path(), source, "scalar");
        build(&request).expect("actual scalar source diagnostic emission");
        let observed = report(&request);
        let receipt = &observed["diagnostic_runtime"];
        let attachment = &receipt["module_attachment"];
        let wire: Vec<u8> = serde_json::from_value(attachment["wire_bytes"].clone()).unwrap();
        assert_eq!(wire, std::fs::read(&request.build.output).unwrap());
        assert_eq!(&wire[..8], b"tMBC\x01\0\0\0");
        let actual = deserialize_module_bytes(&wire[8..]).expect("canonical actual wire reader");
        let data: trust_ir::Module = serde_json::from_value(attachment["module"].clone()).unwrap();
        assert_eq!(data, actual, "complete produced module, not a logical quotation");
        // Mutate the genuinely produced module, not a separately hand-authored
        // quotation. Transport equality is sensitive to its real convention;
        // this does not claim any semantic validator rejects forged receipts.
        let mut mutant = data.clone();
        mutant.functions[0].calling_conv =
            if mutant.functions[0].calling_conv == trust_ir::CallingConv::C {
                trust_ir::CallingConv::Rust
            } else {
                trust_ir::CallingConv::C
            };
        assert_ne!(serialize_diagnostic_module(&mutant).unwrap(), wire);
        assert_ne!(serde_json::to_value(mutant).unwrap(), attachment["module"]);
        assert_eq!(attachment["wire_sha256"], format!("{:x}", Sha256::digest(&wire)));
        assert_eq!(
            attachment["source_closure_sha256"],
            receipt["accepted_original"]["source_closure_sha256"]
        );
        assert_eq!(
            attachment["owned_declarations_sha256"],
            receipt["accepted_original"]["owned_declarations_sha256"]
        );
        assert_eq!(attachment["authority"], "none-data-only-not-source-refinement");
        receipts.push(receipt.clone());
    }
    assert_eq!(receipts[0]["accepted_original"]["owned_payloads"].as_array().unwrap().len(), 2);
    assert_ne!(
        original_payload(&receipts[0], "sibling")["constant"]["value"],
        original_payload(&receipts[1], "sibling")["constant"]["value"]
    );
    assert_eq!(receipts[2]["accepted_original"]["owned_payloads"].as_array().unwrap().len(), 1);
    assert_ne!(
        receipts[0]["accepted_original"]["owned_declarations_sha256"],
        receipts[2]["accepted_original"]["owned_declarations_sha256"]
    );
}

#[test]
fn diagnostic_runtime_serialization_refuses_unwireable_module() {
    let mut module = trust_ir::Module::new("runtime-wire-boundary");
    assert!(serialize_diagnostic_module(&module).unwrap().starts_with(b"tMBC"));

    module.completeness = Some(trust_ir::ModuleCompleteness::Complete);
    let error = serialize_diagnostic_module(&module).unwrap_err();
    assert!(error.contains("diagnostic runtime Trust-IR serialization refused"));
    assert!(error.contains("Module.completeness claim"), "{error}");
}

#[test]
fn diagnostic_selector_retains_quoted_unicode_numeric_and_hierarchy_identity() {
    assert_eq!(entry_name("A.B").unwrap(), Name::anon().str("A").str("B"));
    assert_eq!(entry_name("«A.B»").unwrap(), Name::anon().str("A.B"));
    assert_eq!(entry_name("A.«λ.7»").unwrap(), Name::anon().str("A").str("λ.7"));
    assert_eq!(entry_name("A.«7»").unwrap(), Name::anon().str("A").str("7"));
    assert_eq!(entry_json(r#"[{"str":"A"},{"num":7}]"#).unwrap(), Name::anon().str("A").num(7));
    assert_ne!(entry_name("A.«7»").unwrap(), entry_json(r#"[{"str":"A"},{"num":7}]"#).unwrap());
    for text in ["", "A.", "A B", "A + B", "A.7", "fun x => x", "(A)", "A.{u}"] {
        assert!(entry_name(text).is_err(), "{text}");
    }
    for text in ["[]", r#"[{"num":-1}]"#, r#"[{"str":"x","num":1}]"#, "null"] {
        assert!(entry_json(text).is_err(), "{text}");
    }
}

#[test]
fn selector_bound_messages_state_the_bound_the_guard_actually_enforces() {
    // Both guards are `> N`, so N itself is ACCEPTED. A half-open `1..N` in the
    // message would send a caller trimming a name that was already in range.
    let at_bound = "a".repeat(4096);
    let over_bound = "a".repeat(4097);
    assert!(entry_name(&at_bound).is_ok());
    for text in ["", over_bound.as_str()] {
        assert_eq!(entry_name(text).unwrap_err(), "entry identifier byte bound (1..=4096)");
    }
    let segments = |count: usize| format!("[{}]", vec![r#"{"str":"a"}"#; count].join(","));
    assert!(entry_json(&segments(128)).is_ok());
    for text in [segments(129), "[]".to_owned()] {
        assert_eq!(entry_json(&text).unwrap_err(), "entry JSON segment bound (1..=128)");
    }
}

#[test]
fn diagnostic_cli_requires_explicit_mode_census_and_one_entry() {
    let dir = tempfile::tempdir().unwrap();
    let base = vec![
        dir.path().join("Main.lean").display().to_string(),
        "--emit=diagnostic-runtime-trust-ir".into(),
        "--out=new.tmbc".into(),
    ];
    assert!(parse(&base).is_err());
    let mut args = base.clone();
    args.extend(["--entry=main".into(), "--census=new.json".into()]);
    assert!(parse(&args).is_ok());
    // The USAGE clause about `--verbose`: the shared library parser accepts it
    // in this lane too, and nothing here reads it back.
    let mut with_verbose = args.clone();
    with_verbose.push("--verbose".into());
    assert!(parse(&with_verbose).unwrap().build.verbose);
    assert!(USAGE.contains("--verbose is accepted through the shared library parser"));
    args.push("--entry-json=[{\"str\":\"main\"}]".into());
    assert!(parse(&args).is_err());
    assert!(
        super::super::parse(&base).is_err(),
        "ordinary library parser did not gain a runtime bypass"
    );
    assert!(USAGE.contains("do NOT enable source imports"));
}

#[test]
fn fresh_file_reaches_real_trust_ir_and_retains_all_owned_rows_and_call_occurrences() {
    let dir = tempfile::tempdir().unwrap();
    let request = request(dir.path(), SOURCE, "twice");
    build(&request).unwrap();
    let bytes = std::fs::read(&request.build.output).unwrap();
    assert!(bytes.starts_with(b"tMBC"));
    assert!(serde_json::from_slice::<super::super::LibraryEnvelope>(&bytes).is_err());
    let observed = report(&request);
    let runtime = &observed["diagnostic_runtime"];
    assert_eq!(runtime["status"], "diagnostic-artifact-candidate-not-yet-published");
    assert_eq!(runtime["candidate_artifact"]["sha256"], format!("{:x}", Sha256::digest(&bytes)));
    assert_eq!(runtime["context"]["source"]["delta_complete"], true);
    assert!(runtime["context"]["source"]["after_population"]["constants"].is_u64());
    assert!(runtime["selected_dependency_rows"].as_array().unwrap().iter().all(|row| {
        row["provenance"]["kind"] == "checked-source-environment-observation"
            && row["provenance"]["row_index"].is_u64()
            && row["provenance"]["snapshot_blake3"].as_array().is_some_and(|a| a.len() == 32)
    }));
    let checked = crate::lean_cli::check_batch(std::slice::from_ref(&request.build.input), true);
    let accepted = checked.accepted_context().unwrap();
    let owned: Vec<Name> =
        serde_json::from_value(runtime["context"]["source"]["added"].clone()).unwrap();
    assert_eq!(
        owned.into_iter().collect::<std::collections::BTreeSet<_>>(),
        *accepted.owned_declarations()
    );
    assert!(runtime["context"]["source"]["rows"].as_array().unwrap().len() > 2);
    let edges = runtime["emission"]["named_edge_occurrences"].as_array().unwrap();
    assert_eq!(
        edges.iter().filter(|e| e["callee"] == json!(Name::from_string("identity"))).count(),
        2
    );
    assert!(!runtime["emission"]["fixed_runtime_imports"].as_array().unwrap().is_empty());
}

#[test]
fn diagnostic_serialization_preserves_real_bytes_and_propagates_nonwire_claim_refusal() {
    use clean_compiler::emit_trust_ir::{TrustIrError, deserialize_module_bytes};
    use trust_ir::{ModuleCompleteness, UnloweredRow};

    let dir = tempfile::tempdir().unwrap();
    let request = request(dir.path(), SOURCE, "twice");
    build(&request).expect("real checked source reaches diagnostic runtime emission");
    let bytes = std::fs::read(&request.build.output).unwrap();
    assert_eq!(&bytes[..8], b"tMBC\x01\0\0\0");
    let original = deserialize_module_bytes(&bytes[8..]).expect("canonical emitted module");
    assert!(original.completeness.is_none(), "no implicit completeness claim");
    assert_eq!(serialize_diagnostic_module(&original).unwrap(), bytes);

    // Mutate the actual emitted module at the production serialization seam.
    // No mock serializer or fabricated successful source observation is used.
    for claim in [
        ModuleCompleteness::Complete,
        ModuleCompleteness::Partial(vec![UnloweredRow {
            symbol: "not_lowered".into(),
            display_path: None,
            reason: "unlowered fixture row".into(),
        }]),
        ModuleCompleteness::Partial(vec![]),
    ] {
        let mut module = original.clone();
        module.completeness = Some(claim);
        let before = module.clone();
        let upstream = serialize_tmbc(&module).expect_err("claim has no binary carrier");
        assert!(
            matches!(&upstream, TrustIrError::NoWireIdentity(reason)
                if reason.to_string().contains("Module.completeness")),
            "{upstream}"
        );
        assert_eq!(
            serialize_diagnostic_module(&module).unwrap_err(),
            format!("diagnostic runtime Trust-IR serialization refused: {upstream}")
        );
        assert_eq!(module, before, "refusal must not erase the input claim");
    }
    assert_eq!(std::fs::read(&request.build.output).unwrap(), bytes);
}

#[test]
fn actual_local_import_graph_reaches_runtime_without_changing_source_acceptance() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(
        dir.path().join("Helper.lean"),
        "inductive Data where\n  | make : Data\ndef identity (x : Data) : Data := x\n",
    )
    .unwrap();
    let request =
        request(dir.path(), "import Helper\ndef root (x : Data) : Data := identity x\n", "root");
    let plain = crate::lean_cli::check_batch(std::slice::from_ref(&request.build.input), true);
    let runtime =
        crate::lean_cli::check_batch_for_runtime(std::slice::from_ref(&request.build.input));
    let p = plain.accepted_context().unwrap();
    let r = runtime.accepted_context().unwrap();
    assert_eq!(p.sources(), r.sources());
    assert_eq!(p.owned_declarations(), r.owned_declarations());
    assert_eq!(p.source_closure_sha256(), r.source_closure_sha256());
    assert!(p.runtime_baseline_environment().is_none());
    assert!(r.runtime_baseline_environment().is_some());
    build(&request).unwrap();
    assert_eq!(report(&request)["source_graph"]["sources"].as_array().unwrap().len(), 2);
    assert_eq!(
        report(&request)["external_olean_observation"]["sources"].as_array().unwrap().len(),
        2
    );
}

#[test]
fn runtime_capture_retains_the_final_same_file_alias_context() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::create_dir(dir.path().join("Sub")).unwrap();
    let leaf = dir.path().join("Sub/Leaf.lean");
    std::fs::write(
        &leaf,
        "inductive Data where\n  | make : Data\ndef identity (x : Data) : Data := x\n",
    )
    .unwrap();
    let request =
        request(dir.path(), "import Sub.Leaf\ndef root (x : Data) : Data := identity x\n", "root");
    // Prelisting Leaf gives it its stem key. The elaborator-driven retry must
    // retain Sub.Leaf as an alias of that exact snapshot, without a second row.
    let paths = vec![request.build.input.clone(), leaf];
    let ordinary = crate::lean_cli::check_batch(&paths, true);
    let runtime = crate::lean_cli::check_batch_for_runtime(&paths);
    let original = ordinary.accepted_context().expect("ordinary final alias context");
    let observed = runtime.accepted_context().expect("runtime final alias context");
    assert_eq!(observed.sources(), original.sources());
    assert_eq!(observed.sources().len(), 2);
    assert_eq!(observed.aliases(), original.aliases());
    assert_eq!(observed.aliases().len(), 1);
    assert_eq!(observed.aliases()[0].module, "Sub.Leaf");
    assert_eq!(observed.aliases()[0].source_index, 1);
    assert_eq!(observed.source_closure_sha256(), original.source_closure_sha256());
    assert_eq!(observed.owned_declarations(), original.owned_declarations());
    assert!(original.runtime_baseline_environment().is_none());
    assert!(observed.runtime_baseline_environment().is_some());
    let mut captured = crate::lean_cli::census::capture_external(&runtime, &[], &[]).unwrap();
    assert_eq!(captured.observation.sources.len(), 2);
    assert!(captured.observation.modules.is_empty());
    let import = &captured.observation.sources[0]["imports"][0];
    assert_eq!(import["supplied_source_resolution"], "source-satisfied-typed-binding");
    assert_eq!(import["source_binding"]["source_index"], 1);
    assert_eq!(
        import["source_binding"]["source_sha256"],
        captured.observation.sources[1]["checked_snapshot_sha256"]
    );
    let mut report = json!({});
    let artifact = produce(&request, &runtime, &mut captured, &mut report).unwrap();
    assert!(artifact.starts_with(b"tMBC"));
    assert_eq!(report["context"]["source"]["delta_complete"], true);
    let owned: std::collections::BTreeSet<Name> =
        serde_json::from_value(report["context"]["source"]["added"].clone()).unwrap();
    assert_eq!(&owned, observed.owned_declarations());
}

#[test]
fn source_rejection_and_external_import_remain_refused_with_observations() {
    for source in
        ["theorem bad : False := True.intro", "import External\ndef root (x : UInt8) : UInt8 := x"]
    {
        let dir = tempfile::tempdir().unwrap();
        let mut request = request(dir.path(), source, "root");
        std::fs::write(dir.path().join("External.olean"), b"not an admitted import").unwrap();
        request.build.olean_paths.push(dir.path().into());
        assert!(build(&request).is_err());
        assert!(!request.build.output.exists());
        let report = report(&request);
        assert_eq!(report["diagnostic_runtime"]["status"], "refused-no-artifact");
        assert_eq!(report["source_graph"]["source_closure_accepted"], false);
        assert!(!report["kernel_roster"].is_null());
    }
}

#[test]
fn captured_olean_cannot_replace_the_checked_standin_import() {
    let dir = tempfile::tempdir().unwrap();
    let mut request = request(dir.path(), &format!("import Lean\n{SOURCE}"), "twice");
    let bytes = clean_olean::OleanExporter::export_minimal(&[], &[], &[], &"a".repeat(40)).unwrap();
    std::fs::write(dir.path().join("Lean.olean"), bytes).unwrap();
    request.build.olean_paths.push(dir.path().into());

    let checked =
        crate::lean_cli::check_batch_for_runtime(std::slice::from_ref(&request.build.input));
    assert!(checked.accepted_context().is_some(), "stand-in was kernel-accepted");
    assert!(checked.verdicts().iter().any(|verdict| verdict.standin_imports() == ["Lean"]));
    let captured = crate::lean_cli::census::capture_external(
        &checked,
        &request.build.olean_paths,
        &[request.build.census_output.as_ref().unwrap(), &request.build.output],
    )
    .unwrap();
    assert!(captured.observation.issues.is_empty(), "{:?}", captured.observation.issues);
    assert_eq!(captured.observation.modules[0]["status"], "one-observed-candidate");
    assert_eq!(captured.candidates[0].parts[0].observation["status"], "captured");

    let error = build(&request).unwrap_err();
    assert!(error.contains("stand-in") && error.contains("Lean"), "{error}");
    assert!(!request.build.output.exists());
    let observed = report(&request);
    assert_eq!(observed["source_graph"]["source_closure_accepted"], true);
    assert_eq!(
        observed["external_olean_observation"]["modules"][0]["status"],
        "one-observed-candidate"
    );
    assert_eq!(observed["diagnostic_runtime"]["status"], "refused-no-artifact");
    assert!(observed["diagnostic_runtime"]["candidate_artifact"].is_null());
}

#[test]
fn partial_missing_body_and_unowned_entry_are_retained_refusals() {
    // The original Data fixture has no Inhabited instance: preserve that
    // earlier elaboration refusal, rather than treating it as a captured body.
    let dir = tempfile::tempdir().unwrap();
    let rejected = request(
        dir.path(),
        "inductive Data where\n  | make : Data\npartial def loop (x : Data) : Data := loop x\n",
        "loop",
    );
    assert!(build(&rejected).is_err());
    let observed = report(&rejected);
    assert_eq!(observed["source_graph"]["source_closure_accepted"], false);
    assert!(observed.to_string().contains("Inhabited"), "{observed}");
    assert!(!rejected.build.output.exists());
    for (source, entry) in
        [("partial def loop (n : Nat) : Nat := loop n\n", "loop"), (SOURCE, "missing")]
    {
        let dir = tempfile::tempdir().unwrap();
        let request = request(dir.path(), source, entry);
        assert!(build(&request).is_err());
        assert!(!request.build.output.exists());
        let report = report(&request);
        assert_eq!(report["diagnostic_runtime"]["status"], "refused-no-artifact");
        if entry == "loop" {
            // Elaboration retains the exact bodyless header, but the existing
            // strict source policy rejects its axiom before runtime capture.
            // Do not invent a successful runtime row from this kernel census.
            assert_eq!(report["source_graph"]["source_closure_accepted"], false);
            assert_eq!(
                report["diagnostic_runtime"]["context_status"],
                "unavailable-source-closure-not-accepted"
            );
            assert!(report["diagnostic_runtime"]["context"].is_null());
            assert!(
                report["check_report"]
                    .to_string()
                    .contains("is an axiom; strict islands require checked proof terms")
            );
            let rows = report["kernel_roster"]["declarations"].as_array().unwrap();
            let row =
                rows.iter().find(|r| r["identity"] == json!(Name::from_string("loop"))).unwrap();
            assert_eq!(row["constant_kind"], "Axiom");
            assert_eq!(row["has_value"], false);
        }
    }
}

#[test]
fn diagnostic_outputs_are_create_only_and_cannot_alias_source_or_each_other() {
    for mode in 0..4 {
        let dir = tempfile::tempdir().unwrap();
        let mut request = request(dir.path(), SOURCE, "twice");
        match mode {
            0 => std::fs::write(&request.build.output, b"preserved").unwrap(),
            1 => {
                std::fs::write(request.build.census_output.as_ref().unwrap(), b"preserved").unwrap()
            }
            2 => request.build.output = request.build.input.clone(),
            _ => request.build.census_output = Some(dir.path().join("./new.tmbc")),
        }
        assert!(build(&request).is_err());
        assert_eq!(std::fs::read(&request.build.input).unwrap(), SOURCE.as_bytes());
        if mode == 0 {
            assert_eq!(std::fs::read(&request.build.output).unwrap(), b"preserved");
        }
        if mode == 1 {
            assert_eq!(
                std::fs::read(request.build.census_output.as_ref().unwrap()).unwrap(),
                b"preserved"
            );
        }
    }
}

#[test]
fn source_drift_after_census_write_refuses_artifact_publication() {
    let dir = tempfile::tempdir().unwrap();
    let request = request(dir.path(), SOURCE, "twice");
    let source = request.build.input.clone();
    let error = build_with_census_writer(&request, |path, receipt| {
        crate::lean_cli::write_census(path, receipt)?;
        std::fs::write(&source, "def twice : Nat := 0\n").map_err(|e| e.to_string())
    })
    .unwrap_err();
    assert!(error.contains("diagnostic publication refused after census write"), "{error}");
    assert!(error.contains("checked source path/bytes changed"), "{error}");
    assert!(!request.build.output.exists());
    let observed = report(&request);
    assert_eq!(
        observed["diagnostic_runtime"]["status"],
        "diagnostic-artifact-candidate-not-yet-published"
    );
    assert!(!observed["diagnostic_runtime"]["candidate_artifact"].is_null());
}

#[test]
fn exact_logical_and_raw_import_mirrors_refuse_instead_of_selecting_priority() {
    let dir = tempfile::tempdir().unwrap();
    let request = request(dir.path(), SOURCE, "twice");
    let checked =
        crate::lean_cli::check_batch_for_runtime(std::slice::from_ref(&request.build.input));
    let accepted = checked.accepted_context().unwrap();
    // Export the exact actual checked declaration, not a hand-created
    // Name/body pair. Exporting the entire inherited Environment hits an
    // independent UnsupportedBigNat limitation. This explicitly selected
    // one-row API overlap fixture does not claim a complete external closure;
    // the context still retains the complete checked Environment population.
    let payload = clean_olean::payload::CleanPayload {
        constants: vec![accepted.environment().get_const(&request.entry).unwrap().clone()],
        ..Default::default()
    };
    let bytes = clean_olean::OleanExporter::export_with_payload(
        &[],
        &["twice"],
        &[],
        &"a".repeat(40),
        &payload,
    )
    .unwrap();
    let context = RuntimeContext::capture_with_environment(
        vec![RuntimeModuleInput {
            base: RuntimeOleanInput {
                label: "captured-checked-export.olean".into(),
                bytes: bytes.into(),
            },
            server: None,
            private: None,
            selected: RuntimeOleanPart::Base,
        }],
        accepted.runtime_baseline_environment().unwrap(),
        accepted.environment(),
        accepted
            .sources()
            .iter()
            .map(|s| RuntimeSourceRecord {
                module: s.module.clone(),
                path: s.path.clone(),
                source: s.source.clone(),
            })
            .collect(),
    );
    assert!(context.capture_errors().is_empty(), "{:?}", context.capture_errors());
    assert!(
        matches!(context.declaration(&request.entry),Err(clean_compiler::runtime_lcnf::RuntimeLowerError::Ambiguous(name)) if name==request.entry)
    );
    assert!(
        context
            .lower_trust_ir_diagnostic(
                &request.entry,
                RuntimeLimits::default(),
                RuntimeLowering::ExternCalls
            )
            .is_err()
    );
    assert_eq!(context.captures()[0].parts[0].rows.len(), 1);
    assert!(!context.environment_capture().unwrap().after.is_empty());
}

#[test]
fn lowering_and_source_drift_refusals_are_both_retained() {
    let dir = tempfile::tempdir().unwrap();
    let request = request(dir.path(), SOURCE, "missing");
    let before = crate::lean_cli::census::tool_identity().unwrap();
    let checked =
        crate::lean_cli::check_batch_for_runtime(std::slice::from_ref(&request.build.input));
    assert!(checked.accepted_context().is_some(), "source itself is accepted");
    let mut captured = crate::lean_cli::census::capture_external(&checked, &[], &[]).unwrap();
    let mut observed = json!({});
    let result = produce(&request, &checked, &mut captured, &mut observed);
    let lowering = result.as_ref().unwrap_err().clone();
    assert!(lowering.contains("entry is not an exact owned local source declaration"));

    // The independent postflight observes actual drift from the checked bytes;
    // it must add its refusal without replacing the original lowering refusal.
    std::fs::write(&request.build.input, "def changed : Nat := 0\n").unwrap();
    let (postflight, _) = postflight_errors(&checked, &captured, &before);
    assert!(postflight.iter().any(|error| error.contains("checked source path/bytes changed")));
    let combined = with_postflight_refusals(result, &postflight).unwrap_err();
    assert!(combined.contains(&lowering), "original lowering refusal lost: {combined}");
    for error in &postflight {
        assert!(combined.contains(error), "postflight refusal lost: {combined}");
    }
    assert!(!request.build.output.exists());

    assert_eq!(with_postflight_refusals(Err(lowering.clone()), &[]).unwrap_err(), lowering);
    assert_eq!(with_postflight_refusals(Ok(vec![1, 2, 3]), &[]).unwrap(), [1, 2, 3]);
    let rejected_success = with_postflight_refusals(Ok(vec![1, 2, 3]), &postflight).unwrap_err();
    assert_eq!(rejected_success, postflight.join("; "));
}
