use clean_kernel::env::{ConstantInfo, ConstantKind, Environment, Reducibility, TrustedEnvExt};
use clean_kernel::{Expr, Level, Name};
use clean_olean::OleanExporter;

use super::*;

#[test]
fn same_read_capture_preserves_old_report_and_changed_bytes_are_not_substituted() {
    let fixture = Fixture::new();
    let path = fixture.module("Leaf", &[], &[Name::anon().str("leaf")]);
    let sources = [fixture.source("import Leaf")];
    let old = observe_olean_closure(
        &sources,
        std::slice::from_ref(&fixture.0),
        OleanCensusLimits::default(),
    );
    let capture = capture_olean_closure(
        &sources,
        std::slice::from_ref(&fixture.0),
        OleanCensusLimits::default(),
    );
    assert_eq!(
        serde_json::to_value(old).unwrap(),
        serde_json::to_value(&capture.observation).unwrap()
    );
    assert_eq!(capture.candidates.len(), 1);
    assert!(capture.recheck_paths().is_empty());
    let bytes = std::fs::read(&path).unwrap();
    assert_eq!(capture.candidates[0].parts[0].bytes.as_ref().unwrap(), &bytes);
    std::fs::write(&path, b"replacement").unwrap();
    assert_eq!(capture.candidates[0].parts[0].bytes.as_ref().unwrap(), &bytes);
    assert_eq!(capture.recheck_paths().len(), 1);
    std::fs::write(fixture.0.join("Leaf.olean.server"), b"new companion").unwrap();
    assert_eq!(capture.recheck_paths().len(), 2);
}

#[test]
fn captured_candidates_keep_missing_malformed_and_shadowed_populations() {
    let first = Fixture::new();
    let second = Fixture::new();
    first.module("Leaf", &[], &[Name::anon().str("leaf")]);
    std::fs::write(second.0.join("Leaf.olean"), b"malformed").unwrap();
    // One module per `import`, as in Lean 4.8.0 (Clean 5018d3076). These
    // fixtures used to spell two imports on one line, `import Leaf Missing`,
    // which Lean rejects after `Leaf` ("unexpected identifier; expected
    // command") and which Clean's parser now reads the same way.
    let capture = capture_olean_closure(
        &[first.source("import Leaf\nimport Missing")],
        &[first.0.clone(), second.0.clone()],
        OleanCensusLimits::default(),
    );
    assert_eq!(capture.candidates.len(), 4);
    assert_eq!(capture.candidates.iter().filter(|c| c.parts[0].bytes.is_some()).count(), 2);
    assert!(capture.observation.modules.iter().any(|m| m["status"] == "ambiguous-candidates"));
    assert!(capture.observation.modules.iter().any(|m| m["status"] == "missing"));
    assert!(capture.recheck_paths().is_empty());
    // The one-line spelling imports `Leaf` only, and the census says its
    // parse is incomplete instead of crediting a second module.
    let one_line = capture_olean_closure(
        &[first.source("import Leaf Missing")],
        &[first.0.clone(), second.0.clone()],
        OleanCensusLimits::default(),
    );
    assert_eq!(one_line.candidates.len(), 2);
    assert!(one_line.observation.modules.iter().all(|m| m["status"] != "missing"));
    assert!(
        one_line.observation.issues.iter().any(|i| i.contains("incomplete import parsing")),
        "{:?}",
        one_line.observation.issues
    );
}

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static SERIAL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "trust-olean-observer-{}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos(),
            SERIAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn source(&self, text: &str) -> OleanCensusSource {
        let path = self.0.join("Main.lean");
        std::fs::write(&path, text).unwrap();
        OleanCensusSource { module: "Main".into(), path, source: Ok(text.into()) }
    }
    fn module(&self, name: &str, imports: &[(&str, bool)], names: &[Name]) -> PathBuf {
        let mut env = Environment::default();
        assert!(
            env.extend_constants_structural(names.iter().cloned().map(|name| {
                ConstantInfo::new_with_reducibility(
                    name,
                    vec![],
                    Expr::sort(Level::zero()),
                    None,
                    Reducibility::Opaque,
                    ConstantKind::Axiom,
                )
            }))
            .is_empty()
        );
        let mut bytes =
            OleanExporter::export_with_env(&env, imports, &[], &"a".repeat(40)).unwrap();
        // The current exporter stringifies Names. Install explicit raw typed
        // objects so this test does not confuse its lossy display encoding with
        // a faithful fixture oracle. Keep all original constant row positions.
        let header = OleanHeader::parse(&bytes).unwrap();
        let (array, constants) = {
            let r = clean_olean::CompactedRegion::new(&bytes, header.base_addr);
            let root =
                r.ptr_to_offset(r.read_u64_at(clean_olean::header::HEADER_SIZE).unwrap()).unwrap();
            (
                r.ptr_to_offset(r.read_u64_at(root + 16).unwrap()).unwrap(),
                r.ptr_to_offset(r.read_u64_at(root + 24).unwrap()).unwrap(),
            )
        };
        for (index, name) in names.iter().enumerate() {
            let cv = {
                let r = clean_olean::CompactedRegion::new(&bytes, header.base_addr);
                let ci =
                    r.ptr_to_offset(r.read_u64_at(constants + 24 + index * 8).unwrap()).unwrap();
                let val = r.ptr_to_offset(r.read_u64_at(ci + 8).unwrap()).unwrap();
                r.ptr_to_offset(r.read_u64_at(val + 8).unwrap()).unwrap()
            };
            let pointer = raw_typed_name(&mut bytes, header.base_addr, name);
            bytes[cv + 8..cv + 16].copy_from_slice(&pointer.to_le_bytes());
            bytes[array + 24 + index * 8..array + 32 + index * 8]
                .copy_from_slice(&pointer.to_le_bytes());
        }
        let path = self.0.join(format!("{name}.olean"));
        std::fs::write(&path, bytes).unwrap();
        path
    }
    fn observe(&self, text: &str) -> OleanClosureObservation {
        observe_olean_closure(
            &[self.source(text)],
            std::slice::from_ref(&self.0),
            OleanCensusLimits::default(),
        )
    }
}

fn raw_typed_name(bytes: &mut Vec<u8>, base: u64, name: &Name) -> u64 {
    use clean_kernel::name::NameInner;
    let mut parts = Vec::new();
    let mut cursor = name;
    loop {
        match cursor.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, value) => {
                parts.push(Segment::Str(value.to_string()));
                cursor = parent;
            }
            NameInner::Num(parent, value) => {
                parts.push(Segment::Num(*value));
                cursor = parent;
            }
        }
    }
    let mut parent = 1u64;
    for part in parts.into_iter().rev() {
        while bytes.len() % 8 != 0 {
            bytes.push(0);
        }
        let (tag, value) = match part {
            Segment::Num(value) => (2, value),
            Segment::Str(value) => {
                let pointer = base + bytes.len() as u64;
                bytes.extend_from_slice(&[0, 0, 0, 0, 0, 0, 0, clean_olean::region::tags::STRING]);
                bytes.extend_from_slice(&(value.len() as u64 + 1).to_le_bytes());
                bytes.extend_from_slice(&(value.len() as u64 + 1).to_le_bytes());
                bytes.extend_from_slice(&(value.chars().count() as u64).to_le_bytes());
                bytes.extend_from_slice(value.as_bytes());
                bytes.push(0);
                while bytes.len() % 8 != 0 {
                    bytes.push(0);
                }
                (1, pointer)
            }
        };
        let pointer = base + bytes.len() as u64;
        bytes.extend_from_slice(&[0, 0, 0, 0, 0, 0, 2, tag]);
        bytes.extend_from_slice(&parent.to_le_bytes());
        bytes.extend_from_slice(&value.to_le_bytes());
        parent = pointer;
    }
    parent
}

#[test]
fn olean_census_keeps_typed_quoted_numeric_unicode_and_codegen_names() {
    let f = Fixture::new();
    let names = [
        Name::anon().str("A.B"),
        Name::anon().str("A").str("B"),
        Name::anon().str("A").num(1),
        Name::anon().str("A").str("1"),
        Name::anon().str("fidèle"),
        Name::anon().str("helper").str("_cstage2"),
    ];
    f.module("Lib", &[], &names);
    let out = f.observe("import Lib\ndef untouched : Nat := 0");
    assert!(out.issues.is_empty(), "{:?}", out.issues);
    let rows = out.modules[0]["candidates"][0]["parts"][0]["raw_name_witness"]["constants"]
        .as_array()
        .unwrap();
    assert_eq!(rows.len(), names.len());
    let distinct = rows.iter().map(|r| r["name"].to_string()).collect::<BTreeSet<_>>();
    assert_eq!(distinct.len(), names.len());
    assert!(rows.iter().any(|r| r["name"] == json!(ModuleName(vec![Segment::Str("A.B".into())]))));
    assert!(
        rows.iter().any(
            |r| r["name"] == json!(ModuleName(vec![Segment::Str("A".into()), Segment::Num(1)]))
        )
    );
    assert_eq!(out.denominator_status, "denominator_unverified");
    assert_eq!(out.runtime_body_universe, "unmeasured");
}

#[test]
fn olean_census_ast_imports_include_satisfied_sources_comments_and_quoted_paths() {
    let f = Fixture::new();
    f.module("Quoted.Mod", &[], &[]);
    let main = f.source("/- import Fake -/\nimport «Quoted.Mod»\nimport Helper\n");
    let helper_path = f.0.join("Helper.lean");
    std::fs::write(&helper_path, "def x : Nat := 1").unwrap();
    let helper = OleanCensusSource {
        module: "Helper".into(),
        path: helper_path,
        source: Ok("def x : Nat := 1".into()),
    };
    let out = observe_olean_closure(
        &[main, helper],
        std::slice::from_ref(&f.0),
        OleanCensusLimits::default(),
    );
    assert_eq!(out.sources[0]["imports"].as_array().unwrap().len(), 2);
    assert_eq!(out.modules.len(), 1);
    assert_eq!(out.modules[0]["name"], json!(ModuleName(vec![Segment::Str("Quoted.Mod".into())])));
    assert!(out.issues.is_empty(), "{:?}", out.issues);
}

#[test]
fn olean_census_cycle_missing_runtime_import_and_duplicate_part_rows_are_explicit() {
    let f = Fixture::new();
    let a = f.module("A", &[("B", false), ("Missing", true)], &[Name::anon().str("same")]);
    f.module("B", &[("A", false)], &[]);
    std::fs::copy(&a, f.0.join("A.olean.server")).unwrap();
    let out = f.observe("import A");
    assert!(!out.cycles.is_empty());
    assert!(out.modules.iter().any(|m| m["status"] == "missing"));
    assert!(
        out.duplicate_declarations.iter().any(|r| r["occurrences"].as_array().unwrap().len() == 2)
    );
    let imports = &out.modules[0]["candidates"][0]["parts"][0]["raw_name_witness"]["imports"];
    assert!(imports.as_array().unwrap().iter().any(|i| i["runtime_only"] == true));
}

#[test]
fn olean_census_review_dotted_source_labels_do_not_suppress_typed_candidates() {
    let f = Fixture::new();
    f.module("A.B", &[], &[Name::anon().str("quoted")]);
    std::fs::create_dir(f.0.join("A")).unwrap();
    f.module("A/B", &[], &[Name::anon().str("hierarchical")]);
    let main = f.source("import «A.B»\nimport A.B\n");
    let path = f.0.join("A/B.lean");
    std::fs::write(&path, "def localValue : Nat := 1\n").unwrap();
    let local = OleanCensusSource {
        module: "A.B".into(),
        path,
        source: Ok("def localValue : Nat := 1\n".into()),
    };
    let out = observe_olean_closure(
        &[main, local],
        std::slice::from_ref(&f.0),
        OleanCensusLimits::default(),
    );
    assert_eq!(out.modules.len(), 2, "neither typed candidate may be suppressed");
    let names = out.modules.iter().map(|m| m["name"].to_string()).collect::<BTreeSet<_>>();
    assert_eq!(names.len(), 2);
    for row in out.sources[0]["imports"].as_array().unwrap() {
        assert_eq!(row["supplied_source_candidates"], json!([1]));
        assert_eq!(row["supplied_source_resolution"], "ambiguous-supplied-label");
    }
    assert!(out.modules.iter().all(|m| m["status"] == "one-observed-candidate"));
    assert!(out.issues.iter().any(|s| s.contains("ambiguous supplied source labels")));
    assert_eq!(out.denominator_status, "denominator_unverified");
}

#[test]
fn olean_census_review_duplicate_plain_source_labels_remain_unresolved() {
    let f = Fixture::new();
    f.module("Helper", &[], &[Name::anon().str("external")]);
    let mut sources = vec![f.source("import Helper\n")];
    for basename in ["one", "two"] {
        let path = f.0.join(format!("{basename}.lean"));
        std::fs::write(&path, "").unwrap();
        sources.push(OleanCensusSource { module: "Helper".into(), path, source: Ok("".into()) });
    }
    let out =
        observe_olean_closure(&sources, std::slice::from_ref(&f.0), OleanCensusLimits::default());
    assert_eq!(out.modules.len(), 1, "ambiguous local candidates cannot hide external rows");
    assert_eq!(out.sources[0]["imports"][0]["supplied_source_candidates"], json!([1, 2]));
    assert_eq!(
        out.sources[0]["imports"][0]["supplied_source_resolution"],
        "ambiguous-supplied-label"
    );
    assert!(!out.issues.is_empty());
}

#[test]
fn olean_census_typed_source_bindings_keep_quoted_twins_and_one_snapshot_per_source() {
    let f = Fixture::new();
    f.module("Sub.Leaf", &[], &[Name::anon().str("quoted_external")]);
    let main = f.source("import Sub.Leaf\nimport Other.Leaf\nimport «Sub.Leaf»\n");
    let local_path = f.0.join("Leaf.lean");
    let local_text = "def localValue : Nat := 1\n";
    std::fs::write(&local_path, local_text).unwrap();
    let sources = [
        main,
        OleanCensusSource {
            module: "Leaf".into(),
            path: local_path.clone(),
            source: Ok(local_text.into()),
        },
    ];
    let bindings: Vec<_> = [vec!["Leaf"], vec!["Sub", "Leaf"], vec!["Other", "Leaf"]]
        .into_iter()
        .map(|parts| OleanCensusSourceBinding {
            module: ModuleName(parts.into_iter().map(|part| Segment::Str(part.into())).collect()),
            source_index: 1,
            source_sha256: hash(local_text.as_bytes()),
        })
        .collect();
    let captured = capture_olean_closure_with_source_bindings(
        &sources,
        &bindings,
        std::slice::from_ref(&f.0),
        OleanCensusLimits::default(),
    );
    assert_eq!(captured.observation.sources.len(), 2);
    let imports = captured.observation.sources[0]["imports"].as_array().unwrap();
    assert_eq!(imports.len(), 3);
    for import in &imports[..2] {
        assert_eq!(import["supplied_source_resolution"], "source-satisfied-typed-binding");
        assert_eq!(import["source_binding"]["source_index"], 1);
        assert_eq!(import["source_binding"]["source_sha256"], hash(local_text.as_bytes()));
    }
    assert_eq!(imports[2]["supplied_source_resolution"], "external-no-exact-source-binding");
    assert!(imports[2]["source_binding"].is_null());
    assert_eq!(captured.observation.modules.len(), 1);
    assert_eq!(captured.candidates.len(), 1);
    assert_eq!(captured.candidates[0].module, ModuleName(vec![Segment::Str("Sub.Leaf".into())]));
    assert!(captured.observation.observed_paths().contains(&local_path));
    assert!(captured.observation.observed_paths().contains(&f.0.join("Sub.Leaf.olean")));
    assert!(captured.observation.issues.is_empty(), "{:?}", captured.observation.issues);
}

#[test]
fn olean_census_typed_source_binding_never_suppresses_raw_external_dependencies() {
    let f = Fixture::new();
    std::fs::create_dir(f.0.join("Sub")).unwrap();
    f.module("Sub/Leaf", &[], &[Name::anon().str("raw_external")]);
    f.module("External", &[("Sub.Leaf", false)], &[]);
    let local_path = f.0.join("Leaf.lean");
    std::fs::write(&local_path, "").unwrap();
    let sources = [
        f.source("import Sub.Leaf\nimport External\n"),
        OleanCensusSource { module: "Leaf".into(), path: local_path, source: Ok("".into()) },
    ];
    let name = ModuleName(vec![Segment::Str("Sub".into()), Segment::Str("Leaf".into())]);
    let captured = capture_olean_closure_with_source_bindings(
        &sources,
        &[OleanCensusSourceBinding {
            module: name.clone(),
            source_index: 1,
            source_sha256: hash(b""),
        }],
        std::slice::from_ref(&f.0),
        OleanCensusLimits::default(),
    );
    assert_eq!(
        captured.observation.sources[0]["imports"][0]["supplied_source_resolution"],
        "source-satisfied-typed-binding"
    );
    assert_eq!(captured.observation.modules.len(), 2);
    assert!(captured.candidates.iter().any(|candidate| candidate.module == name));
    assert!(captured.candidates.iter().all(|candidate| candidate.parts[0].bytes.is_some()));
}

#[test]
fn olean_census_invalid_typed_source_bindings_refuse_without_label_fallback() {
    let f = Fixture::new();
    f.module("Helper", &[], &[Name::anon().str("external")]);
    let local_path = f.0.join("Helper.lean");
    std::fs::write(&local_path, "").unwrap();
    let mut sources = [
        f.source("import Helper\n"),
        OleanCensusSource { module: "Helper".into(), path: local_path, source: Ok("".into()) },
    ];
    let binding = OleanCensusSourceBinding {
        module: ModuleName(vec![Segment::Str("Helper".into())]),
        source_index: 1,
        source_sha256: hash(b""),
    };
    let cases = [
        vec![OleanCensusSourceBinding { source_index: 2, ..binding.clone() }],
        vec![OleanCensusSourceBinding { source_sha256: "0".repeat(64), ..binding.clone() }],
        vec![binding.clone(), binding.clone()],
        vec![
            binding.clone(),
            OleanCensusSourceBinding {
                source_index: 0,
                source_sha256: hash(b"import Helper\n"),
                ..binding.clone()
            },
        ],
        vec![OleanCensusSourceBinding { module: ModuleName(vec![]), ..binding.clone() }],
        vec![OleanCensusSourceBinding {
            module: ModuleName(vec![Segment::Str("".into())]),
            ..binding.clone()
        }],
    ];
    for bindings in cases {
        let captured = capture_olean_closure_with_source_bindings(
            &sources,
            &bindings,
            std::slice::from_ref(&f.0),
            OleanCensusLimits::default(),
        );
        assert!(captured.observation.issues.iter().any(|issue| issue.contains("source binding")));
        assert_eq!(
            captured.observation.sources[0]["imports"][0]["supplied_source_resolution"],
            "invalid-source-bindings"
        );
        assert_eq!(
            captured.candidates.len(),
            1,
            "invalid bindings cannot hide the external candidate"
        );
        assert!(captured.candidates[0].parts[0].bytes.is_some());
    }
    sources[1].source = Err("unreadable retained snapshot".into());
    let captured = capture_olean_closure_with_source_bindings(
        &sources,
        &[binding],
        std::slice::from_ref(&f.0),
        OleanCensusLimits::default(),
    );
    assert!(
        captured.observation.issues.iter().any(|issue| issue.contains("snapshot is unreadable"))
    );
    assert_eq!(captured.candidates.len(), 1);
}

#[test]
fn olean_census_review_generic_extension_counts_never_claim_ir_body_decode() {
    use clean_olean::{ParsedExtension, ParsedExtensionEntry, ParsedExtensionEntryData};
    let f = Fixture::new();
    // A generic Name × DataValue projection is not a decoded five-field IR
    // Decl.fdecl or its FnBody, even if the parser has no undecoded-entry residue.
    let extension = ParsedExtension {
        extension_name: "Lean.IR.declMapExt".into(),
        entries: vec![ParsedExtensionEntry::Named {
            name: "passFlag._boxed".into(),
            data: ParsedExtensionEntryData::Scalar(0),
        }],
        undecoded_entries: 0,
    };
    let bytes =
        OleanExporter::export_with_env(&Environment::default(), &[], &[extension], &"a".repeat(40))
            .unwrap();
    std::fs::write(f.0.join("IR.olean"), bytes).unwrap();
    let out = f.observe("import IR\n");
    assert!(!out.issues.is_empty());
    let runtime = &out.modules[0]["candidates"][0]["parts"][0]["runtime_ir"];
    assert_eq!(runtime["rows"][0]["status"], "unmeasured");
    assert!(runtime["rows"][0]["error"].as_str().is_some());
    let extensions = &out.modules[0]["candidates"][0]["parts"][0]["extensions"];
    assert_eq!(extensions["entries"][0]["decoded_entries"], 1);
    assert_eq!(extensions["entries"][0]["undecoded_entries"], 0);
    assert_eq!(extensions["entry_count_semantics"], "generic-parser-projection-counts-only");
    assert_eq!(extensions["ir_computational_body_semantics"], "unmeasured");
    assert_eq!(out.runtime_body_universe, "unmeasured");
}

fn ir_object(bytes: &mut Vec<u8>, base: u64, tag: u8, fields: &[u64], scalar: &[u8]) -> u64 {
    while bytes.len() % 8 != 0 {
        bytes.push(0);
    }
    let pointer = base + bytes.len() as u64;
    bytes.extend_from_slice(&[0, 0, 0, 0, 0, 0, fields.len() as u8, tag]);
    for field in fields {
        bytes.extend_from_slice(&field.to_le_bytes());
    }
    bytes.extend_from_slice(scalar);
    pointer
}

fn ir_array(bytes: &mut Vec<u8>, base: u64, elements: &[u64]) -> u64 {
    let mut fields = vec![elements.len() as u64, elements.len() as u64];
    fields.extend_from_slice(elements);
    ir_object(bytes, base, clean_olean::region::tags::ARRAY, &fields, &[])
}

/// Explicit ABI-layout fixture, separate from the real pinned-Lean controls.
/// The generic exporter supplies only the module/extension envelope.
fn runtime_ir_fixture(duplicate_parameter: bool) -> Vec<u8> {
    use clean_olean::{ParsedExtension, ParsedExtensionEntry, ParsedExtensionEntryData};
    let extension = ParsedExtension {
        extension_name: "Lean.IR.declMapExt".into(),
        entries: vec![ParsedExtensionEntry::Named {
            name: "placeholder".into(),
            data: ParsedExtensionEntryData::Scalar(0),
        }],
        undecoded_entries: 0,
    };
    let mut bytes =
        OleanExporter::export_with_env(&Environment::default(), &[], &[extension], &"a".repeat(40))
            .unwrap();
    let header = OleanHeader::parse(&bytes).unwrap();
    let entries = {
        let r = clean_olean::CompactedRegion::new(&bytes, header.base_addr);
        let root =
            r.ptr_to_offset(r.read_u64_at(clean_olean::header::HEADER_SIZE).unwrap()).unwrap();
        let ext_array = r.ptr_to_offset(r.read_u64_at(root + 40).unwrap()).unwrap();
        let ext = r.ptr_to_offset(r.read_u64_at(ext_array + 24).unwrap()).unwrap();
        r.ptr_to_offset(r.read_u64_at(ext + 16).unwrap()).unwrap()
    };
    let name = raw_typed_name(&mut bytes, header.base_addr, &Name::anon().str("IR.echo"));
    let param = ir_object(&mut bytes, header.base_addr, 0, &[1, 3], &[0]);
    let params = ir_array(
        &mut bytes,
        header.base_addr,
        &if duplicate_parameter { vec![param, param] } else { vec![param] },
    );
    let arg = ir_object(&mut bytes, header.base_addr, 0, &[1], &[]);
    let body = ir_object(&mut bytes, header.base_addr, 10, &[arg], &[]);
    let decl = ir_object(&mut bytes, header.base_addr, 0, &[name, params, 3, body, 1], &[]);
    bytes[entries + 24..entries + 32].copy_from_slice(&decl.to_le_bytes());
    bytes
}

#[test]
fn olean_census_runtime_ir_companion_keeps_quoted_path_and_output_protection() {
    let f = Fixture::new();
    f.module("Quoted.Mod", &[], &[]);
    let path = f.0.join("Quoted.Mod.ir");
    std::fs::write(&path, runtime_ir_fixture(false)).unwrap();
    let out = f.observe("import «Quoted.Mod»\n");
    assert!(out.observed_paths().contains(&path));
    let part = &out.modules[0]["candidates"][0]["parts"][3];
    assert_eq!(part["part"], "ir");
    assert_eq!(part["capture"]["status"], "captured");
    assert_eq!(
        part["runtime_ir"]["rows"][0]["declaration"]["name"],
        json!([{"kind":"str","value":"IR.echo"}])
    );
    assert_eq!(part["runtime_ir"]["rows"][0]["declaration"]["body_ast"]["kind"], "ret");
    assert_eq!(
        part["runtime_ir"]["rows"][0]["identifier_bindings"]["status"],
        "identifier-bindings-resolved-only"
    );
    assert_eq!(out.runtime_body_universe, "unmeasured");
}

#[test]
fn olean_census_runtime_ir_legacy_body_is_not_a_generic_entry_count() {
    let f = Fixture::new();
    std::fs::write(f.0.join("Legacy.olean"), runtime_ir_fixture(false)).unwrap();
    let out = f.observe("import Legacy\n");
    let row = &out.modules[0]["candidates"][0]["parts"][0]["runtime_ir"]["rows"][0];
    assert_eq!(row["status"], "decoded-syntax-only");
    assert_eq!(row["declaration"]["params"][0]["ty"], "uint8");
    assert_eq!(row["declaration"]["body_present"], true);
    assert_eq!(row["declaration"]["effects_and_lowering"], "unmeasured");
    assert_eq!(out.authority, "diagnostic-only-no-import-admission");
}

#[test]
fn olean_census_runtime_ir_duplicate_bindings_remain_visible_and_unadmitted() {
    let f = Fixture::new();
    std::fs::write(f.0.join("Malformed.olean"), runtime_ir_fixture(true)).unwrap();
    let out = f.observe("import Malformed\n");
    let row = &out.modules[0]["candidates"][0]["parts"][0]["runtime_ir"]["rows"][0];
    assert_eq!(row["declaration"]["params"].as_array().unwrap().len(), 2);
    assert_eq!(row["identifier_bindings"]["status"], "unmeasured");
    assert!(!row["identifier_bindings"]["errors"].as_array().unwrap().is_empty());
    assert!(!out.issues.is_empty());
}

#[test]
fn olean_census_runtime_ir_malformed_or_orphan_part_is_not_dropped() {
    let f = Fixture::new();
    let path = f.0.join("Orphan.ir");
    std::fs::write(&path, b"not an IR module").unwrap();
    let out = f.observe("import Orphan\n");
    assert_eq!(out.modules[0]["status"], "missing");
    let part = &out.modules[0]["candidates"][0]["parts"][3];
    assert_eq!(part["capture"]["sha256"], hash(b"not an IR module"));
    assert!(out.observed_paths().contains(&path));
    assert!(!out.issues.is_empty());
}

#[test]
fn olean_census_runtime_ir_zero_budget_is_visible_not_empty_success() {
    let f = Fixture::new();
    std::fs::write(f.0.join("Limited.olean"), runtime_ir_fixture(false)).unwrap();
    let out = observe_olean_closure(
        &[f.source("import Limited\n")],
        &[f.0.clone()],
        OleanCensusLimits { ir_object_accesses: 0, ..Default::default() },
    );
    let ir = &out.modules[0]["candidates"][0]["parts"][0]["runtime_ir"];
    assert_eq!(ir["status"], "incomplete-syntax-observation");
    assert!(!ir["errors"].as_array().unwrap().is_empty());
    assert!(!out.issues.is_empty());
    assert_eq!(out.denominator_status, "denominator_unverified");
}

#[test]
fn olean_census_runtime_ir_wrong_companion_header_retains_capture() {
    let f = Fixture::new();
    f.module("Wrong", &[], &[]);
    let mut bytes = runtime_ir_fixture(false);
    // Byte8 is inside the version-one header's producer identity (bytes6..46).
    bytes[8] = b'b';
    std::fs::write(f.0.join("Wrong.ir"), &bytes).unwrap();
    let out = f.observe("import Wrong\n");
    let part = &out.modules[0]["candidates"][0]["parts"][3];
    assert_eq!(part["capture"]["sha256"], hash(&bytes));
    assert_eq!(part["dependency_resolution"]["status"], "unresolved");
    assert_eq!(part["runtime_ir"]["status"], "unmeasured");
    assert!(!out.issues.is_empty());
}

#[test]
fn olean_census_runtime_ir_unknown_module_envelope_is_explicitly_unmeasured() {
    let original = runtime_ir_fixture(false);
    let header = OleanHeader::parse(&original).unwrap();
    let region = clean_olean::CompactedRegion::new(&original, header.base_addr);
    let root = region
        .ptr_to_offset(region.read_u64_at(clean_olean::header::HEADER_SIZE).unwrap())
        .unwrap();
    for (offset, replacement) in
        [(root + 7, 8), (root + 6, original[root + 6] - 1), (root + 6, original[root + 6] + 1)]
    {
        let f = Fixture::new();
        let mut bytes = original.clone();
        bytes[offset] = replacement;
        std::fs::write(f.0.join("Envelope.olean"), &bytes).unwrap();
        let out = f.observe("import Envelope\n");
        let part = &out.modules[0]["candidates"][0]["parts"][0];
        assert_eq!(part["capture"]["sha256"], hash(&bytes));
        assert_eq!(
            part["runtime_ir"]["status"], "incomplete-syntax-observation",
            "offset {offset} replacement {replacement}"
        );
        assert!(!out.issues.is_empty());
    }
}

#[test]
fn olean_census_runtime_ir_reserved_array_tag_and_root_rc_are_not_assumed_valid() {
    let original = runtime_ir_fixture(false);
    let header = OleanHeader::parse(&original).unwrap();
    let region = clean_olean::CompactedRegion::new(&original, header.base_addr);
    let root = region
        .ptr_to_offset(region.read_u64_at(clean_olean::header::HEADER_SIZE).unwrap())
        .unwrap();
    let extensions = region.ptr_to_offset(region.read_u64_at(root + 40).unwrap()).unwrap();
    for (offset, replacement) in
        [(extensions + 7, clean_olean::region::tags::STRUCT_ARRAY), (root, 1), (root + 4, 55)]
    {
        let f = Fixture::new();
        let mut bytes = original.clone();
        bytes[offset] = replacement;
        std::fs::write(f.0.join("Envelope.olean"), &bytes).unwrap();
        let out = f.observe("import Envelope\n");
        let part = &out.modules[0]["candidates"][0]["parts"][0];
        assert_eq!(part["capture"]["sha256"], hash(&bytes));
        assert_eq!(part["runtime_ir"]["status"], "incomplete-syntax-observation");
        assert!(!out.issues.is_empty());
    }
}

#[test]
fn olean_census_absent_optional_is_not_malformed_present_and_siblings_survive() {
    let f = Fixture::new();
    f.module("A", &[("B", false)], &[]);
    f.module("B", &[], &[]);
    let first = f.observe("import A");
    assert!(first.issues.is_empty(), "{:?}", first.issues);
    assert_eq!(first.modules[0]["candidates"][0]["parts"][1]["capture"]["status"], "absent");
    std::fs::write(f.0.join("A.olean.server"), b"malformed").unwrap();
    let out = f.observe("import A");
    assert_eq!(out.modules.len(), 2);
    assert!(!out.issues.is_empty());
    assert_eq!(
        out.modules[0]["candidates"][0]["parts"][1]["capture"]["sha256"],
        hash(b"malformed")
    );
    assert_eq!(out.modules[1]["candidates"][0]["parts"][0]["parse_status"], "parsed");
}

#[test]
fn olean_census_all_shadow_candidates_and_alias_roots_are_retained() {
    let a = Fixture::new();
    let b = Fixture::new();
    a.module("Lib", &[], &[Name::anon().str("one")]);
    b.module("Lib", &[], &[Name::anon().str("two")]);
    let source = a.source("import Lib");
    let out = observe_olean_closure(
        &[source],
        &[a.0.clone(), b.0.clone(), a.0.join(".")],
        OleanCensusLimits::default(),
    );
    assert_eq!(out.modules[0]["status"], "ambiguous-candidates");
    assert_eq!(out.modules[0]["candidates"].as_array().unwrap().len(), 3);
    assert_eq!(out.duplicate_declarations.len(), 1);
}

#[cfg(unix)]
#[test]
fn olean_census_distinct_modules_cannot_share_one_olean_file() {
    let f = Fixture::new();
    let a = f.module("A", &[], &[]);
    let b = f.0.join("B.olean");
    std::os::unix::fs::symlink(&a, &b).unwrap();

    let out = f.observe("import A\nimport B");
    assert_eq!(out.modules.len(), 2);
    assert!(out.modules.iter().all(|module| module["status"] == "aliased-candidate"));
    assert!(out.issues.iter().any(|issue| issue.contains("share captured .olean file")));

    std::fs::remove_file(&b).unwrap();
    std::fs::hard_link(&a, &b).unwrap();
    let linked = f.observe("import A\nimport B");
    assert!(linked.modules.iter().all(|module| module["status"] == "aliased-candidate"));
    assert!(linked.issues.iter().any(|issue| issue.contains("share captured .olean file")));

    std::fs::remove_file(&b).unwrap();
    std::fs::copy(&a, &b).unwrap();
    let separate = f.observe("import A\nimport B");
    assert!(separate.issues.is_empty(), "{:?}", separate.issues);
    assert!(separate.modules.iter().all(|module| module["status"] == "one-observed-candidate"));

    let capture = capture_olean_closure(
        &[f.source("import A\nimport B")],
        std::slice::from_ref(&f.0),
        OleanCensusLimits::default(),
    );
    assert!(capture.recheck_paths().is_empty());
    let replacement = f.0.join("Replacement.olean");
    std::fs::copy(&a, &replacement).unwrap();
    std::fs::remove_file(&a).unwrap();
    std::fs::rename(replacement, &a).unwrap();
    assert_eq!(capture.recheck_paths().len(), 1, "same-byte inode replacement must drift");
}

#[test]
fn olean_census_second_module_on_one_import_line_is_incomplete_not_imported() {
    // Lean 4.8.0's header takes ONE module per `import` (Clean 5018d3076):
    // `import A B` imports A only and B is a command-position parse error. The
    // census must neither credit B as a root nor report the source as complete.
    let f = Fixture::new();
    f.module("A", &[], &[]);
    f.module("B", &[], &[]);
    let out = f.observe("import A B");
    assert_eq!(out.modules.len(), 1);
    assert_eq!(out.modules[0]["name"], json!(ModuleName(vec![Segment::Str("A".into())])));
    let rows = out.sources[0]["imports"].as_array().unwrap();
    assert_eq!(rows.iter().filter(|r| r["status"] == "parsed-import").count(), 1);
    assert!(out.issues.iter().any(|i| i.contains("incomplete import parsing")), "{:?}", out.issues);
}

#[test]
fn olean_census_parse_error_and_unreadable_sources_are_not_empty_complete() {
    let f = Fixture::new();
    let source = f.source("import Missing\ndef broken : :=\n");
    let missing = OleanCensusSource {
        module: "Lost".into(),
        path: f.0.join("Lost.lean"),
        source: Err("actual read failed".into()),
    };
    let out = observe_olean_closure(
        &[source, missing],
        std::slice::from_ref(&f.0),
        OleanCensusLimits::default(),
    );
    assert!(!out.issues.is_empty());
    assert!(!out.sources[0]["errors"].as_array().unwrap().is_empty());
    assert_eq!(out.sources[1]["checked_snapshot_sha256"], Value::Null);
    assert_eq!(out.sources[1]["errors"][0], "actual read failed");
}

#[test]
fn olean_census_source_drift_and_changed_part_bytes_are_visible() {
    let f = Fixture::new();
    let source = f.source("import Lib");
    let path = f.module("Lib", &[], &[]);
    let first =
        observe_olean_closure(&[source], std::slice::from_ref(&f.0), OleanCensusLimits::default());
    let mut bytes = std::fs::read(&path).unwrap();
    bytes[6] = b'b';
    std::fs::write(&path, bytes).unwrap();
    let source = OleanCensusSource {
        module: "Main".into(),
        path: f.0.join("Main.lean"),
        source: Ok("import Lib\n-- changed retained snapshot".into()),
    };
    let second =
        observe_olean_closure(&[source], std::slice::from_ref(&f.0), OleanCensusLimits::default());
    assert_ne!(
        first.modules[0]["candidates"][0]["parts"][0]["capture"]["sha256"],
        second.modules[0]["candidates"][0]["parts"][0]["capture"]["sha256"]
    );
    assert!(second.issues.iter().any(|s| s.contains("differs from captured check snapshot")));
}

#[test]
fn olean_census_bounds_retain_unvisited_modules_and_never_fake_hashes() {
    let f = Fixture::new();
    f.module("A", &[("B", false)], &[]);
    f.module("B", &[], &[]);
    let mut limits = OleanCensusLimits::default();
    limits.modules = 1;
    let out = observe_olean_closure(&[f.source("import A")], std::slice::from_ref(&f.0), limits);
    assert_eq!(out.deferred_modules, vec![ModuleName(vec![Segment::Str("B".into())])]);
    limits.part_bytes = 1;
    let bounded =
        observe_olean_closure(&[f.source("import A")], std::slice::from_ref(&f.0), limits);
    assert_eq!(bounded.modules[0]["candidates"][0]["parts"][0]["capture"]["status"], "bounded");
    assert_eq!(bounded.modules[0]["candidates"][0]["parts"][0]["capture"]["sha256"], Value::Null);
}

#[test]
fn olean_census_malformed_name_keeps_following_raw_row() {
    let f = Fixture::new();
    let path = f.module("A", &[], &[Name::anon().str("a"), Name::anon().str("b")]);
    let mut bytes = std::fs::read(path).unwrap();
    let header = OleanHeader::parse(&bytes).unwrap();
    let region = clean_olean::CompactedRegion::new(&bytes, header.base_addr);
    let root = region
        .ptr_to_offset(region.read_u64_at(clean_olean::header::HEADER_SIZE).unwrap())
        .unwrap();
    let array = region.ptr_to_offset(region.read_u64_at(root + 24).unwrap()).unwrap();
    let ci = region.ptr_to_offset(region.read_u64_at(array + 24).unwrap()).unwrap();
    let val = region.ptr_to_offset(region.read_u64_at(ci + 8).unwrap()).unwrap();
    let cv = region.ptr_to_offset(region.read_u64_at(val + 8).unwrap()).unwrap();
    bytes[cv + 8..cv + 16].copy_from_slice(&3u64.to_le_bytes());
    let witness = names::witness(&bytes, &[], 100);
    assert_eq!(witness.constants.len(), 2);
    assert!(witness.constants[0].error.is_some());
    assert!(witness.constants[1].name.is_some());
}

#[test]
fn olean_census_module_path_never_uses_display_or_traversal() {
    let root = Path::new("/explicit");
    assert_eq!(
        module_path(root, &ModuleName(vec![Segment::Str("A.B".into())])).unwrap(),
        root.join("A.B.olean")
    );
    assert_eq!(
        module_path(root, &ModuleName(vec![Segment::Str("A".into()), Segment::Str("B".into())]))
            .unwrap(),
        root.join("A/B.olean")
    );
    for name in [
        ModuleName(vec![]),
        ModuleName(vec![Segment::Str("..".into())]),
        ModuleName(vec![Segment::Str("/escape".into())]),
        ModuleName(vec![Segment::Num(1)]),
    ] {
        assert!(module_path(root, &name).is_err());
    }
}

#[test]
fn olean_census_private_requires_server_and_wrong_part_header_stays_visible() {
    let f = Fixture::new();
    let base = f.module("A", &[], &[Name::anon().str("body")]);
    std::fs::copy(&base, f.0.join("A.olean.private")).unwrap();
    let missing_server = f.observe("import A");
    let private = &missing_server.modules[0]["candidates"][0]["parts"][2];
    assert_eq!(private["capture"]["status"], "captured");
    assert!(
        private["issues"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e.as_str().unwrap().contains("requires a captured server"))
    );
    let mut wrong = std::fs::read(&base).unwrap();
    wrong[6] = b'b';
    std::fs::write(f.0.join("A.olean.server"), wrong).unwrap();
    let mismatched = f.observe("import A");
    assert!(
        mismatched.modules[0]["candidates"][0]["parts"][1]["issues"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e.as_str().unwrap().contains("header identity differs"))
    );
    assert_eq!(mismatched.file_observations.len(), 4);
}

#[test]
fn olean_census_raw_array_bounds_block_full_payload_parser_without_fake_empty_pass() {
    let f = Fixture::new();
    f.module("A", &[], &[Name::anon().str("kept")]);
    let limits = OleanCensusLimits { rows_per_array: 0, ..OleanCensusLimits::default() };
    let out = observe_olean_closure(&[f.source("import A")], &[f.0.clone()], limits);
    let part = &out.modules[0]["candidates"][0]["parts"][0];
    assert_eq!(part["parse_status"], "malformed-or-unresolved-part");
    assert!(
        part["issues"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e.as_str().unwrap().contains("row bound"))
    );
    assert!(part["declarations"].is_null());
    assert!(!out.issues.is_empty());
}

#[test]
fn olean_census_clean_payload_retains_separate_typed_rows_without_deduplication() {
    let f = Fixture::new();
    let path = f.module("A", &[], &[Name::anon().str("same")]);
    let make = |name| {
        ConstantInfo::new_with_reducibility(
            name,
            vec![],
            Expr::sort(Level::zero()),
            None,
            Reducibility::Opaque,
            ConstantKind::Axiom,
        )
    };
    let payload = clean_olean::CleanPayload {
        constants: vec![
            make(Name::anon().str("same")),
            make(Name::anon().str("quoted.dot")),
            make(Name::anon().str("N").num(1)),
            make(Name::anon().str("N").str("1")),
        ],
        ..Default::default()
    };
    let mut bytes = std::fs::read(&path).unwrap();
    bytes.extend(clean_olean::encode_clean_payload(&payload).unwrap());
    std::fs::write(path, bytes).unwrap();
    let out = f.observe("import A");
    let part = &out.modules[0]["candidates"][0]["parts"][0];
    assert_eq!(part["raw_name_witness"]["constants"].as_array().unwrap().len(), 1);
    let rows = part["clean_payload_rosters"]["constants"].as_array().unwrap();
    assert_eq!(rows.len(), 4);
    assert_ne!(rows[2]["name"], rows[3]["name"]);
    assert_eq!(part["clean_payload"]["constants"].as_array().unwrap().len(), 4);
    assert_eq!(part["clean_payload_rosters"]["kernel_classification"], "not-checked");
}

#[test]
fn olean_census_lexer_witness_keeps_quoted_all_unicode_and_rejects_mismatched_ast() {
    let text = "module\nimport all «Q.Dot».fidèle\nimport all Plain\n";
    let parsed = clean_parser::parse_file_with_diagnostics(text).unwrap();
    let tokens = clean_parser::lexer::Lexer::tokenize(text);
    let mut rows = Vec::new();
    let mut names = Vec::new();
    imports(&parsed.decls, text, &tokens, &mut rows, &mut names, 0);
    assert_eq!(
        names,
        vec![
            ModuleName(vec![Segment::Str("Q.Dot".into()), Segment::Str("fidèle".into())]),
            ModuleName(vec![Segment::Str("Plain".into())])
        ]
    );
    assert!(rows.iter().all(|r| r["import_all_modifier"] == true));
    let first_import_start =
        tokens.iter().find(|t| matches!(t.kind, clean_parser::lexer::TokenKind::Import)).unwrap().span.start;
    assert!(
        import_tokens(
            text,
            &tokens,
            first_import_start,
            &[clean_parser::SurfaceName::component("wrong", false)]
        )
        .is_err()
    );
    // Equal display strings must not conceal different component boundaries.
    let wrong = clean_parser::SurfaceName::generated_path("Q.Dot.fidèle");
    assert!(import_tokens(text, &tokens, first_import_start, &[wrong]).is_err());
}

#[test]
fn olean_census_quoted_or_line_broken_all_is_unresolved_not_silently_erased() {
    for text in ["module\nimport «all» Foo\n", "module\nimport all\nFoo\n"] {
        let parsed = clean_parser::parse_file_with_diagnostics(text).unwrap();
        let mut rows = Vec::new();
        let mut names = Vec::new();
        imports(
            &parsed.decls,
            text,
            &clean_parser::lexer::Lexer::tokenize(text),
            &mut rows,
            &mut names,
            0,
        );
        assert!(names.is_empty(), "{text}: {names:?}");
        assert!(
            rows.iter().any(|r| r["status"] == "unresolved-import-identity"
                && r["error"].as_str().unwrap().contains("ambiguous import-all")),
            "{rows:?}"
        );
    }
    let text = "import «all»\n";
    let parsed = clean_parser::parse_file_with_diagnostics(text).unwrap();
    let mut rows = Vec::new();
    let mut names = Vec::new();
    imports(
        &parsed.decls,
        text,
        &clean_parser::lexer::Lexer::tokenize(text),
        &mut rows,
        &mut names,
        0,
    );
    assert_eq!(names, vec![ModuleName(vec![Segment::Str("all".into())])]);
    assert_eq!(rows[0]["import_all_modifier"], false);
}

#[test]
fn olean_census_deep_dependency_cycle_uses_bounded_heap_not_native_recursion() {
    let name = |i: usize| ModuleName(vec![Segment::Str(format!("M{i}"))]);
    let mut graph = BTreeMap::new();
    for i in 0..4096 {
        graph.insert(name(i), BTreeSet::from([name((i + 1) % 4096)]));
    }
    let found = cycles(&graph);
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].len(), 4097);
}
