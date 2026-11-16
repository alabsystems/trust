use std::fs;
use std::io::Read as _;
use std::path::Path;
use std::sync::OnceLock;

use super::*;
use crate::Value;

mod fixed_point;

#[test]
fn receipt_reader_does_not_change_the_shared_incumbent_json_semantics() {
    let object: serde_json::Value =
        serde_json::from_str(r#"{"$serde_json::private::Number":"2"}"#).unwrap();
    assert!(object.is_object(), "an ordinary JSON object became a number in another consumer");
    let object: serde_json::Value = serde_json::from_str(r#"{"z":1,"a":2}"#).unwrap();
    assert_eq!(
        object.as_object().unwrap().keys().map(String::as_str).collect::<Vec<_>>(),
        ["a", "z"]
    );
}

#[test]
fn python_repr_preserves_nonempty_objects_order_and_native_scalar_spellings() {
    let value = json::parse(br#"{"z":[true,null,{"inner":false}],"a":"quoted'word"}"#).unwrap();
    assert_eq!(repr(&value), "{'z': [True, None, {'inner': False}], 'a': \"quoted'word\"}");
    let value = json::parse(br#"["\u0000","\u007f","\u0085","\t\n\r"]"#).unwrap();
    assert_eq!(repr(&value), "['\\x00', '\\x7f', '\\x85', '\\t\\n\\r']");
}

fn reference() -> &'static Value {
    static DATA: OnceLock<Value> = OnceLock::new();
    DATA.get_or_init(|| {
        let mut raw = Vec::new();
        flate2::read::GzDecoder::new(&include_bytes!("../tests/data/reference.json.gz")[..])
            .take(8 * 1024 * 1024)
            .read_to_end(&mut raw)
            .unwrap();
        assert_eq!(hash(&raw), "f563c189186c6b9ef0a16bf473e8caec61b774be9ad10d05eeeea68a83a39cfd");
        let value = json::parse(&raw).unwrap();
        assert_eq!(value["schema"], "trust.stage-receipt.golden.v1");
        assert_eq!(
            value["reference_reader_sha256"],
            "068819ea74788a22058e0662878ff1cf6fb9354d63fc113b0e7410a389888c6c"
        );
        value
    })
}

fn unhex(text: &str) -> Vec<u8> {
    assert_eq!(text.len() % 2, 0);
    text.as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let byte = std::str::from_utf8(pair).unwrap();
            u8::from_str_radix(byte, 16).unwrap()
        })
        .collect()
}

/// Each stage-relative name of the table `files` under `root`, holding the bytes its hex gives.
fn write_files(root: &Path, files: &Value) {
    for (name, bytes) in files.as_object().unwrap() {
        assert!(
            !name.starts_with('/') && name.split('/').all(|part| !matches!(part, "" | "." | ".."))
        );
        let path = root.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, unhex(bytes.as_str().unwrap())).unwrap();
    }
}

fn materialize(root: &Path, case: &Value) {
    write_files(root, &case["files"]);
    let path = root.join(RECEIPT_NAME);
    match case["receipt_kind"].as_str().unwrap() {
        "file" => fs::write(path, unhex(case["raw_hex"].as_str().unwrap())).unwrap(),
        "absent" => (),
        "directory" => fs::create_dir(path).unwrap(),
        #[cfg(unix)]
        "link" => std::os::unix::fs::symlink("unowned-receipt", path).unwrap(),
        other => panic!("unsupported reference fixture kind {other}"),
    }
}

#[test]
fn all_204_original_filesystem_controls_preserve_lines_and_refusals() {
    let cases = reference()["file_cases"].as_array().unwrap();
    assert_eq!(cases.len(), 204);
    let mut successes = 0;
    let mut refusals = 0;
    for (index, case) in cases.iter().enumerate() {
        let temporary = tempfile::tempdir().unwrap();
        materialize(temporary.path(), case);
        let actual = inspect_with_limit(
            temporary.path(),
            case["commit"].as_str().unwrap(),
            case["max_bytes"].as_u64().unwrap(),
        );
        if let Some(lines) = case["lines"].as_array() {
            let actual = actual
                .unwrap_or_else(|e| panic!("reference accepted case {index}, native refused: {e}"));
            assert_eq!(
                actual.provenance_lines(),
                lines.iter().map(|v| v.as_str().unwrap().to_owned()).collect::<Vec<_>>(),
                "reference case {index}"
            );
            successes += 1;
        } else {
            let failure = actual.err().unwrap_or_else(|| {
                panic!("native accepted original refusal {index}: {}", case["error"])
            });
            assert!(!failure.0.is_empty());
            refusals += 1;
        }
    }
    assert!(
        successes > 30 && refusals > 80,
        "reference population changed: {successes}/{refusals}"
    );
}

#[test]
fn all_58_original_llvm_controls_match_exact_error_inventories() {
    let cases = reference()["llvm_cases"].as_array().unwrap();
    assert_eq!(cases.len(), 58);
    for (i, case) in cases.iter().enumerate() {
        let value = json::parse(case["value_json"].as_str().unwrap().as_bytes()).unwrap();
        let receipt = json::parse(case["receipt_json"].as_str().unwrap().as_bytes()).unwrap();
        let actual = llvm::identity_errors(&value, &receipt);
        let expected = case["errors"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        assert_eq!(actual, expected, "LLVM reference {i}");
    }
}

#[test]
fn all_36_original_invocation_controls_preserve_strict_unicode_refusal() {
    let cases = reference()["invocation_cases"].as_array().unwrap();
    assert_eq!(cases.len(), 36);
    let known_unpaired = [
        r#"{"schema": "trust.recreator-invocation.v1", "scope": "self-reported", "argv": ["--llvm-config", "/opt/llvm\udcff/bin/llvm-config"]}"#,
        r#"{"argv": ["--llvm-config", "/opt/llvm\udcff/bin/llvm-config"], "schema": "trust.recreator-invocation.v1", "scope": "self-reported"}"#,
        r#"{"schema": "trust.recreator-invocation.v1", "scope": "self-reported", "argv": ["--host", "a\ud800b"]}"#,
        r#"{"argv": ["--host", "a\ud800b"], "schema": "trust.recreator-invocation.v1", "scope": "self-reported"}"#,
        r#"{"schema": "trust.recreator-invocation.v1", "scope": "self-reported", "argv": ["--host", "a\udfffb"]}"#,
        r#"{"argv": ["--host", "a\udfffb"], "schema": "trust.recreator-invocation.v1", "scope": "self-reported"}"#,
    ];
    let mut observed_unpaired = 0;
    for (i, case) in cases.iter().enumerate() {
        let expected = case["errors"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        match json::parse(case["value_json"].as_str().unwrap().as_bytes()) {
            Ok(value) => {
                assert_eq!(invocation_errors(&value), expected, "invocation reference {i}")
            }
            Err(error) => {
                assert_eq!(
                    expected,
                    ["recreator_invocation.argv holds a control or unprintable character"],
                    "JSON refused an original valid invocation {i}: {error}"
                );
                let raw = case["value_json"].as_str().unwrap();
                assert!(
                    known_unpaired.contains(&raw),
                    "unexpected original raw Unicode input {i}: {raw}; {error}"
                );
                observed_unpaired += 1;
            }
        }
    }
    assert_eq!(observed_unpaired, known_unpaired.len());
}

#[test]
fn nested_duplicates_non_json_numbers_and_trailing_bytes_refuse() {
    for raw in [
        br#"{"outer":{"x":1,"x":2}}"#.as_slice(),
        br#"{"x":NaN}"#,
        br#"{"x":Infinity}"#,
        br#"{}{}"#,
    ] {
        assert!(json::parse(raw).is_err());
    }
}

#[test]
fn unicode_ascii_digest_and_shell_arguments_preserve_exact_wire_values() {
    assert_eq!(
        json::ascii_canonical(&json::parse(br#"{"z":"\ud83e\udee8\u007f","a":"\n\\\""}"#).unwrap()),
        r#"{"a":"\n\\\"","z":"\ud83e\udee8\u007f"}"#
    );
    assert_eq!(quoted_arguments(&[]), "(no arguments)");
    assert_eq!(quoted_arguments(&["not-recorded".into()]), "'not-recorded'");
    assert_eq!(
        quoted_arguments(&["a'b".into(), "/opt/llvm 22/bin".into()]),
        "'a'\"'\"'b' '/opt/llvm 22/bin'"
    );
    assert_eq!(quoted_arguments(&["a🫨'\\".into()]), "$'a\\xf0\\x9f\\xab\\xa8\\'\\\\'");
    assert!(quoted_arguments(&["x".repeat(4097)]).starts_with("(not quoted here: 4097 characters"));
}

#[test]
fn receipt_read_is_bounded_and_rejects_live_replacement() {
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join(RECEIPT_NAME);
    fs::write(&path, b"{}").unwrap();
    assert!(inspect_with_limit(temporary.path(), "", 1).unwrap_err().0.contains("more than 1"));
    let loaded = files::read_receipt(&path, MAX_RECEIPT_BYTES).unwrap().unwrap();
    fs::rename(&path, temporary.path().join("old")).unwrap();
    fs::write(&path, b"{}").unwrap();
    assert!(loaded.check_current().unwrap_err().0.contains("changed"));
}

#[test]
fn unlisted_library_bytes_are_not_misrepresented_as_receipt_coverage() {
    let case = reference()["file_cases"]
        .as_array()
        .unwrap()
        .iter()
        .find(|case| {
            case["lines"].as_array().is_some_and(|v| {
                v.iter().any(|s| s == "stage_receipt_status=internal-release-ready")
            })
        })
        .unwrap();
    let temporary = tempfile::tempdir().unwrap();
    materialize(temporary.path(), case);
    let before = inspect(temporary.path(), case["commit"].as_str().unwrap()).unwrap();
    fs::create_dir(temporary.path().join("lib")).unwrap();
    fs::write(temporary.path().join("lib/unlisted-driver"), b"not covered by this reader").unwrap();
    let after = inspect(temporary.path(), case["commit"].as_str().unwrap()).unwrap();
    assert_eq!(before.provenance_lines(), after.provenance_lines());
    assert_eq!(
        before.checked().unwrap().files_verified(),
        after.checked().unwrap().files_verified()
    );
}

#[test]
fn compiler_reported_commit_and_every_listed_file_stay_required() {
    let case = reference()["file_cases"]
        .as_array()
        .unwrap()
        .iter()
        .find(|case| {
            case["lines"].as_array().is_some_and(|v| {
                v.iter().any(|s| s == "stage_receipt_status=internal-release-ready")
            })
        })
        .unwrap();
    let temporary = tempfile::tempdir().unwrap();
    materialize(temporary.path(), case);
    assert!(
        inspect(temporary.path(), &"2".repeat(40)).unwrap_err().0.contains("names source commit")
    );
    fs::write(temporary.path().join("bin/ty"), b"substituted").unwrap();
    assert!(
        inspect(temporary.path(), case["commit"].as_str().unwrap())
            .unwrap_err()
            .0
            .contains("records sha256")
    );
}

fn completed_candidate_fixture(
    stage_token: &str,
    lineage_commit: Option<&str>,
) -> (tempfile::TempDir, String) {
    let case = reference()["file_cases"]
        .as_array()
        .unwrap()
        .iter()
        .find(|case| {
            case["lines"].as_array().is_some_and(|lines| {
                lines.iter().any(|line| line == "stage_receipt_status=internal-release-ready")
            })
        })
        .unwrap();
    let temporary = tempfile::tempdir().unwrap();
    materialize(temporary.path(), case);
    let commit = case["commit"].as_str().unwrap().to_owned();
    let path = temporary.path().join(RECEIPT_NAME);
    let mut data = json::parse(&fs::read(&path).unwrap()).unwrap();
    let closure = "c".repeat(64);
    data["stage"] = Value::String("__ACTUAL_JSON_STAGE_TOKEN__".into());
    data["source_tree_clean"] = Value::Bool(true);
    data["source_lineage"] = json::parse(&serde_json::to_vec(&serde_json::json!({
        "schema":"trust.source-lineage.v1", "status":"immutable_release", "source_tree_clean":true,
        "errors":[], "stable_across_build":true, "closure_sha256":closure,
        "pre_build_closure_sha256":closure, "post_build_closure_sha256":closure,
        "repositories":[{"path":".","head":lineage_commit.unwrap_or(&commit)}]
    })).unwrap()).unwrap();
    let raw = data.to_string().replace("\"__ACTUAL_JSON_STAGE_TOKEN__\"", stage_token);
    fs::write(path, raw).unwrap();
    (temporary, commit)
}

#[test]
fn completed_candidate_preserves_large_integer_stage_acceptance_with_original_read_limit() {
    for token in ["18446744073709551617".into(), "9".repeat(4300)] {
        let (temporary, commit) = completed_candidate_fixture(&token, None);
        let receipt =
            inspect(temporary.path(), &commit).expect("receipt executable hashes remain valid");
        assert!(receipt.checked().unwrap().completed_candidate(&commit).is_ok());
    }
    let (temporary, commit) = completed_candidate_fixture(&"9".repeat(4301), None);
    assert!(inspect(temporary.path(), &commit).unwrap_err().0.contains("4300-digit"));
}

#[test]
fn completed_candidate_binds_the_originally_checked_compiler_commit() {
    let other = "2".repeat(40);
    let (temporary, commit) = completed_candidate_fixture("2", Some(&other));
    assert_ne!(commit, other);
    let receipt =
        inspect(temporary.path(), &commit).expect("original compiler identity still valid");
    assert!(
        receipt.checked().unwrap().completed_candidate(&other).is_err(),
        "a different requested commit cannot adopt this checked compiler"
    );
}

#[test]
fn completed_candidate_keeps_integer_float_boolean_and_object_stages_distinct() {
    for (token, accepted) in [
        ("2", true),
        ("2.0", false),
        ("2e0", false),
        ("true", false),
        ("1", false),
        ("-2", false),
        (r#"{"$serde_json::private::Number":"2"}"#, false),
    ] {
        let (temporary, commit) = completed_candidate_fixture(token, None);
        let receipt = inspect(temporary.path(), &commit).unwrap();
        assert_eq!(
            receipt.checked().unwrap().completed_candidate(&commit).is_ok(),
            accepted,
            "stage token {token}"
        );
    }
}

/// Reference file case 0's receipt with one more key, holding `depth` lists one inside the
/// next, and the byte of its 1000th list. scripts/tests/stage_receipt_reader_parity_test.py
/// builds the same and holds the Python reader to the same verdicts.
fn nested_receipt(depth: usize) -> (Vec<u8>, usize) {
    let raw = unhex(reference()["file_cases"][0]["raw_hex"].as_str().unwrap());
    let raw = raw.trim_ascii_end();
    let body = raw.strip_suffix(b"}").expect("the reference receipt is one JSON object");
    let mut nested = [body, b", \"nested\": "].concat();
    let byte = nested.len() + 999;
    nested.extend("[".repeat(depth).bytes().chain("]".repeat(depth).bytes()));
    nested.extend(b"}\n");
    (nested, byte)
}

#[test]
fn a_receipt_nested_past_the_bound_is_refused_where_the_python_reader_refuses_it() {
    let case = &reference()["file_cases"][0];
    let commit = case["commit"].as_str().unwrap();
    // 999 lists inside the receipt's own object are 1000 containers: read as before.
    let (raw, _) = nested_receipt(999);
    let temporary = tempfile::tempdir().unwrap();
    materialize(temporary.path(), case);
    fs::write(temporary.path().join(RECEIPT_NAME), &raw).unwrap();
    let lines = inspect(temporary.path(), commit).unwrap().provenance_lines();
    assert!(lines.contains(&format!("stage_receipt_sha256={}", hash(&raw))), "{lines:?}");
    assert!(lines.contains(&"stage_receipt_files_verified=19".into()), "{lines:?}");
    // One more is refused at its byte, in the words the Python reader gives too.
    let (raw, byte) = nested_receipt(1000);
    assert_eq!(raw[byte], b'[');
    fs::write(temporary.path().join(RECEIPT_NAME), &raw).unwrap();
    assert_eq!(
        inspect(temporary.path(), commit).unwrap_err().0,
        format!("it is not JSON: JSON nesting exceeds 1000 containers at byte {byte}")
    );
}
