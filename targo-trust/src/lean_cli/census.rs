// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Diagnostic source/check observations; never input or publication authority.
//! The final roster keeps its existing schema. Earlier fresh-session attempts
//! are separate measurements, not declarations to union into a denominator.

use std::io::Read;
use std::path::Path;

use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use trust_certify::lean_source_batch::{CheckedLeanSourceBatch, LeanSourceAlias};

use super::{CheckedLeanBatch, LeanSourceSnapshot};

fn alias_records(aliases: &[LeanSourceAlias]) -> Vec<Value> {
    aliases
        .iter()
        .map(|alias| json!({"module": alias.module, "source_index": alias.source_index}))
        .collect()
}

pub(super) struct Observation {
    attempts: Vec<Value>,
    discoveries: Vec<Value>,
    working_directory: Value,
}

impl Default for Observation {
    fn default() -> Self {
        let working_directory = match std::env::current_dir() {
            Ok(path) => json!({"status": "observed", "path": path.display().to_string()}),
            Err(error) => json!({"status": "unavailable", "error": error.to_string()}),
        };
        Self { attempts: Vec::new(), discoveries: Vec::new(), working_directory }
    }
}

impl Observation {
    pub(super) fn record_attempt(&mut self, checked: &CheckedLeanSourceBatch) {
        self.attempts.push(json!({
            "iteration": self.attempts.len(),
            "scope": "fresh-session-supplied-source-batch",
            "errors": checked.errors(),
            "source_aliases": alias_records(checked.aliases()),
            "kernel_roster": checked.attempt().and_then(|batch| batch.census.as_ref()).map(|census| &census.report),
        }));
    }

    pub(super) fn record_discovery(
        &mut self,
        source: &LeanSourceSnapshot,
        module: &str,
        candidate: &Path,
        is_file: bool,
    ) {
        self.discoveries.push(json!({
            "iteration": self.attempts.len() - 1,
            "source_path": source.path.display().to_string(),
            "source_sha256": source.raw_sha256,
            "imported_module": module,
            "candidate_path": candidate.display().to_string(),
            "candidate_is_file_at_discovery": is_file,
        }));
    }
}

/// Hash the current executable PATH, not a discovered compiler or caller hash.
/// This is not a loaded-image attestation: replacing the executable's directory
/// entry can leave the running process mapped to older bytes. Loaded images,
/// source closure and toolchain provenance need the external run harness.
pub(crate) fn tool_identity() -> Result<Value, String> {
    let path = std::env::current_exe().map_err(|error| error.to_string())?;
    let mut file = std::fs::File::open(&path).map_err(|error| error.to_string())?;
    let mut digest = Sha256::new();
    let mut bytes = [0u8; 65536];
    loop {
        let count = file.read(&mut bytes).map_err(|error| error.to_string())?;
        if count == 0 {
            break;
        }
        digest.update(&bytes[..count]);
    }
    Ok(json!({
        "path": path.display().to_string(),
        "sha256": format!("{:x}", digest.finalize()),
        "version": env!("CARGO_PKG_VERSION"),
        "embedded_source_revision": crate::embedded_trust_repo_commit_hash(option_env!("CFG_VER_HASH")),
        "loaded_dependencies": "not-measured",
        "full_toolchain_closure": "requires-external-run-binding",
        "scope": "current-executable-path-bytes-not-loaded-image",
        "authority": "diagnostic-self-observation-only",
    }))
}

pub(crate) fn observe_external(
    checked: &CheckedLeanBatch,
    roots: &[std::path::PathBuf],
    outputs: &[&Path],
) -> Result<Option<Value>, String> {
    if roots.is_empty() {
        return Ok(None);
    }
    let sources = checked
        .sources()
        .iter()
        .map(|source| trust_clean::olean_census::OleanCensusSource {
            module: source.module.clone(),
            path: source.path.clone(),
            source: source.source.clone(),
        })
        .collect::<Vec<_>>();
    let observed = trust_clean::olean_census::observe_olean_closure(
        &sources,
        roots,
        trust_clean::olean_census::OleanCensusLimits::default(),
    );
    for output in outputs {
        protect_observed_paths(output, observed.observed_paths())?;
    }
    serde_json::to_value(observed).map(Some).map_err(|error| error.to_string())
}

/// Opt-in same-read capture for the diagnostic runtime producer. The existing
/// observer and its JSON-only callers retain their previous behavior.
pub(crate) fn capture_external(
    checked: &CheckedLeanBatch,
    roots: &[std::path::PathBuf],
    outputs: &[&Path],
) -> Result<trust_clean::olean_census::OleanClosureCapture, String> {
    let sources = checked
        .sources()
        .iter()
        .map(|source| trust_clean::olean_census::OleanCensusSource {
            module: source.module.clone(),
            path: source.path.clone(),
            source: source.source.clone(),
        })
        .collect::<Vec<_>>();
    let captured = if let Some(accepted) = checked.accepted_context() {
        use trust_clean::olean_census::{ModuleName, OleanCensusSourceBinding, Segment};
        // Match CheckedLeanSourceBatch's exact source-key interpretation: each
        // dotted path component is a string, including numeric file names.
        // A quoted single component containing a dot is a different identity.
        // The accepted context already binds this ordered source/alias mapping
        // to the exact snapshots; never reconstruct it from report labels.
        let binding = |module: &str, source_index: usize| OleanCensusSourceBinding {
            module: ModuleName(module.split('.').map(|part| Segment::Str(part.into())).collect()),
            source_index,
            source_sha256: format!(
                "{:x}",
                Sha256::digest(accepted.sources()[source_index].source.as_bytes())
            ),
        };
        let bindings: Vec<_> = accepted
            .sources()
            .iter()
            .enumerate()
            .map(|(index, source)| binding(&source.module, index))
            .chain(
                accepted.aliases().iter().map(|alias| binding(&alias.module, alias.source_index)),
            )
            .collect();
        trust_clean::olean_census::capture_olean_closure_with_source_bindings(
            &sources,
            &bindings,
            roots,
            trust_clean::olean_census::OleanCensusLimits::default(),
        )
    } else {
        trust_clean::olean_census::capture_olean_closure(
            &sources,
            roots,
            trust_clean::olean_census::OleanCensusLimits::default(),
        )
    };
    for output in outputs {
        protect_observed_paths(output, captured.observation.observed_paths())?;
    }
    Ok(captured)
}

fn protect_observed_paths(output: &Path, observed: &[std::path::PathBuf]) -> Result<(), String> {
    let resolve_new = |path: &Path| -> std::io::Result<std::path::PathBuf> {
        let parent = path.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
        let name = path.file_name().ok_or_else(|| std::io::Error::other("missing filename"))?;
        Ok(parent.canonicalize()?.join(name))
    };
    let resolve_observed = |path: &Path| -> std::io::Result<std::path::PathBuf> {
        let mut path = path.to_path_buf();
        for _ in 0..40 {
            let resolved = resolve_new(&path)?;
            match std::fs::symlink_metadata(&resolved) {
                Ok(metadata) if metadata.file_type().is_symlink() => {
                    let target = std::fs::read_link(&resolved)?;
                    path = if target.is_absolute() {
                        target
                    } else {
                        resolved.parent().unwrap_or(Path::new(".")).join(target)
                    };
                }
                Ok(_) => return resolved.canonicalize(),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(resolved),
                Err(error) => return Err(error),
            }
        }
        Err(std::io::Error::other("too many observed-path symlinks"))
    };
    let output = resolve_new(output).map_err(|error| error.to_string())?;
    for path in observed {
        match resolve_observed(path) {
            Ok(path) if path == output => {
                return Err(format!(
                    "output {} aliases an observed source or .olean dependency candidate; nothing was published",
                    output.display()
                ));
            }
            Ok(_) => {}
            // A nonexistent parent cannot contain this currently creatable output.
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(format!(
                    "cannot check observed path {} against output: {error}",
                    path.display()
                ));
            }
        }
    }
    Ok(())
}

fn source_record(source: &LeanSourceSnapshot) -> Value {
    json!({
        "path": source.path.display().to_string(),
        "module": source.module,
        "sha256": source.raw_sha256,
        "bytes": source.raw_size,
        "read_status": if source.source.is_ok() { "read-utf8" } else { "read-failed" },
        "read_error": source.source.as_ref().err(),
    })
}

pub(crate) fn report(
    checked: &CheckedLeanBatch,
    requested: &[std::path::PathBuf],
    operation: &str,
    tool_before: &Value,
    tool_after: &Value,
) -> Value {
    // Keep the existing wrapper and final kernel_roster meanings. The new
    // versioned source graph is additive; it is not the compiler JSONL stream.
    json!({
        "schema": "trust.lean.check-kernel-roster/v1",
        "authority": "diagnostic-only",
        "tool_version": env!("CARGO_PKG_VERSION"),
        "tool_source_revision": crate::embedded_trust_repo_commit_hash(option_env!("CFG_VER_HASH")),
        "requested_files": requested.iter().map(|path| path.display().to_string()).collect::<Vec<_>>(),
        "kernel_roster": checked.census().cloned().unwrap_or_else(|| json!({
            "status": "not-collected",
            "denominator_status": "denominator_unverified",
            "runtime_body_universe": "unmeasured",
        })),
        "check_report": serde_json::from_str::<Value>(&super::render_json(checked)).expect("valid check JSON"),
        "source_graph": {
            "schema": "trust.lean.source-check-observation/v1",
            "operation": operation,
            "stage": "after-source-check-before-computational-production",
            "working_directory_at_check_start": checked.observation.as_ref().map(|observation| &observation.working_directory),
            "source_closure_accepted": checked.accepted_context().is_some(),
            "sources": checked.sources().iter().map(source_record).collect::<Vec<_>>(),
            "source_aliases": alias_records(&checked.aliases),
            "unresolved_imports": checked.unresolved_imports().iter().map(|import| json!({
                "source_path": import.source_path().display().to_string(),
                "module": import.module(),
                "diagnostic": import.diagnostic(),
            })).collect::<Vec<_>>(),
            "attempts": checked.observation.as_ref().map(|observation| &observation.attempts),
            "import_discovery": checked.observation.as_ref().map(|observation| &observation.discoveries),
            "tool_before": tool_before,
            "tool_after": tool_after,
            "tool_path_bytes_stable": tool_before == tool_after,
            "denominator_status": "denominator_unverified",
            "runtime_body_universe": "unmeasured",
            "limitations": [
                "Import edges are only unresolved-import discoveries reported by the actual elaborator; imports already satisfied within a supplied batch are not enumerated.",
                "Each attempted roster comes from a fresh kernel session; never union repeated attempt rows into a body denominator.",
                "The final kernel roster includes every observed owned identity and classification, not just emitted computational bodies.",
                "Unreadable sources and failed closure attempts remain explicit; absence of a final roster does not mean an empty complete population.",
                "External .olean packages, lazy kernel enumeration, erased/specialized runtime bodies and complete import reachability remain unverified.",
                "Executable-path hashes bind two on-disk observations only, not the mapped running image, loaded dependency closure, source refinement, compiler or publication authority.",
                "This pre-production report does not assert subsequent lowering, publication, process completion or artifact success."
            ],
        },
    })
}

/// Refuse two spellings of one not-yet-created destination. Both parents must
/// exist; canonicalizing them handles ./, .. and parent symlink aliases. The
/// final create-only writers still protect against subsequent path races.
pub(crate) fn distinct_outputs(left: &Path, right: &Path) -> Result<(), String> {
    let resolved = |path: &Path| -> Result<std::path::PathBuf, String> {
        let parent = path.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
        let parent =
            parent.canonicalize().map_err(|error| format!("{}: {error}", parent.display()))?;
        let name =
            path.file_name().ok_or_else(|| format!("{} has no output filename", path.display()))?;
        Ok(parent.join(name))
    };
    if resolved(left)? == resolved(right)? {
        return Err("--census and --out must name distinct new files; neither was created".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn olean_census_protects_missing_candidates_and_parent_aliases() {
        let dir = tempfile::tempdir().unwrap();
        let missing = dir.path().join("Missing.olean");
        assert!(protect_observed_paths(&missing, std::slice::from_ref(&missing)).is_err());
        assert!(
            protect_observed_paths(
                &dir.path().join("./Missing.olean"),
                std::slice::from_ref(&missing)
            )
            .is_err()
        );
        let unused = dir.path().join("report.json");
        protect_observed_paths(&unused, std::slice::from_ref(&missing)).unwrap();
        assert!(!missing.exists() && !unused.exists());
        #[cfg(unix)]
        {
            let alias = dir.path().join("alias");
            std::os::unix::fs::symlink(dir.path(), &alias).unwrap();
            assert!(protect_observed_paths(&alias.join("Missing.olean"), &[missing]).is_err());
        }
    }

    #[cfg(unix)]
    #[test]
    fn olean_census_refuses_dangling_dependency_symlink_to_output() {
        let dir = tempfile::tempdir().unwrap();
        let main = dir.path().join("Main.lean");
        let output = dir.path().join("report.json");
        let dependency = dir.path().join("External.olean");
        let redirect = dir.path().join("redirect");
        std::fs::write(&main, "import External\ndef ordinary : Nat := 1\n").unwrap();
        std::os::unix::fs::symlink("report.json", &redirect).unwrap();
        std::os::unix::fs::symlink("redirect", &dependency).unwrap();
        let checked = super::super::check_batch(&[main], true);
        let roots = [dir.path().to_path_buf()];

        assert!(observe_external(&checked, &roots, &[&output]).is_err());
        assert!(capture_external(&checked, &roots, &[&output]).is_err());
        assert!(!output.exists());
        assert!(dependency.symlink_metadata().unwrap().file_type().is_symlink());
    }

    #[test]
    fn olean_census_never_promotes_an_external_import_or_mutates_checked_identity() {
        let dir = tempfile::tempdir().unwrap();
        let main = dir.path().join("Main.lean");
        let output = dir.path().join("report.json");
        std::fs::write(&main, "import External\ndef ordinary : Nat := 1").unwrap();
        std::fs::write(dir.path().join("External.olean"), b"present but malformed").unwrap();
        let refused = super::super::check_batch(std::slice::from_ref(&main), true);
        assert!(refused.accepted_context().is_none());
        let before = observe(&refused);
        let external =
            observe_external(&refused, &[dir.path().into()], &[&output]).unwrap().unwrap();
        assert_eq!(external["authority"], "diagnostic-only-no-import-admission");
        assert!(!external["issues"].as_array().unwrap().is_empty());
        assert_eq!(observe(&refused), before);
        assert!(refused.accepted_context().is_none());
        std::fs::write(&main, "def ordinary : Nat := 1").unwrap();
        let accepted = super::super::check_batch(&[main], true);
        let context = accepted.accepted_context().unwrap();
        let root = context.source_closure_sha256().to_string();
        let external =
            observe_external(&accepted, &[dir.path().into()], &[&output]).unwrap().unwrap();
        assert_eq!(external["modules"].as_array().unwrap().len(), 0);
        assert_eq!(accepted.accepted_context().unwrap().source_closure_sha256(), root);
        assert!(observe_external(&accepted, &[], &[&output]).unwrap().is_none());
    }

    fn observe(checked: &CheckedLeanBatch) -> Value {
        report(
            checked,
            &[],
            "check",
            &json!({"test": "not-tool-authority"}),
            &json!({"test": "not-tool-authority"}),
        )
    }

    #[test]
    fn runtime_capture_does_not_use_alias_bindings_without_the_exact_accepted_context() {
        let dir = tempfile::tempdir().unwrap();
        let main = dir.path().join("Main.lean");
        let leaf = dir.path().join("Sub/Leaf.lean");
        std::fs::create_dir(dir.path().join("Sub")).unwrap();
        std::fs::write(&main, "import Sub.Leaf\ndef root : Nat := leaf\n").unwrap();
        std::fs::write(&leaf, "def leaf : Nat := 1\n").unwrap();
        let mut checked = super::super::check_batch_for_runtime(&[main, leaf]);
        assert!(checked.accepted_context().is_some());
        assert_eq!(checked.aliases.len(), 1);
        // A rebound adapter mapping cannot borrow the final accepted session.
        checked.aliases[0].source_index = 0;
        assert!(checked.accepted_context().is_none());
        let captured = capture_external(&checked, &[], &[]).unwrap();
        assert!(captured.observation.source_bindings.is_none());
        assert_eq!(captured.observation.sources.len(), 2);
        assert_eq!(captured.observation.modules.len(), 1);
        assert_eq!(captured.observation.modules[0]["status"], "missing");
    }

    #[test]
    fn import_attempts_and_complete_observed_kernel_population_are_retained() {
        let dir = tempfile::tempdir().unwrap();
        let main = dir.path().join("Main.lean");
        let helper = dir.path().join("Helper.lean");
        std::fs::write(&main, "import Helper\ndef mainValue : UInt8 := 4\n").unwrap();
        std::fs::write(&helper, "def proposition : Prop := True\ndef proofValue : True := True.intro\ntheorem proof : True := True.intro\ndef typeValue : Type := Nat\ninductive CensusChoice where\n | one : CensusChoice\n | two : CensusChoice\n").unwrap();
        let checked = super::super::check_batch(&[main], true);
        assert!(checked.accepted_context().is_some(), "{:?}", checked.verdicts());
        let measured = observe(&checked);
        let graph = &measured["source_graph"];
        assert_eq!(graph["sources"].as_array().unwrap().len(), 2);
        assert_eq!(
            graph["working_directory_at_check_start"]["path"],
            std::env::current_dir().unwrap().display().to_string()
        );
        let attempts = graph["attempts"].as_array().unwrap();
        assert_eq!(attempts.len(), 2);
        assert_eq!(attempts[0]["kernel_roster"]["check_rejected"], true);
        assert_eq!(attempts[1]["kernel_roster"], measured["kernel_roster"]);
        assert_eq!(graph["import_discovery"][0]["imported_module"], "Helper");
        let rows = measured["kernel_roster"]["declarations"].as_array().unwrap();
        for name in [
            "mainValue",
            "proposition",
            "proofValue",
            "proof",
            "typeValue",
            "CensusChoice",
            "CensusChoice.one",
            "CensusChoice.two",
            "CensusChoice.rec",
        ] {
            assert!(rows.iter().any(|row| row["name"] == name), "missing {name}");
        }
        assert!(rows.iter().all(|row| row["runtime_classification"] == "unmeasured"));
        assert_eq!(graph["denominator_status"], "denominator_unverified");
        assert_eq!(
            measured["kernel_roster"]["kernel_classification_schema"],
            "trust.lean.kernel-classification/v1"
        );
        // The diagnostic snapshot is immutable when source paths later drift.
        let before = measured.clone();
        std::fs::write(helper, "def replacement : Nat := 0").unwrap();
        assert_eq!(observe(&checked), before);
    }

    #[test]
    fn failed_utf8_import_retains_raw_hash_and_provisional_attempt_not_final_roster() {
        let dir = tempfile::tempdir().unwrap();
        let main = dir.path().join("Main.lean");
        let invalid = dir.path().join("Invalid.lean");
        std::fs::write(&main, "import Invalid\ndef prior : Nat := 1").unwrap();
        std::fs::write(&invalid, [0xff, 0xfe]).unwrap();
        let checked = super::super::check_batch(&[main], true);
        let measured = observe(&checked);
        assert_eq!(measured["kernel_roster"]["status"], "not-collected");
        let graph = &measured["source_graph"];
        assert_eq!(graph["source_closure_accepted"], false);
        assert_eq!(graph["attempts"].as_array().unwrap().len(), 1);
        assert_eq!(
            graph["sources"][1]["sha256"],
            trust_types::digest::stable_sha256_hex(&[0xff, 0xfe])
        );
        assert_eq!(graph["sources"][1]["bytes"], 2);
        assert_eq!(graph["sources"][1]["read_status"], "read-failed");
        assert_eq!(graph["unresolved_imports"][0]["module"], "Invalid");
        assert_eq!(checked.verdicts().len(), 1, "preserve existing wholesale diagnostics");
    }

    #[test]
    fn missing_input_duplicate_modules_and_false_proof_remain_distinct_failures() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("Bad.lean");
        let missing = observe(&super::super::check_batch(std::slice::from_ref(&path), true));
        assert!(missing["source_graph"]["sources"][0]["sha256"].is_null());
        assert_eq!(missing["source_graph"]["attempts"], json!([]));
        std::fs::write(&path, "theorem falseProof : 0 = 1 := rfl").unwrap();
        let failed = observe(&super::super::check_batch(std::slice::from_ref(&path), true));
        assert_eq!(failed["kernel_roster"]["check_rejected"], true);
        assert_eq!(failed["source_graph"]["sources"][0]["read_status"], "read-utf8");
        let duplicate = observe(&super::super::check_batch(&[path.clone(), path], true));
        assert_eq!(duplicate["source_graph"]["sources"].as_array().unwrap().len(), 2);
        assert_eq!(duplicate["source_graph"]["attempts"], json!([]));
        assert_eq!(duplicate["source_graph"]["source_closure_accepted"], false);
    }

    #[test]
    fn no_observer_has_no_synthetic_attempts_or_denominator() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("Good.lean");
        std::fs::write(&path, "def value : UInt8 := 7").unwrap();
        let plain = super::super::check_batch(std::slice::from_ref(&path), false);
        let measured = super::super::check_batch(&[path], true);
        assert_eq!(super::super::render_json(&plain), super::super::render_json(&measured));
        assert_eq!(
            plain.accepted_context().unwrap().source_closure_sha256(),
            measured.accepted_context().unwrap().source_closure_sha256()
        );
        assert_eq!(
            plain.accepted_context().unwrap().owned_declarations_sha256(),
            measured.accepted_context().unwrap().owned_declarations_sha256()
        );
        assert!(observe(&plain)["source_graph"]["attempts"].is_null());
        assert_eq!(observe(&plain)["kernel_roster"]["status"], "not-collected");
    }

    #[test]
    fn output_aliases_refuse_without_creation_and_tool_drift_is_disclosed() {
        let dir = tempfile::tempdir().unwrap();
        let output = dir.path().join("out.json");
        assert!(distinct_outputs(&output, &dir.path().join("./out.json")).is_err());
        #[cfg(unix)]
        {
            let alias = dir.path().join("alias");
            std::os::unix::fs::symlink(dir.path(), &alias).unwrap();
            assert!(distinct_outputs(&output, &alias.join("out.json")).is_err());
        }
        assert!(!output.exists());
        let checked = super::super::check_batch(&[dir.path().join("Missing.lean")], true);
        let changed =
            report(&checked, &[], "check", &json!({"hash":"before"}), &json!({"hash":"after"}));
        assert_eq!(changed["source_graph"]["tool_path_bytes_stable"], false);
        assert_eq!(changed["authority"], "diagnostic-only");
    }

    #[test]
    fn classification_bound_retains_unknown_identity_and_following_body() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Bound.lean");
        let binders = (0..130).map(|index| format!(" (n{index} : Nat)")).collect::<String>();
        std::fs::write(
            &input,
            format!("def tooDeep{binders} : Nat := 0\ndef following : Nat := 1"),
        )
        .unwrap();
        let checked = super::super::check_batch(&[input], true);
        assert!(checked.accepted_context().is_some());
        let measured = observe(&checked);
        let rows = measured["kernel_roster"]["declarations"].as_array().unwrap();
        let unknown = rows.iter().find(|row| row["name"] == "tooDeep").unwrap();
        assert_eq!(unknown["kernel_classification"]["kind"], "unknown");
        assert_eq!(unknown["runtime_classification"], "unmeasured");
        assert_eq!(
            rows.iter().find(|row| row["name"] == "following").unwrap()["kernel_classification"]["kind"],
            "computational-candidate"
        );
        assert_eq!(rows.len(), 2);
    }
}
