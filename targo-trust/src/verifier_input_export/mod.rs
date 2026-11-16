// Trust: the frontend alone owns fresh verifier-input export runs.
// This output-only observation never imports evidence or changes a verdict.
use std::path::{Path, PathBuf};
use std::{fs, io};

#[path = "../../../src/tools/targo/crates/targo-core/src/util/verifier_input_export/protocol.rs"]
mod protocol;
use protocol::{
    ExportRequest, ExportUnit, PAIRED_INPUTS, REQUEST_FILE, SCHEMA, create_private_directory,
    digest, invalid, private_directory, publish_new, read_bounded,
};

const MAX_JSON_BYTES: u64 = 128 * 1024 * 1024;
const MAX_FILES: usize = 100_000;

#[cfg(test)]
#[path = "../../../src/tools/targo/crates/targo-core/src/util/verifier_input_export/mod.rs"]
mod request_reader;

/// The frontend alone creates this fresh destination. It survives every verifier exit.
pub(crate) struct ExportRun {
    directory: PathBuf,
    command: Vec<String>,
    compiler: PathBuf,
}

impl ExportRun {
    pub(crate) fn create(
        directory: &Path,
        compiler: &Path,
        command: &[String],
    ) -> io::Result<Self> {
        let name =
            directory.file_name().ok_or_else(|| invalid("export needs a new directory name"))?;
        if directory.as_os_str().is_empty()
            || directory.components().any(|c| matches!(c, std::path::Component::ParentDir))
        {
            return Err(invalid("export path must be nonempty and contain no parent traversal"));
        }
        let parent =
            directory.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
        let directory = fs::canonicalize(parent)?.join(name);
        if directory.to_str().is_none() {
            return Err(invalid("export path must be Unicode for the compiler argument transport"));
        }
        if let Some(tool_root) = compiler.parent().and_then(Path::parent) {
            if let Ok(tool_root) = tool_root.canonicalize() {
                if directory.starts_with(tool_root) {
                    return Err(invalid(
                        "export destination overlaps the selected compiler toolchain",
                    ));
                }
            }
        }
        create_private_directory(&directory)?;
        create_private_directory(&directory.join("units"))?;
        Ok(Self { directory, command: command.to_vec(), compiler: compiler.to_owned() })
    }

    pub(crate) fn bind(&self, artifact_root: &Path, session: &str) -> io::Result<()> {
        private_directory(artifact_root)?;
        private_directory(&self.directory)?;
        if !digest(session) {
            return Err(invalid("export requires the current verification session"));
        }
        let request = ExportRequest {
            schema: SCHEMA,
            session: session.to_owned(),
            directory: self.directory.clone(),
        };
        publish_new(&artifact_root.join(REQUEST_FILE), &request)?;
        publish_new(
            &self.directory.join("run.json"),
            &serde_json::json!({
                "schema": SCHEMA, "session": session, "command": self.command,
                "compiler": self.compiler, "proof_authority": false,
                "scope": "normal Cargo check primary verification units; observational output only"
            }),
        )
    }

    pub(crate) fn finish(
        &self,
        verification_succeeded: bool,
        sha256: impl Fn(&[u8]) -> String,
    ) -> io::Result<()> {
        private_directory(&self.directory)?;
        let units = self.directory.join("units");
        private_directory(&units)?;
        let mut inventory = Vec::new();
        let mut emitted = 0usize;
        let mut absent = 0usize;
        let mut excluded = 0usize;
        for entry in fs::read_dir(&units)? {
            let path = entry?.path();
            private_directory(&path)?;
            let unit: ExportUnit =
                serde_json::from_slice(&read_bounded(&path.join("unit.json"), 64 * 1024)?)
                    .map_err(invalid)?;
            if path.file_name().and_then(|n| n.to_str()) != Some(unit.unit_sha256.as_str()) {
                return Err(invalid("export unit directory differs from its declared identity"));
            }
            let selected = unit.role == "primary" && unit.verification_enabled;
            let mut sinks = serde_json::Map::new();
            for sink in ["mir", "native-bundle", PAIRED_INPUTS] {
                let mut files = Vec::new();
                if selected {
                    let dir = if sink == PAIRED_INPUTS {
                        path.join("native-bundle").join(PAIRED_INPUTS)
                    } else {
                        path.join(sink)
                    };
                    private_directory(&dir)?;
                    for artifact in fs::read_dir(&dir)? {
                        let artifact = artifact?.path();
                        // The only nested output namespace is the exact paired
                        // capture sink. It is separately inventoried below.
                        if sink == "native-bundle"
                            && artifact.file_name().is_some_and(|name| name == PAIRED_INPUTS)
                        {
                            private_directory(&artifact)?;
                            continue;
                        }
                        if files.len() >= MAX_FILES {
                            return Err(invalid("too many verifier input artifacts"));
                        }
                        if artifact.extension().and_then(|e| e.to_str()) != Some("json") {
                            return Err(invalid(
                                "unexpected file in verifier input artifact directory",
                            ));
                        }
                        let bytes = read_bounded(&artifact, MAX_JSON_BYTES)?;
                        files.push(serde_json::json!({
                            "path": artifact.strip_prefix(&self.directory).map_err(invalid)?,
                            "sha256": sha256(&bytes), "bytes": bytes.len()
                        }));
                    }
                    files.sort_by_key(|v| v["path"].as_str().unwrap_or("").to_owned());
                }
                let status = if !selected {
                    excluded += 1;
                    "excluded-unit-role"
                } else if files.is_empty() {
                    absent += 1;
                    "absent"
                } else {
                    emitted += 1;
                    "emitted"
                };
                sinks.insert(sink.to_owned(), serde_json::json!({"status":status,"files":files}));
            }
            inventory.push(serde_json::json!({"unit": unit, "sinks": sinks}));
        }
        inventory.sort_by_key(|v| v["unit"]["unit_sha256"].as_str().unwrap_or("").to_owned());
        publish_new(
            &self.directory.join("verifier-inputs.json"),
            &serde_json::json!({
                "schema": SCHEMA, "proof_authority": false,
                "verification_succeeded": verification_succeeded,
                "verification_result_changed_by_export": false,
                "census": {"emitted_sinks": emitted,"absent_sinks": absent,"refused_or_failed_absent_sinks": if verification_succeeded {0} else {absent},"excluded_sinks":excluded},
                "capture_status": if emitted == 0 {"no-artifacts-emitted"} else {"artifacts-emitted"},
                "absence": "Absence is explicit, not a capture or proof. It may mean no eligible obligations, extraction refusal, or an interrupted/failed compiler; use the unchanged verifier report for the reason.",
                "units": inventory
            }),
        )
    }

    pub(crate) fn directory(&self) -> &Path {
        &self.directory
    }
}

#[cfg(test)]
mod tests {
    use std::fs::OpenOptions;
    use std::io::Write as _;

    use super::request_reader::{ExportUnit, request, unit_args};
    use super::*;

    fn session() -> String {
        "a".repeat(64)
    }
    fn fixture() -> (tempfile::TempDir, ExportRun, PathBuf) {
        let base = tempfile::tempdir().unwrap();
        let proof = base.path().canonicalize().unwrap().join("proof");
        create_private_directory(&proof).unwrap();
        let export = ExportRun::create(
            &base.path().join("exports with spaces:one"),
            Path::new("/nonexistent-sdk/bin/trustc"),
            &["targo".into(), "check".into()],
        )
        .unwrap();
        export.bind(&proof, &session()).unwrap();
        (base, export, proof)
    }
    fn unit(role: &str) -> ExportUnit {
        ExportUnit {
            session: session(),
            unit_sha256: "b".repeat(64),
            semantics_sha256: "c".repeat(64),
            package_name: "actual-primary".into(),
            role: role.into(),
            graph_role: role.into(),
            exclusion_reason: None,
            mode: "check".into(),
            verification_enabled: true,
        }
    }
    fn manifest(export: &ExportRun) -> serde_json::Value {
        serde_json::from_slice(&fs::read(export.directory().join("verifier-inputs.json")).unwrap())
            .unwrap()
    }
    fn fingerprint(bytes: &[u8]) -> String {
        format!("test-bytes:{}", bytes.len())
    }

    #[test]
    fn export_requires_fresh_directory_and_never_overwrites_existing_files() {
        let (_base, export, _proof) = fixture();
        let marker = export.directory().join("keep");
        fs::write(&marker, b"keep").unwrap();
        assert!(ExportRun::create(export.directory(), Path::new("/none/bin/trustc"), &[]).is_err());
        assert_eq!(fs::read(marker).unwrap(), b"keep");
    }
    #[test]
    fn export_request_is_session_bound_and_unknown_authority_is_refused() {
        let (_base, _export, proof) = fixture();
        assert!(request(&proof, &"d".repeat(64)).is_err());
        let path = proof.join(REQUEST_FILE);
        let mut value: serde_json::Value =
            serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        value["trust_verify"] = serde_json::json!("off");
        fs::write(&path, serde_json::to_vec(&value).unwrap()).unwrap();
        assert!(request(&proof, &session()).is_err());
    }
    #[test]
    fn export_primary_gets_existing_flags_and_paired_sink_and_dependency_gets_neither() {
        let (_base, export, proof) = fixture();
        let req = request(&proof, &session()).unwrap().unwrap();
        let args = unit_args(&req, &unit("primary")).unwrap();
        assert_eq!(args.len(), 4);
        assert_eq!(args[0], "-Z");
        assert_eq!(args[2], "-Z");
        assert!(args[1].contains("trust-dump=mir:"));
        assert!(args[3].contains("trust-dump=native-bundle:"));
        assert!(args[1].contains("exports with spaces:one"));
        assert!(
            !args
                .iter()
                .any(|s| s.contains("mir-only") || s.contains("policy") || s.contains("verify="))
        );
        let mut dep = unit("dependency");
        dep.unit_sha256 = "d".repeat(64);
        assert!(unit_args(&req, &dep).unwrap().is_empty());
        export.finish(true, fingerprint).unwrap();
        let m = manifest(&export);
        assert_eq!(m["census"]["absent_sinks"], 3);
        assert_eq!(m["census"]["excluded_sinks"], 3);
        assert_eq!(m["capture_status"], "no-artifacts-emitted");
    }
    #[test]
    fn export_excluded_dependency_retains_graph_role_and_cannot_emit_sinks() {
        let (_base, export, proof) = fixture();
        let req = request(&proof, &session()).unwrap().unwrap();
        let mut excluded = unit("excluded");
        excluded.graph_role = "dependency".into();
        excluded.exclusion_reason = Some("dependency-policy".into());
        excluded.verification_enabled = false;
        assert!(unit_args(&req, &excluded).unwrap().is_empty());
        let mut forged = excluded;
        forged.verification_enabled = true;
        assert!(unit_args(&req, &forged).is_err());
        export.finish(false, fingerprint).unwrap();
        let m = manifest(&export);
        assert_eq!(m["units"][0]["unit"]["role"], "excluded");
        assert_eq!(m["units"][0]["unit"]["graph_role"], "dependency");
        assert_eq!(m["units"][0]["unit"]["verification_enabled"], false);
        assert_eq!(m["census"]["excluded_sinks"], 3);
        assert_eq!(m["census"]["emitted_sinks"], 0);
    }

    #[test]
    fn export_unit_identity_collision_and_unknown_role_are_refused() {
        let (_base, _export, proof) = fixture();
        let req = request(&proof, &session()).unwrap().unwrap();
        let primary = unit("primary");
        unit_args(&req, &primary).unwrap();
        assert_eq!(unit_args(&req, &primary).unwrap().len(), 4);
        let mut wrong = primary;
        wrong.package_name = "imposter".into();
        assert!(unit_args(&req, &wrong).is_err());
        let mut wrong = unit("self-asserted-primary");
        wrong.unit_sha256 = "d".repeat(64);
        assert!(unit_args(&req, &wrong).is_err());
        let mut wrong = unit("primary");
        wrong.unit_sha256 = "../other".into();
        assert!(unit_args(&req, &wrong).is_err());
    }
    #[test]
    fn export_preserves_payloads_and_failure_in_its_observational_census() {
        let (_base, export, proof) = fixture();
        let req = request(&proof, &session()).unwrap().unwrap();
        let args = unit_args(&req, &unit("primary")).unwrap();
        let mir = PathBuf::from(args[1].strip_prefix("trust-dump=mir:").unwrap())
            .join("actual-content-addressed.json");
        let payload = b"{\"def_path\":\"fixture::wrong\",\"obligations\":[\"unproved\"]}";
        let mut file = OpenOptions::new().write(true).create_new(true).open(&mir).unwrap();
        file.write_all(payload).unwrap();
        drop(file);
        export.finish(false, fingerprint).unwrap();
        let m = manifest(&export);
        assert_eq!(m["verification_succeeded"], false);
        assert_eq!(m["proof_authority"], false);
        assert_eq!(m["census"]["emitted_sinks"], 1);
        assert_eq!(m["census"]["absent_sinks"], 2);
        assert_eq!(fs::read(&mir).unwrap(), payload);
        assert!(export.finish(true, fingerprint).is_err());
        assert_eq!(manifest(&export)["verification_succeeded"], false);
    }
    #[test]
    fn export_empty_success_has_explicit_absence_and_no_capture_claim() {
        let (_base, export, _proof) = fixture();
        export.finish(true, fingerprint).unwrap();
        let m = manifest(&export);
        assert_eq!(m["capture_status"], "no-artifacts-emitted");
        assert_eq!(m["units"].as_array().unwrap().len(), 0);
        assert_eq!(m["verification_succeeded"], true);
        assert_eq!(m["proof_authority"], false);
    }
    #[test]
    fn export_censuses_paired_objects_separately_without_changing_native_bytes() {
        let (_base, export, proof) = fixture();
        let req = request(&proof, &session()).unwrap().unwrap();
        let args = unit_args(&req, &unit("primary")).unwrap();
        let native = PathBuf::from(args[3].strip_prefix("trust-dump=native-bundle:").unwrap());
        let original = b"{\"native\":\"unchanged\"}";
        fs::write(native.join("original-native.json"), original).unwrap();
        for name in ["public", "requested", "native", "pair"] {
            fs::write(native.join(PAIRED_INPUTS).join(format!("{name}.json")), b"{}").unwrap();
        }
        export.finish(false, fingerprint).unwrap();
        let m = manifest(&export);
        let sinks = &m["units"][0]["sinks"];
        assert_eq!(sinks["native-bundle"]["files"].as_array().unwrap().len(), 1);
        assert_eq!(sinks[PAIRED_INPUTS]["files"].as_array().unwrap().len(), 4);
        assert_eq!(m["census"]["emitted_sinks"], 2);
        assert_eq!(m["census"]["absent_sinks"], 1);
        assert_eq!(fs::read(native.join("original-native.json")).unwrap(), original);
        assert_eq!(m["proof_authority"], false);
    }

    #[test]
    fn export_still_rejects_all_other_nested_directories() {
        for location in [
            "mir/paired-inputs",
            "native-bundle/unexpected",
            "native-bundle/paired-inputs/nested.json",
        ] {
            let (_base, export, proof) = fixture();
            let req = request(&proof, &session()).unwrap().unwrap();
            unit_args(&req, &unit("primary")).unwrap();
            let nested =
                export.directory().join("units").join(unit("primary").unit_sha256).join(location);
            create_private_directory(&nested).unwrap();
            assert!(export.finish(false, fingerprint).is_err(), "{location}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn export_rejects_symlink_paired_directory_and_object() {
        use std::os::unix::fs::symlink;
        for directory in [true, false] {
            let (base, export, proof) = fixture();
            let req = request(&proof, &session()).unwrap().unwrap();
            let args = unit_args(&req, &unit("primary")).unwrap();
            let paired = PathBuf::from(args[3].strip_prefix("trust-dump=native-bundle:").unwrap())
                .join(PAIRED_INPUTS);
            if directory {
                fs::remove_dir(&paired).unwrap();
                let foreign = base.path().canonicalize().unwrap().join("foreign-directory");
                create_private_directory(&foreign).unwrap();
                symlink(foreign, paired).unwrap();
            } else {
                let foreign = base.path().join("foreign.json");
                fs::write(&foreign, b"{}").unwrap();
                symlink(foreign, paired.join("object.json")).unwrap();
            }
            assert!(export.finish(false, fingerprint).is_err());
        }
    }

    #[cfg(unix)]
    #[test]
    fn export_rejects_symlink_request_destination_and_artifact() {
        use std::os::unix::fs::symlink;
        let (base, export, proof) = fixture();
        let alias = base.path().join("alias");
        symlink(export.directory(), &alias).unwrap();
        assert!(ExportRun::create(&alias, Path::new("/none/bin/trustc"), &[]).is_err());
        let req = request(&proof, &session()).unwrap().unwrap();
        let args = unit_args(&req, &unit("primary")).unwrap();
        let dir = PathBuf::from(args[1].strip_prefix("trust-dump=mir:").unwrap());
        let foreign = base.path().join("foreign.json");
        fs::write(&foreign, b"{}").unwrap();
        symlink(&foreign, dir.join("foreign.json")).unwrap();
        assert!(export.finish(false, fingerprint).is_err());
        assert_eq!(fs::read(&foreign).unwrap(), b"{}");
        let request_path = proof.join(REQUEST_FILE);
        let saved = base.path().join("saved-request");
        fs::rename(&request_path, &saved).unwrap();
        symlink(&saved, &request_path).unwrap();
        assert!(request(&proof, &session()).is_err());
    }
}
