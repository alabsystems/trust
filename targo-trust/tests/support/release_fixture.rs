use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

/// A committed release candidate for CLI contracts that do not need the full checkout.
/// The real-checkout metadata test still exercises every tracked path and gitlink.
pub(crate) struct ReleaseFixture {
    _directory: tempfile::TempDir,
    root: PathBuf,
    candidate: String,
}

impl ReleaseFixture {
    pub(crate) fn new(source_root: &Path) -> Self {
        let directory = tempfile::tempdir().expect("temporary release candidate");
        let root = directory.path().join("repo");
        let control = directory.path().join("control");
        let module_source = directory.path().join("module-source");
        for path in [&root, &control.join("empty"), &module_source] {
            fs::create_dir_all(path).expect("create release fixture directories");
        }
        fs::write(control.join("config"), "").expect("write empty fixture Git config");
        let root = fs::canonicalize(root).expect("canonical release fixture root");

        // Keep the real release metadata and the shared public tool-name inventory.
        // Missing proof manifests and distribution archives remain the intentional
        // evidence failures, after valid identity and metadata collection.
        let tool_names = trust_release::default_tool_name_evidence_paths(source_root);
        assert!(!tool_names.is_empty(), "the real checkout has tool-name evidence");
        let mut paths = tool_names.iter().cloned().collect::<BTreeSet<_>>();
        for relative in [
            "Cargo.toml",
            "release/trust-version.toml",
            "release/internal-repo-versions.toml",
            "src/version",
            "src/rust-compat-version",
            "src/ci/channel",
            "src/stage0",
            "bootstrap/trust-stage0/seed-ledger.toml",
            "bootstrap/trust-stage0/dist/channel-rust-trust.toml",
            "bootstrap/trust-stage0/dist/channel-rust-trust.toml.sha256",
        ] {
            paths.insert(source_root.join(relative));
        }
        for source in paths {
            let relative = source.strip_prefix(source_root).expect("checkout-relative metadata");
            let destination = root.join(relative);
            fs::create_dir_all(destination.parent().expect("fixture file parent"))
                .expect("create fixture metadata parent");
            fs::copy(&source, destination)
                .unwrap_or_else(|error| panic!("copy {}: {error}", source.display()));
        }
        let relative_tool_names = |paths: Vec<PathBuf>, base: &Path| {
            paths
                .into_iter()
                .map(|path| path.strip_prefix(base).expect("relative tool-name path").to_path_buf())
                .collect::<Vec<_>>()
        };
        assert_eq!(
            relative_tool_names(trust_release::default_tool_name_evidence_paths(&root), &root),
            relative_tool_names(tool_names, source_root),
            "the fixture must keep the actual public tool-name inputs"
        );

        run_git(&module_source, &control, &["init", "--quiet", "--initial-branch=fixture"]);
        fs::write(module_source.join("tracked.txt"), "fixture\n").expect("write submodule fixture");
        run_git(&module_source, &control, &["add", "tracked.txt"]);
        run_git(&module_source, &control, &["commit", "--quiet", "-m", "submodule fixture"]);
        let module_head =
            run_git(&module_source, &control, &["rev-parse", "HEAD"]).trim().to_owned();

        run_git(&root, &control, &["init", "--quiet", "--initial-branch=fixture"]);
        run_git(
            &root,
            &control,
            &[
                "-c",
                "protocol.file.allow=always",
                "submodule",
                "add",
                "--quiet",
                "--",
                module_source.to_str().expect("UTF-8 fixture path"),
                "first-party/release-fixture",
            ],
        );
        run_git(&root, &control, &["add", "--all"]);
        run_git(&root, &control, &["commit", "--quiet", "-m", "release CLI fixture"]);
        assert_eq!(
            run_git(&root, &control, &["ls-tree", "HEAD", "--", "first-party/release-fixture"]),
            format!("160000 commit {module_head}\tfirst-party/release-fixture\n"),
            "the candidate must commit its real gitlink"
        );
        assert!(
            run_git(&root, &control, &["submodule", "status", "--recursive"]).starts_with(' '),
            "the committed submodule must be initialized at its pin"
        );
        let candidate = run_git(&root, &control, &["rev-parse", "HEAD"]).trim().to_owned();
        Self { _directory: directory, root, candidate }
    }

    pub(crate) fn path(&self) -> &Path {
        &self.root
    }

    pub(crate) fn assert_clean_report(&self, json: &Value) {
        assert_eq!(json["schema_version"], "trust.release-report.v1");
        assert_eq!(json["repo_root"], self.root.display().to_string());
        if cfg!(unix) {
            assert_eq!(json["candidate_commit"], self.candidate);
            assert_eq!(json["repo_dirty_metadata"]["available"], true, "{json}");
            assert_eq!(json["repo_dirty_metadata"]["dirty"], false);
            assert_eq!(json["repo_dirty"], false);
            assert!(json["repo_dirty_metadata"]["porcelain_v1"].as_array().unwrap().is_empty());
            assert_eq!(json["repo_dirty_metadata"]["untracked_files"], "all");
            assert_eq!(json["repo_dirty_metadata"]["ignore_submodules"], "none");
        } else {
            // Controlled system Git deliberately has no authority on non-Unix hosts.
            assert_eq!(json["repo_dirty_metadata"]["available"], false);
            assert_eq!(json["repo_dirty_metadata"]["dirty"], Value::Null);
            assert_eq!(json["repo_dirty"], true);
        }
        for report in json["reports"].as_array().expect("release gate reports") {
            if report["gate"] == "required-metadata" {
                assert_eq!(report["status"], "pass", "fixture metadata must be valid: {json}");
            }
            if cfg!(unix) && report["gate"] == "repository-state" {
                assert_eq!(report["status"], "pass");
            }
        }
    }

    pub(crate) fn assert_clean_terminal(&self, stdout: &str) {
        assert!(stdout.contains("- required-metadata: Pass (0 findings)"), "{stdout}");
        if cfg!(unix) {
            assert!(stdout.contains(&format!("candidate: {}", self.candidate)), "{stdout}");
            // Only RepositoryStatus::Clean produces this terminal gate result.
            assert!(stdout.contains("- repository-state: Pass (0 findings)"), "{stdout}");
        }
    }

    #[cfg(unix)]
    pub(crate) fn assert_submodule_content_is_checked(&self, binary: &Path) {
        let path = self.root.join("first-party/release-fixture/tracked.txt");
        let original = fs::read(&path).expect("read committed submodule content");
        let metadata = fs::metadata(&path).expect("submodule file metadata");
        let accessed = metadata.accessed().expect("submodule access time");
        let modified = metadata.modified().expect("submodule modification time");
        let restore_times = || {
            fs::File::options()
                .write(true)
                .open(&path)
                .expect("open submodule file for timestamps")
                .set_times(fs::FileTimes::new().set_accessed(accessed).set_modified(modified))
                .expect("restore submodule timestamps");
        };
        assert_eq!(original.len(), b"changed\n".len());
        fs::write(&path, b"changed\n").expect("replace same-size submodule content");
        restore_times();
        assert_eq!(fs::metadata(&path).unwrap().modified().unwrap(), modified);

        let changed = self.metadata_report(binary);
        assert_eq!(changed["repo_dirty"], true);
        assert_eq!(changed["repo_dirty_metadata"]["available"], false);
        assert_eq!(changed["repo_dirty_metadata"]["dirty"], Value::Null);
        let error = changed["repo_dirty_metadata"]["error"].as_str().expect("submodule error");
        assert!(
            error.contains("submodule") && error.contains("content-authoritative tracked changes"),
            "{changed}"
        );

        fs::write(&path, original).expect("restore committed submodule content");
        restore_times();
        self.assert_clean_report(&self.metadata_report(binary));
    }

    #[cfg(unix)]
    fn metadata_report(&self, binary: &Path) -> Value {
        let output = Command::new(binary)
            .args(["trust", "release", "check", "--profile=metadata", "--json", "--repo-root"])
            .arg(&self.root)
            .output()
            .expect("probe the fixture through the real release CLI");
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        assert!(output.stderr.is_empty());
        serde_json::from_slice(&output.stdout).expect("fixture release report JSON")
    }
}

// This prepares test repositories only. Every identity assertion above comes
// from the real CLI's unchanged controlled-Git collector.
fn run_git(root: &Path, control: &Path, args: &[&str]) -> String {
    let mut command = Command::new("git");
    command
        .env_clear()
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("LC_ALL", "C")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", control.join("config"))
        .env("GIT_ATTR_NOSYSTEM", "1")
        .env("GIT_AUTHOR_DATE", "2026-10-20T00:00:00Z")
        .env("GIT_COMMITTER_DATE", "2026-10-20T00:00:00Z")
        .current_dir(root)
        .args([
            "-c",
            "user.name=Trust Tests",
            "-c",
            "user.email=trust-tests@example.invalid",
            "-c",
            "commit.gpgSign=false",
            "-c",
            "core.autocrlf=false",
        ])
        .arg("-c")
        .arg(format!("init.templateDir={}", control.join("empty").display()))
        .arg("-c")
        .arg(format!("core.hooksPath={}", control.join("empty").display()))
        .arg("-c")
        .arg(format!("core.attributesFile={}", control.join("config").display()))
        .args(args);
    #[cfg(windows)]
    if let Some(system_root) = std::env::var_os("SystemRoot") {
        command.env("SystemRoot", system_root);
    }
    let output = command.output().expect("run fixture Git setup");
    assert!(
        output.status.success(),
        "fixture git {args:?} failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("UTF-8 fixture Git output")
}
