#![cfg(unix)]
//! Metadata-only fixture tools never build Lean artifacts or certificates.

use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);
const LEAN: &str = "Lean (version 4.8.0, aarch64-unknown-linux-gnu, commit df668f00e6c0, Release)";
const LAKE: &str = "Lake version 5.0.0-df668f0 (Lean version 4.8.0)";

/// Admission executes and reports the canonical installation, never the spelling
/// it was handed (DECISION_QUEUE 2026-11-03), so a fixture keeps both: `root` is
/// the spelling every input is built from, `real` the same directory with every
/// symlink resolved. Expected report bytes come from `real`; `std::env::temp_dir()`
/// is not canonical on macOS (`/var/folders/...` reaches `/private/var` through
/// the `/var` symlink), BRIDGE-CLOSURE-SYMLINKED-TMPDIR-1.
struct Fixture {
    root: PathBuf,
    real: PathBuf,
    prefix: PathBuf,
}
/// A fresh, empty directory at a canonical location.
fn fresh_dir() -> PathBuf {
    let dir = fs::canonicalize(std::env::temp_dir()).unwrap().join(format!(
        "tool-admission-cli-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&dir).unwrap();
    dir
}
impl Fixture {
    /// Inputs spelled by the canonical location itself.
    fn new() -> Self {
        let real = fresh_dir();
        Self::at(real.clone(), real)
    }
    /// Inputs reach the fixture only through a symlink this test creates, so
    /// every path handed to the tool has a symlinked ancestor whatever `$TMPDIR`
    /// the runner has.
    fn behind_symlink() -> Self {
        let real = fresh_dir();
        let mut name = real.file_name().unwrap().to_os_string();
        name.push("-link");
        let root = real.with_file_name(name);
        symlink(&real, &root).unwrap();
        Self::at(root, real)
    }
    fn at(root: PathBuf, real: PathBuf) -> Self {
        let fixture = Self { prefix: root.join("tools"), root, real };
        let (root, prefix) = (&fixture.root, &fixture.prefix);
        fs::create_dir_all(prefix.join("bin")).unwrap();
        fs::create_dir_all(prefix.join("lib/lean")).unwrap();
        fs::create_dir(root.join("snapshot")).unwrap();
        fs::write(root.join("snapshot/lean-toolchain"), "leanprover/lean4:v4.8.0\n").unwrap();
        let lean = r#"#!/bin/sh
printf '%s\000%s\000' "$0" "$1" >> "$TRUST_FIXTURE_CALLS"
case "$1" in
  --version) printf '%s\n' "$TRUST_FIXTURE_LEAN" ;;
  --print-prefix) printf '%s\n' "$TRUST_FIXTURE_PREFIX" ;;
  *) exit 97 ;;
esac
if [ -n "$TRUST_FIXTURE_DIAGNOSTIC" ]; then printf '%s\n' "$TRUST_FIXTURE_DIAGNOSTIC" >&2; fi
exit "${TRUST_FIXTURE_LEAN_EXIT:-0}"
"#;
        let lake = r#"#!/bin/sh
printf '%s\000%s\000' "$0" "$1" >> "$TRUST_FIXTURE_CALLS"
case "$1" in
  --version) printf '%s\n' "$TRUST_FIXTURE_LAKE" ;;
  *) exit 97 ;;
esac
"#;
        for (name, script) in [("lean", lean), ("lake", lake)] {
            let path = prefix.join("bin").join(name);
            fs::write(&path, script).unwrap();
            fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
        }
        fixture
    }
    /// `prefix` at its canonical location: the installation admission reports.
    fn real_prefix(&self) -> PathBuf {
        self.real.join(self.prefix.strip_prefix(&self.root).unwrap())
    }
    fn report(&self) -> PathBuf {
        self.root.join("readback")
    }
    fn command(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_bridge_closure"));
        command
            .arg("--admit-lean-toolchain")
            .arg(self.root.join("snapshot"))
            .arg(self.prefix.join("bin"))
            .arg(self.report())
            .env("TRUST_FIXTURE_LEAN", LEAN)
            .env("TRUST_FIXTURE_LAKE", LAKE)
            .env("TRUST_FIXTURE_PREFIX", &self.prefix)
            .env("TRUST_FIXTURE_CALLS", self.root.join("calls"));
        command
    }
    fn fields(&self) -> Vec<Vec<u8>> {
        fs::read(self.report()).unwrap().split(|b| *b == 0).map(<[u8]>::to_vec).collect()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        if self.root != self.real {
            // The link itself; `remove_dir_all` does not follow it.
            fs::remove_file(&self.root).unwrap();
        }
        fs::remove_dir_all(&self.real).unwrap();
    }
}
fn success(output: Output) {
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert!(output.stdout.is_empty());
}
fn refusal(output: Output, reason: &str) {
    assert_eq!(output.status.code(), Some(1), "{}", String::from_utf8_lossy(&output.stderr));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains(reason));
}

#[test]
fn queries_selected_tools_and_preserves_their_actual_host() {
    let fixture = Fixture::new();
    success(fixture.command().env("PATH", "").output().unwrap());
    let fields = fixture.fields();
    assert_eq!(fields.len(), 7);
    assert_eq!(fields[0], b"trust.lean-toolchain-readback.v1");
    assert_eq!(fields[1], b"aarch64-unknown-linux-gnu");
    assert_eq!(fields[2], b"leanprover/lean4:v4.8.0");
    assert_eq!(fields[3], LEAN.as_bytes());
    assert_eq!(fields[4], fixture.real_prefix().join("bin").as_os_str().as_encoded_bytes());
    assert_eq!(fields[5], fixture.real_prefix().join("lib/lean").as_os_str().as_encoded_bytes());
    assert!(fields[6].is_empty());
    let calls = fs::read(fixture.root.join("calls")).unwrap();
    let calls: Vec<_> = calls.split(|b| *b == 0).collect();
    assert_eq!(calls.len(), 7);
    assert_eq!(calls[0], fixture.real_prefix().join("bin/lean").as_os_str().as_encoded_bytes());
    assert_eq!(calls[1], b"--version");
    assert_eq!(calls[3], b"--print-prefix");
    assert_eq!(calls[4], fixture.real_prefix().join("bin/lake").as_os_str().as_encoded_bytes());
    assert_eq!(calls[5], b"--version");
    assert_eq!(fs::metadata(fixture.report()).unwrap().permissions().mode() & 0o777, 0o600);
}

#[test]
fn newer_versions_wrong_commits_and_help_looking_reports_refuse() {
    let fixture = Fixture::new();
    for (lean, lake) in [
        (LEAN.replace("4.8.0", "4.33.0"), LAKE.replace("4.8.0", "4.33.0")),
        (LEAN.into(), LAKE.replace("df668f0", "abcdef0")),
        ("--help".into(), LAKE.into()),
        (format!("{LEAN}\nforged"), LAKE.into()),
    ] {
        let output = fixture
            .command()
            .env("TRUST_FIXTURE_LEAN", lean)
            .env("TRUST_FIXTURE_LAKE", lake)
            .output()
            .unwrap();
        refusal(output, "toolchain admission failed");
        assert!(!fixture.report().exists());
    }
}

#[test]
fn prefix_mismatch_missing_core_and_query_failure_leave_no_report() {
    let fixture = Fixture::new();
    let foreign = fixture.root.join("foreign");
    fs::create_dir_all(foreign.join("bin")).unwrap();
    refusal(
        fixture.command().env("TRUST_FIXTURE_PREFIX", &foreign).output().unwrap(),
        "reported prefix",
    );
    fs::remove_dir(fixture.prefix.join("lib/lean")).unwrap();
    refusal(fixture.command().output().unwrap(), "core olean directory");
    fs::write(fixture.prefix.join("bin/lean"), "#!/bin/sh\nexit 23\n").unwrap();
    refusal(fixture.command().output().unwrap(), "failed");
    assert!(!fixture.report().exists());
}

#[test]
fn moved_and_symlinked_bins_keep_exact_path_data_with_newlines() {
    let mut fixture = Fixture::new();
    use std::os::unix::ffi::OsStringExt;
    let name = b"moved tools\n$(touch injected)".to_vec();
    #[cfg(target_os = "linux")]
    let name = [name.as_slice(), &[0xff]].concat();
    let moved = fixture.root.join(std::ffi::OsString::from_vec(name));
    fs::rename(&fixture.prefix, &moved).unwrap();
    fixture.prefix = moved;
    let alias = fixture.root.join("bin-alias");
    symlink(fixture.prefix.join("bin"), &alias).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_bridge_closure"))
        .arg("--admit-lean-toolchain")
        .arg(fixture.root.join("snapshot"))
        .arg(&alias)
        .arg(fixture.report())
        .env("TRUST_FIXTURE_LEAN", LEAN)
        .env("TRUST_FIXTURE_LAKE", LAKE)
        .env("TRUST_FIXTURE_PREFIX", &fixture.prefix)
        .env("TRUST_FIXTURE_CALLS", fixture.root.join("calls"))
        .output()
        .unwrap();
    success(output);
    assert_eq!(
        fixture.fields()[4],
        fixture.real_prefix().join("bin").as_os_str().as_encoded_bytes()
    );
    assert!(!fixture.root.join("injected").exists());
}

/// BRIDGE-CLOSURE-SYMLINKED-TMPDIR-1: the snapshot, the selected bin, the
/// prefix Lean reports and the report path all reach the installation through a
/// symlinked ancestor, as they do under macOS's default `$TMPDIR`. Admission
/// still executes and reports the canonical installation, byte for byte.
#[test]
fn symlinked_ancestor_reports_and_runs_the_canonical_installation() {
    let fixture = Fixture::behind_symlink();
    // The inputs' spelling really differs from the canonical one, so an
    // expectation spelled from the inputs cannot pass.
    assert_ne!(fixture.prefix, fixture.real_prefix());
    success(fixture.command().env("PATH", "").output().unwrap());
    let real = fixture.real_prefix();
    let fields = fixture.fields();
    assert_eq!(fields.len(), 7);
    assert_eq!(fields[4], real.join("bin").as_os_str().as_encoded_bytes());
    assert_eq!(fields[5], real.join("lib/lean").as_os_str().as_encoded_bytes());
    assert!(fields[6].is_empty());
    let calls = fs::read(fixture.root.join("calls")).unwrap();
    let calls: Vec<_> = calls.split(|b| *b == 0).collect();
    assert_eq!(calls.len(), 7);
    assert_eq!(calls[0], real.join("bin/lean").as_os_str().as_encoded_bytes());
    assert_eq!(calls[2], real.join("bin/lean").as_os_str().as_encoded_bytes());
    assert_eq!(calls[4], real.join("bin/lake").as_os_str().as_encoded_bytes());
}

#[test]
fn existing_output_is_preserved_and_bad_pin_does_not_execute_tools() {
    let fixture = Fixture::new();
    fs::write(fixture.report(), b"keep existing output").unwrap();
    refusal(fixture.command().output().unwrap(), "exists");
    assert_eq!(fs::read(fixture.report()).unwrap(), b"keep existing output");
    fs::remove_file(fixture.root.join("calls")).unwrap();
    fs::write(fixture.root.join("snapshot/lean-toolchain"), "leanprover/lean4:nightly\n").unwrap();
    refusal(fixture.command().output().unwrap(), "unrecognized");
    assert!(!fixture.root.join("calls").exists());
    assert_eq!(fs::read(fixture.report()).unwrap(), b"keep existing output");
}

#[test]
fn query_status_stderr_and_byte_errors_cannot_become_admission() {
    let fixture = Fixture::new();
    refusal(fixture.command().env("TRUST_FIXTURE_LEAN_EXIT", "23").output().unwrap(), "failed");
    assert!(!fixture.report().exists());
    let output =
        fixture.command().env("TRUST_FIXTURE_DIAGNOSTIC", "tool diagnostic").output().unwrap();
    assert!(String::from_utf8_lossy(&output.stderr).contains("tool diagnostic"));
    success(output);
    fs::remove_file(fixture.report()).unwrap();
    refusal(
        fixture.command().env("TRUST_FIXTURE_PREFIX", "relative-prefix").output().unwrap(),
        "absolute prefix",
    );
    assert!(!fixture.report().exists());
    fs::write(fixture.prefix.join("bin/lean"), "#!/bin/sh\ncase \"$1\" in\n--version) printf '\\377\\n' ;;\n--print-prefix) printf '%s\\n' \"$TRUST_FIXTURE_PREFIX\" ;;\nesac\n").unwrap();
    refusal(fixture.command().output().unwrap(), "not UTF-8");
    assert!(!fixture.report().exists());
}

#[test]
fn pin_file_newlines_are_only_removed_at_the_end() {
    let fixture = Fixture::new();
    for bytes in [
        b"".as_slice(),
        b"leanprover/lean4:v4.8.0 \n",
        b"leanprover/lean4:v4.8.0\r\n",
        b"leanprover/lean4:v4.8.0\nforged\n",
    ] {
        fs::write(fixture.root.join("snapshot/lean-toolchain"), bytes).unwrap();
        refusal(fixture.command().output().unwrap(), "unrecognized");
        assert!(!fixture.report().exists());
    }
    for bytes in [b"leanprover/lean4:v4.8.0".as_slice(), b"leanprover/lean4:v4.8.0\n\n"] {
        fs::write(fixture.root.join("snapshot/lean-toolchain"), bytes).unwrap();
        success(fixture.command().output().unwrap());
        fs::remove_file(fixture.report()).unwrap();
    }
    fs::remove_file(fixture.root.join("snapshot/lean-toolchain")).unwrap();
    refusal(fixture.command().output().unwrap(), "toolchain admission failed");
}
