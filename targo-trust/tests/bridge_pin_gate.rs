#![cfg(unix)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

const MANIFEST: &str = "crates/trust-clean/fixtures/trustir-oleans/MANIFEST.toml";
const TRUSTIR_LINK: &str = "first-party/trust-ir";
const CLEAN_LINK: &str = "first-party/clean";

#[test]
fn bridge_pin_gate_uses_one_resolved_stage_zero_index_pair() {
    let root = TempRepo::new();
    let script = root.path().join("scripts/check_bridge_pin.sh");
    let pin_a = root.pin_a();
    let pin_b = root.pin_b();
    let clean_a = root.clean_a();
    let clean_b = root.clean_b();

    let initial = run(&script, root.path(), &["--check"]);
    assert_success(&initial, "matching committed pair");

    // Stage a new coherent pair, then dirty the worktree manifest back to the
    // old pin. The gate must inspect the proposed index tree, not HEAD or the
    // mutable worktree.
    git(&root.path().join(TRUSTIR_LINK), &["checkout", "--detach", pin_b]);
    stage_gitlink(root.path(), TRUSTIR_LINK, pin_b);
    write_manifest(root.path(), pin_b, clean_a);
    git(root.path(), &["add", MANIFEST]);
    write_manifest(root.path(), pin_a, clean_a);
    let staged = run(&script, root.path(), &["--check"]);
    assert_success(&staged, "coherent staged pair");
    assert!(String::from_utf8_lossy(&staged.stdout).contains(pin_b));

    // A mismatched staged manifest fails even though HEAD was coherent.
    write_manifest(root.path(), pin_a, clean_a);
    git(root.path(), &["add", MANIFEST]);
    let drift = run(&script, root.path(), &["--check"]);
    assert_failure_contains(&drift, "BRIDGE PIN DRIFT");

    // The clean side is an equal invariant, not documentation: clean supplies
    // the olean reader and the kernel the replay runs on, so its pin drifting
    // away from the manifest is the same defect as trust-ir's.
    write_manifest(root.path(), pin_b, clean_b);
    git(root.path(), &["add", MANIFEST]);
    let clean_drift = run(&script, root.path(), &["--check"]);
    assert_failure_contains(&clean_drift, "BRIDGE PIN DRIFT");
    assert_failure_contains(&clean_drift, CLEAN_LINK);

    // A manifest that records only the source end fails closed rather than
    // silently leaving the replay end unpinned.
    fs::write(
        root.path().join(MANIFEST),
        format!("schema = \"test\"\n[provenance]\ntrustir_commit = \"{pin_b}\"\n"),
    )
    .expect("write half manifest");
    git(root.path(), &["add", MANIFEST]);
    let missing = run(&script, root.path(), &["--check"]);
    assert_failure_contains(&missing, "expected exactly one clean_commit");

    // Duplicate authority is malformed, not first-match-wins.
    fs::write(
        root.path().join(MANIFEST),
        format!(
            "[provenance]\ntrustir_commit = \"{pin_b}\"\ntrustir_commit = \"{pin_b}\"\n\
             clean_commit = \"{clean_a}\"\n"
        ),
    )
    .expect("write duplicate manifest");
    git(root.path(), &["add", MANIFEST]);
    let duplicate = run(&script, root.path(), &["--check"]);
    assert_failure_contains(&duplicate, "expected exactly one trustir_commit");

    // --fix must not swallow failure to materialize the exact indexed
    // submodule. This fixture deliberately has no .gitmodules entry.
    write_manifest(root.path(), pin_a, clean_a);
    git(root.path(), &["add", MANIFEST]);
    let fix = run(&script, root.path(), &["--fix"]);
    assert!(!fix.status.success(), "--fix unexpectedly ignored submodule failure");
}

struct TempRepo {
    path: PathBuf,
    pin_a: String,
    pin_b: String,
    clean_a: String,
    clean_b: String,
}

impl TempRepo {
    fn new() -> Self {
        let unique =
            SystemTime::now().duration_since(UNIX_EPOCH).expect("clock after epoch").as_nanos();
        let path = std::env::temp_dir()
            .join(format!("trust-bridge-pin-gate-{}-{unique}", std::process::id()));
        fs::create_dir_all(path.join("scripts")).expect("create scripts dir");
        fs::create_dir_all(path.join("crates/trust-clean/fixtures/trustir-oleans"))
            .expect("create manifest dir");
        fs::write(
            path.join("scripts/check_bridge_pin.sh"),
            include_str!("../../scripts/check_bridge_pin.sh"),
        )
        .expect("copy gate script");

        git(&path, &["init"]);
        git(&path, &["config", "user.email", "trust-tests@example.invalid"]);
        git(&path, &["config", "user.name", "Trust Tests"]);

        // The hardened bridge gate requires an initialized, clean checkout at
        // the exact indexed gitlink. Use two real commits per side instead of
        // synthetic object IDs so the fixture exercises that three-way
        // invariant, on both ends of the replay.
        let (pin_a, pin_b) = seed_pinned_side(&path, TRUSTIR_LINK);
        let (clean_a, clean_b) = seed_pinned_side(&path, CLEAN_LINK);

        write_manifest(&path, &pin_a, &clean_a);
        git(&path, &["add", MANIFEST]);
        stage_gitlink(&path, TRUSTIR_LINK, &pin_a);
        stage_gitlink(&path, CLEAN_LINK, &clean_a);
        git(&path, &["commit", "-m", "fixture"]);
        Self { path, pin_a, pin_b, clean_a, clean_b }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn pin_a(&self) -> &str {
        &self.pin_a
    }

    fn pin_b(&self) -> &str {
        &self.pin_b
    }

    fn clean_a(&self) -> &str {
        &self.clean_a
    }

    fn clean_b(&self) -> &str {
        &self.clean_b
    }
}

/// Build a nested checkout at `gitlink` with two real commits, leave it
/// detached at the first, and return both commit ids.
fn seed_pinned_side(root: &Path, gitlink: &str) -> (String, String) {
    let checkout = root.join(gitlink);
    fs::create_dir_all(&checkout).expect("create nested checkout");
    git(&checkout, &["init"]);
    git(&checkout, &["config", "user.email", "trust-tests@example.invalid"]);
    git(&checkout, &["config", "user.name", "Trust Tests"]);
    fs::write(checkout.join("identity.txt"), "pin-a\n").expect("write first pin payload");
    git(&checkout, &["add", "identity.txt"]);
    git(&checkout, &["commit", "-m", "pin a"]);
    let first = git_stdout(&checkout, &["rev-parse", "HEAD"]);
    fs::write(checkout.join("identity.txt"), "pin-b\n").expect("write second pin payload");
    git(&checkout, &["add", "identity.txt"]);
    git(&checkout, &["commit", "-m", "pin b"]);
    let second = git_stdout(&checkout, &["rev-parse", "HEAD"]);
    git(&checkout, &["checkout", "--detach", &first]);
    (first, second)
}

impl Drop for TempRepo {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn write_manifest(root: &Path, pin: &str, clean_pin: &str) {
    fs::write(
        root.join(MANIFEST),
        format!(
            "schema = \"test\"\n[provenance]\ntrustir_commit = \"{pin}\"\n\
             clean_commit = \"{clean_pin}\"\n"
        ),
    )
    .expect("write manifest");
}

fn stage_gitlink(root: &Path, gitlink: &str, pin: &str) {
    git(
        root,
        &["update-index", "--add", "--cacheinfo", &format!("160000,{pin},{gitlink}")],
    );
}

fn git(root: &Path, args: &[&str]) {
    let output = Command::new("git").args(args).current_dir(root).output().expect("run git");
    assert!(
        output.status.success(),
        "git {} failed\nstdout:\n{}\nstderr:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn git_stdout(root: &Path, args: &[&str]) -> String {
    let output = Command::new("git").args(args).current_dir(root).output().expect("run git");
    assert!(
        output.status.success(),
        "git {} failed\nstdout:\n{}\nstderr:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("git stdout utf8").trim().to_owned()
}

fn run(script: &Path, root: &Path, args: &[&str]) -> Output {
    Command::new("bash")
        .arg(script)
        .args(args)
        .current_dir(root)
        .output()
        .expect("run bridge pin gate")
}

fn assert_success(output: &Output, context: &str) {
    assert!(
        output.status.success(),
        "{context} failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn assert_failure_contains(output: &Output, needle: &str) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "gate unexpectedly passed\nstdout:\n{stdout}");
    assert!(
        stdout.contains(needle) || stderr.contains(needle),
        "missing `{needle}`\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
