#![cfg(unix)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
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

/// 2026-09-24: the gate used to compare commit STRINGS only, so a regeneration on
/// one platform could carry another platform's bytes forward under the new
/// trustir_commit and still read "BRIDGE PIN OK". It now checks every listed
/// olean's staged bytes against its recorded sha256 and every platform table's
/// `built_from_trustir_commit`.
#[test]
fn bridge_pin_gate_checks_staged_digests_and_platform_provenance() {
    const GOOD: &str = "08906a08609317ddac2911bfb05f373157bb266bfc2c051329fb30fcb2f1144a";
    let root = TempRepo::new();
    let script = root.path().join("scripts/check_bridge_pin.sh");
    let (pin, clean) = (root.pin_a().to_owned(), root.clean_a().to_owned());
    let dir = root.path().join("crates/trust-clean/fixtures/trustir-oleans");
    let stage_olean = |rel: &str, bytes: &str| {
        let path = dir.join(rel);
        fs::create_dir_all(path.parent().expect("olean parent")).expect("create olean dir");
        fs::write(&path, bytes).expect("write olean");
        git(root.path(), &["add", "-f", path.to_str().expect("utf8 path")]);
    };
    let stage_manifest = |platforms: &str| {
        fs::write(
            root.path().join(MANIFEST),
            format!(
                "schema = \"test\"\n[provenance]\ntrustir_commit = \"{pin}\"\n\
                 clean_commit = \"{clean}\"\n[files]\n\"TrustIr/A.olean\" = \"{GOOD}\"\n\
                 {platforms}"
            ),
        )
        .expect("write manifest");
        git(root.path(), &["add", MANIFEST]);
    };
    let other = "b".repeat(40);

    stage_olean("TrustIr/A.olean", "good olean bytes\n");
    stage_olean("platform/x-linux/TrustIr/B.olean", "good olean bytes\n");
    let current_and_stale = format!(
        "[platforms.\"x-darwin\"]\nbuilt_from_trustir_commit = \"{pin}\"\n\
         [platforms.\"x-linux\"]\nbuilt_from_trustir_commit = \"{other}\"\n\
         [platforms.\"x-linux\".files]\n\"TrustIr/B.olean\" = \"{GOOD}\"\n"
    );
    stage_manifest(&current_and_stale);
    let ok = run(&script, root.path(), &["--check"]);
    assert_success(&ok, "matching digests, one current platform");
    let stdout = String::from_utf8_lossy(&ok.stdout);
    assert!(stdout.contains("2 staged olean digest(s) match"), "{stdout}");
    assert!(stdout.contains("BRIDGE PLATFORM STALE (disclosed): x-linux"), "{stdout}");

    // Bytes that no longer hash to the manifest fail, shared or per-platform.
    stage_olean("platform/x-linux/TrustIr/B.olean", "tampered bytes\n");
    assert_failure_contains(&run(&script, root.path(), &["--check"]), "BRIDGE DIGEST MISMATCH");
    stage_olean("platform/x-linux/TrustIr/B.olean", "good olean bytes\n");

    // A listed olean that is not staged at all fails.
    git(
        root.path(),
        &["rm", "--cached", "-q", "crates/trust-clean/fixtures/trustir-oleans/TrustIr/A.olean"],
    );
    assert_failure_contains(&run(&script, root.path(), &["--check"]), "BRIDGE DIGEST MISSING");
    stage_olean("TrustIr/A.olean", "good olean bytes\n");

    // A platform that does not say what it was built from fails.
    stage_manifest("[platforms.\"x-darwin\"]\n");
    assert_failure_contains(
        &run(&script, root.path(), &["--check"]),
        "BRIDGE PLATFORM PROVENANCE MISSING",
    );

    // No platform built from trustir_commit: the manifest names a revision no
    // vendored byte came from.
    stage_manifest(&format!("[platforms.\"x-linux\"]\nbuilt_from_trustir_commit = \"{other}\"\n"));
    assert_failure_contains(
        &run(&script, root.path(), &["--check"]),
        "no platform's bytes were built from trustir_commit",
    );
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
        // The clock alone is not a unique key: with a microsecond clock two tests
        // starting together can pick the same directory (observed once, when this
        // file gained its second test: a parallel run failed inside this fixture's
        // git setup, and the failure did not reproduce serially). A process-wide
        // counter makes the directory unique by construction.
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let unique =
            SystemTime::now().duration_since(UNIX_EPOCH).expect("clock after epoch").as_nanos();
        let serial = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir()
            .join(format!("trust-bridge-pin-gate-{}-{unique}-{serial}", std::process::id()));
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
    git(root, &["update-index", "--add", "--cacheinfo", &format!("160000,{pin},{gitlink}")]);
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
