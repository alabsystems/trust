use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn gate_help_lists_rust_owned_repository_gates() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "gate", "--help"])
        .output()
        .expect("run gate help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("targo trust gate check-all"));
    assert!(stdout.contains("targo trust gate verify-examples"));
}

#[test]
fn gate_verify_examples_command_remains_compatible() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "gate", "verify-examples", "--help"])
        .output()
        .expect("run gate verify-examples help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "gate verify-examples should remain compatible\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("Usage: targo trust verify examples"));
}

#[test]
fn gate_scripts_runs_metadata_and_syntax_from_selected_repo_root() {
    let root = temp_test_dir("targo-trust-gate-scripts");
    let scripts = root.join("scripts");
    fs::create_dir_all(&scripts).expect("create scripts dir");
    fs::write(scripts.join("check_cargo_manifest_alignment.py"), "print('ok')\n")
        .expect("write fake manifest alignment script");
    fs::write(scripts.join("check_ledger_expirations.py"), "print('ok')\n")
        .expect("write fake ledger expiration script");
    fs::write(scripts.join("check_seed_freshness.py"), "print('ok')\n")
        .expect("write fake seed freshness script");
    fs::write(scripts.join("check_toolchain_coherence.py"), "print('ok')\n")
        .expect("write fake toolchain coherence script");
    fs::write(
        scripts.join("check_tcb_panic_freedom.sh"),
        "#!/usr/bin/env bash\nset -euo pipefail\n",
    )
    .expect("write fake TCB panic-freedom script");
    fs::write(scripts.join("check_pin_coherence.sh"), "#!/usr/bin/env bash\nset -euo pipefail\n")
        .expect("write fake pin coherence script");
    fs::write(scripts.join("check_bridge_pin.sh"), "#!/usr/bin/env bash\nset -euo pipefail\n")
        .expect("write fake bridge pin coherence script");
    fs::write(scripts.join("dev-test.sh"), "#!/usr/bin/env bash\nset -euo pipefail\n")
        .expect("write fake shell script");
    fs::write(root.join(".gitignore"), "__pycache__/\n").expect("write fixture gitignore");
    let targo_trust = root.join("targo-trust");
    fs::create_dir_all(&targo_trust).expect("create targo-trust dir");
    fs::write(targo_trust.join("Cargo.toml"), "[package]\nname='fixture'\n")
        .expect("write fake targo-trust manifest");
    let examples = root.join("examples");
    fs::create_dir_all(&examples).expect("create examples dir");
    fs::write(examples.join("verify_fake.rs"), "// Expected: BoundsCheck PROVED\nfn main() {}\n")
        .expect("write fake verifier example");
    initialize_clean_git_repo(&root);

    let output = Command::new(targo_trust_binary())
        .args(["trust", "gate", "scripts", "--repo-root", root.to_str().expect("utf-8 temp path")])
        .env("TRUST_SCRIPT_PYTHON", "python3")
        .output()
        .expect("run gate scripts");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "gate scripts should pass\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("PASS: python syntax"));
    assert!(stdout.contains("PASS: shell syntax"));
    assert!(stdout.contains("PASS: verify-example metadata"));
    assert!(stdout.contains("PASS: toolchain coherence"));
    assert!(stdout.contains("PASS: stage0 seed freshness"));
    assert!(stdout.contains("PASS: TCB panic surface within baseline"));
    assert!(stdout.contains("PASS: submodule pin coherence"));
    assert!(stdout.contains("PASS: Lean bridge pin coherence"));
    assert!(stdout.contains("PASS: repository remained clean"));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn gate_script_syntax_alias_is_removed() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "gate", "script-syntax", "--help"])
        .output()
        .expect("run removed gate script-syntax alias");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "gate script-syntax alias should be removed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "removed alias should not run help\nstdout:\n{stdout}");
    assert!(
        stderr.contains("removed alias; use `targo trust gate scripts`"),
        "gate script-syntax alias should explain the canonical command\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn gate_examples_alias_is_removed() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "gate", "examples", "--help"])
        .output()
        .expect("run removed gate examples alias");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "gate examples alias should be removed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "removed alias should not run help\nstdout:\n{stdout}");
    assert!(
        stderr.contains("removed alias; use `targo trust gate verify-examples`"),
        "gate examples alias should explain the canonical command\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// check-all binds the stage2 `trustc`/`targo` it gates with by their version
// answers. Those are files a build has just written, so on a loaded host their
// first exec waits behind macOS's machine-wide syspolicyd scan
// (docs/KNOWN_HAZARDS.md EXEC-ASSESS-STALL-1). Each stand-in answers after 15 s,
// past the old 10 s bound on any host, so the result does not depend on load; it
// is far inside the hang guard the probe now has.
#[cfg(unix)]
#[test]
fn check_all_binds_stage2_tools_whose_version_answer_comes_after_ten_seconds() {
    use std::os::unix::fs::PermissionsExt;

    let root = temp_test_dir("targo-trust-check-all-late-version-answer");
    let targo_trust = root.join("targo-trust");
    fs::create_dir_all(&targo_trust).expect("create targo-trust dir");
    fs::write(targo_trust.join("Cargo.toml"), "[package]\nname='fixture'\n")
        .expect("write fake targo-trust manifest");
    fs::write(root.join(".gitignore"), "build/\n").expect("write fixture gitignore");
    initialize_clean_git_repo(&root);
    let head = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(&root)
        .output()
        .expect("read fixture HEAD");
    assert!(head.status.success(), "fixture git rev-parse failed");
    let head = String::from_utf8(head.stdout).expect("utf-8 HEAD").trim().to_string();

    let bin = root.join("build/host/stage2/bin");
    fs::create_dir_all(&bin).expect("create stage2 bin");
    let stand_ins = [
        (
            "targo",
            "#!/bin/sh\n[ \"${1:-}\" = \"-Vv\" ] || exit 2\n/bin/sleep 15\nprintf 'targo 1.99.0-dev\\nrelease: 1.99.0-dev\\nhost: test-host\\n'\n".to_string(),
        ),
        (
            "trustc",
            format!(
                "#!/bin/sh\n[ \"${{1:-}}\" = \"-vV\" ] || exit 2\n/bin/sleep 15\nprintf 'trustc 1.99.0-dev\\ncommit-hash: {head}\\nhost: test-host\\n'\n"
            ),
        ),
    ];
    for (name, script) in &stand_ins {
        let path = bin.join(name);
        fs::write(&path, script).expect("write stage2 stand-in");
        let mut permissions = fs::metadata(&path).expect("stand-in metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&path, permissions).expect("chmod stage2 stand-in");
    }

    let started = std::time::Instant::now();
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "gate",
            "check-all",
            "--repo-root",
            root.to_str().expect("utf-8 temp path"),
            "--targo",
            bin.join("targo").to_str().expect("utf-8 stage2 path"),
        ])
        .env("TRUST_SCRIPT_PYTHON", "python3")
        .output()
        .expect("run check-all with late stage2 stand-ins");
    let elapsed = started.elapsed();

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    // The fixture has none of the scripts check-all runs next, so it ends red;
    // what this pins is that the stage2 identity was bound and the gate went on.
    assert!(
        !stderr.contains("identity probe"),
        "a late version answer must not fail the stage2 identity probe\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("=== Script syntax and verifier examples ==="),
        "check-all must reach its first step past the stage2 identity\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        elapsed >= std::time::Duration::from_secs(30),
        "both late stand-ins were probed ({elapsed:?})"
    );

    let _ = fs::remove_dir_all(&root);
}

fn initialize_clean_git_repo(repo_root: &std::path::Path) {
    for args in [
        &["init"][..],
        &["config", "user.email", "trust-tests@example.invalid"],
        &["config", "user.name", "Trust Tests"],
        &["add", "."],
        &["commit", "-m", "fixture"],
    ] {
        let output = Command::new("git")
            .args(args)
            .current_dir(repo_root)
            .output()
            .unwrap_or_else(|error| panic!("run fixture git {}: {error}", args.join(" ")));
        assert!(
            output.status.success(),
            "fixture git {} failed\nstdout:\n{}\nstderr:\n{}",
            args.join(" "),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

fn temp_test_dir(label: &str) -> PathBuf {
    let unique =
        SystemTime::now().duration_since(UNIX_EPOCH).expect("clock after epoch").as_nanos();
    std::env::temp_dir().join(format!("{label}-{}-{unique}", std::process::id()))
}

fn targo_trust_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_targo-trust") {
        return PathBuf::from(path);
    }

    let mut path = std::env::current_exe().expect("current test executable path");
    path.pop();
    if path.ends_with("deps") {
        path.pop();
    }
    path.push(format!("targo-trust{}", std::env::consts::EXE_SUFFIX));
    path
}
