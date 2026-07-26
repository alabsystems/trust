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
