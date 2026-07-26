use std::fs;
use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

#[test]
fn version_flags_report_trust_identity() {
    let cases: &[&[&str]] = &[&["--version"], &["-V"], &["trust", "--version"]];
    for args in cases {
        let output = Command::new(targo_trust_binary())
            .args(*args)
            .output()
            .expect("run targo-trust version flag");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "version flag should succeed for {args:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(stdout.starts_with("targo-trust "));
        assert!(stdout.contains("trust.identity=targo trust"));
        assert!(stdout.contains("trust.command=targo trust"));
        let commit_rows = stdout
            .lines()
            .filter_map(|line| line.strip_prefix("trust-repo-commit-hash: "))
            .collect::<Vec<_>>();
        assert_eq!(commit_rows.len(), 1, "version output must carry one Trust repo binding");
        assert!(
            commit_rows[0] == "unbound"
                || (commit_rows[0].len() == 40
                    && commit_rows[0]
                        .bytes()
                        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))),
            "Trust repo binding must be canonical or explicitly unbound: {}",
            commit_rows[0]
        );
        assert!(stderr.is_empty(), "version output should stay on stdout");
    }
}

#[test]
fn trust_version_json_binds_distinct_tool_identities() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "version", "--format=json"])
        .output()
        .expect("run targo-trust trust version --json");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "version json should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.is_empty(), "version JSON should stay on stdout");

    let json: Value = serde_json::from_slice(&output.stdout).expect("parse version json");
    assert_eq!(json["schema_version"], "trust.version.v2");
    assert_eq!(json["product"], "Trust");
    assert_eq!(json["candidate_command"], "targo trust version --json");
    assert_eq!(json["tools"]["frontend"]["name"], "targo");
    assert_eq!(json["tools"]["extension"]["name"], "targo-trust");
    assert_eq!(json["tools"]["compiler"]["name"], "trustc");
    assert_eq!(json["tools"]["documentation"]["name"], "trustdoc");
    assert_eq!(json["tools"]["formatter"]["name"], "trustfmt");
    assert_eq!(json["tools"]["tippy"]["name"], "tippy");
    assert_eq!(json["tools"]["targo_tippy"]["name"], "targo-tippy");
    assert_eq!(json["tools"]["tippy_driver"]["name"], "tippy-driver");
    assert_eq!(json["tools"]["analyzer"]["name"], "trust-analyzer");
    assert_eq!(json["tools"]["daemon"]["name"], "trustd");
    assert_eq!(json["tools"]["miri"]["name"], "trust-miri");
    assert_eq!(json["tools"]["targo_miri"]["name"], "targo-miri");
}

#[test]
fn trust_version_text_is_product_identity_not_compat_version_flag() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "version"])
        .output()
        .expect("run targo-trust trust version");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "version text should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.starts_with("Trust "));
    assert!(stdout.contains("rust-compat:"));
    assert!(stdout.contains("targo:"));
    assert!(stdout.contains("targo-trust:"));
    assert!(stdout.contains("trustc:"));
    assert!(stdout.contains("trustdoc:"));
    assert!(stdout.contains("trustfmt:"));
    assert!(stdout.contains("tippy:"));
    assert!(stdout.contains("targo-tippy:"));
    assert!(stdout.contains("tippy-driver:"));
    assert!(stdout.contains("trust-analyzer:"));
    assert!(stdout.contains("trustd:"));
    assert!(stdout.contains("trust-miri:"));
    assert!(stdout.contains("targo-miri:"));
}

#[cfg(unix)]
#[test]
fn trust_version_json_binds_full_canonical_surface_from_one_trust_root() {
    let root = temp_test_dir("version-full-surface");
    let bin_dir = root.join("bin");
    fs::create_dir_all(&bin_dir).expect("create fake Trust bin dir");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    for tool in [
        "targo",
        "trustdoc",
        "trustfmt",
        "tippy",
        "targo-tippy",
        "tippy-driver",
        "trust-analyzer",
        "trustd",
        "trust-miri",
        "targo-miri",
    ] {
        write_version_tool(&bin_dir.join(tool), tool);
    }
    write_trustc_tool(&bin_dir.join("trustc"));

    let output = Command::new(targo_trust)
        .args(["trust", "version", "--format=json", "--repo-root"])
        .arg(repo_root())
        .output()
        .expect("run copied targo-trust trust version --json");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "version json should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let json: Value = serde_json::from_slice(&output.stdout).expect("parse version json");
    for (field, name) in [
        ("frontend", "targo"),
        ("extension", "targo-trust"),
        ("compiler", "trustc"),
        ("documentation", "trustdoc"),
        ("formatter", "trustfmt"),
        ("tippy", "tippy"),
        ("targo_tippy", "targo-tippy"),
        ("tippy_driver", "tippy-driver"),
        ("analyzer", "trust-analyzer"),
        ("daemon", "trustd"),
        ("miri", "trust-miri"),
        ("targo_miri", "targo-miri"),
    ] {
        assert_eq!(json["tools"][field]["name"], name);
        assert_eq!(json["tools"][field]["resolution"], "bound-executable");
        assert!(
            json["tools"][field]["path"].as_str().is_some_and(|path| path.contains("/bin/")),
            "tool {name} should be path-bound: {}",
            json["tools"][field]
        );
        assert!(
            json["tools"][field]["sha256"].as_str().is_some_and(|sha| sha.len() == 64),
            "tool {name} should expose sha256: {}",
            json["tools"][field]
        );
    }

    let _ = fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn trust_version_json_accepts_same_sysroot_rust_compatible_aliases() {
    let root = temp_test_dir("version-compatible-surface");
    let bin_dir = root.join("bin");
    fs::create_dir_all(&bin_dir).expect("create fake Trust bin dir");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    for tool in
        ["targo", "trustdoc", "tippy", "targo-tippy", "tippy-driver", "trust-analyzer", "trustd"]
    {
        write_version_tool(&bin_dir.join(tool), tool);
    }
    write_trustc_tool(&bin_dir.join("trustc"));
    write_version_tool(&bin_dir.join("trustfmt"), "trustfmt");
    write_version_tool(&bin_dir.join("rustfmt"), "rustfmt");

    let output = Command::new(targo_trust)
        .args(["trust", "version", "--format=json", "--repo-root"])
        .arg(repo_root())
        .output()
        .expect("run copied targo-trust trust version --json with inherited name");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "version inventory should accept same-sysroot compatibility aliases\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let json: Value = serde_json::from_slice(&output.stdout).expect("parse version json");
    let formatter = &json["tools"]["formatter"];
    assert_eq!(formatter["name"], "trustfmt");
    assert_eq!(formatter["resolution"], "bound-executable");
    assert!(
        formatter["path"].as_str().is_some_and(|path| path.ends_with("/bin/trustfmt")),
        "formatter should bind the Trust-preferred executable: {formatter}"
    );

    let _ = fs::remove_dir_all(root);
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

#[cfg(unix)]
fn install_targo_trust_binary(bin_dir: &std::path::Path) -> PathBuf {
    let path = bin_dir.join("targo-trust");
    fs::copy(targo_trust_binary(), &path).expect("copy targo-trust into fake Trust root");
    make_executable(&path);
    path
}

#[cfg(unix)]
fn write_version_tool(path: &std::path::Path, name: &str) {
    fs::write(path, format!("#!/bin/sh\necho \"{name} 1.96.0-trust\"\n"))
        .unwrap_or_else(|error| panic!("write fake tool {}: {error}", path.display()));
    make_executable(path);
}

#[cfg(unix)]
fn write_trustc_tool(path: &std::path::Path) {
    fs::write(
        path,
        "#!/bin/sh\necho \"trustc 1.96.0-trust\"\necho \"commit-hash: abcdef1234567890\"\n",
    )
    .unwrap_or_else(|error| panic!("write fake trustc {}: {error}", path.display()));
    make_executable(path);
}

#[cfg(unix)]
fn make_executable(path: &std::path::Path) {
    use std::os::unix::fs::PermissionsExt;
    let mut permissions = fs::metadata(path).expect("tool metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("chmod fake Trust tool");
}

#[cfg(unix)]
fn temp_test_dir(label: &str) -> PathBuf {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system time")
        .as_nanos();
    std::env::temp_dir().join(format!("targo-trust-{label}-{}-{unique}", std::process::id()))
}

#[cfg(unix)]
fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("targo-trust should live under repo root")
        .to_path_buf()
}
