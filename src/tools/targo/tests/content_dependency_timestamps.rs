//! Same-byte dependency restoration defers only covered edges to checksum checks.

use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::{Duration, SystemTime};

#[expect(
    clippy::disallowed_methods,
    reason = "isolated native consumer uses the explicitly selected compiler and normal PATH"
)]
fn build(root: &Path) -> Vec<serde_json::Value> {
    let output = Command::new(env!("CARGO_BIN_EXE_targo"))
        .env_clear()
        .env("HOME", root)
        .env("CARGO_HOME", root.join("home"))
        .env("CARGO_TARGET_DIR", root.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("explicit compiler"),
        )
        .current_dir(root)
        .args([
            "--unverified",
            "build",
            "--offline",
            "--lib",
            "-j1",
            "--message-format=json",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter(|row| row["reason"] == "compiler-artifact")
        .collect()
}

fn artifact<'a>(rows: &'a [serde_json::Value], name: &str) -> &'a serde_json::Value {
    rows.iter()
        .find(|row| row["target"]["name"] == name)
        .unwrap()
}

#[test]
fn covered_same_bytes_stay_fresh_but_changed_source_and_damaged_outputs_do_not() {
    let temp = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let root = temp.path();
    fs::create_dir_all(root.join("src")).unwrap();
    fs::create_dir_all(root.join("dep/src")).unwrap();
    fs::write(root.join("Cargo.toml"), "[package]\nname='parent'\nversion='0.0.0'\nedition='2021'\n[dependencies]\ndep={path='dep'}\n[workspace]\n").unwrap();
    fs::write(
        root.join("src/lib.rs"),
        "pub fn answer()->u32{dep::answer()}\n",
    )
    .unwrap();
    fs::write(
        root.join("dep/Cargo.toml"),
        "[package]\nname='dep'\nversion='0.0.0'\nedition='2021'\n",
    )
    .unwrap();
    fs::write(root.join("dep/src/lib.rs"), "pub fn answer()->u32{42}\n").unwrap();
    let first = build(root);
    assert_eq!(artifact(&first, "parent")["fresh"], false);
    let files = artifact(&first, "dep")["filenames"].as_array().unwrap();
    let archives: Vec<_> = files
        .iter()
        .filter_map(|v| v.as_str())
        .filter(|p| p.ends_with(".rlib") || p.ends_with(".rmeta"))
        .collect();
    assert!(!archives.is_empty());
    let later = filetime::FileTime::from_system_time(SystemTime::now() + Duration::from_secs(2));
    for path in &archives {
        let before = fs::read(path).unwrap();
        filetime::set_file_mtime(path, later).unwrap();
        assert_eq!(fs::read(path).unwrap(), before);
    }
    let restored = build(root);
    assert_eq!(artifact(&restored, "dep")["fresh"], true);
    assert_eq!(
        artifact(&restored, "parent")["fresh"],
        true,
        "a covered timestamp is not a byte change"
    );

    // Missing read-set coverage cannot acquire the timestamp exception.
    let records: Vec<_> = walkdir::WalkDir::new(root.join("target"))
        .into_iter()
        .map(Result::unwrap)
        .filter(|entry| entry.file_type().is_file() && entry.file_name() == "dep-lib-parent")
        .map(|entry| entry.into_path())
        .collect();
    assert_eq!(records.len(), 1, "one actual parent read-set");
    fs::remove_file(&records[0]).unwrap();
    let missing = build(root);
    assert_eq!(artifact(&missing, "parent")["fresh"], false);

    fs::write(root.join("dep/src/lib.rs"), "pub fn answer()->u32{43}\n").unwrap();
    let changed = build(root);
    assert_eq!(artifact(&changed, "dep")["fresh"], false);
    assert_eq!(artifact(&changed, "parent")["fresh"], false);

    let archive = artifact(&changed, "dep")["filenames"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|v| v.as_str())
        .find(|p| p.ends_with(".rlib"))
        .unwrap();
    let mut damaged = fs::read(archive).unwrap();
    damaged[0] ^= 1;
    fs::write(archive, damaged).unwrap();
    let repaired = build(root);
    assert_eq!(
        artifact(&repaired, "dep")["fresh"],
        false,
        "timestamp optimization cannot bypass output integrity"
    );
}
