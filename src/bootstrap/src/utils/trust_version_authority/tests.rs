use super::*;

fn write(root: &Path, relative: &str, contents: &str) {
    let path = root.join(relative);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, contents).unwrap();
}

fn tree(authority: &str, targo_trust: &str) -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    write(
        root,
        AUTHORITY,
        &format!("[workspace]\nmembers = []\n\n[workspace.package]\nversion = \"{authority}\"\n"),
    );
    write(
        root,
        "targo-trust/Cargo.toml",
        &format!("[package]\nname = \"targo-trust\"\nversion = \"{targo_trust}\"\n"),
    );
    dir
}

#[test]
fn agreeing_mirrors_pass() {
    let dir = tree("0.10.0", "0.10.0");
    assert!(!dir.path().join("crates/Cargo.toml").exists());
    assert!(version_mirror_problems(dir.path(), "0.10.0").is_empty());
}

#[test]
fn every_drifted_mirror_is_named() {
    let dir = tree("0.10.0", "0.1.0");
    let problems = version_mirror_problems(dir.path(), "0.1.0");
    assert_eq!(problems.len(), 2, "{problems:?}");
    assert!(problems[0].starts_with("src/version"), "{problems:?}");
    assert!(problems[1].starts_with("targo-trust/Cargo.toml"), "{problems:?}");
}

#[test]
fn a_nonzero_patch_authority_is_refused() {
    let dir = tree("0.10.1", "0.10.1");
    let problems = version_mirror_problems(dir.path(), "0.10.1");
    assert_eq!(problems.len(), 1, "{problems:?}");
    assert!(problems[0].contains("VERSIONING.md"), "{problems:?}");
}

#[test]
fn the_checked_in_tree_agrees() {
    // The real tree, exactly as `Build::new` checks it.
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let src_version = std::fs::read_to_string(src.join("src/version")).unwrap();
    let problems = version_mirror_problems(&src, src_version.trim());
    assert!(problems.is_empty(), "{problems:?}; run `{SYNC_COMMAND}`");
}
