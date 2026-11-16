//! Actual files/name replacement controls; no compiler/SDK health is fabricated.
use std::fs;
use std::os::unix::fs::symlink;

use super::*;
fn fixture() -> tempfile::TempDir {
    let temp = tempfile::tempdir().unwrap();
    fs::create_dir_all(temp.path().join("build/nested/host")).unwrap();
    temp
}
fn config(root: &Path, bytes: &str) {
    fs::write(root.join("bootstrap.toml"), bytes).unwrap();
}
#[test]
fn default_and_nested_configured_output_use_the_actual_directory() {
    let temp = fixture();
    let root = temp.path().canonicalize().unwrap();
    assert_eq!(SelectedOutput::capture(&root).unwrap().output(), root.join("build"));
    config(&root, "[build]\nbuild-dir='build/nested'\n");
    let selection = SelectedOutput::capture(&root).unwrap();
    assert_eq!(selection.output(), root.join("build/nested"));
    selection.check_current().unwrap();
    assert!(!selection.output().join("lock").exists());
}
#[test]
fn strict_parser_includes_and_profile_observe_normal_precedence() {
    let temp = fixture();
    let root = temp.path();
    fs::create_dir_all(root.join("src/bootstrap/defaults")).unwrap();
    fs::write(
        root.join("src/bootstrap/defaults/bootstrap.compiler.toml"),
        "[build]\nbuild-dir='missing-profile'\n",
    )
    .unwrap();
    fs::write(root.join("a.toml"), "[build]\nbuild-dir='missing-first'\n").unwrap();
    fs::write(root.join("b.toml"), "[build]\nbuild-dir='build/nested'\n").unwrap();
    config(root, "profile='compiler'\ninclude=['a.toml','b.toml']\n");
    assert_eq!(
        SelectedOutput::capture(root).unwrap().output(),
        root.canonicalize().unwrap().join("build/nested")
    );
    config(root, "profile='compiler'\ninclude=['b.toml']\n[build]\nbuild-dir='build'\n");
    assert_eq!(
        SelectedOutput::capture(root).unwrap().output(),
        root.canonicalize().unwrap().join("build")
    );
    config(root, "[build]\nunknown-output-selector='build'\n");
    assert!(SelectedOutput::capture(root).is_err());
    config(root, "include=['missing.toml']\n");
    assert!(SelectedOutput::capture(root).is_err()); // never default
}
#[test]
fn retained_config_rejects_changed_bytes_and_restored_original_name() {
    let temp = fixture();
    let root = temp.path();
    config(root, "[build]\nbuild-dir='build/nested'\n");
    let selection = SelectedOutput::capture(root).unwrap();
    fs::write(root.join("bootstrap.toml"), "[build]\nbuild-dir='build'\n").unwrap();
    assert!(selection.check_current().is_err());
    config(root, "[build]\nbuild-dir='build/nested'\n");
    let selection = SelectedOutput::capture(root).unwrap();
    fs::rename(root.join("bootstrap.toml"), root.join("held-config")).unwrap();
    config(root, "[build]\nbuild-dir='build'\n");
    fs::remove_file(root.join("bootstrap.toml")).unwrap();
    fs::rename(root.join("held-config"), root.join("bootstrap.toml")).unwrap();
    assert!(selection.check_current().is_err());
}
#[test]
fn retained_parent_and_output_mapping_refuse_replacements() {
    let temp = fixture();
    let root = temp.path();
    fs::create_dir(root.join("settings")).unwrap();
    fs::write(root.join("settings/build.toml"), "[build]\nbuild-dir='build/nested'\n").unwrap();
    config(root, "include=['settings/build.toml']\n");
    let selection = SelectedOutput::capture(root).unwrap();
    fs::rename(root.join("settings"), root.join("old-settings")).unwrap();
    fs::create_dir(root.join("settings")).unwrap();
    fs::write(root.join("settings/build.toml"), "[build]\nbuild-dir='build/nested'\n").unwrap();
    assert!(selection.check_current().is_err());
    fs::remove_dir_all(root.join("settings")).unwrap();
    fs::rename(root.join("old-settings"), root.join("settings")).unwrap();
    assert!(selection.check_current().is_err());
    let selection = SelectedOutput::capture(root).unwrap();
    fs::rename(root.join("build/nested"), root.join("build/old")).unwrap();
    fs::create_dir(root.join("build/nested")).unwrap();
    assert!(selection.check_current().is_err());
}
#[test]
fn absent_priority_and_legacy_config_stay_bound() {
    let temp = fixture();
    let root = temp.path();
    fs::write(root.join("config.toml"), "[build]\nbuild-dir='build/nested'\n").unwrap();
    let selection = SelectedOutput::capture(root).unwrap();
    config(root, "[build]\nbuild-dir='build'\n");
    assert!(selection.check_current().is_err());
}
#[test]
fn outside_traversal_symlink_and_config_inside_output_refuse() {
    let temp = fixture();
    let root = temp.path();
    let outside = tempfile::tempdir().unwrap();
    for value in ["../outside".to_owned(), outside.path().display().to_string(), "/".to_owned()] {
        config(root, &format!("[build]\nbuild-dir={value:?}\n"));
        assert!(SelectedOutput::capture(root).is_err(), "{value}");
    }
    symlink(root.join("build/nested"), root.join("alias")).unwrap();
    config(root, "[build]\nbuild-dir='alias'\n");
    assert!(SelectedOutput::capture(root).is_err());
    fs::write(root.join("build/inside.toml"), "[build]\nbuild-dir='build'\n").unwrap();
    config(root, "include=['build/inside.toml']\n");
    assert!(SelectedOutput::capture(root).is_err());
    fs::remove_file(root.join("bootstrap.toml")).unwrap();
    symlink(root.join("missing"), root.join("bootstrap.toml")).unwrap();
    assert!(SelectedOutput::capture(root).is_err());
}
