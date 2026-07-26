use std::fs;
use std::path::PathBuf;

#[test]
fn lintcheck_manifest_is_standalone() {
    let manifest_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("lintcheck/Cargo.toml");
    let contents = fs::read_to_string(&manifest_path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", manifest_path.display()));
    let manifest: toml::Value = toml::from_str(&contents)
        .unwrap_or_else(|error| panic!("failed to parse {}: {error}", manifest_path.display()));

    assert!(
        manifest.get("workspace").is_some(),
        "nested lintcheck must declare its own workspace so its documented standalone Cargo workflow works"
    );
}
