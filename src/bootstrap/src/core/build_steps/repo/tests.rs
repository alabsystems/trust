use std::fs;
use std::path::Path;

use sha2::{Digest, Sha256};

use super::{add_parsed_configs, add_toolchain_inputs, validate_test_path};
use crate::utils::trust_repo_cache as cache;

// Trust: selecting a WP installation cannot silently turn a UI request into a different job.
#[test]
fn native_selection_requires_the_fixed_wp_path_and_explicit_installation() {
    use crate::utils::tests::TestCtx;
    let context = TestCtx::new();
    let config = context
        .config("test")
        .arg("--trust-repo-check")
        .arg("--trust-repo-wp-installation")
        .arg("/immutable/current-trust")
        .arg("first-party/trust-wp")
        .stage(2)
        .create_config();
    assert_eq!(
        super::selection(&config).unwrap(),
        super::Selection::Wp(Path::new("/immutable/current-trust"))
    );
    let config = context
        .config("test")
        .arg("--trust-repo-check")
        .arg("first-party/trust-wp")
        .stage(2)
        .create_config();
    assert!(super::selection(&config).is_err());
    let config = context
        .config("test")
        .arg("--trust-repo-check")
        .arg("--trust-repo-wp-installation")
        .arg("/immutable/current-trust")
        .arg("tests/ui/trust/example.rs")
        .stage(1)
        .create_config();
    assert!(super::selection(&config).is_err());
}

#[test]
fn source_alias_declaration_matches_local_and_downloaded_sysroot_stages() {
    use crate::core::build_steps::compile::sysroot_source_aliases;
    assert_eq!(sysroot_source_aliases(0, false), &["lib/rustlib/rustc-src/rust"]);
    assert_eq!(
        sysroot_source_aliases(1, false),
        &["lib/rustlib/src/rust", "lib/rustlib/rustc-src/rust"]
    );
    assert_eq!(sysroot_source_aliases(0, true), &[] as &[&str]);
    assert_eq!(sysroot_source_aliases(1, true), &["lib/rustlib/src/rust"]);
}

#[test]
fn parallel_toolchain_inputs_preserve_the_serial_identity_and_mutation_floor() {
    let root = tempfile::tempdir().unwrap();
    let tool = root.path().join("tool");
    let sysroot = root.path().join("sysroot");
    fs::write(&tool, b"non-object tool fixture").unwrap();
    fs::create_dir(&sysroot).unwrap();
    fs::write(sysroot.join("library"), b"library before").unwrap();
    let paths = [tool.clone(), sysroot.clone(), tool];
    let mut expected = Sha256::new();
    // Independently retain the old serial framing, including repeated roots.
    for path in &paths {
        let identity = if path.is_dir() {
            cache::tree_digest(path).unwrap()
        } else {
            crate::utils::trust_repo_tools::tool_digest(path).unwrap()
        };
        cache::add(&mut expected, identity);
    }
    let expected = cache::finish(expected);
    for jobs in [1, 2, 7] {
        let mut hash = Sha256::new();
        add_toolchain_inputs(&mut hash, &paths, jobs).unwrap();
        assert_eq!(cache::finish(hash), expected);
    }
    fs::write(sysroot.join("library"), b"library change").unwrap();
    let mut hash = Sha256::new();
    add_toolchain_inputs(&mut hash, &paths, 7).unwrap();
    assert_ne!(cache::finish(hash), expected);
    fs::remove_file(sysroot.join("library")).unwrap();
    fs::write(sysroot.join("different-library"), b"library before").unwrap();
    let mut hash = Sha256::new();
    add_toolchain_inputs(&mut hash, &paths, 7).unwrap();
    assert_ne!(cache::finish(hash), expected);
}

#[test]
fn parallel_dependency_inputs_preserve_order_aliases_and_required_refusals() {
    let root = tempfile::tempdir().unwrap();
    let paths = (0..3).map(|i| root.path().join(format!("package-{i}"))).collect::<Vec<_>>();
    for (i, path) in paths.iter().enumerate() {
        fs::create_dir(path).unwrap();
        fs::write(path.join("source.rs"), format!("pub const ID: u8 = {i};\n")).unwrap();
    }
    #[cfg(unix)]
    std::os::unix::fs::symlink("source.rs", paths[1].join("source-link")).unwrap();
    let expected = paths.iter().map(|path| cache::tree_digest(path).unwrap()).collect::<Vec<_>>();
    for jobs in [1, 2, 7] {
        assert_eq!(cache::hash_leaves(&paths, jobs, cache::tree_digest).unwrap(), expected);
    }
    fs::remove_file(paths[0].join("source.rs")).unwrap();
    fs::remove_dir_all(&paths[2]).unwrap();
    assert!(
        cache::hash_leaves(&paths, 7, cache::tree_digest)
            .unwrap_err()
            .contains(paths[2].to_str().unwrap())
    );
    assert!(cache::hash_leaves(&paths, 0, cache::tree_digest).is_err());
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink("missing", paths[0].join("dangling")).unwrap();
        assert!(
            cache::hash_leaves(&paths, 7, cache::tree_digest).unwrap_err().contains("dangling")
        );
    }
}

#[test]
fn config_movement_before_the_first_snapshot_is_refused() {
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("bootstrap.toml");
    let parsed = b"[rust]\ndeny-warnings = false\n";
    fs::write(&path, parsed).unwrap();
    let loaded = vec![(path.clone(), cache::bytes_digest(parsed))];
    assert!(add_parsed_configs(&mut Sha256::new(), &loaded).is_ok());
    fs::write(&path, "[rust]\ndeny-warnings = true\n").unwrap();
    let error = add_parsed_configs(&mut Sha256::new(), &loaded).unwrap_err();
    assert!(error.contains("moved after bootstrap parsed it"));
}

#[test]
fn ui_selection_is_one_existing_confined_rust_source() {
    let root = tempfile::tempdir().unwrap();
    fs::create_dir_all(root.path().join("tests/ui/trust")).unwrap();
    fs::write(root.path().join("tests/ui/trust/example.rs"), "fn main() {}").unwrap();
    assert!(validate_test_path(root.path(), Path::new("tests/ui/trust/example.rs")).is_ok());
    for path in [
        "tests/ui/trust",
        "tests/ui/trust/missing.rs",
        "tests/ui/trust/../other.rs",
        "/tmp/example.rs",
        "tests/ui/trust/example.stderr",
    ] {
        assert!(validate_test_path(root.path(), Path::new(path)).is_err(), "{path}");
    }
}
