// Copyright 2026 Andrew Yates
use super::*;

#[test]
fn source_bytes_cover_dirty_staged_untracked_ignored_and_tarball_inputs() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    let output = temp.path().join("not-created/output");
    fs::create_dir(&source).unwrap();
    git(&source, &["init", "-q"]).unwrap();
    fs::write(source.join("tracked"), b"first").unwrap();
    fs::write(source.join(".gitignore"), b"ignored\n").unwrap();
    git(&source, &["add", "."]).unwrap();
    git(
        &source,
        &[
            "-c",
            "user.name=Source fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-qm",
            "fixture",
        ],
    )
    .unwrap();
    let observe = || own_cmake_source_digest(&source, &output).unwrap().unwrap();
    let first = observe();
    fs::write(source.join("tracked"), b"other").unwrap();
    let dirty = observe();
    assert_ne!(first, dirty);
    git(&source, &["add", "tracked"]).unwrap();
    assert_eq!(dirty, observe(), "staging identical source bytes adds no source input");
    for name in ["untracked", "ignored"] {
        fs::write(source.join(name), b"first").unwrap();
        let before = observe();
        fs::write(source.join(name), b"other").unwrap();
        assert_ne!(before, observe(), "all source entries matter: {name}");
    }
    let before = observe();
    fs::remove_dir_all(source.join(".git")).unwrap();
    assert_eq!(before, observe(), "the same tarball bytes need no Git metadata");
}

// DC-16c: the digest names the sources, not where a checkout keeps them, so another worktree's
// LLVM tree (or the one atpkg's `llvm-tree` package was built from) has the same stamp.
#[test]
fn the_same_sources_at_another_path_have_the_same_digest() {
    let temp = tempfile::tempdir().unwrap();
    let lay = |checkout: &str| {
        let source = temp.path().join(checkout).join("src/llvm-project");
        fs::create_dir_all(source.join("llvm/lib")).unwrap();
        fs::write(source.join("llvm/CMakeLists.txt"), b"project(LLVM)\n").unwrap();
        fs::write(source.join("llvm/lib/Core.cpp"), b"int core;\n").unwrap();
        std::os::unix::fs::symlink("CMakeLists.txt", source.join("llvm/Alias.txt")).unwrap();
        source
    };
    let (first, second) = (lay("first"), lay("second-worktree"));
    let digest = |source: &Path| {
        let output = source.parent().unwrap().parent().unwrap().join("build/host/llvm");
        own_cmake_source_digest(source, &output).unwrap().unwrap()
    };
    assert_eq!(digest(&first), digest(&second));
    // Where the bytes differ, the digests do.
    fs::write(second.join("llvm/lib/Core.cpp"), b"int other;\n").unwrap();
    assert_ne!(digest(&first), digest(&second));
    // A required tree still names its paths.
    assert_ne!(tree_digest(&first).unwrap(), tree_digest(&lay("third")).unwrap());
}

#[test]
fn source_output_overlap_and_unresolved_routes_refuse_without_mutation() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    fs::create_dir(&source).unwrap();
    fs::write(source.join("sentinel"), b"source").unwrap();
    for output in [&source, &source.join("nested/output"), temp.path()] {
        assert!(own_cmake_source_digest(&source, output).is_err());
    }
    assert!(own_cmake_source_digest(&source, &temp.path().join("missing/../output")).is_err());
    fs::write(temp.path().join("not-directory"), b"outside").unwrap();
    assert!(own_cmake_source_digest(&source, &temp.path().join("not-directory/output")).is_err());
    assert_eq!(fs::read(source.join("sentinel")).unwrap(), b"source");
    assert_eq!(fs::read(temp.path().join("not-directory")).unwrap(), b"outside");
    assert!(!source.join("nested").exists());
}

#[cfg(unix)]
#[test]
fn followed_links_bind_content_and_refuse_overlap_even_after_unknown_content() {
    use std::os::unix::fs::symlink;
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    let linked = temp.path().join("linked");
    let output = temp.path().join("output");
    fs::create_dir(&source).unwrap();
    fs::create_dir(&linked).unwrap();
    fs::create_dir(&output).unwrap();
    fs::write(linked.join("input"), b"first").unwrap();
    fs::write(output.join(".tpde-stamp"), b"completion").unwrap();
    fs::write(output.join("installed"), b"artifact").unwrap();
    symlink(&linked, source.join("link")).unwrap();
    let first = own_cmake_source_digest(&source, &output).unwrap().unwrap();
    fs::write(linked.join("input"), b"other").unwrap();
    assert_ne!(first, own_cmake_source_digest(&source, &output).unwrap().unwrap());
    let fifo = source.join("a-unsupported");
    let name = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes()).unwrap();
    // No reader or writer is opened: this unsupported leaf has a known namespace.
    // SAFETY: the CString owns a valid terminated pathname through this call.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    assert!(own_cmake_source_digest(&source, &output).unwrap().is_none());
    symlink(&output, source.join("z-late-output")).unwrap();
    assert!(
        own_cmake_source_digest(&source, &output).is_err(),
        "Unknown must not hide a later overlap"
    );
    assert_eq!(fs::read(output.join(".tpde-stamp")).unwrap(), b"completion");
    assert_eq!(fs::read(output.join("installed")).unwrap(), b"artifact");
    fs::remove_file(source.join("z-late-output")).unwrap();
    symlink(&source, temp.path().join("output-alias")).unwrap();
    assert!(own_cmake_source_digest(&source, &temp.path().join("output-alias")).is_err());
    assert!(own_cmake_source_digest(&source, &temp.path().join("output-alias/.")).is_err());
    symlink(&output, temp.path().join("disjoint-final-alias")).unwrap();
    assert!(
        own_cmake_source_digest(&source, &temp.path().join("disjoint-final-alias/.")).is_err(),
        "final alias refusal must not rely on a source overlap"
    );
    symlink(&output, temp.path().join("output-parent")).unwrap();
    assert!(
        own_cmake_source_digest(&source, &temp.path().join("output-parent/new")).unwrap().is_none()
    );
    symlink(source.join("absent"), source.join("dangling")).unwrap();
    assert!(
        own_cmake_source_digest(&source, &output).is_err(),
        "unresolved namespace cannot permit deletion"
    );
}

#[test]
fn namespace_change_after_walk_refuses_instead_of_returning_known_content() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    let output = temp.path().join("output");
    fs::create_dir(&source).unwrap();
    fs::create_dir(&output).unwrap();
    fs::write(source.join("input"), b"source").unwrap();
    assert!(
        own_cmake_source_digest_with_hook(&source, &output, || {
            fs::remove_dir(&output).unwrap();
            fs::write(&output, b"changed directory into a regular file").unwrap();
        })
        .is_err()
    );
    assert_eq!(fs::read(source.join("input")).unwrap(), b"source");
}

// Trust: the landing gate's audit row of trust_repo_cache.rs rests on these two
// refusals (scripts/gates/land-escape-audits.toml): under cfg(test) no root, and
// no link the walk follows, may resolve inside this checkout, whoever calls.
#[test]
#[should_panic(expected = "a unit test never hashes CMake sources in this checkout")]
fn a_unit_test_never_hashes_cmake_sources_in_this_checkout() {
    let temp = tempfile::tempdir().unwrap();
    let this_package = Path::new(env!("CARGO_MANIFEST_DIR"));
    let _ = own_cmake_source_digest(this_package, &temp.path().join("out"));
}

#[cfg(unix)]
#[test]
#[should_panic(expected = "a unit test never hashes CMake sources in this checkout")]
fn a_followed_link_never_hashes_cmake_sources_in_this_checkout() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    fs::create_dir(&source).unwrap();
    let defaults = Path::new(env!("CARGO_MANIFEST_DIR")).join("defaults");
    std::os::unix::fs::symlink(defaults, source.join("link")).unwrap();
    let _ = own_cmake_source_digest(&source, &temp.path().join("out"));
}
