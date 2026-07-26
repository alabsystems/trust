use super::*;

#[test]
fn private_sysroot_identity_uses_the_full_compiler_commit() {
    let version = "rustc 1.99.0-nightly (012345678 2026-07-19)\n\
binary: rustc\n\
commit-hash: 0123456789abcdef0123456789abcdef01234567\n\
host: aarch64-apple-darwin\n";

    assert_eq!(
        rustc_commit_hash_from_verbose_version(version),
        Some("0123456789abcdef0123456789abcdef01234567")
    );
    assert_eq!(rustc_commit_hash_from_verbose_version("commit-hash: \n"), None);
    assert_eq!(rustc_commit_hash_from_verbose_version("release: nightly\n"), None);

    let stamp_path = Path::new("build/aarch64-apple-darwin/stage1-rustc/.librustc.stamp");
    let first = rustc_private_sysroot_key_from_entries(
        stamp_path,
        Some("0123456789abcdef0123456789abcdef01234567"),
        Vec::new(),
        None,
        None,
    );
    let repeated = rustc_private_sysroot_key_from_entries(
        stamp_path,
        Some("0123456789abcdef0123456789abcdef01234567"),
        Vec::new(),
        None,
        None,
    );
    let second = rustc_private_sysroot_key_from_entries(
        stamp_path,
        Some("fedcba9876543210fedcba9876543210fedcba98"),
        Vec::new(),
        None,
        None,
    );

    assert_eq!(first, repeated, "the same compiler identity must reuse its private sysroot");
    assert_ne!(first, second, "a different compiler commit must select a different sysroot");
}

#[test]
fn private_sysroot_identity_tracks_in_place_runtime_dylib_rebuilds() {
    let temp = tempfile::TempDir::new().unwrap();
    let runtime = temp.path().join("librustc_driver-same-disambiguator.so");
    fs::write(&runtime, b"runtime-generation-one").unwrap();

    let first_runtime_identity = rustc_private_runtime_dylib_identity(vec![runtime.clone()]);
    let first_sysroot_identity = rustc_private_sysroot_key_from_entries(
        Path::new("build/host/stage1-rustc/.librustc.stamp"),
        Some("unchanged-compiler-commit"),
        vec![(runtime.clone(), DependencyType::Target)],
        Some(&first_runtime_identity),
        None,
    );

    // Keep the path, stamp entry, commit, and byte length fixed. Only the
    // runtime's actual content changes, matching an in-place stage rebuild.
    fs::write(&runtime, b"runtime-generation-two").unwrap();
    let second_runtime_identity = rustc_private_runtime_dylib_identity(vec![runtime.clone()]);
    let second_sysroot_identity = rustc_private_sysroot_key_from_entries(
        Path::new("build/host/stage1-rustc/.librustc.stamp"),
        Some("unchanged-compiler-commit"),
        vec![(runtime, DependencyType::Target)],
        Some(&second_runtime_identity),
        None,
    );

    assert_ne!(first_runtime_identity, second_runtime_identity);
    assert_ne!(
        first_sysroot_identity, second_sysroot_identity,
        "changed runtime bytes must change Cargo's private-sysroot search path"
    );
}

#[test]
fn private_sysroot_identity_tracks_in_place_copied_std_rebuilds() {
    let temp = tempfile::TempDir::new().unwrap();
    let std_artifact = temp.path().join("libcore-same-disambiguator.rlib");
    fs::write(&std_artifact, b"copied-std-generation-one").unwrap();

    let first_std_identity = rustc_private_copied_std_identity(vec![std_artifact.clone()]);
    let first_sysroot_identity = rustc_private_sysroot_key_from_entries(
        Path::new("build/host/stage1-rustc/.librustc.stamp"),
        Some("unchanged-compiler-commit"),
        Vec::new(),
        None,
        Some(&first_std_identity),
    );

    fs::write(&std_artifact, b"copied-std-generation-two").unwrap();
    let second_std_identity = rustc_private_copied_std_identity(vec![std_artifact]);
    let second_sysroot_identity = rustc_private_sysroot_key_from_entries(
        Path::new("build/host/stage1-rustc/.librustc.stamp"),
        Some("unchanged-compiler-commit"),
        Vec::new(),
        None,
        Some(&second_std_identity),
    );

    assert_ne!(first_std_identity, second_std_identity);
    assert_ne!(
        first_sysroot_identity, second_sysroot_identity,
        "changed copied std bytes must select a fresh nested-driver sysroot"
    );
}

#[test]
fn narrow_trust_cg_self_host_boundary_is_stage_and_backend_exact() {
    assert!(!staged_narrow_trust_cg_cannot_self_host(0, false, &CodegenBackendKind::TrustCg,));
    assert!(staged_narrow_trust_cg_cannot_self_host(0, true, &CodegenBackendKind::TrustCg,));
    assert!(staged_narrow_trust_cg_cannot_self_host(1, false, &CodegenBackendKind::TrustCg,));
    assert!(staged_narrow_trust_cg_cannot_self_host(2, false, &CodegenBackendKind::TrustCg,));
    assert!(!staged_narrow_trust_cg_cannot_self_host(2, false, &CodegenBackendKind::Llvm,));

    let error = narrow_trust_cg_self_host_error("the standard library");
    assert!(error.contains("External scalar-register functions"));
    assert!(error.contains("codegen-backends = [\"llvm\", \"trust-cg\"]"));
    assert!(error.contains("LLVM first"));
}

#[test]
fn trust_cg_builtin_selector_considers_every_configured_host() {
    let all_disabled =
        [vec![CodegenBackendKind::Llvm], vec![CodegenBackendKind::Custom("other".into())]];
    assert!(!trust_cg_builtin_enabled_for_any_host(all_disabled.iter().map(Vec::as_slice)));
    assert!(!trust_cg_builtin_enabled_for_host(&all_disabled[0]));
    assert!(!trust_cg_builtin_enabled_for_host(&all_disabled[1]));

    let cross_host_only = [
        vec![CodegenBackendKind::Llvm],
        vec![CodegenBackendKind::TrustCg, CodegenBackendKind::Llvm],
    ];
    assert!(trust_cg_builtin_enabled_for_any_host(cross_host_only.iter().map(Vec::as_slice)));
    assert!(
        !trust_cg_builtin_enabled_for_host(&cross_host_only[0]),
        "a globally registered selector must still skip a host where trust-cg is disabled"
    );
    assert!(trust_cg_builtin_enabled_for_host(&cross_host_only[1]));
}

#[test]
fn preserve_metadata_mode_prunes_stale_metadata_when_rlib_is_installed() {
    let temp = tempfile::TempDir::new().unwrap();
    let sysroot = temp.path();
    fs::write(sysroot.join("libfoo-old.rmeta"), b"stale metadata").unwrap();
    fs::write(sysroot.join("libfoo-new.rmeta"), b"active metadata").unwrap();

    let active_rlib =
        RustArtifact { crate_name: "foo", stem: "libfoo-new", kind: RustArtifactKind::Rlib };

    assert!(prepare_sysroot_artifact_for_copy(
        Path::new("libfoo-new.rlib"),
        sysroot,
        active_rlib,
        SysrootMetadataMode::PreserveMetadataOnlyDeps,
        &HashSet::new(),
    ));

    assert!(sysroot.join("libfoo-new.rmeta").exists());
    assert!(!sysroot.join("libfoo-old.rmeta").exists());
}

#[test]
fn preserve_metadata_mode_keeps_metadata_only_deps_with_existing_rlib() {
    let temp = tempfile::TempDir::new().unwrap();
    let sysroot = temp.path();
    fs::write(sysroot.join("libbar-old.rlib"), b"existing rlib").unwrap();

    let metadata_only_dep =
        RustArtifact { crate_name: "bar", stem: "libbar-new", kind: RustArtifactKind::Rmeta };

    assert!(prepare_sysroot_artifact_for_copy(
        Path::new("libbar-new.rmeta"),
        sysroot,
        metadata_only_dep,
        SysrootMetadataMode::PreserveMetadataOnlyDeps,
        &HashSet::new(),
    ));
}

#[test]
fn public_sysroot_prune_removes_private_and_metadata_only_artifacts() {
    let temp = tempfile::TempDir::new().unwrap();
    let sysroot = temp.path();
    fs::write(sysroot.join("librustc_middle-111.rlib"), b"private rlib").unwrap();
    fs::write(sysroot.join("librustc_middle-111.rmeta"), b"private metadata").unwrap();
    fs::write(sysroot.join("libserde-222.rmeta"), b"metadata-only dep").unwrap();
    fs::write(sysroot.join("libserde_derive-333.so"), b"private proc macro").unwrap();
    fs::write(sysroot.join("libhashbrown-444.rlib"), b"public unstable dep").unwrap();
    fs::write(sysroot.join("libhashbrown-444.rmeta"), b"public unstable metadata").unwrap();
    fs::write(sysroot.join("libstd-555.so"), b"public std dylib").unwrap();
    fs::write(sysroot.join("libstd-555.rmeta"), b"public std metadata").unwrap();

    prune_public_sysroot_compiler_artifacts(sysroot);

    assert!(!sysroot.join("librustc_middle-111.rlib").exists());
    assert!(!sysroot.join("librustc_middle-111.rmeta").exists());
    assert!(!sysroot.join("libserde-222.rmeta").exists());
    assert!(!sysroot.join("libserde_derive-333.so").exists());
    assert!(sysroot.join("libhashbrown-444.rlib").exists());
    assert!(sysroot.join("libhashbrown-444.rmeta").exists());
    assert!(sysroot.join("libstd-555.so").exists());
    assert!(sysroot.join("libstd-555.rmeta").exists());
}

#[test]
fn local_compiler_runtime_artifacts_are_target_dylibs_or_debug_info() {
    assert!(is_local_compiler_runtime_artifact(
        Path::new("librustc_driver-1234.dylib"),
        DependencyType::Target,
    ));
    assert!(is_local_compiler_runtime_artifact(
        Path::new("rustc_driver.pdb"),
        DependencyType::Target,
    ));
    assert!(!is_local_compiler_runtime_artifact(
        Path::new("libproc_macro_helper-1234.dylib"),
        DependencyType::Host,
    ));
    assert!(!is_local_compiler_runtime_artifact(
        Path::new("librustc_driver-1234.rmeta"),
        DependencyType::Target,
    ));
}

#[test]
fn local_compiler_runtime_artifacts_skip_missing_entries() {
    let temp = tempfile::TempDir::new().unwrap();
    let existing_runtime = temp.path().join("librustc_driver-1234.dylib");
    let missing_runtime = temp.path().join("libunrelated-1234.dylib");
    fs::write(&existing_runtime, b"runtime").unwrap();

    assert_eq!(
        existing_local_compiler_runtime_artifacts(vec![
            (existing_runtime.clone(), DependencyType::Target),
            (missing_runtime, DependencyType::Target),
        ]),
        vec![existing_runtime]
    );
}

#[cfg(unix)]
#[test]
fn local_compiler_runtime_artifacts_accept_non_utf8_filenames() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;

    let filename = OsStr::from_bytes(b"librustc_driver-\xFF.dylib");
    assert!(is_local_compiler_runtime_artifact(Path::new(filename), DependencyType::Target));
}

#[test]
fn assembled_compiler_driver_detection_excludes_codegen_plugins() {
    assert!(is_rustc_driver_runtime_artifact(Path::new("librustc_driver-1234.dylib")));
    assert!(is_rustc_driver_runtime_artifact(Path::new("rustc_driver-1234.dll")));
    assert!(!is_rustc_driver_runtime_artifact(Path::new("librustc_codegen_trust_cg-1234.dylib")));
    assert!(!is_rustc_driver_runtime_artifact(Path::new("librustc_driver-1234.rmeta")));
}
