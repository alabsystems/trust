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
fn installing_an_rlib_prunes_metadata_left_by_an_earlier_build() {
    let temp = tempfile::TempDir::new().unwrap();
    let sysroot = temp.path();
    // Neither is recorded as installed by this run, so both are leftovers.
    fs::write(sysroot.join("libfoo-old.rmeta"), b"stale metadata").unwrap();
    fs::write(sysroot.join("libfoo-new.rmeta"), b"active metadata").unwrap();

    let active_rlib =
        RustArtifact { crate_name: "foo", stem: "libfoo-new", kind: RustArtifactKind::Rlib };
    prune_superseded_sysroot_artifacts(sysroot, active_rlib);

    assert!(sysroot.join("libfoo-new.rmeta").exists(), "the active stem's own metadata must stay");
    assert!(!sysroot.join("libfoo-old.rmeta").exists(), "a superseded stem must be pruned");
}

/// Regression test for a sysroot that built successfully and could not be used.
///
/// `lib/rustlib/<target>/lib` is filled from TWO stamps — std's and rustc's —
/// and they legitimately carry the same external crates at different versions
/// (`hashbrown`, `libc`, `object`, `memchr`, `gimli`, `miniz_oxide`, ...).
/// Pruning by crate NAME made whichever population was copied second delete the
/// other's artifacts. Measured on a clean stage2 (2026-08-30), 12 artifacts
/// across 9 crate names went missing and `extern crate rustc_public;` — with no
/// other code at all — failed with E0460 `found possibly newer version of crate
/// hashbrown which rustc_public depends on`, i.e. every out-of-tree
/// `rustc_private` consumer, including this repo's own `trust-mir-extract`.
#[test]
fn two_versions_of_one_external_crate_survive_the_same_build() {
    let temp = tempfile::TempDir::new().unwrap();
    let sysroot = temp.path();

    // std's copy lands first and is recorded, exactly as add_to_sysroot does.
    fs::write(sysroot.join("libhashbrown-aaaa.rmeta"), b"std's metadata").unwrap();
    record_sysroot_install(sysroot, "libhashbrown-aaaa.rmeta");

    // rustc's copy of the same crate at a different version follows.
    let rustc_copy = RustArtifact {
        crate_name: "hashbrown",
        stem: "libhashbrown-bbbb",
        kind: RustArtifactKind::Rlib,
    };
    prune_superseded_sysroot_artifacts(sysroot, rustc_copy);

    assert!(
        sysroot.join("libhashbrown-aaaa.rmeta").exists(),
        "the other population's artifact is not stale — deleting it is the E0460 bug"
    );
}

#[test]
fn a_rustc_private_crate_still_admits_only_one_version() {
    let temp = tempfile::TempDir::new().unwrap();
    let sysroot = temp.path();
    // Even recorded-this-run, rustc_* crates are single-version by construction,
    // so a different hash under the same name is unambiguously a leftover.
    fs::write(sysroot.join("librustc_middle-old.rmeta"), b"leftover").unwrap();
    record_sysroot_install(sysroot, "librustc_middle-old.rmeta");

    let active = RustArtifact {
        crate_name: "rustc_middle",
        stem: "librustc_middle-new",
        kind: RustArtifactKind::Rmeta,
    };
    prune_superseded_sysroot_artifacts(sysroot, active);

    assert!(!sysroot.join("librustc_middle-old.rmeta").exists());
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

#[test]
fn compiler_runtime_restore_prunes_every_stale_driver_generation() {
    let temp = tempfile::TempDir::new().unwrap();
    let old = temp.path().join("librustc_driver-old.dylib");
    let older = temp.path().join("librustc_driver-older.dylib");
    let backend = temp.path().join("librustc_codegen_trust_cg-current.dylib");
    fs::write(&old, b"old driver").unwrap();
    fs::write(&older, b"older driver").unwrap();
    fs::write(&backend, b"current backend").unwrap();

    prune_rustc_driver_runtime_artifacts(temp.path()).unwrap();

    assert!(!old.exists());
    assert!(!older.exists());
    assert!(backend.exists(), "codegen backends are not driver generations");
}

/// SILENT-WRONG-BEHAVIOUR REGRESSION. `TRUST_STD_ENCODE_MIR` used to disable on
/// the exact string `0` and silently ignore every other value, so
/// `TRUST_STD_ENCODE_MIR=false` left `-Zalways-encode-mir` ON while reading like
/// an opt-out. That switch decides whether std is lowerable at all.
#[test]
fn trust_std_encode_mir_refuses_unrecognized_values() {
    // Default and the two accepted values are unchanged.
    assert_eq!(trust_std_encode_mir_enabled(None), Ok(true));
    assert_eq!(trust_std_encode_mir_enabled(Some(OsStr::new("1"))), Ok(true));
    assert_eq!(trust_std_encode_mir_enabled(Some(OsStr::new("0"))), Ok(false));

    // Everything a person might reach for meaning "off" is now a hard error
    // naming the accepted set, rather than a silent ON.
    for value in ["false", "no", "off", "n", "", "00", "1 ", "true", "yes"] {
        let error = trust_std_encode_mir_enabled(Some(OsStr::new(value)))
            .expect_err(&format!("{value:?} was silently accepted"));
        assert!(error.contains(TRUST_STD_ENCODE_MIR_ENV), "{error}");
        assert!(error.contains('`') && error.contains("`1`") && error.contains("`0`"), "{error}");
    }
}
