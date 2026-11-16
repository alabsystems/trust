use super::*;
const NATIVE_VERSION: &str = "rustc 1.101.0-dev (52b1f442a 2026-11-06) (trustc 0.13.0+g52b1f442a)\nbinary: trustc\ncommit-hash: 52b1f442ae50ff083ce2ca240078d1de5555355c\ncommit-date: 2026-11-06\nhost: aarch64-apple-darwin\nrelease: 1.101.0-dev\ntrust: 0.13.0+g52b1f442a\nLLVM version: 23.1.5\n";

#[cfg(unix)]
fn write_native_input(path: &Path, executable: bool, arm64: bool, loads: &[&str]) {
    use std::os::unix::fs::PermissionsExt;
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    let mut commands = Vec::new();
    for load in loads {
        let length = (24 + load.len() + 1).next_multiple_of(8);
        let mut command = vec![0u8; length];
        command[..4].copy_from_slice(&0xcu32.to_le_bytes());
        command[4..8].copy_from_slice(&(length as u32).to_le_bytes());
        command[8..12].copy_from_slice(&24u32.to_le_bytes());
        command[24..24 + load.len()].copy_from_slice(load.as_bytes());
        commands.extend(command);
    }
    let mut bytes = vec![0; 32];
    for (offset, value) in [
        (0, 0xfeedfacfu32),
        (4, if arm64 { 0x0100000c } else { 0x01000007 }),
        (12, if executable { 2 } else { 6 }),
        (16, loads.len() as u32),
        (20, commands.len() as u32),
    ] {
        bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
    }
    bytes.extend(commands);
    fs::write(path, bytes).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(if executable { 0o555 } else { 0o444 }))
        .unwrap();
}

#[cfg(unix)]
fn native_input_fixture(root: &Path) {
    write_native_input(
        &root.join("bin/trustc"),
        true,
        true,
        &["@loader_path/../lib/librustc_driver-fixture.dylib"],
    );
    write_native_input(&root.join("lib/librustc_driver-fixture.dylib"), false, true, &[]);
    let host = root.join("lib/rustlib/aarch64-apple-darwin/lib");
    fs::create_dir_all(&host).unwrap();
    for name in ["libstd-fixture.rlib", "libcore-fixture.rlib"] {
        fs::write(host.join(name), b"bound archive input").unwrap();
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn live_runtime_input_owner_retains_original_descriptors_without_moving_their_offsets() {
    use std::io::{Seek, SeekFrom};
    use std::os::fd::AsRawFd;
    let source = tempfile::tempdir().unwrap();
    let root = fs::canonicalize(source.path()).unwrap();
    native_input_fixture(&root);
    write_native_input(&root.join("bin/trustdoc"), true, true, &[]);
    write_native_input(&root.join("libexec/native-child"), true, true, &[]);
    let held = HeldRuntimeInputs::capture(&root, HOST_TARGET).unwrap();
    held.require_executables(&[root.join("bin/trustdoc"), root.join("libexec/native-child")])
        .unwrap();
    assert!(held.require_executables(&[root.join("bin/absent-trustd")]).is_err());
    let (file, _, _) =
        held.files.iter().find(|(file, _, _)| file.metadata().unwrap().is_file()).unwrap();
    let mut same_ofd = file.try_clone().unwrap();
    same_ofd.seek(SeekFrom::Start(3)).unwrap();
    held.check().unwrap();
    assert_eq!(same_ofd.stream_position().unwrap(), 3);
    assert_ne!(unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFD) } & libc::FD_CLOEXEC, 0);
    assert_eq!(
        unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) } & libc::O_ACCMODE,
        libc::O_RDONLY
    );
    let driver = root.join("lib/librustc_driver-fixture.dylib");
    let original = fs::read(&driver).unwrap();
    fs::rename(&driver, root.join("original-driver-retained")).unwrap();
    fs::write(&driver, original).unwrap();
    assert!(
        held.check().is_err(),
        "same bytes at a replacement inode cannot replace original ownership"
    );
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn live_runtime_input_owner_refuses_changed_runtime_and_non_native_libexec() {
    let source = tempfile::tempdir().unwrap();
    let root = fs::canonicalize(source.path()).unwrap();
    native_input_fixture(&root);
    let held = HeldRuntimeInputs::capture(&root, HOST_TARGET).unwrap();
    fs::write(
        root.join("lib/rustlib/aarch64-apple-darwin/lib/libcore-fixture.rlib"),
        b"changed input",
    )
    .unwrap();
    assert!(held.check().is_err());
    fs::create_dir_all(root.join("libexec")).unwrap();
    let opaque = root.join("libexec/opaque-child");
    fs::write(&opaque, b"uninspected child program").unwrap();
    use std::os::unix::fs::PermissionsExt;
    fs::set_permissions(&opaque, fs::Permissions::from_mode(0o700)).unwrap();
    assert!(HeldRuntimeInputs::capture(&root, HOST_TARGET).is_err());
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
#[ignore = "explicit readonly SDK input only; set TRUST_NATIVE_LIVE_RUNTIME_INPUTS and TRUST_NATIVE_LIVE_RUNTIME_COMPILER_SHA256"]
fn actual_native_live_runtime_input_descriptions() {
    let root = PathBuf::from(
        std::env::var_os("TRUST_NATIVE_LIVE_RUNTIME_INPUTS")
            .expect("explicit immutable runtime input is required"),
    );
    let expected = std::env::var("TRUST_NATIVE_LIVE_RUNTIME_COMPILER_SHA256")
        .expect("independently observed compiler bytes are required");
    assert_eq!(expected.len(), 64);
    assert!(expected.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)));
    let original = HeldRuntimeInputs::capture(&root, HOST_TARGET).unwrap();
    let offer = original.original_descriptions().unwrap();
    assert_eq!(offer.count(), original.files.len() + 1);
    assert_eq!(
        offer.entries.iter().filter(|entry| entry.directory).count(),
        original.inventory.iter().filter(|entry| entry.directory).count()
    );
    for (offered, captured) in offer.entries.iter().zip(&original.inventory) {
        assert_eq!(offered.logical, captured.path);
        assert_eq!(offered.target, captured.target);
        assert_eq!(offered.alias, captured.alias.as_deref());
    }
    let compiler = original
        .inventory
        .iter()
        .find(|entry| entry.path == Path::new("bin/trustc"))
        .expect("original compiler input");
    assert_eq!(compiler.digest, expected);
    original
        .require_executables(
            &["trustc", "trustdoc", "targo", "trustd", "ay"]
                .map(|name| root.join("bin").join(name)),
        )
        .unwrap();
    let mut limits = std::mem::MaybeUninit::<libc::rlimit>::uninit();
    // SAFETY: getrlimit initializes exactly this writable native structure.
    assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, limits.as_mut_ptr()) }, 0);
    // SAFETY: the successful call initialized the complete structure.
    let limits = unsafe { limits.assume_init() };
    println!(
        "original_runtime_descriptions={} files={} directories={} soft_fd_limit={} compiler_sha256={}; all-original borrowed offer checked; input-only, no SDK tool executed, completion or compatibility constructed",
        offer.count(),
        original.inventory.iter().filter(|entry| !entry.directory).count(),
        original.inventory.iter().filter(|entry| entry.directory).count(),
        limits.rlim_cur,
        compiler.digest
    );
    original.check().unwrap();
}

#[cfg(unix)]
#[test]
fn native_input_roles_exclude_source_snapshot_without_following_its_payload() {
    let source = tempfile::tempdir().unwrap();
    let root = fs::canonicalize(source.path()).unwrap();
    native_input_fixture(&root);
    let excluded = "lib/rustlib/source-snapshot";
    let payload = root.join(excluded).join("foreign-compiler-fixture.dylib");
    write_native_input(&payload, false, false, &[]);
    let entries = inventory(&root, false).unwrap();
    assert!(
        entries.iter().all(|entry| !entry.path.starts_with(excluded)),
        "source inputs are separate from the native compiler-test runtime"
    );
    validate_runtime(&root, &entries).unwrap();
    assert!(payload.is_file(), "input selection must not mutate the original SDK");
}

#[cfg(unix)]
#[test]
fn native_input_roles_bind_foreign_target_bytes_without_executing_them() {
    let source = tempfile::tempdir().unwrap();
    let root = fs::canonicalize(source.path()).unwrap();
    native_input_fixture(&root);
    let foreign = "lib/rustlib/x86_64-apple-darwin/lib/libstd-foreign.dylib";
    write_native_input(&root.join(foreign), false, false, &[]);
    let entries = inventory(&root, false).unwrap();
    assert!(
        entries.iter().any(|entry| entry.path == Path::new(foreign) && !entry.digest.is_empty())
    );
    validate_runtime(&root, &entries).unwrap();
    assert!(native_loads(&root.join(foreign)).is_err());
}

#[cfg(unix)]
#[test]
fn native_input_roles_never_promote_foreign_target_data_into_runtime() {
    let source = tempfile::tempdir().unwrap();
    let root = fs::canonicalize(source.path()).unwrap();
    native_input_fixture(&root);
    // Even native-looking bytes in another target's namespace are data.
    let foreign = "lib/rustlib/x86_64-apple-darwin/lib/foreign.dylib";
    write_native_input(&root.join(foreign), false, true, &[]);
    fs::remove_file(root.join("bin/trustc")).unwrap();
    write_native_input(
        &root.join("bin/trustc"),
        true,
        true,
        &[
            "@loader_path/../lib/librustc_driver-fixture.dylib",
            "@loader_path/../lib/rustlib/x86_64-apple-darwin/lib/foreign.dylib",
        ],
    );
    assert!(validate_runtime(&root, &inventory(&root, false).unwrap()).is_err());
}

#[cfg(unix)]
#[test]
fn native_input_roles_reject_host_aliases_into_source_and_foreign_target_data() {
    for data in
        ["lib/rustlib/source-snapshot/compiler", "lib/rustlib/x86_64-apple-darwin/bin/compiler"]
    {
        let source = tempfile::tempdir().unwrap();
        let root = fs::canonicalize(source.path()).unwrap();
        native_input_fixture(&root);
        write_native_input(&root.join(data), true, true, &[]);
        fs::remove_file(root.join("bin/trustc")).unwrap();
        std::os::unix::fs::symlink(root.join(data), root.join("bin/trustc")).unwrap();
        assert!(validate_runtime(&root, &inventory(&root, false).unwrap()).is_err());
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
#[ignore = "explicit immutable SDK input; set TRUST_NATIVE_COMPILER_TEST_FIXTURE"]
fn actual_native_compiler_test_fixture_snapshot() {
    let source = PathBuf::from(std::env::var_os("TRUST_NATIVE_COMPILER_TEST_FIXTURE").unwrap());
    let base = std::env::current_exe().unwrap().parent().unwrap().canonicalize().unwrap();
    let cache = tempfile::Builder::new()
        .prefix("retained-compiler-sdk-")
        .suffix(".noindex")
        .tempdir_in(base)
        .unwrap()
        .keep();
    let fixture =
        RetainedCompilerTestFixture::capture(&source, &cache, "aarch64-apple-darwin").unwrap();
    fixture.revalidate().unwrap();
    assert_eq!(fixture.source_commit().len(), 40);
    assert!(
        fixture
            .inventory
            .iter()
            .all(|entry| { !entry.path.starts_with("lib/rustlib/source-snapshot") })
    );
    eprintln!(
        "actual native fixture source={} identity={} entries={} receipt={}",
        fixture.source_commit(),
        fixture.identity(),
        fixture.inventory.len(),
        fixture.receipt_path().display()
    );
}

#[test]
fn native_version_rejects_wrong_host_corrupt_identity_and_duplicate_claims() {
    assert!(validate_version(NATIVE_VERSION, "aarch64-apple-darwin").is_ok());
    assert!(validate_version(NATIVE_VERSION, "x86_64-apple-darwin").is_err());
    for version in [
        NATIVE_VERSION.replace("(trustc 0.13.0+g52b1f442a)", "(other compiler)"),
        NATIVE_VERSION.replace(
            "commit-hash: 52b1f442ae50ff083ce2ca240078d1de5555355c",
            "commit-hash: not-a-source-id",
        ),
        NATIVE_VERSION.replace("binary: trustc", "binary: rustc"),
        format!("{NATIVE_VERSION}host: aarch64-apple-darwin\n"),
    ] {
        assert!(validate_version(&version, "aarch64-apple-darwin").is_err());
    }
}

#[test]
fn missing_driver_std_and_corrupt_native_image_are_refused() {
    let source = tempfile::tempdir().unwrap();
    let canonical = fs::canonicalize(source.path()).unwrap();
    let root = canonical.as_path();
    fs::create_dir_all(root.join("bin")).unwrap();
    let host = root.join("lib/rustlib/aarch64-apple-darwin");
    fs::create_dir_all(host.join("lib")).unwrap();
    assert!(validate_runtime(root, &inventory(root, false).unwrap()).is_err());
    for path in [
        "bin/trustc",
        "lib/librustc_driver-fixture.dylib",
        "lib/rustlib/aarch64-apple-darwin/lib/libstd-fixture.rlib",
        "lib/rustlib/aarch64-apple-darwin/lib/libcore-fixture.rlib",
    ] {
        fs::write(root.join(path), b"not a native runtime").unwrap();
    }
    assert!(validate_runtime(root, &inventory(root, false).unwrap()).is_err());
    fs::create_dir_all(host.join("codegen-backends")).unwrap();
    fs::write(
        host.join("codegen-backends/librustc_codegen_llvm-fixture.dylib"),
        b"corrupt native backend",
    )
    .unwrap();
    assert!(validate_runtime(root, &inventory(root, false).unwrap()).is_err());
    fs::write(root.join("bin/trustc"), 0xfeedfacfu32.to_le_bytes()).unwrap();
    assert!(
        native_loads(&root.join("bin/trustc")).is_err(),
        "a truncated native header cannot qualify an image"
    );
}
#[test]
fn identity_comparison_includes_every_file_and_ignores_only_copy_location() {
    let entry = |root: &str, hash: &str| Entry {
        path: "lib/driver".into(),
        target: Path::new(root).join("lib/driver"),
        directory: false,
        executable: true,
        bytes: 4,
        digest: hash.into(),
        stamp: vec![],
        alias: None,
    };
    assert!(same_contents(&[entry("/source", "a")], &[entry("/copy", "a")]));
    assert!(!same_contents(&[entry("/source", "a")], &[entry("/copy", "b")]));
    assert!(!same_contents(&[entry("/source", "a")], &[]));
}
#[test]
fn inventory_refuses_depth_overflow_instead_of_silently_omitting_inputs() {
    let source = tempfile::tempdir().unwrap();
    let root = fs::canonicalize(source.path()).unwrap();
    fs::create_dir(root.join("bin")).unwrap();
    let mut directory = root.join("lib");
    fs::create_dir(&directory).unwrap();
    for _ in 0..65 {
        directory.push("nested");
        fs::create_dir(&directory).unwrap();
    }
    fs::write(directory.join("hidden-input"), b"must not be omitted").unwrap();
    assert!(inventory(&root, false).unwrap_err().contains("depth"));
}
#[test]
fn only_exact_nonruntime_source_aliases_are_omitted() {
    assert!(omitted(Path::new("lib/rustlib/src/rust")));
    assert!(omitted(Path::new("lib/rustlib/rustc-src/rust")));
    assert!(omitted(Path::new("lib/rustlib/source-snapshot")));
    for path in [
        "lib/rustlib/src",
        "lib/rustlib/src/rust/extra",
        "lib/rustlib/source-snapshot/extra",
        "lib/rustlib/source-snapshot-extra",
        "lib/rustlib/aarch64-apple-darwin/lib",
        "bin/trustc",
    ] {
        assert!(!omitted(Path::new(path)));
    }
}
#[test]
fn unsupported_host_is_refused_before_any_source_or_cache_access() {
    assert!(
        RetainedCompilerTestFixture::capture(
            Path::new("/absent/source"),
            Path::new("/absent/cache"),
            "x86_64-unknown-linux-gnu"
        )
        .err()
        .unwrap()
        .contains("supports only")
    );
}
#[test]
fn malformed_native_command_cannot_smuggle_loader_path() {
    assert!(load_string(&[0; 8], 8).is_err());
    assert!(
        expand("relative/libevil.dylib", Path::new("/sdk/bin/trustc"), Path::new("/sdk")).is_err()
    );
}
#[test]
fn runtime_images_cannot_fall_back_to_opaque_data() {
    let entry = |path: &str, executable| Entry {
        path: path.into(),
        target: PathBuf::new(),
        directory: false,
        executable,
        bytes: 0,
        digest: String::new(),
        stamp: Vec::new(),
        alias: None,
    };
    for path in [
        "lib/liblazy.dylib",
        "lib/liblazy.so",
        "lib/liblazy.DLL",
        "lib/rustlib/aarch64-apple-darwin/lib/libstd.dylib",
        "lib/rustlib/aarch64-apple-darwin/codegen-backends/backend.dylib",
    ] {
        assert!(requires_native_inspection(&entry(path, false)));
    }
    for path in ["bin/trustc", "lib/rustlib/aarch64-apple-darwin/bin/linker"] {
        assert!(requires_native_inspection(&entry(path, true)));
    }
    for path in ["lib/rustlib/aarch64-apple-darwin/lib/libstd.rlib", "lib/metadata.json"] {
        assert!(!requires_native_inspection(&entry(path, false)));
    }
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("universal.dylib");
    // A fat image is unsupported until its selected native slice can be
    // checked; hashing its bytes alone must not certify loader closure.
    fs::write(&path, [0xca, 0xfe, 0xba, 0xbe, 0, 0, 0, 1]).unwrap();
    assert!(native_loads(&path).unwrap().is_none());
    assert!(requires_native_inspection(&entry("lib/universal.dylib", false)));
}
#[test]
fn copy_is_independent_and_drift_and_external_aliases_are_rejected() {
    let source = tempfile::tempdir().unwrap();
    let copy = tempfile::tempdir().unwrap();
    let source_root = fs::canonicalize(source.path()).unwrap();
    let copy_root = fs::canonicalize(copy.path()).unwrap();
    fs::create_dir(source_root.join("bin")).unwrap();
    fs::create_dir(source_root.join("lib")).unwrap();
    fs::write(source_root.join("bin/trustc"), b"native fixture bytes").unwrap();
    fs::write(source_root.join("lib/runtime"), b"runtime bytes").unwrap();
    let before = inventory(&source_root, false).unwrap();
    copy_inputs(&source_root, &copy_root, &before).unwrap();
    assert!(same_contents(&before, &inventory(&copy_root, false).unwrap()));
    fs::write(source_root.join("lib/runtime"), b"changed bytes").unwrap();
    assert_ne!(before, inventory(&source_root, false).unwrap());
    assert_eq!(fs::read(copy_root.join("lib/runtime")).unwrap(), b"runtime bytes");
    make_readonly(&copy_root).unwrap();
    let frozen = inventory(&copy_root, true).unwrap();
    assert!(same_contents(&before, &frozen));
    #[cfg(unix)]
    {
        let mut permissions = fs::metadata(copy_root.join("bin")).unwrap().permissions();
        permissions.set_readonly(false);
        fs::set_permissions(copy_root.join("bin"), permissions).unwrap();
        std::os::unix::fs::symlink(source_root.join("lib/runtime"), copy_root.join("bin/escape"))
            .unwrap();
        assert!(inventory(&copy_root, false).unwrap_err().contains("escapes root"));
    }
    remove_snapshot(&copy_root);
}
