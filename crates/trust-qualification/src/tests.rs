use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::Path;
use std::process::Command;

use tempfile::TempDir;

use crate::{Git, Result, pair, seal, source};

const COMMIT: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const EXECUTABLES: &[&str] = &[
    "bin/trustc",
    "bin/targo",
    "bin/targo-trust",
    "bin/trustd",
    "bin/trustdoc",
    "bin/ay",
    "bin/clean",
    "bin/ty",
    "bin/tippy",
    "bin/targo-tippy",
    "bin/tippy-driver",
    "bin/trustfmt",
    "bin/targo-fmt",
    "bin/trust-analyzer",
    "libexec/trust-analyzer-proc-macro-srv",
    "lib/rustlib/aarch64-apple-darwin/bin/rust-lld",
    "lib/rustlib/aarch64-apple-darwin/bin/gcc-ld/ld64.lld",
    "lib/rustlib/aarch64-apple-darwin/bin/rust-objcopy",
];
const DATA: &[&str] = &[
    "lib/librustc_driver-0123456789abcdef.dylib",
    "lib/libstd-0123456789abcdef.dylib",
    "lib/rustlib/aarch64-apple-darwin/lib/libstd-0123456789abcdef.rlib",
    "lib/rustlib/aarch64-apple-darwin/lib/libcore-0123456789abcdef.rlib",
    "lib/rustlib/aarch64-apple-darwin/lib/liballoc-0123456789abcdef.rlib",
    "lib/rustlib/aarch64-apple-darwin/lib/librustc_public-0123456789abcdef.rmeta",
    "lib/rustlib/aarch64-apple-darwin/lib/libserde_derive-0123456789abcdef.dylib",
    "lib/rustlib/aarch64-apple-darwin/lib/self-contained/crt2.o",
    "lib/rustlib/aarch64-apple-darwin/codegen-backends/librustc_codegen_trust_cg-0123456789abcdef.dylib",
    "lib/rustlib/x86_64-apple-darwin/lib/libstd-fedcba9876543210.rlib",
    "lib/rustlib/x86_64-apple-darwin/lib/libcore-fedcba9876543210.rlib",
    "lib/rustlib/src/rust/library/core/src/lib.rs",
    "lib/rustlib/rustc-src.json",
    "share/man/man1/trustc.1",
    "share/doc/PROVENANCE",
];
const STOCK: &[(&str, &str)] =
    &[("bin/rustc", "bin/trustc"), ("bin/cargo", "bin/targo"), ("bin/rustdoc", "bin/trustdoc")];

fn write(path: &Path, bytes: impl AsRef<[u8]>, mode: u32) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, bytes).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(mode)).unwrap();
}

fn fixture_seal(root: &Path) {
    for rel in EXECUTABLES {
        write(&root.join(rel), format!("#!/bin/sh\n# {rel}\n"), 0o755);
    }
    for (stock, trust) in STOCK {
        fs::hard_link(root.join(trust), root.join(stock)).unwrap();
    }
    for rel in DATA {
        write(&root.join(rel), format!("payload of {rel}\n"), 0o644);
    }
    let link = root.join("lib/rustlib/rustc-src/rust");
    fs::create_dir_all(link.parent().unwrap()).unwrap();
    symlink("../src/rust", link).unwrap();
    for rel in seal::RECORDS {
        write(&root.join(rel), format!("record {rel}\n"), 0o644);
    }
    fn dirs(path: &Path) {
        fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
        for child in fs::read_dir(path).unwrap() {
            let child = child.unwrap();
            if child.file_type().unwrap().is_dir() {
                dirs(&child.path());
            }
        }
    }
    dirs(root);
}

#[test]
fn every_shipped_executable_library_std_source_and_stock_name_moves_seal_identity() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("seal");
    fixture_seal(&root);
    let baseline = seal::identity(&root).unwrap();
    for rel in EXECUTABLES.iter().chain(DATA).chain(STOCK.iter().map(|(a, _)| a)) {
        let path = root.join(rel);
        let original = fs::read(&path).unwrap();
        let mut changed = original.clone();
        *changed.last_mut().unwrap() ^= 1;
        fs::write(&path, &changed).unwrap();
        assert_ne!(seal::identity(&root).unwrap().sha256, baseline.sha256, "{rel}");
        fs::write(path, original).unwrap();
        assert_eq!(seal::identity(&root).unwrap(), baseline);
    }
}

#[test]
fn seal_mode_covers_special_and_read_execute_bits_on_files_and_directories() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("seal");
    fixture_seal(&root);
    let baseline = seal::identity(&root).unwrap();
    for rel in ["bin/targo-trust", "bin/trustd", DATA[2], "lib/rustlib/aarch64-apple-darwin/lib"] {
        for bit in [0o100, 0o4000, 0o2000, 0o1000, 0o010, 0o004] {
            if rel.ends_with("/lib") && bit == 0o100 {
                continue;
            }
            let path = root.join(rel);
            let mode = fs::metadata(&path).unwrap().permissions().mode();
            fs::set_permissions(&path, fs::Permissions::from_mode(mode ^ bit)).unwrap();
            assert_ne!(seal::identity(&root).unwrap().sha256, baseline.sha256, "{rel} {bit:o}");
            fs::set_permissions(path, fs::Permissions::from_mode(mode)).unwrap();
        }
    }
}

#[test]
fn clearing_group_other_write_and_changing_copy_inode_does_not_change_seal() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("seal");
    fixture_seal(&root);
    let baseline = seal::identity(&root).unwrap();
    for rel in
        EXECUTABLES.iter().chain(DATA).chain([&"bin", &"lib/rustlib/aarch64-apple-darwin/lib"])
    {
        let path = root.join(rel);
        let mode = fs::metadata(&path).unwrap().permissions().mode();
        fs::set_permissions(path, fs::Permissions::from_mode(mode | 0o022)).unwrap();
    }
    for (stock, trust) in STOCK {
        fs::remove_file(root.join(stock)).unwrap();
        fs::copy(root.join(trust), root.join(stock)).unwrap();
    }
    assert_eq!(seal::identity(&root).unwrap(), baseline);
}

#[test]
fn seal_root_records_are_excluded_but_same_names_below_root_are_covered() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("seal");
    fixture_seal(&root);
    let baseline = seal::identity(&root).unwrap();
    for rel in seal::RECORDS {
        write(&root.join(rel), "changed", 0o600);
    }
    fs::remove_file(root.join("SEED-MINT")).unwrap();
    assert_eq!(seal::identity(&root).unwrap(), baseline);
    write(&root.join("share/doc/PROVENANCE"), "changed", 0o644);
    assert_ne!(seal::identity(&root).unwrap().sha256, baseline.sha256);
}

#[test]
fn seal_add_remove_rename_relink_and_empty_directory_are_content() {
    for mutation in 0..7 {
        let temporary = TempDir::new().unwrap();
        let root = temporary.path().join("seal");
        fixture_seal(&root);
        let baseline = seal::identity(&root).unwrap();
        match mutation {
            0 => write(&root.join("bin/trust-wp"), "new", 0o755),
            1 => write(
                &root.join("lib/rustlib/aarch64-apple-darwin/lib/libextra.rlib"),
                "new",
                0o644,
            ),
            2 => fs::remove_file(root.join("bin/trustd")).unwrap(),
            3 => fs::remove_file(root.join(DATA[2])).unwrap(),
            4 => fs::rename(root.join("bin/ty"), root.join("bin/ty2")).unwrap(),
            5 => {
                let path = root.join("lib/rustlib/rustc-src/rust");
                fs::remove_file(&path).unwrap();
                symlink("../src", path).unwrap();
            }
            6 => fs::create_dir(
                root.join("lib/rustlib/aarch64-apple-darwin/lib/self-contained/empty"),
            )
            .unwrap(),
            _ => unreachable!(),
        }
        assert_ne!(seal::identity(&root).unwrap().sha256, baseline.sha256, "mutation {mutation}");
    }
}

#[test]
fn seal_alias_name_counts_manifest_and_prefix_preserve_complete_population() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("seal");
    fixture_seal(&root);
    symlink(&root, temporary.path().join("current")).unwrap();
    let identity = seal::identity(&root).unwrap();
    assert_eq!(identity, seal::identity(&temporary.path().join("current")).unwrap());
    // Captured with the unmodified Python reader and its original complete
    // fixture, retained in seal-python-golden.json in the validation evidence.
    assert_eq!(identity.sha256, "733d2b1230f4d764f82c6ad4189820a87b5329551be52e4825b656a93e250401");
    assert_eq!(identity.files, (EXECUTABLES.len() + DATA.len() + STOCK.len()) as u64);
    assert_eq!(identity.links, 1);
    assert_eq!(identity.directories, 22);
    let entries = seal::entries(&root).unwrap();
    assert_eq!(entries.len() as u64, identity.files + identity.links + identity.directories);
    assert!(entries.windows(2).all(|rows| rows[0].path < rows[1].path));
    assert!(entries.iter().any(|e| e.kind == b'L' && e.value == b"../src/rust"));
    assert!(entries.iter().any(|e| e.kind == b'D' && e.mode == "0755" && e.path == b"bin"));
    assert_eq!(identity.provenance_lines("private_sysroot_content").unwrap().len(), 5);
    assert!(identity.provenance_lines("a-b").is_err());
    assert!(identity.provenance_lines("").is_err());
}

#[test]
fn fifo_is_refused_without_opening_or_blocking() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("seal");
    fixture_seal(&root);
    let path =
        std::ffi::CString::new(root.join("bin/pipe").as_os_str().as_encoded_bytes()).unwrap();
    // SAFETY: path is a live NUL-terminated pathname in this test's owned directory.
    assert_eq!(unsafe { libc::mkfifo(path.as_ptr(), 0o600) }, 0);
    assert!(seal::identity(&root).unwrap_err().to_string().contains("neither a regular file"));
    assert!(source::dependency_identity(&root).is_err());
}

pub(crate) struct TestGit;
impl TestGit {
    fn command(root: &Path, args: &[&str]) -> std::process::Output {
        #[cfg(target_os = "macos")]
        const BIN: &str = "/Library/Developer/CommandLineTools/usr/bin/git";
        #[cfg(not(target_os = "macos"))]
        const BIN: &str = "/usr/bin/git";
        Command::new(BIN)
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .args([
                "-c",
                "core.hooksPath=/dev/null",
                "-c",
                "user.name=qualification-test",
                "-c",
                "user.email=test@example.invalid",
                "-C",
            ])
            .arg(root)
            .args(args)
            .output()
            .unwrap()
    }
    pub(crate) fn run(root: &Path, args: &[&str]) {
        let output = Self::command(root, args);
        assert!(output.status.success(), "{args:?}: {}", String::from_utf8_lossy(&output.stderr));
    }
}
impl Git for TestGit {
    fn probe(&self, root: &Path, args: &[&str]) -> Result<Vec<u8>> {
        let output = Self::command(root, args);
        if !output.status.success() {
            return Err(crate::refusal(String::from_utf8_lossy(&output.stderr).into_owned()));
        }
        Ok(output.stdout)
    }
    fn validate_repository(&self, _: &Path) -> Result<()> {
        Ok(())
    }
}

fn repository(root: &Path) {
    fs::create_dir_all(root).unwrap();
    TestGit::run(root, &["init", "-q"]);
    write(&root.join("Cargo.toml"), "[package]\nname='fixture'\nversion='0.1.0'\n", 0o644);
    write(&root.join("Cargo.lock"), "version=4\n", 0o644);
    write(&root.join("lib.rs"), "pub fn value() -> u8 { 1 }\n", 0o644);
    write(&root.join(".gitignore"), "target/\nignored/\n.cargo/\n", 0o644);
    TestGit::run(root, &["add", "."]);
    TestGit::run(root, &["commit", "-qm", "fixture"]);
}

#[test]
fn frozen_source_matches_its_actual_git_objects_and_rejects_later_drift() {
    let temporary = TempDir::new().unwrap();
    repository(temporary.path());
    let identity = source::identity(&TestGit, temporary.path(), true, false).unwrap();
    assert_eq!(identity, source::identity(&TestGit, temporary.path(), true, false).unwrap());
    assert_eq!(identity.commit.len(), 40);
    assert!(identity.lock_sha256.is_some());
    write(&temporary.path().join("lib.rs"), "pub fn value() -> u8 { 2 }\n", 0o644);
    assert!(source::identity(&TestGit, temporary.path(), true, false).is_err());
}

#[test]
fn hidden_index_flags_cannot_hide_source_mutation() {
    for flag in ["--assume-unchanged", "--skip-worktree"] {
        let temporary = TempDir::new().unwrap();
        repository(temporary.path());
        TestGit::run(temporary.path(), &["update-index", flag, "lib.rs"]);
        assert!(source::identity(&TestGit, temporary.path(), true, false).is_err());
        write(&temporary.path().join("lib.rs"), "changed", 0o644);
        assert!(source::identity(&TestGit, temporary.path(), true, false).is_err());
    }
}

#[test]
fn source_links_bind_only_tracked_regular_files_inside_same_closure() {
    for target in ["lib.rs", "ignored/hidden.rs", "../outside.rs", "."] {
        let temporary = TempDir::new().unwrap();
        let root = temporary.path().join("source");
        repository(&root);
        write(&root.join("ignored/hidden.rs"), "ignored", 0o644);
        write(&temporary.path().join("outside.rs"), "outside", 0o644);
        symlink(target, root.join("alias.rs")).unwrap();
        TestGit::run(&root, &["add", "alias.rs"]);
        TestGit::run(&root, &["commit", "-qm", "link"]);
        assert_eq!(
            source::identity(&TestGit, &root, true, false).is_ok(),
            target == "lib.rs",
            "{target}"
        );
    }
}

#[test]
fn ignored_intermediate_source_link_cannot_change_the_selected_bound_file_silently() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path();
    repository(root);
    write(&root.join("a.rs"), "selected A", 0o644);
    write(&root.join("b.rs"), "selected B", 0o644);
    fs::create_dir(root.join("ignored")).unwrap();
    symlink("../a.rs", root.join("ignored/hop")).unwrap();
    symlink("ignored/hop", root.join("link.rs")).unwrap();
    TestGit::run(root, &["add", "."]);
    TestGit::run(root, &["commit", "-qm", "bound files and indirect source link"]);
    let first = source::identity(&TestGit, root, true, false).unwrap();
    assert_eq!(fs::read(root.join("link.rs")).unwrap(), b"selected A");
    fs::remove_file(root.join("ignored/hop")).unwrap();
    symlink("../b.rs", root.join("ignored/hop")).unwrap();
    let second = source::identity(&TestGit, root, true, false).unwrap();
    assert_eq!(fs::read(root.join("link.rs")).unwrap(), b"selected B");
    assert_eq!(first.commit, second.commit);
    assert_eq!(first.tree, second.tree);
    eprintln!(
        "source selected A -> B; HEAD/tree unchanged; native hashes {} -> {}",
        first.working_sha256, second.working_sha256
    );
    assert_ne!(first.working_sha256, second.working_sha256);
}

#[test]
fn excluded_git_hop_cannot_change_the_selected_dependency_file_silently() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path();
    write(&root.join("a"), "selected A", 0o644);
    write(&root.join("b"), "selected B", 0o644);
    fs::create_dir(root.join(".git")).unwrap();
    symlink("../a", root.join(".git/hop")).unwrap();
    symlink(".git/hop", root.join("link")).unwrap();
    let first = source::dependency_identity(root).unwrap();
    assert_eq!(fs::read(root.join("link")).unwrap(), b"selected A");
    fs::remove_file(root.join(".git/hop")).unwrap();
    symlink("../b", root.join(".git/hop")).unwrap();
    let second = source::dependency_identity(root).unwrap();
    assert_eq!(fs::read(root.join("link")).unwrap(), b"selected B");
    eprintln!("dependency selected A -> B; native hashes {} -> {}", first.sha256, second.sha256);
    assert_ne!(first.sha256, second.sha256);
}

#[test]
fn source_executable_mode_is_bound_and_lock_is_required() {
    let temporary = TempDir::new().unwrap();
    repository(temporary.path());
    fs::set_permissions(temporary.path().join("lib.rs"), fs::Permissions::from_mode(0o755))
        .unwrap();
    assert!(source::identity(&TestGit, temporary.path(), true, false).is_err());
    fs::set_permissions(temporary.path().join("lib.rs"), fs::Permissions::from_mode(0o644))
        .unwrap();
    TestGit::run(temporary.path(), &["rm", "Cargo.lock"]);
    TestGit::run(temporary.path(), &["commit", "-qm", "no lock"]);
    assert!(source::identity(&TestGit, temporary.path(), true, false).is_err());
    assert!(source::identity(&TestGit, temporary.path(), false, false).is_ok());
}

#[test]
fn source_closure_requires_initialized_exact_submodule_pins_and_unchanged_child_bytes() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("root");
    let child_source = temporary.path().join("child-source");
    repository(&root);
    repository(&child_source);
    let child = child_source.to_str().unwrap();
    TestGit::run(
        &root,
        &["-c", "protocol.file.allow=always", "submodule", "add", "-q", child, "child"],
    );
    TestGit::run(&root, &["commit", "-qam", "pinned child"]);
    let baseline = source::identity(&TestGit, &root, true, false).unwrap();
    assert_eq!(baseline, source::identity(&TestGit, &root, true, false).unwrap());
    write(&root.join("child/lib.rs"), "changed child", 0o644);
    assert!(source::identity(&TestGit, &root, true, false).is_err());
}

#[test]
fn raw_path_bytes_are_lossless_and_supported_filesystems_bind_non_utf8_names() {
    use std::os::unix::ffi::OsStrExt;
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("source");
    repository(&root);
    let name = std::ffi::OsStr::from_bytes(b"raw-\xff.rs");
    // This is the production encoding used by both source and seal readers,
    // checked even on APFS, which refuses this pathname with EILSEQ before
    // either reader can observe a file. Never round-trip through lossy UTF8.
    assert_eq!(crate::tree::path_bytes(Path::new(name)), b"raw-\xff.rs");
    match fs::write(root.join(name), "source") {
        Ok(()) => {}
        Err(error) if error.raw_os_error() == Some(libc::EILSEQ) => {
            eprintln!(
                "filesystem refuses non-UTF8 pathname (EILSEQ); production raw-byte encoding asserted; actual-file subcase requires a supporting filesystem"
            );
            return;
        }
        Err(error) => panic!("cannot create raw filename fixture: {error}"),
    }
    fs::set_permissions(root.join(name), fs::Permissions::from_mode(0o644)).unwrap();
    TestGit::run(&root, &["add", "."]);
    TestGit::run(&root, &["commit", "-qm", "raw path"]);
    let baseline = source::identity(&TestGit, &root, true, false).unwrap();
    write(&root.join(name), "changed", 0o644);
    assert!(source::identity(&TestGit, &root, true, false).is_err());
    assert!(!baseline.working_sha256.is_empty());
    let seal_root = temporary.path().join("seal");
    fixture_seal(&seal_root);
    let before = seal::identity(&seal_root).unwrap();
    write(&seal_root.join(name), "sealed", 0o644);
    assert_ne!(seal::identity(&seal_root).unwrap().sha256, before.sha256);
    assert!(seal::entries(&seal_root).unwrap().iter().any(|entry| entry.path == b"raw-\xff.rs"));
}

#[test]
fn cargo_marker_is_one_exact_empty_file_and_only_a_dependency_checkout_exception() {
    let temporary = TempDir::new().unwrap();
    repository(temporary.path());
    write(&temporary.path().join(".cargo-ok"), b"", 0o644);
    let baseline = source::identity(&TestGit, temporary.path(), false, true).unwrap();
    assert!(baseline.cargo_checkout_marker.is_some());
    assert!(source::identity(&TestGit, temporary.path(), false, false).is_err());
    write(&temporary.path().join("other"), b"", 0o644);
    assert!(source::identity(&TestGit, temporary.path(), false, true).is_err());
    fs::remove_file(temporary.path().join("other")).unwrap();
    write(&temporary.path().join(".cargo-ok"), "nonempty", 0o644);
    assert!(source::cargo_checkout_marker(temporary.path()).is_err());
    fs::remove_file(temporary.path().join(".cargo-ok")).unwrap();
    symlink("lib.rs", temporary.path().join(".cargo-ok")).unwrap();
    assert!(source::cargo_checkout_marker(temporary.path()).is_err());
    fs::remove_file(temporary.path().join(".cargo-ok")).unwrap();
    fs::create_dir(temporary.path().join(".cargo-ok")).unwrap();
    assert!(source::cargo_checkout_marker(temporary.path()).is_err());
}

#[test]
fn cargo_marker_replacement_between_lstat_and_open_refuses_without_following() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path();
    write(&root.join(".cargo-ok"), "", 0o644);
    write(&root.join("outside"), "", 0o644);
    assert!(
        source::marker_after_inspection(root, || {
            fs::remove_file(root.join(".cargo-ok")).unwrap();
            symlink("outside", root.join(".cargo-ok")).unwrap();
        })
        .is_err()
    );
}

#[test]
fn cargo_marker_replacement_with_fifo_never_blocks_and_refuses() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path();
    write(&root.join(".cargo-ok"), "", 0o644);
    assert!(
        source::marker_after_inspection(root, || {
            fs::remove_file(root.join(".cargo-ok")).unwrap();
            let path =
                std::ffi::CString::new(root.join(".cargo-ok").as_os_str().as_encoded_bytes())
                    .unwrap();
            // SAFETY: the test exclusively owns this live NUL-terminated pathname.
            assert_eq!(unsafe { libc::mkfifo(path.as_ptr(), 0o600) }, 0);
        })
        .is_err()
    );
}

#[test]
fn cargo_marker_replacement_with_empty_inode_is_still_drift() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path();
    write(&root.join(".cargo-ok"), "", 0o644);
    write(&root.join("replacement"), "", 0o644);
    assert!(
        source::marker_after_inspection(root, || {
            fs::rename(root.join("replacement"), root.join(".cargo-ok")).unwrap();
        })
        .is_err()
    );
}

#[test]
fn dependency_identity_covers_ignored_workspace_sources_and_refuses_escaping_links() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("dependency");
    repository(&root);
    write(&root.join("ignored/workspace.toml"), "original", 0o644);
    let before = source::dependency_identity(&root).unwrap();
    write(&root.join("ignored/workspace.toml"), "changed", 0o644);
    assert_ne!(source::dependency_identity(&root).unwrap(), before);
    write(&temporary.path().join("outside"), "outside", 0o644);
    symlink("../outside", root.join("link")).unwrap();
    assert!(source::dependency_identity(&root).is_err());
    fs::remove_file(root.join("link")).unwrap();
    symlink("lib.rs", root.join("link")).unwrap();
    assert!(source::dependency_identity(&root).is_ok());
}

#[test]
fn ignored_path_package_manifest_and_hidden_package_sources_refuse() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path();
    repository(root);
    source::path_package_bound(&TestGit, &root.join("Cargo.toml"), root)
        .expect("tracked root package");
    write(&root.join("ignored/Cargo.toml"), "package", 0o644);
    assert!(source::path_package_bound(&TestGit, &root.join("ignored/Cargo.toml"), root).is_err());
    assert!(source::path_package_bound(&TestGit, &root.join("Cargo.toml"), root).is_err());
}

fn pair_fixture(temporary: &TempDir) -> pair::Request {
    let root = temporary.path();
    let ay = root.join("ay");
    let vc = root.join("vc");
    repository(&ay);
    repository(&vc);
    for name in ["refutation_step_realbody.rs", "refutation_loop_realbody.rs"] {
        write(&ay.join("crates/ay-pb/proofs/trust_vc").join(name), "proof fixture", 0o644);
    }
    TestGit::run(&ay, &["add", "."]);
    TestGit::run(&ay, &["commit", "-qm", "proof fixtures"]);
    let control = root.join("control");
    let candidate = root.join("candidate");
    for seal in [&control, &candidate] {
        fixture_seal(seal);
        write(&seal.join("tool-provenance.json"), "{\"schema\":\"unvalidated-fixture\"}\n", 0o644);
        reseal(seal);
    }
    let control = fs::canonicalize(control).unwrap();
    let candidate = fs::canonicalize(candidate).unwrap();
    let spec = root.join("spec.rs");
    write(&spec, "scaffold", 0o644);
    pair::Request {
        control,
        candidate_receipt: candidate.join("tool-provenance.json"),
        candidate,
        candidate_commit: COMMIT.into(),
        ay,
        trust_vc: vc,
        trust_spec_source: spec,
        cargo_home: root.join("cargo-home"),
        dependency_roots: Vec::new(),
    }
}

fn reseal(root: &Path) {
    let identity = seal::identity(root).unwrap();
    write(
        &root.join("PROVENANCE"),
        format!(
            "sealed_by=scripts/promote-toolchain.sh\nreported_commit={COMMIT}\nartifact_content_scope={}\nartifact_content_sha256={}\n",
            seal::SCOPE,
            identity.sha256
        ),
        0o644,
    );
}

#[test]
fn paired_runner_consumes_full_native_binding_without_granting_later_stages() {
    let temporary = TempDir::new().unwrap();
    let request = pair_fixture(&temporary);
    let inspected = pair::inspect(&TestGit, request).unwrap();
    let report = inspected.report();
    assert_eq!(report.stage, "input-inspection");
    assert_eq!(report.status, "inspected");
    assert!(report.pending_stages.contains(&"completed-stage-receipt-validation"));
    assert!(report.pending_stages.contains(&"admitted-supervised-execution"));
    assert_eq!(report.inputs.sources.len(), 2);
    assert_eq!(report.inputs.proof_fixtures.len(), 2);
    assert!(report.claim_scope.contains("no execution"));
    inspected.check_unchanged(&TestGit).unwrap();
}

/// Build only receipt statements for these test images. No test executable is
/// launched, and neither the fixture nor its seal authenticates a build.
fn fixture_receipt(root: &Path) -> serde_json::Value {
    let stage = "build/test-host/stage2";
    let sha = |relative: &str| pair::file_identity(&root.join(relative)).unwrap().sha256;
    let closure = "c".repeat(64);
    let tools = ["targo", "targo-trust", "trustd", "ay"]
        .into_iter()
        .map(|name| {
            let digest = sha(&format!("bin/{name}"));
            serde_json::json!({"name":name,"path":format!("{stage}/bin/{name}"),
                "status":"bound","sha256":digest,"producer_sha256":digest})
        })
        .collect::<Vec<_>>();
    serde_json::json!({
        "schema":"trust.stage-tool-provenance.v2", "status":"internal-release-ready",
        "tool_binding_status":"ready", "errors":[], "path_scope":"repository-root-relative",
        "stage_root":stage, "stage":2, "source_tree_clean":true, "trust_from_trust":true,
        "bootstrap_lineage":{"schema":"trust.bootstrap-lineage.v1", "mode":"seed",
            "status":"trust_from_trust", "trust_from_trust":true,"errors":[],
            "validated_seed":{"materialization_status":"fresh-from-validated-archives"}},
        "compiler":{"path":format!("{stage}/bin/trustc"),"compiler_sha256":sha("bin/trustc"),
            "compatibility_alias":format!("{stage}/bin/rustc"),
            "compatibility_alias_sha256":sha("bin/rustc"),"source_commit":COMMIT},
        "rustdoc_alias":{"path":format!("{stage}/bin/rustdoc"),"sha256":sha("bin/rustdoc")},
        "proc_macro_helper":{"path":format!("{stage}/libexec/trust-analyzer-proc-macro-srv"),
            "sha256":sha("libexec/trust-analyzer-proc-macro-srv")},
        "source_lineage":{"schema":"trust.source-lineage.v1", "status":"immutable_release",
            "source_tree_clean":true,"errors":[],"stable_across_build":true,
            "closure_sha256":closure,"pre_build_closure_sha256":closure,
            "post_build_closure_sha256":closure,"repositories":[{"path":".","head":COMMIT}]},
        "tools":tools, "host":"test-host"
    })
}

fn install_fixture_receipt(root: &Path, value: &serde_json::Value) {
    write(&root.join("tool-provenance.json"), serde_json::to_vec(value).unwrap(), 0o644);
    reseal(root);
}

pub(crate) fn receipt_pair_fixture(temporary: &TempDir) -> pair::Request {
    let request = pair_fixture(temporary);
    for root in [&request.candidate, &request.control] {
        install_fixture_receipt(root, &fixture_receipt(root));
    }
    request
}

#[test]
fn native_receipt_stage_consumes_original_owner_and_keeps_later_predicates_pending() {
    let temporary = TempDir::new().unwrap();
    let request = receipt_pair_fixture(&temporary);
    let checked = pair::inspect(&TestGit, request).unwrap().check_receipts(&TestGit).unwrap();
    let report = checked.report();
    assert_eq!(report.stage, "stage-receipt-validation");
    assert_eq!(report.status, "receipts-checked");
    assert!(!report.pending_stages.contains(&"completed-stage-receipt-validation"));
    assert!(report.pending_stages.contains(&"actual-compiler-identity-probes"));
    assert!(report.pending_stages.contains(&"admitted-supervised-execution"));
    assert_eq!(report.candidate_receipt.listed_files_verified, 8);
    assert_eq!(report.control_receipt.listed_files_verified, 8);
    assert_eq!(
        report.candidate_receipt.raw_sha256,
        Some(report.inputs.candidate_receipt.sha256.as_str())
    );
    assert_eq!(report.declared_candidate_source_closure_sha256, "c".repeat(64));
    assert!(report.claim_scope.contains("self-reported"));
    assert!(report.claim_scope.contains("no execution"));
    assert!(report.candidate_receipt.llvm_identity_unstated_reason.contains("no llvm_identity"));
    checked.check_unchanged(&TestGit).unwrap();
}

#[test]
fn compiler_probe_owner_rechecks_original_inputs_after_native_runner_failure() {
    use trust_resource_controller::{MetadataBatch, MetadataBatchReport};

    use crate::probes::MetadataRunner;
    struct Runner {
        image: pair::FileIdentity,
        mutate: std::path::PathBuf,
        called: usize,
    }
    impl MetadataRunner for Runner {
        fn service_image(&self) -> crate::Result<pair::FileIdentity> {
            Ok(self.image.clone())
        }
        fn collect(&mut self, _batch: &MetadataBatch) -> crate::Result<MetadataBatchReport> {
            self.called += 1;
            fs::write(&self.mutate, "changed while native runner refused").unwrap();
            Err(crate::refusal("retained native runner failure"))
        }
        fn execution_observation(&self) -> Option<serde_json::Value> {
            Some(serde_json::json!({"native_transport":"failed-evidence-retained"}))
        }
    }
    let temporary = TempDir::new().unwrap();
    let request = receipt_pair_fixture(&temporary);
    let checked =
        pair::inspect(&TestGit, request.clone()).unwrap().check_receipts(&TestGit).unwrap();
    let original = serde_json::to_value(checked.snapshot()).unwrap();
    let mut runner = Runner {
        image: pair::file_identity(&request.candidate.join("bin/targo")).unwrap(),
        mutate: request.ay.join("Cargo.lock"),
        called: 0,
    };
    let attempt = checked.probe_compilers(&TestGit, &mut runner);
    assert_eq!(runner.called, 1);
    assert!(!attempt.consistent());
    let report = attempt.report();
    assert_eq!(report["receipts"]["inputs"], original);
    assert!(
        report["errors"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e.as_str().unwrap().contains("retained native runner failure"))
    );
    assert!(
        report["errors"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e.as_str().unwrap().contains("original inputs after metadata probes"))
    );
    assert_eq!(report["execution"]["native_transport"], "failed-evidence-retained");
    assert!(
        report["pending_stages"]
            .as_array()
            .unwrap()
            .iter()
            .any(|stage| stage == "actual-compiler-identity-probes")
    );
}

#[test]
fn compiler_probe_preflight_drift_never_calls_a_runner_or_replaces_the_snapshot() {
    use trust_resource_controller::{MetadataBatch, MetadataBatchReport};

    use crate::probes::MetadataRunner;
    struct Never;
    impl MetadataRunner for Never {
        fn service_image(&self) -> crate::Result<pair::FileIdentity> {
            panic!("preflight drift must precede runner selection")
        }
        fn collect(&mut self, _: &MetadataBatch) -> crate::Result<MetadataBatchReport> {
            panic!("changed inputs must never execute")
        }
    }
    let temporary = TempDir::new().unwrap();
    let request = receipt_pair_fixture(&temporary);
    let checked =
        pair::inspect(&TestGit, request.clone()).unwrap().check_receipts(&TestGit).unwrap();
    let original = serde_json::to_value(checked.snapshot()).unwrap();
    fs::write(request.ay.join("Cargo.lock"), "preflight changed").unwrap();
    let attempt = checked.probe_compilers(&TestGit, &mut Never);
    assert!(!attempt.consistent());
    assert_eq!(attempt.report()["receipts"]["inputs"], original);
    assert!(attempt.report()["metadata"].is_null());
}

#[test]
fn input_inspection_does_not_silently_claim_to_validate_a_placeholder_receipt() {
    let temporary = TempDir::new().unwrap();
    let request = pair_fixture(&temporary);
    let inspected = pair::inspect(&TestGit, request).unwrap();
    assert!(inspected.report().pending_stages.contains(&"completed-stage-receipt-validation"));
    assert!(inspected.check_receipts(&TestGit).unwrap_err().0.contains("schema"));
}

#[test]
fn receipt_stage_refuses_incomplete_or_inconsistent_candidate_statements() {
    for mutation in 0..7 {
        let temporary = TempDir::new().unwrap();
        let request = receipt_pair_fixture(&temporary);
        let mut value = fixture_receipt(&request.candidate);
        match mutation {
            0 => value["stage"] = serde_json::json!(2.0),
            1 => value["source_lineage"]["stable_across_build"] = serde_json::json!(false),
            2 => {
                value["source_lineage"]["repositories"][0]["head"] =
                    serde_json::json!("a".repeat(40))
            }
            3 => {
                value["source_lineage"]["post_build_closure_sha256"] =
                    serde_json::json!("d".repeat(64))
            }
            4 => value["tools"][0]["sha256"] = serde_json::json!("e".repeat(64)),
            5 => value["tools"][0]["name"] = serde_json::json!("something-else"),
            6 => value["stage"] = serde_json::json!({"$serde_json::private::Number":"2"}),
            _ => unreachable!(),
        }
        install_fixture_receipt(&request.candidate, &value);
        let inspected = pair::inspect(&TestGit, request).unwrap();
        assert!(inspected.check_receipts(&TestGit).is_err(), "candidate mutation {mutation}");
    }
}

#[test]
fn receipt_stage_rebinds_original_inputs_and_cannot_adopt_a_resealed_substitute() {
    for mutation in 0..3 {
        let temporary = TempDir::new().unwrap();
        let request = receipt_pair_fixture(&temporary);
        let inspected = pair::inspect(&TestGit, request.clone()).unwrap();
        match mutation {
            0 => {
                let mut data = fixture_receipt(&request.candidate);
                data["annotation"] = serde_json::json!("new receipt, otherwise valid");
                install_fixture_receipt(&request.candidate, &data);
            }
            1 => write(&request.trust_spec_source, "changed scaffold", 0o644),
            2 => write(&request.candidate.join(DATA[2]), "changed std", 0o644),
            _ => unreachable!(),
        }
        assert!(inspected.check_receipts(&TestGit).is_err(), "input mutation {mutation}");
    }
}

#[test]
fn control_receipt_absence_is_disclosed_and_a_malformed_present_control_refuses() {
    for present in [false, true] {
        let temporary = TempDir::new().unwrap();
        let request = receipt_pair_fixture(&temporary);
        if present {
            write(&request.control.join("tool-provenance.json"), b"{}", 0o644);
        } else {
            fs::remove_file(request.control.join("tool-provenance.json")).unwrap();
        }
        reseal(&request.control);
        let result = pair::inspect(&TestGit, request).unwrap().check_receipts(&TestGit);
        if present {
            assert!(result.unwrap_err().0.contains("control stage receipt"));
        } else {
            let checked = result.unwrap();
            let report = checked.report();
            assert_eq!(report.control_receipt.state, "absent");
            assert_eq!(report.control_receipt.raw_sha256, None);
            assert_eq!(report.control_receipt.listed_files_verified, 0);
        }
    }
}

#[test]
fn checked_receipts_do_not_replace_later_original_input_custody() {
    let temporary = TempDir::new().unwrap();
    let request = receipt_pair_fixture(&temporary);
    let checked =
        pair::inspect(&TestGit, request.clone()).unwrap().check_receipts(&TestGit).unwrap();
    assert_eq!(checked.report().status, "receipts-checked");
    // Creating an ambient config after receipt validation must invalidate the
    // retained original owner even though all receipt/executable bytes match.
    write(&request.cargo_home.join("config.toml"), "[build]\njobs=1\n", 0o644);
    assert!(checked.check_unchanged(&TestGit).unwrap_err().0.contains("input changed"));
}

#[test]
fn adding_native_receipt_checks_preserves_incumbent_json_object_semantics() {
    // This dependency is shared with unrelated compiler validators. A receipt
    // reader must not globally enable serde's private-number interpretation.
    let value: serde_json::Value =
        serde_json::from_slice(br#"{"$serde_json::private::Number":"2"}"#).unwrap();
    assert!(value.is_object());
    assert_eq!(value["$serde_json::private::Number"], "2");
}

/// Exercise the actual product entry point after building its image. Inputs,
/// raw output and reports survive assertions for independent diagnosis.
#[test]
#[ignore = "requires TRUST_QUALIFICATION_FRONTEND and its exact TRUST_QUALIFICATION_FRONTEND_SHA256"]
fn real_native_cli_receipts_preserve_scope_refusals_and_no_clobber() {
    let frontend = std::path::PathBuf::from(
        std::env::var_os("TRUST_QUALIFICATION_FRONTEND").expect("select built native frontend"),
    );
    let expected = std::env::var("TRUST_QUALIFICATION_FRONTEND_SHA256")
        .expect("bind exact independently inventoried frontend bytes");
    assert!(crate::canonical_hex(&expected, 64));
    assert_eq!(pair::file_identity(&frontend).unwrap().sha256, expected);
    let evidence = TempDir::new().unwrap().keep();
    eprintln!("retained native CLI inputs and results: {}", evidence.display());

    for case in 0..4 {
        let temporary = TempDir::new_in(&evidence).unwrap();
        let root = temporary.path().to_owned();
        let mut request = pair_fixture(&temporary);
        let marker = root.join("compiler-was-executed");
        let quoted_marker = format!("'{}'", marker.to_str().unwrap().replace('\'', "'\"'\"'"));
        // Receipt checks must never run even the exact executables they bind.
        // Give every such image a visible side effect if that boundary regresses.
        for seal in [&request.candidate, &request.control] {
            for relative in EXECUTABLES {
                write(
                    &seal.join(relative),
                    format!("#!/bin/sh\n: > {quoted_marker}\nexit 0\n"),
                    0o755,
                );
            }
            if case != 1 {
                install_fixture_receipt(seal, &fixture_receipt(seal));
            } else {
                reseal(seal);
            }
        }
        match case {
            2 => request.candidate_commit = "a".repeat(40),
            3 => write(&request.ay.join("lib.rs"), "changed source", 0o644),
            _ => {}
        }
        let invocation = std::cell::Cell::new(0usize);
        let run = |stage: &str, name: &str| {
            let ordinal = invocation.get();
            invocation.set(ordinal + 1);
            let report_path = root.join(format!("{name}.json"));
            let output = Command::new(&frontend)
                .env_clear()
                .env("PATH", "/usr/bin:/bin")
                .env("HOME", &root)
                .env("CARGO_HOME", &request.cargo_home)
                .args(["gate", "qualify-pair", stage, "--control"])
                .arg(&request.control)
                .arg("--candidate")
                .arg(&request.candidate)
                .arg("--candidate-receipt")
                .arg(&request.candidate_receipt)
                .arg("--candidate-commit")
                .arg(&request.candidate_commit)
                .arg("--ay")
                .arg(&request.ay)
                .arg("--trust-vc")
                .arg(&request.trust_vc)
                .arg("--trust-spec-source")
                .arg(&request.trust_spec_source)
                .arg("--out")
                .arg(&report_path)
                .output()
                .unwrap();
            fs::write(root.join(format!("{name}-{ordinal}.stdout")), &output.stdout).unwrap();
            fs::write(root.join(format!("{name}-{ordinal}.stderr")), &output.stderr).unwrap();
            fs::write(
                root.join(format!("{name}-{ordinal}.exit.json")),
                serde_json::to_vec(&serde_json::json!({
                    "success": output.status.success(), "code": output.status.code(),
                }))
                .unwrap(),
            )
            .unwrap();
            let bytes = fs::read(&report_path)
                .unwrap_or_else(|error| panic!("case {case}, missing report: {error}; {output:?}"));
            let report: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
            assert!(!marker.exists(), "case {case} executed a bound compiler image");
            assert_eq!(pair::file_identity(&frontend).unwrap().sha256, expected);
            (output.status, report, bytes)
        };
        // Persist before assertions, including the deliberately rejected inputs.
        let _retained = temporary.keep();
        let (status, report, bytes) = run("receipts", "receipts");
        assert_eq!(status.success(), case == 0, "case {case}: {report}");
        assert_eq!(report["stage"], "stage-receipt-validation");
        assert!(report["claim_scope"].as_str().unwrap().contains("no execution"));
        if case == 0 {
            assert_eq!(report["status"], "receipts-checked");
            assert_eq!(report["candidate_receipt"]["listed_files_verified"], 8);
            assert_eq!(report["control_receipt"]["listed_files_verified"], 8);
            assert_eq!(report["runner_image_observation"]["sha256"], expected);
            let pending = report["pending_stages"].as_array().unwrap();
            assert!(!pending.iter().any(|stage| stage == "completed-stage-receipt-validation"));
            assert!(pending.iter().any(|stage| stage == "actual-compiler-identity-probes"));
            assert!(pending.iter().any(|stage| stage == "admitted-supervised-execution"));
            let (again, _, retained) = run("receipts", "receipts");
            assert!(!again.success(), "existing result must not be overwritten");
            assert_eq!(retained, bytes);
        } else {
            assert_eq!(report["status"], "refused");
            let reason = report["reason"].as_str().unwrap();
            let expected_reason = match case {
                1 => "schema",
                2 => "commit",
                3 => "dirty",
                _ => unreachable!(),
            };
            assert!(reason.contains(expected_reason), "case {case}: {reason}");
            if case == 1 {
                let (inspection, report, _) = run("inspect", "inspection");
                assert!(inspection.success(), "input inspection remains its own stage: {report}");
                assert_eq!(report["stage"], "input-inspection");
                assert!(
                    report["pending_stages"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|stage| { stage == "completed-stage-receipt-validation" })
                );
            }
        }
    }
}

#[test]
fn paired_runner_refuses_stale_commit_missing_receipt_and_modified_library() {
    for mutation in 0..3 {
        let temporary = TempDir::new().unwrap();
        let mut request = pair_fixture(&temporary);
        match mutation {
            0 => request.candidate_commit = "a".repeat(40),
            1 => request.candidate_receipt = temporary.path().join("missing"),
            2 => write(&request.candidate.join(DATA[0]), "changed library", 0o644),
            _ => unreachable!(),
        }
        assert!(pair::inspect(&TestGit, request).is_err(), "mutation {mutation}");
    }
}

#[test]
fn paired_runner_binds_cargo_configuration_absence_scaffold_and_fixture_bytes() {
    for mutation in 0..3 {
        let temporary = TempDir::new().unwrap();
        let request = pair_fixture(&temporary);
        let inspected = pair::inspect(&TestGit, request.clone()).unwrap();
        match mutation {
            0 => write(&request.ay.join(".cargo/config.toml"), "[build]\njobs=2\n", 0o644),
            1 => write(&request.trust_spec_source, "changed scaffold", 0o644),
            2 => write(
                &request.ay.join("crates/ay-pb/proofs/trust_vc/refutation_step_realbody.rs"),
                "changed proof",
                0o644,
            ),
            _ => unreachable!(),
        }
        assert!(inspected.check_unchanged(&TestGit).is_err(), "mutation {mutation}");
    }
}

#[test]
fn same_seal_control_is_valid_input_inspection_without_claiming_improvement() {
    let temporary = TempDir::new().unwrap();
    let mut request = pair_fixture(&temporary);
    request.control = request.candidate.clone();
    let inspected = pair::inspect(&TestGit, request).unwrap();
    assert_eq!(inspected.snapshot().control, inspected.snapshot().candidate);
    assert!(inspected.report().claim_scope.contains("no execution"));
}

#[test]
fn paired_inspection_rejects_duplicate_provenance_and_receipt_substitution() {
    for mutation in 0..2 {
        let temporary = TempDir::new().unwrap();
        let mut request = pair_fixture(&temporary);
        if mutation == 0 {
            let path = request.candidate.join("PROVENANCE");
            let text = fs::read_to_string(&path).unwrap()
                + "reported_commit=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n";
            write(&path, text, 0o644);
        } else {
            let receipt = temporary.path().join("receipt.json");
            write(&receipt, "substituted", 0o644);
            request.candidate_receipt = receipt;
        }
        assert!(pair::inspect(&TestGit, request).is_err());
    }
}

#[test]
fn paired_toolchain_links_cannot_escape_even_when_the_link_text_is_sealed() {
    let temporary = TempDir::new().unwrap();
    let request = pair_fixture(&temporary);
    write(&temporary.path().join("foreign-library"), "foreign", 0o644);
    symlink(temporary.path().join("foreign-library"), request.candidate.join("lib/foreign.dylib"))
        .unwrap();
    reseal(&request.candidate);
    assert!(pair::inspect(&TestGit, request).unwrap_err().to_string().contains("link escapes"));
}

#[test]
fn excluded_seal_record_hop_cannot_change_the_selected_covered_library_silently() {
    let temporary = TempDir::new().unwrap();
    let request = pair_fixture(&temporary);
    let candidate = &request.candidate;
    write(&candidate.join("lib/choice-a"), "selected A", 0o644);
    write(&candidate.join("lib/choice-b"), "selected B", 0o644);
    fs::remove_file(candidate.join("SEED-MINT")).unwrap();
    symlink("lib/choice-a", candidate.join("SEED-MINT")).unwrap();
    symlink("../SEED-MINT", candidate.join("lib/selected.dylib")).unwrap();
    reseal(candidate);
    let first = pair::inspect(&TestGit, request.clone()).unwrap();
    assert_eq!(fs::read(candidate.join("lib/selected.dylib")).unwrap(), b"selected A");
    let old_content = first.snapshot().candidate.content.clone();
    fs::remove_file(candidate.join("SEED-MINT")).unwrap();
    symlink("lib/choice-b", candidate.join("SEED-MINT")).unwrap();
    assert_eq!(fs::read(candidate.join("lib/selected.dylib")).unwrap(), b"selected B");
    assert_eq!(
        seal::identity(candidate).unwrap(),
        old_content,
        "seal-content-v1 remains compatible"
    );
    assert!(
        first.check_unchanged(&TestGit).is_err(),
        "paired binding must detect changed selected library"
    );
}

#[test]
fn excluded_promotion_record_bytes_and_absence_remain_frozen_pair_inputs() {
    for name in ["SEED-MINT", "STAGE0-LINEAGE", "PROVENANCE.build-status"] {
        let temporary = TempDir::new().unwrap();
        let request = pair_fixture(&temporary);
        let inspected = pair::inspect(&TestGit, request.clone()).unwrap();
        let content = inspected.snapshot().candidate.content.clone();
        write(&request.candidate.join(name), "changed record", 0o644);
        assert_eq!(seal::identity(&request.candidate).unwrap(), content);
        assert!(inspected.check_unchanged(&TestGit).is_err(), "changed {name}");
    }
}

#[test]
fn committed_internal_symlink_chains_remain_valid_after_selected_target_binding() {
    let temporary = TempDir::new().unwrap();
    repository(temporary.path());
    symlink("lib.rs", temporary.path().join("first-link.rs")).unwrap();
    symlink("first-link.rs", temporary.path().join("second-link.rs")).unwrap();
    TestGit::run(temporary.path(), &["add", "."]);
    TestGit::run(temporary.path(), &["commit", "-qm", "committed valid chain"]);
    let first = source::identity(&TestGit, temporary.path(), true, false).unwrap();
    assert_eq!(first, source::identity(&TestGit, temporary.path(), true, false).unwrap());
}
