use super::*;

#[test]
fn canonical_cargo_dist_names() {
    // Trust: each tool is copied in once, under its Trust name; its stock name is a
    // hard link to that file (`stock_name_link`), never a second copy.
    for (triple, expected) in
        [("x86_64-unknown-linux-gnu", "targo"), ("x86_64-pc-windows-msvc", "targo.exe")]
    {
        assert_eq!(cargo_dist_bin_names(TargetSelection::from_user(triple)), [expected]);
    }
}

#[test]
fn canonical_compiler_dist_names() {
    // Trust: check the target suffix without restoring an alias in the distribution.
    for (triple, expected) in
        [("x86_64-unknown-linux-gnu", "trustc"), ("x86_64-pc-windows-msvc", "trustc.exe")]
    {
        assert_eq!(compiler_dist_bin_names(TargetSelection::from_user(triple)), [expected]);
    }
}

#[test]
fn canonical_secondary_dist_names() {
    // Trust: both secondary tools keep their canonical names on each target.
    for (triple, doc, proc_macro) in [
        ("x86_64-unknown-linux-gnu", "trustdoc", "trust-analyzer-proc-macro-srv"),
        ("x86_64-pc-windows-msvc", "trustdoc.exe", "trust-analyzer-proc-macro-srv.exe"),
    ] {
        let target = TargetSelection::from_user(triple);
        assert_eq!(trustdoc_dist_bin_names(target), [doc]);
        assert_eq!(rust_analyzer_proc_macro_dist_bin_names(target), [proc_macro]);
    }
}

#[test]
fn tippy_dist_exposes_direct_subcommand_and_driver_bins() {
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");

    assert_eq!(
        tippy_dist_bin_names(target),
        ["tippy".to_string(), "targo-tippy".to_string(), "tippy-driver".to_string()]
    );
}

#[test]
fn debugger_scripts_install_only_canonical_trust_entrypoints() {
    let linux = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let linux_names = debugger_script_entrypoints(linux)
        .into_iter()
        .map(|(_, destination)| destination)
        .collect::<Vec<_>>();
    assert_eq!(linux_names, ["trust-gdb", "trust-gdbgui", "trust-lldb"]);

    let windows = TargetSelection::from_user("x86_64-pc-windows-msvc");
    let windows_names = debugger_script_entrypoints(windows)
        .into_iter()
        .map(|(_, destination)| destination)
        .collect::<Vec<_>>();
    assert_eq!(windows_names, ["trust-windbg.cmd", "trust-gdb", "trust-gdbgui", "trust-lldb"]);

    assert!(linux_names.iter().all(|name| !name.starts_with("rust-")));
    assert!(windows_names.iter().all(|name| !name.starts_with("rust-")));
}

#[test]
fn stock_names_are_the_three_aliases_the_toolchain_contract_admits() {
    assert_eq!(
        STOCK_NAME_LINKS,
        [("trustc", "rustc"), ("trustdoc", "rustdoc"), ("targo", "cargo")]
    );
    for (triple, suffix) in [("x86_64-unknown-linux-gnu", ""), ("x86_64-pc-windows-msvc", ".exe")] {
        let target = TargetSelection::from_user(triple);
        for (trust, stock) in STOCK_NAME_LINKS {
            assert_eq!(
                stock_name_link(target, trust),
                (format!("{trust}{suffix}"), format!("{stock}{suffix}"))
            );
        }
        // Each stock name hangs off a Trust file its component actually ships.
        assert!(compiler_dist_bin_names(target).contains(&stock_name_link(target, "trustc").0));
        assert!(trustdoc_dist_bin_names(target).contains(&stock_name_link(target, "trustdoc").0));
        assert!(cargo_dist_bin_names(target).contains(&stock_name_link(target, "targo").0));
    }

    // None is a stock spelling the complete-toolchain contract forbids: promotion
    // would refuse a toolchain that carried it.
    let surface = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/lib/trust_toolchain_surface.sh"),
    )
    .expect("read the toolchain surface contract");
    let forbidden = surface
        .lines()
        .find_map(|line| line.strip_prefix("TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_BINS='"))
        .and_then(|rest| rest.strip_suffix('\''))
        .expect("the contract names its forbidden public bins");
    assert!(forbidden.split_whitespace().any(|name| name == "rustfmt"), "{forbidden}");
    for (_, stock) in STOCK_NAME_LINKS {
        assert!(!forbidden.split_whitespace().any(|name| name == stock), "{stock}: {forbidden}");
    }
}

#[test]
fn a_stock_name_is_a_hard_link_to_its_trust_file_in_the_same_bin() {
    let dir = tempfile::tempdir().unwrap();
    let bin = dir.path().join("bin");
    fs::create_dir(&bin).unwrap();
    fs::write(bin.join("trustc"), b"the trustc image").unwrap();
    // A previous dist run's copy (or link) under the stock name is replaced.
    fs::write(bin.join("rustc"), b"a stale second copy").unwrap();

    hard_link_stock_name(&bin, "trustc", "rustc").unwrap();
    assert_eq!(fs::read(bin.join("rustc")).unwrap(), b"the trustc image");
    // Laying it again changes nothing: still one file under two names.
    hard_link_stock_name(&bin, "trustc", "rustc").unwrap();

    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;

        let trust = fs::symlink_metadata(bin.join("trustc")).unwrap();
        let stock = fs::symlink_metadata(bin.join("rustc")).unwrap();
        assert!(stock.file_type().is_file(), "a hard link, not a symlink");
        assert_eq!((stock.dev(), stock.ino()), (trust.dev(), trust.ino()), "one file");
        assert_eq!(trust.nlink(), 2, "exactly the Trust name and the stock name");
    }
    let mut names = fs::read_dir(&bin)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(names, ["rustc", "trustc"], "nothing is laid outside the one bin/");
    assert_eq!(fs::read_dir(dir.path()).unwrap().count(), 1);
}

#[test]
fn a_stock_name_never_leaves_its_bin_dir() {
    let dir = tempfile::tempdir().unwrap();
    let bin = dir.path().join("bin");
    let other = dir.path().join("lib");
    fs::create_dir(&bin).unwrap();
    fs::create_dir(&other).unwrap();
    fs::write(bin.join("trustc"), b"trustc").unwrap();
    fs::write(other.join("trustc"), b"another directory's trustc").unwrap();

    for (trust, stock) in [
        ("trustc", "../lib/rustc"),
        ("trustc", "sub/rustc"),
        ("trustc", ".."),
        ("trustc", ""),
        ("../lib/trustc", "rustc"),
        ("./trustc", "rustc"),
    ] {
        let error = hard_link_stock_name(&bin, trust, stock).unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::InvalidInput, "{trust} -> {stock}");
    }
    assert!(!other.join("rustc").exists());
    assert!(!bin.join("rustc").exists());
}

#[test]
fn a_stock_name_needs_a_regular_trust_file() {
    let dir = tempfile::tempdir().unwrap();
    let bin = dir.path().join("bin");
    fs::create_dir(&bin).unwrap();

    // Missing: nothing to link.
    assert_eq!(
        hard_link_stock_name(&bin, "trustc", "rustc").unwrap_err().kind(),
        std::io::ErrorKind::NotFound
    );
    // A directory under the Trust name.
    fs::create_dir(bin.join("trustdoc")).unwrap();
    assert_eq!(
        hard_link_stock_name(&bin, "trustdoc", "rustdoc").unwrap_err().kind(),
        std::io::ErrorKind::InvalidInput
    );
    // A symlink under the Trust name: the stock name would be a second name of
    // whatever the link points at, which may be in another directory.
    #[cfg(unix)]
    {
        fs::write(dir.path().join("targo"), b"elsewhere").unwrap();
        std::os::unix::fs::symlink(dir.path().join("targo"), bin.join("targo")).unwrap();
        assert_eq!(
            hard_link_stock_name(&bin, "targo", "cargo").unwrap_err().kind(),
            std::io::ErrorKind::InvalidInput
        );
    }
    assert!(!bin.join("rustc").exists() && !bin.join("rustdoc").exists());
    assert!(!bin.join("cargo").exists());
}

// Off macOS `copy_link` hard-links an executable into the image from the build tree, so
// the image's Trust file can be one name of an inode that also lives outside `bin/`.
// The stock name must still be the second of exactly two names, both in `bin/`.
#[cfg(unix)]
#[test]
fn a_trust_file_shared_with_the_build_tree_is_detached_before_its_stock_name_is_linked() {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let dir = tempfile::tempdir().unwrap();
    let build = dir.path().join("build");
    let bin = dir.path().join("image/bin");
    fs::create_dir_all(&build).unwrap();
    fs::create_dir_all(&bin).unwrap();
    let source = build.join("trustc");
    fs::write(&source, b"the trustc image").unwrap();
    fs::set_permissions(&source, fs::Permissions::from_mode(0o755)).unwrap();
    // What `copy_link(.., FileType::Executable)` lays where `may_hard_link` is true.
    fs::hard_link(&source, bin.join("trustc")).unwrap();
    assert_eq!(fs::metadata(&source).unwrap().nlink(), 2);

    hard_link_stock_name(&bin, "trustc", "rustc").unwrap();
    // Laying it again keeps the pair (a previous run's link is not counted as shared).
    hard_link_stock_name(&bin, "trustc", "rustc").unwrap();

    let trust = fs::symlink_metadata(bin.join("trustc")).unwrap();
    let stock = fs::symlink_metadata(bin.join("rustc")).unwrap();
    let original = fs::symlink_metadata(&source).unwrap();
    assert_eq!((stock.dev(), stock.ino()), (trust.dev(), trust.ino()), "one file");
    assert_eq!(trust.nlink(), 2, "exactly the Trust name and the stock name");
    assert_ne!(original.ino(), trust.ino(), "the build tree's file is not a third name");
    assert_eq!(original.nlink(), 1);
    assert_eq!(fs::read(bin.join("rustc")).unwrap(), b"the trustc image");
    assert_eq!(trust.permissions().mode() & 0o7777, 0o755);
    let mut names = fs::read_dir(&bin)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(names, ["rustc", "trustc"], "no staging file is left in bin/");
}

#[test]
fn the_trust_channel_names_its_archives_version_trust() {
    // The names src/stage0 pins and the pack cut admits.
    assert_eq!(crate::core::session::package_vers("trust", "0.11.0"), "0.11.0-trust");
    assert_eq!(crate::core::session::package_vers("stable", "1.0.0"), "1.0.0");
    assert_eq!(crate::core::session::package_vers("nightly", "1.0.0"), "nightly");
    assert_eq!(crate::core::session::package_vers("dev", "1.0.0"), "1.0.0-dev");
}

#[test]
fn the_targo_dist_reads_files_the_tree_has() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let etc = cargo_etc_dir(&src);
    for file in ["_cargo", "cargo.bashcomp.sh"] {
        assert!(etc.join(file).is_file(), "{} is not a file", etc.join(file).display());
    }
    assert!(etc.join("man").is_dir(), "{} is not a directory", etc.join("man").display());
}
