use std::fs::{self, File};
use std::io::Write;
use std::path::PathBuf;

use crate::utils::helpers::{
    check_cfg_arg, envify, extract_beta_rev, hex_encode, make, set_file_times,
    stage0_release_is_local_rebuild, submodule_path_of_paths, symlink_dir,
};
use crate::utils::tests::TestCtx;

#[test]
fn test_make() {
    for (host, make_path) in vec![
        ("dragonfly", PathBuf::from("gmake")),
        ("netbsd", PathBuf::from("gmake")),
        ("freebsd", PathBuf::from("gmake")),
        ("openbsd", PathBuf::from("gmake")),
        ("linux", PathBuf::from("make")),
        // for checking the default
        ("_", PathBuf::from("make")),
    ] {
        assert_eq!(make(host), make_path);
    }
}

#[test]
fn test_beta_rev_parsing() {
    // single digit revision
    assert_eq!(extract_beta_rev("1.99.9-beta.7 (xxxxxx)"), Some("7".to_string()));
    // multiple digits
    assert_eq!(extract_beta_rev("1.99.9-beta.777 (xxxxxx)"), Some("777".to_string()));
    // nightly channel (no beta revision)
    assert_eq!(extract_beta_rev("1.99.9-nightly (xxxxxx)"), None);
    // stable channel (no beta revision)
    assert_eq!(extract_beta_rev("1.99.9 (xxxxxxx)"), None);
    // invalid string
    assert_eq!(extract_beta_rev("invalid"), None);
}

#[test]
fn test_string_to_hex_encode() {
    let input_string = "Hello, World!";
    let hex_string = hex_encode(input_string);
    assert_eq!(hex_string, "48656c6c6f2c20576f726c6421");
}

#[test]
fn test_check_cfg_arg() {
    assert_eq!(check_cfg_arg("bootstrap", None), "--check-cfg=cfg(bootstrap)");
    assert_eq!(
        check_cfg_arg("target_arch", Some(&["s360"])),
        "--check-cfg=cfg(target_arch,values(\"s360\"))"
    );
    assert_eq!(
        check_cfg_arg("target_os", Some(&["nixos", "nix2"])),
        "--check-cfg=cfg(target_os,values(\"nixos\",\"nix2\"))"
    );
}

#[test]
fn test_symlink_dir() {
    let config = TestCtx::new().config("check").no_dry_run().create_config();
    let tempdir = config.tempdir().join(".tmp-dir");
    let link_path = config.tempdir().join(".tmp-link");

    fs::create_dir_all(&tempdir).unwrap();
    symlink_dir(&config, &tempdir, &link_path).unwrap();

    let link_source = fs::read_link(&link_path).unwrap();
    assert_eq!(link_source, tempdir);

    fs::remove_dir(tempdir).unwrap();

    #[cfg(windows)]
    fs::remove_dir(link_path).unwrap();
    #[cfg(not(windows))]
    fs::remove_file(link_path).unwrap();
}

#[test]
fn test_set_file_times_sanity_check() {
    let config = TestCtx::new().config("check").create_config();
    let tempfile = config.tempdir().join(".tmp-file");

    {
        File::create(&tempfile).unwrap().write_all(b"dummy value").unwrap();
        assert!(tempfile.exists());
    }

    // This might only fail on Windows (if file is default read-only then we try to modify file
    // times).
    let unix_epoch = std::time::SystemTime::UNIX_EPOCH;
    let target_time = fs::FileTimes::new().set_accessed(unix_epoch).set_modified(unix_epoch);
    set_file_times(&tempfile, target_time).unwrap();

    let found_metadata = fs::metadata(tempfile).unwrap();
    assert_eq!(found_metadata.accessed().unwrap(), unix_epoch);
    assert_eq!(found_metadata.modified().unwrap(), unix_epoch)
}

#[test]
fn test_submodule_path_of() {
    let submodules = vec!["src/tools/cargo".to_string(), "src/llvm-project".to_string()];

    assert_eq!(submodule_path_of_paths(&submodules, "invalid/path"), None);
    assert_eq!(
        submodule_path_of_paths(&submodules, "src/tools/cargo"),
        Some("src/tools/cargo".to_string())
    );
    assert_eq!(
        submodule_path_of_paths(&submodules, "src/llvm-project"),
        Some("src/llvm-project".to_string())
    );
    // Make sure subdirs are handled properly
    assert_eq!(
        submodule_path_of_paths(&submodules, "src/tools/cargo/random-subdir"),
        Some("src/tools/cargo".to_string())
    );
    // Make sure paths that only share a string prefix with a submodule are not matched.
    assert_eq!(submodule_path_of_paths(&submodules, "src/tools/cargo-vendor"), None);

    // Trust: Targo and the LLVM tree are vendored as ordinary tracked source in
    // this repository, not gitlinks, so they never appear in the real submodule
    // list; the `first-party/*` siblings are the actual submodules. Asserting the
    // upstream topology here made bootstrap's discovery tests require a topology
    // that does not exist.
    let trust_submodules = vec!["first-party/ay".to_string()];
    assert_eq!(submodule_path_of_paths(&trust_submodules, "src/tools/targo"), None);
    assert_eq!(submodule_path_of_paths(&trust_submodules, "src/llvm-project"), None);
    assert_eq!(
        submodule_path_of_paths(&trust_submodules, "first-party/ay"),
        Some("first-party/ay".to_string())
    );
    // Make sure subdirs are handled properly
    assert_eq!(
        submodule_path_of_paths(&trust_submodules, "first-party/ay/random-subdir"),
        Some("first-party/ay".to_string())
    );
}

#[test]
fn test_envify() {
    struct Case {
        input: &'static str,
        expected: &'static str,
    }
    let cases = &[
        Case { input: "x86_64-unknown-linux-gnu", expected: "X86_64_UNKNOWN_LINUX_GNU" },
        // Arbitrary target containing `.` from the tier-3 target list.
        Case { input: "thumbv8m.base-none-eabi", expected: "THUMBV8M_BASE_NONE_EABI" },
    ];

    for &Case { input, expected } in cases {
        let actual = envify(input);
        assert_eq!(actual, expected, "input = {input:?}");
    }
}

// Trust: a stage0 on this tree's Rust line (`src/rust-compat-version`) is a local rebuild; the
// seed `src/stage0` pins, and Trust's own `src/version` spelling, are not.
#[test]
fn test_stage0_release_is_local_rebuild() {
    let compat = "1.101.0";
    // A stage0 built from this tree (`build/host/stage1`), and later patch releases.
    assert!(stage0_release_is_local_rebuild("1.101.0-dev", compat));
    assert!(stage0_release_is_local_rebuild("1.101.0", compat));
    assert!(stage0_release_is_local_rebuild("1.101.3-nightly", compat));
    // The 0.11.0-trust and 1.99.0-trust seeds both report `release: 1.99.0-dev`.
    assert!(!stage0_release_is_local_rebuild("1.99.0-dev", compat));
    // Trust's own version line, which no stage0 reports.
    assert!(!stage0_release_is_local_rebuild("0.11.0", compat));
    // Minor versions are compared as components, not as string prefixes.
    assert!(!stage0_release_is_local_rebuild("1.10.0", compat));
    assert!(!stage0_release_is_local_rebuild("1.1010.0", compat));
    assert!(!stage0_release_is_local_rebuild("2.101.0", compat));
}
