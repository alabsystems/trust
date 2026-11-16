// Trust: controls for the native WP operation's execution/evidence boundaries.
use super::*;

fn suite(passed: u32) -> String {
    format!(
        "test result: ok. {passed} passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n"
    )
}

#[test]
fn all_declared_suites_must_execute_without_population_loss() {
    let complete = [suite(4), suite(12), suite(12), suite(1)].concat();
    assert!(completed_suites(&complete).is_ok());
    for missing in [String::new(), suite(4), [suite(4), suite(12), suite(1)].concat()] {
        assert!(completed_suites(&missing).is_err());
    }
    for mutation in [
        complete.replacen("4 passed", "0 passed", 1),
        complete.replacen("0 failed", "1 failed", 1),
        complete.replacen("0 ignored", "1 ignored", 1),
        complete.replacen("0 filtered", "1 filtered", 1),
        complete.replacen("ok.", "FAILED.", 1),
        complete.clone() + &suite(1),
    ] {
        assert!(completed_suites(&mutation).is_err(), "{mutation}");
    }
}

#[test]
fn seed_wrong_commit_host_and_duplicate_identity_fields_are_refused() {
    let current = "release: 1.101.0-nightly\ncommit-hash: current\nhost: aarch64-apple-darwin\n";
    let check =
        |text: &str| compiler_identity(text, "1.101.0-nightly", "current", "aarch64-apple-darwin");
    assert!(check(current).is_ok());
    for text in [
        current.replace("1.101.0", "1.99.0"),
        current.replace("current", "old"),
        current.replace("aarch64", "x86_64"),
        current.to_owned() + "commit-hash: current\n",
        "release: 1.101.0-nightly\n".to_owned(),
    ] {
        assert!(check(&text).is_err(), "{text}");
    }
}

#[test]
fn targo_requires_its_explicit_trust_root_identity() {
    let current = "release: 1.101.0-nightly\ncommit-hash: diagnostic\ntrust-repo-commit-hash: current\nhost: aarch64-apple-darwin\n";
    let check =
        |text: &str| targo_identity(text, "1.101.0-nightly", "current", "aarch64-apple-darwin");
    assert!(check(current).is_ok());
    for text in [
        current.replace("trust-repo-commit-hash: current\n", ""),
        current.replace("trust-repo-commit-hash: current", "trust-repo-commit-hash: old"),
        current.to_owned() + "trust-repo-commit-hash: current\n",
    ] {
        assert!(check(&text).is_err(), "{text}");
    }
}

#[test]
fn native_private_view_cannot_fall_back_to_sibling_or_cached_metadata() {
    let temp = tempfile::tempdir().unwrap();
    let root = fs::canonicalize(temp.path()).unwrap();
    let host = "aarch64-apple-darwin";
    let libdir = root.join("lib/rustlib").join(host).join("lib");
    fs::create_dir_all(&libdir).unwrap();
    for name in ["libstd-aa.rlib", "libcore-aa.rlib", "libtest-aa.rlib", "librustc_middle-aa.rmeta"]
    {
        fs::write(libdir.join(name), b"metadata fixture").unwrap();
    }
    let driver = root.join("lib/librustc_driver-aa.dylib");
    let private = libdir.join("librustc_driver-aa.dylib");
    fs::write(&driver, b"selected runtime").unwrap();
    fs::write(&private, b"selected runtime").unwrap();
    assert!(self_contained_private_view(&root, &libdir, host).is_ok());
    fs::write(&private, b"other runtime").unwrap();
    assert!(self_contained_private_view(&root, &libdir, host).is_err());
    fs::write(&private, b"selected runtime").unwrap();
    fs::remove_file(libdir.join("librustc_middle-aa.rmeta")).unwrap();
    assert!(self_contained_private_view(&root, &libdir, host).is_err());
    fs::write(libdir.join("librustc_middle-aa.rmeta"), b"metadata fixture").unwrap();
    let external = tempfile::tempdir().unwrap();
    assert!(self_contained_private_view(&root, external.path(), host).is_err());
    fs::write(root.join("lib/librustc_driver-bb.dylib"), b"another runtime").unwrap();
    assert!(self_contained_private_view(&root, &libdir, host).is_err());
}

#[test]
fn only_the_owning_nested_private_wrapper_is_supported() {
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("config.toml");
    let valid =
        format!("[build]\nrustc-wrapper = '{WRAPPER}'\n[env]\nRUST_MIN_STACK = '16777216'\n");
    fs::write(&path, &valid).unwrap();
    assert!(nested_config(&path).is_ok());
    for text in [
        valid.replace(WRAPPER, "other-wrapper"),
        valid.replace("[env]", "rustflags = ['--cfg', 'changed']\n[env]"),
        valid.clone() + "[target.aarch64-apple-darwin]\nrunner = 'other'\n",
        valid.clone() + "include = 'unbound.toml'\n[target]\n",
        "[build]\nrustc = '/other/compiler'\n".into(),
        valid.clone() + "RUSTC_WRAPPER = { value = 'other', force = true }\n",
        valid.replace(
            "RUST_MIN_STACK = '16777216'",
            "RUST_MIN_STACK = { value = '16777216', force = true }",
        ),
    ] {
        fs::write(&path, text).unwrap();
        assert!(nested_config(&path).is_err());
    }
}

#[test]
fn cargo_environment_aliases_cannot_bypass_the_wrapper_or_host_target() {
    for name in [
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC",
        "CARGO_BUILD_TARGET",
        "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER",
        "TRUST_PRIVATE_DRIVER_CRATES",
    ] {
        assert!(competing_environment(name), "{name}");
    }
    for name in ["CARGO_BUILD_JOBS", "CARGO_BUILD_BUILD_DIR", "CARGO_TARGET_DIR"] {
        assert!(!competing_environment(name), "explicitly set by the operation: {name}");
    }
    let root = tempfile::tempdir().unwrap();
    let config = root.path().join("config.toml");
    fs::write(&config, "[env]\nCARGO_BUILD_RUSTC_WRAPPER = { value = 'other', force = true }\n")
        .unwrap();
    assert!(ancestor_environment(&config).is_err());
}

#[test]
fn native_authority_aliases_follow_compatibility_precedence_and_bound_home() {
    let validate = |entries: &[(&str, &str)]| {
        validate_environment_values(
            &entries
                .iter()
                .map(|(name, value)| (OsString::from(*name), OsString::from(*value)))
                .collect(),
        )
    };
    for (name, value) in [
        ("TARGO_BUILD_TARGET", "foreign-target"),
        ("TARGO_BUILD_RUSTC_WRAPPER", "/other-wrapper"),
        ("TARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "/other-wrapper"),
        ("TARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER", "/other-runner"),
        ("TARGO_ENCODED_RUSTFLAGS", "--cfg=other"),
        ("TARGO_HOME", "/unbound-home"),
        ("TARGO_HOME", ""),
    ] {
        assert!(validate(&[(name, value)]).is_err(), "{name}");
    }
    let home_directory = tempfile::tempdir().unwrap();
    let home = home_directory.path().to_str().unwrap();
    assert!(validate(&[("TARGO_HOME", "/unused-native-home"), ("CARGO_HOME", home)]).is_ok());
    assert!(validate(&[("TARGO_HOME", home), ("CARGO_HOME", "relative")]).is_err());
    assert!(validate(&[("TARGO_HOME", home), ("CARGO_HOME", "")]).is_err());
    // The explicit compatibility spelling wins even when empty; a nonempty
    // unsafe compatibility authority is still rejected on its own entry.
    assert!(validate(&[("TARGO_BUILD_TARGET", "foreign"), ("CARGO_BUILD_TARGET", "")]).is_ok());
    assert!(
        validate(&[("TARGO_BUILD_TARGET", "foreign"), ("CARGO_BUILD_TARGET", "foreign")]).is_err()
    );
    for name in ["TARGO_BUILD_JOBS", "TARGO_TARGET_DIR", "TARGO_BUILD_BUILD_DIR"] {
        assert!(
            validate(&[(name, "unused-native-setting")]).is_ok(),
            "the operation explicitly binds its Cargo spelling: {name}"
        );
    }
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("config.toml");
    for name in ["TARGO_HOME", "TARGO_BUILD_TARGET", "TARGO_BUILD_RUSTC_WRAPPER"] {
        fs::write(&path, format!("[env]\n{name} = {{ value = 'other', force = true }}\n")).unwrap();
        assert!(ancestor_environment(&path).is_err(), "{name}");
    }
}

#[test]
fn complete_public_installation_bin_population_is_accepted() {
    // Trust: a complete ordinary installation must not be refused as helper
    // shadowing. Keep the expected public population explicit so missing tool
    // declarations cannot make the control pass by shrinking its fixture.
    for suffix in ["", ".exe"] {
        let root = tempfile::tempdir().unwrap();
        let bin = root.path();
        for name in [
            "trustc",
            "rustc",
            "trustdoc",
            "rustdoc",
            "targo",
            "cargo",
            "targo-trust",
            "trustd",
            "trustup",
            "ay",
            "ty",
            "clean",
            "tippy",
            "targo-tippy",
            "tippy-driver",
            "trustfmt",
            "targo-fmt",
            "trust-analyzer",
            "trust-miri",
            "targo-miri",
            "trust-gdb",
            "trust-gdbgui",
            "trust-lldb",
            "trust-wp",
            "trust-wp-driver",
            "trust-wp-rustc",
            "targo-trust-wp",
            "cargo-trust-wp",
            "lean",
            "lake",
        ] {
            fs::write(bin.join(format!("{name}{suffix}")), b"declared public tool fixture")
                .unwrap();
        }
        assert!(installation_bin_namespace(bin).is_ok());
        let helper = bin.join(format!("brew{suffix}"));
        fs::write(&helper, b"undeclared native helper fixture").unwrap();
        assert!(installation_bin_namespace(bin).unwrap_err().contains("brew"));
        fs::remove_file(helper).unwrap();
        assert!(installation_bin_namespace(bin).is_ok());
    }
}

#[test]
fn prepended_installation_bin_cannot_shadow_native_helpers() {
    let root = tempfile::tempdir().unwrap();
    let selected = root.path().join("selected/bin");
    let parent = root.path().join("parent/bin");
    fs::create_dir_all(&selected).unwrap();
    fs::create_dir_all(&parent).unwrap();
    fs::write(selected.join("trustc"), b"selected Trust compiler fixture").unwrap();
    assert!(installation_bin_namespace(&selected).is_ok());
    for helper in ["brew", "otool", "awk", "bash", "custom-native-linker"] {
        fs::write(parent.join(helper), b"inventoried parent helper fixture").unwrap();
        fs::write(selected.join(helper), b"different selected helper fixture").unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            for path in [parent.join(helper), selected.join(helper)] {
                fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
            }
        }
        let child_resolution = [&selected, &parent]
            .into_iter()
            .map(|directory| directory.join(helper))
            .find(|path| path.is_file())
            .unwrap();
        assert_ne!(
            child_resolution,
            parent.join(helper),
            "prepending really changes the resolution"
        );
        assert!(installation_bin_namespace(&selected).unwrap_err().contains(helper));
        fs::remove_file(selected.join(helper)).unwrap();
        assert!(installation_bin_namespace(&selected).is_ok());
    }
}

#[test]
fn workspace_command_preserves_the_nested_config_and_explicit_compiler() {
    let root = tempfile::tempdir().unwrap();
    let install = root.path().join("installed");
    let selected = Installation {
        targo: install.join("bin/targo"),
        trustc: install.join("bin/trustc"),
        trustdoc: install.join("bin/trustdoc"),
        root: install,
    };
    let workspace = root.path().join("source/first-party/trust-wp");
    let mut cmd = workspace_command(&selected, &workspace, 7);
    cmd.mark_as_executed();
    assert_eq!(cmd.get_current_dir(), Some(workspace.as_path()));
    let env = cmd.get_envs().collect::<std::collections::BTreeMap<_, _>>();
    assert_eq!(env[std::ffi::OsStr::new("RUSTC")], Some(selected.trustc.as_os_str()));
    assert_eq!(env[std::ffi::OsStr::new("RUSTDOC")], Some(selected.trustdoc.as_os_str()));
    assert_eq!(env[std::ffi::OsStr::new("RUSTC_WRAPPER")], None);
    assert_eq!(env[std::ffi::OsStr::new("RUSTC_WORKSPACE_WRAPPER")], None);
    assert_eq!(env[std::ffi::OsStr::new("RUST_TEST_THREADS")], Some(std::ffi::OsStr::new("4")));
    assert_eq!(
        env[std::ffi::OsStr::new("CARGO_TARGET_DIR")],
        Some(workspace.join("target").as_os_str())
    );
    assert_eq!(
        env[std::ffi::OsStr::new("CARGO_BUILD_BUILD_DIR")],
        env[std::ffi::OsStr::new("CARGO_TARGET_DIR")]
    );
}

/// Trust: the Cargo, compiler and rustdoc the workspace-metadata test runs. `x.py test
/// src/bootstrap` hands the test CARGO, RUSTC and RUSTDOC; a direct `targo test` of the lib
/// sets only CARGO. The bare names this used to fall back to resolve through PATH, and on
/// an aterm host PATH's `rustc` is atpkg's reroute stub, which exits 127, so the direct lane
/// failed in `targo metadata`'s `rustc -vV`. The compiler that built these tests (build.rs's
/// `BOOTSTRAP_TEST_BUILD_RUSTC`, as `direct_test_run_rustc` uses) is the toolchain the caller
/// chose; its rustdoc is its sibling. With neither, the test stops and names RUSTC.
fn wp_test_tools(
    cargo: Option<std::ffi::OsString>,
    rustc: Option<std::ffi::OsString>,
    rustdoc: Option<std::ffi::OsString>,
    build_rustc: Option<&str>,
) -> (PathBuf, PathBuf, PathBuf) {
    let cargo = PathBuf::from(cargo.expect("Cargo sets CARGO for the tests it runs"));
    let build_rustc = build_rustc.filter(|compiler| !compiler.is_empty()).map(PathBuf::from);
    let rustc = rustc.map(PathBuf::from).or_else(|| build_rustc.clone()).unwrap_or_else(|| {
        panic!("no compiler for `targo metadata`: set RUSTC (x.py test src/bootstrap sets it)")
    });
    let rustdoc = rustdoc.map(PathBuf::from).unwrap_or_else(|| {
        let name = match rustc.file_name().and_then(|name| name.to_str()) {
            Some("rustc") => "rustdoc",
            _ => "trustdoc",
        };
        rustc.with_file_name(name)
    });
    (cargo, rustc, rustdoc)
}

#[test]
fn wp_test_tools_never_resolve_a_bare_name_through_path() {
    let cargo = Some("/tc/bin/targo".into());
    // What x.py hands the test wins.
    assert_eq!(
        wp_test_tools(
            cargo.clone(),
            Some("/x/rustc".into()),
            Some("/x/rustdoc".into()),
            Some("/tc/bin/trustc")
        ),
        (PathBuf::from("/tc/bin/targo"), PathBuf::from("/x/rustc"), PathBuf::from("/x/rustdoc")),
    );
    // A direct run: the compiler that built the tests, and its sibling rustdoc.
    assert_eq!(
        wp_test_tools(cargo.clone(), None, None, Some("/tc/bin/trustc")),
        (
            PathBuf::from("/tc/bin/targo"),
            PathBuf::from("/tc/bin/trustc"),
            PathBuf::from("/tc/bin/trustdoc")
        ),
    );
    assert_eq!(
        wp_test_tools(cargo.clone(), Some("/s/rustc".into()), None, None).2,
        PathBuf::from("/s/rustdoc")
    );
    // Neither: stop, naming RUSTC, rather than run whatever PATH's `rustc` is.
    for build_rustc in [None, Some("")] {
        let cargo = cargo.clone();
        let panic = std::panic::catch_unwind(move || wp_test_tools(cargo, None, None, build_rustc))
            .expect_err("no compiler must stop the test");
        // A message with no arguments panics with a `&'static str` payload, one with
        // arguments with a `String`.
        let message = panic
            .downcast_ref::<&str>()
            .map(|message| message.to_string())
            .or_else(|| panic.downcast_ref::<String>().cloned())
            .unwrap_or_default();
        assert!(message.contains("set RUSTC"), "{message}");
    }
}

#[test]
fn workspace_metadata_executes_and_refuses_a_stale_lockfile() {
    let root = tempfile::tempdir().unwrap();
    let workspace = root.path().join("workspace");
    fs::create_dir(&workspace).unwrap();
    let manifest = workspace.join("Cargo.toml");
    let package = "[workspace]\n[package]\nname = 'wp-metadata-input'\nversion = '0.0.0'\nedition = '2021'\n[lib]\npath = 'lib.rs'\n[features]\nextra = []\n";
    fs::write(&manifest, package).unwrap();
    fs::write(workspace.join("lib.rs"), "").unwrap();
    // Trust: use the real native/compatibility executable supplied by the
    // Bootstrap harness, as the existing tool cache execution control does.
    let (targo, trustc, trustdoc) = wp_test_tools(
        env::var_os("CARGO"),
        env::var_os("RUSTC"),
        env::var_os("RUSTDOC"),
        option_env!("BOOTSTRAP_TEST_BUILD_RUSTC"),
    );
    let installation =
        Installation { root: root.path().join("installed"), targo, trustc, trustdoc };
    let execute = |mut cmd: BootstrapCommand| {
        cmd.mark_as_executed();
        let mut process = std::process::Command::new(&installation.targo);
        process.args(cmd.get_args()).current_dir(cmd.get_current_dir().unwrap());
        for (name, value) in cmd.get_envs() {
            match value {
                Some(value) => {
                    process.env(name, value);
                }
                None => {
                    process.env_remove(name);
                }
            }
        }
        process.output().unwrap()
    };
    let mut lock = workspace_command(&installation, &workspace, 1);
    lock.args(["generate-lockfile", "--offline"]);
    let output = execute(lock);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let locked = fs::read(workspace.join("Cargo.lock")).unwrap();

    let output = execute(workspace_metadata_command(&installation, &workspace, 1));
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let metadata: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(metadata["packages"][0]["name"], "wp-metadata-input");
    assert_eq!(metadata["resolve"]["nodes"][0]["features"], serde_json::json!(["extra"]));
    assert_eq!(fs::read(workspace.join("Cargo.lock")).unwrap(), locked);

    let dependency = workspace.join("added-input");
    fs::create_dir(&dependency).unwrap();
    fs::write(dependency.join("Cargo.toml"), "[package]\nname = 'added-input'\nversion = '0.0.0'\nedition = '2021'\n[lib]\npath = 'lib.rs'\n").unwrap();
    fs::write(dependency.join("lib.rs"), "").unwrap();
    fs::write(
        &manifest,
        format!("{package}[dependencies]\nadded-input = {{ path = 'added-input' }}\n"),
    )
    .unwrap();
    let output = execute(workspace_metadata_command(&installation, &workspace, 1));
    assert!(!output.status.success(), "a changed dependency must not update the bound lockfile");
    assert!(String::from_utf8_lossy(&output.stderr).contains("--locked"));
    assert_eq!(fs::read(workspace.join("Cargo.lock")).unwrap(), locked);
}

#[cfg(unix)]
#[test]
fn writable_installs_live_trees_and_escaping_links_refuse() {
    use std::os::unix::fs::{PermissionsExt, symlink};
    let temp = tempfile::tempdir().unwrap();
    let base = fs::canonicalize(temp.path()).unwrap();
    let root = base.join("installed");
    fs::create_dir_all(root.join("bin")).unwrap();
    for name in ["trustc", "trustdoc", "targo"] {
        fs::write(root.join("bin").join(name), b"tool fixture").unwrap();
    }
    assert!(readonly_installation(&root).is_err());
    for entry in walkdir::WalkDir::new(&root) {
        let path = entry.unwrap().into_path();
        let mode = if path.is_dir() { 0o555 } else { 0o444 };
        fs::set_permissions(path, fs::Permissions::from_mode(mode)).unwrap();
    }
    let source = base.join("source");
    let output = source.join("build");
    let accepted = Installation::open(&root, &source, &output);
    // Restore directory write permission even when an assertion below fails.
    fs::set_permissions(&root, fs::Permissions::from_mode(0o755)).unwrap();
    fs::set_permissions(root.join("bin"), fs::Permissions::from_mode(0o755)).unwrap();
    assert!(accepted.is_ok());
    fs::create_dir_all(&source).unwrap();
    symlink(&source, root.join("outside")).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o555)).unwrap();
    fs::set_permissions(root.join("bin"), fs::Permissions::from_mode(0o555)).unwrap();
    let escaped = readonly_installation(&root).unwrap_err();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o755)).unwrap();
    fs::set_permissions(root.join("bin"), fs::Permissions::from_mode(0o755)).unwrap();
    assert!(escaped.contains("escapes"));
    assert!(Installation::open(Path::new("relative"), &source, &output).is_err());
    assert!(Installation::open(&root, &base, &output).is_err());
    let live = base.join("build/stage2");
    fs::create_dir_all(&live).unwrap();
    assert!(Installation::open(&live, &source, &output).is_err());
}
