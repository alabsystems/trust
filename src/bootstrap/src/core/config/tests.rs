use std::collections::BTreeSet;
use std::fs::{File, remove_file};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::{env, fs};

use build_helper::ci::CiEnv;
use build_helper::git::PathFreshness;
use clap::CommandFactory;

use super::flags::Flags;
use super::toml::change_id::ChangeIdWrapper;
use super::toml::rust::{BUILTIN_CODEGEN_BACKENDS, parse_codegen_backends};
use super::{
    Config, DebuggerPath, LlvmCiMode, RUSTC_IF_UNCHANGED_ALLOWED_PATHS, default_initial_cargo_path,
    default_initial_rustdoc_path,
};
use crate::core::backend::CodegenBackendKind;
use crate::core::build_steps::clippy::{LintConfig, get_clippy_rules_in_order};
use crate::core::build_steps::llvm::{LLVM_INVALIDATION_PATHS, LlvmKind, get_llvm_build_status};
use crate::core::builder::Builder;

#[test]
fn library_test_selector_is_explicit_and_mutually_exclusive() {
    use clap::Parser;

    use crate::core::build_steps::test::TestTarget;

    for command in ["test", "miri"] {
        let parsed = Flags::try_parse_from(["x.py", command, "--lib"]).unwrap();
        assert_eq!(parsed.cmd.test_target(), TestTarget::Lib);
        assert!(!parsed.cmd.test_target().runs_doctests());
        let default = Flags::try_parse_from(["x.py", command]).unwrap();
        assert_eq!(default.cmd.test_target(), TestTarget::Default);
        for conflicting in ["--tests", "--all-targets", "--doc", "--no-doc"] {
            assert!(Flags::try_parse_from(["x.py", command, "--lib", conflicting]).is_err());
        }
    }
}

#[test]
fn compiler_profile_keeps_paired_lld_with_selected_external_llvm() {
    let context = crate::utils::tests::TestCtx::new();
    let host = crate::utils::helpers::get_host_target();
    let provider = context.dir().join("selected-provider/bin/llvm-config");
    let config = context
        .config("build")
        .stage(1)
        .path("src/llvm-project/lld")
        .with_default_toml_config(&format!(
            "profile = 'compiler'\n[target.'{host}']\nllvm-config = '{}'\n",
            provider.display(),
        ))
        .create_config();
    assert!(config.lld_enabled);
    assert_eq!(config.target_config.get(&host).unwrap().llvm_config.as_ref(), Some(&provider));
}
#[test]
fn llvm_zstd_metadata_directory_is_an_explicit_target_input() {
    let context = crate::utils::tests::TestCtx::new();
    let host = crate::utils::helpers::get_host_target();
    let directory = context.dir().join("native package with spaces/lib/pkgconfig");
    let config = context
        .config("check")
        .with_default_toml_config(&format!(
            "[target.'{host}']\nllvm-zstd-pkg-config-dir = '{}'\n",
            directory.display(),
        ))
        .create_config();
    assert_eq!(
        config.target_config.get(&host).unwrap().llvm_zstd_pkg_config_dir.as_ref(),
        Some(&directory)
    );
}

use crate::core::config::flags::Subcommand;
use crate::core::config::{
    BootstrapOverrideLld, ChangeId, CompilerBuiltins, Target, TargetSelection,
};
use crate::core::session::Session;
use crate::utils::tests::TestCtx;
use crate::utils::tests::git::git_test;

pub(crate) fn parse(config: &str) -> Config {
    TestCtx::new().config("check").with_default_toml_config(config).create_config()
}

// Trust: AY is also linked into the compiler and other batteries, where its
// own workspace release profile cannot protect it from a consumer's settings.
#[test]
fn verifier_arithmetic_is_checked_independently_of_debug_mode() {
    for (toml, std_checks) in [
        ("", false),
        ("[rust]\ndebug = false\n", false),
        ("[rust]\ndebug = true\n", true),
        ("[rust]\noverflow-checks = true\n", true),
        ("[rust]\noverflow-checks = true\noverflow-checks-std = false\n", false),
        ("[rust]\noverflow-checks-std = true\n", true),
    ] {
        let config = parse(toml);
        assert!(config.rust_overflow_checks, "{toml}");
        assert_eq!(config.rust_overflow_checks_std, std_checks, "{toml}");
    }
}

// Trust: a configuration override must not reintroduce silent solver overflow.
#[test]
#[should_panic(expected = "Trust requires rust.overflow-checks = true")]
fn verifier_arithmetic_cannot_disable_overflow_checks() {
    parse("[rust]\noverflow-checks = false\n");
}

#[test]
fn default_stage0_rustdoc_matches_the_seed_compiler_identity() {
    let temp = tempfile::TempDir::new().unwrap();
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let stock_rustc = temp.path().join("rustc");
    let stock_rustdoc = temp.path().join("rustdoc");
    let trustdoc = temp.path().join("trustdoc");
    File::create(&stock_rustc).unwrap();
    File::create(&stock_rustdoc).unwrap();

    File::create(&trustdoc).unwrap();
    assert_eq!(
        default_initial_rustdoc_path(&stock_rustc, target, false),
        stock_rustdoc,
        "a neighboring trustdoc must not override stock rustc's matching rustdoc"
    );

    remove_file(&stock_rustdoc).unwrap();
    let trustc = temp.path().join("trustc");
    File::create(&trustc).unwrap();
    assert_eq!(
        default_initial_rustdoc_path(&trustc, target, false),
        trustdoc,
        "a Trust stage0 must retain its branded rustdoc path"
    );
}

// Trust: Config unit tests normally override stage0 with their build compiler,
// which hid a migration regression in the real Session default branch. Execute
// that branch against private compiler fixtures with BOTH names present.
#[cfg(unix)]
#[test]
fn session_uses_the_declared_seed_compiler_and_matching_documentation_driver() {
    use std::os::unix::fs::PermissionsExt;

    for (configured_name, explicit_tools) in
        [(None, false), (Some("rustc"), false), (Some("trustc"), false), (Some("trustc"), true)]
    {
        let context = TestCtx::new();
        let mut config = context.config("setup").create_config();
        let host = config.host_target;
        let seed = config.out.join(host).join("stage0");
        let bin = seed.join("bin");
        std::fs::create_dir_all(&bin).unwrap();
        let log = context.dir().join("compiler-probes");
        let script = format!(
            "#!/bin/sh\nprintf '%s\\n' \"$0 $*\" >> '{log}'\n\
             case \"$*\" in\n\
             '--print sysroot --print target-libdir') printf '%s\\n' '{seed}' '{seed}/lib/rustlib/{host}/lib' ;;\n\
             '--version --verbose') printf '%s\\n' 'release: 1.99.0-dev' 'host: {host}' ;;\n\
             *) exit 79 ;;\nesac\n",
            seed = seed.display(),
            log = log.display(),
        );
        for name in ["rustc", "trustc"] {
            let path = bin.join(name);
            std::fs::write(&path, &script).unwrap();
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        config.external_rustc = configured_name.map(|name| bin.join(name));
        config.external_rustdoc = explicit_tools.then(|| bin.join("selected-doc"));
        config.external_cargo = explicit_tools.then(|| bin.join("selected-cargo"));
        let session = Session::new(config);
        let expected_compiler = bin.join(configured_name.unwrap_or("trustc"));
        assert_eq!(session.initial_rustc, expected_compiler);
        assert_eq!(
            session.initial_rustdoc,
            bin.join(if explicit_tools {
                "selected-doc"
            } else if configured_name == Some("rustc") {
                "rustdoc"
            } else {
                "trustdoc"
            })
        );
        assert_eq!(
            session.initial_cargo,
            bin.join(if explicit_tools { "selected-cargo" } else { "cargo" })
        );
        let probes = std::fs::read_to_string(log).unwrap();
        assert!(
            probes
                .lines()
                .all(|line| line.starts_with(&format!("{} ", expected_compiler.display()))),
            "a neighboring compiler must not be probed: {probes}"
        );
    }
}

#[test]
fn downloaded_stage0_rustdoc_uses_the_pinned_trust_seed_identity() {
    for (triple, compiler_name, rustdoc_name) in [
        ("aarch64-apple-darwin", "rustc", "trustdoc"),
        ("x86_64-unknown-linux-gnu", "rustc", "trustdoc"),
        ("x86_64-pc-windows-msvc", "rustc.exe", "trustdoc.exe"),
    ] {
        let target = TargetSelection::from_user(triple);
        let compiler = Path::new("/pinned/stage0/bin").join(compiler_name);
        assert_eq!(
            default_initial_rustdoc_path(&compiler, target, true),
            compiler.with_file_name(rustdoc_name),
            "the downloaded Trust seed owns its branded rustdoc on {triple}",
        );
    }
}

#[test]
fn default_stage0_package_driver_uses_the_cargo_compatibility_identity() {
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let sysroot = Path::new("/trust/stage0");

    assert_eq!(default_initial_cargo_path(sysroot, target), sysroot.join("bin/cargo"));
}

#[test]
fn vendored_targo_uses_the_root_trust_commit_identity() {
    let config = TestCtx::new()
        .config("check")
        .with_default_toml_config("[rust]\nchannel = \"trust\"\n")
        .create_config();
    let rust = config.rust_info.info().expect("root checkout commit info");
    let targo = config.cargo_info.info().expect("vendored Targo commit info");

    assert_eq!(targo.sha, rust.sha);
    assert_eq!(targo.short_sha, rust.short_sha);
    assert_eq!(targo.commit_date, rust.commit_date);
}

fn modified(upstream: impl Into<String>, changes: &[&str]) -> PathFreshness {
    PathFreshness::HasLocalModifications {
        upstream: upstream.into(),
        modifications: changes.iter().copied().map(PathBuf::from).collect(),
    }
}

#[test]
fn download_ci_llvm() {
    let config = TestCtx::new().config("check").create_config();
    assert_eq!(config.llvm_ci_mode, LlvmCiMode::BuildLocally);

    // this doesn't make sense, as we are overriding it later.
    let if_unchanged_config = TestCtx::new()
        .config("check")
        .with_default_toml_config("llvm.download-ci-llvm = \"if-unchanged\"")
        .create_config();
    if if_unchanged_config.is_running_on_ci() {
        let build = Session::new(config.clone());
        let builder = Builder::new(&build);

        let llvm = get_llvm_build_status(&builder, builder.config.host_target);
        let llvm = llvm.llvm_output();
        if llvm.kind() == LlvmKind::DownloadedFromCi {
            let has_changes =
                if_unchanged_config.has_changes_from_upstream(LLVM_INVALIDATION_PATHS);

            assert!(
                !has_changes,
                "CI LLVM can't be enabled with 'if-unchanged' while there are changes in LLVM submodule."
            );
        }
    }
}

#[test]
fn clap_verify() {
    Flags::command().debug_assert();
}

// Trust: native reuse binds actual parser inputs, including includes/profiles.
#[test]
fn native_config_retains_exact_loaded_include_and_profile_bytes() {
    let context = TestCtx::new().retain();
    let included = context.dir().join("extra.toml");
    let nested = context.dir().join("nested.toml");
    let leaf = context.dir().join("leaf.toml");
    fs::write(&included, "include = ['nested.toml']\n[rust]\ndeny-warnings = false\n").unwrap();
    fs::write(&nested, "include = ['leaf.toml']\n").unwrap();
    fs::write(&leaf, "[rust]\ndeny-warnings = true\n").unwrap();
    let config = context
        .config("test")
        .arg("--trust-repo-check")
        .stage(1)
        .with_default_toml_config("include = ['extra.toml']\nprofile = 'compiler'\n")
        .create_config();
    assert!(config.native_repo_config_inputs.len() >= 5);
    for (path, digest) in &config.native_repo_config_inputs {
        assert_eq!(*digest, crate::utils::trust_repo_cache::file_digest(path).unwrap());
    }
    assert!(config.native_repo_config_inputs.iter().any(|(path, _)| path == &included));
    for expected in [&nested, &leaf] {
        let expected = expected.canonicalize().unwrap();
        assert!(config.native_repo_config_inputs.iter().any(|(path, _)| path == &expected));
    }
    assert!(!config.deny_warnings, "the outer include keeps precedence over nested defaults");
    assert!(
        config
            .native_repo_config_inputs
            .iter()
            .any(|(path, _)| path.ends_with("bootstrap.compiler.toml"))
    );
    context.close().expect("remove passed native config fixture");
}

#[test]
fn seed_configuration_projects_the_actual_include_profile_and_empty_override() {
    let context = TestCtx::new().retain();
    let root = context.dir();
    let defaults = root.join("src/bootstrap/defaults");
    fs::create_dir_all(&defaults).unwrap();
    fs::create_dir(root.join("nested")).unwrap();
    let config = root.join("bootstrap.toml");
    let files = [
        (
            config.clone(),
            "include = ['outer.toml', 'later.toml']\nprofile = 'user'\n[build]\nrustc = ''\n",
        ),
        (
            root.join("outer.toml"),
            "include = ['nested/leaf.toml']\n[build]\ncargo = 'outer-cargo'\n",
        ),
        (root.join("later.toml"), "[build]\ncargo = 'later-cargo'\n"),
        (root.join("nested/leaf.toml"), "[build]\ncargo = 'leaf-cargo'\n"),
        (
            defaults.join("bootstrap.dist.toml"),
            "include = ['profile-extra.toml']\n[build]\nrustc = 'profile-rustc'\ncargo = 'profile-cargo'\n",
        ),
        (defaults.join("profile-extra.toml"), "[build]\nrustc = 'profile-extra-rustc'\n"),
    ];
    for (path, text) in &files {
        fs::write(path, text).unwrap();
    }
    let selected = crate::engine::seed_configuration(root, Some(config.clone()), false).unwrap();
    // D12 must reject Some even when the configured path is empty.
    assert_eq!(selected.rustc_override(), Some(Path::new("")));
    assert_eq!(selected.cargo_override(), Some(Path::new("later-cargo")));
    assert_eq!(selected.inputs().len(), files.len());
    for (index, (expected, contents)) in files.iter().enumerate() {
        // The ordinary parser preserves top-level selected spellings and
        // canonicalizes nested include paths before reading them. /var can
        // alias /private/var on macOS; assert those exact reader semantics.
        let expected = if matches!(index, 3 | 5) {
            expected.canonicalize().unwrap()
        } else {
            expected.clone()
        };
        let digest = crate::utils::trust_repo_cache::bytes_digest(contents.as_bytes());
        assert!(
            selected.inputs().iter().any(|(path, value)| path == &expected && value == &digest)
        );
    }

    fs::write(&config, "profile = 'user'\n").unwrap();
    let profile = crate::engine::seed_configuration(root, Some(config.clone()), false).unwrap();
    assert_eq!(profile.rustc_override(), Some(Path::new("profile-rustc")));
    assert_eq!(profile.cargo_override(), Some(Path::new("profile-cargo")));

    fs::write(&config, "").unwrap();
    let tarball = crate::engine::seed_configuration(root, Some(config.clone()), true).unwrap();
    assert_eq!(tarball.rustc_override(), profile.rustc_override());
    assert_eq!(tarball.cargo_override(), profile.cargo_override());
    let checkout = crate::engine::seed_configuration(root, Some(config), false).unwrap();
    assert_eq!(checkout.rustc_override(), None);
    assert_eq!(checkout.cargo_override(), None);
    assert_eq!(checkout.inputs().len(), 1);
    context.close().unwrap();
}

#[test]
fn seed_configuration_returns_invalid_data_without_exiting_for_bad_toml_or_cycles() {
    let context = TestCtx::new().retain();
    let root = context.dir();
    let config = root.join("bootstrap.toml");
    for invalid in [
        "[build]\nrustc = false\n",
        "[build]\ncargo = false\n",
        "[build]\nunknown-seed-selector = 'tool'\n",
        "[build\n",
    ] {
        fs::write(&config, invalid).unwrap();
        let error =
            crate::engine::seed_configuration(root, Some(config.clone()), false).unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::InvalidData, "{error}");
        assert!(error.to_string().contains("bootstrap.toml"));
    }
    fs::write(&config, "include = ['cycle.toml']\n").unwrap();
    fs::write(root.join("cycle.toml"), "include = ['bootstrap.toml']\n").unwrap();
    let error = crate::engine::seed_configuration(root, Some(config), false).unwrap_err();
    assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);
    assert!(error.to_string().contains("Cyclic inclusion detected"));
    context.close().unwrap();
}

#[test]
fn seed_configuration_preserves_missing_input_errors_without_falling_back() {
    let context = TestCtx::new().retain();
    let root = context.dir();
    let config = root.join("bootstrap.toml");
    for contents in [None, Some("include = ['missing.toml']\n"), Some("profile = 'missing'\n")] {
        if let Some(contents) = contents {
            fs::write(&config, contents).unwrap();
        }
        let error =
            crate::engine::seed_configuration(root, Some(config.clone()), false).unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::NotFound, "{error}");
    }
    context.close().unwrap();
}

#[test]
fn native_mode_refuses_test_controls_that_can_skip_or_change_the_selection() {
    for flag in [
        "--bless",
        "--only-modified",
        "--no-fail-fast",
        "--no-capture",
        "--rerun",
        "--doc",
        "--trust-verified",
    ] {
        assert!(
            Flags::command()
                .try_get_matches_from(["bootstrap", "test", "--trust-repo-check", flag])
                .is_err(),
            "{flag}"
        );
    }
}

#[test]
fn setup_link_honors_configured_build_stage() {
    let config = TestCtx::new()
        .config("setup")
        .path("link")
        .with_default_toml_config(
            r#"
            [build]
            rustc = "rustc"
            build-stage = 2
            "#,
        )
        .create_config();

    assert_eq!(config.stage, 2);
}

#[test]
fn setup_link_cli_stage_overrides_configured_build_stage() {
    let config = TestCtx::new()
        .config("setup")
        .path("link")
        .stage(1)
        .with_default_toml_config(
            r#"
            [build]
            rustc = "rustc"
            build-stage = 2
            "#,
        )
        .create_config();

    assert_eq!(config.stage, 1);
}

#[test]
fn override_toml() {
    let config_toml: &str = r#"
    change-id = 0

    [rust]
    lto = "off"
    deny-warnings = true
    download-rustc = false

    [build]
    gdb = "foo"
    tools = []

    [llvm]
    download-ci-llvm = false
    build-config = {}

    [target.aarch64-unknown-linux-gnu]
    sanitizers = true
    rpath = true
    runner = "aarch64-runner"

    [target.x86_64-unknown-linux-gnu]
    sanitizers = true
    rpath = true
    runner = "x86_64-runner"
    "#;

    let args = [
        "--set=change-id=1",
        "--set=rust.lto=fat",
        "--set=rust.deny-warnings=false",
        "--set=build.optimized-compiler-builtins=true",
        "--set=build.gdb=\"bar\"",
        "--set=build.tools=[\"cargo\"]",
        "--set=llvm.build-config={\"foo\" = \"bar\"}",
        "--set=target.x86_64-unknown-linux-gnu.runner=bar",
        "--set=target.x86_64-unknown-linux-gnu.rpath=false",
        "--set=target.aarch64-unknown-linux-gnu.sanitizers=false",
        "--set=target.aarch64-apple-darwin.runner=apple",
        "--set=target.aarch64-apple-darwin.optimized-compiler-builtins=false",
    ];

    let config = TestCtx::new()
        .config("check")
        .with_default_toml_config(config_toml)
        .args(&args)
        .create_config();

    assert_eq!(config.change_id, Some(ChangeId::Id(1)), "setting top-level value");
    assert_eq!(
        config.rust_lto,
        crate::core::config::RustcLto::Fat,
        "setting string value without quotes"
    );
    assert_eq!(
        config.gdb,
        Some(DebuggerPath::Path("bar".into())),
        "setting string value with quotes"
    );
    assert!(!config.deny_warnings, "setting boolean value");
    assert_eq!(
        config.optimized_compiler_builtins,
        CompilerBuiltins::BuildLLVMFuncs,
        "setting boolean value"
    );
    assert_eq!(
        config.tools,
        Some(["cargo".to_string()].into_iter().collect()),
        "setting list value"
    );
    assert_eq!(
        config.llvm_build_config,
        [("foo".to_string(), "bar".to_string())].into_iter().collect(),
        "setting dictionary value"
    );

    let x86_64 = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let x86_64_values = Target {
        sanitizers: Some(true),
        rpath: Some(false),
        runner: Some("bar".into()),
        ..Default::default()
    };
    let aarch64 = TargetSelection::from_user("aarch64-unknown-linux-gnu");
    let aarch64_values = Target {
        sanitizers: Some(false),
        rpath: Some(true),
        runner: Some("aarch64-runner".into()),
        ..Default::default()
    };
    let darwin = TargetSelection::from_user("aarch64-apple-darwin");
    let darwin_values = Target {
        runner: Some("apple".into()),
        optimized_compiler_builtins: Some(CompilerBuiltins::BuildRustOnly),
        ..Default::default()
    };
    assert_eq!(
        config.target_config,
        [(x86_64, x86_64_values), (aarch64, aarch64_values), (darwin, darwin_values)]
            .into_iter()
            .collect(),
        "setting dictionary value"
    );
    std::assert_matches!(config.llvm_ci_mode, LlvmCiMode::BuildLocally);
    assert!(!config.download_rustc());
}

#[test]
#[should_panic]
fn override_toml_duplicate() {
    TestCtx::new()
        .config("check")
        .with_default_toml_config("change-id = 0")
        .arg("--set")
        .arg("change-id=1")
        .arg("--set")
        .arg("change-id=2")
        .create_config();
}

#[test]
fn profile_user_dist() {
    TestCtx::new()
        .config("check")
        .with_default_toml_config(
            r#"
        profile = "user"
    "#,
        )
        .create_config();
}

#[test]
fn rust_optimize() {
    assert!(parse("").rust_optimize.is_release());
    assert!(!parse("rust.optimize = false").rust_optimize.is_release());
    assert!(parse("rust.optimize = true").rust_optimize.is_release());
    assert!(!parse("rust.optimize = 0").rust_optimize.is_release());
    assert!(parse("rust.optimize = 1").rust_optimize.is_release());
    assert!(parse("rust.optimize = \"s\"").rust_optimize.is_release());
    assert_eq!(parse("rust.optimize = 1").rust_optimize.get_opt_level(), Some("1".to_string()));
    assert_eq!(parse("rust.optimize = \"s\"").rust_optimize.get_opt_level(), Some("s".to_string()));
}

#[test]
fn parses_the_trust_backends_by_name() {
    // Trust: both trust-cg products are first-class kinds, never `Custom`:
    // the builtin adapter and the trust-ir → trust-cg self-host plugin.
    let parsed = parse_codegen_backends(
        vec!["llvm", "trust-cg", "trust-ir-cg"].into_iter().map(str::to_owned).collect(),
        "rust",
    );
    assert_eq!(
        parsed,
        vec![CodegenBackendKind::Llvm, CodegenBackendKind::TrustCg, CodegenBackendKind::TrustIrCg]
    );
    assert!(parsed[2].is_trust_ir_cg());
    assert!(!parsed[2].is_trust_cg());
    assert_eq!(parsed[2].name(), "trust-ir-cg");
    assert!(BUILTIN_CODEGEN_BACKENDS.contains(&"trust-ir-cg"));
}

#[test]
#[should_panic(expected = "Duplicate value 'llvm' for 'rust.codegen-backends'")]
fn rejects_duplicate_codegen_backends() {
    parse_codegen_backends(
        vec!["llvm", "llvm", "cranelift"].into_iter().map(str::to_owned).collect(),
        "rust",
    );
}

#[test]
#[should_panic]
fn invalid_rust_optimize() {
    TestCtx::new()
        .config("check")
        .with_default_toml_config("rust.optimize = \"a\"")
        .create_config();
}

#[test]
fn verify_file_integrity() {
    let config = TestCtx::new().config("check").no_dry_run().create_config();

    let tempfile = config.tempdir().join(".tmp-test-file");
    File::create(&tempfile).unwrap().write_all(b"dummy value").unwrap();
    assert!(tempfile.exists());

    assert!(
        config
            .verify(&tempfile, "7e255dd9542648a8779268a0f268b891a198e9828e860ed23f826440e786eae5")
    );
}

#[test]
fn rust_lld() {
    assert!(matches!(parse("").bootstrap_override_lld, BootstrapOverrideLld::None));
    assert!(matches!(
        parse("rust.bootstrap-override-lld = \"self-contained\"").bootstrap_override_lld,
        BootstrapOverrideLld::SelfContained
    ));
    assert!(matches!(
        parse("rust.bootstrap-override-lld = \"external\"").bootstrap_override_lld,
        BootstrapOverrideLld::External
    ));
    assert!(matches!(
        parse("rust.bootstrap-override-lld = true").bootstrap_override_lld,
        BootstrapOverrideLld::External
    ));
    assert!(matches!(
        parse("rust.bootstrap-override-lld = false").bootstrap_override_lld,
        BootstrapOverrideLld::None
    ));
}

#[test]
#[should_panic]
fn parse_config_with_unknown_field() {
    parse("unknown-key = 1");
}

#[test]
fn parse_change_id_with_unknown_field() {
    let config = r#"
        change-id = 3461
        unknown-key = 1
    "#;

    let change_id_wrapper: ChangeIdWrapper = toml::from_str(config).unwrap();
    assert_eq!(change_id_wrapper.inner, Some(ChangeId::Id(3461)));
}

#[test]
fn order_of_clippy_rules() {
    let args = [
        "clippy",
        "--fix",
        "--allow-dirty",
        "--allow-staged",
        "-Aclippy:all",
        "-Wclippy::style",
        "-Aclippy::foo1",
        "-Aclippy::foo2",
    ];
    let config = TestCtx::new().config(&args[0]).args(&args[1..]).create_config();

    let actual = match config.cmd.clone() {
        Subcommand::Clippy { allow, deny, warn, forbid, .. } => {
            let cfg = LintConfig { allow, deny, warn, forbid };
            let args_vec: Vec<String> = args.iter().map(|s| s.to_string()).collect();
            get_clippy_rules_in_order(&args_vec, &cfg)
        }
        _ => panic!("invalid subcommand"),
    };

    let expected = vec![
        "-Aclippy:all".to_string(),
        "-Wclippy::style".to_string(),
        "-Aclippy::foo1".to_string(),
        "-Aclippy::foo2".to_string(),
    ];

    assert_eq!(expected, actual);
}

#[test]
fn clippy_rule_separate_prefix() {
    let args = ["clippy", "-A clippy:all", "-W clippy::style"];
    let config = TestCtx::new().config(&args[0]).args(&args[1..]).create_config();

    let actual = match config.cmd.clone() {
        Subcommand::Clippy { allow, deny, warn, forbid, .. } => {
            let cfg = LintConfig { allow, deny, warn, forbid };
            let args_vec: Vec<String> = args.iter().map(|s| s.to_string()).collect();
            get_clippy_rules_in_order(&args_vec, &cfg)
        }
        _ => panic!("invalid subcommand"),
    };

    let expected = vec!["-A clippy:all".to_string(), "-W clippy::style".to_string()];
    assert_eq!(expected, actual);
}

#[test]
fn verbose_tests_default_value() {
    let config = TestCtx::new().config("build").args(&["compiler".into()]).create_config();
    assert_eq!(config.verbose_tests, false);

    let config =
        TestCtx::new().config("build").args(&["compiler".into(), "-v".into()]).create_config();
    assert_eq!(config.verbose_tests, true);
}

#[test]
fn parse_rust_std_features() {
    let config = TestCtx::new()
        .config("check")
        .with_default_toml_config("rust.std-features = [\"panic-unwind\", \"backtrace\"]")
        .create_config();
    let expected_features: BTreeSet<String> =
        ["panic-unwind", "backtrace"].into_iter().map(|s| s.to_string()).collect();
    assert_eq!(config.rust_std_features, expected_features);
}

#[test]
fn parse_rust_std_features_empty() {
    let config = TestCtx::new()
        .config("check")
        .with_default_toml_config("rust.std-features = []")
        .create_config();
    let expected_features: BTreeSet<String> = BTreeSet::new();
    assert_eq!(config.rust_std_features, expected_features);
}

#[test]
#[should_panic]
fn parse_rust_std_features_invalid() {
    TestCtx::new()
        .config("check")
        .with_default_toml_config("rust.std-features = \"backtrace\"")
        .create_config();
}

#[test]
fn parse_jobs() {
    assert_eq!(
        TestCtx::new()
            .config("check")
            .with_default_toml_config("build.jobs = 1")
            .create_config()
            .jobs,
        Some(1)
    );
}

#[test]
fn jobs_precedence() {
    // `--jobs` should take precedence over using `--set build.jobs`.

    let config = TestCtx::new()
        .config("check")
        .args(&["--jobs=67890", "--set=build.jobs=12345"])
        .create_config();
    assert_eq!(config.jobs, Some(67890));

    // `--set build.jobs` should take precedence over `bootstrap.toml`.
    let config = TestCtx::new()
        .config("check")
        .args(&["--set=build.jobs=12345"])
        .with_default_toml_config(
            r#"
        [build]
        jobs = 67890
    "#,
        )
        .create_config();

    assert_eq!(config.jobs, Some(12345));

    // `--jobs` > `--set build.jobs` > `bootstrap.toml`
    let config = TestCtx::new()
        .config("check")
        .args(&["--jobs=123", "--set=build.jobs=456"])
        .with_default_toml_config(
            r#"
        [build]
        jobs = 789
    "#,
        )
        .create_config();
    assert_eq!(config.jobs, Some(123));
}

// Trust: exercise the real flag/TOML parser with isolated admission variables.
#[test]
fn build_slot_caps_resolved_jobs_without_expanding_smaller_requests() {
    let host_jobs = super::threads_from_config(0);
    for (args, toml, expected) in [
        (vec![], "", host_jobs.min(7)),
        (vec!["--jobs=32"], "", 7),
        (vec!["-j32"], "", 7),
        (vec![], "build.jobs = 32", 7),
        (vec!["--set=build.jobs=32"], "build.jobs = 2", 7),
        (vec!["--jobs=2"], "build.jobs = 32", 2),
        (vec![], "build.jobs = 2", 2),
        (vec!["--jobs=0"], "build.jobs = 32", host_jobs.min(7)),
        (vec![], "build.jobs = 0", host_jobs.min(7)),
    ] {
        let config = TestCtx::new()
            .config("check")
            .args(&args)
            .with_default_toml_config(toml)
            .env("BUILD_SLOT_HELD", "1")
            .env("CARGO_BUILD_JOBS", "7")
            .create_config();
        assert_eq!(config.jobs, Some(expected), "{args:?}, {toml}");
    }
}

#[test]
fn build_slot_variables_do_not_change_jobs_outside_admission() {
    for marker in [None, Some("0"), Some("true")] {
        let ctx = TestCtx::new();
        let mut config = ctx.config("check").arg("--jobs=32").env("CARGO_BUILD_JOBS", "invalid");
        if let Some(marker) = marker {
            config = config.env("BUILD_SLOT_HELD", marker);
        }
        assert_eq!(config.create_config().jobs, Some(32));
    }
}

#[test]
fn checked_original_fixed_budget_caps_explicit_and_configured_bootstrap_jobs() {
    for (args, toml, ceiling, expected) in [
        (vec!["--jobs=32"], "", 1, 1),
        (vec![], "build.jobs=32", 1, 1),
        (vec!["--set=build.jobs=32"], "", 1, 1),
        (vec!["--jobs=2"], "build.jobs=32", 7, 2),
        (vec![], "build.jobs=2", 7, 2),
    ] {
        let actual = TestCtx::new()
            .config("check")
            .args(&args)
            .with_default_toml_config(toml)
            .create_config_with_fixed_budget(Some(ceiling));
        assert_eq!(actual.jobs, Some(expected));
    }
}

#[test]
fn build_slot_requires_a_valid_positive_share_even_with_explicit_jobs() {
    for share in [
        None,
        Some(""),
        Some("0"),
        Some("-1"),
        Some("+7"),
        Some("7.0"),
        Some(" 7"),
        Some("７"),
        Some("4294967296"),
    ] {
        let result = std::panic::catch_unwind(|| {
            let ctx = TestCtx::new();
            let mut config = ctx.config("check").arg("--jobs=1").env("BUILD_SLOT_HELD", "1");
            if let Some(share) = share {
                config = config.env("CARGO_BUILD_JOBS", share);
            }
            config.create_config()
        });
        assert!(result.is_err(), "invalid advertised share accepted: {share:?}");
    }
}

#[cfg(unix)]
#[test]
#[should_panic(expected = "requires a positive u32 CARGO_BUILD_JOBS share")]
fn build_slot_rejects_non_utf8_share() {
    use std::os::unix::ffi::OsStringExt;
    TestCtx::new()
        .config("check")
        .env("BUILD_SLOT_HELD", "1")
        .env("CARGO_BUILD_JOBS", std::ffi::OsString::from_vec(vec![0xff]))
        .create_config();
}

#[test]
fn check_rustc_if_unchanged_paths() {
    let config = TestCtx::new().config("check").create_config();
    let normalised_allowed_paths: Vec<_> = RUSTC_IF_UNCHANGED_ALLOWED_PATHS
        .iter()
        .map(|t| {
            t.strip_prefix(":!").expect(&format!("{t} doesn't have ':!' prefix, but it should."))
        })
        .collect();

    for p in normalised_allowed_paths {
        assert!(config.src.join(p).exists(), "{p} doesn't exist.");
    }
}

#[test]
fn test_explicit_stage() {
    let config = TestCtx::new()
        .config("check")
        .with_default_toml_config(
            r#"
            [build]
            test-stage = 1
        "#,
        )
        .create_config();

    assert!(!config.explicit_stage_from_cli);
    assert!(config.explicit_stage_from_config);
    assert!(config.is_explicit_stage());

    let config = TestCtx::new().config("check").stage(2).create_config();

    assert!(config.explicit_stage_from_cli);
    assert!(!config.explicit_stage_from_config);
    assert!(config.is_explicit_stage());

    let config = TestCtx::new()
        .config("check")
        .stage(2)
        .with_default_toml_config(
            r#"
            [build]
            test-stage = 1
        "#,
        )
        .create_config();

    assert!(config.explicit_stage_from_cli);
    assert!(config.explicit_stage_from_config);
    assert!(config.is_explicit_stage());

    let config = TestCtx::new().config("check").create_config();

    assert!(!config.explicit_stage_from_cli);
    assert!(!config.explicit_stage_from_config);
    assert!(!config.is_explicit_stage());
}

#[test]
fn test_exclude() {
    let exclude_path = "compiler";
    let config = TestCtx::new()
        .config("check")
        .with_default_toml_config(&format!("build.exclude=[\"{}\"]", exclude_path))
        .create_config();

    let first_excluded = config
        .skip
        .first()
        .expect("Expected at least one excluded path")
        .to_str()
        .expect("Failed to convert excluded path to string");

    assert_eq!(first_excluded, exclude_path);
}

#[test]
fn test_ci_flag() {
    let config = TestCtx::new().config("check").arg("--ci").arg("false").create_config();
    assert!(!config.is_running_on_ci());

    let config = TestCtx::new().config("check").arg("--ci").arg("true").create_config();
    assert!(config.is_running_on_ci());

    // If --ci flag is not added, is_running_on_ci() relies on if it is run on actual CI or not.
    let config = TestCtx::new().config("check").create_config();
    assert_eq!(config.is_running_on_ci(), CiEnv::is_ci());
}

#[test]
fn test_precedence_of_includes() {
    let test_ctx = TestCtx::new();
    let testdir = test_ctx.dir();

    let extension = testdir.join("extension.toml");
    let extension_content = br#"
        change-id=543
        include = ["./extension2.toml"]
    "#;
    File::create(extension).unwrap().write_all(extension_content).unwrap();

    let extension = testdir.join("extension2.toml");
    let extension_content = br#"
        change-id=742

        [llvm]
        link-jobs = 10

        [build]
        description = "Some creative description"
    "#;
    File::create(extension).unwrap().write_all(extension_content).unwrap();

    let config = test_ctx
        .config("check")
        .with_default_toml_config(
            r#"
        include = ["./extension.toml"]

        [llvm]
        link-jobs = 2
    "#,
        )
        .create_config();

    assert_eq!(config.change_id.unwrap(), ChangeId::Id(543));
    assert_eq!(config.llvm_link_jobs.unwrap(), 2);
    assert_eq!(config.description.unwrap(), "Some creative description");
}

#[test]
#[should_panic(expected = "Cyclic inclusion detected")]
fn test_cyclic_include_direct() {
    let test_ctx = TestCtx::new();
    let testdir = test_ctx.dir();
    let extension = testdir.join("extension.toml");
    let extension_content = br#"
        include = ["./bootstrap.toml"]
    "#;
    File::create(extension).unwrap().write_all(extension_content).unwrap();

    test_ctx
        .config("check")
        .with_default_toml_config(
            r#"
        include = ["./extension.toml"]
    "#,
        )
        .create_config();
}

#[test]
#[should_panic(expected = "Cyclic inclusion detected")]
fn test_cyclic_include_indirect() {
    let test_ctx = TestCtx::new();
    let testdir = test_ctx.dir();

    let extension = testdir.join("extension.toml");
    let extension_content = br#"
        include = ["./extension2.toml"]
    "#;
    File::create(extension).unwrap().write_all(extension_content).unwrap();

    let extension = testdir.join("extension2.toml");
    let extension_content = br#"
        include = ["./extension3.toml"]
    "#;
    File::create(extension).unwrap().write_all(extension_content).unwrap();

    let extension = testdir.join("extension3.toml");
    let extension_content = br#"
        include = ["./extension.toml"]
    "#;
    File::create(extension).unwrap().write_all(extension_content).unwrap();

    test_ctx
        .config("check")
        .with_default_toml_config(
            r#"
        include = ["./extension.toml"]
    "#,
        )
        .create_config();
}

#[test]
fn test_include_absolute_paths() {
    let test_ctx = TestCtx::new();
    let testdir = test_ctx.dir();

    let extension = testdir.join("extension.toml");
    File::create(&extension).unwrap().write_all(&[]).unwrap();

    let extension_absolute_path =
        extension.canonicalize().unwrap().to_str().unwrap().replace('\\', r"\\");
    let root_config_content = format!(r#"include = ["{}"]"#, extension_absolute_path);
    test_ctx.config("check").with_default_toml_config(&root_config_content).create_config();
}

#[test]
fn test_include_relative_paths() {
    let test_ctx = TestCtx::new();
    let testdir = test_ctx.dir();

    let _ = fs::create_dir_all(&testdir.join("subdir/another_subdir"));

    let extension = testdir.join("subdir/extension.toml");
    let extension_content = br#"
        include = ["../extension2.toml"]
    "#;
    File::create(extension).unwrap().write_all(extension_content).unwrap();

    let extension = testdir.join("extension2.toml");
    let extension_content = br#"
        include = ["./subdir/another_subdir/extension3.toml"]
    "#;
    File::create(extension).unwrap().write_all(extension_content).unwrap();

    let extension = testdir.join("subdir/another_subdir/extension3.toml");
    let extension_content = br#"
        include = ["../../extension4.toml"]
    "#;
    File::create(extension).unwrap().write_all(extension_content).unwrap();

    let extension = testdir.join("extension4.toml");
    File::create(extension).unwrap().write_all(&[]).unwrap();

    test_ctx
        .config("check")
        .with_default_toml_config(
            r#"
        include = ["./subdir/extension.toml"]
    "#,
        )
        .create_config();
}

#[test]
fn test_include_precedence_over_profile() {
    let test_ctx = TestCtx::new();
    let testdir = test_ctx.dir();

    let extension = testdir.join("extension.toml");
    let extension_content = br#"
        [rust]
        channel = "dev"
    "#;
    File::create(extension).unwrap().write_all(extension_content).unwrap();

    let config = test_ctx
        .config("check")
        .with_default_toml_config(
            r#"
        profile = "dist"
        include = ["./extension.toml"]
    "#,
        )
        .create_config();

    // "dist" profile would normally set the channel to "auto-detect", but includes should
    // override profile settings, so we expect this to be "dev" here.
    assert_eq!(config.channel, "dev");
}

#[test]
fn test_pr_ci_unchanged_anywhere() {
    git_test(|ctx| {
        let sha = ctx.create_upstream_merge(&["a"]);
        ctx.create_nonupstream_merge(&["b"]);
        let src = ctx.check_modifications(&["c"], CiEnv::GitHubActions);
        assert_eq!(src, PathFreshness::LastModifiedUpstream { upstream: sha });
    });
}

#[test]
fn test_pr_ci_changed_in_pr() {
    git_test(|ctx| {
        let sha = ctx.create_upstream_merge(&["a"]);
        ctx.create_nonupstream_merge(&["b"]);
        let src = ctx.check_modifications(&["b"], CiEnv::GitHubActions);
        assert_eq!(src, modified(sha, &["b"]));
    });
}

#[test]
fn test_auto_ci_unchanged_anywhere_select_parent() {
    git_test(|ctx| {
        let sha = ctx.create_upstream_merge(&["a"]);
        ctx.create_upstream_merge(&["b"]);
        let src = ctx.check_modifications(&["c"], CiEnv::GitHubActions);
        assert_eq!(src, PathFreshness::LastModifiedUpstream { upstream: sha });
    });
}

#[test]
fn test_auto_ci_changed_in_pr() {
    git_test(|ctx| {
        let sha = ctx.create_upstream_merge(&["a"]);
        ctx.create_upstream_merge(&["b", "c"]);
        let src = ctx.check_modifications(&["c", "d"], CiEnv::GitHubActions);
        assert_eq!(src, modified(sha, &["c"]));
    });
}

#[test]
fn test_local_uncommitted_modifications() {
    git_test(|ctx| {
        let sha = ctx.create_upstream_merge(&["a"]);
        ctx.create_branch("feature");
        ctx.modify("a");

        assert_eq!(ctx.check_modifications(&["a", "d"], CiEnv::None), modified(sha, &["a"]),);
    });
}

#[test]
fn test_local_committed_modifications() {
    git_test(|ctx| {
        let sha = ctx.create_upstream_merge(&["a"]);
        ctx.create_upstream_merge(&["b", "c"]);
        ctx.create_branch("feature");
        ctx.modify("x");
        ctx.commit();
        ctx.modify("a");
        ctx.commit();

        assert_eq!(ctx.check_modifications(&["a", "d"], CiEnv::None), modified(sha, &["a"]),);
    });
}

#[test]
fn test_local_committed_modifications_subdirectory() {
    git_test(|ctx| {
        let sha = ctx.create_upstream_merge(&["a/b/c"]);
        ctx.create_upstream_merge(&["b", "c"]);
        ctx.create_branch("feature");
        ctx.modify("a/b/d");
        ctx.commit();

        assert_eq!(ctx.check_modifications(&["a/b"], CiEnv::None), modified(sha, &["a/b/d"]),);
    });
}

#[test]
fn test_local_changes_in_head_upstream() {
    git_test(|ctx| {
        // We want to resolve to the upstream commit that made modifications to a,
        // even if it is currently HEAD
        let sha = ctx.create_upstream_merge(&["a"]);
        assert_eq!(
            ctx.check_modifications(&["a", "d"], CiEnv::None),
            PathFreshness::LastModifiedUpstream { upstream: sha }
        );
    });
}

#[test]
fn test_local_changes_in_previous_upstream() {
    git_test(|ctx| {
        // We want to resolve to this commit, which modified a
        let sha = ctx.create_upstream_merge(&["a", "e"]);
        // Not to this commit, which is the latest upstream commit
        ctx.create_upstream_merge(&["b", "c"]);
        ctx.create_branch("feature");
        ctx.modify("d");
        ctx.commit();

        assert_eq!(
            ctx.check_modifications(&["a"], CiEnv::None),
            PathFreshness::LastModifiedUpstream { upstream: sha }
        );
    });
}

#[test]
fn test_local_no_upstream_commit_with_changes() {
    git_test(|ctx| {
        ctx.create_upstream_merge(&["a", "e"]);
        ctx.create_upstream_merge(&["a", "e"]);
        // We want to fall back to this commit, because there are no commits
        // that modified `x`.
        let sha = ctx.create_upstream_merge(&["a", "e"]);
        ctx.create_branch("feature");
        ctx.modify("d");
        ctx.commit();
        assert_eq!(
            ctx.check_modifications(&["x"], CiEnv::None),
            PathFreshness::LastModifiedUpstream { upstream: sha }
        );
    });
}

#[test]
fn test_local_no_upstream_commit() {
    git_test(|ctx| {
        let src = ctx.check_modifications(&["c", "d"], CiEnv::None);
        assert_eq!(src, PathFreshness::MissingUpstream);
    });
}

#[test]
fn test_local_changes_negative_path() {
    git_test(|ctx| {
        let upstream = ctx.create_upstream_merge(&["a"]);
        ctx.create_branch("feature");
        ctx.modify("b");
        ctx.modify("d");
        ctx.commit();

        assert_eq!(
            ctx.check_modifications(&[":!b", ":!d"], CiEnv::None),
            PathFreshness::LastModifiedUpstream { upstream: upstream.clone() }
        );
        assert_eq!(
            ctx.check_modifications(&[":!c"], CiEnv::None),
            modified(&upstream, &["b", "d"]),
        );
        assert_eq!(
            ctx.check_modifications(&[":!d", ":!x"], CiEnv::None),
            modified(&upstream, &["b"]),
        );
    });
}

#[test]
fn test_local_changes_subtree_that_used_bors() {
    // Here we simulate a very specific situation related to subtrees.
    // When you have merge commits locally, we should ignore them w.r.t. the artifact download
    // logic.
    // The upstream search code currently uses a simple heuristic:
    // - Find commits by bors (or in general an author with the merge commit e-mail)
    // - Find the newest such commit
    // This should make it work even for subtrees that:
    // - Used bors in the past (so they have bors merge commits in their history).
    // - Use Josh to merge rustc into the subtree, in a way that the rustc history is the second
    // parent, not the first one.
    //
    // In addition, when searching for modified files, we cannot simply start from HEAD, because
    // in this situation git wouldn't find the right commit.
    //
    // This test checks that this specific scenario will resolve to the right rustc commit, both
    // when finding a modified file and when finding a non-existent file (which essentially means
    // that we just lookup the most recent upstream commit).
    //
    // See https://github.com/rust-lang/rust/issues/101907#issuecomment-2697671282 for more details.
    git_test(|ctx| {
        ctx.create_upstream_merge(&["a"]);

        // Start unrelated subtree history
        ctx.run_git(&["switch", "--orphan", "subtree"]);
        ctx.modify("bar");
        ctx.commit();
        // Now we need to emulate old bors commits in the subtree.
        // Git only has a resolution of one second, which is a problem, since our git logic orders
        // merge commits by their date.
        // To avoid sleeping in the test, we modify the commit date to be forcefully in the past.
        ctx.create_upstream_merge(&["subtree/a"]);
        ctx.run_git(&["commit", "--amend", "--date", "Wed Feb 16 14:00 2011 +0100", "--no-edit"]);

        // Merge the subtree history into rustc
        ctx.switch_to_branch("main");
        ctx.run_git(&["merge", "subtree", "--allow-unrelated"]);

        // Create a rustc commit that modifies a path that we're interested in (`x`)
        let upstream_1 = ctx.create_upstream_merge(&["x"]);
        // Create another bors commit
        let upstream_2 = ctx.create_upstream_merge(&["a"]);

        ctx.switch_to_branch("subtree");

        // Create a subtree branch
        ctx.create_branch("subtree-pr");
        ctx.modify("baz");
        ctx.commit();
        // We merge rustc into this branch (simulating a "subtree pull")
        ctx.merge("main", "committer <committer@foo.bar>");

        // And then merge that branch into the subtree (simulating a situation right before a
        // "subtree push")
        ctx.switch_to_branch("subtree");
        ctx.merge("subtree-pr", "committer <committer@foo.bar>");

        // And we want to check that we resolve to the right commits.
        assert_eq!(
            ctx.check_modifications(&["x"], CiEnv::None),
            PathFreshness::LastModifiedUpstream { upstream: upstream_1 }
        );
        assert_eq!(
            ctx.check_modifications(&["nonexistent"], CiEnv::None),
            PathFreshness::LastModifiedUpstream { upstream: upstream_2 }
        );
    });
}

/// Trust: the verified compiletest lane is OPT-IN, and the default is untouched.
///
/// `--trust-verified` absent must leave `trust_verified()` false for every other
/// spelling of `x.py test`, because bootstrap forwards `--trust-verified` to
/// compiletest on exactly that predicate — and compiletest turns it into a
/// different rustc flag vector (`-Ztrust-verify=on -Ztrust-policy=strict`
/// instead of `-Ztrust-verify=off`). Silently flipping the default would turn
/// every existing green run into an unwitnessed one.
#[test]
fn trust_verified_is_opt_in_and_excludes_vanilla() {
    fn flags(args: &[&str]) -> Flags {
        Flags::parse(&args.iter().map(|a| a.to_string()).collect::<Vec<_>>())
    }

    let plain = flags(&["test", "--stage", "2", "tests/ui"]);
    assert!(!plain.cmd.trust_verified(), "default lane must not claim the verified lane");
    assert!(!plain.cmd.trust_vanilla());

    let vanilla = flags(&["test", "--stage", "2", "--trust-vanilla", "tests/ui"]);
    assert!(vanilla.cmd.trust_vanilla());
    assert!(!vanilla.cmd.trust_verified());

    let verified = flags(&["test", "--stage", "2", "--trust-verified", "tests/ui"]);
    assert!(verified.cmd.trust_verified());
    assert!(!verified.cmd.trust_vanilla(), "the verified lane is not the vanilla lane");

    // A non-`test` subcommand never claims a lane.
    assert!(!flags(&["build", "--stage", "2"]).cmd.trust_verified());
}

/// Trust: asking for both lanes is refused at argument parse, not resolved.
///
/// The two lanes assert opposite verification states for the same run; a run
/// that quietly picked one would mislabel every exception row it fed into
/// `tests/upstream-rust/test-exception-lanes.toml`.
#[test]
fn trust_vanilla_and_trust_verified_conflict() {
    let args = ["x.py", "test", "--stage", "2", "--trust-vanilla", "--trust-verified"]
        .iter()
        .map(|a| a.to_string());
    let err = <Flags as clap::Parser>::try_parse_from(args)
        .expect_err("--trust-vanilla --trust-verified must be refused");
    assert_eq!(err.kind(), clap::error::ErrorKind::ArgumentConflict, "{err}");
}

/// Trust: cleanup scope conflicts belong to the native parser, before any
/// default or selected crate step can assemble a compiler or delete output.
#[test]
fn clean_all_conflicts_with_stage_before_step_selection() {
    for paths in [&[][..], &["compiler/rustc"][..], &["library/core"][..]] {
        for stage in ["0", "1"] {
            for options in [
                vec!["clean", "--all", "--stage", stage],
                vec!["clean", "--stage", stage, "--all"],
                vec!["--stage", stage, "clean", "--all"],
            ] {
                let args = options
                    .into_iter()
                    .chain(paths.iter().copied())
                    .map(str::to_owned)
                    .collect::<Vec<_>>();
                let err = Flags::try_parse(&args)
                    .expect_err("--all and --stage must conflict even with explicit crate paths");
                assert_eq!(err.kind(), clap::error::ErrorKind::ArgumentConflict, "{args:?}: {err}");
            }
        }
    }
}

#[test]
fn nonconflicting_clean_scopes_and_explicit_paths_remain_accepted() {
    for paths in [&[][..], &["compiler/rustc"][..], &["library/core"][..]] {
        for (options, expected_all, expected_stage) in [
            (vec!["clean"], false, None),
            (vec!["clean", "--all"], true, None),
            (vec!["clean", "--stage", "0"], false, Some(0)),
            (vec!["clean", "--stage", "1"], false, Some(1)),
            (vec!["--stage", "1", "clean"], false, Some(1)),
        ] {
            let args = options
                .into_iter()
                .chain(paths.iter().copied())
                .map(str::to_owned)
                .collect::<Vec<_>>();
            let flags = Flags::try_parse(&args)
                .unwrap_or_else(|error| panic!("nonconflicting cleanup request {args:?}: {error}"));
            assert!(
                matches!(flags.cmd, Subcommand::Clean { all, stage }
                    if all == expected_all && stage == expected_stage),
                "{args:?}: {:?}",
                flags.cmd
            );
            assert_eq!(
                flags.paths,
                paths.iter().copied().map(PathBuf::from).collect::<Vec<_>>(),
                "{args:?}"
            );
        }
    }
}

/// Trust: a direct `cargo test` of bootstrap's lib (RUSTC unset) needs a stage0
/// compiler for its dry-run configs. The checkout's `build/<host>/stage0` wins; a
/// checkout without one (a git worktree) falls back to the compiler that built the
/// tests, instead of a `<tmp>/build/<host>/stage0/bin/trustc` that never exists.
#[test]
fn direct_test_run_rustc_prefers_checkout_stage0_then_the_build_compiler() {
    use super::direct_test_run_rustc;

    let dir = tempfile::tempdir().unwrap();
    let missing = dir.path().join("build/host/stage0/bin/trustc");
    assert_eq!(
        direct_test_run_rustc(missing.clone(), Some("/toolchain/bin/trustc")),
        PathBuf::from("/toolchain/bin/trustc")
    );
    fs::create_dir_all(missing.parent().unwrap()).unwrap();
    File::create(&missing).unwrap();
    assert_eq!(direct_test_run_rustc(missing.clone(), Some("/toolchain/bin/trustc")), missing);

    let absent = dir.path().join("elsewhere/trustc");
    for build_compiler in [None, Some("")] {
        let panic =
            std::panic::catch_unwind(|| direct_test_run_rustc(absent.clone(), build_compiler))
                .expect_err("no stage0 and no build compiler must stop the run");
        let message = panic.downcast_ref::<String>().cloned().unwrap_or_default();
        assert!(message.contains("set RUSTC (and CARGO)"), "{message}");
    }
}

/// Trust: whatever launched this test binary, the config it parses must name a
/// stage0 compiler that exists. Before `direct_test_run_rustc`, a direct run with
/// `CARGO_TARGET_DIR` set and no `build/<host>/stage0` resolved
/// `<tmp>/build/<host>/stage0/bin/trustc` and died in `detail_exit`.
#[test]
fn test_configs_resolve_an_existing_initial_rustc() {
    let config = TestCtx::new().config("check").create_config();
    // Trust: `initial_rustc` moved from Config to Session upstream; the
    // resolved stage0 compiler a direct test run picks is `external_rustc`.
    let rustc =
        config.external_rustc.clone().expect("a direct test run resolves an external stage0 rustc");
    let rustc = &rustc;
    let resolvable = rustc.exists()
        || (rustc.components().count() == 1
            && env::split_paths(&env::var_os("PATH").unwrap_or_default())
                .any(|dir| dir.join(rustc).is_file()));
    assert!(resolvable, "initial rustc does not exist: {}", rustc.display());
}

#[test]
fn dry_download_plans_ignore_and_do_not_populate_real_download_cache() {
    use std::sync::OnceLock;

    let context = crate::utils::tests::TestCtx::new();
    let mut requested = context.config("build").stage(1).create_config();
    requested.download_rustc_commit = Some("requested-commit".into());
    let mut local = context.config("build").stage(1).create_config();
    local.download_rustc_commit = None;
    assert!(requested.dry_run() && local.dry_run());

    let absent = OnceLock::from(None);
    let other = OnceLock::from(Some("another-real-session".into()));
    let fresh = OnceLock::new();
    for cache in [&absent, &other, &fresh] {
        assert_eq!(requested.download_rustc_commit_cached(cache), Some("requested-commit"));
        assert_eq!(local.download_rustc_commit_cached(cache), None);
        assert_eq!(requested.download_rustc_commit_cached(cache), Some("requested-commit"));
    }
    assert_eq!(absent.get(), Some(&None));
    assert_eq!(other.get().and_then(Option::as_deref), Some("another-real-session"));
    assert!(fresh.get().is_none());
}

// Trust: these are actual TOML parser inputs, not a second paired-input parser.
#[test]
fn vf5_resource_config_keeps_absence_and_source_relative_pair() {
    assert!(parse("").vf5_base.is_none());
    let digest = "12".repeat(32);
    let config =
        parse(&format!("[build]\nvf5-base = 'mathematics/base'\nvf5-base-sha256 = '{digest}'\n"));
    let input = config.vf5_base.as_ref().unwrap();
    assert_eq!(input.package, config.src.join("mathematics/base"));
    assert_eq!(input.manifest_sha256, digest);
}

#[test]
fn vf5_resource_config_refuses_each_missing_half() {
    for value in
        ["vf5-base = 'base'".to_owned(), format!("vf5-base-sha256 = '{}'", "12".repeat(32))]
    {
        assert!(std::panic::catch_unwind(|| parse(&format!("[build]\n{value}\n"))).is_err());
    }
}

#[test]
fn vf5_resource_config_refuses_malformed_digest_and_empty_package() {
    for digest in [String::new(), "12".to_owned(), "A0".repeat(32), "g0".repeat(32)] {
        assert!(
            std::panic::catch_unwind(|| parse(&format!(
                "[build]\nvf5-base = 'base'\nvf5-base-sha256 = '{digest}'\n"
            )))
            .is_err()
        );
    }
    assert!(
        std::panic::catch_unwind(|| parse(&format!(
            "[build]\nvf5-base = ''\nvf5-base-sha256 = '{}'\n",
            "12".repeat(32)
        )))
        .is_err()
    );
}

#[test]
fn linked_submodule_checkout_names_the_store_it_shares() {
    // A second worktree's checkout made by `scripts/submodule_sync.sh
    // --restore`: its `.git` file names <store>/worktrees/<id>, which has a
    // commondir. bootstrap's `update_submodule` must leave such a checkout to
    // the script.
    let temp = tempfile::TempDir::new().unwrap();
    let root = temp.path();
    let store = root.join("first/.git/modules/m");
    let registration = store.join("worktrees/m");
    fs::create_dir_all(&registration).unwrap();
    fs::write(registration.join("commondir"), "../..\n").unwrap();
    let linked = root.join("second/m");
    fs::create_dir_all(&linked).unwrap();
    fs::write(linked.join(".git"), "gitdir: ../../first/.git/modules/m/worktrees/m\n").unwrap();
    let shared = super::linked_submodule_store(&linked).expect("a linked checkout shares a store");
    assert_eq!(shared.canonicalize().unwrap(), store.canonicalize().unwrap());

    // The first checkout's own: its `.git` file names the store itself.
    let own = root.join("first/m");
    fs::create_dir_all(&own).unwrap();
    fs::write(own.join(".git"), "gitdir: ../.git/modules/m\n").unwrap();
    assert_eq!(super::linked_submodule_store(&own), None);
    // A clone of its own, and a directory nothing has checked out yet.
    let cloned = root.join("cloned");
    fs::create_dir_all(cloned.join(".git")).unwrap();
    assert_eq!(super::linked_submodule_store(&cloned), None);
    let empty = root.join("empty");
    fs::create_dir_all(&empty).unwrap();
    assert_eq!(super::linked_submodule_store(&empty), None);
}
