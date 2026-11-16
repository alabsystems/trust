use std::ffi::OsStr;
use std::fs;
use std::path::Path;
use std::process::Command;

use clap::Parser;

use super::{
    PreparationScope, anchored_program, ensure, ensure_bound, full_check_command, run_full_check,
};
use crate::core::config::Config;
use crate::core::config::flags::Flags;

fn configuration(arguments: &[&str], toml: &str, dry_run: bool) -> Config {
    let temp = tempfile::TempDir::new().unwrap();
    let config = temp.path().join("bootstrap.toml");
    fs::write(&config, toml).unwrap();
    // Put harness flags BEFORE the scenario, so a trailing -- really belongs
    // to the requested tool rather than swallowing this test's configuration.
    let mut args = vec![
        "--config".to_owned(),
        config.display().to_string(),
        "--build-dir".to_owned(),
        temp.path().join("build").display().to_string(),
        "--set".to_owned(),
        "build.submodules=false".to_owned(),
        "--set".to_owned(),
        "llvm.download-ci-llvm=false".to_owned(),
    ];
    if dry_run {
        args.push("--dry-run".into());
    }
    args.extend(arguments.iter().map(|argument| (*argument).to_owned()));
    Config::parse_with_env(Flags::parse(&args), |_| None)
}

#[test]
fn supported_test_options_keep_selected_native_request_scope() {
    for args in [
        vec!["test", "--stage", "1", "--force-rerun", "tests/run-make"],
        vec!["test", "--stage=1", "--tests", "compiler/rustc_interface"],
        vec![
            "test",
            "--stage",
            "0",
            "src/bootstrap",
            "--test-args",
            "--stage=2",
            "--set",
            "build.compiletest-allow-stage0=true",
        ],
        vec!["test", "--stage", "1", "tests/ui", "--", "--stage=2"],
        vec![
            "build",
            "--stage",
            "1",
            "compiler/rustc",
            "--set",
            "rust.trust-source-identity=false",
        ],
        vec!["r", "--stage", "0", "src/tools/tidy"],
    ] {
        let config = configuration(&args, "", true);
        assert_eq!(
            PreparationScope::for_config(&config),
            PreparationScope::RequestSources,
            "{args:?}"
        );
    }
}

#[test]
fn forwarded_stage_values_do_not_select_a_developer_stage() {
    for args in [
        vec!["test", "tests/ui", "--test-args", "--stage=1"],
        vec!["test", "tests/ui", "--compiletest-rustc-args", "--stage=1"],
        vec!["test", "tests/ui", "--", "--stage=1"],
        vec!["run", "src/tools/tidy", "--args", "--stage=1"],
    ] {
        let config = configuration(&args, "", true);
        assert!(!config.explicit_stage_from_cli, "{args:?}");
        assert_eq!(
            PreparationScope::for_config(&config),
            PreparationScope::FullEnvelope,
            "{args:?}"
        );
    }
}

#[test]
fn full_default_high_stage_and_distribution_requests_keep_full_envelope() {
    for args in [
        vec!["build"],
        vec!["run", "--stage", "0"],
        vec!["test", "--stage", "1", "--force-rerun"],
        vec!["build", "--stage", "2", "compiler/rustc"],
        vec!["test", "--stage", "1", "tests/ui", "--include-default-paths"],
        vec!["dist", "--stage", "1", "rustc"],
        vec!["install", "--stage", "1", "rustc"],
    ] {
        let config = configuration(&args, "", true);
        assert_eq!(
            PreparationScope::for_config(&config),
            PreparationScope::FullEnvelope,
            "{args:?}"
        );
    }
    let config = configuration(&["test", "tests/ui"], "[build]\ntest-stage = 1\n", true);
    assert_eq!(config.stage, 1);
    assert!(!config.explicit_stage_from_cli);
    assert_eq!(PreparationScope::for_config(&config), PreparationScope::FullEnvelope);
}

#[test]
fn native_parser_refuses_unknown_options_without_entering_a_build() {
    assert!(
        Flags::try_parse_from([
            "bootstrap",
            "test",
            "--stage",
            "1",
            "tests/ui",
            "--unknown-native-option",
        ])
        .is_err()
    );
    assert!(Flags::try_parse_from(["bootstrap", "build", "--stage", "1", ""]).is_err());
}

#[test]
fn maintenance_commands_do_not_fetch_the_recipe_envelope() {
    for command in ["fmt", "clean", "setup", "vendor"] {
        let config = configuration(&[command], "", false);
        assert_eq!(PreparationScope::for_config(&config), PreparationScope::NotProducer);
        ensure(&config, Path::new("missing-rustc"), Path::new("missing-cargo")).unwrap();
    }
}

#[test]
fn verbose_format_help_uses_ordinary_clap_without_a_build_session() {
    let args = ["fmt", "-h", "-v"].map(str::to_owned);
    assert!(!Flags::try_parse_verbose_help(&args));
}

#[test]
#[should_panic(expected = "status code: 1")]
fn native_config_still_refuses_unsupported_stage0_testing() {
    configuration(&["test", "--stage", "0", "tests/ui"], "", true);
}

#[test]
fn selected_requests_and_dry_runs_do_not_launch_the_full_checker() {
    for (args, dry_run) in [
        (vec!["test", "--stage", "1", "--tests", "--force-rerun", "src/bootstrap"], false),
        (vec!["build", "--stage", "2"], true),
    ] {
        let config = configuration(&args, "", dry_run);
        ensure(&config, Path::new("missing-rustc"), Path::new("missing-cargo")).unwrap();
    }
}

#[test]
fn early_flags_and_config_share_the_same_scope_without_a_python_classifier() {
    for args in [
        vec!["build"],
        vec!["--stage=1", "b", "compiler/rustc"],
        vec!["test", "tests/ui", "--test-args", "--stage=1"],
        vec!["test", "--stage", "1", "tests/ui", "--", "--stage=2"],
        vec!["build", "--stage", "1", "compiler/rustc", "--include-default-paths"],
        vec!["dist", "--stage", "1", "rustc"],
        vec!["fmt"],
        vec!["vendor"],
    ] {
        let native =
            Flags::try_parse(&args.iter().map(|arg| (*arg).to_owned()).collect::<Vec<_>>())
                .unwrap();
        let config = configuration(&args, "", true);
        assert_eq!(
            PreparationScope::for_flags(&native),
            PreparationScope::for_config(&config),
            "{args:?}"
        );
    }
}

#[test]
fn xpy_display_and_forwarded_arguments_keep_the_native_scope() {
    use std::ffi::OsString;
    let classify = |args: &[&str]| {
        crate::engine::xpy_preparation_scope(&args.iter().map(OsString::from).collect::<Vec<_>>())
    };
    for args in [
        vec![],
        vec!["--help"],
        vec!["help", "build"],
        vec!["build", "--help"],
        vec!["build", "--dry-run"],
    ] {
        assert_eq!(classify(&args).unwrap(), PreparationScope::NotProducer, "{args:?}");
    }
    assert_eq!(
        classify(&["test", "tests/ui", "--", "--stage=1"]).unwrap(),
        PreparationScope::FullEnvelope
    );
    assert_eq!(
        classify(&["b", "--stage=1", "compiler/rustc"]).unwrap(),
        PreparationScope::RequestSources
    );
    assert!(classify(&["build", "--invented-skip-full-check"]).is_err());
}

#[test]
fn development_component_keeps_stage2_and_distribution_full_envelope() {
    let config = configuration(&["build", "--stage", "1", "trustc-dev"], "", false);
    assert_eq!(PreparationScope::for_config(&config), PreparationScope::RequestSources);
    for kind in ["build", "dist", "install"] {
        let config = configuration(&[kind, "--stage", "2", "trustc-dev"], "", false);
        assert_eq!(PreparationScope::for_config(&config), PreparationScope::FullEnvelope);
    }
    for kind in ["dist", "install"] {
        let config = configuration(&[kind, "--stage", "1", "rustc-dev"], "", false);
        assert_eq!(PreparationScope::for_config(&config), PreparationScope::FullEnvelope);
    }
}

#[test]
fn input_layout_reuses_actual_config_includes_profile_set_and_cli_precedence() {
    use std::ffi::OsString;
    let directory = tempfile::tempdir().unwrap();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap();
    let included = directory.path().join("included.toml");
    let main = directory.path().join("bootstrap.toml");
    let included_output = directory.path().join("included-output");
    let set_output = directory.path().join("set-output");
    let cli_output = directory.path().join("cli-output");
    fs::write(&included, format!("[build]\nbuild-dir = '{}'\n", included_output.display()))
        .unwrap();
    fs::write(
        &main,
        "profile = 'compiler'\ninclude = ['included.toml']\n[build]\nsubmodules = false\n[llvm]\ndownload-ci-llvm = false\n",
    )
    .unwrap();
    for (extra, expected) in [
        (vec![], &included_output),
        (vec!["--set".into(), format!("build.build-dir='{}'", set_output.display())], &set_output),
        (
            vec![
                "--set".into(),
                format!("build.build-dir='{}'", set_output.display()),
                "--build-dir".into(),
                cli_output.display().to_string(),
            ],
            &cli_output,
        ),
    ] {
        let mut args = vec![
            "build".to_owned(),
            "--src".into(),
            root.display().to_string(),
            "--config".into(),
            main.display().to_string(),
            "--dry-run".into(),
        ];
        args.extend(extra);
        let layout =
            crate::engine::xpy_input_layout(&args.iter().map(OsString::from).collect::<Vec<_>>())
                .unwrap();
        let config = Config::parse_with_env(Flags::parse(&args), |_| None);
        assert_eq!(layout.source(), config.src);
        assert_eq!(layout.output(), config.out);
        assert_eq!(layout.output(), expected);
        assert!(!expected.exists(), "read-only selection must not create an output");
    }
    assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 2);
}

#[test]
fn input_layout_uses_absolute_output_and_explicit_native_source_without_a_session() {
    use std::ffi::OsString;
    let directory = tempfile::tempdir().unwrap();
    let config = directory.path().join("bootstrap.toml");
    fs::write(&config, "[build]\nbuild-dir = 'layout-relative-unused'\n").unwrap();
    let args = [
        OsString::from("build"),
        OsString::from("--src"),
        directory.path().as_os_str().to_owned(),
        OsString::from("--config"),
        config.as_os_str().to_owned(),
    ];
    let layout = crate::engine::xpy_input_layout(&args).unwrap();
    assert_eq!(layout.source(), directory.path());
    assert_eq!(layout.output(), std::path::absolute("layout-relative-unused").unwrap());
    assert!(!layout.output().exists());
    assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 1);
    for args in [vec![], vec![OsString::from("--help")], vec![OsString::from("help")]] {
        assert!(crate::engine::xpy_input_layout(&args).is_err());
    }
    assert!(
        crate::engine::xpy_input_layout(&["build".into(), "--invented-option".into()]).is_err()
    );
}

#[test]
fn full_check_uses_actual_driver_and_inherits_operator_policy() {
    let config = configuration(&["build"], "", true);
    let cargo = Path::new("relative tools/cargo");
    let rustc = Path::new("selected tools/trustc");
    let invocation_dir = std::env::current_dir().unwrap();
    let command = full_check_command(&config, rustc, cargo, OsStr::new("./bound python")).unwrap();
    assert_eq!(command.get_program(), invocation_dir.join("./bound python"));
    assert_eq!(command.get_current_dir(), Some(config.src.as_path()));
    let args: Vec<_> = command.get_args().collect();
    assert_eq!(&args[..3], &["-I", "-S", "-B"]);
    assert_eq!(args[3], config.src.join("scripts/bootstrap_dependency_closure.py"));
    assert_eq!(&args[4..6], &["check", "--repo-root"]);
    assert_eq!(args[6], config.src);
    assert_eq!(args[7], "--targo");
    assert_eq!(args[8], invocation_dir.join(cargo));
    let env: Vec<_> = command.get_envs().collect();
    let bound_rustc = invocation_dir.join(rustc);
    assert!(env.contains(&(OsStr::new("RUSTC"), Some(bound_rustc.as_os_str()))));
    assert!(env.contains(&(OsStr::new("RUSTC_BOOTSTRAP"), Some(OsStr::new("1")))));
    assert!(env.contains(&(OsStr::new("CARGO_BUILD_TARGET"), None)));
    let loader_path = crate::utils::helpers::dylib_path_var();
    if loader_path != "PATH" {
        assert!(env.contains(&(OsStr::new(loader_path), None)));
    }
    for name in [
        "CARGO_HOME",
        "CARGO_BUILD_WARNINGS",
        "TARGO_BUILD_WARNINGS",
        "CARGO_NET_OFFLINE",
        "RUSTFLAGS",
        "PATH",
    ] {
        assert!(!env.iter().any(|(key, _)| *key == name), "operator policy overridden: {name}");
    }
}

#[test]
fn changed_cwd_cannot_rebind_relative_tool_paths_or_compatibility_names() {
    let temp = tempfile::TempDir::new().unwrap();
    let invocation_dir = temp.path().join("invocation");
    for name in ["../tools/cargo", "./tools/targo", "tools/trustc"] {
        let bound = anchored_program(Path::new(name), &invocation_dir).unwrap();
        assert_eq!(bound, invocation_dir.join(name));
        assert_eq!(bound.file_name(), Path::new(name).file_name());
    }
    let absolute = temp.path().join("cargo");
    assert_eq!(anchored_program(&absolute, &invocation_dir).unwrap(), absolute);
    assert!(anchored_program(Path::new("cargo"), &invocation_dir).is_err());
}

#[cfg(unix)]
#[test]
fn actual_checker_failure_and_missing_executable_refuse() {
    let mut failure = Command::new("/bin/sh");
    failure.args(["-c", "exit 23"]);
    let error = run_full_check(&mut failure).unwrap_err();
    assert!(error.contains("refused") && error.contains("23"), "{error}");
    let temp = tempfile::TempDir::new().unwrap();
    let error = run_full_check(&mut Command::new(temp.path().join("absent"))).unwrap_err();
    assert!(error.contains("cannot execute"), "{error}");
}

/// A full request has one route on every host, macOS included: the complete
/// checker. This fixture is that checker's interpreter; it refuses with its
/// own exit status, so the refusal read here is the checker's and no host
/// refuses the request before the checker runs.
#[cfg(unix)]
#[test]
fn full_request_reaches_the_complete_checker_on_this_host() {
    use std::os::unix::fs::PermissionsExt;
    let directory = tempfile::tempdir().unwrap();
    let interpreter = directory.path().join("bound interpreter");
    let observed = directory.path().join("observed-mode");
    fs::write(
        &interpreter,
        format!("#!/bin/sh\nprintf '%s\\n' \"$5\" > '{}'\nexit 23\n", observed.display()),
    )
    .unwrap();
    fs::set_permissions(&interpreter, fs::Permissions::from_mode(0o700)).unwrap();
    let config = configuration(&["build"], "", false);
    assert_eq!(PreparationScope::for_config(&config), PreparationScope::FullEnvelope);
    let compiler = directory.path().join("selected trustc");
    let targo = directory.path().join("selected cargo");
    let error = ensure_bound(&config, &compiler, &targo, Some(interpreter.into_os_string()))
        .expect_err("the fixture checker refuses");
    assert!(error.contains("refused") && error.contains("23"), "{error}");
    assert_eq!(fs::read_to_string(&observed).unwrap(), "check\n");
}

#[cfg(unix)]
#[test]
fn existing_full_checker_command_is_really_executed_and_failure_stays_refused() {
    use std::os::unix::fs::PermissionsExt;
    let directory = tempfile::tempdir().unwrap();
    let interpreter = directory.path().join("bound interpreter");
    let observed = directory.path().join("observed-arguments");
    // A refusing executable fixture records the REAL production command; it
    // never claims dependency availability, Linux custody or Full completion.
    fs::write(
        &interpreter,
        format!("#!/bin/sh\nprintf '%s\\n' \"$@\" > '{}'\nexit 23\n", observed.display()),
    )
    .unwrap();
    fs::set_permissions(&interpreter, fs::Permissions::from_mode(0o700)).unwrap();
    let config = configuration(&["build"], "", true);
    let compiler = directory.path().join("selected trustc");
    let targo = directory.path().join("selected cargo");
    let mut command =
        full_check_command(&config, &compiler, &targo, interpreter.as_os_str()).unwrap();
    let error = run_full_check(&mut command).unwrap_err();
    assert!(error.contains("refused") && error.contains("23"), "{error}");
    let actual = fs::read_to_string(&observed).unwrap();
    let expected = [
        "-I".to_owned(),
        "-S".into(),
        "-B".into(),
        config.src.join("scripts/bootstrap_dependency_closure.py").display().to_string(),
        "check".into(),
        "--repo-root".into(),
        config.src.display().to_string(),
        "--targo".into(),
        targo.display().to_string(),
    ]
    .join("\n")
        + "\n";
    assert_eq!(actual, expected);
}
