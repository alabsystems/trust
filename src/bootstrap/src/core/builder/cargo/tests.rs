use std::ffi::OsStr;

use super::{
    RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV, Rustflags, TRUST_BOOTSTRAP_NO_VERIFY_FLAG,
    TRUST_BOOTSTRAP_NO_VERIFY_OPTION, TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV,
    TRUST_VERIFIABLE_LIBRARY_UNITS, apply_bootstrap_trust_verification_default,
    bootstrap_disables_default_trust_verification, bootstrap_verification_request_refusal,
    compiler_defaults_to_polonius, effective_codegen_units, effective_debuginfo_level, flags_env,
    is_bootstrap_no_verify_option, is_trust_verifier_unstable_option,
    parse_trust_verify_library_request, refuse_bootstrap_verification_request,
    retired_trust_bootstrap_shim_target_only_refusal, rustflags_request_bootstrap_verification,
    std_out_dir_needs_clear, trust_cg_codegen_flags, trust_cg_codegen_is_active,
    trust_verifier_controls, trust_verify_library_units_authorized,
};
use crate::core::backend::CodegenBackendKind;
use crate::core::builder::Kind;
use crate::core::config::{DebuginfoLevel, TargetSelection};
use crate::core::session::Mode;

// Trust: these exercise real ordinary Session selection and cache paths only;
// no fixture constructs an actual Full source/SDK/native execution owner.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn original_control_driver_requires_actual_full_owner_and_keeps_other_identities() {
    use super::{Builder, CargoInput};
    let context = crate::utils::tests::TestCtx::new();
    let session =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    let builder = Builder::new(&session);
    assert!(session.original_control_targo().is_err());
    assert_eq!(CargoInput::Seed.for_original(&session), CargoInput::Seed);
    assert_eq!(builder.cargo_input(Mode::ToolBootstrap), CargoInput::Seed);
    for input in [
        CargoInput::CurrentBuildTool,
        CargoInput::CurrentBuildToolSnapshotStd,
        CargoInput::CurrentNativeUnitTests,
    ] {
        assert_eq!(input.for_original(&session), input);
    }
    assert!(CargoInput::OriginalControl.uses_snapshot_compiler());
    assert!(!CargoInput::OriginalControl.uses_current_build_tool());
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn original_control_cache_writer_and_artifact_reader_are_separate_from_seed_and_produced() {
    use super::{Builder, CargoInput, Compiler, MakeflagsPolicy, makeflags_policy};
    let context = crate::utils::tests::TestCtx::new();
    let session =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    let builder = Builder::new(&session);
    let host = builder.host_target;
    let compiler = Compiler::new(0, host);
    for mode in [Mode::ToolBootstrap, Mode::ToolTarget] {
        let writer = builder.cargo_stage_out(compiler, mode, CargoInput::OriginalControl);
        assert_eq!(writer, builder.out.join(host).join("bootstrap-control-tools"));
        for other in [CargoInput::Seed, CargoInput::CurrentBuildTool] {
            let other_writer = builder.cargo_stage_out(compiler, mode, other);
            assert_ne!(writer, other_writer);
            assert_eq!(other_writer, builder.stage_out(compiler, other.cache_mode(mode)));
            assert_eq!(
                builder.cargo_out_for_input(compiler, mode, host, other),
                builder.cargo_out(compiler, other.cache_mode(mode), host)
            );
        }
        let reader = builder.cargo_out_for_input(compiler, mode, host, CargoInput::OriginalControl);
        assert_eq!(
            reader,
            writer.join(host).join(builder.cargo_dir(CargoInput::OriginalControl.cache_mode(mode)))
        );
        assert_eq!(writer, builder.cargo_stage_out(compiler, mode, CargoInput::OriginalControl));
    }
    assert_eq!(makeflags_policy(None, CargoInput::OriginalControl, true), MakeflagsPolicy::Strip);
}

#[test]
fn bootstrap_sysroot_rpath_preserves_direct_and_driver_interfaces() {
    use std::path::Path;

    use super::{append_sysroot_rpath, configured_direct_linker};

    for name in [
        "lld",
        "rust-lld",
        "ld.lld",
        "lld-link",
        "ld",
        "link",
        "aarch64-linux-gnu-ld",
        "lld-23",
        "lld-",
        "lld-٢٣",
    ] {
        assert!(configured_direct_linker(Some(Path::new(name))), "{name}");
    }
    for name in ["cc", "clang", "clang-23", "clang++", "lld-wrapper", "lld-2x", "ld64.lld"] {
        assert!(!configured_direct_linker(Some(Path::new(name))), "{name}");
    }
    assert!(!configured_direct_linker(None));
    for (triple, loader, origin) in [
        ("aarch64-apple-darwin", "@loader_path/../lib", false),
        ("x86_64-unknown-linux-gnu", "$ORIGIN/../lib", true),
    ] {
        let target = TargetSelection::from_user(triple);
        for direct in [false, true] {
            let mut flags = Rustflags::new(target);
            append_sysroot_rpath(&mut flags, target, "lib", direct);
            let actual: Vec<_> = flags.0.split('\x1f').collect();
            if direct {
                assert!(actual.contains(&"-Clink-arg=-rpath"));
                assert!(actual.contains(&format!("-Clink-arg={loader}").as_str()));
                assert!(actual.iter().all(|x| !x.contains("-Wl,")));
                assert_eq!(actual.contains(&"-Clink-arg=-z"), origin);
                assert_eq!(actual.contains(&"-Clink-arg=origin"), origin);
            } else {
                assert!(actual.contains(&format!("-Clink-args=-Wl,-rpath,{loader}").as_str()));
                assert_eq!(actual.contains(&"-Clink-args=-Wl,-z,origin"), origin);
            }
            assert_eq!(actual.contains(&"-Zosx-rpath-install-name"), !origin);
        }
    }
}

#[test]
fn bootstrap_sysroot_rpath_composed_commands_keep_tooltarget_closed() {
    use crate::core::build_steps::tool::SourceType;
    use crate::core::builder::{Builder, Cargo, Kind};
    use crate::core::compiler::Compiler;
    use crate::core::session::Session;
    use crate::utils::tests::TestCtx;

    for direct in [false, true] {
        let context = TestCtx::new();
        let mut config = context.config("build").stage(1).create_config();
        let host = config.host_target;
        config.rust_rpath = true;
        config.target_config.entry(host).or_default().linker =
            Some(if direct { "/owned/bin/lld" } else { "/usr/bin/cc" }.into());
        let build = Session::new(config);
        let builder = Builder::new(&build);
        for mode in [Mode::Rustc, Mode::ToolRustcPrivate, Mode::ToolTarget] {
            let cargo = Cargo::new(
                &builder,
                Compiler::new(0, host),
                mode,
                SourceType::InTree,
                host,
                Kind::Build,
            );
            let flags = cargo.rustflags.0.clone();
            let mut command = cargo.into_cmd();
            command.mark_as_executed();
            if mode == Mode::ToolTarget {
                assert!(!flags.contains("-rpath"), "standalone tool: {flags}");
                assert!(!flags.contains("loader_path"));
            } else if direct {
                assert!(flags.contains("-Clink-arg=-rpath"), "{mode:?}: {flags}");
                assert!(!flags.contains("-Wl,-rpath"));
            } else {
                assert!(flags.contains("-Clink-args=-Wl,-rpath,"), "{mode:?}: {flags}");
            }
        }
    }
}

// Trust: the 1.101 bootstrap must still run the shipped 1.99 Trust Cargo.
// These are Cargo's advertised option rows, not compiler version guesses.
#[test]
fn split_metadata_policy_accepts_both_seed_spellings() {
    use super::no_embed_metadata_flag_from_help;
    let legacy = "Available unstable (nightly-only) flags:\n    -Z no-embed-metadata  Avoid embedding metadata in library artifacts\n";
    let current = "Available unstable (nightly-only) flags:\n    -Z embed-metadata  Avoid embedding metadata in library artifacts\n";
    assert_eq!(no_embed_metadata_flag_from_help(legacy), Some("-Zno-embed-metadata"));
    assert_eq!(super::no_embed_metadata_flag_from_help(current), Some("-Zembed-metadata=no"));
    assert_eq!(
        no_embed_metadata_flag_from_help(&format!("{legacy}{current}")),
        Some("-Zembed-metadata=no"),
        "prefer the current spelling when a transitional seed advertises both",
    );
}

// Trust: a mention in prose or a similarly named option grants no capability.
#[test]
fn split_metadata_policy_requires_an_advertised_exact_option() {
    use super::no_embed_metadata_flag_from_help;
    for help in [
        "",
        "-Z binary-dep-depinfo Track changes to dependency artifacts",
        "This seed does not implement -Z embed-metadata or -Z no-embed-metadata",
        "-Z embed-metadata-extra A different option",
        "-Z no-embed-metadata-extra A different option",
    ] {
        assert_eq!(no_embed_metadata_flag_from_help(help), None, "{help:?}");
    }
}

// Trust: exercise actual composed consumer commands, not a routing predicate.
// Omit-hash is an existing supported SDK configuration; only the explicit
// engineering CLI target requires source identity.
#[test]
fn compiled_cargo_consumers_share_one_build_tool_and_leave_the_seed_pinned() {
    use crate::core::build_steps::{compile, tool};
    use crate::core::builder::{Builder, Cargo, CargoInput};
    use crate::core::compiler::Compiler;
    use crate::core::session::Session;
    use crate::utils::helpers::exe;
    use crate::utils::tests::TestCtx;

    let context = TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .args(&["--set", "rust.omit-git-hash=true"])
        .create_config();
    let build = Session::new(config);
    let builder = Builder::new(&build);
    let pinned = build.initial_cargo.clone();
    let configured = build.config.external_cargo.clone();
    let host = builder.host_target;
    let compiler = Compiler::new(0, host);
    let mut prerequisite = builder.bare_cargo(compiler, Mode::ToolBootstrap, host, Kind::Build);
    prerequisite.mark_as_executed();
    assert_eq!(prerequisite.get_program(), pinned.as_os_str());
    assert!(!builder.step_cache().contains::<tool::TargoBuildTool>());

    let expected = builder.tools_dir(compiler, host).join(exe("cargo", host));
    for mode in [
        Mode::Std,
        Mode::Rustc,
        Mode::Codegen,
        Mode::ToolTarget,
        Mode::ToolStd,
        Mode::ToolRustcPrivate,
    ] {
        let cargo =
            Cargo::new(&builder, compiler, mode, tool::SourceType::InTree, host, Kind::Build);
        let mut command = cargo.into_cmd();
        command.mark_as_executed();
        assert_eq!(command.get_program(), expected.as_os_str(), "{mode:?}");
        assert_eq!(
            command
                .get_envs()
                .find(|(key, _)| *key == OsStr::new("CARGO"))
                .and_then(|(_, value)| value),
            Some(expected.as_os_str()),
            "{mode:?}: nested Cargo must use the same selected program",
        );
        assert!(command.get_args().any(|arg| arg == "-Zembed-metadata=no"));
        assert!(!command.get_args().any(|arg| arg == "--unverified"));
    }
    let first = builder.build_cargo_program(CargoInput::CurrentBuildTool);
    let again = builder.build_cargo_program(CargoInput::CurrentBuildTool);
    assert_eq!(first.path, again.path);
    let producers =
        builder.step_cache().inspect_all_steps_of_type::<tool::TargoBuildTool, _>(|_, result| {
            (
                result.artifact.build_compiler.stage,
                result.artifact.tool_path.clone(),
                result.cargo.path.clone(),
            )
        });
    assert_eq!(producers, vec![(0, expected.with_file_name(exe("targo", host)), expected)]);
    assert!(!builder.step_cache().contains::<compile::Rustc>());
    assert!(
        builder
            .step_cache()
            .inspect_all_steps_of_type::<compile::Assemble, _>(|step, _| step.target_compiler.stage)
            .iter()
            .all(|stage| *stage == 0)
    );
    assert_eq!(build.initial_cargo, pinned);
    assert_eq!(build.config.external_cargo, configured);
    assert!(
        !std::fs::read_to_string(context.dir().join("bootstrap.toml")).unwrap().contains("cargo =")
    );
}

/// Every `Mode` bootstrap can drive a cargo invocation with. Spelled out rather
/// than derived so a new variant makes these tests fail to compile and forces a
/// decision about which side of the library/self-proof line it falls on.
const ALL_MODES: &[Mode] = &[
    Mode::Std,
    Mode::Rustc,
    Mode::Codegen,
    Mode::ToolBootstrap,
    Mode::ToolTarget,
    Mode::ToolStd,
    Mode::ToolRustcPrivate,
];

// Trust: every actual compiled producer must enforce immutable locks and
// offline source readiness, even without the full Python recipe-envelope check.
#[test]
fn native_cargo_producers_are_frozen_in_every_mode() {
    use crate::core::build_steps::tool::SourceType;
    use crate::core::builder::Builder;
    use crate::core::session::Session;
    use crate::utils::exec::BootstrapCommand;
    use crate::utils::tests::TestCtx;

    for kind in ["build", "check", "clippy", "doc", "test", "bench"] {
        for locked in [false, true] {
            let context = TestCtx::new();
            let setting = format!("build.locked-deps={locked}");
            let config = context.config(kind).stage(1).args(&["--set", &setting]).create_config();
            assert_eq!(config.locked_deps, locked);
            assert!(!config.vendor);
            let build = Session::new(config);
            let builder = Builder::new(&build);
            let host = builder.config.host_target;
            let compiler = builder.compiler(0, host);
            for &mode in ALL_MODES {
                // These combinations have no producer: Builder::cargo rejects
                // them before command construction for documentation requests.
                if kind == "doc" && matches!(mode, Mode::Codegen | Mode::ToolStd) {
                    continue;
                }
                let cargo = builder.cargo(compiler, mode, SourceType::InTree, host, builder.kind);
                let mut command = BootstrapCommand::from(cargo);
                command.mark_as_executed();
                assert_eq!(
                    command.get_args().filter(|arg| *arg == "--frozen").count(),
                    1,
                    "{kind} {mode:?} locked={locked}: producer needs frozen source policy",
                );
            }
        }
    }
}

// Trust: the 1.101 bootstrap must still request separate rmeta output through
// its admitted 1.99 Cargo; an unsupported or merely mentioned flag is not enough.
#[test]
fn metadata_sidecars_use_the_pinned_cargo_driver_spelling() {
    use super::no_embed_metadata_flag_from_help;

    assert_eq!(
        no_embed_metadata_flag_from_help(
            "    -Z no-embed-metadata  Avoid embedding metadata in library artifacts\n"
        ),
        Some("-Zno-embed-metadata"),
    );
    assert_eq!(
        no_embed_metadata_flag_from_help(
            "    -Z embed-metadata  Avoid embedding metadata in library artifacts\n"
        ),
        Some("-Zembed-metadata=no"),
    );
    assert_eq!(
        no_embed_metadata_flag_from_help(" -Z no-embed-metadata old\n -Z embed-metadata current\n"),
        Some("-Zembed-metadata=no"),
    );
    for unsupported in [
        "",
        "error: unknown unstable option embed-metadata",
        " -Z other-option use embed-metadata instead\n",
        " -Z no-embed-metadata-extra unrelated\n",
    ] {
        assert_eq!(no_embed_metadata_flag_from_help(unsupported), None);
    }
}

// Cargo omits target rustflags from explicit-target host dependencies. The
// seed's current off-switch must therefore also reach the compiler shim.
#[test]
fn seed_built_commands_request_host_verification_isolation() {
    use crate::core::build_steps::tool::SourceType;
    use crate::core::builder::Builder;
    use crate::core::session::Session;
    use crate::utils::exec::BootstrapCommand;
    use crate::utils::tests::TestCtx;

    for kind in ["build", "check", "test"] {
        let context = TestCtx::new();
        let config = context.config(kind).stage(1).create_config();
        let build = Session::new(config);
        let builder = Builder::new(&build);
        let host = builder.config.host_target;
        let compiler = builder.compiler(0, host);
        for &mode in ALL_MODES {
            let cargo = builder.cargo(compiler, mode, SourceType::InTree, host, builder.kind);
            let mut command = BootstrapCommand::from(cargo);
            command.mark_as_executed();
            assert_eq!(
                command
                    .get_envs()
                    .find(|(name, _)| *name == OsStr::new("TRUST_BOOTSTRAP_SHIM_NO_VERIFY"))
                    .map(|(_, value)| value),
                Some(Some(OsStr::new("1"))),
                "{kind} {mode:?}: target flags cannot isolate seed-built host dependencies"
            );
        }
    }
}

// Trust: x.py's actual Bootstrap command must bind the fixture's compiler to
// the real driver, rather than recursively recording its RUSTC wrapper.
#[test]
fn bootstrap_test_compiler_selection_uses_the_real_command_driver() {
    use crate::core::build_steps::tool::SourceType;
    use crate::core::builder::Builder;
    use crate::core::session::Session;
    use crate::utils::exec::BootstrapCommand;
    use crate::utils::tests::TestCtx;
    use crate::utils::tests::bootstrap_build_script::test_build_rustc;

    // Test invocations require stage1 or later. Their Bootstrap tool command
    // still uses the stage0 compiler, which is the binding checked below.
    for requested_stage in [1, 2] {
        let context = TestCtx::new();
        let config = context.config("test").stage(requested_stage).create_config();
        let build = Session::new(config);
        let builder = Builder::new(&build);
        let host = builder.config.host_target;
        // ToolBootstrap always uses stage0, including a later-stage test run.
        let compiler = builder.compiler(0, host);
        let cargo =
            builder.cargo(compiler, Mode::ToolBootstrap, SourceType::InTree, host, builder.kind);
        let mut command = BootstrapCommand::from(cargo);
        command.mark_as_executed();
        let configured = |name| {
            command
                .get_envs()
                .find_map(|(key, value)| (key == OsStr::new(name)).then_some(value).flatten())
                .and_then(OsStr::to_str)
        };
        let rustc = configured("RUSTC").unwrap();
        let real = configured("RUSTC_REAL").unwrap();
        assert_ne!(rustc, real, "the actual compiler must be distinct from its shim");
        assert_eq!(configured("RUSTC_SNAPSHOT"), Some(real));
        assert_eq!(
            test_build_rustc(
                Some(rustc),
                configured("RUSTC_WRAPPER"),
                configured("RUSTC_STAGE"),
                Some(real)
            ),
            Ok(Some(real)),
        );
    }
}

// Trust: check the real Cargo command, including compiler dependencies and all
// battery modes; merely preserving standalone AY's manifest misses consumers.
#[test]
fn bootstrap_commands_keep_verifier_overflow_checks_enabled() {
    use crate::core::build_steps::tool::SourceType;
    use crate::core::builder::Builder;
    use crate::core::session::Session;
    use crate::utils::exec::BootstrapCommand;
    use crate::utils::tests::TestCtx;

    for kind in ["build", "check", "test"] {
        let context = TestCtx::new();
        let config = context
            .config(kind)
            .stage(1)
            .with_default_toml_config("[rust]\ndebug = false\noverflow-checks-std = false\n")
            .create_config();
        let build = Session::new(config);
        let builder = Builder::new(&build);
        let host = builder.config.host_target;
        let compiler = builder.compiler(0, host);
        for &mode in ALL_MODES {
            let cargo = builder.cargo(compiler, mode, SourceType::InTree, host, builder.kind);
            let variable = super::cargo_profile_var("OVERFLOW_CHECKS", &builder.config, mode);
            let mut command = BootstrapCommand::from(cargo);
            command.mark_as_executed();
            let expected = if mode == Mode::Std { "false" } else { "true" };
            assert_eq!(
                command
                    .get_envs()
                    .find(|(name, _)| *name == OsStr::new(&variable))
                    .map(|(_, value)| value),
                Some(Some(OsStr::new(expected))),
                "{kind} {mode:?} must retain checked verifier arithmetic and explicit std policy"
            );
        }
    }
}

// Trust: rustc accepts both codegen spellings, split arguments, underscore
// aliases, and four false values. Test the encoded representation used at the
// final command boundary without mutating process-global flag variables.
#[test]
fn engine_overflow_refusal_recognizes_codegen_overrides() {
    for name in ["overflow-checks", "overflow_checks", "debug-assertions", "debug_assertions"] {
        for value in ["n", "no", "off", "false"] {
            for prefix in ["-C", "-C\x1f", "--codegen=", "--codegen\x1f"] {
                let flags = format!("-Cdebuginfo=1\x1f{prefix}{name}={value}");
                assert!(super::checked_engine_flags(&flags).is_err(), "{flags:?}");
            }
        }
    }
    for flags in [
        "",
        "-Cdebuginfo=1",
        "-Coverflow-checks=on",
        "--codegen=overflow_checks=yes",
        "-C\x1foverflow-checks=true",
        "--sysroot\x1f/path with spaces",
        "-Clink-arg=/path with -Coverflow-checks=off in its name",
    ] {
        assert!(super::checked_engine_flags(flags).is_ok(), "{flags:?}");
    }
    for flags in ["@hidden-flags", "-C\x1f@hidden-flags", "--codegen\x1f@hidden-flags"] {
        assert!(super::checked_engine_flags(flags).is_err(), "{flags:?}");
    }
    for flags in ["-Copt-level=3", "-C\x1fopt_level=0", "--codegen=opt-level=s"] {
        assert!(super::checked_engine_flags(flags).is_err(), "{flags:?}");
    }
}

#[test]
fn engine_overflow_refusal_checks_forwarded_cargo_config() {
    let directory = tempfile::tempdir().unwrap();
    let cwd = directory.path();
    for setting in [
        "profile.release.overflow-checks=false",
        "profile.dev.build-override.overflow-checks=false",
        "profile.release.package.ay.overflow-checks=false",
        "build.rustflags=['-C', 'overflow_checks=off']",
        "target.x.rustdocflags=['--codegen=overflow-checks=no']",
        "host.x.rustflags='-Coverflow-checks=false'",
        "env.RUSTC_HOST_FLAGS='-Coverflow-checks=off'",
        "env.RUSTC_HOST_FLAGS={value='-Coverflow-checks=off',force=true}",
        "include='extra.toml'",
        "extra.toml",
    ] {
        for args in
            [vec!["--config".into(), setting.into()], vec![format!("--config={setting}").into()]]
        {
            assert!(super::checked_engine_cargo_args(&args, cwd).is_err(), "{args:?}");
        }
    }
    for setting in [
        "profile.release.overflow-checks=true",
        "profile.dev.build-override.overflow-checks=true",
        "build.rustflags=['-Cdebuginfo=1']",
        "profile.release.debug-assertions=false",
        "net.offline=true",
    ] {
        assert!(
            super::checked_engine_cargo_args(&["--config".into(), setting.into()], cwd).is_ok()
        );
    }
    assert!(super::checked_engine_cargo_args(&["--config".into()], cwd).is_err());
    // An existing file wins even when its name is valid inline TOML.
    std::fs::write(cwd.join("net.offline=true"), "[profile.release]\noverflow-checks=false\n")
        .unwrap();
    assert!(super::checked_engine_cargo_args(&["--config=net.offline=true".into()], cwd).is_err());
}

#[test]
fn actual_engine_commands_refuse_overrides_and_clear_ambient_host_flags() {
    use crate::core::build_steps::tool::SourceType;
    use crate::core::builder::Builder;
    use crate::core::session::Session;
    use crate::utils::exec::BootstrapCommand;
    use crate::utils::tests::TestCtx;

    for stage in [0, 1] {
        for optimize in [false, true] {
            let context = TestCtx::new();
            let config = context
                .config("build")
                .stage(1)
                .with_default_toml_config(&format!(
                    "[rust]\noptimize={optimize}\ndebug-assertions=true\n"
                ))
                .create_config();
            let build = Session::new(config);
            let builder = Builder::new(&build);
            let host = builder.config.host_target;
            for &mode in ALL_MODES {
                // Bootstrap-only tools always use the seed, including in a
                // later stage's graph. Other modes exercise both compilers.
                let compiler =
                    builder.compiler(if mode == Mode::ToolBootstrap { 0 } else { stage }, host);
                for source in ["rustflags", "rustdocflags", "extra", "cargo", "assertions", "opt"] {
                    let mut cargo =
                        builder.cargo(compiler, mode, SourceType::InTree, host, builder.kind);
                    cargo.command.mark_as_executed();
                    match source {
                        "rustflags" => {
                            cargo.rustflags.arg("-Coverflow-checks=off");
                        }
                        "rustdocflags" => {
                            cargo.rustdocflags.arg("--codegen=overflow_checks=false");
                        }
                        "extra" => cargo.extra_rustflags.push("-Coverflow-checks=no".into()),
                        "assertions" => {
                            cargo.rustflags.arg("-Cdebug_assertions=off");
                        }
                        "opt" => {
                            cargo.rustflags.arg("-Copt-level=3");
                        }
                        "cargo" => {
                            cargo.args([
                                "--config",
                                "profile.release.package.ay.overflow-checks=false",
                            ]);
                        }
                        _ => unreachable!(),
                    }
                    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        BootstrapCommand::from(cargo)
                    }));
                    assert_eq!(
                        result.is_ok(),
                        mode == Mode::Std,
                        "{stage} {optimize} {mode:?} {source}"
                    );
                }
                let mut cargo =
                    builder.cargo(compiler, mode, SourceType::InTree, host, builder.kind);
                cargo.hostflags.rustc.clear();
                let mut command = BootstrapCommand::from(cargo);
                command.mark_as_executed();
                assert_eq!(
                    command
                        .get_envs()
                        .find(|(name, _)| *name == "RUSTC_HOST_FLAGS")
                        .map(|(_, value)| value),
                    Some(None)
                );
            }
        }
    }
}

// Trust: the pinned seed and current Cargo advertise different names for the
// same separate-metadata operation. Prefer the current name when both exist.
#[test]
fn embed_metadata_accepts_both_advertised_cargo_generations() {
    let old = "Available unstable (nightly-only) flags:\n    -Z no-embed-metadata           Avoid embedding metadata in library artifacts\n";
    let current = "Available unstable (nightly-only) flags:\n    -Z embed-metadata              Avoid embedding metadata in library artifacts\n";
    assert_eq!(super::no_embed_metadata_flag_from_help(old), Some("-Zno-embed-metadata"));
    assert_eq!(super::no_embed_metadata_flag_from_help(current), Some("-Zembed-metadata=no"));
    assert_eq!(
        super::no_embed_metadata_flag_from_help(&format!("{old}{current}")),
        Some("-Zembed-metadata=no")
    );
}

// Trust: a diagnostic, descriptive mention, prefix match or unknown help must
// not authorize an option, and must never silently remove metadata separation.
#[test]
fn embed_metadata_requires_an_exact_advertised_option() {
    for help in [
        "",
        "error: unknown `-Z` flag specified: embed-metadata",
        "    -Z another-feature         See -Z embed-metadata for details\n",
        "    -Z embed-metadata-extra    A different feature\n",
        "    -Zno-embed-metadata        Unrecognized help layout\n",
    ] {
        assert_eq!(super::no_embed_metadata_flag_from_help(help), None, "{help:?}");
    }
}

// Trust: native compiler units need a real successful native spelling; a
// compatibility/help refusal cannot fall back to an otherwise valid cargo.
#[cfg(unix)]
#[test]
fn native_unit_probe_refuses_alias_and_failed_capabilities() {
    use std::os::unix::fs::PermissionsExt;

    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("native-probe");
    for (help_status, native, metadata_status, accepted) in
        [(0, true, 0, true), (0, false, 0, false), (1, true, 0, false), (0, true, 1, false)]
    {
        let brand = if native { "--unverified" } else { "Cargo compatibility" };
        std::fs::write(
            &path,
            format!(
                r#"#!/bin/sh
if [ "$1" = --help ]; then printf '%s\n' '{brand}'; exit {help_status}; fi
[ "$1" = --unverified ] && shift
[ "$1" = -Z ] && [ "$2" = help ] || exit 99
printf '%s\n' '    -Z embed-metadata'; exit {metadata_status}
"#
            ),
        )
        .unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let context = crate::utils::exec::ExecutionContext::new(0, false);
            super::CargoProgram::probe_native(&context, path.clone())
        }));
        assert_eq!(result.is_ok(), accepted, "{help_status}/{native}/{metadata_status}");
        if let Ok(program) = result {
            assert_eq!(program.path, path);
            assert!(program.unverified_lane);
            assert_eq!(program.metadata_flag, "-Zembed-metadata=no");
        }
    }
    // Compatibility remains usable even when the original native path is
    // missing; selecting native must refuse rather than reuse this alias.
    std::fs::write(
        &path,
        "#!/bin/sh\nif [ \"$1\" = --help ]; then exit 0; fi\nprintf '%s\\n' '    -Z embed-metadata'\n",
    )
    .unwrap();
    let context = crate::utils::exec::ExecutionContext::new(0, false);
    let compatibility = super::CargoProgram::probe(&context, path.clone());
    let missing = temp.path().join("missing-native");
    for input in
        [super::CargoInput::CurrentBuildTool, super::CargoInput::CurrentBuildToolSnapshotStd]
    {
        let selected = compatibility.for_current_input(&context, missing.clone(), input);
        assert_eq!(selected.path, compatibility.path);
        assert_eq!(selected.unverified_lane, compatibility.unverified_lane);
        assert_eq!(selected.metadata_flag, compatibility.metadata_flag);
    }
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            compatibility.for_current_input(
                &context,
                missing,
                super::CargoInput::CurrentNativeUnitTests,
            )
        }))
        .is_err()
    );
}

// Trust: the native owner selects its actual produced spelling and managed queue;
// it retains the current generation's cache and selected compiler/std inputs.
#[test]
fn native_unit_command_uses_original_targo_and_current_cache() {
    use super::{Cargo, CargoInput};
    use crate::core::build_steps::tool::SourceType;
    use crate::core::builder::Builder;
    use crate::core::session::Session;
    use crate::utils::helpers::exe;
    use crate::utils::tests::TestCtx;

    let context = TestCtx::new();
    let config = context.config("test").stage(1).create_config();
    let session = Session::new(config);
    let builder = Builder::new(&session);
    let host = builder.host_target;
    let compiler = builder.compiler(0, host);
    let command = |input| {
        let cargo = Cargo::new_with_input(
            &builder,
            compiler,
            Mode::Rustc,
            SourceType::InTree,
            host,
            Kind::Test,
            input,
        );
        let mut command = cargo.into_cmd();
        command.mark_as_executed();
        command
    };
    let native = command(CargoInput::CurrentNativeUnitTests);
    let compatibility = command(CargoInput::CurrentBuildTool);
    let original =
        std::path::Path::new(compatibility.get_program()).with_file_name(exe("targo", host));
    assert_eq!(native.get_program(), original.as_os_str());
    let env = |command: &crate::utils::exec::BootstrapCommand, name: &str| {
        command
            .get_envs()
            .find(|(key, _)| *key == OsStr::new(name))
            .and_then(|(_, value)| value)
            .map(std::ffi::OsStr::to_owned)
    };
    assert_eq!(env(&native, "CARGO").as_deref(), Some(native.get_program()));
    for name in ["CARGO_TARGET_DIR", "CARGO_BUILD_BUILD_DIR", "RUSTC_REAL", "RUSTC_SYSROOT"] {
        assert_eq!(env(&native, name), env(&compatibility, name), "{name}");
    }
    assert!(!compatibility.get_args().any(|arg| {
        arg == OsStr::new("build.test-jobs=2") || arg == OsStr::new("build.test-weight=1")
    }));
    let mut native_args = native.get_args().collect::<Vec<_>>();
    assert_eq!(
        &native_args[1..5],
        ["--config", "build.test-jobs=2", "--config", "build.test-weight=1"].map(OsStr::new),
    );
    native_args.drain(1..5);
    assert_eq!(native_args, compatibility.get_args().collect::<Vec<_>>());
}

// Trust: failed/missing tools and invalid output may not fall back to an
// option or run a build. These fixtures exercise the real process boundary.
#[cfg(unix)]
#[test]
fn embed_metadata_probe_refuses_missing_failed_and_unparseable_tools() {
    use std::os::unix::fs::PermissionsExt;

    use super::CargoProgram;
    use crate::utils::exec::ExecutionContext;

    let temp = tempfile::tempdir().unwrap();
    let cargo = temp.path().join("bound cargo");
    let probe = || {
        // Delay failures to prove the capability check itself rejects them.
        let exec_ctx = ExecutionContext::new(0, false);
        CargoProgram::probe(&exec_ctx, cargo.clone())
    };
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(&probe)).is_err());

    for body in [
        "printf '%s\\n' '    -Z no-embed-metadata'; exit 1",
        "printf '\\377'",
        "printf '%s\\n' '    -Z unrelated-feature'",
    ] {
        std::fs::write(
            &cargo,
            format!("#!/bin/sh\nif [ \"$1\" = --help ]; then exit 0; fi\n{body}\n"),
        )
        .unwrap();
        std::fs::set_permissions(&cargo, std::fs::Permissions::from_mode(0o755)).unwrap();
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(&probe)).is_err(),
            "{body} must refuse"
        );
    }

    std::fs::write(
        &cargo,
        "#!/bin/sh\nif [ \"$1\" = --help ]; then exit 0; fi\n\
         [ \"$1\" = -Z ] && [ \"$2\" = help ] || exit 99\n\
         printf '%s\\n' '    -Z no-embed-metadata'\n",
    )
    .unwrap();
    assert_eq!(probe().metadata_flag, "-Zno-embed-metadata");
}

// Trust: exercise the actual Cargo command boundary, including final flag/env
// propagation. A layout fix limited to compiler tests leaves `x check compiler`
// and full tool builds unable to spawn rustc on a large dependency graph.
#[test]
fn bootstrap_commands_keep_dynamic_library_paths_bounded() {
    use crate::core::build_steps::tool::SourceType;
    use crate::core::builder::Builder;
    use crate::core::session::Session;
    use crate::utils::exec::BootstrapCommand;
    use crate::utils::tests::TestCtx;

    for kind in ["build", "check", "test"] {
        let context = TestCtx::new();
        let build = Session::new(context.config(kind).stage(1).create_config());
        let builder = Builder::new(&build);
        let host = builder.config.host_target;
        let compiler = builder.compiler(0, host);
        for &mode in ALL_MODES {
            let cargo = builder.cargo(compiler, mode, SourceType::InTree, host, builder.kind);
            let mut command = BootstrapCommand::from(cargo);
            command.mark_as_executed();
            for control in
                ["CARGO_UNSTABLE_BUILD_DIR_NEW_LAYOUT", "CARGO_UNSTABLE_FINE_GRAIN_LOCKING"]
            {
                assert_eq!(
                    command.get_envs().find(|(name, _)| *name == control).map(|(_, value)| value),
                    Some(Some(OsStr::new("false"))),
                    "{kind} {mode:?} must use a bounded dynamic-library search path"
                );
            }
        }
    }
}

// Trust: Cargo isolates host dependencies from RUSTFLAGS under --target. Inspect
// the composed commands: stage0 target flags alone cannot make a bootstrap
// tool's build scripts/proc macros native, and the shim owns seed capability.
#[test]
fn bootstrap_seed_host_units_receive_the_capability_checked_native_marker() {
    use crate::core::build_steps::tool::SourceType;
    use crate::core::builder::Builder;
    use crate::core::session::Session;
    use crate::utils::exec::BootstrapCommand;
    use crate::utils::tests::TestCtx;

    for kind in ["build", "check", "test"] {
        let context = TestCtx::new();
        let build = Session::new(context.config(kind).stage(2).create_config());
        let builder = Builder::new(&build);
        let host = builder.config.host_target;
        for stage in [0, 1] {
            let compiler = builder.compiler(stage, host);
            for mode in [Mode::ToolBootstrap, Mode::ToolTarget, Mode::Std] {
                // ToolBootstrap is always built with the snapshot compiler.
                if mode == Mode::ToolBootstrap && stage != 0 {
                    continue;
                }
                let cargo = builder.cargo(compiler, mode, SourceType::InTree, host, builder.kind);
                let mut command = BootstrapCommand::from(cargo);
                command.mark_as_executed();
                assert_eq!(
                    command
                        .get_envs()
                        .find(|(name, _)| *name == "TRUST_BOOTSTRAP_SHIM_NO_VERIFY")
                        .map(|(_, value)| value),
                    Some(Some(OsStr::new("1"))),
                    "{kind} {mode:?} stage{stage}: --target host units lost native policy"
                );
                assert_eq!(
                    command
                        .get_envs()
                        .find(|(name, _)| *name == "RUSTC_WRAPPER")
                        .map(|(_, value)| value),
                    Some(Some(builder.bootstrap_out.join("rustc").as_os_str())),
                    "the marker must reach the existing capability-checking shim"
                );
                assert!(
                    !command.get_envs().any(|(name, _)| name == "TRUST_NO_VERIFY"),
                    "the command must not bypass per-unit shim/verification policy"
                );
            }
        }
    }
}

/// Every rustflags string the two verifier questions are asked about, so both
/// answers are always taken over the SAME set of tokens.
const VERIFIER_CONTROL_RUSTFLAGS: &[&str] = &[
    "-Ztrust-verify-full",
    "-Ztrust-verify=on",
    "-Ztrust-policy=advisory",
    "-Z trust-verify-output=json",
    "-Ztrust-verify-function-budget-ms=60000",
    "-Ztrust-policy=memory-safe",
];

#[test]
fn trust_verifier_control_detection_accepts_combined_and_split_flags() {
    for rustflags in VERIFIER_CONTROL_RUSTFLAGS {
        assert!(
            !trust_verifier_controls(rustflags).is_empty(),
            "{rustflags} is a verifier control"
        );
    }
    assert!(trust_verifier_controls("-Zrandomize-layout -Cdebuginfo=2").is_empty());
    assert!(trust_verifier_controls("-Ztrustworthy-layout").is_empty());
    // Both token shapes yield the option WITHOUT the `-Z`, which is the form
    // the off-switch comparison is made against.
    assert_eq!(trust_verifier_controls("-Ztrust-verify=off"), vec!["trust-verify=off"]);
    assert_eq!(trust_verifier_controls("-Z trust-verify=off"), vec!["trust-verify=off"]);
    assert_eq!(
        trust_verifier_controls("-Wrust_2018_idioms -Ztrust-verify=off -Ztrust-policy=advisory"),
        vec!["trust-verify=off", "trust-policy=advisory"]
    );
}

#[test]
fn no_verify_option_and_flag_are_the_same_switch() {
    assert_eq!(TRUST_BOOTSTRAP_NO_VERIFY_FLAG, format!("-Z{TRUST_BOOTSTRAP_NO_VERIFY_OPTION}"));
}

#[test]
fn non_stage0_bootstrap_uses_no_verify_env_by_default() {
    assert!(bootstrap_disables_default_trust_verification(1, ""));
}

#[test]
fn stage0_bootstrap_does_not_use_no_verify_env() {
    assert!(!bootstrap_disables_default_trust_verification(0, ""));
}

/// FAIL-OPEN REGRESSION. The suppression used to admit ANY verifier control,
/// while the self-proof panic refuses everything except the exact off-switch —
/// so the residual cases were unreachable only by accident of ordering, and the
/// two functions shared no assertion. Narrowing the panic later would silently
/// have produced units with no off-switch and verification default-ON.
///
/// This pins the coupling as a property of the SUPPRESSION alone, so it holds
/// whatever the panic does: a verifier control that is not bootstrap's own
/// off-switch never suppresses the default, and the composed rustflags still
/// end with the off-switch.
#[test]
fn only_the_exact_off_switch_suppresses_the_bootstrap_default() {
    for rustflags in VERIFIER_CONTROL_RUSTFLAGS {
        assert!(
            bootstrap_disables_default_trust_verification(1, rustflags),
            "{rustflags} must not suppress bootstrap's off-switch default"
        );
        let (_, value) = bootstrap_rustflags_env(1, &rustflags.split(' ').collect::<Vec<_>>());
        assert!(
            value.split(['\x1f', ' ']).any(|flag| flag == TRUST_BOOTSTRAP_NO_VERIFY_FLAG),
            "{rustflags} must still be handed the off-switch, got {value:?}"
        );
    }

    // The one case that legitimately suppresses it: the flag is already there,
    // in either token shape, so it is not duplicated.
    assert!(!bootstrap_disables_default_trust_verification(1, "-Ztrust-verify=off"));
    assert!(!bootstrap_disables_default_trust_verification(1, "-Z trust-verify=off"));
    assert!(!bootstrap_disables_default_trust_verification(
        1,
        "-Wrust_2018_idioms -Ztrust-verify=off"
    ));

    // Mixed: bootstrap's off-switch plus a control the refusal rejects. The
    // refusal is what stops this reaching a compiler today; the suppression
    // answer stays consistent either way.
    assert!(rustflags_request_bootstrap_verification("-Ztrust-verify=off -Ztrust-policy=advisory"));
}

#[test]
fn bootstrap_allows_only_the_exact_off_switch() {
    assert!(!rustflags_request_bootstrap_verification("-Ztrust-verify=off"));
    assert!(!rustflags_request_bootstrap_verification("-Z trust-verify=off"));
    assert!(rustflags_request_bootstrap_verification("-Ztrust-verify=on"));
    assert!(rustflags_request_bootstrap_verification("-Ztrust-verify-full"));
    assert!(rustflags_request_bootstrap_verification("-Z trust-policy=advisory"));
}

/// `-Z` option names accept `_` for `-` (the driver normalizes before lookup),
/// so the underscore spellings are the SAME controls and both walker questions
/// must answer the same about them. Before the normalization in
/// `is_trust_verifier_unstable_option`, `-Ztrust_policy=advisory` walked past
/// the self-proof refusal — and on a unit named by the library opt-in, whose
/// shim replaces only the on/off switch, the policy downgrade would have
/// survived into the one verifying compile.
#[test]
fn underscore_spellings_are_the_same_verifier_controls() {
    // Requests, in the underscore spelling, still refused.
    assert!(rustflags_request_bootstrap_verification("-Ztrust_verify=on"));
    assert!(rustflags_request_bootstrap_verification("-Z trust_policy=advisory"));
    assert!(rustflags_request_bootstrap_verification("-Ztrust_verify_session=x"));
    assert!(rustflags_request_bootstrap_verification("-Ztrust-verify_session=x"));
    // The off-switch, in the underscore spelling, is still the off-switch:
    // not a request, and it suppresses the default so exactly one off-switch
    // (in whichever spelling the caller authored) reaches the driver.
    assert!(!rustflags_request_bootstrap_verification("-Ztrust_verify=off"));
    assert!(!bootstrap_disables_default_trust_verification(1, "-Ztrust_verify=off"));
    // An underscored VALUE cannot alias the off-switch's name+value identity.
    assert!(rustflags_request_bootstrap_verification("-Ztrust-verify=o_ff"));
}

/// STEP 4 falsification, direction one: the library lane's own channel — the
/// env opt-in — never reaches the self-proof refusal, because it never rides
/// rustflags. An authorized `Mode::Std` invocation still composes rustflags
/// that carry only the off-switch, and the refusal sees nothing to refuse.
#[test]
fn the_library_lane_env_channel_never_trips_the_self_proof_refusal() {
    let units = parse_trust_verify_library_request(Some(OsStr::new("core")))
        .expect("`core` is an allowed library unit")
        .expect("a set value parses to a unit list");
    assert_eq!(units, vec!["core".to_string()]);
    assert!(trust_verify_library_units_authorized(Mode::Std, 1));
    // The composed rustflags of that same invocation, off-switch included.
    let (_, rustflags) = bootstrap_rustflags_env(1, &[]);
    assert!(
        bootstrap_verification_request_refusal(Mode::Std, &rustflags).is_none(),
        "the lane's rustflags must not read as a self-proof request: {rustflags:?}"
    );
}

/// STEP 4 falsification, direction two: the protected path still panics, and
/// it panics even for a spelling that names the library lane's own controls.
/// The lane is separately NAMED precisely so the refusal never needs a carve-out;
/// this pins that nobody narrows the panic "for the std lane" later.
#[test]
#[should_panic(expected = "bootstrap compiler verification flags are unsupported")]
fn the_library_lane_name_cannot_enter_through_rustflags() {
    refuse_bootstrap_verification_request(
        Mode::Std,
        "-Ztrust-verify-session=bootstrap-library-core",
    );
}

/// Reproduce `Cargo::from`'s composition: bootstrap's own flags, then the
/// verification default, then the env pair Cargo is handed.
fn bootstrap_rustflags_env(
    build_compiler_stage: u32,
    bootstrap_flags: &[&str],
) -> (String, String) {
    let mut rustflags = Rustflags::new(TargetSelection::from_user("aarch64-apple-darwin"));
    for flag in bootstrap_flags {
        rustflags.arg(flag);
    }
    apply_bootstrap_trust_verification_default(&mut rustflags, build_compiler_stage);
    let (var, value) = flags_env("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", &rustflags.0);
    (var.to_string(), value)
}

/// The regression this pins: Cargo honours exactly ONE rustflags source, so the
/// off-switch has to be in the same payload as bootstrap's other flags. Deliver
/// it through `CARGO_TARGET_<TRIPLE>_RUSTFLAGS` instead and Cargo drops it on
/// the floor, silently verifying the whole third-party dependency graph.
#[test]
fn bootstrap_off_switch_rides_the_same_lane_as_bootstrap_s_other_flags() {
    // `-Wrust_2018_idioms` is unconditional in bootstrap, so the competing
    // `RUSTFLAGS`/`CARGO_ENCODED_RUSTFLAGS` lane always exists in practice.
    let (var, value) = bootstrap_rustflags_env(1, &["-Wrust_2018_idioms", "-Wunused_lifetimes"]);

    assert!(matches!(var.as_str(), "RUSTFLAGS" | "CARGO_ENCODED_RUSTFLAGS"), "{var}");
    assert!(value.contains(TRUST_BOOTSTRAP_NO_VERIFY_FLAG), "{var}={value:?}");
    assert!(value.contains("-Wrust_2018_idioms"), "{var}={value:?}");
}

#[test]
fn bootstrap_off_switch_survives_when_bootstrap_has_no_other_flags() {
    let (var, value) = bootstrap_rustflags_env(1, &[]);

    assert_eq!(var, "RUSTFLAGS");
    assert_eq!(value, TRUST_BOOTSTRAP_NO_VERIFY_FLAG);
}

#[test]
fn stage0_units_keep_the_seed_default() {
    let (_, value) = bootstrap_rustflags_env(0, &["-Wrust_2018_idioms"]);

    assert!(!value.contains("trust-verify"), "{value:?}");
}

#[test]
fn an_explicit_off_switch_is_not_duplicated() {
    let (_, value) = bootstrap_rustflags_env(1, &["-Ztrust-verify=off"]);

    assert_eq!(value.matches(TRUST_BOOTSTRAP_NO_VERIFY_FLAG).count(), 1, "{value:?}");
}

/// A developer control that is NOT bootstrap's off-switch no longer takes
/// ownership of the verifier surface. It is refused before it can reach a
/// compiler (`refuse_bootstrap_verification_request`), and if that refusal is
/// ever narrowed, the unit still gets the off-switch rather than defaulting to
/// verification ON. The control itself is preserved, so nothing is lost.
#[test]
fn a_deliberate_verifier_control_does_not_strip_the_default() {
    let mut rustflags = Rustflags::new(TargetSelection::from_user("aarch64-apple-darwin"));
    rustflags.arg("-Ztrust-verify-output=json");
    apply_bootstrap_trust_verification_default(&mut rustflags, 1);

    assert!(rustflags.0.contains("-Ztrust-verify-output=json"), "{:?}", rustflags.0);
    assert!(rustflags.0.contains(TRUST_BOOTSTRAP_NO_VERIFY_FLAG), "{:?}", rustflags.0);
}

#[test]
fn trust_cg_abort_policy_starts_with_the_staged_compiler() {
    assert!(!trust_cg_codegen_is_active(0, &CodegenBackendKind::TrustCg));
    assert!(trust_cg_codegen_is_active(1, &CodegenBackendKind::TrustCg));
    assert!(trust_cg_codegen_is_active(2, &CodegenBackendKind::TrustCg));
    assert!(!trust_cg_codegen_is_active(1, &CodegenBackendKind::Llvm));
    assert!(!trust_cg_codegen_is_active(1, &CodegenBackendKind::Custom("other".into())));
}

#[test]
fn trust_cg_profiles_disable_unimplemented_debuginfo() {
    assert_eq!(effective_debuginfo_level(true, DebuginfoLevel::Full), DebuginfoLevel::None);
    assert_eq!(
        effective_debuginfo_level(true, DebuginfoLevel::LineTablesOnly),
        DebuginfoLevel::None
    );
    assert_eq!(
        effective_debuginfo_level(false, DebuginfoLevel::LineTablesOnly),
        DebuginfoLevel::LineTablesOnly
    );
}

#[test]
fn trust_cg_profiles_force_the_single_supported_codegen_unit() {
    assert_eq!(effective_codegen_units(true, None), Some(1));
    assert_eq!(effective_codegen_units(true, Some(16)), Some(1));
    assert_eq!(effective_codegen_units(false, Some(16)), Some(16));
    assert_eq!(effective_codegen_units(false, None), None);
}

#[test]
fn trust_cg_panic_flags_cover_normal_and_test_units() {
    assert_eq!(trust_cg_codegen_flags(false, false), &[] as &[&str]);
    assert_eq!(trust_cg_codegen_flags(false, true), &[] as &[&str]);
    assert_eq!(trust_cg_codegen_flags(true, false), &["-Cpanic=abort"]);
    assert_eq!(trust_cg_codegen_flags(true, true), &["-Cpanic=abort", "-Zpanic-abort-tests"]);
}

// ---------------------------------------------------------------------------
// The self-proof refusal, and the per-unit `library/` opt-in that does NOT
// relax it. Two different claims, two different switches.
// ---------------------------------------------------------------------------

/// (A) "bootstrap verified ITSELF" stays blocked. The refusal is not narrowed by
/// the library opt-in, and it does not care which `Mode` asked: a verifier
/// control in bootstrap's own rustflags is invocation-wide, so honouring one for
/// a `Mode::Std` invocation would verify std's entire third-party dependency
/// graph with no unit named anywhere.
#[test]
fn the_self_proof_refusal_still_fires_for_every_mode() {
    for mode in ALL_MODES {
        for rustflags in [
            "-Ztrust-verify=on",
            "-Z trust-verify=on",
            "-Ztrust-verify-full",
            "-Wrust_2018_idioms -Ztrust-policy=certify",
        ] {
            let refusal = bootstrap_verification_request_refusal(*mode, rustflags);
            let refusal = refusal.unwrap_or_else(|| {
                panic!("{mode:?} accepted bootstrap verification {rustflags:?}")
            });
            assert!(
                refusal.starts_with(
                    "bootstrap compiler verification flags are unsupported without an \
                     authenticated artifact-bound bootstrap protocol; \
                     use `targo trust verify self --full-verifier` instead"
                ),
                "{refusal}"
            );
        }
    }
}

#[test]
fn the_self_proof_refusal_leaves_the_off_switch_and_ordinary_flags_alone() {
    for mode in ALL_MODES {
        assert!(bootstrap_verification_request_refusal(*mode, "").is_none());
        assert!(bootstrap_verification_request_refusal(*mode, "-Ztrust-verify=off").is_none());
        assert!(bootstrap_verification_request_refusal(*mode, "-Z trust-verify=off").is_none());
        assert!(
            bootstrap_verification_request_refusal(*mode, "-Wrust_2018_idioms -Cdebuginfo=2")
                .is_none()
        );
    }
}

#[test]
#[should_panic(expected = "bootstrap compiler verification flags are unsupported")]
fn compiler_units_still_panic_on_a_bootstrap_verification_request() {
    refuse_bootstrap_verification_request(Mode::Rustc, "-Wrust_2018_idioms -Ztrust-verify=on");
}

#[test]
#[should_panic(expected = "bootstrap compiler verification flags are unsupported")]
fn bootstrap_tool_units_still_panic_on_a_bootstrap_verification_request() {
    refuse_bootstrap_verification_request(Mode::ToolBootstrap, "-Ztrust-policy=certify");
}

/// The opt-in is not a way into the rustflags lane: a library invocation that
/// asks for verification through RUSTFLAGS is refused exactly like a compiler
/// one.
#[test]
#[should_panic(expected = "bootstrap compiler verification flags are unsupported")]
fn library_units_still_panic_on_a_bootstrap_verification_request() {
    refuse_bootstrap_verification_request(Mode::Std, "-Ztrust-verify=on");
}

/// (B) the per-unit opt-in is honoured for library invocations and refused
/// everywhere else. `Mode::Std` is the only mode whose units are `library/`
/// crates; every other mode is the compiler, bootstrap, or a tool.
#[test]
fn the_library_opt_in_is_refused_for_compiler_bootstrap_and_tool_units() {
    for mode in ALL_MODES {
        for stage in [1, 2, 3] {
            assert_eq!(
                trust_verify_library_units_authorized(*mode, stage),
                *mode == Mode::Std,
                "{mode:?} at stage {stage}"
            );
        }
    }
}

/// The stage0 build compiler is the SEED, whose vintage is the pin's and not
/// this tree's. It is never the "already-built stage2 trustc" this lane means.
#[test]
fn the_library_opt_in_never_runs_on_the_stage0_seed() {
    for mode in ALL_MODES {
        assert!(!trust_verify_library_units_authorized(*mode, 0), "{mode:?}");
    }
}

#[test]
fn an_unset_opt_in_is_the_only_silent_outcome() {
    assert_eq!(parse_trust_verify_library_request(None), Ok(None));
}

#[test]
fn the_opt_in_accepts_the_named_library_units() {
    assert_eq!(
        parse_trust_verify_library_request(Some(OsStr::new("core"))),
        Ok(Some(vec!["core".to_string()]))
    );
    assert_eq!(
        parse_trust_verify_library_request(Some(OsStr::new(" core , alloc "))),
        Ok(Some(vec!["core".to_string(), "alloc".to_string()]))
    );
    // Cargo spells crate names with underscores; accept either spelling and
    // canonicalize, so `panic-abort` and `panic_abort` cannot disagree.
    assert_eq!(
        parse_trust_verify_library_request(Some(OsStr::new("panic-abort,panic_abort"))),
        Ok(Some(vec!["panic_abort".to_string()]))
    );
    for unit in TRUST_VERIFIABLE_LIBRARY_UNITS {
        assert!(
            parse_trust_verify_library_request(Some(OsStr::new(unit))).is_ok(),
            "allowlisted unit {unit} was rejected"
        );
    }
}

/// A control that is silently ignored is indistinguishable from one that
/// worked. Every degenerate input is an error, not a no-op.
#[test]
fn a_malformed_opt_in_is_an_error_rather_than_a_silent_no_op() {
    for raw in ["", " ", "core,", ",core", "core,,alloc"] {
        assert!(
            parse_trust_verify_library_request(Some(OsStr::new(raw))).is_err(),
            "{raw:?} was accepted"
        );
    }
}

/// The names this must refuse are the whole point of the lane: compiler crates,
/// bootstrap itself, tools, and the third-party crates that the SAME `Mode::Std`
/// cargo invocation compiles alongside `core`.
#[test]
fn the_opt_in_refuses_compiler_bootstrap_tool_and_third_party_units() {
    for raw in [
        "rustc_middle",
        "rustc_driver",
        "bootstrap",
        "compiletest",
        "tidy",
        "compiler_builtins",
        "libc",
        "hashbrown",
        "memchr",
        "rustc_std_workspace_core",
        "all",
        "*",
    ] {
        let error = parse_trust_verify_library_request(Some(OsStr::new(raw)))
            .expect_err(&format!("{raw:?} was accepted as a library unit"));
        assert!(error.contains("not an in-tree `library/` unit"), "{error}");
    }
}

/// SILENT NO-OP REGRESSION. `TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY` is
/// retired but still scrubbed in six places, so setting it produced neither an
/// error nor an effect — indistinguishable from a control that worked. It is now
/// refused by name, like `TRUST_FLYWHEEL`, and the message names what to use
/// instead.
#[test]
fn the_retired_target_only_shim_marker_is_refused_not_ignored() {
    assert_eq!(retired_trust_bootstrap_shim_target_only_refusal(None), None);

    // Presence is the trigger: no value can have the effect the name promises.
    for value in ["1", "0", "", "true", "no"] {
        let message = retired_trust_bootstrap_shim_target_only_refusal(Some(OsStr::new(value)))
            .unwrap_or_else(|| panic!("{value:?} was ignored"));
        assert!(message.contains(RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV), "{message}");
        assert!(message.contains("retired"), "{message}");
        // Names the replacements, so the error is a one-line fix.
        assert!(message.contains("TRUST_BOOTSTRAP_SHIM_NO_VERIFY=1"), "{message}");
        assert!(message.contains(TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV), "{message}");
    }
}

/// Trust: the flags `rust.trust-ir-metadata` adds to a `Mode::Std` unit
/// (`compile::TRUST_STD_IR_METADATA_FLAGS`) are not verifier controls.
///
/// Both halves matter. If the matcher classified a producer flag,
/// the self-proof refusal would abort every std build with the option on; and if either
/// were read as the off-switch, bootstrap would stop appending `-Ztrust-verify=off` and
/// the unit would default to verification ON. The producer is turned on by
/// `-Ztrust-ir-lower=on` alone, beside an off-switch that is still there, once, last.
#[test]
fn the_std_producer_flags_are_not_verifier_controls() {
    use crate::core::build_steps::compile::{TRUST_STD_IR_METADATA_FLAGS, trust_std_rustflags};

    assert_eq!(TRUST_STD_IR_METADATA_FLAGS, [
        "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no", "-Ztrust-ir-lower-templates",
    ]);
    for flag in TRUST_STD_IR_METADATA_FLAGS {
        let option = flag.strip_prefix("-Z").expect("a -Z option");
        // Both `-`/`_` spellings, since the matcher normalizes them, and both token
        // shapes, since the walker accepts them.
        for option in [option.to_string(), option.replace('-', "_")] {
            assert!(!is_trust_verifier_unstable_option(&option), "{option}");
            assert!(!is_bootstrap_no_verify_option(&option), "{option}");
            for rustflags in [format!("-Z{option}"), format!("-Z {option}")] {
                assert!(trust_verifier_controls(&rustflags).is_empty(), "{rustflags}");
                assert!(!rustflags_request_bootstrap_verification(&rustflags), "{rustflags}");
                assert!(
                    bootstrap_disables_default_trust_verification(1, &rustflags),
                    "{rustflags} must not suppress bootstrap's off-switch default"
                );
            }
        }
    }

    // The matcher is still a matcher: the names it exists for are classified, so the
    // negatives above are about the producer options and not about a broken walker.
    assert!(is_trust_verifier_unstable_option("trust-verify=on"));
    assert!(is_trust_verifier_unstable_option("trust-policy=advisory"));

    // The whole list a stage >= 1 std unit gets with the option on, composed the way
    // `Cargo::from` composes it.
    let flags = trust_std_rustflags(1, true, None).unwrap();
    assert_eq!(flags.len(), 4, "{flags:?}");
    let mut composed = vec!["-Wrust_2018_idioms"];
    composed.extend(&flags);
    let (_, value) = bootstrap_rustflags_env(1, &composed);
    let tokens = value.split(['\x1f', ' ']).collect::<Vec<_>>();
    assert_eq!(
        tokens.iter().filter(|token| **token == TRUST_BOOTSTRAP_NO_VERIFY_FLAG).count(),
        1,
        "{value:?}"
    );
    assert_eq!(tokens.last(), Some(&TRUST_BOOTSTRAP_NO_VERIFY_FLAG), "{value:?}");
    for flag in &flags {
        assert_eq!(tokens.iter().filter(|token| *token == flag).count(), 1, "{flag}: {value:?}");
    }
    assert_eq!(trust_verifier_controls(&value), vec![TRUST_BOOTSTRAP_NO_VERIFY_OPTION]);
    for mode in ALL_MODES {
        assert!(
            bootstrap_verification_request_refusal(*mode, &value).is_none(),
            "{mode:?}: the producer flags read as a self-proof request: {value:?}"
        );
    }
    refuse_bootstrap_verification_request(Mode::Std, &value);

    // Stage 0 gets neither the producer flags nor the off-switch.
    let seed = trust_std_rustflags(0, true, None).unwrap();
    let (_, value) = bootstrap_rustflags_env(0, &seed);
    assert!(!value.contains("trust-ir") && !value.contains("trust-verify"), "{value:?}");
}

/// The compiler's retired-name wall, read from source. Bootstrap cannot link
/// `rustc_session`, and the point of the pin is the NAMES, which are literal
/// text in that list.
const RUSTC_SESSION_CONFIG_RS: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../compiler/rustc_session/src/config.rs"
));

fn legacy_trust_semantic_env_vars() -> Vec<String> {
    let (_, rest) = RUSTC_SESSION_CONFIG_RS
        .split_once("pub const LEGACY_TRUST_SEMANTIC_ENV_VARS: &[&str] = &[")
        .expect("LEGACY_TRUST_SEMANTIC_ENV_VARS moved or was renamed");
    let (list, _) = rest.split_once("\n];").expect("unterminated LEGACY_TRUST_SEMANTIC_ENV_VARS");
    let names = list
        .lines()
        .filter_map(|line| line.trim().strip_prefix('"'))
        .filter_map(|line| line.split_once('"').map(|(name, _)| name.to_string()))
        .collect::<Vec<_>>();
    assert!(names.len() > 50, "parsed only {} names; the parse broke", names.len());
    names
}

/// `LEGACY_TRUST_SEMANTIC_ENV_VARS` is an EXACT-NAME wall that only fires once
/// Trust IR lowering is on. That makes a collision invisible: a live control
/// whose name is on the list is inert on every bootstrap unit today and turns
/// into an `early_fatal` the first time someone enables verification — i.e.
/// exactly when the new library lane is first used, and nowhere near the change
/// that caused it.
///
/// A PREFIX rule for the retired family would be the fuller fix, but it lives in
/// the compiler and cannot be validated without a stage rebuild. This pins the
/// property that matters and can be measured here: no name bootstrap uses as a
/// LIVE control is on the retired list.
#[test]
fn no_live_bootstrap_control_collides_with_the_retired_trust_env_wall() {
    let retired = legacy_trust_semantic_env_vars();

    for live in [
        // Bootstrap -> shim IPC and the user-facing opt-in.
        "TRUST_BOOTSTRAP_SHIM_NO_VERIFY",
        "TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS",
        TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV,
        // The version-invariant transport for stage0 seeds, and the quiet-note
        // marker that rides with it.
        "TRUST_NO_VERIFY",
        "TRUST_VANILLA_ANNOUNCED",
        // Frontend authority, and the std lowerability switch.
        "TRUST_TARGO_FRONTEND",
        "TRUST_STD_ENCODE_MIR",
    ] {
        assert!(
            !retired.iter().any(|name| name == live),
            "{live} is a LIVE bootstrap control but is on the compiler's retired-name wall; \
             setting it would become an early_fatal the moment Trust IR lowering is enabled"
        );
    }

    // And the wall really does still contain retired names, so a passing test
    // is evidence about the list rather than about an empty parse.
    assert!(retired.iter().any(|name| name == "TRUST_VERIFY_POLICY"), "{retired:?}");
    assert!(retired.iter().any(|name| name == "TRUST_DISABLE_TV"), "{retired:?}");
}

/// Every `Kind` bootstrap can drive a cargo invocation with. Spelled out rather than derived so
/// a new variant fails to compile here and forces a decision about whether it writes into a std
/// output directory.
const ALL_KINDS: &[Kind] = &[
    Kind::Build,
    Kind::Check,
    Kind::Clippy,
    Kind::Fix,
    Kind::Format,
    Kind::Test,
    Kind::Miri,
    Kind::MiriSetup,
    Kind::MiriTest,
    Kind::Bench,
    Kind::Doc,
    Kind::Clean,
    Kind::Dist,
    Kind::Install,
    Kind::Run,
    Kind::Setup,
    Kind::Vendor,
];

/// Regression test for the never-cleared `build/<host>/stage2-std`.
///
/// `x.py test --stage 2` builds std units into `stage2-std`, but stage-2 std is UPLIFTED from
/// stage 1 (`Std::should_be_uplifted_from_stage_1`), so a `Mode::Std` + `Kind::Build` cargo is
/// never constructed for that directory. Gating the clear on `Kind::Build` alone therefore left
/// it never cleared, and since Trust's `CFG_VERSION` embeds the git short sha, every commit
/// changed compiler identity and stranded artifacts there. Measured 2026-08-24: the release
/// gate's log carried 16x `E0514: found crate 'core' compiled by an incompatible version of
/// rustc`, each followed by `cannot resolve a prelude import`.
#[test]
fn std_out_dir_is_cleared_for_test_not_only_build() {
    // The bug: `Kind::Test` used to answer `false` here, so `stage2-std` was never cleared.
    assert!(
        std_out_dir_needs_clear(Mode::Std, Kind::Test),
        "x.py test --stage 2 builds std units into stage2-std, which no Kind::Build cargo ever \
         targets (stage-2 std is uplifted); not clearing strands artifacts built by a rustc with \
         a different CFG_VERSION and yields E0514 on core"
    );
    assert!(std_out_dir_needs_clear(Mode::Std, Kind::Build), "upstream's original case");
}

#[test]
fn std_out_dir_clear_is_confined_to_std_and_to_building_kinds() {
    // Non-std modes are Cargo's business: it can see those dependencies via depdep info.
    for &mode in ALL_MODES {
        for &kind in ALL_KINDS {
            if mode == Mode::Std {
                continue;
            }
            assert!(
                !std_out_dir_needs_clear(mode, kind),
                "{mode:?} + {kind:?} must not clear a std out dir; only Mode::Std has the \
                 rustc-identity problem bootstrap has to solve on Cargo's behalf"
            );
        }
    }

    // Within Mode::Std, only the kinds that actually compile std units clear. Widening this
    // would delete artifacts a read-only kind is about to report on.
    for &kind in ALL_KINDS {
        let expected = matches!(kind, Kind::Build | Kind::Test);
        assert_eq!(
            std_out_dir_needs_clear(Mode::Std, kind),
            expected,
            "Mode::Std + {kind:?}: a kind that writes std units must clear, one that does not \
             must leave the directory alone"
        );
    }
}

/// Trust: `trust_verifier_controls` must parse the `\x1f`-JOINED form, not only
/// the whitespace form.
///
/// `Rustflags::arg` joins with the ASCII unit separator — it asserts no argument
/// contains one, precisely because that byte IS the separator. `split_whitespace`
/// does not treat `\x1f` as whitespace (U+001F is not in Unicode's White_Space
/// set), so the old implementation collapsed an entire `Rustflags` value into a
/// single unrecognizable token and returned an EMPTY control list no matter what
/// the flags actually said.
///
/// This survived because every existing test fed it the whitespace form, which
/// parsed correctly. The production callers feed it `Rustflags.0`, which does not.
///
/// Two things were blind as a result, and both are asserted below:
///   * the already-present check, which then added a SECOND `-Ztrust-verify=off`
///     — a repeated rustflag forks the cargo unit, because rustflags feed cargo's
///     `unit_id` but not its `c_metadata`;
///   * `rustflags_request_bootstrap_verification`, the self-proof refusal, whose
///     whole job is to notice a verifier control in bootstrap's own rustflags.
#[test]
fn trust_verifier_controls_parses_the_unit_separator_form() {
    // Exactly how `Rustflags` stores it.
    let joined = "-Zannotate-moves\u{1f}--check-cfg=cfg(bootstrap)\u{1f}-Ztrust-verify=off";
    assert_eq!(
        trust_verifier_controls(joined),
        vec![TRUST_BOOTSTRAP_NO_VERIFY_OPTION],
        "a \\x1f-joined Rustflags value must parse; returning [] here is what made the \
         already-present check add a duplicate flag and fork the std unit"
    );

    // The whitespace form (an inherited `RUSTFLAGS`) must keep working.
    let spaced = "-Zannotate-moves --check-cfg=cfg(bootstrap) -Ztrust-verify=off";
    assert_eq!(trust_verifier_controls(spaced), vec![TRUST_BOOTSTRAP_NO_VERIFY_OPTION]);

    // The consequence that mattered: with the flag already present, the default
    // must NOT add a second copy.
    assert!(
        !bootstrap_disables_default_trust_verification(1, joined),
        "the flag is already in these rustflags, so the default must not re-add it — \
         observed as `stage=1 present=1 add=true` before this fix"
    );
    // ...and with it absent, it still must.
    assert!(bootstrap_disables_default_trust_verification(
        1,
        "-Zannotate-moves\u{1f}--check-cfg=cfg(bootstrap)"
    ));

    // The self-proof refusal must see a REAL verifier request in the joined form.
    assert!(
        rustflags_request_bootstrap_verification("-Zannotate-moves\u{1f}-Ztrust-verify=on"),
        "the refusal exists to notice exactly this, and could not"
    );
    assert!(!rustflags_request_bootstrap_verification(joined), "the off-switch is not a request");
}

/// The value every Cargo command bootstrap composes gives `CARGO_CACHE_RUSTC_INFO`, read off
/// the actual composed commands (`None` when one leaves it unset). Each such command names
/// bootstrap's own `rustc` shim as RUSTC, which is why the value matters (TG16).
fn composed_cargo_rustc_info_cache_settings() -> Vec<(String, Mode, Option<std::ffi::OsString>)> {
    use crate::core::build_steps::tool::SourceType;
    use crate::core::builder::Builder;
    use crate::core::session::Session;
    use crate::utils::exec::BootstrapCommand;
    use crate::utils::tests::TestCtx;

    let mut settings = Vec::new();
    for kind in ["build", "check", "test"] {
        let context = TestCtx::new();
        let build = Session::new(context.config(kind).stage(1).create_config());
        let builder = Builder::new(&build);
        let host = builder.config.host_target;
        let compiler = builder.compiler(0, host);
        let shim = builder.bootstrap_out.join("rustc");
        for &mode in ALL_MODES {
            let cargo = builder.cargo(compiler, mode, SourceType::InTree, host, builder.kind);
            let mut command = BootstrapCommand::from(cargo);
            command.mark_as_executed();
            let env = |name: &str| {
                command.get_envs().find(|(key, _)| *key == name).and_then(|(_, value)| value)
            };
            assert_eq!(
                env("RUSTC"),
                Some(shim.as_os_str()),
                "{kind} {mode:?}: RUSTC is bootstrap's shim; the cache key reads it"
            );
            settings.push((
                kind.to_string(),
                mode,
                env("CARGO_CACHE_RUSTC_INFO").map(|value| value.to_owned()),
            ));
        }
    }
    settings
}

/// Trust (TG16): Cargo keys its persisted compiler queries (`<build-dir>/.rustc_info.json`:
/// `-vV` and the target-info probes, failed answers included) on RUSTC's path, size and times.
/// Bootstrap's RUSTC is its fixed shim, so a driver rebuilt behind it was answered with the
/// previous driver's `-vV`, the units it built were kept, and std's consumers failed E0514.
/// Every composed command, in every mode and building kind, turns the cache off.
#[test]
fn bootstrap_cargo_never_persists_compiler_queries_behind_its_shim() {
    let settings = composed_cargo_rustc_info_cache_settings();
    assert_eq!(settings.len(), 3 * ALL_MODES.len());
    for (kind, mode, value) in settings {
        assert_eq!(
            value.as_deref(),
            Some(OsStr::new("0")),
            "{kind} {mode:?}: a Cargo whose RUSTC is the shim must not persist `-vV`"
        );
    }
}

/// Trust (TG16): the behaviour behind the wiring above, measured on the Cargo this test runs
/// under. A fixed shim stands in for `bin/rustc.rs`; two driver generations differ only in
/// their `-vV`. With Cargo's persisted cache on (the old bootstrap), the second generation is
/// answered from `.rustc_info.json` and the unit the first one built is kept: the E0514
/// precondition. With the setting bootstrap's composed commands carry, the second generation
/// rebuilds, a repeat is still reused, and switching back rebuilds again.
#[cfg(unix)]
#[test]
fn a_driver_rebuilt_behind_the_fixed_shim_is_seen_by_bootstraps_cargo() {
    use std::fs;
    use std::os::unix::fs::PermissionsExt;
    use std::path::Path;
    use std::process::Command;

    use crate::utils::tests::TestCtx;

    let composed = composed_cargo_rustc_info_cache_settings()
        .into_iter()
        .find(|(kind, mode, _)| kind == "build" && *mode == Mode::Std)
        .and_then(|(_, _, value)| value);

    // The compiler the generations run: the one this test run's bootstrap configs resolve
    // (`x test bootstrap`'s RUSTC, or the direct-run stage0), as the other real-Cargo tests use.
    let actual = crate::core::session::Session::new(TestCtx::new().config("check").create_config())
        .initial_rustc
        .clone();

    let directory = tempfile::TempDir::new().unwrap();
    let crate_dir = directory.path().join("driver-generation");
    fs::create_dir_all(crate_dir.join("src")).unwrap();
    fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\n\
         name = \"driver-generation\"\n\
         version = \"0.0.0\"\n\
         edition = \"2024\"\n\
         [workspace]\n",
    )
    .unwrap();
    fs::write(crate_dir.join("src/lib.rs"), "pub fn generation() {}\n").unwrap();

    let executable = |path: &Path, body: String| {
        fs::write(path, body).unwrap();
        let mut permissions = fs::metadata(path).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions).unwrap();
    };
    // Bootstrap's shim: one path, one set of bytes and times for the whole test.
    let shim = directory.path().join("rustc-shim");
    executable(&shim, "#!/bin/sh\nexec \"$TRUST_TEST_RUSTC_REAL\" \"$@\"\n".to_string());
    let generation = |name: &str| {
        let driver = directory.path().join(format!("driver-{name}"));
        executable(
            &driver,
            format!(
                "#!/bin/sh\n\
                 if [ \"$1\" = -vV ]; then\n\
                 \"$TRUST_TEST_RUSTC_ACTUAL\" -vV || exit $?\n\
                 printf '%s\\n' 'trust-test-driver-generation: {name}'\n\
                 exit 0\n\
                 fi\n\
                 printf '%s\\n' \"$*\" >> \"$TRUST_RUSTC_INVOCATION_LOG\"\n\
                 exec \"$TRUST_TEST_RUSTC_ACTUAL\" \"$@\"\n"
            ),
        );
        driver
    };
    let (first, second) = (generation("a"), generation("b"));

    let target_dir = directory.path().join("target");
    let invocation_log = directory.path().join("rustc-invocations");
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "targo".into());
    let explicit_lane =
        Command::new(&cargo).args(["--unverified", "--version"]).output().unwrap().status.success();
    let run = |driver: &Path, cache_rustc_info: Option<&OsStr>| {
        let mut command = Command::new(&cargo);
        if explicit_lane {
            command.arg("--unverified");
        }
        command
            .current_dir(&crate_dir)
            .args(["check", "--offline", "--quiet", "--target-dir"])
            .arg(&target_dir)
            .env("RUSTC", &shim)
            .env("TRUST_TEST_RUSTC_REAL", driver)
            .env("TRUST_TEST_RUSTC_ACTUAL", &actual)
            .env("TRUST_RUSTC_INVOCATION_LOG", &invocation_log)
            .env("CARGO_INCREMENTAL", "0");
        // Nothing from an enclosing bootstrap Cargo may steer this one: its wrapper, its
        // build directory, or its own cache setting.
        for inherited in [
            "RUSTC_WRAPPER",
            "RUSTC_WORKSPACE_WRAPPER",
            "RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "CARGO_TARGET_DIR",
            "CARGO_BUILD_TARGET_DIR",
            "CARGO_BUILD_BUILD_DIR",
            "CARGO_CACHE_RUSTC_INFO",
        ] {
            command.env_remove(inherited);
        }
        if let Some(value) = cache_rustc_info {
            command.env("CARGO_CACHE_RUSTC_INFO", value);
        }
        // Native entry already captured the enclosing scheduler. A raw
        // Command would retain its advertisement but close its actual GNU
        // descriptors at exec, so the real compiler must refuse that launch.
        // Borrow the SAME original transport through this closed fixture's
        // synchronous Cargo/compiler work; never create replacement credit.
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        let output = {
            use std::io::{Read as _, Seek as _};
            use std::process::{Output, Stdio};
            let mut stdout = tempfile::tempfile().unwrap();
            let mut stderr = tempfile::tempfile().unwrap();
            command
                .stdin(Stdio::null())
                .stdout(stdout.try_clone().unwrap())
                .stderr(stderr.try_clone().unwrap());
            let status = crate::utils::metadata_scheduler::stream_original(&mut command)
                .expect("original captured scheduler for the compiler-generation fixture")
                .wait()
                .expect("original Cargo child terminal");
            stdout.rewind().unwrap();
            stderr.rewind().unwrap();
            let mut out = Vec::new();
            let mut err = Vec::new();
            stdout.read_to_end(&mut out).unwrap();
            stderr.read_to_end(&mut err).unwrap();
            Output { status, stdout: out, stderr: err }
        };
        // The native transport owner exists on macOS/Linux. Other Unix
        // targets retain this fixture's existing standalone Cargo execution.
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "nested cargo check failed\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    };
    let compiled = || {
        fs::read_to_string(&invocation_log)
            .unwrap_or_default()
            .lines()
            .filter(|line| line.split_whitespace().any(|arg| arg.ends_with("src/lib.rs")))
            .count()
    };
    let persisted = || fs::read_to_string(target_dir.join(".rustc_info.json")).ok();

    // The old bootstrap: Cargo's persisted cache on.
    run(&first, None);
    let built = compiled();
    assert_eq!(built, 1, "the first generation compiles the library once");
    assert!(
        persisted().is_some_and(|json| json.contains("generation: a")),
        "the control needs Cargo to persist the first generation's `-vV`: {:?}",
        persisted()
    );
    run(&second, None);
    assert_eq!(
        compiled(),
        built,
        "negative control: behind an unchanged shim the persisted `-vV` hides the new driver, \
         so the first generation's unit is kept (the E0514 precondition)"
    );
    assert!(persisted().is_some_and(|json| !json.contains("generation: b")));

    // Bootstrap now: the value its composed commands carry.
    let composed = composed.as_deref();
    run(&second, composed);
    assert_eq!(
        compiled(),
        built + 1,
        "with bootstrap's setting ({composed:?}) the new driver's `-vV` must be asked for and \
         the unit rebuilt"
    );
    run(&second, composed);
    assert_eq!(compiled(), built + 1, "an unchanged driver still reuses the unit");
    run(&first, composed);
    assert_eq!(compiled(), built + 2, "switching back is a change too");
}

#[test]
fn a_trust_stage0_of_1_101_or_later_defaults_to_polonius() {
    // PERF-SEP26-DEFAULTS: the trust channel takes nightly's Polonius default; a stock
    // beta does not, and a compiler before 1.101 has no `-Zpolonius=off` to pass.
    let trust = "rustc 1.101.0-dev (82bb867ed 2026-11-07) (trustc 0.13.0+g82bb867ed)\nbinary: trustc\ncommit-hash: 82bb867eddb94599f68194f701c766f2b6f5a02f\nhost: aarch64-apple-darwin\nrelease: 1.101.0-dev\ntrust: 0.13.0+g82bb867ed\n";
    let beta = "rustc 1.101.0-beta.1 (bbcdfd90a 2026-11-10)\nbinary: rustc\ncommit-hash: bbcdfd90a3f81ca2a5f6d69b943a6ff0d8582102\nhost: aarch64-apple-darwin\nrelease: 1.101.0-beta.1\n";
    assert!(compiler_defaults_to_polonius(trust));
    assert!(compiler_defaults_to_polonius(&trust.replace("1.101.0-dev", "1.102.0-dev")));
    assert!(compiler_defaults_to_polonius(&trust.replace("1.101.0-dev", "2.0.0")));
    assert!(!compiler_defaults_to_polonius(beta));
    assert!(!compiler_defaults_to_polonius(&trust.replace("1.101.0-dev", "1.100.0-dev")));
    assert!(!compiler_defaults_to_polonius(&trust.replace("(trustc 0.13.0+g82bb867ed)", "")));
    assert!(!compiler_defaults_to_polonius(&trust.replace("release: 1.101.0-dev\n", "")));
    assert!(!compiler_defaults_to_polonius(""));
}

// Trust (BOOTSTRAP-JOBSERVER-PROBE-1): what each Cargo command gets of the GNU
// jobserver. An inherited FIFO is forwarded, a numeric pipe is stripped, and a
// seed Cargo that inherits no FIFO gets its builder's own.
#[cfg(unix)]
mod makeflags {
    use std::ffi::{OsStr, OsString};
    use std::os::unix::fs::{FileTypeExt as _, PermissionsExt as _};
    use std::path::{Path, PathBuf};
    use std::process::Command;

    use super::super::{MakeflagsPolicy, makeflags_policy};
    use crate::core::build_steps::tool::SourceType;
    use crate::core::builder::{Builder, Cargo, CargoInput, Kind};
    use crate::core::compiler::Compiler;
    use crate::core::session::{Mode, Session};
    use crate::utils::exec::{BootstrapCommand, command};
    use crate::utils::seed_jobserver::{DIRECTORY_PREFIX, FIFO_NAME, SeedJobserver, is_live};
    use crate::utils::tests::TestCtx;

    const NUMERIC: &str = "-j --jobserver-fds=3,4 --jobserver-auth=3,4";
    const FIFO: &str = "-j6 --jobserver-auth=fifo:/inherited/jobserver.fifo";
    const OTHER_INPUTS: [CargoInput; 3] = [
        CargoInput::CurrentBuildTool,
        CargoInput::CurrentBuildToolSnapshotStd,
        CargoInput::CurrentNativeUnitTests,
    ];
    // Every variable through which a Cargo finds a GNU jobserver.
    const JOBSERVER_ENV: [&str; 4] =
        ["MAKEFLAGS", "MFLAGS", "CARGO_MAKEFLAGS", jobserver_utils::DESCENDANT_HANDOFF_ENV];

    // The value this command sets for `key`: None when it leaves the inherited
    // one alone, Some(None) when it removes it.
    fn env<'a>(command: &'a BootstrapCommand, key: &str) -> Option<Option<&'a OsStr>> {
        command.get_envs().find(|(name, _)| *name == OsStr::new(key)).map(|(_, value)| value)
    }

    fn apply(
        builder: &Builder<'_>,
        inherited: Option<&str>,
        input: CargoInput,
    ) -> BootstrapCommand {
        let mut cargo = command("cargo");
        cargo.env("MFLAGS", "-j9").env("CARGO_MAKEFLAGS", NUMERIC);
        cargo.env(jobserver_utils::DESCENDANT_HANDOFF_ENV, "ambient");
        builder.apply_makeflags_policy(&mut cargo, inherited.map(OsStr::new), input);
        cargo.mark_as_executed();
        cargo
    }

    // The FIFO path a seed command's MAKEFLAGS names, checked against Bootstrap's spelling.
    fn seed_fifo(builder: &Builder<'_>, cargo: &BootstrapCommand) -> PathBuf {
        let flags = env(cargo, "MAKEFLAGS").flatten().expect("seed Cargo got no MAKEFLAGS");
        let flags = flags.to_str().unwrap();
        let prefix = format!("-j{} --jobserver-auth=fifo:", builder.jobs());
        let path = PathBuf::from(flags.strip_prefix(&prefix).unwrap_or_else(|| panic!("{flags}")));
        assert!(
            path.starts_with(builder.tempdir()),
            "{} not under the build's tmp",
            path.display()
        );
        path
    }

    fn tokens(path: &Path) -> usize {
        let client = jobserver_utils::Jobserver::from_fifo(path).unwrap();
        client.client().available().unwrap()
    }

    fn assert_live_fifo(path: &Path, tokens_left: u32) {
        let fifo = std::fs::symlink_metadata(path).unwrap();
        assert!(fifo.file_type().is_fifo());
        assert_eq!(fifo.permissions().mode() & 0o7777, 0o600);
        assert_eq!(tokens(path), tokens_left as usize);
    }

    fn session() -> (TestCtx, Session) {
        let context = TestCtx::new();
        let config = context
            .config("build")
            .stage(1)
            .args(&["--set", "rust.omit-git-hash=true"])
            .create_config();
        let build = Session::new(config);
        (context, build)
    }

    fn builder_test(test: impl FnOnce(&Builder<'_>)) {
        let (_context, build) = session();
        test(&Builder::new(&build));
    }

    // The seed Cargo of a seed tool and a current-tool Cargo, as Bootstrap composes them.
    fn composed(builder: &Builder<'_>) -> (BootstrapCommand, BootstrapCommand) {
        let host = builder.host_target;
        let compiler = Compiler::new(0, host);
        let mut seed = builder.bare_cargo(compiler, Mode::ToolBootstrap, host, Kind::Build);
        seed.mark_as_executed();
        let mut current =
            Cargo::new(builder, compiler, Mode::Std, SourceType::InTree, host, Kind::Build)
                .into_cmd();
        current.mark_as_executed();
        (seed, current)
    }

    #[test]
    fn only_the_seed_cargo_gets_bootstraps_own_fifo() {
        for inherited in [None, Some("-j8"), Some("--silent"), Some(NUMERIC)] {
            let flags = inherited.map(OsStr::new);
            assert_eq!(makeflags_policy(flags, CargoInput::Seed, false), MakeflagsPolicy::SeedFifo);
            // Under an enclosing owner's dispatch every command is handed that
            // owner's transport when it starts; Bootstrap's FIFO would go unused.
            assert_eq!(makeflags_policy(flags, CargoInput::Seed, true), MakeflagsPolicy::Strip);
            for input in OTHER_INPUTS {
                for enclosing in [false, true] {
                    assert_eq!(
                        makeflags_policy(flags, input, enclosing),
                        MakeflagsPolicy::Strip,
                        "{input:?}"
                    );
                }
            }
        }
        for input in [CargoInput::Seed].into_iter().chain(OTHER_INPUTS) {
            for enclosing in [false, true] {
                let flags = Some(OsStr::new(FIFO));
                assert_eq!(
                    makeflags_policy(flags, input, enclosing),
                    MakeflagsPolicy::ForwardInherited
                );
            }
        }
    }

    #[test]
    fn a_seed_cargo_without_an_inherited_fifo_gets_a_live_private_one() {
        builder_test(|builder| {
            for inherited in [None, Some(NUMERIC)] {
                let cargo = apply(builder, inherited, CargoInput::Seed);
                let path = seed_fifo(builder, &cargo);
                assert_live_fifo(&path, builder.jobs() - 1);
                // Every other GNU advertisement is replaced: the jobserver
                // crate reads CARGO_MAKEFLAGS first, and an ambient handoff
                // names another pool.
                for key in ["MFLAGS", "CARGO_MAKEFLAGS", jobserver_utils::DESCENDANT_HANDOFF_ENV] {
                    assert_eq!(env(&cargo, key), Some(None), "{key} {inherited:?}");
                }
                // One server per builder: the next seed command names the same FIFO.
                let again = apply(builder, inherited, CargoInput::Seed);
                assert_eq!(seed_fifo(builder, &again), path);
            }
        });
    }

    #[test]
    fn an_inherited_fifo_is_forwarded_unchanged() {
        builder_test(|builder| {
            for input in [CargoInput::Seed].into_iter().chain(OTHER_INPUTS) {
                let cargo = apply(builder, Some(FIFO), input);
                // Nothing set or removed: the command inherits Bootstrap's own.
                assert_eq!(env(&cargo, "MAKEFLAGS"), None, "{input:?}");
                assert_eq!(env(&cargo, "MFLAGS").flatten(), Some(OsStr::new("-j9")));
            }
            assert!(builder.seed_jobserver.get().is_none(), "a forwarded FIFO made a server");
        });
    }

    #[test]
    fn a_non_fifo_makeflags_is_still_stripped_for_the_current_tool() {
        builder_test(|builder| {
            for inherited in [None, Some("-j8"), Some(NUMERIC)] {
                for input in OTHER_INPUTS {
                    let cargo = apply(builder, inherited, input);
                    assert_eq!(env(&cargo, "MAKEFLAGS"), Some(None), "{input:?} {inherited:?}");
                    assert_eq!(env(&cargo, "MFLAGS"), Some(None), "{input:?} {inherited:?}");
                }
            }
            assert!(builder.seed_jobserver.get().is_none(), "a current-tool Cargo made a server");
        });
    }

    // The server lives as long as the builder that composed the seed commands,
    // a dry-run one included, and goes with it: a process that builds many
    // sessions (this test binary) holds one per live builder, not one per build
    // directory it ever saw.
    #[test]
    fn a_builder_removes_its_seed_jobserver_when_it_is_dropped() {
        let (_context, build) = session();
        assert!(build.config.dry_run());
        // A server a killed Bootstrap left: only a build that holds the build
        // lock removes it, and a dry run does not.
        let stale = build.tempdir().join(format!("{DIRECTORY_PREFIX}stale"));
        std::fs::create_dir(&stale).unwrap();
        let (directory, path) = {
            let builder = Builder::new(&build);
            let path = seed_fifo(&builder, &apply(&builder, None, CargoInput::Seed));
            let server = builder.seed_jobserver.get().expect("no server made");
            assert_eq!(server.path(), path);
            assert!(is_live(server.directory()));
            (server.directory().to_owned(), path)
        };
        assert!(!path.exists(), "{} outlived its builder", path.display());
        assert!(!directory.exists());
        assert!(!is_live(&directory), "a dropped builder's server is still registered");
        assert!(stale.exists(), "a dry run removed another server's directory");
        // The next builder of the same session makes its own.
        let builder = Builder::new(&build);
        let again = seed_fifo(&builder, &apply(&builder, None, CargoInput::Seed));
        assert_ne!(again, path);
        assert_live_fifo(&again, builder.jobs() - 1);
        assert!(again.ends_with(FIFO_NAME));
    }

    // The composed seed and current-tool commands follow the policy for the
    // MAKEFLAGS this process itself inherited. Each case runs this test alone
    // in a child given that MAKEFLAGS, since it is read from the environment.
    #[test]
    fn composed_commands_follow_the_policy_for_bootstraps_own_makeflags() {
        const ROLE: &str = "TRUST_BOOTSTRAP_COMPOSED_MAKEFLAGS";
        const NAME: &str = "core::builder::cargo::tests::makeflags::\
                            composed_commands_follow_the_policy_for_bootstraps_own_makeflags";
        if let Some(role) = std::env::var_os(ROLE) {
            builder_test(|builder| {
                let (seed, current) = composed(builder);
                match role.to_str().unwrap() {
                    "fifo" => {
                        for (name, command) in [("seed", &seed), ("current", &current)] {
                            for key in JOBSERVER_ENV {
                                assert_eq!(env(command, key), None, "{name} {key}");
                            }
                        }
                        assert!(builder.seed_jobserver.get().is_none());
                    }
                    "plain" => {
                        assert_live_fifo(&seed_fifo(builder, &seed), builder.jobs() - 1);
                        assert_eq!(env(&current, "MAKEFLAGS"), Some(None));
                        assert_eq!(env(&current, "MFLAGS"), Some(None));
                    }
                    other => panic!("unknown role {other}"),
                }
            });
            println!("composed-makeflags-checked={}", role.display());
            return;
        }
        // The pool a GNU make 4.4 running x.py hands it.
        let pool_directory = tempfile::tempdir().unwrap();
        let pool = SeedJobserver::create(pool_directory.path(), 3).unwrap();
        for (role, makeflags) in [("fifo", pool.makeflags()), ("plain", "-j8".to_owned())] {
            let output = crate::test_entry::synthetic_observer(Command::new(
                std::env::current_exe().unwrap(),
            ))
            .args(["--exact", NAME, "--nocapture"])
            .env(ROLE, role)
            .env("MAKEFLAGS", &makeflags)
            .output()
            .unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(output.status.success(), "{role}: {output:?}");
            assert!(stdout.contains(&format!("composed-makeflags-checked={role}")), "{stdout}");
        }
        assert_eq!(tokens(pool.path()), 2, "the inherited pool lost or gained a token");
    }

    // rustix 1.1.6 build.rs `can_compile`, unchanged in what reaches the shim
    // (RUSTC_WRAPPER then RUSTC as its first argument, --target, stdin source).
    // Two deviations, both to report rather than race: the probe's stderr goes
    // to a file instead of /dev/null, and a failed write to the refused probe's
    // stdin is recorded instead of unwrapped (rustix panics there, or answers
    // "no" when the shim exits after the write).
    const PROBE_BUILD_SCRIPT: &str = r#"use std::env::var;
use std::io::Write;
use std::process::{Command, Stdio};

fn main() {
    println!("cargo:rustc-check-cfg=cfg(seed_probe)");
    let out = std::path::PathBuf::from(var("OUT_DIR").unwrap());
    let rustc = var("RUSTC").unwrap();
    let wrapper = var("RUSTC_WRAPPER").ok().filter(|w| !w.is_empty());
    let mut cmd = match wrapper {
        Some(wrapper) => {
            let mut cmd = Command::new(wrapper);
            cmd.arg(rustc);
            cmd
        }
        None => Command::new(rustc),
    };
    let stderr = out.join("probe.stderr");
    cmd.arg("--crate-type=rlib")
        .arg("--emit=metadata")
        .arg("--target")
        .arg(var("TARGET").unwrap())
        .arg("-o")
        .arg(out.join("rustix_test_can_compile"))
        .stdout(Stdio::null());
    if let Ok(rustflags) = var("CARGO_ENCODED_RUSTFLAGS") {
        if !rustflags.is_empty() {
            for arg in rustflags.split('\x1f') {
                cmd.arg(arg);
            }
        }
    }
    let mut child = cmd
        .arg("-")
        .stdin(Stdio::piped())
        .stderr(std::fs::File::create(&stderr).unwrap())
        .spawn()
        .unwrap();
    let wrote = writeln!(child.stdin.take().unwrap(), "pub fn probe() {{}}");
    let status = child.wait().unwrap();
    if wrote.is_err() || !status.success() {
        let stderr = std::fs::read_to_string(&stderr).unwrap_or_default();
        panic!("PROBE-LOST write={wrote:?} status={status:?}\n{stderr}");
    }
    println!("cargo:rustc-cfg=seed_probe");
    println!("cargo:warning=PROBE-OK");
}
"#;

    struct ProbeInputs {
        cargo: PathBuf,
        rustc: PathBuf,
        shim: PathBuf,
        host: String,
        sysroot: PathBuf,
    }

    impl ProbeInputs {
        fn from_env() -> Self {
            let input = |name: &str| {
                let path = PathBuf::from(std::env::var_os(name).unwrap_or_else(|| {
                    panic!("{name} must name the input; see this test's #[ignore] reason")
                }));
                assert!(path.is_absolute() && path.is_file(), "{name}: {}", path.display());
                path
            };
            let cargo = input("BOOTSTRAP_SEED_PROBE_CARGO");
            let shim = input("BOOTSTRAP_SEED_PROBE_SHIM");
            let rustc = cargo.with_file_name("rustc");
            assert!(rustc.is_file(), "no rustc beside the seed Cargo at {}", rustc.display());
            let ask = |args: &[&str]| {
                let output = Command::new(&rustc).args(args).output().unwrap();
                assert!(output.status.success(), "{output:?}");
                String::from_utf8(output.stdout).unwrap()
            };
            let host = ask(&["-vV"])
                .lines()
                .find_map(|line| line.strip_prefix("host: "))
                .unwrap()
                .to_owned();
            let sysroot = PathBuf::from(ask(&["--print", "sysroot"]).trim());
            ProbeInputs { cargo, rustc, shim, host, sysroot }
        }

        // The seed Cargo as Bootstrap runs it for a seed tool: RUSTC and
        // RUSTC_WRAPPER are the shim, in an environment holding nothing else
        // but the GNU jobserver variables given.
        fn build(
            &self,
            root: &Path,
            label: &str,
            jobs: u32,
            jobserver: &[(&str, Option<OsString>)],
        ) -> (bool, String) {
            use std::os::unix::process::CommandExt as _;
            let home = root.join(label);
            std::fs::create_dir(&home).unwrap();
            let log = home.join("output.log");
            let mut command = Command::new(&self.cargo);
            command
                .env_clear()
                .env("PATH", "/usr/bin:/bin")
                .env("HOME", &home)
                .env("CARGO_HOME", home.join("cargo-home"))
                .env("CARGO_TARGET_DIR", home.join("target"))
                .env("RUSTC", &self.shim)
                .env("RUSTC_WRAPPER", &self.shim)
                .env("RUSTC_REAL", &self.rustc)
                .env("RUSTC_SNAPSHOT", &self.rustc)
                .env("RUSTC_SYSROOT", &self.sysroot)
                .env("RUSTC_LIBDIR", self.sysroot.join("lib"))
                .env("RUSTC_SNAPSHOT_LIBDIR", self.sysroot.join("lib"))
                .env("RUSTC_STAGE", "0")
                .env("CFG_COMPILER_BUILD_TRIPLE", &self.host)
                .env("TRUST_BOOTSTRAP_SHIM_NO_VERIFY", "1")
                .env("RUSTC_BOOTSTRAP", "1");
            for (key, value) in jobserver {
                if let Some(value) = value {
                    command.env(key, value);
                }
            }
            let jobs = jobs.to_string();
            let manifest = root.join("crate").join("Cargo.toml");
            // One description for both streams, so neither overwrites the other.
            let output = std::fs::File::create(&log).unwrap();
            command
                .args(["build", "--offline", "-j", &jobs, "--target", &self.host])
                .arg("--manifest-path")
                .arg(manifest)
                .stdin(std::process::Stdio::null())
                .stdout(output.try_clone().unwrap())
                .stderr(output)
                .process_group(0);
            let mut child = command.spawn().unwrap();
            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(300);
            let status = loop {
                if let Some(status) = child.try_wait().unwrap() {
                    break status;
                }
                if std::time::Instant::now() >= deadline {
                    // SAFETY: only this test's private process group is killed.
                    unsafe { libc::kill(-(child.id() as i32), libc::SIGKILL) };
                    let _ = child.wait();
                    panic!("{label}: the seed Cargo did not finish in 300 s");
                }
                std::thread::sleep(std::time::Duration::from_millis(50));
            };
            let output = std::fs::read_to_string(&log).unwrap();
            println!(
                "{label}: exit {status}, PROBE-OK {}, PROBE-LOST {}",
                output.contains("PROBE-OK"),
                output.contains("PROBE-LOST")
            );
            (status.success(), output)
        }
    }

    // BOOTSTRAP-JOBSERVER-PROBE-1's regression at probe scale: a Cargo without
    // CARGO_JOBSERVER_HANDOFF, the real shim, and a one-file crate whose build
    // script is rustix's `can_compile` probe. Given the GNU variables Bootstrap's
    // own seed command carries, the probe compiles and every token comes back.
    // The control is the same Cargo with those variables removed, as Bootstrap
    // did before (it stripped MAKEFLAGS): the shim refuses the probe.
    #[test]
    #[ignore = "explicit inputs: BOOTSTRAP_SEED_PROBE_CARGO, a Cargo without CARGO_JOBSERVER_HANDOFF \
                with its rustc beside it (the 29ebb403de stage2 bin/cargo), and \
                BOOTSTRAP_SEED_PROBE_SHIM, the rustc shim built from this tree \
                (`targo --unverified build --offline --locked --bin rustc` in src/bootstrap)"]
    fn a_handoff_less_seed_cargos_probe_compiles_through_the_shim_with_bootstraps_jobserver() {
        let inputs = ProbeInputs::from_env();
        let root = tempfile::tempdir().unwrap();
        let fixture = root.path().join("crate");
        std::fs::create_dir_all(fixture.join("src")).unwrap();
        std::fs::write(
            fixture.join("Cargo.toml"),
            "[package]\nname = \"seed-probe-fixture\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\
             build = \"build.rs\"\n\n[workspace]\n",
        )
        .unwrap();
        std::fs::write(fixture.join("build.rs"), PROBE_BUILD_SCRIPT).unwrap();
        std::fs::write(
            fixture.join("src/lib.rs"),
            "#[cfg(not(seed_probe))]\ncompile_error!(\"the build script's probe cfg was lost\");\n\
             pub fn fixture() {}\n",
        )
        .unwrap();

        let inherited = std::env::var_os("MAKEFLAGS");
        assert_ne!(
            makeflags_policy(inherited.as_deref(), CargoInput::Seed, false),
            MakeflagsPolicy::ForwardInherited,
            "this process inherits a FIFO MAKEFLAGS, which Bootstrap forwards; run without one \
             to measure Bootstrap's own"
        );
        builder_test(|builder| {
            let (seed, _) = composed(builder);
            let jobs = builder.jobs();
            // What Bootstrap's seed command does to each GNU variable: set,
            // removed, or left to this process's own value.
            let jobserver: Vec<(&str, Option<OsString>)> = JOBSERVER_ENV
                .into_iter()
                .map(|key| {
                    let value = match env(&seed, key) {
                        Some(value) => value.map(OsStr::to_owned),
                        None => std::env::var_os(key),
                    };
                    (key, value)
                })
                .collect();

            let (refused, output) = inputs.build(root.path(), "stripped", jobs, &[]);
            assert!(
                !refused,
                "the probe passed without a jobserver: this Cargo hands build scripts a \
                 recoverable one, and the regression needs one without CARGO_JOBSERVER_HANDOFF\n{}",
                tail(&output)
            );
            assert!(output.contains("PROBE-LOST"), "{}", tail(&output));
            assert!(
                output.contains("cannot inherit bootstrap jobserver: invalid advertised jobserver"),
                "{}",
                tail(&output)
            );

            let (built, output) = inputs.build(root.path(), "bootstrap", jobs, &jobserver);
            assert!(built, "{}", tail(&output));
            assert!(output.contains("PROBE-OK"), "{}", tail(&output));
            assert!(!output.contains("PROBE-LOST"), "{}", tail(&output));
            // It was Bootstrap's own FIFO, and every token came back.
            assert_live_fifo(&seed_fifo(builder, &seed), jobs - 1);
            println!(
                "seed probe: stripped refused, Bootstrap's FIFO compiled, {} tokens back",
                jobs - 1
            );
        });
    }

    fn tail(output: &str) -> &str {
        let mut start = output.len().saturating_sub(4000);
        while !output.is_char_boundary(start) {
            start += 1;
        }
        &output[start..]
    }
}
