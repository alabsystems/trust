//! Trust: the new selection must retain native graph and configuration boundaries.
use super::*;
use crate::core::build_steps::compile;
use crate::core::builder::Step;
use crate::core::session::Session;
use crate::utils::tests::TestCtx;

#[test]
fn immutable_install_selection_is_explicit_and_bounded() {
    let context = TestCtx::new();
    let base = || {
        context.config("install").stage(2).arg(SELECTION).args(&[
            "--set",
            "install.prefix=/immutable/current-trust",
            "--set",
            "build.extended=true",
        ])
    };
    let config = base().create_config();
    assert!(is_wp_installation(config.cmd.kind(), &config.paths));
    assert!(validate_with_environment(&config, &Default::default()).is_ok());
    assert!(!is_wp_installation(Kind::Build, &config.paths));
    assert!(!is_wp_installation(Kind::Install, &["trustc".into()]));
    for extra in
        ["trustc", "targo-trust", "--keep-stage=1", "--skip=compiler", "--include-default-paths"]
    {
        let config = base().arg(extra).create_config();
        assert!(validate_with_environment(&config, &Default::default()).is_err(), "{extra}");
    }
    for setting in [
        "install.prefix=relative",
        "install.prefix=/tmp/build/final",
        "install.prefix=/tmp/stage2/final",
        "install.prefix=/tmp/rustc-private-sysroots/final",
        "install.bindir=other",
        "install.libdir=other",
        "build.extended=false",
    ] {
        // Each case reaches the installer validator through a valid parse.
        // Duplicate --set entries are a separate parser refusal.
        let mut arguments = context.config("install").stage(2).arg(SELECTION);
        if !setting.starts_with("install.prefix=") {
            arguments = arguments.args(&["--set", "install.prefix=/immutable/current-trust"]);
        }
        if !setting.starts_with("build.extended=") {
            arguments = arguments.args(&["--set", "build.extended=true"]);
        }
        let config = arguments.args(&["--set", setting]).create_config();
        assert!(validate_with_environment(&config, &Default::default()).is_err(), "{setting}");
    }
    assert!(!config.native_repo_config_inputs.is_empty(), "actual parsed config bytes are bound");
}

#[test]
fn immutable_install_accepts_default_and_both_documentation_tool_selectors() {
    let context = TestCtx::new();
    let base = || {
        context.config("install").stage(2).arg(SELECTION).args(&[
            "--set",
            "install.prefix=/immutable/current-trust",
            "--set",
            "build.extended=true",
        ])
    };
    let default = base().create_config();
    assert!(default.tools.is_none(), "the absent allowlist keeps all default tools");
    assert!(validate_with_environment(&default, &Default::default()).is_ok());
    for selector in ["trustdoc", "rustdoc"] {
        let config = base()
            .args(&[
                "--set",
                &format!(
                    "build.tools=[\"targo\",\"{selector}\",\"ty\",\"clean\",\"trustfmt\",\"tippy\"]"
                ),
            ])
            .create_config();
        assert!(config.tools.as_ref().unwrap().contains(selector));
        assert!(!config.tools.as_ref().unwrap().contains("ay"), "AY needs no explicit selector");
        assert!(validate_with_environment(&config, &Default::default()).is_ok(), "{selector}");
    }
}

#[test]
fn immutable_install_refuses_tool_allowlists_without_documentation() {
    let context = TestCtx::new();
    for tools in
        ["[]", "[\"targo\",\"clean\",\"ty\"]", "[\"targo\",\"trustdoc-other\",\"clean\",\"ty\"]"]
    {
        let config = context
            .config("install")
            .stage(2)
            .arg(SELECTION)
            .args(&[
                "--set",
                "install.prefix=/immutable/current-trust",
                "--set",
                "build.extended=true",
                "--set",
                &format!("build.tools={tools}"),
            ])
            .create_config();
        let error = validate_with_environment(&config, &Default::default()).unwrap_err();
        assert!(error.contains("trustdoc"), "{tools}: {error}");
        assert!(error.contains("build.tools"), "{tools}: {error}");
    }
}

#[test]
fn immutable_install_refuses_each_omitted_required_backend() {
    let context = TestCtx::new();
    for (tools, missing) in [
        ("[\"targo\",\"trustdoc\",\"ay\",\"clean\"]", "ty"),
        ("[\"targo\",\"rustdoc\",\"ay\",\"ty\"]", "clean"),
    ] {
        let config = context
            .config("install")
            .stage(2)
            .arg(SELECTION)
            .args(&[
                "--set",
                "install.prefix=/immutable/current-trust",
                "--set",
                "build.extended=true",
                "--set",
                &format!("build.tools={tools}"),
            ])
            .create_config();
        assert_eq!(
            validate_with_environment(&config, &Default::default()).unwrap_err(),
            format!("WP installation requires {missing} in build.tools"),
            "{tools}"
        );
    }
}

#[test]
fn immutable_install_requires_formatter_and_linter_selectors() {
    let context = TestCtx::new();
    let config = |formatter: &str, linter: &str| {
        context
            .config("install")
            .stage(2)
            .arg(SELECTION)
            .args(&[
                "--set",
                "install.prefix=/immutable/current-trust",
                "--set",
                "build.extended=true",
                "--set",
                &format!(
                    "build.tools=[\"targo\",\"trustdoc\",\"ty\",\"clean\",\"{formatter}\",\"{linter}\"]"
                ),
            ])
            .create_config()
    };
    for (formatter, linter) in [
        ("trustfmt", "tippy"),
        ("rustfmt", "clippy"),
        ("trustfmt", "cargo-clippy"),
        ("trustfmt", "tippy-driver"),
    ] {
        assert!(validate_with_environment(&config(formatter, linter), &Default::default()).is_ok());
    }
    for (formatter, linter, missing) in [
        ("", "tippy", "trustfmt"),
        ("trustfmt-other", "tippy", "trustfmt"),
        ("trustfmt", "", "tippy"),
        ("trustfmt", "tippy-other", "tippy"),
    ] {
        assert_eq!(
            validate_with_environment(&config(formatter, linter), &Default::default()).unwrap_err(),
            format!("WP installation requires {missing} in build.tools")
        );
    }
}

#[test]
fn immutable_install_graph_keeps_component_owners_and_std_uplift_policy() {
    for full in [false, true] {
        let context = TestCtx::new();
        let session = Session::new(
            context
                .config("install")
                .stage(2)
                .arg(SELECTION)
                .args(&[
                    "--set",
                    "install.prefix=/immutable/current-trust",
                    "--set",
                    "build.extended=true",
                    "--set",
                    &format!("build.full-bootstrap={full}"),
                ])
                .create_config(),
        );
        let builder = Builder::new(&session);
        let produced = components(&builder);
        assert_eq!(
            produced.map(|(name, _)| name),
            ["trustc", "trust-std", "trustc-dev", "targo", "targo-trust", "trustfmt", "tippy"]
        );
        assert!(
            builder
                .step_cache()
                .get(&dist::Rustc { target_compiler: builder.compiler(2, builder.host_target) })
                .is_some()
        );
        let compilers = RustcPrivateCompilers::new(&builder, 2, builder.host_target);
        assert_eq!(compilers.build_compiler(), builder.compiler(1, builder.host_target));
        assert_eq!(compilers.target_compiler(), builder.compiler(2, builder.host_target));
        assert!(
            builder
                .step_cache()
                .get(&dist::Rustfmt { compilers, target: builder.host_target })
                .is_some()
        );
        assert!(
            builder
                .step_cache()
                .get(&dist::Clippy { compilers, target: builder.host_target })
                .is_some()
        );
        assert!(builder.step_cache().get(&tool::Rustfmt::from_compilers(compilers)).is_some());
        assert!(builder.step_cache().get(&tool::Cargofmt::from_compilers(compilers)).is_some());
        assert!(builder.step_cache().get(&tool::Clippy::from_compilers(compilers)).is_some());
        assert!(builder.step_cache().get(&tool::CargoClippy::from_compilers(compilers)).is_some());
        let std = dist::Std::new(&builder, builder.host_target);
        assert!(builder.step_cache().get(&std).is_some());
        assert_eq!(std.build_compiler.stage, if full { 2 } else { 1 });
        assert!(
            builder.step_cache().get(&dist::RustcDev::new(&builder, builder.host_target)).is_some()
        );
        assert!(
            builder
                .step_cache()
                .get(&dist::Cargo {
                    build_compiler: builder.compiler(1, builder.host_target),
                    target: builder.host_target
                })
                .is_some()
        );
        // Trust: ensuring the verifier in a stage sysroot is insufficient: its
        // dedicated image must participate in the immutable transaction too.
        let build_compiler = builder.compiler(1, builder.host_target);
        assert!(
            builder
                .step_cache()
                .get(&dist::TCargoTrust { build_compiler, target: builder.host_target })
                .is_some()
        );
        assert!(
            builder
                .step_cache()
                .get(&tool::TCargoTrust::from_build_compiler(build_compiler, builder.host_target))
                .is_some()
        );
        assert!(
            builder
                .step_cache()
                .get(&tool::Trustd::from_build_compiler(build_compiler, builder.host_target))
                .is_some()
        );
        let steps = builder.step_cache().executed_steps();
        let count = |metadata| {
            steps.iter().filter(|step| step.metadata.as_ref() == Some(&metadata)).count()
        };
        assert_eq!(
            count(
                Step::metadata(&compile::Rustc::new(
                    builder.compiler(1, builder.host_target),
                    builder.host_target
                ))
                .unwrap()
            ),
            1
        );
    }
}

#[test]
fn installer_selection_refuses_unbound_native_cargo_home_target_and_wrapper_authority() {
    let context = TestCtx::new();
    let config = context
        .config("install")
        .stage(2)
        .arg(SELECTION)
        .args(&["--set", "install.prefix=/immutable/current-trust", "--set", "build.extended=true"])
        .create_config();
    let mut environment = std::collections::BTreeMap::new();
    assert!(validate_with_environment(&config, &environment).is_ok());
    for (key, value) in [
        ("TARGO_HOME", "/unbound/native-home"),
        ("CARGO_HOME", "relative"),
        ("TARGO_BUILD_TARGET", "foreign-target"),
        ("CARGO_BUILD_TARGET", "foreign-target"),
        ("TARGO_BUILD_RUSTC_WRAPPER", "/unbound/wrapper"),
        ("RUSTC_WRAPPER", "/unbound/wrapper"),
        ("RUSTC_WORKSPACE_WRAPPER", "/unbound/wrapper"),
        ("RUSTC_WRAPPER_REAL", "/unbound/wrapper"),
        ("RUSTFLAGS", "@/unbound/flags"),
        ("DESTDIR", "/different/destination"),
    ] {
        environment.insert(key.into(), value.into());
        assert!(validate_with_environment(&config, &environment).is_err(), "{key}");
        environment.clear();
    }
    environment.insert("TARGO_HOME".into(), "/unused/native-home".into());
    environment.insert("CARGO_HOME".into(), "/declared/cargo-home".into());
    assert!(
        validate_with_environment(&config, &environment).is_ok(),
        "explicit inventoried compatibility home wins"
    );
}
