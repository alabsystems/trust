//! Parsed planning controls only. No fixture constructs an SDK, Host operation,
//! protected source/output scope, GNU loan, artifact or completion authority.
use super::*;
use crate::core::build_steps::frontend_runtime::{self, FrontendRuntime};
use crate::core::build_steps::{compile, tool};
use crate::core::session::Session;
use crate::utils::tests::TestCtx;

#[test]
fn only_the_complete_parsed_native_object_profile_is_eligible() {
    let context = TestCtx::new();
    let valid = || {
        context
            .config("build")
            .stage(1)
            .args(&["--set", "rust.omit-git-hash=false"])
            .path("native-object-leaf")
            .create_config()
    };
    let config = valid();
    validate_config(&config).unwrap();
    crate::engine::validate_config(&config).unwrap();
    assert!(crate::engine::Plan::from_config(&config).is_native_object_leaf());
    // A first-node selection is not a completed-runtime producer selection.
    assert!(frontend_runtime::validate_config(&config).is_err());
    let mut config = valid();
    config.paths.push(std::path::PathBuf::from("library/std"));
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.stage = 2;
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.include_default_paths = true;
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.keep_stage.push(1);
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.keep_stage_std.push(1);
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.skip.push(std::path::PathBuf::from("compiler/rustc"));
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.download_rustc_commit = Some("0".repeat(40));
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.bypass_bootstrap_lock = true;
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.omit_git_hash = true;
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.hosts.clear();
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.hosts.push(config.host_target);
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.targets.clear();
    assert!(validate_config(&config).is_err());
    let mut config = valid();
    config.targets.push(config.host_target);
    assert!(validate_config(&config).is_err());
    for kind in ["check", "test", "bench"] {
        let config = context
            .config(kind)
            .stage(1)
            .args(&["--set", "rust.omit-git-hash=false"])
            .path("native-object-leaf")
            .create_config();
        assert!(validate_config(&config).is_err(), "wrong parsed verb {kind}");
        assert!(!crate::engine::Plan::from_config(&config).is_native_object_leaf());
    }
    for selector in [
        "frontend-runtime-owner",
        "library/std",
        "native-object-leaf-extra",
        "./native-object-leaf",
    ] {
        let mut config = valid();
        config.paths = vec![std::path::PathBuf::from(selector)];
        assert!(validate_config(&config).is_err(), "lookalike/nonobject selector {selector}");
        assert!(!crate::engine::Plan::from_config(&config).is_native_object_leaf());
    }
}

#[test]
fn native_named_custom_json_and_synthetic_targets_do_not_select_the_native_node() {
    let context = TestCtx::new();
    let mut config = context
        .config("build")
        .stage(1)
        .args(&["--set", "rust.omit-git-hash=false"])
        .path("native-object-leaf")
        .create_config();
    let scratch = tempfile::tempdir().unwrap();
    let path = scratch.path().join("aarch64-apple-darwin.json");
    std::fs::write(&path, b"{}").unwrap();
    let selected = TargetSelection::from_user(path.to_str().unwrap());
    assert_eq!(&*selected.triple, "aarch64-apple-darwin");
    assert!(selected.file.is_some());
    config.host_target = selected;
    config.hosts = vec![selected];
    config.targets = vec![selected];
    assert!(validate_config(&config).is_err());
    assert!(!crate::engine::Plan::from_config(&config).is_native_object_leaf());
    let selected =
        TargetSelection::create_synthetic("aarch64-apple-darwin", path.to_str().unwrap());
    config.host_target = selected;
    config.hosts = vec![selected];
    config.targets = vec![selected];
    assert!(validate_config(&config).is_err());
    assert!(!crate::engine::Plan::from_config(&config).is_native_object_leaf());
}

#[test]
fn the_exact_native_object_dry_plan_runs_one_node_without_runtime_producers() {
    let context = TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .args(&["--set", "rust.omit-git-hash=false"])
        .path("native-object-leaf")
        .create_config();
    assert!(config.dry_run());
    validate_config(&config).unwrap();
    let session = Session::new(config);
    let builder = Builder::new(&session);
    assert!(!NativeObject::is_default_step(&builder));
    builder.execute_cli();
    let cache = builder.step_cache();
    assert!(cache.contains::<NativeObject>());
    assert!(!cache.contains::<FrontendRuntime>());
    assert!(!cache.contains::<compile::Rustc>());
    assert!(!cache.contains::<compile::Std>());
    assert!(!cache.contains::<tool::Cargo>());
    assert!(!cache.contains::<tool::TCargoTrust>());
}

#[test]
fn embedded_original_sdk_validation_cannot_be_disabled_by_a_parsed_flag() {
    let words = |values: &[&str]| values.iter().map(|word| (*word).to_owned()).collect::<Vec<_>>();
    let flags = crate::core::config::flags::Flags::parse(&words(&[
        "build",
        "--stage",
        "1",
        "native-object-leaf",
    ]));
    crate::engine::validate_flags(&flags).unwrap();
    let flags = crate::core::config::flags::Flags::parse(&words(&[
        "build",
        "--stage",
        "1",
        "--skip-stage0-validation",
        "native-object-leaf",
    ]));
    assert!(crate::engine::validate_flags(&flags).is_err());
}
