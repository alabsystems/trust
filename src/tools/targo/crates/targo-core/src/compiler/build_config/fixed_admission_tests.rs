use cargo_util_terminal::Shell;

use super::*;

#[test]
fn ordinary_build_configuration_keeps_its_requested_jobs_without_fixed_custody() {
    let root = tempfile::tempdir().unwrap();
    let mut gctx = GlobalContext::new(Shell::new(), root.path().into(), root.path().join("home"));
    gctx.set_env(Default::default());
    let config = BuildConfig::new(
        &gctx,
        Some(JobsConfig::Integer(2)),
        false,
        &[],
        UserIntent::Build,
    )
    .unwrap();
    assert_eq!(config.jobs, 2);
    assert_eq!(config.resource_intent.ceiling, 2);
    assert!(gctx.fixed_admission().unwrap().is_none());
}

#[test]
fn invalid_fixed_handoff_refuses_before_loading_project_configuration() {
    let root = tempfile::tempdir().unwrap();
    std::fs::create_dir(root.path().join(".cargo")).unwrap();
    std::fs::write(
        root.path().join(".cargo/config.toml"),
        "[build\njobs = impossible",
    )
    .unwrap();
    let mut gctx = GlobalContext::new(Shell::new(), root.path().into(), root.path().join("home"));
    let mut env = crate::util::data_structures::HashMap::default();
    env.insert(
        trust_build_tree::admission::FIXED_HANDOFF_ENV.to_owned(),
        "0".to_owned(),
    );
    gctx.set_env(env);
    let error = BuildConfig::new(
        &gctx,
        Some(JobsConfig::Integer(2)),
        false,
        &[],
        UserIntent::Build,
    )
    .unwrap_err();
    assert!(
        format!("{error:#}").contains("cannot retain original fixed command admission"),
        "{error:#}"
    );
    // Refusal is never cached as successful absence on another consumer call.
    assert!(gctx.fixed_admission().is_err());
}
