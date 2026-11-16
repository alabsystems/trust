use super::*;
use crate::utils::tests::TestCtx;

#[test]
fn parsed_full_selection_rejects_changed_source_output_scope_and_bypass() {
    let context = TestCtx::new();
    let mut config = context.config("check").stage(1).no_dry_run().create_config();
    let arguments = [
        "check".into(),
        "--stage".into(),
        "1".into(),
        "--src".into(),
        config.src.as_os_str().to_owned(),
        "--build-dir".into(),
        config.out.as_os_str().to_owned(),
    ];
    let layout = crate::engine::xpy_input_layout(&arguments).unwrap();
    validate_selection(&config, &layout).unwrap();
    let original = config.out.clone();
    config.out = context.dir().join("foreign-output");
    assert!(validate_selection(&config, &layout).is_err());
    config.out = original;
    let original = config.src.clone();
    config.src = context.dir().join("foreign-source");
    assert!(validate_selection(&config, &layout).is_err());
    config.src = original;
    config.bypass_bootstrap_lock = true;
    assert!(validate_selection(&config, &layout).is_err());
    config.bypass_bootstrap_lock = false;
    config.paths.push("compiler/rustc".into());
    assert!(validate_selection(&config, &layout).is_err());
    config.paths.clear();
    validate_selection(&config, &layout).unwrap();
}

#[test]
fn original_source_alias_is_bookended_against_real_replacement() {
    let context = TestCtx::new();
    let original = context.dir().join("original");
    let other = context.dir().join("other");
    let alias = context.dir().join("alias");
    std::fs::create_dir(&original).unwrap();
    std::fs::create_dir(&other).unwrap();
    std::os::unix::fs::symlink(&original, &alias).unwrap();
    let original = original.canonicalize().unwrap();
    same_source(&alias, &original).unwrap();
    std::fs::remove_file(&alias).unwrap();
    std::os::unix::fs::symlink(other, &alias).unwrap();
    assert!(same_source(&alias, &original).is_err());
    std::fs::remove_file(&alias).unwrap();
    assert!(same_source(&alias, &original).is_err());
}
