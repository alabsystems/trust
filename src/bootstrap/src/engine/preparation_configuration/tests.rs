use super::*;
fn args(input: &[&str]) -> Vec<String> {
    input.iter().map(|arg| (*arg).into()).collect()
}
#[test]
fn exact_external_config_profile_override_order_and_duplicates_are_retained() {
    let original = args(&[
        "build",
        "--config",
        "/evidence/full.toml",
        "--set",
        "profile=\"compiler\"",
        "--set",
        "build.jobs=2",
        "--set",
        "build.jobs=1",
        "--build-dir",
        "/original-output",
    ]);
    let selected = ClosedFullPreparationConfiguration::from_parser_input(
        &original,
        Path::new("/original-cwd"),
    )
    .unwrap();
    assert_eq!(selected.parser_input(), original);
    assert_eq!(selected.invocation_directory(), Path::new("/original-cwd"));
}
#[test]
fn existing_parser_scope_and_stage0_contract_refuse_unsupported_selection() {
    for input in [
        args(&["--help"]),
        args(&["--version"]),
        args(&["build", "--unknown-option"]),
        args(&["build", "--dry-run"]),
        args(&["build", "--stage", "1", "compiler/rustc"]),
        args(&["build", "--skip-stage0-validation"]),
        args(&["setup"]),
    ] {
        assert!(
            ClosedFullPreparationConfiguration::from_parser_input(&input, Path::new("/cwd"))
                .is_err()
        );
    }
    let defaults =
        args(&["build", "--stage", "1", "--include-default-paths", "compiler/rustc"]);
    ClosedFullPreparationConfiguration::from_parser_input(&defaults, Path::new("/cwd"))
        .unwrap();
}
#[test]
fn malformed_or_unbounded_parser_data_never_implies_original_selection() {
    for input in [
        vec![],
        args(&["build", "--config", "bad\0path"]),
        vec!["build".into(); MAX_ARGUMENTS + 1],
        args(&["build", "--set", &"x".repeat(MAX_BYTES)]),
    ] {
        assert!(
            ClosedFullPreparationConfiguration::from_parser_input(&input, Path::new("/cwd"))
                .is_err()
        );
    }
    assert!(
        ClosedFullPreparationConfiguration::from_parser_input(
            &args(&["build"]),
            Path::new("relative")
        )
        .is_err()
    );
}
#[test]
fn actual_caller_keeps_non_full_scope_separate_and_retains_full_parser_error() {
    let selected = args(&["build", "--stage", "1", "compiler/rustc"]);
    let flags = crate::core::config::flags::Flags::try_parse(&selected).unwrap();
    assert!(capture_original_configuration(&selected, &flags).unwrap().is_none());
    let unsupported = args(&["build", "--skip-stage0-validation"]);
    let flags = crate::core::config::flags::Flags::try_parse(&unsupported).unwrap();
    assert!(capture_original_configuration(&unsupported, &flags).is_err());
}
#[cfg(unix)]
#[test]
fn decoded_configuration_data_requires_the_same_fallible_parser_and_full_scope() {
    let original = args(&["build", "--config", "/external/full.toml", "--set", "build.jobs=2"]);
    let captured =
        ClosedFullPreparationConfiguration::from_parser_input(&original, Path::new("/cwd"))
            .unwrap();
    let mut attachment = captured.attachment().unwrap();
    let same = ClosedFullPreparationConfiguration::from_attachment(&attachment).unwrap();
    assert_eq!(same.parser_input(), original);
    assert_eq!(same.invocation_directory(), captured.invocation_directory());
    for unsupported in [
        args(&["--help"]),
        args(&["--unknown-option"]),
        args(&["build", "--stage", "1", "compiler/rustc"]),
        args(&["build", "--skip-stage0-validation"]),
    ] {
        attachment.parser_input = unsupported;
        attachment.validate().unwrap(); // syntax DATA has no scope authority
        assert!(ClosedFullPreparationConfiguration::from_attachment(&attachment).is_err());
    }
}
