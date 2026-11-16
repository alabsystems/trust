//! Actual command-constructor policy, not Host/SDK admission or execution.
use super::*;

#[test]
fn tool_metadata_declares_only_its_platform_environment_removal() {
    for program in ["trustc", "targo"] {
        let mut metadata = tool_metadata_command(program);
        metadata.arg("--version");
        assert_eq!(metadata.get_program(), OsStr::new(program));
        assert_eq!(metadata.get_args().collect::<Vec<_>>(), [OsStr::new("--version")]);
        assert!(!metadata.metadata_scheduler, "the constructor grants no transport selection");
        let edits = metadata.get_envs().collect::<Vec<_>>();
        if cfg!(target_os = "macos") {
            assert_eq!(edits, [(OsStr::new("__CF_USER_TEXT_ENCODING"), None)]);
        } else {
            assert!(edits.is_empty());
        }
        metadata.mark_as_executed();
    }
}

#[test]
fn source_commands_and_other_metadata_inputs_keep_their_explicit_environment() {
    let mut source = command("trustc");
    source
        .arg("source.rs")
        .env("__CF_USER_TEXT_ENCODING", "caller-source-value")
        .env("PRIVATE_POLICY", "caller-policy-value");
    assert_eq!(
        source.get_envs().find(|(key, _)| *key == "__CF_USER_TEXT_ENCODING"),
        Some((OsStr::new("__CF_USER_TEXT_ENCODING"), Some(OsStr::new("caller-source-value"))))
    );
    assert!(!source.metadata_scheduler);

    let mut metadata = tool_metadata_command("trustc");
    metadata
        .arg("--print=sysroot")
        .env("RUSTC_BOOTSTRAP", "1")
        .env("PRIVATE_POLICY", "caller-policy-value")
        .env_remove("EXPLICIT_REMOVAL");
    metadata.metadata_scheduler();
    assert!(metadata.metadata_scheduler);
    for (key, value) in [
        ("RUSTC_BOOTSTRAP", Some("1")),
        ("PRIVATE_POLICY", Some("caller-policy-value")),
        ("EXPLICIT_REMOVAL", None),
    ] {
        assert_eq!(
            metadata.get_envs().find(|(name, _)| *name == key),
            Some((OsStr::new(key), value.map(OsStr::new)))
        );
    }
    source.mark_as_executed();
    metadata.mark_as_executed();
}
