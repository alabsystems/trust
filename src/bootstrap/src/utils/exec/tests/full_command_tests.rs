//! Actual wrapper provenance, without constructing an execution owner.
use super::*;
use crate::engine::OriginalCommand;

#[test]
fn full_projection_keeps_clear_environment_edits_arguments_and_cwd() {
    let mut original = command("targo");
    original
        .arg("--locked")
        .env("BEFORE_CLEAR", "removed")
        .env_clear()
        .env("AFTER_CLEAR", "selected")
        .env_remove("REMOVED")
        .current_dir("/actual/source");
    original.mark_as_executed();
    let projected = OriginalCommand::capture(&original.command, original.original_inputs).unwrap();
    assert!(projected.environment_cleared());
    assert_eq!(projected.command().get_program(), OsStr::new("targo"));
    assert_eq!(projected.command().get_args().collect::<Vec<_>>(), [OsStr::new("--locked")]);
    assert_eq!(projected.command().get_current_dir(), Some(Path::new("/actual/source")));
    let edits = projected.command().get_envs().collect::<Vec<_>>();
    assert_eq!(edits, [(OsStr::new("AFTER_CLEAR"), Some(OsStr::new("selected")))]);

    let mut inherited = command("targo");
    inherited.env_remove("REMOVED");
    inherited.mark_as_executed();
    let projected =
        OriginalCommand::capture(&inherited.command, inherited.original_inputs).unwrap();
    assert!(!projected.environment_cleared());
    assert_eq!(projected.command().get_envs().collect::<Vec<_>>(), [(OsStr::new("REMOVED"), None)]);
}

#[test]
fn full_projection_refuses_unobservable_imports_and_explicit_stdin() {
    let mut raw = Command::new("targo");
    raw.env_clear().stdin(Stdio::piped());
    let mut imported: BootstrapCommand = raw.into();
    imported.mark_as_executed();
    assert!(OriginalCommand::capture(&imported.command, imported.original_inputs).is_err());
    // A known environment does not repair opaque imported stdin.
    imported.env_clear();
    assert!(OriginalCommand::capture(&imported.command, imported.original_inputs).is_err());

    for stdin in [Stdio::null(), Stdio::inherit(), Stdio::piped()] {
        let mut selected = command("targo");
        selected.stdin(stdin);
        selected.mark_as_executed();
        assert!(OriginalCommand::capture(&selected.command, selected.original_inputs).is_err());
    }
}
