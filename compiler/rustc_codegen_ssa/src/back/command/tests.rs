use super::*;

#[test]
fn final_path_preserves_inheritance_override_remove_and_clear_order() {
    let inherited = OsStr::new("/original/bin:/usr/bin");
    let mut command = Command::new("cc");
    assert_eq!(
        command.final_child_path(&command.command(), Some(inherited)),
        Some(inherited.into())
    );
    command.env("PATH", "/localized/bin");
    assert_eq!(
        command.final_child_path(&command.command(), Some(inherited)),
        Some("/localized/bin".into())
    );
    command.env_remove("PATH");
    assert_eq!(command.final_child_path(&command.command(), Some(inherited)), None);
    command.env_clear();
    // The existing builder clears even previously installed overrides.
    assert_eq!(command.final_child_path(&command.command(), Some(inherited)), None);
}

#[test]
fn observation_reads_program_and_final_overlays_without_rewriting_argv0() {
    let command = Command::lld("/absolute/ld", LldFlavor::Ld);
    let mut actual = command.command();
    actual.env("PATH", "/final/bin");
    assert_eq!(
        command.final_child_path(&actual, Some(OsStr::new("/parent"))),
        Some("/final/bin".into())
    );
    assert_eq!(actual.get_program(), OsStr::new("/absolute/ld"));
    assert_eq!(
        actual.get_args().collect::<Vec<_>>(),
        vec![OsStr::new("-flavor"), OsStr::new("gnu")]
    );
}

#[test]
#[allow(rustc::bad_opt_access)]
fn local_resource_v2_keeps_actual_paired_lld_program_flavor_and_path() {
    use rustc_session::tool_inputs::{Profile, local_profile_for_options};
    let mut opts = rustc_session::config::Options::default();
    opts.resource_worker_v2 = true;
    assert_eq!(local_profile_for_options(&opts), Some(Profile::LocalUnixNativeResourceV2));
    let mut command = Command::lld("/paired/sdk/bin/rust-lld", LldFlavor::Ld64);
    command.env("PATH", "/paired/sdk/bin:/usr/bin");
    let actual = command.command();
    assert_eq!(actual.get_program(), OsStr::new("/paired/sdk/bin/rust-lld"));
    assert_eq!(
        actual.get_args().collect::<Vec<_>>(),
        vec![OsStr::new("-flavor"), OsStr::new("darwin")]
    );
    assert_eq!(
        command.final_child_path(&actual, Some(OsStr::new("/original"))),
        Some("/paired/sdk/bin:/usr/bin".into())
    );
    // Runtime CPU width is not part of the execution profile. Changing the
    // parsed transport mode, however, cannot reuse the previous cc recipe.
    opts.resource_worker_v2 = false;
    assert_ne!(local_profile_for_options(&opts), Some(Profile::LocalUnixNativeResourceV2));
}
