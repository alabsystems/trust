// Copyright 2026 Andrew Yates
//! Trust: one genuine entry owner for Bootstrap's complete library test suite.

use std::process::Command;

const UNCAPTURED_ACTOR: &str = "TRUST_BOOTSTRAP_UNCAPTURED_TEST_ACTOR";

// These are advertisements of native custody, never fixture authority.
fn native_advertisements() -> &'static [&'static str] {
    &[
        "ATERM_SDK_LEASE_V3",
        jobserver_utils::CPU_HANDOFF_ENV,
        jobserver_utils::FIXED_CLAIM_HANDOFF_ENV,
        jobserver_utils::DESCENDANT_HANDOFF_ENV,
        "BUILD_SLOT_CPU_PROTOCOL",
        "BUILD_SLOT_HELD",
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        build_helper::admission::FIXED_HANDOFF_ENV,
    ]
}

/// Only intentional synthetic/missing-owner controls use this launcher. Transported
/// GNU observers use normal entry and never receive this opt-out.
pub(crate) fn uncaptured_actor(command: Command) -> Command {
    let mut command = synthetic_observer(command);
    command.env(UNCAPTURED_ACTOR, "1");
    command
}

/// An observer of a newly constructed synthetic GNU pool still captures at entry;
/// its fixture must not accidentally advertise the parent's real native custody.
pub(crate) fn synthetic_observer(mut command: Command) -> Command {
    for key in native_advertisements() {
        command.env_remove(key);
    }
    command.env_remove("CARGO_MAKEFLAGS").env_remove("MAKEFLAGS").env_remove("MFLAGS");
    command.env_remove(UNCAPTURED_ACTOR);
    command
}

fn initialize() -> Result<(), String> {
    let actor = std::env::var_os(UNCAPTURED_ACTOR);
    // SAFETY: genuine generated entry, before threads or arbitrary callbacks. Consume
    // this test-only mode so a later observer cannot accidentally inherit it.
    #[allow(unknown_lints, env_mutation)]
    unsafe {
        std::env::remove_var(UNCAPTURED_ACTOR)
    };
    if let Some(actor) = actor {
        if actor != "1" || native_advertisements().iter().any(|key| std::env::var_os(key).is_some())
        {
            return Err("uncaptured test actor cannot retain native custody advertisements".into());
        }
        return Ok(());
    }
    // SAFETY: syscall-only setup at original generated entry.
    unsafe { crate::native_entry::clamp_creation_mask_at_entry() };
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    let fixed = crate::snapshot_fixed_at_entry()?;
    // SAFETY: no descriptor allocation or arbitrary callback preceded capture.
    unsafe { crate::capture_scheduler_at_entry() }?;
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    crate::capture_fixed_at_entry(fixed)?;
    Ok(())
}

pub(crate) fn run(tests: &[&test::TestDescAndFn]) {
    if let Err(error) = initialize() {
        eprintln!("bootstrap unit entry refused: {error}");
        std::process::exit(75);
    }
    #[cfg(panic = "unwind")]
    let result = test::test_main_env_args(tests);
    #[cfg(not(panic = "unwind"))]
    let result = test::test_main_env_args_abort(tests);
    result.exit_process();
}

#[cfg(test)]
// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires: the file sits
// under test_entry/ so the module keeps its `test_entry::tests` path.
#[path = "test_entry/tests.rs"]
mod tests;
