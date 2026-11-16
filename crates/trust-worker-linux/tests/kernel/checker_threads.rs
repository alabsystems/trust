use super::*;

fn checker(mode: &str, modified: Option<&str>) -> Result<Observation> {
    run_fixture(mode, modified, Path::new(env!("CARGO_BIN_EXE_checker-threads-fixture")))
}
#[test]
fn real_builder_name_tls_sleep_and_join_under_fixed_profile() -> Result<()> {
    let result = checker("positive", None)?;
    assert_eq!(result.cause, Cause::Exit);
    assert!(
        result.status.success(),
        "{} {}",
        result.status,
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(result.stdout, b"INSTALLED\nPASS\n");
    assert_eq!(result.control, b"TDJ");
    Ok(())
}
#[test]
fn address_space_limit_refuses_large_thread_stack() -> Result<()> {
    let result = checker("as-limit", None)?;
    assert_eq!(result.cause, Cause::Exit);
    assert!(
        result.status.success(),
        "{} {}",
        result.status,
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(result.stdout, b"INSTALLED\nAS-REFUSED\n");
    Ok(())
}
#[test]
fn raw_process_namespace_and_alternate_clone_flags_are_killed() -> Result<()> {
    for mode in [
        "clone-process",
        "clone-vfork",
        "clone-untraced",
        "clone-pidfd",
        "clone-newuser",
        "clone-newns",
        "clone-missing-vm",
        "clone-signal",
        "clone-high",
    ] {
        let result = checker(mode, None)?;
        assert_eq!(result.cause, Cause::Exit, "{mode}");
        assert_eq!(
            result.status.signal(),
            Some(libc::SIGSYS),
            "{mode}: {} {}",
            result.status,
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(result.stdout, b"INSTALLED\n", "{mode}");
    }
    Ok(())
}
#[test]
fn new_profile_keeps_other_authority_and_old_thread_profile_closed() -> Result<()> {
    for mode in [
        "signal-peer",
        "shared-wake",
        "robust-shape",
        "rseq-shape",
        "privilege",
        "exec",
        "strict-thread",
    ] {
        let result = checker(mode, None)?;
        assert_eq!(result.cause, Cause::Exit, "{mode}");
        assert_eq!(
            result.status.signal(),
            Some(libc::SIGSYS),
            "{mode}: {} {}",
            result.status,
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(result.stdout, b"INSTALLED\n", "{mode}");
    }
    Ok(())
}
#[test]
fn checker_entry_preserves_parent_input_and_environment_admission() -> Result<()> {
    for mutation in ["hash", "unsealed", "environment", "parent"] {
        let result = checker("positive", Some(mutation))?;
        assert_eq!(result.status.code(), Some(72), "{mutation}");
        assert!(result.stdout.is_empty());
        assert!(result.stderr.starts_with(b"REFUSED: "));
    }
    let cancelled = checker("cancelled", None)?;
    assert_eq!(cancelled.status.code(), Some(72));
    assert!(cancelled.stdout.is_empty());
    assert!(String::from_utf8_lossy(&cancelled.stderr).contains("Phase"));
    Ok(())
}
#[test]
fn zombie_leader_does_not_publish_completion_with_live_sibling_thread() -> Result<()> {
    let result = checker("leader-exit", None)?;
    assert_eq!(result.cause, Cause::Deadline);
    assert!(result.leader_zombie_before_reap, "leader never reached the observed zombie boundary");
    assert_eq!(result.control, b"TL");
    assert_eq!(result.stdout, b"INSTALLED\n");
    // The leader already exited(0). Linux delays its waitable exit until every
    // sibling dies; the parent killed the whole group before this leader reap.
    // Linux reports the final group-exit SIGKILL, not the leader's earlier 0.
    assert_eq!(result.status.signal(), Some(libc::SIGKILL));
    Ok(())
}
