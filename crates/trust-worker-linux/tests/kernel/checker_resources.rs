use super::*;

fn resource(mode: &str, mutation: Option<&str>) -> Result<Observation> {
    run_fixture(mode, mutation, Path::new(env!("CARGO_BIN_EXE_checker-threads-fixture")))
}

#[test]
fn live_proc_reads_measure_resident_growth_and_work_from_pthread() -> Result<()> {
    let result = resource("resource-positive", None)?;
    assert_eq!(result.cause, Cause::Exit);
    assert!(
        result.status.success(),
        "{} {}",
        result.status,
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(result.stdout, b"INSTALLED\nLIVE-RESOURCES\n");
    Ok(())
}

#[test]
fn live_resource_roles_cannot_be_swapped_or_imposed_by_regular_files() -> Result<()> {
    for mode in ["resource-wrong-role", "resource-imitation"] {
        let result = resource(mode, None)?;
        assert_eq!(result.cause, Cause::Exit, "{mode}");
        assert_eq!(result.status.code(), Some(72), "{mode}");
        assert!(result.stdout.is_empty());
        assert!(result.stderr.starts_with(b"REFUSED: "));
    }
    Ok(())
}

#[test]
fn actual_kernel_denies_resource_mutation_aliases_and_wider_observations() -> Result<()> {
    for mode in [
        "resource-read",
        "resource-write",
        "resource-close",
        "resource-seek",
        "resource-large",
        "resource-offset",
        "resource-map",
        "resource-dup",
        "resource-open",
        "resource-children",
    ] {
        let result = resource(mode, None)?;
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
fn resource_entry_preserves_parent_input_and_empty_environment_checks() -> Result<()> {
    for mutation in ["hash", "unsealed", "environment", "parent"] {
        let result = resource("resource-positive", Some(mutation))?;
        assert_eq!(result.cause, Cause::Exit, "{mutation}");
        assert_eq!(result.status.code(), Some(72), "{mutation}");
        assert!(result.stdout.is_empty());
        assert!(result.stderr.starts_with(b"REFUSED: "));
    }
    Ok(())
}
