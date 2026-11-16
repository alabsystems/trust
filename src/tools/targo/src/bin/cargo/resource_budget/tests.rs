use super::*;

fn words(values: &[&str]) -> Vec<OsString> {
    values.iter().map(OsString::from).collect()
}

#[test]
fn native_budget_parses_every_closed_mode_without_project_configuration() {
    for mode in ["measure", "admit-overlap", "governor"] {
        assert_eq!(options(&words(&[mode])).unwrap().mode, mode);
    }
    for workload in ["rustc-build", "ui-test", "crates-test", "fast-lane"] {
        for mode in ["plan", "jobs"] {
            let value = options(&words(&[mode, workload, "--max", "2"])).unwrap();
            assert_eq!(value.request.workload.name(), workload);
            assert_eq!(value.request.maximum_jobs.unwrap().get(), 2);
        }
    }
    for values in [
        vec![],
        vec!["plan"],
        vec!["jobs", "other"],
        vec!["jobs", "rustc-build", "--max", "0"],
        vec!["governor", "--max", "2"],
        vec!["measure", "--namespace", "/other"],
    ] {
        assert!(options(&words(&values)).is_err());
    }
}

#[test]
fn counts_and_legacy_or_host_locators_do_not_create_an_original_budget() {
    unsupported_profile(|_| false).unwrap();
    for key in [
        "BUILD_SLOT_HELD",
        "ATERM_RESOURCE_JOB_V3",
        "ATERM_SDK_LEASE_V3",
        "TRUST_CPU_HANDOFF",
        "TRUST_CPU_IMPLICIT_FD",
    ] {
        assert!(
            unsupported_profile(|actual| actual == key).is_err(),
            "{key}"
        );
    }
    // This is the current authenticated courier route, not an old admission
    // marker. NestedInput plus the real importer still must authenticate it;
    // the None branch independently refuses an uncaptured advertisement.
    unsupported_profile(|key| key == cargo_util::FIXED_CLAIM_HANDOFF_ENV).unwrap();
    // These are only parser inputs. No count or public observation constructs
    // NestedInput, InheritedFixedClaim, CPU rights, or an admission owner.
    for value in ["NaN", "inf", "-1", "0", "1e100", "0.00000000000000001"] {
        assert!(gib_value(value).is_err(), "{value}");
    }
    assert_eq!(gib_value("2.5").unwrap().get(), 5 * 1024 * 1024 * 1024 / 2);
}
