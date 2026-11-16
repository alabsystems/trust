//! Trust (LEAN-CENSUS-IMPORT-BATCH-1): the observer's roster/phase binding.
//! The rosters carry only the fields `roster_matches_phase` reads, spelled as
//! `trust_certify::clean_census::LeanKernelRoster::capture` and
//! `CleanIslandSession::check_import_islands_with_census` write them.

use serde_json::{Value, json};

use super::CheckPhase::*;
use super::*;

/// `check_all_with_census`: the pre-walk module batch.
fn module_roster(rejected: bool) -> Value {
    json!({
        "check_mode": "header-first-batch",
        "registration_semantics": "transactional-module",
        "check_rejected": rejected,
        "source_declaration_metadata": "elaborator-module-outcome",
    })
}

/// `check_import_islands_with_census`: TG14's deferred-suffix batch.
fn import_roster(refused: &[u64], rejected: bool) -> Value {
    let mut roster = module_roster(rejected);
    roster["source_declaration_metadata"] = json!("unavailable-from-import-wrapper");
    roster["import_recovery"] = json!({
        "refused_units": refused,
        "all_original_sources_retained": true,
        "survivors_checked_together": true,
    });
    roster
}

#[test]
fn the_pre_walk_batch_is_a_module_roster_without_import_recovery() {
    for rejected in [false, true] {
        assert!(roster_matches_phase(&module_roster(rejected), 2, HeaderFirst, rejected));
        assert!(!roster_matches_phase(&module_roster(rejected), 2, HeaderFirst, !rejected));
        let mut unavailable = module_roster(rejected);
        unavailable["source_declaration_metadata"] = json!("unavailable-before-module-outcome");
        assert!(roster_matches_phase(&unavailable, 2, HeaderFirst, rejected));
        // An import roster is not the pre-walk check, and a module roster is
        // not the suffix, in either lane.
        assert!(!roster_matches_phase(&import_roster(&[], rejected), 2, HeaderFirst, rejected));
        for phase in [AfterProgramAdmissions, VerificationDisabled] {
            assert!(!roster_matches_phase(&module_roster(rejected), 2, phase, rejected));
        }
    }
}

#[test]
fn the_suffix_is_one_import_batch_roster_that_names_its_refused_units() {
    for phase in [AfterProgramAdmissions, VerificationDisabled] {
        assert!(roster_matches_phase(&import_roster(&[], false), 2, phase, false));
        // An unattributed rejection names no unit; the reader requires its taint.
        assert!(roster_matches_phase(&import_roster(&[], true), 2, phase, true));
        assert!(roster_matches_phase(&import_roster(&[0], true), 2, phase, true));
        assert!(roster_matches_phase(&import_roster(&[0, 2], true), 3, phase, true));
        assert!(roster_matches_phase(&import_roster(&[0, 1, 2], true), 3, phase, true));
    }
}

#[test]
fn mismatched_import_rosters_are_refused() {
    let mutations: [(&str, fn(&mut Value)); 13] = [
        ("sequential checker", |roster| roster["check_mode"] = json!("sequential-island")),
        ("per-declaration registration", |roster| {
            roster["registration_semantics"] = json!("nontransactional-per-declaration")
        }),
        ("module metadata", |roster| {
            roster["source_declaration_metadata"] = json!("elaborator-module-outcome")
        }),
        ("missing recovery", |roster| {
            *roster = module_roster(true);
            roster["source_declaration_metadata"] = json!("unavailable-from-import-wrapper");
        }),
        ("null recovery", |roster| roster["import_recovery"] = Value::Null),
        ("unit outside the batch", |roster| {
            roster["import_recovery"]["refused_units"] = json!([0, 2])
        }),
        ("unsorted units", |roster| roster["import_recovery"]["refused_units"] = json!([1, 0])),
        ("duplicate units", |roster| roster["import_recovery"]["refused_units"] = json!([0, 0])),
        ("non-integer unit", |roster| roster["import_recovery"]["refused_units"] = json!(["0"])),
        ("units not a list", |roster| roster["import_recovery"]["refused_units"] = json!(0)),
        ("lost original sources", |roster| {
            roster["import_recovery"]["all_original_sources_retained"] = json!(false)
        }),
        ("survivors checked apart", |roster| {
            roster["import_recovery"]["survivors_checked_together"] = json!(false)
        }),
        ("extra recovery claim", |roster| {
            roster["import_recovery"]["survivors_committed"] = json!(true)
        }),
    ];
    for phase in [AfterProgramAdmissions, VerificationDisabled] {
        for (label, mutate) in mutations {
            let mut roster = import_roster(&[0], true);
            assert!(roster_matches_phase(&roster, 2, phase, true), "{label}: baseline");
            mutate(&mut roster);
            assert!(!roster_matches_phase(&roster, 2, phase, true), "{label}");
        }
        // A refused unit attributes a rejection; on an accepted batch it is a
        // contradiction, and an outer/kernel outcome mismatch stays refused.
        assert!(!roster_matches_phase(&import_roster(&[0], false), 2, phase, false));
        assert!(!roster_matches_phase(&import_roster(&[0], true), 2, phase, false));
        assert!(!roster_matches_phase(&import_roster(&[], false), 2, phase, true));
    }
}
