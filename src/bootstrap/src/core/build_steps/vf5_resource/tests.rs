use super::*;
use std::path::PathBuf;

fn input(digest: &str) -> Vf5BaseInput {
    Vf5BaseInput { package: PathBuf::from("/prepared-mathematics"), manifest_sha256: digest.into() }
}

fn policy(pairs: &[(&str, &str)], required: bool) -> ResourcePolicy {
    ResourcePolicy { schema: 1, kind: "vf5-resource-policy-v1".into(),
        production_pin_required: required, production_admission: false,
        allowed_packages: pairs.iter().map(|(manifest, env)| PackagePin {
            manifest_sha256: (*manifest).into(), environment_sha256: (*env).into(),
        }).collect() }
}

#[test]
fn pin_off_preserves_absence_but_pin_on_requires_exact_configured_manifest() {
    let manifest = "12".repeat(32);
    let environment = "34".repeat(32);
    assert!(policy_allows(&policy(&[], false), None).is_ok());
    assert!(policy_allows(&policy(&[], false), Some(&input(&manifest))).is_ok());
    let enabled = policy(&[(&manifest, &environment)], true);
    assert!(policy_allows(&enabled, Some(&input(&manifest))).is_ok());
    assert!(policy_allows(&enabled, None).is_err());
    assert!(policy_allows(&enabled, Some(&input(&"56".repeat(32)))).is_err());
}

#[test]
fn malformed_or_authority_bearing_host_policy_never_silently_becomes_pin_off() {
    let manifest = "12".repeat(32);
    let environment = "34".repeat(32);
    let mut invalid = policy(&[], false);
    invalid.production_admission = true;
    assert!(policy_allows(&invalid, None).is_err());
    assert!(policy_allows(&policy(&[], true), None).is_err());
    assert!(policy_allows(&policy(&[(&manifest, &environment)], false), None).is_err());
    let zero = "00".repeat(32);
    for pins in [vec![(&manifest[..], "short")], vec![(&manifest[..], &environment[..]), (&manifest[..], &environment[..])],
        vec![(&manifest[..], &zero[..])]] {
        assert!(policy_allows(&policy(&pins, true), Some(&input(&manifest))).is_err());
    }
}

// The former two path-parent tests did not cover mutation before a refusal.
// Parent filesystem tests now live with the actual held-FD stage_sysroot_resource
// mechanism (fixed path/repeat/aliases, both overlaps, actual parent-name swap).
