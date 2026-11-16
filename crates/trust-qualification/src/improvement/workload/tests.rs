// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;

#[test]
fn complete_population_and_fingerprint_include_every_planned_variant() {
    let plan = WorkloadPlan::new(3).unwrap();
    assert_eq!(plan.scenarios().len(), 6);
    assert_eq!(plan.scenarios().last(), Some(&Scenario::AmbiguousModuleRefusal));
    assert_eq!(plan.scenarios()[4].required_consumers(), &["app", "peer"]);
    assert!(plan.scenarios()[5].required_consumers().is_empty());
    let identity = plan.identity_sha256();
    assert_eq!(identity.len(), 64);
    assert!(identity.bytes().all(|b| b.is_ascii_hexdigit()));
    assert_eq!(identity, WorkloadPlan::new(3).unwrap().identity_sha256());
    assert_ne!(identity, WorkloadPlan::new(4).unwrap().identity_sha256());
    assert!(WorkloadPlan::new(0).is_err());
    assert!(WorkloadPlan::new(32).is_err());
}

#[test]
fn source_invalidation_is_one_same_size_change_and_negative_lookup_is_real() {
    let plan = WorkloadPlan::new(1).unwrap();
    let before = plan.sources(SourceVariant::Initial);
    let after = plan.sources(SourceVariant::Changed);
    assert_eq!(before.len(), 9);
    assert_eq!(before.len(), after.len());
    let changes = before.iter().zip(&after).filter(|(a, b)| a != b).collect::<Vec<_>>();
    assert_eq!(changes.len(), 1);
    let (a, b) = changes[0];
    assert_eq!(a.path, "leaf/src/implementation.rs");
    assert_eq!(a.path, b.path);
    assert_eq!(a.bytes.len(), b.bytes.len());
    assert_eq!(a.bytes, b"pub fn base() -> u32 { 42 }\n");
    assert_eq!(b.bytes, b"pub fn base() -> u32 { 43 }\n");
    let ambiguous = plan.sources(SourceVariant::Ambiguous);
    assert_eq!(ambiguous.len(), after.len() + 1);
    assert!(after.iter().all(|source| ambiguous.contains(source)));
    assert!(ambiguous.iter().any(|source| source.path == "leaf/src/implementation/mod.rs"));
    for consumer in ["app", "peer"] {
        let lock =
            before.iter().find(|source| source.path == format!("{consumer}/Cargo.lock")).unwrap();
        assert!(std::str::from_utf8(&lock.bytes).unwrap().contains("name = \"native_leaf\""));
        assert!(
            after.contains(lock),
            "same-size source changes do not alter selected dependency graph"
        );
    }
}

#[test]
fn concurrency_has_fresh_inputs_without_resetting_the_sequential_source_history() {
    for scenario in [
        Scenario::Cold,
        Scenario::Warm,
        Scenario::PreservedMtimeSourceChange,
        Scenario::FeatureChange,
        Scenario::AmbiguousModuleRefusal,
    ] {
        assert_eq!(scenario.cache_domain(), CacheDomain::Sequential);
    }
    let concurrent = Scenario::ConcurrentConsumers;
    assert_eq!(concurrent.cache_domain(), CacheDomain::Concurrent);
    assert_eq!(concurrent.transition(), Transition::FreshInputsAndCache);
    assert_eq!(concurrent.source_variant(), SourceVariant::Initial);
    assert_eq!(concurrent.required_consumers(), &["app", "peer"]);
    assert_eq!(Scenario::Warm.transition(), Transition::Unchanged);
    assert_eq!(
        Scenario::PreservedMtimeSourceChange.transition(),
        Transition::ReplaceSameSizePreservingMtime
    );
    assert_eq!(Scenario::FeatureChange.transition(), Transition::ConfigurationOnly);
    assert_eq!(Scenario::FeatureChange.features(), &["offset"]);
    assert!(Scenario::AmbiguousModuleRefusal.features().is_empty());
    assert_eq!(Scenario::AmbiguousModuleRefusal.transition(), Transition::AddAmbiguousModule);
    assert_eq!(Scenario::AmbiguousModuleRefusal.source_variant(), SourceVariant::Ambiguous);
}

#[test]
fn parent_checks_actual_runtime_result_for_source_feature_and_both_consumers() {
    let plan = WorkloadPlan::new(1).unwrap();
    for (scenario, consumer, argument, result) in [
        (Scenario::Cold, "app", 17, 59),
        (Scenario::Warm, "app", 251, 293),
        (Scenario::PreservedMtimeSourceChange, "app", 17, 60),
        (Scenario::FeatureChange, "app", 17, 1060),
        (Scenario::ConcurrentConsumers, "app", 0, 42),
        (Scenario::ConcurrentConsumers, "peer", 251, 293),
    ] {
        let output = format!("native-targo-behavior-v1:{result}\n");
        plan.validate_app_output(scenario, consumer, argument, output.as_bytes(), b"").unwrap();
        assert!(
            plan.validate_app_output(scenario, consumer, argument, output.as_bytes(), b"warning\n")
                .is_err()
        );
    }
}

#[test]
fn json_success_stale_value_missing_and_unselected_behavior_never_pass() {
    let plan = WorkloadPlan::new(1).unwrap();
    for output in [
        b"{\"status\":\"success\",\"value\":60}\n".as_slice(),
        b"native-targo-behavior-v1:59\n",
        b"",
        b"native-targo-behavior-v1:60\nextra\n",
    ] {
        assert!(
            plan.validate_app_output(Scenario::PreservedMtimeSourceChange, "app", 17, output, b"")
                .is_err()
        );
    }
    assert!(
        plan.validate_app_output(Scenario::Warm, "peer", 17, b"native-targo-behavior-v1:59\n", b"")
            .is_err()
    );
    assert!(
        plan.validate_app_output(
            Scenario::Warm,
            "app",
            252,
            b"native-targo-behavior-v1:294\n",
            b""
        )
        .is_err()
    );
    assert!(
        plan.validate_app_output(
            Scenario::AmbiguousModuleRefusal,
            "app",
            17,
            b"native-targo-behavior-v1:60\n",
            b""
        )
        .is_err()
    );
}
