// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual compiler-world source controls. These require the configured pinned
//! library DATA: unavailable input is a failure, never a skipped qualification.

use clean_kernel::Expr;
use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility, TrustedEnvExt as _};

use super::*;

fn input(module: &str, text: &str) -> LeanSourceInput {
    LeanSourceInput {
        module: module.into(),
        path: format!("/unread-source-label/{module}.lean"),
        source: text.into(),
    }
}

#[test]
fn pinned_source_world_complete_source_refusal_and_custody_controls() {
    // Match Clean's maintained genuine Init import tests' stack allocation.
    // This is runtime resources only; all semantic/refusal checks stay exact.
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(complete_source_refusal_and_custody_controls)
        .unwrap()
        .join()
        .unwrap();
}

fn complete_source_refusal_and_custody_controls() {
    let mut world = PinnedLeanSourceWorld::new().expect("configured genuine pinned Init DATA");
    let identity = vec![input("Identity", "def identity64 (x : UInt64) : UInt64 := x")];
    let legacy = CheckedLeanSourceBatch::check(identity.clone(), false);
    let legacy = legacy.accepted_context().expect("existing scalar source path");
    for census in [false, true] {
        let checked = world.check_with_runtime_baseline(identity.clone(), census);
        let context = checked.accepted_context().expect("genuine compiler-world identity");
        assert!(context.source_world().is_some());
        let decidable = context
            .environment()
            .get_inductive(&Name::from_string("Decidable"))
            .expect("genuine recent Init Decidable family");
        assert_eq!(
            decidable.constructor_names,
            vec![Name::from_string("Decidable.isFalse"), Name::from_string("Decidable.isTrue")]
        );
        assert!(
            context.environment().get_const(&Name::from_string("UInt16.not_neg_one")).is_some(),
            "full genuine Init witness, not a handwritten or Prelude-only fallback"
        );

        assert!(legacy.source_world().is_none());
        assert_eq!(context.sources(), identity);
        assert_ne!(context.source_closure_sha256(), legacy.source_closure_sha256());
        assert_eq!(
            context.owned_declarations(),
            &BTreeSet::from([Name::from_string("identity64")])
        );
        let baseline = context.runtime_baseline_environment().unwrap();
        assert_eq!(
            owned_names(context.environment())
                .difference(&owned_names(baseline))
                .cloned()
                .collect::<BTreeSet<_>>(),
            *context.owned_declarations()
        );
        assert_eq!(checked.attempt().unwrap().census.is_some(), census);
        eprintln!("PINNED_SOURCE_CONTROL identity/world/baseline/census={census}: accepted");

        // A fresh batch can reuse a source name and cannot see prior source
        // declarations through the initializer's immutable Init snapshot.
        assert!(world.check(identity.clone(), census).accepted_context().is_some());
        assert!(
            world
                .check(vec![input("NoLeak", "#check identity64")], census)
                .accepted_context()
                .is_none()
        );
        eprintln!("PINNED_SOURCE_CONTROL fresh-snapshot/census={census}: accepted/refused");

        let inputs = vec![
            input("Main", "import Sub.Helper\ndef uses : UInt64 := helper"),
            input("Helper", "def helper : UInt64 := 7"),
        ];
        let aliases = vec![LeanSourceAlias { module: "Sub.Helper".into(), source_index: 1 }];
        let checked = world.check_with_aliases(inputs.clone(), aliases.clone(), census);
        let context = checked.accepted_context().expect("complete supplied alias closure");
        assert_eq!(context.sources(), inputs);
        assert_eq!(context.aliases(), aliases);
        assert_eq!(
            context.owned_declarations(),
            &BTreeSet::from([Name::from_string("uses"), Name::from_string("helper"),])
        );
        assert!(world.check(inputs, census).accepted_context().is_none());
        eprintln!("PINNED_SOURCE_CONTROL aliases/whole-owned/census={census}: accepted/refused");

        for marker in ["lcAny", "lcErased"] {
            let name = Name::from_string(marker);
            let actual = baseline.get_const(&name).expect("actual genuine Init compiler axiom");
            assert_eq!(actual.kind, ConstantKind::Axiom);
            assert!(actual.value.is_none());
            eprintln!(
                "PINNED_SOURCE_MARKER_DATA {marker}: type={:?}, unsafe={}",
                actual.type_,
                baseline.is_unsafe(&name)
            );
            for (role, source) in [
                ("value", format!("def markerDependency := {marker}")),
                ("anonymous-type", format!("example : {marker} -> {marker} := fun x => x")),
            ] {
                let refused = world.check(vec![input("HostileMarker", &source)], census);
                assert!(
                    refused.accepted_context().is_none(),
                    "{marker}/{role}/{census} gained source authority"
                );
                let mut reasons = refused.errors().to_vec();
                if let Some(attempt) = refused.attempt() {
                    reasons.extend(
                        attempt
                            .outcomes
                            .iter()
                            .flat_map(|row| row.errors.iter().map(|e| e.message.clone())),
                    );
                }
                let reason = reasons.join("\n");
                let lower = reason.to_lowercase();
                assert!(
                    !lower.contains("unknown identifier")
                        && !lower.contains("unknown constant")
                        && !lower.contains("unresolved")
                        && !lower.contains("type mismatch")
                        && !lower.contains("typemismatch"),
                    "{marker}/{role}: unexpected refusal: {reason}"
                );
                assert!(
                    lower.contains("unsafe")
                        || (reason.contains(marker)
                            && (lower.contains("axiom")
                                || lower.contains("reference")
                                || lower.contains("trust debt"))),
                    "{marker}/{role}: not an unsafe/tripwire refusal: {reason}"
                );
                eprintln!(
                    "PINNED_SOURCE_CONTROL compiler-marker-{marker}/{role}/census={census}: refused ({reason})"
                );
            }
        }

        let generic = "universe u\nexample (α : Sort u) (x : α) : x = x := by rfl";
        let checked = world.check(vec![input("Generic", generic)], census);
        assert!(checked.accepted_context().is_some(), "{:?}", checked.errors());
        assert!(checked.attempt().unwrap().outcomes[0].anonymous_judgments > 0);
        eprintln!("PINNED_SOURCE_CONTROL generic-anonymous/census={census}: accepted");

        for (label, text) in [
            ("false-proof", "theorem bad : False := by exact True.intro"),
            ("anonymous-false", "example : False := by exact True.intro"),
            ("sorry", "theorem bad : False := by sorry"),
            ("axiom", "axiom unresolved : UInt64\ndef uses : UInt64 := unresolved"),
            ("unused-axiom", "def kept : UInt64 := 7\naxiom unused : UInt64"),
            ("unsafe", "def kept : UInt64 := 7\nunsafe def hidden : UInt64 := 8"),
            ("partial", "partial def loop (n : UInt64) : UInt64 := loop n"),
            ("external-import", "import UnprovidedPinnedSourceModule\ndef kept : UInt64 := 7"),
            ("prelude", "prelude\ndef kept : Nat := 0"),
        ] {
            let checked = world.check(vec![input(label, text)], census);
            assert!(
                checked.accepted_context().is_none(),
                "{label}/{census} gained source acceptance"
            );
            assert!(
                !checked.errors().is_empty()
                    || checked.attempt().is_some_and(|batch| batch.is_rejected())
            );
            eprintln!("PINNED_SOURCE_CONTROL {label}/census={census}: refused");
        }
    }

    let original =
        include_str!("../../../trust-clean-ir-gate/probes/source_closure_refinement/Original.lean");
    let actual =
        world.check_with_runtime_baseline(vec![input("ActualClosureInput", original)], false);
    let context =
        actual.accepted_context().expect("actual original three definitions in genuine world");
    assert_eq!(
        context.owned_declarations(),
        &BTreeSet::from([
            Name::from_string("EscapingOriginal.makeAffine"),
            Name::from_string("EscapingOriginal.apply64"),
            Name::from_string("EscapingOriginal.useAffine"),
        ])
    );
    assert!(context.source_world().is_some());
    assert_eq!(context.sources()[0].source, original);
    eprintln!(
        "PINNED_SOURCE_CONTROL actual-accepted-three: complete exact source and owned roster retained"
    );

    // A genuine source-generated family has auxiliaries absent from named
    // heads. It must never be accepted by dropping those original records.
    let generated = world.check(
        vec![input(
            "Generated",
            "inductive SourceChoice where\n| first : SourceChoice\n| second : SourceChoice",
        )],
        true,
    );
    let census = &generated.attempt().unwrap().census.as_ref().unwrap().report;
    let helper = Name::from_string("SourceChoice.recOn");
    assert!(
        census["declarations"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| serde_json::from_value::<Name>(row["identity"].clone()).unwrap() == helper)
    );
    assert!(!generated.attempt().unwrap().outcomes[0].registered.contains(&helper.to_string()));
    if let Some(context) = generated.accepted_context() {
        assert!(context.owns_declaration(&helper));
    } else {
        assert!(generated.attempt().unwrap().is_rejected());
    }
    eprintln!(
        "PINNED_SOURCE_CONTROL actual-generated-auxiliary: retained in measured/accepted-or-refused denominator"
    );

    // Directly exercise imported/producer DATA outside the registered-head
    // roster. Honest baseline acceptance makes the following refusals
    // discriminating, including an independent unused generated bad helper.
    let genuine = world.fresh_prelude(&[]).unwrap().into_parts().0;
    let baseline = owned_names(&genuine);
    for (label, dependency) in [
        (
            "raw-bad-helper",
            ConstantInfo::new_with_reducibility(
                Name::from_string("generated.badAux"),
                Vec::new(),
                Expr::const_str("False"),
                Some(Expr::const_str("True.intro")),
                Reducibility::Opaque,
                ConstantKind::Definition,
            ),
        ),
        (
            "raw-domain-axiom",
            ConstantInfo::new_with_reducibility(
                Name::from_string("generated.badAssumption"),
                Vec::new(),
                Expr::const_str("False"),
                None,
                Reducibility::Opaque,
                ConstantKind::Axiom,
            ),
        ),
    ] {
        for census in [false, true] {
            let mut good = genuine.clone();
            let mut context = clean_elab::FileContext::new();
            context.disable_external_import_search();
            let accepted = crate::clean_island_batch::check_pinned_sources_batched(
                &mut good,
                &mut context,
                &["def independent : UInt64 := 7"],
                &[],
                census,
                &baseline,
            );
            assert!(!accepted.is_rejected(), "honest baseline for {label}: {accepted:?}");

            let mut bad = genuine.clone();
            assert!(
                bad.extend_constants_structural(std::iter::once(dependency.clone())).is_empty()
            );
            let mut context = clean_elab::FileContext::new();
            context.disable_external_import_search();
            let refused = crate::clean_island_batch::check_pinned_sources_batched(
                &mut bad,
                &mut context,
                &["def independent : UInt64 := 7"],
                &[],
                census,
                &baseline,
            );
            assert!(refused.is_rejected(), "{label} outside named heads gained authority");
            eprintln!(
                "PINNED_SOURCE_CONTROL {label}/census={census}: honest baseline accepted; bad whole-owned DATA refused"
            );
        }
    }

    // A used preexisting dependency is outside the eager-added denominator,
    // but still inside the original judgment's mandatory closed cone.
    let imported = world.check(vec![input("Library", "def imported : UInt64 := 7")], false);
    let imported_context = imported.accepted_context().unwrap();
    let good_library = imported_context.environment();
    let good_before = owned_names(good_library);
    for census in [false, true] {
        let mut good = good_library.clone();
        let mut context = clean_elab::FileContext::new();
        context.disable_external_import_search();
        let checked = crate::clean_island_batch::check_pinned_sources_batched(
            &mut good,
            &mut context,
            &["def root : UInt64 := imported"],
            &[],
            census,
            &good_before,
        );
        assert!(!checked.is_rejected(), "valid preexisting dependency: {checked:?}");

        for (label, kind, value) in [
            ("bad-preexisting-body", ConstantKind::Definition, Some(Expr::const_str("True.intro"))),
            ("preexisting-domain-axiom", ConstantKind::Axiom, None),
        ] {
            let mut bad = genuine.clone();
            let row = ConstantInfo::new_with_reducibility(
                Name::from_string("imported"),
                Vec::new(),
                Expr::const_str("UInt64"),
                value,
                Reducibility::Opaque,
                kind,
            );
            assert!(bad.extend_constants_structural(std::iter::once(row)).is_empty());
            let before = owned_names(&bad);
            let mut context = clean_elab::FileContext::new();
            context.disable_external_import_search();
            let checked = crate::clean_island_batch::check_pinned_sources_batched(
                &mut bad,
                &mut context,
                &["def root : UInt64 := imported"],
                &[],
                census,
                &before,
            );
            assert!(checked.is_rejected(), "{label} escaped the original dependency cone");
            eprintln!(
                "PINNED_SOURCE_CONTROL {label}/census={census}: used nonowned dependency refused"
            );
        }
    }

    let home = tempfile::tempdir().unwrap();
    let facts = std::sync::Arc::new(crate::clean_fact::FactContext::for_tests(
        home.path(),
        "pinned-source-facts",
        false,
    ));
    let mut ordinary = CleanIslandSession::new();
    ordinary.enable_facts(facts.clone());
    assert!(ordinary.facts_active_for_tests(), "valid fact store baseline");
    let mut source =
        CleanIslandSession::new_for_pinned_source_batch(world.fresh_prelude(&[]).unwrap());
    source.enable_facts(facts);
    assert!(!source.facts_active_for_tests(), "source initializer activated ordinary island facts");
    eprintln!(
        "PINNED_SOURCE_CONTROL facts-poison: ordinary baseline enabled; source enable refused"
    );
}

#[test]
fn pinned_source_explicit_init_keeps_exact_sources_owned_roster_and_refusals() {
    std::thread::Builder::new().stack_size(128 << 20).spawn(|| {
        let mut world = PinnedLeanSourceWorld::new().expect("actual configured pinned Init DATA");
        let exact = "import Init\ndef explicitIdentity64 (x : UInt64) : UInt64 := x\ndef extraOwned64 (x : UInt64) : UInt64 := x";
        for census in [false, true] {
            let sources = vec![input("ExplicitInit", exact)];
            let checked = world.check_with_runtime_baseline(sources.clone(), census);
            let context = checked.accepted_context().expect("genuine already-provided Init import");
            assert_eq!(context.sources(), sources);
            assert_eq!(context.owned_declarations(), &BTreeSet::from([
                Name::from_string("explicitIdentity64"), Name::from_string("extraOwned64"),
            ]));
            assert_eq!(checked.attempt().unwrap().census.is_some(), census);
            assert!(context.runtime_baseline_environment().unwrap().get_const(&Name::from_string("UInt16.not_neg_one")).is_some());
            let source_pair = vec![
                input("Main", "import Init\nimport Sub.Helper\ndef explicitUses : UInt64 := helper64"),
                input("Helper", "import Init\ndef helper64 : UInt64 := 7"),
            ];
            let aliases = vec![LeanSourceAlias { module: "Sub.Helper".into(), source_index: 1 }];
            let pair = world.check_with_aliases(source_pair.clone(), aliases.clone(), census);
            let pair_context = pair.accepted_context().expect("actual artifact plus complete supplied source aliases");
            assert_eq!(pair_context.sources(), source_pair);
            assert_eq!(pair_context.aliases(), aliases);
            assert_eq!(pair_context.owned_declarations(), &BTreeSet::from([
                Name::from_string("explicitUses"), Name::from_string("helper64"),
            ]));
            let no_donation = world.check(vec![input("Later", "import Init\nimport Sub.Helper\ndef later64 : UInt64 := helper64")], census);
            assert!(no_donation.accepted_context().is_none(), "a previous request must not donate source imports");
            let donation_reasons = no_donation.attempt().unwrap().outcomes.iter()
                .flat_map(|row| row.errors.iter().map(|error| error.message.as_str()))
                .collect::<Vec<_>>().join("\n");
            assert!(donation_reasons.contains("unresolved import `Sub.Helper`"), "{donation_reasons}");
            for text in [
                "import InitUnprovided\ndef noFake (x : UInt64) : UInt64 := x",
                "import Init.DefinitelyNotProvided\ndef noPrefix (x : UInt64) : UInt64 := x",
                "import Init\nexample : False := True.intro",
                "import Init\ndef forbiddenMarker := lcAny",
            ] {
                let refused = world.check(vec![input("HostileExplicitImport", text)], census);
                assert!(refused.accepted_context().is_none(), "completed imports must not supply source permission: {text}");
                let reasons = refused.attempt().unwrap().outcomes.iter()
                    .flat_map(|row| row.errors.iter().map(|error| error.message.as_str()))
                    .collect::<Vec<_>>().join("\n");
                if text.contains("False") || text.contains("lcAny") {
                    assert!(!reasons.contains("unresolved import") && !reasons.contains("unknown identifier"), "body refusal required: {reasons}");
                } else {
                    assert!(reasons.contains("unresolved import"), "missing artifact refusal required: {reasons}");
                }
            }
            eprintln!("PINNED_EXPLICIT_INIT census={census}: exact source/whole-owned/alias positives; missing/prefix/donation/False/unsafe refusals");
        }
    }).unwrap().join().unwrap();
}
