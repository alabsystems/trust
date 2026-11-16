// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Synthetic selection-policy controls for completed enum markers. These
//! hand-built metadata values are not compiler-layout evidence or proof input.
//! Real compiler fixtures separately check which layouts the producer records.

use super::*;

const ENUM_NAME: &str = "fixture[1111]::Choice::<u8>";

fn bare_marker(name: &str) -> TrustTy {
    TrustTy::Datatype { name: name.into(), variants: Vec::new() }
}

fn synthetic_complete_enum(name: &str) -> TrustTy {
    let mut definition = TrustTy::adt_enum(
        name,
        vec![trust_types::VariantDef {
            name: "Only".into(),
            discriminant: 0,
            fields: vec![("0".into(), TrustTy::Int { width: 8, signed: false })],
        }],
    );
    let TrustTy::Adt { adt_kind, faithful_enum_repr, enum_layout, .. } = &mut definition else {
        panic!("adt_enum must construct an Adt");
    };
    *adt_kind = Some(trust_types::AdtKind::Enum);
    *faithful_enum_repr = Some(None);
    *enum_layout = Some(Box::new(trust_types::EnumLayoutInfo {
        encoding: trust_types::EnumTagEncodingInfo::Untagged,
        size: 1,
        align: 1,
        variant_field_offsets: vec![vec![0]],
    }));
    definition
}

fn collector_with_definition(definition: TrustTy) -> DatatypeDefCollector {
    // Direct insertion deliberately permits malformed test cases; production
    // insertion validates names before storing a completed definition.
    let mut collector = DatatypeDefCollector::default();
    collector.defs.insert(ENUM_NAME.into(), definition);
    collector
}

fn assert_lookup(
    collector: &DatatypeDefCollector,
    marker: &TrustTy,
    expected_marker: &TrustTy,
    expected_result: bool,
) {
    let before = (
        collector.defs.clone(),
        collector.in_progress.clone(),
        collector.refused.clone(),
        marker.clone(),
        expected_marker.clone(),
    );
    assert_eq!(
        completed_enum_marker_has_layout(collector, marker, expected_marker),
        expected_result
    );
    assert_eq!(collector.defs, before.0, "lookup must not expand or replace table entries");
    assert_eq!(collector.in_progress, before.1);
    assert_eq!(collector.refused, before.2);
    assert_eq!(*marker, before.3, "the supplied marker must stay bare");
    assert_eq!(*expected_marker, before.4);
}

#[test]
fn completed_enum_lookup_succeeds_without_mutation_or_expansion() {
    let mut collector = collector_with_definition(synthetic_complete_enum(ENUM_NAME));
    // Other incomplete/refused nodes do not change this exact node's status.
    collector.in_progress.insert("fixture::OtherInProgress".into());
    collector.refused.insert("fixture::OtherRefused".into());
    let marker = bare_marker(ENUM_NAME);
    assert_lookup(&collector, &marker, &marker, true);
    assert!(matches!(&marker, TrustTy::Datatype { variants, .. } if variants.is_empty()));
}

#[test]
fn missing_definition_is_refused() {
    let marker = bare_marker(ENUM_NAME);
    assert_lookup(&DatatypeDefCollector::default(), &marker, &marker, false);
}

#[test]
fn present_but_in_progress_definition_is_refused() {
    let mut collector = collector_with_definition(synthetic_complete_enum(ENUM_NAME));
    collector.in_progress.insert(ENUM_NAME.into());
    let marker = bare_marker(ENUM_NAME);
    assert_lookup(&collector, &marker, &marker, false);
}

#[test]
fn present_but_permanently_refused_definition_is_refused() {
    let mut collector = collector_with_definition(synthetic_complete_enum(ENUM_NAME));
    collector.refused.insert(ENUM_NAME.into());
    let marker = bare_marker(ENUM_NAME);
    assert_lookup(&collector, &marker, &marker, false);
}

#[test]
fn matching_definition_stored_under_wrong_key_is_not_searched_for() {
    let mut collector = DatatypeDefCollector::default();
    collector.defs.insert("fixture::WrongKey".into(), synthetic_complete_enum(ENUM_NAME));
    let marker = bare_marker(ENUM_NAME);
    assert_lookup(&collector, &marker, &marker, false);
}

#[test]
fn matching_key_with_mismatched_definition_name_is_refused() {
    let collector = collector_with_definition(synthetic_complete_enum("fixture::Other"));
    let marker = bare_marker(ENUM_NAME);
    assert_lookup(&collector, &marker, &marker, false);
}

#[test]
fn bare_marker_table_entry_is_not_a_completed_definition() {
    let marker = bare_marker(ENUM_NAME);
    let collector = collector_with_definition(marker.clone());
    assert_lookup(&collector, &marker, &marker, false);
}

#[test]
fn logical_datatype_definition_is_not_physical_enum_metadata() {
    let collector = collector_with_definition(TrustTy::Datatype {
        name: ENUM_NAME.into(),
        variants: vec![("Only".into(), vec![("0".into(), TrustTy::Bool)])],
    });
    let marker = bare_marker(ENUM_NAME);
    assert_lookup(&collector, &marker, &marker, false);
}

#[test]
fn struct_union_and_missing_kind_are_refused_despite_enum_metadata() {
    for kind in [Some(trust_types::AdtKind::Struct), Some(trust_types::AdtKind::Union), None] {
        let mut definition = synthetic_complete_enum(ENUM_NAME);
        let TrustTy::Adt { adt_kind, .. } = &mut definition else {
            panic!("synthetic enum must be an Adt");
        };
        // Keep all other enum metadata: only the required kind gate can reject
        // this deliberately contradictory synthetic entry.
        *adt_kind = kind;
        let collector = collector_with_definition(definition);
        let marker = bare_marker(ENUM_NAME);
        assert_lookup(&collector, &marker, &marker, false);
    }
}

#[test]
fn enum_without_faithful_repr_is_refused() {
    let mut definition = synthetic_complete_enum(ENUM_NAME);
    let TrustTy::Adt { faithful_enum_repr, .. } = &mut definition else {
        panic!("synthetic enum must be an Adt");
    };
    *faithful_enum_repr = None;
    let collector = collector_with_definition(definition);
    let marker = bare_marker(ENUM_NAME);
    assert_lookup(&collector, &marker, &marker, false);
}

#[test]
fn enum_without_concrete_layout_is_refused() {
    let mut definition = synthetic_complete_enum(ENUM_NAME);
    let TrustTy::Adt { enum_layout, .. } = &mut definition else {
        panic!("synthetic enum must be an Adt");
    };
    *enum_layout = None;
    let collector = collector_with_definition(definition);
    let marker = bare_marker(ENUM_NAME);
    assert_lookup(&collector, &marker, &marker, false);
}

#[test]
fn enum_without_variants_is_refused_even_with_fields_and_layout() {
    let mut definition = synthetic_complete_enum(ENUM_NAME);
    let TrustTy::Adt { variants, fields, .. } = &mut definition else {
        panic!("synthetic enum must be an Adt");
    };
    variants.make_mut().clear();
    // Nonempty fields keep the generic definition validator satisfied, so this
    // specifically exercises the completed-enum helper's variant requirement.
    assert!(!fields.is_empty());
    let collector = collector_with_definition(definition);
    let marker = bare_marker(ENUM_NAME);
    assert_lookup(&collector, &marker, &marker, false);
}

#[test]
fn compiler_expected_marker_requires_exact_generic_crate_and_full_name() {
    for other_name in [
        "fixture[1111]::Choice::<u16>",
        "fixture[2222]::Choice::<u8>",
        "fixture[1111]::Choice",
        "fixture[1111]::Choice::<u8>::Nested",
        "other::fixture[1111]::Choice::<u8>",
    ] {
        let mut collector = collector_with_definition(synthetic_complete_enum(ENUM_NAME));
        collector.defs.insert(other_name.into(), synthetic_complete_enum(other_name));
        let marker = bare_marker(ENUM_NAME);
        let other_marker = bare_marker(other_name);
        // Each name independently has a complete entry. Neither direction may
        // equate them by prefix, short name, generic erasure, or crate erasure.
        assert_lookup(&collector, &marker, &other_marker, false);
        assert_lookup(&collector, &other_marker, &marker, false);
        assert_lookup(&collector, &other_marker, &other_marker, true);
    }
}

#[test]
fn expanded_datatype_operand_is_not_a_bare_marker() {
    let collector = collector_with_definition(synthetic_complete_enum(ENUM_NAME));
    let expanded = TrustTy::Datatype {
        name: ENUM_NAME.into(),
        variants: vec![("Only".into(), vec![("0".into(), TrustTy::Bool)])],
    };
    // Even exact equality with the expected operand does not waive bareness.
    assert_lookup(&collector, &expanded, &expanded, false);
}

#[test]
fn inline_adt_operand_is_not_a_marker_even_when_identical_to_expected() {
    let definition = synthetic_complete_enum(ENUM_NAME);
    let collector = collector_with_definition(definition.clone());
    assert_lookup(&collector, &definition, &definition, false);
}

#[test]
fn bare_marker_does_not_equal_an_inline_expected_definition() {
    let definition = synthetic_complete_enum(ENUM_NAME);
    let collector = collector_with_definition(definition.clone());
    let marker = bare_marker(ENUM_NAME);
    assert_lookup(&collector, &marker, &definition, false);
}
