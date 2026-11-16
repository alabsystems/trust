// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 28 — a refusal states the reason the declaration was actually
//! refused for, and a `def` that was never a candidate says so.**
//!
//! # The two gaps this control closes (both measured 2026-09-16)
//!
//! 1. **The swallowed admission error.** `rustc_resolve::trust_clean_mint`
//!    mapped every `admit_certified_island_definition` error onto a fabricated
//!    `KernelStatus::Parsed`, so `def sfst (a : Int64) (b : Int64) : Int64 := a`
//!    — accepted by the batch and reported "kernel-checked" by the same build —
//!    was described at its call site as a merely `parsed` symbol, with the
//!    advice to remove a `sorry` it did not contain. Fail-closed, and a v7/D3
//!    defect: no option offered could fix the situation.
//!    [`MintRefusal::CertifiedAdmissionRefused`] carries the admitter's reason
//!    verbatim instead.
//! 2. **The silent namespace.** A `def` inside `namespace Geo … end Geo` is
//!    registered as `Geo.area`, is never a mint candidate, and its Rust call
//!    site got a bare `E0425`/`E0433`. [`nested_island_definitions`] finds such
//!    declarations so the call site can be told, with the wrapper that works.
//!
//! Like control 14, every declaration here goes through the REAL island
//! pipeline (`CleanIslandSession::check_all`) — a hand-built environment would
//! prove nothing about what the elaborator registers.
//!
//! # What it does NOT prove
//!
//! Nothing about spans, error codes or the resolver hook that attaches these
//! notes — those are `tests/ui/trust/clean_origin_refusal_real_reason.rs` and
//! `clean_origin_namespaced_def_*.rs`. And nothing here mints or un-mints: both
//! additions are wording for a refusal that was already fail-closed.

use clean_kernel::Environment;
use trust_clean_origin::{
    MintRefusal, decide_mint, leading_type_variable_binders, nested_island_definitions,
};

struct Island {
    env: Environment,
    registered: Vec<String>,
}

fn island(source: &str) -> Island {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    Island {
        env: session.environment().expect("an untainted session has an environment").clone(),
        registered: batch.outcomes[0].registered.clone(),
    }
}

fn admit(island: &Island, name: &str) -> Result<trust_spec_elab::Admission, String> {
    let mut facets = trust_spec_elab::FacetTable::new();
    trust_certify::clean_island::admit_certified_island_definition_for_name(
        &island.env,
        &clean_kernel::Name::from_string(name),
        &mut facets,
    )
}

/// The measured repro (probe-call 04a). The batch ACCEPTS the declaration, the
/// certified re-admission refuses it, and the note says what the admitter said
/// — not that the symbol is `parsed`, and not that it holds a `sorry`.
#[test]
fn an_accepted_declaration_the_admitter_refuses_is_reported_with_the_admitters_reason() {
    let island = island("def sfst (a : Int64) (b : Int64) : Int64 := a\n");
    assert!(island.registered.contains(&"sfst".to_string()), "{:?}", island.registered);

    let reason = admit(&island, "sfst").expect_err(
        "PREMISE MOVED: `sfst` over `Int64` now passes the certified admission. The mint \
         site's refusal arm is then unreachable for this repro — find another declaration \
         the batch accepts and the admitter refuses, or retire this control with evidence.",
    );

    let constant = island.env.get_const(&clean_kernel::Name::from_string("sfst")).unwrap();
    let carrier = trust_clean_carrier::carrier_signature_for(&constant.type_)
        .err()
        .map(|refusal| refusal.to_string());
    // The ROOT cause, which neither refusal states: the Clean prelude declares
    // no `Int64`, so the name was auto-bound as a type VARIABLE and `sfst` is a
    // projection polymorphic over an arbitrary type. The kernel type shows it.
    let type_variable_binders = leading_type_variable_binders(&constant.type_);
    assert!(
        type_variable_binders >= 1,
        "PREMISE MOVED: `sfst`'s kernel type no longer begins with a type-variable binder \
         ({:?}) — if the Clean prelude now declares `Int64`, this repro needs another \
         undeclared type name",
        constant.type_
    );
    let note = MintRefusal::CertifiedAdmissionRefused {
        name: "sfst".to_owned(),
        reason: reason.clone(),
        carrier: carrier.clone(),
        type_variable_binders,
    }
    .note();

    assert!(note.contains("LIKELY CAUSE") && note.contains("auto-bound-implicit"), "{note}");
    assert!(note.contains(&reason), "the admitter's reason must appear VERBATIM:\n{note}");
    if let Some(carrier) = &carrier {
        assert!(note.contains(carrier), "the carrier refusal must appear VERBATIM:\n{note}");
    }
    // The old story, which was false for this declaration.
    assert!(!note.contains("`parsed`"), "{note}");
    assert!(!note.contains("remove any `sorry`"), "{note}");
    // v7/D3: options, and more than one — one option is an ultimatum.
    let options = note.split_once("options:\n").expect("the note must list options").1;
    assert!(options.matches("\n- ").count() + 1 >= 2, "{note}");
    assert!(options.starts_with("- "), "{note}");
}

/// CLOSE NEGATIVE TWIN: the same shape at a width that carries. It admits, the
/// mint decision grants, and the refusal variant is never constructed — the
/// new arm did not become a second way to refuse a good declaration.
#[test]
fn the_same_declaration_at_a_carried_width_still_admits_and_still_mints() {
    let island = island("def ufst (a : UInt64) (b : UInt64) : UInt64 := a\n");
    let admission = admit(&island, "ufst").expect("a UInt64 projection must admit");
    let constant = island.env.get_const(&clean_kernel::Name::from_string("ufst")).unwrap();
    let carrier = trust_clean_carrier::carrier_signature_for(&constant.type_)
        .map(|signature| signature.result().clone());
    decide_mint("ufst", admission.status(), carrier).expect("and the mint decision must grant");
    // And a monomorphic signature shows no type variable, so the LIKELY CAUSE
    // paragraph can never be attached to a declaration like this one.
    assert_eq!(leading_type_variable_binders(&constant.type_), 0);
    let note = MintRefusal::CertifiedAdmissionRefused {
        name: "ufst".to_owned(),
        reason: "some other reason".to_owned(),
        carrier: None,
        type_variable_binders: 0,
    }
    .note();
    assert!(!note.contains("LIKELY CAUSE"), "{note}");
}

/// CONTROL: the variant the fabricated status used to reach is unchanged. A
/// status that really is `Parsed` still gets the `parsed` story — the fix moved
/// one caller off that arm, it did not reword the arm.
#[test]
fn a_status_that_really_is_parsed_keeps_its_own_note() {
    let island = island("def ufst (a : UInt64) (b : UInt64) : UInt64 := a\n");
    let constant = island.env.get_const(&clean_kernel::Name::from_string("ufst")).unwrap();
    let carrier = trust_clean_carrier::carrier_signature_for(&constant.type_)
        .map(|signature| signature.result().clone());
    let refusal = decide_mint("ufst", &trust_symbols::KernelStatus::Parsed, carrier)
        .expect_err("a parsed status must never mint");
    assert!(matches!(refusal, MintRefusal::NotKernelChecked { .. }), "{refusal:?}");
    assert!(refusal.note().contains("`parsed`"), "{}", refusal.note());
}

const NAMESPACED: &str = "\
namespace Geo
def area (w : UInt64) (h : UInt64) : UInt64 := w * h
theorem area_comm (w h : UInt64) : area w h = area w h := rfl
end Geo
def area_w (w : UInt64) (h : UInt64) : UInt64 := Geo.area w h
";

/// The measured repro (probe-call 24/24b/24c): `Geo.area` is registered, is a
/// `Definition`, and is not a top-level `def` of the island — so it is reported
/// as nested, with the namespace the call site walked through.
#[test]
fn a_def_inside_a_namespace_is_reported_as_nested_with_the_wrapper_option() {
    let island = island(NAMESPACED);
    let nested = nested_island_definitions(&island.env, &island.registered, &["area_w"]);

    let [MintRefusal::NotTopLevel { name, clean_name, namespace }] = nested.as_slice() else {
        panic!("expected exactly `Geo.area`; registered {:?}, got {nested:?}", island.registered);
    };
    assert_eq!((name.as_str(), clean_name.as_str()), ("area", "Geo.area"));
    assert_eq!(namespace.as_deref(), Some("Geo"));

    let note = nested[0].note();
    assert!(note.contains("A Clean namespace is not a Rust module"), "{note}");
    assert!(note.contains("`Geo::area`"), "the path the user tried must be named: {note}");
    // The option measured to work (probe 24c): a top-level wrapper.
    assert!(note.contains(":= Geo.area <the same arguments>"), "{note}");
    let options = note.split_once("options:\n").expect("the note must list options").1;
    assert!(options.matches("\n- ").count() + 1 >= 2, "{note}");
}

/// CLOSE NEGATIVE TWINS, one island each way a registered name is NOT a nested
/// `def` the author could wrap:
///
/// * a top-level `def` (it is a mint candidate; its refusals are its own);
/// * a THEOREM inside the namespace (`Geo.area_comm` above — not callable from
///   any position, so a note promising a wrapper would be false);
/// * whatever a recursive top-level `def` makes the elaborator register under
///   ITS name — a name qualified by a `Definition` is that definition's helper,
///   not a namespace member.
#[test]
fn top_level_defs_theorems_and_a_definitions_own_auxiliaries_are_not_nested_defs() {
    let island_ = island(NAMESPACED);
    let nested = nested_island_definitions(&island_.env, &island_.registered, &["area_w"]);
    assert!(
        nested.iter().all(|refusal| refusal.name() != "area_w" && refusal.name() != "area_comm"),
        "{nested:?}"
    );

    let recursive = island(
        "def sum_to (n : Nat) : Nat :=\n  match n with\n  | 0 => 0\n  | k + 1 => (k + 1) + sum_to k\n",
    );
    let nested = nested_island_definitions(&recursive.env, &recursive.registered, &["sum_to"]);
    assert!(
        nested.is_empty(),
        "an auxiliary of `sum_to` was reported as a nested `def`: {nested:?} (registered {:?})",
        recursive.registered
    );
}
