// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cross-crate proof composition: the positive fixtures, the close negative
//! twins that must stay refused, and the controls that make each invariant
//! refusal actually fire.

use trust_types::Ty;

use super::*;

/// A well-formed transported unit: the digest is the one the PRODUCER would
/// have published for these exact bytes, computed by the one shared function.
/// A test that wants a corrupted transport moves the bytes and leaves the
/// digest, which is what `a_dependency_whose_bytes_do_not_match_its_published_
/// digest_is_refused` does.
fn unit(name: &str, id: u64, sources: &[&str]) -> ExternProofUnit {
    let sources: Vec<String> = sources.iter().map(|s| (*s).to_string()).collect();
    let kernel_version = clean_kernel::VERSION.to_string();
    let declared_source_digest =
        extern_proof_source_digest(name, id, &kernel_version, &sources).expect("digestible");
    ExternProofUnit {
        id: ExternProofUnitId { crate_name: name.to_string(), stable_crate_id: id },
        kernel_version,
        declared_source_digest,
        sources,
    }
}

fn id(name: &str, id: u64) -> ExternProofUnitId {
    ExternProofUnitId { crate_name: name.to_string(), stable_crate_id: id }
}

/// Compose with no Rust callees — the shape of a crate that has none.
fn compose(
    units: Vec<ExternProofUnit>,
    local: &[&str],
) -> Result<ExternProofComposition, ExternProofRefusal> {
    compose_extern_proof_batch(units, local, &[])
}

/// The dependency of the flagship shape: a PURE SPEC crate — a definition and
/// a theorem about it, nothing callable from Rust.
const SPEC_ISLAND: &str = "def cap (x : UInt64) : UInt64 := if x < 100 then x else 100\n\
                           theorem cap_is_cap (x : UInt64) : cap x = cap x := rfl\n";

/// This crate's own island.
const LOCAL_ISLAND: &str = "def twice (x : UInt64) : UInt64 := x + x\n";

// ---------------------------------------------------------------------------
// POSITIVE
// ---------------------------------------------------------------------------

#[test]
fn a_dependency_theorem_is_composed_and_resolves_crate_qualified() {
    let composition = compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND])
        .expect("a pure spec dependency composes with this crate's island");

    let env =
        composition.ungated_environment().expect("an accepted composition has an environment");
    assert!(
        env.get_const(&Name::from_string("cap_is_cap")).is_some(),
        "the dependency's theorem is registered in the composed environment"
    );
    assert!(
        env.get_const(&Name::from_string("twice")).is_some(),
        "this crate's own declaration is still registered"
    );

    match composition.resolve_cited("spec.cap_is_cap") {
        CitedExternResolution::Dependency { unit, kernel_name } => {
            assert_eq!(unit.crate_name, "spec");
            assert_eq!(kernel_name, Name::from_string("cap_is_cap"));
        }
        other => panic!("crate-qualified citation must resolve, got {other:?}"),
    }

    assert_eq!(
        composition.owner_of(&Name::from_string("cap")),
        Some(DeclarationOrigin::Dependency(id("spec", 7))),
    );
    assert_eq!(
        composition.owner_of(&Name::from_string("twice")),
        Some(DeclarationOrigin::LocalCrate),
    );
    assert_eq!(
        composition.local_island_offset(),
        1,
        "one dependency island precedes the local one"
    );
    assert_eq!(composition.sources().len(), 2);
    assert_eq!(composition.sources()[1], LOCAL_ISLAND, "local islands are the batch's suffix");
    assert_eq!(
        composition.composed_batch().outcomes.len(),
        2,
        "the composed batch is handed back whole, one outcome per island"
    );
}

#[test]
fn zero_units_is_the_crate_local_batch_and_resolves_nothing_to_a_dependency() {
    let composition = compose(Vec::new(), &[LOCAL_ISLAND]).expect("a crate with no units composes");
    assert_eq!(composition.sources(), &[LOCAL_ISLAND.to_string()]);
    assert_eq!(composition.local_island_offset(), 0);
    assert!(composition.units().is_empty());
    assert_eq!(composition.resolve_cited("twice"), CitedExternResolution::LocalLookup);
    assert_eq!(composition.resolve_cited("anything"), CitedExternResolution::LocalLookup);
    assert!(composition.bare_name_is_extern_owned(&Name::from_string("twice")).is_none());
    assert!(composition.standin_disclosures().is_empty(), "this island imports nothing");
    assert_eq!(
        composition.composed_batch().outcomes.len(),
        1,
        "the crate's own batch is still reported per island"
    );
}

#[test]
fn two_dependencies_compose_and_the_order_is_canonical_not_supplied() {
    let alpha = unit("alpha", 1, &["def alpha_one (x : UInt64) : UInt64 := x\n"]);
    let zeta = unit("zeta", 2, &["def zeta_one (x : UInt64) : UInt64 := x\n"]);

    let supplied_one = compose(vec![zeta.clone(), alpha.clone()], &[LOCAL_ISLAND])
        .expect("two independent dependencies compose");
    let supplied_two = compose(vec![alpha, zeta], &[LOCAL_ISLAND]).expect("same, reordered");

    assert_eq!(
        supplied_one.sources(),
        supplied_two.sources(),
        "the composed batch does not depend on the order the units were supplied"
    );
    assert_eq!(
        supplied_one.composition_digest(),
        supplied_two.composition_digest(),
        "neither does its identity"
    );
    assert_eq!(supplied_one.units()[0].id.crate_name, "alpha");
    assert_eq!(supplied_one.units()[1].id.crate_name, "zeta");
}

#[test]
fn a_local_island_calling_a_rust_callee_still_composes_when_a_dependency_is_present() {
    // The capability round 1 landed (Lean-calls-Rust): `trust_check_clean_islands`
    // declares this crate's Rust callees BEFORE its island batch, so this island
    // compiles today. A composition that did not declare them would reject this
    // crate's own islands the moment any dependency carried proof material — and
    // the refusal would say the errors are the author's.
    let callees =
        [RustCallee { clean_name: "inc".to_owned(), params: vec![Ty::u64()], result: Ty::u64() }];
    let local = "def twice_inc (x : UInt64) : UInt64 := inc (inc x)\n";
    let composition =
        compose_extern_proof_batch(vec![unit("spec", 7, &[SPEC_ISLAND])], &[local], &callees)
            .expect("a Lean-calls-Rust island composes with a dependency");
    assert_eq!(
        composition.owner_of(&Name::from_string("twice_inc")),
        Some(DeclarationOrigin::LocalCrate),
    );
    assert_eq!(
        composition.owner_of(&Name::from_string("inc")),
        Some(DeclarationOrigin::LocalRustCallee),
        "the callee is this crate's, and it occupies the bare name in the same namespace"
    );
    assert!(
        composition.bare_name_is_extern_owned(&Name::from_string("inc")).is_none(),
        "a Rust callee is never an extern-owned name"
    );
}

#[test]
fn a_well_founded_recursive_dependency_composes_and_its_generated_helpers_stay_additive() {
    // The shape round 1 landed in library crates (`clean_origin_wf_lib_proof_only.rs`),
    // and the one most likely to break additivity: WF recursion generates
    // auxiliary declarations, and the control compares a per-unit STANDALONE
    // delta against the composed delta. If a generated helper's name depended
    // on batch-wide state the two would differ and this would refuse a
    // perfectly good input.
    let wf = "def cnt (f n : Nat) : Nat := if h : 0 < f then cnt (f - 1) (n + 1) else n\n\
              termination_by f\n\
              theorem cnt_zero (n : Nat) : cnt 0 n = n := rfl\n";
    let composition = compose(vec![unit("spec", 7, &[wf])], &[LOCAL_ISLAND]).expect(
        "a WF-recursive dependency composes; a spurious NonAdditiveComposition here \
                 would be a false refusal of the round-1 library shape",
    );
    assert_eq!(
        composition.owner_of(&Name::from_string("cnt_zero")),
        Some(DeclarationOrigin::Dependency(id("spec", 7))),
    );
    assert_eq!(
        composition.owner_of(&Name::from_string("twice")),
        Some(DeclarationOrigin::LocalCrate),
    );
}

// ---------------------------------------------------------------------------
// NEGATIVE TWINS — each must stay refused
// ---------------------------------------------------------------------------

#[test]
fn a_tampered_dependency_source_is_refused_by_the_local_re_check() {
    // The twin of the positive fixture: one byte of the dependency's proof is
    // changed so the theorem no longer holds. Nothing about the transport
    // changes; the local kernel is what refuses it.
    let tampered = "def cap (x : UInt64) : UInt64 := if x < 100 then x else 100\n\
                    theorem cap_is_cap (x : UInt64) : cap x = x := rfl\n";
    let refusal = compose(vec![unit("spec", 7, &[tampered])], &[LOCAL_ISLAND])
        .expect_err("a dependency whose proof does not check must be refused");
    match &refusal {
        ExternProofRefusal::UnitDoesNotElaborate { id, diagnostics } => {
            assert_eq!(id.crate_name, "spec");
            let first = diagnostics.first().expect("the kernel's own refusal rides along");
            assert_eq!(first.island, 0, "the island index survives");
            assert!(
                first.end > first.start,
                "so do the island-relative offsets the span arithmetic needs: {first:?}"
            );
        }
        other => panic!("expected UnitDoesNotElaborate, got {other:?}"),
    }
    assert!(refusal.headline().contains("spec"), "the refusal names the crate");
    assert!(refusal.note().contains("options:"), "v7/D3: the refusal carries options");
}

#[test]
fn a_tampered_dependency_source_changes_the_unit_digest() {
    // The mutation control for the identity half: the digest is over the exact
    // transported bytes, so a tampered source cannot present the same identity.
    let honest = unit("spec", 7, &[SPEC_ISLAND]);
    let mutated = unit("spec", 7, &[format!("{SPEC_ISLAND}-- one more byte\n").as_str()]);
    let honest_digest = unit_digest(&honest).expect("honest digest");
    let mutated_digest = unit_digest(&mutated).expect("mutated digest");
    assert_ne!(honest_digest, mutated_digest);
    // And each is the digest its own producer published: `unit_digest` and the
    // public producer-side function are one function, so an accepted unit's
    // identity here IS the string the dependency recorded.
    assert_eq!(honest_digest, honest.declared_source_digest);
    assert_eq!(mutated_digest, mutated.declared_source_digest);

    // ... and so does the composition digest, through the per-unit digest.
    let honest = compose(vec![honest], &[LOCAL_ISLAND]).expect("honest");
    let mutated = compose(vec![mutated], &[LOCAL_ISLAND]).expect("mutated");
    assert_ne!(honest.composition_digest(), mutated.composition_digest());
}

#[test]
fn two_dependencies_declaring_the_same_name_are_refused_naming_both() {
    let first = unit("alpha", 1, &["def shared_name (x : UInt64) : UInt64 := x\n"]);
    let second = unit("beta", 2, &["def shared_name (x : UInt64) : UInt64 := x + x\n"]);
    let refusal = compose(vec![first, second], &[LOCAL_ISLAND])
        .expect_err("two dependencies may not both own one declaration name");
    match &refusal {
        ExternProofRefusal::DeclarationCollision { name, first, second } => {
            assert_eq!(name, "shared_name");
            assert_eq!(first, &DeclarationOrigin::Dependency(id("alpha", 1)));
            assert_eq!(second, &DeclarationOrigin::Dependency(id("beta", 2)));
        }
        other => panic!("expected DeclarationCollision, got {other:?}"),
    }
    let headline = refusal.headline();
    assert!(headline.contains("alpha") && headline.contains("beta"));
}

#[test]
fn a_dependency_shadowing_a_local_declaration_is_refused() {
    // THE soundness twin. Without this refusal `ensures result == twice(x)`
    // could be graded against the dependency's `twice` while the rest of the
    // compilation means this crate's — the same family the clause
    // name-capture guard closed for const generics and same-named Rust fns.
    let shadow = unit("spec", 7, &["def twice (x : UInt64) : UInt64 := x\n"]);
    let refusal = compose(vec![shadow], &[LOCAL_ISLAND])
        .expect_err("a dependency may not declare a name this crate declares");
    match &refusal {
        ExternProofRefusal::DeclarationCollision { name, first, second } => {
            assert_eq!(name, "twice");
            assert_eq!(first, &DeclarationOrigin::LocalCrate);
            assert_eq!(second, &DeclarationOrigin::Dependency(id("spec", 7)));
        }
        other => panic!("expected DeclarationCollision, got {other:?}"),
    }
}

#[test]
fn a_dependency_declaration_colliding_with_a_rust_callee_is_refused_by_name() {
    // The callee occupies its bare name in the same kernel namespace as every
    // island declaration, so a dependency's `def inc` and this crate's Rust
    // `fn inc` collide. Refused BY NAME with both origins, rather than
    // discovered as a Clean duplicate-declaration error pointing into a file
    // this crate's author never opened.
    let callees =
        [RustCallee { clean_name: "inc".to_owned(), params: vec![Ty::u64()], result: Ty::u64() }];
    let dep = unit("spec", 7, &["def inc (x : UInt64) : UInt64 := x\n"]);
    let refusal = compose_extern_proof_batch(vec![dep], &[LOCAL_ISLAND], &callees)
        .expect_err("a dependency may not declare a name this crate's Rust callee holds");
    match &refusal {
        ExternProofRefusal::DeclarationCollision { name, first, second } => {
            assert_eq!(name, "inc");
            assert_eq!(first, &DeclarationOrigin::LocalRustCallee);
            assert_eq!(second, &DeclarationOrigin::Dependency(id("spec", 7)));
        }
        other => panic!("expected DeclarationCollision, got {other:?}"),
    }
    assert!(
        refusal.headline().contains("Rust callee"),
        "the headline says which of this crate's name spaces it is: {}",
        refusal.headline()
    );
}

#[test]
fn a_source_file_both_crates_share_by_path_collides_and_the_note_names_that_case() {
    // The `#[path = "../shared/Defs.lean"] clean mod defs;` pattern is the only
    // cross-crate share that works today, and it makes BOTH crates own the same
    // declaration names from byte-identical text. The composition cannot tell
    // that from a shadow — the kernel would refuse the second registration
    // either way — so it refuses, and the note must name the case and the
    // migration rather than offering escapes that do not apply to it.
    let shared = "def shared_cap (x : UInt64) : UInt64 := x\n";
    let refusal = compose(vec![unit("spec", 7, &[shared])], &[shared])
        .expect_err("two crates owning one declaration name is refused however they got it");
    match &refusal {
        ExternProofRefusal::DeclarationCollision { name, .. } => {
            assert_eq!(name, "shared_cap");
        }
        other => panic!("expected DeclarationCollision, got {other:?}"),
    }
    let note = refusal.note();
    assert!(note.contains("#[path"), "the note names the shared-unit case: {note}");
    assert!(
        note.contains("Dropping the citation does not help"),
        "and says why 'stop citing it' is not an escape: {note}"
    );

    // And the measurement that justifies refusing rather than recognizing the
    // two as one declaration: the batch itself will not register byte-identical
    // text twice, so a relaxation would only move the failure from a named
    // refusal to a Clean duplicate-declaration error pointing into a file the
    // author never opened.
    let (mut session, _) = fresh_session(&[]).expect("a fresh session");
    let batch = session.check_all(&[shared, shared]);
    assert!(
        batch.is_rejected(),
        "one declaration name, registered twice, is refused by the batch: {:?}",
        batch.outcomes.iter().map(|outcome| &outcome.errors).collect::<Vec<_>>()
    );
}

#[test]
fn a_dependency_built_by_a_different_kernel_is_refused_before_any_elaboration() {
    let mut skewed = unit("spec", 7, &[SPEC_ISLAND]);
    skewed.kernel_version = format!("{}-not-this-one", clean_kernel::VERSION);
    let refusal = compose(vec![skewed], &[LOCAL_ISLAND])
        .expect_err("kernel skew is refused, never accepted on a matching hash");
    match &refusal {
        ExternProofRefusal::KernelSkew { id, minted, local } => {
            assert_eq!(id.crate_name, "spec");
            assert_ne!(minted, local);
            assert_eq!(local, clean_kernel::VERSION);
        }
        other => panic!("expected KernelSkew, got {other:?}"),
    }
    let note = refusal.note();
    assert!(note.contains(clean_kernel::VERSION), "both kernel strings are named verbatim");
    assert!(note.contains("options:"));
}

#[test]
fn a_stale_transport_that_lost_its_sources_is_refused_rather_than_read_as_empty() {
    // The "stale rmeta" twin: the crate is listed as carrying proof material
    // but the source array is empty. Reading that as "a crate with no
    // declarations" would make every citation into it a plain
    // `TheoremNotFound`, hiding the real cause.
    let refusal = compose(vec![unit("spec", 7, &[])], &[LOCAL_ISLAND])
        .expect_err("a listed unit with no sources is a transport defect, not an empty crate");
    match &refusal {
        ExternProofRefusal::NoSources { id } => assert_eq!(id.crate_name, "spec"),
        other => panic!("expected NoSources, got {other:?}"),
    }
}

#[test]
fn two_crates_of_the_same_name_are_refused_as_ambiguous() {
    let refusal =
        compose(vec![unit("spec", 1, &[SPEC_ISLAND]), unit("spec", 2, &[LOCAL_ISLAND])], &[])
            .expect_err("a citation names a crate, not a version");
    match &refusal {
        ExternProofRefusal::AmbiguousCrateName { crate_name, first, second } => {
            assert_eq!(crate_name, "spec");
            assert_eq!((*first, *second), (1, 2));
        }
        other => panic!("expected AmbiguousCrateName, got {other:?}"),
    }
}

#[test]
fn the_same_unit_supplied_twice_is_refused() {
    let refusal = compose(vec![unit("spec", 7, &[SPEC_ISLAND]); 2], &[LOCAL_ISLAND])
        .expect_err("one crate contributes one unit");
    assert!(matches!(refusal, ExternProofRefusal::DuplicateUnit { .. }), "got {refusal:?}");
}

#[test]
fn a_malformed_unit_is_refused_by_identity_not_by_the_order_it_was_supplied() {
    // Determinism of the refusal itself: two units are both malformed, and the
    // one named must not depend on the order the dependency graph was walked.
    let mut skewed = unit("zeta", 2, &[SPEC_ISLAND]);
    skewed.kernel_version = format!("{}-not-this-one", clean_kernel::VERSION);
    let empty = unit("alpha", 1, &[]);
    let one = compose(vec![skewed.clone(), empty.clone()], &[LOCAL_ISLAND]).expect_err("refused");
    let two = compose(vec![empty, skewed], &[LOCAL_ISLAND]).expect_err("refused");
    assert_eq!(one, two, "the preflight runs in canonical order, so the refusal is the same");
    assert!(matches!(one, ExternProofRefusal::NoSources { .. }), "got {one:?}");
}

#[test]
fn a_rejected_local_batch_is_refused_before_anything_is_composed_on_top_of_it() {
    let refusal = compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &["def : broken\n"])
        .expect_err("a partial local environment mints no positive evidence");
    match &refusal {
        ExternProofRefusal::LocalBatchRejected { diagnostics } => {
            assert!(!diagnostics.is_empty());
        }
        other => panic!("expected LocalBatchRejected, got {other:?}"),
    }
}

#[test]
fn a_local_island_naming_a_dependency_declaration_is_refused_and_the_note_states_that_rule() {
    // A requirement THIS composition adds: the local batch is checked without
    // the dependencies, because the resolve-time mint decides this crate's
    // callable definitions in exactly that environment. The composed batch is
    // header-first and WOULD have accepted this island, so the note must not
    // claim the refusal adds no new requirement — it does, and it is the first
    // thing an author needs told.
    let local = "def uses_dep (x : UInt64) : UInt64 := cap x\n";
    let refusal = compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[local])
        .expect_err("a local island may not name a dependency's declaration");
    match &refusal {
        ExternProofRefusal::LocalBatchRejected { diagnostics } => {
            assert!(!diagnostics.is_empty(), "Clean's own errors ride along");
        }
        other => panic!("expected LocalBatchRejected, got {other:?}"),
    }
    let note = refusal.note();
    assert!(
        note.contains("may therefore not name a dependency's declaration"),
        "the note states the requirement this composition adds: {note}"
    );
    assert!(!note.contains("adds no new requirement"), "and must not claim the opposite: {note}");
    assert!(note.contains("vendor the declaration"), "with a way forward: {note}");

    // The control that makes the claim above measured rather than asserted:
    // the same island composes when the declaration it names is this crate's.
    let vendored = format!("{SPEC_ISLAND}{local}");
    compose(Vec::new(), &[vendored.as_str()])
        .expect("the island is well-formed; only the crate boundary refused it");
}

// ---------------------------------------------------------------------------
// THE CONSERVATIVE-EXTENSION CONTROLS
//
// Each refusal below is reached by a fixture. The two invariant refusals are
// also exercised directly against hand-built inputs, because a refusal that
// no test can make fire is not a control — and the elaborator this build pins
// may simply not produce the leak that would trip it through a source batch.
// ---------------------------------------------------------------------------

#[test]
fn the_additivity_control_fires_on_a_name_that_no_part_owned() {
    let expected: BTreeSet<Name> = ["a", "b"].into_iter().map(Name::from_string).collect();
    let composed: BTreeSet<Name> = ["a", "b", "Dep.a"].into_iter().map(Name::from_string).collect();
    let refusal = check_name_additivity(&expected, &composed).expect_err("not additive");
    match &refusal {
        ExternProofRefusal::NonAdditiveComposition { unexpected, missing } => {
            assert_eq!(unexpected, &vec!["Dep.a".to_string()]);
            assert!(missing.is_empty());
        }
        other => panic!("expected NonAdditiveComposition, got {other:?}"),
    }
    assert!(refusal.note().contains("Dep.a"), "the note names it: {}", refusal.note());
}

#[test]
fn the_additivity_control_fires_on_a_part_name_the_composition_lost() {
    // The re-homing direction: a dependency that opens a `namespace` and never
    // closes it registers this crate's `twice` as `Dep.twice`, so the name a
    // part owned is MISSING from the composition and an unowned one appeared.
    let expected: BTreeSet<Name> = ["twice", "cap"].into_iter().map(Name::from_string).collect();
    let composed: BTreeSet<Name> =
        ["Dep.twice", "cap"].into_iter().map(Name::from_string).collect();
    let refusal = check_name_additivity(&expected, &composed).expect_err("not additive");
    match &refusal {
        ExternProofRefusal::NonAdditiveComposition { unexpected, missing } => {
            assert_eq!(unexpected, &vec!["Dep.twice".to_string()]);
            assert_eq!(missing, &vec!["twice".to_string()]);
        }
        other => panic!("expected NonAdditiveComposition, got {other:?}"),
    }
}

#[test]
fn the_payload_control_names_every_declaration_whose_kernel_term_moved() {
    // The half a name-set check cannot do: same names, different kernel
    // payloads. This is what a leaked `open`, a notation declaration or a
    // `set_option` in another part would produce, in either direction.
    let alone: BTreeMap<Name, String> = [
        (Name::from_string("twice"), "digest-A".to_string()),
        (Name::from_string("thrice"), "digest-B".to_string()),
    ]
    .into_iter()
    .collect();
    let mut composed = alone.clone();
    assert!(rebound_names(&alone, &composed).is_empty(), "identical payloads are not rebound");

    composed.insert(Name::from_string("twice"), "digest-A-prime".to_string());
    assert_eq!(rebound_names(&alone, &composed), vec!["twice".to_string()]);

    composed.remove(&Name::from_string("thrice"));
    assert_eq!(
        rebound_names(&alone, &composed),
        vec!["thrice".to_string(), "twice".to_string()],
        "a payload that cannot be read back at all counts as moved, and the list is sorted"
    );

    // And the refusal each direction produces names the crate it is about.
    let local = ExternProofRefusal::LocalDeclarationsRebound { names: vec!["twice".to_string()] };
    assert!(local.note().contains("twice"));
    let dependency = ExternProofRefusal::DependencyDeclarationsRebound {
        id: id("spec", 7),
        names: vec!["cap_is_cap".to_string()],
    };
    assert!(dependency.headline().contains("spec"), "{}", dependency.headline());
    assert!(
        dependency.note().contains("re-checks"),
        "the note says why the dependency direction matters: {}",
        dependency.note()
    );
}

#[test]
fn a_dependency_that_opens_a_block_it_never_closes_cannot_rehome_this_crate() {
    // A dependency island that opens a `namespace` and does not close it would
    // otherwise register THIS crate's `twice` as `Dep.twice` — the local
    // declaration keeps its spelling in source and changes its kernel identity,
    // which is exactly what the mint's local-only environment would not see.
    //
    // MEASURED on this build's elaborator (2026-09-18): the composition is
    // ACCEPTED, because the batch checker does not leak an unclosed block past
    // the island that opened it — the dependency's own `dep_one` is registered
    // as `Dep.dep_one` and this crate's `twice` is untouched. So this fixture
    // pins the arm that actually runs; it does NOT reach the invariant's
    // refusal, which is why the two controls above exercise that refusal
    // directly instead of through a source batch.
    let leaky = unit("dep", 3, &["namespace Dep\ndef dep_one (x : UInt64) : UInt64 := x\n"]);
    let composition = compose(vec![leaky], &[LOCAL_ISLAND])
        .expect("the unclosed block does not reach this crate");
    let env = composition.ungated_environment().expect("accepted");
    assert!(
        env.get_const(&Name::from_string("twice")).is_some(),
        "this crate's declaration is in the COMPOSED environment under its own name"
    );
    assert!(
        env.get_const(&Name::from_string("Dep.twice")).is_none(),
        "and was not re-homed under the dependency's namespace"
    );
    assert!(
        env.get_const(&Name::from_string("Dep.dep_one")).is_some()
            && env.get_const(&Name::from_string("dep_one")).is_none(),
        "the block did apply inside the dependency's own island"
    );
}

#[test]
fn composition_is_additive_in_the_composed_environment_for_the_positive_fixture() {
    // Asserted against the COMPOSED environment, not against the per-part
    // deltas: `owner_of` answers from the deltas and could not report what
    // composition did.
    let composition = compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND])
        .expect("the positive fixture composes");
    let env = composition.ungated_environment().expect("accepted");
    for name in ["cap", "cap_is_cap", "twice"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "`{name}` is in the composed environment"
        );
    }
    let alone = compose(Vec::new(), &[LOCAL_ISLAND]).expect("the crate alone composes");
    let alone_env = alone.ungated_environment().expect("accepted");
    assert!(
        alone_env.get_const(&Name::from_string("cap")).is_none(),
        "and `cap` is there only because the dependency put it there"
    );
}

#[test]
fn composing_the_same_inputs_twice_is_byte_identical() {
    // The invariant compares digests over kernel payloads. If anything
    // reachable from `ConstantInfo`/`Expr` were interning- or
    // generation-dependent, `LocalDeclarationsRebound` would fire on run-to-run
    // noise rather than on a real rebinding.
    let one = compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND]).expect("first");
    let two = compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND]).expect("second");
    assert_eq!(one.composition_digest(), two.composition_digest());
    assert_eq!(one.unit_digest(0), two.unit_digest(0));

    let names: BTreeSet<Name> =
        ["cap", "cap_is_cap", "twice"].into_iter().map(Name::from_string).collect();
    let first = payload_digests(one.ungated_environment().expect("accepted"), &names)
        .expect("payloads read back");
    let second = payload_digests(two.ungated_environment().expect("accepted"), &names)
        .expect("payloads read back");
    assert_eq!(first, second, "the payload digests are stable across runs");
}

#[test]
fn two_unit_source_partitions_that_flatten_alike_have_different_identities() {
    // `composition_digest` folds the PER-UNIT digests, so "crate A owns both
    // islands" and "A owns one, B owns the other" are different compositions
    // even though the concatenated source vector is the same.
    let a = "def p_one (x : UInt64) : UInt64 := x\n";
    let b = "def p_two (x : UInt64) : UInt64 := x\n";
    let together = compose(vec![unit("alpha", 1, &[a, b])], &[LOCAL_ISLAND]).expect("one unit");
    let split = compose(vec![unit("alpha", 1, &[a]), unit("beta", 2, &[b])], &[LOCAL_ISLAND])
        .expect("two units");
    assert_eq!(together.sources(), split.sources(), "the same bytes in the same order");
    assert_ne!(
        together.composition_digest(),
        split.composition_digest(),
        "but not the same composition"
    );
}

// ---------------------------------------------------------------------------
// THE CITATION-SPELLING RULE
// ---------------------------------------------------------------------------

#[test]
fn a_bare_name_that_only_a_dependency_owns_is_refused_with_the_qualified_spelling() {
    let composition = compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND])
        .expect("the positive fixture composes");
    match composition.resolve_cited("cap_is_cap") {
        CitedExternResolution::BareDependencyName { unit, qualified_spelling } => {
            assert_eq!(unit.crate_name, "spec");
            assert_eq!(qualified_spelling, "spec.cap_is_cap");
        }
        other => panic!("a bare dependency name must be refused, got {other:?}"),
    }
}

#[test]
fn a_local_name_still_resolves_locally_when_a_dependency_is_present() {
    let composition = compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND])
        .expect("the positive fixture composes");
    assert_eq!(composition.resolve_cited("twice"), CitedExternResolution::LocalLookup);
    assert_eq!(
        composition.owner_of(&Name::from_string("twice")),
        Some(DeclarationOrigin::LocalCrate),
        "and it is local because this crate declared it, not by default"
    );
    // A name nothing owns is also the local lookup's business — it is where
    // `TheoremNotFound` is reported, and this function must not pre-empt it.
    assert_eq!(composition.resolve_cited("no_such_name"), CitedExternResolution::LocalLookup);
    assert!(composition.bare_name_is_extern_owned(&Name::from_string("no_such_name")).is_none());
}

#[test]
fn a_qualified_citation_into_a_dependency_that_lacks_the_declaration_is_refused() {
    let composition = compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND])
        .expect("the positive fixture composes");
    match composition.resolve_cited("spec.not_there") {
        CitedExternResolution::NotInDependency { unit, kernel_name } => {
            assert_eq!(unit.crate_name, "spec");
            assert_eq!(kernel_name, Name::from_string("not_there"));
        }
        other => panic!("expected NotInDependency, got {other:?}"),
    }
}

#[test]
fn a_local_dotted_name_whose_head_is_a_dependency_that_owns_the_tail_is_ambiguous_not_ranked() {
    // The name-capture twin at the SPELLING level: this crate declares
    // `spec.cap_is_cap` inside its own `namespace spec`, and the dependency
    // `spec` owns `cap_is_cap`. Two readings exist; neither may win silently.
    let local = "namespace spec\ndef cap_is_cap (x : UInt64) : UInt64 := x\nend spec\n";
    let composition =
        compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[local]).expect("no kernel-name collision");
    match composition.resolve_cited("spec.cap_is_cap") {
        CitedExternResolution::AmbiguousWithNonDependency { unit, spelling } => {
            assert_eq!(unit.crate_name, "spec");
            assert_eq!(spelling, "spec.cap_is_cap");
        }
        other => panic!("expected AmbiguousWithNonDependency, got {other:?}"),
    }
}

#[test]
fn a_dependency_declaring_into_a_namespace_of_its_own_crate_name_is_not_a_local_lookup() {
    // THE CAPTURE TWIN R1 EXISTS FOR, in the shape a Lean author writes by
    // habit: crate `spec`'s island wraps its declarations in `namespace spec`,
    // so `spec` owns the kernel name `spec.cap_is_cap` and owns no bare
    // `cap_is_cap` at all.
    //
    // The spelling `spec.cap_is_cap` therefore has two readings and BOTH are
    // the dependency's — "crate `spec`, declaration `cap_is_cap`" (which does
    // not exist) and "the declaration `spec.cap_is_cap`" (which does). Before
    // this was fixed, `resolves_without_unit` asked the COMPOSED environment,
    // which physically contains the dependency's own declarations, so the
    // second reading answered and the citation came back `LocalLookup` — the
    // arm whose doc says "not a dependency citation". A seam that honoured
    // that answer would have looked the name up in the composed environment,
    // found the dependency's theorem and discharged the contract with no
    // dependency binding and no unit digest in the payload.
    let island = "namespace spec\n\
                  def cap (x : UInt64) : UInt64 := if x < 100 then x else 100\n\
                  theorem cap_is_cap (x : UInt64) : cap x = cap x := rfl\n\
                  end spec\n";
    let composition = compose(vec![unit("spec", 7, &[island])], &[LOCAL_ISLAND]).expect("composes");
    match composition.resolve_cited("spec.cap_is_cap") {
        CitedExternResolution::DottedNameOwnedByDependency {
            head,
            declaring,
            spelling,
            ratified_spelling,
            head_owns_tail,
        } => {
            assert_eq!(head.crate_name, "spec");
            assert_eq!(declaring.crate_name, "spec");
            assert_eq!(spelling, "spec.cap_is_cap");
            assert_eq!(ratified_spelling, "spec.spec.cap_is_cap");
            assert!(!head_owns_tail, "`spec` owns `spec.cap_is_cap`, not a bare `cap_is_cap`");
        }
        other => panic!("a dependency-owned dotted name must never be LocalLookup, got {other:?}"),
    }
    let note = composition.resolve_cited("spec.cap_is_cap").note().expect("a refusal has a note");
    assert!(note.contains("options:"), "v7/D3: {note}");
    assert!(note.contains("spec.spec.cap_is_cap"), "and it offers the spelling: {note}");
    // The offered option is not a dead end: the R1 spelling resolves.
    assert!(
        matches!(
            composition.resolve_cited("spec.spec.cap_is_cap"),
            CitedExternResolution::Dependency { ref unit, ref kernel_name }
                if unit.crate_name == "spec" && kernel_name.to_string() == "spec.cap_is_cap"
        ),
        "the option the refusal offers must be one an author can take, got {:?}",
        composition.resolve_cited("spec.spec.cap_is_cap")
    );
}

#[test]
fn a_dependency_declaring_into_another_dependencys_crate_name_refuses_naming_both() {
    // The second shape, and the one the brief names: two dependencies where
    // `beta`'s island declares into a `namespace` called `alpha` while `alpha`
    // is also a dependency that owns a bare `cap_is_cap`. `DeclarationCollision`
    // cannot see it — `cap_is_cap` and `alpha.cap_is_cap` are different kernel
    // names — so the refusal has to come from the citation resolver, and it has
    // to name the crate that actually declares the name the author wrote.
    let beta_island = "namespace alpha\n\
                       theorem cap_is_cap (x : UInt64) : x = x := rfl\n\
                       end alpha\n";
    let composition = compose(
        vec![unit("alpha", 7, &[SPEC_ISLAND]), unit("beta", 8, &[beta_island])],
        &[LOCAL_ISLAND],
    )
    .expect("two different kernel names do not collide");
    match composition.resolve_cited("alpha.cap_is_cap") {
        CitedExternResolution::DottedNameOwnedByDependency {
            head,
            declaring,
            ratified_spelling,
            head_owns_tail,
            ..
        } => {
            assert_eq!(head.crate_name, "alpha", "the head the author wrote");
            assert_eq!(declaring.crate_name, "beta", "the crate that declares the whole name");
            assert_eq!(ratified_spelling, "beta.alpha.cap_is_cap");
            assert!(head_owns_tail, "`alpha` really does own a bare `cap_is_cap` as well");
        }
        other => panic!("`beta` must not answer for a citation addressed to `alpha`: {other:?}"),
    }
    let note = composition.resolve_cited("alpha.cap_is_cap").note().expect("a refusal has a note");
    assert!(note.contains("`alpha`") && note.contains("`beta`"), "both are named: {note}");
    assert!(note.contains("options:"), "v7/D3: {note}");
}

#[test]
fn a_dependency_named_like_a_prelude_namespace_does_not_capture_a_prelude_citation() {
    // A prelude theorem is citable today (`grade_cited_theorem_against_goal`
    // is a plain `env.get_const`). `Nat` is a legal Rust crate name, so a
    // workspace crate called `Nat` that carries proof material must not make
    // `Nat.<prelude theorem>` re-read as a citation into that crate — that
    // would break a citation that compiles today and blame the wrong thing.
    let composition = compose(vec![unit("Nat", 9, &[SPEC_ISLAND])], &[LOCAL_ISLAND])
        .expect("a crate may be named `Nat`");
    let env = composition.ungated_environment().expect("accepted");
    // MEASURED on this build's kernel (2026-09-18): the prelude owns all of
    // `Nat.add_comm`, `Nat.succ`, `Nat.le`, `Nat.le.refl` and `Nat.zero`.
    assert!(
        env.get_const(&Name::from_string("Nat.add_comm")).is_some(),
        "the premise of this test: the prelude owns `Nat.add_comm`"
    );
    assert_eq!(
        composition.resolve_cited("Nat.add_comm"),
        CitedExternResolution::LocalLookup,
        "`Nat.add_comm` is the prelude's, and the crate named `Nat` does not own `add_comm`"
    );
    // The other direction still holds: the crate named `Nat` is citable.
    assert!(matches!(
        composition.resolve_cited("Nat.cap_is_cap"),
        CitedExternResolution::Dependency { .. }
    ));
}

// ---------------------------------------------------------------------------
// THE CLAUSE-IDENTIFIER GATE
//
// A clause's ordinary identifiers are resolved at a different seam from the
// `by` citation name, and that seam looks a bare name up in the environment
// directly. These pin what the seam must ask before it does.
// ---------------------------------------------------------------------------

#[test]
fn a_bare_clause_identifier_only_a_dependency_owns_is_refused_with_a_note() {
    let composition = compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND])
        .expect("the positive fixture composes");
    match composition.clause_identifier("cap") {
        ClauseIdentifierDisposition::ExternOwned { unit, qualified_spelling } => {
            assert_eq!(unit.crate_name, "spec");
            assert_eq!(qualified_spelling, "spec.cap");
            let note = composition.clause_identifier("cap").note().expect("a refusal has a note");
            assert!(note.contains("options:"), "v7/D3: {note}");
            assert!(
                note.contains("proof position"),
                "and it names the one cross-crate surface: {note}"
            );
        }
        other => panic!("a dependency may not answer for a bare clause identifier, got {other:?}"),
    }
}

#[test]
fn a_clause_identifier_this_crate_owns_is_left_to_the_crate_local_rule() {
    let callees =
        [RustCallee { clean_name: "inc".to_owned(), params: vec![Ty::u64()], result: Ty::u64() }];
    let composition = compose_extern_proof_batch(
        vec![unit("spec", 7, &[SPEC_ISLAND])],
        &[LOCAL_ISLAND],
        &callees,
    )
    .expect("composes");
    for name in ["twice", "inc", "nothing_owns_this"] {
        assert_eq!(
            composition.clause_identifier(name),
            ClauseIdentifierDisposition::LocalOrPrelude,
            "`{name}` is not a dependency's"
        );
        assert!(composition.clause_identifier(name).note().is_none());
    }
}

// ---------------------------------------------------------------------------
// DISCLOSURE
// ---------------------------------------------------------------------------

#[test]
fn a_dependency_import_served_by_the_prelude_standin_is_disclosed_to_the_dependent() {
    // The dependent's author never opened the dependency's island, so this is
    // the only way the substitution reaches them. Harvested from the COMPOSED
    // batch — the run whose environment was accepted.
    let with_import = unit("spec", 7, &[format!("import Lean\n{SPEC_ISLAND}").as_str()]);
    let composition =
        compose(vec![with_import], &[LOCAL_ISLAND]).expect("a stand-in-served import composes");
    let disclosures = composition.standin_disclosures();
    let dependency = disclosures
        .iter()
        .find(|entry| entry.origin == DeclarationOrigin::Dependency(id("spec", 7)))
        .expect("the dependency's stand-in import is disclosed with its crate");
    assert_eq!(dependency.import.module, "Lean");
    assert_eq!(dependency.island, 0, "and with the composed-batch island it was written in");
    assert!(dependency.import.disclosure().contains("stand-in"));
    assert!(dependency.import.options().contains("options:"));
}

#[test]
fn this_crates_own_standin_import_is_disclosed_too() {
    // The zero-unit path is the one every ordinary crate takes, and the local
    // crate's own disclosures are what a green resting on `import Lean`
    // rests on. They must not be dropped on the way through this API.
    let local = format!("import Lean\n{LOCAL_ISLAND}");
    let composition = compose(Vec::new(), &[local.as_str()]).expect("composes");
    let disclosures = composition.standin_disclosures();
    assert!(
        disclosures
            .iter()
            .any(|entry| entry.origin == DeclarationOrigin::LocalCrate
                && entry.import.module == "Lean"),
        "the compiled crate's own stand-in imports reach the caller: {disclosures:?}"
    );
}

// ---------------------------------------------------------------------------
// TRANSPORT AGREEMENT — the digest the dependency published, over the bytes
// that arrived
// ---------------------------------------------------------------------------

#[test]
fn a_dependency_whose_bytes_do_not_match_its_published_digest_is_refused() {
    // The close negative twin of the positive fixture, at the TRANSPORT seam
    // rather than the kernel: the bytes are perfectly good Clean — they
    // elaborate, they prove what they say — but they are not the bytes `spec`
    // published a digest for. Refused before anything is elaborated, because
    // the alternative is a contract proved from a declaration the dependency
    // does not have, with no diagnostic that says so.
    let mut corrupted = unit("spec", 7, &[SPEC_ISLAND]);
    corrupted.sources = vec![format!("{SPEC_ISLAND}def extra (x : UInt64) : UInt64 := x\n")];
    let refusal = compose(vec![corrupted], &[LOCAL_ISLAND])
        .expect_err("bytes that do not match the published digest must be refused");
    match &refusal {
        ExternProofRefusal::TransportDigestMismatch { id, declared, recomputed } => {
            assert_eq!(id.crate_name, "spec");
            assert_ne!(declared, recomputed, "both digests are reported, and they differ");
            assert_eq!(declared.len(), 64, "canonical-JSON SHA-256, hex");
        }
        other => panic!("expected TransportDigestMismatch, got {other:?}"),
    }
    assert!(refusal.headline().contains("spec"), "the refusal names the crate");
    assert!(refusal.note().contains("options:"), "v7/D3: the refusal carries options");
    assert!(
        refusal.note().contains("not what makes them"),
        "and it says the digest is identity, not authority: {}",
        refusal.note()
    );
}

#[test]
fn a_well_formed_transport_reaches_the_kernel_and_its_digest_is_its_identity() {
    // The positive control for the twin above: the SAME shape carrying the
    // digest its producer would have published composes, and the identity the
    // composition reports is exactly that published string.
    let honest = unit("spec", 7, &[SPEC_ISLAND]);
    let published = honest.declared_source_digest.clone();
    let composition = compose(vec![honest], &[LOCAL_ISLAND]).expect("a well-formed unit composes");
    assert_eq!(
        composition.unit_digest(0),
        Some(published.as_str()),
        "an accepted unit's identity IS the digest its producer published"
    );
}

#[test]
fn kernel_skew_is_reported_as_skew_although_the_digest_moves_with_it() {
    // An ordering control. The digest covers the recorded kernel version, so a
    // skewed unit would also fail a digest check computed under OUR version.
    // The author's problem is the skew, so skew is what the refusal must say —
    // and the digest is recomputed under the unit's OWN recorded version
    // precisely so the two questions stay separate.
    let mut skewed = unit("spec", 7, &[SPEC_ISLAND]);
    skewed.kernel_version = format!("{}-not-this-one", clean_kernel::VERSION);
    skewed.declared_source_digest = extern_proof_source_digest(
        &skewed.id.crate_name,
        skewed.id.stable_crate_id,
        &skewed.kernel_version,
        &skewed.sources,
    )
    .expect("digestible");
    let refusal = compose(vec![skewed], &[LOCAL_ISLAND]).expect_err("skew is refused");
    assert!(
        matches!(refusal, ExternProofRefusal::KernelSkew { .. }),
        "a skewed unit is refused as SKEW, not as a corrupted transport: {refusal:?}"
    );
}

// ---------------------------------------------------------------------------
// RULING R1 — the citation spelling, and the refusal of every other one
// ---------------------------------------------------------------------------

#[test]
fn the_rust_path_spelling_is_refused_and_names_the_dotted_one() {
    let composition =
        compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND]).expect("composes");
    match composition.resolve_cited("spec::cap_is_cap") {
        CitedExternResolution::RustPathSpelling { spelling, ratified_spelling } => {
            assert_eq!(spelling, "spec::cap_is_cap");
            assert_eq!(ratified_spelling, "spec.cap_is_cap");
        }
        other => panic!("the Rust path spelling must be refused, got {other:?}"),
    }
    let note = composition
        .resolve_cited("spec::cap_is_cap")
        .note()
        .expect("a refused spelling carries a note");
    assert!(note.contains("spec.cap_is_cap"), "and names the ratified spelling: {note}");
    assert!(note.contains("options:"), "v7/D3");
}

#[test]
fn the_rust_path_spelling_is_refused_even_with_no_dependency_of_that_name() {
    // The rule is about the SPELLING, not about the dependency graph: a
    // refusal that appeared only when a matching crate happened to be present
    // would teach that `::` is fine until it is not.
    let composition = compose(Vec::new(), &[LOCAL_ISLAND]).expect("composes");
    assert!(
        matches!(
            composition.resolve_cited("nowhere::thing"),
            CitedExternResolution::RustPathSpelling { .. }
        ),
        "the spelling is refused with zero units"
    );
}

#[test]
fn every_refusing_citation_arm_carries_a_note_and_the_accepting_ones_do_not() {
    let composition =
        compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND]).expect("composes");
    assert!(composition.resolve_cited("spec.cap_is_cap").note().is_none(), "Dependency accepts");
    assert!(composition.resolve_cited("twice").note().is_none(), "LocalLookup accepts");
    for spelling in ["cap_is_cap", "spec.nope", "spec::cap_is_cap"] {
        let note = composition
            .resolve_cited(spelling)
            .note()
            .unwrap_or_else(|| panic!("`{spelling}` is refused, so it owes a note"));
        assert!(note.contains("options:"), "v7/D3 for `{spelling}`: {note}");
    }
    // The two arms the fixture above cannot reach, each from the composition
    // that makes it fire: a dependency-owned dotted name, and the spelling that
    // also resolves without any dependency.
    let namespaced = "namespace spec\ntheorem cap_is_cap (x : UInt64) : x = x := rfl\nend spec\n";
    let owned = compose(vec![unit("spec", 7, &[namespaced])], &[LOCAL_ISLAND]).expect("composes");
    let note = owned
        .resolve_cited("spec.cap_is_cap")
        .note()
        .expect("DottedNameOwnedByDependency is refused, so it owes a note");
    assert!(note.contains("options:"), "v7/D3: {note}");
    let local_namespace = "namespace spec\ndef cap_is_cap (x : UInt64) : UInt64 := x\nend spec\n";
    let ambiguous = compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[local_namespace])
        .expect("no kernel-name collision");
    let note = ambiguous
        .resolve_cited("spec.cap_is_cap")
        .note()
        .expect("AmbiguousWithNonDependency is refused, so it owes a note");
    assert!(note.contains("options:"), "v7/D3: {note}");
}

// ---------------------------------------------------------------------------
// §3.2 — the constructor the COMPILER uses, measured rather than assumed
// ---------------------------------------------------------------------------

/// The session `trust_check_clean_islands` builds: `CleanIslandSession::new()`
/// over this crate's islands, with no dependency anywhere.
fn verify_pass_style_session(local: &[&str]) -> CleanIslandSession {
    let mut session = CleanIslandSession::new();
    let batch = session.check_all(local);
    assert!(!batch.is_rejected(), "the verify-pass-style batch must be accepted: {batch:?}");
    assert!(!session.is_tainted());
    session
}

#[test]
fn the_verify_pass_session_agrees_with_the_composition_about_this_crate_zero_units() {
    // MEASUREMENT (2026-09-19), settling residual §3.2 of the design note:
    // every batch in this module starts from `new_for_source_batch()` (PProd
    // prologue materialized BEFORE the baseline) while the verify pass starts
    // from `new()` (PProd materialized lazily by an `import`). Whether that
    // difference reaches this crate's own DECLARATIONS was unmeasured, and the
    // wiring plan depends on the answer: the composed environment may only
    // grade a goal built in the compiler's session if the two agree about
    // every declaration that goal can mention.
    let composition = compose(Vec::new(), &[LOCAL_ISLAND]).expect("composes");
    let session = verify_pass_style_session(&[LOCAL_ISLAND]);
    let env = session.environment().expect("an accepted batch has an environment");
    composition
        .reconcile_with_local_environment(env)
        .expect("the two constructors agree about this crate's declarations");
}

#[test]
fn the_verify_pass_session_agrees_with_the_composition_with_a_dependency_present() {
    // The case that matters: the composed environment carries a dependency's
    // declarations, and this crate's own must still mean in it what they mean
    // in the session the compiler built without any dependency at all.
    let composition =
        compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND]).expect("composes");
    let session = verify_pass_style_session(&[LOCAL_ISLAND]);
    let env = session.environment().expect("an accepted batch has an environment");
    composition
        .reconcile_with_local_environment(env)
        .expect("a dependency's presence does not move this crate's declarations");
}

#[test]
fn a_session_built_from_different_local_sources_is_refused_by_the_reconciliation() {
    // The mutation control: a refusal nothing can make fire is not a control.
    // Here the compiler's session ran DIFFERENT local sources — the shape a
    // seam bug would produce by composing over one batch and grading in
    // another — and the reconciliation names the declaration.
    let composition = compose(Vec::new(), &[LOCAL_ISLAND]).expect("composes");
    let other = "def twice (x : UInt64) : UInt64 := x + x + x\n";
    let session = verify_pass_style_session(&[other]);
    let env = session.environment().expect("an accepted batch has an environment");
    let refusal = composition
        .reconcile_with_local_environment(env)
        .expect_err("a different body for the same name must be refused");
    match &refusal {
        ExternProofRefusal::LocalSessionDisagrees { missing, rebound } => {
            assert!(missing.is_empty(), "the name is present in both: {missing:?}");
            assert_eq!(rebound, &vec!["twice".to_string()]);
        }
        other => panic!("expected LocalSessionDisagrees, got {other:?}"),
    }
    assert!(refusal.note().contains("options:"), "v7/D3");
    assert!(
        refusal.note().contains("fail-closed"),
        "and it says what happens meanwhile: {}",
        refusal.note()
    );
}

#[test]
fn a_session_missing_this_crates_declaration_is_refused_by_the_reconciliation() {
    // The other half of the same control: absent, not merely different.
    let composition = compose(Vec::new(), &[LOCAL_ISLAND]).expect("composes");
    let session = verify_pass_style_session(&["def unrelated (x : UInt64) : UInt64 := x\n"]);
    let env = session.environment().expect("an accepted batch has an environment");
    let refusal = composition
        .reconcile_with_local_environment(env)
        .expect_err("a missing declaration must be refused");
    match &refusal {
        ExternProofRefusal::LocalSessionDisagrees { missing, rebound } => {
            assert_eq!(missing, &vec!["twice".to_string()]);
            assert!(rebound.is_empty());
        }
        other => panic!("expected LocalSessionDisagrees, got {other:?}"),
    }
}

#[test]
fn a_dependency_name_the_compilers_own_session_already_binds_is_refused() {
    // THE CAPTURE THE `local_owned` PASS CANNOT SEE. The constructor's
    // `DeclarationCollision` compares a unit's names against this crate's
    // ISLAND declarations and the Rust callees its caller passed. The session
    // the compiler hands to this function carries more than that: Rust callees
    // it declared itself, and the E6 program functions `admit_program_
    // functions` admits AFTER the composition was built. A dependency that
    // owns one of those names would have its definition bound under it in the
    // composed environment, and a goal built in the compiler's session that
    // mentions the name would be graded against the dependency's body.
    //
    // Here the compiler's session binds `cap` — the name the dependency `spec`
    // owns — beside this crate's own `twice`, which is exactly the shape a
    // program-function admission produces. `twice` agrees in both environments,
    // so the `local_owned` pass is SILENT: this test isolates the new check.
    let composition =
        compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND]).expect("composes");
    let admitted = "def cap (x : UInt64) : UInt64 := x\n";
    let session = verify_pass_style_session(&[LOCAL_ISLAND, admitted]);
    let env = session.environment().expect("an accepted batch has an environment");
    let refusal = composition
        .reconcile_with_local_environment(env)
        .expect_err("a dependency may not answer for a name this compilation already bound");
    match &refusal {
        ExternProofRefusal::DependencyNameBoundLocally { id, names } => {
            assert_eq!(id.crate_name, "spec");
            assert_eq!(names, &vec!["cap".to_string()]);
        }
        other => panic!("expected DependencyNameBoundLocally, got {other:?}"),
    }
    let note = refusal.note();
    assert!(note.contains("options:"), "v7/D3: {note}");
    assert!(note.contains("fail-closed"), "and it says what happens meanwhile: {note}");
    assert!(refusal.headline().contains("spec"), "the headline names the crate");
}

#[test]
fn the_capture_check_is_silent_when_no_dependency_name_is_bound_locally() {
    // The other half of the control: the check must not fire on the positive
    // fixture, or it would fail-close every compilation that has a dependency.
    let composition =
        compose(vec![unit("spec", 7, &[SPEC_ISLAND])], &[LOCAL_ISLAND]).expect("composes");
    let session =
        verify_pass_style_session(&[LOCAL_ISLAND, "def other (x : UInt64) : UInt64 := x\n"]);
    let env = session.environment().expect("an accepted batch has an environment");
    composition
        .reconcile_with_local_environment(env)
        .expect("a local name no dependency owns is not a capture");
}
