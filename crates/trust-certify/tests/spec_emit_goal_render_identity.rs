// Trust (v6/D1): byte-identity control for the `targo trust spec --emit clean`
// artifact renderer — trust-certify half (the grade call's own inputs).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

//! ACCEPTANCE CONTROL for the spec-emit increment: pin that the artifact
//! renderer applied to the elaborated `Expr` equals the kernel `Display` of
//! the goal the grade call received.
//!
//! Structure of the argument, since `kernel_discharge_ensures_citation` does
//! not (yet) return its goal:
//!
//! * the grade call computes its goal as
//!   `elaborate_ensures(clause, params, self_fn, facets)` — that is the
//!   expression `cert_meter::grade` re-typechecks the cited proof term
//!   against (see `kernel_discharge_ensures_citation`);
//! * the artifact writer (`trust_spec_emit.rs`) computes
//!   `elaborate_ensures(clause, params, self_fn, facets).map(|g| g.to_string())`
//!   with THE SAME argument values, in the same process;
//! * so published-render == Display(goal-the-grade-received) exactly when the
//!   shared elaboration is deterministic on those inputs. This file drives a
//!   REAL kernel environment through the real grade call and pins: (1) the
//!   verdict is `Certified` (the pinned goal is one the kernel actually
//!   proved, not a fabrication), (2) the render is byte-stable across
//!   repeated elaboration, (3) in the refusal direction the verdict's
//!   `ClauseOutsideFragment` reason is byte-identical to the renderer's
//!   error — both sides demonstrably ran the one shared elaboration path.

use trust_certify::clean_island::{
    CitationVerdict, CleanIslandSession, admit_certified_island_definition,
    kernel_discharge_ensures_citation,
};
use trust_spec_elab::FacetTable;

const ISLAND: &str = "def self_id (x : UInt64) : UInt64 := x\n\n\
     theorem t : forall (x : UInt64), Nat.le (UInt64.toNat x) (UInt64.toNat x) := \
         fun x => Nat.le.refl (UInt64.toNat x)";

const CLAUSE: &str = "result >= x";
const PARAMS: &[(&str, &str)] = &[("x", "u64")];
const SELF_FN: &str = "self_id";

/// The artifact renderer, verbatim from `trust_spec_emit.rs`.
fn artifact_render(facets: &FacetTable) -> Result<String, String> {
    trust_spec_elab::elaborate_ensures(CLAUSE, PARAMS, SELF_FN, facets).map(|goal| goal.to_string())
}

fn kernel_checked_setup() -> (CleanIslandSession, FacetTable) {
    let mut session = CleanIslandSession::new();
    let outcome = session.check(ISLAND);
    assert!(!outcome.is_rejected(), "setup island must kernel-check: {:?}", outcome.errors);
    let env = session.environment().expect("untainted session has an environment").clone();
    let mut facets = FacetTable::new();
    admit_certified_island_definition(&env, SELF_FN, &mut facets)
        .expect("self_id is a strict island definition and must admit");
    (session, facets)
}

#[test]
fn the_artifact_render_pins_the_goal_the_certified_grade_call_received() {
    let (session, facets) = kernel_checked_setup();
    let env = session.environment().expect("environment");

    // (1) The REAL grade call, on the REAL kernel environment: Certified.
    // Whatever goal it graded, it was elaborate_ensures(CLAUSE, PARAMS,
    // SELF_FN, &facets) — the same call the renderer below makes.
    let verdict = kernel_discharge_ensures_citation(env, "t", CLAUSE, PARAMS, SELF_FN, &facets);
    assert!(
        matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
        "the control theorem must discharge so the pinned goal is kernel-proven: {verdict:?}"
    );

    // (2) The artifact render is byte-stable across repeated elaboration —
    // the property that makes it equal the Display of the grade call's goal.
    let rendered = artifact_render(&facets).expect("the graded clause elaborates");
    for round in 0..16 {
        assert_eq!(
            rendered,
            artifact_render(&facets).expect("repeat elaboration"),
            "round {round}: the published render drifted from the graded goal"
        );
    }

    // (3) Pin the exact Clean text. This is the byte payload `targo trust
    // spec --emit clean` prints for this obligation; a change here is a
    // change to what the kernel is asked to prove and must be REVIEWED, not
    // absorbed.
    assert_eq!(
        rendered, "(u : UInt64) -> Nat.le (UInt64.toNat u) (UInt64.toNat (self_id u))",
        "the emitted Clean goal text changed; if intentional, re-pin after review"
    );
}

#[test]
fn refusal_direction_verdict_reason_and_artifact_elab_error_are_byte_identical() {
    // No admission for `self_id` here: `result` cannot be substituted, so the
    // grade call refuses with ClauseOutsideFragment{reason} and the artifact
    // writer records `elab_error`. Both must be the SAME bytes — the direct
    // observable that verdict lane and emit lane ran the one shared
    // elaboration on the same inputs.
    let mut session = CleanIslandSession::new();
    let outcome = session.check(ISLAND);
    assert!(!outcome.is_rejected(), "setup island: {:?}", outcome.errors);
    let env = session.environment().expect("environment");
    let empty_facets = FacetTable::new();

    let verdict =
        kernel_discharge_ensures_citation(env, "t", CLAUSE, PARAMS, SELF_FN, &empty_facets);
    let CitationVerdict::ClauseOutsideFragment { reason } = verdict else {
        panic!("an unadmitted `result` substitution must fail closed: {verdict:?}");
    };
    let elab_error =
        artifact_render(&empty_facets).expect_err("the artifact path must refuse identically");
    assert_eq!(
        reason, elab_error,
        "the verdict's refusal and the artifact's elab_error diverged — the emit path is no \
         longer running the elaboration the grade call ran"
    );
}

#[test]
fn a_failed_citation_still_gets_its_goal_rendered() {
    // v7/D3 / the ruling's debugging case: the goal must be printable exactly
    // when the citation FAILS. An absent theorem name refuses the discharge,
    // but the goal itself elaborates and renders — the artifact row carries
    // verdict "theorem-not-found" WITH the goal text.
    let (session, facets) = kernel_checked_setup();
    let env = session.environment().expect("environment");
    let verdict =
        kernel_discharge_ensures_citation(env, "t_absent", CLAUSE, PARAMS, SELF_FN, &facets);
    assert!(
        matches!(verdict, CitationVerdict::TheoremNotFound),
        "an absent citation fails closed: {verdict:?}"
    );
    let rendered = artifact_render(&facets)
        .expect("the goal renders even though the citation missed — that is the instrument");
    assert!(rendered.contains("UInt64"), "a real proposition, not a placeholder: {rendered}");
}
