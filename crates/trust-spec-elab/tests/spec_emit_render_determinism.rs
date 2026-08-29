// Trust (v6/D1): byte-identity control for the `targo trust spec --emit clean`
// artifact renderer — trust-spec-elab half.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

//! The compiler-side artifact writer
//! (`compiler/rustc_mir_transform/src/trust_spec_emit.rs`) renders the goal it
//! publishes by calling `elaborate_ensures` with THE SAME argument values the
//! discharge lane's grade call (`kernel_discharge_ensures_citation`) passed,
//! in the same process, and rendering the returned kernel `Expr` with its own
//! `Display`. That render is byte-identical to the Display of the goal the
//! grade call received **iff `elaborate_ensures` is deterministic**: both
//! calls are the same pure function on the same inputs. These tests pin that
//! property shut for the shapes the emitter meets, so the published text can
//! never drift from the proposition the kernel was asked to close.

use trust_spec_elab::{FacetTable, elaborate_ensures, elaborate_goal_typed_with_facets};

/// The artifact renderer, verbatim: what `trust_spec_emit.rs` applies to the
/// elaborated goal (`Ok` arm) or records as `elab_error` (`Err` arm).
fn artifact_render(
    clause: &str,
    params: &[(&str, &str)],
    self_fn_name: &str,
    facets: &FacetTable,
) -> Result<String, String> {
    elaborate_ensures(clause, params, self_fn_name, facets).map(|goal| goal.to_string())
}

#[test]
fn result_free_ensures_render_is_deterministic_across_repeated_elaboration() {
    let facets = FacetTable::new();
    let params: &[(&str, &str)] = &[("x", "u64"), ("y", "u64")];
    let first = artifact_render("x + y >= x", params, "self_fn", &facets)
        .expect("a result-free in-fragment clause elaborates");
    for round in 0..16 {
        let again = artifact_render("x + y >= x", params, "self_fn", &facets)
            .expect("repeat elaboration stays in-fragment");
        assert_eq!(first, again, "round {round}: the render drifted between elaborations");
    }
    // The render is the kernel Display of a closed proposition (fresh binder
    // names), not a restatement of the surface text: the encoded operation
    // and ordering carrier must be present.
    assert!(
        first.contains("UInt64.add") && first.contains("Nat.le"),
        "goal carries the kernel encoding: {first}"
    );
}

#[test]
fn quantified_clause_render_is_deterministic() {
    let facets = FacetTable::new();
    let params: &[(&str, &str)] = &[("n", "u64")];
    let clause = "forall i: u64, i <= i";
    let Ok(first) = artifact_render(clause, params, "self_fn", &facets) else {
        // If the E3 fragment ever narrows, this control must fail loudly
        // rather than silently pin nothing.
        panic!("the E3 quantifier fragment refused a reflexive closed clause");
    };
    for _ in 0..16 {
        assert_eq!(
            first,
            artifact_render(clause, params, "self_fn", &facets).expect("repeat"),
            "quantified render drifted"
        );
    }
}

#[test]
fn out_of_fragment_refusal_reason_is_deterministic_too() {
    // The emitter publishes the `Err` reason as `elab_error`, and the verdict
    // lane surfaces the SAME `elaborate_ensures` error as
    // `ClauseOutsideFragment { reason }` — so the refusal text must be as
    // stable as the success render.
    let facets = FacetTable::new();
    let params: &[(&str, &str)] = &[("x", "u64")];
    // `result` without an admitted self-function is the canonical fail-closed
    // refusal on the ensures path.
    let first = artifact_render("result >= x", params, "unadmitted_fn", &facets)
        .expect_err("`result` without an admission must fail closed");
    for _ in 0..16 {
        assert_eq!(
            first,
            artifact_render("result >= x", params, "unadmitted_fn", &facets)
                .expect_err("repeat refusal"),
            "refusal reason drifted"
        );
    }
    assert!(first.contains("unadmitted_fn"), "the refusal names the function: {first}");
}

#[test]
fn typed_goal_elaboration_display_is_deterministic() {
    // `elaborate_goal_typed_with_facets` is the other consumer named by the
    // audit (the citation sweep path); pin its Display stability on the same
    // grounds.
    let facets = FacetTable::new();
    let bindings: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
    let first = elaborate_goal_typed_with_facets("a <= a + b", bindings, &facets)
        .expect("in-fragment typed goal elaborates")
        .to_string();
    for _ in 0..16 {
        assert_eq!(
            first,
            elaborate_goal_typed_with_facets("a <= a + b", bindings, &facets)
                .expect("repeat")
                .to_string(),
            "typed goal render drifted"
        );
    }
}
