// trust_vcgen/spec_parser.rs: Generate VCs from FunctionSpec attributes
//
// Bridges the FunctionSpec (string-based #[requires], #[ensures], #[invariant]
// attributes) on VerifiableFunction to verification conditions. Uses the
// spec expression parser in trust-types to convert spec strings to Formulas.
//
// This complements contracts.rs which processes the Vec<Contract> field.
// spec_parser.rs processes the FunctionSpec field, which is populated by
// trust-mir-extract from parsed #[requires("...")] / #[ensures("...")] attributes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    ContractKind, Formula, FunctionSpec, VcKind, VerifiableFunction, VerificationCondition,
    parse_spec_expr,
};

/// Generate verification conditions from a function's `FunctionSpec` field.
///
/// For each spec clause:
/// - `requires` clauses become `Precondition` VCs
/// - `ensures` clauses become `Postcondition` VCs
/// - `invariant` clauses become `Assertion` VCs
///
/// Each VC's formula is the *negation* of the spec formula (we check for
/// violations: if UNSAT, the spec holds; if SAT, the model is a counterexample).
///
/// Unparseable strings become non-refutable `UnsupportedMir` rows. They are
/// never silently skipped and never sent to a solver as if they described a
/// concrete program counterexample.
pub(crate) fn generate_spec_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let spec = &func.spec;
    if spec.is_empty() {
        return Vec::new();
    }

    let contract_metadata = Some(spec.to_contract_metadata());
    let mut vcs = Vec::new();
    // MIR extraction mirrors every raw source contract into `FunctionSpec`.
    // Consume each raw row at most once so the compatibility lane does not
    // manufacture a second obligation for the same authored clause.  A
    // spec-only clause, or an excess duplicate beyond the raw-row
    // cardinality, remains visible here.
    let mut claimed_raw_contracts = Vec::new();

    // Preconditions: #[requires("...")]
    //
    // Trust: At the function's *definition* site, a precondition is an
    // assumption (callees rely on it), not a proof obligation. Caller-side
    // precondition checks are emitted by `modular.rs` at each call site.
    // Here we still emit one Precondition VC per parseable requires clause
    // for downstream reporting/tooling, but encode the proof obligation as
    // `Bool(false)` so the verifier discharges it trivially. The clause
    // remains available as a hypothesis on other VCs through
    // `func.preconditions`.
    for expr in &spec.requires {
        if claim_raw_contract_mirror(func, ContractKind::Requires, expr, &mut claimed_raw_contracts)
        {
            continue;
        }
        if let Some(formula) = parse_spec_expr(expr) {
            if crate::contracts::formula_uses_unmodeled_machine_arithmetic_in_function(
                func, &formula,
            ) {
                vcs.push(crate::contracts::spec_unverifiable_vc(
                    func,
                    func.span.clone(),
                    "requires uses unmodeled fixed-width machine arithmetic",
                    expr,
                    contract_metadata,
                ));
                continue;
            }
            vcs.push(VerificationCondition {
                kind: VcKind::Precondition { callee: func.name.clone() },
                function: func.name.as_str().into(),
                location: func.span.clone(),
                formula: Formula::Bool(false),
                contract_metadata,
            });
        } else {
            vcs.push(crate::contracts::spec_unverifiable_vc(
                func,
                func.span.clone(),
                "unparseable requires",
                expr,
                contract_metadata,
            ));
        }
    }

    // Postconditions: #[ensures("...")]
    for expr in &spec.ensures {
        if claim_raw_contract_mirror(func, ContractKind::Ensures, expr, &mut claimed_raw_contracts)
        {
            continue;
        }
        if let Some(formula) = parse_spec_expr(expr) {
            if crate::contracts::formula_uses_unmodeled_machine_arithmetic_in_function(
                func, &formula,
            ) {
                vcs.push(crate::contracts::spec_unverifiable_vc(
                    func,
                    func.span.clone(),
                    "ensures uses unmodeled fixed-width machine arithmetic",
                    expr,
                    contract_metadata,
                ));
                continue;
            }
            // SOUNDNESS: an ensures whose predicate references synthetic
            // spec-model terms (`{base}_discr`/`{base}_value*`/`{base}_sign`/
            // `.__trust_ok_i`) is under-constrained — nothing grounds those
            // names, so `Not(formula)` is satisfiable by havoc regardless of
            // the body (a minted counterexample, not a program trace). Emit
            // the fail-closed NON-REFUTABLE Unknown shape instead; see
            // `contracts::spec_model_ungrounded_vc`.
            let ungrounded = crate::contracts::ungrounded_spec_model_vars(&formula);
            if !ungrounded.is_empty() {
                vcs.push(crate::contracts::spec_model_ungrounded_vc(
                    func,
                    func.span.clone(),
                    expr,
                    &ungrounded,
                    contract_metadata,
                ));
                continue;
            }
            vcs.push(VerificationCondition {
                kind: VcKind::Postcondition,
                function: func.name.as_str().into(),
                location: func.span.clone(),
                formula: Formula::Not(Box::new(formula)),
                contract_metadata,
            });
        } else {
            vcs.push(crate::contracts::spec_ensures_unparseable_vc(func, func.span.clone(), expr));
        }
    }

    // Invariants: #[invariant("...")]
    for expr in &spec.invariants {
        if claim_raw_contract_mirror(
            func,
            ContractKind::Invariant,
            expr,
            &mut claimed_raw_contracts,
        ) {
            continue;
        }
        if let Some(formula) = parse_spec_expr(expr) {
            if crate::contracts::formula_uses_unmodeled_machine_arithmetic_in_function(
                func, &formula,
            ) {
                vcs.push(crate::contracts::spec_unverifiable_vc(
                    func,
                    func.span.clone(),
                    "invariant uses unmodeled fixed-width machine arithmetic",
                    expr,
                    contract_metadata,
                ));
                continue;
            }
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion { message: format!("invariant: {expr}") },
                function: func.name.as_str().into(),
                location: func.span.clone(),
                formula: Formula::Not(Box::new(formula)),
                contract_metadata,
            });
        } else {
            vcs.push(crate::contracts::spec_unverifiable_vc(
                func,
                func.span.clone(),
                "unparseable invariant",
                expr,
                contract_metadata,
            ));
        }
    }

    vcs
}

/// Claim one canonical raw-contract row that owns this exact compatibility
/// `FunctionSpec` clause. MIR extraction derives FunctionSpec text directly
/// from those rows, so emitting a second row would double-count one source
/// clause. Ownership is deliberately textual (after the producer's prefix and
/// boundary-whitespace normalization), not merely parsed-formula equality: an
/// independently supplied clause that happens to parse to the same AST still
/// has distinct source provenance and must remain visible. Claims are
/// cardinality-aware, so a divergent, spec-only, or excess duplicate clause
/// also remains visible.
fn claim_raw_contract_mirror(
    func: &VerifiableFunction,
    spec_kind: ContractKind,
    expression: &str,
    claimed: &mut Vec<usize>,
) -> bool {
    let matching_index = func.contracts.iter().enumerate().find_map(|(index, contract)| {
        if claimed.contains(&index) {
            return None;
        }
        let kind_matches = match spec_kind {
            ContractKind::Invariant => {
                matches!(contract.kind, ContractKind::Invariant | ContractKind::LoopInvariant)
            }
            _ => contract.kind == spec_kind,
        };
        if !kind_matches {
            return None;
        }
        let body = contract
            .body
            .strip_prefix(crate::contracts::LOWERED_CONTRACT_PREFIX)
            .unwrap_or(&contract.body)
            .trim();
        (body == expression.trim()).then_some(index)
    });
    if let Some(index) = matching_index {
        claimed.push(index);
        true
    } else {
        false
    }
}

/// Check if a FunctionSpec would produce any VCs (without actually generating them).
///
/// Useful for pre-filtering functions before full VC generation.
#[must_use]
pub fn has_spec_vcs(spec: &FunctionSpec) -> bool {
    // Every authored clause produces either an ordinary VC or an explicit
    // fail-closed unsupported row.
    !spec.is_empty()
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BlockId, Contract, Formula, LocalDecl, Sort, SourceSpan, Terminator, Ty,
        VerifiableBody,
    };

    use super::*;

    fn spec_test_function(spec: FunctionSpec) -> VerifiableFunction {
        VerifiableFunction {
            name: "spec_fn".to_string(),
            def_path: "test::spec_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("y".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec,
        }
    }

    #[test]
    fn test_empty_spec_produces_no_vcs() {
        let func = spec_test_function(FunctionSpec::default());
        let vcs = generate_spec_vcs(&func);
        assert!(vcs.is_empty());
    }

    #[test]
    fn spec_only_machine_arithmetic_clauses_all_fail_closed() {
        let spec = FunctionSpec {
            requires: vec!["x + 1 > x".to_string()],
            ensures: vec!["result + 1 > result".to_string()],
            invariants: vec!["y - 1 < y".to_string()],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 3, "every authored clause remains visible: {vcs:#?}");
        assert!(vcs.iter().all(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == crate::contracts::SPEC_UNVERIFIABLE_KIND)
                && vc.formula == Formula::Bool(true)
        }));
        assert!(
            !vcs.iter().any(|vc| {
                matches!(
                    vc.kind,
                    VcKind::Precondition { .. } | VcKind::Postcondition | VcKind::Assertion { .. }
                )
            }),
            "no mathematical-Int contract row may reach a solver: {vcs:#?}",
        );
    }

    #[test]
    fn test_requires_generates_precondition_vc() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec![],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { callee } if callee == "spec_fn"));
        // Trust: definition-site Precondition VCs are trivially provable
        // (`Bool(false)` means the negated obligation is UNSAT). The
        // precondition expression itself is preserved in `func.preconditions`
        // and conjoined onto other VCs as a hypothesis.
        assert_eq!(vcs[0].formula, Formula::Bool(false));
    }

    #[test]
    fn test_ensures_generates_postcondition_vc() {
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::Postcondition));
        // "result" maps to "_0" in the spec parser
        assert_eq!(
            vcs[0].formula,
            Formula::Not(Box::new(Formula::Ge(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
        );
    }

    #[test]
    fn test_invariant_generates_assertion_vc() {
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec![],
            invariants: vec!["n > 0".to_string()],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(
            matches!(&vcs[0].kind, VcKind::Assertion { message } if message == "invariant: n > 0")
        );
    }

    #[test]
    fn test_multiple_specs_generate_multiple_vcs() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string(), "y > 0".to_string()],
            ensures: vec!["result >= x".to_string()],
            invariants: vec!["x + y > 0".to_string()],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 4);

        let pre_count =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).count();
        let post_count = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).count();
        let inv_count = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Assertion { .. })).count();
        let unsupported_count =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })).count();

        assert_eq!(pre_count, 2);
        assert_eq!(post_count, 1);
        assert_eq!(inv_count, 0);
        assert_eq!(unsupported_count, 1, "the arithmetic invariant must fail closed");
    }

    #[test]
    fn test_ungrounded_result_model_ensures_is_unknown_not_postcondition() {
        // `result.is_ok()` parses to `_0_discr != 0` — a SYNTHETIC model term
        // this lane never grounds, so the old `Not(formula)` Postcondition VC
        // was satisfiable by havoc (reported Failed with a minted, non-program
        // counterexample). It must emit the fail-closed NON-REFUTABLE Unknown
        // shape instead, and never be silently dropped.
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec!["result.is_ok()".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 1, "the obligation must not vanish: {vcs:#?}");
        assert!(
            matches!(&vcs[0].kind, VcKind::UnsupportedMir { kind, .. }
                if kind == crate::contracts::SPEC_MODEL_UNGROUNDED_KIND),
            "ungrounded spec ensures must be the fail-closed Unknown shape: {:?}",
            vcs[0].kind
        );
        assert_eq!(
            vcs[0].formula,
            Formula::Bool(true),
            "the fail-closed row is non-refutable (never proved, never a minted cex)"
        );
        assert!(!vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)));
    }

    #[test]
    fn test_unparseable_specs_are_explicit_unknown_rows() {
        let spec = FunctionSpec {
            requires: vec!["???".to_string(), "x > 0".to_string()],
            ensures: vec!["@@@".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 3, "no authored clause may disappear: {vcs:#?}");
        assert_eq!(
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).count(),
            1
        );
        assert_eq!(
            vcs.iter()
                .filter(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                    if kind == crate::contracts::SPEC_UNVERIFIABLE_KIND
                        || kind == crate::contracts::SPEC_ENSURES_UNPARSEABLE_KIND))
                .count(),
            2
        );
    }

    #[test]
    fn mirrored_unparseable_contract_is_reported_once() {
        let body = "???".to_string();
        let spec =
            FunctionSpec { requires: vec![body.clone()], ensures: vec![], invariants: vec![] };
        let mut func = spec_test_function(spec);
        func.contracts.push(Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body,
        });

        let vcs = crate::generate_vcs(&func);
        assert_eq!(vcs.len(), 1, "one source clause must produce one proof-gap row: {vcs:#?}");
        assert!(matches!(&vcs[0].kind, VcKind::UnsupportedMir { kind, .. }
            if kind == crate::contracts::SPEC_UNVERIFIABLE_KIND));
    }

    #[test]
    fn production_mirrored_requires_has_one_source_owned_definition_entry_row() {
        let expression = "x > 0";
        let raw_span = SourceSpan {
            file: "mirrored_requires.rs".to_string(),
            line_start: 7,
            col_start: 3,
            line_end: 7,
            col_end: 25,
        };
        let spec = FunctionSpec {
            requires: vec![expression.to_string()],
            ensures: vec![],
            invariants: vec![],
        };
        let mut func = spec_test_function(spec);
        func.contracts.push(Contract {
            kind: ContractKind::Requires,
            span: raw_span.clone(),
            body: format!("{}{expression}", crate::contracts::LOWERED_CONTRACT_PREFIX),
        });
        func.preconditions.push(parse_spec_expr(expression).expect("parse precondition"));

        let vcs = crate::generate_vcs(&func);
        let preconditions = vcs
            .iter()
            .filter(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
            .collect::<Vec<_>>();
        assert_eq!(
            preconditions.len(),
            1,
            "raw Contract + compatibility FunctionSpec + formula carrier is one source clause: {vcs:#?}",
        );
        assert_eq!(preconditions[0].formula, Formula::Bool(false));
        assert_eq!(preconditions[0].location, raw_span);
        assert_eq!(
            preconditions[0].contract_metadata.and_then(|metadata| metadata.source_contract_index),
            Some(0),
        );
    }

    #[test]
    fn mirrored_requires_consumption_is_cardinality_aware() {
        let expression = "x > 0";
        let spec = FunctionSpec {
            requires: vec![expression.to_string(), "x > 0".to_string()],
            ensures: vec![],
            invariants: vec![],
        };
        let mut func = spec_test_function(spec);
        func.contracts.push(Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: expression.to_string(),
        });

        let spec_rows = generate_spec_vcs(&func);
        assert_eq!(
            spec_rows.len(),
            1,
            "one raw row consumes one mirror; the independently supplied duplicate stays visible",
        );
        assert!(matches!(spec_rows[0].kind, VcKind::Precondition { .. }));
    }

    #[test]
    fn parsed_equal_but_text_distinct_spec_clause_is_not_claimed_as_a_raw_mirror() {
        let raw_expression = "x > 0";
        let independent_expression = "(x > 0)";
        assert_eq!(
            parse_spec_expr(raw_expression),
            parse_spec_expr(independent_expression),
            "fixture must isolate source identity from parsed semantics",
        );
        let spec = FunctionSpec {
            requires: vec![independent_expression.to_string()],
            ensures: vec![],
            invariants: vec![],
        };
        let mut func = spec_test_function(spec);
        func.contracts.push(Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: raw_expression.to_string(),
        });

        let spec_rows = generate_spec_vcs(&func);
        assert_eq!(
            spec_rows.len(),
            1,
            "a parsed-equal clause without the exact mirrored spelling must remain visible",
        );
        assert!(matches!(spec_rows[0].kind, VcKind::Precondition { .. }));

        let all_rows = crate::generate_vcs(&func)
            .into_iter()
            .filter(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
            .collect::<Vec<_>>();
        assert_eq!(
            all_rows.len(),
            2,
            "the raw source row and independent compatibility clause must retain separate provenance",
        );
        assert_eq!(
            all_rows
                .iter()
                .filter(|vc| vc
                    .contract_metadata
                    .and_then(|metadata| metadata.source_contract_index)
                    == Some(0))
                .count(),
            1,
            "only the raw source row may carry source-contract index 0",
        );
    }

    #[test]
    fn spec_only_requires_with_formula_carrier_remains_visible() {
        let expression = "x > 0";
        let spec = FunctionSpec {
            requires: vec![expression.to_string()],
            ensures: vec![],
            invariants: vec![],
        };
        let mut func = spec_test_function(spec);
        func.preconditions.push(parse_spec_expr(expression).expect("parse precondition"));

        let vcs = crate::generate_vcs(&func);
        let preconditions = vcs
            .iter()
            .filter(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
            .collect::<Vec<_>>();
        assert_eq!(preconditions.len(), 1, "a spec-only clause must not disappear: {vcs:#?}");
        assert_eq!(preconditions[0].formula, Formula::Bool(false));
        assert_eq!(
            preconditions[0].contract_metadata.and_then(|metadata| metadata.source_contract_index),
            None,
        );
    }

    #[test]
    fn test_contract_metadata_attached() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        for vc in &vcs {
            let meta = vc.contract_metadata.expect("should have contract metadata");
            assert!(meta.has_requires);
            assert!(meta.has_ensures);
            assert!(!meta.has_invariant);
            assert!(!meta.has_variant);
            assert!(meta.has_any());
        }
    }

    #[test]
    fn test_arithmetic_ensures_result_maps_to_fail_closed_row() {
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec!["result == a + b".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::UnsupportedMir { kind, .. }
            if kind == crate::contracts::SPEC_UNVERIFIABLE_KIND));
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    #[test]
    fn test_has_spec_vcs_empty() {
        assert!(!has_spec_vcs(&FunctionSpec::default()));
    }

    #[test]
    fn test_has_spec_vcs_with_parseable() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec![],
            invariants: vec![],
        };
        assert!(has_spec_vcs(&spec));
    }

    #[test]
    fn test_has_spec_vcs_all_unparseable() {
        let spec = FunctionSpec {
            requires: vec!["???".to_string()],
            ensures: vec!["@@@".to_string()],
            invariants: vec![],
        };
        assert!(has_spec_vcs(&spec), "unparseable clauses still produce proof-gap rows");
    }

    #[test]
    fn test_complex_ensures_with_arithmetic_fails_closed() {
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec!["result >= x + y && result <= x * y".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::UnsupportedMir { kind, .. }
            if kind == crate::contracts::SPEC_UNVERIFIABLE_KIND));
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    #[test]
    fn test_vcs_reference_correct_function_name() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["result > 0".to_string()],
            invariants: vec!["x > 0".to_string()],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        for vc in &vcs {
            assert_eq!(vc.function, "spec_fn");
        }
    }

    /// Gap-A EMIT: a CHECKER-CORE recursive-spec postcondition (`is_whnf(result)`)
    /// flows through the STANDARD `generate_vcs` pipeline from its `#[ensures]`
    /// STRING to an emitted `VcKind::Postcondition` VC — the negated opaque
    /// checker-core predicate over the return slot `_0`. This is the rung the
    /// arithmetic postcondition lane (`result >= step`) already reached, now
    /// carrying a structural/inductive property of the result instead of a
    /// first-order bound. (The `spec_test_function` return type is `usize`; the
    /// predicate's Int carrier is the opaque GHOST HANDLE of the result — the
    /// EMIT mechanics are return-type agnostic. Grounding the handle to a literal
    /// `Expr`-returning kernel fn's MIR is the DISCHARGE rung, mapped separately.)
    #[test]
    fn checker_core_is_whnf_postcondition_is_emitted() {
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec!["is_whnf(result)".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = crate::generate_vcs(&func);

        let post: Vec<_> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
        assert!(!post.is_empty(), "checker-core `is_whnf(result)` must emit a Postcondition VC");

        // Every emitted checker-core Postcondition VC negates the opaque `is_whnf`
        // predicate applied to the return slot `_0` (the pin the postcondition lane
        // uses). Opaque => a first-order solver can never prove it => the VC is
        // reported not-proved (fail-closed; never a false PROVE) until a
        // kernel-checked KExpr discharge runs.
        for vc in &post {
            let mut saw_is_whnf_pred = false;
            vc.formula.visit(&mut |f| {
                if let Formula::Pred(name, args) = f
                    && name.as_str() == "is_whnf"
                {
                    saw_is_whnf_pred = true;
                    assert_eq!(args.len(), 1, "is_whnf is unary");
                    assert_eq!(
                        args[0].var_name(),
                        Some("_0"),
                        "the checker-core predicate must be applied to the return slot _0"
                    );
                }
            });
            assert!(
                saw_is_whnf_pred,
                "the Postcondition VC must contain the opaque `is_whnf` checker-core predicate; \
                 formula was {:?}",
                vc.formula
            );
        }
    }

    #[test]
    fn test_spec_vcs_integrated_with_generate_vcs() {
        // Verify that spec VCs show up in the full generate_vcs pipeline
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = crate::generate_vcs(&func);

        let pre_count =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).count();
        let post_count = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).count();

        assert!(pre_count >= 1, "should have at least 1 precondition VC from spec");
        assert!(post_count >= 1, "should have at least 1 postcondition VC from spec");
    }
}
