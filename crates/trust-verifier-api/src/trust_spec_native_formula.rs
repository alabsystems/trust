//! Shared strict conversion of original typed specifications to the native
//! arithmetic-free formula codec. This translates a claim; it grants no proof.

use trust_types::trust_formula_v1::TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION;

use crate::{
    TRUST_SPEC_PREDICATE_SCHEMA_VERSION, TrustSpecBinaryOp, TrustSpecExpr, TrustSpecExprKind,
    TrustSpecPredicate, TrustSpecSort, TrustSpecUnaryOp,
};

fn canonical_trust_formula_payload(value: &serde_json::Value) -> Result<String, String> {
    trust_types::trust_formula_v1::canonical_arithmetic_free_trust_formula_v1_payload(value)
}

pub fn trust_spec_predicate_to_trust_formula_payload(
    predicate: &TrustSpecPredicate,
) -> Result<String, String> {
    if !predicate.has_current_schema() {
        return Err(format!(
            "unsupported TrustSpecPredicate schema `{}`, expected `{TRUST_SPEC_PREDICATE_SCHEMA_VERSION}`",
            predicate.schema_version
        ));
    }
    if predicate.root_sort != TrustSpecSort::Bool || predicate.root.sort != TrustSpecSort::Bool {
        return Err("TrustSpecPredicate root must be a typed boolean predicate".to_string());
    }
    predicate.validate()?;
    let (expr_mentions_array, expr_mentions_float, expr_has_div_mod) =
        scan_trust_spec_expr_features(&predicate.root);
    // TrustFormulaV1 is a scalar replay format. `TrustSpecSort::Array` is a
    // valid public specification sort, but it has no faithful representation in
    // this adapter and must fail closed before any scalar claim is serialized.
    if predicate
        .variables
        .iter()
        .any(|variable| matches!(variable.sort, TrustSpecSort::Array { .. }))
        || expr_mentions_array
    {
        return Err(
            "TrustSpecPredicate array sort is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                .to_string(),
        );
    }
    // Float sorts are likewise valid public specification sorts with no
    // faithful representation here: replaying IEEE-754 comparisons (NaN is
    // unordered, +0.0 == -0.0) over the scalar int/bool fragment would give
    // the terms the wrong semantics, so they must fail closed before any
    // scalar claim is serialized.
    if predicate
        .variables
        .iter()
        .any(|variable| matches!(variable.sort, TrustSpecSort::Float { .. }))
        || expr_mentions_float
    {
        return Err(
            "TrustSpecPredicate float sort is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                .to_string(),
        );
    }
    if expr_has_div_mod {
        let mut assumptions = Vec::new();
        validate_trust_spec_expr_div_mod_defined(&predicate.root, &mut assumptions, false)?;
    }

    let mut result_sort = None;
    let body = trust_spec_expr_to_trust_formula_body(&predicate.root, &mut result_sort)?;
    let mut variables = Vec::with_capacity(predicate.variables.len());
    for variable in &predicate.variables {
        if variable.name.trim().is_empty() {
            return Err("TrustSpecPredicate variable name is empty".to_string());
        }
        variables.push(serde_json::json!({
            "name": variable.name,
            "sort": trust_spec_sort_label(variable.sort),
        }));
    }

    let mut payload = serde_json::Map::new();
    payload.insert("schema".to_string(), serde_json::json!(TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION));
    payload.insert("variables".to_string(), serde_json::Value::Array(variables));
    if let Some(sort) = result_sort {
        payload.insert(
            "result".to_string(),
            serde_json::json!({
                "name": "result",
                "sort": trust_spec_sort_label(sort),
            }),
        );
    }
    payload.insert("body".to_string(), body);

    canonical_trust_formula_payload(&serde_json::Value::Object(payload)).map_err(|err| {
        format!("could not canonicalize TrustSpecPredicate as TrustFormulaV1: {err}")
    })
}

fn trust_spec_expr_to_trust_formula_body(
    expr: &TrustSpecExpr,
    result_sort: &mut Option<TrustSpecSort>,
) -> Result<serde_json::Value, String> {
    match &expr.kind {
        TrustSpecExprKind::BoolLiteral { value } => {
            require_sort(expr, TrustSpecSort::Bool, "bool literal")?;
            Ok(serde_json::json!({ "bool": value }))
        }
        TrustSpecExprKind::IntLiteral { value } => {
            require_sort(expr, TrustSpecSort::Int, "int literal")?;
            let parsed = trust_types::trust_formula_v1::trust_formula_v1_integer_literal(value)?;
            Ok(serde_json::json!({ "int": parsed }))
        }
        TrustSpecExprKind::Variable { name } => {
            if name.trim().is_empty() {
                return Err("TrustSpecPredicate variable reference has an empty name".to_string());
            }
            Ok(serde_json::json!({ "var": name }))
        }
        TrustSpecExprKind::Result => {
            if let Some(existing) = result_sort {
                if *existing != expr.sort {
                    return Err("TrustSpecPredicate uses result with inconsistent sorts".to_string());
                }
            } else {
                *result_sort = Some(expr.sort);
            }
            Ok(serde_json::json!({ "result": true }))
        }
        TrustSpecExprKind::Unary { op, expr: inner } => {
            match op {
                TrustSpecUnaryOp::Not => {
                    require_sort(expr, TrustSpecSort::Bool, "not expression")?;
                    require_sort(inner, TrustSpecSort::Bool, "not operand")?;
                }
                // Trust (#29): `Neg` is arithmetic — refuse it in the
                // bare-claim lane for the same amendment-1 reason as the
                // binary arithmetic refusal below.
                TrustSpecUnaryOp::Neg => {
                    return Err(trust_spec_bare_claim_arithmetic_refusal("neg"));
                }
            }
            Ok(serde_json::json!({
                "op": trust_spec_unary_op_label(*op)?,
                "expr": trust_spec_expr_to_trust_formula_body(inner, result_sort)?,
            }))
        }
        TrustSpecExprKind::Binary { op, lhs, rhs } => {
            // Trust (#29, defense-in-depth): refuse machine arithmetic in the
            // BARE (non-body-bound) trust-wp claim lane, mirroring the
            // compiler's copy of this lowering
            // (rustc_mir_transform::trust_verify) and the body-bound bridge
            // fragment (`trust_ir_bridge::trust_wp_claim::
            // spec_predicate_to_sibling_json`, blueprint amendment 1).
            // Machine-integer predicates lowered as unbounded-Int arithmetic
            // are a confirmed false-proof vector: the sibling's linear-int
            // rule proves free-variable Int tautologies such as
            // `ensures result + 1 > result`, which is FALSE at `u64::MAX`
            // under Rust's wrapping machine semantics. Fail-closed: this
            // refusal surfaces as "is not an eligible canonical typed claim"
            // and the obligation demotes to Unsupported, never Proved.
            if matches!(
                op,
                TrustSpecBinaryOp::Add
                    | TrustSpecBinaryOp::Sub
                    | TrustSpecBinaryOp::Mul
                    | TrustSpecBinaryOp::Div
                    | TrustSpecBinaryOp::Mod
            ) {
                return Err(trust_spec_bare_claim_arithmetic_refusal(
                    trust_spec_binary_op_label(*op)?,
                ));
            }
            validate_trust_spec_binary(*op, expr, lhs, rhs)?;
            Ok(serde_json::json!({
                "op": trust_spec_binary_op_label(*op)?,
                "lhs": trust_spec_expr_to_trust_formula_body(lhs, result_sort)?,
                "rhs": trust_spec_expr_to_trust_formula_body(rhs, result_sort)?,
            }))
        }
        TrustSpecExprKind::Old { expr: inner } => Ok(serde_json::json!({
            "old": trust_spec_expr_to_trust_formula_body(inner, result_sort)?,
        })),
        TrustSpecExprKind::Field { .. }
        | TrustSpecExprKind::Index { .. }
        | TrustSpecExprKind::Quantifier { .. } => Err(
            "TrustSpecPredicate node is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                .to_string(),
        ),
        _ => Err(
            "TrustSpecPredicate future node is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                .to_string(),
        ),
    }
}

fn scan_trust_spec_expr_features(root: &TrustSpecExpr) -> (bool, bool, bool) {
    let mut mentions_array = false;
    let mut mentions_float = false;
    let mut has_div_mod = false;
    let mut pending = vec![root];
    while let Some(expr) = pending.pop() {
        match expr.sort {
            TrustSpecSort::Array { .. } => mentions_array = true,
            TrustSpecSort::Float { .. } => mentions_float = true,
            _ => {}
        }
        match &expr.kind {
            TrustSpecExprKind::Unary { expr, .. }
            | TrustSpecExprKind::Old { expr }
            | TrustSpecExprKind::BvUnary { expr, .. }
            | TrustSpecExprKind::BvFromInt { expr, .. }
            | TrustSpecExprKind::IntFromBv { expr, .. } => pending.push(expr),
            TrustSpecExprKind::Binary { op, lhs, rhs } => {
                if matches!(op, TrustSpecBinaryOp::Div | TrustSpecBinaryOp::Mod) {
                    has_div_mod = true;
                }
                pending.push(lhs);
                pending.push(rhs);
            }
            TrustSpecExprKind::BvBinary { lhs, rhs, .. } => {
                pending.push(lhs);
                pending.push(rhs);
            }
            TrustSpecExprKind::Field { base, .. } => pending.push(base),
            TrustSpecExprKind::Index { base, index } => {
                pending.push(base);
                pending.push(index);
            }
            TrustSpecExprKind::Quantifier { variable_sort, body, .. } => {
                match variable_sort {
                    TrustSpecSort::Array { .. } => mentions_array = true,
                    TrustSpecSort::Float { .. } => mentions_float = true,
                    _ => {}
                }
                pending.push(body);
            }
            TrustSpecExprKind::IsVariant { scrutinee, .. }
            | TrustSpecExprKind::VariantField { scrutinee, .. } => pending.push(scrutinee),
            TrustSpecExprKind::FloatLiteral { .. } => mentions_float = true,
            TrustSpecExprKind::BoolLiteral { .. }
            | TrustSpecExprKind::IntLiteral { .. }
            | TrustSpecExprKind::Variable { .. }
            | TrustSpecExprKind::Result
            | TrustSpecExprKind::BitVecLiteral { .. } => {}
            _ => {}
        }
    }
    (mentions_array, mentions_float, has_div_mod)
}

// Trust (#29): amendment-1 arithmetic refusal for the bare trust-wp claim
// lane. Kept as a single helper so the walker's unary (`Neg`) and binary
// (`Add`/`Sub`/`Mul`/`Div`/`Mod`) refusals stay message-identical with the
// compiler's copy of this lowering (rustc_mir_transform::trust_verify).
fn trust_spec_bare_claim_arithmetic_refusal(op: &str) -> String {
    format!(
        "TrustSpecPredicate arithmetic operator `{op}` is outside the trust-wp TrustFormulaV1 bare-claim fragment: machine arithmetic modeled over unbounded Int is a false-proof vector (`ensures result + 1 > result` is Int-provable but false at u64::MAX); see 2026-07-17 trust-wp lowering blueprint amendment 1"
    )
}

fn validate_trust_spec_expr_div_mod_defined<'a>(
    expr: &'a TrustSpecExpr,
    assumptions: &mut Vec<&'a TrustSpecExpr>,
    in_and_chain: bool,
) -> Result<(), String> {
    match &expr.kind {
        TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::And, lhs, rhs } => {
            let checkpoint = assumptions.len();
            if !in_and_chain {
                collect_trust_spec_definedness_facts(expr, assumptions);
            }
            let res = validate_trust_spec_expr_div_mod_defined(lhs, assumptions, true)
                .and_then(|()| validate_trust_spec_expr_div_mod_defined(rhs, assumptions, true));
            assumptions.truncate(checkpoint);
            res
        }
        TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Implies, lhs, rhs } => {
            let checkpoint = assumptions.len();
            collect_trust_spec_definedness_facts(lhs, assumptions);
            let res = validate_trust_spec_expr_div_mod_defined(lhs, assumptions, false)
                .and_then(|()| validate_trust_spec_expr_div_mod_defined(rhs, assumptions, false));
            assumptions.truncate(checkpoint);
            res
        }
        TrustSpecExprKind::Binary {
            op: op @ (TrustSpecBinaryOp::Div | TrustSpecBinaryOp::Mod),
            lhs,
            rhs,
        } => {
            validate_trust_spec_expr_div_mod_defined(lhs, assumptions, false)?;
            validate_trust_spec_expr_div_mod_defined(rhs, assumptions, false)?;
            if trust_spec_expr_known_nonzero(rhs, assumptions) {
                Ok(())
            } else {
                Err(format!(
                    "TrustSpecPredicate {:?} divisor must be syntactically nonzero or guarded by a nonzero assumption for trust_wp TrustFormulaV1 native replay",
                    op
                ))
            }
        }
        TrustSpecExprKind::Binary { lhs, rhs, .. } => {
            validate_trust_spec_expr_div_mod_defined(lhs, assumptions, false)?;
            validate_trust_spec_expr_div_mod_defined(rhs, assumptions, false)
        }
        TrustSpecExprKind::Unary { expr: inner, .. } | TrustSpecExprKind::Old { expr: inner } => {
            validate_trust_spec_expr_div_mod_defined(inner, assumptions, false)
        }
        TrustSpecExprKind::Field { base, .. } => {
            validate_trust_spec_expr_div_mod_defined(base, assumptions, false)
        }
        TrustSpecExprKind::Index { base, index } => {
            validate_trust_spec_expr_div_mod_defined(base, assumptions, false)?;
            validate_trust_spec_expr_div_mod_defined(index, assumptions, false)
        }
        TrustSpecExprKind::Quantifier { body, .. } => {
            validate_trust_spec_expr_div_mod_defined(body, assumptions, false)
        }
        TrustSpecExprKind::BoolLiteral { .. }
        | TrustSpecExprKind::IntLiteral { .. }
        | TrustSpecExprKind::Variable { .. }
        | TrustSpecExprKind::Result => Ok(()),
        _ => Ok(()),
    }
}

fn collect_trust_spec_definedness_facts<'a>(
    expr: &'a TrustSpecExpr,
    facts: &mut Vec<&'a TrustSpecExpr>,
) {
    match &expr.kind {
        TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::And, lhs, rhs } => {
            collect_trust_spec_definedness_facts(lhs, facts);
            collect_trust_spec_definedness_facts(rhs, facts);
        }
        TrustSpecExprKind::Binary { op, .. }
            if trust_spec_is_definedness_fact_operator(*op)
                && !trust_spec_contains_div_mod(expr) =>
        {
            facts.push(expr);
        }
        _ => {}
    }
}

fn trust_spec_is_definedness_fact_operator(op: TrustSpecBinaryOp) -> bool {
    matches!(
        op,
        TrustSpecBinaryOp::Eq
            | TrustSpecBinaryOp::Ne
            | TrustSpecBinaryOp::Lt
            | TrustSpecBinaryOp::Le
            | TrustSpecBinaryOp::Gt
            | TrustSpecBinaryOp::Ge
    )
}

fn trust_spec_expr_known_nonzero(expr: &TrustSpecExpr, assumptions: &[&TrustSpecExpr]) -> bool {
    trust_spec_constant_int(expr).is_some_and(|value| value != 0)
        || assumptions
            .iter()
            .any(|assumption| trust_spec_assumption_proves_nonzero(assumption, expr))
}

fn trust_spec_assumption_proves_nonzero(
    assumption: &TrustSpecExpr,
    target: &TrustSpecExpr,
) -> bool {
    let TrustSpecExprKind::Binary { op, lhs, rhs } = &assumption.kind else {
        return false;
    };
    match op {
        TrustSpecBinaryOp::Ne => {
            (lhs.as_ref() == target && trust_spec_is_int_zero(rhs))
                || (rhs.as_ref() == target && trust_spec_is_int_zero(lhs))
        }
        TrustSpecBinaryOp::Gt | TrustSpecBinaryOp::Lt => {
            (lhs.as_ref() == target && trust_spec_is_int_zero(rhs))
                || (trust_spec_is_int_zero(lhs) && rhs.as_ref() == target)
        }
        _ => false,
    }
}

fn trust_spec_contains_div_mod(expr: &TrustSpecExpr) -> bool {
    match &expr.kind {
        TrustSpecExprKind::Binary {
            op: TrustSpecBinaryOp::Div | TrustSpecBinaryOp::Mod, ..
        } => true,
        TrustSpecExprKind::Binary { lhs, rhs, .. } => {
            trust_spec_contains_div_mod(lhs) || trust_spec_contains_div_mod(rhs)
        }
        TrustSpecExprKind::Unary { expr: inner, .. } | TrustSpecExprKind::Old { expr: inner } => {
            trust_spec_contains_div_mod(inner)
        }
        TrustSpecExprKind::Field { base, .. } => trust_spec_contains_div_mod(base),
        TrustSpecExprKind::Index { base, index } => {
            trust_spec_contains_div_mod(base) || trust_spec_contains_div_mod(index)
        }
        TrustSpecExprKind::Quantifier { body, .. } => trust_spec_contains_div_mod(body),
        TrustSpecExprKind::BoolLiteral { .. }
        | TrustSpecExprKind::IntLiteral { .. }
        | TrustSpecExprKind::Variable { .. }
        | TrustSpecExprKind::Result => false,
        _ => false,
    }
}

fn trust_spec_is_int_zero(expr: &TrustSpecExpr) -> bool {
    trust_spec_constant_int(expr) == Some(0)
}

fn trust_spec_constant_int(expr: &TrustSpecExpr) -> Option<i64> {
    match &expr.kind {
        TrustSpecExprKind::IntLiteral { value } => value.parse::<i64>().ok(),
        _ => None,
    }
}

fn require_sort(
    expr: &TrustSpecExpr,
    expected: TrustSpecSort,
    context: &str,
) -> Result<(), String> {
    if expr.sort == expected {
        Ok(())
    } else {
        Err(format!(
            "TrustSpecPredicate {context} has sort {:?}, expected {:?}",
            expr.sort, expected
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn upper_bound(value: &str) -> TrustSpecPredicate {
        TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Le,
                TrustSpecExpr::result(TrustSpecSort::Int),
                TrustSpecExpr::int_literal(value),
            ),
            Vec::new(),
        )
    }

    #[test]
    fn native_unsigned_high_half_bounds_keep_their_exact_magnitude() {
        for bound in [1_u64 << 63, u64::MAX] {
            let payload =
                trust_spec_predicate_to_trust_formula_payload(&upper_bound(&bound.to_string()))
                    .unwrap();
            let decoded: serde_json::Value = serde_json::from_str(&payload).unwrap();
            assert_eq!(decoded["body"]["rhs"]["int"].as_u64(), Some(bound));
            assert_eq!(decoded["body"]["lhs"]["result"], true);
            assert_eq!(decoded["result"]["sort"], "int");
        }
    }

    #[test]
    fn native_literal_bounds_do_not_admit_wider_or_fractional_values() {
        for bound in ["18446744073709551616", "-9223372036854775809", "9223372036854775808.0"] {
            assert!(trust_spec_predicate_to_trust_formula_payload(&upper_bound(bound)).is_err());
        }
    }
}

fn validate_trust_spec_binary(
    op: TrustSpecBinaryOp,
    expr: &TrustSpecExpr,
    lhs: &TrustSpecExpr,
    rhs: &TrustSpecExpr,
) -> Result<(), String> {
    require_sort(expr, op.result_sort(), "binary expression")?;
    match op {
        TrustSpecBinaryOp::Add
        | TrustSpecBinaryOp::Sub
        | TrustSpecBinaryOp::Mul
        | TrustSpecBinaryOp::Div
        | TrustSpecBinaryOp::Mod => {
            require_sort(lhs, TrustSpecSort::Int, "arithmetic lhs")?;
            require_sort(rhs, TrustSpecSort::Int, "arithmetic rhs")
        }
        TrustSpecBinaryOp::Eq | TrustSpecBinaryOp::Ne => {
            if lhs.sort == rhs.sort {
                require_sort(expr, TrustSpecSort::Bool, "comparison expression")
            } else {
                Err(format!(
                    "TrustSpecPredicate equality compares incompatible sorts {:?} and {:?}",
                    lhs.sort, rhs.sort
                ))
            }
        }
        TrustSpecBinaryOp::Lt
        | TrustSpecBinaryOp::Le
        | TrustSpecBinaryOp::Gt
        | TrustSpecBinaryOp::Ge => {
            require_sort(lhs, TrustSpecSort::Int, "comparison lhs")?;
            require_sort(rhs, TrustSpecSort::Int, "comparison rhs")?;
            require_sort(expr, TrustSpecSort::Bool, "comparison expression")
        }
        TrustSpecBinaryOp::And | TrustSpecBinaryOp::Or | TrustSpecBinaryOp::Implies => {
            require_sort(lhs, TrustSpecSort::Bool, "boolean lhs")?;
            require_sort(rhs, TrustSpecSort::Bool, "boolean rhs")?;
            require_sort(expr, TrustSpecSort::Bool, "boolean expression")
        }
    }
}

fn trust_spec_sort_label(sort: TrustSpecSort) -> &'static str {
    match sort {
        TrustSpecSort::Bool => "bool",
        TrustSpecSort::Int => "int",
        TrustSpecSort::BitVec { .. } => "bit_vec",
        TrustSpecSort::Array { .. } => "array",
        // Unreachable in the TrustFormulaV1 lane: float-sorted predicates are
        // rejected up front in `trust_spec_predicate_to_trust_formula_payload`
        // (IEEE semantics have no faithful scalar int/bool replay).
        TrustSpecSort::Float { .. } => "float",
    }
}

fn trust_spec_unary_op_label(op: TrustSpecUnaryOp) -> Result<&'static str, String> {
    match op {
        TrustSpecUnaryOp::Not => Ok("not"),
        TrustSpecUnaryOp::Neg => Ok("neg"),
    }
}

fn trust_spec_binary_op_label(op: TrustSpecBinaryOp) -> Result<&'static str, String> {
    match op {
        TrustSpecBinaryOp::Add => Ok("add"),
        TrustSpecBinaryOp::Sub => Ok("sub"),
        TrustSpecBinaryOp::Mul => Ok("mul"),
        TrustSpecBinaryOp::Div => Ok("div"),
        TrustSpecBinaryOp::Mod => Ok("mod"),
        TrustSpecBinaryOp::Eq => Ok("eq"),
        TrustSpecBinaryOp::Ne => Ok("ne"),
        TrustSpecBinaryOp::Lt => Ok("lt"),
        TrustSpecBinaryOp::Le => Ok("le"),
        TrustSpecBinaryOp::Gt => Ok("gt"),
        TrustSpecBinaryOp::Ge => Ok("ge"),
        TrustSpecBinaryOp::And => Ok("and"),
        TrustSpecBinaryOp::Or => Ok("or"),
        TrustSpecBinaryOp::Implies => Ok("implies"),
    }
}
