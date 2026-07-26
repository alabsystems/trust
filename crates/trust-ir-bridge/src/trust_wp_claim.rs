// trust-ir-bridge: body-bound trust-wp claim construction (task #23, Slice 1).
//
// Blueprint of record: docs/design-notes/2026-07-17-trust-wp-lowering-blueprint.md.
//
// An uncited `ensures` postcondition (e.g. `fn ge_refl(x: u64) -> u64
// ensures result >= x { x }`) reaches the trust-wp deductive lane as a typed
// `trust.spec-predicate.v1` predicate, but the lane fails closed because no
// one lowers the contract into the sibling verifier's
// `trust-wp.trust-formula.v1` claim envelope. This module builds that
// envelope BODY-BOUND: `result` is let-bound to the function's exact defining
// expression (recovered from the trust-ir SSA body by a fail-closed walker),
// so the sibling's pure-expr replay proves the postcondition of THIS body,
// not a free-variable abstraction of it.
//
// v1 fragment (deliberately narrow, every exclusion fails CLOSED to the
// existing Unsupported path — the fail-closed enumeration is in the
// blueprint):
//   * defining expression: the returned value must resolve, through `Copy`
//     chains inside a SINGLE entry block, to an entry-block parameter or an
//     i64-representable integer / bool constant. Anything else — arithmetic,
//     calls, branches, multiple blocks — refuses.
//   * predicate: comparisons + boolean connectives over Var / `result` /
//     int & bool literals ONLY. NO arithmetic anywhere (amendment 1: machine
//     arithmetic modeled over unbounded Int is a confirmed false-proof
//     vector — `ensures result + 1 > result` is Int-provable and false at
//     u64::MAX).
//   * any spec variable literally named `result` refuses (the sibling's
//     let-binding of `result` must be unambiguous; its decoder also rejects
//     shadowing).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde_json::{Value, json};
use trust_ir::{Constant, FuncId, Inst, Module, Ty, ValueId};
use trust_verifier_api::{
    TrustSpecBinaryOp, TrustSpecExpr, TrustSpecExprKind, TrustSpecPredicate, TrustSpecUnaryOp,
};

/// Schema string the sibling's decoder validates (pinned by
/// first-party/trust-wp/crates/trust-wp-lib/tests/trust_ir_native_bundle.rs —
/// note the HYPHENATED `trust-wp`, not `trust_wp`).
pub const TRUST_WP_TRUST_FORMULA_SCHEMA: &str = "trust-wp.trust-formula.v1";

/// The function's defining expression, recovered fail-closed from its trust-ir
/// SSA body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefiningExpr {
    /// The returned value IS the entry-block parameter at this position
    /// (0-based over the entry block's parameter list).
    EntryParam(usize),
    /// The returned value is this integer constant (canonical trust-ir
    /// `Constant::Int(i128)` verified to fit i64 — amendment 5: out-of-range
    /// refuses, never bit-casts).
    IntConst(i64),
    /// The returned value is this boolean constant.
    BoolConst(bool),
}

/// Why a claim could not be body-bound. Every variant is a fail-closed refusal
/// — the obligation keeps today's Unsupported path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustWpClaimError {
    MissingFunction,
    /// The selected function does not satisfy the local, authority-critical
    /// subset of TrustIR validation used by this walker (unique function/SSA
    /// identity, entry/signature agreement, dominance, and exact Const/Copy
    /// typing). The whole module must still pass trust-ir-build validation at
    /// the publication seam.
    MalformedBody(&'static str),
    /// The body is not a single entry block (branches/loops refuse in v1).
    MultipleBlocks,
    /// The entry block does not end in `Return` of exactly one value.
    NoSingleReturn,
    /// An instruction outside the {Const, Copy} whitelist contributes to the
    /// returned value (arithmetic, calls, loads, ... all refuse in v1).
    UnsupportedInstruction,
    /// The returned constant is not an i64-representable integer or a bool.
    UnsupportedConstant,
    /// The returned value resolves to nothing recognizable (dataflow gap).
    UnresolvedValue,
    /// A predicate node is outside the v1 fragment (arithmetic, Old, Field,
    /// Index, quantifiers, ...). Amendment 1 lives here.
    UnsupportedPredicateNode(&'static str),
    /// The canonical typed predicate failed its schema, sort, declaration, or
    /// expression validation before lowering.
    InvalidPredicate(String),
    /// A spec variable is literally named `result`.
    ReservedResultName,
    /// A claim binding or result sort is outside this helper's exact v1
    /// int/bool envelope fragment.
    InvalidEnvelope(String),
    /// The predicate references a variable the envelope cannot bind.
    UnboundVariable(String),
    /// A refutation-shaped root (top-level `And` containing a `Not` conjunct)
    /// — deliberate v1 overbreadth against synthetic-contract inversion
    /// (amendment 2's secondary belt).
    RefutationShapedRoot,
}

impl std::fmt::Display for TrustWpClaimError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingFunction => write!(f, "selected function missing from module"),
            Self::MalformedBody(reason) => write!(f, "malformed TrustIR body: {reason}"),
            Self::MultipleBlocks => write!(f, "body is not a single entry block"),
            Self::NoSingleReturn => write!(f, "entry block does not end in a single-value Return"),
            Self::UnsupportedInstruction => {
                write!(f, "returned value depends on a non-Const/Copy instruction")
            }
            Self::UnsupportedConstant => {
                write!(f, "returned constant is not an i64-representable int or bool")
            }
            Self::UnresolvedValue => write!(f, "returned value did not resolve"),
            Self::UnsupportedPredicateNode(node) => {
                write!(f, "predicate node outside the v1 fragment: {node}")
            }
            Self::InvalidPredicate(reason) => write!(f, "invalid typed predicate: {reason}"),
            Self::ReservedResultName => write!(f, "a spec variable is named `result`"),
            Self::InvalidEnvelope(reason) => write!(f, "invalid trust-wp envelope: {reason}"),
            Self::UnboundVariable(name) => {
                write!(f, "predicate references unbindable variable `{name}`")
            }
            Self::RefutationShapedRoot => {
                write!(f, "refutation-shaped root (And containing Not) refused in v1")
            }
        }
    }
}

/// Recover the defining expression of `function_id`'s return value, fail-closed.
///
/// v1 accepts exactly: a single entry block whose terminator is
/// `Return { values: [v] }`, where `v` resolves through zero or more
/// `Copy` instructions (within that block) to an entry-block parameter, an
/// i64-representable `Constant::Int`, or a `Constant::Bool`.
pub fn trust_wp_result_defining_expr(
    module: &Module,
    function_id: FuncId,
) -> Result<DefiningExpr, TrustWpClaimError> {
    match module.functions.iter().filter(|function| function.id == function_id).count() {
        0 => return Err(TrustWpClaimError::MissingFunction),
        1 => {}
        _ => return Err(TrustWpClaimError::MalformedBody("function id is not unique")),
    }
    let function = module.function_by_id(function_id).ok_or(TrustWpClaimError::MissingFunction)?;
    if function.blocks.len() != 1 {
        return Err(TrustWpClaimError::MultipleBlocks);
    }
    let entry = &function.blocks[0];
    if function.entry != entry.id {
        return Err(TrustWpClaimError::MalformedBody("sole block is not the declared entry"));
    }
    let signature = module
        .func_type(function.ty)
        .ok_or(TrustWpClaimError::MalformedBody("function type is missing"))?;
    if signature.is_vararg {
        return Err(TrustWpClaimError::MalformedBody(
            "variadic function signatures are unsupported",
        ));
    }
    if signature.params.len() != entry.params.len()
        || signature
            .params
            .iter()
            .zip(&entry.params)
            .any(|(expected, (_, actual))| expected != actual)
    {
        return Err(TrustWpClaimError::MalformedBody(
            "entry parameters do not match the function signature",
        ));
    }
    let [return_ty] = signature.returns.as_slice() else {
        return Err(TrustWpClaimError::MalformedBody(
            "function signature does not have exactly one return",
        ));
    };
    validate_local_ssa(entry)?;
    let Some(terminator) = entry.body.last() else {
        return Err(TrustWpClaimError::NoSingleReturn);
    };
    if !terminator.results.is_empty()
        || entry.body[..entry.body.len() - 1].iter().any(trust_ir::InstrNode::is_terminator)
    {
        return Err(TrustWpClaimError::MalformedBody(
            "terminator placement or result arity is invalid",
        ));
    }
    let Inst::Return { values } = &terminator.inst else {
        return Err(TrustWpClaimError::NoSingleReturn);
    };
    let [returned] = values.as_slice() else {
        return Err(TrustWpClaimError::NoSingleReturn);
    };
    let resolved = resolve_value(entry, *returned, entry.body.len() - 1, 0)?;
    if &resolved.ty != return_ty {
        return Err(TrustWpClaimError::MalformedBody(
            "returned value type does not match the function signature",
        ));
    }
    Ok(resolved.expr)
}

/// Reject duplicate parameter/result definitions before the resolver chooses
/// any producer. This is deliberately local rather than a substitute for
/// `trust_ir_build::validate_module`: it makes the public helper fail closed
/// even if a future caller accidentally invokes it before the canonical
/// validator.
fn validate_local_ssa(entry: &trust_ir::Block) -> Result<(), TrustWpClaimError> {
    let mut defined = Vec::new();
    for (parameter, _) in &entry.params {
        if defined.contains(parameter) {
            return Err(TrustWpClaimError::MalformedBody("duplicate SSA parameter"));
        }
        defined.push(*parameter);
    }
    for node in &entry.body {
        for result in &node.results {
            if defined.contains(result) {
                return Err(TrustWpClaimError::MalformedBody("duplicate SSA definition"));
            }
            defined.push(*result);
        }
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ResolvedDefiningExpr {
    expr: DefiningExpr,
    ty: Ty,
}

fn resolve_value(
    entry: &trust_ir::Block,
    value: ValueId,
    use_index: usize,
    depth: u32,
) -> Result<ResolvedDefiningExpr, TrustWpClaimError> {
    // A Copy chain longer than the block is a cycle; refuse rather than spin.
    if depth as usize > entry.body.len() {
        return Err(TrustWpClaimError::UnresolvedValue);
    }
    if let Some((position, (_, ty))) =
        entry.params.iter().enumerate().find(|(_, (param, _))| *param == value)
    {
        return Ok(ResolvedDefiningExpr {
            expr: DefiningExpr::EntryParam(position),
            ty: ty.clone(),
        });
    }
    let Some((producer_index, node)) =
        entry.body.iter().enumerate().find(|(_, node)| node.results.contains(&value))
    else {
        return Err(TrustWpClaimError::UnresolvedValue);
    };
    if producer_index >= use_index {
        return Err(TrustWpClaimError::MalformedBody("SSA use is not dominated by its definition"));
    }
    if node.results.as_slice() != [value] {
        return Err(TrustWpClaimError::MalformedBody(
            "accepted Const/Copy producer does not have exactly one result",
        ));
    }
    match &node.inst {
        Inst::Const { ty, value: constant } => match constant {
            Constant::Int(raw) if ty.is_integer() && constant.value_matches_ty(ty) => {
                i64::try_from(*raw)
                    .map(|value| ResolvedDefiningExpr {
                        expr: DefiningExpr::IntConst(value),
                        ty: ty.clone(),
                    })
                    .map_err(|_| TrustWpClaimError::UnsupportedConstant)
            }
            Constant::Bool(value) if ty == &Ty::Bool => {
                Ok(ResolvedDefiningExpr { expr: DefiningExpr::BoolConst(*value), ty: Ty::Bool })
            }
            // U128 / floats / aggregates / mismatched constant types / everything
            // else refuses — amendment 5: never bit-cast a canonical constant.
            _ => Err(TrustWpClaimError::UnsupportedConstant),
        },
        Inst::Copy { ty, operand } => {
            if ty == &Ty::Error {
                return Err(TrustWpClaimError::MalformedBody("Copy has no concrete type"));
            }
            let resolved = resolve_value(entry, *operand, producer_index, depth + 1)?;
            if &resolved.ty != ty {
                return Err(TrustWpClaimError::MalformedBody(
                    "Copy type does not match its defining operand",
                ));
            }
            Ok(resolved)
        }
        _ => Err(TrustWpClaimError::UnsupportedInstruction),
    }
}

/// One spec variable of the ensures predicate: source name + declared sort
/// (only "int" / "bool" reach v1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClaimVariable {
    pub name: String,
    pub sort: &'static str,
}

/// Build the body-bound `trust-wp.trust-formula.v1` envelope.
///
/// Inputs are the ALREADY-VALIDATED pieces the finalize seam assembled:
/// * `variables` — the ensures predicate's spec variables (each cross-checked
///   upstream against the function's arg locals by position AND name;
///   amendment 4);
/// * `predicate_body` — the ensures predicate translated to sibling JSON by
///   [`spec_predicate_to_sibling_json`] (v1 fragment already enforced there);
/// * `defining` — the walker's result, rendered as the `let result = ...`
///   value; for `EntryParam(k)` the caller passes the matching parameter NAME.
///
/// Construction rules (blueprint "claim_shape", schema spelling corrected to
/// the sibling's pinned `trust-wp.trust-formula.v1`):
/// * NO top-level `result` record — `result` is introduced solely by the
///   `let` (the sibling decoder rejects shadowing);
/// * params referenced by the defining expression but absent from the
///   variables list must be appended by the CALLER before calling (the
///   envelope refuses unbound `var` references defensively).
pub fn body_bound_trust_formula_envelope(
    variables: &[ClaimVariable],
    predicate_body: &Value,
    result_sort: &'static str,
    defining_value: &Value,
) -> Result<Value, TrustWpClaimError> {
    if variables.iter().any(|v| v.name == "result") {
        return Err(TrustWpClaimError::ReservedResultName);
    }
    if !is_v1_claim_sort(result_sort) {
        return Err(TrustWpClaimError::InvalidEnvelope(format!(
            "result sort `{result_sort}` is not `int` or `bool`"
        )));
    }
    let mut declared_names = Vec::with_capacity(variables.len());
    for variable in variables {
        if !is_v1_claim_sort(variable.sort) {
            return Err(TrustWpClaimError::InvalidEnvelope(format!(
                "variable `{}` has unsupported sort `{}`",
                variable.name, variable.sort
            )));
        }
        if !is_v1_claim_name(&variable.name) {
            return Err(TrustWpClaimError::InvalidEnvelope(format!(
                "variable name `{}` is outside the sibling claim-name grammar",
                variable.name
            )));
        }
        if declared_names.contains(&variable.name.as_str()) {
            return Err(TrustWpClaimError::InvalidEnvelope(format!(
                "duplicate variable binding `{}`",
                variable.name
            )));
        }
        declared_names.push(variable.name.as_str());
    }
    // Defensive unbound-variable sweep over both the defining value and the
    // predicate body: every {"var": name} must be a declared variable or the
    // let-bound `result`.
    check_vars_bound(defining_value, &declared_names, false)?;
    check_vars_bound(predicate_body, &declared_names, true)?;

    let vars_json: Vec<Value> =
        variables.iter().map(|v| json!({"name": v.name, "sort": v.sort})).collect();
    Ok(json!({
        "schema": TRUST_WP_TRUST_FORMULA_SCHEMA,
        "variables": vars_json,
        "body": {
            "op": "let",
            "name": "result",
            "sort": result_sort,
            "value": defining_value,
            "body": predicate_body,
        },
    }))
}

fn is_v1_claim_sort(sort: &str) -> bool {
    matches!(sort, "int" | "bool")
}

/// Match the sibling decoder's opaque claim-name grammar locally. Keeping the
/// exact check here prevents this helper from emitting JSON that is known to
/// fail at replay, while the sibling remains the authoritative decoder.
fn is_v1_claim_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| {
            ch == '_'
                || ch.is_ascii_alphanumeric()
                || matches!(ch, '#' | '.' | '[' | ']' | '*' | '@' | '-' | ';' | '=')
        })
}

fn check_vars_bound(
    node: &Value,
    declared: &[&str],
    result_bound: bool,
) -> Result<(), TrustWpClaimError> {
    match node {
        Value::Object(map) => {
            if let Some(Value::String(name)) = map.get("var") {
                let ok = declared.contains(&name.as_str()) || (result_bound && name == "result");
                if !ok {
                    return Err(TrustWpClaimError::UnboundVariable(name.clone()));
                }
            }
            for value in map.values() {
                check_vars_bound(value, declared, result_bound)?;
            }
            Ok(())
        }
        Value::Array(items) => {
            for item in items {
                check_vars_bound(item, declared, result_bound)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Validate and translate one canonical `trust.spec-predicate.v1` predicate
/// into the sibling's expression JSON, enforcing the v1 fragment.
///
/// Accepted: BoolLiteral, IntLiteral (i64-parsable), Variable, Result,
/// Unary Not, Binary {Eq, Ne, Lt, Le, Gt, Ge, And, Or, Implies}.
/// EVERYTHING else refuses (amendment 1: no Add/Sub/Mul/Div/Rem/Neg; no Old /
/// Field / Index / quantifiers / bitwise).
pub fn spec_predicate_to_sibling_json(
    predicate: &TrustSpecPredicate,
) -> Result<Value, TrustWpClaimError> {
    predicate.validate().map_err(TrustWpClaimError::InvalidPredicate)?;
    if predicate.variables.iter().any(|variable| variable.name == "result") {
        return Err(TrustWpClaimError::ReservedResultName);
    }
    spec_expr_to_sibling_json(&predicate.root)
}

fn spec_expr_to_sibling_json(node: &TrustSpecExpr) -> Result<Value, TrustWpClaimError> {
    match &node.kind {
        TrustSpecExprKind::BoolLiteral { value } => Ok(json!({"bool": value})),
        TrustSpecExprKind::IntLiteral { value: raw } => {
            let value: i64 = raw.parse().map_err(|_| TrustWpClaimError::UnsupportedConstant)?;
            Ok(json!({"int": value}))
        }
        TrustSpecExprKind::Variable { name } => {
            if name == "result" {
                return Err(TrustWpClaimError::ReservedResultName);
            }
            Ok(json!({"var": name}))
        }
        TrustSpecExprKind::Result => Ok(json!({"var": "result"})),
        TrustSpecExprKind::Unary { op: TrustSpecUnaryOp::Not, expr } => {
            let inner = spec_expr_to_sibling_json(expr)?;
            Ok(json!({"op": "not", "expr": inner}))
        }
        TrustSpecExprKind::Unary { .. } => {
            Err(TrustWpClaimError::UnsupportedPredicateNode("Unary(non-Not)"))
        }
        TrustSpecExprKind::Binary { op, lhs, rhs } => {
            let sibling_op = match op {
                TrustSpecBinaryOp::Eq => "eq",
                TrustSpecBinaryOp::Ne => "ne",
                TrustSpecBinaryOp::Lt => "lt",
                TrustSpecBinaryOp::Le => "le",
                TrustSpecBinaryOp::Gt => "gt",
                TrustSpecBinaryOp::Ge => "ge",
                TrustSpecBinaryOp::And => "and",
                TrustSpecBinaryOp::Or => "or",
                TrustSpecBinaryOp::Implies => "implies",
                // Amendment 1: Add/Sub/Mul/Div/Rem/... all refuse — machine
                // arithmetic over unbounded Int is a false-proof vector.
                _ => return Err(TrustWpClaimError::UnsupportedPredicateNode("Binary(arith)")),
            };
            let lhs = spec_expr_to_sibling_json(lhs)?;
            let rhs = spec_expr_to_sibling_json(rhs)?;
            Ok(json!({"op": sibling_op, "lhs": lhs, "rhs": rhs}))
        }
        TrustSpecExprKind::Old { .. } => Err(TrustWpClaimError::UnsupportedPredicateNode("Old")),
        TrustSpecExprKind::Field { .. } => {
            Err(TrustWpClaimError::UnsupportedPredicateNode("Field"))
        }
        TrustSpecExprKind::Index { .. } => {
            Err(TrustWpClaimError::UnsupportedPredicateNode("Index"))
        }
        _ => Err(TrustWpClaimError::UnsupportedPredicateNode("unknown")),
    }
}

/// Amendment 2's secondary belt: refuse a refutation-shaped predicate root —
/// a top-level `And` (in sibling JSON) with any direct `not` conjunct.
pub fn reject_refutation_shaped_root(body: &Value) -> Result<(), TrustWpClaimError> {
    let mut frontier = vec![body];
    while let Some(node) = frontier.pop() {
        let Some(op) = node.get("op").and_then(Value::as_str) else {
            return Ok(());
        };
        match op {
            "and" => {
                for side in ["lhs", "rhs"] {
                    if let Some(child) = node.get(side) {
                        if child.get("op").and_then(Value::as_str) == Some("not") {
                            return Err(TrustWpClaimError::RefutationShapedRoot);
                        }
                        frontier.push(child);
                    }
                }
            }
            _ => return Ok(()),
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use trust_ir::{Block, BlockId, FuncTy, FuncTyId, Function, InstrNode};
    use trust_verifier_api::{TrustSpecSort, TrustSpecVariable, TrustSpecVariableOrigin};

    use super::*;

    fn local(name: &str, sort: TrustSpecSort, index: usize) -> TrustSpecVariable {
        TrustSpecVariable {
            name: name.to_string(),
            sort,
            origin: TrustSpecVariableOrigin::Local { index },
        }
    }

    fn walker_module(
        signature_params: Vec<Ty>,
        signature_returns: Vec<Ty>,
        entry: BlockId,
        blocks: Vec<Block>,
    ) -> Module {
        let mut module = Module::new("trust_wp_walker");
        let function_ty = module.add_func_type(FuncTy {
            params: signature_params,
            returns: signature_returns,
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "subject", function_ty, entry);
        function.blocks = blocks;
        module.add_function(function);
        module
    }

    fn single_block_module(
        signature_params: Vec<Ty>,
        return_ty: Ty,
        entry_params: Vec<(ValueId, Ty)>,
        body: Vec<InstrNode>,
    ) -> Module {
        walker_module(
            signature_params,
            vec![return_ty],
            BlockId::new(0),
            vec![Block { id: BlockId::new(0), params: entry_params, body }],
        )
    }

    fn return_value(value: ValueId) -> InstrNode {
        InstrNode::new(Inst::Return { values: vec![value] })
    }

    fn int_constant(result: ValueId, ty: Ty, value: i128) -> InstrNode {
        InstrNode::new(Inst::Const { ty, value: Constant::Int(value) }).with_result(result)
    }

    fn bool_constant(result: ValueId, ty: Ty, value: bool) -> InstrNode {
        InstrNode::new(Inst::Const { ty, value: Constant::Bool(value) }).with_result(result)
    }

    fn copy(result: ValueId, ty: Ty, operand: ValueId) -> InstrNode {
        InstrNode::new(Inst::Copy { ty, operand }).with_result(result)
    }

    #[test]
    fn walker_accepts_entry_parameter() {
        let module = single_block_module(
            vec![Ty::I64, Ty::Bool],
            Ty::Bool,
            vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::Bool)],
            vec![return_value(ValueId::new(1))],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&module, FuncId::new(0)),
            Ok(DefiningExpr::EntryParam(1))
        );
    }

    #[test]
    fn walker_accepts_integer_and_boolean_constants() {
        let integer = single_block_module(
            vec![],
            Ty::I64,
            vec![],
            vec![int_constant(ValueId::new(0), Ty::I64, -41), return_value(ValueId::new(0))],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&integer, FuncId::new(0)),
            Ok(DefiningExpr::IntConst(-41))
        );

        let boolean = single_block_module(
            vec![],
            Ty::Bool,
            vec![],
            vec![bool_constant(ValueId::new(0), Ty::Bool, true), return_value(ValueId::new(0))],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&boolean, FuncId::new(0)),
            Ok(DefiningExpr::BoolConst(true))
        );
    }

    #[test]
    fn walker_accepts_dominated_well_typed_copy_chain() {
        let module = single_block_module(
            vec![Ty::I64],
            Ty::I64,
            vec![(ValueId::new(0), Ty::I64)],
            vec![
                copy(ValueId::new(1), Ty::I64, ValueId::new(0)),
                copy(ValueId::new(2), Ty::I64, ValueId::new(1)),
                return_value(ValueId::new(2)),
            ],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&module, FuncId::new(0)),
            Ok(DefiningExpr::EntryParam(0))
        );
    }

    #[test]
    fn walker_refuses_missing_and_duplicate_function_identity() {
        assert_eq!(
            trust_wp_result_defining_expr(&Module::new("empty"), FuncId::new(0)),
            Err(TrustWpClaimError::MissingFunction)
        );

        let mut duplicate = single_block_module(
            vec![],
            Ty::Bool,
            vec![],
            vec![bool_constant(ValueId::new(0), Ty::Bool, true), return_value(ValueId::new(0))],
        );
        duplicate.functions.push(duplicate.functions[0].clone());
        assert_eq!(
            trust_wp_result_defining_expr(&duplicate, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody("function id is not unique"))
        );
    }

    #[test]
    fn walker_refuses_multiple_blocks() {
        let module = walker_module(
            vec![Ty::I64],
            vec![Ty::I64],
            BlockId::new(0),
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![(ValueId::new(0), Ty::I64)],
                    body: vec![return_value(ValueId::new(0))],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(ValueId::new(1), Ty::I64)],
                    body: vec![return_value(ValueId::new(1))],
                },
            ],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&module, FuncId::new(0)),
            Err(TrustWpClaimError::MultipleBlocks)
        );
    }

    #[test]
    fn walker_refuses_bad_return_shape_and_unresolved_return() {
        let empty = single_block_module(vec![], Ty::I64, vec![], vec![]);
        assert_eq!(
            trust_wp_result_defining_expr(&empty, FuncId::new(0)),
            Err(TrustWpClaimError::NoSingleReturn)
        );

        let no_value = single_block_module(
            vec![],
            Ty::I64,
            vec![],
            vec![InstrNode::new(Inst::Return { values: vec![] })],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&no_value, FuncId::new(0)),
            Err(TrustWpClaimError::NoSingleReturn)
        );

        let too_many = single_block_module(
            vec![Ty::I64, Ty::I64],
            Ty::I64,
            vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(0), ValueId::new(1)] })],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&too_many, FuncId::new(0)),
            Err(TrustWpClaimError::NoSingleReturn)
        );

        let unresolved =
            single_block_module(vec![], Ty::I64, vec![], vec![return_value(ValueId::new(99))]);
        assert_eq!(
            trust_wp_result_defining_expr(&unresolved, FuncId::new(0)),
            Err(TrustWpClaimError::UnresolvedValue)
        );
    }

    #[test]
    fn walker_refuses_non_const_copy_producer() {
        let module = single_block_module(
            vec![Ty::I64, Ty::I64],
            Ty::I64,
            vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            vec![
                InstrNode::new(Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                return_value(ValueId::new(2)),
            ],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&module, FuncId::new(0)),
            Err(TrustWpClaimError::UnsupportedInstruction)
        );
    }

    #[test]
    fn walker_refuses_integer_constant_outside_i64() {
        let module = single_block_module(
            vec![],
            Ty::I128,
            vec![],
            vec![
                int_constant(ValueId::new(0), Ty::I128, i128::from(i64::MAX) + 1),
                return_value(ValueId::new(0)),
            ],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&module, FuncId::new(0)),
            Err(TrustWpClaimError::UnsupportedConstant)
        );
    }

    #[test]
    fn walker_refuses_untyped_mismatched_and_out_of_type_constants() {
        for module in [
            single_block_module(
                vec![],
                Ty::I64,
                vec![],
                vec![int_constant(ValueId::new(0), Ty::Error, 1), return_value(ValueId::new(0))],
            ),
            single_block_module(
                vec![],
                Ty::I64,
                vec![],
                vec![bool_constant(ValueId::new(0), Ty::I64, true), return_value(ValueId::new(0))],
            ),
            single_block_module(
                vec![],
                Ty::Bool,
                vec![],
                vec![int_constant(ValueId::new(0), Ty::Bool, 1), return_value(ValueId::new(0))],
            ),
            single_block_module(
                vec![],
                Ty::U8,
                vec![],
                vec![int_constant(ValueId::new(0), Ty::U8, 256), return_value(ValueId::new(0))],
            ),
        ] {
            assert_eq!(
                trust_wp_result_defining_expr(&module, FuncId::new(0)),
                Err(TrustWpClaimError::UnsupportedConstant)
            );
        }
    }

    #[test]
    fn walker_refuses_untyped_and_mismatched_copies() {
        let untyped = single_block_module(
            vec![Ty::I64],
            Ty::I64,
            vec![(ValueId::new(0), Ty::I64)],
            vec![copy(ValueId::new(1), Ty::Error, ValueId::new(0)), return_value(ValueId::new(1))],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&untyped, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody("Copy has no concrete type"))
        );

        let mismatched = single_block_module(
            vec![Ty::I64],
            Ty::I32,
            vec![(ValueId::new(0), Ty::I64)],
            vec![copy(ValueId::new(1), Ty::I32, ValueId::new(0)), return_value(ValueId::new(1))],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&mismatched, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody("Copy type does not match its defining operand"))
        );
    }

    #[test]
    fn walker_refuses_duplicate_ssa_definitions() {
        let duplicate_parameter = single_block_module(
            vec![Ty::I64],
            Ty::I64,
            vec![(ValueId::new(0), Ty::I64)],
            vec![int_constant(ValueId::new(0), Ty::I64, 5), return_value(ValueId::new(0))],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&duplicate_parameter, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody("duplicate SSA definition"))
        );

        let duplicate_result = single_block_module(
            vec![],
            Ty::I64,
            vec![],
            vec![
                int_constant(ValueId::new(0), Ty::I64, 5),
                int_constant(ValueId::new(0), Ty::I64, 6),
                return_value(ValueId::new(0)),
            ],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&duplicate_result, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody("duplicate SSA definition"))
        );
    }

    #[test]
    fn walker_refuses_use_before_definition_and_copy_cycle() {
        let use_before_definition = single_block_module(
            vec![],
            Ty::I64,
            vec![],
            vec![
                copy(ValueId::new(0), Ty::I64, ValueId::new(1)),
                int_constant(ValueId::new(1), Ty::I64, 5),
                return_value(ValueId::new(0)),
            ],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&use_before_definition, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody("SSA use is not dominated by its definition"))
        );

        let cycle = single_block_module(
            vec![],
            Ty::I64,
            vec![],
            vec![
                copy(ValueId::new(0), Ty::I64, ValueId::new(1)),
                copy(ValueId::new(1), Ty::I64, ValueId::new(0)),
                return_value(ValueId::new(1)),
            ],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&cycle, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody("SSA use is not dominated by its definition"))
        );
    }

    #[test]
    fn walker_refuses_signature_and_entry_mismatches() {
        let wrong_entry = walker_module(
            vec![Ty::I64],
            vec![Ty::I64],
            BlockId::new(1),
            vec![Block {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), Ty::I64)],
                body: vec![return_value(ValueId::new(0))],
            }],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&wrong_entry, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody("sole block is not the declared entry"))
        );

        let wrong_param = single_block_module(
            vec![Ty::I64],
            Ty::Bool,
            vec![(ValueId::new(0), Ty::Bool)],
            vec![return_value(ValueId::new(0))],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&wrong_param, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody(
                "entry parameters do not match the function signature"
            ))
        );

        let wrong_return = single_block_module(
            vec![Ty::Bool],
            Ty::I64,
            vec![(ValueId::new(0), Ty::Bool)],
            vec![return_value(ValueId::new(0))],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&wrong_return, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody(
                "returned value type does not match the function signature"
            ))
        );

        let mut missing_signature = single_block_module(
            vec![],
            Ty::Bool,
            vec![],
            vec![bool_constant(ValueId::new(0), Ty::Bool, true), return_value(ValueId::new(0))],
        );
        missing_signature.functions[0].ty = FuncTyId::new(99);
        assert_eq!(
            trust_wp_result_defining_expr(&missing_signature, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody("function type is missing"))
        );

        let mut variadic = single_block_module(
            vec![Ty::I64],
            Ty::I64,
            vec![(ValueId::new(0), Ty::I64)],
            vec![return_value(ValueId::new(0))],
        );
        variadic.func_types[0].is_vararg = true;
        assert_eq!(
            trust_wp_result_defining_expr(&variadic, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody("variadic function signatures are unsupported"))
        );

        let no_return_type = walker_module(
            vec![],
            vec![],
            BlockId::new(0),
            vec![Block {
                id: BlockId::new(0),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            }],
        );
        assert_eq!(
            trust_wp_result_defining_expr(&no_return_type, FuncId::new(0)),
            Err(TrustWpClaimError::MalformedBody(
                "function signature does not have exactly one return"
            ))
        );
    }

    /// The blueprint's golden ge_refl envelope: `ensures result >= x { x }`.
    #[test]
    fn golden_ge_refl_envelope() {
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Ge,
                TrustSpecExpr::result(TrustSpecSort::Int),
                TrustSpecExpr::variable("x", TrustSpecSort::Int),
            ),
            vec![local("x", TrustSpecSort::Int, 0)],
        );
        // Pin the actual canonical serde representation at this integration
        // boundary, then lower the round-tripped public type rather than a
        // hand-authored lookalike JSON schema.
        let canonical = serde_json::to_value(&predicate).expect("serialize canonical predicate");
        assert_eq!(
            canonical,
            json!({
                "schema_version": "trust.spec-predicate.v1",
                "root": {
                    "sort": "bool",
                    "kind": {
                        "node": "binary",
                        "op": "ge",
                        "lhs": {
                            "sort": "int",
                            "kind": {"node": "result"},
                        },
                        "rhs": {
                            "sort": "int",
                            "kind": {"node": "variable", "name": "x"},
                        },
                    },
                },
                "root_sort": "bool",
                "variables": [{
                    "name": "x",
                    "sort": "int",
                    "origin": {"origin": "local", "index": 0},
                }],
            })
        );
        let canonical: TrustSpecPredicate =
            serde_json::from_value(canonical).expect("round-trip canonical predicate");
        let body = spec_predicate_to_sibling_json(&canonical).expect("v1 fragment");
        reject_refutation_shaped_root(&body).expect("not refutation-shaped");
        let envelope = body_bound_trust_formula_envelope(
            &[ClaimVariable { name: "x".into(), sort: "int" }],
            &body,
            "int",
            &json!({"var": "x"}),
        )
        .expect("envelope");
        assert_eq!(
            envelope,
            json!({
                "schema": "trust-wp.trust-formula.v1",
                "variables": [{"name": "x", "sort": "int"}],
                "body": {
                    "op": "let",
                    "name": "result",
                    "sort": "int",
                    "value": {"var": "x"},
                    "body": {"op": "ge", "lhs": {"var": "result"}, "rhs": {"var": "x"}},
                },
            })
        );
    }

    /// Amendment 1 (falsification): arithmetic in the predicate REFUSES —
    /// `ensures result + 1 > result` is the confirmed Int-vs-u64 false proof.
    #[test]
    fn arithmetic_predicate_refuses() {
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Gt,
                TrustSpecExpr::binary(
                    TrustSpecBinaryOp::Add,
                    TrustSpecExpr::result(TrustSpecSort::Int),
                    TrustSpecExpr::int_literal("1"),
                ),
                TrustSpecExpr::result(TrustSpecSort::Int),
            ),
            Vec::new(),
        );
        assert_eq!(
            spec_predicate_to_sibling_json(&predicate),
            Err(TrustWpClaimError::UnsupportedPredicateNode("Binary(arith)"))
        );
    }

    /// A spec variable literally named `result` refuses (shadowing).
    #[test]
    fn result_named_variable_refuses() {
        let body = json!({"op": "ge", "lhs": {"var": "result"}, "rhs": {"var": "x"}});
        let err = body_bound_trust_formula_envelope(
            &[
                ClaimVariable { name: "x".into(), sort: "int" },
                ClaimVariable { name: "result".into(), sort: "int" },
            ],
            &body,
            "int",
            &json!({"var": "x"}),
        );
        assert_eq!(err, Err(TrustWpClaimError::ReservedResultName));
    }

    #[test]
    fn invalid_envelope_binding_names_sorts_and_duplicates_refuse_locally() {
        let body = json!({"bool": true});
        let defining = json!({"int": 0});

        assert_eq!(
            body_bound_trust_formula_envelope(&[], &body, "seq", &defining),
            Err(TrustWpClaimError::InvalidEnvelope(
                "result sort `seq` is not `int` or `bool`".into()
            ))
        );
        assert_eq!(
            body_bound_trust_formula_envelope(
                &[ClaimVariable { name: "x".into(), sort: "seq" }],
                &body,
                "int",
                &defining,
            ),
            Err(TrustWpClaimError::InvalidEnvelope(
                "variable `x` has unsupported sort `seq`".into()
            ))
        );
        assert_eq!(
            body_bound_trust_formula_envelope(
                &[ClaimVariable { name: "".into(), sort: "int" }],
                &body,
                "int",
                &defining,
            ),
            Err(TrustWpClaimError::InvalidEnvelope(
                "variable name `` is outside the sibling claim-name grammar".into()
            ))
        );
        assert_eq!(
            body_bound_trust_formula_envelope(
                &[ClaimVariable { name: "9x".into(), sort: "int" }],
                &body,
                "int",
                &defining,
            ),
            Err(TrustWpClaimError::InvalidEnvelope(
                "variable name `9x` is outside the sibling claim-name grammar".into()
            ))
        );
        assert_eq!(
            body_bound_trust_formula_envelope(
                &[
                    ClaimVariable { name: "x".into(), sort: "int" },
                    ClaimVariable { name: "x".into(), sort: "int" },
                ],
                &body,
                "int",
                &defining,
            ),
            Err(TrustWpClaimError::InvalidEnvelope("duplicate variable binding `x`".into()))
        );
    }

    /// Old() refuses (two-state is not v1).
    #[test]
    fn old_refuses() {
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::old(TrustSpecExpr::variable("p", TrustSpecSort::Bool)),
            vec![local("p", TrustSpecSort::Bool, 0)],
        );
        assert_eq!(
            spec_predicate_to_sibling_json(&predicate),
            Err(TrustWpClaimError::UnsupportedPredicateNode("Old"))
        );
    }

    #[test]
    fn invalid_canonical_predicate_refuses_before_lowering() {
        let mut predicate = TrustSpecPredicate::new(TrustSpecExpr::bool_literal(true), Vec::new());
        predicate.schema_version = "trust.spec-predicate.future".to_string();
        assert!(matches!(
            spec_predicate_to_sibling_json(&predicate),
            Err(TrustWpClaimError::InvalidPredicate(_))
        ));

        let mut inconsistent_root =
            TrustSpecPredicate::new(TrustSpecExpr::bool_literal(true), Vec::new());
        inconsistent_root.root_sort = TrustSpecSort::Int;
        assert!(matches!(
            spec_predicate_to_sibling_json(&inconsistent_root),
            Err(TrustWpClaimError::InvalidPredicate(reason))
                if reason.contains("root must be consistently Bool-sorted")
        ));

        let undeclared = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                TrustSpecExpr::variable("x", TrustSpecSort::Int),
                TrustSpecExpr::int_literal("0"),
            ),
            Vec::new(),
        );
        assert!(matches!(
            spec_predicate_to_sibling_json(&undeclared),
            Err(TrustWpClaimError::InvalidPredicate(reason))
                if reason.contains("variable `x` is undeclared")
        ));

        let x = local("x", TrustSpecSort::Int, 0);
        let duplicate =
            TrustSpecPredicate::new(TrustSpecExpr::bool_literal(true), vec![x.clone(), x]);
        assert!(matches!(
            spec_predicate_to_sibling_json(&duplicate),
            Err(TrustWpClaimError::InvalidPredicate(reason))
                if reason.contains("duplicate variables")
        ));

        let mut inconsistent_operand = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Ge,
                TrustSpecExpr::result(TrustSpecSort::Int),
                TrustSpecExpr::int_literal("0"),
            ),
            Vec::new(),
        );
        let TrustSpecExprKind::Binary { lhs, .. } = &mut inconsistent_operand.root.kind else {
            unreachable!("test fixture is binary")
        };
        lhs.sort = TrustSpecSort::Bool;
        assert!(matches!(
            spec_predicate_to_sibling_json(&inconsistent_operand),
            Err(TrustWpClaimError::InvalidPredicate(reason))
                if reason.contains("binary lhs has inconsistent sort")
        ));
    }

    /// Refutation-shaped root refuses: `P && !Q` at the top.
    #[test]
    fn refutation_root_refuses() {
        let body = json!({"op": "and",
            "lhs": {"op": "ge", "lhs": {"var": "x"}, "rhs": {"int": 0}},
            "rhs": {"op": "not", "expr": {"op": "ge", "lhs": {"var": "x"}, "rhs": {"int": 0}}}});
        assert_eq!(
            reject_refutation_shaped_root(&body),
            Err(TrustWpClaimError::RefutationShapedRoot)
        );
    }

    /// Unbound variable in the predicate refuses.
    #[test]
    fn unbound_variable_refuses() {
        let body = json!({"op": "ge", "lhs": {"var": "result"}, "rhs": {"var": "y"}});
        let err = body_bound_trust_formula_envelope(
            &[ClaimVariable { name: "x".into(), sort: "int" }],
            &body,
            "int",
            &json!({"var": "x"}),
        );
        assert_eq!(err, Err(TrustWpClaimError::UnboundVariable("y".into())));
    }
}
