// trust-transval: Router-backed SMT translation validation
//
// Provides a solver-facing API over trust-transval's VC generation. The
// validator uses trust-router for backend dispatch. The default constructor is
// fail-closed; callers must explicitly supply a router before solver-backed
// translation validation can be accepted.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_router::Router;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Counterexample, CounterexampleValue, Formula,
    LocalDecl, Operand, Rvalue, Sort, Statement, Ty, VcKind, VerifiableFunction,
    VerificationCondition, VerificationResult,
};
use trust_vcgen::simplify::{boolean_simplify, constant_fold};

use crate::equivalence::EquivalenceVcGenerator;
use crate::error::TransvalError;
use crate::refinement::{RefinementChecker, ValidationVerdict};
use crate::simulation::SimulationRelationBuilder;

/// Per-VC solver outcome.
#[derive(Debug, Clone)]
pub struct VcOutcome {
    /// The VC that was dispatched to the router.
    pub vc: VerificationCondition,
    /// The router/backend result for that VC.
    pub result: VerificationResult,
}

/// SMT-backed translation-validation result.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum SmtValidationResult {
    /// Every validation condition was UNSAT.
    Equivalent { proof_time_ms: u64, proof_certificates: Vec<Vec<u8>> },
    /// At least one validation condition was SAT.
    Divergent { counterexamples: Vec<Counterexample>, time_ms: u64 },
    /// The solver stack could not fully classify the VC set.
    Inconclusive { reason: String, partial_results: Vec<VcOutcome> },
}

/// SMT-backed property-checking result.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum SmtPropertyResult {
    /// The negated property was UNSAT.
    Holds { time_ms: u64 },
    /// The negated property was SAT.
    Violated { counterexample: Counterexample, time_ms: u64 },
    /// The solver stack could not classify the property VC.
    Inconclusive { reason: String },
}

/// Router-backed translation validator.
///
/// The default validator is fail-closed and returns inconclusive solver
/// outcomes. Callers that want backend dispatch must inject a router configured
/// for the intended proof backend.
pub struct TranslationValidator {
    router: Router,
    dispatch_enabled: bool,
}

impl Default for TranslationValidator {
    fn default() -> Self {
        Self::new()
    }
}

impl TranslationValidator {
    /// Create a fail-closed validator without trusted solver dispatch.
    #[must_use]
    pub fn new() -> Self {
        Self { router: Router::new(), dispatch_enabled: false }
    }

    /// Create a validator with a caller-provided router.
    #[must_use]
    pub fn with_router(router: Router) -> Self {
        Self { router, dispatch_enabled: true }
    }

    /// Validate that `target` refines `source`.
    pub fn validate_refinement(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Result<SmtValidationResult, TransvalError> {
        let validation = RefinementChecker::new().check(source, target)?;
        let verdict = validation.verdict.clone();
        let vcs = validation.vcs;

        if let ValidationVerdict::Unknown { reason } = &verdict
            && vcs.is_empty()
        {
            return Ok(SmtValidationResult::Inconclusive {
                reason: reason.clone(),
                partial_results: Vec::new(),
            });
        }

        let mut prepared = if vcs.is_empty() {
            vec![PreparedVc::new(structural_vc(
                target,
                "no verification conditions generated".to_string(),
                Formula::Bool(true),
            ))]
        } else {
            vcs.into_iter().map(PreparedVc::new).collect()
        };

        if let ValidationVerdict::Refuted { reason } = &verdict {
            force_divergence(&mut prepared, Counterexample::new(Vec::new()), reason);
        } else {
            normalize_refinement_vcs(source, target, &mut prepared);
        }

        Ok(aggregate_validation(self.dispatch_all(prepared)))
    }

    /// Validate a specific source/target block pair.
    pub fn validate_block_pair(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
        source_block: BlockId,
        target_block: BlockId,
    ) -> Result<SmtValidationResult, TransvalError> {
        let relation = SimulationRelationBuilder::new().build_from_functions(source, target)?;
        let vcs = EquivalenceVcGenerator::new().generate_for_block_pair(
            source,
            target,
            &relation,
            source_block,
            target_block,
        )?;

        if vcs.is_empty() {
            return Ok(SmtValidationResult::Inconclusive {
                reason: format!(
                    "no verification conditions generated for block pair {source_block:?} -> {target_block:?}"
                ),
                partial_results: Vec::new(),
            });
        }

        let mut prepared = vcs.into_iter().map(PreparedVc::new).collect::<Vec<_>>();
        normalize_block_pair_vcs(source, target, source_block, target_block, &mut prepared);

        Ok(aggregate_validation(self.dispatch_all(prepared)))
    }

    /// Check a user-specified property on a function.
    ///
    /// The VC asserts `NOT(property)`. UNSAT means the property holds; SAT
    /// yields a counterexample showing the property can be violated.
    pub fn check_property(
        &self,
        func: &VerifiableFunction,
        property: &Formula,
    ) -> Result<SmtPropertyResult, TransvalError> {
        let mut prepared = PreparedVc::new(VerificationCondition {
            kind: VcKind::TranslationValidation {
                pass: "user-property".to_string(),
                check: "property".to_string(),
            },
            function: func.name.clone().into(),
            location: func.span.clone(),
            formula: Formula::Not(Box::new(property.clone())),
            contract_metadata: None,
            obligation: None,
        });

        normalize_property_vc(&mut prepared);
        let outcome = self.dispatch_one(prepared);

        Ok(match outcome.result {
            VerificationResult::Proved { time_ms, .. } => SmtPropertyResult::Holds { time_ms },
            VerificationResult::Failed { time_ms, counterexample, .. } => {
                SmtPropertyResult::Violated {
                    counterexample: counterexample
                        .unwrap_or_else(|| Counterexample::new(Vec::new())),
                    time_ms,
                }
            }
            VerificationResult::Unknown { reason, .. } => {
                SmtPropertyResult::Inconclusive { reason }
            }
            VerificationResult::Timeout { solver, timeout_ms } => SmtPropertyResult::Inconclusive {
                reason: format!("{solver} timed out after {timeout_ms}ms while checking property"),
            },
            _ => SmtPropertyResult::Inconclusive {
                reason: "unsupported verification result".to_string(),
            },
        })
    }

    fn dispatch_all(&self, vcs: Vec<PreparedVc>) -> Vec<VcOutcome> {
        vcs.into_iter().map(|vc| self.dispatch_one(vc)).collect()
    }

    fn dispatch_one(&self, prepared: PreparedVc) -> VcOutcome {
        if !self.dispatch_enabled {
            return VcOutcome {
                vc: prepared.vc,
                result: VerificationResult::Unknown {
                    solver: "translation-validator".into(),
                    time_ms: 0,
                    reason: "no trusted solver router supplied; construct with TranslationValidator::with_router".to_string(),
                },
            };
        }
        let result = attach_counterexample(
            self.router.verify_one(&prepared.vc),
            prepared.synthetic_counterexample,
        );

        VcOutcome { vc: prepared.vc, result }
    }
}

#[derive(Debug)]
struct PreparedVc {
    vc: VerificationCondition,
    synthetic_counterexample: Option<Counterexample>,
}

impl PreparedVc {
    fn new(mut vc: VerificationCondition) -> Self {
        vc.formula = simplify_formula(vc.formula);
        let synthetic_counterexample =
            matches!(vc.formula, Formula::Bool(true)).then(|| Counterexample::new(Vec::new()));

        Self { vc, synthetic_counterexample }
    }
}

#[derive(Debug)]
enum StraightLineOutcome {
    Divergent(Counterexample),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum EvalValue {
    Bool(bool),
    Int(i128),
    UInt(u128),
}

fn aggregate_validation(outcomes: Vec<VcOutcome>) -> SmtValidationResult {
    if outcomes.is_empty() {
        return SmtValidationResult::Inconclusive {
            reason: "no verification conditions were dispatched".to_string(),
            partial_results: Vec::new(),
        };
    }

    let total_time_ms = outcomes.iter().map(|outcome| outcome.result.time_ms()).sum();

    let mut proof_certificates = Vec::new();
    let mut counterexamples = Vec::new();
    let mut inconclusive_reasons = Vec::new();

    let mut has_failed = false;
    let mut has_inconclusive = false;

    for outcome in &outcomes {
        match &outcome.result {
            VerificationResult::Proved { proof_certificate, .. } => {
                if let Some(cert) = proof_certificate {
                    proof_certificates.push(cert.clone());
                }
            }
            VerificationResult::Failed { counterexample, .. } => {
                has_failed = true;
                counterexamples.push(
                    counterexample.clone().unwrap_or_else(|| Counterexample::new(Vec::new())),
                );
            }
            VerificationResult::Unknown { solver, reason, .. } => {
                has_inconclusive = true;
                inconclusive_reasons.push(format!("{solver}: {reason}"));
            }
            VerificationResult::Timeout { solver, timeout_ms } => {
                has_inconclusive = true;
                inconclusive_reasons.push(format!("{solver} timed out after {timeout_ms}ms"));
            }
            _ => {
                has_inconclusive = true;
                inconclusive_reasons.push("unsupported verification result".to_string());
            }
        }
    }

    if has_failed {
        return SmtValidationResult::Divergent { counterexamples, time_ms: total_time_ms };
    }

    if has_inconclusive {
        let reason = if inconclusive_reasons.is_empty() {
            "solver returned inconclusive results".to_string()
        } else {
            inconclusive_reasons.join("; ")
        };

        return SmtValidationResult::Inconclusive { reason, partial_results: outcomes };
    }

    SmtValidationResult::Equivalent { proof_time_ms: total_time_ms, proof_certificates }
}

fn normalize_refinement_vcs(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
    prepared: &mut [PreparedVc],
) {
    if prepared.is_empty() {
        return;
    }

    if let Some(outcome) = straight_line_function_outcome(source, target) {
        apply_straight_line_outcome(prepared, outcome);
    }
}

fn normalize_block_pair_vcs(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
    source_block: BlockId,
    target_block: BlockId,
    prepared: &mut [PreparedVc],
) {
    if prepared.is_empty() {
        return;
    }

    if let Some(outcome) = straight_line_block_outcome(source, target, source_block, target_block) {
        apply_straight_line_outcome(prepared, outcome);
    }
}

fn normalize_property_vc(prepared: &mut PreparedVc) {
    prepared.vc.formula = simplify_formula(prepared.vc.formula.clone());

    if matches!(prepared.vc.formula, Formula::Bool(true)) {
        prepared.synthetic_counterexample = Some(Counterexample::new(Vec::new()));
        return;
    }

    if matches!(prepared.vc.formula, Formula::Bool(false)) {
        prepared.synthetic_counterexample = None;
        return;
    }

    if let Some(counterexample) = find_counterexample_for_formula(&prepared.vc.formula) {
        prepared.vc.formula = Formula::Bool(true);
        prepared.synthetic_counterexample = Some(counterexample);
    }
}

fn apply_straight_line_outcome(prepared: &mut [PreparedVc], outcome: StraightLineOutcome) {
    // The straight-line analysis is a divergence *detector* only; it never
    // positively validates (see `straight_line_block_outcome`). A proposed
    // divergence is the fail-safe direction (a false divergence is a
    // conservative reject, never a false-PROVE), so it is the only outcome that
    // rewrites the prepared VCs.
    let StraightLineOutcome::Divergent(counterexample) = outcome;
    force_divergence(prepared, counterexample, "straight-line mismatch");
}

fn force_divergence(prepared: &mut [PreparedVc], counterexample: Counterexample, reason: &str) {
    if let Some((first, rest)) = prepared.split_first_mut() {
        first.vc.formula = Formula::Bool(true);
        first.synthetic_counterexample = Some(counterexample);

        if let VcKind::TranslationValidation { check, .. } = &mut first.vc.kind {
            *check = reason.to_string();
        }

        for vc in rest {
            vc.vc.formula = Formula::Bool(false);
            vc.synthetic_counterexample = None;
        }
    }
}

fn attach_counterexample(
    result: VerificationResult,
    synthetic_counterexample: Option<Counterexample>,
) -> VerificationResult {
    match result {
        VerificationResult::Failed { solver, time_ms, counterexample } => {
            VerificationResult::Failed {
                solver,
                time_ms,
                counterexample: counterexample.or(synthetic_counterexample),
            }
        }
        other => other,
    }
}

fn structural_vc(
    func: &VerifiableFunction,
    check: String,
    formula: Formula,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::TranslationValidation { pass: "refinement".to_string(), check },
        function: func.name.clone().into(),
        location: func.span.clone(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

fn straight_line_function_outcome(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> Option<StraightLineOutcome> {
    if source.body.blocks.len() != 1 || target.body.blocks.len() != 1 {
        return None;
    }

    let source_block = source.body.blocks.first()?.id;
    let target_block = target.body.blocks.first()?.id;
    straight_line_block_outcome(source, target, source_block, target_block)
}

fn straight_line_block_outcome(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
    source_block: BlockId,
    target_block: BlockId,
) -> Option<StraightLineOutcome> {
    let source_expr = evaluate_return_expr_for_block(source, source_block)?;
    let target_expr = evaluate_return_expr_for_block(target, target_block)?;

    let source_expr = simplify_formula(source_expr);
    let target_expr = simplify_formula(target_expr);

    // Soundness: syntactic equality of the simplified return expressions is NOT
    // a refinement proof, so the shortcut must never positively validate from
    // it. `local_formula` types every machine integer as the unbounded
    // `Sort::Int`, `evaluate_rvalue` models `Cast` as identity (no
    // truncation/width), and this comparison ignores memory effects and panics
    // entirely — two functions differing only by a truncating cast (`x as u8`
    // vs `x`) compare equal here. On equality we therefore defer to the real,
    // width-aware VC dispatched to the solver (or fail closed to `Unknown` when
    // no router is attached), rather than discharging the obligation to
    // `Bool(false)`. The shortcut only ever *proposes a divergence*.
    if source_expr == target_expr {
        return None;
    }

    let mismatch =
        Formula::Not(Box::new(Formula::Eq(Box::new(source_expr), Box::new(target_expr))));

    find_counterexample_for_formula(&mismatch).map(StraightLineOutcome::Divergent)
}

fn evaluate_return_expr_for_block(func: &VerifiableFunction, block_id: BlockId) -> Option<Formula> {
    let block = find_block(func, block_id)?;
    if !matches!(block.terminator, trust_types::Terminator::Return) {
        return None;
    }

    let mut locals = func
        .body
        .locals
        .iter()
        .map(|decl| (decl.index, local_formula(decl)))
        .collect::<BTreeMap<_, _>>();

    for stmt in &block.stmts {
        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                if !place.projections.is_empty() {
                    return None;
                }
                let value = evaluate_rvalue(rvalue, &locals)?;
                locals.insert(place.local, simplify_formula(value));
            }
            Statement::Nop => {}
            _ => return None,
        }
    }

    locals.get(&0).cloned()
}

fn find_block(func: &VerifiableFunction, block_id: BlockId) -> Option<&BasicBlock> {
    func.body.blocks.iter().find(|block| block.id == block_id)
}

fn local_formula(local: &LocalDecl) -> Formula {
    let name = local.name.clone().unwrap_or_else(|| format!("_{}", local.index));
    let sort = match &local.ty {
        Ty::Bool => Sort::Bool,
        _ => Sort::Int,
    };

    Formula::Var(name, sort)
}

fn evaluate_rvalue(rvalue: &Rvalue, locals: &BTreeMap<usize, Formula>) -> Option<Formula> {
    match rvalue {
        Rvalue::Use(operand) => evaluate_operand(operand, locals),
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let lhs = evaluate_operand(lhs, locals)?;
            let rhs = evaluate_operand(rhs, locals)?;
            apply_binop(*op, lhs, rhs)
        }
        Rvalue::UnaryOp(trust_types::UnOp::Neg, operand) => {
            let inner = evaluate_operand(operand, locals)?;
            Some(Formula::Neg(Box::new(inner)))
        }
        Rvalue::UnaryOp(trust_types::UnOp::Not, operand) => {
            let inner = evaluate_operand(operand, locals)?;
            Some(Formula::Not(Box::new(inner)))
        }
        Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, operand) | Rvalue::Cast(operand, _) => {
            evaluate_operand(operand, locals)
        }
        _ => None,
    }
}

fn evaluate_operand(operand: &Operand, locals: &BTreeMap<usize, Formula>) -> Option<Formula> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            if !place.projections.is_empty() {
                return None;
            }
            locals.get(&place.local).cloned()
        }
        Operand::Constant(value) => const_to_formula(value),
        Operand::Symbolic(formula) => Some(formula.clone()),
        _ => None,
    }
}

fn const_to_formula(value: &ConstValue) -> Option<Formula> {
    match value {
        ConstValue::Bool(value) => Some(Formula::Bool(*value)),
        ConstValue::Int(value) => Some(Formula::Int(*value)),
        ConstValue::Uint(value, _) => Some(Formula::UInt(*value)),
        _ => None,
    }
}

fn apply_binop(op: BinOp, lhs: Formula, rhs: Formula) -> Option<Formula> {
    match op {
        BinOp::Add => Some(Formula::Add(Box::new(lhs), Box::new(rhs))),
        BinOp::Sub => Some(Formula::Sub(Box::new(lhs), Box::new(rhs))),
        BinOp::Mul => Some(Formula::Mul(Box::new(lhs), Box::new(rhs))),
        BinOp::Div => Some(Formula::Div(Box::new(lhs), Box::new(rhs))),
        BinOp::Rem => Some(Formula::Rem(Box::new(lhs), Box::new(rhs))),
        BinOp::Eq => Some(Formula::Eq(Box::new(lhs), Box::new(rhs))),
        BinOp::Ne => Some(Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs))))),
        BinOp::Lt => Some(Formula::Lt(Box::new(lhs), Box::new(rhs))),
        BinOp::Le => Some(Formula::Le(Box::new(lhs), Box::new(rhs))),
        BinOp::Gt => Some(Formula::Gt(Box::new(lhs), Box::new(rhs))),
        BinOp::Ge => Some(Formula::Ge(Box::new(lhs), Box::new(rhs))),
        _ => None,
    }
}

fn simplify_formula(mut formula: Formula) -> Formula {
    for _ in 0..6 {
        let next = boolean_simplify(constant_fold(formula.clone()));
        if next == formula {
            return next;
        }
        formula = next;
    }
    formula
}

fn find_counterexample_for_formula(formula: &Formula) -> Option<Counterexample> {
    let vars = collect_variables(formula);
    if vars.len() > 4 {
        return None;
    }

    let mut assignments = BTreeMap::new();
    search_counterexample(&vars, 0, formula, &mut assignments)
}

fn collect_variables(formula: &Formula) -> Vec<(String, Sort)> {
    let mut vars = BTreeMap::new();
    formula.visit(&mut |term| {
        if let Formula::Var(name, sort) = term {
            vars.entry(name.clone()).or_insert_with(|| sort.clone());
        }
    });
    vars.into_iter().collect()
}

fn search_counterexample(
    vars: &[(String, Sort)],
    index: usize,
    formula: &Formula,
    assignments: &mut BTreeMap<String, EvalValue>,
) -> Option<Counterexample> {
    if index == vars.len() {
        let value = eval_formula(formula, assignments)?;
        if matches!(value, EvalValue::Bool(true)) {
            let assignments = assignments
                .iter()
                .map(|(name, value)| (name.clone(), counterexample_value(value)))
                .collect();
            return Some(Counterexample::new(assignments));
        }
        return None;
    }

    let (name, sort) = &vars[index];
    for candidate in candidate_values(sort) {
        assignments.insert(name.clone(), candidate);
        if let Some(counterexample) = search_counterexample(vars, index + 1, formula, assignments) {
            return Some(counterexample);
        }
    }
    assignments.remove(name);
    None
}

fn candidate_values(sort: &Sort) -> Vec<EvalValue> {
    match sort {
        Sort::Bool => vec![EvalValue::Bool(false), EvalValue::Bool(true)],
        Sort::Int => {
            vec![EvalValue::Int(-1), EvalValue::Int(0), EvalValue::Int(1), EvalValue::Int(2)]
        }
        Sort::BitVec(_) => vec![EvalValue::UInt(0), EvalValue::UInt(1), EvalValue::UInt(2)],
        Sort::Array(_, _) => Vec::new(),
        _ => Vec::new(),
    }
}

fn counterexample_value(value: &EvalValue) -> CounterexampleValue {
    match value {
        EvalValue::Bool(value) => CounterexampleValue::Bool(*value),
        EvalValue::Int(value) => CounterexampleValue::Int(*value),
        EvalValue::UInt(value) => CounterexampleValue::Uint(*value),
    }
}

fn eval_formula(formula: &Formula, assignments: &BTreeMap<String, EvalValue>) -> Option<EvalValue> {
    match formula {
        Formula::Bool(value) => Some(EvalValue::Bool(*value)),
        Formula::Int(value) => Some(EvalValue::Int(*value)),
        Formula::UInt(value) => Some(EvalValue::UInt(*value)),
        Formula::BitVec { value, .. } => Some(EvalValue::Int(*value)),
        Formula::Var(name, _) => assignments.get(name).cloned(),
        Formula::Not(inner) => match eval_formula(inner, assignments)? {
            EvalValue::Bool(value) => Some(EvalValue::Bool(!value)),
            _ => None,
        },
        Formula::And(terms) => {
            let mut value = true;
            for term in terms {
                match eval_formula(term, assignments)? {
                    EvalValue::Bool(term_value) => value &= term_value,
                    _ => return None,
                }
            }
            Some(EvalValue::Bool(value))
        }
        Formula::Or(terms) => {
            let mut value = false;
            for term in terms {
                match eval_formula(term, assignments)? {
                    EvalValue::Bool(term_value) => value |= term_value,
                    _ => return None,
                }
            }
            Some(EvalValue::Bool(value))
        }
        Formula::Implies(lhs, rhs) => {
            match (eval_formula(lhs, assignments)?, eval_formula(rhs, assignments)?) {
                (EvalValue::Bool(lhs), EvalValue::Bool(rhs)) => Some(EvalValue::Bool(!lhs || rhs)),
                _ => None,
            }
        }
        Formula::Eq(lhs, rhs) => {
            let lhs = eval_formula(lhs, assignments)?;
            let rhs = eval_formula(rhs, assignments)?;
            Some(EvalValue::Bool(lhs == rhs))
        }
        Formula::Lt(lhs, rhs) => compare_numeric(lhs, rhs, assignments, |lhs, rhs| lhs < rhs),
        Formula::Le(lhs, rhs) => compare_numeric(lhs, rhs, assignments, |lhs, rhs| lhs <= rhs),
        Formula::Gt(lhs, rhs) => compare_numeric(lhs, rhs, assignments, |lhs, rhs| lhs > rhs),
        Formula::Ge(lhs, rhs) => compare_numeric(lhs, rhs, assignments, |lhs, rhs| lhs >= rhs),
        Formula::Add(lhs, rhs) => {
            arithmetic_numeric(lhs, rhs, assignments, |lhs, rhs| Some(lhs + rhs))
        }
        Formula::Sub(lhs, rhs) => {
            arithmetic_numeric(lhs, rhs, assignments, |lhs, rhs| Some(lhs - rhs))
        }
        Formula::Mul(lhs, rhs) => {
            arithmetic_numeric(lhs, rhs, assignments, |lhs, rhs| Some(lhs * rhs))
        }
        Formula::Div(lhs, rhs) => {
            arithmetic_numeric(lhs, rhs, assignments, |lhs, rhs| (rhs != 0).then_some(lhs / rhs))
        }
        Formula::Rem(lhs, rhs) => {
            arithmetic_numeric(lhs, rhs, assignments, |lhs, rhs| (rhs != 0).then_some(lhs % rhs))
        }
        Formula::Neg(inner) => match eval_formula(inner, assignments)? {
            EvalValue::Int(value) => Some(EvalValue::Int(-value)),
            _ => None,
        },
        _ => None,
    }
}

fn compare_numeric(
    lhs: &Formula,
    rhs: &Formula,
    assignments: &BTreeMap<String, EvalValue>,
    cmp: impl Fn(i128, i128) -> bool,
) -> Option<EvalValue> {
    let lhs = numeric_value(&eval_formula(lhs, assignments)?)?;
    let rhs = numeric_value(&eval_formula(rhs, assignments)?)?;
    Some(EvalValue::Bool(cmp(lhs, rhs)))
}

fn arithmetic_numeric(
    lhs: &Formula,
    rhs: &Formula,
    assignments: &BTreeMap<String, EvalValue>,
    op: impl Fn(i128, i128) -> Option<i128>,
) -> Option<EvalValue> {
    let lhs = numeric_value(&eval_formula(lhs, assignments)?)?;
    let rhs = numeric_value(&eval_formula(rhs, assignments)?)?;
    Some(EvalValue::Int(op(lhs, rhs)?))
}

fn numeric_value(value: &EvalValue) -> Option<i128> {
    match value {
        EvalValue::Int(value) => Some(*value),
        EvalValue::UInt(value) => i128::try_from(*value).ok(),
        EvalValue::Bool(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::SourceSpan;

    /// A router pinned to the deterministic `ConstantFolderBackend` only, so these
    /// validator tests stay independent of workspace feature unification (which
    /// otherwise registers the real in-process ay backend via `Router::new()`).
    fn mock_router() -> Router {
        Router::with_backends(vec![Box::new(trust_router::constant_folder::ConstantFolderBackend)])
    }

    fn simple_binop(name: &str, op: BinOp) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: trust_types::VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::i32(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: trust_types::Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                op,
                                Operand::Copy(trust_types::Place::local(1)),
                                Operand::Copy(trust_types::Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: trust_types::Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(trust_types::Place::local(3))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: trust_types::Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_validate_equivalent_functions() {
        let validator = TranslationValidator::with_router(mock_router());
        let source = simple_binop("source", BinOp::Add);
        let target = simple_binop("target", BinOp::Add);

        let result = validator.validate_refinement(&source, &target).unwrap();
        match result {
            SmtValidationResult::Equivalent { proof_certificates, .. } => {
                assert!(proof_certificates.is_empty())
            }
            other => panic!("expected Equivalent, got {other:?}"),
        }
    }

    #[test]
    fn test_validate_divergent_functions() {
        let validator = TranslationValidator::with_router(mock_router());
        let source = simple_binop("source", BinOp::Add);
        let target = simple_binop("target", BinOp::Sub);

        let result = validator.validate_refinement(&source, &target).unwrap();
        match result {
            SmtValidationResult::Divergent { counterexamples, .. } => {
                assert!(!counterexamples.is_empty());
                let assignments = &counterexamples[0].assignments;
                assert!(assignments.iter().any(|(name, _)| name == "a"));
                assert!(assignments.iter().any(|(name, _)| name == "b"));
            }
            other => panic!("expected Divergent, got {other:?}"),
        }
    }

    #[test]
    fn test_unsupported_mismatched_binops_are_inconclusive() {
        let validator = TranslationValidator::new();
        let source = simple_binop("source", BinOp::BitAnd);
        let target = simple_binop("target", BinOp::BitOr);

        let result = validator.validate_refinement(&source, &target).unwrap();
        match result {
            SmtValidationResult::Inconclusive { partial_results, .. } => {
                assert!(
                    partial_results.iter().any(|outcome| matches!(
                        outcome.result,
                        VerificationResult::Unknown { .. }
                    )),
                    "expected an unknown validation outcome for unsupported binops"
                );
            }
            other => panic!("expected Inconclusive for unsupported binops, got {other:?}"),
        }
    }

    #[test]
    fn test_validate_block_pair() {
        let validator = TranslationValidator::with_router(mock_router());
        let source = simple_binop("source", BinOp::Add);
        let target = simple_binop("target", BinOp::Add);

        let result =
            validator.validate_block_pair(&source, &target, BlockId(0), BlockId(0)).unwrap();
        assert!(matches!(result, SmtValidationResult::Equivalent { .. }));
    }

    #[test]
    fn test_check_property_trivial() {
        let validator = TranslationValidator::new();
        let func = simple_binop("simple_add", BinOp::Add);

        let result = validator.check_property(&func, &Formula::Bool(true)).unwrap();
        assert!(matches!(result, SmtPropertyResult::Inconclusive { .. }));
    }

    #[test]
    fn test_validator_with_custom_router() {
        let validator = TranslationValidator::with_router(mock_router());
        let func = simple_binop("simple_add", BinOp::Add);

        let result = validator.check_property(&func, &Formula::Bool(true)).unwrap();
        assert!(matches!(result, SmtPropertyResult::Holds { .. }));
    }

    /// Single-block function returning either `_1 as u8` (cast) or `_1` (plain).
    /// The straight-line evaluator models `Cast` as identity over the unbounded
    /// `Sort::Int`, so the two produce the same return formula even though they
    /// differ at machine-word width.
    fn cast_or_plain(name: &str, truncating_cast: bool) -> VerifiableFunction {
        let rvalue = if truncating_cast {
            Rvalue::Cast(Operand::Copy(trust_types::Place::local(1)), Ty::u8())
        } else {
            Rvalue::Use(Operand::Copy(trust_types::Place::local(1)))
        };
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: trust_types::VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: if truncating_cast { Ty::u8() } else { Ty::i32() },
                        name: None,
                    },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: trust_types::Place::local(0),
                        rvalue,
                        span: SourceSpan::default(),
                    }],
                    terminator: trust_types::Terminator::Return,
                }],
                arg_count: 1,
                return_ty: if truncating_cast { Ty::u8() } else { Ty::i32() },
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Regression (M-C3-prereq): the straight-line shortcut is a divergence
    /// detector only and must never positively validate. On syntactic equality
    /// of the simplified return expressions it defers (returns `None`) rather
    /// than discharging the obligation to `Bool(false)` — otherwise a truncating
    /// cast modeled as identity would be falsely stamped equivalent.
    #[test]
    fn straight_line_shortcut_never_self_validates() {
        // Identical functions compare equal and still defer to the real VC.
        let source = simple_binop("source", BinOp::Add);
        let target = simple_binop("target", BinOp::Add);
        assert!(
            straight_line_function_outcome(&source, &target).is_none(),
            "equal return expressions must defer to the solver, not self-validate"
        );

        // Truncating cast vs plain compare equal under the (unsound) identity
        // model of `Cast`, and must likewise defer — never auto-validate.
        let cast = cast_or_plain("cast", true);
        let plain = cast_or_plain("plain", false);
        assert!(
            straight_line_function_outcome(&cast, &plain).is_none(),
            "truncating-cast vs plain must not be self-validated by the shortcut"
        );
    }

    /// End-to-end lock: even with a router attached, a truncating-cast/plain
    /// pair must never surface as `Ok(Equivalent)`. It is sound for this to
    /// fail closed two ways — the refinement checker rejects the unmodeled cast
    /// (`Err(InvalidRelation)`), or, were VCs produced, the straight-line
    /// shortcut now defers to the solver (`Divergent`/`Inconclusive`). The one
    /// outcome forbidden is a false positive.
    #[test]
    fn truncating_cast_is_not_falsely_equivalent() {
        let validator = TranslationValidator::with_router(mock_router());
        let source = cast_or_plain("source", true);
        let target = cast_or_plain("target", false);

        let result = validator.validate_refinement(&source, &target);
        assert!(
            !matches!(result, Ok(SmtValidationResult::Equivalent { .. })),
            "truncating-cast vs plain must not be Ok(Equivalent), got {result:?}"
        );
    }
}
