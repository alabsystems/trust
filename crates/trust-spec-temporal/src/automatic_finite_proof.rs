//! Automatic exact Clean proofs for the function-valued finite-model lane.
//!
//! This first authority family covers finite models whose independently
//! replayed TY fixpoint keeps every Boolean-function pack at zero.  That is not
//! a vacuous scalar fallback: updates may use whole-function values, access,
//! `EXCEPT`, and bounded comprehensions, and invariants may use bounded forall.
//! The generated Clean inhabitant reconstructs every expression derivation and
//! proves initiation, action closure, and preservation for the exact applied
//! function model.  Unsupported or non-zero function rows decline closed.

use crate::clean_model_lane::{
    CleanAppliedModelProof, CleanFiniteModel, CleanFiniteModelCertificate, CleanFunctionVar,
    CleanScalarAction, CleanScalarExpr, CleanScalarModelError, CleanScalarUpdate,
    certify_clean_finite_model_with_ty, prove_clean_finite_model_safety_claim,
    recheck_clean_finite_model_safety_claim_proof, recheck_clean_finite_model_with_ty,
};

pub const CLEAN_AUTOMATIC_FINITE_PROOF_SCHEMA_V1: &str = "trust.clean-automatic-finite-proof/v1";

const GENERATED_NAMESPACE: &str = "TrustGeneratedR5AutomaticFinite";
const GENERATED_ROWS: &str = "TrustGeneratedR5AutomaticFinite.ReachableRows";
const GENERATED_CLAIM: &str = "TrustGeneratedR5AutomaticFinite.AppliedClaim";
const GENERATED_PROOF: &str = "TrustGeneratedR5AutomaticFinite.AppliedProof";
const ZERO_FUNCTION: &str = "TrustGeneratedR5AutomaticFinite.ZeroFunction";

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CleanAutomaticFiniteProof {
    pub schema: String,
    pub finite: CleanFiniteModelCertificate,
    pub rows: Vec<Vec<u64>>,
    pub generated_suffix: String,
    pub applied_proof: CleanAppliedModelProof,
}

#[derive(Clone, Debug)]
struct Local<'a> {
    name: &'a str,
    term: String,
    lower: String,
    upper: String,
    low_value: u64,
    high_value: u64,
}

#[derive(Clone, Debug)]
enum ExactValue {
    Nat { term: String, concrete: Option<u64> },
    Bool(bool),
    Function { range: String },
}

#[derive(Clone, Debug)]
struct ExactExpr {
    expression: String,
    value: ExactValue,
    proof: String,
}

fn quoted(value: &str) -> String {
    serde_json::to_string(value).expect("String serialization cannot fail")
}

fn lean_list(items: &[String]) -> String {
    format!("[{}]", items.join(", "))
}

fn every_term(handlers: &[String]) -> String {
    handlers.iter().rev().fold("True.intro".to_owned(), |tail, head| format!("⟨{head}, {tail}⟩"))
}

fn member_at(index: usize) -> String {
    let mut proof = "Member.head _".to_owned();
    for _ in 0..index {
        proof = format!("Member.tail _ _ ({proof})");
    }
    proof
}

fn function_coordinate_at(row_proof: &str, index: usize) -> String {
    let mut coordinate = format!("({row_proof}).2.2");
    for _ in 0..index {
        coordinate.push_str(".2");
    }
    coordinate.push_str(".1");
    coordinate
}

fn render_function_var(entry: &CleanFunctionVar) -> String {
    format!("FunctionVar.mk {} {}", quoted(&entry.name), quoted(&entry.range_constant))
}

fn render_expr(expression: &CleanScalarExpr) -> String {
    match expression {
        CleanScalarExpr::Int(value) => format!("ScalarExpr.int {value}"),
        CleanScalarExpr::Var(name) => format!("ScalarExpr.var {}", quoted(name)),
        CleanScalarExpr::ConstRef(name) => {
            format!("ScalarExpr.constRef {}", quoted(name))
        }
        CleanScalarExpr::Bool(value) => format!("ScalarExpr.bool {value}"),
        CleanScalarExpr::Add(a, b) => {
            format!("ScalarExpr.add ({}) ({})", render_expr(a), render_expr(b))
        }
        CleanScalarExpr::Sub(a, b) => {
            format!("ScalarExpr.sub ({}) ({})", render_expr(a), render_expr(b))
        }
        CleanScalarExpr::Gt(a, b) => {
            format!("ScalarExpr.gt ({}) ({})", render_expr(a), render_expr(b))
        }
        CleanScalarExpr::Le(a, b) => {
            format!("ScalarExpr.le ({}) ({})", render_expr(a), render_expr(b))
        }
        CleanScalarExpr::Eq(a, b) => {
            format!("ScalarExpr.eq ({}) ({})", render_expr(a), render_expr(b))
        }
        CleanScalarExpr::Neq(a, b) => {
            format!("ScalarExpr.neq ({}) ({})", render_expr(a), render_expr(b))
        }
        CleanScalarExpr::Or(a, b) => {
            format!("ScalarExpr.or ({}) ({})", render_expr(a), render_expr(b))
        }
        CleanScalarExpr::And(a, b) => {
            format!("ScalarExpr.and ({}) ({})", render_expr(a), render_expr(b))
        }
        CleanScalarExpr::Iff(a, b) => {
            format!("ScalarExpr.iff ({}) ({})", render_expr(a), render_expr(b))
        }
        CleanScalarExpr::If(c, a, b) => {
            format!("ScalarExpr.ite ({}) ({}) ({})", render_expr(c), render_expr(a), render_expr(b))
        }
        CleanScalarExpr::Forall(index, low, high, body) => format!(
            "ScalarExpr.forallIn {} ({}) ({}) ({})",
            quoted(index),
            render_expr(low),
            render_expr(high),
            render_expr(body)
        ),
        CleanScalarExpr::FnAccess(name, index) => {
            format!("ScalarExpr.fnAccess {} ({})", quoted(name), render_expr(index))
        }
        CleanScalarExpr::Except(name, index, value) => format!(
            "ScalarExpr.except {} ({}) ({})",
            quoted(name),
            render_expr(index),
            render_expr(value)
        ),
        CleanScalarExpr::Comprehension(index, low, high, body) => format!(
            "ScalarExpr.comprehension {} ({}) ({}) ({})",
            quoted(index),
            render_expr(low),
            render_expr(high),
            render_expr(body)
        ),
    }
}

fn render_update(update: &CleanScalarUpdate) -> String {
    format!("Update.mk {} ({})", quoted(&update.var), render_expr(&update.value))
}

fn render_action(action: &CleanScalarAction) -> String {
    let guard = action.guard.as_ref().map_or_else(
        || "Guard.always".to_owned(),
        |guard| format!("Guard.when ({})", render_expr(guard)),
    );
    format!(
        "Action.mk {} ({guard}) {}",
        quoted(&action.name),
        lean_list(&action.updates.iter().map(render_update).collect::<Vec<_>>())
    )
}

fn constant_index(model: &CleanFiniteModel, name: &str) -> Result<usize, CleanScalarModelError> {
    model.scalar.constants.iter().position(|entry| entry.name == name).ok_or_else(|| {
        CleanScalarModelError::Definition(format!(
            "automatic finite proof found undeclared constant `{name}`"
        ))
    })
}

fn constant_found(
    model: &CleanFiniteModel,
    name: &str,
) -> Result<(u64, String), CleanScalarModelError> {
    let index = constant_index(model, name)?;
    let entry = &model.scalar.constants[index];
    let value = u64::try_from(entry.value).map_err(|_| {
        CleanScalarModelError::Definition(format!(
            "constant `{name}` is outside the nonnegative Clean finite carrier"
        ))
    })?;
    Ok((value, format!("⟨Constant.mk {} {value}, {}, rfl, rfl⟩", quoted(name), member_at(index))))
}

fn unique_constant(model: &CleanFiniteModel, model_name: &str, name: &str, value: u64) -> String {
    let handlers = model
        .scalar
        .constants
        .iter()
        .map(|candidate| {
            if candidate.name == name {
                "fun _ => rfl".to_owned()
            } else {
                format!(
                    "fun same => False.elim ((show ¬ ({} = {}) from by decide) same)",
                    quoted(&candidate.name),
                    quoted(name)
                )
            }
        })
        .collect::<Vec<_>>();
    format!(
        "uniqueConstantValueOfEvery {model_name} {} {value} ({})",
        quoted(name),
        every_term(&handlers)
    )
}

fn function_index(model: &CleanFiniteModel, name: &str) -> Result<usize, CleanScalarModelError> {
    model.function_variables.iter().position(|entry| entry.name == name).ok_or_else(|| {
        CleanScalarModelError::Definition(format!(
            "automatic finite proof found undeclared function `{name}`"
        ))
    })
}

fn function_facts(
    model: &CleanFiniteModel,
    model_name: &str,
    name: &str,
) -> Result<(usize, String, String, String), CleanScalarModelError> {
    let index = function_index(model, name)?;
    let entry = &model.function_variables[index];
    let found = format!("⟨{}, {}, rfl, rfl⟩", render_function_var(entry), member_at(index));
    let handlers = model
        .function_variables
        .iter()
        .map(|candidate| {
            if candidate.name == name {
                "fun _ => rfl".to_owned()
            } else {
                format!(
                    "fun same => False.elim ((show ¬ ({} = {}) from by decide) same)",
                    quoted(&candidate.name),
                    quoted(name)
                )
            }
        })
        .collect::<Vec<_>>();
    let unique = format!(
        "uniqueFunctionRangeOfEvery {model_name} {} {} ({})",
        quoted(name),
        quoted(&entry.range_constant),
        every_term(&handlers)
    );
    Ok((index, entry.range_constant.clone(), found, unique))
}

fn all_names_differ<'a>(names: impl Iterator<Item = &'a str>, target: &str) -> String {
    every_term(
        &names
            .map(|name| format!("show ¬ ({} = {}) from by decide", quoted(name), quoted(target)))
            .collect::<Vec<_>>(),
    )
}

fn locals_term(locals: &[Local<'_>]) -> String {
    lean_list(
        &locals
            .iter()
            .map(|local| format!("({}, {})", quoted(local.name), local.term))
            .collect::<Vec<_>>(),
    )
}

fn exact_expression(
    model: &CleanFiniteModel,
    model_name: &str,
    state: &str,
    row_proof: &str,
    locals: &[Local<'_>],
    expression: &CleanScalarExpr,
) -> Result<ExactExpr, CleanScalarModelError> {
    let local_term = locals_term(locals);
    match expression {
        CleanScalarExpr::Int(value) => {
            let value = u64::try_from(*value).map_err(|_| {
                CleanScalarModelError::Definition(
                    "automatic finite proof accepts only nonnegative integers".to_owned(),
                )
            })?;
            Ok(ExactExpr {
                expression: format!("ScalarExpr.int {value}"),
                value: ExactValue::Nat { term: value.to_string(), concrete: Some(value) },
                proof: format!("exactFunctionInt {model_name} {local_term} {state} {value}"),
            })
        }
        CleanScalarExpr::Bool(value) => Ok(ExactExpr {
            expression: format!("ScalarExpr.bool {value}"),
            value: ExactValue::Bool(*value),
            proof: format!("exactFunctionBool {model_name} {local_term} {state} {value}"),
        }),
        CleanScalarExpr::ConstRef(name) => {
            let (value, found) = constant_found(model, name)?;
            let unique = unique_constant(model, model_name, name, value);
            Ok(ExactExpr {
                expression: format!("ScalarExpr.constRef {}", quoted(name)),
                value: ExactValue::Nat { term: value.to_string(), concrete: Some(value) },
                proof: format!(
                    "exactFunctionConst {model_name} {local_term} {state} {} {value} ({found}) ({unique})",
                    quoted(name)
                ),
            })
        }
        CleanScalarExpr::Var(name) => {
            if let Some((local_index, local)) =
                locals.iter().enumerate().find(|(_, local)| local.name == name)
            {
                if locals.iter().filter(|local| local.name == name).count() != 1 {
                    return Err(CleanScalarModelError::Definition(format!(
                        "automatic finite proof declines shadowed local `{name}`"
                    )));
                }
                let handlers = locals
                    .iter()
                    .map(|candidate| {
                        if candidate.name == name {
                            "fun _ => rfl".to_owned()
                        } else {
                            format!(
                                "fun same => False.elim ((show ¬ ({} = {}) from by decide) same)",
                                quoted(candidate.name),
                                quoted(name)
                            )
                        }
                    })
                    .collect::<Vec<_>>();
                let found = format!(
                    "⟨({}, {}), {}, rfl, rfl⟩",
                    quoted(name),
                    local.term,
                    member_at(local_index)
                );
                let unique = format!(
                    "uniqueLocalValueOfEvery {local_term} {} ({}) ({})",
                    quoted(name),
                    local.term,
                    every_term(&handlers)
                );
                let no_scalar = format!(
                    "noDeclaredScalarOfEvery {model_name} {} ({})",
                    quoted(name),
                    all_names_differ(
                        model.scalar.variables.iter().map(|entry| entry.name.as_str()),
                        name
                    )
                );
                let no_function = format!(
                    "noFunctionRangeOfEvery {model_name} {} ({})",
                    quoted(name),
                    all_names_differ(
                        model.function_variables.iter().map(|entry| entry.name.as_str()),
                        name
                    )
                );
                return Ok(ExactExpr {
                    expression: format!("ScalarExpr.var {}", quoted(name)),
                    value: ExactValue::Nat { term: local.term.clone(), concrete: None },
                    proof: format!(
                        "exactFunctionLocalVar {model_name} {local_term} {state} {} ({}) ({found}) ({unique}) ({no_scalar}) (fun range found => {no_function} range found)",
                        quoted(name),
                        local.term
                    ),
                });
            }
            if model.scalar.variables.iter().any(|entry| entry.name == *name) {
                return Err(CleanScalarModelError::Definition(
                    "the current automatic function family declines scalar state coordinates"
                        .to_owned(),
                ));
            }
            let (index, range, found, unique) = function_facts(model, model_name, name)?;
            let coordinate = function_coordinate_at(row_proof, index);
            let no_scalar = format!(
                "noDeclaredScalarOfEvery {model_name} {} ({})",
                quoted(name),
                all_names_differ(
                    model.scalar.variables.iter().map(|entry| entry.name.as_str()),
                    name
                )
            );
            let no_local = format!(
                "fun value found => noLocalValueOfEvery {local_term} {} ({}) value found",
                quoted(name),
                all_names_differ(locals.iter().map(|entry| entry.name), name)
            );
            Ok(ExactExpr {
                expression: format!("ScalarExpr.var {}", quoted(name)),
                value: ExactValue::Function { range: range.clone() },
                proof: format!(
                    "exactFunctionVarValue {model_name} {local_term} {state} {} {} {ZERO_FUNCTION} ({found}) ({unique}) ({no_scalar}) ({no_local}) ({coordinate})",
                    quoted(name),
                    quoted(&range)
                ),
            })
        }
        CleanScalarExpr::Eq(left, right) => {
            let left = exact_expression(model, model_name, state, row_proof, locals, left)?;
            let right = exact_expression(model, model_name, state, row_proof, locals, right)?;
            let (
                ExactValue::Nat { term: left_term, concrete: left_value },
                ExactValue::Nat { term: right_term, concrete: right_value },
            ) = (&left.value, &right.value)
            else {
                return Err(CleanScalarModelError::Definition(
                    "automatic finite equality currently requires Nat operands".to_owned(),
                ));
            };
            if left_value.is_none() || left_value != right_value {
                return Err(CleanScalarModelError::Definition(
                    "automatic finite equality currently requires an exact true closed equality"
                        .to_owned(),
                ));
            }
            let expression = format!("ScalarExpr.eq ({}) ({})", left.expression, right.expression);
            Ok(ExactExpr {
                expression,
                value: ExactValue::Bool(true),
                proof: format!(
                    "exactFunctionEqTrue {model_name} {local_term} {state} ({}) ({}) ({left_term}) ({right_term}) ({}) ({}) rfl",
                    left.expression, right.expression, left.proof, right.proof
                ),
            })
        }
        CleanScalarExpr::And(left, right) => {
            let left = exact_expression(model, model_name, state, row_proof, locals, left)?;
            let right = exact_expression(model, model_name, state, row_proof, locals, right)?;
            if !matches!(left.value, ExactValue::Bool(true))
                || !matches!(right.value, ExactValue::Bool(true))
            {
                return Err(CleanScalarModelError::Definition(
                    "automatic finite conjunction did not evaluate true".to_owned(),
                ));
            }
            Ok(ExactExpr {
                expression: format!("ScalarExpr.and ({}) ({})", left.expression, right.expression),
                value: ExactValue::Bool(true),
                proof: format!(
                    "exactFunctionAndTrue {model_name} {local_term} {state} ({}) ({}) ({}) ({})",
                    left.expression, right.expression, left.proof, right.proof
                ),
            })
        }
        CleanScalarExpr::Iff(left, right) => {
            let left = exact_expression(model, model_name, state, row_proof, locals, left)?;
            let right = exact_expression(model, model_name, state, row_proof, locals, right)?;
            if !matches!(left.value, ExactValue::Bool(false))
                || !matches!(right.value, ExactValue::Bool(false))
            {
                return Err(CleanScalarModelError::Definition(
                    "automatic finite iff currently requires two exact false operands".to_owned(),
                ));
            }
            Ok(ExactExpr {
                expression: format!("ScalarExpr.iff ({}) ({})", left.expression, right.expression),
                value: ExactValue::Bool(true),
                proof: format!(
                    "exactFunctionIffFalseFalse {model_name} {local_term} {state} ({}) ({}) ({}) ({})",
                    left.expression, right.expression, left.proof, right.proof
                ),
            })
        }
        CleanScalarExpr::FnAccess(name, index_expression) => {
            let index_exact =
                exact_expression(model, model_name, state, row_proof, locals, index_expression)?;
            let ExactValue::Nat { term: index_term, concrete } = &index_exact.value else {
                return Err(CleanScalarModelError::Definition(
                    "function access index is not Nat".to_owned(),
                ));
            };
            let (function_index, range, found, _) = function_facts(model, model_name, name)?;
            let (high, range_found) = constant_found(model, &range)?;
            let domain = if let Some(value) = concrete {
                if !(1..=high).contains(value) {
                    return Err(CleanScalarModelError::Definition(
                        "function access index is outside its exact range".to_owned(),
                    ));
                }
                format!("⟨{high}, {range_found}, by decide, by decide⟩")
            } else {
                let local =
                    locals.iter().find(|local| local.term == *index_term).ok_or_else(|| {
                        CleanScalarModelError::Definition(
                            "symbolic function access lacks a bounded local proof".to_owned(),
                        )
                    })?;
                if local.low_value != 1 || local.high_value != high {
                    return Err(CleanScalarModelError::Definition(
                        "symbolic function access bounds differ from the declared range".to_owned(),
                    ));
                }
                format!("⟨{high}, {range_found}, {}, {}⟩", local.lower, local.upper)
            };
            let coordinate = format!(
                "congrArg (fun contents : Nat → Bool => contents ({index_term})) ({})",
                function_coordinate_at(row_proof, function_index)
            );
            Ok(ExactExpr {
                expression: format!(
                    "ScalarExpr.fnAccess {} ({})",
                    quoted(name),
                    index_exact.expression
                ),
                value: ExactValue::Bool(false),
                proof: format!(
                    "exactFunctionAccessValue {model_name} {local_term} {state} {} {} ({}) ({index_term}) false ({found}) ({}) ({domain}) ({coordinate})",
                    quoted(name),
                    quoted(&range),
                    index_exact.expression,
                    index_exact.proof
                ),
            })
        }
        CleanScalarExpr::Forall(index, low, high, body) => {
            let low_exact = exact_expression(model, model_name, state, row_proof, locals, low)?;
            let high_exact = exact_expression(model, model_name, state, row_proof, locals, high)?;
            let (
                ExactValue::Nat { concrete: Some(low_value), .. },
                ExactValue::Nat { concrete: Some(high_value), .. },
            ) = (&low_exact.value, &high_exact.value)
            else {
                return Err(CleanScalarModelError::Definition(
                    "bounded forall requires closed Nat bounds".to_owned(),
                ));
            };
            let local = Local {
                name: index,
                term: "candidate".to_owned(),
                lower: "lower".to_owned(),
                upper: "upper".to_owned(),
                low_value: *low_value,
                high_value: *high_value,
            };
            let mut body_locals = vec![local];
            body_locals.extend_from_slice(locals);
            let body_exact =
                exact_expression(model, model_name, state, row_proof, &body_locals, body)?;
            if !matches!(body_exact.value, ExactValue::Bool(true)) {
                return Err(CleanScalarModelError::Definition(
                    "bounded forall body is not exactly true on the zero-function row".to_owned(),
                ));
            }
            Ok(ExactExpr {
                expression: format!(
                    "ScalarExpr.forallIn {} ({}) ({}) ({})",
                    quoted(index),
                    low_exact.expression,
                    high_exact.expression,
                    body_exact.expression
                ),
                value: ExactValue::Bool(true),
                proof: format!(
                    "exactFunctionForallTrue {model_name} {local_term} {state} {} ({}) ({}) ({}) {low_value} {high_value} ({}) ({}) (fun candidate lower upper => {})",
                    quoted(index),
                    low_exact.expression,
                    high_exact.expression,
                    body_exact.expression,
                    low_exact.proof,
                    high_exact.proof,
                    body_exact.proof
                ),
            })
        }
        CleanScalarExpr::Except(name, index_expression, new_value) => {
            let index_exact =
                exact_expression(model, model_name, state, row_proof, locals, index_expression)?;
            let value_exact =
                exact_expression(model, model_name, state, row_proof, locals, new_value)?;
            let ExactValue::Nat { term: index_term, concrete } = &index_exact.value else {
                return Err(CleanScalarModelError::Definition(
                    "EXCEPT index is not Nat".to_owned(),
                ));
            };
            if !matches!(value_exact.value, ExactValue::Bool(false)) {
                return Err(CleanScalarModelError::Definition(
                    "zero-function family accepts only false EXCEPT updates".to_owned(),
                ));
            }
            let (function_index, range, found, unique_range) =
                function_facts(model, model_name, name)?;
            let (high, range_found) = constant_found(model, &range)?;
            let unique_constant = unique_constant(model, model_name, &range, high);
            let domain = if let Some(value) = concrete {
                if !(1..=high).contains(value) {
                    return Err(CleanScalarModelError::Definition(
                        "EXCEPT index is outside its exact range".to_owned(),
                    ));
                }
                format!("⟨{high}, {range_found}, by decide, by decide⟩")
            } else {
                return Err(CleanScalarModelError::Definition(
                    "zero-function EXCEPT currently requires a closed index".to_owned(),
                ));
            };
            let coordinate = function_coordinate_at(row_proof, function_index);
            let others = format!(
                "fun other _ _ => Eq.symm (congrArg (fun contents : Nat → Bool => contents other) ({coordinate}))"
            );
            let classify = format!(
                "fun candidate => functionDomainClassify {model_name} {} {high} ({index_term}) candidate ({range_found}) ({unique_constant})",
                quoted(&range)
            );
            Ok(ExactExpr {
                expression: format!(
                    "ScalarExpr.except {} ({}) ({})",
                    quoted(name),
                    index_exact.expression,
                    value_exact.expression
                ),
                value: ExactValue::Function { range: range.clone() },
                proof: format!(
                    "exactFunctionExcept {model_name} {local_term} {state} {} {} ({}) ({}) ({index_term}) false {ZERO_FUNCTION} ({found}) ({unique_range}) ({}) ({domain}) ({}) rfl ({others}) (fun _ _ => rfl) ({classify})",
                    quoted(name),
                    quoted(&range),
                    index_exact.expression,
                    value_exact.expression,
                    index_exact.proof,
                    value_exact.proof
                ),
            })
        }
        CleanScalarExpr::Comprehension(index, low, high, body) => {
            let (CleanScalarExpr::Int(1), CleanScalarExpr::ConstRef(range)) =
                (low.as_ref(), high.as_ref())
            else {
                return Err(CleanScalarModelError::Definition(
                    "function comprehension must use the exact 1..Range ABI shape".to_owned(),
                ));
            };
            let low_exact = exact_expression(model, model_name, state, row_proof, locals, low)?;
            let high_exact = exact_expression(model, model_name, state, row_proof, locals, high)?;
            let (high_value, found) = constant_found(model, range)?;
            let local = Local {
                name: index,
                term: "candidate".to_owned(),
                lower: "lower".to_owned(),
                upper: "upper".to_owned(),
                low_value: 1,
                high_value,
            };
            let mut body_locals = vec![local];
            body_locals.extend_from_slice(locals);
            let body_exact =
                exact_expression(model, model_name, state, row_proof, &body_locals, body)?;
            if !matches!(body_exact.value, ExactValue::Bool(false)) {
                return Err(CleanScalarModelError::Definition(
                    "zero-function comprehension body is not exactly false".to_owned(),
                ));
            }
            Ok(ExactExpr {
                expression: format!(
                    "ScalarExpr.comprehension {} ({}) ({}) ({})",
                    quoted(index),
                    low_exact.expression,
                    high_exact.expression,
                    body_exact.expression
                ),
                value: ExactValue::Function { range: range.clone() },
                proof: format!(
                    "exactFunctionComprehension {model_name} {local_term} {state} {} {} ({}) ({}) ({}) 1 {high_value} {ZERO_FUNCTION} rfl rfl rfl ({found}) ({}) ({}) (fun candidate lower upper => {}) (fun _ _ => rfl) (fun candidate => natIntervalClassify 1 {high_value} candidate)",
                    quoted(index),
                    quoted(range),
                    low_exact.expression,
                    high_exact.expression,
                    body_exact.expression,
                    low_exact.proof,
                    high_exact.proof,
                    body_exact.proof
                ),
            })
        }
        unsupported => Err(CleanScalarModelError::Definition(format!(
            "expression `{}` is outside the exact zero-function automatic family",
            render_expr(unsupported)
        ))),
    }
}

fn generated_row(model: &CleanFiniteModel) -> String {
    format!(
        "FiniteRow.mk [] {}",
        lean_list(&vec![ZERO_FUNCTION.to_owned(); model.function_variables.len()])
    )
}

fn action_handler(
    model: &CleanFiniteModel,
    model_name: &str,
    action: &CleanScalarAction,
) -> Result<String, CleanScalarModelError> {
    let row_proof = "rowProof";
    if let Some(guard) = &action.guard {
        let exact = exact_expression(model, model_name, "before", row_proof, &[], guard)?;
        if !matches!(exact.value, ExactValue::Bool(true)) {
            return Err(CleanScalarModelError::Definition(format!(
                "action `{}` is disabled on the only TY reachable function row",
                action.name
            )));
        }
    }
    let action_term = render_action(action);
    let mut coordinates = Vec::new();
    for (function_index, function) in model.function_variables.iter().enumerate() {
        let entry = render_function_var(function);
        if let Some(update_index) = action.updates.iter().position(|u| u.var == function.name) {
            let update = &action.updates[update_index];
            let exact =
                exact_expression(model, model_name, "before", row_proof, &[], &update.value)?;
            if !matches!(
                &exact.value,
                ExactValue::Function { range } if range == &function.range_constant
            ) {
                return Err(CleanScalarModelError::Definition(format!(
                    "function update `{}` does not reconstruct the declared zero function",
                    function.name
                )));
            }
            let handlers = action
                .updates
                .iter()
                .map(|candidate| {
                    if candidate.var == function.name {
                        Ok(format!(
                            "fun _ evaluation => congrArg valueFunctionProjection (({}).unique (Value.function {} (after.function {})) evaluation)",
                            exact.proof,
                            quoted(&function.range_constant),
                            quoted(&function.name)
                        ))
                    } else {
                        Ok(format!(
                            "fun same _ => False.elim ((show ¬ ({} = {}) from by decide) same)",
                            quoted(&candidate.var),
                            quoted(&function.name)
                        ))
                    }
                })
                .collect::<Result<Vec<_>, CleanScalarModelError>>()?;
            let matching = format!("⟨{}, {}, rfl⟩", render_update(update), member_at(update_index));
            coordinates.push(format!(
                "functionCoordinateOfUpdatedAction {model_name} ({action_term}) before after ({entry}) {ZERO_FUNCTION} ({}) ({}) ({matching}) holds",
                member_at(function_index),
                every_term(&handlers)
            ));
        } else {
            coordinates.push(format!(
                "functionCoordinateOfUnchangedAction {model_name} ({action_term}) before after ({entry}) {ZERO_FUNCTION} ({}) ({}) ({}) holds",
                member_at(function_index),
                function_coordinate_at(row_proof, function_index),
                all_names_differ(action.updates.iter().map(|update| update.var.as_str()), &function.name)
            ));
        }
    }
    Ok(format!(
        "fun holds => ⟨{}, Member.head [], ⟨holds.2.1, True.intro, {}⟩⟩",
        generated_row(model),
        every_term(&coordinates)
    ))
}

fn generated_suffix(
    model: &CleanFiniteModel,
    model_name: &str,
    rows: &[Vec<u64>],
) -> Result<String, CleanScalarModelError> {
    if !model.scalar.variables.is_empty() {
        return Err(CleanScalarModelError::Definition(
            "the exact zero-function family currently requires no scalar state variables"
                .to_owned(),
        ));
    }
    if model.function_variables.is_empty() {
        return Err(CleanScalarModelError::Definition(
            "automatic finite proof requires at least one function-valued state variable"
                .to_owned(),
        ));
    }
    if rows.is_empty()
        || rows.iter().any(|row| {
            row.len() != model.function_variables.len() || row.iter().any(|value| *value != 0)
        })
    {
        return Err(CleanScalarModelError::Definition(
            "the exact zero-function family requires every independently replayed TY row to contain only zero function packs"
                .to_owned(),
        ));
    }

    let initial_coordinates = model
        .function_variables
        .iter()
        .enumerate()
        .map(|(index, entry)| {
            format!(
                "functionCoordinateOfInitial {model_name} state ({}) {ZERO_FUNCTION} ({}) (fun _ => rfl) initial",
                render_function_var(entry),
                member_at(index)
            )
        })
        .collect::<Vec<_>>();
    let initiation = format!(
        "fun state initial => ⟨{}, Member.head [], ⟨initial.1, True.intro, {}⟩⟩",
        generated_row(model),
        every_term(&initial_coordinates)
    );

    let action_handlers = model
        .scalar
        .actions
        .iter()
        .map(|action| action_handler(model, model_name, action))
        .collect::<Result<Vec<_>, _>>()?;
    let row_handler = format!(
        "fun rowProof => everyMember (fun candidate : Action => ActionHolds {model_name} candidate before after → FiniteRowsStrengthening {model_name} {GENERATED_ROWS} after) action {model_name}.actions ({}) actionFacts.1 actionFacts.2",
        every_term(&action_handlers)
    );
    let consecution = format!(
        "fun before after strengthening next => Exists.elim strengthening (fun row rowFacts => Exists.elim next (fun action actionFacts => everyMember (fun candidate : FiniteRow => FiniteRowDenotes {model_name} candidate before → FiniteRowsStrengthening {model_name} {GENERATED_ROWS} after) row {GENERATED_ROWS} (⟨{row_handler}, True.intro⟩) rowFacts.1 rowFacts.2))"
    );

    let invariant_handlers = model
        .scalar
        .invariants
        .iter()
        .map(|invariant| {
            let exact =
                exact_expression(model, model_name, "state", "rowProof", &[], &invariant.value)?;
            if !matches!(exact.value, ExactValue::Bool(true)) {
                return Err(CleanScalarModelError::Definition(format!(
                    "TY zero-function row violates invariant `{}`",
                    invariant.name
                )));
            }
            Ok(format!("({}).derives", exact.proof))
        })
        .collect::<Result<Vec<_>, CleanScalarModelError>>()?;
    let invariant_dispatch = format!(
        "fun rowProof invariant invariantMember => everyMember (fun candidate : Invariant => InvariantHolds {model_name} candidate state) invariant {model_name}.invariants ({}) invariantMember",
        every_term(&invariant_handlers)
    );
    let preservation = format!(
        "fun state strengthening => Exists.elim strengthening (fun row rowFacts => everyMember (fun candidate : FiniteRow => FiniteRowDenotes {model_name} candidate state → AllInvariantsHold {model_name} state) row {GENERATED_ROWS} (⟨{invariant_dispatch}, True.intro⟩) rowFacts.1 rowFacts.2)"
    );

    Ok(format!(
        "\nnamespace {GENERATED_NAMESPACE}\n\nopen Trust.Temporal.FiniteModel\n\ndef ZeroFunction : Nat → Bool :=\n  fun _ => false\n\ndef ReachableRows : List FiniteRow :=\n  [{}]\n\ndef AppliedClaim : Prop :=\n  SafetyClaim {model_name}\n\ntheorem AppliedProof : AppliedClaim :=\n  finiteSafetyClaimOfRows {model_name} ReachableRows\n    ({initiation})\n    ({consecution})\n    ({preservation})\n\nend {GENERATED_NAMESPACE}\n",
        generated_row(model)
    ))
}

fn exact_rows(
    certificate: &CleanFiniteModelCertificate,
    model: &CleanFiniteModel,
) -> Result<Vec<Vec<u64>>, CleanScalarModelError> {
    let parsed =
        tla_check::cert::SafetyCertificate::from_json(&certificate.safety_certificate_json)
            .map_err(CleanScalarModelError::ArtifactMismatch)?;
    let fixpoint = parsed.explicit_fixpoint.ok_or_else(|| {
        CleanScalarModelError::Definition(
            "automatic finite proof requires TY explicit-fixpoint evidence".to_owned(),
        )
    })?;
    if fixpoint.unbounded_invariant.is_some()
        || fixpoint.sorts.len() != model.scalar.variables.len() + model.function_variables.len()
    {
        return Err(CleanScalarModelError::Definition(
            "TY finite function columns differ from the exact Clean declaration order".to_owned(),
        ));
    }
    if !model.scalar.variables.is_empty() {
        return Err(CleanScalarModelError::Definition(
            "the zero-function authority family has no scalar columns".to_owned(),
        ));
    }
    for (sort, function) in fixpoint.sorts.iter().zip(&model.function_variables) {
        let (limit, _) = constant_found(model, &function.range_constant)?;
        match sort {
            tla_check::explicit_fixpoint_cert::ColSort::Func {
                base,
                arity,
                cells,
                dom,
                dom_kind,
            } if *base >= 2
                && u64::from(*arity) == limit
                && u64::try_from(cells.len()) == Ok(limit)
                && cells.iter().all(|cell| {
                    matches!(cell, tla_check::explicit_fixpoint_cert::CellSort::Bool)
                })
                && u64::try_from(dom.len()) == Ok(limit)
                && *dom_kind == tla_check::explicit_fixpoint_cert::EnumKind::Int
                && dom
                    .iter()
                    .zip(1..=limit)
                    .all(|(actual, expected)| actual == &expected.to_string()) => {}
            other => {
                return Err(CleanScalarModelError::Definition(format!(
                    "TY column for `{}` is not the exact bounded Boolean function carrier: {other:?}",
                    function.name
                )));
            }
        }
    }
    Ok(fixpoint.reachable)
}

fn bind_finite_and_proof(
    finite: &CleanFiniteModelCertificate,
    proof: &CleanAppliedModelProof,
) -> Result<(), CleanScalarModelError> {
    if finite.model.model_definition != proof.binding.model_definition
        || finite.model.type_expr != proof.binding.model_type
        || finite.model.value_expr != proof.binding.model_value
    {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "automatic finite rows and Clean proof name different model artifacts".to_owned(),
        ));
    }
    Ok(())
}

pub fn certify_automatic_clean_finite_model(
    clean_source: &str,
    model_definition: &str,
) -> Result<CleanAutomaticFiniteProof, CleanScalarModelError> {
    let finite = certify_clean_finite_model_with_ty(clean_source, model_definition)?;
    let decoded =
        crate::clean_model_lane::recheck_clean_finite_model_artifact(&finite.model, clean_source)?;
    let rows = exact_rows(&finite, &decoded)?;
    let generated_suffix = generated_suffix(&decoded, model_definition, &rows)?;
    let generated_source = format!("{clean_source}{generated_suffix}");
    let applied_proof = prove_clean_finite_model_safety_claim(
        &generated_source,
        model_definition,
        GENERATED_CLAIM,
        GENERATED_PROOF,
    )?;
    bind_finite_and_proof(&finite, &applied_proof)?;
    Ok(CleanAutomaticFiniteProof {
        schema: CLEAN_AUTOMATIC_FINITE_PROOF_SCHEMA_V1.to_owned(),
        finite,
        rows,
        generated_suffix,
        applied_proof,
    })
}

pub fn recheck_automatic_clean_finite_model(
    certificate: &CleanAutomaticFiniteProof,
    expected_clean_source: &str,
) -> Result<(), CleanScalarModelError> {
    if certificate.schema != CLEAN_AUTOMATIC_FINITE_PROOF_SCHEMA_V1 {
        return Err(CleanScalarModelError::ArtifactMismatch(format!(
            "unsupported automatic finite proof schema `{}`",
            certificate.schema
        )));
    }
    if certificate.finite.model.clean_source != expected_clean_source {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "authored Clean source changed".to_owned(),
        ));
    }
    bind_finite_and_proof(&certificate.finite, &certificate.applied_proof)?;
    if certificate.applied_proof.canonical_inhabitant != certificate.applied_proof.proof_value
        || certificate.applied_proof.canonical_inhabitant_type
            != certificate.applied_proof.binding.canonical_claim
    {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "automatic finite proof inhabitant fields are internally spliced".to_owned(),
        ));
    }
    recheck_clean_finite_model_with_ty(&certificate.finite, expected_clean_source)?;
    let decoded = crate::clean_model_lane::recheck_clean_finite_model_artifact(
        &certificate.finite.model,
        expected_clean_source,
    )?;
    let rows = exact_rows(&certificate.finite, &decoded)?;
    if rows != certificate.rows {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "function rows differ from freshly replayed TY fixpoint".to_owned(),
        ));
    }
    let suffix = generated_suffix(&decoded, &certificate.finite.model.model_definition, &rows)?;
    if suffix != certificate.generated_suffix {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "automatic finite proof source differs after deterministic regeneration".to_owned(),
        ));
    }
    let generated_source = format!("{expected_clean_source}{suffix}");
    if certificate.applied_proof.binding.clean_source != generated_source {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "applied function proof is not bound to the generated source".to_owned(),
        ));
    }
    recheck_clean_finite_model_safety_claim_proof(&certificate.applied_proof, &generated_source)
}

#[cfg(test)]
mod tests {
    use super::*;

    const FUNCTION_EXAMPLE_SOURCE: &str = r#"
namespace FunctionExample

def One : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.int 1
def Limit : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.constRef "Limit"
def Buggy : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.constRef "Buggy"
def Index : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.var "n"
def LiveAtIndex : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.fnAccess "live" Index
def CopyLive : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.comprehension "n" One Limit LiveAtIndex
def WholeLive : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.var "live"
def ClearFirst : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.except "live" One
    (Trust.Temporal.FiniteModel.ScalarExpr.bool false)
def AllFalse : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.forallIn "n" One Limit
    (Trust.Temporal.FiniteModel.ScalarExpr.iff LiveAtIndex
      (Trust.Temporal.FiniteModel.ScalarExpr.bool false))
def DialOff : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.eq Buggy
    (Trust.Temporal.FiniteModel.ScalarExpr.int 0)

def FunctionModel : Trust.Temporal.FiniteModel.Model :=
  Trust.Temporal.FiniteModel.Model.mk "CleanFunction"
    [Trust.Temporal.FiniteModel.Constant.mk "Buggy" 0,
     Trust.Temporal.FiniteModel.Constant.mk "Limit" 2]
    []
    [Trust.Temporal.FiniteModel.FunctionVar.mk "live" "Limit"]
    [Trust.Temporal.FiniteModel.Action.mk "CopyRange"
       Trust.Temporal.FiniteModel.Guard.always
       [Trust.Temporal.FiniteModel.Update.mk "live" CopyLive],
     Trust.Temporal.FiniteModel.Action.mk "CopyWhole"
       Trust.Temporal.FiniteModel.Guard.always
       [Trust.Temporal.FiniteModel.Update.mk "live" WholeLive],
     Trust.Temporal.FiniteModel.Action.mk "Clear"
       Trust.Temporal.FiniteModel.Guard.always
       [Trust.Temporal.FiniteModel.Update.mk "live" ClearFirst]]
    [Trust.Temporal.FiniteModel.Invariant.mk "Safe"
       (Trust.Temporal.FiniteModel.ScalarExpr.and DialOff AllFalse)]

def AppliedSafety : Prop :=
  Trust.Temporal.FiniteModel.SafetyClaim FunctionModel

end FunctionExample
"#;

    #[test]
    fn function_example_automatically_proves_and_freshly_replays() {
        let certificate = certify_automatic_clean_finite_model(
            FUNCTION_EXAMPLE_SOURCE,
            "FunctionExample.FunctionModel",
        )
        .expect("the exact FunctionExample vocabulary must automatically prove its Clean claim");
        assert_eq!(certificate.schema, CLEAN_AUTOMATIC_FINITE_PROOF_SCHEMA_V1);
        assert_eq!(certificate.rows, vec![vec![0]]);
        assert!(certificate.generated_suffix.contains("finiteSafetyClaimOfRows"));
        assert!(certificate.generated_suffix.contains("exactFunctionComprehension"));
        assert!(certificate.generated_suffix.contains("exactFunctionExcept"));
        assert_eq!(
            certificate.applied_proof.canonical_inhabitant,
            certificate.applied_proof.proof_value
        );
        assert_eq!(
            certificate.applied_proof.canonical_inhabitant_type,
            certificate.applied_proof.binding.canonical_claim
        );

        recheck_automatic_clean_finite_model(&certificate, FUNCTION_EXAMPLE_SOURCE)
            .expect("TY rows and the generated Clean proof must freshly replay");

        let encoded = serde_json::to_vec(&certificate)
            .expect("automatic finite proof certificate must serialize");
        let decoded: CleanAutomaticFiniteProof = serde_json::from_slice(&encoded)
            .expect("automatic finite proof certificate must deserialize");
        recheck_automatic_clean_finite_model(&decoded, FUNCTION_EXAMPLE_SOURCE)
            .expect("serialized automatic finite evidence must retain replay authority");
    }

    #[test]
    fn automatic_function_proof_tampering_fails_closed() {
        let certificate = certify_automatic_clean_finite_model(
            FUNCTION_EXAMPLE_SOURCE,
            "FunctionExample.FunctionModel",
        )
        .expect("the FunctionExample fixture must certify before mutation");

        let mut wrong_row = certificate.clone();
        wrong_row.rows[0][0] = 1;
        assert!(matches!(
            recheck_automatic_clean_finite_model(&wrong_row, FUNCTION_EXAMPLE_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));

        let mut wrong_suffix = certificate.clone();
        wrong_suffix.generated_suffix.push(' ');
        assert!(matches!(
            recheck_automatic_clean_finite_model(&wrong_suffix, FUNCTION_EXAMPLE_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));

        let mut spliced_inhabitant = certificate.clone();
        spliced_inhabitant.applied_proof.canonical_inhabitant.push(0);
        assert!(matches!(
            recheck_automatic_clean_finite_model(&spliced_inhabitant, FUNCTION_EXAMPLE_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));

        let mut wrong_schema = certificate;
        wrong_schema.schema = "trust.clean-automatic-finite-proof/unknown".to_owned();
        assert!(matches!(
            recheck_automatic_clean_finite_model(&wrong_schema, FUNCTION_EXAMPLE_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));
    }
}
