//! Automatic kernel proof synthesis for the retired scalar macro surface.
//!
//! The producer is deliberately untrusted.  It either quotes the exact reachable
//! rows from TY's independently replayed finite fixpoint evidence or translates
//! TY's supported parametric invariant witness.  Both paths emit a constructive
//! Clean proof of initiation, transition closure, and invariant preservation.
//! Fresh replay regenerates the source byte-for-byte and asks the Clean kernel to
//! check the resulting inhabitant of the exact applied model claim.

use num_bigint::BigUint;

use crate::clean_model_lane::{
    CleanAppliedModelProof, CleanScalarAction, CleanScalarExpr, CleanScalarModel,
    CleanScalarModelCertificate, CleanScalarModelError, CleanScalarUpdate,
    certify_clean_scalar_model_with_ty, prove_clean_scalar_model_safety_claim,
    recheck_clean_scalar_model_safety_claim_proof, recheck_clean_scalar_model_with_ty,
};

/// Schema for an automatically generated scalar safety proof.
pub const CLEAN_AUTOMATIC_SCALAR_PROOF_SCHEMA_V1: &str = "trust.clean-automatic-scalar-proof/v1";

const GENERATED_NAMESPACE: &str = "TrustGeneratedR5AutomaticScalar";
const GENERATED_ROWS: &str = "TrustGeneratedR5AutomaticScalar.ReachableRows";
const GENERATED_CLAIM: &str = "TrustGeneratedR5AutomaticScalar.AppliedClaim";
const GENERATED_PROOF: &str = "TrustGeneratedR5AutomaticScalar.AppliedProof";

/// TY evidence plus the deterministic Clean source that turns its finite rows or
/// parametric invariant witness into a proof of the exact state-machine claim.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CleanAutomaticScalarProof {
    pub schema: String,
    pub scalar: CleanScalarModelCertificate,
    pub family: CleanAutomaticScalarProofFamily,
    pub rows: Vec<Vec<u64>>,
    pub generated_suffix: String,
    pub applied_proof: CleanAppliedModelProof,
}

/// Exact proof family selected from freshly replayed TY evidence.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CleanAutomaticScalarProofFamily {
    FiniteRows,
    UnboundedAffine { init: u64, delta: u64, bound: u64 },
    UnboundedAffineTuple { pairs: Vec<(u64, u64)> },
    UnboundedRelational { init: u64, delta: u64 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ScalarValue {
    Nat(BigUint),
    Bool(bool),
}

impl ScalarValue {
    fn lean_term(&self) -> String {
        match self {
            Self::Nat(value) => format!("Value.nat {value}"),
            Self::Bool(value) => format!("Value.bool {value}"),
        }
    }

    fn as_nat(&self, context: &str) -> Result<&BigUint, CleanScalarModelError> {
        match self {
            Self::Nat(value) => Ok(value),
            Self::Bool(_) => Err(CleanScalarModelError::Definition(format!(
                "automatic scalar proof expected Nat in {context}"
            ))),
        }
    }

    fn as_bool(&self, context: &str) -> Result<bool, CleanScalarModelError> {
        match self {
            Self::Bool(value) => Ok(*value),
            Self::Nat(_) => Err(CleanScalarModelError::Definition(format!(
                "automatic scalar proof expected Bool in {context}"
            ))),
        }
    }
}

#[derive(Debug)]
struct ExactExpr {
    expression: String,
    value: ScalarValue,
    proof: String,
}

fn quoted(value: &str) -> String {
    // Temporal identifiers are already constrained to ASCII identifier bytes,
    // but JSON string quoting also keeps this helper correct if that admission
    // policy is widened later.
    serde_json::to_string(value).expect("String serialization cannot fail")
}

fn lean_list(items: &[String]) -> String {
    format!("[{}]", items.join(", "))
}

fn nat_row(row: &[u64]) -> String {
    lean_list(&row.iter().map(u64::to_string).collect::<Vec<_>>())
}

fn rows_term(rows: &[Vec<u64>]) -> String {
    lean_list(&rows.iter().map(|row| nat_row(row)).collect::<Vec<_>>())
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

fn coordinate_at(row_proof: &str, index: usize) -> String {
    let mut coordinate = format!("({row_proof}).2");
    for _ in 0..index {
        coordinate.push_str(".2");
    }
    coordinate.push_str(".1");
    coordinate
}

fn every_coordinate_at(proof: &str, index: usize) -> String {
    let mut coordinate = format!("({proof})");
    for _ in 0..index {
        coordinate.push_str(".2");
    }
    coordinate.push_str(".1");
    coordinate
}

fn render_expr(expression: &CleanScalarExpr) -> String {
    enum Task<'a> {
        Visit(&'a CleanScalarExpr),
        Combine(&'a CleanScalarExpr),
    }

    let mut tasks = vec![Task::Visit(expression)];
    let mut rendered = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(node) => match node {
                CleanScalarExpr::Int(value) => {
                    rendered.push(format!("ScalarExpr.int {value}"));
                }
                CleanScalarExpr::Var(name) => {
                    rendered.push(format!("ScalarExpr.var {}", quoted(name)));
                }
                CleanScalarExpr::ConstRef(name) => {
                    rendered.push(format!("ScalarExpr.constRef {}", quoted(name)));
                }
                CleanScalarExpr::Add(left, right)
                | CleanScalarExpr::Sub(left, right)
                | CleanScalarExpr::Gt(left, right)
                | CleanScalarExpr::Le(left, right)
                | CleanScalarExpr::Eq(left, right) => {
                    tasks.push(Task::Combine(node));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                }
                CleanScalarExpr::If(condition, then_value, else_value) => {
                    tasks.push(Task::Combine(node));
                    tasks.push(Task::Visit(else_value));
                    tasks.push(Task::Visit(then_value));
                    tasks.push(Task::Visit(condition));
                }
                // These forms are in the wider finite ABI, but were never
                // accepted by the retired DSL's ratified scalar grammar.
                CleanScalarExpr::Neq(..)
                | CleanScalarExpr::Or(..)
                | CleanScalarExpr::And(..)
                | CleanScalarExpr::Iff(..)
                | CleanScalarExpr::Forall(..)
                | CleanScalarExpr::FnAccess(..)
                | CleanScalarExpr::Except(..)
                | CleanScalarExpr::Comprehension(..)
                | CleanScalarExpr::Bool(_) => {
                    rendered.push("__unsupported_scalar_expression__".to_owned());
                }
            },
            Task::Combine(node) => {
                let mut operand = || rendered.pop().expect("expression operand was rendered");
                let term = match node {
                    CleanScalarExpr::Add(..) => {
                        let (right, left) = (operand(), operand());
                        format!("ScalarExpr.add ({left}) ({right})")
                    }
                    CleanScalarExpr::Sub(..) => {
                        let (right, left) = (operand(), operand());
                        format!("ScalarExpr.sub ({left}) ({right})")
                    }
                    CleanScalarExpr::Gt(..) => {
                        let (right, left) = (operand(), operand());
                        format!("ScalarExpr.gt ({left}) ({right})")
                    }
                    CleanScalarExpr::Le(..) => {
                        let (right, left) = (operand(), operand());
                        format!("ScalarExpr.le ({left}) ({right})")
                    }
                    CleanScalarExpr::Eq(..) => {
                        let (right, left) = (operand(), operand());
                        format!("ScalarExpr.eq ({left}) ({right})")
                    }
                    CleanScalarExpr::If(..) => {
                        let (else_value, then_value, condition) = (operand(), operand(), operand());
                        format!("ScalarExpr.ite ({condition}) ({then_value}) ({else_value})")
                    }
                    _ => unreachable!("only legacy compound expressions are combined"),
                };
                rendered.push(term);
            }
        }
    }
    rendered.pop().expect("one expression was rendered")
}

fn render_update(update: &CleanScalarUpdate) -> String {
    format!("Update.mk {} ({})", quoted(&update.var), render_expr(&update.value))
}

fn render_action(action: &CleanScalarAction) -> String {
    let guard = action.guard.as_ref().map_or_else(
        || "Guard.always".to_owned(),
        |guard| format!("Guard.when ({})", render_expr(guard)),
    );
    let updates = action.updates.iter().map(render_update).collect::<Vec<_>>();
    format!("Action.mk {} ({guard}) {}", quoted(&action.name), lean_list(&updates))
}

fn render_state_var(model: &CleanScalarModel, index: usize) -> String {
    let entry = &model.variables[index];
    format!("StateVar.mk {} {}", quoted(&entry.name), entry.init)
}

fn biguint_to_u64(value: &BigUint, context: &str) -> Result<u64, CleanScalarModelError> {
    let digits = value.to_u64_digits();
    if digits.len() > 1 {
        return Err(CleanScalarModelError::Definition(format!(
            "automatic scalar proof value exceeds TY's u64 row carrier in {context}: {value}"
        )));
    }
    Ok(digits.first().copied().unwrap_or(0))
}

fn exact_expression(
    model: &CleanScalarModel,
    model_name: &str,
    state_name: &str,
    row: &[u64],
    row_proof: &str,
    expression: &CleanScalarExpr,
) -> Result<ExactExpr, CleanScalarModelError> {
    enum Task<'a> {
        Visit(&'a CleanScalarExpr),
        Combine(&'a CleanScalarExpr),
    }

    let applied_model = format!("{model_name}.asModel");
    let mut tasks = vec![Task::Visit(expression)];
    let mut values: Vec<ExactExpr> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(node) => match node {
                CleanScalarExpr::Int(value) => {
                    let value = u64::try_from(*value).map_err(|_| {
                        CleanScalarModelError::Definition(
                            "automatic scalar proofs accept only nonnegative macro literals"
                                .to_owned(),
                        )
                    })?;
                    let expression = format!("ScalarExpr.int {value}");
                    values.push(ExactExpr {
                        expression,
                        value: ScalarValue::Nat(BigUint::from(value)),
                        proof: format!("exactScalarInt {applied_model} {state_name} {value}"),
                    });
                }
                CleanScalarExpr::Var(name) => {
                    let index =
                        model.variables.iter().position(|entry| entry.name == *name).ok_or_else(
                            || {
                                CleanScalarModelError::Definition(format!(
                                    "automatic scalar proof found undeclared variable `{name}`"
                                ))
                            },
                        )?;
                    let value = *row.get(index).ok_or_else(|| {
                        CleanScalarModelError::Definition(
                            "reachable row width differs from scalar declaration order".to_owned(),
                        )
                    })?;
                    let entry = render_state_var(model, index);
                    let declared = format!("⟨{entry}, {}, rfl⟩", member_at(index));
                    let coordinate = coordinate_at(row_proof, index);
                    let expression = format!("ScalarExpr.var {}", quoted(name));
                    let no_function = format!(
                        "fun range found => scalarModelNoFunctionRange {model_name} {} range found",
                        quoted(name)
                    );
                    values.push(ExactExpr {
                        expression,
                        value: ScalarValue::Nat(BigUint::from(value)),
                        proof: format!(
                            "exactScalarVar {applied_model} {state_name} {} {value} ({declared}) ({coordinate}) ({no_function})",
                            quoted(name)
                        ),
                    });
                }
                CleanScalarExpr::ConstRef(name) => {
                    let index =
                        model.constants.iter().position(|entry| entry.name == *name).ok_or_else(
                            || {
                                CleanScalarModelError::Definition(format!(
                                    "automatic scalar proof found undeclared constant `{name}`"
                                ))
                            },
                        )?;
                    let constant = &model.constants[index];
                    let value = u64::try_from(constant.value).map_err(|_| {
                        CleanScalarModelError::Definition(format!(
                            "constant `{name}` is outside the Clean Nat carrier"
                        ))
                    })?;
                    let entry = format!("Constant.mk {} {value}", quoted(&constant.name));
                    let found = format!("⟨{entry}, {}, rfl, rfl⟩", member_at(index));
                    let handlers = model
                        .constants
                        .iter()
                        .map(|candidate| {
                            if candidate.name == *name {
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
                        "uniqueConstantValueOfEvery {applied_model} {} {value} ({})",
                        quoted(name),
                        every_term(&handlers)
                    );
                    let expression = format!("ScalarExpr.constRef {}", quoted(name));
                    values.push(ExactExpr {
                        expression,
                        value: ScalarValue::Nat(BigUint::from(value)),
                        proof: format!(
                            "exactScalarConst {applied_model} {state_name} {} {value} ({found}) ({unique})",
                            quoted(name)
                        ),
                    });
                }
                CleanScalarExpr::Add(left, right)
                | CleanScalarExpr::Sub(left, right)
                | CleanScalarExpr::Gt(left, right)
                | CleanScalarExpr::Le(left, right)
                | CleanScalarExpr::Eq(left, right) => {
                    tasks.push(Task::Combine(node));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                }
                CleanScalarExpr::If(condition, then_value, else_value) => {
                    tasks.push(Task::Combine(node));
                    tasks.push(Task::Visit(else_value));
                    tasks.push(Task::Visit(then_value));
                    tasks.push(Task::Visit(condition));
                }
                CleanScalarExpr::Neq(..)
                | CleanScalarExpr::Or(..)
                | CleanScalarExpr::And(..)
                | CleanScalarExpr::Iff(..)
                | CleanScalarExpr::Forall(..)
                | CleanScalarExpr::FnAccess(..)
                | CleanScalarExpr::Except(..)
                | CleanScalarExpr::Comprehension(..)
                | CleanScalarExpr::Bool(_) => {
                    return Err(CleanScalarModelError::Definition(
                        "automatic scalar proof is restricted to the ratified scalar grammar"
                            .to_owned(),
                    ));
                }
            },
            Task::Combine(node) => match node {
                CleanScalarExpr::Add(..) | CleanScalarExpr::Sub(..) => {
                    let right = values.pop().expect("right expression proof exists");
                    let left = values.pop().expect("left expression proof exists");
                    let left_value = left.value.as_nat("arithmetic left operand")?;
                    let right_value = right.value.as_nat("arithmetic right operand")?;
                    let result = if matches!(node, CleanScalarExpr::Add(..)) {
                        left_value + right_value
                    } else if left_value >= right_value {
                        left_value - right_value
                    } else {
                        BigUint::from(0_u8)
                    };
                    let constructor =
                        if matches!(node, CleanScalarExpr::Add(..)) { "add" } else { "sub" };
                    let theorem = if matches!(node, CleanScalarExpr::Add(..)) {
                        "exactScalarAdd"
                    } else {
                        "exactScalarSub"
                    };
                    let expression = format!(
                        "ScalarExpr.{constructor} ({}) ({})",
                        left.expression, right.expression
                    );
                    let proof = format!(
                        "{theorem} {applied_model} {state_name} ({}) ({}) {} {} ({}) ({})",
                        left.expression,
                        right.expression,
                        left_value,
                        right_value,
                        left.proof,
                        right.proof
                    );
                    values.push(ExactExpr { expression, value: ScalarValue::Nat(result), proof });
                }
                CleanScalarExpr::Gt(..) | CleanScalarExpr::Le(..) | CleanScalarExpr::Eq(..) => {
                    let right = values.pop().expect("right expression proof exists");
                    let left = values.pop().expect("left expression proof exists");
                    let left_value = left.value.as_nat("comparison left operand")?;
                    let right_value = right.value.as_nat("comparison right operand")?;
                    let (constructor, theorem, truth, relation_proof) = match node {
                        CleanScalarExpr::Gt(..) if left_value > right_value => {
                            ("gt", "exactScalarGtTrue", true, "by decide")
                        }
                        CleanScalarExpr::Gt(..) => ("gt", "exactScalarGtFalse", false, "by decide"),
                        CleanScalarExpr::Le(..) if left_value <= right_value => {
                            ("le", "exactScalarLeTrue", true, "by decide")
                        }
                        CleanScalarExpr::Le(..) => ("le", "exactScalarLeFalse", false, "by decide"),
                        CleanScalarExpr::Eq(..) if left_value == right_value => {
                            ("eq", "exactScalarEqTrue", true, "rfl")
                        }
                        CleanScalarExpr::Eq(..) => ("eq", "exactScalarEqFalse", false, "by decide"),
                        _ => unreachable!(),
                    };
                    let expression = format!(
                        "ScalarExpr.{constructor} ({}) ({})",
                        left.expression, right.expression
                    );
                    let proof = format!(
                        "{theorem} {applied_model} {state_name} ({}) ({}) {} {} ({}) ({}) ({relation_proof})",
                        left.expression,
                        right.expression,
                        left_value,
                        right_value,
                        left.proof,
                        right.proof
                    );
                    values.push(ExactExpr { expression, value: ScalarValue::Bool(truth), proof });
                }
                CleanScalarExpr::If(..) => {
                    let else_value = values.pop().expect("else expression proof exists");
                    let then_value = values.pop().expect("then expression proof exists");
                    let condition = values.pop().expect("condition expression proof exists");
                    let condition_truth = condition.value.as_bool("conditional guard")?;
                    if then_value.value != else_value.value
                        && std::mem::discriminant(&then_value.value)
                            != std::mem::discriminant(&else_value.value)
                    {
                        return Err(CleanScalarModelError::Definition(
                            "automatic scalar proof found mixed conditional branch sorts"
                                .to_owned(),
                        ));
                    }
                    let chosen = if condition_truth { &then_value } else { &else_value };
                    let theorem =
                        if condition_truth { "exactScalarIteTrue" } else { "exactScalarIteFalse" };
                    let expression = format!(
                        "ScalarExpr.ite ({}) ({}) ({})",
                        condition.expression, then_value.expression, else_value.expression
                    );
                    let proof = format!(
                        "{theorem} {applied_model} {state_name} ({}) ({}) ({}) ({}) ({}) ({})",
                        condition.expression,
                        then_value.expression,
                        else_value.expression,
                        chosen.value.lean_term(),
                        condition.proof,
                        chosen.proof
                    );
                    values.push(ExactExpr { expression, value: chosen.value.clone(), proof });
                }
                _ => unreachable!("unsupported expressions decline before combination"),
            },
        }
    }
    values.pop().ok_or_else(|| {
        CleanScalarModelError::Definition(
            "automatic scalar evaluator produced no result".to_owned(),
        )
    })
}

fn exact_update_handlers(
    model: &CleanScalarModel,
    model_name: &str,
    before: &str,
    after: &str,
    row: &[u64],
    row_proof: &str,
    action: &CleanScalarAction,
    variable_index: usize,
    expected: u64,
) -> Result<Vec<String>, CleanScalarModelError> {
    let variable = &model.variables[variable_index];
    action
        .updates
        .iter()
        .map(|update| {
            if update.var == variable.name {
                let exact = exact_expression(
                    model,
                    model_name,
                    before,
                    row,
                    row_proof,
                    &update.value,
                )?;
                let actual = biguint_to_u64(
                    exact.value.as_nat("scalar update")?,
                    "scalar update",
                )?;
                if actual != expected {
                    return Err(CleanScalarModelError::Definition(format!(
                        "generated successor disagrees with exact update for `{}`",
                        variable.name
                    )));
                }
                Ok(format!(
                    "fun _ evaluation => congrArg valueNatProjection (({}).unique (Value.nat ({after}.scalar {})) evaluation)",
                    exact.proof,
                    quoted(&variable.name)
                ))
            } else {
                Ok(format!(
                    "fun same _ => False.elim ((show ¬ ({} = {}) from by decide) same)",
                    quoted(&update.var),
                    quoted(&variable.name)
                ))
            }
        })
        .collect()
}

fn action_handler(
    model: &CleanScalarModel,
    model_name: &str,
    rows: &[Vec<u64>],
    before: &str,
    after: &str,
    row: &[u64],
    row_proof: &str,
    action: &CleanScalarAction,
) -> Result<String, CleanScalarModelError> {
    if let Some(guard) = &action.guard {
        let exact = exact_expression(model, model_name, before, row, row_proof, guard)?;
        if !exact.value.as_bool("action guard")? {
            return Ok(format!(
                "fun holds => False.elim (falseOfExactFalseEvaluatesTrue {model_name}.asModel {before} ({}) ({}) holds.1)",
                exact.expression, exact.proof
            ));
        }
    }

    let mut successor = row.to_vec();
    for update in &action.updates {
        let index =
            model.variables.iter().position(|entry| entry.name == update.var).ok_or_else(|| {
                CleanScalarModelError::Definition(format!(
                    "action `{}` updates unknown variable `{}`",
                    action.name, update.var
                ))
            })?;
        let exact = exact_expression(model, model_name, before, row, row_proof, &update.value)?;
        successor[index] =
            biguint_to_u64(exact.value.as_nat("action update")?, "action successor")?;
    }
    let successor_index = rows.iter().position(|candidate| *candidate == successor).ok_or_else(|| {
        CleanScalarModelError::Definition(format!(
            "TY reachable rows are not closed under Clean action `{}` from row {:?}: successor {:?}",
            action.name, row, successor
        ))
    })?;

    let action_term = render_action(action);
    let mut coordinates = Vec::with_capacity(model.variables.len());
    for (index, variable) in model.variables.iter().enumerate() {
        let entry = render_state_var(model, index);
        let entry_member = member_at(index);
        if let Some(update_index) =
            action.updates.iter().position(|update| update.var == variable.name)
        {
            let update = &action.updates[update_index];
            let handlers = exact_update_handlers(
                model,
                model_name,
                before,
                after,
                row,
                row_proof,
                action,
                index,
                successor[index],
            )?;
            let has_matching =
                format!("⟨{}, {}, rfl⟩", render_update(update), member_at(update_index));
            coordinates.push(format!(
                "scalarCoordinateOfUpdatedAction {model_name}.asModel ({action_term}) {before} {after} ({entry}) {} ({entry_member}) ({}) ({has_matching}) holds",
                successor[index],
                every_term(&handlers)
            ));
        } else {
            let handlers = action
                .updates
                .iter()
                .map(|update| {
                    format!(
                        "show ¬ ({} = {}) from by decide",
                        quoted(&update.var),
                        quoted(&variable.name)
                    )
                })
                .collect::<Vec<_>>();
            coordinates.push(format!(
                "scalarCoordinateOfUnchangedAction {model_name}.asModel ({action_term}) {before} {after} ({entry}) {} ({entry_member}) ({}) ({}) holds",
                successor[index],
                coordinate_at(row_proof, index),
                every_term(&handlers)
            ));
        }
    }
    let coordinates = every_term(&coordinates);
    Ok(format!(
        "fun holds => ⟨{}, {}, ⟨holds.2.1, {}⟩⟩",
        nat_row(&successor),
        member_at(successor_index),
        coordinates
    ))
}

fn finite_generated_suffix(
    model: &CleanScalarModel,
    model_name: &str,
    rows: &[Vec<u64>],
) -> Result<String, CleanScalarModelError> {
    if rows.is_empty() {
        return Err(CleanScalarModelError::Definition(
            "finite automatic proof requires a nonempty reachable set".to_owned(),
        ));
    }
    if rows.iter().any(|row| row.len() != model.variables.len()) {
        return Err(CleanScalarModelError::Definition(
            "reachable row width differs from scalar model declarations".to_owned(),
        ));
    }
    if model.variables.is_empty() {
        return Err(CleanScalarModelError::Definition(
            "automatic macro-retirement proof requires at least one scalar variable".to_owned(),
        ));
    }

    let initial_row = model
        .variables
        .iter()
        .map(|entry| {
            u64::try_from(entry.init).map_err(|_| {
                CleanScalarModelError::Definition(format!(
                    "initial value for `{}` is outside Clean Nat",
                    entry.name
                ))
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let initial_index = rows.iter().position(|row| *row == initial_row).ok_or_else(|| {
        CleanScalarModelError::Definition(
            "TY reachable rows omit the exact Clean initial state".to_owned(),
        )
    })?;
    let initial_coordinates = model
        .variables
        .iter()
        .enumerate()
        .map(|(index, _)| {
            format!("initial.2.1 ({}) ({})", render_state_var(model, index), member_at(index))
        })
        .collect::<Vec<_>>();
    let initiation = format!(
        "fun state initial => ⟨{}, {}, ⟨initial.1, {}⟩⟩",
        nat_row(&initial_row),
        member_at(initial_index),
        every_term(&initial_coordinates)
    );

    let before = "before";
    let after = "after";
    let row_proof = "beforeRow";
    let mut row_action_dispatch = Vec::with_capacity(rows.len());
    for row in rows {
        let action_handlers = model
            .actions
            .iter()
            .map(|action| {
                action_handler(model, model_name, rows, before, after, row, row_proof, action)
            })
            .collect::<Result<Vec<_>, _>>()?;
        row_action_dispatch.push(format!(
            "fun {row_proof} => everyMember (fun candidate : Action => ActionHolds {model_name}.asModel candidate {before} {after} → ScalarRowsStrengthening {model_name} {GENERATED_ROWS} {after}) action {model_name}.actions ({}) actionFacts.1 actionFacts.2",
            every_term(&action_handlers)
        ));
    }
    let consecution = format!(
        "fun {before} {after} strengthening next => Exists.elim strengthening (fun row rowFacts => Exists.elim next (fun action actionFacts => everyMember (fun candidate : List Nat => ScalarRowDenotes {model_name} candidate {before} → ScalarRowsStrengthening {model_name} {GENERATED_ROWS} {after}) row {GENERATED_ROWS} ({}) rowFacts.1 rowFacts.2))",
        every_term(&row_action_dispatch)
    );

    let mut row_invariant_dispatch = Vec::with_capacity(rows.len());
    for row in rows {
        let invariant_handlers = model
            .invariants
            .iter()
            .map(|invariant| {
                let exact = exact_expression(
                    model,
                    model_name,
                    "state",
                    row,
                    "rowProof",
                    &invariant.value,
                )?;
                if !exact.value.as_bool("invariant")? {
                    return Err(CleanScalarModelError::Definition(format!(
                        "reachable row {:?} violates Clean invariant `{}`",
                        row, invariant.name
                    )));
                }
                Ok(format!("({}).derives", exact.proof))
            })
            .collect::<Result<Vec<_>, _>>()?;
        row_invariant_dispatch.push(format!(
            "fun rowProof invariant invariantMember => everyMember (fun candidate : Invariant => InvariantHolds {model_name}.asModel candidate state) invariant {model_name}.invariants ({}) invariantMember",
            every_term(&invariant_handlers)
        ));
    }
    let preservation = format!(
        "fun state strengthening => Exists.elim strengthening (fun row rowFacts => everyMember (fun candidate : List Nat => ScalarRowDenotes {model_name} candidate state → AllInvariantsHold {model_name}.asModel state) row {GENERATED_ROWS} ({}) rowFacts.1 rowFacts.2)",
        every_term(&row_invariant_dispatch)
    );

    Ok(format!(
        "\nnamespace {GENERATED_NAMESPACE}\n\nopen Trust.Temporal.FiniteModel\n\ndef ReachableRows : List (List Nat) :=\n  {}\n\ndef AppliedClaim : Prop :=\n  ScalarModel.safetyClaim {model_name}\n\ntheorem AppliedProof : AppliedClaim :=\n  scalarSafetyClaimOfRows {model_name} ReachableRows\n    ({initiation})\n    ({consecution})\n    ({preservation})\n\nend {GENERATED_NAMESPACE}\n",
        rows_term(rows)
    ))
}

fn is_ground_affine_expression(expression: &CleanScalarExpr) -> bool {
    let mut pending = vec![expression];
    while let Some(node) = pending.pop() {
        match node {
            CleanScalarExpr::Int(_) | CleanScalarExpr::ConstRef(_) => {}
            CleanScalarExpr::Add(left, right) | CleanScalarExpr::Sub(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            _ => return false,
        }
    }
    true
}

fn is_scalar_var(expression: &CleanScalarExpr, name: &str) -> bool {
    matches!(expression, CleanScalarExpr::Var(found) if found == name)
}

fn symbolic_var_exact(
    model: &CleanScalarModel,
    model_name: &str,
    state: &str,
    name: &str,
) -> Result<ExactExpr, CleanScalarModelError> {
    let index = model.variables.iter().position(|entry| entry.name == name).ok_or_else(|| {
        CleanScalarModelError::Definition(format!(
            "unbounded affine proof found undeclared scalar `{name}`"
        ))
    })?;
    let expression = format!("ScalarExpr.var {}", quoted(name));
    let entry = render_state_var(model, index);
    let declared = format!("⟨{entry}, {}, rfl⟩", member_at(index));
    let value = format!("{state}.scalar {}", quoted(name));
    let no_function = format!(
        "fun range found => scalarModelNoFunctionRange {model_name} {} range found",
        quoted(name)
    );
    Ok(ExactExpr {
        expression,
        // This field is not consulted for symbolic expressions.  Keeping a
        // concrete placeholder would be dangerous, so callers use only the
        // rendered proof and expression and the private function does not
        // escape this module.
        value: ScalarValue::Nat(BigUint::from(0_u8)),
        proof: format!(
            "exactScalarVar {model_name}.asModel {state} {} ({value}) ({declared}) rfl ({no_function})",
            quoted(name)
        ),
    })
}

fn unbounded_updated_coordinate(
    model: &CleanScalarModel,
    model_name: &str,
    action: &CleanScalarAction,
    variable_index: usize,
    expected_delta: u64,
    before: &str,
    after: &str,
    holds: &str,
) -> Result<String, CleanScalarModelError> {
    let variable = model.variables.get(variable_index).ok_or_else(|| {
        CleanScalarModelError::Definition(
            "unbounded witness variable index exceeds the Clean declaration list".to_owned(),
        )
    })?;
    let matching = action
        .updates
        .iter()
        .enumerate()
        .filter(|(_, update)| update.var == variable.name)
        .collect::<Vec<_>>();
    let [(update_index, update)] = matching.as_slice() else {
        return Err(CleanScalarModelError::Definition(format!(
            "unbounded affine action must update `{}` exactly once",
            variable.name
        )));
    };
    let delta_expression = match &update.value {
        CleanScalarExpr::Add(left, right)
            if is_scalar_var(left, &variable.name) && is_ground_affine_expression(right) =>
        {
            right.as_ref()
        }
        CleanScalarExpr::Add(left, right)
            if is_ground_affine_expression(left) && is_scalar_var(right, &variable.name) =>
        {
            left.as_ref()
        }
        _ => {
            return Err(CleanScalarModelError::Definition(format!(
                "unbounded affine update for `{}` must have exact owner form `x + ground-delta`",
                variable.name
            )));
        }
    };
    let zero_row = vec![0; model.variables.len()];
    let delta_exact = exact_expression(
        model,
        model_name,
        before,
        &zero_row,
        "unusedGroundRow",
        delta_expression,
    )?;
    let delta = biguint_to_u64(
        delta_exact.value.as_nat("unbounded affine delta")?,
        "unbounded affine delta",
    )?;
    if delta != expected_delta {
        return Err(CleanScalarModelError::Definition(format!(
            "TY affine delta for `{}` differs from the exact Clean update expression",
            variable.name
        )));
    }
    let before_var = symbolic_var_exact(model, model_name, before, &variable.name)?;
    let (
        left_expression,
        right_expression,
        left_proof,
        right_proof,
        left_value,
        right_value,
        variable_on_left,
    ) = match &update.value {
        CleanScalarExpr::Add(left, _) if is_scalar_var(left, &variable.name) => (
            before_var.expression,
            delta_exact.expression,
            before_var.proof,
            delta_exact.proof,
            format!("{before}.scalar {}", quoted(&variable.name)),
            delta.to_string(),
            true,
        ),
        CleanScalarExpr::Add(_, right) if is_scalar_var(right, &variable.name) => (
            delta_exact.expression,
            before_var.expression,
            delta_exact.proof,
            before_var.proof,
            delta.to_string(),
            format!("{before}.scalar {}", quoted(&variable.name)),
            false,
        ),
        _ => unreachable!("the exact affine update orientation was checked above"),
    };
    let update_exact = format!(
        "exactScalarAdd {model_name}.asModel {before} ({left_expression}) ({right_expression}) ({left_value}) ({right_value}) ({left_proof}) ({right_proof})"
    );
    let update_handlers = action
        .updates
        .iter()
        .enumerate()
        .map(|(index, candidate)| {
            if index == *update_index {
                let exact_equality = format!(
                    "congrArg valueNatProjection (({update_exact}).unique (Value.nat ({after}.scalar {})) evaluation)",
                    quoted(&variable.name)
                );
                let normalized = if variable_on_left {
                    exact_equality
                } else {
                    format!(
                        "Eq.trans ({exact_equality}) (Nat.add_comm {delta} ({before}.scalar {}))",
                        quoted(&variable.name)
                    )
                };
                format!("fun _ evaluation => {normalized}")
            } else {
                format!(
                    "fun same _ => False.elim ((show ¬ ({} = {}) from by decide) same)",
                    quoted(&candidate.var),
                    quoted(&variable.name)
                )
            }
        })
        .collect::<Vec<_>>();
    let action_term = render_action(action);
    let entry = render_state_var(model, variable_index);
    Ok(format!(
        "namedScalarCoordinateOfUpdatedAction {model_name}.asModel ({action_term}) {before} {after} ({entry}) {} ({before}.scalar {} + {delta}) ({}) rfl ({}) (⟨{}, {}, rfl⟩) {holds}",
        quoted(&variable.name),
        quoted(&variable.name),
        member_at(variable_index),
        every_term(&update_handlers),
        render_update(update),
        member_at(*update_index)
    ))
}

fn unbounded_generated_suffix(
    model: &CleanScalarModel,
    model_name: &str,
    witness: &tla_check::explicit_fixpoint_cert::UnboundedInvariantCert,
) -> Result<String, CleanScalarModelError> {
    if model.variables.len() != 1
        || model.actions.len() != 1
        || model.invariants.len() != 1
        || witness.relational.is_some()
        || witness.pairs.len() != 1
    {
        return Err(CleanScalarModelError::Definition(
            "unbounded automatic proof accepts exactly one scalar, one affine action, and one lower-bound invariant"
                .to_owned(),
        ));
    }
    let variable = &model.variables[0];
    let init = u64::try_from(variable.init).map_err(|_| {
        CleanScalarModelError::Definition(
            "unbounded affine initializer is outside Clean Nat".to_owned(),
        )
    })?;
    if witness.init != init
        || witness.delta != witness.pairs[0].1
        || witness.init != witness.pairs[0].0
        || init < witness.bound
    {
        return Err(CleanScalarModelError::Definition(
            "TY unbounded witness does not match the exact Clean initializer/bound".to_owned(),
        ));
    }

    let action = &model.actions[0];
    if action.guard.is_some() || action.updates.len() != 1 || action.updates[0].var != variable.name
    {
        return Err(CleanScalarModelError::Definition(
            "unbounded affine action must be unguarded and update the sole scalar exactly once"
                .to_owned(),
        ));
    }
    let entry = render_state_var(model, 0);
    let coordinate = unbounded_updated_coordinate(
        model,
        model_name,
        action,
        0,
        witness.delta,
        "before",
        "after",
        "holds",
    )?;
    let action_handler = format!(
        "fun holds => Eq.mpr (congrArg (fun value : Nat => Nat.le {} value) ({coordinate})) (Nat.le_trans {} (before.scalar {}) (before.scalar {} + {}) lower (Nat.le_add_right (before.scalar {}) {}))",
        witness.bound,
        witness.bound,
        quoted(&variable.name),
        quoted(&variable.name),
        witness.delta,
        quoted(&variable.name),
        witness.delta
    );
    let strengthening = format!(
        "fun state : State => Nat.le {} (state.scalar {})",
        witness.bound,
        quoted(&variable.name)
    );
    let initiation = format!(
        "fun state initial => scalarLowerBoundOfInitial {model_name}.asModel state ({entry}) {} {init} {} ({}) rfl rfl (by decide) initial",
        quoted(&variable.name),
        witness.bound,
        member_at(0)
    );
    let consecution = format!(
        "fun before after lower next => Exists.elim next (fun action facts => everyMember (fun candidate : Action => ActionHolds {model_name}.asModel candidate before after → Nat.le {} (after.scalar {})) action {model_name}.actions ({}) facts.1 facts.2)",
        witness.bound,
        quoted(&variable.name),
        every_term(&[action_handler])
    );

    let invariant = &model.invariants[0];
    let lower_expression = match &invariant.value {
        CleanScalarExpr::Le(lower, upper)
            if is_ground_affine_expression(lower) && is_scalar_var(upper, &variable.name) =>
        {
            lower.as_ref()
        }
        _ => {
            return Err(CleanScalarModelError::Definition(
                "unbounded affine invariant must have exact owner form `ground-bound <= x`"
                    .to_owned(),
            ));
        }
    };
    let lower_exact =
        exact_expression(model, model_name, "state", &[0], "unusedGroundRow", lower_expression)?;
    let lower = biguint_to_u64(
        lower_exact.value.as_nat("unbounded safety lower bound")?,
        "unbounded safety lower bound",
    )?;
    if lower != witness.bound {
        return Err(CleanScalarModelError::Definition(
            "TY safety bound differs from the exact Clean invariant".to_owned(),
        ));
    }
    let state_var = symbolic_var_exact(model, model_name, "state", &variable.name)?;
    let invariant_exact = format!(
        "exactScalarLeTrue {model_name}.asModel state ({}) ({}) {lower} (state.scalar {}) ({}) ({}) lower",
        lower_exact.expression,
        state_var.expression,
        quoted(&variable.name),
        lower_exact.proof,
        state_var.proof
    );
    let preservation = format!(
        "fun state lower invariant member => everyMember (fun candidate : Invariant => InvariantHolds {model_name}.asModel candidate state) invariant {model_name}.invariants ({}) member",
        every_term(&[format!("({invariant_exact}).derives")])
    );

    Ok(format!(
        "\nnamespace {GENERATED_NAMESPACE}\n\nopen Trust.Temporal.FiniteModel\n\ndef AppliedClaim : Prop :=\n  ScalarModel.safetyClaim {model_name}\n\ntheorem AppliedProof : AppliedClaim :=\n  safetyClaimOfStrengthening {model_name}.asModel\n    ({strengthening})\n    ({initiation})\n    ({consecution})\n    ({preservation})\n\nend {GENERATED_NAMESPACE}\n"
    ))
}

fn unbounded_tuple_generated_suffix(
    model: &CleanScalarModel,
    model_name: &str,
    witness: &tla_check::explicit_fixpoint_cert::UnboundedInvariantCert,
) -> Result<String, CleanScalarModelError> {
    let pairs = &witness.pairs;
    if witness.relational.is_some()
        || pairs.len() < 2
        || model.variables.len() != pairs.len()
        || model.actions.len() != 1
        || model.invariants.len() != model.variables.len()
        || witness.bound != 0
        || witness.init != pairs[0].0
        || witness.delta != pairs[0].1
    {
        return Err(CleanScalarModelError::Definition(
            "tuple unbounded proof requires the exact TY nonnegative affine family".to_owned(),
        ));
    }
    for (variable, (init, _)) in model.variables.iter().zip(pairs) {
        let clean_init = u64::try_from(variable.init).map_err(|_| {
            CleanScalarModelError::Definition(format!(
                "unbounded affine initializer for `{}` is outside Clean Nat",
                variable.name
            ))
        })?;
        if clean_init != *init {
            return Err(CleanScalarModelError::Definition(format!(
                "TY tuple initializer for `{}` differs from the exact Clean model",
                variable.name
            )));
        }
    }

    let action = &model.actions[0];
    if action.guard.is_some() || action.updates.len() != model.variables.len() {
        return Err(CleanScalarModelError::Definition(
            "tuple unbounded affine action must be unguarded and update every scalar once"
                .to_owned(),
        ));
    }
    let initiation_coordinates = model
        .variables
        .iter()
        .enumerate()
        .zip(pairs)
        .map(|((index, variable), (init, _))| {
            format!(
                "scalarLowerBoundOfInitial {model_name}.asModel state ({}) {} {init} 0 ({}) rfl rfl (by decide) initial",
                render_state_var(model, index),
                quoted(&variable.name),
                member_at(index)
            )
        })
        .collect::<Vec<_>>();
    let initiation = format!("fun state initial => {}", every_term(&initiation_coordinates));

    let closure_coordinates = model
        .variables
        .iter()
        .enumerate()
        .zip(pairs)
        .map(|((index, variable), (_, delta))| {
            let coordinate = unbounded_updated_coordinate(
                model, model_name, action, index, *delta, "before", "after", "holds",
            )?;
            let lower = every_coordinate_at("lower", index);
            Ok(format!(
                "Eq.mpr (congrArg (fun value : Nat => Nat.le 0 value) ({coordinate})) (Nat.le_trans 0 (before.scalar {}) (before.scalar {} + {delta}) ({lower}) (Nat.le_add_right (before.scalar {}) {delta}))",
                quoted(&variable.name),
                quoted(&variable.name),
                quoted(&variable.name)
            ))
        })
        .collect::<Result<Vec<_>, CleanScalarModelError>>()?;
    let action_handler = format!("fun holds => {}", every_term(&closure_coordinates));
    let strengthening = format!(
        "fun state : State => Every (fun entry : StateVar => Nat.le 0 (state.scalar entry.name)) {model_name}.variables"
    );
    let consecution = format!(
        "fun before after lower next => Exists.elim next (fun action facts => everyMember (fun candidate : Action => ActionHolds {model_name}.asModel candidate before after → Every (fun entry : StateVar => Nat.le 0 (after.scalar entry.name)) {model_name}.variables) action {model_name}.actions ({}) facts.1 facts.2)",
        every_term(&[action_handler])
    );

    let zero_row = vec![0; model.variables.len()];
    let mut covered = vec![false; model.variables.len()];
    let invariant_handlers = model
        .invariants
        .iter()
        .map(|invariant| {
            let (lower_expression, name) = match &invariant.value {
                CleanScalarExpr::Le(lower, upper)
                    if is_ground_affine_expression(lower) =>
                {
                    let CleanScalarExpr::Var(name) = upper.as_ref() else {
                        return Err(CleanScalarModelError::Definition(
                            "tuple safety must compare a ground zero lower bound to a scalar"
                                .to_owned(),
                        ));
                    };
                    (lower.as_ref(), name)
                }
                _ => {
                    return Err(CleanScalarModelError::Definition(
                        "tuple safety must contain one exact lower-bound invariant per scalar"
                            .to_owned(),
                    ));
                }
            };
            let index = model
                .variables
                .iter()
                .position(|variable| variable.name == *name)
                .ok_or_else(|| {
                    CleanScalarModelError::Definition(format!(
                        "tuple safety names undeclared scalar `{name}`"
                    ))
                })?;
            if std::mem::replace(&mut covered[index], true) {
                return Err(CleanScalarModelError::Definition(format!(
                    "tuple safety repeats scalar `{name}`"
                )));
            }
            let lower_exact = exact_expression(
                model,
                model_name,
                "state",
                &zero_row,
                "unusedGroundRow",
                lower_expression,
            )?;
            let lower = biguint_to_u64(
                lower_exact.value.as_nat("tuple safety lower bound")?,
                "tuple safety lower bound",
            )?;
            if lower != 0 {
                return Err(CleanScalarModelError::Definition(
                    "TY tuple nonnegative witness differs from the exact Clean safety bound"
                        .to_owned(),
                ));
            }
            let state_var = symbolic_var_exact(model, model_name, "state", name)?;
            let lower_proof = every_coordinate_at("lower", index);
            Ok(format!(
                "(exactScalarLeTrue {model_name}.asModel state ({}) ({}) 0 (state.scalar {}) ({}) ({}) ({lower_proof})).derives",
                lower_exact.expression,
                state_var.expression,
                quoted(name),
                lower_exact.proof,
                state_var.proof
            ))
        })
        .collect::<Result<Vec<_>, CleanScalarModelError>>()?;
    if covered.iter().any(|covered| !covered) {
        return Err(CleanScalarModelError::Definition(
            "tuple safety omits a scalar from TY's nonnegative witness".to_owned(),
        ));
    }
    let preservation = format!(
        "fun state lower invariant member => everyMember (fun candidate : Invariant => InvariantHolds {model_name}.asModel candidate state) invariant {model_name}.invariants ({}) member",
        every_term(&invariant_handlers)
    );

    Ok(format!(
        "\nnamespace {GENERATED_NAMESPACE}\n\nopen Trust.Temporal.FiniteModel\n\ndef AppliedClaim : Prop :=\n  ScalarModel.safetyClaim {model_name}\n\ntheorem AppliedProof : AppliedClaim :=\n  safetyClaimOfStrengthening {model_name}.asModel\n    ({strengthening})\n    ({initiation})\n    ({consecution})\n    ({preservation})\n\nend {GENERATED_NAMESPACE}\n"
    ))
}

fn unbounded_relational_generated_suffix(
    model: &CleanScalarModel,
    model_name: &str,
    witness: &tla_check::explicit_fixpoint_cert::UnboundedInvariantCert,
    init: u64,
    delta: u64,
) -> Result<String, CleanScalarModelError> {
    if model.variables.len() != 2
        || model.actions.len() != 1
        || model.invariants.len() != 1
        || !witness.pairs.is_empty()
        || witness.bound != 0
        || witness.init != init
        || witness.delta != delta
        || witness.relational != Some((init, delta))
    {
        return Err(CleanScalarModelError::Definition(
            "relational unbounded proof requires the exact TY two-scalar lockstep family"
                .to_owned(),
        ));
    }
    for variable in &model.variables {
        if u64::try_from(variable.init).ok() != Some(init) {
            return Err(CleanScalarModelError::Definition(format!(
                "relational initializer for `{}` differs from TY's shared value",
                variable.name
            )));
        }
    }
    let action = &model.actions[0];
    if action.guard.is_some() || action.updates.len() != 2 {
        return Err(CleanScalarModelError::Definition(
            "relational lockstep action must be unguarded and update both scalars once".to_owned(),
        ));
    }
    let left = &model.variables[0];
    let right = &model.variables[1];
    let left_entry = render_state_var(model, 0);
    let right_entry = render_state_var(model, 1);
    let left_initial = format!(
        "scalarCoordinateOfInitial {model_name}.asModel state ({left_entry}) {} {init} ({}) rfl rfl initial",
        quoted(&left.name),
        member_at(0)
    );
    let right_initial = format!(
        "scalarCoordinateOfInitial {model_name}.asModel state ({right_entry}) {} {init} ({}) rfl rfl initial",
        quoted(&right.name),
        member_at(1)
    );
    let initiation =
        format!("fun state initial => Eq.trans ({left_initial}) (Eq.symm ({right_initial}))");
    let left_coordinate = unbounded_updated_coordinate(
        model, model_name, action, 0, delta, "before", "after", "holds",
    )?;
    let right_coordinate = unbounded_updated_coordinate(
        model, model_name, action, 1, delta, "before", "after", "holds",
    )?;
    let action_handler = format!(
        "fun holds => Eq.trans ({left_coordinate}) (Eq.trans (congrArg (fun value : Nat => Nat.add value {delta}) equal) (Eq.symm ({right_coordinate})))"
    );
    let strengthening = format!(
        "fun state : State => Eq Nat (state.scalar {}) (state.scalar {})",
        quoted(&left.name),
        quoted(&right.name)
    );
    let consecution = format!(
        "fun before after equal next => Exists.elim next (fun action facts => everyMember (fun candidate : Action => ActionHolds {model_name}.asModel candidate before after → Eq Nat (after.scalar {}) (after.scalar {})) action {model_name}.actions ({}) facts.1 facts.2)",
        quoted(&left.name),
        quoted(&right.name),
        every_term(&[action_handler])
    );

    let invariant = &model.invariants[0];
    let (invariant_left, invariant_right, same) = match &invariant.value {
        CleanScalarExpr::Eq(invariant_left, invariant_right) => {
            let (CleanScalarExpr::Var(left_name), CleanScalarExpr::Var(right_name)) =
                (invariant_left.as_ref(), invariant_right.as_ref())
            else {
                return Err(CleanScalarModelError::Definition(
                    "relational safety must be an equality between the two scalars".to_owned(),
                ));
            };
            if left_name == &left.name && right_name == &right.name {
                (left_name, right_name, "equal".to_owned())
            } else if left_name == &right.name && right_name == &left.name {
                (left_name, right_name, "Eq.symm equal".to_owned())
            } else {
                return Err(CleanScalarModelError::Definition(
                    "relational safety differs from TY's exact scalar pair".to_owned(),
                ));
            }
        }
        _ => {
            return Err(CleanScalarModelError::Definition(
                "relational safety must be an equality between the two scalars".to_owned(),
            ));
        }
    };
    let left_exact = symbolic_var_exact(model, model_name, "state", invariant_left)?;
    let right_exact = symbolic_var_exact(model, model_name, "state", invariant_right)?;
    let invariant_exact = format!(
        "exactScalarEqTrue {model_name}.asModel state ({}) ({}) (state.scalar {}) (state.scalar {}) ({}) ({}) ({same})",
        left_exact.expression,
        right_exact.expression,
        quoted(invariant_left),
        quoted(invariant_right),
        left_exact.proof,
        right_exact.proof
    );
    let preservation = format!(
        "fun state equal invariant member => everyMember (fun candidate : Invariant => InvariantHolds {model_name}.asModel candidate state) invariant {model_name}.invariants ({}) member",
        every_term(&[format!("({invariant_exact}).derives")])
    );

    Ok(format!(
        "\nnamespace {GENERATED_NAMESPACE}\n\nopen Trust.Temporal.FiniteModel\n\ndef AppliedClaim : Prop :=\n  ScalarModel.safetyClaim {model_name}\n\ntheorem AppliedProof : AppliedClaim :=\n  safetyClaimOfStrengthening {model_name}.asModel\n    ({strengthening})\n    ({initiation})\n    ({consecution})\n    ({preservation})\n\nend {GENERATED_NAMESPACE}\n"
    ))
}

fn automatic_family_and_suffix(
    certificate: &CleanScalarModelCertificate,
    model: &CleanScalarModel,
    model_name: &str,
) -> Result<(CleanAutomaticScalarProofFamily, Vec<Vec<u64>>, String), CleanScalarModelError> {
    let parsed =
        tla_check::cert::SafetyCertificate::from_json(&certificate.safety_certificate_json)
            .map_err(CleanScalarModelError::ArtifactMismatch)?;
    let fixpoint = parsed.explicit_fixpoint.as_ref().ok_or_else(|| {
        CleanScalarModelError::Definition(
            "automatic scalar proof requires TY explicit-fixpoint evidence".to_owned(),
        )
    })?;
    if let Some(witness) = &fixpoint.unbounded_invariant {
        if let Some((init, delta)) = witness.relational {
            let suffix =
                unbounded_relational_generated_suffix(model, model_name, witness, init, delta)?;
            return Ok((
                CleanAutomaticScalarProofFamily::UnboundedRelational { init, delta },
                Vec::new(),
                suffix,
            ));
        }
        if witness.pairs.len() == 1 {
            let suffix = unbounded_generated_suffix(model, model_name, witness)?;
            return Ok((
                CleanAutomaticScalarProofFamily::UnboundedAffine {
                    init: witness.init,
                    delta: witness.delta,
                    bound: witness.bound,
                },
                Vec::new(),
                suffix,
            ));
        }
        if witness.pairs.len() >= 2 {
            let suffix = unbounded_tuple_generated_suffix(model, model_name, witness)?;
            return Ok((
                CleanAutomaticScalarProofFamily::UnboundedAffineTuple {
                    pairs: witness.pairs.clone(),
                },
                Vec::new(),
                suffix,
            ));
        }
        return Err(CleanScalarModelError::Definition(
            "TY unbounded witness names no supported exact family".to_owned(),
        ));
    }
    let rows = finite_rows(certificate, model.variables.len())?;
    let suffix = finite_generated_suffix(model, model_name, &rows)?;
    Ok((CleanAutomaticScalarProofFamily::FiniteRows, rows, suffix))
}

fn finite_rows(
    certificate: &CleanScalarModelCertificate,
    variable_count: usize,
) -> Result<Vec<Vec<u64>>, CleanScalarModelError> {
    let parsed =
        tla_check::cert::SafetyCertificate::from_json(&certificate.safety_certificate_json)
            .map_err(CleanScalarModelError::ArtifactMismatch)?;
    let fixpoint = parsed.explicit_fixpoint.ok_or_else(|| {
        CleanScalarModelError::Definition(
            "automatic finite proof requires TY explicit-fixpoint evidence".to_owned(),
        )
    })?;
    if fixpoint.unbounded_invariant.is_some() {
        return Err(CleanScalarModelError::Definition(
            "unbounded affine evidence must use the parametric proof family".to_owned(),
        ));
    }
    if fixpoint.sorts.len() != variable_count
        || fixpoint
            .sorts
            .iter()
            .any(|sort| !matches!(sort, tla_check::explicit_fixpoint_cert::ColSort::Int))
    {
        return Err(CleanScalarModelError::Definition(
            "automatic scalar proof requires one nonnegative Int column per scalar declaration"
                .to_owned(),
        ));
    }
    Ok(fixpoint.reachable)
}

fn bind_scalar_and_proof(
    scalar: &CleanScalarModelCertificate,
    proof: &CleanAppliedModelProof,
) -> Result<(), CleanScalarModelError> {
    if scalar.model.model_definition != proof.binding.model_definition
        || scalar.model.type_expr != proof.binding.model_type
        || scalar.model.value_expr != proof.binding.model_value
    {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "automatic rows and Clean proof name different model artifacts".to_owned(),
        ));
    }
    Ok(())
}

/// Certify a supported scalar model and automatically synthesize the exact Clean
/// safety inhabitant required to retire the legacy scalar macro use.
pub fn certify_automatic_clean_scalar_model(
    clean_source: &str,
    model_definition: &str,
) -> Result<CleanAutomaticScalarProof, CleanScalarModelError> {
    let scalar = certify_clean_scalar_model_with_ty(clean_source, model_definition)?;
    let decoded =
        crate::clean_model_lane::recheck_clean_scalar_model_artifact(&scalar.model, clean_source)?;
    let (family, rows, generated_suffix) =
        automatic_family_and_suffix(&scalar, &decoded, model_definition)?;
    let generated_source = format!("{clean_source}{generated_suffix}");
    let applied_proof = prove_clean_scalar_model_safety_claim(
        &generated_source,
        model_definition,
        GENERATED_CLAIM,
        GENERATED_PROOF,
    )?;
    bind_scalar_and_proof(&scalar, &applied_proof)?;
    Ok(CleanAutomaticScalarProof {
        schema: CLEAN_AUTOMATIC_SCALAR_PROOF_SCHEMA_V1.to_owned(),
        scalar,
        family,
        rows,
        generated_suffix,
        applied_proof,
    })
}

/// Freshly replay TY, regenerate the proof source, and recheck the exact Clean
/// inhabitant.  Any row/model/action/invariant/proof splice changes at least
/// one byte compared below or fails a fresh kernel judgment.
pub fn recheck_automatic_clean_scalar_model(
    certificate: &CleanAutomaticScalarProof,
    expected_clean_source: &str,
) -> Result<(), CleanScalarModelError> {
    if certificate.schema != CLEAN_AUTOMATIC_SCALAR_PROOF_SCHEMA_V1 {
        return Err(CleanScalarModelError::ArtifactMismatch(format!(
            "unsupported automatic scalar proof schema `{}`",
            certificate.schema
        )));
    }
    if certificate.scalar.model.clean_source != expected_clean_source {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "authored Clean source changed".to_owned(),
        ));
    }
    let stored_generated_source =
        format!("{expected_clean_source}{}", certificate.generated_suffix);
    if certificate.applied_proof.binding.clean_source != stored_generated_source {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "applied proof is not bound to the stored generated source".to_owned(),
        ));
    }
    bind_scalar_and_proof(&certificate.scalar, &certificate.applied_proof)?;
    if certificate.applied_proof.canonical_inhabitant != certificate.applied_proof.proof_value
        || certificate.applied_proof.canonical_inhabitant_type
            != certificate.applied_proof.binding.canonical_claim
    {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "automatic proof inhabitant fields are internally spliced".to_owned(),
        ));
    }
    recheck_clean_scalar_model_with_ty(&certificate.scalar, expected_clean_source)?;
    let decoded = crate::clean_model_lane::recheck_clean_scalar_model_artifact(
        &certificate.scalar.model,
        expected_clean_source,
    )?;
    let (family, rows, suffix) = automatic_family_and_suffix(
        &certificate.scalar,
        &decoded,
        &certificate.scalar.model.model_definition,
    )?;
    if family != certificate.family {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "automatic proof family differs from freshly replayed TY evidence".to_owned(),
        ));
    }
    if rows != certificate.rows {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "quoted rows differ from freshly replayed TY fixpoint".to_owned(),
        ));
    }
    if suffix != certificate.generated_suffix {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "automatic Clean proof source differs after deterministic regeneration".to_owned(),
        ));
    }
    let generated_source = format!("{expected_clean_source}{suffix}");
    recheck_clean_scalar_model_safety_claim_proof(&certificate.applied_proof, &generated_source)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SOURCE: &str = include_str!("../examples/clean_scalar_complete.lean");
    const LOCKSTEP_SOURCE: &str = include_str!("../examples/clean_scalar_lockstep.lean");
    const NONINDUCTIVE_SOURCE: &str = r#"
namespace NoninductiveExample

open Trust.Temporal.FiniteModel

def X : ScalarExpr := ScalarExpr.var "x"
def Zero : ScalarExpr := ScalarExpr.int 0
def Two : ScalarExpr := ScalarExpr.int 2
def One : ScalarExpr := ScalarExpr.int 1
def Buggy : ScalarExpr := ScalarExpr.constRef "Buggy"

def Model : ScalarModel :=
  ScalarModel.mk "NoninductiveReachableSafety"
    [Constant.mk "Buggy" 0]
    [StateVar.mk "x" 0]
    [Action.mk "UnreachableAdvance"
       (Guard.when (ScalarExpr.gt X Zero))
       [Update.mk "x" (ScalarExpr.add X One)]]
    [Invariant.mk "SafeReachable" (ScalarExpr.le X Two),
     Invariant.mk "DialOff" (ScalarExpr.eq Buggy Zero)]

end NoninductiveExample
"#;
    const UNBOUNDED_SOURCE: &str = r#"
namespace UnboundedExample

open Trust.Temporal.FiniteModel

def X : ScalarExpr := ScalarExpr.var "x"
def Three : ScalarExpr := ScalarExpr.int 3
def Buggy : ScalarExpr := ScalarExpr.constRef "Buggy"

def Model : ScalarModel :=
  ScalarModel.mk "UnboundedAffine"
    [Constant.mk "Buggy" 0]
    [StateVar.mk "x" 0]
    [Action.mk "Advance" Guard.always
       [Update.mk "x" (ScalarExpr.add X Three)]]
    [Invariant.mk "Safe" (ScalarExpr.le Buggy X)]

end UnboundedExample
"#;
    const UNBOUNDED_TUPLE_SOURCE: &str = r#"
namespace UnboundedTupleExample

open Trust.Temporal.FiniteModel

def X : ScalarExpr := ScalarExpr.var "x"
def Y : ScalarExpr := ScalarExpr.var "y"
def One : ScalarExpr := ScalarExpr.int 1
def Two : ScalarExpr := ScalarExpr.int 2
def Buggy : ScalarExpr := ScalarExpr.constRef "Buggy"

def Model : ScalarModel :=
  ScalarModel.mk "UnboundedAffineTuple"
    [Constant.mk "Buggy" 0]
    [StateVar.mk "x" 0, StateVar.mk "y" 2]
    [Action.mk "Advance" Guard.always
       [Update.mk "x" (ScalarExpr.add X One),
        Update.mk "y" (ScalarExpr.add Two Y)]]
    [Invariant.mk "NonnegativeX" (ScalarExpr.le Buggy X),
     Invariant.mk "NonnegativeY" (ScalarExpr.le Buggy Y)]

end UnboundedTupleExample
"#;
    const UNBOUNDED_RELATIONAL_SOURCE: &str = r#"
namespace UnboundedRelationalExample

open Trust.Temporal.FiniteModel

def X : ScalarExpr := ScalarExpr.var "x"
def Y : ScalarExpr := ScalarExpr.var "y"
def Zero : ScalarExpr := ScalarExpr.int 0
def Buggy : ScalarExpr := ScalarExpr.constRef "Buggy"

def Model : ScalarModel :=
  ScalarModel.mk "UnboundedRelational"
    [Constant.mk "Buggy" 0]
    [StateVar.mk "x" 0, StateVar.mk "y" 0]
    [Action.mk "Advance" Guard.always
       [Update.mk "x" (ScalarExpr.add X Zero),
        Update.mk "y" (ScalarExpr.add Y Buggy)]]
    [Invariant.mk "Lockstep" (ScalarExpr.eq X Y)]

end UnboundedRelationalExample
"#;

    fn tamper_ty_unbounded_witness(certificate: &mut CleanAutomaticScalarProof) {
        let mut safety = tla_check::cert::SafetyCertificate::from_json(
            &certificate.scalar.safety_certificate_json,
        )
        .expect("stored TY certificate parses before mutation");
        let witness = safety
            .explicit_fixpoint
            .as_mut()
            .and_then(|fixpoint| fixpoint.unbounded_invariant.as_mut())
            .expect("test fixture must carry an unbounded witness");
        witness.delta = witness.delta.wrapping_add(1);
        certificate.scalar.safety_certificate_json =
            serde_json::to_string(&safety).expect("mutated TY certificate serializes");
    }

    fn assert_cross_family_splices_fail(certificate: &CleanAutomaticScalarProof, source: &str) {
        let families = [
            CleanAutomaticScalarProofFamily::FiniteRows,
            CleanAutomaticScalarProofFamily::UnboundedAffine { init: 17, delta: 19, bound: 23 },
            CleanAutomaticScalarProofFamily::UnboundedAffineTuple {
                pairs: vec![(17, 19), (23, 29)],
            },
            CleanAutomaticScalarProofFamily::UnboundedRelational { init: 17, delta: 19 },
        ];
        for family in families {
            if family == certificate.family {
                continue;
            }
            let mut splice = certificate.clone();
            splice.family = family;
            assert!(matches!(
                recheck_automatic_clean_scalar_model(&splice, source),
                Err(CleanScalarModelError::ArtifactMismatch(_))
            ));
        }
    }

    #[test]
    fn finite_rows_automatically_inhabit_exact_applied_claim() {
        let certificate =
            certify_automatic_clean_scalar_model(SOURCE, "AuthorityExample.CompleteAuthority")
                .expect("the finite owner-grammar model must automatically prove its Clean claim");
        assert_eq!(certificate.rows, vec![vec![0], vec![1], vec![2], vec![3]]);
        recheck_automatic_clean_scalar_model(&certificate, SOURCE)
            .expect("the automatic proof must freshly replay");

        let mut wrong_row = certificate.clone();
        wrong_row.rows[0][0] = 9;
        assert!(matches!(
            recheck_automatic_clean_scalar_model(&wrong_row, SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));

        let mut tampered = certificate;
        tampered.generated_suffix.push(' ');
        assert!(matches!(
            recheck_automatic_clean_scalar_model(&tampered, SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));
    }

    #[test]
    fn finite_rows_cover_multiple_variables_actions_and_full_macro_grammar() {
        let certificate = certify_automatic_clean_scalar_model(LOCKSTEP_SOURCE, "Example.Lockstep")
            .expect("the multi-variable macro grammar fixture must automatically prove");
        assert_eq!(certificate.rows, vec![vec![0, 0], vec![1, 1], vec![2, 2]]);
        recheck_automatic_clean_scalar_model(&certificate, LOCKSTEP_SOURCE)
            .expect("the multi-variable proof must freshly replay");

        let wrong_action = LOCKSTEP_SOURCE.replacen("\"Step\"", "\"StaleStep\"", 1);
        let wrong_model = LOCKSTEP_SOURCE.replacen("\"CleanLockstep\"", "\"OtherModel\"", 1);
        let wrong_invariant = LOCKSTEP_SOURCE.replacen("\"Lockstep\"", "\"WrongInvariant\"", 1);
        for changed in [&wrong_action, &wrong_model, &wrong_invariant] {
            assert!(matches!(
                recheck_automatic_clean_scalar_model(&certificate, changed),
                Err(CleanScalarModelError::ArtifactMismatch(_))
            ));
        }

        let mut spliced = certificate.clone();
        spliced.applied_proof.binding.model_definition = "Example.UnrelatedModel".to_owned();
        assert!(matches!(
            recheck_automatic_clean_scalar_model(&spliced, LOCKSTEP_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));

        let mut proof_tamper = certificate.clone();
        proof_tamper.applied_proof.canonical_inhabitant.push(0);
        assert!(matches!(
            recheck_automatic_clean_scalar_model(&proof_tamper, LOCKSTEP_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));
    }

    #[test]
    fn reachable_strengthening_handles_safe_but_noninductive_authored_predicate() {
        let certificate = certify_automatic_clean_scalar_model(
            NONINDUCTIVE_SOURCE,
            "NoninductiveExample.Model",
        )
        .expect("reachable-set induction must not require the authored safety predicate to be inductive");
        assert_eq!(certificate.rows, vec![vec![0]]);
        recheck_automatic_clean_scalar_model(&certificate, NONINDUCTIVE_SOURCE)
            .expect("the noninductive-safety proof must freshly replay");
    }

    #[test]
    fn unbounded_affine_counter_gets_parametric_clean_proof_without_finite_cutoff() {
        let certificate =
            certify_automatic_clean_scalar_model(UNBOUNDED_SOURCE, "UnboundedExample.Model")
                .expect("the unbounded affine counter must receive a parametric Clean proof");
        assert_eq!(
            certificate.family,
            CleanAutomaticScalarProofFamily::UnboundedAffine { init: 0, delta: 3, bound: 0 }
        );
        assert!(certificate.rows.is_empty(), "unbounded proof must not invent a cutoff");
        recheck_automatic_clean_scalar_model(&certificate, UNBOUNDED_SOURCE)
            .expect("the parametric proof must freshly replay");

        let mut wrong_delta = certificate.clone();
        wrong_delta.family =
            CleanAutomaticScalarProofFamily::UnboundedAffine { init: 0, delta: 4, bound: 0 };
        assert!(matches!(
            recheck_automatic_clean_scalar_model(&wrong_delta, UNBOUNDED_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));

        let wrong_action = UNBOUNDED_SOURCE.replacen("ScalarExpr.add X Three", "X", 1);
        assert!(matches!(
            recheck_automatic_clean_scalar_model(&certificate, &wrong_action),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));

        let mut witness_tamper = certificate.clone();
        tamper_ty_unbounded_witness(&mut witness_tamper);
        assert!(recheck_automatic_clean_scalar_model(&witness_tamper, UNBOUNDED_SOURCE).is_err());
        let mut proof_tamper = certificate.clone();
        proof_tamper.applied_proof.canonical_inhabitant.push(0);
        assert!(matches!(
            recheck_automatic_clean_scalar_model(&proof_tamper, UNBOUNDED_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));
        assert_cross_family_splices_fail(&certificate, UNBOUNDED_SOURCE);
    }

    #[test]
    fn unbounded_affine_tuple_gets_exact_conjoined_clean_proof() {
        let certificate = certify_automatic_clean_scalar_model(
            UNBOUNDED_TUPLE_SOURCE,
            "UnboundedTupleExample.Model",
        )
        .expect("the unbounded tuple must receive a conjoined parametric Clean proof");
        assert_eq!(
            certificate.family,
            CleanAutomaticScalarProofFamily::UnboundedAffineTuple { pairs: vec![(0, 1), (2, 2)] }
        );
        assert!(certificate.rows.is_empty(), "unbounded proof must not invent a cutoff");
        recheck_automatic_clean_scalar_model(&certificate, UNBOUNDED_TUPLE_SOURCE)
            .expect("the tuple proof must freshly replay");

        let wrong_model =
            UNBOUNDED_TUPLE_SOURCE.replacen("\"UnboundedAffineTuple\"", "\"StaleTupleModel\"", 1);
        let wrong_action = UNBOUNDED_TUPLE_SOURCE.replacen("ScalarExpr.add Two Y", "Y", 1);
        let wrong_invariant =
            UNBOUNDED_TUPLE_SOURCE.replacen("ScalarExpr.le Buggy Y", "ScalarExpr.eq X Y", 1);
        for changed in [&wrong_model, &wrong_action, &wrong_invariant] {
            assert!(matches!(
                recheck_automatic_clean_scalar_model(&certificate, changed),
                Err(CleanScalarModelError::ArtifactMismatch(_))
            ));
        }
        let mut witness_tamper = certificate.clone();
        tamper_ty_unbounded_witness(&mut witness_tamper);
        assert!(
            recheck_automatic_clean_scalar_model(&witness_tamper, UNBOUNDED_TUPLE_SOURCE).is_err()
        );
        let mut splice = certificate.clone();
        splice.applied_proof.binding.model_definition = "Other.Model".to_owned();
        assert!(matches!(
            recheck_automatic_clean_scalar_model(&splice, UNBOUNDED_TUPLE_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));
        let mut proof_tamper = certificate.clone();
        proof_tamper.applied_proof.canonical_inhabitant.push(0);
        assert!(matches!(
            recheck_automatic_clean_scalar_model(&proof_tamper, UNBOUNDED_TUPLE_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));
        assert_cross_family_splices_fail(&certificate, UNBOUNDED_TUPLE_SOURCE);
    }

    #[test]
    fn unbounded_relational_lockstep_gets_exact_clean_proof() {
        let certificate = certify_automatic_clean_scalar_model(
            UNBOUNDED_RELATIONAL_SOURCE,
            "UnboundedRelationalExample.Model",
        )
        .expect("the relational unbounded family must receive a parametric Clean proof");
        assert_eq!(
            certificate.family,
            CleanAutomaticScalarProofFamily::UnboundedRelational { init: 0, delta: 0 }
        );
        assert!(certificate.rows.is_empty(), "unbounded proof must not invent a cutoff");
        recheck_automatic_clean_scalar_model(&certificate, UNBOUNDED_RELATIONAL_SOURCE)
            .expect("the relational proof must freshly replay");

        let wrong_model = UNBOUNDED_RELATIONAL_SOURCE.replacen(
            "\"UnboundedRelational\"",
            "\"StaleRelationalModel\"",
            1,
        );
        let wrong_action = UNBOUNDED_RELATIONAL_SOURCE.replacen("ScalarExpr.add Y Buggy", "Y", 1);
        let wrong_invariant =
            UNBOUNDED_RELATIONAL_SOURCE.replacen("ScalarExpr.eq X Y", "ScalarExpr.le X Y", 1);
        for changed in [&wrong_model, &wrong_action, &wrong_invariant] {
            assert!(matches!(
                recheck_automatic_clean_scalar_model(&certificate, changed),
                Err(CleanScalarModelError::ArtifactMismatch(_))
            ));
        }
        let mut witness_tamper = certificate.clone();
        tamper_ty_unbounded_witness(&mut witness_tamper);
        assert!(
            recheck_automatic_clean_scalar_model(&witness_tamper, UNBOUNDED_RELATIONAL_SOURCE)
                .is_err()
        );
        let mut splice = certificate.clone();
        splice.applied_proof.binding.model_definition = "Other.Model".to_owned();
        assert!(matches!(
            recheck_automatic_clean_scalar_model(&splice, UNBOUNDED_RELATIONAL_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));
        let mut proof_tamper = certificate.clone();
        proof_tamper.applied_proof.canonical_inhabitant.push(0);
        assert!(matches!(
            recheck_automatic_clean_scalar_model(&proof_tamper, UNBOUNDED_RELATIONAL_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));
        assert_cross_family_splices_fail(&certificate, UNBOUNDED_RELATIONAL_SOURCE);
    }
}
