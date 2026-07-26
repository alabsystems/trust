//! Fallible, parser-checked rendering of verification formulas as Trust source contracts.
//!
//! This is the single Formula -> source-expression boundary.  It deliberately
//! supports only the lossless subset understood by `spec_parse`; unsupported
//! solver nodes fail closed instead of leaking `Debug` output into Rust source.

use std::collections::BTreeMap;

use crate::{
    Formula, HighLevelSpecAttr, Sort, SpecBinOp, SpecExpr, SpecParseError, SpecUnaryOp,
    check_formula_sort, parse_spec_attr, parse_spec_expr_result,
};

/// A source-contract rendering or round-trip validation failure.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum SpecRenderError {
    /// Source contracts must be predicates.
    #[error("source contract has non-Boolean top-level sort {actual:?}")]
    NonBoolean { actual: Sort },
    /// A variable name cannot be represented without changing or injecting tokens.
    #[error("invalid source-contract variable name `{name}`")]
    InvalidIdentifier { name: String },
    /// One source name was assigned incompatible sorts.
    #[error("source-contract variable `{name}` has conflicting sorts {first:?} and {second:?}")]
    ConflictingVariableSort { name: String, first: Sort, second: Sort },
    /// The formula node has no lossless spelling in the Trust contract grammar.
    #[error("formula variant is not supported by the source-contract grammar")]
    UnsupportedFormula,
    /// The emitted expression did not parse as a complete contract expression.
    #[error("rendered source contract did not parse: {0}")]
    Parse(#[from] SpecParseError),
    /// Parsing the emitted expression changed its formula structure or typed variables.
    #[error("source-contract parse round-trip changed the formula")]
    RoundTripMismatch,
    /// An operator's children are not recursively well-sorted.
    #[error("ill-typed source contract: {detail}")]
    IllTyped { detail: String },
    /// A source identifier is not a parameter or a bound quantifier variable.
    #[error("source-contract variable `{name}` is not in scope")]
    UnknownVariable { name: String },
    /// `result` is only meaningful in a postcondition.
    #[error("`result` is only allowed in an ensures clause")]
    ResultOutsidePostcondition,
    /// `old(...)` is only meaningful in a postcondition.
    #[error("`old(...)` is only allowed in an ensures clause")]
    OldOutsidePostcondition,
    /// A unit-returning function has no value that `result` can denote.
    #[error("`result` is not available for a unit-returning function")]
    UnitResult,
    /// A source-level function/predicate is outside the closed contract vocabulary.
    #[error("unsupported source-contract call `{name}`")]
    UnsupportedCall { name: String },
}

/// The source clause whose scope rules apply to an external expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceContractClause {
    Requires,
    Ensures,
    Invariant,
    Decreases,
}

impl SourceContractClause {
    fn attr_name(self) -> &'static str {
        match self {
            Self::Requires => "requires",
            Self::Ensures => "ensures",
            Self::Invariant => "invariant",
            Self::Decreases => "decreases",
        }
    }
}

/// Retype variable leaves using a source/MIR type environment.
///
/// The Trust parser intentionally starts ordinary identifiers at `Sort::Int`.
/// Consumers that know the signature must call this before accepting a parsed
/// predicate, notably for `bool` parameters and the Boolean return place.
#[must_use]
pub fn retype_formula_variables(formula: Formula, sorts: &BTreeMap<String, Sort>) -> Formula {
    formula.map(&mut |node| match node {
        Formula::Var(name, old_sort) => {
            let sort = sorts.get(&name).cloned().unwrap_or(old_sort);
            Formula::Var(name, sort)
        }
        Formula::SymVar(symbol, old_sort) => {
            let sort = sorts.get(symbol.as_str()).cloned().unwrap_or(old_sort);
            Formula::SymVar(symbol, sort)
        }
        other => other,
    })
}

/// Render a Boolean formula into a complete, parser-validated Trust expression.
///
/// Variable sorts are collected from the formula and restored after parsing;
/// acceptance therefore requires an exact typed AST round trip rather than a
/// merely syntactic parse that silently changes `Bool`/bitvector variables to
/// the parser's default `Int` sort.
pub fn formula_to_spec_expr(formula: &Formula) -> Result<String, SpecRenderError> {
    let sorts = formula_variable_sorts(formula)?;
    render_and_validate(formula, &sorts)
}

/// Parse and canonicalize an externally supplied contract expression.
///
/// `sorts` should contain the source signature's parameter names and `_0`
/// return place.  The canonical expression is accepted only if reparsing it,
/// then restoring those sorts, gives the exact same typed formula.
pub fn canonicalize_spec_expr_with_sorts(
    expression: &str,
    sorts: &BTreeMap<String, Sort>,
) -> Result<String, SpecRenderError> {
    let parsed = parse_spec_expr_result(expression)?;
    let typed = retype_formula_variables(parsed, sorts);
    render_and_validate(&typed, sorts)
}

/// Parse and canonicalize a contract whose variables use the parser's default sorts.
pub fn canonicalize_spec_expr(expression: &str) -> Result<String, SpecRenderError> {
    canonicalize_spec_expr_with_sorts(expression, &BTreeMap::new())
}

/// Validate an externally supplied expression against its exact source clause
/// and function signature, while preserving the user's token spelling.
///
/// This boundary deliberately validates the high-level [`SpecExpr`] before it
/// is lowered to synthetic solver names.  Lowering `arr.len()` to `arr_len`,
/// `result` to `_0`, or `old(x)` to `old_x` first loses source scope and can
/// collide with legitimate parameters carrying those names.  The returned text
/// is therefore the trimmed original expression, not a re-rendered Formula.
pub fn validate_source_spec_expr(
    expression: &str,
    clause: SourceContractClause,
    signature_sorts: &BTreeMap<String, Sort>,
) -> Result<String, SpecRenderError> {
    validate_source_spec_expr_inner(expression, clause, signature_sorts, false)
}

/// Validate a native verifier-language clause against exact source projection
/// sorts.
///
/// Unlike [`validate_source_spec_expr`], this rejects indexing and built-in
/// collection accessors on non-array bases, and rejects ordinary fields until
/// exact source layouts are available. Native query callers must not inherit
/// the legacy integer aggregate abstraction retained by the compatibility
/// entry point.
pub fn validate_source_spec_expr_with_exact_projections(
    expression: &str,
    clause: SourceContractClause,
    signature_sorts: &BTreeMap<String, Sort>,
) -> Result<String, SpecRenderError> {
    validate_source_spec_expr_inner(expression, clause, signature_sorts, true)
}

fn validate_source_spec_expr_inner(
    expression: &str,
    clause: SourceContractClause,
    signature_sorts: &BTreeMap<String, Sort>,
    exact_projections: bool,
) -> Result<String, SpecRenderError> {
    let parsed = parse_spec_attr(clause.attr_name(), expression)?;
    let expr = match parsed {
        HighLevelSpecAttr::Requires(expr)
        | HighLevelSpecAttr::Ensures(expr)
        | HighLevelSpecAttr::Invariant(expr)
        | HighLevelSpecAttr::Decreases(expr) => expr,
        HighLevelSpecAttr::Pure | HighLevelSpecAttr::Trusted => {
            return Err(SpecRenderError::UnsupportedFormula);
        }
        #[allow(unreachable_patterns)]
        _ => return Err(SpecRenderError::UnsupportedFormula),
    };

    // `_0` is an internal return-place name, never an ordinary source binding
    // in this context.  Callers must reject a real parameter named `_0` before
    // constructing this map; otherwise the two source meanings are impossible
    // to distinguish after lowering.
    let mut variables = signature_sorts.clone();
    let return_sort = variables.remove("_0");
    let actual = check_source_expr_sort(
        &expr,
        clause,
        &return_sort,
        &mut variables,
        true,
        exact_projections,
    )?;
    let expected = if clause == SourceContractClause::Decreases { Sort::Int } else { Sort::Bool };
    if actual != expected {
        return Err(SpecRenderError::IllTyped {
            detail: format!(
                "{} clause must have sort {expected:?}, found {actual:?}",
                clause.attr_name()
            ),
        });
    }
    Ok(expression.trim().to_string())
}

fn source_expect(operator: &str, actual: Sort, expected: Sort) -> Result<(), SpecRenderError> {
    if actual == expected {
        Ok(())
    } else {
        Err(SpecRenderError::IllTyped {
            detail: format!("{operator} requires {expected:?}, found {actual:?}"),
        })
    }
}

fn source_same(operator: &str, left: Sort, right: Sort) -> Result<Sort, SpecRenderError> {
    if left == right {
        Ok(left)
    } else {
        Err(SpecRenderError::IllTyped {
            detail: format!("{operator} operands have different sorts {left:?} and {right:?}"),
        })
    }
}

fn check_source_expr_sort(
    expr: &SpecExpr,
    clause: SourceContractClause,
    return_sort: &Option<Sort>,
    variables: &mut BTreeMap<String, Sort>,
    allow_result: bool,
    exact_projections: bool,
) -> Result<Sort, SpecRenderError> {
    match expr {
        SpecExpr::BoolLit(_) => Ok(Sort::Bool),
        SpecExpr::IntLit(_) | SpecExpr::UIntLit(_) => Ok(Sort::Int),
        // An f64 literal carries its IEEE binary64 sort, matching the
        // executable formula parser's `FpConst { eb: 11, sb: 53 }` atom.
        SpecExpr::FloatLit(_) => Ok(Sort::Float { eb: 11, sb: 53 }),
        SpecExpr::Var(name) => variables
            .get(name)
            .cloned()
            .ok_or_else(|| SpecRenderError::UnknownVariable { name: name.clone() }),
        SpecExpr::Result => {
            if clause != SourceContractClause::Ensures || !allow_result {
                return Err(SpecRenderError::ResultOutsidePostcondition);
            }
            return_sort.clone().ok_or(SpecRenderError::UnitResult)
        }
        SpecExpr::Old(inner) => {
            if clause != SourceContractClause::Ensures {
                return Err(SpecRenderError::OldOutsidePostcondition);
            }
            // `old(result)` has no entry-state meaning.  Parameters and their
            // projections retain the operand's signature-derived sort.
            check_source_expr_sort(inner, clause, return_sort, variables, false, exact_projections)
        }
        SpecExpr::UnaryOp { op, expr } => {
            let actual = check_source_expr_sort(
                expr,
                clause,
                return_sort,
                variables,
                allow_result,
                exact_projections,
            )?;
            match op {
                SpecUnaryOp::Not => {
                    source_expect("logical not", actual, Sort::Bool)?;
                    Ok(Sort::Bool)
                }
                SpecUnaryOp::Neg => {
                    source_expect("arithmetic negation", actual, Sort::Int)?;
                    Ok(Sort::Int)
                }
                #[allow(unreachable_patterns)]
                _ => Err(SpecRenderError::UnsupportedFormula),
            }
        }
        SpecExpr::BinOp { lhs, op, rhs } => {
            let left = check_source_expr_sort(
                lhs,
                clause,
                return_sort,
                variables,
                allow_result,
                exact_projections,
            )?;
            let right = check_source_expr_sort(
                rhs,
                clause,
                return_sort,
                variables,
                allow_result,
                exact_projections,
            )?;
            match op {
                SpecBinOp::Add
                | SpecBinOp::Sub
                | SpecBinOp::Mul
                | SpecBinOp::Div
                | SpecBinOp::Mod => {
                    // Arithmetic is defined over ONE numeric sort at a time:
                    // both operands Int (the established abstraction), or both
                    // the SAME IEEE float sort — what a float difference bound
                    // (`(near) - (far) <= (-1.0e-6)`) needs. `%` has no float
                    // contract meaning and stays integer-only; mixed operands
                    // never validate (fail-closed).
                    let operand = source_same("arithmetic", left, right)?;
                    match operand {
                        Sort::Int => Ok(Sort::Int),
                        Sort::Float { .. } if *op != SpecBinOp::Mod => Ok(operand),
                        other => Err(SpecRenderError::IllTyped {
                            detail: format!(
                                "arithmetic operator is not defined for operand sort {other:?}"
                            ),
                        }),
                    }
                }
                SpecBinOp::Eq | SpecBinOp::Ne => {
                    source_same("equality", left, right)?;
                    Ok(Sort::Bool)
                }
                SpecBinOp::Lt | SpecBinOp::Le | SpecBinOp::Gt | SpecBinOp::Ge => {
                    // Ordering, like arithmetic, needs one numeric sort on both
                    // sides: Int, or the same IEEE float sort (the float
                    // magnitude bounds `(self.0) <= (1.0e30)`). Bool ordering
                    // stays a hard type error.
                    let operand = source_same("ordering comparison", left, right)?;
                    if matches!(operand, Sort::Int | Sort::Float { .. }) {
                        Ok(Sort::Bool)
                    } else {
                        Err(SpecRenderError::IllTyped {
                            detail: format!(
                                "ordering comparison is not defined for operand sort {operand:?}"
                            ),
                        })
                    }
                }
                SpecBinOp::And | SpecBinOp::Or => {
                    source_expect("Boolean connective", left, Sort::Bool)?;
                    source_expect("Boolean connective", right, Sort::Bool)?;
                    Ok(Sort::Bool)
                }
                #[allow(unreachable_patterns)]
                _ => Err(SpecRenderError::UnsupportedFormula),
            }
        }
        SpecExpr::Implies { lhs, rhs } => {
            let left = check_source_expr_sort(
                lhs,
                clause,
                return_sort,
                variables,
                allow_result,
                exact_projections,
            )?;
            let right = check_source_expr_sort(
                rhs,
                clause,
                return_sort,
                variables,
                allow_result,
                exact_projections,
            )?;
            source_expect("implication", left, Sort::Bool)?;
            source_expect("implication", right, Sort::Bool)?;
            Ok(Sort::Bool)
        }
        SpecExpr::Field { base, field } => {
            // A pure projection chain over a named base (`self.0`,
            // `self.0[3].1`) is looked up under its exact signature-environment
            // spelling. The environment, not the field token alone, is the
            // authority for the projected sort.
            if let Some(sort) = projected_chain_sort(expr, variables) {
                return Ok(sort);
            }
            // Validate the base's scope even though v1 lacks structural source
            // type metadata for arbitrary fields. Exact native admission
            // rejects ordinary fields until signatures carry layouts;
            // compatibility callers retain the established integer abstraction.
            let base_sort = check_source_expr_sort(
                base,
                clause,
                return_sort,
                variables,
                allow_result,
                exact_projections,
            )?;
            if exact_projections {
                Err(SpecRenderError::IllTyped {
                    detail: format!(
                        "ordinary field projection `{field}` is unsupported without exact field layout for base {base_sort:?}"
                    ),
                })
            } else {
                Ok(Sort::Int)
            }
        }
        SpecExpr::MethodCall { base, method } => {
            // Preserve the pre-split source-admission policy: collection
            // accessors have exact Array typing, while other modeled methods
            // remain compatibility-only until source aggregate layouts are
            // represented here.
            let base_sort = check_source_expr_sort(
                base,
                clause,
                return_sort,
                variables,
                allow_result,
                exact_projections,
            )?;
            match method.as_str() {
                "len" | "is_empty"
                    if exact_projections && !matches!(base_sort, Sort::Array(..)) =>
                {
                    Err(SpecRenderError::IllTyped {
                        detail: format!(
                            "collection accessor `{method}` requires an Array base, found {base_sort:?}"
                        ),
                    })
                }
                "len" => Ok(Sort::Int),
                "is_empty" => Ok(Sort::Bool),
                _ if exact_projections => Err(SpecRenderError::IllTyped {
                    detail: format!(
                        "method call `{method}()` is unsupported without exact source type semantics for base {base_sort:?}"
                    ),
                }),
                _ => Ok(Sort::Int),
            }
        }
        SpecExpr::Index { base, index } => {
            // Literal indexing inside a pure projected chain can carry an exact
            // signature-environment sort. Computed indexing cannot form such a
            // name and proceeds through the structural Array rules below.
            if let Some(sort) = projected_chain_sort(expr, variables) {
                return Ok(sort);
            }
            let base = check_source_expr_sort(
                base,
                clause,
                return_sort,
                variables,
                allow_result,
                exact_projections,
            )?;
            let index = check_source_expr_sort(
                index,
                clause,
                return_sort,
                variables,
                allow_result,
                exact_projections,
            )?;
            if let Sort::Array(index_sort, element_sort) = base {
                source_expect("index", index, *index_sort)?;
                Ok(*element_sort)
            } else if exact_projections {
                Err(SpecRenderError::IllTyped {
                    detail: format!("index requires an Array base, found {base:?}"),
                })
            } else {
                // Compatibility callers predating structural signature sorts
                // represent aggregate bases as Int. Retain that conservative
                // legacy result, while exact native-loop Array environments
                // preserve their actual element sort above.
                source_expect("index", index, Sort::Int)?;
                Ok(Sort::Int)
            }
        }
        SpecExpr::FnCall { name, args } => {
            let Some(expected) = crate::pred_arg_sorts(name) else {
                return Err(SpecRenderError::UnsupportedCall { name: name.clone() });
            };
            if expected.len() != args.len() || !crate::is_valid_pred(name, args.len()) {
                return Err(SpecRenderError::UnsupportedCall { name: name.clone() });
            }
            for (argument, expected) in args.iter().zip(expected) {
                let actual = check_source_expr_sort(
                    argument,
                    clause,
                    return_sort,
                    variables,
                    allow_result,
                    exact_projections,
                )?;
                source_expect("predicate argument", actual, expected.clone())?;
            }
            Ok(Sort::Bool)
        }
        SpecExpr::Forall { var, ty, body } | SpecExpr::Exists { var, ty, body } => {
            let bound_sort = match ty.as_str() {
                "int" | "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32"
                | "u64" | "u128" | "usize" => Sort::Int,
                "bool" => Sort::Bool,
                _ => return Err(SpecRenderError::UnsupportedFormula),
            };
            let previous = variables.insert(var.clone(), bound_sort);
            let body_sort = check_source_expr_sort(
                body,
                clause,
                return_sort,
                variables,
                allow_result,
                exact_projections,
            );
            if let Some(previous) = previous {
                variables.insert(var.clone(), previous);
            } else {
                variables.remove(var);
            }
            source_expect("quantifier body", body_sort?, Sort::Bool)?;
            Ok(Sort::Bool)
        }
        #[allow(unreachable_patterns)]
        _ => Err(SpecRenderError::UnsupportedFormula),
    }
}

/// Look up a pure projection chain's signature-environment sort under its
/// canonical projected spelling.  `None` (no chain name, or no binding) sends
/// the expression to the structural fallback rules (fail-closed).
fn projected_chain_sort(expr: &SpecExpr, variables: &BTreeMap<String, Sort>) -> Option<Sort> {
    variables.get(&projected_chain_name(expr)?).cloned()
}

/// The canonical projected-place spelling of a pure projection chain over a
/// named base: `self` + `.0` + `[3]` + `.1` spells `self.0[3].1`, byte-for-byte
/// the var name the executable formula parser (`spec_parse`) produces for the
/// same source tokens.  Only a `Var` base, named/numeric fields, and LITERAL
/// non-negative array indices form a stable place spelling; any other shape
/// (computed index, `old(..)`/`result` in the chain) returns `None`.
fn projected_chain_name(expr: &SpecExpr) -> Option<String> {
    match expr {
        SpecExpr::Var(name) => Some(name.clone()),
        SpecExpr::Field { base, field } => Some(format!("{}.{field}", projected_chain_name(base)?)),
        SpecExpr::Index { base, index } => match index.as_ref() {
            SpecExpr::IntLit(value) if *value >= 0 => {
                Some(format!("{}[{value}]", projected_chain_name(base)?))
            }
            _ => None,
        },
        _ => None,
    }
}

fn render_and_validate(
    formula: &Formula,
    supplied_sorts: &BTreeMap<String, Sort>,
) -> Result<String, SpecRenderError> {
    let actual = check_formula_sort(formula)
        .map_err(|error| SpecRenderError::IllTyped { detail: error.to_string() })?;
    if actual != Sort::Bool {
        return Err(SpecRenderError::NonBoolean { actual });
    }

    let rendered = render_inner(formula)?;
    let reparsed = parse_spec_expr_result(&rendered)?;

    // Formula-owned sorts take precedence, while supplied signature sorts fill
    // in parser-created names.  Conflicts are rejected by collection above.
    let mut sorts = supplied_sorts.clone();
    for (name, sort) in formula_variable_sorts(formula)? {
        if let Some(existing) = sorts.get(&name)
            && existing != &sort
        {
            return Err(SpecRenderError::ConflictingVariableSort {
                name,
                first: existing.clone(),
                second: sort,
            });
        }
        sorts.insert(name, sort);
    }
    let reparsed = retype_formula_variables(reparsed, &sorts);
    if reparsed != *formula {
        return Err(SpecRenderError::RoundTripMismatch);
    }
    Ok(rendered)
}

fn formula_variable_sorts(formula: &Formula) -> Result<BTreeMap<String, Sort>, SpecRenderError> {
    let mut sorts: BTreeMap<String, Sort> = BTreeMap::new();
    let mut conflict = None;
    formula.visit(&mut |node| {
        let (name, sort) = match node {
            Formula::Var(name, sort) => (name.clone(), sort.clone()),
            Formula::SymVar(symbol, sort) => (symbol.as_str().to_string(), sort.clone()),
            _ => return,
        };
        if let Some(first) = sorts.get(&name)
            && first != &sort
        {
            conflict = Some(SpecRenderError::ConflictingVariableSort {
                name,
                first: first.clone(),
                second: sort,
            });
        } else {
            sorts.insert(name, sort);
        }
    });
    conflict.map_or(Ok(sorts), Err)
}

fn render_inner(formula: &Formula) -> Result<String, SpecRenderError> {
    fn binary(op: &str, lhs: &Formula, rhs: &Formula) -> Result<String, SpecRenderError> {
        Ok(format!("({} {op} {})", render_inner(lhs)?, render_inner(rhs)?))
    }

    match formula {
        Formula::Bool(value) => Ok(value.to_string()),
        Formula::Int(value) => Ok(value.to_string()),
        // The parser has no UInt/BitVec literal node, so accepting these would
        // necessarily fail the exact structural round trip.
        Formula::UInt(_) | Formula::BitVec { .. } => Err(SpecRenderError::UnsupportedFormula),
        Formula::Var(name, _) => render_variable(name),
        Formula::SymVar(symbol, _) => render_variable(symbol.as_str()),
        Formula::Not(inner) => Ok(format!("!({})", render_inner(inner)?)),
        Formula::And(items) => match items.as_slice() {
            [] => Ok("true".to_string()),
            [only] => render_inner(only),
            _ => {
                let parts = items.iter().map(render_inner).collect::<Result<Vec<_>, _>>()?;
                Ok(format!("({})", parts.join(" && ")))
            }
        },
        Formula::Or(items) => match items.as_slice() {
            [] => Ok("false".to_string()),
            [only] => render_inner(only),
            _ => {
                let parts = items.iter().map(render_inner).collect::<Result<Vec<_>, _>>()?;
                Ok(format!("({})", parts.join(" || ")))
            }
        },
        Formula::Implies(lhs, rhs) => binary("=>", lhs, rhs),
        Formula::Eq(lhs, rhs) => binary("==", lhs, rhs),
        Formula::Lt(lhs, rhs) => binary("<", lhs, rhs),
        Formula::Le(lhs, rhs) => binary("<=", lhs, rhs),
        Formula::Gt(lhs, rhs) => binary(">", lhs, rhs),
        Formula::Ge(lhs, rhs) => binary(">=", lhs, rhs),
        Formula::Add(lhs, rhs) => binary("+", lhs, rhs),
        Formula::Sub(lhs, rhs) => binary("-", lhs, rhs),
        Formula::Mul(lhs, rhs) => binary("*", lhs, rhs),
        Formula::Div(lhs, rhs) => binary("/", lhs, rhs),
        Formula::Rem(lhs, rhs) => binary("%", lhs, rhs),
        Formula::Neg(inner) => Ok(format!("-({})", render_inner(inner)?)),
        _ => Err(SpecRenderError::UnsupportedFormula),
    }
}

fn render_variable(name: &str) -> Result<String, SpecRenderError> {
    // MIR names a dereferenced source parameter `a*`; the source grammar spells
    // that same leaf `*a`.  Preserve multiple deref projections exactly.
    let derefs = name.as_bytes().iter().rev().take_while(|byte| **byte == b'*').count();
    let base = &name[..name.len() - derefs];
    let source_base = if base == "_0" {
        // `_0` is MIR's return place, but only `result` is in scope in a
        // source postcondition. The parser maps it back to `_0` exactly.
        "result".to_string()
    } else if let Some(field) = base.strip_prefix("_0.") {
        if field.split('.').all(is_projected_component) {
            format!("result.{field}")
        } else {
            return Err(SpecRenderError::InvalidIdentifier { name: name.to_string() });
        }
    } else if let Some(old_name) = base.strip_prefix("old_") {
        // Only `old(identifier)` carries enough provenance to reconstruct the
        // parser's synthetic `old_<identifier>` variable without guessing.
        let source_old = if old_name == "_0" { "result" } else { old_name };
        if is_identifier(source_old) || source_old == "result" {
            format!("old({source_old})")
        } else {
            return Err(SpecRenderError::InvalidIdentifier { name: name.to_string() });
        }
    } else if is_projected_identifier(base) {
        base.to_string()
    } else {
        return Err(SpecRenderError::InvalidIdentifier { name: name.to_string() });
    };
    Ok(format!("{}{}", "*".repeat(derefs), source_base))
}

fn is_projected_identifier(name: &str) -> bool {
    let mut components = name.split('.');
    let Some(base) = components.next() else { return false };
    // The base component may carry index segments (`x[0].1`) but its head must
    // be an ordinary identifier, never a bare tuple index.
    let head = &base[..base.find('[').unwrap_or(base.len())];
    if !is_identifier(head) || !is_projected_component(base) {
        return false;
    }
    components.all(is_projected_component)
}

/// One `.`-separated projection component: a field name or tuple index
/// followed by zero or more LITERAL array-index segments — `0`, `x`, `0[3]`,
/// `x[0][1]` — exactly the spellings the contract parser's postfix grammar can
/// re-produce.  The exact-reparse round trip rejects non-canonical digit forms
/// (`[00]`) that pass here, so acceptance stays byte-exact.
fn is_projected_component(component: &str) -> bool {
    let (head, mut rest) = component.split_at(component.find('[').unwrap_or(component.len()));
    if head.is_empty() || !(head.bytes().all(|byte| byte.is_ascii_digit()) || is_identifier(head)) {
        return false;
    }
    while let Some(after) = rest.strip_prefix('[') {
        let Some((digits, tail)) = after.split_once(']') else { return false };
        if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
            return false;
        }
        rest = tail;
    }
    rest.is_empty()
}

fn is_identifier(name: &str) -> bool {
    let mut bytes = name.bytes();
    let Some(first) = bytes.next() else { return false };
    (first == b'_' || first.is_ascii_alphabetic())
        && bytes.all(|byte| byte == b'_' || byte.is_ascii_alphanumeric())
        && !is_reserved_identifier(name)
}

fn is_reserved_identifier(name: &str) -> bool {
    matches!(
        name,
        "as" | "break"
            | "const"
            | "continue"
            | "crate"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "fn"
            | "for"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "pub"
            | "ref"
            | "return"
            | "self"
            | "Self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "type"
            | "unsafe"
            | "use"
            | "where"
            | "while"
            | "async"
            | "await"
            | "dyn"
            | "abstract"
            | "become"
            | "box"
            | "do"
            | "final"
            | "macro"
            | "override"
            | "priv"
            | "typeof"
            | "unsized"
            | "virtual"
            | "yield"
            | "try"
            | "forall"
            | "exists"
            | "old"
            | "result"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    #[test]
    fn arithmetic_predicate_round_trips_structurally() {
        let formula = Formula::Eq(
            Box::new(Formula::Add(Box::new(int_var("a")), Box::new(int_var("b")))),
            Box::new(Formula::Int(10)),
        );
        let rendered = formula_to_spec_expr(&formula).unwrap();
        assert_eq!(
            retype_formula_variables(
                parse_spec_expr_result(&rendered).unwrap(),
                &formula_variable_sorts(&formula).unwrap()
            ),
            formula
        );
    }

    #[test]
    fn bool_environment_is_preserved_exactly() {
        let mut sorts = BTreeMap::new();
        sorts.insert("flag".to_string(), Sort::Bool);
        assert_eq!(
            canonicalize_spec_expr_with_sorts("flag == true", &sorts).unwrap(),
            "(flag == true)"
        );
        let typed =
            retype_formula_variables(parse_spec_expr_result("flag == true").unwrap(), &sorts);
        assert_eq!(crate::infer_sort(&typed), Sort::Bool);
    }

    #[test]
    fn implication_not_and_precedence_are_lossless() {
        let formula = Formula::Implies(
            Box::new(Formula::Var("p".into(), Sort::Bool)),
            Box::new(Formula::Not(Box::new(Formula::Var("q".into(), Sort::Bool)))),
        );
        let rendered = formula_to_spec_expr(&formula).unwrap();
        assert_eq!(rendered, "(p => !(q))");
        let sorts = formula_variable_sorts(&formula).unwrap();
        assert_eq!(
            retype_formula_variables(parse_spec_expr_result(&rendered).unwrap(), &sorts),
            formula
        );
    }

    #[test]
    fn rejects_injection_unsupported_nodes_and_sort_erasure() {
        let injected = Formula::Eq(
            Box::new(Formula::Var("x) || true || (x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        assert!(formula_to_spec_expr(&injected).is_err());
        assert!(
            formula_to_spec_expr(&Formula::Forall(vec![], Box::new(Formula::Bool(true)))).is_err()
        );
        assert!(
            formula_to_spec_expr(&Formula::Eq(
                Box::new(Formula::BitVec { value: 1, width: 8 }),
                Box::new(Formula::BitVec { value: 1, width: 8 }),
            ))
            .is_err()
        );
    }

    #[test]
    fn canonicalizer_rejects_english_and_trailing_token_injection() {
        assert!(canonicalize_spec_expr("caller must ensure: x > 0").is_err());
        assert!(canonicalize_spec_expr("x > 0); fn injected() {").is_err());
    }

    #[test]
    fn projected_and_deref_names_round_trip() {
        let projected = Formula::Gt(Box::new(int_var("p.value")), Box::new(Formula::Int(0)));
        assert_eq!(formula_to_spec_expr(&projected).unwrap(), "(p.value > 0)");
        let deref = Formula::Le(Box::new(int_var("a*")), Box::new(Formula::Int(100)));
        assert_eq!(formula_to_spec_expr(&deref).unwrap(), "(*a <= 100)");
    }

    #[test]
    fn return_place_and_old_value_use_source_scope_spellings() {
        let formula = Formula::Eq(
            Box::new(int_var("_0")),
            Box::new(Formula::Add(Box::new(int_var("old_x")), Box::new(Formula::Int(1)))),
        );
        let rendered = formula_to_spec_expr(&formula).unwrap();
        assert_eq!(rendered, "(result == (old(x) + 1))");
        assert!(!rendered.contains("_0"));
        assert_eq!(parse_spec_expr_result(&rendered).unwrap(), formula);
    }

    #[test]
    fn external_source_validation_preserves_high_level_tokens() {
        let mut sorts = BTreeMap::new();
        sorts.insert("arr".to_string(), Sort::Int);
        sorts.insert("x".to_string(), Sort::Int);
        sorts.insert("_0".to_string(), Sort::Int);

        let source = "arr.len() > 0 && result > old(x)";
        assert_eq!(
            validate_source_spec_expr(source, SourceContractClause::Ensures, &sorts).unwrap(),
            source
        );
    }

    #[test]
    fn source_provenance_distinguishes_old_prefix_and_return_place_names() {
        let mut sorts = BTreeMap::new();
        sorts.insert("x".to_string(), Sort::Bool);
        sorts.insert("old_x".to_string(), Sort::Bool);
        sorts.insert("_0".to_string(), Sort::Bool);

        assert!(
            validate_source_spec_expr("old_x == old(x)", SourceContractClause::Ensures, &sorts,)
                .is_ok()
        );
        assert!(matches!(
            validate_source_spec_expr("result == true", SourceContractClause::Requires, &sorts,),
            Err(SpecRenderError::ResultOutsidePostcondition)
        ));
        assert!(matches!(
            validate_source_spec_expr("old(x) == true", SourceContractClause::Requires, &sorts,),
            Err(SpecRenderError::OldOutsidePostcondition)
        ));
    }

    #[test]
    fn source_validation_rejects_unknown_and_recursively_ill_typed_terms() {
        let mut sorts = BTreeMap::new();
        sorts.insert("flag".to_string(), Sort::Bool);
        sorts.insert("n".to_string(), Sort::Int);

        assert!(matches!(
            validate_source_spec_expr(
                "unknown > 0",
                SourceContractClause::Requires,
                &sorts,
            ),
            Err(SpecRenderError::UnknownVariable { name }) if name == "unknown"
        ));
        for expression in ["flag + 1 > 0", "!n", "flag == n"] {
            assert!(matches!(
                validate_source_spec_expr(expression, SourceContractClause::Requires, &sorts,),
                Err(SpecRenderError::IllTyped { .. })
            ));
        }
    }

    fn f64_sorts(names: &[&str]) -> BTreeMap<String, Sort> {
        names.iter().map(|name| (name.to_string(), Sort::Float { eb: 11, sb: 53 })).collect()
    }

    #[test]
    fn source_validation_accepts_a3d_float_field_magnitude_contract() {
        // ACCEPTANCE: the EXACT canonicalized a3d dot-contract text. Before the
        // numeric-field / float-literal parser arms and the float ordering rule,
        // this failed validation and the callee's requires became Bool(false) —
        // unprovable at every call site.
        let sorts = f64_sorts(&["self.0", "self.1", "self.2", "o.0", "o.1", "o.2"]);
        let source = "(self.0) <= (1.0e30) && (self.0) >= (-(1.0e30)) && \
                      (self.1) <= (1.0e30) && (self.1) >= (-(1.0e30)) && \
                      (self.2) <= (1.0e30) && (self.2) >= (-(1.0e30)) && \
                      (o.0) <= (1.0e30) && (o.0) >= (-(1.0e30)) && \
                      (o.1) <= (1.0e30) && (o.1) >= (-(1.0e30)) && \
                      (o.2) <= (1.0e30) && (o.2) >= (-(1.0e30))";
        assert_eq!(
            validate_source_spec_expr(source, SourceContractClause::Requires, &sorts).unwrap(),
            source,
        );
    }

    #[test]
    fn source_validation_accepts_bracketed_chain_float_bound() {
        // A literal-index chain validates against its exact projected spelling.
        let sorts = f64_sorts(&["self.0[0].1"]);
        assert!(
            validate_source_spec_expr(
                "(self.0[0].1) <= (1.0e30)",
                SourceContractClause::Requires,
                &sorts,
            )
            .is_ok()
        );
    }

    #[test]
    fn source_validation_accepts_float_difference_bound() {
        // Float arithmetic over one IEEE sort: the perspective-projection
        // difference bound `(near) - (far) <= (-1.0e-6)`.
        let sorts = f64_sorts(&["near", "far"]);
        assert!(
            validate_source_spec_expr(
                "(near) - (far) <= (-(1.0e-6))",
                SourceContractClause::Requires,
                &sorts,
            )
            .is_ok()
        );
    }

    #[test]
    fn source_validation_rejects_unbound_or_computed_float_chains() {
        // MUST-NOT-VALIDATE twins for the projected-chain rule.
        // A computed index never forms a chain name; with neither `self` nor
        // `i` in scope the whole contract stays rejected (fail-closed).
        let sorts = f64_sorts(&["self.0[0].1"]);
        assert!(matches!(
            validate_source_spec_expr(
                "(self.0[i].1) <= (1.0e30)",
                SourceContractClause::Requires,
                &sorts,
            ),
            Err(SpecRenderError::UnknownVariable { .. })
        ));
        // An unbound sibling field falls back to the Int abstraction, which a
        // float literal comparison must not satisfy.
        let mut sorts = BTreeMap::new();
        sorts.insert("self".to_string(), Sort::Int);
        assert!(matches!(
            validate_source_spec_expr(
                "(self.9) <= (1.0e30)",
                SourceContractClause::Requires,
                &sorts,
            ),
            Err(SpecRenderError::IllTyped { .. })
        ));
        // A wholly unknown base is out of scope.
        assert!(matches!(
            validate_source_spec_expr(
                "(q.0) <= (1.0e30)",
                SourceContractClause::Requires,
                &BTreeMap::new(),
            ),
            Err(SpecRenderError::UnknownVariable { .. })
        ));
    }

    #[test]
    fn source_validation_rejects_mixed_and_non_numeric_orderings() {
        // MUST-NOT-VALIDATE twins for the widened numeric rules: Float never
        // mixes with Int, Bool never orders, and `%` stays integer-only.
        let mut sorts = f64_sorts(&["self.0", "near", "far"]);
        sorts.insert("flag".to_string(), Sort::Bool);
        for expression in
            ["(self.0) <= (1)", "flag < flag", "(near) % (far) <= (1.0)", "(near) - (1) <= (1.0)"]
        {
            assert!(
                matches!(
                    validate_source_spec_expr(expression, SourceContractClause::Requires, &sorts,),
                    Err(SpecRenderError::IllTyped { .. })
                ),
                "must reject: {expression}",
            );
        }
    }

    #[test]
    fn bracketed_projection_names_render_and_round_trip() {
        // The render lane accepts literal-index segments, guarded by the exact
        // reparse round trip. (`self` stays render-rejected as a reserved base
        // identifier — a pre-existing render-lane rule; the VALIDATE lane keeps
        // the user's own `self.0[3].1` spelling and never renders.)
        let formula = Formula::Gt(Box::new(int_var("p.0[3].1")), Box::new(Formula::Int(0)));
        assert_eq!(formula_to_spec_expr(&formula).unwrap(), "(p.0[3].1 > 0)");
        // MUST-NOT-RENDER twins: a computed index, a non-canonical digit form
        // (round-trip mismatch), malformed brackets, and a bare index base.
        for name in ["x[i]", "x[00]", "x[", "x[0]y", "[0]"] {
            let bad = Formula::Gt(Box::new(int_var(name)), Box::new(Formula::Int(0)));
            assert!(formula_to_spec_expr(&bad).is_err(), "{name} must not render");
        }
    }

    #[test]
    fn source_validation_preserves_exact_array_element_sort() {
        let mut sorts = BTreeMap::new();
        sorts.insert("flags".to_string(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool)));
        sorts.insert("i".to_string(), Sort::Int);

        assert!(
            validate_source_spec_expr_with_exact_projections(
                "flags[i]",
                SourceContractClause::Invariant,
                &sorts,
            )
            .is_ok()
        );
        assert!(
            validate_source_spec_expr_with_exact_projections(
                "flags.is_empty()",
                SourceContractClause::Invariant,
                &sorts,
            )
            .is_ok()
        );
        assert!(
            validate_source_spec_expr_with_exact_projections(
                "flags.len()",
                SourceContractClause::Decreases,
                &sorts,
            )
            .is_ok()
        );
        for (expression, clause) in [
            ("flags[i]", SourceContractClause::Decreases),
            ("flags[i] == 0", SourceContractClause::Invariant),
        ] {
            assert!(matches!(
                validate_source_spec_expr_with_exact_projections(expression, clause, &sorts),
                Err(SpecRenderError::IllTyped { .. })
            ));
        }
    }

    #[test]
    fn exact_source_projections_reject_non_array_bases() {
        let mut sorts = BTreeMap::new();
        sorts.insert("flag".to_string(), Sort::Bool);
        sorts.insert("n".to_string(), Sort::Int);
        sorts.insert(
            "state".to_string(),
            Sort::Datatype { name: "State".to_string(), constructors: Vec::new() },
        );

        for expression in
            ["flag[0]", "n.len() > 0", "n.is_empty()", "flag.nope == 0", "state.nope == 0"]
        {
            assert!(matches!(
                validate_source_spec_expr_with_exact_projections(
                    expression,
                    SourceContractClause::Invariant,
                    &sorts,
                ),
                Err(SpecRenderError::IllTyped { .. })
            ));
        }

        // Compatibility callers may still represent aggregate bases as Int.
        assert!(
            validate_source_spec_expr(
                "n[0] >= 0 && n.len() >= 0",
                SourceContractClause::Invariant,
                &sorts,
            )
            .is_ok()
        );
    }

    #[test]
    fn result_is_rejected_when_no_return_sort_exists() {
        let sorts = BTreeMap::new();
        assert!(matches!(
            validate_source_spec_expr("result == 0", SourceContractClause::Ensures, &sorts,),
            Err(SpecRenderError::UnitResult)
        ));
    }
}
