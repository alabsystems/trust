//! Kernel-elaborated Clean finite-model definitions routed to ty.
//!
//! This lane replaces the owner-ratified operational domain of the scalar
//! data-model fragment of `trust_model!` without introducing a second, hand-maintained
//! semantic object. `R5_TEMPORAL_PARITY_BLOCKERS` is empty. Mechanically, the
//! model-item cap survives only as a 65_536-element
//! decode-cost guard and the expression-depth cap only as a 65_536-level
//! decode-cost guard over fully iterative expression walks — neither is a
//! practical gap. The former process-global legacy-name interner and
//! its distinct-name/interned-name caps are DELETED: the shared certification
//! core is name-representation generic, so [`CleanScalarModel::to_model`]
//! feeds `certify_model` an owned `String`-named [`Model`] directly — nothing
//! is leaked and no process-wide budget can decline an otherwise valid model.
//! The legacy automatic link-time model inventory
//! was deleted as extraneous — owner ruling 2026-07-20 — so callers own the
//! explicit definition list they certify.
//! Identifier grammar is shared with the legacy certification preflight and is
//! the ratified parity target, not a gap (owner ruling 2026-07-20). The user authors one
//! [`ScalarModel`](CleanScalarModel) value in Clean. We fresh-elaborate it
//! with the canonical
//! [`FINITE_MODEL_PRELUDE`], read the registered definition body, and decode only
//! that kernel-checked expression tree.  Source text is never scanned for model
//! syntax.  Malformed structures accepted by the legacy parser fail validation
//! before ty lowering.
//!
//! Honest scope: the result is proof evidence about the exact finite model that
//! was decoded and rendered for ty.  This module does not claim that its data
//! decoder is a kernel proof of a `Trust.Temporal.StateMachine` proposition.
//! Function-valued variables and general `~>` discharge remain outside v1.

use std::collections::BTreeSet;

use clean_kernel::ConstantKind;
use clean_kernel::env::Environment;
use clean_kernel::expr::{Expr as KernelExpr, ExprKind, Literal};
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;

use crate::clean_surface::{CleanTemporalCertificateError, elaborate_temporal_definitions};
use crate::{
    Action, BoundTyCert, Expr, FnVar, Invariant, Model, ModelVerdict, StateVar, TyCertifyError,
    Update, bind_model_configuration, certify_model, parse_and_bind_ty_cert,
    recheck_model_bound_clean_kernel,
};

/// Canonical Clean datatype used by the general scalar model lane.
pub const FINITE_MODEL_PRELUDE: &str = include_str!("../clean/Trust/FiniteModel.lean");

/// Versioned artifact/certificate schema for this lane.
pub const CLEAN_SCALAR_MODEL_SCHEMA_V1: &str = "trust.clean-scalar-model/v1";

const SCALAR_MODEL_TYPE: &str = "Trust.Temporal.FiniteModel.ScalarModel";
const PREFIX: &str = "Trust.Temporal.FiniteModel";
/// Per-section list-length cap for decoded Clean models.
///
/// Kept finite purely as a decode-cost (DoS) guard: the list walk is
/// iterative, so the only exposure is time/memory spent decoding an
/// adversarially long `List.cons` chain. The macro lane's implicit bound is
/// compile-time source size, and no realistic authored model approaches
/// 65 536 items per section, so this cap is no longer a practical
/// admission-parity gap (widened 1_024 → 65_536, 2026-07-20).
const MAX_MODEL_ITEMS: usize = 65_536;
/// Nesting-depth cap for decoded Clean scalar expressions.
///
/// Kept finite purely as a decode-cost (DoS) guard, matching the
/// [`MAX_MODEL_ITEMS`] convention: every production operation in this crate
/// that is reachable from the kernel-decoded expression — decode
/// ([`Decoder::scalar_expr`]), validation
/// ([`CleanScalarModel::validate_expr`]), certification-carrier conversion (in
/// [`CleanScalarModel::to_model`]), shared sort preflight (`model_expr_sort`),
/// TLA+ rendering (`Expr::to_tla`), and destruction — uses an explicit heap
/// worklist. The remaining exposure is time/memory spent on an adversarially
/// deep expression. Recursive derived convenience traits are outside that
/// production route and are documented separately on [`CleanScalarExpr`]. The
/// macro lane's implicit bound is compile-time source nesting, and no realistic
/// authored model approaches 65 536 levels, so this cap is no longer a
/// practical admission-parity gap (widened 256 → 65_536, 2026-07-20; the
/// production walks and destructor were converted to iteration first).
const MAX_EXPR_DEPTH: usize = 65_536;
pub(crate) const MAX_NAME_BYTES: usize = 128;

/// Identifier-shaped fixed tokens recognized by the repository-pinned ty TLA+
/// lexer.  Such a token cannot safely be emitted as a user declaration name:
/// the parser will lex it as its dedicated token rather than as `Ident`.
///
/// The source-coupling test below derives this set from all three local lexer
/// token groups, so a ty lexer update cannot silently make this mirror stale.
pub(crate) const TLA_RESERVED_IDENTIFIER_TOKENS: &[&str] = &[
    "ASSUME",
    "ASSUMPTION",
    "AXIOM",
    "Append",
    "BOOLEAN",
    "BY",
    "CASE",
    "CHOOSE",
    "CONSTANT",
    "CONSTANTS",
    "COROLLARY",
    "DEF",
    "DEFINE",
    "DEFS",
    "DOMAIN",
    "ELSE",
    "ENABLED",
    "EXCEPT",
    "EXTENDS",
    "FALSE",
    "HAVE",
    "HIDE",
    "Head",
    "IF",
    "IN",
    "INSTANCE",
    "INTER",
    "LAMBDA",
    "LEMMA",
    "LET",
    "LOCAL",
    "Len",
    "MODULE",
    "NEW",
    "OBVIOUS",
    "OMITTED",
    "ONLY",
    "OTHER",
    "PICK",
    "PROOF",
    "PROPOSITION",
    "QED",
    "RECURSIVE",
    "SF_",
    "SUBSET",
    "SUFFICES",
    "SelectSeq",
    "Seq",
    "SubSeq",
    "TAKE",
    "THEN",
    "THEOREM",
    "TRUE",
    "Tail",
    "UNCHANGED",
    "UNION",
    "USE",
    "VARIABLE",
    "VARIABLES",
    "WF_",
    "WITH",
    "WITNESS",
];

/// Owned mirror of the scalar expression union decoded from Clean.
///
/// Its destructor is iterative. The derived `Debug`, `Clone`, equality, and
/// serde implementations remain structurally recursive convenience APIs; the
/// kernel-decoded certification route does not apply them to the expression
/// tree, and callers must not treat those traits as stack-safe at the admission
/// boundary.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CleanScalarExpr {
    Int(i64),
    Var(String),
    ConstRef(String),
    Add(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
    Gt(Box<Self>, Box<Self>),
    Le(Box<Self>, Box<Self>),
    Eq(Box<Self>, Box<Self>),
    Neq(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    And(Box<Self>, Box<Self>),
    If(Box<Self>, Box<Self>, Box<Self>),
    Iff(Box<Self>, Box<Self>),
    Forall(String, Box<Self>, Box<Self>, Box<Self>),
    Bool(bool),
}

impl CleanScalarExpr {
    /// Detach direct children into the iterative destructor's heap worklist.
    fn detach_children_for_drop(&mut self, pending: &mut Vec<Self>) {
        fn detach(child: &mut Box<CleanScalarExpr>) -> CleanScalarExpr {
            std::mem::replace(child.as_mut(), CleanScalarExpr::Int(0))
        }

        match self {
            Self::Add(left, right)
            | Self::Sub(left, right)
            | Self::Gt(left, right)
            | Self::Le(left, right)
            | Self::Eq(left, right)
            | Self::Neq(left, right)
            | Self::Or(left, right)
            | Self::And(left, right)
            | Self::Iff(left, right) => {
                pending.push(detach(left));
                pending.push(detach(right));
            }
            Self::If(first, second, third) | Self::Forall(_, first, second, third) => {
                pending.push(detach(first));
                pending.push(detach(second));
                pending.push(detach(third));
            }
            Self::Int(_) | Self::Var(_) | Self::ConstRef(_) | Self::Bool(_) => {}
        }
    }
}

impl Drop for CleanScalarExpr {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.detach_children_for_drop(&mut pending);
        while let Some(mut child) = pending.pop() {
            child.detach_children_for_drop(&mut pending);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanScalarConstant {
    pub name: String,
    pub value: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanScalarStateVar {
    pub name: String,
    pub init: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanScalarUpdate {
    pub var: String,
    pub value: CleanScalarExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanScalarAction {
    pub name: String,
    pub guard: Option<CleanScalarExpr>,
    pub updates: Vec<CleanScalarUpdate>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanScalarInvariant {
    pub name: String,
    pub value: CleanScalarExpr,
}

/// Fully owned finite scalar model decoded from a Clean definition.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanScalarModel {
    pub name: String,
    pub constants: Vec<CleanScalarConstant>,
    pub variables: Vec<CleanScalarStateVar>,
    pub actions: Vec<CleanScalarAction>,
    pub invariants: Vec<CleanScalarInvariant>,
}

/// Exact Clean definition artifact.  Both type and value are serialized because
/// replay must reject a same-named definition whose elaborated meaning changed.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanScalarModelArtifact {
    pub schema: String,
    pub clean_source: String,
    pub model_definition: String,
    pub type_expr: Vec<u8>,
    pub value_expr: Vec<u8>,
}

/// Exact positive and negative evidence for one Clean-authored scalar model.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanScalarModelCertificate {
    pub schema: String,
    pub model: CleanScalarModelArtifact,
    pub spec_src: String,
    pub config_src: String,
    pub safety_certificate_json: String,
    pub buggy_config_src: String,
    pub buggy_counterexample_json: String,
}

/// Fail-closed errors from Clean model extraction, validation, or replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CleanScalarModelError {
    Clean(CleanTemporalCertificateError),
    Definition(String),
    Temporal(String),
    ArtifactMismatch(String),
}

impl std::fmt::Display for CleanScalarModelError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Clean(error) => write!(formatter, "Clean finite model declined: {error}"),
            Self::Definition(detail) => {
                write!(formatter, "unsupported Clean finite model: {detail}")
            }
            Self::Temporal(detail) => {
                write!(formatter, "ty finite-model evidence declined: {detail}")
            }
            Self::ArtifactMismatch(detail) => {
                write!(formatter, "Clean finite-model artifact mismatch: {detail}")
            }
        }
    }
}

impl std::error::Error for CleanScalarModelError {}

impl From<CleanTemporalCertificateError> for CleanScalarModelError {
    fn from(error: CleanTemporalCertificateError) -> Self {
        Self::Clean(error)
    }
}

impl From<TyCertifyError> for CleanScalarModelError {
    fn from(error: TyCertifyError) -> Self {
        Self::Temporal(error.to_string())
    }
}

fn encoded(expression: &KernelExpr) -> Result<Vec<u8>, CleanScalarModelError> {
    serde_json::to_vec(expression)
        .map_err(|error| CleanScalarModelError::ArtifactMismatch(error.to_string()))
}

fn finite_environment(source: &str) -> Result<Environment, CleanScalarModelError> {
    // `elaborate_temporal_definitions` prepends the temporal prelude and uses a
    // fresh environment with external imports disabled.  Appending this fixed
    // data vocabulary before user source gives the model constructors the same
    // fresh-context and no-shadow guarantees.
    let mut combined = String::with_capacity(FINITE_MODEL_PRELUDE.len() + source.len() + 1);
    combined.push_str(FINITE_MODEL_PRELUDE);
    combined.push('\n');
    combined.push_str(source);
    Ok(elaborate_temporal_definitions(&combined)?)
}

struct Decoder<'environment> {
    checker: TypeChecker<'environment>,
}

impl<'environment> Decoder<'environment> {
    fn new(environment: &'environment Environment) -> Self {
        Self { checker: TypeChecker::with_mode(environment, environment.mode()) }
    }

    fn whnf(&self, expression: &KernelExpr) -> KernelExpr {
        self.checker.whnf(expression)
    }

    fn head_and_args(
        &self,
        expression: &KernelExpr,
    ) -> Result<(String, Vec<KernelExpr>), CleanScalarModelError> {
        let expression = self.whnf(expression);
        let head = match expression.get_app_fn().kind() {
            ExprKind::Const(name, _) => name.to_string(),
            other => {
                return Err(CleanScalarModelError::Definition(format!(
                    "expected constructor application, got head {other:?}"
                )));
            }
        };
        let args = expression.get_app_args().iter().map(|arg| (*arg).clone()).collect();
        Ok((head, args))
    }

    fn constructor_args(
        &self,
        expression: &KernelExpr,
        expected: &str,
        arity: usize,
    ) -> Result<Vec<KernelExpr>, CleanScalarModelError> {
        let (head, args) = self.head_and_args(expression)?;
        if head != expected || args.len() != arity {
            return Err(CleanScalarModelError::Definition(format!(
                "expected `{expected}` with {arity} argument(s), got `{head}` with {}",
                args.len()
            )));
        }
        Ok(args)
    }

    fn string(&self, expression: &KernelExpr) -> Result<String, CleanScalarModelError> {
        match self.whnf(expression).kind() {
            ExprKind::Lit(Literal::String(value)) => Ok(value.to_string()),
            other => Err(CleanScalarModelError::Definition(format!(
                "expected a String literal, got {other:?}"
            ))),
        }
    }

    fn integer(&self, expression: &KernelExpr) -> Result<i64, CleanScalarModelError> {
        match self.whnf(expression).kind() {
            ExprKind::Lit(Literal::Nat(value)) => value.to_string().parse::<i64>().map_err(|_| {
                CleanScalarModelError::Definition(
                    "Nat value does not fit the legacy scalar i64 domain".to_owned(),
                )
            }),
            other => Err(CleanScalarModelError::Definition(format!(
                "expected a Nat literal, got {other:?}"
            ))),
        }
    }

    fn boolean(&self, expression: &KernelExpr) -> Result<bool, CleanScalarModelError> {
        let (head, args) = self.head_and_args(expression)?;
        if !args.is_empty() {
            return Err(CleanScalarModelError::Definition(format!(
                "expected a Bool constructor, got `{head}` with arguments"
            )));
        }
        match head.as_str() {
            "Bool.true" => Ok(true),
            "Bool.false" => Ok(false),
            _ => Err(CleanScalarModelError::Definition(format!(
                "expected Bool.true or Bool.false, got `{head}`"
            ))),
        }
    }

    fn list<T>(
        &self,
        expression: &KernelExpr,
        mut decode: impl FnMut(&Self, &KernelExpr) -> Result<T, CleanScalarModelError>,
    ) -> Result<Vec<T>, CleanScalarModelError> {
        let mut current = expression.clone();
        let mut values = Vec::new();
        loop {
            let (head, args) = self.head_and_args(&current)?;
            match head.as_str() {
                "List.nil" if args.len() == 1 => return Ok(values),
                "List.cons" if args.len() == 3 => {
                    if values.len() >= MAX_MODEL_ITEMS {
                        return Err(CleanScalarModelError::Definition(format!(
                            "model list exceeds {MAX_MODEL_ITEMS} elements"
                        )));
                    }
                    values.push(decode(self, &args[1])?);
                    current = args[2].clone();
                }
                _ => {
                    return Err(CleanScalarModelError::Definition(format!(
                        "expected a concrete List, got `{head}` with {} argument(s)",
                        args.len()
                    )));
                }
            }
        }
    }

    /// Decode one kernel scalar expression with an explicit heap stack.
    ///
    /// The walk is iterative (depth-first, left-to-right — the same node and
    /// error-discovery order as the recursive original), so nesting depth can
    /// never overflow the Rust stack; `MAX_EXPR_DEPTH` survives purely as a
    /// decode-cost guard.
    fn scalar_expr(
        &self,
        expression: &KernelExpr,
        depth: usize,
    ) -> Result<CleanScalarExpr, CleanScalarModelError> {
        /// Reassembly step run after a node's children were all decoded (their
        /// results sit on `decoded`, last child on top).
        enum Assemble {
            Binary(fn(Box<CleanScalarExpr>, Box<CleanScalarExpr>) -> CleanScalarExpr),
            If,
            Forall(String),
        }
        enum Task {
            Decode(KernelExpr, usize),
            Assemble(Assemble),
        }

        let mut tasks = vec![Task::Decode(expression.clone(), depth)];
        let mut decoded: Vec<CleanScalarExpr> = Vec::new();
        while let Some(task) = tasks.pop() {
            let (expression, depth) = match task {
                Task::Assemble(Assemble::Binary(ctor)) => {
                    let right = decoded.pop().expect("binary decode scheduled two operands");
                    let left = decoded.pop().expect("binary decode scheduled two operands");
                    decoded.push(ctor(Box::new(left), Box::new(right)));
                    continue;
                }
                Task::Assemble(Assemble::If) => {
                    let else_value = decoded.pop().expect("ite decode scheduled three operands");
                    let then_value = decoded.pop().expect("ite decode scheduled three operands");
                    let condition = decoded.pop().expect("ite decode scheduled three operands");
                    decoded.push(CleanScalarExpr::If(
                        Box::new(condition),
                        Box::new(then_value),
                        Box::new(else_value),
                    ));
                    continue;
                }
                Task::Assemble(Assemble::Forall(index)) => {
                    let body = decoded.pop().expect("forallIn decode scheduled three operands");
                    let high = decoded.pop().expect("forallIn decode scheduled three operands");
                    let low = decoded.pop().expect("forallIn decode scheduled three operands");
                    decoded.push(CleanScalarExpr::Forall(
                        index,
                        Box::new(low),
                        Box::new(high),
                        Box::new(body),
                    ));
                    continue;
                }
                Task::Decode(expression, depth) => (expression, depth),
            };
            if depth > MAX_EXPR_DEPTH {
                return Err(CleanScalarModelError::Definition(format!(
                    "scalar expression exceeds depth {MAX_EXPR_DEPTH}"
                )));
            }
            let (head, args) = self.head_and_args(&expression)?;
            let binary_ctor: Option<
                fn(Box<CleanScalarExpr>, Box<CleanScalarExpr>) -> CleanScalarExpr,
            > = match head.as_str() {
                name if name == format!("{PREFIX}.ScalarExpr.add") => Some(CleanScalarExpr::Add),
                name if name == format!("{PREFIX}.ScalarExpr.sub") => Some(CleanScalarExpr::Sub),
                name if name == format!("{PREFIX}.ScalarExpr.gt") => Some(CleanScalarExpr::Gt),
                name if name == format!("{PREFIX}.ScalarExpr.le") => Some(CleanScalarExpr::Le),
                name if name == format!("{PREFIX}.ScalarExpr.eq") => Some(CleanScalarExpr::Eq),
                name if name == format!("{PREFIX}.ScalarExpr.neq") => Some(CleanScalarExpr::Neq),
                name if name == format!("{PREFIX}.ScalarExpr.or") => Some(CleanScalarExpr::Or),
                name if name == format!("{PREFIX}.ScalarExpr.and") => Some(CleanScalarExpr::And),
                name if name == format!("{PREFIX}.ScalarExpr.iff") => Some(CleanScalarExpr::Iff),
                _ => None,
            };
            if let Some(ctor) = binary_ctor {
                if args.len() != 2 {
                    return Err(CleanScalarModelError::Definition(format!(
                        "`{head}` expects two arguments, got {}",
                        args.len()
                    )));
                }
                let mut operands = args.into_iter();
                let left = operands.next().expect("arity was checked");
                let right = operands.next().expect("arity was checked");
                tasks.push(Task::Assemble(Assemble::Binary(ctor)));
                tasks.push(Task::Decode(right, depth + 1));
                tasks.push(Task::Decode(left, depth + 1));
                continue;
            }
            match head.as_str() {
                name if name == format!("{PREFIX}.ScalarExpr.int") => {
                    if args.len() != 1 {
                        return Err(CleanScalarModelError::Definition(
                            "ScalarExpr.int arity drift".to_owned(),
                        ));
                    }
                    decoded.push(CleanScalarExpr::Int(self.integer(&args[0])?));
                }
                name if name == format!("{PREFIX}.ScalarExpr.var") => {
                    if args.len() != 1 {
                        return Err(CleanScalarModelError::Definition(
                            "ScalarExpr.var arity drift".to_owned(),
                        ));
                    }
                    decoded.push(CleanScalarExpr::Var(self.string(&args[0])?));
                }
                name if name == format!("{PREFIX}.ScalarExpr.constRef") => {
                    if args.len() != 1 {
                        return Err(CleanScalarModelError::Definition(
                            "ScalarExpr.constRef arity drift".to_owned(),
                        ));
                    }
                    decoded.push(CleanScalarExpr::ConstRef(self.string(&args[0])?));
                }
                name if name == format!("{PREFIX}.ScalarExpr.ite") => {
                    if args.len() != 3 {
                        return Err(CleanScalarModelError::Definition(
                            "ScalarExpr.ite arity drift".to_owned(),
                        ));
                    }
                    let mut operands = args.into_iter();
                    let condition = operands.next().expect("arity was checked");
                    let then_value = operands.next().expect("arity was checked");
                    let else_value = operands.next().expect("arity was checked");
                    tasks.push(Task::Assemble(Assemble::If));
                    tasks.push(Task::Decode(else_value, depth + 1));
                    tasks.push(Task::Decode(then_value, depth + 1));
                    tasks.push(Task::Decode(condition, depth + 1));
                }
                name if name == format!("{PREFIX}.ScalarExpr.forallIn") => {
                    if args.len() != 4 {
                        return Err(CleanScalarModelError::Definition(
                            "ScalarExpr.forallIn arity drift".to_owned(),
                        ));
                    }
                    let index = self.string(&args[0])?;
                    let mut operands = args.into_iter().skip(1);
                    let low = operands.next().expect("arity was checked");
                    let high = operands.next().expect("arity was checked");
                    let body = operands.next().expect("arity was checked");
                    tasks.push(Task::Assemble(Assemble::Forall(index)));
                    tasks.push(Task::Decode(body, depth + 1));
                    tasks.push(Task::Decode(high, depth + 1));
                    tasks.push(Task::Decode(low, depth + 1));
                }
                name if name == format!("{PREFIX}.ScalarExpr.bool") => {
                    if args.len() != 1 {
                        return Err(CleanScalarModelError::Definition(
                            "ScalarExpr.bool arity drift".to_owned(),
                        ));
                    }
                    decoded.push(CleanScalarExpr::Bool(self.boolean(&args[0])?));
                }
                _ => {
                    return Err(CleanScalarModelError::Definition(format!(
                        "unsupported scalar expression constructor `{head}`"
                    )));
                }
            }
        }
        Ok(decoded.pop().expect("iterative decode produced exactly one root expression"))
    }

    fn constant(
        &self,
        expression: &KernelExpr,
    ) -> Result<CleanScalarConstant, CleanScalarModelError> {
        let args = self.constructor_args(expression, &format!("{PREFIX}.Constant.mk"), 2)?;
        Ok(CleanScalarConstant { name: self.string(&args[0])?, value: self.integer(&args[1])? })
    }

    fn state_var(
        &self,
        expression: &KernelExpr,
    ) -> Result<CleanScalarStateVar, CleanScalarModelError> {
        let args = self.constructor_args(expression, &format!("{PREFIX}.StateVar.mk"), 2)?;
        Ok(CleanScalarStateVar { name: self.string(&args[0])?, init: self.integer(&args[1])? })
    }

    fn update(&self, expression: &KernelExpr) -> Result<CleanScalarUpdate, CleanScalarModelError> {
        let args = self.constructor_args(expression, &format!("{PREFIX}.Update.mk"), 2)?;
        Ok(CleanScalarUpdate { var: self.string(&args[0])?, value: self.scalar_expr(&args[1], 0)? })
    }

    fn guard(
        &self,
        expression: &KernelExpr,
    ) -> Result<Option<CleanScalarExpr>, CleanScalarModelError> {
        let (head, args) = self.head_and_args(expression)?;
        if head == format!("{PREFIX}.Guard.always") && args.is_empty() {
            return Ok(None);
        }
        if head == format!("{PREFIX}.Guard.when") && args.len() == 1 {
            return Ok(Some(self.scalar_expr(&args[0], 0)?));
        }
        Err(CleanScalarModelError::Definition(format!(
            "expected Guard.always or Guard.when, got `{head}` with {} argument(s)",
            args.len()
        )))
    }

    fn action(&self, expression: &KernelExpr) -> Result<CleanScalarAction, CleanScalarModelError> {
        let args = self.constructor_args(expression, &format!("{PREFIX}.Action.mk"), 3)?;
        Ok(CleanScalarAction {
            name: self.string(&args[0])?,
            guard: self.guard(&args[1])?,
            updates: self.list(&args[2], Self::update)?,
        })
    }

    fn invariant(
        &self,
        expression: &KernelExpr,
    ) -> Result<CleanScalarInvariant, CleanScalarModelError> {
        let args = self.constructor_args(expression, &format!("{PREFIX}.Invariant.mk"), 2)?;
        Ok(CleanScalarInvariant {
            name: self.string(&args[0])?,
            value: self.scalar_expr(&args[1], 0)?,
        })
    }

    fn model(&self, expression: &KernelExpr) -> Result<CleanScalarModel, CleanScalarModelError> {
        let args = self.constructor_args(expression, &format!("{PREFIX}.ScalarModel.mk"), 5)?;
        let model = CleanScalarModel {
            name: self.string(&args[0])?,
            constants: self.list(&args[1], Self::constant)?,
            variables: self.list(&args[2], Self::state_var)?,
            actions: self.list(&args[3], Self::action)?,
            invariants: self.list(&args[4], Self::invariant)?,
        };
        model.validate()?;
        Ok(model)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScalarSort {
    Int,
    Bool,
}

impl CleanScalarModel {
    fn validate_name(name: &str, role: &str) -> Result<(), CleanScalarModelError> {
        crate::validate_temporal_identifier(name, role).map_err(CleanScalarModelError::Definition)
    }

    /// Sort-check one decoded scalar expression with an explicit heap stack.
    ///
    /// The walk is iterative (same depth-first, left-to-right node and
    /// error-discovery order as the recursive original), so validation depth is
    /// bounded by heap, not the Rust stack.
    fn validate_expr(
        &self,
        expression: &CleanScalarExpr,
        bound: &mut Vec<String>,
    ) -> Result<ScalarSort, CleanScalarModelError> {
        use CleanScalarExpr as E;
        enum Task<'e> {
            Sort(&'e CleanScalarExpr),
            /// Pop one computed sort and require it (the shared error shape).
            Expect(ScalarSort, &'static str),
            /// Pop the two branch sorts of an `If` and require they agree.
            MatchIfArms,
            PushBinder(&'e str),
            PopBinder,
            Emit(ScalarSort),
        }
        let expect = |found: ScalarSort, wanted: ScalarSort, context: &str| {
            if found == wanted {
                Ok(())
            } else {
                Err(CleanScalarModelError::Definition(format!(
                    "{context} has the wrong scalar sort"
                )))
            }
        };

        let mut tasks = vec![Task::Sort(expression)];
        let mut sorts: Vec<ScalarSort> = Vec::new();
        while let Some(task) = tasks.pop() {
            let expression = match task {
                Task::Expect(wanted, context) => {
                    let found = sorts.pop().expect("a sort was scheduled before every Expect");
                    expect(found, wanted, context)?;
                    continue;
                }
                Task::MatchIfArms => {
                    let else_sort = sorts.pop().expect("if scheduled both branch sorts");
                    let then_sort = sorts.pop().expect("if scheduled both branch sorts");
                    if then_sort != else_sort {
                        return Err(CleanScalarModelError::Definition(
                            "if branches have different scalar sorts".to_owned(),
                        ));
                    }
                    sorts.push(then_sort);
                    continue;
                }
                Task::PushBinder(index) => {
                    bound.push(index.to_owned());
                    continue;
                }
                Task::PopBinder => {
                    bound.pop();
                    continue;
                }
                Task::Emit(sort) => {
                    sorts.push(sort);
                    continue;
                }
                Task::Sort(expression) => expression,
            };
            match expression {
                E::Int(_) => sorts.push(ScalarSort::Int),
                E::Bool(_) => sorts.push(ScalarSort::Bool),
                E::Var(name) => {
                    if self.variables.iter().any(|variable| variable.name == *name)
                        || bound.iter().any(|binder| binder == name)
                    {
                        sorts.push(ScalarSort::Int);
                    } else {
                        return Err(CleanScalarModelError::Definition(format!(
                            "unknown state/bound variable `{name}`"
                        )));
                    }
                }
                E::ConstRef(name) => {
                    if self.constants.iter().any(|constant| constant.name == *name) {
                        sorts.push(ScalarSort::Int);
                    } else {
                        return Err(CleanScalarModelError::Definition(format!(
                            "unknown constant `{name}`"
                        )));
                    }
                }
                E::Add(left, right) | E::Sub(left, right) => {
                    tasks.push(Task::Emit(ScalarSort::Int));
                    tasks.push(Task::Expect(ScalarSort::Int, "arithmetic rhs"));
                    tasks.push(Task::Sort(right));
                    tasks.push(Task::Expect(ScalarSort::Int, "arithmetic lhs"));
                    tasks.push(Task::Sort(left));
                }
                E::Gt(left, right)
                | E::Le(left, right)
                | E::Eq(left, right)
                | E::Neq(left, right) => {
                    tasks.push(Task::Emit(ScalarSort::Bool));
                    tasks.push(Task::Expect(ScalarSort::Int, "comparison rhs"));
                    tasks.push(Task::Sort(right));
                    tasks.push(Task::Expect(ScalarSort::Int, "comparison lhs"));
                    tasks.push(Task::Sort(left));
                }
                E::Or(left, right) | E::And(left, right) | E::Iff(left, right) => {
                    tasks.push(Task::Emit(ScalarSort::Bool));
                    tasks.push(Task::Expect(ScalarSort::Bool, "boolean rhs"));
                    tasks.push(Task::Sort(right));
                    tasks.push(Task::Expect(ScalarSort::Bool, "boolean lhs"));
                    tasks.push(Task::Sort(left));
                }
                E::If(condition, then_value, else_value) => {
                    tasks.push(Task::MatchIfArms);
                    tasks.push(Task::Sort(else_value));
                    tasks.push(Task::Sort(then_value));
                    tasks.push(Task::Expect(ScalarSort::Bool, "if condition"));
                    tasks.push(Task::Sort(condition));
                }
                E::Forall(index, low, high, body) => {
                    Self::validate_name(index, "quantifier index")?;
                    if self.constants.iter().any(|constant| constant.name == *index)
                        || self.variables.iter().any(|variable| variable.name == *index)
                        || bound.iter().any(|binder| binder == index)
                    {
                        return Err(CleanScalarModelError::Definition(format!(
                            "quantifier index `{index}` shadows another identifier"
                        )));
                    }
                    tasks.push(Task::Emit(ScalarSort::Bool));
                    tasks.push(Task::Expect(ScalarSort::Bool, "forall body"));
                    tasks.push(Task::PopBinder);
                    tasks.push(Task::Sort(body));
                    tasks.push(Task::PushBinder(index));
                    tasks.push(Task::Expect(ScalarSort::Int, "forall upper bound"));
                    tasks.push(Task::Sort(high));
                    tasks.push(Task::Expect(ScalarSort::Int, "forall lower bound"));
                    tasks.push(Task::Sort(low));
                }
            }
        }
        Ok(sorts.pop().expect("iterative validation produced exactly one root sort"))
    }

    fn validate(&self) -> Result<(), CleanScalarModelError> {
        Self::validate_name(&self.name, "model")?;
        if self.variables.is_empty() || self.actions.is_empty() || self.invariants.is_empty() {
            return Err(CleanScalarModelError::Definition(
                "a certifiable model needs at least one variable, action, and invariant".to_owned(),
            ));
        }

        let mut global = BTreeSet::from([
            "Init".to_owned(),
            "Next".to_owned(),
            "Spec".to_owned(),
            "vars".to_owned(),
        ]);
        for (role, names) in [
            (
                "constant",
                self.constants.iter().map(|entry| entry.name.as_str()).collect::<Vec<_>>(),
            ),
            ("variable", self.variables.iter().map(|entry| entry.name.as_str()).collect()),
            ("action", self.actions.iter().map(|entry| entry.name.as_str()).collect()),
            ("invariant", self.invariants.iter().map(|entry| entry.name.as_str()).collect()),
        ] {
            for name in names {
                Self::validate_name(name, role)?;
                if !global.insert(name.to_owned()) {
                    return Err(CleanScalarModelError::Definition(format!(
                        "duplicate or reserved {role} name `{name}`"
                    )));
                }
            }
        }

        for action in &self.actions {
            if let Some(guard) = &action.guard {
                if self.validate_expr(guard, &mut Vec::new())? != ScalarSort::Bool {
                    return Err(CleanScalarModelError::Definition(format!(
                        "action `{}` guard is not Boolean",
                        action.name
                    )));
                }
            }
            let mut updated = BTreeSet::new();
            for update in &action.updates {
                if !self.variables.iter().any(|variable| variable.name == update.var) {
                    return Err(CleanScalarModelError::Definition(format!(
                        "action `{}` updates unknown variable `{}`",
                        action.name, update.var
                    )));
                }
                if !updated.insert(update.var.as_str()) {
                    return Err(CleanScalarModelError::Definition(format!(
                        "action `{}` updates `{}` more than once",
                        action.name, update.var
                    )));
                }
                if self.validate_expr(&update.value, &mut Vec::new())? != ScalarSort::Int {
                    return Err(CleanScalarModelError::Definition(format!(
                        "action `{}` update of `{}` is not integer-valued",
                        action.name, update.var
                    )));
                }
            }
        }
        for invariant in &self.invariants {
            if self.validate_expr(&invariant.value, &mut Vec::new())? != ScalarSort::Bool {
                return Err(CleanScalarModelError::Definition(format!(
                    "invariant `{}` is not Boolean",
                    invariant.name
                )));
            }
        }
        Ok(())
    }

    /// Convert to the shared certification [`Model`] carrier after validation.
    ///
    /// The certification core is name-representation generic, so the decoded
    /// owned `String` names feed it directly: no interning, no leak, and no
    /// process-wide budget that could decline an otherwise valid model based
    /// on unrelated earlier conversions.
    pub fn to_model(&self) -> Result<Model<String>, CleanScalarModelError> {
        self.validate()?;

        /// Convert one decoded expression to the certification carrier with an
        /// explicit heap stack (iterative, so conversion depth is bounded by
        /// heap, not the Rust stack).
        fn expression(value: &CleanScalarExpr) -> Expr<String> {
            enum Build {
                Binary(fn(Box<Expr<String>>, Box<Expr<String>>) -> Expr<String>),
                If,
                Forall(String),
            }
            enum Task<'e> {
                Convert(&'e CleanScalarExpr),
                Build(Build),
            }
            fn binary<'e>(
                tasks: &mut Vec<Task<'e>>,
                ctor: fn(Box<Expr<String>>, Box<Expr<String>>) -> Expr<String>,
                a: &'e CleanScalarExpr,
                b: &'e CleanScalarExpr,
            ) {
                tasks.push(Task::Build(Build::Binary(ctor)));
                tasks.push(Task::Convert(b));
                tasks.push(Task::Convert(a));
            }
            let mut tasks = vec![Task::Convert(value)];
            let mut converted: Vec<Expr<String>> = Vec::new();
            while let Some(task) = tasks.pop() {
                let node = match task {
                    Task::Build(Build::Binary(ctor)) => {
                        let b = converted.pop().expect("binary conversion scheduled two operands");
                        let a = converted.pop().expect("binary conversion scheduled two operands");
                        converted.push(ctor(Box::new(a), Box::new(b)));
                        continue;
                    }
                    Task::Build(Build::If) => {
                        let b = converted.pop().expect("if conversion scheduled three operands");
                        let a = converted.pop().expect("if conversion scheduled three operands");
                        let c = converted.pop().expect("if conversion scheduled three operands");
                        converted.push(Expr::If(Box::new(c), Box::new(a), Box::new(b)));
                        continue;
                    }
                    Task::Build(Build::Forall(index)) => {
                        let body =
                            converted.pop().expect("forall conversion scheduled three operands");
                        let high =
                            converted.pop().expect("forall conversion scheduled three operands");
                        let low =
                            converted.pop().expect("forall conversion scheduled three operands");
                        converted.push(Expr::Forall(
                            index,
                            Box::new(low),
                            Box::new(high),
                            Box::new(body),
                        ));
                        continue;
                    }
                    Task::Convert(node) => node,
                };
                match node {
                    CleanScalarExpr::Int(value) => converted.push(Expr::Int(*value)),
                    CleanScalarExpr::Var(value) => converted.push(Expr::Var(value.clone())),
                    CleanScalarExpr::ConstRef(value) => {
                        converted.push(Expr::ConstRef(value.clone()));
                    }
                    CleanScalarExpr::Bool(value) => converted.push(Expr::Bool(*value)),
                    CleanScalarExpr::Add(a, b) => binary(&mut tasks, Expr::Add, a, b),
                    CleanScalarExpr::Sub(a, b) => binary(&mut tasks, Expr::Sub, a, b),
                    CleanScalarExpr::Gt(a, b) => binary(&mut tasks, Expr::Gt, a, b),
                    CleanScalarExpr::Le(a, b) => binary(&mut tasks, Expr::Le, a, b),
                    CleanScalarExpr::Eq(a, b) => binary(&mut tasks, Expr::Eq, a, b),
                    CleanScalarExpr::Neq(a, b) => binary(&mut tasks, Expr::Neq, a, b),
                    CleanScalarExpr::Or(a, b) => binary(&mut tasks, Expr::Or, a, b),
                    CleanScalarExpr::And(a, b) => binary(&mut tasks, Expr::And, a, b),
                    CleanScalarExpr::Iff(a, b) => binary(&mut tasks, Expr::Iff, a, b),
                    CleanScalarExpr::If(c, a, b) => {
                        tasks.push(Task::Build(Build::If));
                        tasks.push(Task::Convert(b));
                        tasks.push(Task::Convert(a));
                        tasks.push(Task::Convert(c));
                    }
                    CleanScalarExpr::Forall(index, low, high, body) => {
                        tasks.push(Task::Build(Build::Forall(index.clone())));
                        tasks.push(Task::Convert(body));
                        tasks.push(Task::Convert(high));
                        tasks.push(Task::Convert(low));
                    }
                }
            }
            converted.pop().expect("iterative conversion produced exactly one root expression")
        }

        let model = Model {
            name: self.name.clone(),
            consts: self.constants.iter().map(|entry| (entry.name.clone(), entry.value)).collect(),
            vars: self
                .variables
                .iter()
                .map(|entry| StateVar { name: entry.name.clone(), init: entry.init })
                .collect(),
            fn_vars: Vec::<FnVar<String>>::new(),
            actions: self
                .actions
                .iter()
                .map(|entry| Action {
                    name: entry.name.clone(),
                    guard: entry.guard.as_ref().map(expression),
                    updates: entry
                        .updates
                        .iter()
                        .map(|update| Update {
                            var: update.var.clone(),
                            expr: expression(&update.value),
                        })
                        .collect(),
                })
                .collect(),
            invariants: self
                .invariants
                .iter()
                .map(|entry| Invariant { name: entry.name.clone(), expr: expression(&entry.value) })
                .collect(),
        };
        crate::validate_model_for_certification(&model)
            .map_err(|error| CleanScalarModelError::Definition(error.to_string()))?;
        Ok(model)
    }
}

/// Freshly elaborate and decode one fully qualified Clean `ScalarModel` definition.
pub fn extract_clean_scalar_model(
    clean_source: &str,
    model_definition: &str,
) -> Result<(CleanScalarModelArtifact, CleanScalarModel), CleanScalarModelError> {
    let environment = finite_environment(clean_source)?;
    let declaration =
        environment.get_const(&Name::from_string(model_definition)).ok_or_else(|| {
            CleanScalarModelError::Definition(format!("missing `{model_definition}`"))
        })?;
    if declaration.kind != ConstantKind::Definition {
        return Err(CleanScalarModelError::Definition(format!(
            "`{model_definition}` is {:?}, not a definition",
            declaration.kind
        )));
    }
    let value = declaration.value.as_ref().ok_or_else(|| {
        CleanScalarModelError::Definition(format!("`{model_definition}` has no value"))
    })?;
    let decoder = Decoder::new(&environment);
    let normalized_type = decoder.whnf(&declaration.type_);
    match normalized_type.kind() {
        ExprKind::Const(name, _) if name.to_string() == SCALAR_MODEL_TYPE => {}
        other => {
            return Err(CleanScalarModelError::Definition(format!(
                "`{model_definition}` must have type `{SCALAR_MODEL_TYPE}`, got {other:?}"
            )));
        }
    }
    let model = decoder.model(value)?;
    let artifact = CleanScalarModelArtifact {
        schema: CLEAN_SCALAR_MODEL_SCHEMA_V1.to_owned(),
        clean_source: clean_source.to_owned(),
        model_definition: model_definition.to_owned(),
        type_expr: encoded(&declaration.type_)?,
        value_expr: encoded(value)?,
    };
    Ok((artifact, model))
}

/// Freshly replay an extraction artifact and return the decoded model.
pub fn recheck_clean_scalar_model_artifact(
    artifact: &CleanScalarModelArtifact,
    expected_clean_source: &str,
) -> Result<CleanScalarModel, CleanScalarModelError> {
    if artifact.schema != CLEAN_SCALAR_MODEL_SCHEMA_V1 {
        return Err(CleanScalarModelError::ArtifactMismatch(format!(
            "unsupported schema `{}`",
            artifact.schema
        )));
    }
    if artifact.clean_source != expected_clean_source {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "authored Clean source changed".to_owned(),
        ));
    }
    let (fresh, model) =
        extract_clean_scalar_model(expected_clean_source, &artifact.model_definition)?;
    if fresh.type_expr != artifact.type_expr || fresh.value_expr != artifact.value_expr {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "fresh kernel elaboration differs from stored model definition".to_owned(),
        ));
    }
    Ok(model)
}

fn buggy_envelope<S: AsRef<str>>(
    model: &Model<S>,
) -> Result<tla_check::verdict::VerdictEnvelope, CleanScalarModelError> {
    crate::validate_committed_buggy_baseline(model)?;
    let _ty_transaction = crate::in_process_ty_transaction_lock();
    let spec_src = model.to_tla();
    let config_src = model.to_replay_cfg_with(&[("Buggy", 1)]);
    let config = tla_check::Config::parse(&config_src).map_err(|error| {
        CleanScalarModelError::Temporal(format!("invalid Buggy=1 config: {error:?}"))
    })?;
    let tree = tla_core::parse_to_syntax_tree(&spec_src);
    let module = tla_core::lower(tla_core::FileId(0), &tree).module.ok_or_else(|| {
        CleanScalarModelError::Temporal("generated Buggy=1 model failed to lower".to_owned())
    })?;
    let result = tla_check::check_module(&module, &config);
    let envelope = tla_check::verdict::build_violation_envelope(
        &spec_src,
        Some(&config_src),
        &config,
        &result,
        tla_check::verdict::Completeness::Exhaustive,
        tla_check::verdict::ProducerIdentity::current(),
    )
    .ok_or_else(|| {
        CleanScalarModelError::Temporal(format!(
            "Buggy=1 did not produce a replayable invariant violation: {result:?}"
        ))
    })?;
    let report = tla_check::verdict::verify_violation_envelope(&envelope);
    if !matches!(report.verdict, tla_check::verdict::VerdictVerdict::Verified)
        || !matches!(envelope.kind, tla_check::verdict::ViolationKind::Invariant)
        || !envelope.violated.as_deref().is_some_and(|name| {
            model.invariants.iter().any(|invariant| invariant.name.as_ref() == name)
        })
    {
        return Err(CleanScalarModelError::Temporal(format!(
            "Buggy=1 counterexample replay declined or named an unbound invariant: {}",
            report.detail
        )));
    }
    Ok(envelope)
}

fn replay_safety<S: AsRef<str>>(
    raw: &str,
    model: &Model<S>,
) -> Result<BoundTyCert, CleanScalarModelError> {
    let _ty_transaction = crate::in_process_ty_transaction_lock();
    let expected_invariants =
        model.invariants.iter().map(|invariant| invariant.name.as_ref()).collect::<Vec<_>>();
    let mut bound = parse_and_bind_ty_cert(raw, &model.to_tla(), &expected_invariants)?;
    bind_model_configuration(&bound, model)?;
    recheck_model_bound_clean_kernel(&mut bound, model)?;
    Ok(bound)
}

/// Certify the exact kernel-elaborated scalar model through the pinned ty lane.
pub fn certify_clean_scalar_model_with_ty(
    clean_source: &str,
    model_definition: &str,
) -> Result<CleanScalarModelCertificate, CleanScalarModelError> {
    let _ty_transaction = crate::in_process_ty_transaction_lock();
    let (artifact, decoded) = extract_clean_scalar_model(clean_source, model_definition)?;
    crate::validate_committed_buggy_values(
        decoded
            .constants
            .iter()
            .filter_map(|constant| (constant.name == "Buggy").then_some(constant.value)),
    )?;
    let model = decoded.to_model()?;
    crate::validate_committed_buggy_baseline(&model)?;
    let outcome = certify_model(&model);
    if outcome.verdict != ModelVerdict::Proved {
        return Err(CleanScalarModelError::Temporal(format!(
            "positive/kernel/non-vacuity gates did not close: {:?}",
            outcome.verdict
        )));
    }
    let safety = outcome.bound.map_err(CleanScalarModelError::from)?;
    if !safety.kernel_rechecked {
        return Err(CleanScalarModelError::Temporal(
            "positive certificate was not kernel-rechecked".to_owned(),
        ));
    }
    let buggy = buggy_envelope(&model)?;
    Ok(CleanScalarModelCertificate {
        schema: CLEAN_SCALAR_MODEL_SCHEMA_V1.to_owned(),
        model: artifact,
        spec_src: model.to_tla(),
        config_src: model.to_cfg(),
        safety_certificate_json: safety.raw_json,
        buggy_config_src: model.to_replay_cfg_with(&[("Buggy", 1)]),
        buggy_counterexample_json: buggy.to_json(),
    })
}

/// Replay both the Clean extraction and the stored positive/negative ty objects.
pub fn recheck_clean_scalar_model_with_ty(
    certificate: &CleanScalarModelCertificate,
    expected_clean_source: &str,
) -> Result<(), CleanScalarModelError> {
    let _ty_transaction = crate::in_process_ty_transaction_lock();
    if certificate.schema != CLEAN_SCALAR_MODEL_SCHEMA_V1 {
        return Err(CleanScalarModelError::ArtifactMismatch(format!(
            "unsupported schema `{}`",
            certificate.schema
        )));
    }
    let decoded = recheck_clean_scalar_model_artifact(&certificate.model, expected_clean_source)?;
    crate::validate_committed_buggy_values(
        decoded
            .constants
            .iter()
            .filter_map(|constant| (constant.name == "Buggy").then_some(constant.value)),
    )?;
    let model = decoded.to_model()?;
    // The public certificate carrier is constructible.  Establish the exact
    // committed mutation baseline before considering either stored evidence
    // object; otherwise independently valid evidence from distinct Buggy
    // configurations could be assembled into one accepted certificate.
    crate::validate_committed_buggy_baseline(&model)?;
    if model.to_tla() != certificate.spec_src || model.to_cfg() != certificate.config_src {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "freshly decoded model generates different ty inputs".to_owned(),
        ));
    }
    replay_safety(&certificate.safety_certificate_json, &model)?;

    let _ty_transaction = crate::in_process_ty_transaction_lock();
    let expected_buggy_config = model.to_replay_cfg_with(&[("Buggy", 1)]);
    if certificate.buggy_config_src != expected_buggy_config {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "Buggy=1 configuration differs from the decoded model".to_owned(),
        ));
    }
    let envelope =
        tla_check::verdict::VerdictEnvelope::from_json(&certificate.buggy_counterexample_json)
            .map_err(CleanScalarModelError::ArtifactMismatch)?;
    if envelope.spec_src != certificate.spec_src
        || envelope.config_src.as_deref() != Some(expected_buggy_config.as_str())
        || !matches!(envelope.kind, tla_check::verdict::ViolationKind::Invariant)
        || !envelope
            .violated
            .as_deref()
            .is_some_and(|name| model.invariants.iter().any(|invariant| invariant.name == name))
    {
        return Err(CleanScalarModelError::ArtifactMismatch(
            "Buggy=1 envelope is not bound to this model and its invariants".to_owned(),
        ));
    }
    let report = tla_check::verdict::verify_violation_envelope(&envelope);
    if !matches!(report.verdict, tla_check::verdict::VerdictVerdict::Verified) {
        return Err(CleanScalarModelError::Temporal(format!(
            "stored Buggy=1 counterexample declined replay: {}",
            report.detail
        )));
    }
    Ok(())
}

#[cfg(test)]
#[allow(deprecated)] // differential vectors deliberately exercise the legacy macro twin
mod tests {
    use super::*;
    use crate::recheck_bound_clean_kernel;

    // This pair is intentionally redundant test input: one legacy macro value
    // and one user-authored Clean value describe the same machine.  Keeping all
    // grammar forms in one differential fixture makes bounded-subset parity a
    // byte oracle over the actual public generators, not a hand-written claim.
    #[allow(deprecated)]
    fn legacy_macro_grammar_parity_model() -> Model {
        crate::trust_model! {
            MacroGrammarParity {
                const Buggy = 0;
                const Limit = 5;
                const Bias = 1;
                var x = 0;
                var y = 1;
                action Advance when (((x + 1) <= (Limit - Bias))) {
                    x = x + 1;
                    y = if x > 0 {
                        if Buggy == 0 { y + Bias } else { y - 1 }
                    } else if Limit > 0 {
                        1
                    } else {
                        0
                    };
                }
                action Reset {
                    x = 0;
                    y = Limit;
                }
                invariant Bounded: x <= Limit;
                invariant PositiveY: y > 0;
                invariant ConditionalBool:
                    if Buggy == 0 { x <= Limit } else { x > Limit };
            }
        }
    }

    #[allow(deprecated)]
    fn legacy_unchanged_parity_model() -> Model {
        crate::trust_model! {
            UnchangedParity {
                const Buggy = 0;
                var x = 0;
                var y = 1;
                action AdvanceX { x = x + 1; }
                action Stutter { }
                invariant Safe: Buggy <= x;
            }
        }
    }

    #[allow(deprecated)]
    fn complete_authority_model() -> Model {
        crate::trust_model! {
            CompleteAuthority {
                const Buggy = 0;
                var x = 0;
                action Step when (x <= 2) {
                    x = x + 1;
                }
                invariant Safe: Buggy <= x;
            }
        }
    }

    // The legacy parser constructs these malformed values.  They are compile
    // vectors, not models the migration surface promises to preserve.
    #[allow(deprecated)]
    fn legacy_macro_accepts_missing_model_sections() -> (Model, Model, Model) {
        let no_variables = crate::trust_model! {
            LegacyNoVariables {
                const Buggy = 0;
                action Step { }
                invariant DialOff: Buggy == 0;
            }
        };
        let no_actions = crate::trust_model! {
            LegacyNoActions {
                const Buggy = 0;
                var x = 0;
                invariant Safe: x == 0;
            }
        };
        let no_invariants = crate::trust_model! {
            LegacyNoInvariants {
                const Buggy = 0;
                var x = 0;
                action Step { x = 0; }
            }
        };
        (no_variables, no_actions, no_invariants)
    }

    #[allow(deprecated)]
    fn legacy_macro_accepts_duplicate_and_reserved_names() -> (Model, Model, Model) {
        let duplicate = crate::trust_model! {
            LegacyDuplicateNames {
                const Buggy = 0;
                var x = 0;
                var x = 1;
                action Step { x = 0; }
                invariant Safe: x == 0;
            }
        };
        let reserved = crate::trust_model! {
            LegacyReservedName {
                const Buggy = 0;
                var Init = 0;
                action Step { Init = 0; }
                invariant Safe: Init == 0;
            }
        };
        let tla_keyword = crate::trust_model! {
            LegacyTlaKeywordName {
                const Buggy = 0;
                var TRUE = 0;
                action Step { TRUE = 0; }
                invariant Safe: TRUE == 0;
            }
        };
        (duplicate, reserved, tla_keyword)
    }

    #[allow(deprecated)]
    fn legacy_macro_accepts_leading_underscore_name() -> Model {
        crate::trust_model! {
            LegacyLeadingUnderscore {
                const Buggy = 0;
                var _x = 0;
                action Step { _x = 0; }
                invariant Safe: _x == 0;
            }
        }
    }

    #[allow(deprecated)]
    fn legacy_macro_accepts_unknown_and_duplicate_updates() -> (Model, Model) {
        let unknown = crate::trust_model! {
            LegacyUnknownUpdate {
                const Buggy = 0;
                var x = 0;
                action Step { missing = 0; }
                invariant Safe: x == 0;
            }
        };
        let duplicate = crate::trust_model! {
            LegacyDuplicateUpdate {
                const Buggy = 0;
                var x = 0;
                action Step {
                    x = 0;
                    x = 1;
                }
                invariant Safe: x == 0;
            }
        };
        (unknown, duplicate)
    }

    fn valid_clean_fixture(name: &str) -> CleanScalarModel {
        CleanScalarModel {
            name: name.to_owned(),
            constants: vec![CleanScalarConstant { name: "Buggy".to_owned(), value: 0 }],
            variables: vec![CleanScalarStateVar { name: "x".to_owned(), init: 0 }],
            actions: vec![CleanScalarAction {
                name: "Step".to_owned(),
                guard: None,
                updates: vec![CleanScalarUpdate {
                    var: "x".to_owned(),
                    value: CleanScalarExpr::Int(0),
                }],
            }],
            invariants: vec![CleanScalarInvariant {
                name: "Safe".to_owned(),
                value: CleanScalarExpr::Eq(
                    Box::new(CleanScalarExpr::Var("x".to_owned())),
                    Box::new(CleanScalarExpr::Int(0)),
                ),
            }],
        }
    }

    fn assert_definition_error(model: CleanScalarModel, expected: &str) {
        match model.to_model() {
            Err(CleanScalarModelError::Definition(detail)) => assert!(
                detail.contains(expected),
                "expected `{expected}` in validation error, got `{detail}`"
            ),
            other => panic!("malformed Clean model did not fail closed: {other:?}"),
        }
    }

    const MACRO_GRAMMAR_PARITY_SOURCE: &str = r#"
namespace MigrationExample

def X : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.var "x"
def Y : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.var "y"
def Zero : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.int 0
def One : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.int 1
def Limit : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.constRef "Limit"
def Bias : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.constRef "Bias"
def Buggy : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.constRef "Buggy"

def MacroGrammarParity : Trust.Temporal.FiniteModel.ScalarModel :=
  Trust.Temporal.FiniteModel.ScalarModel.mk "MacroGrammarParity"
    [Trust.Temporal.FiniteModel.Constant.mk "Buggy" 0,
     Trust.Temporal.FiniteModel.Constant.mk "Limit" 5,
     Trust.Temporal.FiniteModel.Constant.mk "Bias" 1]
    [Trust.Temporal.FiniteModel.StateVar.mk "x" 0,
     Trust.Temporal.FiniteModel.StateVar.mk "y" 1]
    [Trust.Temporal.FiniteModel.Action.mk "Advance"
       (Trust.Temporal.FiniteModel.Guard.when
         (Trust.Temporal.FiniteModel.ScalarExpr.le
           (Trust.Temporal.FiniteModel.ScalarExpr.add X One)
           (Trust.Temporal.FiniteModel.ScalarExpr.sub Limit Bias)))
       [Trust.Temporal.FiniteModel.Update.mk "x"
          (Trust.Temporal.FiniteModel.ScalarExpr.add X One),
        Trust.Temporal.FiniteModel.Update.mk "y"
          (Trust.Temporal.FiniteModel.ScalarExpr.ite
            (Trust.Temporal.FiniteModel.ScalarExpr.gt X Zero)
            (Trust.Temporal.FiniteModel.ScalarExpr.ite
              (Trust.Temporal.FiniteModel.ScalarExpr.eq Buggy Zero)
              (Trust.Temporal.FiniteModel.ScalarExpr.add Y Bias)
              (Trust.Temporal.FiniteModel.ScalarExpr.sub Y One))
            (Trust.Temporal.FiniteModel.ScalarExpr.ite
              (Trust.Temporal.FiniteModel.ScalarExpr.gt Limit Zero)
              One Zero))],
     Trust.Temporal.FiniteModel.Action.mk "Reset"
       Trust.Temporal.FiniteModel.Guard.always
       [Trust.Temporal.FiniteModel.Update.mk "x" Zero,
        Trust.Temporal.FiniteModel.Update.mk "y" Limit]]
    [Trust.Temporal.FiniteModel.Invariant.mk "Bounded"
       (Trust.Temporal.FiniteModel.ScalarExpr.le X Limit),
     Trust.Temporal.FiniteModel.Invariant.mk "PositiveY"
       (Trust.Temporal.FiniteModel.ScalarExpr.gt Y Zero),
     Trust.Temporal.FiniteModel.Invariant.mk "ConditionalBool"
       (Trust.Temporal.FiniteModel.ScalarExpr.ite
         (Trust.Temporal.FiniteModel.ScalarExpr.eq Buggy Zero)
         (Trust.Temporal.FiniteModel.ScalarExpr.le X Limit)
         (Trust.Temporal.FiniteModel.ScalarExpr.gt X Limit))]

end MigrationExample
"#;

    const UNCHANGED_PARITY_SOURCE: &str = r#"
namespace UnchangedMigration

def X : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.var "x"
def One : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.int 1
def Buggy : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.constRef "Buggy"

def UnchangedParity : Trust.Temporal.FiniteModel.ScalarModel :=
  Trust.Temporal.FiniteModel.ScalarModel.mk "UnchangedParity"
    [Trust.Temporal.FiniteModel.Constant.mk "Buggy" 0]
    [Trust.Temporal.FiniteModel.StateVar.mk "x" 0,
     Trust.Temporal.FiniteModel.StateVar.mk "y" 1]
    [Trust.Temporal.FiniteModel.Action.mk "AdvanceX"
       Trust.Temporal.FiniteModel.Guard.always
       [Trust.Temporal.FiniteModel.Update.mk "x"
          (Trust.Temporal.FiniteModel.ScalarExpr.add X One)],
     Trust.Temporal.FiniteModel.Action.mk "Stutter"
       Trust.Temporal.FiniteModel.Guard.always
       []]
    [Trust.Temporal.FiniteModel.Invariant.mk "Safe"
       (Trust.Temporal.FiniteModel.ScalarExpr.le Buggy X)]

end UnchangedMigration
"#;

    const UNCHANGED_PARITY_TLA: &str = "---- MODULE UnchangedParity ----\n\
EXTENDS Naturals\n\
CONSTANT Buggy\n\
VARIABLES x, y\n\
vars == << x, y >>\n\
Init == x = 0 /\\ y = 1\n\
AdvanceX == x' = (x + 1) /\\ UNCHANGED << y >>\n\
Stutter == UNCHANGED << x, y >>\n\
Next == AdvanceX \\/ Stutter\n\
Spec == Init /\\ [][Next]_vars\n\
Safe == Buggy =< x\n\
====\n";

    const UNCHANGED_PARITY_CFG: &str = "CONSTANT Buggy = 0\n\
SPECIFICATION Spec\n\
INVARIANT Safe\n\
CHECK_DEADLOCK FALSE\n";

    const SOURCE: &str = include_str!("../examples/clean_scalar_lockstep.lean");

    const COMPLETE_AUTHORITY_SOURCE: &str = include_str!("../examples/clean_scalar_complete.lean");

    fn buggy_baseline_source_variants() -> [(String, &'static str); 3] {
        let missing = SOURCE
            .replace(
                "[Trust.Temporal.FiniteModel.Constant.mk \"Buggy\" 0,\n     Trust.Temporal.FiniteModel.Constant.mk \"Limit\" 2]",
                "[Trust.Temporal.FiniteModel.Constant.mk \"Limit\" 2]",
            )
            .replace(
                "Trust.Temporal.FiniteModel.ScalarExpr.eq Buggy Zero",
                "Trust.Temporal.FiniteModel.ScalarExpr.eq Zero Zero",
            );
        let nonzero = SOURCE.replacen(
            "Trust.Temporal.FiniteModel.Constant.mk \"Buggy\" 0",
            "Trust.Temporal.FiniteModel.Constant.mk \"Buggy\" 2",
            1,
        );
        let duplicate = SOURCE.replacen(
            "Trust.Temporal.FiniteModel.Constant.mk \"Buggy\" 0,",
            "Trust.Temporal.FiniteModel.Constant.mk \"Buggy\" 0,\n     Trust.Temporal.FiniteModel.Constant.mk \"Buggy\" 0,",
            1,
        );
        for changed in [&missing, &nonzero, &duplicate] {
            assert_ne!(changed, SOURCE, "the baseline mutation fixture must change the source");
        }
        [(missing, "found none"), (nonzero, "found value 2"), (duplicate, "found duplicates")]
    }

    #[test]
    fn decoded_clean_model_matches_every_macro_grammar_form_in_a_valid_model() {
        let legacy = legacy_macro_grammar_parity_model();
        let (_, decoded) = extract_clean_scalar_model(
            MACRO_GRAMMAR_PARITY_SOURCE,
            "MigrationExample.MacroGrammarParity",
        )
        .expect("the Clean migration model must decode");
        let clean = decoded.to_model().expect("the decoded migration model must validate");

        assert_eq!(
            clean.to_tla().as_bytes(),
            legacy.to_tla().as_bytes(),
            "generated TLA+ must remain byte-for-byte identical"
        );
        assert_eq!(
            clean.to_cfg().as_bytes(),
            legacy.to_cfg().as_bytes(),
            "generated ty config must remain byte-for-byte identical"
        );

        let error = certify_clean_scalar_model_with_ty(
            MACRO_GRAMMAR_PARITY_SOURCE,
            "MigrationExample.MacroGrammarParity",
        )
        .unwrap_err();
        assert!(
            matches!(error, CleanScalarModelError::Temporal(ref detail)
                if (detail.contains("enumerator-assisted")
                        && detail.contains("missing the Next completeness"))
                    || detail.contains("the explicit-fixpoint certificate lane declined")),
            "grammar parity remains exact, but this richer fixture must stay below the Certified \
             authority tier until the mandatory TY producer accepts it: {error:?}"
        );
    }

    #[test]
    fn decoded_clean_partial_and_empty_updates_match_macro_unchanged_bytes() {
        let legacy = legacy_unchanged_parity_model();
        let (_, decoded) = extract_clean_scalar_model(
            UNCHANGED_PARITY_SOURCE,
            "UnchangedMigration.UnchangedParity",
        )
        .expect("the Clean partial/empty-update model must decode");
        assert_eq!(
            decoded.actions.iter().map(|action| action.updates.len()).collect::<Vec<_>>(),
            vec![1, 0],
            "the Clean decoder must preserve partial and empty update lists"
        );
        let clean = decoded.to_model().expect("the decoded UNCHANGED model must validate");

        let clean_tla = clean.to_tla();
        let legacy_tla = legacy.to_tla();
        assert_eq!(
            clean_tla.as_bytes(),
            legacy_tla.as_bytes(),
            "Clean and trust_model! must emit byte-identical UNCHANGED actions"
        );
        assert_eq!(
            clean_tla.as_bytes(),
            UNCHANGED_PARITY_TLA.as_bytes(),
            "partial and empty update lists must generate the exact UNCHANGED clauses"
        );

        let clean_cfg = clean.to_cfg();
        let legacy_cfg = legacy.to_cfg();
        assert_eq!(
            clean_cfg.as_bytes(),
            legacy_cfg.as_bytes(),
            "Clean and trust_model! must emit byte-identical ty configs"
        );
        assert_eq!(
            clean_cfg.as_bytes(),
            UNCHANGED_PARITY_CFG.as_bytes(),
            "the UNCHANGED fixture's ty config must remain exact"
        );
    }

    #[test]
    fn concurrent_positive_replay_and_buggy_ratchets_remain_run_isolated() {
        let model = complete_authority_model();
        let outcome = certify_model(&model);
        assert_eq!(outcome.verdict, ModelVerdict::Proved);
        let bound = outcome.bound.expect("the positive fixture must produce replayable evidence");
        let same_thread_buggy = buggy_envelope(&model)
            .expect("the immediate Buggy=1 leg must not reuse positive caches");
        assert_eq!(same_thread_buggy.violated.as_deref(), Some("Safe"));
        let mut same_thread_replay = bound.clone();
        recheck_bound_clean_kernel(&mut same_thread_replay)
            .expect("positive replay after the Buggy=1 leg must remain exact");

        std::thread::scope(|scope| {
            let start = std::sync::Arc::new(std::sync::Barrier::new(4));
            let mut runs = Vec::new();
            for _ in 0..2 {
                let start = std::sync::Arc::clone(&start);
                let model = &model;
                runs.push(scope.spawn(move || {
                    start.wait();
                    let envelope = buggy_envelope(model)
                        .expect("every concurrent Buggy=1 run must find its own violation");
                    assert_eq!(envelope.violated.as_deref(), Some("Safe"));
                }));
            }
            for _ in 0..2 {
                let start = std::sync::Arc::clone(&start);
                let mut replay = bound.clone();
                runs.push(scope.spawn(move || {
                    start.wait();
                    recheck_bound_clean_kernel(&mut replay)
                        .expect("concurrent positive evidence replay must stay isolated");
                }));
            }
            for run in runs {
                run.join().expect("concurrent embedded ty transaction must not panic");
            }
        });
    }

    #[test]
    fn production_reset_cannot_invalidate_a_guarded_preparse_transaction() {
        let model = legacy_macro_grammar_parity_model();
        let _ty_transaction = crate::in_process_ty_transaction_lock();
        let spec_src = model.to_tla();
        let config_src = model.to_replay_cfg_with(&[("Buggy", 1)]);
        let config = tla_check::Config::parse(&config_src).expect("Buggy config must parse");
        let tree = tla_core::parse_to_syntax_tree(&spec_src);
        let module =
            tla_core::lower(tla_core::FileId(0), &tree).module.expect("Buggy module must lower");

        std::thread::spawn(tla_check::reset_global_state)
            .join()
            .expect("concurrent reset must fail closed without panicking");

        let result = tla_check::check_module(&module, &config);
        let envelope = tla_check::verdict::build_violation_envelope(
            &spec_src,
            Some(&config_src),
            &config,
            &result,
            tla_check::verdict::Completeness::Exhaustive,
            tla_check::verdict::ProducerIdentity::current(),
        )
        .unwrap_or_else(|| {
            panic!("guarded Buggy=1 check lost its violation after reset: {result:?}")
        });
        // The Boolean-valued conditional is deliberately false in the Buggy=1
        // image.  Reaching it after a concurrent reset proves that the parsed
        // semantic input, including the newly covered Boolean ITE arm, stayed
        // live for the whole guarded transaction.
        assert_eq!(envelope.violated.as_deref(), Some("ConditionalBool"));
    }

    #[test]
    fn clean_rejects_macro_accepted_models_with_missing_required_sections() {
        let (legacy_no_variables, legacy_no_actions, legacy_no_invariants) =
            legacy_macro_accepts_missing_model_sections();
        assert!(legacy_no_variables.vars.is_empty());
        assert!(legacy_no_actions.actions.is_empty());
        assert!(legacy_no_invariants.invariants.is_empty());

        let mut no_variables = valid_clean_fixture("CleanNoVariables");
        no_variables.variables.clear();
        assert_definition_error(no_variables, "at least one variable, action, and invariant");

        let mut no_actions = valid_clean_fixture("CleanNoActions");
        no_actions.actions.clear();
        assert_definition_error(no_actions, "at least one variable, action, and invariant");

        let mut no_invariants = valid_clean_fixture("CleanNoInvariants");
        no_invariants.invariants.clear();
        assert_definition_error(no_invariants, "at least one variable, action, and invariant");
    }

    #[test]
    fn clean_rejects_macro_accepted_duplicate_and_reserved_names() {
        let (legacy_duplicate, legacy_reserved, legacy_tla_keyword) =
            legacy_macro_accepts_duplicate_and_reserved_names();
        assert_eq!(legacy_duplicate.vars.iter().filter(|var| var.name == "x").count(), 2);
        assert!(legacy_reserved.vars.iter().any(|var| var.name == "Init"));
        assert!(legacy_tla_keyword.vars.iter().any(|var| var.name == "TRUE"));

        let mut duplicate = valid_clean_fixture("CleanDuplicateNames");
        duplicate.variables.push(CleanScalarStateVar { name: "x".to_owned(), init: 1 });
        assert_definition_error(duplicate, "duplicate or reserved variable name `x`");

        let mut reserved = valid_clean_fixture("CleanReservedName");
        reserved.variables[0].name = "Init".to_owned();
        reserved.actions[0].updates[0].var = "Init".to_owned();
        reserved.invariants[0].value = CleanScalarExpr::Eq(
            Box::new(CleanScalarExpr::Var("Init".to_owned())),
            Box::new(CleanScalarExpr::Int(0)),
        );
        assert_definition_error(reserved, "duplicate or reserved variable name `Init`");

        let mut tla_keyword = valid_clean_fixture("CleanTlaKeywordName");
        tla_keyword.variables[0].name = "TRUE".to_owned();
        assert_definition_error(tla_keyword, "variable `TRUE` is a reserved TLA+ lexer token");
    }

    #[test]
    fn clean_rejects_macro_accepted_leading_underscore_name() {
        let legacy = legacy_macro_accepts_leading_underscore_name();
        assert!(legacy.vars.iter().any(|variable| variable.name == "_x"));

        let mut clean = valid_clean_fixture("CleanLeadingUnderscore");
        clean.variables[0].name = "_x".to_owned();
        clean.actions[0].updates[0].var = "_x".to_owned();
        clean.invariants[0].value = CleanScalarExpr::Eq(
            Box::new(CleanScalarExpr::Var("_x".to_owned())),
            Box::new(CleanScalarExpr::Int(0)),
        );
        assert_definition_error(clean, "variable `_x` is not a supported TLA+ identifier");
    }

    /// Differential guard for the ratified parity target (owner ruling
    /// 2026-07-20): identifier grammar is SHARED, not Clean-only. The macro can
    /// still CONSTRUCT a model with a leading-underscore or over-`MAX_NAME_BYTES`
    /// name, but the legacy lane's own certification preflight rejects it —
    /// macro-CERTIFIABLE, not merely macro-constructible, is the parity domain,
    /// so these rejections are anti-injection enforcement, not an
    /// admission-domain parity gap.
    #[test]
    fn legacy_lane_rejects_underscore_and_oversized_names_at_certification() {
        // Leading underscore: macro-constructible ...
        let underscore = legacy_macro_accepts_leading_underscore_name();
        assert!(underscore.vars.iter().any(|variable| variable.name == "_x"));
        // ... but the shared preflight declines it before any backend runs ...
        let error = crate::validate_model_for_certification(&underscore).unwrap_err();
        assert!(
            matches!(
                error,
                TyCertifyError::Setup(ref detail)
                    if detail.contains("variable `_x` is not a supported TLA+ identifier")
            ),
            "legacy preflight must reject the leading-underscore name: {error:?}"
        );
        // ... and the full certification entry point fails closed, never Proved.
        let outcome = certify_model(&underscore);
        assert!(matches!(
            &outcome.verdict,
            ModelVerdict::Unknown(detail)
                if detail.contains("variable `_x` is not a supported TLA+ identifier")
        ));
        assert_eq!(outcome.non_vacuity, None);

        // Over-MAX_NAME_BYTES name: the macro grammar accepts any Rust
        // identifier length, so this too is legacy-constructible; certification
        // rejects it in the same shared preflight.
        let long_name: &'static str = Box::leak("A".repeat(MAX_NAME_BYTES + 1).into_boxed_str());
        assert!(long_name.len() > MAX_NAME_BYTES);
        let mut oversized = legacy_macro_grammar_parity_model();
        oversized.name = long_name;
        let error = crate::validate_model_for_certification(&oversized).unwrap_err();
        assert!(
            matches!(
                error,
                TyCertifyError::Setup(ref detail)
                    if detail.contains("not a supported TLA+ identifier")
                        && detail.contains("max 128 bytes")
            ),
            "legacy preflight must reject the over-cap name: {error:?}"
        );
        let outcome = certify_model(&oversized);
        assert!(matches!(
            &outcome.verdict,
            ModelVerdict::Unknown(detail) if detail.contains("max 128 bytes")
        ));
        assert_eq!(outcome.non_vacuity, None);
    }

    #[test]
    fn every_identifier_shaped_ty_lexer_token_is_rejected_before_lowering() {
        for &reserved in TLA_RESERVED_IDENTIFIER_TOKENS {
            let mut model = valid_clean_fixture("CleanReservedTyToken");
            model.variables[0].name = reserved.to_owned();
            assert_definition_error(
                model,
                &format!("variable `{reserved}` is a reserved TLA+ lexer token"),
            );
        }
    }

    #[test]
    fn reserved_identifier_mirror_tracks_the_local_ty_lexer_sources() {
        fn fixed_identifier_tokens(source: &str) -> BTreeSet<&str> {
            source
                .lines()
                .filter_map(|line| {
                    let marker = "#[token(\"";
                    let start = line.find(marker)? + marker.len();
                    let end = start + line[start..].find('"')?;
                    let token = &line[start..end];
                    crate::valid_tla_identifier(token).then_some(token)
                })
                .collect()
        }

        let mut lexer_tokens = BTreeSet::new();
        for source in [
            include_str!(
                "../../../first-party/ty/crates/tla-core/src/syntax/lexer/token_groups/keywords.rs"
            ),
            include_str!(
                "../../../first-party/ty/crates/tla-core/src/syntax/lexer/token_groups/operators.rs"
            ),
            include_str!(
                "../../../first-party/ty/crates/tla-core/src/syntax/lexer/token_groups/surface.rs"
            ),
        ] {
            lexer_tokens.extend(fixed_identifier_tokens(source));
        }
        let mirrored = TLA_RESERVED_IDENTIFIER_TOKENS.iter().copied().collect::<BTreeSet<_>>();
        assert_eq!(mirrored, lexer_tokens, "reserved-name validation must track ty's lexer");
    }

    #[test]
    fn clean_rejects_macro_accepted_unknown_and_duplicate_updates() {
        let (legacy_unknown, legacy_duplicate) =
            legacy_macro_accepts_unknown_and_duplicate_updates();
        assert_eq!(legacy_unknown.actions[0].updates[0].var, "missing");
        assert_eq!(legacy_duplicate.actions[0].updates.len(), 2);

        let mut unknown = valid_clean_fixture("CleanUnknownUpdate");
        unknown.actions[0].updates[0].var = "missing".to_owned();
        assert_definition_error(unknown, "updates unknown variable `missing`");

        let mut duplicate = valid_clean_fixture("CleanDuplicateUpdate");
        duplicate.actions[0]
            .updates
            .push(CleanScalarUpdate { var: "x".to_owned(), value: CleanScalarExpr::Int(1) });
        assert_definition_error(duplicate, "updates `x` more than once");
    }

    #[test]
    fn scalar_if_preserves_common_branch_sort_and_rejects_mixed_branches() {
        let condition = CleanScalarExpr::Eq(
            Box::new(CleanScalarExpr::Var("x".to_owned())),
            Box::new(CleanScalarExpr::Int(0)),
        );

        let mut boolean = valid_clean_fixture("CleanBooleanIf");
        boolean.invariants[0].value = CleanScalarExpr::If(
            Box::new(condition.clone()),
            Box::new(CleanScalarExpr::Bool(true)),
            Box::new(CleanScalarExpr::Bool(false)),
        );
        boolean.to_model().expect("a Boolean-valued conditional is a valid invariant");

        let mut mixed = valid_clean_fixture("CleanMixedIf");
        mixed.invariants[0].value = CleanScalarExpr::If(
            Box::new(condition),
            Box::new(CleanScalarExpr::Int(1)),
            Box::new(CleanScalarExpr::Bool(false)),
        );
        assert_definition_error(mixed, "if branches have different scalar sorts");
    }

    #[test]
    fn fresh_kernel_decode_covers_multiple_vars_actions_and_invariants() {
        let (artifact, decoded) = extract_clean_scalar_model(SOURCE, "Example.Lockstep")
            .expect("the canonical Clean scalar model must decode");
        assert_eq!(decoded.variables.len(), 2);
        assert_eq!(decoded.actions.len(), 2);
        assert_eq!(decoded.invariants.len(), 2);
        assert!(decoded.actions.iter().all(|action| action.updates.len() == 2));
        let model = decoded.to_model().expect("decoded model remains valid");
        assert!(model.to_tla().contains("Next == Step \\/ Reset"));
        assert!(model.to_tla().contains("Lockstep == x = y"));
        assert_eq!(recheck_clean_scalar_model_artifact(&artifact, SOURCE).unwrap(), decoded);
    }

    #[test]
    fn source_or_elaborated_model_drift_cannot_reuse_artifact() {
        let (artifact, _) = extract_clean_scalar_model(SOURCE, "Example.Lockstep").unwrap();
        let changed = SOURCE.replacen("\"Limit\" 2", "\"Limit\" 3", 1);
        assert!(matches!(
            recheck_clean_scalar_model_artifact(&artifact, &changed),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));

        let unknown = SOURCE.replace(
            "ScalarExpr.add X One",
            "ScalarExpr.add (Trust.Temporal.FiniteModel.ScalarExpr.var \"missing\") One",
        );
        assert!(matches!(
            extract_clean_scalar_model(&unknown, "Example.Lockstep"),
            Err(CleanScalarModelError::Definition(_))
        ));
    }

    #[test]
    fn exact_clean_model_certifies_and_replays_positive_and_buggy_evidence() {
        let certificate = certify_clean_scalar_model_with_ty(
            COMPLETE_AUTHORITY_SOURCE,
            "AuthorityExample.CompleteAuthority",
        )
        .expect("complete finite Clean model must certify");
        recheck_clean_scalar_model_with_ty(&certificate, COMPLETE_AUTHORITY_SOURCE)
            .expect("stored positive and Buggy=1 evidence must replay");

        let mut tampered = certificate;
        tampered.buggy_config_src = tampered.buggy_config_src.replace("Buggy = 1", "Buggy = 0");
        assert!(matches!(
            recheck_clean_scalar_model_with_ty(&tampered, COMPLETE_AUTHORITY_SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));
    }

    #[test]
    fn lockstep_model_serializes_and_replays_s4_authority_and_buggy_witness() {
        let certificate = certify_clean_scalar_model_with_ty(SOURCE, "Example.Lockstep")
            .expect("the documented Lockstep model must certify through the S4 projection");
        let encoded = serde_json::to_vec(&certificate).expect("Lockstep certificate serializes");
        let certificate: CleanScalarModelCertificate =
            serde_json::from_slice(&encoded).expect("Lockstep certificate deserializes");

        let producer =
            tla_check::cert::SafetyCertificate::from_json(&certificate.safety_certificate_json)
                .expect("stored safety evidence remains a real TY certificate");
        assert!(producer.explicit_fixpoint.is_some());
        assert!(producer.var_sorts.is_empty(), "the Clean projection must not rewrite TY JSON");
        assert_eq!(producer.compute_digest(), producer.digest);

        let envelope =
            tla_check::verdict::VerdictEnvelope::from_json(&certificate.buggy_counterexample_json)
                .expect("Lockstep Buggy=1 counterexample envelope parses");
        assert_eq!(
            envelope.violated.as_deref(),
            Some("Lockstep"),
            "Buggy=1 must falsify the documented relational invariant",
        );
        recheck_clean_scalar_model_with_ty(&certificate, SOURCE)
            .expect("the deserialized Lockstep certificate must freshly replay");

        let mut wrong_schema = certificate.clone();
        wrong_schema.schema = "trust.clean-scalar-model/unknown".to_owned();
        assert!(matches!(
            recheck_clean_scalar_model_with_ty(&wrong_schema, SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));

        let mut wrong_source = certificate;
        wrong_source.model.clean_source.push('\n');
        assert!(matches!(
            recheck_clean_scalar_model_with_ty(&wrong_source, SOURCE),
            Err(CleanScalarModelError::ArtifactMismatch(_))
        ));
    }

    #[test]
    fn clean_certification_rejects_missing_nonzero_and_duplicate_buggy_baselines() {
        for (changed, expected) in buggy_baseline_source_variants() {
            match certify_clean_scalar_model_with_ty(&changed, "Example.Lockstep") {
                Err(CleanScalarModelError::Temporal(detail)) => assert!(
                    detail.contains("`Buggy` constant must equal 0") && detail.contains(expected),
                    "expected an exact baseline rejection containing `{expected}`, got `{detail}`"
                ),
                Err(CleanScalarModelError::Definition(detail))
                    if expected == "found duplicates" && detail.contains("duplicate") => {}
                other => panic!(
                    "Clean certification did not reject the invalid Buggy baseline: {other:?}"
                ),
            }
        }
    }

    // ------------------------------------------------------------------
    // Positive near-cap CERTIFIED evidence (the D1 coverage requirement).
    //
    // The vectors below take model classes the pre-2026-07-20 resource caps
    // DECLINED and prove they now convert and certify end-to-end. The retired
    // thresholds are pinned locally so each vector must construct an input
    // strictly beyond what the old lane admitted:
    //   * `MAX_EXPR_DEPTH` was 256 before the expression walks became
    //     iterative (widened to 65_536);
    //   * `MAX_MODEL_NAMES` was 4_096 — the per-model distinct-name preflight
    //     deleted with the String-named certification core;
    //   * `MAX_INTERNED_NAMES` was 16_384 — the process-global interner
    //     budget whose cumulative exhaustion declined otherwise-valid models
    //     based on unrelated earlier conversions.
    // ------------------------------------------------------------------

    const OLD_MAX_EXPR_DEPTH: usize = 256;
    const OLD_MAX_MODEL_NAMES: usize = 4_096;
    const OLD_MAX_INTERNED_NAMES: usize = 16_384;

    /// Destruction is part of the Clean-input production path: both the decoded
    /// tree and its generic certification carrier are dropped after every
    /// certification/replay. Keep the test thread much smaller than the default
    /// harness stack so recursively generated destructor glue would overflow,
    /// while constructing and dropping the deepest admitted left spine.
    #[test]
    fn admitted_expression_depth_drops_both_representations_on_a_small_stack() {
        const SMALL_STACK_BYTES: usize = 64 * 1024;

        std::thread::Builder::new()
            .name("r5-expression-drop-boundary".to_owned())
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let mut decoded = CleanScalarExpr::Int(0);
                for _ in 0..MAX_EXPR_DEPTH {
                    decoded =
                        CleanScalarExpr::Add(Box::new(decoded), Box::new(CleanScalarExpr::Int(1)));
                }
                drop(decoded);

                let mut transported = Expr::<String>::Int(0);
                for _ in 0..MAX_EXPR_DEPTH {
                    transported = Expr::Add(Box::new(transported), Box::new(Expr::Int(1)));
                }
                drop(transported);
            })
            .expect("the operating system must admit a 64 KiB test stack")
            .join()
            .expect("both admitted-depth expression trees must drop without stack overflow");
    }

    /// `add` nodes in the beyond-old-cap chain: strictly beyond the old depth
    /// cap, small enough that kernel elaboration and rendering stay fast.
    const DEEP_ADD_NODES: usize = 300;

    /// `add` nodes in the deep chain certified end-to-end ON EVERY suite run.
    /// The remaining depth ceiling is no longer this crate's admission caps
    /// (every production certification walk and destruction are iterative) but
    /// the pinned ty producer: its
    /// certificate cost climbs steeply past ~16 nodes (~33s here, ~290s at 20,
    /// ~640s at 55, all measured 2026-07-20 in debug), so the always-on vector
    /// sits at the deepest point that keeps the suite fast. The full ceiling
    /// is exercised by the opt-in
    /// [`deepest_transportable_expression_certifies_end_to_end`].
    const DEEP_CERTIFIED_ADD_NODES: usize = 16;

    /// `add` nodes in the deepest chain the CURRENT ty certificate transport
    /// carries end-to-end at all (verified Proved + replay, 2026-07-20):
    /// at 60 nodes and beyond the producer's certificate JSON nests past
    /// serde_json's 128-level recursion guard and certification declines
    /// fail-closed ("recursion limit exceeded") — a completeness ceiling in
    /// the pinned producer's transport, never false proof authority.
    const DEEP_TRANSPORT_CEILING_ADD_NODES: usize = 55;

    /// A minimal model in the exact shape of `clean_scalar_complete.lean`
    /// (guarded bounded counter, `Buggy <= x` invariant broken at init under
    /// the `Buggy = 1` mutant), which the full authority chain accepts.
    /// [`valid_clean_fixture`] is NOT certifiable — its `x == 0` invariant
    /// survives the mutant — so the positive vectors extend this shape.
    fn certifiable_clean_fixture(name: &str) -> CleanScalarModel {
        CleanScalarModel {
            name: name.to_owned(),
            constants: vec![CleanScalarConstant { name: "Buggy".to_owned(), value: 0 }],
            variables: vec![CleanScalarStateVar { name: "x".to_owned(), init: 0 }],
            actions: vec![CleanScalarAction {
                name: "Step".to_owned(),
                guard: Some(CleanScalarExpr::Le(
                    Box::new(CleanScalarExpr::Var("x".to_owned())),
                    Box::new(CleanScalarExpr::Int(2)),
                )),
                updates: vec![CleanScalarUpdate {
                    var: "x".to_owned(),
                    value: CleanScalarExpr::Add(
                        Box::new(CleanScalarExpr::Var("x".to_owned())),
                        Box::new(CleanScalarExpr::Int(1)),
                    ),
                }],
            }],
            invariants: vec![CleanScalarInvariant {
                name: "Safe".to_owned(),
                value: CleanScalarExpr::Le(
                    Box::new(CleanScalarExpr::ConstRef("Buggy".to_owned())),
                    Box::new(CleanScalarExpr::Var("x".to_owned())),
                ),
            }],
        }
    }

    /// A `CompleteAuthority`-shaped machine whose `Step` update is a
    /// left-nested `((x + 1) + 0) + 0 ...` chain of `nodes` additions —
    /// semantically still `x + 1`, structurally as deep as requested. Built as
    /// chained small `def`s so every elaboration and whnf step stays shallow;
    /// only the decoded ScalarExpr tree is deep.
    fn deep_update_clean_source(model: &str, nodes: usize) -> String {
        let p = "Trust.Temporal.FiniteModel";
        let mut source = String::new();
        source.push_str("namespace DeepMigration\n\n");
        source.push_str(&format!("def X : {p}.ScalarExpr := {p}.ScalarExpr.var \"x\"\n"));
        source.push_str(&format!("def Zero : {p}.ScalarExpr := {p}.ScalarExpr.int 0\n"));
        source.push_str(&format!("def One : {p}.ScalarExpr := {p}.ScalarExpr.int 1\n"));
        source.push_str(&format!("def D0 : {p}.ScalarExpr := {p}.ScalarExpr.add X One\n"));
        for index in 1..nodes {
            source.push_str(&format!(
                "def D{index} : {p}.ScalarExpr := {p}.ScalarExpr.add D{} Zero\n",
                index - 1
            ));
        }
        source.push_str(&format!(
            "\ndef {model} : {p}.ScalarModel :=\n  \
             {p}.ScalarModel.mk \"{model}\"\n    \
             [{p}.Constant.mk \"Buggy\" 0]\n    \
             [{p}.StateVar.mk \"x\" 0]\n    \
             [{p}.Action.mk \"Step\"\n       \
             ({p}.Guard.when ({p}.ScalarExpr.le X ({p}.ScalarExpr.int 2)))\n       \
             [{p}.Update.mk \"x\" D{}]]\n    \
             [{p}.Invariant.mk \"Safe\"\n       \
             ({p}.ScalarExpr.le ({p}.ScalarExpr.constRef \"Buggy\") X)]\n\n\
             end DeepMigration\n",
            nodes - 1
        ));
        source
    }

    /// The legacy-lane twin of [`deep_update_clean_source`]: the same machine
    /// authored directly in the legacy carrier. The nesting is beyond what a
    /// literal `trust_model!` invocation could practically spell, so the value
    /// is built programmatically — it is the exact `Model<&'static str>` type
    /// every `trust_model!` expansion produces.
    fn legacy_deep_update_twin(name: &'static str, nodes: usize) -> Model {
        let mut deep = Expr::Add(Box::new(Expr::Var("x")), Box::new(Expr::Int(1)));
        for _ in 1..nodes {
            deep = Expr::Add(Box::new(deep), Box::new(Expr::Int(0)));
        }
        Model {
            name,
            consts: vec![("Buggy", 0)],
            vars: vec![StateVar { name: "x", init: 0 }],
            fn_vars: Vec::new(),
            actions: vec![Action {
                name: "Step",
                guard: Some(Expr::Le(Box::new(Expr::Var("x")), Box::new(Expr::Int(2)))),
                updates: vec![Update { var: "x", expr: deep }],
            }],
            invariants: vec![Invariant {
                name: "Safe",
                expr: Expr::Le(Box::new(Expr::ConstRef("Buggy")), Box::new(Expr::Var("x"))),
            }],
        }
    }

    /// D1 positive vector 1a: an expression tree deeper than the old
    /// `MAX_EXPR_DEPTH` (256) — which the old decoder declined outright at
    /// `Decoder::scalar_expr` — now decodes, converts, passes the shared
    /// certification preflight, and renders byte-identically to its
    /// legacy-lane twin. FULL ty-backed certification of THIS depth is not
    /// run here: the pinned ty producer's recursive spec walks and the
    /// serde_json 128-level guard on its certificate JSON decline such depths
    /// fail-closed (a completeness ceiling in the transport, not proof
    /// authority; the certified companion vector below is
    /// [`deep_certified_expression_certifies_end_to_end_with_legacy_byte_parity`]).
    #[test]
    fn expression_deeper_than_the_old_depth_cap_converts_with_legacy_byte_parity() {
        assert!(DEEP_ADD_NODES > OLD_MAX_EXPR_DEPTH, "the vector must exceed the old cap");
        let source = deep_update_clean_source("DeepUpdate", DEEP_ADD_NODES);
        let (artifact, decoded) = extract_clean_scalar_model(&source, "DeepMigration.DeepUpdate")
            .expect("a decode the old 256-level depth cap declined must now succeed");

        // Prove the decoded update really exceeds the old cap: the chain is
        // left-nested by construction, so its left spine counts the depth.
        let mut depth = 0usize;
        let mut node = &decoded.actions[0].updates[0].value;
        while let CleanScalarExpr::Add(left, _) = node {
            depth += 1;
            node = left;
        }
        assert!(
            depth >= DEEP_ADD_NODES && depth > OLD_MAX_EXPR_DEPTH,
            "decoded update depth {depth} must exceed the old cap {OLD_MAX_EXPR_DEPTH}"
        );

        let clean = decoded.to_model().expect("the deep model must validate");
        crate::validate_model_for_certification(&clean)
            .expect("the shared certification preflight must admit the deep model");
        let legacy = legacy_deep_update_twin("DeepUpdate", DEEP_ADD_NODES);
        assert_eq!(
            clean.to_tla().as_bytes(),
            legacy.to_tla().as_bytes(),
            "the formerly depth-declined model must render byte-identically to its legacy twin"
        );
        assert_eq!(
            clean.to_cfg().as_bytes(),
            legacy.to_cfg().as_bytes(),
            "the formerly depth-declined model's ty config must match its legacy twin"
        );
        recheck_clean_scalar_model_artifact(&artifact, &source)
            .expect("the deep extraction artifact must freshly replay");
    }

    /// Shared body for the two certified deep vectors: full end-to-end
    /// certification — Proved verdict, kernel recheck, Buggy=1 non-vacuity
    /// break, byte parity with the legacy twin, and fresh replay.
    fn assert_deep_chain_certifies(model: &'static str, nodes: usize) {
        let source = deep_update_clean_source(model, nodes);
        let legacy = legacy_deep_update_twin(model, nodes);
        let certificate =
            certify_clean_scalar_model_with_ty(&source, &format!("DeepMigration.{model}")).expect(
                "the deep-chain model must certify end-to-end \
                 (Proved + kernel recheck + Buggy=1 break)",
            );
        assert_eq!(
            certificate.spec_src.as_bytes(),
            legacy.to_tla().as_bytes(),
            "the certified spec bytes must be the legacy twin's bytes"
        );
        assert_eq!(
            certificate.config_src.as_bytes(),
            legacy.to_cfg().as_bytes(),
            "the certified config bytes must be the legacy twin's bytes"
        );
        recheck_clean_scalar_model_with_ty(&certificate, &source)
            .expect("the deep-chain certificate must freshly replay");
    }

    /// D1 positive vector 1b: an expression far deeper than any previously
    /// certified fixture certifies END-TO-END on every suite run. Under the
    /// old recursive walks the guard was `MAX_EXPR_DEPTH`; with this crate's
    /// production certification walks and destruction iterative, the binding
    /// ceiling moved into the pinned ty producer (see
    /// [`DEEP_CERTIFIED_ADD_NODES`] for the measured cost/ceiling data).
    #[test]
    fn deep_certified_expression_certifies_end_to_end_with_legacy_byte_parity() {
        assert_deep_chain_certifies("DeepCertified", DEEP_CERTIFIED_ADD_NODES);
    }

    /// D1 positive vector 1c (opt-in: ~640s in debug): the DEEPEST expression
    /// the current ty certificate transport is verified to carry certifies
    /// end-to-end; a few nodes past [`DEEP_TRANSPORT_CEILING_ADD_NODES`]
    /// (measured at 60) the producer's certificate JSON exceeds serde_json's
    /// 128-level guard and the lane declines fail-closed instead.
    #[test]
    #[ignore = "transport-ceiling evidence, ~640s in debug: run explicitly"]
    fn deepest_transportable_expression_certifies_end_to_end() {
        assert_deep_chain_certifies("DeepCeiling", DEEP_TRANSPORT_CEILING_ADD_NODES);
    }

    /// D1 positive vector 2: a model with more distinct names than the old
    /// `MAX_MODEL_NAMES` (4_096) — which the deleted `to_model` preflight
    /// declined before interning — now converts, renders byte-identically to a
    /// legacy-lane twin, and certifies end-to-end with verdict Proved.
    #[test]
    fn model_with_more_distinct_names_than_the_old_cap_certifies_end_to_end() {
        const EXTRA_CONSTANTS: usize = 4_200;
        let mut wide = certifiable_clean_fixture("WideNames");
        let wide_names: Vec<String> =
            (0..EXTRA_CONSTANTS).map(|index| format!("Wide{index:04}")).collect();
        wide.constants.extend(
            wide_names.iter().map(|name| CleanScalarConstant { name: name.clone(), value: 0 }),
        );

        // Count distinct names over every role the deleted preflight counted.
        let mut distinct = BTreeSet::new();
        distinct.insert(wide.name.as_str());
        distinct.extend(wide.constants.iter().map(|constant| constant.name.as_str()));
        distinct.extend(wide.variables.iter().map(|variable| variable.name.as_str()));
        distinct.extend(wide.actions.iter().map(|action| action.name.as_str()));
        distinct.extend(wide.invariants.iter().map(|invariant| invariant.name.as_str()));
        assert!(
            distinct.len() > OLD_MAX_MODEL_NAMES,
            "the vector must exceed the old {OLD_MAX_MODEL_NAMES}-name cap, got {}",
            distinct.len()
        );

        let clean = wide
            .to_model()
            .expect("the conversion the old 4_096-distinct-name preflight declined must succeed");

        // Legacy-lane twin over borrowed names: same machine, same renderer.
        let mut consts: Vec<(&str, i64)> = vec![("Buggy", 0)];
        consts.extend(wide_names.iter().map(|name| (name.as_str(), 0)));
        let legacy: Model<&str> = Model {
            name: "WideNames",
            consts,
            vars: vec![StateVar { name: "x", init: 0 }],
            fn_vars: Vec::new(),
            actions: vec![Action {
                name: "Step",
                guard: Some(Expr::Le(Box::new(Expr::Var("x")), Box::new(Expr::Int(2)))),
                updates: vec![Update {
                    var: "x",
                    expr: Expr::Add(Box::new(Expr::Var("x")), Box::new(Expr::Int(1))),
                }],
            }],
            invariants: vec![Invariant {
                name: "Safe",
                expr: Expr::Le(Box::new(Expr::ConstRef("Buggy")), Box::new(Expr::Var("x"))),
            }],
        };
        assert_eq!(clean.to_tla().as_bytes(), legacy.to_tla().as_bytes());
        assert_eq!(clean.to_cfg().as_bytes(), legacy.to_cfg().as_bytes());

        let outcome = certify_model(&clean);
        assert_eq!(
            outcome.verdict,
            ModelVerdict::Proved,
            "the formerly name-declined model must reach full Certified authority"
        );
        assert_eq!(outcome.non_vacuity, Some(ModelVerdict::Proved));
        let bound = outcome.bound.expect("Proved requires replayable bound evidence");
        assert!(bound.kernel_rechecked, "positive evidence must be kernel-rechecked");
        bind_model_configuration(&bound, &clean)
            .expect("the wide-name model's certificate configuration must bind exactly");
    }

    /// D1 positive vector 3 (the interner blocker's user-visible symptom,
    /// closed empirically): more than 100 conversions with fresh distinct
    /// names on every iteration. The old process-global interner budget
    /// (16_384) was cumulative across conversions, so this loop used to fail
    /// mid-way regardless of each model's own validity; now every conversion
    /// succeeds with legacy byte-parity, and full end-to-end certification is
    /// spot-checked at the sentinel iterations (first, first-past-the-old-
    /// budget, last — full certification per iteration would only repeat the
    /// identical ty/kernel work ~110 times).
    #[test]
    fn conversions_past_the_old_interner_budget_all_certify() {
        const CONVERSIONS: usize = 110;
        const FRESH_CONSTANTS_PER_CONVERSION: usize = 156;
        assert!(CONVERSIONS > 100, "the vector must run more than 100 conversions");

        let mut cumulative: BTreeSet<String> = BTreeSet::from(["Buggy".to_owned()]);
        let mut first_past_budget = None;
        let mut certified_sentinels = 0usize;
        for index in 0..CONVERSIONS {
            let mut model = certifiable_clean_fixture(&format!("Interner{index:03}"));
            model.variables[0].name = format!("v{index:03}");
            model.actions[0].name = format!("Step{index:03}");
            model.actions[0].updates[0].var = model.variables[0].name.clone();
            model.invariants[0].name = format!("Safe{index:03}");
            let var = || Box::new(CleanScalarExpr::Var(format!("v{index:03}")));
            model.actions[0].guard =
                Some(CleanScalarExpr::Le(var(), Box::new(CleanScalarExpr::Int(2))));
            model.actions[0].updates[0].value =
                CleanScalarExpr::Add(var(), Box::new(CleanScalarExpr::Int(1)));
            model.invariants[0].value =
                CleanScalarExpr::Le(Box::new(CleanScalarExpr::ConstRef("Buggy".to_owned())), var());
            model.constants.extend((0..FRESH_CONSTANTS_PER_CONVERSION).map(|extra| {
                CleanScalarConstant { name: format!("K{index:03}x{extra:03}"), value: 0 }
            }));

            cumulative.insert(model.name.clone());
            cumulative.extend(model.constants.iter().map(|constant| constant.name.clone()));
            cumulative.extend(model.variables.iter().map(|variable| variable.name.clone()));
            cumulative.extend(model.actions.iter().map(|action| action.name.clone()));
            cumulative.extend(model.invariants.iter().map(|invariant| invariant.name.clone()));
            let past_budget = cumulative.len() > OLD_MAX_INTERNED_NAMES;
            if past_budget && first_past_budget.is_none() {
                first_past_budget = Some(index);
            }

            // The conversion the old cumulative budget used to decline.
            let clean = model.to_model().unwrap_or_else(|error| {
                panic!("conversion {index} must succeed with no process-wide budget: {error}")
            });

            // Legacy-lane byte parity on every iteration.
            let legacy: Model<&str> = Model {
                name: &model.name,
                consts: model
                    .constants
                    .iter()
                    .map(|constant| (constant.name.as_str(), constant.value))
                    .collect(),
                vars: vec![StateVar { name: &model.variables[0].name, init: 0 }],
                fn_vars: Vec::new(),
                actions: vec![Action {
                    name: &model.actions[0].name,
                    guard: Some(Expr::Le(
                        Box::new(Expr::Var(&model.variables[0].name)),
                        Box::new(Expr::Int(2)),
                    )),
                    updates: vec![Update {
                        var: &model.variables[0].name,
                        expr: Expr::Add(
                            Box::new(Expr::Var(&model.variables[0].name)),
                            Box::new(Expr::Int(1)),
                        ),
                    }],
                }],
                invariants: vec![Invariant {
                    name: &model.invariants[0].name,
                    expr: Expr::Le(
                        Box::new(Expr::ConstRef("Buggy")),
                        Box::new(Expr::Var(&model.variables[0].name)),
                    ),
                }],
            };
            assert_eq!(clean.to_tla().as_bytes(), legacy.to_tla().as_bytes());
            assert_eq!(clean.to_cfg().as_bytes(), legacy.to_cfg().as_bytes());

            // Full end-to-end certification at the sentinels.
            let sentinel =
                index == 0 || Some(index) == first_past_budget || index == CONVERSIONS - 1;
            if sentinel {
                let outcome = certify_model(&clean);
                assert_eq!(
                    outcome.verdict,
                    ModelVerdict::Proved,
                    "sentinel conversion {index} must certify end-to-end"
                );
                assert_eq!(outcome.non_vacuity, Some(ModelVerdict::Proved));
                let bound = outcome.bound.expect("Proved requires replayable bound evidence");
                assert!(bound.kernel_rechecked);
                bind_model_configuration(&bound, &clean)
                    .expect("sentinel certificate configuration must bind exactly");
                certified_sentinels += 1;
            }
        }
        assert!(
            cumulative.len() > OLD_MAX_INTERNED_NAMES,
            "the loop must exhaust the old {OLD_MAX_INTERNED_NAMES}-name interner budget, \
             got {} distinct names",
            cumulative.len()
        );
        let crossing = first_past_budget
            .expect("the old budget must be crossed inside the loop, not merely at its end");
        assert!(
            (1..CONVERSIONS - 1).contains(&crossing),
            "the old budget must be crossed mid-loop (crossed at {crossing})"
        );
        assert_eq!(certified_sentinels, 3, "all three sentinel certifications must run");
    }
}
