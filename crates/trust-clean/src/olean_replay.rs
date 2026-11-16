//! Fresh, axiom-free replay of an explicitly inventoried ordinary declaration batch.
//!
//! Local type/value checks in an already populated imported environment cannot
//! establish its consistency: a theorem can cite itself or an invalid dependency.
//! This entry point never receives or copies that environment. Every admitted
//! declaration passes `Environment::add_decl` against earlier checked declarations.
//! An incomplete batch exposes no checked environment, even if a prefix passed.
//!
//! This is a kernel-replay building block, not an `.olean` loader, source-byte
//! attestation, complete external dependency census, or source-to-Trust-IR proof.
//! Inductive families/recursors and runtime primitives require separate checked
//! reconstruction; callers must not turn them into ordinary or bodyless entries.
//! Resource limits bound declaration/Expr occurrence counts and kernel heartbeats,
//! not wire parsing, Name/Level graph size, recursive stack depth, or wall time.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use clean_kernel::env::{Declaration, DeclarationVerification, Environment};
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;
use serde::Serialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum DeclarationSafety {
    Safe,
    Unsafe,
    Partial,
    Unmeasured,
}

/// The caller must retain the complete input inventory, including refused kinds.
/// `Unsupported` is a row, not permission to drop an imported declaration.
#[derive(Clone, Debug)]
pub enum ReplayInput {
    Ordinary { declaration: Declaration, safety: DeclarationSafety },
    Unsupported { name: Name, kind: String },
}

impl ReplayInput {
    pub fn name(&self) -> &Name {
        match self {
            Self::Ordinary { declaration, .. } => declaration_parts(declaration).0,
            Self::Unsupported { name, .. } => name,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ReplayLimits {
    pub declarations: usize,
    pub expression_nodes: usize,
    pub kernel_heartbeats_per_declaration: u32,
}

impl Default for ReplayLimits {
    fn default() -> Self {
        Self {
            declarations: 100_000,
            expression_nodes: 1_000_000,
            kernel_heartbeats_per_declaration: 100_000,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum ReplayFailure {
    DuplicateIdentity,
    UnsafeOrUnmeasured(DeclarationSafety),
    UnsupportedKind(String),
    UnauthorizedAxiom,
    UnsupportedExpression,
    ExpressionBudget,
    MissingDependency(Name),
    FailedDependency(Name),
    /// At least one cycle remains in the prerequisite graph. A dependent of a
    /// cycle has this same incomplete status; it is not falsely called cyclic.
    UnresolvedDependencyCycle,
    KernelRejected(String),
    KernelDidNotRetainCheckedDeclaration,
}

#[derive(Clone, Debug, Serialize)]
pub struct ReplayRow {
    pub input_index: usize,
    pub name: Name,
    pub dependencies: BTreeSet<Name>,
    pub kernel_checked: bool,
    pub failures: Vec<ReplayFailure>,
}

#[derive(Debug, Serialize)]
pub struct ReplayReport {
    pub schema: &'static str,
    pub supplied_declarations: usize,
    pub supplied_expected_identities: usize,
    pub inventory_errors: Vec<String>,
    pub rows: Vec<ReplayRow>,
}

/// Not deserializable or caller-constructible. The report is diagnostic; only
/// the private successful construction stores a fresh checked environment.
pub struct FreshReplay {
    report: ReplayReport,
    checked: Option<Environment>,
}

impl FreshReplay {
    pub fn report(&self) -> &ReplayReport {
        &self.report
    }
    pub fn checked_environment(&self) -> Option<&Environment> {
        self.checked.as_ref()
    }
}

fn declaration_parts(declaration: &Declaration) -> (&Name, &Expr, Option<&Expr>) {
    match declaration {
        Declaration::Definition { name, type_, value, .. }
        | Declaration::Theorem { name, type_, value, .. }
        | Declaration::Opaque { name, type_, value, .. } => (name, type_, Some(value)),
        Declaration::Axiom { name, type_, .. } => (name, type_, None),
    }
}

fn dependencies(
    expressions: &[&Expr],
    remaining: &mut usize,
) -> Result<BTreeSet<Name>, ReplayFailure> {
    let mut result = BTreeSet::new();
    let mut pending = expressions.to_vec();
    while let Some(expression) = pending.pop() {
        *remaining = remaining.checked_sub(1).ok_or(ReplayFailure::ExpressionBudget)?;
        match expression.kind() {
            ExprKind::BVar(_) | ExprKind::Sort(_) => {}
            ExprKind::Const(name, _) => {
                result.insert(name.clone());
            }
            ExprKind::App(left, right)
            | ExprKind::Lam(_, left, right)
            | ExprKind::Pi(_, left, right) => {
                pending.push(left);
                pending.push(right);
            }
            ExprKind::Let(_, ty, value, body, _) => {
                pending.push(ty);
                pending.push(value);
                pending.push(body);
            }
            ExprKind::MData(_, value) => pending.push(value),
            ExprKind::Proj(name, _, value) => {
                result.insert(name.clone());
                pending.push(value);
            }
            // Literal typing has implicit runtime/type dependencies. Until
            // those are reconstructed, do not pretend the explicit Const scan
            // supplies a complete dependency set. Extension modes are likewise
            // outside this constructive replay entry point.
            _ => return Err(ReplayFailure::UnsupportedExpression),
        }
    }
    Ok(result)
}

/// Check the exact supplied population, not a chosen subset of emitted rows.
/// Expected identities must match input identities bijectively. They are a
/// supplied inventory, not independently authenticated source completeness.
pub fn replay_closed_declarations(
    inputs: &[ReplayInput],
    expected: &[Name],
    limits: ReplayLimits,
) -> FreshReplay {
    let mut report = ReplayReport {
        schema: "trust.lean.fresh-ordinary-replay/v1",
        supplied_declarations: inputs.len(),
        supplied_expected_identities: expected.len(),
        inventory_errors: Vec::new(),
        rows: Vec::new(),
    };
    if inputs.len() > limits.declarations || expected.len() > limits.declarations {
        report
            .inventory_errors
            .push("declaration inventory exceeds the explicit resource limit".into());
        return FreshReplay { report, checked: None };
    }
    if limits.kernel_heartbeats_per_declaration == 0 {
        report.inventory_errors.push(
            "kernel heartbeat limit must be positive; zero disables the underlying check".into(),
        );
        return FreshReplay { report, checked: None };
    }
    if inputs.is_empty() || expected.is_empty() {
        report
            .inventory_errors
            .push("empty declaration or expected inventory is not an admitted batch".into());
    }
    let mut indices: BTreeMap<Name, Vec<usize>> = BTreeMap::new();
    for (index, input) in inputs.iter().enumerate() {
        indices.entry(input.name().clone()).or_default().push(index);
    }
    let expected_set: BTreeSet<_> = expected.iter().cloned().collect();
    if expected_set.len() != expected.len() {
        report.inventory_errors.push("duplicate expected identity".into());
    }
    if expected_set != indices.keys().cloned().collect() {
        report.inventory_errors.push("expected and supplied declaration identities differ".into());
    }
    let mut remaining = limits.expression_nodes;
    for (index, input) in inputs.iter().enumerate() {
        let mut row = ReplayRow {
            input_index: index,
            name: input.name().clone(),
            dependencies: BTreeSet::new(),
            kernel_checked: false,
            failures: Vec::new(),
        };
        if indices[&row.name].len() != 1 {
            row.failures.push(ReplayFailure::DuplicateIdentity);
        }
        match input {
            ReplayInput::Unsupported { kind, .. } => {
                row.failures.push(ReplayFailure::UnsupportedKind(kind.clone()))
            }
            ReplayInput::Ordinary { declaration, safety } => {
                if *safety != DeclarationSafety::Safe {
                    row.failures.push(ReplayFailure::UnsafeOrUnmeasured(*safety));
                }
                let (_, ty, value) = declaration_parts(declaration);
                if value.is_none() {
                    row.failures.push(ReplayFailure::UnauthorizedAxiom);
                }
                let mut expressions = vec![ty];
                if let Some(value) = value {
                    expressions.push(value);
                }
                match dependencies(&expressions, &mut remaining) {
                    Ok(dependencies) => row.dependencies = dependencies,
                    Err(error) => row.failures.push(error),
                }
            }
        }
        for dependency in &row.dependencies {
            if !indices.contains_key(dependency) {
                row.failures.push(ReplayFailure::MissingDependency(dependency.clone()));
            }
        }
        report.rows.push(row);
    }
    // Kahn ordering over every exact input row. Failed prerequisites are still
    // processed as failures, so no downstream declaration borrows their types.
    let mut incoming = vec![0usize; inputs.len()];
    let mut users = vec![Vec::new(); inputs.len()];
    for (index, row) in report.rows.iter().enumerate() {
        for dependency in &row.dependencies {
            if let Some(providers) = indices.get(dependency) {
                for provider in providers {
                    incoming[index] += 1;
                    users[*provider].push(index);
                }
            }
        }
    }
    let mut ready: VecDeque<_> =
        incoming.iter().enumerate().filter_map(|(index, n)| (*n == 0).then_some(index)).collect();
    let mut processed = vec![false; inputs.len()];
    // `new`/`with_prelude` would install additional declarations. Default is
    // empty: no imported environment, provisional headers, axiom stubs, native
    // reducer registrations or caller-supplied origin flags are copied.
    let mut checked = Environment::default();
    checked.set_option(
        "maxHeartbeats".into(),
        Some(limits.kernel_heartbeats_per_declaration.to_string()),
    );
    while let Some(index) = ready.pop_front() {
        let dependencies = report.rows[index].dependencies.clone();
        for dependency in dependencies {
            if let Some(providers) = indices.get(&dependency) {
                if providers.iter().any(|provider| !report.rows[*provider].kernel_checked) {
                    report.rows[index].failures.push(ReplayFailure::FailedDependency(dependency));
                }
            }
        }
        if report.rows[index].failures.is_empty() {
            if let ReplayInput::Ordinary { declaration, .. } = &inputs[index] {
                match checked.add_decl(declaration.clone()) {
                    Ok(()) => {
                        let (name, ty, value) = declaration_parts(declaration);
                        let exact = checked.get_const(name).is_some_and(|constant| {
                            &constant.type_ == ty && constant.value.as_ref() == value
                        });
                        if exact
                            && checked.declaration_verification(name)
                                == Some(DeclarationVerification::FullKernelCheck)
                        {
                            report.rows[index].kernel_checked = true;
                        } else {
                            report.rows[index]
                                .failures
                                .push(ReplayFailure::KernelDidNotRetainCheckedDeclaration);
                        }
                    }
                    Err(error) => report.rows[index]
                        .failures
                        .push(ReplayFailure::KernelRejected(format!("{error:?}"))),
                }
            }
        }
        processed[index] = true;
        for user in &users[index] {
            incoming[*user] -= 1;
            if incoming[*user] == 0 {
                ready.push_back(*user);
            }
        }
    }
    for (index, was_processed) in processed.iter().enumerate() {
        if !was_processed {
            report.rows[index].failures.push(ReplayFailure::UnresolvedDependencyCycle);
        }
    }
    let complete =
        report.inventory_errors.is_empty() && report.rows.iter().all(|row| row.kernel_checked);
    FreshReplay { report, checked: complete.then_some(checked) }
}

#[cfg(test)]
#[path = "olean_replay/tests.rs"]
mod tests;
