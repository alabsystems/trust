// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `clean { … }` parser-island checking (two-language design E10).
//!
//! The compiler hands this module the island's raw text (recovered from the
//! source map); it parses it with the REAL Clean parser, elaborates and
//! registers every declaration into a kernel [`Environment`] — registration
//! runs the CIC kernel's type check (`add_decl` re-typechecks, the L5 gate) —
//! and reports every failure with island-relative BYTE OFFSETS so the caller
//! can emit source-accurate Rust diagnostics. A rejected island must fail the
//! Rust build; silent acceptance is banned (design §1.2-6).
//!
//! Current surface boundary: rustc still uses a Rust token tree to delimit
//! `clean { ... }` before this checker receives the body. Consequently this is
//! the Rust-tokenizable Clean subset, not arbitrary Lean source: braces inside
//! Lean `--` / `/- -/` comments can terminate the Rust delimiter first. Those
//! forms fail closed in rustc's parser; supporting them requires a dedicated
//! lexer-level opaque-island mode. Quoted braces remain token-tree-safe.

use clean_elab::{
    ElabResult, FileContext, RegistrationWarningKind,
    elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context,
};
use clean_kernel::{ConstantKind, Environment};

// Re-export for the compiler's E9 in-walk discharge, which stashes a clone of
// the island-checked environment in session state (it has no direct
// clean_kernel dependency).
pub use clean_kernel::Environment as KernelEnvironment;

/// One island failure, spanning `start..end` BYTE OFFSETS into the island
/// text (the caller maps these onto the enclosing Rust span).
#[derive(Debug, Clone)]
pub struct CleanIslandDiagnostic {
    pub start: usize,
    pub end: usize,
    pub message: String,
}

/// The outcome of checking one island.
#[derive(Debug, Clone, Default)]
pub struct CleanIslandOutcome {
    /// Names of declarations that elaborated, registered, and kernel-checked.
    pub registered: Vec<String>,
    /// Every failure, with island-relative byte offsets. Non-empty ⇒ the
    /// island is REJECTED and the build must fail.
    pub errors: Vec<CleanIslandDiagnostic>,
}

impl CleanIslandOutcome {
    #[must_use]
    pub fn is_rejected(&self) -> bool {
        !self.errors.is_empty()
    }
}

/// The registered declaration's primary name (mirrors trust-clean's
/// `elab_result_name`; kept local so the island lane has no trust-clean dep).
fn elab_result_name(result: &ElabResult) -> String {
    match result {
        ElabResult::Definition { name, .. }
        | ElabResult::Theorem { name, .. }
        | ElabResult::Axiom { name, .. }
        | ElabResult::Opaque { name, .. }
        | ElabResult::Structure { name, .. }
        | ElabResult::Instance { name, .. }
        | ElabResult::Inductive { name, .. } => name.to_string(),
        ElabResult::MutualInductive { decl, .. } => decl
            .types
            .first()
            .map_or_else(|| "(mutual inductive)".to_string(), |t| t.name.to_string()),
        ElabResult::Failed { name, .. } => name.clone(),
        ElabResult::Example { .. } => "(example)".to_string(),
        _ => "(skipped)".to_string(),
    }
}

/// Turn an authoritative parser byte position into a non-empty, UTF-8-safe
/// source range whenever the input itself is non-empty.
fn point_diagnostic_span(source: &str, at: usize) -> (usize, usize) {
    let mut at = at.min(source.len());
    while at > 0 && !source.is_char_boundary(at) {
        at -= 1;
    }
    if let Some(ch) = source[at..].chars().next() {
        return (at, at + ch.len_utf8());
    }
    source.char_indices().next_back().map_or((0, 0), |(start, ch)| (start, start + ch.len_utf8()))
}

/// The verdict of kernel-unifying a `by <thm>` citation (E9) against a
/// clause's elaborated mathematical statement. A `KernelStatementMatch*`
/// verdict is advisory evidence about that statement only: it never discharges
/// a Rust/TrustIR VC. Both match verdicts are minted BY the kernel:
/// `check_type(term, goal)` performs statement unification (up to definitional
/// equality), while the canonical certification audit rechecks the complete
/// reachable type/value/provenance graph.
#[derive(Debug, Clone)]
pub enum CitationVerdict {
    /// An earlier island was rejected after possibly registering successful
    /// siblings. Positive evidence is forbidden from a partial environment.
    SessionTainted,
    /// The cited theorem's proof term matches the elaborated statement and its
    /// certification audit is clean. This remains non-authoritative for the
    /// Rust VC until the typed TrustIR obligation is bound end-to-end.
    KernelStatementMatchCertified,
    /// The term matches the statement but rests on named assumptions or trust
    /// provenance. This remains non-authoritative for the Rust VC.
    KernelStatementMatchTrusted { closure: Vec<String> },
    /// No declaration with this name is registered (island or prelude).
    TheoremNotFound,
    /// The cited declaration exists but is not a theorem. Definitions,
    /// opaques, and axioms cannot masquerade as theorem citations.
    DeclarationNotTheorem { kind: String },
    /// The cited theorem is marked `unsafe` and is ineligible even for an
    /// advisory statement match.
    UnsafeTheorem,
    /// The cited theorem is marked `partial` and is ineligible even for an
    /// advisory statement match.
    PartialTheorem,
    /// A malformed theorem record has no proof term.
    NoProofTerm,
    /// The clause predicate is outside the elaborable fragment — the
    /// citation cannot be checked, so it confers nothing (fail-closed).
    ClauseOutsideFragment { reason: String },
    /// The strict root judgment or reachable certification audit rejected.
    /// This includes statement drift and provenance/integrity failures; both
    /// are hard citation failures with no fallback.
    StatementOrCertificationRejected { detail: String },
}

/// Kernel-unify one citation: elaborate the clause predicate to a CIC goal
/// (total over the supported fragment, fail-closed outside), look the cited
/// theorem up in `env`, and ask the kernel whether the theorem's term proves
/// the goal. See [`CitationVerdict`].
#[must_use]
pub fn kernel_unify_citation(
    env: &Environment,
    theorem: &str,
    clause_src: &str,
) -> CitationVerdict {
    kernel_unify_citation_typed(env, theorem, clause_src, &[])
}

/// Kernel-unify a citation with EXPLICIT clause variable types
/// (two-language design §1.1 domain-tagged arithmetic). `var_types` maps each
/// free clause variable to an explicit compatibility domain tag (`"u64"`,
/// `"u32"`, `"nat"`, …), and the elaborated statement quantifies over that
/// carrier. The binding set must be exact; in particular, an empty set is
/// valid only for a closed clause. This API does not establish that textual
/// names/tags are the compiler's actual source bindings, so the verdict stays
/// statement-only and never grades a Rust/TrustIR obligation.
#[must_use]
pub fn kernel_unify_citation_typed(
    env: &Environment,
    theorem: &str,
    clause_src: &str,
    var_types: &[(&str, &str)],
) -> CitationVerdict {
    // No facet records: program-fn calls in the clause get the base E6
    // fail-closed diagnostic from the elaborator.
    kernel_unify_citation_typed_with_facets(
        env,
        theorem,
        clause_src,
        var_types,
        &trust_spec_elab::FacetTable::new(),
    )
}

/// Like [`kernel_unify_citation_typed`], with an E6 facet table consulted for
/// program-function calls in the clause. Facets refine the out-of-fragment
/// DIAGNOSTIC only — every call still fails closed until the E6 admission
/// gate (kernel import of a defining equation) lands, so this variant can
/// never mint a verdict the plain one would refuse.
#[must_use]
pub fn kernel_unify_citation_typed_with_facets(
    env: &Environment,
    theorem: &str,
    clause_src: &str,
    var_types: &[(&str, &str)],
    facets: &trust_spec_elab::FacetTable,
) -> CitationVerdict {
    let goal =
        match trust_spec_elab::elaborate_goal_typed_with_facets(clause_src, var_types, facets) {
            Ok(goal) => goal,
            Err(reason) => return CitationVerdict::ClauseOutsideFragment { reason },
        };
    grade_cited_theorem_against_goal(env, theorem, &goal)
}

/// E9 discharge (design note 2026-07-15): grade a cited theorem against the
/// POSTCONDITION goal of an `ensures` clause — `∀ params, Q(params,
/// self_fn_def(params))` from [`trust_spec_elab::elaborate_ensures`], where the
/// return value is the E6-admitted self-function's defining equation (NOT a
/// ∀-closed `result`, which would be the generally-false statement no honest
/// theorem proves). A [`CitationVerdict::KernelStatementMatchCertified`] here is
/// a genuine DISCHARGE: `cert_meter::grade` re-typechecks that the proof term
/// proves this exact goal AND walks its full transitive closure, rejecting any
/// `sorry`/`trustedArith`/non-foundational axiom anywhere in it.
///
/// `param_types` are the parameters ONLY (no `result`; it is substituted).
/// `self_fn_name` must be E6-admitted (enforced inside `elaborate_ensures`).
#[must_use]
pub fn kernel_discharge_ensures_citation(
    env: &Environment,
    theorem: &str,
    clause_src: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &trust_spec_elab::FacetTable,
) -> CitationVerdict {
    let goal =
        match trust_spec_elab::elaborate_ensures(clause_src, param_types, self_fn_name, facets) {
            Ok(goal) => goal,
            Err(reason) => return CitationVerdict::ClauseOutsideFragment { reason },
        };
    // The elaborated goal is the single most useful thing a user can be told
    // when a citation or a defeq discharge fails, and nothing printed it: the
    // author saw "not definitionally equal" or "bindings are not exact" with no
    // way to see the proposition the kernel was actually asked to close. Since
    // a cited theorem must be stated over the COMPILER'S encoding of the body,
    // not seeing that encoding makes the citation lane guess-and-check. This is
    // the cheap stand-in for the unbuilt `targo trust spec --emit clean`.
    if std::env::var_os("TRUST_E9_DEBUG").is_some() {
        eprintln!("TRUST_E9_DEBUG GOAL clause={clause_src:?} goal={goal}");
    }
    grade_cited_theorem_against_goal(env, theorem, &goal)
}

/// R4 §1: the arity (Pi-telescope length of the declared type) of an
/// unfoldable island Definition — what a facet-table [`Admission`] needs so
/// the clause elaborator resolves a CALL to the island name against the
/// kernel constant. Same category discipline as
/// [`island_definition_value`]: non-definitions answer `None`.
#[must_use]
pub fn island_definition_arity(env: &KernelEnvironment, name: &str) -> Option<usize> {
    island_definition_value(env, name)?;
    let info = env.get_const(&clean_kernel::Name::from_string(name))?;
    let mut arity = 0usize;
    let mut ty: &clean_kernel::Expr = &info.type_;
    while let clean_kernel::ExprKind::Pi(_, _, codomain) = ty.kind() {
        arity += 1;
        ty = codomain;
    }
    Some(arity)
}

/// Authenticate an island [`ConstantKind::Definition`] and install the exact
/// facet/admission pair needed to elaborate calls to it.
///
/// This is deliberately stronger than calling [`trust_spec_elab::FacetTable::admit`]:
/// an admission is usable only alongside four certified facets. A strict Clean
/// definition justifies those facets because its body is pure, deterministic,
/// total, and panic-free by the kernel language's semantics, but only after the
/// canonical certification meter rechecks a reflexive judgment rooted at the
/// named constant, which in turn rechecks its type, body, and complete reachable
/// provenance closure. Trusted/unsafe/partial/unchecked definitions therefore
/// fail closed. An existing facet key is also rejected so an island declaration
/// cannot silently shadow or overwrite a Rust program-function identity.
pub fn admit_certified_island_definition(
    env: &KernelEnvironment,
    name: &str,
    facets: &mut trust_spec_elab::FacetTable,
) -> Result<trust_spec_elab::Admission, String> {
    if facets.get(name).is_some() {
        // Re-admitting THE SAME island definition is idempotent, not a
        // collision. A clause may call one definition more than once
        // (`result == f(x) && x == f(x)`), and the per-callee admission loop
        // then reaches it twice; refusing the second attempt aborted the whole
        // discharge with a misleading "collides with an existing
        // program-function facet key".
        //
        // The two cases are distinguishable by the admitted kernel constant:
        // an island definition is admitted under its OWN name, while a program
        // function is admitted under a `trust_import_`-prefixed constant
        // (`kernel_import_name`). So a genuine shadowing of a program-function
        // facet key still fails closed here — only the identical re-admission
        // is allowed through, and it returns the admission already recorded
        // rather than minting a second one.
        if let Some(existing) = facets.admitted(name)
            && existing.kernel_const == name
        {
            return Ok(existing.clone());
        }
        return Err(format!(
            "island definition `{name}` collides with an existing program-function facet key"
        ));
    }
    let kernel_name = clean_kernel::Name::from_string(name);
    let info = env
        .get_const(&kernel_name)
        .ok_or_else(|| format!("island definition `{name}` is not registered"))?;
    if info.kind != ConstantKind::Definition {
        return Err(format!("island declaration `{name}` is not an unfoldable Definition"));
    }
    if info.value.is_none() {
        return Err(format!("island definition `{name}` has no checked body"));
    }
    if !info.level_params.is_empty() {
        return Err(format!(
            "island definition `{name}` is universe-polymorphic, which the clause-call fragment does not support"
        ));
    }
    if env.is_unsafe(&kernel_name) {
        return Err(format!("island definition `{name}` is unsafe"));
    }
    if env.is_partial(&kernel_name) {
        return Err(format!("island definition `{name}` is partial"));
    }
    // `cert_meter::grade` grades proof judgments and therefore (correctly)
    // rejects a data type as its direct `goal`. Root the audit in the
    // proposition `name = name` instead: the term is honest reflexivity, while
    // the named constant in both sides forces the kernel audit to recheck this
    // declaration's type, value, verification provenance, and full transitive
    // dependency closure. This is stronger than checking the detached body
    // alone because the declaration record itself stays in the audited graph.
    let level = clean_kernel::TypeChecker::new(env)
        .infer_sort(&info.type_)
        .map_err(|error| format!("island definition `{name}` has an invalid type: {error:?}"))?;
    let subject = clean_kernel::Expr::const_(kernel_name, Vec::new());
    let goal = clean_kernel::Expr::apps(
        clean_kernel::Expr::const_(
            clean_kernel::Name::from_string("Eq"),
            vec![level.clone()],
        ),
        [info.type_.clone(), subject.clone(), subject.clone()],
    );
    let proof = clean_kernel::Expr::apps(
        clean_kernel::Expr::const_(
            clean_kernel::Name::from_string("Eq.refl"),
            vec![level],
        ),
        [info.type_.clone(), subject],
    );
    match cert_meter::grade(env, &goal, &proof) {
        cert_meter::Grade::Certified => {}
        cert_meter::Grade::Trusted { closure } => {
            return Err(format!(
                "island definition `{name}` depends on trust provenance: {}",
                closure.join(", ")
            ));
        }
        cert_meter::Grade::Rejected { error } => {
            return Err(format!(
                "island definition `{name}` failed its certification audit: {error}"
            ));
        }
    }

    let arity = island_definition_arity(env, name)
        .ok_or_else(|| format!("island definition `{name}` has no supported arity"))?;
    let certified = || trust_spec_elab::FacetStatus::Certified {
        evidence: "clean-island-kernel-definition".to_string(),
    };
    facets.insert(
        name,
        trust_spec_elab::FnFacets {
            pure: certified(),
            total: certified(),
            deterministic: certified(),
            no_panic: certified(),
        },
    );
    let admission = trust_spec_elab::Admission { kernel_const: name.to_string(), arity };
    facets.admit(name, admission.clone());
    Ok(admission)
}

/// R4 §1 (typed-citation discharge; design note §1a): prove an UNCITED
/// ensures clause by KERNEL DEFINITIONAL EQUALITY. The clause elaborates
/// through the exact same `elaborate_ensures` path as the cited-theorem
/// lane (self-admission gate, facet table, prime discipline all included);
/// when the goal is a Pi-telescoped `Eq lhs rhs`, the candidate proof term
/// `fun … => Eq.refl lhs` is CONSTRUCTED to mirror the telescope and handed
/// to the kernel's `check_type` against the goal — the kernel itself judges
/// whether `lhs ≡ rhs` definitionally (unfolding the E6-admitted
/// `trust_import_*` constant on one side and the island definition on the
/// other). No hand-rolled equality, no textual expansion — the divergence
/// battery's forbidden route is structurally unreachable from here: a
/// wrap-vs-Int divergence makes the two sides NOT defeq and the proof term
/// simply fails to check (fail-closed to the rejected verdict).
/// Build the candidate proof term for a telescope-stripped goal.
///
/// `Eq ty lhs rhs` yields `Eq.refl ty lhs` — the kernel then judges whether
/// `lhs ≡ rhs`, which is the whole mechanism.
///
/// A CONJUNCTION is split rather than refused: `And A B` yields
/// `And.intro A B <proof A> <proof B>`, recursively. Without this, writing two
/// facts in one clause (`result == f(x) && result == g(x)`) fell out of the
/// defeq route entirely on a purely syntactic ground — the head was `And`, not
/// `Eq` — even though each conjunct was individually dischargeable. Splitting
/// adds no proving power the kernel did not already have and cannot admit
/// anything it would otherwise refuse: every leaf is still an `Eq.refl` the
/// kernel checks itself, and a single failing conjunct fails the whole term.
fn defeq_proof_for_goal(body: &clean_kernel::Expr) -> Result<clean_kernel::Expr, String> {
    // `And A B` — note this must be tried BEFORE the Eq extraction, since both
    // are two-argument applications and the Eq arm would misread the operands.
    if let clean_kernel::ExprKind::App(and_a_app, b) = body.kind()
        && let clean_kernel::ExprKind::App(and_const, a) = and_a_app.kind()
        && let clean_kernel::ExprKind::Const(and_name, _) = and_const.kind()
        && and_name.to_string() == "And"
    {
        let proof_a = defeq_proof_for_goal(a)?;
        let proof_b = defeq_proof_for_goal(b)?;
        let intro =
            clean_kernel::Expr::const_(clean_kernel::Name::from_string("And.intro"), Vec::new());
        return Ok(clean_kernel::Expr::app(
            clean_kernel::Expr::app(
                clean_kernel::Expr::app(
                    clean_kernel::Expr::app(intro, (**a).clone()),
                    (**b).clone(),
                ),
                proof_a,
            ),
            proof_b,
        ));
    }

    // The head must be `Eq ty lhs rhs` — extract with the goal's OWN levels.
    let clean_kernel::ExprKind::App(eq_lhs_app, _rhs) = body.kind() else {
        return Err("defeq route requires an equality-headed goal".to_string());
    };
    let clean_kernel::ExprKind::App(eq_ty_app, lhs) = eq_lhs_app.kind() else {
        return Err("defeq route requires an equality-headed goal".to_string());
    };
    let clean_kernel::ExprKind::App(eq_const, ty) = eq_ty_app.kind() else {
        return Err("defeq route requires an equality-headed goal".to_string());
    };
    let clean_kernel::ExprKind::Const(eq_name, eq_levels) = eq_const.kind() else {
        return Err("defeq route requires an `Eq`-headed goal".to_string());
    };
    if eq_name.to_string() != "Eq" {
        return Err(format!("defeq route requires `Eq`, found `{eq_name}`"));
    }
    Ok(clean_kernel::Expr::app(
        clean_kernel::Expr::app(
            clean_kernel::Expr::const_(
                clean_kernel::Name::from_string("Eq.refl"),
                eq_levels.to_vec(),
            ),
            (**ty).clone(),
        ),
        (**lhs).clone(),
    ))
}

#[must_use]
pub fn kernel_prove_ensures_by_defeq(
    env: &Environment,
    clause_src: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &trust_spec_elab::FacetTable,
) -> CitationVerdict {
    let goal =
        match trust_spec_elab::elaborate_ensures(clause_src, param_types, self_fn_name, facets) {
            Ok(goal) => goal,
            Err(reason) => return CitationVerdict::ClauseOutsideFragment { reason },
        };
    // The elaborated goal is the single most useful thing a user can be told
    // when a citation or a defeq discharge fails, and nothing printed it: the
    // author saw "not definitionally equal" or "bindings are not exact" with no
    // way to see the proposition the kernel was actually asked to close. Since
    // a cited theorem must be stated over the COMPILER'S encoding of the body,
    // not seeing that encoding makes the citation lane guess-and-check. This is
    // the cheap stand-in for the unbuilt `targo trust spec --emit clean`.
    if std::env::var_os("TRUST_E9_DEBUG").is_some() {
        eprintln!("TRUST_E9_DEBUG GOAL clause={clause_src:?} goal={goal}");
    }
    // Strip the Pi telescope, remembering binders for the mirroring lambda.
    let mut binders: Vec<(clean_kernel::BinderData, clean_kernel::Expr)> = Vec::new();
    let mut body: &clean_kernel::Expr = &goal;
    while let clean_kernel::ExprKind::Pi(bd, domain, codomain) = body.kind() {
        binders.push((*bd, (**domain).clone()));
        body = codomain;
    }
    let refl = match defeq_proof_for_goal(body) {
        Ok(proof) => proof,
        Err(detail) => return CitationVerdict::StatementOrCertificationRejected { detail },
    };
    let proof = binders
        .into_iter()
        .rev()
        .fold(refl, |acc, (bd, domain)| clean_kernel::Expr::lam(bd, domain, acc));
    if clean_kernel::TypeChecker::new(env).check_type(&proof, &goal).is_ok() {
        CitationVerdict::KernelStatementMatchCertified
    } else {
        CitationVerdict::StatementOrCertificationRejected {
            detail: "the two sides are not definitionally equal (Eq.refl does not check)"
                .to_string(),
        }
    }
}

/// Shared, soundness-critical tail: look up the cited theorem, reject a
/// non-theorem / unsafe / partial / proofless declaration, then grade its proof
/// term against `goal` via `cert_meter::grade` (the transitive
/// sorry/axiom-closure + proof-checks-goal audit). `Certified` is the ONLY
/// dischargeable verdict; `Trusted` (axiom/marker-tainted) and `Rejected` are
/// not.
fn grade_cited_theorem_against_goal(
    env: &Environment,
    theorem: &str,
    goal: &clean_kernel::Expr,
) -> CitationVerdict {
    let theorem_name = clean_kernel::Name::from_string(theorem);
    let Some(info) = env.get_const(&theorem_name) else {
        return CitationVerdict::TheoremNotFound;
    };
    if info.kind != ConstantKind::Theorem {
        return CitationVerdict::DeclarationNotTheorem { kind: format!("{:?}", info.kind) };
    }
    if env.is_unsafe(&theorem_name) {
        return CitationVerdict::UnsafeTheorem;
    }
    if env.is_partial(&theorem_name) {
        return CitationVerdict::PartialTheorem;
    }
    let Some(term) = info.value.as_ref() else {
        return CitationVerdict::NoProofTerm;
    };
    match cert_meter::grade(env, goal, term) {
        cert_meter::Grade::Certified => CitationVerdict::KernelStatementMatchCertified,
        cert_meter::Grade::Trusted { closure } => {
            CitationVerdict::KernelStatementMatchTrusted { closure }
        }
        cert_meter::Grade::Rejected { error } => {
            CitationVerdict::StatementOrCertificationRejected { detail: error }
        }
    }
}

/// E6 kernel-import of ONE program function into `env` (design note
/// 2026-07-15-e6-kernel-import-spec): if `func` is admissible in `facet_table`
/// (all four facets certified) AND its body is a recognized elaborator shape,
/// mint the kernel-checked defining equation into `env` and return the
/// `Admission`. Fail-closed (`None`) otherwise — non-admissible, unrecognized
/// shape, out-of-fragment domains, or kernel rejection all mint nothing. Free
/// function (not a session method) so the E9 in-walk discharge can mint a LEAF
/// self-function into a per-body CLONE of the island env without owning a
/// session.
#[must_use]
pub fn admit_function_into(
    env: &mut Environment,
    func: &trust_types::VerifiableFunction,
    facet_table: &trust_spec_elab::FacetTable,
) -> Option<(String, trust_spec_elab::Admission)> {
    use trust_types::admissible_body::{recognize_admissible_body, AdmissibleBody};
    if std::env::var_os("TRUST_E6_DEBUG").is_some() {
        let admissible =
            facet_table.get(&func.def_path).is_some_and(trust_spec_elab::FnFacets::admissible);
        let call_terms: Vec<&str> = func
            .body
            .blocks
            .iter()
            .filter_map(|b| match &b.terminator {
                trust_types::Terminator::Call { func: c, .. } => Some(c.as_str()),
                _ => None,
            })
            .collect();
        eprintln!(
            "TRUST_E6_DEBUG fn={} admissible={} blocks={} arg_count={} calls={:?} recognize={:?}",
            func.def_path,
            admissible,
            func.body.blocks.len(),
            func.body.arg_count,
            call_terms,
            recognize_admissible_body(func),
        );
    }
    if !facet_table.get(&func.def_path).is_some_and(trust_spec_elab::FnFacets::admissible) {
        return None;
    }
    let kernel_const = mangle_kernel_const(&func.def_path);
    let result = match recognize_admissible_body(func)? {
        AdmissibleBody::ConstantUint { value, width_bits } => {
            let (Some(width), Ok(v)) = (machine_width(width_bits), u64::try_from(value)) else {
                return None;
            };
            trust_spec_elab::admit_constant_function(env, &kernel_const, v, width)
        }
        AdmissibleBody::Projection { param } => {
            // Derive every parameter's domain from its declared type; fail
            // closed if any parameter is not a supported machine/bool
            // domain (the projection's return type is the projected
            // parameter's type, which admit_projection_function reads).
            let param_domains = param_domains_of(func)?;
            trust_spec_elab::admit_projection_function(env, &kernel_const, &param_domains, param)
        }
        AdmissibleBody::Select { cmp, cmp_left, cmp_right, then_param, else_param } => {
            let param_domains = param_domains_of(func)?;
            use trust_types::admissible_body::SelectCmp as RecCmp;
            let cmp = match cmp {
                RecCmp::Lt => trust_spec_elab::SelectCmp::Lt,
                RecCmp::Le => trust_spec_elab::SelectCmp::Le,
                RecCmp::Eq => trust_spec_elab::SelectCmp::Eq,
            };
            trust_spec_elab::admit_select_function(
                env,
                &kernel_const,
                &param_domains,
                cmp,
                cmp_left,
                cmp_right,
                then_param,
                else_param,
            )
        }
        AdmissibleBody::Arithmetic { op, left, right } => {
            // admit_expr_function is single-domain (every parameter and
            // the result share one domain).
            let param_domains = param_domains_of(func)?;
            let domain = param_domains.first().cloned()?;
            if !param_domains.iter().all(|d| *d == domain) {
                return None;
            }
            // Build a spec-syntax body over POSITIONAL parameter names
            // (`p0`, `p1`, …) so nothing depends on retained source names:
            // e.g. `wrapping_add(p0, 1)` → `p0 + 1` (machine `+`/`-`/`*` is
            // the wrapping encoding admit_expr_function elaborates — for `-`,
            // the Machine domain's fixed-width wrapping carrier sub, exactly
            // `wrapping_sub`'s unsigned semantics).
            use trust_types::admissible_body::{ArithBinOp, ArithOperand};
            let opnd = |o: ArithOperand| match o {
                ArithOperand::Param(i) => format!("p{i}"),
                ArithOperand::Const(v) => v.to_string(),
            };
            let opstr = match op {
                ArithBinOp::Add => "+",
                ArithBinOp::Sub => "-",
                ArithBinOp::Mul => "*",
            };
            let body = format!("{} {} {}", opnd(left), opstr, opnd(right));
            let names: Vec<String> = (0..func.body.arg_count).map(|i| format!("p{i}")).collect();
            let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
            trust_spec_elab::admit_expr_function(env, &kernel_const, &body, &name_refs, &domain)
        }
        trust_types::admissible_body::AdmissibleBody::Composed { expr } => {
            let param_domains = param_domains_of(func)?;
            let domain = param_domains.first().cloned()?;
            if !param_domains.iter().all(|d| *d == domain) {
                return None;
            }
            // Render the composed tree FULLY PARENTHESIZED so the spec parser
            // reconstructs exactly this tree — precedence can never reshape
            // it — over the same Machine-domain wrapping ops as the
            // single-op arm (faithfulness composes node-for-node).
            use trust_types::admissible_body::{ArithBinOp, ArithExpr, ArithOperand};
            fn render(expr: &ArithExpr) -> String {
                match expr {
                    ArithExpr::Operand(ArithOperand::Param(i)) => format!("p{i}"),
                    ArithExpr::Operand(ArithOperand::Const(v)) => v.to_string(),
                    ArithExpr::Bin { op, left, right } => {
                        let opstr = match op {
                            ArithBinOp::Add => "+",
                            ArithBinOp::Sub => "-",
                            ArithBinOp::Mul => "*",
                        };
                        format!("({} {} {})", render(left), opstr, render(right))
                    }
                }
            }
            let body = render(&expr);
            let names: Vec<String> = (0..func.body.arg_count).map(|i| format!("p{i}")).collect();
            let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
            trust_spec_elab::admit_expr_function(env, &kernel_const, &body, &name_refs, &domain)
        }
    };
    result.ok().map(|admission| (func.def_path.clone(), admission))
}

/// Stateful, crate-local Clean checking session. A crate gets exactly one
/// kernel environment and one file context, so declarations, namespaces,
/// `open`s, notation, and options evolve in source order across islands. The
/// file context permanently disables external `.olean` search: Rust builds
/// may only rely on declarations checked in this Clean-native environment.
pub struct CleanIslandSession {
    env: Environment,
    file_ctx: FileContext,
    tainted: bool,
}

impl Default for CleanIslandSession {
    fn default() -> Self {
        Self::new()
    }
}

impl CleanIslandSession {
    /// Start a strict crate-local session from Clean's built-in prelude.
    #[must_use]
    pub fn new() -> Self {
        let mut file_ctx = FileContext::new();
        file_ctx.disable_external_import_search();
        Self { env: Environment::with_prelude(), file_ctx, tainted: false }
    }

    /// Whether any earlier island in this session was rejected. Elaboration
    /// deliberately reports all sibling failures and can therefore have
    /// registered good declarations before discovering a bad one. A tainted
    /// session must never mint positive citation evidence from that partial
    /// environment (the Rust build is already failing).
    #[must_use]
    pub fn is_tainted(&self) -> bool {
        self.tainted
    }

    /// Strictly parse, elaborate, register, and kernel-check the next island.
    pub fn check(&mut self, source: &str) -> CleanIslandOutcome {
        let outcome = check_clean_island_with_context(source, &mut self.env, &mut self.file_ctx);
        self.tainted |= outcome.is_rejected();
        outcome
    }

    /// E6 kernel-import: for every ADMISSIBLE program function among
    /// `functions`, import its defining equation into this session's kernel
    /// environment and return `(def_path, Admission)` for each one minted. The
    /// caller records these via `FacetTable::admit`, after which a spec that
    /// cites the function elaborates to the imported kernel constant.
    ///
    /// A function is eligible only when `facet_table` certifies all four E6
    /// facets for it AND its body is a shape the recognizer + elaborator handle.
    /// Everything is FAIL-CLOSED: a non-admissible facet record, an unrecognized
    /// body shape, an out-of-fragment width, or a kernel rejection simply mints
    /// nothing for that function — never a wrong or unchecked definition. The
    /// kernel (via `admit_constant_function`'s `add_decl`) is the sole trust
    /// root; the body recognizer's faithfulness is the only added assumption, and
    /// it is deliberately conservative (see
    /// `trust_types::admissible_body::recognize_admissible_body`).
    #[must_use]
    pub fn admit_program_functions(
        &mut self,
        functions: &[trust_types::VerifiableFunction],
        facet_table: &trust_spec_elab::FacetTable,
    ) -> Vec<(String, trust_spec_elab::Admission)> {
        functions
            .iter()
            .filter_map(|func| admit_function_into(&mut self.env, func, facet_table))
            .collect()
    }

    /// Invalidate positive evidence after a caller-side island ingestion
    /// failure (for example, rustc could not recover the island source from
    /// its source map). The session cannot know about failures that happen
    /// before [`Self::check`], but they must have the same fail-closed effect:
    /// later citations cannot consult an incomplete crate environment.
    pub fn invalidate(&mut self) {
        self.tainted = true;
    }

    /// Validate a closed citation against this exact crate-local environment.
    /// A tainted session fails before consulting partially registered state.
    #[must_use]
    pub fn check_citation(&self, theorem: &str, clause_src: &str) -> CitationVerdict {
        self.check_citation_with_facets(theorem, clause_src, &trust_spec_elab::FacetTable::new())
    }

    /// [`Self::check_citation`] with an E6 facet table for program-function
    /// calls in the clause. Diagnostics-only refinement (see
    /// [`kernel_unify_citation_typed_with_facets`]); the tainted-session gate
    /// is identical.
    ///
    /// Uses an EMPTY domain binding — only a closed clause elaborates cleanly.
    /// A clause with free machine-typed variables (`x <= y` over `u64`) needs
    /// [`Self::check_citation_typed_with_facets`], which threads the caller's
    /// parameter type table (two-language design §1.1 domain-tagged
    /// arithmetic).
    #[must_use]
    pub fn check_citation_with_facets(
        &self,
        theorem: &str,
        clause_src: &str,
        facets: &trust_spec_elab::FacetTable,
    ) -> CitationVerdict {
        self.check_citation_typed_with_facets(theorem, clause_src, &[], facets)
    }

    /// [`Self::check_citation_with_facets`] with EXPLICIT clause variable types
    /// (§1.1). `var_types` maps each free clause variable to its compatibility
    /// domain tag (`"u64"`, `"nat"`, …); the elaborated statement quantifies
    /// over that carrier, so a machine-typed citation clause is validated over
    /// the matching UInt domain instead of failing closed as ungroundable.
    /// The tainted-session gate is identical, and the verdict stays
    /// statement-only (it never grades a Rust/TrustIR obligation).
    #[must_use]
    pub fn check_citation_typed_with_facets(
        &self,
        theorem: &str,
        clause_src: &str,
        var_types: &[(&str, &str)],
        facets: &trust_spec_elab::FacetTable,
    ) -> CitationVerdict {
        if self.tainted {
            CitationVerdict::SessionTainted
        } else {
            kernel_unify_citation_typed_with_facets(
                &self.env, theorem, clause_src, var_types, facets,
            )
        }
    }

    /// E9 discharge for an `ensures` clause: grade the cited theorem against the
    /// postcondition goal (`result` bound to the E6-admitted self-function's
    /// defining equation). A [`CitationVerdict::KernelStatementMatchCertified`]
    /// is a genuine kernel discharge of the postcondition VC. Fail-closed while
    /// tainted. `param_types` are the parameters ONLY (no `result`).
    #[must_use]
    pub fn check_ensures_discharge(
        &self,
        theorem: &str,
        clause_src: &str,
        param_types: &[(&str, &str)],
        self_fn_name: &str,
        facets: &trust_spec_elab::FacetTable,
    ) -> CitationVerdict {
        if self.tainted {
            CitationVerdict::SessionTainted
        } else {
            kernel_discharge_ensures_citation(
                &self.env, theorem, clause_src, param_types, self_fn_name, facets,
            )
        }
    }

    /// The crate-local kernel environment, available only while the session
    /// is untainted. Partial island registration must not mint positive
    /// evidence of any kind — certified-monitor evidence included — so a
    /// tainted session yields `None` (the same fail-closed policy as
    /// [`Self::check_citation`]).
    #[must_use]
    pub fn environment(&self) -> Option<&Environment> {
        if self.tainted { None } else { Some(&self.env) }
    }
}

fn registration_debt_label(kind: RegistrationWarningKind) -> &'static str {
    match kind {
        RegistrationWarningKind::ExplicitSorry => "explicit `sorry`",
        RegistrationWarningKind::SyntheticSorry => "synthetic `sorry`",
        RegistrationWarningKind::TrustedArith => "`trustedArith`",
        RegistrationWarningKind::TrustedAy => "`trustedAy`",
    }
}

fn leaf_declaration_names(result: &ElabResult) -> Vec<&clean_kernel::Name> {
    match result {
        ElabResult::MutualInductive { decl, .. } => decl.types.iter().map(|ty| &ty.name).collect(),
        _ => result.declaration_name().into_iter().collect(),
    }
}

/// A fresh, valid kernel constant name for a program function imported under E6.
/// Non-identifier characters of the def-path (`::`, `<`, `>`, spaces, …) become
/// `_`, under a `trust_import_` prefix that namespaces these constants away from
/// prelude and island declarations.
fn mangle_kernel_const(def_path: &str) -> String {
    let sanitized: String =
        def_path.chars().map(|c| if c.is_alphanumeric() { c } else { '_' }).collect();
    format!("trust_import_{sanitized}")
}

/// The machine-integer width for a bit count, or `None` outside the supported
/// widths (which fails the import closed).
fn machine_width(bits: u32) -> Option<trust_spec_elab::MachineUIntWidth> {
    use trust_spec_elab::MachineUIntWidth::{U16, U32, U64, U8};
    Some(match bits {
        8 => U8,
        16 => U16,
        32 => U32,
        64 => U64,
        _ => return None,
    })
}

/// The E6 elaboration [`trust_spec_elab::Domain`] a Rust type carries, or `None`
/// for a type outside the supported fragment (signed integers, floats,
/// references, aggregates, …) — which fails the import closed.
fn ty_to_domain(ty: &trust_types::Ty) -> Option<trust_spec_elab::Domain> {
    use trust_spec_elab::{Domain, MachineUIntWidth};
    match ty {
        trust_types::Ty::Bool => Some(Domain::Bool),
        trust_types::Ty::Int { width, signed: false } => {
            machine_width(*width).map(Domain::Machine)
        }
        trust_types::Ty::PtrSizedInt { signed: false } => Some(Domain::Machine(MachineUIntWidth::U64)),
        _ => None,
    }
}

/// The domains of every value parameter of `func`, in order, or `None` if any
/// parameter's type is outside the supported fragment. Parameters are locals
/// `1..=arg_count` (local `0` is the return place).
fn param_domains_of(
    func: &trust_types::VerifiableFunction,
) -> Option<Vec<trust_spec_elab::Domain>> {
    (1..=func.body.arg_count)
        .map(|i| func.body.locals.iter().find(|l| l.index == i).and_then(|l| ty_to_domain(&l.ty)))
        .collect()
}

/// Enforce the strict island authority policy after kernel registration. The
/// environment may retain the rejected declaration for diagnostics, but the
/// caller taints the whole session and the Rust build fails.
fn strict_leaf_policy_error(env: &Environment, leaf: &ElabResult) -> Option<String> {
    match leaf {
        ElabResult::Axiom { name, .. } => {
            return Some(format!(
                "Clean island declaration `{name}` is an axiom; strict islands require checked proof terms"
            ));
        }
        ElabResult::Opaque { name, val: None, .. } => {
            return Some(format!(
                "Clean island declaration `{name}` is a valueless opaque (an assumption); strict islands require checked bodies"
            ));
        }
        _ => {}
    }

    for name in leaf_declaration_names(leaf) {
        // The `trust_import_` prefix is the compiler's own namespace for E6
        // kernel-imported program functions (`mangle_kernel_const`). An island
        // must never declare into it. Without this check an island could
        // pre-declare `trust_import_crate__f` with a body that is NOT `f`'s;
        // the compiler's later mint for `f` then fails with `DuplicateName`,
        // `admit_function_into` returns `None`, and the island's version stays
        // in the environment under the name every downstream lane believes is
        // the compiler's own import.
        //
        // Today that fails closed further downstream — `elaborate_ensures`
        // gates the self-call on a real admission, so no clause discharges
        // against the impostor. This check moves the refusal to the point of
        // declaration, where the diagnostic names the actual mistake, and stops
        // the environment from ever holding a constant that lies about which
        // Rust function it came from.
        if name.to_string().starts_with("trust_import_") {
            return Some(format!(
                "Clean island declaration `{name}` declares into the compiler's kernel-import \
                 namespace (`trust_import_*`); that namespace is reserved for E6 program-function \
                 imports and an island may not define or shadow a name in it"
            ));
        }
        if env.is_unsafe(name) {
            return Some(format!(
                "Clean island declaration `{name}` is marked `unsafe`; strict islands reject unsafe declarations"
            ));
        }
        if env.is_partial(name) {
            return Some(format!(
                "Clean island declaration `{name}` is marked `partial`; strict islands require total declarations"
            ));
        }
        if let Some(warning) = clean_elab::register::registration_warning_for_name(env, name) {
            return Some(format!(
                "Clean island declaration `{}` uses {}; strict islands reject all trust debt",
                warning.decl_name,
                registration_debt_label(warning.kind)
            ));
        }
    }

    // The strict Clean authority API starts at the actual theorem judgment
    // and rechecks its complete reachable type/value/provenance closure. This
    // catches structural/unchecked/import-recheck/cycle/forged-foundation
    // states that an axiom-name closure cannot see.
    let proof_judgment = match leaf {
        ElabResult::Theorem { name, ty, proof, .. } => Some((name.to_string(), ty, proof)),
        ElabResult::Example { ty, val } => Some(("(example)".to_string(), ty, val)),
        _ => None,
    };
    if let Some((name, ty, proof)) = proof_judgment {
        match cert_meter::grade(env, ty, proof) {
            cert_meter::Grade::Certified => {}
            cert_meter::Grade::Trusted { closure } => {
                return Some(format!(
                    "Clean island proof `{name}` failed the strict certification audit because it depends on trust provenance: {}",
                    closure.join(", ")
                ));
            }
            cert_meter::Grade::Rejected { error } => {
                return Some(format!(
                    "Clean island proof `{name}` failed the strict certification audit: {error}"
                ));
            }
        }
    }
    None
}

/// Crate-private, declaration-only compatibility/test helper. It shares only
/// `env`: every call creates a fresh file context, so namespaces, `open`s,
/// notation, options, import policy state, and taint do **not** persist. It
/// must never implement a crate's multi-island semantics; crate consumers use
/// [`CleanIslandSession`]. Every declaration is attempted after sibling
/// failures so one island reports all errors at once.
#[cfg(test)]
#[must_use]
pub(crate) fn check_clean_island_into(source: &str, env: &mut Environment) -> CleanIslandOutcome {
    let mut file_ctx = FileContext::new();
    file_ctx.disable_external_import_search();
    check_clean_island_with_context(source, env, &mut file_ctx)
}

fn check_clean_island_with_context(
    source: &str,
    env: &mut Environment,
    file_ctx: &mut FileContext,
) -> CleanIslandOutcome {
    let mut outcome = CleanIslandOutcome::default();

    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = match clean_parser::parse_file_with_tactics_located(source, &patterns) {
        Ok(decls) => decls,
        Err(err) => {
            let (start, end) = point_diagnostic_span(source, err.byte_offset);
            outcome.errors.push(CleanIslandDiagnostic {
                start,
                end,
                message: format!("Clean island failed to parse: {err}"),
            });
            return outcome;
        }
    };

    for decl in &decls {
        let span = decl.span();
        let processed = preprocess_decl_with_context(decl, file_ctx);
        match elaborate_decl_and_register_with_context_and_warning(env, &processed, file_ctx) {
            Ok(registered) => {
                // Namespace/section/mutual results can contain arbitrarily
                // nested `Multiple` nodes. Examine every declaration leaf:
                // a successful sibling must not hide a failed or trust-tainted
                // sibling.
                let mut leaves = Vec::new();
                registered.result.leaf_decls(&mut leaves);
                if leaves.is_empty() {
                    continue;
                }
                for leaf in leaves {
                    if let ElabResult::Failed { name, decl, error } = leaf {
                        let failed_span = decl.span();
                        outcome.errors.push(CleanIslandDiagnostic {
                            start: failed_span.start.min(source.len()),
                            end: failed_span.end.min(source.len()),
                            message: format!(
                                "Clean island declaration `{name}` failed to elaborate: {error:?}"
                            ),
                        });
                        continue;
                    }

                    if let Some(message) = strict_leaf_policy_error(env, leaf) {
                        outcome.errors.push(CleanIslandDiagnostic {
                            start: span.start.min(source.len()),
                            end: span.end.min(source.len()),
                            message,
                        });
                        continue;
                    }

                    outcome.registered.push(elab_result_name(leaf));
                }
            }
            Err(err) => {
                outcome.errors.push(CleanIslandDiagnostic {
                    start: span.start.min(source.len()),
                    end: span.end.min(source.len()),
                    message: format!("Clean island declaration rejected: {err:?}"),
                });
            }
        }
    }

    // NOTE: the register path runs the kernel check per declaration and every
    // failure surfaces as `Err` or `ElabResult::Failed` above. The global
    // `kernel_check_failure_count` counter is process-wide and races across
    // concurrent island checks, so it is deliberately NOT consulted here.

    outcome
}

/// Single-island convenience over [`check_clean_island_into`] with a fresh
/// prelude environment.
#[must_use]
pub fn check_clean_island(source: &str) -> CleanIslandOutcome {
    CleanIslandSession::new().check(source)
}

/// R4 §1 (by-citation wiring, ratified 2026-07-22) groundwork: the value
/// expression of an island-registered DEFINITION, for definitional-unfolding
/// discharge — the certify lane substitutes this kernel-checked body in place
/// of the cited symbol and proceeds with the existing recognizers, so no
/// solver ever sees the island name as an uninterpreted function.
///
/// Fail-closed: only [`ConstantKind::Definition`] with a present value
/// qualifies. Theorems are proof-irrelevant (their value is a proof object,
/// not a definitional body), opaques hide their value by declaration, and
/// axioms have none — unfolding any of them as a definition would be a
/// category error, so all return `None` and the caller must refuse the
/// citation rather than guess.
#[must_use]
pub fn island_definition_value<'env>(
    env: &'env KernelEnvironment,
    name: &str,
) -> Option<&'env clean_kernel::Expr> {
    let name = clean_kernel::Name::from_string(name);
    let info = env.get_const(&name)?;
    if info.kind != ConstantKind::Definition {
        return None;
    }
    info.value.as_ref()
}

/// R4 §1(c): kernel-checked definitional unfolding of an island application.
/// Builds `name arg…` as a kernel term, TYPE-CHECKS it in the island
/// environment (fail-closed: an ill-typed application unfolds to nothing),
/// and reduces with the kernel's own WHNF — the kernel PERFORMS the
/// unfolding, so no hand-rolled substitution can diverge from kernel
/// semantics. `None` unless the name is an unfoldable Definition
/// ([`island_definition_value`]'s category discipline) and the application
/// checks. The §1 discharge consumer substitutes the returned term for the
/// cited symbol and proceeds with the existing recognizers.
#[must_use]
pub fn unfold_island_application(
    env: &KernelEnvironment,
    name: &str,
    args: &[clean_kernel::Expr],
) -> Option<clean_kernel::Expr> {
    island_definition_value(env, name)?;
    let kernel_name = clean_kernel::Name::from_string(name);
    let info = env.get_const(&kernel_name)?;
    let tc = clean_kernel::TypeChecker::new(env);
    // `infer_type` is infer-only (App argument checks skipped, matching
    // Lean); the fail-closed gate walks the definition's Pi telescope and
    // CHECKS each argument against its declared domain.
    let mut ty = tc.whnf(&info.type_);
    for arg in args {
        let clean_kernel::ExprKind::Pi(_, domain, codomain) = ty.kind() else {
            return None; // over-application
        };
        tc.check_type(arg, domain).ok()?;
        ty = tc.whnf(&codomain.instantiate(arg));
    }
    let mut app = clean_kernel::Expr::const_(kernel_name, Vec::new());
    for arg in args {
        app = clean_kernel::Expr::app(app, arg.clone());
    }
    Some(tc.whnf(&app))
}

/// The per-clause monitor-artifact status (two-language design §1.1). A spec
/// clause is `Monitored` when a sealed Bool monitor and a kernel-checked
/// equivalence theorem `monitor = true ↔ P` can be constructed; otherwise it
/// is `Unmonitored` with the rejection reason. One-way soundness is insufficient:
/// it would permit a monitor that always returns `false` and therefore does not
/// decide the proposition it claims to enforce.
///
/// The variant name does **not** make this status execution authority. This
/// report-only enum deliberately drops the artifact; the compiler runtime lane
/// separately reconstructs the sealed certificate and binds it to the exact
/// typed clause before inserting a check. This status never changes a verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MonitorStatus {
    /// A certified monitor artifact exists; this status alone cannot execute it.
    Monitored,
    /// No certified monitor could be built; `reason` is the diagnostic.
    Unmonitored { reason: String },
}

impl MonitorStatus {
    /// Whether a certified monitor exists.
    #[must_use]
    pub fn is_monitored(&self) -> bool {
        matches!(self, MonitorStatus::Monitored)
    }
}

/// Compute the [`MonitorStatus`] of a spec clause: build and KERNEL-CERTIFY a
/// monitor artifact via `trust-spec-elab`, reporting whether it certified.
///
/// `predicate` is the clause's Rust boolean-expression text (recovered from the
/// clause span); `var_types` maps each free variable to its Rust type name
/// (e.g. `("x", "u64")`), which resolves the arithmetic domain (§1.1). `env`
/// should be a prelude environment (with any in-scope Clean islands already
/// registered).
///
/// This helper itself is not an input to compiler execution or runtime checking.
/// It NEVER changes a verification verdict; the returned status is report-only
/// and orthogonal to the obligation/proof decision. The compiler lane binds the
/// sealed artifact independently rather than trusting this lossy status.
#[must_use]
pub fn clause_monitor_status(
    env: &Environment,
    predicate: &str,
    var_types: &[(&str, &str)],
) -> MonitorStatus {
    match trust_spec_elab::certify_monitor_typed(env, predicate, var_types) {
        Ok(_certified) => MonitorStatus::Monitored,
        Err(reason) => MonitorStatus::Unmonitored { reason },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admit_program_functions_mints_only_admissible_recognized_bodies() {
        use trust_types::{
            BasicBlock, BlockId, ConstValue, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let constant_fn = |def_path: &str, v: u128| VerifiableFunction {
            name: "f".into(),
            def_path: def_path.into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: Vec::new(),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(v, 64))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        };
        let funcs = [constant_fn("crate::answer", 42), constant_fn("crate::other", 7)];
        // `answer` is admissible on all four facets; `other` is not (NoPanic false).
        let facets = trust_spec_elab::FacetTable::from_structural_facets([
            ("crate::answer", true, true, true, true),
            ("crate::other", true, false, true, true),
        ]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&funcs, &facets);
        assert_eq!(minted.len(), 1, "only the admissible constant is minted: {minted:?}");
        assert_eq!(minted[0].0, "crate::answer");
        assert_eq!(minted[0].1.arity, 0);
        // The mint succeeded, so the kernel accepted the imported defining
        // equation (admit_constant_function returns Ok only on add_decl success).
    }

    #[test]
    fn admit_program_functions_mints_projections() {
        use trust_types::{
            BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        // fn fst(x: u64, y: u64) -> u64 { x }  — returns parameter 0 (local 1).
        let fst = VerifiableFunction {
            name: "fst".into(),
            def_path: "crate::fst".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u64(), name: None },
                    LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::u64(), name: Some("y".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u64(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        };
        let facets =
            trust_spec_elab::FacetTable::from_structural_facets([("crate::fst", true, true, true, true)]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[fst], &facets);
        assert_eq!(minted.len(), 1, "the admissible projection is minted: {minted:?}");
        assert_eq!(minted[0].0, "crate::fst");
        // arity 2 (two parameters); the mint succeeded so the kernel accepted
        // `fun x y => x : u64 -> u64 -> u64`.
        assert_eq!(minted[0].1.arity, 2);
    }

    #[test]
    fn admit_program_functions_mints_select_min2() {
        use trust_types::{
            BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let u = || Ty::u64();
        let asn = |p: usize, rv: Rvalue| Statement::Assign {
            place: Place::local(p),
            rvalue: rv,
            span: SourceSpan::default(),
        };
        // fn min2(a: u64, b: u64) -> u64 { if a < b { a } else { b } }
        let min2 = VerifiableFunction {
            name: "min2".into(),
            def_path: "crate::min2".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: u(), name: None },
                    LocalDecl { index: 1, ty: u(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: u(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: u(), name: None },
                    LocalDecl { index: 4, ty: Ty::Bool, name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![asn(
                            4,
                            Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                        )],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(4)),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(1),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![asn(3, Rvalue::Use(Operand::Copy(Place::local(1))))],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![asn(3, Rvalue::Use(Operand::Copy(Place::local(2))))],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![asn(0, Rvalue::Use(Operand::Copy(Place::local(3))))],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: u(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        };
        let facets = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::min2",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[min2], &facets);
        assert_eq!(minted.len(), 1, "min2 is minted: {minted:?}");
        assert_eq!(minted[0].0, "crate::min2");
        // arity 2; the mint succeeded so the kernel accepted
        // `fun a b => if a < b then a else b : u64 -> u64 -> u64`.
        assert_eq!(minted[0].1.arity, 2);
    }

    /// `fn min2(a: u64, b: u64) -> u64 { if a < b { a } else { b } }` as the
    /// MIR-shaped input the Select recognizer expects.
    fn min2_verifiable_function() -> trust_types::VerifiableFunction {
        use trust_types::{
            BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let u = Ty::u64;
        let asn = |p: usize, rv: Rvalue| Statement::Assign {
            place: Place::local(p),
            rvalue: rv,
            span: SourceSpan::default(),
        };
        VerifiableFunction {
            name: "min2".into(),
            def_path: "crate::min2".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: u(), name: None },
                    LocalDecl { index: 1, ty: u(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: u(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: u(), name: None },
                    LocalDecl { index: 4, ty: Ty::Bool, name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![asn(
                            4,
                            Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                        )],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(4)),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(1),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![asn(3, Rvalue::Use(Operand::Copy(Place::local(1))))],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![asn(3, Rvalue::Use(Operand::Copy(Place::local(2))))],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![asn(0, Rvalue::Use(Operand::Copy(Place::local(3))))],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: u(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        }
    }

    /// THE GOAL (docs/design/2026-07-25-select-encoding-ergonomics.md, RULED):
    /// an island written the way a person writes it —
    /// `if a < b then a else b` — discharges an uncited clause, with no helper
    /// definitions, no `cond`, no `Bool.rec` and no theorem.
    ///
    /// This works because the mint now emits the SAME term Clean's `elab_if`
    /// produces. Both sides are stuck on a neutral `Decidable`, and two
    /// syntactically identical stuck terms are definitionally equal. Under the
    /// previous `Bool.rec`-over-`Nat.ble` mint the two sides were stuck at
    /// different recursors of different inductives and never unified.
    #[test]
    fn natural_if_island_discharges_against_the_minted_select() {
        let min2 = min2_verifiable_function();
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::min2",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[min2], &facet_seed);
        assert_eq!(minted.len(), 1, "min2 must mint: {minted:?}");

        // The island, written naturally. No helpers, no cond, no Bool.rec.
        let outcome = session
            .check("def min_isl (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b");
        assert!(!outcome.is_rejected(), "island must check: {:?}", outcome.errors);

        let mut table = facet_seed.clone();
        for (path, admission) in &minted {
            table.admit(path.clone(), admission.clone());
            if let Some(bare) = path.rsplit("::").next() {
                table.admit(bare.to_string(), admission.clone());
            }
        }
        let env = session.environment().expect("session env").clone();
        // The compiler admits each island definition a clause calls; do the same.
        admit_certified_island_definition(&env, "min_isl", &mut table)
            .expect("the island definition must be admissible");
        let verdict = kernel_prove_ensures_by_defeq(
            &env,
            "result == min_isl(a, b)",
            &[("a", "u64"), ("b", "u64")],
            "crate::min2",
            &table,
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the NATURAL island spelling must discharge; got {verdict:?}"
        );
    }

    #[test]
    fn admit_program_functions_mints_wrapping_arithmetic() {
        use trust_types::{
            BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
            VerifiableBody, VerifiableFunction,
        };
        // fn winc(x: u64) -> u64 { x.wrapping_add(1) }
        let winc = VerifiableFunction {
            name: "winc".into(),
            def_path: "crate::winc".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u64(), name: None },
                    LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: Vec::new(),
                        terminator: Terminator::Call {
                            func: "core::num::<impl u64>::wrapping_add".into(),
                            args: vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ],
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                            unwind: trust_types::UnwindEdge::Unreachable,
                            is_foreign: false,
                            is_unsafe_sig: false,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: Vec::new(),
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::u64(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        };
        let facets = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::winc",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[winc], &facets);
        assert_eq!(minted.len(), 1, "winc is minted: {minted:?}");
        assert_eq!(minted[0].0, "crate::winc");
        // arity 1; the mint succeeded so the kernel accepted `fun p0 => p0 + 1`
        // (the wrapping-add encoding) at u64 -> u64.
        assert_eq!(minted[0].1.arity, 1);
    }

    /// E6 widening increment 3 end-to-end: a composed wrapping call chain
    /// (`fn chain(x: u64) { x.wrapping_add(1).wrapping_mul(2) }`) admits — the
    /// recognizer builds the tree, the fully-parenthesized rendering
    /// `(p0 + 1) * 2` elaborates over the Machine domain, and the REAL kernel
    /// accepts the minted definition.
    #[test]
    fn island_definition_value_unfolds_definitions_only() {
        let mut session = CleanIslandSession::new();
        // NOTE: no axiom case — strict islands reject axioms at registration
        // ("strict islands require checked proof terms"), so the unfolding
        // question never arises for one.
        let outcome = session.check(
            "def unfold_pin (x : Int) : Int := (x * x)\n\n\
             theorem unfold_pin_thm : 0 = 0 := rfl\n\n\
             opaque unfold_pin_opaque : Int := 7",
        );
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        let env = session.environment().expect("untainted session exposes its environment");

        // A Definition unfolds to its kernel-checked body.
        let value = island_definition_value(env, "unfold_pin");
        assert!(value.is_some(), "definition must expose its value for unfolding");

        // Theorems (proof objects), opaques (hidden by declaration), axioms
        // (no value), and absent names all refuse — the citation caller must
        // fail closed rather than unfold a non-definition.
        for refused in ["unfold_pin_thm", "unfold_pin_opaque", "no_such"] {
            assert!(
                island_definition_value(env, refused).is_none(),
                "{refused} must not unfold as a definition"
            );
        }

        // The taint policy composes: after a rejected island, the accessor
        // itself refuses, so no unfolding can draw on the partial state.
        let _ = session.check("theorem bad_pin : True := sorry");
        assert!(session.is_tainted());
        assert!(session.environment().is_none(), "tainted session must expose nothing");
    }

    /// R4 §1 composition pin: an UNCITED ensures clause calling an island
    /// definition discharges by KERNEL DEFEQ when the E6-admitted self
    /// constant and the island def are definitionally equal — and is
    /// REJECTED when they differ (the divergence direction), with the
    /// kernel itself as the only judge (the constructed `Eq.refl` term
    /// either checks against the elaborated goal or it does not).
    #[test]
    fn uncited_island_call_discharges_by_defeq_only_when_bodies_agree() {
        use trust_spec_elab::FacetTable;
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def self_dq (x : UInt64) : UInt64 := x\n\n\
             def same_dq (x : UInt64) : UInt64 := x\n\n\
             def diff_dq (x : UInt64) : UInt64 := UInt64.add x 1",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);

        let mut facets = FacetTable::new();
        for name in ["self_dq", "same_dq", "diff_dq"] {
            let admission = admit_certified_island_definition(&env, name, &mut facets)
                .expect("strict kernel definition must be admitted");
            assert_eq!(admission.arity, 1);
        }
        let params: &[(&str, &str)] = &[("x", "u64")];

        // Agreement: `result == same_dq(x)` — both sides unfold to `x`.
        assert!(
            matches!(
                kernel_prove_ensures_by_defeq(
                    &env,
                    "result == same_dq(x)",
                    params,
                    "self_dq",
                    &facets
                ),
                CitationVerdict::KernelStatementMatchCertified
            ),
            "definitionally-equal bodies must discharge by defeq"
        );

        // Divergence: `result == diff_dq(x)` — bodies differ; the kernel
        // must refuse (this is the semantic class the divergence battery
        // guards: no silent prove when the readings differ).
        assert!(
            matches!(
                kernel_prove_ensures_by_defeq(
                    &env,
                    "result == diff_dq(x)",
                    params,
                    "self_dq",
                    &facets
                ),
                CitationVerdict::StatementOrCertificationRejected { .. }
            ),
            "differing bodies must NOT discharge"
        );

        // A non-equality clause refuses on the route's own gate.
        assert!(
            matches!(
                kernel_prove_ensures_by_defeq(&env, "x >= x", params, "self_dq", &facets),
                CitationVerdict::StatementOrCertificationRejected { .. }
                    | CitationVerdict::ClauseOutsideFragment { .. }
            ),
            "non-Eq goals take no defeq shortcut"
        );
    }

    /// A CONJUNCTIVE clause is split into `And.intro` over per-conjunct
    /// `Eq.refl` rather than refused for having a non-`Eq` head. Before this,
    /// writing two facts in one clause fell out of the defeq route on a purely
    /// syntactic ground even when each conjunct was individually
    /// dischargeable.
    ///
    /// The second assertion is the one that matters: splitting must not become
    /// a way to smuggle a false conjunct through. One failing conjunct fails
    /// the whole term, because every leaf is still an `Eq.refl` the kernel
    /// checks itself.
    #[test]
    fn conjunctive_clause_splits_into_and_intro() {
        use trust_spec_elab::FacetTable;
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def self_dq (x : UInt64) : UInt64 := x\n\n\
             def same_dq (x : UInt64) : UInt64 := x\n\n\
             def diff_dq (x : UInt64) : UInt64 := UInt64.add x 1",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);

        let mut facets = FacetTable::new();
        for name in ["self_dq", "same_dq", "diff_dq"] {
            admit_certified_island_definition(&env, name, &mut facets)
                .expect("strict kernel definition must be admitted");
        }
        let params: &[(&str, &str)] = &[("x", "u64")];

        // Both conjuncts agree definitionally — the whole conjunction discharges.
        assert!(
            matches!(
                kernel_prove_ensures_by_defeq(
                    &env,
                    "result == same_dq(x) && result == same_dq(x)",
                    params,
                    "self_dq",
                    &facets
                ),
                CitationVerdict::KernelStatementMatchCertified
            ),
            "a conjunction of dischargeable conjuncts must discharge"
        );

        // One conjunct diverges — the conjunction must NOT discharge. This is
        // the soundness direction of the split.
        assert!(
            !matches!(
                kernel_prove_ensures_by_defeq(
                    &env,
                    "result == same_dq(x) && result == diff_dq(x)",
                    params,
                    "self_dq",
                    &facets
                ),
                CitationVerdict::KernelStatementMatchCertified
            ),
            "a conjunction with ONE diverging conjunct must not discharge"
        );
    }

    /// Admitting the SAME island definition twice is idempotent. A clause may
    /// name one definition more than once, and the per-callee admission loop
    /// then reaches it twice; the second attempt used to fail with "collides
    /// with an existing program-function facet key" and abort the discharge.
    ///
    /// The genuine collision — an island definition shadowing a program
    /// function's facet key — must still be refused, which is the second half
    /// of this test.
    #[test]
    fn re_admitting_the_same_island_definition_is_idempotent() {
        use trust_spec_elab::{Admission, FacetTable, FacetStatus, FnFacets};
        let mut env = Environment::with_prelude();
        let outcome =
            check_clean_island_into("def ident_isl (x : UInt64) : UInt64 := x", &mut env);
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);

        let mut facets = FacetTable::new();
        let first = admit_certified_island_definition(&env, "ident_isl", &mut facets)
            .expect("first admission must succeed");
        let second = admit_certified_island_definition(&env, "ident_isl", &mut facets)
            .expect("re-admitting the same island definition must be idempotent");
        assert_eq!(first.kernel_const, second.kernel_const);
        assert_eq!(first.arity, second.arity);

        // A PROGRAM FUNCTION already occupying the key is a real collision:
        // its admission is under a `trust_import_`-prefixed constant, so the
        // idempotence path must not fire.
        let mut shadowed = FacetTable::new();
        let certified = || FacetStatus::Certified { evidence: "test".to_string() };
        shadowed.insert(
            "ident_isl",
            FnFacets {
                pure: certified(),
                total: certified(),
                deterministic: certified(),
                no_panic: certified(),
            },
        );
        shadowed.admit(
            "ident_isl",
            Admission { kernel_const: "trust_import_ident_isl".to_string(), arity: 1 },
        );
        assert!(
            admit_certified_island_definition(&env, "ident_isl", &mut shadowed).is_err(),
            "an island definition shadowing a program-function facet key must still be refused"
        );
    }

    /// An island may not declare into `trust_import_*`, the compiler's own
    /// namespace for E6 kernel-imported program functions.
    ///
    /// The hazard this closes: an island that pre-declares
    /// `trust_import_crate__f` with a body that is NOT `f`'s. The compiler's
    /// later mint for `f` fails with `DuplicateName`, `admit_function_into`
    /// returns `None`, and the island's version remains in the environment
    /// under the name every downstream lane treats as the compiler's import.
    /// It failed closed further downstream — `elaborate_ensures` gates the
    /// self-call on a real admission — but the environment should never hold a
    /// constant that lies about which Rust function it came from.
    #[test]
    fn an_island_may_not_declare_into_the_kernel_import_namespace() {
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def trust_import_probe__fst (x : UInt64) (y : UInt64) : UInt64 := y",
            &mut env,
        );
        assert!(
            outcome.is_rejected(),
            "an island declaring into `trust_import_*` must be refused, got {:?}",
            outcome.errors
        );
        assert!(
            outcome.errors.iter().any(|e| e.message.contains("kernel-import namespace")),
            "the diagnostic must name the reserved namespace, got {:?}",
            outcome.errors
        );

        // An ordinary name that merely CONTAINS the prefix elsewhere is fine —
        // the reservation is on the leading namespace, not on the substring.
        let mut env2 = Environment::with_prelude();
        let ok = check_clean_island_into(
            "def my_trust_import_helper (x : UInt64) : UInt64 := x",
            &mut env2,
        );
        assert!(
            !ok.is_rejected(),
            "a name that merely contains the prefix must not be refused, got {:?}",
            ok.errors
        );
    }

    #[test]
    fn island_definition_admission_rejects_collisions_and_trust_debt() {
        use trust_spec_elab::{FacetTable, FnFacets};

        let mut clean_env = Environment::with_prelude();
        let clean =
            check_clean_island_into("def collision_pin (x : UInt64) : UInt64 := x", &mut clean_env);
        assert!(!clean.is_rejected(), "clean island: {:?}", clean.errors);
        let mut collision = FacetTable::new();
        collision.insert("collision_pin", FnFacets::unknown());
        let error = admit_certified_island_definition(&clean_env, "collision_pin", &mut collision)
            .expect_err("an island name must not overwrite a program-function facet key");
        assert!(error.contains("collides"), "{error}");
        assert!(collision.admitted("collision_pin").is_none());

        let mut debt_env = Environment::with_prelude();
        let debt = check_clean_island_into(
            "axiom island_debt : UInt64\n\n\
             def debt_backed (x : UInt64) : UInt64 := island_debt",
            &mut debt_env,
        );
        assert!(debt.is_rejected(), "strict islands must report the injected axiom");
        let mut facets = FacetTable::new();
        let error = admit_certified_island_definition(&debt_env, "debt_backed", &mut facets)
            .expect_err("a definition whose closure reaches an axiom must not be admitted");
        assert!(
            error.contains("trust provenance") || error.contains("certification audit"),
            "{error}"
        );
        assert!(facets.admitted("debt_backed").is_none());

        let mut structural_env = Environment::with_prelude();
        structural_env
            .add_decl_structural(clean_kernel::Declaration::Definition {
                name: clean_kernel::Name::from_string("structural_nat"),
                level_params: Vec::new(),
                type_: clean_kernel::Expr::const_str("Nat"),
                value: clean_kernel::Expr::const_str("Nat.zero"),
                is_reducible: true,
            })
            .expect("install a well-typed but structural-only definition");
        let mut facets = FacetTable::new();
        let error =
            admit_certified_island_definition(&structural_env, "structural_nat", &mut facets)
                .expect_err("structural-only provenance must not mint an island admission");
        assert!(error.contains("certification audit"), "{error}");
        assert!(facets.admitted("structural_nat").is_none());
    }

    /// §1(c) pin: the kernel unfolds an island definition applied to a
    /// literal — the result's head is no longer the cited constant (delta
    /// happened, performed by the kernel itself), an ill-typed application
    /// unfolds to nothing, and non-definitions never unfold.
    #[test]
    fn unfold_island_application_is_kernel_performed() {
        let mut session = CleanIslandSession::new();
        let outcome = session.check("def unfold_app_pin (x : Int) : Int := (x * x)");
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        let env = session.environment().expect("untainted");

        let three = clean_kernel::Expr::app(
            clean_kernel::Expr::const_(clean_kernel::Name::from_string("Int.ofNat"), vec![]),
            clean_kernel::Expr::nat_lit(3),
        );
        let unfolded = unfold_island_application(env, "unfold_app_pin", &[three.clone()])
            .expect("well-typed application must unfold");
        let display = format!("{unfolded:?}");
        assert!(
            !display.contains("unfold_app_pin"),
            "delta must eliminate the cited head: {display}"
        );

        // Ill-typed application (Prop argument to an Int parameter): nothing.
        let bad = clean_kernel::Expr::const_(clean_kernel::Name::from_string("True"), vec![]);
        assert!(unfold_island_application(env, "unfold_app_pin", &[bad]).is_none());

        // Unknown name: nothing.
        assert!(unfold_island_application(env, "no_such_def", &[three]).is_none());
    }

    #[test]
    fn admit_program_functions_mints_composed_wrapping_chain() {
        use trust_types::{
            BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
            VerifiableBody, VerifiableFunction,
        };
        let prim = |callee: &str, args: Vec<Operand>, dest: Place, target: BlockId| {
            Terminator::Call {
                func: callee.into(),
                args,
                dest,
                target: Some(target),
                span: SourceSpan::default(),
                atomic: None,
                unwind: trust_types::UnwindEdge::Unreachable,
                is_foreign: false,
                is_unsafe_sig: false,
            }
        };
        let chain = VerifiableFunction {
            name: "chain".into(),
            def_path: "crate::chain".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u64(), name: None },
                    LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::u64(), name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: Vec::new(),
                        terminator: prim(
                            "core::num::<impl u64>::wrapping_add",
                            vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ],
                            Place::local(2),
                            BlockId(1),
                        ),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: Vec::new(),
                        terminator: prim(
                            "core::num::<impl u64>::wrapping_mul",
                            vec![
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ],
                            Place::local(0),
                            BlockId(2),
                        ),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: Vec::new(),
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::u64(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        };
        let facets = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::chain",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[chain], &facets);
        assert_eq!(minted.len(), 1, "composed chain is minted: {minted:?}");
        assert_eq!(minted[0].0, "crate::chain");
        assert_eq!(minted[0].1.arity, 1);
    }

    #[test]
    fn good_island_registers_and_kernel_checks() {
        let outcome = check_clean_island(
            "def Always (p : Nat -> Prop) : Prop := forall n, p n\n\
             theorem always_unfolds (p : Nat -> Prop) : Always p = Always p := rfl\n",
        );
        assert!(!outcome.is_rejected(), "errors: {:?}", outcome.errors);
        assert!(
            outcome.registered.iter().any(|n| n.contains("Always")),
            "registered: {:?}",
            outcome.registered
        );
    }

    #[test]
    fn ill_typed_island_is_rejected_with_offsets() {
        let src = "def bad : Nat := True\n";
        let outcome = check_clean_island(src);
        assert!(outcome.is_rejected(), "must reject an ill-typed def");
        let err = &outcome.errors[0];
        assert!(err.start < err.end && err.end <= src.len(), "offsets: {err:?}");
    }

    #[test]
    fn parse_error_is_rejected() {
        let outcome = check_clean_island("def : := :=\n");
        assert!(outcome.is_rejected());
    }

    #[test]
    fn parser_recovery_placeholder_is_rejected_at_authoritative_offset() {
        let src = "def good := 0\ndef ??? := !!!\ndef later := 0\n";
        let outcome = check_clean_island(src);
        assert!(outcome.is_rejected(), "recovery must never become accepted source");
        let err = &outcome.errors[0];
        let malformed = src.find("def ???").unwrap();
        assert!(
            err.start >= malformed && err.start < src.find("def later").unwrap(),
            "located recovery offset must point into the malformed declaration: {err:?}"
        );
    }

    #[test]
    fn diagnostic_point_defensively_handles_non_utf8_boundary() {
        let source = "é";
        assert_eq!(point_diagnostic_span(source, 1), (0, 2));
        assert_eq!(point_diagnostic_span(source, usize::MAX), (0, 2));
    }

    #[test]
    fn nested_failed_leaf_rejects_the_whole_island() {
        let outcome = check_clean_island(
            "namespace Nested\n\
               def good : Nat := 0\n\
               def bad : Nat := True\n\
             end Nested\n",
        );
        assert!(outcome.is_rejected(), "nested failure must not hide in Multiple");
        assert!(
            outcome.errors.iter().any(|err| err.message.contains("Nested.bad")),
            "nested failure must be named: {:?}",
            outcome.errors
        );
    }

    #[test]
    fn strict_island_rejects_every_registration_trust_warning() {
        for (source, expected) in [
            ("theorem hole : True := sorry\n", "explicit `sorry`"),
            ("theorem arith_debt : True := trustedArith\n", "`trustedArith`"),
            ("theorem ay_debt : True := trustedAy\n", "`trustedAy`"),
        ] {
            let outcome = check_clean_island(source);
            assert!(outcome.is_rejected(), "trust debt must reject: {source}");
            assert!(
                outcome.errors.iter().any(|err| err.message.contains(expected)),
                "missing {expected} diagnostic: {:?}",
                outcome.errors
            );
        }
        assert_eq!(
            registration_debt_label(RegistrationWarningKind::SyntheticSorry),
            "synthetic `sorry`"
        );
    }

    #[test]
    fn strict_policy_rejects_an_actual_synthetic_sorry_term() {
        use clean_parser::{DeclModifiers, Span, SurfaceDecl, SurfaceExpr, TerminationHints};

        let mut env = Environment::with_prelude();
        env.init_true_false().expect("True/False prelude");
        let mut file_ctx = FileContext::new();
        file_ctx.disable_external_import_search();
        let decl = SurfaceDecl::Theorem {
            span: Span::dummy(),
            name: "synthetic_hole".to_string(),
            universe_params: vec![],
            binders: vec![],
            ty: Box::new(clean_parser::parse_expr("True").expect("type")),
            proof: Box::new(SurfaceExpr::SyntheticSorry(Span::dummy())),
            attrs: vec![],
            termination: TerminationHints::default(),
            modifiers: DeclModifiers::default(),
            where_decls: vec![],
        };
        let registered =
            elaborate_decl_and_register_with_context_and_warning(&mut env, &decl, &mut file_ctx)
                .expect("synthetic fixture registers with explicit debt");
        let error = strict_leaf_policy_error(&env, &registered.result)
            .expect("synthetic sorry must be rejected by strict policy");
        assert!(error.contains("synthetic `sorry`"), "{error}");
    }

    #[test]
    fn nameless_examples_receive_the_same_strict_proof_audit() {
        let clean = check_clean_island("example : 0 = 0 := rfl\n");
        assert!(!clean.is_rejected(), "clean example: {:?}", clean.errors);

        let trusted = check_clean_island("example : True := sorry\n");
        assert!(trusted.is_rejected(), "sorry example must fail strict audit");
        assert!(
            trusted.errors.iter().any(|err| {
                err.message.contains("(example)")
                    && err.message.contains("strict certification audit")
            }),
            "trusted example diagnostics: {:?}",
            trusted.errors
        );
    }

    #[test]
    fn strict_island_rejects_assumptions_and_transitive_assumption_closure() {
        let outcome = check_clean_island(
            "axiom assumed_true : True\n\
             theorem inherited : True := assumed_true\n\
             opaque missing_body : Nat\n",
        );
        assert!(outcome.is_rejected());
        let messages = outcome.errors.iter().map(|err| err.message.as_str()).collect::<Vec<_>>();
        assert!(messages.iter().any(|msg| msg.contains("is an axiom")), "{messages:?}");
        assert!(
            messages
                .iter()
                .any(|msg| msg.contains("strict certification audit")
                    && msg.contains("assumed_true")),
            "{messages:?}"
        );
        assert!(messages.iter().any(|msg| msg.contains("valueless opaque")), "{messages:?}");
    }

    #[test]
    fn one_session_preserves_namespace_and_open_state_across_islands() {
        let mut session = CleanIslandSession::new();
        assert!(!session.file_ctx.external_import_search_enabled());
        let first = session.check(
            "namespace Shared\n\
               theorem zero_eq : 0 = 0 := rfl\n\
             end Shared\n\
             open Shared\n",
        );
        assert!(!first.is_rejected(), "first island: {:?}", first.errors);
        let second = session.check("theorem reused : 0 = 0 := zero_eq\n");
        assert!(!second.is_rejected(), "second island: {:?}", second.errors);

        let duplicate = session.check("theorem reused : 0 = 0 := rfl\n");
        assert!(duplicate.is_rejected(), "duplicate across islands must reject");
        assert!(session.is_tainted());
        assert!(matches!(
            session.check_citation("reused", "0 == 0"),
            CitationVerdict::SessionTainted
        ));
    }

    #[test]
    fn caller_side_ingestion_failure_invalidates_citation_evidence() {
        let mut session = CleanIslandSession::new();
        let outcome = session.check("theorem before_failure : 0 = 0 := rfl\n");
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        assert!(matches!(
            session.check_citation("before_failure", "0 == 0"),
            CitationVerdict::KernelStatementMatchCertified
        ));

        session.invalidate();
        assert!(session.is_tainted());
        assert!(matches!(
            session.check_citation("before_failure", "0 == 0"),
            CitationVerdict::SessionTainted
        ));
    }

    /// E9 machine domain: a citation with u64 var types elaborates the goal
    /// over UInt64 (wrapping) — a distinct goal from the Nat elaboration, so a
    /// Nat theorem does NOT match a machine clause (domain safety, §1.1).
    #[test]
    fn machine_typed_citation_uses_machine_goal() {
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "theorem nat_add_zero : forall (x : Nat), x + 0 = x := fun x => rfl\n",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        // The Nat theorem matches the Nat-domain statement, without acquiring
        // any Rust-VC authority...
        assert!(matches!(
            kernel_unify_citation_typed(&env, "nat_add_zero", "x + 0 == x", &[("x", "nat")]),
            CitationVerdict::KernelStatementMatchCertified
        ));
        // ...but NOT the u64-domain clause (goal quantifies over UInt64, which
        // the Nat proof term does not inhabit) — domain-safe by construction.
        assert!(matches!(
            kernel_unify_citation_typed(&env, "nat_add_zero", "x + 0 == x", &[("x", "u64")]),
            CitationVerdict::StatementOrCertificationRejected { .. }
        ));
    }

    /// E9 DISCHARGE (design note 2026-07-15, piece 3): a cited kernel theorem
    /// that proves the postcondition goal `∀ params, Q(params, self_def(params))`
    /// yields `KernelStatementMatchCertified` — a genuine discharge — while a
    /// wrong statement or an un-admitted self-fn fails closed. The discharge
    /// reuses `cert_meter::grade`, so the transitive sorry/axiom firewall + the
    /// proof-checks-goal audit apply exactly as for advisory citations.
    #[test]
    fn ensures_citation_discharges_a_kernel_proved_postcondition() {
        use trust_spec_elab::{Admission, FacetStatus, FacetTable, FnFacets};
        let mut env = Environment::with_prelude();
        // Author the postcondition's proof in a clean island (real Clean parser;
        // a bad proof term would make this island `is_rejected`).
        let outcome = check_clean_island_into(
            "theorem u64_ge_refl : forall (x : UInt64), \
             Nat.le (UInt64.toNat x) (UInt64.toNat x) := \
             fun x => Nat.le.refl (UInt64.toNat x)\n",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);

        // `fn identity(x: u64) -> u64 { x }` is E6-admissible (all four facets).
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let admissible =
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let mut facets = FacetTable::new();
        facets.insert("identity", admissible);
        facets.admit("identity", Admission { kernel_const: "identity".to_string(), arity: 1 });
        let params: &[(&str, &str)] = &[("x", "u64")];

        // DISCHARGE: the u64 reflexivity theorem proves `ensures x >= x`.
        assert!(
            matches!(
                kernel_discharge_ensures_citation(
                    &env, "u64_ge_refl", "x >= x", params, "identity", &facets
                ),
                CitationVerdict::KernelStatementMatchCertified
            ),
            "reflexivity theorem must DISCHARGE `ensures x >= x`"
        );

        // FALSIFICATION — wrong statement: a `>=` proof must NOT discharge `> `
        // (the strict-order goal is a different proposition the proof does not
        // inhabit).
        assert!(
            matches!(
                kernel_discharge_ensures_citation(
                    &env, "u64_ge_refl", "x > x", params, "identity", &facets
                ),
                CitationVerdict::StatementOrCertificationRejected { .. }
            ),
            "a `>=` proof must NOT discharge a strict `>` postcondition"
        );

        // A RESULT-FREE clause is a ∀-params statement independent of the
        // function's body: its kernel proof covers the postcondition for ANY
        // body, so it discharges even on an un-admitted self-fn (d15ef437618;
        // the elaborator requires the self-admission gate only when `result`
        // must be substituted with the defining equation).
        assert!(
            matches!(
                kernel_discharge_ensures_citation(
                    &env, "u64_ge_refl", "x >= x", params, "not_admitted", &facets
                ),
                CitationVerdict::KernelStatementMatchCertified
            ),
            "a result-free ∀-params clause discharges on any body"
        );

        // FALSIFICATION — un-admitted self-fn with a RESULT-mentioning clause:
        // `result` has no kernel denotation without the E6-admitted defining
        // equation, so this must fail closed even with a valid cited theorem.
        assert!(
            matches!(
                kernel_discharge_ensures_citation(
                    &env, "u64_ge_refl", "result >= x", params, "not_admitted", &facets
                ),
                CitationVerdict::ClauseOutsideFragment { .. }
            ),
            "un-admitted self-fn must fail closed when the clause mentions result"
        );

        // FALSIFICATION — unknown theorem: fail closed.
        assert!(
            matches!(
                kernel_discharge_ensures_citation(
                    &env, "no_such_thm", "x >= x", params, "identity", &facets
                ),
                CitationVerdict::TheoremNotFound
            ),
            "unknown cited theorem must fail closed"
        );
    }

    /// E9 end-to-end: an island theorem whose statement matches the clause's
    /// elaborated statement MATCHES it (kernel-unified, clean canonical audit);
    /// a mismatched theorem is a citation FAILURE; unknown names and
    /// out-of-fragment clauses confer nothing.
    #[test]
    fn citation_kernel_unification() {
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into("theorem zero_eq_thm : 0 = 0 := rfl\n", &mut env);
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);

        // Matching statement: kernel unifies and the canonical audit is clean.
        match kernel_unify_citation(&env, "zero_eq_thm", "0 == 0") {
            CitationVerdict::KernelStatementMatchCertified => {}
            other => panic!("matching citation must report a certified match, got {other:?}"),
        }
        // Mismatched statement: the kernel rejects — citation failure.
        match kernel_unify_citation(&env, "zero_eq_thm", "0 <= 0") {
            CitationVerdict::StatementOrCertificationRejected { .. } => {}
            other => panic!("mismatch must fail the strict statement audit, got {other:?}"),
        }
        // Unknown theorem.
        match kernel_unify_citation(&env, "no_such_thm", "0 == 0") {
            CitationVerdict::TheoremNotFound => {}
            other => panic!("unknown name must be TheoremNotFound, got {other:?}"),
        }
        // Out-of-fragment clause text.
        match kernel_unify_citation(&env, "zero_eq_thm", "result <= x + 1") {
            CitationVerdict::ClauseOutsideFragment { .. } => {}
            other => panic!("out-of-fragment must fail closed, got {other:?}"),
        }
    }

    #[test]
    fn citations_require_a_safe_total_theorem_declaration() {
        let mut env = Environment::with_prelude();
        let definition = check_clean_island_into("def proof_shaped_def : 0 = 0 := rfl\n", &mut env);
        assert!(!definition.is_rejected(), "definition: {:?}", definition.errors);
        assert!(matches!(
            kernel_unify_citation(&env, "proof_shaped_def", "0 == 0"),
            CitationVerdict::DeclarationNotTheorem { .. }
        ));

        let unsafe_theorem =
            check_clean_island_into("unsafe theorem unsafe_zero : 0 = 0 := rfl\n", &mut env);
        assert!(unsafe_theorem.is_rejected(), "strict islands must reject unsafe theorems");
        assert!(matches!(
            kernel_unify_citation(&env, "unsafe_zero", "0 == 0"),
            CitationVerdict::UnsafeTheorem
        ));

        let partial_theorem =
            check_clean_island_into("partial theorem partial_zero : 0 = 0 := rfl\n", &mut env);
        assert!(partial_theorem.is_rejected(), "strict islands must reject partial theorems");
        assert!(matches!(
            kernel_unify_citation(&env, "partial_zero", "0 == 0"),
            CitationVerdict::PartialTheorem
        ));
    }

    #[test]
    fn clause_monitor_status_bridges_the_monitor_lane() {
        let env = Environment::with_prelude();
        // A monitorable clause (Nat comparison / conjunction / negation, and a
        // machine-int equality) reports Monitored.
        for (spec, types) in [
            ("x <= y", vec![("x", "nat"), ("y", "nat")]),
            ("x <= y && x == z", vec![("x", "nat"), ("y", "nat"), ("z", "nat")]),
            ("!(x == y)", vec![("x", "nat"), ("y", "nat")]),
            ("x == y", vec![("x", "u64"), ("y", "u64")]),
        ] {
            assert!(
                clause_monitor_status(&env, spec, &types).is_monitored(),
                "`{spec}` should be Monitored"
            );
        }
        // A non-propositional fragment reports Unmonitored (never a verdict).
        match clause_monitor_status(&env, "x + y", &[("x", "nat"), ("y", "nat")]) {
            MonitorStatus::Unmonitored { reason } => assert!(!reason.is_empty()),
            MonitorStatus::Monitored => panic!("`x + y` is not a proposition"),
        }
        // An unsupported variable type also fails closed to Unmonitored.
        assert!(!clause_monitor_status(&env, "x == y", &[("x", "String")]).is_monitored());
        // Missing names never default to Nat or borrow another binding.
        assert!(!clause_monitor_status(&env, "x == y", &[("x", "u64")]).is_monitored());
    }

    #[test]
    fn typed_citation_threads_var_types_where_untyped_fails_closed() {
        // E6/§1.1 seam: a machine-typed free-variable citation clause needs the
        // caller's var_types. The untyped `check_citation_with_facets` path
        // (empty binding) cannot ground `x <= y`, so it never yields a positive
        // statement match; the typed path elaborates over the u64 domain.
        let mut session = CleanIslandSession::new();
        // Register a trivially-true theorem the clause could cite.
        let outcome = session.check("theorem le_refl_u64 : True := True.intro");
        assert!(!outcome.is_rejected(), "prelude theorem must register: {outcome:?}");

        let facets = trust_spec_elab::FacetTable::new();
        // Untyped path: `x <= y` cannot elaborate without domains → outside the
        // exact statement fragment (never a positive match).
        let untyped = session.check_citation_with_facets("le_refl_u64", "x <= y", &facets);
        assert!(
            matches!(untyped, CitationVerdict::ClauseOutsideFragment { .. }),
            "untyped free-var clause must fail closed: {untyped:?}"
        );
        // Typed path: the same clause elaborates over u64 (it no longer fails
        // for want of a domain — the verdict is now a real statement judgment,
        // not an out-of-fragment rejection).
        let typed = session.check_citation_typed_with_facets(
            "le_refl_u64",
            "x <= y",
            &[("x", "u64"), ("y", "u64")],
            &facets,
        );
        assert!(
            !matches!(typed, CitationVerdict::ClauseOutsideFragment { .. }),
            "typed clause must elaborate (not out-of-fragment): {typed:?}"
        );
    }
}
