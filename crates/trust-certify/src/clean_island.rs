// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-10-17; do not grow casually
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
// Re-export for the compiler's E9 in-walk discharge, which stashes a clone of
// the island-checked environment in session state (it has no direct
// clean_kernel dependency).
pub use clean_kernel::Environment as KernelEnvironment;
use clean_kernel::{ConstantKind, Environment};
pub use continuation::PreparedCleanIslandBatch;
pub use model_check::{
    CleanIslandBinding, CleanIslandModelCheck, CleanIslandModelVerdict, CleanIslandSeal,
    DEFAULT_STATE_BUDGET, HEARTBEATS_PER_WORK, KERNEL_WORK_LIMIT, OPT_IN_SECONDS,
};
pub use model_trace::{CleanIslandModelStep, CleanIslandModelTruncation};
pub(crate) use trust_spec_elab::e6_import::ty_to_domain;
use trust_spec_elab::e6_import::{
    admit_e6_only_body, machine_width, param_domains_of, signed_machine_width,
};

// Trust (E6 expansion I0): which E6 gate refused a function, for the refusal
// a user sees. Diagnostics only.
mod continuation;
mod e6_refusal;
mod ensures_evidence;
mod exact_admission;
mod extern_proof;
mod island_forwarding;
mod keyed_env;
mod model_check;
mod model_progress;
mod model_trace;
// Trust (ref-self I1): minting the import of a borrow-erased PARAMETER VIEW.
mod param_view;

#[cfg(test)]
mod reference_fence_tests;

#[cfg(test)]
mod import_disclosure_tests;

#[cfg(test)]
mod registered_carrier_tests;

// Trust (E9-ODT-FACE-SELF-CALL-1): the E9 self-call over TG11's ODT imports.
#[cfg(test)]
mod odt_self_call_tests;

pub use e6_refusal::{
    E6_IMPORTABLE_SHAPES, E6_SCALAR_CARRIERS, E6RefusalContext, explain_e6_admission_refusal,
    explain_e6_admission_refusal_with,
};
// E9 discharge evidence: the `CleanCic` payload an `ensures` kernel discharge
// (cited theorem or island defeq) ships to the publication boundary.
pub use ensures_evidence::{
    EnsuresDischargeCertificate, EnsuresDischargeClause, EnsuresDischargeRoute,
    audit_presented_ensures_discharge, certify_ensures_discharge,
    certify_ensures_discharge_with_domains, recheck_ensures_discharge,
    recheck_ensures_discharge_with_domains,
};
// Cross-crate PROOF-position composition: a dependency crate's island sources
// re-elaborated under THIS build's kernel, so a contract may cite them. Grants
// no CALL capability and mints nothing — see the module docs.
pub use extern_proof::{
    CitedExternResolution, ClauseIdentifierDisposition, DeclarationOrigin, ExternProofComposition,
    ExternProofDiagnostic, ExternProofRefusal, ExternProofStandinImport, ExternProofUnit,
    ExternProofUnitId, compose_extern_proof_batch, extern_proof_source_digest,
};
// Trust (TG6): re-checking the local kernel fact store.
pub use keyed_env::{FactRecheck, FactStoreReport};
// Trust (ref-self I1): the view mint, for the compiler's two E6 mint seams.
pub use param_view::admit_view_function_into;

/// Trust (TG6): rescan the local kernel fact store's integrity and re-check
/// every fact in it from its own log (`targo trust store verify --facts`).
/// Every fact that does not reproduce is quarantined.
#[must_use]
pub fn verify_fact_store(store: &crate::clean_fact::FactStore) -> FactStoreReport {
    keyed_env::verify_store(store)
}

/// One island failure, spanning `start..end` BYTE OFFSETS into the island
/// text (the caller maps these onto the enclosing Rust span).
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CleanIslandDiagnostic {
    pub start: usize,
    pub end: usize,
    pub message: String,
}

/// One `import` an ACCEPTED island had served by Clean's built-in prelude
/// stand-in, with `start..end` BYTE OFFSETS pointing at its `import` keyword
/// in the island text.
///
/// Not a rejection. The island lane permanently disables external `.olean`
/// search and marks no module satisfied-from-source, so an `import` the
/// elaborator accepts can only have been served by a prelude provider that
/// names the module verbatim (`Mathlib`, `Lean`, `Lean.*`, …). Every
/// declaration of the island was kernel-checked against THAT, which says
/// nothing about the library of the same name — so a bare "kernel-checked"
/// over `import Mathlib` is a green that lies (measured 2026-09-16: the island
/// lane printed only `Clean island kernel-checked`, while the standalone
/// `.lean` lane already disclosed the substitution, `targo-trust`'s
/// `lean_cli::standin_imports_of`). clean-elab logs the substitution at
/// `warn`, and no compiler seam installs a subscriber, so this record is the
/// only way the notice reaches the author.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanIslandStandinImport {
    pub start: usize,
    pub end: usize,
    /// The module as the author spelled it (`Mathlib`, `Lean.Meta`).
    pub module: String,
}

impl CleanIslandStandinImport {
    /// What was substituted, and what the island's verdict is therefore
    /// relative to. ONE wording for every compiler seam that reports an
    /// accepted island (`rustc_resolve` and `rustc_mir_transform` cannot share
    /// a renderer; they can share this text).
    #[must_use]
    pub fn disclosure(&self) -> String {
        format!(
            "`import {}` was served by Clean's built-in prelude stand-in, NOT by the library \
             of that name — a `clean {{ … }}` island or `clean mod` unit resolves no external \
             `.olean`, so every declaration this island registers was kernel-checked relative \
             to that stand-in",
            self.module
        )
    }

    /// The ways forward (ruling v7/D3), worded as the standalone `.lean` lane
    /// words them.
    #[must_use]
    pub fn options(&self) -> String {
        format!(
            "options:\n\
             - vendor the declarations you need as Clean source in this crate (an island or a \
               `clean mod` unit) and drop `import {module}`;\n\
             - drop `import {module}` if nothing depends on it;\n\
             - build against the real library with `clean lake build`, which compiles and \
               judges nothing — it is not a substitute for this check.",
            module = self.module
        )
    }
}

/// The outcome of checking one island.
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct CleanIslandOutcome {
    /// Original anonymous judgments checked by the acceptance fence. They
    /// register no dependency root, so facts containing them bind the whole
    /// input base even when command expansion hides the lexical marker.
    pub anonymous_judgments: usize,
    /// Names of declarations that elaborated, registered, and kernel-checked.
    pub registered: Vec<String>,
    /// Every failure, with island-relative byte offsets. Non-empty ⇒ the
    /// island is REJECTED and the build must fail.
    pub errors: Vec<CleanIslandDiagnostic>,
    /// Every `import` of an ACCEPTED island that Clean's built-in prelude
    /// stand-in served, in source order, one entry per module. Always empty
    /// for a rejected island: nothing is reported green for it, so there is no
    /// green to qualify. A consumer that reports `registered` must report
    /// these alongside it.
    pub standin_imports: Vec<CleanIslandStandinImport>,
    /// Every finite model this island declared (a constant whose kernel type
    /// is `Trust.Temporal.FiniteModel.ScalarModel`) and what the automatic
    /// check found, in declaration order — filled only by a session that
    /// called [`CleanIslandSession::enable_model_checks`] ([`model_check`]'s
    /// module docs). An unsafe model is also in `errors`. A consumer that
    /// reports `registered` must report these alongside it
    /// ([`CleanIslandModelCheck::report`]): an explicitly bounded incomplete
    /// model is recorded here without a theorem; an unbounded one is also
    /// rejected. An unchecked model must never look like a checked one.
    pub model_checks: Vec<CleanIslandModelCheck>,
    /// Every binding this island declared between a model and the code (a
    /// constant whose kernel type is `Trust.Protocol.Binding`), in
    /// declaration order — filled only by a session that called
    /// [`CleanIslandSession::enable_model_checks`] or
    /// [`CleanIslandSession::enable_binding_reads`]. It is data: the consumer
    /// must check each against the code and fail the build when it does not
    /// hold, or say that it was not checked. One that could not be read is in
    /// `errors`.
    pub bindings: Vec<CleanIslandBinding>,
    /// Every seal this island declared on a type of the crate (a constant
    /// whose kernel type is `Trust.Protocol.Seal`), in declaration order,
    /// under the same terms as `bindings`.
    pub seals: Vec<CleanIslandSeal>,
    /// Every top-level command Clean parsed from this island, in authored
    /// order, with the span and canonical name Clean's own parse and
    /// elaboration assigned it and whether something refused it — filled only
    /// by the batch check (`CleanIslandSession::check_all`). `None` when the
    /// island did not parse (or was not checked by the batch), so a consumer
    /// cannot enumerate its declarations and must not report it complete.
    pub declarations: Option<Vec<CleanIslandDeclaration>>,
}

/// One top-level command of an island as Clean parsed and elaborated it: a
/// declaration, an `example`, or a command (`open`, `#check`, …). Scope
/// commands (`namespace`, `section`, `end`) and `set_option` are not listed.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanIslandDeclaration {
    /// Island-relative byte offsets of Clean's span of the command: its
    /// keyword (`theorem`, `def`, `example`, `#` of `#check`), past any
    /// attribute or `set_option … in` before it. Clean places an error in a
    /// declaration's body at this span too, so an error that starts here is
    /// the command's own.
    pub start: usize,
    pub end: usize,
    /// The canonical name Clean assigned it (`None` for an `example`, a
    /// `mutual` block or a lexical command).
    pub name: Option<String>,
    /// Something refused THIS command: Clean refused it, Trust's strict
    /// registered-declaration policy or the reference kernel recheck refused
    /// it, the publish audit named it (a `sorry` it reaches), it is on a
    /// dependency cycle, or an error that is not a whole-batch refusal lies in
    /// its span. `false` is not acceptance: a refused batch registers nothing,
    /// so no command of a rejected batch is accepted
    /// ([`crate::clean_island_batch::CleanIslandBatch::is_rejected`]).
    pub refused: bool,
}

impl CleanIslandDiagnostic {
    /// Whether this refusal belongs to the whole batch rather than to the
    /// command its span points at (a publish-audit or header fixed-point
    /// refusal, the uncommitted-batch tripwire, a refused reference base):
    /// those are placed at the batch's first byte only so they have a
    /// location.
    #[must_use]
    pub fn is_whole_batch(&self) -> bool {
        self.message.starts_with(crate::clean_island_batch::UNRECOVERABLE_BATCH_PREFIX)
    }
}

impl CleanIslandOutcome {
    #[must_use]
    pub fn is_rejected(&self) -> bool {
        !self.errors.is_empty()
    }
}

/// The registered declaration's primary name (mirrors trust-clean's
/// `elab_result_name`; kept local so the island lane has no trust-clean dep).
pub(crate) fn elab_result_name(result: &ElabResult) -> String {
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

/// The source of `modules` and everything they depend on, in serving order
/// (`trust_temporal_prelude::MODULES`) — the parser prelude that puts their
/// parse-time notation in scope ([`check_clean_island_with_parser_prelude`]).
fn served_parser_prelude(modules: &[&str]) -> String {
    fn closure(module: &str, out: &mut Vec<&'static str>) {
        if let Some((name, deps, _)) =
            trust_temporal_prelude::MODULES.iter().find(|(name, _, _)| *name == module)
        {
            for dep in *deps {
                closure(dep, out);
            }
            if !out.contains(name) {
                out.push(name);
            }
        }
    }
    let mut wanted = Vec::new();
    for module in modules {
        closure(module, &mut wanted);
    }
    let mut prelude = String::new();
    for (name, _, source) in trust_temporal_prelude::MODULES {
        if wanted.contains(name) {
            prelude.push_str(source);
            prelude.push('\n');
        }
    }
    prelude
}

/// Every `import` among `decls` (walking namespace/section/mutual blocks and
/// `open`/`set_option ... in` bodies), as `(start, end, module)` — the parse
/// [`CleanIslandSession::serve_trust_imports_named`] reads.
fn trust_module_imports(
    decls: &[clean_parser::SurfaceDecl],
    out: &mut Vec<(usize, usize, String)>,
) {
    use clean_parser::SurfaceDecl;
    for decl in decls {
        match decl {
            SurfaceDecl::Import { span, paths } => {
                for path in paths {
                    out.push((span.start, span.end, path.to_string()));
                }
            }
            SurfaceDecl::Namespace { decls, .. }
            | SurfaceDecl::Section { decls, .. }
            | SurfaceDecl::Mutual { decls, .. } => trust_module_imports(decls, out),
            SurfaceDecl::Open { body: Some(body), .. }
            | SurfaceDecl::SetOption { body: Some(body), .. } => {
                trust_module_imports(std::slice::from_ref(body.as_ref()), out);
            }
            _ => {}
        }
    }
}

/// The `import`s among an ACCEPTED island's parsed declarations that Clean's
/// built-in prelude stand-in served — see [`CleanIslandStandinImport`].
///
/// Read off the REAL parse (`SurfaceDecl::Import`), never a text scan, and
/// only ever called for an island with no error: an unresolved import is an
/// elaboration refusal, so in an accepted island every `import` was accepted.
/// What served an accepted import is then decided by the file context alone:
///
/// * external `.olean` search ENABLED — a real artifact may have served it, so
///   nothing is claimed (no compiler lane runs this way; the session
///   constructor disables the search permanently);
/// * the module is marked satisfied-from-source (the `.lean` front door's
///   sibling operands) — its declarations were elaborated from source in this
///   same batch, which is not a stand-in;
/// * otherwise — a prelude provider that names the module verbatim.
///
/// Every declaration-bearing wrapper is walked: namespace/section/mutual
/// blocks and `open`/`set_option ... in` commands.
pub(crate) fn standin_imports_in(
    decls: &[clean_parser::SurfaceDecl],
    file_ctx: &FileContext,
) -> Vec<CleanIslandStandinImport> {
    use clean_parser::SurfaceDecl;

    fn walk(
        decls: &[SurfaceDecl],
        file_ctx: &FileContext,
        out: &mut Vec<CleanIslandStandinImport>,
    ) {
        for decl in decls {
            // Exhaustive so a new SurfaceDecl variant needs review here.
            match decl {
                SurfaceDecl::Import { span, paths } => {
                    for path in paths {
                        if file_ctx.import_satisfied_from_source(path.name()) {
                            continue;
                        }
                        let module = path.to_string();
                        if !out.iter().any(|known| known.module == module) {
                            out.push(CleanIslandStandinImport {
                                start: span.start,
                                end: span.end,
                                module,
                            });
                        }
                    }
                }
                SurfaceDecl::Namespace { decls, .. }
                | SurfaceDecl::Section { decls, .. }
                | SurfaceDecl::Mutual { decls, .. } => walk(decls, file_ctx, out),
                SurfaceDecl::Open { body: Some(body), .. }
                | SurfaceDecl::SetOption { body: Some(body), .. }
                | SurfaceDecl::GuardMsgs { cmd: body, .. } => {
                    walk(std::slice::from_ref(body.as_ref()), file_ctx, out);
                }
                // These leaf commands contain no nested import declaration.
                // Elaboration and the acceptance fence still check them.
                SurfaceDecl::Prelude { .. }
                | SurfaceDecl::Alias { .. }
                | SurfaceDecl::Reduce { .. }
                | SurfaceDecl::Def { .. }
                | SurfaceDecl::Theorem { .. }
                | SurfaceDecl::Axiom { .. }
                | SurfaceDecl::Opaque { .. }
                | SurfaceDecl::Inductive { .. }
                | SurfaceDecl::Coinductive { .. }
                | SurfaceDecl::Codata { .. }
                | SurfaceDecl::Codef { .. }
                | SurfaceDecl::Structure { .. }
                | SurfaceDecl::Class { .. }
                | SurfaceDecl::Instance { .. }
                | SurfaceDecl::Example { .. }
                | SurfaceDecl::UniverseDecl { .. }
                | SurfaceDecl::Variable { .. }
                | SurfaceDecl::IncludeVars { .. }
                | SurfaceDecl::OmitVars { .. }
                | SurfaceDecl::Open { body: None, .. }
                | SurfaceDecl::Export { .. }
                | SurfaceDecl::DerivingInstance { .. }
                | SurfaceDecl::Check { .. }
                | SurfaceDecl::Eval { .. }
                | SurfaceDecl::Print { .. }
                | SurfaceDecl::PrintAxioms { .. }
                | SurfaceDecl::Guard { .. }
                | SurfaceDecl::Syntax { .. }
                | SurfaceDecl::DeclareSyntaxCat { .. }
                | SurfaceDecl::Macro { .. }
                | SurfaceDecl::MacroRules { .. }
                | SurfaceDecl::Notation { .. }
                | SurfaceDecl::Elab { .. }
                | SurfaceDecl::RawDecl { .. }
                | SurfaceDecl::Attribute { .. }
                | SurfaceDecl::SetOption { body: None, .. }
                | SurfaceDecl::DeclareAesopRuleSets { .. }
                | SurfaceDecl::LibraryNote { .. } => {}
            }
        }
    }
    let mut out = Vec::new();
    if !file_ctx.external_import_search_enabled() {
        walk(decls, file_ctx, &mut out);
    }
    out
}

/// Turn an authoritative parser byte position into a non-empty, UTF-8-safe
/// source range whenever the input itself is non-empty.
pub(crate) fn point_diagnostic_span(source: &str, at: usize) -> (usize, usize) {
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
    // fail-closed diagnostic from the elaborator. This closed statement-only
    // entry predates the nat-lift and keeps its fragment by saying so.
    kernel_unify_citation_typed_with_facets_in(
        env,
        theorem,
        clause_src,
        var_types,
        &trust_spec_elab::FacetTable::new(),
        &trust_spec_elab::ProofClauseInputs::strict(),
    )
}

/// Like [`kernel_unify_citation_typed`], with an E6 facet table consulted for
/// program-function calls in the clause, and the CLAUSE MODE stated. Facets
/// refine the out-of-fragment DIAGNOSTIC only — every call still fails closed
/// until the E6 admission gate (kernel import of a defining equation) lands, so
/// the table can never mint a verdict an empty one would refuse.
///
/// Trust (d1, 2026-09-28): this is the ∀-`result` reading of a cited clause —
/// `result`, when the clause names it, is an ordinary universally quantified
/// variable typed from `var_types`, never a call on the specified function
/// (which is why no self-function name is passed). The E9 citation sweep runs
/// it after the postcondition discharge rung, and the two MUST elaborate one
/// clause in one mode: the discharge rung ran at `ClauseMode::ProofLift` and
/// this entry was fixed at `Strict`, so a lifted clause (`x as nat`) the
/// verified lane certifies was refused here as outside the fragment — a hard
/// error with verification off, where the discharge rung cannot bind `result`
/// and this reading is the only one left.
///
/// The mode has no default here on purpose, exactly as for
/// [`kernel_discharge_ensures_citation_in`]: the Strict twin this replaced is
/// how one call site drifted, and a defaulted twin would set up the next one.
/// At [`trust_spec_elab::ProofClauseInputs::strict`] this is the pre-existing
/// behaviour to the byte: Strict records no signed-lift width, so the goal is
/// graded against `env` itself.
///
/// A signed lift (`x as int` over `iN`) names `trust_checked_toInt{N}`, which
/// is seeded into a CLONE of `env` before the goal is typed or graded — the
/// same obligation [`kernel_discharge_ensures_citation_in`] satisfies. A
/// seeding refusal (a foreign homonym) is `ClauseOutsideFragment`, never a
/// verdict the unverified lane's statement-mismatch allowance could relax.
#[must_use]
pub fn kernel_unify_citation_typed_with_facets_in(
    env: &Environment,
    theorem: &str,
    clause_src: &str,
    var_types: &[(&str, &str)],
    facets: &trust_spec_elab::FacetTable,
    inputs: &trust_spec_elab::ProofClauseInputs,
) -> CitationVerdict {
    let clause = match trust_spec_elab::elaborate_goal_typed_in_mode(
        trust_symbols::Capability::Proof,
        clause_src,
        var_types,
        facets,
        inputs,
        None,
    ) {
        Ok(clause) => clause,
        Err(reason) => return CitationVerdict::ClauseOutsideFragment { reason },
    };
    let seeded = match env_for_lifted_goal(env, &clause.required_signed_lift_widths) {
        Ok(seeded) => seeded,
        Err(reason) => return CitationVerdict::ClauseOutsideFragment { reason },
    };
    grade_cited_theorem_against_goal(seeded.as_ref().unwrap_or(env), theorem, &clause.goal)
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

/// Trust (nat-lift §3.1): satisfy a clause's SEEDING OBLIGATION.
///
/// The elaborator emits the signed lift `trust_checked_toInt{N}` by NAME and
/// holds no kernel environment, so it reports which widths the goal names and
/// this is where they are actually seeded. Seeding happens into a CLONE of the
/// session environment: the discharge entries take `&Environment`, the
/// obligation is per-clause, and a clause that fails must not leave definitions
/// behind in the session.
///
/// `seed_signed_lift_model` accepts an existing same-body definition and HARD
/// ERRORS on a homonym with any other body, so an island that got a
/// `trust_checked_*` name past the declaration-time reservation still cannot
/// capture the lift: the clause is refused here instead.
///
/// Returns the environment the goal must be typed and graded against, or the
/// refusal.
fn env_for_lifted_goal(
    env: &Environment,
    widths: &[trust_spec_elab::MachineSIntWidth],
) -> Result<Option<Environment>, String> {
    if widths.is_empty() {
        // The overwhelmingly common case, and the pre-existing hot path: no
        // clone, no seeding, nothing changed.
        return Ok(None);
    }
    let mut seeded = env.clone();
    for width in widths {
        trust_spec_elab::seed_signed_lift_model(&mut seeded, *width)?;
    }
    Ok(Some(seeded))
}

/// Trust (nat-lift): elaborate one `ensures` clause for a discharge lane,
/// satisfying its seeding obligation, and hand back the goal with the
/// environment it must be judged against.
fn lifted_ensures_goal(
    env: &Environment,
    clause_src: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &trust_spec_elab::FacetTable,
    inputs: &trust_spec_elab::ProofClauseInputs,
) -> Result<(clean_kernel::Expr, Option<Environment>), CitationVerdict> {
    let clause = match trust_spec_elab::elaborate_ensures_in(
        clause_src,
        param_types,
        self_fn_name,
        facets,
        inputs,
    ) {
        Ok(clause) => clause,
        Err(reason) => return Err(CitationVerdict::ClauseOutsideFragment { reason }),
    };
    match env_for_lifted_goal(env, &clause.required_signed_lift_widths) {
        Ok(seeded) => Ok((clause.goal, seeded)),
        Err(reason) => Err(CitationVerdict::ClauseOutsideFragment { reason }),
    }
}

#[must_use]
pub fn kernel_discharge_ensures_citation(
    env: &Environment,
    theorem: &str,
    clause_src: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &trust_spec_elab::FacetTable,
) -> CitationVerdict {
    kernel_discharge_ensures_citation_in(
        env,
        theorem,
        clause_src,
        param_types,
        self_fn_name,
        facets,
        &trust_spec_elab::ProofClauseInputs::strict(),
    )
}

/// Trust (nat-lift): [`kernel_discharge_ensures_citation`] with the CLAUSE MODE
/// stated. The mode has no default here on purpose — a discharge lane must say
/// which fragment it is speaking, and the plain entry above is exactly this one
/// at `Strict`.
#[must_use]
pub fn kernel_discharge_ensures_citation_in(
    env: &Environment,
    theorem: &str,
    clause_src: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &trust_spec_elab::FacetTable,
    inputs: &trust_spec_elab::ProofClauseInputs,
) -> CitationVerdict {
    let (goal, seeded) =
        match lifted_ensures_goal(env, clause_src, param_types, self_fn_name, facets, inputs) {
            Ok(pair) => pair,
            Err(verdict) => return verdict,
        };
    let env = seeded.as_ref().unwrap_or(env);
    // The elaborated goal is the single most useful thing a user can be told
    // when a citation or a defeq discharge fails, and nothing printed it: the
    // author saw "not definitionally equal" or "bindings are not exact" with no
    // way to see the proposition the kernel was actually asked to close. Since
    // a cited theorem must be stated over the COMPILER'S encoding of the body,
    // not seeing that encoding makes the citation lane guess-and-check. This is
    // the cheap stand-in for the unbuilt `targo trust spec --emit clean`.
    if e9_debug_enabled() {
        eprintln!("TRUST_E9_DEBUG GOAL clause={clause_src:?} goal={goal}");
    }
    grade_cited_theorem_against_goal(env, theorem, &goal)
}

fn e9_debug_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("TRUST_E9_DEBUG").is_some())
}

pub(super) fn e6_debug_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("TRUST_E6_DEBUG").is_some())
}

/// Which goal a cited theorem's DECLARED type was found to state.
///
/// This is a REPORTING axis, not an authority axis: `cert_meter::grade` remains
/// the only thing that decides whether a proof term proves a goal, and the rung
/// only says which goal was graded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CitationRung {
    /// `G0` — `∀ params, Q(params, f_def params)`. The postcondition for EVERY
    /// input; says nothing about any precondition.
    Unconditional,
    /// `G1` — `∀ params, H_0 → … → H_{n-1} → Q(params, f_def params)`. The
    /// postcondition for inputs that satisfy the CARRIED `requires` clauses, and
    /// NOTHING about inputs that violate them.
    UnderRequires,
    /// The theorem states neither goal.
    Neither,
}

/// Trust (OR-A1, 2026-09-27): WHICH READING of the function's own
/// `requires` the hypotheses of a conditional discharge took — the
/// requires→hypothesis link (`F_R ⇒ P_R`: what callers are charged implies what
/// the cited theorem consumes).
///
/// DATA, not a grade. In Inc 1a BOTH links credit a row at `Trusted`; the
/// ruling reserves `Certified` for a link that is itself kernel-checked as the
/// identical canonical term, and whether a definitional-equality judgment
/// against the compiler-built `T_j` is that check is the Inc 1b decision
/// (`docs/DECISION_QUEUE.md`), not this type's.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RequiresLink {
    /// The theorem proved `G1★`: every hypothesis in the LIFTED mathematical
    /// reading `T_j` of the query-owned canonical text callers are charged
    /// (`trust_spec_elab::EnsuresUnderRequires::canonical_goal`). The kernel
    /// judged the theorem's hypothesis binders against `T_j` itself (up to
    /// definitional equality); the Rust-side step is the CONSTRUCTION of `T_j`
    /// — the closed lift table over the arithmetic-free fragment — which is the
    /// same goal-construction base the unconditional rung already trusts.
    KernelCanonical,
    /// The theorem proved `G1` only: every hypothesis in its Clean
    /// (machine-carrier) reading `H_j`, linked to what callers are charged by
    /// the `E-allow` soundness argument (`trust_spec_elab`, the
    /// `requires`-as-hypotheses section) — code, not a kernel check.
    AllowListed,
}

impl RequiresLink {
    /// The disclosure spelling — the `requires_link` value of a spec-clean goal
    /// row and the `requires-link:` marker of the compiler's notes.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            RequiresLink::KernelCanonical => "kernel-canonical",
            RequiresLink::AllowListed => "allow-listed",
        }
    }

    /// The weaker of two links. A function's rows are not attributed to
    /// clauses, so a discharge that rests on several cited clauses is only as
    /// strong as its weakest link.
    #[must_use]
    pub fn weakest(self, other: RequiresLink) -> RequiresLink {
        if self == RequiresLink::AllowListed || other == RequiresLink::AllowListed {
            RequiresLink::AllowListed
        } else {
            RequiresLink::KernelCanonical
        }
    }
}

/// The outcome of the ensures-citation ladder (`G0`, then `G1★`, then `G1`).
#[derive(Debug, Clone)]
pub struct EnsuresCitationLadder {
    /// Which goal the verdict below was graded against.
    pub rung: CitationRung,
    /// The grade. `KernelStatementMatchCertified` on rung
    /// [`CitationRung::UnderRequires`] is a CONDITIONAL discharge and must never
    /// be reported as the unconditional one.
    pub verdict: CitationVerdict,
    /// One row per candidate `requires` clause, in contract order. Empty when
    /// `G1` was not built.
    pub hypotheses: Vec<trust_spec_elab::HypothesisRow>,
    /// Why `G1` was not built, when it was not.
    pub g1_refusal: Option<String>,
    /// `G0`, rendered — the diagnostic's goal (1). `None` on the
    /// conditional-only entry, which does not build it.
    pub goal_unconditional: Option<String>,
    /// `G1`, rendered — the diagnostic's goal (2).
    pub goal_under_requires: Option<String>,
    /// `G1`'s value binders, outermost first (clause-side names).
    pub value_binders: Vec<String>,
    /// Trust (OR-A1): `G1★`, rendered — the kernel-canonical goal, when built.
    pub goal_under_requires_canonical: Option<String>,
    /// Trust (OR-A1): why `G1★` was not built, when `G1` was.
    pub canonical_refusal: Option<String>,
    /// Trust (OR-A1): which conditional goal certified — `Some` exactly when
    /// [`Self::discharged_rung`] is [`CitationRung::UnderRequires`].
    pub requires_link: Option<RequiresLink>,
}

impl EnsuresCitationLadder {
    /// A ladder with nothing built and nothing graded beyond `verdict`.
    fn refused(verdict: CitationVerdict, g1_refusal: Option<String>) -> Self {
        EnsuresCitationLadder {
            rung: CitationRung::Neither,
            verdict,
            hypotheses: Vec::new(),
            g1_refusal,
            goal_unconditional: None,
            goal_under_requires: None,
            value_binders: Vec::new(),
            goal_under_requires_canonical: None,
            canonical_refusal: None,
            requires_link: None,
        }
    }

    /// The disclosure fields of a `G1`/`G1★` build attempt, with no grade yet.
    fn from_conditional_build(
        built: &Result<trust_spec_elab::EnsuresUnderRequires, String>,
        verdict: CitationVerdict,
    ) -> Self {
        match built {
            Ok(built) => EnsuresCitationLadder {
                rung: CitationRung::Neither,
                verdict,
                hypotheses: built.hypotheses.clone(),
                g1_refusal: None,
                goal_unconditional: None,
                goal_under_requires: Some(built.goal.to_string()),
                value_binders: built.value_binders.clone(),
                goal_under_requires_canonical: built
                    .canonical_goal
                    .as_ref()
                    .map(ToString::to_string),
                canonical_refusal: built.canonical_refusal.clone(),
                requires_link: None,
            },
            Err(reason) => Self::refused(verdict, Some(reason.clone())),
        }
    }

    /// Whether this ladder discharged the clause, and conditionally on what.
    ///
    /// Deliberately NOT a bare boolean: every consumer has to decide what to do
    /// with a conditional discharge, and a boolean is how that decision stops
    /// being made.
    #[must_use]
    pub fn discharged_rung(&self) -> Option<CitationRung> {
        matches!(self.verdict, CitationVerdict::KernelStatementMatchCertified)
            .then_some(self.rung)
            .filter(|r| !matches!(r, CitationRung::Neither))
    }

    /// Trust (OR-A1): the link of a CONDITIONAL discharge — `Some` exactly when
    /// a conditional goal (`G1★` or `G1`) certified. This says what the kernel
    /// graded; it is NOT a credit decision. The compiler still requires a
    /// non-vacuous precondition (a ground witness `Found`), no parameter view,
    /// and no existing static proof on the row before it installs anything.
    #[must_use]
    pub fn conditional_link(&self) -> Option<RequiresLink> {
        (self.discharged_rung() == Some(CitationRung::UnderRequires))
            .then_some(self.requires_link)
            .flatten()
    }
}

/// A1 + OR-A1: the ensures-citation ladder in the STRICT clause mode
/// (`trust_spec_elab::ProofClauseInputs::strict`) — see
/// [`kernel_discharge_ensures_citation_under_in`].
#[must_use]
pub fn kernel_discharge_ensures_citation_under(
    env: &Environment,
    theorem: &str,
    clause_src: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &trust_spec_elab::FacetTable,
    hyps: &[trust_spec_elab::HypothesisInput],
) -> EnsuresCitationLadder {
    kernel_discharge_ensures_citation_under_in(
        env,
        theorem,
        clause_src,
        param_types,
        self_fn_name,
        facets,
        hyps,
        &trust_spec_elab::ProofClauseInputs::strict(),
    )
}

/// A1 (design revision 2 `requires-hyps` §2.2) and OR-A1: the ensures-citation
/// ladder.
///
/// [`kernel_discharge_ensures_citation`] asks a cited theorem to prove the
/// UNCONDITIONAL postcondition, so a theorem that is true only under the
/// function's own `requires` cannot be cited at all. This entry point tries that
/// goal FIRST — byte for byte, in the same clause mode, so no program that is
/// green today changes — and only then the strictly weaker conditional goals
///
/// ```text
/// G1★ := ∀ (value binders), T_0 → … → T_{n-1} → Q(params, f_def params)
/// G1  := ∀ (value binders), H_0 → … → H_{n-1} → Q(params, f_def params)
/// ```
///
/// where each `H_j` is the Clean elaboration of one ELIGIBLE `requires` clause
/// and `T_j` is its LIFTED mathematical reading
/// (`trust_spec_elab::elaborate_ensures_under_requires_in`, which owns the
/// eligibility rule, both readings, and the soundness argument for the
/// hypothesis polarity). `G1★` is graded before `G1` because it carries the
/// stronger link ([`RequiresLink::KernelCanonical`]); when the two goals are
/// the SAME term (an unsigned `<=` clause) `G1` is not graded a second time.
///
/// WHAT A CONDITIONAL DISCHARGE DOES AND DOES NOT SAY. It says: for every input
/// that satisfies the carried preconditions, the postcondition holds of the
/// imported defining equation. It says NOTHING about an input that violates
/// them. A consumer that credits a VC row from this must therefore be able to
/// point at the mechanism that charges callers those same preconditions — which
/// is why [`EnsuresCitationLadder::discharged_rung`] hands back the rung instead
/// of a boolean, and [`EnsuresCitationLadder::conditional_link`] the link.
///
/// ONE SEEDED ENVIRONMENT (H6). `G0` is graded in the environment its own
/// seeding obligation produces, exactly as
/// [`kernel_discharge_ensures_citation_in`] grades it; both conditional goals
/// are graded in one clone seeded with the UNION of the signed lift widths the
/// conclusion and the lifted hypotheses name.
///
/// THREE GRADES AT MOST. When nothing certifies, the RUNG REPORTED is chosen by
/// asking the kernel which goal the theorem's declared type actually states — an
/// untrusted selector, so that a theorem of the right type whose proof carries a
/// `sorry` is reported as a certification failure on that rung, not as "it
/// states neither goal".
#[allow(clippy::too_many_arguments)]
#[must_use]
pub fn kernel_discharge_ensures_citation_under_in(
    env: &Environment,
    theorem: &str,
    clause_src: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &trust_spec_elab::FacetTable,
    hyps: &[trust_spec_elab::HypothesisInput],
    inputs: &trust_spec_elab::ProofClauseInputs,
) -> EnsuresCitationLadder {
    let (g0, seeded0) =
        match lifted_ensures_goal(env, clause_src, param_types, self_fn_name, facets, inputs) {
            Ok(pair) => pair,
            // The conclusion itself is outside the fragment: there is no rung to
            // climb, and this is byte-identical to the single-rung lane.
            Err(verdict) => return EnsuresCitationLadder::refused(verdict, None),
        };
    let env0 = seeded0.as_ref().unwrap_or(env);
    let g1 = trust_spec_elab::elaborate_ensures_under_requires_in(
        clause_src,
        param_types,
        self_fn_name,
        facets,
        hyps,
        inputs,
    );
    if e9_debug_enabled() {
        eprintln!("TRUST_E9_DEBUG GOAL clause={clause_src:?} goal={g0}");
        debug_print_conditional_goals(&g1);
    }
    let v0 = grade_cited_theorem_against_goal(env0, theorem, &g0);
    let certified0 = matches!(v0, CitationVerdict::KernelStatementMatchCertified);
    let mut ladder = EnsuresCitationLadder::from_conditional_build(&g1, v0);
    ladder.goal_unconditional = Some(g0.to_string());
    if certified0 {
        ladder.rung = CitationRung::Unconditional;
        return ladder;
    }
    if let Ok(built) = &g1 {
        let (rung, verdict, link) = grade_conditional_rungs(env, theorem, built);
        if rung == CitationRung::UnderRequires {
            ladder.rung = rung;
            ladder.verdict = verdict;
            ladder.requires_link = link;
            return ladder;
        }
    }
    // Neither conditional goal is certified or stated: report against `G0`,
    // keeping `G0`'s verdict.
    ladder.rung = if theorem_states_goal(env0, theorem, &g0) {
        CitationRung::Unconditional
    } else {
        CitationRung::Neither
    };
    ladder
}

/// Trust (OR-A1): the CONDITIONAL rungs only — `G1★`, then `G1` — for a lane
/// that has ALREADY graded `G0` and seen it fail (the in-walk and deferred
/// discharge lanes, the citation sweep). Saves the repeated `G0` grade; grades
/// nothing `G0`-related, so `goal_unconditional` is `None` and a rung of
/// [`CitationRung::Neither`] means "no conditional goal certified or was
/// stated", not a statement about `G0`.
#[allow(clippy::too_many_arguments)]
#[must_use]
pub fn kernel_discharge_ensures_citation_conditional_in(
    env: &Environment,
    theorem: &str,
    clause_src: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &trust_spec_elab::FacetTable,
    hyps: &[trust_spec_elab::HypothesisInput],
    inputs: &trust_spec_elab::ProofClauseInputs,
) -> EnsuresCitationLadder {
    let g1 = trust_spec_elab::elaborate_ensures_under_requires_in(
        clause_src,
        param_types,
        self_fn_name,
        facets,
        hyps,
        inputs,
    );
    if e9_debug_enabled() {
        debug_print_conditional_goals(&g1);
    }
    let Ok(built) = &g1 else {
        let reason = g1.as_ref().err().cloned().unwrap_or_default();
        return EnsuresCitationLadder::refused(
            CitationVerdict::ClauseOutsideFragment { reason: reason.clone() },
            Some(reason),
        );
    };
    let (rung, verdict, link) = grade_conditional_rungs(env, theorem, built);
    let mut ladder = EnsuresCitationLadder::from_conditional_build(&g1, verdict);
    ladder.rung = rung;
    ladder.requires_link = link;
    ladder
}

fn debug_print_conditional_goals(g1: &Result<trust_spec_elab::EnsuresUnderRequires, String>) {
    match g1 {
        Ok(built) => {
            eprintln!("TRUST_E9_DEBUG GOAL-UNDER-REQUIRES goal={}", built.goal);
            match (&built.canonical_goal, &built.canonical_refusal) {
                (Some(goal), _) => {
                    eprintln!("TRUST_E9_DEBUG GOAL-UNDER-REQUIRES-CANONICAL goal={goal}");
                }
                (None, reason) => eprintln!(
                    "TRUST_E9_DEBUG NO-CANONICAL-UNDER-REQUIRES-GOAL reason={}",
                    reason.as_deref().unwrap_or("")
                ),
            }
        }
        Err(reason) => eprintln!("TRUST_E9_DEBUG NO-UNDER-REQUIRES-GOAL reason={reason}"),
    }
}

/// Trust (OR-A1): grade `G1★` then `G1` against the cited theorem, in ONE
/// environment seeded with the union of the signed lift widths both goals name
/// (H6), and report `(rung, verdict, link)`.
///
/// `link` is `Some` exactly when a conditional goal certified. When none did,
/// the rung is the one the theorem's declared type STATES (the untrusted
/// selector [`theorem_states_goal`], which can never mint anything), with that
/// goal's verdict, or [`CitationRung::Neither`] with the last grade.
fn grade_conditional_rungs(
    env: &Environment,
    theorem: &str,
    built: &trust_spec_elab::EnsuresUnderRequires,
) -> (CitationRung, CitationVerdict, Option<RequiresLink>) {
    let seeded = match env_for_lifted_goal(env, &built.required_signed_lift_widths) {
        Ok(seeded) => seeded,
        Err(reason) => {
            return (
                CitationRung::Neither,
                CitationVerdict::ClauseOutsideFragment { reason },
                None,
            );
        }
    };
    let env = seeded.as_ref().unwrap_or(env);
    let canonical = built.canonical_goal.as_ref();
    let canonical_verdict =
        canonical.map(|goal| grade_cited_theorem_against_goal(env, theorem, goal));
    if matches!(canonical_verdict, Some(CitationVerdict::KernelStatementMatchCertified)) {
        return (
            CitationRung::UnderRequires,
            CitationVerdict::KernelStatementMatchCertified,
            Some(RequiresLink::KernelCanonical),
        );
    }
    // When `G1★` IS `G1` (an unsigned `<=`/`<` clause: `Nat.le (toNat b)
    // (toNat a)` in both readings) its grade is `G1`'s grade; grading the same
    // term twice would only report the weaker link for the same judgment.
    let identical = canonical == Some(&built.goal);
    let allow_verdict =
        (!identical).then(|| grade_cited_theorem_against_goal(env, theorem, &built.goal));
    if matches!(allow_verdict, Some(CitationVerdict::KernelStatementMatchCertified)) {
        return (
            CitationRung::UnderRequires,
            CitationVerdict::KernelStatementMatchCertified,
            Some(RequiresLink::AllowListed),
        );
    }
    if let (Some(goal), Some(verdict)) = (canonical, &canonical_verdict) {
        if theorem_states_goal(env, theorem, goal) {
            return (CitationRung::UnderRequires, verdict.clone(), None);
        }
    }
    if let Some(verdict) = &allow_verdict {
        if theorem_states_goal(env, theorem, &built.goal) {
            return (CitationRung::UnderRequires, verdict.clone(), None);
        }
    }
    let verdict = allow_verdict.or(canonical_verdict).unwrap_or_else(|| {
        CitationVerdict::ClauseOutsideFragment {
            reason: "internal: no conditional goal was graded".to_string(),
        }
    });
    (CitationRung::Neither, verdict, None)
}

/// UNTRUSTED rung selector: does the theorem's DECLARED type state `goal`?
///
/// Used only to choose which failing rung to report. It can never mint a
/// discharge — `cert_meter::grade` is the sole authority and has already run on
/// both rungs by the time this is consulted — and it never widens one: a `true`
/// here on an ungraded goal would still leave the verdict non-`Certified`.
/// A goal the kernel cannot TYPE is never compared, so `is_def_eq`'s
/// well-typedness precondition holds at every call.
///
/// It re-checks no certificate, yet goes through `kernel_stop` (on critic B1's
/// list): a spent count turns its `true` into `false`, which changes which
/// failing rung, and so which failing verdict, is reported (KERNEL-STOP-1).
fn theorem_states_goal(env: &Environment, theorem: &str, goal: &clean_kernel::Expr) -> bool {
    if reject_untyped_goal(env, goal).is_some() {
        return false;
    }
    let Some(info) = env.get_const(&clean_kernel::Name::from_string(theorem)) else {
        return false;
    };
    if info.kind != ConstantKind::Theorem {
        return false;
    }
    crate::kernel_stop::is_def_eq(clean_kernel::TypeChecker::new(env), &info.type_, goal)
}

/// R4 §1: the arity (Pi-telescope length of the declared type) of an
/// unfoldable island Definition — what a facet-table [`Admission`] needs so
/// the clause elaborator resolves a CALL to the island name against the
/// kernel constant. Same category discipline as
/// [`island_definition_value`]: non-definitions answer `None`.
#[must_use]
pub fn island_definition_arity(env: &KernelEnvironment, name: &str) -> Option<usize> {
    island_definition_signature(env, name).map(|(arity, _)| arity)
}

/// [`island_definition_arity`] plus the definition's RESULT domain, when the
/// Clean codomain determines one unambiguously.
///
/// Only a literal `Bool` codomain is reported. The Clean-type → `Domain` map is
/// NOT injective — `BitVec 64` is the carrier of both `Signed(I64)` and
/// `USize(W64)`, and `Nat` is a carrier the clause fragment reaches from several
/// places — so reading a domain back off a numeric carrier would type a clause
/// atom at a carrier the island author never wrote. `Bool` has exactly one
/// preimage, which is why it is the one case recorded; everything else answers
/// `None` and every consumer of [`trust_spec_elab::Admission::ret_domain`] fails
/// closed on `None`. This keeps behaviour for every non-`Bool` island definition
/// byte-identical to before the field existed.
#[must_use]
pub fn island_definition_signature(
    env: &KernelEnvironment,
    name: &str,
) -> Option<(usize, Option<trust_spec_elab::Domain>)> {
    island_definition_signature_for_name(env, &clean_kernel::Name::from_string(name))
}

fn island_definition_signature_for_name(
    env: &KernelEnvironment,
    name: &clean_kernel::Name,
) -> Option<(usize, Option<trust_spec_elab::Domain>)> {
    island_definition_value_for_name(env, name)?;
    let info = env.get_const(name)?;
    let mut arity = 0usize;
    let mut ty: &clean_kernel::Expr = &info.type_;
    while let clean_kernel::ExprKind::Pi(_, _, codomain) = ty.kind() {
        arity += 1;
        ty = codomain;
    }
    let ret_domain = match ty.kind() {
        clean_kernel::ExprKind::Const(n, _) if n.to_string() == "Bool" => {
            Some(trust_spec_elab::Domain::Bool)
        }
        // `Option (BitVec N)` (checked-arithmetic lane): TODAY this codomain
        // has exactly ONE preimage — `Domain::OptionSigned(N)` is the sole
        // Option-carrier domain — so the map stays injective and reading it
        // back cannot retype an author's carrier. The consumers it feeds are
        // safe even in spirit: the recorded domain drives only the RELATION
        // carrier (`Eq (Option (BitVec N))`, signedness-neutral) and the
        // constructor formers' INNER typing, whose wrapping arithmetic is
        // bit-identical for signed and unsigned two's-complement. THE DAY an
        // unsigned-Option domain is added, this arm must go back to `None`
        // exactly as the numeric carriers do — the injectivity note above is
        // the contract.
        _ => option_signed_width_of_codomain(ty).map(trust_spec_elab::Domain::OptionSigned),
    };
    Some((arity, ret_domain))
}

/// The `MachineSIntWidth` of a Clean codomain `Option (BitVec N)` — accepting
/// both the elaborator's bare `Nat` width literal and the island elaborator's
/// `OfNat.ofNat Nat N (instOfNatNat N)` wrapping (the two defeq spellings the
/// vendored elaborators actually produce) — else `None`.
fn option_signed_width_of_codomain(
    ty: &clean_kernel::Expr,
) -> Option<trust_spec_elab::MachineSIntWidth> {
    use clean_kernel::ExprKind;
    let ExprKind::App(option_head, payload) = ty.kind() else {
        return None;
    };
    let ExprKind::Const(option_name, _) = option_head.kind() else {
        return None;
    };
    if option_name.to_string() != "Option" {
        return None;
    }
    let ExprKind::App(bitvec_head, width_expr) = payload.kind() else {
        return None;
    };
    let ExprKind::Const(bitvec_name, _) = bitvec_head.kind() else {
        return None;
    };
    if bitvec_name.to_string() != "BitVec" {
        return None;
    }
    let width = nat_literal_of(width_expr)?;
    use trust_spec_elab::MachineSIntWidth::{I8, I16, I32, I64, I128};
    Some(match width {
        8 => I8,
        16 => I16,
        32 => I32,
        64 => I64,
        128 => I128,
        _ => return None,
    })
}

/// The small `Nat` a literal-or-`OfNat`-wrapped width expression denotes.
fn nat_literal_of(e: &clean_kernel::Expr) -> Option<u64> {
    use clean_kernel::{ExprKind, Literal};
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        // OfNat.ofNat Nat <lit> (instOfNatNat <lit>) — take the explicit
        // literal argument (the instance repeats it).
        ExprKind::App(f, _inst) => {
            let ExprKind::App(f2, lit) = f.kind() else {
                return None;
            };
            let ExprKind::App(head, _nat_ty) = f2.kind() else {
                return None;
            };
            let ExprKind::Const(name, _) = head.kind() else {
                return None;
            };
            if name.to_string() != "OfNat.ofNat" {
                return None;
            }
            let ExprKind::Lit(Literal::Nat(n)) = lit.kind() else {
                return None;
            };
            n.to_u64()
        }
        _ => None,
    }
}

/// The DECLARED Clean carrier types of an island definition's value parameters
/// and result, read straight off the kernel's recorded declaration — the
/// authoritative answer to "what does this constant actually take, and at what
/// widths?" (E6/E9 widening increment 8).
///
/// WHY A [`trust_spec_elab::Carrier`] AND NOT A `Domain`. This walks the same
/// Pi telescope as [`island_definition_signature`] and is bound by the same
/// injectivity caveat documented there: `BitVec 64` is the carrier of `i64`,
/// `usize` and `isize` alike, so a `Domain` read back off it would be a GUESS.
/// A `Carrier` is the Clean type itself, normalized — the codomain of the
/// `Domain -> Carrier` map, never its inverse. The clause elaborator uses it
/// only to CHECK a domain some other authority already fixed (the Rust
/// signature behind the clause binding), so nothing here can retype a term.
///
/// Fail-closed by construction: a carrier this reader does not RECOGNIZE — an
/// a dependent `BitVec n` whose width is a bound variable or a
/// universe-polymorphic head — answers `None` for the WHOLE signature, and
/// [`trust_spec_elab::Admission::carriers`] being `None` puts the elaborator
/// back on its pre-increment behaviour (one ambient domain across the atom).
/// A definition whose telescope is dependent therefore cannot be read as
/// non-dependent by accident: the dependency shows up as an unreadable width
/// and the whole record is refused.
/// Checked monomorphic, non-indexed ADTs are read from the current environment,
/// retaining their ordered constructor telescopes and closed type arguments.
/// This is a readback of the Clean declaration, not evidence that a Rust type
/// has that representation or that a reflected Rust function is kernel-checked.
#[must_use]
pub fn island_definition_carriers(
    env: &KernelEnvironment,
    name: &str,
) -> Option<trust_spec_elab::DeclaredCarriers> {
    island_definition_carriers_for_name(env, &clean_kernel::Name::from_string(name))
}

fn island_definition_carriers_for_name(
    env: &KernelEnvironment,
    name: &clean_kernel::Name,
) -> Option<trust_spec_elab::DeclaredCarriers> {
    island_definition_value_for_name(env, name)?;
    let info = env.get_const(name)?;
    // A universe-polymorphic declaration is already refused by the admission
    // path; refuse it here too so this reader is safe to call on its own.
    if !info.level_params.is_empty() {
        return None;
    }
    let mut params = Vec::new();
    let mut ty: &clean_kernel::Expr = &info.type_;
    while let clean_kernel::ExprKind::Pi(_, domain, codomain) = ty.kind() {
        params.push(carrier_of_clean_type(env, domain)?);
        ty = codomain;
    }
    let ret = carrier_of_clean_type(env, ty)?;
    Some(trust_spec_elab::DeclaredCarriers { params, ret })
}

/// One Clean type read as a [`trust_spec_elab::Carrier`], or `None` when the
/// shape is not one of the closed set the clause fragment has carriers for.
///
/// The `BitVec`/`Option` arms accept BOTH width spellings the vendored
/// elaborators produce (a bare `Nat` literal and the
/// `OfNat.ofNat Nat N (instOfNatNat N)` wrapping) via [`nat_literal_of`], for
/// the same reason [`option_signed_width_of_codomain`] does: the two are defeq
/// and an island author never chooses between them.
///
/// A type whose head is a type ALIAS (`abbrev Flag := Bool`) is read through it
/// ([`unfold_clean_type_alias`]).
fn carrier_of_clean_type(
    env: &KernelEnvironment,
    ty: &clean_kernel::Expr,
) -> Option<trust_spec_elab::Carrier> {
    carrier_of_spelled_clean_type(env, ty)
        .or_else(|| carrier_of_spelled_clean_type(env, &unfold_clean_type_alias(env, ty)?))
}

/// `ty` with the type alias at its head unfolded to the kernel's own weak-head
/// normal form, or `None` when `ty` is not closed or its head is not a
/// transparent, universe-monomorphic [`ConstantKind::Definition`].
///
/// Reading through an alias widens nothing. The kernel's definitional equality
/// already unfolds it, so a goal applying the island constant to a `Bool`
/// argument at a `Flag` binder typechecks, and what the alias names must still
/// be a carrier [`carrier_of_spelled_clean_type`] recognizes: `abbrev Pred :=
/// Nat -> Bool` unfolds to a function type and stays unreadable. Without it one
/// binder spelled through an alias made the WHOLE carrier record `None` while
/// [`island_return_domain`] still recorded the result's domain, so the clause
/// elaborator read the call's arguments as operands of the relation and refused
/// it as mixed (TG15 open item 2).
fn unfold_clean_type_alias(
    env: &KernelEnvironment,
    ty: &clean_kernel::Expr,
) -> Option<clean_kernel::Expr> {
    let mut head = ty;
    while let clean_kernel::ExprKind::App(function, _) = head.kind() {
        head = function;
    }
    let clean_kernel::ExprKind::Const(name, levels) = head.kind() else {
        return None;
    };
    let info = env.get_const(name)?;
    if ty.has_loose_bvars()
        || !levels.is_empty()
        || info.kind != ConstantKind::Definition
        || info.value.is_none()
        || !info.level_params.is_empty()
    {
        return None;
    }
    Some(clean_kernel::TypeChecker::new(env).whnf(ty))
}

/// [`carrier_of_clean_type`] on `ty` exactly as spelled: no alias at its head
/// is unfolded (an argument is read through [`carrier_of_clean_type`] again).
fn carrier_of_spelled_clean_type(
    env: &KernelEnvironment,
    ty: &clean_kernel::Expr,
) -> Option<trust_spec_elab::Carrier> {
    use clean_kernel::ExprKind;
    use trust_spec_elab::{Carrier, MachineUIntWidth};
    match ty.kind() {
        ExprKind::Const(name, _) => match name.to_string().as_str() {
            "Nat" => Some(Carrier::Nat),
            // Trust (nat-lift §3.1): `Int` is the codomain of the signed and
            // `Int`-targeted lift rows, so an island definition declared over
            // it must be readable back or the clause could never name one.
            "Int" => Some(Carrier::Int),
            "Bool" => Some(Carrier::Bool),
            "UInt8" => Some(Carrier::UInt(MachineUIntWidth::U8)),
            "UInt16" => Some(Carrier::UInt(MachineUIntWidth::U16)),
            "UInt32" => Some(Carrier::UInt(MachineUIntWidth::U32)),
            "UInt64" => Some(Carrier::UInt(MachineUIntWidth::U64)),
            _ => registered_carrier_of_clean_type(env, ty).map(Carrier::RegisteredAdt),
        },
        ExprKind::App(head, arg) => {
            let ExprKind::Const(head_name, _) = head.kind() else {
                return registered_carrier_of_clean_type(env, ty).map(Carrier::RegisteredAdt);
            };
            match head_name.to_string().as_str() {
                "BitVec" => {
                    let bits = nat_literal_of(arg)?;
                    Some(Carrier::BitVec(u32::try_from(bits).ok()?))
                }
                "Option" => Some(Carrier::Option(Box::new(carrier_of_clean_type(env, arg)?))),
                _ => registered_carrier_of_clean_type(env, ty).map(Carrier::RegisteredAdt),
            }
        }
        _ => None,
    }
}

/// Read the schema of an already registered Clean family, then validate it
/// against the same environment. Unlike a compiler-supplied Rust schema, this
/// expected shape is deliberately a declaration reader: it establishes checked
/// carrier identity and provenance, NOT source-to-model correspondence. The
/// shared validator checks both side tables and constants, the whole ordered
/// constructor telescopes, closed type arguments, and certification provenance.
fn registered_carrier_of_clean_type(
    env: &KernelEnvironment,
    ty: &clean_kernel::Expr,
) -> Option<trust_spec_elab::RegisteredAdt> {
    use clean_kernel::ExprKind;
    use trust_spec_elab::{AdtSchema, ConstructorSchema, RegisteredAdt};

    let mut head = ty;
    let mut arguments = Vec::new();
    while let ExprKind::App(function, argument) = head.kind() {
        arguments.push(argument.as_ref().clone());
        head = function;
    }
    arguments.reverse();
    let ExprKind::Const(name, levels) = head.kind() else {
        return None;
    };
    if !levels.is_empty() {
        return None;
    }
    let info = env.get_inductive(name)?;
    let constructors = info
        .constructor_names
        .iter()
        .map(|name| {
            let constructor = env.get_constructor(name)?;
            Some(ConstructorSchema { name: name.clone(), type_: constructor.type_.clone() })
        })
        .collect::<Option<Vec<_>>>()?;
    let schema = AdtSchema {
        name: name.clone(),
        type_: info.type_.clone(),
        num_params: info.num_params,
        constructors,
    };
    RegisteredAdt::validate(env, &schema, &arguments).ok()
}

/// The compiler's reserved namespace for E6 kernel-imported program functions
/// — the constants [`mangle_kernel_const`] mints and I2 records as
/// `trust_symbols::KernelStatus::Reflected`.
///
/// It is reserved in both directions: an island may not declare into it
/// (`strict_leaf_policy_error`), and a constant inside it may not be admitted
/// as a kernel-checked Clean declaration
/// ([`admit_certified_island_definition`]). One spelling, so the two halves
/// cannot drift apart.
pub const KERNEL_IMPORT_PREFIX: &str = "trust_import_";

/// Trust (nat-lift §3.1): the compiler's reserved namespace for the SEEDED
/// kernel models — the checked-arithmetic models and the signed lift
/// (`trust_checked_toInt{N}`), which `trust_spec_elab::seed_signed_lift_model`
/// mints.
///
/// It must be reserved for a reason the `trust_import_` prefix does not have.
/// The elaborator emits the lift constant BY NAME and holds no environment, so
/// an island that declared `def trust_checked_toInt64 (v : BitVec 64) : Int :=
/// 0` would capture every signed lift and turn each signed goal into `0 = 0` —
/// a well-typed, kernel-checkable, entirely vacuous proposition. Two
/// independent checks close that: this one, at the point of declaration, and
/// `seed_decl`'s structural-identity refusal when the seeder meets a homonym
/// with any other body. Either alone would do; both, because the failure mode
/// is silent.
pub const SEEDED_MODEL_PREFIX: &str = "trust_checked_";

/// Trust (TG16, after TG11): the compiler's reserved namespace for the readable ODT aliases
/// E6 generates for Rust types — `trust_type_<crate>__<Type>` and its `.casesOn`,
/// `.constructors.*`, `.fields.*`, `.toTag` and `.mk` members (`odt_e6::aliases`).
///
/// The aliases are minted after an island batch is checked, so an island that declared
/// `trust_type_c__Phase.toTag` first either held the generated spelling (and turned the later
/// mint into a spanless `DuplicateName` fatal naming neither the island nor the reservation)
/// or, as a `private` declaration, shadowed the alias inside the user's own islands. Which of
/// the two happened depended on the lane and on whether that Rust type got a face. The
/// reservation is namespace-wide because nothing narrower can be decided at declaration time.
/// One spelling, shared with the generator, so the two cannot drift.
pub const ODT_ALIAS_PREFIX: &str = "trust_type_";

/// Trust (TG16, after TG10/TG11): the root of the compiler's nominal ODT identities
/// (`TrustOdt.k<crate>_<path>` and the constructors, recursors and fields the kernel registers
/// under them). Reserved for the reason [`ODT_ALIAS_PREFIX`] is.
pub use trust_odt::KERNEL_ROOT as ODT_KERNEL_ROOT;

/// Why an island may not declare `name`: it lies in a namespace the compiler mints into —
/// E6 program-function imports ([`KERNEL_IMPORT_PREFIX`]), seeded kernel models
/// ([`SEEDED_MODEL_PREFIX`]), readable ODT aliases ([`ODT_ALIAS_PREFIX`]) or nominal ODT
/// identities ([`ODT_KERNEL_ROOT`]).
///
/// Both lanes call it on the name the kernel registered, so `namespace`, `section`, dotted and
/// `_root_` spellings are all seen fully qualified. A `private` declaration registers under a
/// mangled `_private.…` name that cannot collide in the kernel, but it resolves under its
/// user-facing spelling inside the user's own islands — where it would shadow the compiler's
/// constant — so that spelling is checked too.
pub(crate) fn reserved_namespace_error(name: &clean_kernel::Name) -> Option<String> {
    let user_facing = clean_elab::private_names::user_facing_name(name);
    let spelling = user_facing.to_string();
    if spelling.starts_with(KERNEL_IMPORT_PREFIX) {
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
        // The import-island recovery guard keys on this wording
        // (`KERNEL_IMPORT_DECLARATION_REFUSAL`, `4be596b7005`).
        return Some(format!(
            "Clean island declaration `{user_facing}` {KERNEL_IMPORT_DECLARATION_REFUSAL} \
             (`trust_import_*`); that namespace is reserved for E6 program-function imports \
             and an island may not define or shadow a name in it"
        ));
    }
    if spelling.starts_with(SEEDED_MODEL_PREFIX) {
        // Trust (nat-lift §3.1): the same reservation for the seeded kernel
        // models. See `SEEDED_MODEL_PREFIX` for the capture this prevents.
        return Some(format!(
            "Clean island declaration `{user_facing}` declares into the compiler's seeded-model \
             namespace (`trust_checked_*`); that namespace is reserved for the kernel models \
             the compiler seeds — the signed integer lift among them — and an island may not \
             define or shadow a name in it. Rename the definition; if you need a different \
             model of the same operation, give it your own name and relate the two with a \
             theorem"
        ));
    }
    if spelling.starts_with(ODT_ALIAS_PREFIX) {
        return Some(format!(
            "Clean island declaration `{user_facing}` declares into the compiler's ODT \
             readable-alias namespace (`trust_type_*`); that namespace is reserved for the \
             checked aliases the compiler generates for Rust types, and an island may not \
             define or shadow a name in it. Refer to the generated `trust_type_<crate>__<Type>` \
             names from your theorems, and give your own declarations your own names"
        ));
    }
    if spelling == ODT_KERNEL_ROOT
        || spelling.strip_prefix(ODT_KERNEL_ROOT).is_some_and(|rest| rest.starts_with('.'))
    {
        return Some(format!(
            "Clean island declaration `{user_facing}` declares into the compiler's ODT \
             nominal-type namespace (`{ODT_KERNEL_ROOT}.*`); that namespace is reserved for the \
             nominal identities of Rust types and the members the kernel registers under them, \
             and an island may not define or shadow a name in it. Give your declaration your \
             own name"
        ));
    }
    None
}

/// Authenticate an island [`ConstantKind::Definition`] and install the exact
/// facet/admission pair needed to elaborate calls to it.
///
/// **I2 (decision of record §7).** This is a "`KernelChecked` is required"
/// position. It refuses a reflected Rust carrier — see the two checks at the
/// top of the body — and on success it mints an [`trust_spec_elab::Admission`]
/// carrying `KernelStatus::KernelChecked`, so downstream can tell the two
/// apart by type rather than by inspecting the constant's spelling.
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
    admit_island_definition_named(env, &clean_kernel::Name::from_string(name), name, facets)
}

/// Parse one source identifier without splitting quoted components or accepting an expression.
/// Native AST symbols contain canonical source spelling, not a kernel-name display.
pub fn island_source_name(source: &str) -> Result<clean_kernel::Name, String> {
    clean_parser::parse_name(source)
        .map(clean_parser::SurfaceName::into_name)
        .map_err(|error| format!("invalid Clean declaration identifier `{source}`: {error:?}"))
}

/// The canonical source spelling of a kernel name — the inverse of
/// [`island_source_name`] (a component that is not one plain identifier is
/// quoted, so the one-component `«A.b»` never renders as the two-component
/// `A.b`). `None` for a name with a generated numeric component, which has no
/// identifier spelling; callers keep the typed name as the identity.
#[must_use]
pub fn island_source_spelling(name: &clean_kernel::Name) -> Option<String> {
    clean_parser::SurfaceName::from_name(name.clone()).source_spelling()
}

/// Admit the exact structural declaration supplied by the native source reader.
/// Facet keys still use source syntax. Names with generated numeric components
/// cannot be represented by that transport yet and are refused, never flattened.
pub fn admit_certified_island_definition_for_name(
    env: &KernelEnvironment,
    declaration: &clean_kernel::Name,
    facets: &mut trust_spec_elab::FacetTable,
) -> Result<trust_spec_elab::Admission, String> {
    let name = clean_parser::SurfaceName::from_name(declaration.clone())
        .source_spelling()
        .filter(|spelling| !spelling.is_empty())
        .ok_or_else(|| "the island facet transport cannot encode this generated declaration name; retain its structural identity and extend the transport before admission".to_string())?;
    admit_island_definition_named(env, declaration, &name, facets)
}

fn admit_island_definition_named(
    env: &KernelEnvironment,
    kernel_name: &clean_kernel::Name,
    name: &str,
    facets: &mut trust_spec_elab::FacetTable,
) -> Result<trust_spec_elab::Admission, String> {
    refuse_reflected_carrier(name, kernel_name, facets)?;
    let cached = cached_island_admission_under_key(facets, name, name)?;
    let admission = audited_island_definition_admission(env, kernel_name, name)?;
    install_island_admission(facets, name, admission, cached)
}

/// Record a Clean-origin def's identity under the RUST def-path of the item
/// the compiler materialized for it (joint Rust+Lean cited lane, 2026-09-15).
///
/// This is the one channel through which "the Rust callee `crate::pb_max` IS
/// the kernel constant `pb_max`" enters the facet table, and it is written by
/// the compiler from its Clean-origin registry — the same registry
/// `rustc_resolve` filled when it minted the `DefId`, and the only authority on
/// that pairing. Nothing in this crate derives it: `admit_function_into`'s
/// forwarding arm READS the row back through
/// [`trust_spec_elab::FacetTable::admitted`] and
/// [`trust_spec_elab::Admission::require_kernel_check`], and a def-path with no
/// such row simply fails closed, however its last segment happens to be spelled.
///
/// The admission recorded is the SAME certification-audited, `KernelChecked`
/// admission [`admit_certified_island_definition_for_name`] mints — same
/// audit, same status seam, same declared-carrier read — keyed under
/// `rust_def_path` instead of the Clean source spelling. Its four facets are
/// `Certified` for the reason that function's are: a strict Clean definition is
/// pure, total, deterministic and panic-free by the kernel language's
/// semantics. The caller is responsible for one fact this crate cannot see —
/// that the MATERIALIZED Rust body carries no caller precondition (a Clean
/// declaration whose hypothesis binder was erased into a runtime obligation is
/// not panic-free at every call site) — and must not call this for a def whose
/// plan of record states one.
///
/// Refuses (fail-closed, never overwrites): an empty or reserved-namespace
/// def-path, a reflected carrier, any audit failure, and a facet record already
/// present under `rust_def_path` that is not this exact admission (modulo the
/// stand-in disclosures below, which only ever grow).
///
/// # The stand-in qualification is a PARAMETER, not an option
///
/// Trust (GREEN THAT LIES, `docs/KNOWN_HAZARDS.md` 2026-09-18). An `import
/// Mathlib` inside a `clean { … }` island is served by Clean's built-in
/// prelude STAND-IN, never by the library of that name, and
/// [`CleanIslandOutcome::standin_imports`] states the invariant: a consumer
/// that reports `registered` must report these alongside it. THIS seam is such
/// a consumer at one remove — it reports a `Certified` row on a RUST function,
/// derived from the registered island environment — and the invariant did not
/// literally reach it, because it never reports `registered` itself. That is
/// the whole defect: nothing was forged (the kernel really re-checked the
/// declaration and [`audited_island_definition_admission`] really ran the
/// audit), the row was simply missing the QUALIFICATION.
///
/// `standin_imports` is therefore a required parameter rather than an
/// attachment the caller may forget: pass
/// [`CleanIslandSession::standin_imports`] of the session whose environment
/// `env` is. An empty slice is the honest value for a session with no
/// substitution, and it is the only way to record "no qualification" — which a
/// reader of this call can see at the call site. Passing them NEVER changes
/// whether the row is minted or how strong it is: a stand-in-served island
/// stays admissible, exactly as authors rely on.
pub fn admit_clean_origin_callee_identity(
    env: &KernelEnvironment,
    declaration: &clean_kernel::Name,
    rust_def_path: &str,
    standin_imports: &[CleanIslandStandinImport],
    facets: &mut trust_spec_elab::FacetTable,
) -> Result<trust_spec_elab::Admission, String> {
    let name = clean_parser::SurfaceName::from_name(declaration.clone())
        .source_spelling()
        .filter(|spelling| !spelling.is_empty())
        .ok_or_else(|| "the island facet transport cannot encode this generated declaration name; retain its structural identity and extend the transport before admission".to_string())?;
    if rust_def_path.is_empty() {
        return Err(format!(
            "Clean-origin identity for `{name}` requires the materialized item's def-path"
        ));
    }
    if rust_def_path.starts_with(KERNEL_IMPORT_PREFIX) {
        return Err(format!(
            "Clean-origin identity key `{rust_def_path}` lies in the reserved kernel-import \
             namespace `{KERNEL_IMPORT_PREFIX}*`; a Clean declaration may not be recorded there"
        ));
    }
    refuse_reflected_carrier(&name, declaration, facets)?;
    let cached = cached_island_admission_under_key(facets, rust_def_path, &name)?;
    let admission = audited_island_definition_admission(env, declaration, &name)?
        // The green travels with its qualification, in the ONE wording every
        // compiler seam uses. Rendered here, at the mint, so no consumer has
        // to know how to spell it.
        .with_standin_disclosures(standin_imports.iter().map(CleanIslandStandinImport::disclosure));
    install_island_admission(facets, rust_def_path, admission, cached)
}

/// I2 — a REFLECTED Rust carrier may not be admitted as a Clean declaration.
/// See the long comment in [`audited_island_definition_admission`]'s caller
/// history: two independent checks, the typed status and the reserved-namespace
/// backstop, so an admitter that cannot tell Reflected from KernelChecked
/// refuses.
fn refuse_reflected_carrier(
    name: &str,
    kernel_name: &clean_kernel::Name,
    facets: &trust_spec_elab::FacetTable,
) -> Result<(), String> {
    // ------------------------------------------------------------------
    // I2 — a REFLECTED Rust carrier may not be admitted here.
    // ------------------------------------------------------------------
    // This function is the GATE in front of the compiler's "`KernelChecked` is
    // required" admitters — `admit_island_definition_named` (keyed by the Clean
    // source spelling) and `admit_clean_origin_callee_identity` (keyed by the
    // materialized Rust item's def-path). Both run it first, and each then
    // stamps four `FacetStatus::Certified { evidence:
    // "clean-island-kernel-definition" }` facets through
    // `install_island_admission`. This function stamps nothing itself; it only
    // refuses, which is why the refusal has to be complete here — no admitter
    // re-examines the carrier after it returns `Ok`. Those admitters exist to
    // authenticate a Clean declaration the CIC kernel re-checked.
    //
    // A `trust_import_*` constant is not that. It is a Rust `fn` projected into
    // the environment by
    // `admit_function_into`: the kernel checked that the carrier's body inhabits
    // its type, and never checked that the constant DENOTES that `fn`. The
    // compiler asserts the correspondence, and it is TCB.
    //
    // Before I2 this call SUCCEEDED on a reflected carrier — the reflexive
    // `name = name` audit passes for it, because the declaration really is a
    // well-formed kernel Definition — and the environment then carried a row
    // claiming `clean-island-kernel-definition` evidence for a reflection, a
    // claim the kernel never made. Two independent checks close it:
    //
    //  1. the TYPED one: ask the admission record what status the constant was
    //     minted under. The real caller (`trust_verify.rs`'s in-walk discharge)
    //     reaches here with the very table the program-function mints were
    //     recorded in, so the provenance is present and does not have to be
    //     guessed from the spelling;
    //  2. the STRUCTURAL backstop: `trust_import_*` is a reserved namespace —
    //     `strict_leaf_policy_error` refuses any island that declares into it —
    //     so a constant there is a reflected carrier by construction, even when
    //     the caller hands us a table that never saw the mint. Fail-closed: an
    //     admitter that cannot tell Reflected from KernelChecked must refuse.
    if let Some(status) = facets.kernel_const_status(name)
        && let Err(refusal) = status.require_kernel_check(name)
    {
        return Err(refusal.to_string());
    }
    if name.starts_with(KERNEL_IMPORT_PREFIX)
        || kernel_name.to_string().starts_with(KERNEL_IMPORT_PREFIX)
    {
        return Err(trust_symbols::KernelStatus::Reflected
            .require_kernel_check(name)
            .expect_err("Reflected never satisfies a kernel-check requirement")
            .to_string());
    }
    Ok(())
}

/// The idempotence candidate already recorded under `key`, if any: an existing
/// record is acceptable ONLY when it is a `KernelChecked` admission of this very
/// constant; anything else under the key is a collision and refuses.
fn cached_island_admission_under_key(
    facets: &trust_spec_elab::FacetTable,
    key: &str,
    kernel_const: &str,
) -> Result<Option<trust_spec_elab::Admission>, String> {
    if facets.get(key).is_none() {
        return Ok(None);
    }
    // A prior admission is only an idempotence candidate. The caller may
    // reuse its facet table with a changed or entirely different kernel
    // environment. Re-audit the CURRENT declaration and dependency closure
    // before comparing the complete freshly derived admission.
    if let Some(existing) = facets.admitted(key)
        && existing.kernel_const == kernel_const
        && existing.require_kernel_check().is_ok()
    {
        return Ok(Some(existing.clone()));
    }
    if key == kernel_const {
        return Err(format!(
            "island definition `{kernel_const}` collides with an existing program-function facet key"
        ));
    }
    Err(format!(
        "Clean-origin identity for `{kernel_const}` collides with an existing facet record under \
         `{key}` that is not this declaration's kernel-checked admission"
    ))
}

/// Install a freshly audited admission under `key`, or — when `cached` holds a
/// prior admission under that key — require the fresh one to be identical
/// APART FROM the stand-in disclosure set, which is merged monotonically. A
/// refusal never modifies either map.
///
/// # Why the disclosure set is the one field allowed to differ
///
/// Trust (GREEN THAT LIES, 2026-09-18). The compiler records Clean-origin
/// identity rows TWICE — once before the body walk, once after the deferred
/// island suffix is kernel-checked — and a deferred island may be the one that
/// spells `import Mathlib`. Under a strict equality the second call would
/// refuse, leaving the row admitted under the EARLIER, less-qualified
/// disclosure set: the row would survive (so no verdict moves) carrying less
/// qualification than the compilation now knows about. That is precisely the
/// under-disclosure this record exists to prevent, so the merge takes the
/// UNION and the set only ever grows.
///
/// The relaxation is confined to a field that carries no authority: everything
/// the kernel, the elaborator and the capability firewall read — status,
/// capability, kernel constant, arity, carriers, param names, proof-only-via
/// and return domain, i.e. every OTHER field of [`trust_spec_elab::Admission`]
/// — is still compared exactly, because the comparison is still the derived
/// `PartialEq`, so a matching term hash still cannot authorize mutated
/// admission fields.
fn install_island_admission(
    facets: &mut trust_spec_elab::FacetTable,
    key: &str,
    admission: trust_spec_elab::Admission,
    cached: Option<trust_spec_elab::Admission>,
) -> Result<trust_spec_elab::Admission, String> {
    if let Some(existing) = cached {
        // This comparison also retains carrier/signature/capability restrictions:
        // a matching term hash alone cannot authorize mutated admission fields.
        // Rebasing the FRESH admission onto the cached disclosure set is what
        // takes that one field out of the comparison, without a second
        // equality relation that could drift from `PartialEq`.
        let rebased = admission
            .clone()
            .with_standin_disclosures(existing.standin_disclosures().iter().cloned());
        if existing != rebased {
            return Err(format!(
                "cached admission for island definition `{}` no longer matches the \
                 current checked declaration or admission metadata; use a fresh facet table \
                 after rebuilding the environment; the existing entry was not overwritten",
                admission.kernel_const
            ));
        }
        let mut merged: Vec<String> = existing.standin_disclosures().to_vec();
        for line in admission.standin_disclosures() {
            if !merged.iter().any(|known| known == line) {
                merged.push(line.clone());
            }
        }
        if merged.len() == existing.standin_disclosures().len() {
            return Ok(existing);
        }
        // Qualification-only update: same audited admission, more of the
        // disclosure it must be read relative to.
        let qualified = existing.with_standin_disclosures(merged);
        facets.admit(key, qualified.clone());
        return Ok(qualified);
    }
    let certified = || trust_spec_elab::FacetStatus::Certified {
        evidence: "clean-island-kernel-definition".to_string(),
    };
    // All fallible checking and exact encoding has finished. A refusal above
    // leaves both the diagnostic facet map and admission map untouched.
    facets.insert(
        key,
        trust_spec_elab::FnFacets {
            pure: certified(),
            total: certified(),
            deterministic: certified(),
            no_panic: certified(),
        },
    );
    facets.admit(key, admission.clone());
    Ok(admission)
}

/// Authenticate an island [`ConstantKind::Definition`] and derive its
/// admission — the certification audit and the `KernelChecked` status mint —
/// WITHOUT touching any facet table. The two installers above decide the key.
fn audited_island_definition_admission(
    env: &KernelEnvironment,
    kernel_name: &clean_kernel::Name,
    name: &str,
) -> Result<trust_spec_elab::Admission, String> {
    let info = env
        .get_const(kernel_name)
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
    if env.is_unsafe(kernel_name) {
        return Err(format!("island definition `{name}` is unsafe"));
    }
    if env.is_partial(kernel_name) {
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
    let subject = clean_kernel::Expr::const_(kernel_name.clone(), Vec::new());
    let goal = clean_kernel::Expr::apps(
        clean_kernel::Expr::const_(clean_kernel::Name::from_string("Eq"), vec![level.clone()]),
        [info.type_.clone(), subject.clone(), subject.clone()],
    );
    let proof = clean_kernel::Expr::apps(
        clean_kernel::Expr::const_(clean_kernel::Name::from_string("Eq.refl"), vec![level]),
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

    let (arity, ret_domain) = island_definition_signature_for_name(env, kernel_name)
        .ok_or_else(|| format!("island definition `{name}` has no supported arity"))?;
    // The DECLARED carriers, straight from the kernel's recorded type for this
    // constant — the only authority on what the island author actually wrote.
    // `None` (an unrecognized carrier anywhere in the telescope) leaves the
    // clause elaborator on its pre-increment single-ambient-domain behaviour,
    // which is fail-closed, not permissive.
    //
    // The arity CROSS-CHECK is not decoration: `arity` above and `params` here
    // are two independent walks of the same Pi telescope, and the elaborator
    // indexes arguments by one while checking against the other. A disagreement
    // means one of the two reads the declaration wrongly, so drop the carrier
    // record rather than index into a list that does not describe this
    // constant.
    let carriers =
        island_definition_carriers_for_name(env, kernel_name).filter(|c| c.params.len() == arity);
    // ------------------------------------------------------------------
    // I2 — mint the status through the sealed seam.
    // ------------------------------------------------------------------
    // `trust_symbols::CicKernelRecheck::held_by_kernel_recheck` is an
    // ASSERTION, and this is the review it exists to concentrate. Its three
    // clauses, against what just happened above:
    //
    //  1. "the kernel re-checked the declaration's own obligation — not a
    //     sibling's, not a synthetic `name = name`, not a parse". The goal here
    //     IS syntactically `name = name`, and that caveat is the reason this
    //     paragraph exists rather than a one-line call. It holds anyway, and
    //     for a checked reason: `cert_meter::grade` delegates to
    //     `Environment::audit_certification`, which collects the const refs of
    //     goal AND term — `name` among them — and then runs
    //     `check_decl_readonly_strict` on the RECONSTRUCTED declaration of
    //     every reachable constant
    //     (`first-party/clean/crates/clean-kernel/src/env/axiom_audit.rs:1242`,
    //     `:1284`). That call re-checks this definition's own `value : type`
    //     obligation. The reflexivity is the vehicle that puts the declaration
    //     into the audited closure, not a substitute for checking it — which is
    //     what the caveat forbids.
    //  2. "the caller can produce the exact term that was checked". The digest
    //     below is taken over this declaration's own type and value, the two
    //     halves of the obligation `check_decl_readonly_strict` re-checked.
    //  3. "the caller ran the full certification audit, so the AxiomClosure
    //     distinguishes audited-empty from not audited". `cert_meter::grade`
    //     returned `Certified`, which is exactly `audit.is_certified()` — an
    //     EMPTY issue list over the unfiltered transitive closure. `Trusted`
    //     (a non-empty closure) and `Rejected` both returned `Err` above and
    //     never reach here, so `audited([])` is the honest closure and not an
    //     `unrecorded()` one.
    //
    // A reflected Rust carrier deliberately does not come through here: it gets
    // `Reflected`, which needs no token, because its correspondence to the Rust
    // item is TCB.
    use trust_symbols::KernelAuthority as _;
    let digest = exact_admission::definition_digest(kernel_name, info)?;
    let status = trust_symbols::CicKernelRecheck::held_by_kernel_recheck()
        .kernel_checked(digest, trust_symbols::AxiomClosure::audited([]));
    debug_assert!(status.is_certified(), "a Certified grade must project to a Certified status");
    let admission = trust_spec_elab::Admission::kernel_checked(name, arity, status)
        .with_declared_signature(ret_domain, carriers);
    // Record the island definition's RETURN domain — the Pi-telescope codomain
    // of the type the kernel just re-checked — so a variable-free clause atom
    // citing it (`answer() == c42(0)`) is typed at the definition's own
    // carrier rather than the `Nat` default. Steering only: an unmapped
    // codomain attaches nothing and the fail-closed default stays.
    Ok(match island_return_domain(env, &info.type_) {
        Some(domain) => admission.with_return_domain(domain),
        None => admission,
    })
}

/// The elaboration [`trust_spec_elab::Domain`] named by an island
/// definition's RETURN type — the Pi-telescope codomain of its declared
/// kernel type — or `None` when the codomain is not one of the closed
/// carriers the clause fragment supports, in which case no return domain is
/// recorded and a variable-free atom keeps its fail-closed default. `BitVec
/// _` is deliberately unanswered: `i64`, `u128`, and `usize64` all share that
/// carrier, so the codomain alone cannot name the Rust-side domain.
///
/// Trust (2026-11-10, E9-RESULT-CARRIER-4): the codomain is read by
/// [`carrier_of_clean_type`], the reader the binders already use, and mapped
/// back only through [`trust_spec_elab::Carrier::unique_domain`], the one
/// partial inverse of `Domain -> Carrier`: a domain is recorded exactly when
/// the carrier has a single preimage. That reader sees through a closed,
/// transparent, monomorphic type alias, so `def f (a : Bool) : Flag` with
/// `abbrev Flag := Bool` records `Bool`, as its binders already read. This
/// function matched the codomain's spelled constant name before, so an alias
/// recorded no domain and every `-> bool` proposition arm refused the call
/// (TG15 residual 1). For every non-alias codomain the answer is unchanged:
/// `unique_domain` maps exactly the spelled set the match had, `BitVec N`
/// still answers `None`, and `Option (BitVec N)` now answers the
/// `OptionSigned(N)` the declared signature already records for it.
fn island_return_domain(
    env: &KernelEnvironment,
    ty: &clean_kernel::Expr,
) -> Option<trust_spec_elab::Domain> {
    let mut codomain = ty;
    while let clean_kernel::ExprKind::Pi(_, _, next) = codomain.kind() {
        codomain = next;
    }
    carrier_of_clean_type(env, codomain)?.unique_domain()
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
/// other). TG9 also requires the full certification audit of that closed
/// judgment before returning Certified, including raw trustc callers.
/// No hand-rolled equality, no textual expansion — the divergence
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

/// The CLOSED candidate proof for a whole elaborated goal: strip the Pi
/// telescope, build the [`defeq_proof_for_goal`] term for the body, and mirror
/// the telescope back as lambdas. Shared by the grade route below and by the
/// evidence producer ([`ensures_evidence`]) so the term that ships is, by
/// construction, the term the kernel was asked to judge.
fn defeq_closed_proof(goal: &clean_kernel::Expr) -> Result<clean_kernel::Expr, String> {
    // Strip the Pi telescope, remembering binders for the mirroring lambda.
    let mut binders: Vec<(clean_kernel::BinderData, clean_kernel::Expr)> = Vec::new();
    let mut body: &clean_kernel::Expr = goal;
    while let clean_kernel::ExprKind::Pi(bd, domain, codomain) = body.kind() {
        binders.push((*bd, (**domain).clone()));
        body = codomain;
    }
    let refl = defeq_proof_for_goal(body)?;
    Ok(binders
        .into_iter()
        .rev()
        .fold(refl, |acc, (bd, domain)| clean_kernel::Expr::lam(bd, domain, acc)))
}

#[must_use]
pub fn kernel_prove_ensures_by_defeq(
    env: &Environment,
    clause_src: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &trust_spec_elab::FacetTable,
) -> CitationVerdict {
    kernel_prove_ensures_by_defeq_in(
        env,
        clause_src,
        param_types,
        self_fn_name,
        facets,
        &trust_spec_elab::ProofClauseInputs::strict(),
    )
}

/// Trust (nat-lift): [`kernel_prove_ensures_by_defeq`] with the CLAUSE MODE
/// stated.
#[must_use]
pub fn kernel_prove_ensures_by_defeq_in(
    env: &Environment,
    clause_src: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &trust_spec_elab::FacetTable,
    inputs: &trust_spec_elab::ProofClauseInputs,
) -> CitationVerdict {
    let (goal, seeded) =
        match lifted_ensures_goal(env, clause_src, param_types, self_fn_name, facets, inputs) {
            Ok(pair) => pair,
            Err(verdict) => return verdict,
        };
    let env = seeded.as_ref().unwrap_or(env);
    // The elaborated goal is the single most useful thing a user can be told
    // when a citation or a defeq discharge fails, and nothing printed it: the
    // author saw "not definitionally equal" or "bindings are not exact" with no
    // way to see the proposition the kernel was actually asked to close. Since
    // a cited theorem must be stated over the COMPILER'S encoding of the body,
    // not seeing that encoding makes the citation lane guess-and-check. This is
    // the cheap stand-in for the unbuilt `targo trust spec --emit clean`.
    if e9_debug_enabled() {
        eprintln!("TRUST_E9_DEBUG GOAL clause={clause_src:?} goal={goal}");
    }
    // The same ill-typed-goal gate as the citation route: `check_type` below
    // judges the PROOF term and treats the goal expression as given, so it
    // must not be handed a goal the kernel cannot type (see
    // [`reject_untyped_goal`]).
    if let Some(verdict) = reject_untyped_goal(env, &goal) {
        return verdict;
    }
    let proof = match defeq_closed_proof(&goal) {
        Ok(proof) => proof,
        Err(detail) => return CitationVerdict::StatementOrCertificationRejected { detail },
    };
    let (checked, stop) = crate::kernel_stop::check_type_naming_stop(
        clean_kernel::TypeChecker::new(env),
        &proof,
        &goal,
    );
    if checked.is_err() {
        return CitationVerdict::StatementOrCertificationRejected {
            detail: defeq_decline_detail(stop),
        };
    }
    // Trust: TG9 — conversion alone does not audit the goal/proof's complete
    // declaration closure. Raw trustc must apply the cited route's full audit
    // before granting authority, even when no evidence payload is requested.
    match cert_meter::grade(env, &goal, &proof) {
        cert_meter::Grade::Certified => CitationVerdict::KernelStatementMatchCertified,
        cert_meter::Grade::Trusted { closure } => {
            CitationVerdict::KernelStatementMatchTrusted { closure }
        }
        cert_meter::Grade::Rejected { error } => {
            CitationVerdict::StatementOrCertificationRejected { detail: error }
        }
    }
}

/// The detail of a declined `Eq.refl` check. The compiler calls
/// [`kernel_prove_ensures_by_defeq_in`] directly, with no certify run around it
/// to read a stop (KERNEL-STOP-1, `docs/DECISION_QUEUE.md`), so a decline a
/// count ended names that count here. The verdict stays a rejection
/// (fail-closed); only its detail stops claiming the two sides differ when the
/// kernel stopped before deciding.
fn defeq_decline_detail(stop: Option<trust_types::determinism::StopCause>) -> String {
    use trust_types::determinism::StopCause;
    match stop {
        None => "the two sides are not definitionally equal (Eq.refl does not check)".to_string(),
        Some(StopCause::Effort) => "the clean kernel's heartbeat count ran out before Eq.refl \
                                    checked (stop: effort), so the two sides were not shown to \
                                    differ"
            .to_string(),
        Some(StopCause::Unclassified) => "the kernel's declaration budget ran out before Eq.refl \
                                          checked (stop: unclassified), so the two sides were not \
                                          shown to differ"
            .to_string(),
        Some(cause) => format!(
            "the kernel stopped before Eq.refl checked (stop: {cause}), so the two sides were not \
             shown to differ"
        ),
    }
}

/// An elaborated clause goal must itself TYPECHECK before any discharge is
/// attempted against it. The kernel's definitional-equality judgment computes
/// on the goal AS A TERM and does not re-derive its typing, so a clause that
/// applies an island definition at a different carrier than its declared
/// domain (`def ident_i (x : Int) : Int := x` called from an `i64`- or
/// `u64`-typed clause) elaborates to an ILL-TYPED equality whose two sides can
/// still CONVERGE computationally — and `Eq.refl` or a cited proof term is
/// then accepted against a proposition that does not type. Measured
/// 2026-08-23 on fragment probe f13 and its u64 twin: the acceptance predates
/// the signed widening (the widening only made it reachable from `iN`
/// clauses). Fail closed instead, and carry the fix.
fn reject_untyped_goal(env: &Environment, goal: &clean_kernel::Expr) -> Option<CitationVerdict> {
    // `infer_sort` is the kernel's FULL-CHECKING validation entry (the one
    // `add_decl` itself uses; `infer_only=false`, so application arguments
    // are actually checked — plain `infer_type` deliberately skips that and
    // accepts the ill-typed application this gate exists to catch).
    match clean_kernel::TypeChecker::new(env).infer_sort(goal) {
        Ok(_) => None,
        Err(error) => Some(CitationVerdict::ClauseOutsideFragment {
            reason: format!(
                "the elaborated goal does not typecheck ({error:?}); a call in the clause most \
                 likely applies an island definition at a different carrier than its declared \
                 domain — restate the island definition over the clause's carrier, or change \
                 the clause to compare values of one carrier (TRUST_E9_DEBUG prints the exact \
                 goal)"
            ),
        }),
    }
}

/// Shared, soundness-critical tail: reject a goal the kernel cannot TYPE
/// (see [`reject_untyped_goal`]), look up the cited theorem, reject a
/// non-theorem / unsafe / partial / proofless declaration, then grade its proof
/// term against `goal` via `cert_meter::grade` (the transitive
/// sorry/axiom-closure + proof-checks-goal audit). `Certified` is the ONLY
/// dischargeable verdict; `Trusted` (axiom/marker-tainted) and `Rejected` are
/// not.
///
/// **I3 disposition, recorded so the next reader does not have to re-derive
/// it.** This lookup is the second of the two name→symbol sites (the other is
/// `trust_spec_elab`'s call arm, which is where the firewall is enforced), and
/// it deliberately consults NO capability. Citing a theorem is a PROOF position
/// — §4.1.1 gives PROOF total observer capability over every declaration
/// including private internals, with zero annotations — so a capability check
/// here could only ever refuse something the ratified semantics permits. The
/// `TheoremNotFound` below is therefore not the forbidden "not found": it fires
/// only when the constant is genuinely absent from the environment, never when
/// a visible declaration is merely unexecutable. A CALL-position consumer of
/// this machinery does not exist and must not be added here; it belongs on
/// `trust_spec_elab::elaborate_goal_typed_in`, which takes the use site's
/// capability and answers with `ProofOnlyRefusal`.
fn grade_cited_theorem_against_goal(
    env: &Environment,
    theorem: &str,
    goal: &clean_kernel::Expr,
) -> CitationVerdict {
    if let Some(verdict) = reject_untyped_goal(env, goal) {
        return verdict;
    }
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

/// The BODY-INDEPENDENT half of a citation check: everything that can be
/// enforced about a cited theorem without knowing the clause's goal.
///
/// `Ok(())` means exactly: `theorem` is registered, is a `theorem` (not a
/// definition, opaque or axiom), is neither `unsafe` nor `partial`, carries a
/// proof term, and that term passes the strict certification audit against the
/// theorem's OWN declared statement — so its complete transitive closure is
/// free of `sorry`, trust markers and non-foundational axioms. `Err` carries
/// the ordinary refusal verdict, reported exactly as the citation lanes report
/// it.
///
/// WHAT THIS IS NOT. It says NOTHING about whether the theorem proves any
/// clause: the goal handed to the audit is the theorem's own type, never a
/// clause's. That is why the success value is `()` and not a
/// [`CitationVerdict`] — there is no `KernelStatementMatch*` to return, and a
/// caller cannot mistake a clean audit for a statement match or a discharge.
///
/// The one caller is the `-Ztrust-verify=off` citation sweep, for a cited
/// `ensures` whose goal mentions `result`. That lane imports no function body,
/// so the discharge goal (`result` bound to the defining equation) cannot be
/// built and the clause cannot be judged there; this keeps the unverified lane
/// enforcing what it CAN — a citation of a missing, non-theorem, `sorry`- or
/// axiom-backed declaration still fails the build — without pretending to
/// have judged the rest. Grading against the theorem's own statement also
/// SEPARATES the two failure classes the ordinary grade merges: a statement
/// mismatch co-occurring with an axiom in the closure grades `Rejected` there
/// (any non-assumption issue wins), which would hide the axiom; here the root
/// judgment holds by construction, so an assumption surfaces as the
/// provenance failure it is.
pub fn kernel_audit_cited_theorem(env: &Environment, theorem: &str) -> Result<(), CitationVerdict> {
    let theorem_name = clean_kernel::Name::from_string(theorem);
    let Some(info) = env.get_const(&theorem_name) else {
        return Err(CitationVerdict::TheoremNotFound);
    };
    // The remaining declaration checks (theorem / unsafe / partial / proof
    // term) are `grade_cited_theorem_against_goal`'s own, run against the
    // declared statement so there is one implementation of them.
    let statement = info.type_.clone();
    match grade_cited_theorem_against_goal(env, theorem, &statement) {
        CitationVerdict::KernelStatementMatchCertified => Ok(()),
        refusal => Err(refusal),
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
///
/// **I2 (decision of record §7): every admission this mints is
/// `trust_symbols::KernelStatus::Reflected`, never `KernelChecked`.** The
/// kernel really did check the minted declaration — `Environment::add_decl`
/// verifies that the value inhabits the type, and a mistaken term is rejected
/// rather than admitted. What the kernel did *not* check, and cannot, is that
/// the constant DENOTES `func`: that correspondence is asserted by this
/// function, from the MIR body, and is TCB (`docs/TCB.md`). A theorem proved
/// about the carrier is therefore only as good as the reflection, which is
/// exactly why the status has to say `Reflected`. The four
/// `trust_spec_elab::admit_*_function` minters below are where the status is
/// attached; this function never upgrades it, and holds no token that could.
/// Trust (#63, R3) — THE FAITHFULNESS GATE for island-def-originated carriers.
///
/// R2 (island `def` -> executable Rust) is the ONE direction in this system that
/// can PRODUCE a value: a divergence there is a **wrong binary**, not a refused
/// proof. Every other gate can only decline to certify. The plan
/// (`docs/plans/2026-08-02-v7-island-parse-and-produce.md` §4, sequencing §6)
/// therefore lands this gate BEFORE R2 is reachable from user code, and its
/// acceptance criterion is the RED case: a generated body that does not match its
/// Clean definition must FAIL THE BUILD.
///
/// MECHANISM — item 10 phase 2 run backwards, zero new kernel machinery:
///  1. the island `def` is admitted for citation
///     ([`admit_certified_island_definition`]);
///  2. the GENERATED carrier body is E6-admitted as its `trust_import_*`
///     constant ([`admit_function_into`] — kernel-checked defining equation,
///     `Reflected` status per I2);
///  3. the goal `∀ params, carrier(params) = def(params)` elaborates through the
///     SAME `elaborate_ensures` path every citation uses, and the kernel judges
///     it by DEFINITIONAL EQUALITY ([`kernel_prove_ensures_by_defeq`]) —
///     unfolding the carrier constant on one side and the island definition on
///     the other. No hand-rolled equality; the kernel is the only judge.
///
/// FAIL-CLOSED at every step, and each rejection names its repair (v7/D3): a
/// carrier body outside the E6 fragment is REFUSED (R2 may only originate bodies
/// this gate can check — that bounds the generator, deliberately), an
/// unmappable parameter type is refused naming the type, and a defeq refusal
/// reports the elaborated goal so the divergence is inspectable.
#[derive(Debug)]
pub enum CarrierFaithfulnessRejection {
    /// The island definition could not be admitted for citation.
    IslandDefinitionNotAdmissible { def_name: String, detail: String },
    /// A carrier parameter (or return) type has no elaborable Rust spelling.
    /// R2's own acceptance says this fails the build naming the type.
    UnrepresentableType { def_name: String, ty: String },
    /// The generated body is outside the E6-recognizable fragment, so the gate
    /// CANNOT check it — which means R2 must not emit it. Extending the
    /// generator requires extending the E6 fragment first, never skipping the
    /// check (v7/D2: extending capability extends the CHECK, never trust).
    CarrierOutsideCheckedFragment { carrier: String },
    /// The kernel refused `carrier ≡ def` — THE red case. The generated binary
    /// would compute something other than the Clean definition.
    NotDefinitionallyEqual { def_name: String, carrier: String, detail: String },
}

/// Trust (#63, R3): kernel-verify that a GENERATED carrier body IS its Clean
/// island definition, by definitional equality. `Ok(())` is the ONLY green;
/// every other outcome must fail the build at the caller.
pub fn check_generated_carrier_faithfulness(
    env: &mut Environment,
    island_def: &str,
    carrier: &trust_types::VerifiableFunction,
    facets: &mut trust_spec_elab::FacetTable,
) -> Result<(), CarrierFaithfulnessRejection> {
    use CarrierFaithfulnessRejection as R;
    // 1. The island definition, admitted for citation.
    let admission =
        admit_certified_island_definition(env, island_def, facets).map_err(|detail| {
            R::IslandDefinitionNotAdmissible { def_name: island_def.to_string(), detail }
        })?;
    // 2. Parameter spellings, from the CARRIER's own signature (what the binary
    //    will actually use). Synthetic names — the goal quantifies over them, so
    //    the source-level names are irrelevant to the proposition.
    let rust_ty = |ty: &trust_types::Ty| -> Option<&'static str> {
        match ty {
            trust_types::Ty::Int { width: 64, signed: false } => Some("u64"),
            trust_types::Ty::Int { width: 64, signed: true } => Some("i64"),
            trust_types::Ty::Int { width: 32, signed: false } => Some("u32"),
            trust_types::Ty::Int { width: 32, signed: true } => Some("i32"),
            trust_types::Ty::Bool => Some("bool"),
            _ => None,
        }
    };
    if carrier.body.arg_count != admission.arity {
        return Err(R::NotDefinitionallyEqual {
            def_name: island_def.to_string(),
            carrier: carrier.def_path.clone(),
            detail: format!(
                "arity mismatch: carrier takes {}, definition takes {}",
                carrier.body.arg_count, admission.arity
            ),
        });
    }
    let mut names: Vec<String> = Vec::new();
    let mut params: Vec<(&str, &str)> = Vec::new();
    for i in 1..=carrier.body.arg_count {
        names.push(format!("x{}", i - 1));
    }
    for (i, local) in (1..=carrier.body.arg_count).zip(names.iter()) {
        let decl = carrier.body.locals.iter().find(|d| d.index == i).ok_or_else(|| {
            R::UnrepresentableType {
                def_name: island_def.to_string(),
                ty: format!("<missing local decl for parameter {i}>"),
            }
        })?;
        let spelled = rust_ty(&decl.ty).ok_or_else(|| R::UnrepresentableType {
            def_name: island_def.to_string(),
            ty: format!("{:?}", decl.ty),
        })?;
        params.push((local.as_str(), spelled));
    }
    // 3. E6-admit the generated body, and RECORD the admission — the ensures
    //    elaborator consults the facet table for it, and an unrecorded mint
    //    fails elaboration with "not E6-admitted" (caught by this gate's own
    //    GREEN control the first time around). A decline means the gate cannot
    //    check this carrier, so the build must refuse it.
    // Trust (E6 expansion P/I1′, review H3): the FROZEN shapes only. A
    // new-reader shape is refused here until it has been measured against
    // this gate, so widening E6 never widens what a generator may emit.
    let Some((_kernel_name, carrier_admission)) =
        admit_function_into_lanes(env, carrier, facets, AdmissionLanes::FrozenShapes)
    else {
        return Err(R::CarrierOutsideCheckedFragment { carrier: carrier.def_path.clone() });
    };
    facets.admit(carrier.def_path.clone(), carrier_admission);
    // 4. The goal: result == island_def(x0, .., xN) over the carrier — the SAME
    //    defeq route every uncited ensures clause takes; the kernel unfolds both
    //    constants and judges.
    let clause = format!("result == {island_def}({})", names.join(", "));
    // Trust (nat-lift): this gate is the CALL direction — an island `def`
    // becoming executable Rust — and it deliberately takes the STRICT entry.
    // The lift exists so a PROOF-position clause can compare a machine value
    // with an unbounded one; letting it in here would let the gate accept a
    // carrier whose Rust body agrees with the definition only after a lift,
    // which is not what "this binary computes that definition" means. The
    // structural guarantee is stronger than the choice: this function takes no
    // mode parameter, so a caller cannot hand it one.
    match kernel_prove_ensures_by_defeq(env, &clause, &params, &carrier.def_path, facets) {
        CitationVerdict::KernelStatementMatchCertified => Ok(()),
        CitationVerdict::ClauseOutsideFragment { reason } => Err(R::NotDefinitionallyEqual {
            def_name: island_def.to_string(),
            carrier: carrier.def_path.clone(),
            detail: format!("goal did not elaborate: {reason}"),
        }),
        other => Err(R::NotDefinitionallyEqual {
            def_name: island_def.to_string(),
            carrier: carrier.def_path.clone(),
            detail: format!("kernel refused definitional equality: {other:?}"),
        }),
    }
}

#[must_use]
/// Mint ONE kernel definition PER FIELD of a struct-returning body, and return
/// them keyed for the discharge lane.
///
/// A clause on an aggregate return names `result.<field>`, never `result`, so
/// what the lane needs is field `i`'s defining expression -- not a Clean
/// structure for the client's ADT, which would mean mapping every client type
/// into the kernel. Each field is minted with the SAME helper its shape would
/// use as a whole body (`admit_projection_function`, `admit_select_function`),
/// under a per-field constant, over the FLATTENED parameter list that
/// `admit_field_projection_function` already established as the calling
/// convention for a signature carrying an aggregate.
///
/// PER FIELD, FAIL-CLOSED. A field whose shape has no mint, or whose operands
/// are not single flattened scalars, is SKIPPED rather than refusing the
/// others -- `sat_term`'s `lit` field is a `Lit`, which flattens to two rows
/// and is not a scalar operand, while its `coeff` field is the cap and mints
/// cleanly. A skipped field simply has no kernel denotation, so a clause naming
/// it fails closed exactly as an unadmitted call does.
///
/// The minted `param_names` are recorded so `elaborate_ensures` can enforce
/// ORDER AGREEMENT against the compiler's own flattening, which is the one
/// failure the kernel cannot catch: the goal would still type, and a theorem
/// about `coeff` would discharge a clause about `degree`.
pub fn admit_function_fields_into(
    env: &mut Environment,
    func: &trust_types::VerifiableFunction,
    facet_table: &trust_spec_elab::FacetTable,
) -> Vec<(String, trust_spec_elab::Admission)> {
    use trust_types::admissible_body::{AdmissibleBody, recognize_admissible_body};
    if !facet_table.get(&func.def_path).is_some_and(trust_spec_elab::FnFacets::admissible) {
        return Vec::new();
    }
    let Some(AdmissibleBody::AggregateFields { fields }) = recognize_admissible_body(func) else {
        return Vec::new();
    };
    let debug = e6_debug_enabled();
    let Some(rows) = param_flat_rows(func) else {
        if debug {
            eprintln!(
                "TRUST_E6_DEBUG field-mint fn={} REFUSED: parameters do not flatten to scalars",
                func.def_path
            );
        }
        return Vec::new();
    };
    // A source parameter is usable as a scalar operand only when its OWN
    // declared type is a scalar domain.
    //
    // Not "flattens to one row": a single-field struct also flattens to one
    // row, and minting its flat position for a `Projection` of the WHOLE
    // parameter would give `result.lit` the term of `lit.var` -- a `Lit`
    // denoted by a `u32`, so a clause comparing the field would compare the
    // wrong thing at the wrong carrier. Caught by
    // `a_struct_returning_body_mints_one_constant_per_field`, which expects a
    // non-scalar field SKIPPED and saw it minted.
    let scalar_flat = |p: usize| -> Option<usize> {
        let local = func.body.locals.iter().find(|l| l.index == p + 1)?;
        ty_to_domain(&local.ty)?;
        Some(rows.iter().take(p).map(Vec::len).sum::<usize>())
    };
    // The flat row of parameter `p`'s FIELD `f` -- what a `FieldProjection`
    // shape names. `-O` copies `self.var` into a temp before building the
    // aggregate, so a constructor that forwards a field of a STRUCT parameter
    // arrives in this shape rather than as a whole-parameter `Projection`.
    // `scalar_flat` cannot serve it: it asks whether the parameter's OWN type
    // is scalar, and here it is deliberately a struct.
    //
    // Admitted ONLY when the parameter is a plain struct whose every field
    // occupies exactly one flat row, which is what makes the field's index
    // equal its offset. A field that itself flattens to several rows (a nested
    // struct) would put the offset somewhere else entirely, so the counts must
    // agree before the index may be used as a position -- the same
    // wrong-carrier hazard `scalar_flat` guards against, one level down.
    let field_flat = |p: usize, f: usize| -> Option<usize> {
        let local = func.body.locals.iter().find(|l| l.index == p + 1)?;
        let trust_types::Ty::Adt { fields: pfields, variants, .. } = &local.ty else {
            return None;
        };
        if !variants.is_empty() || pfields.len() != rows.get(p)?.len() || f >= pfields.len() {
            return None;
        }
        Some(rows.iter().take(p).map(Vec::len).sum::<usize>() + f)
    };
    let trust_types::Ty::Adt { fields: declared, variants, .. } = &func.body.return_ty else {
        if debug {
            eprintln!(
                "TRUST_E6_DEBUG field-mint fn={} REFUSED: return type is not an Adt ({:?})",
                func.def_path, func.body.return_ty
            );
        }
        return Vec::new();
    };
    // An enum's field is variant-relative, and a positional mismatch would key
    // a field's term under another field's name.
    if !variants.is_empty() || declared.len() != fields.len() {
        if debug {
            eprintln!(
                "TRUST_E6_DEBUG field-mint fn={} REFUSED: return type has {} declared field(s) \
                 against {} recognized, or is an enum",
                func.def_path,
                declared.len(),
                fields.len()
            );
        }
        return Vec::new();
    }
    let (domains, names): (Vec<_>, Vec<_>) =
        rows.iter().flatten().cloned().unzip::<_, _, Vec<_>, Vec<_>>();
    let base = mangle_kernel_const(&func.def_path);
    let mut out = Vec::new();
    for (index, (shape, (field_name, _))) in fields.iter().zip(declared.iter()).enumerate() {
        let kernel_const = format!("{base}__f{index}");
        // A field with NO shape is skipped: nothing is claimed for it, so a
        // clause naming it fails closed as an unadmitted call.
        let Some(shape) = shape else { continue };
        let minted = match shape {
            AdmissibleBody::Projection { param } => {
                let Some(flat) = scalar_flat(*param) else { continue };
                trust_spec_elab::admit_projection_function(env, &kernel_const, &domains, flat)
            }
            AdmissibleBody::Select { cmp, cmp_left, cmp_right, then_param, else_param } => {
                use trust_types::admissible_body::SelectCmp as RecCmp;
                let (Some(l), Some(r), Some(t), Some(e)) = (
                    scalar_flat(*cmp_left),
                    scalar_flat(*cmp_right),
                    scalar_flat(*then_param),
                    scalar_flat(*else_param),
                ) else {
                    continue;
                };
                let cmp = match cmp {
                    RecCmp::Lt => trust_spec_elab::SelectCmp::Lt,
                    RecCmp::Le => trust_spec_elab::SelectCmp::Le,
                    RecCmp::Eq => trust_spec_elab::SelectCmp::Eq,
                };
                trust_spec_elab::admit_select_function(
                    env,
                    &kernel_const,
                    &domains,
                    cmp,
                    l,
                    r,
                    t,
                    e,
                )
            }
            AdmissibleBody::FieldProjection { param, field } => {
                let Some(flat) = field_flat(*param, *field) else { continue };
                trust_spec_elab::admit_projection_function(env, &kernel_const, &domains, flat)
            }
            // Every other shape is skipped rather than guessed at.
            _ => continue,
        };
        match minted {
            Ok(mut admission) => {
                admission.param_names = Some(names.clone());
                let key = format!("{}__field_{field_name}", func.def_path);
                if debug {
                    eprintln!(
                        "TRUST_E6_DEBUG field-mint fn={} field={field_name} MINTED as {key}",
                        func.def_path
                    );
                }
                out.push((key, admission));
            }
            Err(reason) => {
                // A field that does not mint leaves a clause naming it failing
                // closed with "no per-field import", which says nothing about
                // WHY. Say it here instead of making the next reader guess.
                if debug {
                    eprintln!(
                        "TRUST_E6_DEBUG field-mint fn={} field={field_name} REFUSED: {reason}",
                        func.def_path
                    );
                }
            }
        }
    }
    out
}

pub fn admit_function_into(
    env: &mut Environment,
    func: &trust_types::VerifiableFunction,
    facet_table: &trust_spec_elab::FacetTable,
) -> Option<(String, trust_spec_elab::Admission)> {
    admit_function_into_lanes(env, func, facet_table, AdmissionLanes::All)
}

/// Which readers and producers an E6 admission may use (E6 admission
/// expansion, design note 2026-09-28 §5).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AdmissionLanes {
    /// Every lane: the frozen `recognize_admissible_body` chain, island
    /// forwarding, and the E6-ONLY reader and producers each increment adds.
    All,
    /// The frozen chain and forwarding only. For
    /// [`check_generated_carrier_faithfulness`], the wrong-BINARY gate: a
    /// generated carrier body it cannot check must not be generated, and a
    /// new-reader shape has not been measured against that gate yet (review
    /// H3), so it stays outside it until an increment measures it there.
    FrozenShapes,
}

fn admit_function_into_lanes(
    env: &mut Environment,
    func: &trust_types::VerifiableFunction,
    facet_table: &trust_spec_elab::FacetTable,
    lanes: AdmissionLanes,
) -> Option<(String, trust_spec_elab::Admission)> {
    use trust_types::admissible_body::{AdmissibleBody, recognize_admissible_body};
    if e6_debug_enabled() {
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
        // The DEFICITS are what a reader actually needs when `admissible` is
        // false: without them the line says a body was refused but not by
        // which facet or why, which cost real time chasing `sat_term`.
        let deficits = facet_table
            .get(&func.def_path)
            .map(|f| f.deficits().join("; "))
            .unwrap_or_else(|| "<no facet record>".to_string());
        // A COMPACT BODY SUMMARY. Three separate recognizer bugs were chased by
        // guessing what `-O` had done to a body -- if-conversion, parameter-slot
        // reuse, block ordering -- because nothing printed the shape. One line
        // per block, naming each statement's destination and rvalue kind and
        // the terminator, ends that.
        let shape: Vec<String> = func
            .body
            .blocks
            .iter()
            .map(|b| {
                let stmts: Vec<String> = b
                    .stmts
                    .iter()
                    .filter_map(|st| match st {
                        trust_types::Statement::Assign { place, rvalue, .. } => Some(format!(
                            "_{}{}={}",
                            place.local,
                            if place.projections.is_empty() { String::new() } else { ".*".into() },
                            match rvalue {
                                trust_types::Rvalue::Use(_) => "use",
                                trust_types::Rvalue::BinaryOp(..) => "binop",
                                trust_types::Rvalue::CheckedBinaryOp(..) => "checked",
                                trust_types::Rvalue::Aggregate(..) => "aggregate",
                                trust_types::Rvalue::Cast(..) => "cast",
                                trust_types::Rvalue::UnaryOp(..) => "unop",
                                _ => "other",
                            }
                        )),
                        _ => None,
                    })
                    .collect();
                let term = match &b.terminator {
                    trust_types::Terminator::Return => "ret".to_string(),
                    trust_types::Terminator::Goto(t) => format!("goto{}", t.0),
                    trust_types::Terminator::SwitchInt { targets, otherwise, .. } => format!(
                        "switch[{}]else{}",
                        targets
                            .iter()
                            .map(|(v, t)| format!("{v}->{}", t.0))
                            .collect::<Vec<_>>()
                            .join(","),
                        otherwise.0
                    ),
                    trust_types::Terminator::Call { .. } => "call".to_string(),
                    other => format!("{other:?}").chars().take(12).collect(),
                };
                format!("bb{}[{}|{}]", b.id.0, stmts.join(","), term)
            })
            .collect();
        eprintln!(
            "TRUST_E6_DEBUG fn={} admissible={} blocks={} arg_count={} calls={:?} recognize={:?} shape={} deficits=[{}]",
            func.def_path,
            admissible,
            func.body.blocks.len(),
            func.body.arg_count,
            call_terms,
            recognize_admissible_body(func),
            shape.join(" "),
            deficits,
        );
    }
    if !facet_table.get(&func.def_path).is_some_and(trust_spec_elab::FnFacets::admissible) {
        return None;
    }
    let kernel_const = mangle_kernel_const(&func.def_path);
    let Some(recognized) = recognize_admissible_body(func) else {
        // No trust-types shape. The one further shape this crate recognizes on
        // its own is the island FORWARDING body (`{ pb_max(lhs, rhs) }` over a
        // kernel-checked Clean definition).
        if let Some(forwarded) = admit_island_forwarding_into(env, func, facet_table, &kernel_const)
        {
            return Some(forwarded);
        }
        // Trust (E6 expansion I1′): then the E6-ONLY reader — consulted only
        // after the frozen chain AND forwarding answered `None`, the pattern
        // forwarding itself uses, so `recognize_admissible_body` (side B of the
        // Clean-origin faithfulness gate) is never widened. Everything it does
        // not read stays unadmitted.
        if lanes == AdmissionLanes::FrozenShapes {
            return None;
        }
        return finish_admission(func, admit_e6_only_body(env, func, &kernel_const)?);
    };
    let result = match recognized {
        AdmissibleBody::ConstantUint { value, width_bits } => {
            let (Some(width), Ok(v)) = (machine_width(width_bits), u64::try_from(value)) else {
                return None;
            };
            // Belt-and-braces: the recognized value must fit the recognized
            // width (Domain::numeral re-checks this downstream and fails
            // closed, but an out-of-range constant should never even reach a
            // mint attempt). `machine_width` restricts `width_bits` to
            // 8/16/32/64, so the shift cannot overflow a u128.
            if value >> width_bits != 0 {
                return None;
            }
            if func.body.arg_count == 0 {
                trust_spec_elab::admit_constant_function(env, &kernel_const, v, width)
            } else {
                // ARITY-PRESERVING route for a constant behind ignored
                // parameters. The recognizer ERASES arity — a unary
                // `fn f(a: u64) -> u64 { 6 }` reports the same
                // `ConstantUint` a nullary one does — and the nullary mint
                // (`admit_constant_function`, type `d`) then hands the defeq
                // comparison a type-mismatched side B against the n-ary side
                // A (`d → … → d`), which is why every unary-constant defeq
                // refused (probe_e3, `fragment_widening_probes.rs`). The
                // expr route mints the lambda-wrapped constant
                // `fun p0 … p_{n-1} => <value>` instead — probe_e3 route 2
                // measured the kernel ADMITs it in both side-A spellings.
                //
                // Guards mirror the Arithmetic arm below:
                // `admit_expr_function` is single-domain, so every parameter
                // must share one domain, the return type must be that same
                // domain, and the recognized constant's width must BE that
                // domain (a constant of a different width than the
                // signature's carrier is a shape this routing must not
                // launder).
                let param_domains = param_domains_of(func)?;
                let domain = trust_spec_elab::Domain::Machine(width);
                if ty_to_domain(&func.body.return_ty).as_ref() != Some(&domain) {
                    return None;
                }
                if param_domains.iter().all(|d| *d == domain) {
                    let names: Vec<String> =
                        (0..func.body.arg_count).map(|i| format!("p{i}")).collect();
                    let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
                    trust_spec_elab::admit_expr_function(
                        env,
                        &kernel_const,
                        &v.to_string(),
                        &name_refs,
                        &domain,
                    )
                } else {
                    // Trust (2026-11-10, E9-CONSTANT-UINT-MIXED-1; TG15 residual
                    // 2): a parameter at a DIFFERENT carrier than the result, as in
                    // `fn six(flag: bool) -> u8 { 6 }`. `admit_expr_function` is
                    // single-domain, so this declined and every clause naming
                    // `six(flag)` was refused. The E6 tree producer mints
                    // `fun p0 … p_{n-1} => 6` with EACH parameter at its own
                    // carrier, exactly as `ConstantInt`'s arity-preserving route
                    // below does, and `add_decl` re-checks it at `d0 → … → UIntW`.
                    // The return-domain guard above is unchanged, so the
                    // recognized constant's width still must BE the signature's
                    // carrier. The all-same-domain case keeps the measured expr
                    // route. Not on the frozen lane, for the reason the signed
                    // twin states: the tree producer is unmeasured against that
                    // gate.
                    if lanes == AdmissionLanes::FrozenShapes {
                        return None;
                    }
                    trust_spec_elab::admit_e6_tree_function(
                        env,
                        &kernel_const,
                        &param_domains,
                        &domain,
                        &trust_spec_elab::E6TreeTerm::Int(i128::from(v)),
                    )
                }
            }
        }
        AdmissibleBody::ConstantInt { value, width_bits } => {
            // The signed sibling. The recognizer already pinned the declared
            // return type to a signed carrier of exactly `width_bits`, pinned
            // the return place `_0` to agree, and range-checked the literal
            // against it. Here: the width must be a supported
            // `MachineSIntWidth`, and — belt and braces over the recognizer —
            // the return type must resolve to exactly that signed domain, so a
            // width the domain table spells differently can never mint.
            let width = signed_machine_width(width_bits)?;
            let domain = trust_spec_elab::Domain::Signed(width);
            if ty_to_domain(&func.body.return_ty).as_ref() != Some(&domain) {
                return None;
            }
            if func.body.arg_count == 0 {
                trust_spec_elab::admit_signed_constant_function(env, &kernel_const, value, width)
            } else {
                // ARITY-PRESERVING route, the signed twin of `ConstantUint`'s
                // (TG15 open item 5). The recognizer erases arity here too:
                // `fn neg1(flag: bool) -> i8 { -1 }` reports the `ConstantInt`
                // a nullary `fn neg1() -> i8 { -1 }` does, and the nullary mint
                // (type `BitVec 8`) left every clause naming `neg1(flag)`
                // refused for arity. The E6 tree producer mints
                // `fun p0 … p_{n-1} => <value>` with EACH parameter at its own
                // carrier (`ConstantUint`'s `admit_expr_function` route is
                // single-domain and would refuse a `bool` parameter beside an
                // `i8` result), and renders the literal through the same
                // `zero`/`numeral`/`negative_numeral` routing
                // `admit_signed_constant_function` uses, so the body is that
                // mint's term under `n` binders; `add_decl` re-checks it at
                // `d0 → … → d_{n-1} → BitVec w`.
                //
                // Not on the carrier-faithfulness gate's frozen lane: the tree
                // producer has not been measured against that gate (review
                // H3), as for the `bool`-equality arm below, and the nullary
                // image this arm minted there before was never a faithful
                // import of an n-ary carrier. The gate refuses the carrier.
                if lanes == AdmissionLanes::FrozenShapes {
                    return None;
                }
                let param_domains = param_domains_of(func)?;
                trust_spec_elab::admit_e6_tree_function(
                    env,
                    &kernel_const,
                    &param_domains,
                    &domain,
                    &trust_spec_elab::E6TreeTerm::Int(value),
                )
            }
        }
        AdmissibleBody::AggregateFields { .. } => {
            // Recognized, but NOT minted -- and this arm is fail-closed on
            // purpose rather than unimplemented by oversight.
            //
            // Every other arm mints ONE Clean definition for the whole
            // function, because every other shape returns a scalar. An
            // aggregate return has no such term: minting it would require
            // mapping the client's ADT onto a Clean structure, which is a far
            // larger commitment than the clause actually needs. What a clause
            // on such a function names is `result.<i>`, so what the discharge
            // lane needs is FIELD i's defining term, not the record's.
            //
            // Recognizing the shape is still worth doing on its own: it is what
            // lets the facet lane admit these bodies, which is what makes
            // `gate_admissible_coverage` demand a contract on them. The clause
            // then discharges through the NATIVE verifier (`sat_term` proves
            // `result.coeff <= degree` that way today) rather than by citation.
            //
            // The next increment is a per-field mint plus an E9 binding for
            // `result.<i>`; until it lands, returning None here means such a
            // function simply carries no kernel import, which is exactly the
            // state the citation lane already fails closed on.
            return None;
        }
        AdmissibleBody::Projection { param } => {
            // Derive every parameter's domain from its declared type; fail
            // closed if any parameter is not a supported machine/bool
            // domain (the projection's return type is the projected
            // parameter's type, which admit_projection_function reads).
            let param_domains = param_domains_of(func)?;
            trust_spec_elab::admit_projection_function(env, &kernel_const, &param_domains, param)
        }
        AdmissibleBody::FieldProjection { param, field } => {
            // The kernel never sees the aggregate: the import is minted over
            // the FLATTENED scalar parameter list, so `fn degree_of(c: Cst)`
            // becomes `fun degree coeff => degree`. The recognizer already
            // pinned the body to `_0 = _p.f` on a by-value struct parameter
            // whose field type IS the return type; this arm maps `(p, f)` onto
            // its position in that flat list and re-checks the carrier.
            let rows = param_flat_rows(func)?;
            if field >= rows.get(param)?.len() {
                return None;
            }
            let flat_index = rows.iter().take(param).map(Vec::len).sum::<usize>() + field;
            let (domains, names): (Vec<_>, Vec<_>) = rows.into_iter().flatten().unzip();
            // Belt and braces over the recognizer's own return-type check: the
            // projected carrier must be the one the function returns.
            if ty_to_domain(&func.body.return_ty).as_ref() != domains.get(flat_index) {
                return None;
            }
            trust_spec_elab::admit_field_projection_function(
                env,
                &kernel_const,
                &domains,
                &names,
                flat_index,
            )
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
        // R2/C9: the param-vs-const compare, routed through the NEW admit
        // route (`admit_select_literal_function` — the phase-1 probes
        // measured that no pre-existing producer could mint this side B).
        // Same boundary translation as the parameter select above; the
        // producer does its own single-domain/Machine-only guards and
        // range-checks the literal fail-closed.
        AdmissibleBody::SelectLiteral { cmp, cmp_param, literal, then_param, else_param } => {
            let param_domains = param_domains_of(func)?;
            use trust_types::admissible_body::SelectCmp as RecCmp;
            let cmp = match cmp {
                RecCmp::Lt => trust_spec_elab::SelectCmp::Lt,
                RecCmp::Le => trust_spec_elab::SelectCmp::Le,
                RecCmp::Eq => trust_spec_elab::SelectCmp::Eq,
            };
            trust_spec_elab::admit_select_literal_function(
                env,
                &kernel_const,
                &param_domains,
                cmp,
                cmp_param,
                literal,
                then_param,
                else_param,
            )
        }
        AdmissibleBody::ComparisonBool { cmp, left, right } => {
            // The recognizer already pinned the declared return type to
            // `bool` and normalized `>`/`>=` by operand swap; the mint enforces
            // the single machine/signed parameter domain (the decision's
            // carrier) and range-checks any literal operand against it.
            let param_domains = param_domains_of(func)?;
            use trust_types::admissible_body::{CmpOperand as RecOp, SelectCmp as RecCmp};
            // Trust (E6 expansion I1′, review H1): a comparison over BOOL
            // operands dispatches ON THE OPERATOR. The recognizer reads
            // `a < b` / `a <= b` over `bool` as `ComparisonBool { Lt | Le }`
            // (and `>`/`>=` by operand swap); those are ORDERINGS
            // (`false < true`), so ONLY `Eq` reaches the new equality producer
            // and an ordering fails closed here — never an `==` image. The
            // frozen `admit_comparison_function` (which refuses `Bool`) is not
            // edited: Clean-origin side B calls it directly.
            let compared = [left, right].into_iter().find_map(|o| match o {
                RecOp::Param(i) => param_domains.get(i).cloned(),
                _ => None,
            });
            if compared == Some(trust_spec_elab::Domain::Bool) {
                if lanes == AdmissionLanes::FrozenShapes {
                    return None;
                }
                let RecCmp::Eq = cmp else {
                    return None;
                };
                let bool_operand = |o: RecOp| match o {
                    RecOp::Param(i) => Some(i),
                    RecOp::Const(_) | RecOp::NegConst(_) => None,
                };
                let result = trust_spec_elab::admit_bool_cmp_function(
                    env,
                    &kernel_const,
                    &param_domains,
                    trust_spec_elab::BoolCmp::Eq,
                    bool_operand(left)?,
                    bool_operand(right)?,
                );
                return finish_admission(func, result);
            }
            let cmp = match cmp {
                RecCmp::Lt => trust_spec_elab::SelectCmp::Lt,
                RecCmp::Le => trust_spec_elab::SelectCmp::Le,
                RecCmp::Eq => trust_spec_elab::SelectCmp::Eq,
            };
            let opnd = |o: RecOp| match o {
                RecOp::Param(i) => trust_spec_elab::CmpOperand::Param(i),
                RecOp::Const(v) => trust_spec_elab::CmpOperand::Const(v),
                RecOp::NegConst(m) => trust_spec_elab::CmpOperand::NegConst(m),
            };
            trust_spec_elab::admit_comparison_function(
                env,
                &kernel_const,
                &param_domains,
                cmp,
                opnd(left),
                opnd(right),
            )
        }
        AdmissibleBody::BoolBinary { op, left, right } => {
            // Each leaf is an already-admissible comparison; the mint composes
            // the two leaf decisions with `Bool.and`/`Bool.or`, matching the
            // clause lane's `A && B` / `A || B` elaboration exactly. The
            // single-domain / literal-range checks live in the mint, shared
            // with the single-comparison arm above.
            let param_domains = param_domains_of(func)?;
            use trust_types::admissible_body::{
                BoolBinOp as RecBoolOp, CmpOperand as RecOp, ComparisonLeaf, SelectCmp as RecCmp,
            };
            let cmp = |c: RecCmp| match c {
                RecCmp::Lt => trust_spec_elab::SelectCmp::Lt,
                RecCmp::Le => trust_spec_elab::SelectCmp::Le,
                RecCmp::Eq => trust_spec_elab::SelectCmp::Eq,
            };
            let opnd = |o: RecOp| match o {
                RecOp::Param(i) => trust_spec_elab::CmpOperand::Param(i),
                RecOp::Const(v) => trust_spec_elab::CmpOperand::Const(v),
                RecOp::NegConst(m) => trust_spec_elab::CmpOperand::NegConst(m),
            };
            let op = match op {
                RecBoolOp::And => trust_spec_elab::BoolBinOp::And,
                RecBoolOp::Or => trust_spec_elab::BoolBinOp::Or,
            };
            let ComparisonLeaf { cmp: lc, left: ll, right: lr } = left;
            let ComparisonLeaf { cmp: rc, left: rl, right: rr } = right;
            trust_spec_elab::admit_bool_binary_function(
                env,
                &kernel_const,
                &param_domains,
                op,
                cmp(lc),
                opnd(ll),
                opnd(lr),
                cmp(rc),
                opnd(rl),
                opnd(rr),
            )
        }
        AdmissibleBody::Arithmetic { op, left, right } => {
            // admit_expr_function is single-domain (every parameter and
            // the result share one domain).
            let param_domains = param_domains_of(func)?;
            let domain = param_domains.first().cloned()?;
            if !param_domains.iter().all(|d| *d == domain)
                || ty_to_domain(&func.body.return_ty).as_ref() != Some(&domain)
            {
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
        AdmissibleBody::CheckedArithmetic { op, width_bits, left, right } => {
            // The recognizer already pinned: the pinned std `Option<iN>`
            // return shape (Direct tag), the exact CheckedBinaryOp dataflow /
            // marked-callee identity, no `Assert`, and in-range operands.
            // Here: every parameter must live at the SIGNED operand carrier
            // of the SAME width (the mint re-checks this), and the width must
            // be a supported `MachineSIntWidth` — anything else fails the
            // import closed.
            let width = signed_machine_width(width_bits)?;
            let param_domains = param_domains_of(func)?;
            use trust_types::admissible_body::{ArithOperand, CheckedArithOp as RecOp};
            let opnd = |o: ArithOperand| match o {
                ArithOperand::Param(i) => trust_spec_elab::CmpOperand::Param(i),
                ArithOperand::Const(v) => trust_spec_elab::CmpOperand::Const(v),
            };
            let op = match op {
                RecOp::Add => trust_spec_elab::CheckedArithOp::Add,
                RecOp::Sub => trust_spec_elab::CheckedArithOp::Sub,
                RecOp::Mul => trust_spec_elab::CheckedArithOp::Mul,
            };
            trust_spec_elab::admit_checked_arithmetic_function(
                env,
                &kernel_const,
                &param_domains,
                op,
                width,
                opnd(left),
                opnd(right),
            )
        }
        AdmissibleBody::GuardedNarrow { from_bits, to_bits, param } => {
            // The recognizer already pinned: the pinned std `Option<iN>`
            // return shape (Direct tag), the exact `i64::MIN`/`i64::MAX`
            // conjunction guard over exactly this parameter, the `Some`-of-its
            // -truncation / `None` arm split with BOTH guard-false edges on
            // the SAME `None` block, no `Assert` and no call. Here: the source
            // and target widths must be supported `MachineSIntWidth`s and
            // every parameter must have a supported domain — anything else
            // fails the import closed. The mint re-checks that the narrowed
            // parameter lives at the source carrier and that the (from, to)
            // pair is the one this increment admits.
            let from = signed_machine_width(from_bits)?;
            let to = signed_machine_width(to_bits)?;
            let param_domains = param_domains_of(func)?;
            trust_spec_elab::admit_guarded_narrow_function(
                env,
                &kernel_const,
                &param_domains,
                from,
                to,
                param,
            )
        }
        AdmissibleBody::WidenedEq {
            from_bits,
            to_bits,
            narrow_param,
            wide_param,
            cast_on_left,
        } => {
            // The recognizer already pinned: one block, exactly the measured
            // cast-then-`Eq` pair, a SIGNED source and a SIGNED strictly-wider
            // target (so the cast is sign extension, never zero extension and
            // never truncation), both operands bare parameters at their own
            // carriers, and a `bool` return. Here: both widths must be
            // supported `MachineSIntWidth`s, every parameter must have a
            // supported domain, and the return type must resolve to `bool` —
            // anything else fails the import closed. The mint re-checks that
            // each parameter lives at the carrier its role requires and that
            // the (from, to) pair is the one this increment admits.
            let from = signed_machine_width(from_bits)?;
            let to = signed_machine_width(to_bits)?;
            if ty_to_domain(&func.body.return_ty) != Some(trust_spec_elab::Domain::Bool) {
                return None;
            }
            let param_domains = param_domains_of(func)?;
            trust_spec_elab::admit_widened_eq_function(
                env,
                &kernel_const,
                &param_domains,
                from,
                to,
                narrow_param,
                wide_param,
                cast_on_left,
            )
        }
        trust_types::admissible_body::AdmissibleBody::Composed { expr } => {
            let param_domains = param_domains_of(func)?;
            let domain = param_domains.first().cloned()?;
            if !param_domains.iter().all(|d| *d == domain)
                || ty_to_domain(&func.body.return_ty).as_ref() != Some(&domain)
            {
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
    finish_admission(func, result)
}

/// The shared tail of every [`admit_function_into`] mint: a refused mint is
/// `None`, a minted one is keyed by the function's def path.
fn finish_admission(
    func: &trust_types::VerifiableFunction,
    result: Result<trust_spec_elab::Admission, String>,
) -> Option<(String, trust_spec_elab::Admission)> {
    result.ok().map(|admission| {
        // Record the callee's RETURN domain on the admission when the typed
        // signature pins one, so a VARIABLE-FREE clause atom (`answer() ==
        // c42(0)` after the ensures-path `result` rewrite) elaborates at the
        // machine domain instead of the `Nat` default — which minted an
        // ill-typed `Eq Nat` over machine-carrier terms and defeq-rejected
        // the e6 f06–f09 probes. Steering only, never authority: a wrong
        // domain yields an ill-typed goal the kernel rejects, and an
        // unsupported return type attaches nothing (the fail-closed default
        // stays in force).
        let admission = match ty_to_domain(&func.body.return_ty) {
            Some(domain) => admission.with_return_domain(domain),
            None => admission,
        };
        (func.def_path.clone(), admission)
    })
}

/// The `KernelChecked` island admission a forwarding body's callee resolves
/// to, or `None` — the ONE identity step of the forwarding lane (joint
/// Rust+Lean cited lane, 2026-09-15).
///
/// The callee is looked up under the def-path the extractor spelled in the
/// `Call` terminator, and only a row the compiler wrote from its Clean-origin
/// registry ([`admit_clean_origin_callee_identity`]) can answer: the row must
/// be admissible (all four facets certified) AND carry a `KernelChecked`
/// admission whose constant is a registered, unfoldable Definition of the
/// callee's arity. A reflected Rust carrier under the def-path (an ordinary
/// Rust callee) answers `None` — a Rust→Rust forwarding body is not this lane
/// — and so does any def-path with no row at all, whatever its bare name.
fn kernel_checked_island_callee_row<'t>(
    facet_table: &'t trust_spec_elab::FacetTable,
    callee_def_path: &str,
    arity: usize,
) -> Option<&'t trust_spec_elab::Admission> {
    let admission = facet_table.admitted(callee_def_path)?;
    admission.require_kernel_check().ok()?;
    if admission.kernel_const.starts_with(KERNEL_IMPORT_PREFIX)
        || admission.arity != arity
        || admission.carriers.is_none()
    {
        return None;
    }
    Some(admission)
}

/// [`kernel_checked_island_callee_row`] plus the environment half: the
/// declaration the row names must still be a registered, unfoldable Definition
/// of exactly this arity in THIS environment (a row may have been recorded
/// against an earlier environment clone). The mint arm needs the environment
/// anyway; the facet closure deliberately does not (see
/// [`certify_clean_origin_forwarding_facets`]).
fn kernel_checked_island_callee<'t>(
    env: &Environment,
    facet_table: &'t trust_spec_elab::FacetTable,
    callee_def_path: &str,
    arity: usize,
) -> Option<&'t trust_spec_elab::Admission> {
    let admission = kernel_checked_island_callee_row(facet_table, callee_def_path, arity)?;
    let kernel_name = clean_kernel::Name::from_string(&admission.kernel_const);
    island_definition_value_for_name(env, &kernel_name)?;
    if island_definition_signature_for_name(env, &kernel_name)?.0 != arity {
        return None;
    }
    Some(admission)
}

/// The FORWARDING arm of [`admit_function_into`]: mint the defining equation of
/// a body that is one call to a kernel-checked Clean island definition with
/// the function's own parameters as arguments — `fn pb_max_r(lhs, rhs) {
/// pb_max(lhs, rhs) }` becomes `trust_import_…pb_max_r := fun p0 p1 => pb_max
/// p0 p1` (joint Rust+Lean cited lane, 2026-09-15).
///
/// This is what lets `result` in `ensures result >= lhs by pb_max_ge_left`
/// denote `pb_max lhs rhs` — the SAME kernel constant the theorem is stated
/// about — so the citation audit can check the theorem's proof term against
/// `∀ lhs rhs, lhs ≤ pb_max lhs rhs` instead of the ∀-closed `result` reading
/// no honest theorem proves. The substitution comes from the body's actual
/// admitted defining equation, exactly as for every other E6 shape.
///
/// Gates, all fail-closed:
///  1. the body IS the forwarding shape — an affirmative allow-list
///     ([`island_forwarding::recognize_island_forwarding_body`]);
///  2. the function's own facet record is admissible — established by
///     [`certify_clean_origin_forwarding_facets`] from the callee's record, or
///     by the compiler's structural composition; this arm does not bypass it;
///  3. the callee def-path resolves to a `KernelChecked` island admission of
///     the call's arity ([`kernel_checked_island_callee`]) — the identity the
///     compiler recorded, never a name;
///  4. the callee's DECLARED carriers agree, position by position, with the
///     carriers of the source parameters the call actually forwards (in the
///     call's argument order) and with the return carrier — a `u32` forwarded
///     into a `UInt64` slot refuses here;
///  5. the kernel re-checks the minted equation (`add_decl`), which re-derives
///     4 from the callee's recorded type.
fn admit_island_forwarding_into(
    env: &mut Environment,
    func: &trust_types::VerifiableFunction,
    facet_table: &trust_spec_elab::FacetTable,
    kernel_const: &str,
) -> Option<(String, trust_spec_elab::Admission)> {
    let debug = e6_debug_enabled();
    let forwarding = island_forwarding::recognize_island_forwarding_body(func)?;
    let Some(callee) = kernel_checked_island_callee(
        env,
        facet_table,
        &forwarding.callee,
        forwarding.arg_params.len(),
    ) else {
        if debug {
            eprintln!(
                "TRUST_E6_DEBUG forwarding fn={} REFUSED: callee `{}` has no kernel-checked \
                 Clean-origin identity row of arity {}",
                func.def_path,
                forwarding.callee,
                forwarding.arg_params.len()
            );
        }
        return None;
    };
    let param_domains = param_domains_of(func)?;
    let ret_domain = ty_to_domain(&func.body.return_ty)?;
    // Gate 4: the callee's declared telescope against the FORWARDED carriers.
    let declared = callee.carriers.as_ref()?;
    if declared.params.len() != forwarding.arg_params.len() {
        return None;
    }
    for (slot, &param) in forwarding.arg_params.iter().enumerate() {
        if param_domains.get(param)?.carrier() != declared.params[slot] {
            if debug {
                eprintln!(
                    "TRUST_E6_DEBUG forwarding fn={} REFUSED: argument {slot} forwards parameter \
                     {param} at carrier {:?}, callee declares {:?}",
                    func.def_path,
                    param_domains[param].carrier(),
                    declared.params[slot]
                );
            }
            return None;
        }
    }
    if ret_domain.carrier() != declared.ret {
        if debug {
            eprintln!(
                "TRUST_E6_DEBUG forwarding fn={} REFUSED: return carrier {:?}, callee declares {:?}",
                func.def_path,
                ret_domain.carrier(),
                declared.ret
            );
        }
        return None;
    }
    match trust_spec_elab::admit_forwarding_function(
        env,
        kernel_const,
        &param_domains,
        &callee.kernel_const,
        &forwarding.arg_params,
        &ret_domain,
    ) {
        Ok(admission) => {
            if debug {
                eprintln!(
                    "TRUST_E6_DEBUG forwarding fn={} MINTED as {kernel_const} := {} {:?}",
                    func.def_path, callee.kernel_const, forwarding.arg_params
                );
            }
            // Trust (GREEN THAT LIES, 2026-09-18): a forwarding body's whole
            // authority is its callee's — its defining equation IS one
            // application of the callee's kernel constant — so it inherits the
            // callee's qualification too. Without this the ROW that a
            // postcondition actually rests on (this function's, not the
            // island def's) would be the unqualified green again, one hop
            // removed.
            //
            // KNOWN GAP, unmeasured, in the DEFERRED direction: this copies
            // what the callee's row carries AT MINT TIME, and the compiler
            // mints program admissions exactly once
            // (`trust_mint_program_admissions`), BEFORE the deferred island
            // suffix is checked. The identity row widens afterwards (the
            // second `trust_record_clean_origin_identity_rows`, union-merged);
            // this forwarding row does NOT, because nothing re-mints it. So a
            // substitution that only a DEFERRED island introduces reaches the
            // callee's row and the post-walk discharge notes but not this
            // one. Diagnostic-only in both cases — no verdict, strength or
            // admissibility depends on the field — and closing it means
            // re-minting or re-stamping forwarding rows after the suffix,
            // which is a compiler-side change, not one this function can make.
            Some((
                func.def_path.clone(),
                admission
                    .with_return_domain(ret_domain)
                    .with_standin_disclosures(callee.standin_disclosures().iter().cloned()),
            ))
        }
        Err(reason) => {
            if debug {
                eprintln!("TRUST_E6_DEBUG forwarding fn={} REFUSED: {reason}", func.def_path);
            }
            None
        }
    }
}

/// Certify the four E6 facets of every FORWARDING body in `functions` whose
/// callee has a `KernelChecked` Clean-origin identity row in `table` (joint
/// Rust+Lean cited lane, 2026-09-15). Returns the def-paths certified.
///
/// The compiler's structural facet scan closes facets over callees "by exact
/// def-path identity" — over the bodies it has WALKED. A Clean-origin def has
/// no body the verifier walks (its correctness authority is the faithfulness
/// gate), so a Rust body that merely forwards to one reports every facet
/// `Undetermined: call to <def>, which is not itself structurally certified`,
/// and can never be E6-admitted, and `result` in its postcondition can never
/// be bound. This is the missing closure step for exactly that callee class,
/// and it is derived, not asserted:
///
///  * the body is the forwarding shape (allow-list), so every facet of the
///    body reduces to the same facet of its one callee;
///  * the callee's row is admissible — four `Certified` facets — and its
///    admission is `KernelChecked`: a strict Clean Definition, pure, total and
///    deterministic by the kernel language's semantics, and panic-free at every
///    call site because the compiler records the row only for a plan with no
///    caller precondition ([`admit_clean_origin_callee_identity`]).
///
/// Monotone like [`trust_spec_elab::FacetTable::upgrade_from_structural`]: only
/// `Unknown`/`Undetermined` facets are promoted, a `Refuted` facet refuses the
/// whole function, an existing `Certified` facet keeps its own evidence, and a
/// def-path with NO record (an ambiguity-evicted key, or a body the compiler
/// never recorded) is left alone — this never invents a record.
///
/// Table-only on purpose: the `KernelChecked` status on the callee's row is
/// minted through `trust_symbols`' sealed seam after the certification audit
/// and cannot be assembled anywhere else, so the row IS the evidence; the
/// environment re-check belongs to the mint, which has the environment in
/// hand. Intended caller: the compiler's composed-table construction, after the
/// structural composition and before any consumer reads the table.
///
/// # Where the stand-in qualification lives, and why not here
///
/// Trust (GREEN THAT LIES, 2026-09-18). This promotion is what lets a
/// forwarding body's postcondition row reach `Certified`, so it is the lane the
/// hazard entry names — but a [`trust_spec_elab::FacetStatus`] has room for one
/// evidence STRING and nothing else, and overloading that string is how a
/// qualification gets parsed by accident. The disclosure therefore rides on the
/// ADMISSION: [`admit_clean_origin_callee_identity`] attaches the island
/// session's `standin_imports` to the callee's row, and
/// [`admit_island_forwarding_into`] copies them onto the forwarding function's
/// own admission. Both are reachable from a table by
/// `FacetTable::admitted(def_path).standin_disclosures()`, which is the
/// per-FUNCTION statement the per-ISLAND compiler note could not make.
pub fn certify_clean_origin_forwarding_facets(
    functions: &[trust_types::VerifiableFunction],
    table: &mut trust_spec_elab::FacetTable,
) -> Vec<String> {
    use trust_spec_elab::FacetStatus;
    let mut certified = Vec::new();
    for func in functions {
        let Some(existing) = table.get(&func.def_path).cloned() else { continue };
        if existing.admissible() {
            continue;
        }
        let Some(forwarding) = island_forwarding::recognize_island_forwarding_body(func) else {
            continue;
        };
        if kernel_checked_island_callee_row(table, &forwarding.callee, forwarding.arg_params.len())
            .is_none()
        {
            continue;
        }
        let promote = |status: &FacetStatus| -> Option<FacetStatus> {
            match status {
                FacetStatus::Certified { .. } => Some(status.clone()),
                FacetStatus::Unknown | FacetStatus::Undetermined { .. } => {
                    Some(FacetStatus::Certified { evidence: "clean-origin-forwarding".to_string() })
                }
                FacetStatus::Refuted { .. } => None,
            }
        };
        let (Some(pure), Some(total), Some(deterministic), Some(no_panic)) = (
            promote(&existing.pure),
            promote(&existing.total),
            promote(&existing.deterministic),
            promote(&existing.no_panic),
        ) else {
            continue;
        };
        table.insert(
            func.def_path.clone(),
            trust_spec_elab::FnFacets { pure, total, deterministic, no_panic },
        );
        certified.push(func.def_path.clone());
    }
    certified
}

/// Stateful, crate-local Clean checking session. A crate gets exactly one
/// kernel environment and one file context, so declarations, namespaces,
/// `open`s, notation, and options evolve in source order across islands. The
/// file context permanently disables external `.olean` search: Rust builds
/// may only rely on declarations checked in this Clean-native environment.
pub struct CleanIslandSession {
    /// The kernel environment (materialized on first use: building Clean's
    /// prelude is ~0.8 s, and a crate with no island and no Rust callee to
    /// declare never needs it — see [`Self::environment_is_materialized`]),
    /// the elaborator's file context and the served temporal modules, owned
    /// by the KEYED environment: every change to them is a keyed operation
    /// or ends the session's use of local kernel facts (TG6, `keyed_env`).
    keyed: keyed_env::KeyedEnv,
    tainted: bool,
    /// Exact metadata names read by the current model-checking operation,
    /// including absent names. These are fact dependencies, not proof authority.
    model_metadata_reads: Vec<clean_kernel::Name>,
    /// A prepared continuation serializes its original constant-name baseline.
    model_baseline_read: bool,
    /// Whether this session checks the finite models its islands declare
    /// ([`Self::enable_model_checks`]); off unless the owner of the session
    /// reports island results.
    model_checks: bool,
    /// Whether to hand back the bindings the islands declare
    /// ([`Self::enable_binding_reads`]) without checking any model.
    binding_reads: bool,
    /// The state budget of a model that declares none
    /// ([`Self::set_model_state_budget`]).
    model_state_budget: u64,
    /// The kernel's limits for the model checks: the search size past which
    /// it is not asked by default, and its evaluation budget per unit of
    /// search size ([`Self::set_model_kernel_limits`]).
    model_work_limit: u64,
    model_heartbeats_per_work: u64,
    /// Trust (GREEN THAT LIES, 2026-09-18): every `import` ANY island of this
    /// session had served by Clean's built-in prelude stand-in, accumulated in
    /// check order and deduplicated by module.
    ///
    /// SESSION-scoped, deliberately, and this is the part a per-island reading
    /// gets wrong. One crate gets one `Environment` and one `FileContext`: the
    /// import providers an `import` resolves against are shared state, so
    /// "which island's text spelled the import" does not bound which
    /// declarations were checked relative to the substitution. Attributing the
    /// fact to the spelling island alone would UNDER-report, which is the
    /// direction this record exists to prevent; over-reporting a session-wide
    /// qualification costs a note and no verdict.
    ///
    /// ONLY `module` (and therefore
    /// [`CleanIslandStandinImport::disclosure`]/`options`) is meaningful on
    /// these entries. `start`/`end` are byte offsets into the text of whichever
    /// island FIRST spelled the module, and the session does not record which
    /// island that was — so remapping one onto an enclosing Rust span, the way
    /// the per-island seam legitimately does with its OWN outcome, would point
    /// at an arbitrary island. Use [`CleanIslandOutcome::standin_imports`] for
    /// anything span-shaped.
    standin_imports: Vec<CleanIslandStandinImport>,
}

/// Recovery results for deferred import units. Unlike an atomic
/// CleanIslandBatch, this may retain independent checked units while reporting
/// refused units/cycles. Every unsuccessful atomic attempt published nothing.
#[derive(Debug, Clone, Default)]
pub struct CleanImportBatch {
    /// Original source order and island-relative diagnostics.
    pub outcomes: Vec<CleanIslandOutcome>,
    /// Cycles among refused units; independent units may still be checked.
    pub cycles: Vec<crate::clean_island_batch::CleanIslandCycle>,
    /// Original indices excluded from the final successful atomic batch.
    pub refused_islands: Vec<usize>,
}

impl CleanImportBatch {
    #[must_use]
    pub fn is_rejected(&self) -> bool {
        !self.refused_islands.is_empty()
            || !self.cycles.is_empty()
            || self.outcomes.iter().any(CleanIslandOutcome::is_rejected)
    }
}

// Shared by the integrity-error producer and transactional rollback guard.
// A user diagnostic can only conservatively preserve taint by matching it.
const LOCAL_FACT_FAILURE_PREFIX: &str =
    "internal: this session's local kernel facts (TG6) failed here:";

/// The refusal `strict_leaf_declaration_error` gives an island that declares
/// into the `trust_import_*` namespace. Shared with the import-island recovery
/// guard: that is a policy violation, not a missing admission, so it keeps the
/// session tainted exactly as it does in the pre-walk batch.
const KERNEL_IMPORT_DECLARATION_REFUSAL: &str =
    "declares into the compiler's kernel-import namespace";

fn import_failure_is_global(message: &str) -> bool {
    message.starts_with(LOCAL_FACT_FAILURE_PREFIX)
        || message.starts_with(crate::clean_island_batch::UNRECOVERABLE_BATCH_PREFIX)
        || message.contains(KERNEL_IMPORT_DECLARATION_REFUSAL)
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
        Self {
            keyed: keyed_env::KeyedEnv::new(),
            tainted: false,
            model_metadata_reads: Vec::new(),
            model_baseline_read: false,
            standin_imports: Vec::new(),
            model_checks: false,
            binding_reads: false,
            model_state_budget: DEFAULT_STATE_BUDGET,
            model_work_limit: KERNEL_WORK_LIMIT,
            model_heartbeats_per_work: HEARTBEATS_PER_WORK,
        }
    }

    fn env(&self) -> &Environment {
        self.keyed.env()
    }

    /// Read and write LOCAL KERNEL FACTS (TG6) through `facts`: an
    /// elaboration whose every input is unchanged since a process of this
    /// compiler stored its fact imports that fact instead of elaborating and
    /// checking again ([`crate::clean_fact`], `keyed_env`). Takes effect only
    /// on a session nothing has changed yet.
    pub fn enable_facts(&mut self, facts: std::sync::Arc<crate::clean_fact::FactContext>) {
        self.keyed.enable_facts(facts);
    }

    /// This session's settings, as a fact key reads them.
    fn params(&self) -> keyed_env::SessionParams {
        keyed_env::SessionParams {
            model_checks: self.model_checks,
            binding_reads: self.binding_reads,
            model_state_budget: self.model_state_budget,
            model_work_limit: self.model_work_limit,
            model_heartbeats_per_work: self.model_heartbeats_per_work,
        }
    }

    /// Set this session's settings (a replay runs each logged operation
    /// under the settings it first ran with).
    fn set_params(&mut self, params: &keyed_env::SessionParams) {
        self.model_checks = params.model_checks;
        self.binding_reads = params.binding_reads;
        self.model_state_budget = params.model_state_budget;
        self.model_work_limit = params.model_work_limit;
        self.model_heartbeats_per_work = params.model_heartbeats_per_work;
    }

    /// Before anything elaborates: a session that imported facts rebuilds
    /// its elaborator by replaying its log with real elaboration
    /// (`keyed_env` module docs), each operation under its own settings. A
    /// log that cannot rebuild it, or a rebuild that disagrees with a hit
    /// this session applied (an outcome or the environment), taints the
    /// session and fails the caller's operation: nothing positive is minted
    /// from an elaborator the compiler could not reconstruct, and nothing a
    /// disproved hit reported stands.
    fn ensure_live(&mut self) -> Result<(), String> {
        if !self.keyed.is_stale() {
            return Ok(());
        }
        let (log, built) = match self.keyed.start_rebuild() {
            Ok(started) => started,
            Err(why) => {
                self.tainted = true;
                return Err(why);
            }
        };
        let tainted = self.tainted;
        let settings = self.params();
        let mut prepared = None;
        let mut diverged = None;
        for (index, entry) in log.iter().enumerate() {
            if let Some(params) = &entry.params {
                self.set_params(params);
            }
            match self.replay(&entry.op, &mut prepared) {
                Ok(outcome) => {
                    if diverged.is_none() && self.keyed.replay_differs(index, outcome.as_deref()) {
                        diverged = Some(format!(
                            "the outcome of `{}` at log entry {index}",
                            entry.op.kind()
                        ));
                    }
                }
                Err(why) => {
                    self.set_params(&settings);
                    self.tainted = true;
                    // The replay already failed; the comparison adds nothing.
                    let _ = self.keyed.finish_rebuild(log, &built, None);
                    return Err(why);
                }
            }
        }
        self.set_params(&settings);
        // The replay re-ran checks whose side effects the hits already
        // recorded; it must not change the session's own verdict.
        self.tainted = tainted;
        if let Err(why) = self.keyed.finish_rebuild(log, &built, diverged) {
            self.tainted = true;
            return Err(why);
        }
        Ok(())
    }

    /// Run `op` again for real (a rebuild, or the re-check of a stored
    /// fact), returning the stored form of its outcome when it is a fact's
    /// operation (`CheckAll`, `Check`, `Prepare`, `Report`). `prepared`
    /// carries the last `Prepare`'s declarations to the `Report` that follows
    /// it. A replayed elaboration may be rejected exactly as its original was
    /// (a rejected operation stays in the log, and a store may hold a
    /// rejection written before rejections stopped being stored, or forged);
    /// the caller compares outcomes.
    fn replay(
        &mut self,
        op: &keyed_env::LoggedOp,
        prepared: &mut Option<continuation::PreparedDeclarations>,
    ) -> Result<Option<Vec<u8>>, String> {
        use keyed_env::LoggedOp;
        match op {
            LoggedOp::Callees(callees) => {
                let (env, _, _) = self.keyed.parts_mut();
                declare_rust_callees(env, callees)
                    .map(|()| None)
                    .map_err(|refusal| format!("{refusal:?}"))
            }
            LoggedOp::MarkSatisfied(module) => {
                let (_, file_ctx, _) = self.keyed.parts_mut();
                file_ctx
                    .mark_import_satisfied_from_source(&clean_kernel::Name::from_string(module));
                Ok(None)
            }
            LoggedOp::CheckAll(sources) => {
                let sources: Vec<&str> = sources.iter().map(String::as_str).collect();
                Ok(encode_batch(&self.check_all_uncached(&sources)))
            }
            LoggedOp::Check(source) => Ok(encode_outcome(&self.check_uncached(source))),
            LoggedOp::Admissions(delta) => self.keyed.replay_admissions(delta).map(|()| None),
            LoggedOp::Prepare(sources) => {
                let sources: Vec<&str> = sources.iter().map(String::as_str).collect();
                let declarations = self.prepare_declarations(&sources, true);
                let outcome = declarations.encode();
                *prepared = Some(declarations);
                Ok(outcome)
            }
            LoggedOp::Report(sources) => {
                let declarations =
                    prepared.take().ok_or("a report with no preparation before it in the log")?;
                let sources: Vec<&str> = sources.iter().map(String::as_str).collect();
                Ok(encode_batch(&self.finish_declarations(&sources, declarations)))
            }
        }
    }

    /// A local-fact failure (a rebuild that could not run, a stored outcome
    /// that does not decode) is an error on the island it struck.
    fn rebuild_failure(why: &str) -> CleanIslandDiagnostic {
        CleanIslandDiagnostic {
            start: 0,
            end: 0,
            message: format!(
                "{LOCAL_FACT_FAILURE_PREFIX} {why}. Please \
                 report it; `targo trust store verify --facts` re-checks the fact store, and \
                 deleting the store works around it."
            ),
        }
    }

    /// Whether anything has touched this session's kernel environment yet. An
    /// unmaterialized session checked no island and declared no callee, so its
    /// environment would be exactly `Environment::with_prelude()` — a caller
    /// that only needs the environment conditionally can skip building it.
    #[must_use]
    pub fn environment_is_materialized(&self) -> bool {
        self.keyed.is_materialized()
    }

    /// Fresh standalone-source session with the elaborator's unconditional
    /// PProd builtin prologue materialized before any source/baseline snapshot.
    /// Clean's batch lexical pass calls that prologue for an `import`, whereas
    /// direct definition scheduling need not. Initializing the SAME kernel
    /// builtin here makes its ownership independent of that source syntax.
    /// No source declaration is checked, no names are filtered, and the ordinary
    /// Rust-island constructor above is unchanged. Other lazy/import providers
    /// and the actual runtime closure are not claimed complete by this phase.
    pub(crate) fn new_for_source_batch() -> Result<Self, String> {
        let mut session = Self::new();
        session.keyed.env_mut().init_pprod().map_err(|error| {
            format!("source-batch builtin PProd initialization failed: {error}")
        })?;
        Ok(session)
    }

    /// Whether ordinary checking or caller ingestion invalidated this session.
    /// Elaboration can register good declarations before discovering a bad
    /// sibling, so ordinary rejection forbids positive citation evidence from
    /// that partial environment. Transactionally refused deferred import
    /// islands restore their complete prior state and do not taint it.
    #[must_use]
    pub fn is_tainted(&self) -> bool {
        self.tainted
    }

    /// Strictly parse, elaborate, register, and kernel-check the next island
    /// — or import its local kernel fact (TG6).
    pub fn check(&mut self, source: &str) -> CleanIslandOutcome {
        let op = keyed_env::LoggedOp::Check(source.to_string());
        let outcome = match self.keyed.lookup(op, &self.params()) {
            keyed_env::Lookup::Hit(stored) => decode_outcome(&stored),
            keyed_env::Lookup::Miss(mut pending) => {
                if let Err(why) = self.ensure_live() {
                    let mut outcome = CleanIslandOutcome::default();
                    outcome.errors.push(Self::rebuild_failure(&why));
                    outcome
                } else {
                    self.keyed.begin(&mut pending);
                    let outcome = self.check_uncached(source);
                    self.keyed.finish(
                        *pending,
                        encode_outcome(&outcome),
                        outcome.is_rejected(),
                        outcome.anonymous_judgments != 0,
                        &self.model_metadata_reads,
                        self.model_baseline_read,
                    );
                    outcome
                }
            }
        };
        self.tainted |= outcome.is_rejected();
        self.record_standin_imports(std::slice::from_ref(&outcome));
        outcome
    }

    /// [`Self::check`]'s elaboration, inside a keyed operation.
    fn check_uncached(&mut self, source: &str) -> CleanIslandOutcome {
        self.model_metadata_reads.clear();
        self.model_baseline_read = false;
        let (served, imported) = self.serve_trust_imports_named(&[source]);
        let parser_prelude = served_parser_prelude(imported.first().map_or(&[][..], Vec::as_slice));
        let models = self.model_watch();
        let (env, file_ctx, _) = self.keyed.parts_mut();
        let mut outcome =
            check_clean_island_with_parser_prelude(&parser_prelude, source, env, file_ctx);
        outcome.errors.extend(served.into_iter().map(|(_, diagnostic)| diagnostic));
        self.check_declared_models(
            models,
            &[source],
            std::slice::from_ref(&parser_prelude),
            std::slice::from_mut(&mut outcome),
        );
        outcome
    }

    /// Check a deferred suffix with header-first name resolution. Missing
    /// admissions are refused before elaboration. Every failed whole attempt
    /// is rolled back, refused units are removed, and ALL survivors are checked
    /// again together. No successful interpretation from a partial environment
    /// is retained (clean_island_batch's first-success-wins hazard).
    pub fn check_import_islands(&mut self, sources: &[&str]) -> CleanImportBatch {
        if sources.is_empty() {
            return CleanImportBatch::default();
        }
        let mut refusals: Vec<Option<CleanIslandOutcome>> = sources.iter().map(|source| {
            let mut outcome = CleanIslandOutcome::default();
            // A name the island itself declares is not a reference to an
            // admission. Leave it to the strict leaf policy, which refuses the
            // declaration for naming the reserved namespace and taints.
            let declared = island_kernel_import_declarations(source);
            for (start, end, name) in island_kernel_import_identifiers(source) {
                if declared.contains(&name) {
                    continue;
                }
                if self.env().get_const(&clean_kernel::Name::from_string(&name)).is_none() {
                    outcome.errors.push(CleanIslandDiagnostic { start, end, message: format!(
                        "`{name}` has no checked E6 program admission; this island cannot be checked") });
                }
            }
            outcome.is_rejected().then_some(outcome)
        }).collect();
        let keyed = self.keyed.clone();
        let tainted = self.tainted;
        let standins = self.standin_imports.clone();
        let mut cycles = Vec::new();
        let mut result = loop {
            if refusals.iter().all(Option::is_some) {
                break crate::clean_island_batch::CleanIslandBatch {
                    outcomes: vec![CleanIslandOutcome::default(); sources.len()],
                    cycles: Vec::new(),
                    census: None,
                };
            }
            // Keep original unit indices and spans. An excluded unit has no
            // declarations, notation, imports, namespaces or other lexical effect.
            let surviving: Vec<&str> = sources
                .iter()
                .zip(&refusals)
                .map(|(source, refused)| if refused.is_some() { "" } else { *source })
                .collect();
            self.keyed.set_transactional(true);
            let batch = self.check_all(&surviving);
            self.keyed.set_transactional(false);
            let global_failure = batch
                .outcomes
                .iter()
                .flat_map(|outcome| &outcome.errors)
                .any(|error| import_failure_is_global(&error.message));
            if global_failure || !batch.is_rejected() {
                // Integrity failure keeps global taint/quarantine, including
                // for earlier hits. An accepted surviving batch commits once.
                break batch;
            }
            let mut removed = false;
            for (slot, outcome) in refusals.iter_mut().zip(&batch.outcomes) {
                if slot.is_none() && outcome.is_rejected() {
                    *slot = Some(outcome.clone());
                    removed = true;
                }
            }
            for cycle in &batch.cycles {
                for site in &cycle.sites {
                    if let Some(slot) = refusals.get_mut(site.island) {
                        if slot.is_none() {
                            *slot = Some(CleanIslandOutcome::default());
                            removed = true;
                        }
                    }
                }
            }
            cycles.extend(batch.cycles);
            if !removed {
                self.tainted = true;
                let mut outcomes = vec![CleanIslandOutcome::default(); sources.len()];
                if let Some(first) = outcomes.first_mut() {
                    first.errors.push(CleanIslandDiagnostic {
                        start: 0,
                        end: 0,
                        message: format!(
                            "{} a refused import batch has no attributable failed unit",
                            crate::clean_island_batch::UNRECOVERABLE_BATCH_PREFIX
                        ),
                    });
                }
                break crate::clean_island_batch::CleanIslandBatch {
                    outcomes,
                    cycles: Vec::new(),
                    census: None,
                };
            }
            // Restore all semantic keyed state. Counters retain the work that
            // actually ran. The next attempt revisits EVERY surviving source.
            let elaborations = self.keyed.elaborations;
            let rebuilds = self.keyed.rebuilds;
            self.keyed = keyed.clone();
            self.keyed.elaborations = elaborations;
            self.keyed.rebuilds = rebuilds;
            self.tainted = tainted;
            self.standin_imports.clone_from(&standins);
        };
        let refused_islands: Vec<usize> = refusals
            .iter()
            .enumerate()
            .filter_map(|(index, outcome)| outcome.as_ref().map(|_| index))
            .collect();
        for (outcome, refusal) in result.outcomes.iter_mut().zip(refusals) {
            if let Some(mut refusal) = refusal {
                // These declarations were rolled back, not published.
                refusal.registered.clear();
                refusal.errors.extend(
                    outcome
                        .errors
                        .iter()
                        .filter(|error| import_failure_is_global(&error.message))
                        .cloned(),
                );
                *outcome = refusal;
            }
        }
        cycles.extend(result.cycles);
        CleanImportBatch { outcomes: result.outcomes, cycles, refused_islands }
    }

    /// A singleton convenience over the same header-first recovery operation.
    pub fn check_import_island(&mut self, source: &str) -> CleanIslandOutcome {
        let mut batch = self.check_import_islands(&[source]);
        let mut outcome = batch.outcomes.remove(0);
        for cycle in &batch.cycles {
            let (start, end) = cycle.sites.first().map_or((0, 0), |site| (site.start, site.end));
            outcome.errors.push(CleanIslandDiagnostic {
                start,
                end,
                message: cycle.message.clone(),
            });
        }
        outcome
    }

    /// Observe the same canonical check_all operation; never substitute a
    /// second elaborator. Keep ALL original source hashes, including refused
    /// units. This wrapper has no ModuleOutcome ownership map, so the roster
    /// explicitly remains denominator-unverified and does not infer one from
    /// successful registration names or the filtered source inventory.
    pub fn check_import_islands_with_census(
        &mut self,
        sources: &[&str],
    ) -> (CleanImportBatch, crate::clean_census::LeanKernelRoster) {
        let before = crate::clean_census::owned_names(self.env());
        let batch = self.check_import_islands(sources);
        let mut census = crate::clean_census::LeanKernelRoster::capture(
            &before,
            self.env(),
            sources,
            None,
            batch.is_rejected(),
        );
        census.report["batch_committed"] = serde_json::json!(!batch.is_rejected());
        census.report["source_declaration_metadata"] =
            serde_json::json!("unavailable-from-import-wrapper");
        census.report["import_recovery"] = serde_json::json!({
            "refused_units": batch.refused_islands,
            "all_original_sources_retained": true,
            "survivors_checked_together": true,
        });
        census.mark_session_tainted(self.tainted);
        (batch, census)
    }

    /// Fold one batch's stand-in substitutions into the session record, in
    /// check order, one entry per module. Every path that checks an island
    /// runs this: the invariant on
    /// [`CleanIslandOutcome::standin_imports`] is that a consumer reporting
    /// `registered` reports these alongside it, and the Clean-origin identity
    /// seam is such a consumer at one remove (it reports a row derived from
    /// the registered environment).
    fn record_standin_imports(&mut self, outcomes: &[CleanIslandOutcome]) {
        for outcome in outcomes {
            for import in &outcome.standin_imports {
                if !self.standin_imports.iter().any(|known| known.module == import.module) {
                    self.standin_imports.push(import.clone());
                }
            }
        }
    }

    /// Every `import` this session had served by Clean's built-in prelude
    /// stand-in, in check order, one entry per module. See the field docs for
    /// why this is a session fact and not an island fact.
    #[must_use]
    pub fn standin_imports(&self) -> &[CleanIslandStandinImport] {
        &self.standin_imports
    }

    /// [`Self::standin_imports`] rendered through the ONE wording every
    /// compiler seam reports a stand-in substitution in
    /// ([`CleanIslandStandinImport::disclosure`]) — the exact strings a
    /// Clean-origin row must carry, so a consumer reading verdicts without
    /// this compilation's diagnostics still reads the qualification.
    #[must_use]
    pub fn standin_disclosures(&self) -> Vec<String> {
        self.standin_imports.iter().map(CleanIslandStandinImport::disclosure).collect()
    }

    /// Observe the exact sequential [`Self::check`] path, including partial
    /// registration on rejection. This does NOT substitute the header-first
    /// batch checker or make a failed island transactional. The eager identity
    /// delta retains generated additions but cannot attribute them to source
    /// declarations using the sequential checker's lossy registered-name list.
    /// Neither this diagnostic roster nor a partial environment grants authority.
    pub fn check_with_census(
        &mut self,
        source: &str,
    ) -> (CleanIslandOutcome, crate::clean_census::LeanKernelRoster) {
        let before = crate::clean_census::owned_names(self.env());
        let outcome = self.check(source);
        let mut census = crate::clean_census::LeanKernelRoster::capture_sequential(
            &before,
            self.env(),
            source,
            &outcome,
        );
        census.mark_session_tainted(self.tainted);
        (outcome, census)
    }

    /// Check EVERY island of a crate together, header-first (Trust I1).
    ///
    /// Unlike repeated [`Self::check`], this does not make source order
    /// load-bearing for name resolution: every declaration's header is
    /// elaborated before any body is, so an earlier island may name a
    /// declaration a later island introduces — exactly as Rust items resolve
    /// from a whole-crate symbol table.
    ///
    /// Returns one outcome per input island, in input order, with
    /// island-relative byte offsets, plus any dependency cycles. A cycle means
    /// NOTHING from the batch was registered.
    ///
    /// The session is tainted if any island was rejected or any cycle found,
    /// so positive citation evidence is withheld exactly as it is for
    /// [`Self::check`].
    /// TRUST'S TEMPORAL VOCABULARY, SERVED FROM SOURCE (temporal P1,
    /// 2026-09-29). An island that writes `import Trust.Temporal`,
    /// `import Trust.FiniteModel` or `import Trust.FiniteModelCheck` (the
    /// executable checker whose `checkSafety M n rfl` the kernel evaluates)
    /// gets that module's canonical text
    /// (`trust_temporal_prelude::MODULES`, the files `trust-spec-temporal`
    /// certifies against) elaborated and kernel-checked into this session's
    /// environment — once per session, dependencies first — and the module
    /// marked satisfied from source, so the import resolves to the REAL
    /// declarations (`Trust.Temporal.StateMachine`, `□`'s `Always`,
    /// `Satisfies`, `FiniteModel.ScalarModel.safetyClaim`, …) rather than a prelude
    /// stand-in, and is not disclosed as one. A temporal model or claim can then
    /// live in the program, checked by this compiler during the build.
    ///
    /// Imports are read off the REAL parse (`SurfaceDecl::Import`), never a text
    /// scan; a source that does not parse serves nothing (its own check reports
    /// the parse error). A served module that fails to check is an error on
    /// every island that imported it, as `(island index, diagnostic)`; nothing
    /// is marked satisfied for it, so its import stays the verbatim refusal.
    ///
    /// Also returns each island's imported served modules — the parser
    /// prelude its own check needs for their notation.
    fn serve_trust_imports_named(
        &mut self,
        sources: &[&str],
    ) -> (Vec<(usize, CleanIslandDiagnostic)>, Vec<Vec<&'static str>>) {
        let mut per_island: Vec<Vec<&'static str>> = vec![Vec::new(); sources.len()];
        let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
        let mut wanted: Vec<(usize, usize, usize, &'static str)> = Vec::new();
        for (island, source) in sources.iter().enumerate() {
            // An island written with a served module's notation (`Trust.Protocol`'s
            // `⊞`, …) parses only with that notation in scope, so its imports are read
            // off a parse with every served module's notation: still the real parse,
            // and the island's own check parses with only the modules it imports.
            let (decls, base) =
                match clean_parser::parse_file_with_tactics_located(source, &patterns) {
                    Ok(decls) => (decls, 0),
                    Err(_) => {
                        let mut combined = trust_temporal_prelude::notation();
                        let base = combined.len();
                        combined.push_str(source);
                        let Ok(decls) =
                            clean_parser::parse_file_with_tactics_located(&combined, &patterns)
                        else {
                            continue;
                        };
                        (decls.into_iter().filter(|decl| decl.span().start >= base).collect(), base)
                    }
                };
            let mut imports = Vec::new();
            trust_module_imports(&decls, &mut imports);
            for (start, end, module) in imports {
                let (start, end) = (start.saturating_sub(base), end.saturating_sub(base));
                if let Some((served, _, _)) =
                    trust_temporal_prelude::MODULES.iter().find(|(name, _, _)| *name == module)
                {
                    wanted.push((island, start, end, served));
                    per_island[island].push(served);
                }
            }
        }
        let mut errors = Vec::new();
        for (island, start, end, module) in wanted {
            if let Err(why) = self.serve_trust_module(module) {
                errors.push((
                    island,
                    CleanIslandDiagnostic {
                        start,
                        end,
                        message: format!(
                            "`import {module}` names Trust's temporal vocabulary, but its canonical \
                             source did not check in this session: {why}"
                        ),
                    },
                ));
            }
        }
        (errors, per_island)
    }

    /// Serve one module of `trust_temporal_prelude::MODULES` (its dependencies
    /// first); see [`Self::serve_trust_imports_named`].
    fn serve_trust_module(&mut self, module: &'static str) -> Result<(), String> {
        if self.keyed.served().contains(&module) {
            return Ok(());
        }
        let Some((_, deps, source)) =
            trust_temporal_prelude::MODULES.iter().find(|(name, _, _)| *name == module)
        else {
            return Err(format!("`{module}` is not a served module"));
        };
        for dep in *deps {
            self.serve_trust_module(dep)?;
        }
        let parser_prelude = served_parser_prelude(deps);
        let (env, file_ctx, _) = self.keyed.parts_mut();
        let outcome = check_clean_island_audited(
            &parser_prelude,
            source,
            env,
            file_ctx,
            StrictAudit::OncePerModule,
        );
        if let Some(first) = outcome.errors.first() {
            self.tainted = true;
            return Err(format!(
                "{} error(s), the first at bytes {}..{}: {}",
                outcome.errors.len(),
                first.start,
                first.end,
                first.message
            ));
        }
        let (_, file_ctx, served) = self.keyed.parts_mut();
        file_ctx.mark_import_satisfied_from_source(&clean_kernel::Name::from_string(module));
        served.push(module);
        Ok(())
    }

    /// The modules of Trust's temporal vocabulary this session has served.
    #[must_use]
    pub fn served_trust_modules(&self) -> &[&'static str] {
        self.keyed.served()
    }

    /// Record that `module`'s declarations are supplied by a source THIS run
    /// elaborates (W2/lean-sibling-imports): the `.lean` front door marks each
    /// operand's module name before [`Self::check_all`], so an `import` of a
    /// SIBLING OPERAND resolves — under whole-batch header-first elaboration
    /// it is semantically a no-op, and clean-elab's `ImportPolicy` doc has
    /// always counted this resolution class as resolved (the clean-native path
    /// simply never received the record). Only name-resolution bookkeeping:
    /// every marked module's declarations are still elaborated from source and
    /// kernel-checked in this same session, external `.olean` search stays
    /// permanently disabled, and an unmarked module keeps the verbatim
    /// fail-closed refusal. The island lane marks nothing.
    pub fn mark_import_satisfied_from_source(&mut self, module: &clean_kernel::Name) {
        // A file-context change later elaborations read: a logged operation,
        // in the chain of every later fact.
        self.keyed.logged(keyed_env::LoggedOp::MarkSatisfied(module.to_string()), |_, file_ctx| {
            file_ctx.mark_import_satisfied_from_source(module);
        });
    }

    pub fn check_all(&mut self, sources: &[&str]) -> crate::clean_island_batch::CleanIslandBatch {
        let op = keyed_env::LoggedOp::CheckAll(sources.iter().map(|s| (*s).to_string()).collect());
        let batch = match self.keyed.lookup(op, &self.params()) {
            keyed_env::Lookup::Hit(stored) => decode_batch(&stored, sources.len()),
            keyed_env::Lookup::Miss(mut pending) => {
                if let Err(why) = self.ensure_live() {
                    failed_batch(sources.len(), &why)
                } else {
                    self.keyed.begin(&mut pending);
                    let batch = self.check_all_uncached(sources);
                    self.keyed.finish(
                        *pending,
                        encode_batch(&batch),
                        batch.is_rejected(),
                        batch.has_anonymous_judgments(),
                        &self.model_metadata_reads,
                        self.model_baseline_read,
                    );
                    batch
                }
            }
        };
        self.tainted |= batch.is_rejected();
        self.record_standin_imports(&batch.outcomes);
        batch
    }

    /// [`Self::check_all`]'s elaboration, inside a keyed operation: the
    /// declaration phase, then the reporting phase, as an unprepared batch runs
    /// them (`continuation.rs`).
    fn check_all_uncached(
        &mut self,
        sources: &[&str],
    ) -> crate::clean_island_batch::CleanIslandBatch {
        let declarations = self.prepare_declarations(sources, false);
        self.finish_declarations(sources, declarations)
    }

    /// Check the same batch while independently measuring new owned kernel
    /// identities. This diagnostic roster is not the reachable runtime-body
    /// denominator and cannot upgrade producer or citation evidence.
    pub fn check_all_with_census(
        &mut self,
        sources: &[&str],
    ) -> crate::clean_island_batch::CleanIslandBatch {
        // A census measures the elaboration itself, so it is never a fact: the
        // change below is unkeyed and ends this session's use of facts.
        if let Err(why) = self.ensure_live() {
            self.tainted = true;
            return failed_batch(sources.len(), &why);
        }
        let (env, file_ctx, _) = self.keyed.parts_mut();
        let mut batch =
            crate::clean_island_batch::check_islands_batched_with_census(env, file_ctx, sources);
        self.tainted |= batch.is_rejected();
        self.record_standin_imports(&batch.outcomes);
        if let Some(census) = &mut batch.census {
            census.mark_session_tainted(self.tainted);
        }
        batch
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
    /// Trust (ref-self I1): mint ONE borrow-erased PARAMETER VIEW into this
    /// session's environment, returning the `(callee_path, Admission)` pair
    /// [`admit_view_function_into`] returns.
    ///
    /// It exists so the SESSION lane can hold the view, not only the two
    /// per-body env clones the in-walk discharge lanes build. Without it the
    /// post-walk CITATION SWEEP — which reads this session's environment and
    /// the session facet table — grades a `&self` clause against an
    /// environment that has no defining equation for it, and emits a hard
    /// error on the very row the in-walk lane sealed as proved.
    ///
    /// A tainted session mints nothing: an environment that is missing any part
    /// of the crate's islands must not gain a constant that later evidence
    /// could rest on.
    #[must_use]
    pub fn admit_parameter_view(
        &mut self,
        view: &trust_types::e6_param_view::E6ParamView,
        facet_table: &trust_spec_elab::FacetTable,
    ) -> Option<(String, trust_spec_elab::Admission)> {
        if self.tainted {
            return None;
        }
        self.keyed.admit(|env| param_view::admit_view_function_into(env, view, facet_table))
    }

    #[must_use]
    pub fn admit_program_functions(
        &mut self,
        functions: &[trust_types::VerifiableFunction],
        facet_table: &trust_spec_elab::FacetTable,
    ) -> Vec<(String, trust_spec_elab::Admission)> {
        // A struct-returning body contributes ONE admission PER FIELD; every
        // other shape contributes at most one for the whole function.
        self.keyed.admit(|env| {
            let mut out = Vec::new();
            for func in functions {
                out.extend(admit_function_fields_into(env, func, facet_table));
                if let Some(one) = admit_function_into(env, func, facet_table) {
                    out.push(one);
                }
            }
            out
        })
    }

    /// TG11: ODT admissions precede the legacy flattened scalar reader.
    pub fn admit_odt_program_functions(
        &mut self,
        faces: &[crate::odt_e6::FaceInput],
        functions: &[trust_types::VerifiableFunction],
        facets: &trust_spec_elab::FacetTable,
    ) -> Result<Vec<(String, trust_spec_elab::Admission)>, String> {
        if self.tainted {
            return Ok(Vec::new());
        }
        // TG6: the sole ODT environment mutation, inside an admission window.
        // The window's delta is logged, and every datatype, alias and `toTag`
        // it adds enters each later fact through its dependencies (a tag-only
        // edit misses whatever reaches the tag). Never take keyed.parts_mut
        // here: an unlogged write ends the session's use of facts.
        self.keyed.admit(|env| crate::odt_e6::admit(env, faces, functions, facets))
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
    /// [`kernel_unify_citation_typed_with_facets_in`]); the tainted-session
    /// gate is identical.
    ///
    /// Uses an EMPTY domain binding — only a closed clause elaborates cleanly —
    /// and the pre-nat-lift `Strict` fragment, stated explicitly. A clause with
    /// free machine-typed variables (`x <= y` over `u64`) needs
    /// [`Self::check_citation_typed_with_facets_in`], which threads the
    /// caller's parameter type table (two-language design §1.1 domain-tagged
    /// arithmetic) and the clause mode.
    #[must_use]
    pub fn check_citation_with_facets(
        &self,
        theorem: &str,
        clause_src: &str,
        facets: &trust_spec_elab::FacetTable,
    ) -> CitationVerdict {
        self.check_citation_typed_with_facets_in(
            theorem,
            clause_src,
            &[],
            facets,
            &trust_spec_elab::ProofClauseInputs::strict(),
        )
    }

    /// [`Self::check_citation_with_facets`] with EXPLICIT clause variable types
    /// (§1.1) and the CLAUSE MODE stated. `var_types` maps each free clause
    /// variable to its compatibility domain tag (`"u64"`, `"nat"`, …); the
    /// elaborated statement quantifies over that carrier, so a machine-typed
    /// citation clause is validated over the matching UInt domain instead of
    /// failing closed as ungroundable. The tainted-session gate is identical,
    /// and the verdict stays statement-only (it never grades a Rust/TrustIR
    /// obligation).
    ///
    /// Trust (d1, 2026-09-28): the mode is REQUIRED — there is no Strict
    /// default twin. The E9 sweep's ∀-`result` fallback called a defaulted
    /// twin while its discharge rung ran at `ProofLift`, and a lifted cited
    /// `ensures` the verified lane certifies became a hard error with
    /// verification off. A caller passes the SAME inputs as the rung it falls
    /// back from; see [`kernel_unify_citation_typed_with_facets_in`].
    #[must_use]
    pub fn check_citation_typed_with_facets_in(
        &self,
        theorem: &str,
        clause_src: &str,
        var_types: &[(&str, &str)],
        facets: &trust_spec_elab::FacetTable,
        inputs: &trust_spec_elab::ProofClauseInputs,
    ) -> CitationVerdict {
        if self.tainted {
            CitationVerdict::SessionTainted
        } else {
            kernel_unify_citation_typed_with_facets_in(
                self.env(),
                theorem,
                clause_src,
                var_types,
                facets,
                inputs,
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
        self.check_ensures_discharge_in(
            theorem,
            clause_src,
            param_types,
            self_fn_name,
            facets,
            &trust_spec_elab::ProofClauseInputs::strict(),
        )
    }

    /// Trust (nat-lift): [`Self::check_ensures_discharge`] with the CLAUSE MODE
    /// stated. Fail-closed while tainted, exactly as the plain entry is.
    #[must_use]
    pub fn check_ensures_discharge_in(
        &self,
        theorem: &str,
        clause_src: &str,
        param_types: &[(&str, &str)],
        self_fn_name: &str,
        facets: &trust_spec_elab::FacetTable,
        inputs: &trust_spec_elab::ProofClauseInputs,
    ) -> CitationVerdict {
        if self.tainted {
            CitationVerdict::SessionTainted
        } else {
            kernel_discharge_ensures_citation_in(
                self.env(),
                theorem,
                clause_src,
                param_types,
                self_fn_name,
                facets,
                inputs,
            )
        }
    }

    /// Produce a recheckable certificate for exact-domain, strict `ensures`
    /// clauses against this session's actual environment. The certificate
    /// establishes the Lean goal, not Rust representation/source correspondence.
    /// Scalar proof-lift callers retain the existing mode-aware API.
    #[must_use]
    pub fn certify_ensures_discharge_with_domains(
        &self,
        clauses: &[EnsuresDischargeClause<'_>],
        params: &[(&str, trust_spec_elab::Domain)],
        self_fn_name: &str,
    ) -> Option<EnsuresDischargeCertificate> {
        if self.tainted {
            return None;
        }
        certify_ensures_discharge_with_domains(self.env(), clauses, params, self_fn_name)
    }

    /// The body-independent citation audit ([`kernel_audit_cited_theorem`])
    /// against this crate-local environment. Fail-closed while tainted, like
    /// every other citation entry point: a partially registered environment
    /// must not vouch for a theorem either.
    pub fn audit_cited_theorem(&self, theorem: &str) -> Result<(), CitationVerdict> {
        if self.tainted {
            Err(CitationVerdict::SessionTainted)
        } else {
            kernel_audit_cited_theorem(self.env(), theorem)
        }
    }

    /// A1: [`Self::check_ensures_discharge`] widened to the ladder — the
    /// unconditional goal first, then the same postcondition UNDER this
    /// function's eligible `requires` clauses. See
    /// [`kernel_discharge_ensures_citation_under_in`] for what a conditional
    /// discharge does and does not say. Fail-closed while tainted: a tainted
    /// session yields the same `SessionTainted` verdict on rung
    /// [`CitationRung::Neither`], so a partial island registration can mint no
    /// conditional evidence either. This is
    /// [`Self::check_ensures_discharge_under_requires_in`] in the STRICT clause
    /// mode.
    #[must_use]
    pub fn check_ensures_discharge_under_requires(
        &self,
        theorem: &str,
        clause_src: &str,
        param_types: &[(&str, &str)],
        self_fn_name: &str,
        facets: &trust_spec_elab::FacetTable,
        hyps: &[trust_spec_elab::HypothesisInput],
    ) -> EnsuresCitationLadder {
        self.check_ensures_discharge_under_requires_in(
            theorem,
            clause_src,
            param_types,
            self_fn_name,
            facets,
            hyps,
            &trust_spec_elab::ProofClauseInputs::strict(),
        )
    }

    /// Trust (OR-A1, Inc 0): [`Self::check_ensures_discharge_under_requires`]
    /// with the CLAUSE MODE stated — the same inputs
    /// [`Self::check_ensures_discharge_in`] takes, so the ladder grades the same
    /// `G0` the single-rung lane grades.
    #[allow(clippy::too_many_arguments)]
    #[must_use]
    pub fn check_ensures_discharge_under_requires_in(
        &self,
        theorem: &str,
        clause_src: &str,
        param_types: &[(&str, &str)],
        self_fn_name: &str,
        facets: &trust_spec_elab::FacetTable,
        hyps: &[trust_spec_elab::HypothesisInput],
        inputs: &trust_spec_elab::ProofClauseInputs,
    ) -> EnsuresCitationLadder {
        if self.tainted {
            return Self::tainted_ladder();
        }
        kernel_discharge_ensures_citation_under_in(
            self.env(),
            theorem,
            clause_src,
            param_types,
            self_fn_name,
            facets,
            hyps,
            inputs,
        )
    }

    /// Trust (OR-A1): the CONDITIONAL rungs only
    /// ([`kernel_discharge_ensures_citation_conditional_in`]) against this
    /// session's environment, for a lane that already graded `G0` through
    /// [`Self::check_ensures_discharge_in`]. Fail-closed while tainted, exactly
    /// as every other citation entry point is.
    #[allow(clippy::too_many_arguments)]
    #[must_use]
    pub fn check_ensures_discharge_conditional_in(
        &self,
        theorem: &str,
        clause_src: &str,
        param_types: &[(&str, &str)],
        self_fn_name: &str,
        facets: &trust_spec_elab::FacetTable,
        hyps: &[trust_spec_elab::HypothesisInput],
        inputs: &trust_spec_elab::ProofClauseInputs,
    ) -> EnsuresCitationLadder {
        if self.tainted {
            return Self::tainted_ladder();
        }
        kernel_discharge_ensures_citation_conditional_in(
            self.env(),
            theorem,
            clause_src,
            param_types,
            self_fn_name,
            facets,
            hyps,
            inputs,
        )
    }

    fn tainted_ladder() -> EnsuresCitationLadder {
        EnsuresCitationLadder::refused(
            CitationVerdict::SessionTainted,
            Some(
                "an earlier Clean island was rejected, so this crate's environment is \
                 tainted and no positive evidence may be minted from it"
                    .to_string(),
            ),
        )
    }

    /// The crate-local kernel environment, available only while the session
    /// is untainted. Partial island registration must not mint positive
    /// evidence of any kind — certified-monitor evidence included — so a
    /// tainted session yields `None` (the same fail-closed policy as
    /// [`Self::check_citation`]).
    #[must_use]
    pub fn environment(&self) -> Option<&Environment> {
        if self.tainted { None } else { Some(self.env()) }
    }

    /// Trust (W5 increment 1, Lean-calls-Rust): declare this crate's
    /// admissible Rust callees in the session's kernel environment, BEFORE
    /// [`Self::check_all`]. See [`declare_rust_callees`] for what is declared
    /// and why it licenses nothing. A refusal taints the session: an
    /// environment that holds only some of the callees the mint decided on
    /// is a partial environment, and nothing positive may be minted from it.
    pub fn declare_rust_callees(
        &mut self,
        callees: &[RustCallee],
    ) -> Result<(), RustCalleeDeclRefusal> {
        if callees.is_empty() {
            // Declares nothing, so it must not build the prelude either.
            return Ok(());
        }
        let outcome =
            self.keyed.logged(keyed_env::LoggedOp::Callees(callees.to_vec()), |env, _| {
                declare_rust_callees(env, callees)
            });
        if outcome.is_err() {
            self.tainted = true;
        }
        outcome
    }
}

/// A batch whose elaboration could not run, with the reason on its first
/// island (every island when there is none).
fn failed_batch(islands: usize, why: &str) -> crate::clean_island_batch::CleanIslandBatch {
    let mut outcomes = vec![CleanIslandOutcome::default(); islands.max(1)];
    outcomes[0].errors.push(CleanIslandSession::rebuild_failure(why));
    crate::clean_island_batch::CleanIslandBatch { outcomes, cycles: Vec::new(), census: None }
}

// The stored forms of a fact's outcome (TG6). A stored outcome was produced
// by this compiler identity and read back through a content-addressed store,
// so one that does not decode is a broken store, and the island reports it.

fn encode_outcome(outcome: &CleanIslandOutcome) -> Option<Vec<u8>> {
    crate::clean_fact::encode(outcome)
}

fn decode_outcome(bytes: &[u8]) -> CleanIslandOutcome {
    crate::clean_fact::decode(bytes).unwrap_or_else(|error| {
        let mut outcome = CleanIslandOutcome::default();
        outcome.errors.push(CleanIslandSession::rebuild_failure(&format!(
            "a stored outcome does not decode: {error}"
        )));
        outcome
    })
}

fn encode_batch(batch: &crate::clean_island_batch::CleanIslandBatch) -> Option<Vec<u8>> {
    crate::clean_fact::encode(&(&batch.outcomes, &batch.cycles))
}

fn decode_batch(bytes: &[u8], islands: usize) -> crate::clean_island_batch::CleanIslandBatch {
    type Stored = (Vec<CleanIslandOutcome>, Vec<crate::clean_island_batch::CleanIslandCycle>);
    match crate::clean_fact::decode::<Stored>(bytes) {
        Ok((outcomes, cycles)) if outcomes.len() == islands => {
            crate::clean_island_batch::CleanIslandBatch { outcomes, cycles, census: None }
        }
        Ok(_) => failed_batch(islands, "a stored batch outcome has another island count"),
        Err(error) => {
            failed_batch(islands, &format!("a stored batch outcome does not decode: {error}"))
        }
    }
}

/// Trust (W5 increment 1, Lean-calls-Rust, design of record
/// `docs/design/2026-09-13-lean-calls-rust-lane.md` ENVIRONMENT): one Rust
/// `fn` the compiler admitted as callable from a Clean island — its bare name
/// (the Clean constant it is declared as) and the Rust carrier of every
/// signature position.
///
/// Built by the compiler from the callee's own signature (the mint seam reads
/// the AST header; MIR time reads `tcx.fn_sig`) and carried through
/// `ResolverGlobalCtxt`, so every session that elaborates islands declares the
/// SAME set. Only the closed carrier vocabulary `bool`/`u8`/`u16`/`u32`/`u64`
/// is accepted here; anything else is refused rather than guessed.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RustCallee {
    /// The bare Rust item name, which is also the Clean constant name.
    pub clean_name: String,
    /// The Rust parameter types, in order.
    pub params: Vec<trust_types::Ty>,
    /// The Rust result type.
    pub result: trust_types::Ty,
}

/// Why a Rust callee could not be declared in the Clean environment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustCalleeDeclRefusal {
    /// The callee's bare name.
    pub callee: String,
    /// The reason, in the user's terms.
    pub reason: String,
}

impl std::fmt::Display for RustCalleeDeclRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Rust callee `{}` could not be declared in Clean: {}", self.callee, self.reason)
    }
}

/// The Clean type a Rust carrier denotes at a callee's signature position,
/// or `None` outside the closed vocabulary this lane admits.
///
/// Deliberately the SAME reading `trust_clean_carrier` makes in the other
/// direction (`UIntN` ↔ `uN`, `Bool` ↔ `bool`), restated over the closed
/// enum so a position this lane cannot spell is a refusal, never a guess.
fn rust_callee_clean_type(ty: &trust_types::Ty) -> Option<clean_kernel::Expr> {
    use clean_kernel::{Expr, Name};
    let name = match ty {
        trust_types::Ty::Bool => "Bool".to_owned(),
        trust_types::Ty::Int { width: width @ (8 | 16 | 32 | 64), signed: false } => {
            format!("UInt{width}")
        }
        _ => return None,
    };
    Some(Expr::const_(Name::from_string(&name), vec![]))
}

/// The hidden inhabitant of a callee's result carrier: `Bool.false`, or
/// `UIntN.ofNat 0`. It exists only so the declaration can be an `Opaque`
/// rather than an `Axiom`; the kernel never unfolds it (see
/// [`declare_rust_callees`]).
fn rust_callee_zero(ty: &trust_types::Ty) -> Option<clean_kernel::Expr> {
    use clean_kernel::{Expr, Name};
    match ty {
        trust_types::Ty::Bool => Some(Expr::const_(Name::from_string("Bool.false"), vec![])),
        trust_types::Ty::Int { width: width @ (8 | 16 | 32 | 64), signed: false } => {
            Some(Expr::app(
                Expr::const_(Name::from_string(&format!("UInt{width}.ofNat")), vec![]),
                Expr::nat_lit(0),
            ))
        }
        _ => None,
    }
}

/// **THE ONE HELPER** that puts a crate's admissible Rust callees into a Clean
/// environment (W5 increment 1, ENVIRONMENT decision, bound to ruling v7/D1:
/// the island is checked in a REAL environment, so a Rust `fn` it calls must
/// be a real constant in that environment).
///
/// Each callee becomes a kernel [`clean_kernel::Declaration::Opaque`]:
/// `inc : UInt64 → UInt64` with a HIDDEN inhabitant `fun _ => UInt64.ofNat 0`.
///
/// # Why `Opaque` with a hidden value, and NOT surface `opaque`/`axiom`
///
/// * A valueless declaration is an AXIOM to the kernel, and an axiom in a
///   declaration's provenance closure makes every dependent grade `Trusted`
///   (`trust-cert-meter`'s `NonFoundationalAxiom`) — so
///   [`admit_certified_island_definition`] would REFUSE `twice_inc` and the
///   mint would withhold the `DefId`. The hidden inhabitant keeps the closure
///   axiom-free: `Opaque` is counted, not reported, by the certification
///   audit.
/// * The kernel NEVER delta-unfolds an `Opaque`, so the hidden value can prove
///   nothing: `theorem t : inc 0 = 0 := rfl` is REJECTED (pinned by
///   `control_23_rust_call_emitter_mutation::half_9`). The environment learns
///   exactly the callee's TYPE, which is all a caller in Clean may rely on.
///
/// What the compiler asserts on top of that — that the constant `inc` DENOTES
/// the Rust `fn inc` it was built from — is a compiler-asserted identity, not
/// a kernel fact (`docs/TCB.md`, the Lean-calls-Rust row). The kernel gate on
/// the emitted body (`trust_clean_origin::admit_lowering`) compares two
/// applications of the same stuck head, so a swapped argument or a wrong
/// callee refuses; which Rust body the head stands for is the link the
/// compiler owns.
///
/// The declared names are compiler-declared, never island text: the strict
/// island policy (`strict_leaf_policy_error`, `strict_registered_policy_error`)
/// grades only declarations the batch REGISTERED, so these are never graded
/// as island debt, and the `trust_import_*` namespace stays E6-only.
///
/// # Errors
///
/// A position outside `bool`/`u8`/`u16`/`u32`/`u64`, or a name the
/// environment already holds (a prelude constant, or a callee declared twice
/// — the mint's ambiguity rule refuses the second before it gets here).
/// The environment may hold a PREFIX of `callees` after an error; every
/// caller treats a refusal as fatal to the whole session.
pub fn declare_rust_callees(
    env: &mut Environment,
    callees: &[RustCallee],
) -> Result<(), RustCalleeDeclRefusal> {
    use clean_kernel::{BinderInfo, Declaration, Expr, Name};
    for callee in callees {
        let refuse =
            |reason: String| RustCalleeDeclRefusal { callee: callee.clean_name.clone(), reason };
        let mut param_types = Vec::with_capacity(callee.params.len());
        for (position, param) in callee.params.iter().enumerate() {
            let Some(clean) = rust_callee_clean_type(param) else {
                return Err(refuse(format!(
                    "parameter {position} has Rust type `{param:?}`, which is outside the \
                     `bool`/`u8`/`u16`/`u32`/`u64` vocabulary a Clean island can call at"
                )));
            };
            param_types.push(clean);
        }
        let (Some(result), Some(zero)) =
            (rust_callee_clean_type(&callee.result), rust_callee_zero(&callee.result))
        else {
            return Err(refuse(format!(
                "its result has Rust type `{:?}`, which is outside the \
                 `bool`/`u8`/`u16`/`u32`/`u64` vocabulary a Clean island can call at",
                callee.result
            )));
        };
        // `UInt64 → UInt64 → Bool`, built right-to-left.
        let type_ =
            param_types.iter().rev().fold(result, |acc, param| Expr::arrow(param.clone(), acc));
        // `fun (_ : UInt64) (_ : UInt64) => Bool.false` — one binder per
        // parameter, the hidden inhabitant underneath.
        let value = param_types
            .iter()
            .rev()
            .fold(zero, |acc, param| Expr::lam(BinderInfo::Default, param.clone(), acc));
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(&callee.clean_name),
            level_params: vec![],
            type_,
            value,
        })
        .map_err(|error| match error {
            clean_kernel::EnvError::DuplicateName(_) => refuse(format!(
                "the Clean environment already holds a constant named `{}` (a prelude \
                 declaration, or an earlier declaration of the same bare name)",
                callee.clean_name
            )),
            other => refuse(format!("the kernel refused the declaration: {other}")),
        })?;
    }
    Ok(())
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
/// `_`, under a [`KERNEL_IMPORT_PREFIX`] prefix that namespaces these constants
/// away from prelude and island declarations.
fn mangle_kernel_const(def_path: &str) -> String {
    let sanitized: String =
        def_path.chars().map(|c| if c.is_alphanumeric() { c } else { '_' }).collect();
    format!("{KERNEL_IMPORT_PREFIX}{sanitized}")
}

/// Whether an island identifier can name a kernel constant the E6 mint makes
/// for the program function at `def_path`: the whole-function import
/// ([`mangle_kernel_const`]) or one of its per-field imports (`…__f<i>`).
///
/// TG3 (COMPILE-TIME-FACTS-1): with verification off the compiler imports
/// only the bodies an island names, and it selects them with this predicate.
/// The mangling is lossy (`a::b_c` and `a_b::c` share a name), so the answer
/// can include a function the island does not mean; that only costs an extra
/// import attempt, because the kernel names the constant and a second holder
/// is refused at the mint (`DuplicateName`), never silently substituted.
pub fn island_identifier_names_kernel_import(identifier: &str, def_path: &str) -> bool {
    let base = mangle_kernel_const(def_path);
    identifier
        .strip_prefix(base.as_str())
        .is_some_and(|rest| rest.is_empty() || rest.starts_with("__f"))
}

/// Every identifier in an island's source that names the kernel-import
/// namespace, as `(start, end, name)`: the byte span of the identifier token
/// and the `trust_import_*` component it spells.
///
/// Read with Clean's own lexer, so comments (`--`, `/- … -/`, doc comments)
/// and string literals are trivia and never count. This is THE predicate that
/// decides whether an island is deferred until program admissions exist —
/// the resolver's mint seam and the compiler's island partition both call
/// [`island_names_kernel_import`] — and it replaced a byte search
/// (`text.contains("trust_import_")`) under which a comment mentioning the
/// namespace deferred the island and every island after it (TG3, reported by
/// aterm's PF1 worker, 2026-11-05).
pub fn island_kernel_import_identifiers(text: &str) -> Vec<(usize, usize, String)> {
    clean_parser::lexer::Lexer::tokenize(text)
        .into_iter()
        .filter_map(|token| match token.kind {
            clean_parser::lexer::TokenKind::Ident(name) => {
                let component = name
                    .split('.')
                    .find(|component| component.starts_with(KERNEL_IMPORT_PREFIX))?
                    .to_string();
                Some((token.span.start, token.span.end, component))
            }
            _ => None,
        })
        .collect()
}

/// The `trust_import_*` names an island declares: the identifier right after a
/// declaration keyword, read with Clean's lexer. Used only to tell a
/// declaration into the reserved namespace (a strict-policy refusal) apart from
/// a reference to a missing E6 admission; it grants nothing.
pub fn island_kernel_import_declarations(text: &str) -> Vec<String> {
    use clean_parser::lexer::TokenKind as K;
    let tokens = clean_parser::lexer::Lexer::tokenize(text);
    tokens
        .windows(2)
        .filter_map(|pair| {
            let declares = matches!(
                pair[0].kind,
                K::Def
                    | K::Theorem
                    | K::Lemma
                    | K::Axiom
                    | K::Opaque
                    | K::Abbrev
                    | K::Instance
                    | K::Structure
                    | K::Class
                    | K::Inductive
                    | K::Coinductive
                    | K::Codata
                    | K::Codef
            );
            match (&pair[1].kind, declares) {
                (K::Ident(name), true) => name
                    .split('.')
                    .find(|component| component.starts_with(KERNEL_IMPORT_PREFIX))
                    .map(str::to_string),
                _ => None,
            }
        })
        .collect()
}

/// Whether an island's source names a `trust_import_*` constant outside its
/// comments and string literals (see [`island_kernel_import_identifiers`]).
pub fn island_names_kernel_import(text: &str) -> bool {
    !island_kernel_import_identifiers(text).is_empty()
}

/// How many of a crate's islands, in authored order, are checked BEFORE program
/// admissions exist: every island before the first that names the
/// `trust_import_*` namespace ([`island_names_kernel_import`]).
///
/// That island and the whole authored suffix after it are deferred. The
/// resolver mints Clean-origin defs from this prefix alone, and the verify pass
/// and the kernel-only lane check the suffix later, against the E6 admissions
/// it names, in the session that already holds the prefix. A fresh session
/// holds no admission and cannot check the suffix, so a compiler seam that
/// re-checks the mint's environment (`clean_origin_mir::clean_crate_environment`)
/// checks exactly this prefix (E9-DEFERRED-SUFFIX-ENV-1).
#[must_use]
pub fn pre_admission_island_count<S: AsRef<str>>(sources: &[S]) -> usize {
    sources
        .iter()
        .position(|source| island_names_kernel_import(source.as_ref()))
        .unwrap_or(sources.len())
}

#[cfg(test)]
mod island_names_kernel_import_tests {
    use super::{island_kernel_import_identifiers, island_names_kernel_import};

    #[test]
    fn a_comment_or_a_string_does_not_name_the_namespace() {
        assert!(!island_names_kernel_import("-- trust_import_k__f\ntheorem t : True := trivial"));
        assert!(!island_names_kernel_import("/- trust_import_k__f -/ def x : Nat := 1"));
        assert!(!island_names_kernel_import("/-- trust_import_k__f -/\ndef x : Nat := 1"));
        assert!(!island_names_kernel_import("def s : String := \"trust_import_k__f\""));
        assert!(!island_names_kernel_import("def my_trust_import_x : Nat := 1"));
    }

    #[test]
    fn an_identifier_does_with_its_span() {
        let text = "theorem t : trust_import_k__f 1 = 1 := rfl";
        assert!(island_names_kernel_import(text));
        let found = island_kernel_import_identifiers(text);
        assert_eq!(found.len(), 1);
        let (start, end, name) = &found[0];
        assert_eq!(name, "trust_import_k__f");
        assert_eq!(&text[*start..*end], "trust_import_k__f");
        // A qualified spelling names it too.
        assert!(island_names_kernel_import("theorem t : Foo.trust_import_k__f 1 = 1 := rfl"));
    }

    #[test]
    fn the_pre_admission_prefix_ends_at_the_first_island_naming_the_namespace() {
        use super::pre_admission_island_count as prefix;
        let def = "def spec (a b : UInt8) : Bool := decide (a = b)";
        let cites = "theorem t (a b : UInt8) : trust_import_k__f a b = spec a b := rfl";
        let later = "theorem u : True := trivial";
        let mention = "-- trust_import_k__f\ntheorem v : True := trivial";
        assert_eq!(prefix::<&str>(&[]), 0);
        assert_eq!(prefix(&[def, later]), 2);
        assert_eq!(prefix(&[def, cites]), 1);
        // The whole authored suffix is deferred, an island after it that names
        // nothing included.
        assert_eq!(prefix(&[def, cites, later]), 1);
        assert_eq!(prefix(&[cites, def]), 0);
        // A comment that mentions the namespace defers nothing.
        assert_eq!(prefix(&[def, mention]), 2);
    }
}

#[cfg(test)]
mod island_identifier_names_kernel_import_tests {
    use super::island_identifier_names_kernel_import as names;

    #[test]
    fn the_whole_import_and_its_field_imports_name_the_function() {
        assert!(names("trust_import_k__ok", "k::ok"));
        assert!(names("trust_import_k__ok__f0", "k::ok"));
        assert!(names("trust_import_k__ok__f12", "k::ok"));
    }

    #[test]
    fn a_longer_or_different_name_does_not() {
        // A function whose name EXTENDS another's is a different import.
        assert!(!names("trust_import_k__okay", "k::ok"));
        assert!(!names("trust_import_k__ok_x", "k::ok"));
        assert!(!names("trust_import_k__o", "k::ok"));
        assert!(!names("k__ok", "k::ok"));
        assert!(!names("trust_import_", "k::ok"));
    }
}

/// The FLATTENED clause-side parameter rows of `func`, GROUPED BY SOURCE
/// PARAMETER: for each value parameter in declaration order, the
/// `(domain, clause-side name)` rows it contributes — one row for itself when
/// it is a supported scalar, or ONE ROW PER DECLARED FIELD when it is a struct
/// (E6/E9 widening increment 7). `None` if any parameter contributes nothing
/// this lane can name.
///
/// This must produce the SAME list, in the SAME order, as the compiler's
/// `trust_fn_param_type_names` — which computes it independently from HIR
/// types. Two properties keep them from drifting:
///
///   * **All-or-nothing per parameter, ON THIS SIDE.** A struct contributes
///     rows here only when EVERY declared field maps to a supported domain; one
///     unsupported field refuses the whole parameter (and, since a projection
///     mint needs every row, the whole function). **The compiler side is NOT
///     symmetric, and this comment used to claim it was:**
///     `trust_param_scalar_rows` SKIPS a field it cannot type and keeps the
///     scalar siblings' rows (its `continue`, and the reason beside it — one
///     non-scalar field used to suppress every sibling row). So there IS a
///     per-field filter on one side; what keeps the two from drifting is not
///     its absence.
///
///     The two type vocabularies are not identical either: the clause side sees
///     the bare Rust name `usize`/`isize`, which `Domain::from_binding_ty`
///     refuses on purpose, while the extraction side is never shown that name at
///     all. The E6 intake's extractor collapses a pointer-sized integer to
///     `Int { width: <target pointer width>, .. }` before [`ty_to_domain`] sees
///     it, so it maps exactly like the same-width `u64`/`i64`. ([`ty_to_domain`]
///     does carry a `PtrSizedInt` arm for the FAITHFUL extractor's spelling, but
///     that arm is unreachable from this lane and hard-codes 64 bits; its own
///     doc records the inspection and what wiring it up would require.) The E9
///     DISCHARGE lanes close that one gap outside this function, by resolving
///     those two names to the target's fixed-width spelling before the
///     elaborator sees them (`trust_fn_discharge_binder_types`) — both sides
///     then name the SAME target width, which is why that agreement argument is
///     not 64-bit-specific; every other divergence stands. What a residual
///     disagreement changes is the ARITY, which makes the goal ill-typed and
///     `reject_untyped_goal` refuses it, or the NAMES, which the next bullet
///     catches. A struct with a non-scalar field therefore still cannot carry a
///     citing clause — the MINT refuses it here — while a clause naming a field
///     the compiler skipped fails closed as an unbound variable.
///   * **The names are recorded.** `Admission::param_names` carries this list
///     into `elaborate_ensures`, which refuses a clause whose own parameter
///     list differs. That is what catches a same-length REORDERING, the one
///     drift the kernel cannot see.
///
/// A parameter with no recorded local name yields `None`: without it there is
/// no clause-side spelling to record, and an unnamed row could not be checked.
///
/// **A FROZEN SHARED POINTEE (`&self`, `&T`) NEVER REACHES THIS FUNCTION AS A
/// BORROW, which is why ref-self I2 could skip ITS unsupported fields while the
/// all-or-nothing rule above stands here.** The view mint
/// (`clean_island::param_view::admit_view_function_into`) runs the unchanged
/// `admit_function_into` on `trust_types::e6_param_view`'s borrow-erased copy,
/// whose parameters are already by-value scalars — so every one of them takes
/// the `ty_to_domain` arm below and the all-or-nothing `collect` has no struct
/// to refuse. Do not "make the two sides consistent" by relaxing this one: on
/// the by-value lane it really is the only filter, and probe `f40` pins that it
/// stays.
fn param_flat_rows(
    func: &trust_types::VerifiableFunction,
) -> Option<Vec<Vec<(trust_spec_elab::Domain, String)>>> {
    (1..=func.body.arg_count)
        .map(|i| {
            let local = func.body.locals.iter().find(|l| l.index == i)?;
            let name = local.name.as_deref()?;
            if let Some(domain) = ty_to_domain(&local.ty) {
                return Some(vec![(domain, name.to_string())]);
            }
            // An ENUM is refused: its `fields` list is the union view across
            // variants, so field `i` is variant-relative and does not name one
            // value of the parameter.
            let trust_types::Ty::Adt { fields, variants, .. } = &local.ty else {
                return None;
            };
            if !variants.is_empty() {
                return None;
            }
            fields
                .iter()
                .map(|(field, ty)| Some((ty_to_domain(ty)?, format!("{name}.{field}"))))
                .collect::<Option<Vec<_>>>()
        })
        .collect()
}

/// Enforce the strict island authority policy after kernel registration. The
/// environment may retain the rejected declaration for diagnostics, but the
/// caller taints the whole session and the Rust build fails.
pub(crate) fn strict_leaf_policy_error(env: &Environment, leaf: &ElabResult) -> Option<String> {
    strict_leaf_declaration_error(env, leaf).or_else(|| strict_leaf_audit_error(env, leaf)).or_else(
        || {
            let reference = crate::reference_mint::IslandReference::new(env);
            leaf_reference_error(&reference, leaf)
        },
    )
}

/// The declaration-level half of [`strict_leaf_policy_error`]: no assumptions,
/// no reserved namespaces, no `unsafe`, no `partial`, no trust debt.
fn strict_leaf_declaration_error(env: &Environment, leaf: &ElabResult) -> Option<String> {
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
        // The compiler's own namespaces (`trust_import_*`, `trust_checked_*`,
        // `trust_type_*`, `TrustOdt.*`): see `reserved_namespace_error`.
        if let Some(message) = reserved_namespace_error(name) {
            return Some(message);
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
    None
}

/// Reference checks run over the completed immutable island environment, so
/// the entry rechecks a common dependency only once. Anonymous judgments retain
/// their original elaborated terms, including their universe parameters.
fn leaf_reference_error(
    reference: &crate::reference_mint::IslandReference,
    leaf: &ElabResult,
) -> Option<String> {
    for name in leaf_declaration_names(leaf) {
        if let Err(error) = reference.check_registered(name) {
            return Some(format!(
                "Clean island declaration `{name}` failed the reference kernel recheck: {error}"
            ));
        }
    }
    if let ElabResult::Example { ty, val } = leaf {
        if let Err(error) = reference.check_judgment(ty, val) {
            return Some(format!(
                "Clean island anonymous judgment failed the reference kernel recheck: {error}"
            ));
        }
    }
    None
}

/// The audit half of [`strict_leaf_policy_error`].
fn strict_leaf_audit_error(env: &Environment, leaf: &ElabResult) -> Option<String> {
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

/// The same strict island authority policy as [`strict_leaf_policy_error`],
/// addressed BY NAME instead of by elaboration result.
///
/// The batch lane never holds an `ElabResult`: `clean_elab::module_batch` owns
/// elaboration and registration and reports names. So the policy reads the
/// constant the kernel actually stored — which is the object the leaf-addressed
/// form ultimately grades too — and applies the identical rules in the identical
/// order:
///
///   1. an `axiom` or a valueless `opaque` is an ASSUMPTION, and a strict island
///      hosts none;
///   2. no declaration into the compiler's `trust_import_*` namespace;
///   3. no `unsafe`, no `partial`, no trust debt (`sorry`, `trustedArith`, …);
///   4. every proof judgment must pass the certification audit with an EMPTY
///      trust closure — `Trusted` and `Rejected` are both build errors, and the
///      `Trusted` message discloses the assumptions BY NAME.
///
/// Registration by the Clean kernel is necessary, never sufficient: Clean will
/// register an axiom, and Trust will not accept one.
pub(crate) fn strict_registered_policy_error(
    env: &Environment,
    name: &clean_kernel::Name,
) -> Option<String> {
    strict_registered_policy_error_with_reference(env, name, None)
}

pub(crate) fn strict_registered_policy_error_with_reference(
    env: &Environment,
    name: &clean_kernel::Name,
    reference: Option<&crate::reference_mint::IslandReference>,
) -> Option<String> {
    strict_registered_pre_reference_error(env, name).or_else(|| {
        let owned;
        let reference = match reference {
            Some(reference) => reference,
            None => {
                owned = crate::reference_mint::IslandReference::new(env);
                &owned
            }
        };
        reference.check_registered(name).err().map(|error| {
            format!(
                "Clean island declaration `{name}` failed the reference kernel recheck: {error}"
            )
        })
    })
}

/// Declaration/audit diagnostics before the batch is eligible for acceptance.
/// A rejected batch's provisional headers cannot authorize anything; recovery
/// reruns the complete surviving batch and must pass the reference gate there.
pub(crate) fn strict_registered_pre_reference_error(
    env: &Environment,
    name: &clean_kernel::Name,
) -> Option<String> {
    // Failed transactional batches report temporary registered names but
    // commit no constants. They are progress data only. The successful-batch
    // reference gate still refuses every absent name (check_registered).
    let info = env.get_const(name)?;

    match info.kind {
        ConstantKind::Axiom => {
            return Some(format!(
                "Clean island declaration `{name}` is an axiom; strict islands require checked proof terms"
            ));
        }
        ConstantKind::Opaque if info.value.is_none() => {
            return Some(format!(
                "Clean island declaration `{name}` is a valueless opaque (an assumption); strict islands require checked bodies"
            ));
        }
        _ => {}
    }

    // The compiler's own namespaces, refused at the point of declaration rather
    // than downstream: see `reserved_namespace_error`.
    if let Some(message) = reserved_namespace_error(name) {
        return Some(message);
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

    if info.kind == ConstantKind::Theorem {
        let Some(proof) = &info.value else {
            return Some(format!(
                "Clean island proof `{name}` was registered without a proof term; strict islands \
                 require a checked term, not a statement"
            ));
        };
        match cert_meter::grade(env, &info.type_, proof) {
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

/// [`check_clean_island_with_parser_prelude`] with no parser prelude — the
/// ordinary island check, for the tests that drive a hand-built environment
/// (the session's own paths all go through the prelude-aware form).
#[cfg(test)]
fn check_clean_island_with_context(
    source: &str,
    env: &mut Environment,
    file_ctx: &mut FileContext,
) -> CleanIslandOutcome {
    check_clean_island_with_parser_prelude("", source, env, file_ctx)
}

/// Strictly parse, elaborate, register and kernel-check one island, with
/// `parser_prelude` — already-checked
/// Clean source (a served module of Trust's temporal vocabulary) — parsed in
/// front of `source`, so the prelude's parse-time notation (`□`, `◇`, `~>`,
/// `⊨`) is in scope for it, the technique `trust-spec-temporal`'s
/// `elaborate_suffix_with_parser_prelude` uses. Only `source`'s declarations
/// are elaborated, and every diagnostic stays relative to `source`. An empty
/// `parser_prelude` is the ordinary island check.
fn check_clean_island_with_parser_prelude(
    parser_prelude: &str,
    source: &str,
    env: &mut Environment,
    file_ctx: &mut FileContext,
) -> CleanIslandOutcome {
    check_clean_island_audited(parser_prelude, source, env, file_ctx, StrictAudit::PerProof)
}

/// When the strict certification audit of a source's proofs runs.
#[derive(Clone, Copy, PartialEq, Eq)]
enum StrictAudit {
    /// After each proof, rooted at that proof: an island, whose rejection
    /// names the proof that failed.
    PerProof,
    /// Once, after the last declaration, rooted at a term that mentions every
    /// theorem of the source ([`module_audit_error`]). The audit re-runs the
    /// declaration checker over a root's whole reachable closure and keeps
    /// nothing between calls, so auditing a module's theorems one by one
    /// rechecks its early lemmas once per later theorem. A served module is the
    /// compiler's own text, and a failure in it names the module either way.
    OncePerModule,
}

/// The strict certification audit of every theorem in `theorems` at once: one
/// audit rooted at `(fun (_ : P1) => … (fun (_ : Pn) => True.intro) …) t1 … tn :
/// True`. The audit walks every constant the root mentions, so each theorem is
/// a reachable stored declaration: it gets the full declaration recheck and the
/// provenance checks, and so does everything it depends on, each once. That is
/// at least what an audit rooted at the theorem's own judgment checks. A theorem
/// with universe parameters, or a root the kernel has no `True` for, is audited
/// on its own judgment as before.
fn module_audit_error(env: &Environment, theorems: &[clean_kernel::Name]) -> Option<String> {
    let truth = clean_kernel::Name::from_string("True");
    let intro = clean_kernel::Name::from_string("True.intro");
    let own_judgment = |name: &clean_kernel::Name| {
        let info = env.get_const(name)?;
        let proof = info.value.as_ref()?;
        match cert_meter::grade(env, &info.type_, proof) {
            cert_meter::Grade::Certified => None,
            cert_meter::Grade::Trusted { closure } => Some(format!(
                "Clean island proof `{name}` failed the strict certification audit because it depends on trust provenance: {}",
                closure.join(", ")
            )),
            cert_meter::Grade::Rejected { error } => Some(format!(
                "Clean island proof `{name}` failed the strict certification audit: {error}"
            )),
        }
    };
    if env.get_const(&truth).is_none() || env.get_const(&intro).is_none() {
        return theorems.iter().find_map(own_judgment);
    }
    let mut root = clean_kernel::Expr::const_(intro, Vec::new());
    let mut alone: Vec<&clean_kernel::Name> = Vec::new();
    for name in theorems.iter().rev() {
        match env.get_const(name) {
            Some(info) if info.level_params.is_empty() => {
                root = clean_kernel::Expr::app(
                    clean_kernel::Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        info.type_.clone(),
                        root,
                    ),
                    clean_kernel::Expr::const_(name.clone(), Vec::new()),
                );
            }
            _ => alone.push(name),
        }
    }
    let goal = clean_kernel::Expr::const_(truth, Vec::new());
    if cert_meter::grade(env, &goal, &root).is_certified() {
        return alone.into_iter().find_map(own_judgment);
    }
    // Not certified: audit each proof on its own judgment, so the rejection
    // names the proof and the reason exactly as an island's would.
    theorems.iter().find_map(own_judgment).or_else(|| {
        Some(
            "the module's strict certification audit failed, and no single proof's audit \
             reproduces the failure"
                .to_owned(),
        )
    })
}

fn check_clean_island_audited(
    parser_prelude: &str,
    source: &str,
    env: &mut Environment,
    file_ctx: &mut FileContext,
    audit: StrictAudit,
) -> CleanIslandOutcome {
    let mut outcome = CleanIslandOutcome::default();
    // Theorems whose audit `StrictAudit::OncePerModule` defers.
    let mut deferred: Vec<clean_kernel::Name> = Vec::new();
    let mut reference_names = Vec::new();
    let mut reference_judgments = Vec::new();

    let (combined, base) = if parser_prelude.is_empty() {
        (std::borrow::Cow::Borrowed(source), 0)
    } else {
        let mut combined = String::with_capacity(parser_prelude.len() + source.len() + 1);
        combined.push_str(parser_prelude);
        combined.push('\n');
        let base = combined.len();
        combined.push_str(source);
        (std::borrow::Cow::Owned(combined), base)
    };
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = match clean_parser::parse_file_with_tactics_located(&combined, &patterns) {
        Ok(decls) => decls,
        Err(err) => {
            let (start, end) = point_diagnostic_span(source, err.byte_offset.saturating_sub(base));
            outcome.errors.push(CleanIslandDiagnostic {
                start,
                end,
                message: format!("Clean island failed to parse: {err}"),
            });
            return outcome;
        }
    };
    let decls: Vec<clean_parser::SurfaceDecl> =
        decls.into_iter().filter(|decl| decl.span().start >= base).collect();
    let local = |span: clean_parser::Span| {
        clean_parser::Span::new(span.start.saturating_sub(base), span.end.saturating_sub(base))
    };

    for decl in &decls {
        let span = local(decl.span());
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
                        let failed_span = local(decl.span());
                        outcome.errors.push(CleanIslandDiagnostic {
                            start: failed_span.start.min(source.len()),
                            end: failed_span.end.min(source.len()),
                            message: format!(
                                "Clean island declaration `{name}` failed to elaborate: {error:?}"
                            ),
                        });
                        continue;
                    }

                    let deferrable = audit == StrictAudit::OncePerModule
                        && matches!(leaf, ElabResult::Theorem { .. });
                    let refused = strict_leaf_declaration_error(env, leaf).or_else(|| {
                        if deferrable { None } else { strict_leaf_audit_error(env, leaf) }
                    });
                    if let Some(message) = refused {
                        outcome.errors.push(CleanIslandDiagnostic {
                            start: span.start.min(source.len()),
                            end: span.end.min(source.len()),
                            message,
                        });
                        continue;
                    }
                    if let (true, ElabResult::Theorem { name, .. }) = (deferrable, leaf) {
                        deferred.push(name.clone());
                    }

                    if matches!(leaf, ElabResult::Example { .. }) {
                        outcome.anonymous_judgments += 1;
                    }
                    for name in leaf_declaration_names(leaf) {
                        reference_names.push((span, name.clone()));
                    }
                    if let ElabResult::Example { ty, val } = leaf {
                        reference_judgments.push((span, ty.clone(), val.clone()));
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

    if !deferred.is_empty() && !outcome.is_rejected() {
        if let Some(message) = module_audit_error(env, &deferred) {
            outcome.errors.push(CleanIslandDiagnostic { start: 0, end: 0, message });
        }
    }

    if !outcome.is_rejected() {
        let reference = crate::reference_mint::IslandReference::new(env);
        if let Some(error) = reference.base_error() {
            outcome.errors.push(CleanIslandDiagnostic {
                start: 0,
                end: 0,
                message: format!("Clean island reference base refused: {error}"),
            });
        }
        for (span, name) in &reference_names {
            if let Err(error) = reference.check_registered(name) {
                outcome.errors.push(CleanIslandDiagnostic {
                    start: span.start.min(source.len()),
                    end: span.end.min(source.len()),
                    message: format!("Clean island declaration `{name}` failed the reference kernel recheck: {error}"),
                });
            }
        }
        for (span, ty, val) in &reference_judgments {
            if let Err(error) = reference.check_judgment(ty, val) {
                outcome.errors.push(CleanIslandDiagnostic {
                    start: span.start.min(source.len()),
                    end: span.end.min(source.len()),
                    message: format!("Clean island anonymous judgment failed the reference kernel recheck: {error}"),
                });
            }
        }
    }

    // NOTE: the register path runs the kernel check per declaration and every
    // failure surfaces as `Err` or `ElabResult::Failed` above. The global
    // `kernel_check_failure_count` counter is process-wide and races across
    // concurrent island checks, so it is deliberately NOT consulted here.

    // An accepted island discloses every import the prelude stand-in served;
    // a rejected one reports no green, so it has nothing to qualify.
    if !outcome.is_rejected() {
        outcome.standin_imports = standin_imports_in(&decls, file_ctx);
    }

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
    island_definition_value_for_name(env, &clean_kernel::Name::from_string(name))
}

fn island_definition_value_for_name<'env>(
    env: &'env KernelEnvironment,
    name: &clean_kernel::Name,
) -> Option<&'env clean_kernel::Expr> {
    let info = env.get_const(name)?;
    if info.kind != ConstantKind::Definition {
        return None;
    }
    info.value.as_ref()
}

/// Which of `declarations` DIRECTLY name the constant `target` — in the type
/// or the value the kernel holds for them.
///
/// Diagnostics only. The Lean-calls-Rust mint refuses a sibling Rust `fn`
/// whose bare name an island `def` in ANOTHER module already bears ("Clean
/// sees one namespace"), but that refusal used to surface only through an
/// `Unknown identifier` — which never fires when the name DOES resolve, to the
/// other module's `def`. Measured 2026-09-16 (probe 16c/16g): `def twice_inc
/// := inc (inc x)` beside a Rust `fn inc` silently meant the `def inc` of
/// `mod a`, in either source order. This answers the one question the mint
/// cannot ask the AST: did an island next to the refused `fn` actually USE the
/// contested name? It reads the kernel's own terms, so it is a statement about
/// what was checked and emitted, never a scan of source text.
///
/// Direct references only. A reference the elaborator moved into an auxiliary
/// constant (a `match` or well-founded-recursion helper) is not found, so this
/// can MISS a use and never invents one. `declarations` and `target` are
/// kernel-name spellings as [`CleanIslandOutcome::registered`] reports them; a
/// name the environment does not hold is skipped. Result keeps input order.
#[must_use]
pub fn island_declarations_naming(
    env: &KernelEnvironment,
    declarations: &[String],
    target: &str,
) -> Vec<String> {
    let target = clean_kernel::Name::from_string(target);
    declarations
        .iter()
        .filter(|declaration| {
            let Some(info) = env.get_const(&clean_kernel::Name::from_string(declaration)) else {
                return false;
            };
            info.name != target
                && (info.type_.collect_constants().contains(&target)
                    || info
                        .value
                        .as_ref()
                        .is_some_and(|value| value.collect_constants().contains(&target)))
        })
        .cloned()
        .collect()
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

    /// TRUST'S TEMPORAL VOCABULARY IN AN ISLAND (temporal P1, 2026-09-29).
    /// `import Trust.Temporal` serves the canonical source, kernel-checked:
    /// the island defines a transition system as a real
    /// `Trust.Temporal.StateMachine`, states `□` safety of it with the real
    /// `Satisfies`/`Always`/`Lift`, and proves it by induction over `Runs` —
    /// the model and its claim live in the program. The claim restated in the
    /// served module's own notation (`□`) parses, because the island is parsed
    /// behind the served source. The import is served from source, so it is
    /// not disclosed as a prelude stand-in.
    #[test]
    fn an_island_states_and_proves_a_temporal_claim_over_trusts_vocabulary() {
        let mut session = CleanIslandSession::new();
        let outcome = session.check(
            r#"
import Trust.Temporal

namespace Latch

def machine : Trust.Temporal.StateMachine Nat :=
  { init := fun s => s = 0, next := fun s t => t = 1 }

def Bounded : Nat -> Prop := fun s => s <= 1

theorem step_bounded (b : Trust.Temporal.Behavior Nat) (h : Trust.Temporal.Runs machine b)
    (k : Nat) (ih : Bounded (b k)) : Bounded (b (Nat.succ k)) := by
  cases h.2 k with
  | inl hstep =>
    rw [hstep]
    exact Nat.le_refl 1
  | inr hstutter =>
    rw [hstutter]
    exact ih

theorem init_bounded (b : Trust.Temporal.Behavior Nat) (h : Trust.Temporal.Runs machine b) :
    Bounded (b 0) := by
  rw [h.1]
  exact Nat.zero_le 1

theorem bounded_along (b : Trust.Temporal.Behavior Nat) (h : Trust.Temporal.Runs machine b) :
    (n : Nat) -> Bounded (b n) := by
  intro n
  induction n with
  | zero => exact init_bounded b h
  | succ k ih => exact step_bounded b h k ih

theorem always_bounded :
    Trust.Temporal.Satisfies machine (Trust.Temporal.Always (Trust.Temporal.Lift Bounded)) := by
  intro b h n
  exact bounded_along b h n

theorem always_bounded_in_notation :
    Trust.Temporal.Satisfies machine (□ (Trust.Temporal.Lift Bounded)) :=
  always_bounded

end Latch
"#,
        );
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        assert!(
            outcome.registered.iter().any(|name| name == "Latch.always_bounded"),
            "{:?}",
            outcome.registered
        );
        assert!(
            outcome.registered.iter().any(|name| name == "Latch.always_bounded_in_notation"),
            "the served module's `□` notation parses in the importing island: {:?}",
            outcome.registered
        );
        assert_eq!(session.served_trust_modules(), ["Trust.Temporal"]);
        assert!(
            outcome.standin_imports.is_empty(),
            "a served module is not a stand-in: {:?}",
            outcome.standin_imports
        );
    }

    /// THE BATCH PATH TOO (the compiler's resolve-phase and verify-phase
    /// `check_all`): an island importing `Trust.Temporal` and writing `□` is
    /// parsed behind the served source, header-first with a plain sibling
    /// island, and a diagnostic in it stays relative to its own text.
    #[test]
    fn the_batch_path_serves_the_temporal_vocabulary_and_its_notation() {
        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[
            "def unrelated : Nat := 7",
            r#"import Trust.Temporal

def machine : Trust.Temporal.StateMachine Nat :=
  { init := fun s => s = 0, next := fun s t => t = s }

def Stays : Nat -> Prop := fun s => s = 0

def claim : Prop := Trust.Temporal.Satisfies machine (□ (Trust.Temporal.Lift Stays))
"#,
        ]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        assert!(
            batch.outcomes[1].registered.iter().any(|name| name == "claim"),
            "{:?}",
            batch.outcomes
        );
        assert!(batch.outcomes[1].standin_imports.is_empty());

        let broken = "import Trust.Temporal

def bad : Nat := missing_name
";
        let rejected = CleanIslandSession::new().check_all(&[broken]);
        let error = rejected.outcomes[0].errors.first().expect("an unknown name is rejected");
        assert!(
            error.start >= broken.find("def bad").unwrap() && error.end <= broken.len(),
            "the diagnostic points into the island's own text: {error:?}"
        );
    }

    /// `import Trust.FiniteModel` serves its dependency first and then the
    /// finite-model data: trust-spec-temporal's canonical example model
    /// (`examples/clean_scalar_lockstep.lean`, the one its certification lanes
    /// decode) compiles unchanged as an island and names its applied safety
    /// claim. NEGATIVE CONTROL: the same island without the import does not
    /// resolve the vocabulary.
    #[test]
    fn the_canonical_finite_model_compiles_as_an_island() {
        const MODEL: &str =
            include_str!("../../trust-spec-temporal/examples/clean_scalar_lockstep.lean");
        const CLAIM: &str = "def Example.claim : Prop :=\n  \
             Trust.Temporal.FiniteModel.ScalarModel.safetyClaim Example.Lockstep\n";
        let mut session = CleanIslandSession::new();
        let outcome = session.check(&format!("import Trust.FiniteModel\n{MODEL}\n{CLAIM}"));
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        for name in ["Example.Lockstep", "Example.claim"] {
            assert!(
                outcome.registered.iter().any(|registered| registered == name),
                "{name}: {:?}",
                outcome.registered
            );
        }
        assert_eq!(session.served_trust_modules(), ["Trust.Temporal", "Trust.FiniteModel"]);

        let unserved = CleanIslandSession::new().check(MODEL);
        assert!(unserved.is_rejected(), "without the import nothing resolves the vocabulary");
    }

    /// `import Trust.FiniteModelCheck` serves the executable checker after its
    /// dependencies, and the KERNEL RUNS IT while the island compiles: the
    /// canonical model is proved safe by `proveSafe Example.Lockstep 64 rfl`
    /// — the untrusted bounded search and the checker are evaluated by
    /// reduction, and the served module's kernel-checked soundness theorem
    /// turns the verdict into the applied `ScalarModel.safetyClaim`.
    /// NEGATIVE CONTROL: the same island over the `Buggy = 1` model, whose
    /// `x = y` invariant breaks, is rejected and the diagnostic names the
    /// broken invariant — the model still checks, the safety theorem does not.
    #[test]
    fn the_canonical_finite_model_is_proved_safe_by_the_kernel_checker() {
        const MODEL: &str =
            include_str!("../../trust-spec-temporal/examples/clean_scalar_lockstep.lean");
        fn island(model: &str) -> String {
            format!(
                "import Trust.FiniteModelCheck\n{model}\n\
                 theorem Example.safe : Trust.Temporal.FiniteModel.ScalarModel.safetyClaim \
                 Example.Lockstep :=\n  \
                 Trust.Temporal.FiniteModel.proveSafe Example.Lockstep 64 rfl\n"
            )
        }
        let mut session = CleanIslandSession::new();
        let outcome = session.check(&island(MODEL));
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        assert!(
            outcome.registered.iter().any(|name| name == "Example.safe"),
            "{:?}",
            outcome.registered
        );
        assert_eq!(
            session.served_trust_modules(),
            ["Trust.Temporal", "Trust.FiniteModel", "Trust.FiniteModelCheck"]
        );

        let buggy = MODEL.replace("\"Buggy\" 0", "\"Buggy\" 1");
        assert_ne!(buggy, MODEL, "the control flips the model's Buggy constant");
        let rejected = CleanIslandSession::new().check(&island(&buggy));
        assert!(rejected.is_rejected(), "a model whose invariant breaks is not proved safe");
        assert!(
            format!("{:?}", rejected.errors).contains("invariantFails"),
            "the rejection names the broken invariant: {:?}",
            rejected.errors
        );
        assert!(
            rejected.registered.iter().any(|name| name == "Example.Lockstep"),
            "the buggy model itself still checks: {:?}",
            rejected.registered
        );
        assert!(
            !rejected.registered.iter().any(|name| name == "Example.safe"),
            "{:?}",
            rejected.registered
        );
    }

    /// The prelude is built on first use, never by `new()`: a crate with no
    /// island pays nothing for it. Declaring an EMPTY callee list must not build
    /// it either (the compiler always makes that call), and the first reader
    /// gets exactly Clean's prelude.
    #[test]
    fn session_environment_is_built_only_when_read() {
        let mut session = CleanIslandSession::new();
        assert!(!session.environment_is_materialized());
        assert!(session.declare_rust_callees(&[]).is_ok());
        assert!(!session.environment_is_materialized());
        let prelude = Environment::with_prelude();
        let env = session.environment().expect("an untainted session has an environment");
        assert_eq!(env.num_constants(), prelude.num_constants());
        assert!(session.environment_is_materialized());
    }

    /// The NORMATIVE AUTHORED client spellings (veripb_kernel.lean §checked
    /// arithmetic — the byte-level term structure the checked-arith spec makes
    /// the plan of record: sign-case-match `toIntN`, the exact literals, the
    /// `fitsI64` guard shape, `fitsI128` as authored), elaborated by the SAME
    /// island elaborator a client island goes through — plus the two §5.7
    /// FORGERY twins (`checkedAddSwapped64` with the `some`/`none` arms
    /// reversed; `checkedSub64` for the add↔sub swap).
    const CHECKED_MODEL_ISLAND: &str = r#"
def key64 (v : BitVec 64) : Nat :=
    Nat.xor (BitVec.toNat v) 9223372036854775808

def toInt64 (v : BitVec 64) : Int :=
    match Nat.ble 9223372036854775808 (key64 v) with
    | true  => Int.ofNat (Nat.sub (key64 v) 9223372036854775808)
    | false => Int.negSucc (Nat.sub 9223372036854775807 (key64 v))

def i64Max : Int := 9223372036854775807
def i64Min : Int := Int.neg 9223372036854775808

def fitsI64 (x : Int) : Bool :=
  match Int.ble i64Min x with
  | true  => Int.ble x i64Max
  | false => false

def ofInt64 (x : Int) : BitVec 64 :=
    match Int.ble (Int.ofNat 0) x with
    | true  => BitVec.ofNat 64 (Int.toNat x)
    | false => BitVec.ofNat 64 (Int.toNat (Int.add x (Int.ofNat 18446744073709551616)))

def checkedAdd64 (a : BitVec 64) (b : BitVec 64) : Option (BitVec 64) :=
    match fitsI64 (Int.add (toInt64 a) (toInt64 b)) with
    | true  => some (ofInt64 (Int.add (toInt64 a) (toInt64 b)))
    | false => none

def checkedSub64 (a : BitVec 64) (b : BitVec 64) : Option (BitVec 64) :=
    match fitsI64 (Int.sub (toInt64 a) (toInt64 b)) with
    | true  => some (ofInt64 (Int.sub (toInt64 a) (toInt64 b)))
    | false => none

def checkedMul64 (a : BitVec 64) (b : BitVec 64) : Option (BitVec 64) :=
    match fitsI64 (Int.mul (toInt64 a) (toInt64 b)) with
    | true  => some (ofInt64 (Int.mul (toInt64 a) (toInt64 b)))
    | false => none

def checkedAddSwapped64 (a : BitVec 64) (b : BitVec 64) : Option (BitVec 64) :=
    match fitsI64 (Int.add (toInt64 a) (toInt64 b)) with
    | true  => none
    | false => some (ofInt64 (Int.add (toInt64 a) (toInt64 b)))

def key128 (v : BitVec 128) : Nat :=
    Nat.xor (BitVec.toNat v) 170141183460469231731687303715884105728

def toInt128 (v : BitVec 128) : Int :=
    match Nat.ble 170141183460469231731687303715884105728 (key128 v) with
    | true  => Int.ofNat (Nat.sub (key128 v) 170141183460469231731687303715884105728)
    | false => Int.negSucc (Nat.sub 170141183460469231731687303715884105727 (key128 v))

def i128Max : Int := 170141183460469231731687303715884105727
def i128Min : Int := Int.neg 170141183460469231731687303715884105728

def fitsI128 (x : Int) : Bool :=
    match Int.ble i128Min x with
    | true  => Int.ble x i128Max
    | false => false

def ofInt128 (x : Int) : BitVec 128 :=
    match Int.ble (Int.ofNat 0) x with
    | true  => BitVec.ofNat 128 (Int.toNat x)
    | false => BitVec.ofNat 128 (Int.toNat (Int.add x (Int.ofNat 340282366920938463463374607431768211456)))

def checkedMul128 (a : BitVec 128) (b : BitVec 128) : Option (BitVec 128) :=
    match fitsI128 (Int.mul (toInt128 a) (toInt128 b)) with
    | true  => some (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
    | false => none

def trunc64 (v : BitVec 128) : BitVec 64 :=
    BitVec.ofNat 64 (BitVec.toNat v)

def narrowWide (x : BitVec 128) : Option (BitVec 64) :=
    match fitsI64 (toInt128 x) with
    | true  => some (trunc64 x)
    | false => none

def narrowWideSwapped (x : BitVec 128) : Option (BitVec 64) :=
    match fitsI64 (toInt128 x) with
    | true  => none
    | false => some (trunc64 x)

def trunc64Narrower (v : BitVec 128) : BitVec 64 :=
    BitVec.ofNat 64 (BitVec.toNat (BitVec.ofNat 32 (BitVec.toNat v)))

def narrowWideTrunc32 (x : BitVec 128) : Option (BitVec 64) :=
    match fitsI64 (toInt128 x) with
    | true  => some (trunc64Narrower x)
    | false => none

def narrowWideFitsWide (x : BitVec 128) : Option (BitVec 64) :=
    match fitsI128 (toInt128 x) with
    | true  => some (trunc64 x)
    | false => none

def sextWide (v : BitVec 64) : BitVec 128 :=
    ofInt128 (toInt64 v)

def eqOkW (m : BitVec 64) (t : BitVec 128) : Bool :=
    Decidable.decide (Eq (BitVec.toNat (sextWide m)) (BitVec.toNat t))
                     (Nat.decEq (BitVec.toNat (sextWide m)) (BitVec.toNat t))

def zextWide (v : BitVec 64) : BitVec 128 :=
    BitVec.ofNat 128 (BitVec.toNat v)

def eqOkZeroExt (m : BitVec 64) (t : BitVec 128) : Bool :=
    Decidable.decide (Eq (BitVec.toNat (zextWide m)) (BitVec.toNat t))
                     (Nat.decEq (BitVec.toNat (zextWide m)) (BitVec.toNat t))

def eqOkTrunc (m : BitVec 64) (t : BitVec 128) : Bool :=
    Decidable.decide (Eq (BitVec.toNat m) (BitVec.toNat (trunc64 t)))
                     (Nat.decEq (BitVec.toNat m) (BitVec.toNat (trunc64 t)))

def zeroI64 : BitVec 64 := BitVec.ofNat 64 Nat.zero
def oneI64 : BitVec 64 := BitVec.ofNat 64 1
def twoI64 : BitVec 64 := BitVec.ofNat 64 2
def negOneI64 : BitVec 64 := BitVec.ofNat 64 18446744073709551615
def minI64Bits : BitVec 64 := BitVec.ofNat 64 9223372036854775808
def maxI64Bits : BitVec 64 := BitVec.ofNat 64 9223372036854775807
def oneI32 : BitVec 32 := BitVec.ofNat 32 1
def zeroI128 : BitVec 128 := BitVec.ofNat 128 Nat.zero
def oneI128 : BitVec 128 := BitVec.ofNat 128 1
def minI128Bits : BitVec 128 := BitVec.ofNat 128 170141183460469231731687303715884105728
def maxI128Bits : BitVec 128 := BitVec.ofNat 128 170141183460469231731687303715884105727
"#;

    /// The §5.7 discipline, end to end: the CHECKED-ARITHMETIC MINT's seeded
    /// model is DELTA-DEFEQ to the client island's AUTHORED model — through
    /// the real island elaborator, with the vendored (literal-only-`toNat`)
    /// kernel, so the equality closes by lazy-delta unfolding on STUCK
    /// scrutinees with no closed-pipeline evaluation — and every forged
    /// variant (swapped `some`/`none` arms; `add`↔`sub`) is CAUGHT, not
    /// silently green.
    #[test]
    fn checked_mint_is_defeq_to_the_island_authored_model_and_swaps_are_caught() {
        use trust_spec_elab::{CheckedArithOp, CmpOperand, Domain, MachineSIntWidth};
        let mut env = Environment::with_prelude();
        let mut file_ctx = FileContext::new();
        file_ctx.disable_external_import_search();
        let outcome =
            check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
        assert!(!outcome.is_rejected(), "the authored island must register: {outcome:?}");

        let i64d = Domain::Signed(MachineSIntWidth::I64);
        let i128d = Domain::Signed(MachineSIntWidth::I128);
        for (mint_name, op, dom, width) in [
            ("cadd64_mint", CheckedArithOp::Add, &i64d, MachineSIntWidth::I64),
            ("csub64_mint", CheckedArithOp::Sub, &i64d, MachineSIntWidth::I64),
            ("cmul64_mint", CheckedArithOp::Mul, &i64d, MachineSIntWidth::I64),
            ("cmul128_mint", CheckedArithOp::Mul, &i128d, MachineSIntWidth::I128),
        ] {
            trust_spec_elab::admit_checked_arithmetic_function(
                &mut env,
                mint_name,
                &[dom.clone(), dom.clone()],
                op,
                width,
                CmpOperand::Param(0),
                CmpOperand::Param(1),
            )
            .unwrap_or_else(|e| panic!("{mint_name} must admit into the island env: {e}"));
        }

        // The island definition's `Option (BitVec 64)` codomain records the
        // (currently unique-preimage) Option result domain, which is what lets
        // a probe clause spell `result == cadd_isl(a, b)`.
        assert_eq!(
            island_definition_signature(&env, "checkedAdd64"),
            Some((2, Some(Domain::OptionSigned(MachineSIntWidth::I64)))),
            "an Option (BitVec 64) island codomain must record OptionSigned(I64)"
        );
        assert_eq!(
            island_definition_signature(&env, "checkedMul128"),
            Some((2, Some(Domain::OptionSigned(MachineSIntWidth::I128)))),
            "an Option (BitVec 128) island codomain must record OptionSigned(I128)"
        );

        let tc = clean_kernel::TypeChecker::new(&env);
        let bv_lit = |bits: u64, v: u64| {
            clean_kernel::Expr::apps(
                clean_kernel::Expr::const_(clean_kernel::Name::from_string("BitVec.ofNat"), vec![]),
                [clean_kernel::Expr::nat_lit(bits), clean_kernel::Expr::nat_lit(v)],
            )
        };
        let app2 = |f: &str, a: clean_kernel::Expr, b: clean_kernel::Expr| {
            clean_kernel::Expr::apps(
                clean_kernel::Expr::const_(clean_kernel::Name::from_string(f), vec![]),
                [a, b],
            )
        };
        let (a64, b64) = (bv_lit(64, 1), bv_lit(64, 2));
        let (a128, b128) = (bv_lit(128, 1), bv_lit(128, 2));

        // POSITIVE: mint ≡ island authored model, per op, both widths.
        for (mint_name, island_name, a, b) in [
            ("cadd64_mint", "checkedAdd64", &a64, &b64),
            ("csub64_mint", "checkedSub64", &a64, &b64),
            ("cmul64_mint", "checkedMul64", &a64, &b64),
            ("cmul128_mint", "checkedMul128", &a128, &b128),
        ] {
            assert!(
                tc.is_def_eq(
                    &app2(mint_name, a.clone(), b.clone()),
                    &app2(island_name, a.clone(), b.clone())
                ),
                "{mint_name} must be delta-defeq to the island's authored {island_name}"
            );
        }

        // §5.7 NEG probe 1: the swapped-`some`/`none` island twin is NOT
        // def-eq to the mint (a consistently-reversed model must be CAUGHT).
        assert!(
            !tc.is_def_eq(
                &app2("cadd64_mint", a64.clone(), b64.clone()),
                &app2("checkedAddSwapped64", a64.clone(), b64.clone())
            ),
            "a swapped some/none model must NOT close against the mint"
        );

        // §5.7 NEG probe 2: the add↔sub swap is CAUGHT in both directions.
        assert!(
            !tc.is_def_eq(
                &app2("cadd64_mint", a64.clone(), b64.clone()),
                &app2("checkedSub64", a64.clone(), b64.clone())
            ),
            "an add mint must NOT close against the island's checkedSub64"
        );
        assert!(
            !tc.is_def_eq(
                &app2("csub64_mint", a64.clone(), b64.clone()),
                &app2("checkedAdd64", a64.clone(), b64.clone())
            ),
            "a sub mint must NOT close against the island's checkedAdd64"
        );
    }

    /// The §5.7 discipline for the GUARDED-NARROW lane: the mint's seeded
    /// model is DELTA-DEFEQ to the client island's AUTHORED `narrowWide` —
    /// through the real island elaborator — and each of the three forgeries is
    /// CAUGHT, not silently green.
    ///
    /// The forgeries are compared on an OPAQUE argument, never a literal: at a
    /// closed literal the guard scrutinee evaluates away, and the `fitsI128`
    /// forgery would agree with the mint on every value that happens to fit
    /// `i64` — the exact false-`Some` bug it must detect would go unseen. On an
    /// opaque argument both guards are stuck and structurally different, which
    /// is the comparison the citation lane actually performs.
    #[test]
    fn guarded_narrow_mint_is_defeq_to_the_island_model_and_forgeries_are_caught() {
        use trust_spec_elab::{Domain, MachineSIntWidth};
        let mut env = Environment::with_prelude();
        let mut file_ctx = FileContext::new();
        file_ctx.disable_external_import_search();
        let outcome =
            check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
        assert!(!outcome.is_rejected(), "the authored island must register: {outcome:?}");

        let i128d = Domain::Signed(MachineSIntWidth::I128);
        trust_spec_elab::admit_guarded_narrow_function(
            &mut env,
            "narrow_mint",
            std::slice::from_ref(&i128d),
            MachineSIntWidth::I128,
            MachineSIntWidth::I64,
            0,
        )
        .expect("the guarded-narrow mint must admit into the island env");

        // The island definition's `Option (BitVec 64)` codomain over a
        // `BitVec 128` parameter is what lets a probe clause spell
        // `result == narrow_isl(x)` at MIXED widths.
        assert_eq!(
            island_definition_signature(&env, "narrowWide"),
            Some((1, Some(Domain::OptionSigned(MachineSIntWidth::I64)))),
            "an Option (BitVec 64) island codomain must record OptionSigned(I64)"
        );

        let tc = clean_kernel::TypeChecker::new(&env);
        let app1 = |f: &str, a: clean_kernel::Expr| {
            clean_kernel::Expr::app(
                clean_kernel::Expr::const_(clean_kernel::Name::from_string(f), vec![]),
                a,
            )
        };
        // An OPAQUE wide argument: no closed-pipeline evaluation, so the
        // comparison is the delta-unfolding one the citation lane performs.
        let opaque = clean_kernel::Expr::fvar(clean_kernel::FVarId::new(0));
        let literal = clean_kernel::Expr::apps(
            clean_kernel::Expr::const_(clean_kernel::Name::from_string("BitVec.ofNat"), vec![]),
            [clean_kernel::Expr::nat_lit(128), clean_kernel::Expr::nat_lit(7)],
        );

        // POSITIVE: mint ≡ the island's authored model, opaque and closed.
        for (what, arg) in [("an opaque argument", &opaque), ("a closed literal", &literal)] {
            assert!(
                tc.is_def_eq(&app1("narrow_mint", arg.clone()), &app1("narrowWide", arg.clone())),
                "the guarded-narrow mint must be delta-defeq to the island's \
                 authored narrowWide at {what}"
            );
        }

        // NEG (a): arms swapped — `None` where the guard holds. This is the
        // wrong-verdict shape the recognizer already forbids structurally;
        // the oracle double-covers it, because a positive fixture alone
        // closes under a CONSISTENTLY wrong mint.
        // NEG (b): a narrower truncation — the payload loses its high bits.
        // NEG (c): the guard widened to `fitsI128`, which is TRUE for every
        //          `i128`, so every wide value would be admitted wrapped —
        //          exactly the VeriPB bug-C false-`Some` class.
        for (forgery, why) in [
            ("narrowWideSwapped", "a swapped some/none model"),
            ("narrowWideTrunc32", "a wrong-width truncation"),
            ("narrowWideFitsWide", "a guard widened to fitsI128"),
        ] {
            assert!(
                !tc.is_def_eq(&app1("narrow_mint", opaque.clone()), &app1(forgery, opaque.clone())),
                "{why} must NOT close against the guarded-narrow mint"
            );
        }

        drop(tc);

        // A wrong-width or wrong-direction request fails the MINT closed
        // rather than producing a differently-typed admission.
        for (from, to) in [
            (MachineSIntWidth::I128, MachineSIntWidth::I32),
            (MachineSIntWidth::I64, MachineSIntWidth::I64),
            (MachineSIntWidth::I64, MachineSIntWidth::I128),
        ] {
            assert!(
                trust_spec_elab::admit_guarded_narrow_function(
                    &mut env,
                    "narrow_parked",
                    std::slice::from_ref(&i128d),
                    from,
                    to,
                    0,
                )
                .is_err(),
                "({from:?} -> Option<{to:?}>) must park"
            );
        }
        // A parameter that is not at the source carrier, and an out-of-range
        // parameter index, both fail closed.
        assert!(
            trust_spec_elab::admit_guarded_narrow_function(
                &mut env,
                "narrow_parked",
                &[Domain::Signed(MachineSIntWidth::I64)],
                MachineSIntWidth::I128,
                MachineSIntWidth::I64,
                0,
            )
            .is_err(),
            "a narrowed parameter off the source carrier must fail closed"
        );
        assert!(
            trust_spec_elab::admit_guarded_narrow_function(
                &mut env,
                "narrow_parked",
                std::slice::from_ref(&i128d),
                MachineSIntWidth::I128,
                MachineSIntWidth::I64,
                1,
            )
            .is_err(),
            "an out-of-range parameter index must fail closed"
        );
    }

    /// The wiring arm for the GUARDED-NARROW lane: the measured `c2` body with
    /// certified facets mints through [`admit_function_into`] with the
    /// `Option<i64>` return domain recorded; uncertified facets mint nothing,
    /// and the UNGUARDED body (`c11`) mints nothing even with every facet
    /// certified.
    #[test]
    fn admit_function_into_mints_guarded_narrow() {
        use trust_types::{
            AggregateKind, BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
            SourceSpan, Statement, Terminator, Ty, VariantDef, VerifiableBody, VerifiableFunction,
        };
        let i64_ty = Ty::Int { width: 64, signed: true };
        let i128_ty = Ty::Int { width: 128, signed: true };
        let option = Ty::adt_enum_with_disc_safety(
            "core::option::Option",
            vec![
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), i64_ty.clone())],
                },
            ],
            true,
        );
        let agg = |variant: usize| AggregateKind::Adt {
            name: "core::option::Option".into(),
            variant,
            active_field: None,
            args: Some("core::option::Option<i64>".into()),
        };
        let stmt = |place: Place, rvalue: Rvalue| Statement::Assign {
            place,
            rvalue,
            span: SourceSpan::default(),
        };
        let switch = |flag: usize, zero: usize, other: usize| Terminator::SwitchInt {
            discr: Operand::Move(Place::local(flag)),
            targets: vec![(0, BlockId(zero))],
            otherwise: BlockId(other),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
        let narrow = VerifiableFunction {
            name: "narrow".into(),
            def_path: "crate::narrow".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: option.clone(), name: None },
                    LocalDecl { index: 1, ty: i128_ty, name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: None },
                    LocalDecl { index: 3, ty: Ty::Bool, name: None },
                    LocalDecl { index: 4, ty: i64_ty.clone(), name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![stmt(
                            Place::local(2),
                            Rvalue::BinaryOp(
                                trust_types::BinOp::Ge,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(-9_223_372_036_854_775_808)),
                            ),
                        )],
                        terminator: switch(2, 3, 1),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![stmt(
                            Place::local(3),
                            Rvalue::BinaryOp(
                                trust_types::BinOp::Le,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(9_223_372_036_854_775_807)),
                            ),
                        )],
                        terminator: switch(3, 3, 2),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![
                            stmt(
                                Place::local(4),
                                Rvalue::Cast(Operand::Copy(Place::local(1)), i64_ty),
                            ),
                            stmt(
                                Place::local(0),
                                Rvalue::Aggregate(agg(1), vec![Operand::Move(Place::local(4))]),
                            ),
                        ],
                        terminator: Terminator::Goto(BlockId(4)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![stmt(Place::local(0), Rvalue::Aggregate(agg(0), vec![]))],
                        terminator: Terminator::Goto(BlockId(4)),
                    },
                    BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: option,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let certified = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::narrow",
            true,
            true,
            true,
            true,
        )]);
        let mut env = Environment::with_prelude();
        let (path, admission) = admit_function_into(&mut env, &narrow, &certified)
            .expect("certified + recognized must mint");
        assert_eq!(path, "crate::narrow");
        assert_eq!(admission.arity, 1);
        assert_eq!(
            admission.return_domain().cloned(),
            Some(trust_spec_elab::Domain::OptionSigned(trust_spec_elab::MachineSIntWidth::I64))
        );
        assert_eq!(admission.param_names, None);

        // Uncertified facets: nothing mints even for the recognized body.
        let uncertified = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::narrow",
            true,
            true,
            false,
            true,
        )]);
        let mut env2 = Environment::with_prelude();
        assert!(
            admit_function_into(&mut env2, &narrow, &uncertified).is_none(),
            "uncertified facets must not mint"
        );

        // The UNGUARDED body — `Some(x as i64)` with no width check — mints
        // NOTHING even with every facet certified. If this ever mints, an
        // unguarded truncation has been admitted as if it were guarded.
        let mut unguarded = narrow;
        unguarded.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: unguarded.body.blocks[2].stmts.clone(),
            terminator: Terminator::Return,
        }];
        let mut env3 = Environment::with_prelude();
        assert!(
            admit_function_into(&mut env3, &unguarded, &certified).is_none(),
            "an unguarded narrowing cast must never mint"
        );
    }

    /// The wiring arm: a recognized checked body with certified facets mints
    /// through [`admit_function_into`]; uncertified facets or an unmarked
    /// callee mint nothing.
    #[test]
    fn admit_function_into_mints_checked_arithmetic() {
        use trust_types::{
            BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty, VariantDef,
            VerifiableBody, VerifiableFunction,
        };
        let int = Ty::Int { width: 64, signed: true };
        let option = Ty::adt_enum_with_disc_safety(
            "core::option::Option",
            vec![
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), int.clone())],
                },
            ],
            true,
        );
        let cadd = |callee: &str| VerifiableFunction {
            name: "cadd".into(),
            def_path: "crate::cadd".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: option.clone(), name: None },
                    LocalDecl { index: 1, ty: int.clone(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: int.clone(), name: Some("b".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: callee.into(),
                            callee_identity: None,
                            callee_key: None,
                            args: vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ],
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                            is_foreign: false,
                            is_unsafe_sig: false,
                            unwind: trust_types::UnwindEdge::Unreachable,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: option.clone(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let marked = "@trust-rustc-checked-primitive-method::core::num::<impl i64>::checked_add";

        // Certified facets + the marked callee: the admission mints, with the
        // Option return domain recorded.
        let certified = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::cadd",
            true,
            true,
            true,
            true,
        )]);
        let mut env = Environment::with_prelude();
        let minted = admit_function_into(&mut env, &cadd(marked), &certified);
        let (path, admission) = minted.expect("certified + recognized must mint");
        assert_eq!(path, "crate::cadd");
        assert_eq!(admission.arity, 2);
        assert_eq!(
            admission.return_domain().cloned(),
            Some(trust_spec_elab::Domain::OptionSigned(trust_spec_elab::MachineSIntWidth::I64))
        );
        assert_eq!(admission.param_names, None);

        // Uncertified facets: nothing mints even for the recognized body.
        let uncertified = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::cadd",
            true,
            false,
            true,
            true,
        )]);
        let mut env2 = Environment::with_prelude();
        assert!(
            admit_function_into(&mut env2, &cadd(marked), &uncertified).is_none(),
            "uncertified facets must not mint"
        );

        // An UNMARKED callee: the recognizer refuses, nothing mints.
        let mut env3 = Environment::with_prelude();
        assert!(
            admit_function_into(&mut env3, &cadd("core::num::<impl i64>::checked_add"), &certified)
                .is_none(),
            "an unmarked callee must not mint"
        );
    }

    /// A struct-returning per-term rule step mints ONE CONSTANT PER FIELD, and
    /// the coefficient field's constant really is the cap.
    ///
    /// This is the shape `TRUST_E6_DEBUG` reports for
    /// `veripb_core_proved::sat_term` at `-O`: an asymmetric select diamond
    /// whose empty arm keeps `coeff`, feeding an aggregate built in the return
    /// block, with the contract closure constructed in the entry block.
    #[test]
    fn a_struct_returning_body_mints_one_constant_per_field() {
        use trust_types::{
            AggregateKind, BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan,
            Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let i64t = || Ty::Int { width: 64, signed: true };
        let lit = Ty::adt("crate::Lit", vec![("var".into(), Ty::Int { width: 32, signed: false })]);
        let term =
            Ty::adt("crate::Term", vec![("coeff".into(), i64t()), ("lit".into(), lit.clone())]);
        let assign = |place: Place, rvalue: Rvalue| Statement::Assign {
            place,
            rvalue,
            span: SourceSpan::default(),
        };
        let func = VerifiableFunction {
            name: "sat".into(),
            def_path: "crate::sat".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: term.clone(), name: None },
                    LocalDecl { index: 1, ty: i64t(), name: Some("degree".into()) },
                    LocalDecl { index: 2, ty: i64t(), name: Some("coeff".into()) },
                    LocalDecl { index: 3, ty: lit, name: Some("lit".into()) },
                    LocalDecl { index: 4, ty: Ty::Bool, name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![assign(
                            Place::local(4),
                            Rvalue::BinaryOp(
                                trust_types::BinOp::Le,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(1)),
                            ),
                        )],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Move(Place::local(4)),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(1),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    // EMPTY arm: `_2` already holds `coeff`.
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![assign(
                            Place::local(2),
                            Rvalue::Use(Operand::Copy(Place::local(1))),
                        )],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![assign(
                            Place::local(0),
                            Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    name: "crate::Term".into(),
                                    variant: 0,
                                    active_field: None,
                                    args: None,
                                },
                                vec![
                                    Operand::Copy(Place::local(2)),
                                    Operand::Copy(Place::local(3)),
                                ],
                            ),
                        )],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 3,
                return_ty: term,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let facets = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::sat",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[func], &facets);

        // `coeff` mints; `lit` is skipped, because a `Lit` parameter flattens to
        // more than one row and is not a scalar operand.
        let coeff =
            minted.iter().find(|(key, _)| key == "crate::sat__field_coeff").unwrap_or_else(|| {
                panic!(
                    "no coeff field admission in {:?}",
                    minted.iter().map(|(k, _)| k).collect::<Vec<_>>()
                )
            });
        assert!(
            minted.iter().all(|(key, _)| key != "crate::sat__field_lit"),
            "a field with no scalar mint must be SKIPPED, not guessed"
        );

        // …and it IS the cap, by definitional reduction over the flattened
        // parameter list (degree, coeff, lit.var).
        let env = session.environment().expect("session env");
        let tc = clean_kernel::TypeChecker::new(env);
        let bv = |bits: u64, v: u64| {
            clean_kernel::Expr::apps(
                clean_kernel::Expr::const_(clean_kernel::Name::from_string("BitVec.ofNat"), vec![]),
                [clean_kernel::Expr::nat_lit(bits), clean_kernel::Expr::nat_lit(v)],
            )
        };
        let n = |v: u64| bv(64, v);
        let app = |deg: u64, cf: u64| {
            clean_kernel::Expr::apps(
                clean_kernel::Expr::const_(
                    clean_kernel::Name::from_string(&coeff.1.kernel_const),
                    vec![],
                ),
                [n(deg), n(cf), bv(32, 0)],
            )
        };
        assert!(tc.is_def_eq(&app(3, 5), &n(3)), "cap(degree=3, coeff=5) = 3");
        assert!(tc.is_def_eq(&app(5, 3), &n(3)), "cap(degree=5, coeff=3) = 3");
    }

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
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let facets = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::fst",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[fst], &facets);
        assert_eq!(minted.len(), 1, "the admissible projection is minted: {minted:?}");
        assert_eq!(minted[0].0, "crate::fst");
        // arity 2 (two parameters); the mint succeeded so the kernel accepted
        // `fun x y => x : u64 -> u64 -> u64`.
        assert_eq!(minted[0].1.arity, 2);
    }

    /// `fn degree_of(c: Cst) -> u64 { c.degree }` with `Cst { degree, coeff }`
    /// — the E6/E9 increment-7 shape, as the extractor produces it.
    fn field_projection_fixture(
        field_index: usize,
        fields: Vec<(String, trust_types::Ty)>,
    ) -> trust_types::VerifiableFunction {
        use trust_types::{
            BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
            Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        VerifiableFunction {
            name: "degree_of".into(),
            def_path: "crate::degree_of".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u64(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::adt("crate::Cst", fields),
                        name: Some("c".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Field(field_index)],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u64(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn scalar_cst_fields() -> Vec<(String, trust_types::Ty)> {
        vec![
            ("degree".to_string(), trust_types::Ty::u64()),
            ("coeff".to_string(), trust_types::Ty::u64()),
        ]
    }

    /// Certified facets under BOTH the def-path and the bare name — the
    /// dual keying `discharge_ensures_citations_in_walk` performs, since a
    /// clause names the function the way source does.
    fn all_facets(path: &str) -> trust_spec_elab::FacetTable {
        let bare = path.rsplit("::").next().unwrap_or(path);
        trust_spec_elab::FacetTable::from_structural_facets([
            (path, true, true, true, true),
            (bare, true, true, true, true),
        ])
    }

    /// The whole increment-7 lane in one assertion: an aggregate-parameter
    /// function is minted over its FLATTENED scalar list, and an `ensures`
    /// clause spelling a dotted path closes against it.
    #[test]
    fn admit_program_functions_mints_a_field_projection_and_a_dotted_clause_discharges() {
        let func = field_projection_fixture(0, scalar_cst_fields());
        let facets = all_facets("crate::degree_of");
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[func], &facets);
        assert_eq!(minted.len(), 1, "the field projection is minted: {minted:?}");
        let admission = &minted[0].1;
        // ONE BINDER PER SCALAR FIELD — the aggregate itself never reaches the
        // kernel, so the arity is 2 (`degree`, `coeff`), not 1.
        assert_eq!(admission.arity, 2);
        assert_eq!(
            admission.param_names.as_deref(),
            Some(["c.degree".to_string(), "c.coeff".to_string()].as_slice()),
            "the mint records the flattened clause-side names it bound"
        );

        // The clause `result == c.degree` now elaborates and closes by
        // reflexivity against the minted body `fun degree coeff => degree`.
        let mut table = facets.clone();
        table.admit("degree_of", admission.clone());
        let params = [("c.degree", "u64"), ("c.coeff", "u64")];
        let goal =
            trust_spec_elab::elaborate_ensures("result == c.degree", &params, "degree_of", &table)
                .expect("a dotted-path ensures clause elaborates");
        let env = session.environment().expect("an untainted session");
        assert!(
            clean_kernel::TypeChecker::new(env).infer_sort(&goal).is_ok(),
            "the elaborated goal must itself typecheck (the `reject_untyped_goal` gate): {goal}"
        );
    }

    /// The cross-check that makes the two independent flattenings safe: a
    /// clause whose parameter list is a REORDERING of the minted one is
    /// refused, even though it has the right length and the right domains and
    /// the resulting goal would typecheck perfectly well.
    #[test]
    fn a_reordered_parameter_list_is_refused_against_the_minted_import() {
        let func = field_projection_fixture(0, scalar_cst_fields());
        let facets = all_facets("crate::degree_of");
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[func], &facets);
        let mut table = facets.clone();
        table.admit("degree_of", minted[0].1.clone());
        let swapped = [("c.coeff", "u64"), ("c.degree", "u64")];
        let err =
            trust_spec_elab::elaborate_ensures("result == c.degree", &swapped, "degree_of", &table)
                .expect_err("a reordered flattening must NOT discharge");
        assert!(
            err.contains("disagrees with the parameter list"),
            "the refusal must name the real cause: {err}"
        );
    }

    /// ALL-OR-NOTHING: one field outside the supported scalar vocabulary
    /// refuses the whole parameter, and therefore the whole mint. Filtering it
    /// out instead would make this side's list disagree with the compiler's.
    ///
    /// SCOPE, since ref-self I2 (2026-09-19) made the opposite choice one lane
    /// over: this is the BY-VALUE struct parameter, where the rule stands and
    /// probe `f40` pins it. A FROZEN SHARED POINTEE skips its unsupported
    /// fields instead — soundly, because the mint there runs on the VIEW's own
    /// all-scalar body and never reaches this flattening at all. See
    /// `param_flat_rows`' doc.
    #[test]
    fn a_struct_with_a_non_scalar_field_mints_nothing() {
        let fields = vec![
            ("degree".to_string(), trust_types::Ty::u64()),
            (
                "terms".to_string(),
                trust_types::Ty::Slice { elem: Box::new(trust_types::Ty::u64()) },
            ),
        ];
        let func = field_projection_fixture(0, fields);
        let facets = all_facets("crate::degree_of");
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[func], &facets);
        assert!(minted.is_empty(), "an unsupported field refuses the whole mint: {minted:?}");
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
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
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

    /// THE LOAD-BEARING SOUNDNESS ARTIFACT for the `ite` select encoding.
    ///
    /// The mint emits Clean's own `ite` term, so the discharge is a TAUTOLOGY
    /// ABOUT `instLT{T}`: both sides are the same term, `Eq.refl` checks, and
    /// nothing is verified about what `<` MEANS. The previous
    /// `Nat.ble`-over-`toNat` encoding stated unsignedness out loud; this one
    /// delegates it. These theorems are what keep that honest.
    ///
    /// Each is proved by `fun h => h`, because the two sides are δβ-identical
    /// through `T.lt` → `instLTBitVec` → `Nat.lt` over `BitVec.toNat`. That is
    /// precisely what FAILS for a signed carrier, whose `.lt` would not unfold
    /// to a Nat order on `toNat` — so the theorem cannot be vacuously true.
    /// Swap in a signed instance and this test stops passing.
    ///
    /// The witness it rules out: `a = 2^63`, `b = 0`. Unsigned, `a < b` is
    /// false and Rust returns `b`. Signed, it is true and the island would
    /// denote `a`. Without this agreement, that divergence reports `Proved`
    /// with kernel-defeq strength — a false accept.
    #[test]
    fn machine_comparison_agrees_with_unsigned_nat_order_at_every_width() {
        for (ty, to_nat) in [
            ("UInt8", "UInt8.toNat"),
            ("UInt16", "UInt16.toNat"),
            ("UInt32", "UInt32.toNat"),
            ("UInt64", "UInt64.toNat"),
        ] {
            let mut env = Environment::with_prelude();
            let src = format!(
                "theorem lt_agrees : forall (a : {ty}) (b : {ty}), \
                     Iff (LT.lt a b) (Nat.lt ({to_nat} a) ({to_nat} b)) := \
                     fun a b => Iff.intro (fun h => h) (fun h => h)\n\n\
                 theorem le_agrees : forall (a : {ty}) (b : {ty}), \
                     Iff (LE.le a b) (Nat.le ({to_nat} a) ({to_nat} b)) := \
                     fun a b => Iff.intro (fun h => h) (fun h => h)"
            );
            let outcome = check_clean_island_into(&src, &mut env);
            assert!(
                !outcome.is_rejected(),
                "{ty}: machine comparison must agree with unsigned Nat order on \
                 the toNat images; kernel said {:?}",
                outcome.errors
            );

            // TEETH. The agreement above is proved by `fun h => h`, so it is
            // worth nothing unless the kernel would REFUSE a false agreement.
            // Reverse the operands: `a < b` iff `toNat b < toNat a` is exactly
            // what a wrong (or signed, or byte-swapped) instance would satisfy,
            // and it must not typecheck.
            let mut env_neg = Environment::with_prelude();
            let bogus = format!(
                "theorem lt_disagrees : forall (a : {ty}) (b : {ty}), \
                     Iff (LT.lt a b) (Nat.lt ({to_nat} b) ({to_nat} a)) := \
                     fun a b => Iff.intro (fun h => h) (fun h => h)"
            );
            let neg = check_clean_island_into(&bogus, &mut env_neg);
            assert!(
                neg.is_rejected(),
                "{ty}: a REVERSED agreement must be refused, or the positive \
                 direction proves nothing"
            );
        }
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
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    /// `fn <name>(a0: <param_ty>, …) -> u64 { 6 }` — a constant body behind
    /// `arg_count` (possibly zero) ignored parameters, as MIR shapes it: one
    /// block, `_0 = const 6u64`, return. The recognizer reports the SAME
    /// `ConstantUint { 6, 64 }` at every arity (it erases the parameters), so
    /// this is the input that distinguishes the arity-preserving routing from
    /// the nullary mint.
    fn const6_verifiable_function(
        name: &str,
        arg_count: usize,
        param_ty: trust_types::Ty,
    ) -> trust_types::VerifiableFunction {
        use trust_types::{
            BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
            Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let mut locals = vec![LocalDecl { index: 0, ty: Ty::u64(), name: None }];
        for i in 1..=arg_count {
            locals.push(LocalDecl {
                index: i,
                ty: param_ty.clone(),
                name: Some(format!("a{}", i - 1)),
            });
        }
        VerifiableFunction {
            name: name.into(),
            def_path: format!("crate::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(6, 64))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count,
                return_ty: Ty::u64(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    /// C6 (R2 campaign) — the `ConstantUint` routing is ARITY-PRESERVING.
    ///
    /// The recognizer erases arity: `fn c(a: u64) -> u64 { 6 }` reports the
    /// same `ConstantUint { 6, 64 }` a nullary `fn c() -> u64 { 6 }` does.
    /// `admit_function_into` used to route BOTH through the nullary mint
    /// (`admit_constant_function`, side B of type `d`), so a caller applying
    /// the unary function handed the defeq lane a type-mismatched term —
    /// measured as `Disagreement` in `fragment_widening_probes.rs::probe_e3`,
    /// whose route 2 also measured that the lambda-wrapped constant (the
    /// `admit_expr_function` spelling) ADMITS. This test pins the routing at
    /// the routing itself:
    ///
    ///  1. a unary constant admits at arity 1 and DISCHARGES an ensures
    ///     clause end-to-end by kernel defeq (with a wrong-value control, so
    ///     the discharge is not vacuous);
    ///  2. the nullary path is byte-for-byte unchanged (arity 0);
    ///  3. a mixed-domain unary constant (u32 parameter, u64 constant) mints
    ///     through the E6 tree producer at `UInt32 → UInt64`, the right value
    ///     and not a wrong one, and still declines on the frozen lane
    ///     (E9-CONSTANT-UINT-MIXED-1; it declined everywhere before, because
    ///     `admit_expr_function` is single-domain).
    #[test]
    fn constant_uint_routing_preserves_arity() {
        use trust_spec_elab::FacetTable;

        // (1) UNARY constant: mints lambda-wrapped, discharges by defeq.
        // Facets are recorded under BOTH the def-path and the bare name,
        // exactly as the compiler lane dual-keys them (`FacetTable::admitted`
        // requires the facet record and the admission under the SAME key, and
        // the ensures self-call resolves the bare name).
        let unary = const6_verifiable_function("c6u", 1, trust_types::Ty::u64());
        let table = FacetTable::from_structural_facets([
            ("crate::c6u", true, true, true, true),
            ("c6u", true, true, true, true),
        ]);
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def c6_isl (x : UInt64) : UInt64 := 6\n\ndef c7_isl (x : UInt64) : UInt64 := 7",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let (path, admission) = admit_function_into(&mut env, &unary, &table).expect(
            "a unary constant must mint through the arity-preserving expr route \
             (the nullary-only routing was the probe_e3 defect)",
        );
        assert_eq!(path, "crate::c6u");
        assert_eq!(
            admission.arity, 1,
            "the routing must preserve the function's arity; 0 is the erased mint"
        );
        let params: &[(&str, &str)] = &[("a", "u64")];
        let mut discharge_table = table.clone();
        discharge_table.admit("c6u", admission.clone());
        admit_certified_island_definition(&env, "c6_isl", &mut discharge_table)
            .expect("the island definition must admit for citation");
        let verdict = kernel_prove_ensures_by_defeq(
            &env,
            "result == c6_isl(a)",
            params,
            "c6u",
            &discharge_table,
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the lambda-wrapped constant must discharge end-to-end by kernel defeq; \
             got {verdict:?}"
        );

        // TEETH: the same route must NOT identify the constant with a
        // DIFFERENT island value, or the positive direction proves nothing.
        let mut wrong_table = table.clone();
        wrong_table.admit("c6u", admission);
        admit_certified_island_definition(&env, "c7_isl", &mut wrong_table)
            .expect("the control island definition must admit for citation");
        let wrong =
            kernel_prove_ensures_by_defeq(&env, "result == c7_isl(a)", params, "c6u", &wrong_table);
        assert!(
            !matches!(wrong, CitationVerdict::KernelStatementMatchCertified),
            "`6 == 7` must not certify; got {wrong:?}"
        );

        // (2) NULLARY path unchanged: arity 0 through the constant mint.
        let nullary = const6_verifiable_function("c6n", 0, trust_types::Ty::u64());
        let table_n = FacetTable::from_structural_facets([("crate::c6n", true, true, true, true)]);
        let mut env_n = Environment::with_prelude();
        let (_, admission_n) = admit_function_into(&mut env_n, &nullary, &table_n)
            .expect("the nullary constant path must keep minting");
        assert_eq!(admission_n.arity, 0, "a genuinely nullary constant stays nullary");

        // (3) MIXED-DOMAIN unary constant: u32 parameter, u64 constant
        // return. The single-domain expr route cannot type it; the tree
        // producer mints it with the parameter at its own carrier.
        let mixed =
            const6_verifiable_function("c6m", 1, trust_types::Ty::Int { width: 32, signed: false });
        let table_m = FacetTable::from_structural_facets([("crate::c6m", true, true, true, true)]);
        let mut env_m = Environment::with_prelude();
        let outcome_m = check_clean_island_into(
            "def c6m_isl (x : UInt32) : UInt64 := 6\n\ndef c7m_isl (x : UInt32) : UInt64 := 7",
            &mut env_m,
        );
        assert!(!outcome_m.is_rejected(), "island: {:?}", outcome_m.errors);
        let (_, admission_m) = admit_function_into(&mut env_m, &mixed, &table_m)
            .expect("a mixed-domain unary constant must mint through the tree producer");
        assert_eq!(admission_m.arity, 1, "the routing must preserve the arity");
        let tc = clean_kernel::TypeChecker::new(&env_m);
        let konst =
            |n: &str| clean_kernel::Expr::const_(clean_kernel::Name::from_string(n), vec![]);
        let image = konst(admission_m.kernel_const.as_str());
        tc.check_type(&image, &clean_kernel::Expr::arrow(konst("UInt32"), konst("UInt64")))
            .unwrap_or_else(|e| panic!("the image must be `UInt32 → UInt64`: {e:?}"));
        let x = clean_kernel::Expr::fvar(clean_kernel::FVarId::new(0));
        let at = |f: clean_kernel::Expr| clean_kernel::Expr::app(f, x.clone());
        assert!(
            tc.is_def_eq(&at(image.clone()), &at(konst("c6m_isl"))),
            "the image applied to any `x` must be the island's `6`"
        );
        assert!(!tc.is_def_eq(&at(image), &at(konst("c7m_isl"))), "`6` must not be `7`");
        drop(tc);
        // The frozen lane still declines: the tree producer is unmeasured
        // against the carrier-faithfulness gate. A fresh environment, so the
        // All-lane mint above cannot answer for it.
        let mut env_frozen = Environment::with_prelude();
        assert!(
            admit_function_into_lanes(
                &mut env_frozen,
                &mixed,
                &table_m,
                AdmissionLanes::FrozenShapes
            )
            .is_none(),
            "the frozen lane must decline a mixed-domain unary constant"
        );
        let mut env_all = Environment::with_prelude();
        assert!(
            admit_function_into_lanes(&mut env_all, &mixed, &table_m, AdmissionLanes::All)
                .is_some(),
            "control: the same function in a fresh environment mints on the All lane"
        );
    }

    /// PHASE D, PILLAR 2 — MEASURED. What does a citation actually bind to?
    ///
    /// §4.1.1 ratifies that a citation binds `ItemKey` (crate-instance ×
    /// declaration-path-hash × sort) plus revision digests, and that is ABSENT:
    /// `kernel_discharge_ensures_citation` takes the theorem as a bare NAME and
    /// looks it up in the environment. The scoping note calls this a
    /// soundness-relevant gap in a lane that already ships.
    ///
    /// This test measures how much a same-named substitute can actually get
    /// away with, because "resolves by name" overstates the exposure. Two
    /// CONTENT-based checks sit downstream of the lookup, and both are load
    /// bearing:
    ///
    ///   1. the theorem's statement must match the elaborated goal;
    ///   2. its proof term must grade `Certified` — an axiom or `sorry` in the
    ///      transitive closure downgrades it to `Trusted`, which does not
    ///      discharge.
    ///
    /// So substituting a DIFFERENT theorem under the same name only succeeds
    /// when that theorem genuinely proves the same goal with a clean closure —
    /// which is a different valid proof, not a hijack. The real `ItemKey` risk
    /// is cross-crate version skew, where "the same" name changes meaning
    /// between compilations; that is not reachable from a single environment
    /// and is what the pillar still has to address.
    #[test]
    fn a_citation_is_bound_by_statement_and_provenance_even_though_it_resolves_by_name() {
        let params: &[(&str, &str)] = &[("x", "u64")];

        // (1) An honest theorem under the name discharges.
        let mut env = Environment::with_prelude();
        let ok = check_clean_island_into(
            "def self_id (x : UInt64) : UInt64 := x\n\n\
             theorem t : forall (x : UInt64), Nat.le (UInt64.toNat x) (UInt64.toNat x) := \
                 fun x => Nat.le.refl (UInt64.toNat x)",
            &mut env,
        );
        assert!(!ok.is_rejected(), "setup island: {:?}", ok.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "self_id", &mut facets)
            .expect("self_id must admit");
        let verdict =
            kernel_discharge_ensures_citation(&env, "t", "result >= x", params, "self_id", &facets);
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "an honest theorem must discharge; got {verdict:?}"
        );

        // (2) SAME NAME, DIFFERENT STATEMENT — refused by the statement match,
        // not by any identity check.
        let mut env2 = Environment::with_prelude();
        let ok2 = check_clean_island_into(
            "def self_id (x : UInt64) : UInt64 := x\n\n\
             theorem t : forall (n : Nat), Nat.le n n := fun n => Nat.le.refl n",
            &mut env2,
        );
        assert!(!ok2.is_rejected(), "setup island 2: {:?}", ok2.errors);
        let mut facets2 = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env2, "self_id", &mut facets2)
            .expect("self_id must admit");
        let swapped = kernel_discharge_ensures_citation(
            &env2,
            "t",
            "result >= x",
            params,
            "self_id",
            &facets2,
        );
        assert!(
            !matches!(swapped, CitationVerdict::KernelStatementMatchCertified),
            "a same-named theorem with a different statement must NOT discharge; got {swapped:?}"
        );

        // (3) A NAME THAT IS NOT THERE fails closed rather than resolving to
        // anything nearby.
        let absent = kernel_discharge_ensures_citation(
            &env,
            "t_absent",
            "result >= x",
            params,
            "self_id",
            &facets,
        );
        assert!(
            !matches!(absent, CitationVerdict::KernelStatementMatchCertified),
            "an absent citation must fail closed; got {absent:?}"
        );
    }

    /// ITEM 10 HYPOTHESIS TEST — can an island theorem be stated over the Rust
    /// function ITSELF, via its E6 kernel import, rather than restating the
    /// body as an island definition and hoping it matches?
    ///
    /// This is the experiment the adversarial review asked for before anyone
    /// spends build time on two-phase island checking. It deliberately does in
    /// ONE test what the compiler does in two ordered phases, but in the
    /// OPPOSITE order: mint the program admission FIRST, then check an island
    /// that names `trust_import_crate__min2`.
    ///
    /// If this certifies, the feature is real and item 10 is purely an ORDERING
    /// problem — today `trust_check_clean_islands` runs before
    /// `trust_mint_program_admissions`, so the constant does not exist yet when
    /// the island is elaborated and any such theorem fails with an unknown
    /// constant. If it does NOT certify, item 10 is dead and no one need build
    /// the two-phase scheme.
    ///
    /// Note what the clause says: `result <= a` — pure Rust vocabulary, with
    /// NOTHING restated about the body. That is the whole point of the feature.
    #[test]
    fn an_island_theorem_can_be_stated_over_the_kernel_import() {
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::min2",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[min2_verifiable_function()], &facet_seed);
        assert_eq!(minted.len(), 1, "min2 must mint first: {minted:?}");
        assert_eq!(minted[0].1.kernel_const, "trust_import_crate__min2");

        // The island names the COMPILED FUNCTION, not a restatement of it.
        let outcome = session.check(
            "theorem min2_thm : forall (a : UInt64) (b : UInt64), \
                 Nat.le (UInt64.toNat (trust_import_crate__min2 a b)) (UInt64.toNat a) := \
                 fun a b => Decidable.casesOn \
                     (motive := fun (d : Decidable (LT.lt a b)) => \
                         Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64) \
                             d (fun _ => b) (fun _ => a))) (UInt64.toNat a)) \
                     (instDecidableUInt64Lt a b) \
                     (fun h => Iff.mp (Nat.not_lt (UInt64.toNat a) (UInt64.toNat b)) h) \
                     (fun h => Nat.le.refl (UInt64.toNat a))",
        );
        assert!(
            !outcome.is_rejected(),
            "an island theorem over the kernel import must check; got {:?}",
            outcome.errors
        );
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

    /// C6 clause-path regression, end-to-end at the crates level (e6 probe
    /// f06's exact shape): `fn answer() -> u64 { 42 }` with
    /// `ensures result == c42(0)` against an island
    /// `def c42 (x : UInt64) : UInt64 := 42`. After the `result` rewrite the
    /// clause is VARIABLE-FREE, and the atom used to default to `Nat` —
    /// minting `Eq Nat` over UInt64 terms, which the defeq route then
    /// rejected even though both sides reduce to `UInt64.ofNat 42`. The
    /// admissions' recorded return domains now steer the atom to the machine
    /// domain and the clause discharges.
    #[test]
    fn variable_free_constant_clause_discharges_at_the_machine_domain() {
        use trust_types::{
            BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
            Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        // fn answer() -> u64 { 42 } — the probes' nullary self-function.
        let answer = VerifiableFunction {
            name: "answer".into(),
            def_path: "crate::answer".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::u64(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::u64(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::answer",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[answer], &facet_seed);
        assert_eq!(minted.len(), 1, "answer must mint: {minted:?}");
        // The typed signature's return domain rides on the admission.
        assert_eq!(
            minted[0].1.return_domain(),
            Some(&trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64)),
            "the mint must record the u64 return domain"
        );

        let mut table = facet_seed.clone();
        for (path, admission) in &minted {
            table.admit(path.clone(), admission.clone());
            if let Some(bare) = path.rsplit("::").next() {
                table.admit(bare.to_string(), admission.clone());
            }
        }
        // f06's island: a one-parameter def the clause applies to a literal.
        let outcome = session.check("def c42 (x : UInt64) : UInt64 := 42");
        assert!(!outcome.is_rejected(), "island must check: {:?}", outcome.errors);
        let env = session.environment().expect("session env").clone();
        let c42 = admit_certified_island_definition(&env, "c42", &mut table)
            .expect("the island definition must be admissible");
        assert_eq!(
            c42.return_domain(),
            Some(&trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64)),
            "the island admission must record the UInt64 codomain"
        );

        let verdict =
            kernel_prove_ensures_by_defeq(&env, "result == c42(0)", &[], "crate::answer", &table);
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the variable-free constant clause must discharge by defeq; got {verdict:?}"
        );
    }

    /// The f04 driver shape, end-to-end at the crates level: a NULLARY island
    /// constant cited BARE — `ensures result == forty_two_isl`, no argument
    /// list at all. This was the LAST constant refusal after the C6 pair
    /// landed (74f315aa368 arity routing, 0acfcc223a2 clause domain): the
    /// bare identifier was lexed as a clause VARIABLE, so the exact-binding
    /// bijection demanded a type for it and elaboration refused before the
    /// kernel ever saw the goal (and, at the driver, `called_identifiers`
    /// never proposed it as a citation — measured TRUST_E9_DEBUG
    /// NO-ISLAND-CALL). The bare spelling now resolves through the SAME
    /// admission, firewall, and kernel constant as `forty_two_isl()`; the
    /// discharge below is the same Eq.refl-rechecked defeq as every other
    /// constant probe.
    #[test]
    fn bare_identifier_nullary_constant_citation_discharges() {
        use trust_types::{
            BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
            Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        // fn answer() -> u64 { 42 } — f04's nullary self-function.
        let answer = VerifiableFunction {
            name: "answer".into(),
            def_path: "crate::answer".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::u64(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::u64(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::answer",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[answer], &facet_seed);
        assert_eq!(minted.len(), 1, "answer must mint: {minted:?}");

        let mut table = facet_seed.clone();
        for (path, admission) in &minted {
            table.admit(path.clone(), admission.clone());
            if let Some(bare) = path.rsplit("::").next() {
                table.admit(bare.to_string(), admission.clone());
            }
        }
        // f04's island: a zero-arity def the clause cites with no parens.
        let outcome = session.check("def forty_two_isl : UInt64 := 42");
        assert!(!outcome.is_rejected(), "island must check: {:?}", outcome.errors);
        let env = session.environment().expect("session env").clone();
        let isl = admit_certified_island_definition(&env, "forty_two_isl", &mut table)
            .expect("the island definition must be admissible");
        assert_eq!(isl.arity, 0, "a non-Pi island type is a zero-arity definition");
        assert_eq!(
            isl.return_domain(),
            Some(&trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64)),
            "the island admission must record the UInt64 codomain"
        );

        let verdict = kernel_prove_ensures_by_defeq(
            &env,
            "result == forty_two_isl",
            &[],
            "crate::answer",
            &table,
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the bare nullary citation must discharge by defeq; got {verdict:?}"
        );
    }

    /// The negative control the bare spelling needs on day one (the same
    /// question f25 answers for the called spelling): island and clause
    /// BYTE-IDENTICAL to the discharging bare-citation test above; only the
    /// island's VALUE differs (43 against a body of 42). If this ever
    /// discharges, the bare-citation lane is reading the clause and not the
    /// kernel, and every bare discharge is worthless.
    #[test]
    fn bare_identifier_citation_of_a_wrong_constant_is_refused() {
        use trust_types::{
            BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
            Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let answer = VerifiableFunction {
            name: "answer".into(),
            def_path: "crate::answer".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::u64(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::u64(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::answer",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[answer], &facet_seed);
        assert_eq!(minted.len(), 1, "answer must mint: {minted:?}");
        let mut table = facet_seed.clone();
        for (path, admission) in &minted {
            table.admit(path.clone(), admission.clone());
            if let Some(bare) = path.rsplit("::").next() {
                table.admit(bare.to_string(), admission.clone());
            }
        }
        // The wrong constant: 43 against a Rust body of 42.
        let outcome = session.check("def forty_two_isl : UInt64 := 43");
        assert!(!outcome.is_rejected(), "island must check: {:?}", outcome.errors);
        let env = session.environment().expect("session env").clone();
        admit_certified_island_definition(&env, "forty_two_isl", &mut table)
            .expect("the island definition must be admissible");
        let verdict = kernel_prove_ensures_by_defeq(
            &env,
            "result == forty_two_isl",
            &[],
            "crate::answer",
            &table,
        );
        assert!(
            !matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "42 == 43 must NOT discharge by defeq; got {verdict:?}"
        );
    }

    /// `fn min2_i64(a: i64, b: i64) -> i64 { if a < b { a } else { b } }` —
    /// byte-for-byte the MIR of [`min2_verifiable_function`] at the SIGNED
    /// 64-bit carrier (the recognizer is shape-only; only the local types and
    /// the def path differ).
    fn min2_i64_verifiable_function() -> trust_types::VerifiableFunction {
        let mut func = min2_verifiable_function();
        func.name = "min2_i64".into();
        func.def_path = "crate::min2_i64".into();
        for local in &mut func.body.locals {
            if local.ty == trust_types::Ty::u64() {
                local.ty = trust_types::Ty::i64();
            }
        }
        func.body.return_ty = trust_types::Ty::i64();
        func
    }

    /// The i64 sign-flip order key, as island source: `Nat.xor (BitVec.toNat v)
    /// 2^63`. The SAME key spelling the E9 goal builder prints
    /// (`TRUST_E9_DEBUG`), so this constant doubles as the documentation of
    /// what an island author copies.
    fn i64_key(v: &str) -> String {
        format!("(Nat.xor (BitVec.toNat {v}) 9223372036854775808)")
    }

    /// E6 WIDENING INCREMENT 4 (signed select), citation lane end-to-end: a
    /// SIGNED i64 min2 mints through `ty_to_domain`/`admit_select_function`,
    /// and an island theorem over the kernel import DISCHARGES
    /// `ensures result <= a`. This is the acceptance shape for carrying
    /// compiler-checked contracts on i64 kernel functions (veripb Coeff=i64).
    #[test]
    fn signed_select_citation_discharges_over_the_kernel_import() {
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::min2_i64",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted =
            session.admit_program_functions(&[min2_i64_verifiable_function()], &facet_seed);
        assert_eq!(minted.len(), 1, "signed min2 must mint: {minted:?}");
        assert_eq!(minted[0].1.kernel_const, "trust_import_crate__min2_i64");

        // The island theorem, stated over the kernel import at the SIGNED
        // encoding: comparisons go through the sign-flip order keys, exactly
        // as the elaborated goal spells them. The proof is a REAL case split
        // on the minted `Nat.decLt` decision — not rfl-trivial.
        let (ka, kb) = (i64_key("a"), i64_key("b"));
        let theorem = format!(
            "theorem smin2_le_a : forall (a : BitVec 64) (b : BitVec 64), \
                 Nat.le (Nat.xor (BitVec.toNat (trust_import_crate__min2_i64 a b)) \
                     9223372036854775808) {ka} := \
                 fun a b => Decidable.casesOn \
                     (motive := fun (d : Decidable (Nat.lt {ka} {kb})) => \
                         Nat.le (Nat.xor (BitVec.toNat (Decidable.casesOn \
                             (motive := fun _ => BitVec 64) d (fun _ => b) (fun _ => a))) \
                             9223372036854775808) {ka}) \
                     (Nat.decLt {ka} {kb}) \
                     (fun h => Iff.mp (Nat.not_lt {ka} {kb}) h) \
                     (fun h => Nat.le.refl {ka})",
        );
        let outcome = session.check(&theorem);
        assert!(
            !outcome.is_rejected(),
            "the signed island theorem must check; got {:?}",
            outcome.errors
        );

        let mut table = facet_seed.clone();
        for (path, admission) in &minted {
            table.admit(path.clone(), admission.clone());
        }
        let env = session.environment().expect("session env");
        let params: &[(&str, &str)] = &[("a", "i64"), ("b", "i64")];
        let verdict = kernel_discharge_ensures_citation(
            env,
            "smin2_le_a",
            "result <= a",
            params,
            "crate::min2_i64",
            &table,
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the signed citation must DISCHARGE `ensures result <= a`; got {verdict:?}"
        );

        // FALSIFICATION — the same theorem must NOT discharge the converse
        // clause (`result >= a` is false for min2 in general).
        let converse = kernel_discharge_ensures_citation(
            env,
            "smin2_le_a",
            "result >= a",
            params,
            "crate::min2_i64",
            &table,
        );
        assert!(
            !matches!(converse, CitationVerdict::KernelStatementMatchCertified),
            "a `<=` proof must NOT discharge `result >= a`; got {converse:?}"
        );
    }

    /// `fn both(a: bool, b: bool) -> u8 { if a && b { 1 } else { 0 } }` as `-O`
    /// MIR shapes it (measured, `TRUST_E6_DEBUG`: `bb0[|switch[0->3]else1]
    /// bb1[|switch[0->3]else2] bb2[_0=use|goto4] bb3[_0=use|goto4] bb4[|ret]`):
    /// `bool` parameters and an integer result, the shape the E6 tree reader
    /// mints.
    fn both_flags_u8_verifiable_function() -> trust_types::VerifiableFunction {
        use trust_types::{
            BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
            Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let set = |v: u128| Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(v, 8))),
            span: SourceSpan::default(),
        };
        let switch = |flag: usize, otherwise: usize| Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(flag)),
            targets: vec![(0, BlockId(3))],
            otherwise: BlockId(otherwise),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
        VerifiableFunction {
            name: "both".into(),
            def_path: "crate::both".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u8(), name: None },
                    LocalDecl { index: 1, ty: Ty::Bool, name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("b".into()) },
                ],
                blocks: vec![
                    BasicBlock { id: BlockId(0), stmts: vec![], terminator: switch(1, 1) },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: switch(2, 2) },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![set(1)],
                        terminator: Terminator::Goto(BlockId(4)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![set(0)],
                        terminator: Terminator::Goto(BlockId(4)),
                    },
                    BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::u8(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    /// A cited `ensures result == spec(a, b)` on a function with `bool`
    /// parameters and a `u8` result DISCHARGES: the goal is
    /// `∀ a b : Bool, @Eq UInt8 (import a b) (spec a b)`.
    ///
    /// aterm's `relay_live::cursor` (`(bool, bool, bool, bool) -> u8`, cited by
    /// `cursor_is_exact`) was graded `unsupported_mir` on Trust build 16387: the
    /// goal builder typed the relation by the clause's variables, all `bool`, and
    /// built `@Eq Bool` over two `UInt8` terms, which the kernel refused
    /// (`TypeMismatch expected Bool, inferred UInt8 at [PiBody, PiBody, AppFn,
    /// AppArg]`). Here the import is the real E6 tree mint of the MIR body, the
    /// specification and the theorem are real island source, and the grade is the
    /// entry every E9 lane calls; a theorem about a different definition must
    /// still be refused, so the discharge is not the carrier change alone.
    #[test]
    fn cited_clause_with_bool_parameters_and_an_integer_result_discharges() {
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::both",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted =
            session.admit_program_functions(&[both_flags_u8_verifiable_function()], &facet_seed);
        assert_eq!(minted.len(), 1, "the `bool, bool -> u8` body must mint: {minted:?}");
        assert_eq!(minted[0].1.kernel_const, "trust_import_crate__both");

        let outcome = session.check(
            "def spec_both (a b : Bool) : UInt8 :=\n  if (a && b) = true then 1 else 0\n\n\
             def spec_either (a b : Bool) : UInt8 :=\n  if (a || b) = true then 1 else 0\n\n\
             theorem both_is_exact (a b : Bool) :\n    \
                 trust_import_crate__both a b = spec_both a b := by\n  \
               cases a <;> cases b <;> rfl\n\n\
             theorem either_refl (a b : Bool) : spec_either a b = spec_either a b := rfl",
        );
        assert!(!outcome.is_rejected(), "the island must check; got {:?}", outcome.errors);
        let env = session.environment().expect("session env");

        let mut table = facet_seed.clone();
        for (path, admission) in &minted {
            table.admit(path.clone(), admission.clone());
        }
        for name in ["spec_both", "spec_either"] {
            admit_certified_island_definition(env, name, &mut table)
                .unwrap_or_else(|e| panic!("`{name}` must be admitted: {e}"));
        }
        let params: &[(&str, &str)] = &[("a", "bool"), ("b", "bool")];
        let verdict = kernel_discharge_ensures_citation(
            env,
            "both_is_exact",
            "result == spec_both(a, b)",
            params,
            "crate::both",
            &table,
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the citation must DISCHARGE `ensures result == spec_both(a, b)`; got {verdict:?}"
        );

        // NEGATIVES. The right theorem on a clause naming another definition,
        // and a theorem about another definition, prove other propositions.
        for (theorem, clause) in [
            ("both_is_exact", "result == spec_either(a, b)"),
            ("either_refl", "result == spec_both(a, b)"),
        ] {
            let verdict = kernel_discharge_ensures_citation(
                env,
                theorem,
                clause,
                params,
                "crate::both",
                &table,
            );
            assert!(
                matches!(verdict, CitationVerdict::StatementOrCertificationRejected { .. }),
                "`{theorem}` must not discharge `{clause}`; got {verdict:?}"
            );
        }
    }

    /// TG15 open item 2 (`docs/validation/2026-11-06-tg15-result-carrier.md`):
    /// island binders spelled through a type alias. The carrier reader did not
    /// recognize `Flag` in `def spec_both_flag (a b : Flag) : UInt8`, so the
    /// WHOLE carrier record was `None` while the `UInt8` return domain was still
    /// recorded; the elaborator then read the call's `bool` arguments as
    /// operands of the relation and refused `result == spec_both_flag(a, b)`
    /// against the `u8` self-call. The reader now sees through the alias, as
    /// the kernel's definitional equality does: the record is the declared
    /// telescope and the citation discharges. A theorem about another
    /// definition is still refused, and an alias of a function type is still
    /// not a carrier.
    #[test]
    fn island_return_domain_reads_a_result_spelled_through_a_type_alias() {
        // Trust (2026-11-10, E9-RESULT-CARRIER-4): the RESULT is read by the
        // same alias-aware reader as the binders, and recorded only where its
        // carrier has one preimage.
        use trust_spec_elab::{Domain, MachineUIntWidth};
        let mut session = CleanIslandSession::new();
        let outcome = session.check(
            "abbrev Flag := Bool\n\n\
             abbrev Byte := UInt8\n\n\
             abbrev Word := BitVec 64\n\n\
             abbrev Pred := Nat -> Bool\n\n\
             def keep_flag (a : Bool) : Flag := a",
        );
        assert!(!outcome.is_rejected(), "the island must check; got {:?}", outcome.errors);
        let env = session.environment().expect("session env");
        let named =
            |name: &str| clean_kernel::Expr::const_(clean_kernel::Name::from_string(name), vec![]);
        assert_eq!(island_return_domain(env, &named("Flag")), Some(Domain::Bool));
        assert_eq!(
            island_return_domain(env, &named("Byte")),
            Some(Domain::Machine(MachineUIntWidth::U8))
        );
        // `BitVec 64` carries `i64`, `u128` and `usize64` alike: an alias of it
        // must not pick one.
        assert_eq!(island_return_domain(env, &named("Word")), None);
        assert_eq!(island_return_domain(env, &named("Pred")), None);
        // Spelled controls keep their answers.
        assert_eq!(island_return_domain(env, &named("Bool")), Some(Domain::Bool));
        assert_eq!(island_return_domain(env, &named("Nat")), Some(Domain::Nat));
        assert_eq!(island_return_domain(env, &named("Int")), Some(Domain::Int));
        // Through a definition's declared Pi type, as the admission reads it.
        let declared = env
            .get_const(&clean_kernel::Name::from_string("keep_flag"))
            .expect("the island defines keep_flag");
        assert_eq!(island_return_domain(env, &declared.type_), Some(Domain::Bool));
    }

    #[test]
    fn island_carriers_read_a_binder_through_a_type_alias() {
        use trust_spec_elab::{Carrier, DeclaredCarriers, MachineUIntWidth};
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::both",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted =
            session.admit_program_functions(&[both_flags_u8_verifiable_function()], &facet_seed);
        assert_eq!(minted.len(), 1, "the `bool, bool -> u8` body must mint: {minted:?}");

        let outcome = session.check(
            "abbrev Flag := Bool\n\n\
             abbrev Pred := Nat -> Bool\n\n\
             def spec_both_flag (a b : Flag) : UInt8 :=\n  if (a && b) = true then 1 else 0\n\n\
             def spec_either_flag (a b : Flag) : UInt8 :=\n  if (a || b) = true then 1 else 0\n\n\
             theorem both_flag_is_exact (a b : Bool) :\n    \
                 trust_import_crate__both a b = spec_both_flag a b := by\n  \
               cases a <;> cases b <;> rfl",
        );
        assert!(!outcome.is_rejected(), "the island must check; got {:?}", outcome.errors);
        let env = session.environment().expect("session env");
        assert_eq!(
            island_definition_carriers(env, "spec_both_flag"),
            Some(DeclaredCarriers {
                params: vec![Carrier::Bool, Carrier::Bool],
                ret: Carrier::UInt(MachineUIntWidth::U8),
            }),
            "a binder spelled through `abbrev Flag := Bool` is read as the `Bool` it names"
        );
        // Read directly rather than through a definition over it, so the
        // control does not rest on the island elaborating an application of an
        // alias-typed binder.
        let pred = clean_kernel::Expr::const_(clean_kernel::Name::from_string("Pred"), vec![]);
        assert_eq!(
            carrier_of_clean_type(env, &pred),
            None,
            "an alias of a function type is not a carrier"
        );

        let mut table = facet_seed.clone();
        for (path, admission) in &minted {
            table.admit(path.clone(), admission.clone());
        }
        for name in ["spec_both_flag", "spec_either_flag"] {
            admit_certified_island_definition(env, name, &mut table)
                .unwrap_or_else(|e| panic!("`{name}` must be admitted: {e}"));
        }
        let params: &[(&str, &str)] = &[("a", "bool"), ("b", "bool")];
        let verdict = kernel_discharge_ensures_citation(
            env,
            "both_flag_is_exact",
            "result == spec_both_flag(a, b)",
            params,
            "crate::both",
            &table,
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the citation must DISCHARGE `ensures result == spec_both_flag(a, b)`; got {verdict:?}"
        );
        let verdict = kernel_discharge_ensures_citation(
            env,
            "both_flag_is_exact",
            "result == spec_either_flag(a, b)",
            params,
            "crate::both",
            &table,
        );
        assert!(
            matches!(verdict, CitationVerdict::StatementOrCertificationRejected { .. }),
            "a theorem about another definition must not discharge; got {verdict:?}"
        );
    }

    /// The ill-typed-goal gate (2026-08-23), pinned on the exact shape that
    /// found it: an island definition over `Int` cited from an `i64` clause.
    /// Both sides of the elaborated equality beta-reduce to the same term, so
    /// WITHOUT the gate the kernel accepted `Eq.refl` against a proposition
    /// that does not type (`ident_int x` applies `Int -> Int` to a
    /// `BitVec 64`). The gate infers the goal's type first and fails closed
    /// with the fix in the message. The same acceptance reproduced at u64 —
    /// the hole predated the signed widening — so the u64 twin is pinned too.
    #[test]
    fn cross_carrier_island_call_fails_closed_not_ill_typed_discharge() {
        use trust_types::{
            BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, VerifiableBody, VerifiableFunction,
        };
        for (fn_ty, dom) in [(trust_types::Ty::i64(), "i64"), (trust_types::Ty::u64(), "u64")] {
            // `fn idi(x) -> x` at fn_ty — the identity projection, so BOTH
            // sides of the clause's equality beta-reduce to `x` and the ONLY
            // thing standing between the ill-typed goal and a discharge is
            // the gate under test.
            let func = VerifiableFunction {
                name: "idi".into(),
                def_path: "crate::idi".into(),
                span: SourceSpan::default(),
                body: VerifiableBody {
                    locals: vec![
                        LocalDecl { index: 0, ty: fn_ty.clone(), name: None },
                        LocalDecl { index: 1, ty: fn_ty.clone(), name: Some("x".into()) },
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
                    arg_count: 1,
                    return_ty: fn_ty.clone(),
                    datatype_defs: Default::default(),
                },
                contracts: Vec::new(),
                preconditions: Vec::new(),
                postconditions: Vec::new(),
                spec: Default::default(),
                tuple_layouts: Default::default(),
            };
            let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
                "crate::idi",
                true,
                true,
                true,
                true,
            )]);
            let mut session = CleanIslandSession::new();
            let minted = session.admit_program_functions(&[func], &facet_seed);
            assert_eq!(minted.len(), 1, "identity must mint at {dom}");

            let outcome = session.check("def ident_int (x : Int) : Int := x");
            assert!(!outcome.is_rejected(), "Int island must check: {:?}", outcome.errors);

            let mut table = facet_seed.clone();
            for (path, admission) in &minted {
                table.admit(path.clone(), admission.clone());
            }
            let env = session.environment().expect("session env").clone();
            admit_certified_island_definition(&env, "ident_int", &mut table)
                .expect("island definition must be admissible");
            let params: &[(&str, &str)] = &[("x", dom)];
            let defeq = kernel_prove_ensures_by_defeq(
                &env,
                "result == ident_int(x)",
                params,
                "crate::idi",
                &table,
            );
            assert!(
                matches!(defeq, CitationVerdict::ClauseOutsideFragment { .. }),
                "a cross-carrier island call must fail closed at {dom}; got {defeq:?}"
            );
        }
    }

    /// The UI-fixture shape for the signed lane, pinned at the library level:
    /// islands check FIRST (so the theorem cannot name the `trust_import_*`
    /// constant) and are stated over the UNFOLDED encoding instead, exactly
    /// like `tests/ui/trust/e9_min2_case_split_discharge.rs` does for u64.
    /// For i64 the readable island spelling is a named key helper —
    /// `def key64 (v : BitVec 64) : Nat := Nat.xor (BitVec.toNat v) 2^63` —
    /// with the theorem written through it; `key64` is an unfoldable island
    /// Definition, so kernel delta-reduction bridges it to the mint's inlined
    /// keys during grading. (The FULLY-inline spelling, with the ite and keys
    /// written raw inside the statement, trips a Clean elaborator unification
    /// corner — measured 2026-08-23 — so the helper form is the documented
    /// authoring shape.)
    #[test]
    fn signed_island_first_unfolded_theorem_discharges() {
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::min2_i64",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let keydef = "def key64 (v : BitVec 64) : Nat := \
             Nat.xor (BitVec.toNat v) 9223372036854775808";
        let outcome_key = session.check(keydef);
        assert!(!outcome_key.is_rejected(), "key helper must check: {:?}", outcome_key.errors);
        let theorem = "theorem min2_i64_le_left : forall (a : BitVec 64) (b : BitVec 64), \
                 Nat.le (key64 (if Nat.lt (key64 a) (key64 b) then a else b)) (key64 a) := \
                 fun a b => Decidable.casesOn \
                     (motive := fun (d : Decidable (Nat.lt (key64 a) (key64 b))) => \
                         Nat.le (key64 (Decidable.casesOn \
                             (motive := fun _ => BitVec 64) d (fun _ => b) \
                             (fun _ => a))) (key64 a)) \
                     (Nat.decLt (key64 a) (key64 b)) \
                     (fun h => Iff.mp (Nat.not_lt (key64 a) (key64 b)) h) \
                     (fun h => Nat.le.refl (key64 a))";
        let outcome = session.check(theorem);
        assert!(!outcome.is_rejected(), "island theorem must check: {:?}", outcome.errors);

        // The mint happens AFTER the islands, as in the compiler.
        let minted =
            session.admit_program_functions(&[min2_i64_verifiable_function()], &facet_seed);
        assert_eq!(minted.len(), 1, "signed min2 must mint: {minted:?}");
        let mut table = facet_seed.clone();
        for (path, admission) in &minted {
            table.admit(path.clone(), admission.clone());
        }
        let env = session.environment().expect("session env");
        let verdict = kernel_discharge_ensures_citation(
            env,
            "min2_i64_le_left",
            "result <= a",
            &[("a", "i64"), ("b", "i64")],
            "crate::min2_i64",
            &table,
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the island-first unfolded-encoding theorem must discharge; got {verdict:?}"
        );
    }

    /// THE SHARED-BARE-NAME DEFECT (fixed 2026-08-26), end to end through the
    /// citation lane.
    ///
    /// `record_fn_facets` keys an item's facet record under its canonical
    /// def-path AND every spellable suffix, and evicts (forever) any key two
    /// def-paths claim. That eviction is correct and is KEPT: an ambiguous
    /// spelling an author writes in a clause must fail closed. But the
    /// contracted function's OWN identity is not something an author wrote —
    /// the compiler knows the item — and the ensures lane used to derive it from
    /// the BARE name, re-entering the ambiguity keyspace through the one door it
    /// did not need. A contract on `veripb_core_proved::cap_coeff` (bare name
    /// shared with `CoeffDomain::cap_coeff` and four impls) could therefore
    /// NEVER bind `result`.
    ///
    /// Here: two items claim the bare `min2_i64`, so that key is evicted; the
    /// canonical def-path survives and the SAME theorem, clause, and mint
    /// discharge through it — while the old bare identity still fails closed.
    #[test]
    fn ensures_discharge_keys_on_the_def_path_when_the_bare_name_is_evicted() {
        let self_path = "crate::min2_i64";
        let twin_path = "crate::other::min2_i64";
        // The collision `record_fn_facets` detects: both items' spellable suffix
        // sets contain the bare name.
        let bare = "min2_i64".to_string();
        assert!(trust_spec_elab::spec_spellings(self_path).contains(&bare));
        assert!(trust_spec_elab::spec_spellings(twin_path).contains(&bare));
        // …so the table it leaves behind holds every key EXCEPT that one.
        // `other::min2_i64` (the twin's unambiguous suffix) survives too; the
        // contracted function has no surviving suffix at all, only its def-path.
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([
            (self_path, true, true, true, true),
            (twin_path, true, true, true, true),
            ("other::min2_i64", true, true, true, true),
        ]);
        assert!(facet_seed.get(&bare).is_none(), "the ambiguous bare key must stay evicted");

        let mut session = CleanIslandSession::new();
        let keydef = "def key64 (v : BitVec 64) : Nat := \
             Nat.xor (BitVec.toNat v) 9223372036854775808";
        assert!(!session.check(keydef).is_rejected(), "key helper must check");
        let theorem = "theorem min2_i64_le_left : forall (a : BitVec 64) (b : BitVec 64), \
                 Nat.le (key64 (if Nat.lt (key64 a) (key64 b) then a else b)) (key64 a) := \
                 fun a b => Decidable.casesOn \
                     (motive := fun (d : Decidable (Nat.lt (key64 a) (key64 b))) => \
                         Nat.le (key64 (Decidable.casesOn \
                             (motive := fun _ => BitVec 64) d (fun _ => b) \
                             (fun _ => a))) (key64 a)) \
                     (Nat.decLt (key64 a) (key64 b)) \
                     (fun h => Iff.mp (Nat.not_lt (key64 a) (key64 b)) h) \
                     (fun h => Nat.le.refl (key64 a))";
        let outcome = session.check(theorem);
        assert!(!outcome.is_rejected(), "island theorem must check: {:?}", outcome.errors);

        let minted =
            session.admit_program_functions(&[min2_i64_verifiable_function()], &facet_seed);
        assert_eq!(minted.len(), 1, "the contracted function must still mint: {minted:?}");
        // Admission keying mirrors `trust_mint_program_admissions`: def-path plus
        // every spelling. The evicted bare key gets an admission entry but NO
        // facet record, so `FacetTable::admitted` still refuses it — that is the
        // fail-closed invariant this test also pins.
        let mut table = facet_seed.clone();
        for (path, admission) in &minted {
            for spelling in trust_spec_elab::spec_spellings(path) {
                if spelling != *path {
                    table.admit(spelling, admission.clone());
                }
            }
            table.admit(path.clone(), admission.clone());
        }
        assert!(table.admitted(&bare).is_none(), "an evicted spelling is never admitted");

        let env = session.environment().expect("session env");
        let params: &[(&str, &str)] = &[("a", "i64"), ("b", "i64")];

        // FIXED: the canonical def-path identity reaches the surviving record
        // and the postcondition discharges.
        let by_def_path = kernel_discharge_ensures_citation(
            env,
            "min2_i64_le_left",
            "result <= a",
            params,
            self_path,
            &table,
        );
        assert!(
            matches!(by_def_path, CitationVerdict::KernelStatementMatchCertified),
            "the canonical def-path must discharge; got {by_def_path:?}"
        );

        // UNCHANGED (eviction untouched): the ambiguous bare spelling still
        // fails closed — it can never bind `result` to one of several candidate
        // items.
        let by_bare = kernel_discharge_ensures_citation(
            env,
            "min2_i64_le_left",
            "result <= a",
            params,
            &bare,
            &table,
        );
        match by_bare {
            CitationVerdict::ClauseOutsideFragment { ref reason } => {
                assert!(reason.contains("E6-admitted"), "{reason}");
            }
            other => panic!("an evicted bare identity must fail closed; got {other:?}"),
        }
    }

    /// Signed select, defeq lane + the two NEG probes the mint's comment
    /// demands: (1) an island def over the sign-flip keys discharges
    /// `result == isl(a, b)` by pure kernel defeq; (2) the UNSIGNED-order
    /// confusion (plain `toNat` keys, no sign flip) must NOT discharge — that
    /// island denotes a function that differs at mixed-sign inputs; (3) the
    /// swapped-branch (max-where-min) island must NOT discharge — the
    /// `ite` argument-order trap is only caught by a NEG probe.
    #[test]
    fn signed_island_defeq_discharges_and_confusions_fail_closed() {
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::min2_i64",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted =
            session.admit_program_functions(&[min2_i64_verifiable_function()], &facet_seed);
        assert_eq!(minted.len(), 1, "signed min2 must mint: {minted:?}");

        let (ka, kb) = (i64_key("a"), i64_key("b"));
        // (1) The signed island spelling: keys compared through Nat's `<`.
        let smin = format!(
            "def smin_isl (a : BitVec 64) (b : BitVec 64) : BitVec 64 := \
                 if Nat.lt {ka} {kb} then a else b"
        );
        // (2) The unsigned-order CONFUSION: raw toNat keys. A DIFFERENT
        // function at mixed signs (it calls i64::MIN the larger value).
        let umin = "def umin_isl (a : BitVec 64) (b : BitVec 64) : BitVec 64 := \
                 if Nat.lt (BitVec.toNat a) (BitVec.toNat b) then a else b"
            .to_string();
        // (3) The argument-order trap: branches swapped mints max, not min.
        let smax = format!(
            "def smax_isl (a : BitVec 64) (b : BitVec 64) : BitVec 64 := \
                 if Nat.lt {ka} {kb} then b else a"
        );
        for src in [&smin, &umin, &smax] {
            let outcome = session.check(src);
            assert!(!outcome.is_rejected(), "island must check: {src}: {:?}", outcome.errors);
        }

        let mut table = facet_seed.clone();
        for (path, admission) in &minted {
            table.admit(path.clone(), admission.clone());
        }
        let env = session.environment().expect("session env").clone();
        for isl in ["smin_isl", "umin_isl", "smax_isl"] {
            admit_certified_island_definition(&env, isl, &mut table)
                .expect("island definition must be admissible");
        }
        let params: &[(&str, &str)] = &[("a", "i64"), ("b", "i64")];
        let discharge = |clause: &str| {
            kernel_prove_ensures_by_defeq(&env, clause, params, "crate::min2_i64", &table)
        };

        let verdict = discharge("result == smin_isl(a, b)");
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the signed island spelling must defeq-discharge; got {verdict:?}"
        );
        let confusion = discharge("result == umin_isl(a, b)");
        assert!(
            !matches!(confusion, CitationVerdict::KernelStatementMatchCertified),
            "the UNSIGNED-order island must NOT discharge a signed select; got {confusion:?}"
        );
        let swapped = discharge("result == smax_isl(a, b)");
        assert!(
            !matches!(swapped, CitationVerdict::KernelStatementMatchCertified),
            "the swapped-branch island must NOT discharge; got {swapped:?}"
        );
    }

    /// `fn le_i64(a: i64, b: i64) -> bool { a <= b }` — the comparison-to-bool
    /// shape (E6 widening increment 5) as MIR lowers it: one block, one
    /// `BinaryOp(Le, _1, _2)` assigned to the return place.
    fn le_i64_verifiable_function() -> trust_types::VerifiableFunction {
        use trust_types::{
            BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        VerifiableFunction {
            name: "le_i64".into(),
            def_path: "crate::le_i64".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: None },
                    LocalDecl { index: 1, ty: Ty::i64(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i64(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Bool,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    /// E6 widening increment 5, end-to-end at the admission level: the
    /// guard-shape comparison function (`fn le_i64(a: i64, b: i64) -> bool`)
    /// mints through `ty_to_domain` + `admit_comparison_function`, and the
    /// IMPORTED constant is semantically validated by definitional reduction
    /// at the kernel — including the mixed-sign row an unsigned-order mint
    /// gets wrong.
    ///
    /// MEASURED BOUNDARY (2026-08-23, this increment): the E9 defeq/citation
    /// lanes cannot yet carry a clause over a BOOL-RETURNING program
    /// function, for a reason OUTSIDE this shape: `atom_domain` infers a
    /// comparison atom's carrier from its argument VARIABLES, so
    /// `result == le_isl(a, b)` over i64 params mints `Eq (BitVec 64) …`
    /// around two Bool-valued calls — a wrong-typed goal that fails closed
    /// (never wrongly discharges). Widening the clause elaborator to type
    /// call atoms by their admitted callee's RETURN domain is the follow-on
    /// increment; the admission below is what it will consume.
    #[test]
    fn comparison_bool_shape_mints_and_is_semantically_faithful() {
        let facet_seed = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::le_i64",
            true,
            true,
            true,
            true,
        )]);
        let mut session = CleanIslandSession::new();
        let minted = session.admit_program_functions(&[le_i64_verifiable_function()], &facet_seed);
        assert_eq!(minted.len(), 1, "le_i64 must mint: {minted:?}");
        assert_eq!(minted[0].1.kernel_const, "trust_import_crate__le_i64");
        assert_eq!(minted[0].1.arity, 2);

        // Semantic validation of the IMPORT by definitional reduction, on the
        // kernel-canonical raw-literal BitVec values (see the spec-elab signed
        // select test for why raw literals).
        let env = session.environment().expect("session env");
        let tc = clean_kernel::TypeChecker::new(env);
        let btrue =
            clean_kernel::Expr::const_(clean_kernel::Name::from_string("Bool.true"), vec![]);
        let bfalse =
            clean_kernel::Expr::const_(clean_kernel::Name::from_string("Bool.false"), vec![]);
        let lit = |v: u128| clean_kernel::Expr::nat_lit(u64::try_from(v).unwrap());
        let app2 = |a: clean_kernel::Expr, b: clean_kernel::Expr| {
            clean_kernel::Expr::apps(
                clean_kernel::Expr::const_(
                    clean_kernel::Name::from_string("trust_import_crate__le_i64"),
                    vec![],
                ),
                [a, b],
            )
        };
        let neg1 = (1u128 << 64) - 1; // -1 as a two's-complement bit pattern
        assert!(tc.is_def_eq(&app2(lit(3), lit(5)), &btrue), "le_i64(3, 5)");
        assert!(tc.is_def_eq(&app2(lit(5), lit(3)), &bfalse), "!le_i64(5, 3)");
        // Le-vs-Lt discriminator: a mint that read `<=` as `<` fails here.
        assert!(tc.is_def_eq(&app2(lit(3), lit(3)), &btrue), "le_i64(3, 3)");
        // The mixed-sign row: signed order says -1 <= 1; raw bit order says
        // the opposite. A mint that dropped the sign-flip keys fails here.
        assert!(tc.is_def_eq(&app2(lit(neg1), lit(1)), &btrue), "le_i64(-1, 1)");
        assert!(tc.is_def_eq(&app2(lit(1), lit(neg1)), &bfalse), "!le_i64(1, -1)");

        // NEG: without the facet certification nothing mints.
        let mut bare_session = CleanIslandSession::new();
        let none = bare_session.admit_program_functions(
            &[le_i64_verifiable_function()],
            &trust_spec_elab::FacetTable::new(),
        );
        assert!(none.is_empty(), "an uncertified comparison body must not mint");
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
                            func: "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add".into(),
                            callee_identity: None,
                            callee_key: None,
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
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
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

    /// The CITED twin of the test above — the conversion idiom
    /// `ensures result == spec(x) by impl_is_spec`. A cited clause that names
    /// an island definition elaborates ONLY once that definition is admitted
    /// into the clause's facet table (the compiler's cited lanes now do that,
    /// through the same `admit_certified_island_definition` the uncited lane
    /// always used); without the admission it is the measured refusal "no
    /// diagnostic E6 facet record exists". The admission decides which kernel
    /// constant `spec_cd` denotes and nothing else: the cited theorem must
    /// still prove the resulting goal, so a theorem about a DIFFERENT
    /// definition, or the right theorem on a clause naming a different
    /// definition, stays rejected.
    #[test]
    fn cited_clause_naming_an_island_definition_needs_the_admission_and_the_right_theorem() {
        use trust_spec_elab::FacetTable;
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def self_cd (x : UInt64) : UInt64 := x\n\n\
             def spec_cd (x : UInt64) : UInt64 := x\n\n\
             def other_cd (x : UInt64) : UInt64 := UInt64.add x 1\n\n\
             theorem self_is_spec : forall (x : UInt64), self_cd x = spec_cd x := fun x => rfl\n\n\
             theorem other_refl : forall (x : UInt64), other_cd x = other_cd x := fun x => rfl",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let params: &[(&str, &str)] = &[("x", "u64")];

        // The function's own table: `self_cd` stands in for the E6 import, as
        // in the uncited test above. No island definition is admitted yet.
        let mut function_table = FacetTable::new();
        admit_certified_island_definition(&env, "self_cd", &mut function_table)
            .expect("strict kernel definition must be admitted");

        // BEFORE the admission: the clause is outside the fragment, whatever
        // the theorem says. This is the refusal the cited lane used to stop at.
        match kernel_discharge_ensures_citation(
            &env,
            "self_is_spec",
            "result == spec_cd(x)",
            params,
            "self_cd",
            &function_table,
        ) {
            CitationVerdict::ClauseOutsideFragment { reason } => {
                assert!(
                    reason.contains("no diagnostic E6 facet record exists for `spec_cd`"),
                    "{reason}"
                );
            }
            other => panic!("an unadmitted island callee must fail closed, got {other:?}"),
        }

        // WITH a clause-local admission of exactly the definition the clause
        // names: the theorem is graded against `∀ x, self_cd x = spec_cd x`.
        let mut clause_table = function_table.clone();
        admit_certified_island_definition(&env, "spec_cd", &mut clause_table)
            .expect("strict kernel definition must be admitted");
        assert!(
            matches!(
                kernel_discharge_ensures_citation(
                    &env,
                    "self_is_spec",
                    "result == spec_cd(x)",
                    params,
                    "self_cd",
                    &clause_table,
                ),
                CitationVerdict::KernelStatementMatchCertified
            ),
            "the right theorem must discharge the island-naming clause"
        );
        // The admission is CLAUSE-LOCAL: the function's table is untouched.
        assert!(function_table.admitted("spec_cd").is_none());

        // NEGATIVE — a theorem about a DIFFERENT definition proves a different
        // proposition (`other_cd x = other_cd x`), not this goal.
        assert!(
            matches!(
                kernel_discharge_ensures_citation(
                    &env,
                    "other_refl",
                    "result == spec_cd(x)",
                    params,
                    "self_cd",
                    &clause_table,
                ),
                CitationVerdict::StatementOrCertificationRejected { .. }
            ),
            "a theorem about a different definition must not discharge"
        );

        // NEGATIVE — the right theorem on a clause naming a DIFFERENT
        // definition: the body is `x`, `other_cd x` is `x + 1`.
        let mut other_table = function_table.clone();
        admit_certified_island_definition(&env, "other_cd", &mut other_table)
            .expect("strict kernel definition must be admitted");
        assert!(
            matches!(
                kernel_discharge_ensures_citation(
                    &env,
                    "self_is_spec",
                    "result == other_cd(x)",
                    params,
                    "self_cd",
                    &other_table,
                ),
                CitationVerdict::StatementOrCertificationRejected { .. }
            ),
            "a false island-naming clause must not discharge"
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

    /// The E6/E9 widening increment 8 pin, end to end and at BOTH shapes the
    /// increment unblocks — with the clause elaborator, the real island
    /// elaborator, and the kernel all in the loop.
    ///
    /// (1) A MIXED-WIDTH island CALL. `eqOkW (m : BitVec 64) (t : BitVec 128)`
    ///     applied to an `i64` and an `i128` parameter. Before the increment
    ///     the elaborator typed an atom's operands by ONE ambient domain taken
    ///     from its variables, so this reported "mixed domains in one
    ///     comparison (Signed(I64) and Signed(I128))" and the clause never
    ///     reached the kernel — even though the two widths were never in one
    ///     comparison, only in one argument list.
    ///
    /// (2) A VARIABLE-LESS atom. `result == zeroI64()` on a nullary signed
    ///     constant. Before the increment an atom with no variables defaulted
    ///     to `Nat`, putting a `BitVec 64` island constant under an `Eq Nat`,
    ///     which the ill-typed-goal gate refused — the documented f04-f09 wall.
    ///
    /// (3) The NEGATIVE that must NOT move: a bare `machine == truth` across
    ///     two widths, with NO typed callee to justify it. The elaborator has
    ///     no cast there and refuses it exactly as before. This is the pin that
    ///     keeps the widening from becoming a silent coercion.
    #[test]
    fn typed_call_arguments_take_the_callees_declared_carriers() {
        use trust_spec_elab::{Domain, FacetStatus, FacetTable, FnFacets, MachineSIntWidth};
        let mut env = Environment::with_prelude();
        let mut file_ctx = FileContext::new();
        file_ctx.disable_external_import_search();
        let outcome =
            check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
        assert!(!outcome.is_rejected(), "the authored island must register: {outcome:?}");

        let i64d = Domain::Signed(MachineSIntWidth::I64);
        let i128d = Domain::Signed(MachineSIntWidth::I128);
        // The SELF mints: `fn eq_ok(machine: i64, truth: i128) -> bool` and
        // `fn zero_i64() -> i64 { 0 }`, exactly as the compiler mints them.
        let eq_ok = trust_spec_elab::admit_widened_eq_function(
            &mut env,
            "eq_ok_def",
            &[i64d.clone(), i128d.clone()],
            MachineSIntWidth::I64,
            MachineSIntWidth::I128,
            0,
            1,
            true,
        )
        .expect("the widened-equality mint must admit");
        let zero_i64 = trust_spec_elab::admit_signed_constant_function(
            &mut env,
            "zero_i64_def",
            0,
            MachineSIntWidth::I64,
        )
        .expect("the signed-constant mint must admit");

        let cert = || FacetStatus::Certified { evidence: "increment-8-pin".to_string() };
        let admissible =
            || FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let mut facets = FacetTable::new();
        facets.insert("eq_ok", admissible());
        facets.admit("eq_ok", eq_ok);
        facets.insert("zero_i64", admissible());
        facets.admit("zero_i64", zero_i64);
        for island in ["eqOkW", "zeroI64", "eqOkZeroExt"] {
            admit_certified_island_definition(&env, island, &mut facets)
                .unwrap_or_else(|e| panic!("island `{island}` must be admitted: {e}"));
        }

        // (1) The mixed-width call now elaborates AND closes: both sides unfold
        // to the same stuck `toInt64`/`ofInt128` chain.
        let mixed_params: &[(&str, &str)] = &[("machine", "i64"), ("truth", "i128")];
        let verdict = kernel_prove_ensures_by_defeq(
            &env,
            "result == eqOkW(machine, truth)",
            mixed_params,
            "eq_ok",
            &facets,
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "a call whose DECLARED parameters differ in width must discharge: {verdict:?}"
        );

        // ...and the widening buys no proving power: the ZERO-extending twin,
        // which agrees with the mint on every non-negative `machine` and
        // differs on every negative one, is still refused by the kernel.
        assert!(
            !matches!(
                kernel_prove_ensures_by_defeq(
                    &env,
                    "result == eqOkZeroExt(machine, truth)",
                    mixed_params,
                    "eq_ok",
                    &facets
                ),
                CitationVerdict::KernelStatementMatchCertified
            ),
            "a zero-extending forgery must NOT discharge against the sign-extending mint"
        );

        // (2) The variable-less atom takes the mint's RECORDED return domain,
        // and the island's declared `BitVec 64` result carrier agrees with it.
        let verdict =
            kernel_prove_ensures_by_defeq(&env, "result == zeroI64()", &[], "zero_i64", &facets);
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "a nullary signed constant against an island constant must discharge: {verdict:?}"
        );

        // (3) THE NEGATIVE. Two operands of different widths in ONE comparison,
        // reached through no callee at all: the elaborator has no cast to
        // justify it and must still refuse, with the same message as before.
        let verdict = kernel_prove_ensures_by_defeq(
            &env,
            "result == eqOkW(machine, truth) && machine == truth",
            mixed_params,
            "eq_ok",
            &facets,
        );
        match verdict {
            CitationVerdict::ClauseOutsideFragment { reason } => assert!(
                reason.contains("mixed domains in one comparison"),
                "the bare cross-width comparison must keep its own refusal: {reason}"
            ),
            other => panic!("a bare cross-width comparison must fail closed, got {other:?}"),
        }

        // (4) A call at the WRONG carrier is refused BY NAME rather than
        // elaborated and left for the ill-typed-goal gate: `eqOkW` declares its
        // first parameter at `BitVec 64`, and an `i128` argument is not that.
        let verdict = kernel_prove_ensures_by_defeq(
            &env,
            "result == eqOkW(truth, truth)",
            mixed_params,
            "eq_ok",
            &facets,
        );
        match verdict {
            CitationVerdict::ClauseOutsideFragment { reason } => assert!(
                reason.contains("declares parameter 0 at carrier `BitVec 64`"),
                "an argument off the declared carrier must be named: {reason}"
            ),
            other => panic!("an argument off the declared carrier must fail closed, got {other:?}"),
        }
    }

    /// The carrier reader is the AUTHORITY the increment-8 check rests on, so
    /// it is pinned directly: it reports the island's declared telescope, and
    /// it answers `None` — leaving the elaborator on its pre-increment
    /// behaviour — for anything it does not recognize.
    #[test]
    fn island_definition_carriers_reports_the_declared_telescope() {
        use trust_spec_elab::{Carrier, MachineUIntWidth};
        let mut env = Environment::with_prelude();
        let mut file_ctx = FileContext::new();
        file_ctx.disable_external_import_search();
        let outcome =
            check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
        assert!(!outcome.is_rejected(), "the authored island must register: {outcome:?}");

        let eq_ok_w =
            island_definition_carriers(&env, "eqOkW").expect("eqOkW has readable carriers");
        assert_eq!(eq_ok_w.params, vec![Carrier::BitVec(64), Carrier::BitVec(128)]);
        assert_eq!(eq_ok_w.ret, Carrier::Bool);

        let zero =
            island_definition_carriers(&env, "zeroI64").expect("zeroI64 has readable carriers");
        assert_eq!(zero.params, Vec::new());
        assert_eq!(zero.ret, Carrier::BitVec(64));

        let checked =
            island_definition_carriers(&env, "checkedAdd64").expect("checkedAdd64 is readable");
        assert_eq!(checked.params, vec![Carrier::BitVec(64), Carrier::BitVec(64)]);
        assert_eq!(checked.ret, Carrier::Option(Box::new(Carrier::BitVec(64))));

        // Trust (nat-lift §3.1): `Int` IS a clause carrier now — it is the
        // codomain of the lift table's signed and `Int`-targeted rows, so an
        // island definition declared over it has to be nameable from a clause
        // or the lane is unusable. This assertion previously read
        // "an `Int` codomain is unreadable"; the change is deliberate and its
        // reason is that `Carrier::Int`, like `Carrier::Nat`, has exactly ONE
        // Rust-side preimage, which is the property the read-back requires.
        let to_int = island_definition_carriers(&env, "toInt64")
            .expect("an `Int` codomain is readable for the lift lane");
        assert_eq!(to_int.params, vec![Carrier::BitVec(64)]);
        assert_eq!(to_int.ret, Carrier::Int);
        assert_eq!(Carrier::Int.unique_domain(), Some(trust_spec_elab::Domain::Int));
        assert!(island_definition_carriers(&env, "no_such_def").is_none());

        // `BitVec N` has THREE domain preimages and must never be inverted;
        // the carriers with exactly one may be.
        assert!(Carrier::BitVec(64).unique_domain().is_none(), "BitVec must not invert");
        assert_eq!(Carrier::Bool.unique_domain(), Some(trust_spec_elab::Domain::Bool));
        assert_eq!(
            Carrier::UInt(MachineUIntWidth::U64).unique_domain(),
            Some(trust_spec_elab::Domain::Machine(MachineUIntWidth::U64))
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
        use trust_spec_elab::{Admission, FacetStatus, FacetTable, FnFacets};
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into("def ident_isl (x : UInt64) : UInt64 := x", &mut env);
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
        shadowed.admit("ident_isl", Admission::reflected("trust_import_ident_isl", 1));
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

    /// TG16 (after TG11): the ODT namespaces the compiler mints into — readable aliases
    /// `trust_type_*` and nominal identities `TrustOdt.*` — are reserved against island
    /// declarations in BOTH lanes: the sequential `check` (deferred islands) and the batch
    /// `check_all` (the resolver's and the MIR pre-walk's). Each refusal names the namespace.
    /// The accepted spellings are the controls that keep the reservation on the leading
    /// namespace, not on a substring.
    #[test]
    fn an_island_may_not_declare_into_the_odt_namespaces() {
        let alias = "`trust_type_*`";
        let nominal = "`TrustOdt.*`";
        let refused: &[(&str, &str)] = &[
            ("def trust_type_Foo : Nat := 0", alias),
            ("theorem trust_type_x : True := True.intro", alias),
            ("def trust_type_test__Phase.toTag (n : Nat) : UInt8 := 0", alias),
            (
                "namespace trust_type_test__Phase\ntheorem helper : True := True.intro\nend trust_type_test__Phase",
                alias,
            ),
            ("inductive trust_type_I where\n  | a\n  | b", alias),
            ("private def trust_type_p : Nat := 0", alias),
            ("def TrustOdt.x : Nat := 0", nominal),
            ("namespace TrustOdt\ndef y : Nat := 0\nend TrustOdt", nominal),
            ("structure TrustOdt.Bar where\n  x : UInt8", nominal),
            ("structure TrustOdt where\n  x : UInt8", nominal),
        ];
        for (source, namespace) in refused {
            let sequential = CleanIslandSession::new().check(source);
            assert!(
                sequential.is_rejected()
                    && sequential.errors.iter().any(|e| e.message.contains(namespace)),
                "sequential lane must refuse {source:?} naming {namespace}, got {:?}",
                sequential.errors
            );
            let batch = CleanIslandSession::new().check_all(&[source]);
            assert!(
                batch.is_rejected()
                    && batch.outcomes[0].errors.iter().any(|e| e.message.contains(namespace)),
                "batch lane must refuse {source:?} naming {namespace}, got {:?}",
                batch.outcomes
            );
        }

        let accepted = [
            "def my_trust_type_helper : Nat := 0",
            "def TrustOdtish : Nat := 0",
            "def Foo.TrustOdt.x : Nat := 0",
            "def Foo.trust_type_x : Nat := 0",
        ];
        for source in accepted {
            let sequential = CleanIslandSession::new().check(source);
            assert!(!sequential.is_rejected(), "{source:?}: {:?}", sequential.errors);
            let batch = CleanIslandSession::new().check_all(&[source]);
            assert!(!batch.is_rejected(), "{source:?}: {:?}", batch.outcomes);
        }
    }

    /// TG16: a `mutual` block is refused in both lanes when its members land in `TrustOdt.*`
    /// through the enclosing namespace, naming the namespace; the same block in an ordinary
    /// namespace is the control. A member whose OWN name is dotted (`inductive TrustOdt.Od`
    /// inside `mutual`) does not elaborate in Clean today (`UnknownIdent`), so it is refused
    /// before any name is registered; that spelling is pinned as refused, for whatever reason,
    /// so the day Clean accepts it the reservation has to be what refuses it.
    #[test]
    fn a_reserved_member_of_a_mutual_block_is_refused_in_both_lanes() {
        let block = "mutual\n\
                     inductive Ev where\n  | zero\n  | succ (o : Od)\n\
                     inductive Od where\n  | succ (e : Ev)\n\
                     end";
        let source = format!("namespace TrustOdt\n{block}\nend TrustOdt");
        let sequential = CleanIslandSession::new().check(&source);
        assert!(
            sequential.is_rejected()
                && sequential.errors.iter().any(|e| e.message.contains("`TrustOdt.*`")),
            "{:?}",
            sequential.errors
        );
        let batch = CleanIslandSession::new().check_all(&[source.as_str()]);
        assert!(
            batch.is_rejected()
                && batch.outcomes[0].errors.iter().any(|e| e.message.contains("`TrustOdt.*`")),
            "{:?}",
            batch.outcomes
        );
        // Control: the same block in an ordinary namespace is admitted by both lanes.
        let control = format!("namespace OddNat\n{block}\nend OddNat");
        let sequential = CleanIslandSession::new().check(&control);
        assert!(!sequential.is_rejected(), "{:?}", sequential.errors);
        let batch = CleanIslandSession::new().check_all(&[control.as_str()]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);

        let dotted = "mutual\n\
                      inductive Ev where\n  | zero\n\
                      inductive TrustOdt.Od where\n  | one\n\
                      end";
        assert!(CleanIslandSession::new().check(dotted).is_rejected());
        assert!(CleanIslandSession::new().check_all(&[dotted]).is_rejected());
    }

    /// **I2's control, from the decision of record
    /// (`docs/design/2026-08-04-two-language-compiler-architecture.md` §7):**
    /// *"a `Reflected` symbol cited where `KernelChecked` is required must be
    /// REFUSED, not silently accepted."*
    ///
    /// `admit_certified_island_definition` is the compiler's one
    /// "`KernelChecked` required" site: it exists to authenticate a Clean
    /// declaration the CIC kernel re-checked, and on success it stamps four
    /// `FacetStatus::Certified { evidence: "clean-island-kernel-definition" }`
    /// facets. A `trust_import_*` constant is NOT that: it is a **reflected**
    /// Rust carrier, minted by `admit_function_into`, whose correspondence to
    /// the Rust `fn` is asserted by the compiler and taken on trust by the
    /// kernel (TCB). The kernel checked that the body inhabits the type; it
    /// never checked that the constant denotes `crate::min2`.
    ///
    /// So handing that constant to the island admitter must fail closed. If it
    /// succeeds, the environment carries a row claiming
    /// `clean-island-kernel-definition` evidence for a reflection — a claim the
    /// kernel never made.
    #[test]
    fn a_reflected_rust_carrier_is_refused_where_a_kernel_checked_declaration_is_required() {
        use trust_spec_elab::FacetTable;

        // 1. Reflect a Rust program function into the Clean environment. This
        //    is the I2 direction: `crate::min2` enters as `trust_import_crate__min2`.
        let min2 = min2_verifiable_function();
        let mut table =
            FacetTable::from_structural_facets([("crate::min2", true, true, true, true)]);
        let mut env = Environment::with_prelude();
        let (path, admission) = admit_function_into(&mut env, &min2, &table)
            .expect("the reflected carrier must mint — this test is about what happens next");
        assert_eq!(admission.kernel_const, "trust_import_crate__min2");
        assert!(
            admission.status().is_reflected(),
            "a Rust program function enters the Clean environment as Reflected, got {:?}",
            admission.status()
        );
        assert!(
            admission.require_kernel_check().is_err(),
            "and it never satisfies a kernel-check requirement"
        );
        table.admit(path, admission);

        // 2. Cite it where a kernel-CHECKED declaration is required. The real
        //    compiler path (`trust_verify.rs:19970-20013`) reaches this with the
        //    very same table the mints were recorded in, so the refusal has the
        //    provenance available to it and does not have to guess.
        let refusal =
            admit_certified_island_definition(&env, "trust_import_crate__min2", &mut table);

        let error = refusal.expect_err(
            "a Reflected Rust carrier must be REFUSED where a KernelChecked Clean \
             declaration is required — the reflection is TCB and the kernel never \
             re-checked that `trust_import_crate__min2` denotes `crate::min2`",
        );
        assert!(
            error.contains("reflected"),
            "the refusal must NAME the status that caused it, got: {error}"
        );
        // v7/D3: a refusal carries the fix, with options.
        assert!(
            error.contains("options:"),
            "the refusal must name the fix with options (v7/D3), got: {error}"
        );

        // And it must not have stamped island evidence on the way out.
        assert!(
            table.admitted("trust_import_crate__min2").is_none(),
            "the refused carrier must not acquire an island admission"
        );

        // 3. The STRUCTURAL backstop: a caller that hands us a table which
        //    never saw the mint still cannot get the carrier through, because
        //    `trust_import_*` is a reserved namespace no island may declare
        //    into. Fail-closed — an admitter that cannot tell Reflected from
        //    KernelChecked refuses rather than assumes.
        let mut blind = FacetTable::new();
        let blind_error =
            admit_certified_island_definition(&env, "trust_import_crate__min2", &mut blind)
                .expect_err("the reserved-namespace backstop must refuse too");
        assert_eq!(blind_error, error, "both routes must give the same refusal");

        // 4. The POSITIVE direction, so this test cannot pass by the admitter
        //    having simply stopped working: a genuine Clean island `def` is
        //    still admitted, and its admission SATISFIES the kernel-check
        //    requirement the reflected carrier failed.
        let mut island_env = Environment::with_prelude();
        let outcome =
            check_clean_island_into("def isl_min (x : UInt64) : UInt64 := x", &mut island_env);
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let mut island_facets = FacetTable::new();
        let admitted =
            admit_certified_island_definition(&island_env, "isl_min", &mut island_facets)
                .expect("a kernel-re-checked island definition must still be admitted");
        let verdict = admitted
            .require_kernel_check()
            .expect("an island definition the kernel re-checked carries KernelChecked");
        assert!(
            verdict.closure().is_audited_empty(),
            "a Certified grade means an AUDITED-empty closure, not an unrecorded one"
        );
        assert!(admitted.status().is_certified());
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
        let prim =
            |callee: &str, args: Vec<Operand>, dest: Place, target: BlockId| Terminator::Call {
                func: callee.into(),
                callee_identity: None,
                callee_key: None,
                args,
                dest,
                target: Some(target),
                span: SourceSpan::default(),
                atomic: None,
                unwind: trust_types::UnwindEdge::Unreachable,
                is_foreign: false,
                is_unsafe_sig: false,
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
                            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
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
                            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_mul",
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
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
            // clean acdc2459: declaration names are structural, not strings.
            name: clean_parser::SurfaceName::component("synthetic_hole", false),
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

    /// A served module is audited once, rooted at all its theorems
    /// (`StrictAudit::OncePerModule`). That audit accepts a clean module, and
    /// refuses what the per-proof audit refuses: a theorem that leans on an
    /// assumption, directly or through another theorem, named with the
    /// assumption.
    #[test]
    fn the_module_rooted_audit_refuses_what_the_per_proof_audit_refuses() {
        let mut session = CleanIslandSession::new();
        let clean = check_clean_island_audited(
            "",
            "theorem base : 0 = 0 := rfl\n\
             theorem uses_base : 0 = 0 := base\n\
             theorem alone : 1 = 1 := rfl\n",
            session.keyed.env_mut_for_tests(),
            &mut {
                let mut file_ctx = FileContext::new();
                file_ctx.disable_external_import_search();
                file_ctx
            },
            StrictAudit::OncePerModule,
        );
        assert!(!clean.is_rejected(), "{:?}", clean.errors);
        assert_eq!(clean.registered.len(), 3, "{:?}", clean.registered);

        // The axiom is refused where it is declared, and its dependents stay
        // registered: the audit is what refuses them.
        let mut session = CleanIslandSession::new();
        let outcome = session.check(
            "axiom assumed_true : True\n\
             theorem inherited : True := assumed_true\n\
             theorem deeper : True := inherited\n\
             theorem honest : 0 = 0 := rfl\n",
        );
        assert!(outcome.is_rejected());
        let name = clean_kernel::Name::from_string;
        let env = session.keyed.env_mut_for_tests();
        assert_eq!(module_audit_error(env, &[name("honest")]), None);
        for theorems in [
            vec![name("inherited")],
            vec![name("honest"), name("deeper")],
            vec![name("deeper"), name("inherited"), name("honest")],
        ] {
            let message = module_audit_error(env, &theorems).expect("an inherited assumption");
            assert!(
                message.contains("strict certification audit") && message.contains("assumed_true"),
                "{theorems:?}: {message}"
            );
        }
    }

    #[test]
    fn one_session_preserves_namespace_and_open_state_across_islands() {
        let mut session = CleanIslandSession::new();
        assert!(!session.keyed.file_ctx_for_tests().external_import_search_enabled());
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
        // A hand-built island-shaped admission for an elaboration test: it is
        // not minted by the kernel-recheck path, so it is `reflected` — the
        // weaker, fail-closed status. The elaborator does not require a kernel
        // re-check, so this still exercises what it is meant to exercise.
        facets.admit("identity", Admission::reflected("identity", 1));
        let params: &[(&str, &str)] = &[("x", "u64")];

        // DISCHARGE: the u64 reflexivity theorem proves `ensures x >= x`.
        assert!(
            matches!(
                kernel_discharge_ensures_citation(
                    &env,
                    "u64_ge_refl",
                    "x >= x",
                    params,
                    "identity",
                    &facets
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
                    &env,
                    "u64_ge_refl",
                    "x > x",
                    params,
                    "identity",
                    &facets
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
                    &env,
                    "u64_ge_refl",
                    "x >= x",
                    params,
                    "not_admitted",
                    &facets
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
                    &env,
                    "u64_ge_refl",
                    "result >= x",
                    params,
                    "not_admitted",
                    &facets
                ),
                CitationVerdict::ClauseOutsideFragment { .. }
            ),
            "un-admitted self-fn must fail closed when the clause mentions result"
        );

        // FALSIFICATION — unknown theorem: fail closed.
        assert!(
            matches!(
                kernel_discharge_ensures_citation(
                    &env,
                    "no_such_thm",
                    "x >= x",
                    params,
                    "identity",
                    &facets
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

        // Clean refuses `unsafe theorem` at elaboration, as both pinned Leans do
        // ("'unsafe' theorems are not allowed"; Clean R133), so the refused island
        // leaves no constant behind to cite.
        let unsafe_theorem =
            check_clean_island_into("unsafe theorem unsafe_zero : 0 = 0 := rfl\n", &mut env);
        assert!(unsafe_theorem.is_rejected(), "strict islands must reject unsafe theorems");
        assert!(matches!(
            kernel_unify_citation(&env, "unsafe_zero", "0 == 0"),
            CitationVerdict::TheoremNotFound
        ));
        // A theorem that reaches the environment marked unsafe by another route
        // (an import, a replayed environment) is refused by its marker: the same
        // safe theorem certifies until it is marked, and is refused after.
        let safe_theorem =
            check_clean_island_into("theorem unsafe_zero : 0 = 0 := rfl\n", &mut env);
        assert!(!safe_theorem.is_rejected(), "safe theorem: {:?}", safe_theorem.errors);
        assert!(matches!(
            kernel_unify_citation(&env, "unsafe_zero", "0 == 0"),
            CitationVerdict::KernelStatementMatchCertified
        ));
        env.mark_unsafe(clean_kernel::Name::from_string("unsafe_zero"));
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
        let typed = session.check_citation_typed_with_facets_in(
            "le_refl_u64",
            "x <= y",
            &[("x", "u64"), ("y", "u64")],
            &facets,
            &trust_spec_elab::ProofClauseInputs::strict(),
        );
        assert!(
            !matches!(typed, CitationVerdict::ClauseOutsideFragment { .. }),
            "typed clause must elaborate (not out-of-fragment): {typed:?}"
        );
    }

    /// `usize` in the E9 discharge lanes. The compiler resolves a `usize`
    /// binder through `trust_spec_elab::discharge_binding_ty_for_target` before
    /// either lane sees it; this pins what that resolution buys and — the part
    /// that matters — what it must never buy.
    ///
    /// `keep_us` stands in for the E6 import of `fn keep(n: usize) -> usize
    /// { n }` on a 64-bit target: the verifier's extraction lane spells `usize`
    /// `Int { width: 64, signed: false }`, so that import is minted at `UInt64`
    /// exactly as a `u64` function's is.
    #[test]
    fn usize_discharge_binders_take_the_import_carrier_at_the_target_width() {
        use trust_spec_elab::{FacetTable, TargetPointerWidth, discharge_binding_ty_for_target};
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def keep_us (n : UInt64) : UInt64 := n\n\n\
             def id_us (n : UInt64) : UInt64 := n\n\n\
             def bump_us (n : UInt64) : UInt64 := UInt64.add n 1\n\n\
             theorem u64_ge_refl : forall (x : UInt64), \
                 Nat.le (UInt64.toNat x) (UInt64.toNat x) := \
                 fun x => Nat.le.refl (UInt64.toNat x)\n\n\
             theorem u32_ge_refl : forall (x : UInt32), \
                 Nat.le (UInt32.toNat x) (UInt32.toNat x) := \
                 fun x => Nat.le.refl (UInt32.toNat x)\n\n\
             theorem i64_le_refl : forall (x : BitVec 64), \
                 Nat.le (Nat.xor (BitVec.toNat x) 9223372036854775808) \
                        (Nat.xor (BitVec.toNat x) 9223372036854775808) := \
                 fun x => Nat.le.refl (Nat.xor (BitVec.toNat x) 9223372036854775808)",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);

        // `isize` takes the SIGNED fixed-width spelling: `BitVec 64` under the
        // sign-flip order key on a 64-bit target, exactly as `i64` does.
        let i64w = discharge_binding_ty_for_target("isize", TargetPointerWidth::W64);
        let i32w = discharge_binding_ty_for_target("isize", TargetPointerWidth::W32);
        let signed64 = kernel_unify_citation_typed(&env, "i64_le_refl", "n <= n", &[("n", i64w)]);
        assert!(
            matches!(signed64, CitationVerdict::KernelStatementMatchCertified),
            "a signed 64-bit theorem must close a 64-bit isize clause; got {signed64:?}"
        );
        let signed32 = kernel_unify_citation_typed(&env, "i64_le_refl", "n <= n", &[("n", i32w)]);
        assert!(
            !matches!(signed32, CitationVerdict::KernelStatementMatchCertified),
            "a 64-bit signed theorem must NOT close an isize clause on a 32-bit target; \
             got {signed32:?}"
        );
        // SIGNEDNESS CONTROL: `usize` and `isize` share a width and nothing
        // else. The signed theorem must not close the unsigned clause, nor the
        // unsigned theorem the signed one.
        let w64_for_sign = discharge_binding_ty_for_target("usize", TargetPointerWidth::W64);
        for (theorem, binder, what) in [
            ("i64_le_refl", w64_for_sign, "a signed theorem on a usize clause"),
            ("u64_ge_refl", i64w, "an unsigned theorem on an isize clause"),
        ] {
            let verdict = kernel_unify_citation_typed(&env, theorem, "n <= n", &[("n", binder)]);
            assert!(
                !matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
                "{what} must not discharge; got {verdict:?}"
            );
        }

        let w64 = discharge_binding_ty_for_target("usize", TargetPointerWidth::W64);
        let w32 = discharge_binding_ty_for_target("usize", TargetPointerWidth::W32);
        let w16 = discharge_binding_ty_for_target("usize", TargetPointerWidth::W16);

        // CITED, result-free: a theorem over `UInt64` closes a `usize` clause
        // on a 64-bit target.
        let cited64 = kernel_unify_citation_typed(&env, "u64_ge_refl", "n >= n", &[("n", w64)]);
        assert!(
            matches!(cited64, CitationVerdict::KernelStatementMatchCertified),
            "a UInt64 theorem must close a 64-bit usize clause; got {cited64:?}"
        );
        // WIDTH NEGATIVE CONTROL: the SAME theorem must not close the SAME
        // clause on a narrower target. The goal quantifies over that target's
        // carrier, which the 64-bit proof term does not inhabit.
        for (narrow, bits) in [(w32, 32), (w16, 16)] {
            let verdict =
                kernel_unify_citation_typed(&env, "u64_ge_refl", "n >= n", &[("n", narrow)]);
            assert!(
                matches!(verdict, CitationVerdict::StatementOrCertificationRejected { .. }),
                "a 64-bit theorem must NOT close a usize clause on a {bits}-bit target; \
                 got {verdict:?}"
            );
        }
        // …and that refusal is the WIDTH, not a broken narrow lane: the theorem
        // stated at the target's own width closes it.
        let cited32 = kernel_unify_citation_typed(&env, "u32_ge_refl", "n >= n", &[("n", w32)]);
        assert!(
            matches!(cited32, CitationVerdict::KernelStatementMatchCertified),
            "a UInt32 theorem must close a 32-bit usize clause; got {cited32:?}"
        );
        // CLOSE NEGATIVE TWIN: the unresolved name is still outside the
        // fragment — the binding gate was not relaxed.
        let bare = kernel_unify_citation_typed(&env, "u64_ge_refl", "n >= n", &[("n", "usize")]);
        assert!(
            matches!(bare, CitationVerdict::ClauseOutsideFragment { .. }),
            "bare `usize` must never guess a target; got {bare:?}"
        );

        let mut facets = FacetTable::new();
        for name in ["keep_us", "id_us", "bump_us"] {
            admit_certified_island_definition(&env, name, &mut facets)
                .expect("strict kernel definition must be admitted");
        }

        // UNCITED DEFEQ, result-mentioning — the form contracts on `usize`
        // functions actually take (`ensures result == spec(n)`).
        let defeq64 = kernel_prove_ensures_by_defeq(
            &env,
            "result == id_us(n)",
            &[("n", w64)],
            "keep_us",
            &facets,
        );
        assert!(
            matches!(defeq64, CitationVerdict::KernelStatementMatchCertified),
            "a 64-bit usize clause must discharge against the UInt64 import; got {defeq64:?}"
        );
        // MUTATION CONTROL: a specification that is not the body must refuse,
        // or the discharge above proves nothing.
        let mutated = kernel_prove_ensures_by_defeq(
            &env,
            "result == bump_us(n)",
            &[("n", w64)],
            "keep_us",
            &facets,
        );
        assert!(
            matches!(mutated, CitationVerdict::StatementOrCertificationRejected { .. }),
            "a differing specification must NOT discharge; got {mutated:?}"
        );
        // CARRIER CONTROLS. `usize64` (`BitVec 64`) is the spelling the
        // statement-only lanes use; against a `UInt64` import it is a carrier
        // mismatch, which is why the discharge lanes do not use it. A 32-bit
        // binder against the 64-bit import is the width control on this lane.
        // Both must fail closed — never coerce.
        for (binder, what) in [("usize64", "a BitVec 64 binder"), (w32, "a 32-bit usize binder")] {
            let verdict = kernel_prove_ensures_by_defeq(
                &env,
                "result == id_us(n)",
                &[("n", binder)],
                "keep_us",
                &facets,
            );
            assert!(
                !matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
                "{what} must not discharge against a UInt64 import; got {verdict:?}"
            );
        }

        // CITED, result-mentioning: same agreement, through the citation route.
        let cited_result = kernel_discharge_ensures_citation(
            &env,
            "u64_ge_refl",
            "result >= n",
            &[("n", w64)],
            "keep_us",
            &facets,
        );
        assert!(
            matches!(cited_result, CitationVerdict::KernelStatementMatchCertified),
            "a cited result-mentioning usize clause must discharge at 64 bits; \
             got {cited_result:?}"
        );
        let cited_result32 = kernel_discharge_ensures_citation(
            &env,
            "u64_ge_refl",
            "result >= n",
            &[("n", w32)],
            "keep_us",
            &facets,
        );
        assert!(
            !matches!(cited_result32, CitationVerdict::KernelStatementMatchCertified),
            "the 64-bit citation must NOT discharge on a 32-bit target; got {cited_result32:?}"
        );
    }

    /// The body-independent citation audit the `-Ztrust-verify=off` sweep runs
    /// for a `result`-mentioning cited `ensures` (whose goal that lane cannot
    /// build). It enforces the theorem's existence, kind and provenance, and —
    /// by construction — asserts nothing about the clause.
    #[test]
    fn cited_theorem_audit_is_body_independent_and_never_a_statement_match() {
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def proof_shaped_def : 0 = 0 := rfl\n\n\
             theorem u64_ge_refl : forall (x : UInt64), \
                 Nat.le (UInt64.toNat x) (UInt64.toNat x) := \
                 fun x => Nat.le.refl (UInt64.toNat x)",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);

        // THE REPRO this audit exists for: with no imported body, `result` is
        // a ∀-binder, so the honest theorem does not match `result >= x`…
        let unverified_reading = kernel_unify_citation_typed(
            &env,
            "u64_ge_refl",
            "result >= x",
            &[("result", "u64"), ("x", "u64")],
        );
        assert!(
            matches!(unverified_reading, CitationVerdict::StatementOrCertificationRejected { .. }),
            "the ∀-result reading is not what the theorem proves; got {unverified_reading:?}"
        );
        // …while the theorem ITSELF is sound and clean, which is all the audit
        // reports.
        assert!(
            kernel_audit_cited_theorem(&env, "u64_ge_refl").is_ok(),
            "a registered, axiom-free theorem must pass the body-independent audit"
        );

        // CLOSE NEGATIVE TWINS: everything that needs no body still refuses.
        assert!(matches!(
            kernel_audit_cited_theorem(&env, "no_such_thm"),
            Err(CitationVerdict::TheoremNotFound)
        ));
        assert!(matches!(
            kernel_audit_cited_theorem(&env, "proof_shaped_def"),
            Err(CitationVerdict::DeclarationNotTheorem { .. })
        ));

        // ADVERSARIAL: an assumption-backed theorem. A strict island rejects it
        // at registration; whether or not the rejected declaration is retained
        // for diagnostics, the audit must never vouch for it.
        let mut tainted_env = Environment::with_prelude();
        let assumed = check_clean_island_into(
            "axiom assumed_true : True\n\
             theorem inherited : True := assumed_true\n",
            &mut tainted_env,
        );
        assert!(assumed.is_rejected(), "strict islands must reject an axiom-backed theorem");
        let inherited = kernel_audit_cited_theorem(&tainted_env, "inherited");
        assert!(
            inherited.is_err(),
            "an axiom-backed theorem must not pass the audit; got {inherited:?}"
        );
        assert!(
            kernel_audit_cited_theorem(&tainted_env, "assumed_true").is_err(),
            "an axiom is not a citable theorem"
        );

        // A tainted SESSION refuses before consulting its environment.
        let mut session = CleanIslandSession::new();
        assert!(!session.check("theorem reused : 0 = 0 := rfl\n").is_rejected());
        assert!(session.audit_cited_theorem("reused").is_ok());
        assert!(session.check("theorem reused : 0 = 0 := rfl\n").is_rejected());
        assert!(session.is_tainted());
        assert!(matches!(
            session.audit_cited_theorem("reused"),
            Err(CitationVerdict::SessionTainted)
        ));
    }

    /// The §5.7 discipline for the SIGNED-CONSTANT lane: each minted literal
    /// is DELTA-DEFEQ to the island's authored `BitVec` spelling of that same
    /// value — through the real island elaborator — and the wrong-VALUE and
    /// wrong-WIDTH forgeries are CAUGHT, not silently green.
    ///
    /// The boundary rows are the ones with content. `0` must take
    /// `Domain::zero`'s `Nat.zero` spelling; a negative must take the
    /// TWO'S-COMPLEMENT pattern, so `-1` is `2^64 - 1` and NOT `1`; and
    /// `iN::MIN` is the extreme where a magnitude carried as `-value` would
    /// have overflowed.
    #[test]
    fn signed_constant_mint_is_defeq_to_the_island_model_and_forgeries_are_caught() {
        use trust_spec_elab::{Domain, MachineSIntWidth};
        let mut env = Environment::with_prelude();
        let mut file_ctx = FileContext::new();
        file_ctx.disable_external_import_search();
        let outcome =
            check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
        assert!(!outcome.is_rejected(), "the authored island must register: {outcome:?}");

        // POSITIVE: mint ≡ the island's authored literal, per value and width.
        let rows: [(&str, i128, MachineSIntWidth, &str); 9] = [
            ("zero64_mint", 0, MachineSIntWidth::I64, "zeroI64"),
            ("one64_mint", 1, MachineSIntWidth::I64, "oneI64"),
            ("negone64_mint", -1, MachineSIntWidth::I64, "negOneI64"),
            ("min64_mint", i128::from(i64::MIN), MachineSIntWidth::I64, "minI64Bits"),
            ("max64_mint", i128::from(i64::MAX), MachineSIntWidth::I64, "maxI64Bits"),
            ("zero128_mint", 0, MachineSIntWidth::I128, "zeroI128"),
            ("one128_mint", 1, MachineSIntWidth::I128, "oneI128"),
            ("min128_mint", i128::MIN, MachineSIntWidth::I128, "minI128Bits"),
            ("max128_mint", i128::MAX, MachineSIntWidth::I128, "maxI128Bits"),
        ];
        for (mint_name, value, width, _) in rows {
            let adm =
                trust_spec_elab::admit_signed_constant_function(&mut env, mint_name, value, width)
                    .unwrap_or_else(|e| panic!("{mint_name} must admit into the island env: {e}"));
            assert_eq!(adm.arity, 0);
            assert_eq!(adm.return_domain().cloned(), Some(Domain::Signed(width)));
            assert_eq!(adm.param_names, None);
        }

        let tc = clean_kernel::TypeChecker::new(&env);
        let konst =
            |n: &str| clean_kernel::Expr::const_(clean_kernel::Name::from_string(n), vec![]);
        for (mint_name, value, _, island_name) in rows {
            assert!(
                tc.is_def_eq(&konst(mint_name), &konst(island_name)),
                "the mint of {value} must be delta-defeq to the island's {island_name}"
            );
        }

        // NEG (a): a wrong VALUE is caught — including the one that matters,
        // `-1` read as its MAGNITUDE rather than its two's-complement pattern.
        for (mint_name, forgery, why) in [
            ("one64_mint", "twoI64", "an off-by-one value"),
            ("negone64_mint", "oneI64", "a negative read as its magnitude"),
            ("min64_mint", "maxI64Bits", "MIN read as MAX"),
            ("zero64_mint", "oneI64", "zero read as one"),
        ] {
            assert!(
                !tc.is_def_eq(&konst(mint_name), &konst(forgery)),
                "{why} must NOT close against the signed-constant mint"
            );
        }
        // NEG (b): a wrong WIDTH is caught by TYPING — which is where a
        // `BitVec` constant's carrier actually lives.
        //
        // MEASURED 2026-08-26, and worth recording because it is not what a
        // reader would guess: `is_def_eq` ALONE is width-BLIND on closed
        // `BitVec.ofNat` literals. The kernel's `reduce_bitvec_of_nat` turns
        // `BitVec.ofNat W n` into the payload literal, so `BitVec.ofNat 32 1`
        // and `BitVec.ofNat 64 1` share a normal form and the equality
        // judgment answers `true` for both. That is NOT a hole in this lane:
        // `add_decl` FULL-TYPE-CHECKS every mint against its declared carrier
        // before the `Admission` exists, and the citation lane type-checks the
        // `Eq.refl` it constructs, so a width the mint did not declare can
        // never be reached. But it does mean the width pin must be asserted
        // with the TYPE CHECKER rather than the equality judgment — asserting
        // it with `is_def_eq` would have been a test that passes for the wrong
        // reason, or (as here) fails for the right one.
        let bv_ty = |bits: u64| {
            clean_kernel::Expr::app(
                clean_kernel::Expr::const_(clean_kernel::Name::from_string("BitVec"), vec![]),
                clean_kernel::Expr::nat_lit(bits),
            )
        };
        for (mint_name, good, bad) in
            [("one64_mint", 64u64, 32u64), ("one128_mint", 128, 64), ("min64_mint", 64, 128)]
        {
            tc.check_type(&konst(mint_name), &bv_ty(good))
                .unwrap_or_else(|e| panic!("{mint_name} must inhabit BitVec {good}: {e:?}"));
            assert!(
                tc.check_type(&konst(mint_name), &bv_ty(bad)).is_err(),
                "{mint_name} must NOT inhabit BitVec {bad} — the carrier is part of \
                 the constant's identity"
            );
        }
        // …and symmetrically, the wrong-width island twin does not inhabit the
        // mint's carrier.
        assert!(
            tc.check_type(&konst("oneI32"), &bv_ty(64)).is_err(),
            "a `BitVec 32` island twin must not inhabit the mint's `BitVec 64`"
        );

        drop(tc);

        // A literal that does not fit the requested carrier fails the MINT
        // closed, BEFORE the kernel — mirroring rustc's own out-of-range
        // rejection, so `ofNat`'s wrap-around can never be picked up silently.
        for (value, width) in [
            (128i128, MachineSIntWidth::I8),
            (-129, MachineSIntWidth::I8),
            (i128::from(i32::MAX) + 1, MachineSIntWidth::I32),
            (i128::from(i32::MIN) - 1, MachineSIntWidth::I32),
            (i128::from(i64::MAX) + 1, MachineSIntWidth::I64),
            (i128::from(i64::MIN) - 1, MachineSIntWidth::I64),
        ] {
            assert!(
                trust_spec_elab::admit_signed_constant_function(&mut env, "parked", value, width)
                    .is_err(),
                "{value} must fail closed at {width:?}"
            );
        }
    }

    /// The §5.7 discipline for the WIDENING-CAST comparison lane: the mint's
    /// seeded sign-extension model is DELTA-DEFEQ to the client island's
    /// authored `eqOkW` — through the real island elaborator — and each
    /// forgery is CAUGHT.
    ///
    /// The forgeries are compared on OPAQUE arguments, never literals: at a
    /// closed literal both models evaluate away and a ZERO-extending twin
    /// would agree with the mint on every NON-NEGATIVE value, so the exact
    /// wrong-accept bug it must detect would go unseen. On opaque arguments
    /// both sides are stuck and structurally different, which is the
    /// comparison the citation lane actually performs.
    #[test]
    fn widened_eq_mint_is_defeq_to_the_island_model_and_forgeries_are_caught() {
        use trust_spec_elab::{Domain, MachineSIntWidth};
        let mut env = Environment::with_prelude();
        let mut file_ctx = FileContext::new();
        file_ctx.disable_external_import_search();
        let outcome =
            check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
        assert!(!outcome.is_rejected(), "the authored island must register: {outcome:?}");

        let i64d = Domain::Signed(MachineSIntWidth::I64);
        let i128d = Domain::Signed(MachineSIntWidth::I128);
        let adm = trust_spec_elab::admit_widened_eq_function(
            &mut env,
            "eq_ok_mint",
            &[i64d.clone(), i128d.clone()],
            MachineSIntWidth::I64,
            MachineSIntWidth::I128,
            0,
            1,
            true,
        )
        .expect("the widened-equality mint must admit into the island env");
        assert_eq!(adm.arity, 2);
        assert_eq!(
            adm.return_domain().cloned(),
            Some(Domain::Bool),
            "the decision's codomain is `Bool`"
        );

        let tc = clean_kernel::TypeChecker::new(&env);
        let app2 = |f: &str, a: clean_kernel::Expr, b: clean_kernel::Expr| {
            clean_kernel::Expr::apps(
                clean_kernel::Expr::const_(clean_kernel::Name::from_string(f), vec![]),
                [a, b],
            )
        };
        // OPAQUE arguments: no closed-pipeline evaluation, so the comparison
        // is the delta-unfolding one the citation lane performs.
        let m = clean_kernel::Expr::fvar(clean_kernel::FVarId::new(0));
        let t = clean_kernel::Expr::fvar(clean_kernel::FVarId::new(1));

        // POSITIVE: mint ≡ the island's authored sign-extending model.
        assert!(
            tc.is_def_eq(
                &app2("eq_ok_mint", m.clone(), t.clone()),
                &app2("eqOkW", m.clone(), t.clone())
            ),
            "the widened-equality mint must be delta-defeq to the island's authored eqOkW"
        );

        // NEG (a): ZERO extension — `BitVec.ofNat 128 (BitVec.toNat v)`. This
        // is THE faithfulness hazard of this lane: it agrees with the mint on
        // every non-negative `machine` and disagrees on every negative one, so
        // a wrong model here would let the contract claim a false equality for
        // exactly the wrapped values the guard exists to reject.
        // NEG (b): the comparison pulled down to the NARROW width, i.e. the
        // wide side truncated instead of the narrow side widened — the
        // opposite direction, and information-losing.
        for (forgery, why) in [
            ("eqOkZeroExt", "a ZERO-extending model"),
            ("eqOkTrunc", "a truncating (narrow-width) comparison"),
        ] {
            assert!(
                !tc.is_def_eq(
                    &app2("eq_ok_mint", m.clone(), t.clone()),
                    &app2(forgery, m.clone(), t.clone())
                ),
                "{why} must NOT close against the widened-equality mint"
            );
        }

        drop(tc);

        // A wrong-width or wrong-DIRECTION request fails the MINT closed.
        for (from, to) in [
            (MachineSIntWidth::I128, MachineSIntWidth::I64),
            (MachineSIntWidth::I32, MachineSIntWidth::I64),
            (MachineSIntWidth::I64, MachineSIntWidth::I64),
        ] {
            assert!(
                trust_spec_elab::admit_widened_eq_function(
                    &mut env,
                    "parked",
                    &[i64d.clone(), i128d.clone()],
                    from,
                    to,
                    0,
                    1,
                    true,
                )
                .is_err(),
                "({from:?} -> {to:?}) must park"
            );
        }
        // Parameters off their required carriers, the same index on both
        // sides, and an out-of-range index all fail closed.
        for (domains, narrow, wide, why) in [
            (
                vec![i128d.clone(), i128d.clone()],
                0usize,
                1usize,
                "a narrow parameter at the wide carrier",
            ),
            (vec![i64d.clone(), i64d.clone()], 0, 1, "a wide parameter at the narrow carrier"),
            (vec![i64d.clone(), i128d.clone()], 0, 0, "the same parameter on both sides"),
            (vec![i64d.clone(), i128d.clone()], 0, 2, "an out-of-range index"),
            (vec![Domain::Bool, i128d.clone()], 0, 1, "a `bool` narrow parameter"),
        ] {
            assert!(
                trust_spec_elab::admit_widened_eq_function(
                    &mut env,
                    "parked",
                    &domains,
                    MachineSIntWidth::I64,
                    MachineSIntWidth::I128,
                    narrow,
                    wide,
                    true,
                )
                .is_err(),
                "{why} must fail closed"
            );
        }
    }

    /// The wiring arm for the SIGNED-CONSTANT lane: each of the four real
    /// client bodies this increment unblocks
    /// (`<i64 as CoeffDomain>::zero`/`::one`, `<i128 as Exact>::zero`/`::one`)
    /// mints through [`admit_function_into`] with the signed return domain
    /// recorded; uncertified facets mint nothing, and an UNSIGNED return at
    /// the identical body shape mints nothing.
    #[test]
    fn admit_function_into_mints_signed_constants() {
        use trust_types::{
            BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
            Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let constant_fn = |path: &str, value: i128, ty: Ty| VerifiableFunction {
            name: "k".into(),
            def_path: path.into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: ty.clone(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(value))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: ty,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let i64_ty = Ty::Int { width: 64, signed: true };
        let i128_ty = Ty::Int { width: 128, signed: true };

        // `Environment::with_prelude()` is expensive, so the whole matrix runs
        // in THREE environments rather than one per row: all the positives
        // mint into one env (each `def_path` mangles to its own kernel
        // constant, so they cannot collide), and the two negative classes
        // share one each.
        let mut env = Environment::with_prelude();
        let mut env_uncertified = Environment::with_prelude();
        let mut env_refused = Environment::with_prelude();

        // The four blocked client functions, by the shape their bodies have.
        for (path, value, ty, width) in [
            (
                "veripb_core_proved::<i64 as CoeffDomain>::zero",
                0i128,
                &i64_ty,
                trust_spec_elab::MachineSIntWidth::I64,
            ),
            (
                "veripb_core_proved::<i64 as CoeffDomain>::one",
                1,
                &i64_ty,
                trust_spec_elab::MachineSIntWidth::I64,
            ),
            (
                "veripb_core_proved::<i128 as Exact>::zero",
                0,
                &i128_ty,
                trust_spec_elab::MachineSIntWidth::I128,
            ),
            (
                "veripb_core_proved::<i128 as Exact>::one",
                1,
                &i128_ty,
                trust_spec_elab::MachineSIntWidth::I128,
            ),
        ] {
            let func = constant_fn(path, value, ty.clone());
            let certified = trust_spec_elab::FacetTable::from_structural_facets([(
                path, true, true, true, true,
            )]);
            let (got_path, admission) = admit_function_into(&mut env, &func, &certified)
                .unwrap_or_else(|| panic!("{path} must mint once recognized"));
            assert_eq!(got_path, path);
            assert_eq!(admission.arity, 0);
            assert_eq!(
                admission.return_domain().cloned(),
                Some(trust_spec_elab::Domain::Signed(width)),
                "{path} must record its signed carrier"
            );

            // Uncertified facets: nothing mints even for the recognized body.
            let uncertified = trust_spec_elab::FacetTable::from_structural_facets([(
                path, true, true, false, true,
            )]);
            assert!(
                admit_function_into(&mut env_uncertified, &func, &uncertified).is_none(),
                "uncertified facets must not mint {path}"
            );
        }

        // A NEGATIVE literal mints too — the case whose kernel spelling is the
        // two's-complement pattern rather than the magnitude.
        let neg = constant_fn("crate::neg", -1, i64_ty.clone());
        let certified = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::neg",
            true,
            true,
            true,
            true,
        )]);
        assert!(
            admit_function_into(&mut env, &neg, &certified).is_some(),
            "a negative literal mints"
        );

        // An UNSIGNED return at the identical body shape mints NOTHING: a
        // `ConstValue::Int` at a `uN` carrier has no signed reading, and
        // taking one would give `-1` the value `u64::MAX`.
        let unsigned = constant_fn("crate::u", -1, Ty::Int { width: 64, signed: false });
        let certified_u = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::u", true, true, true, true,
        )]);
        assert!(
            admit_function_into(&mut env_refused, &unsigned, &certified_u).is_none(),
            "a signed literal at an unsigned return must never mint"
        );
    }

    /// TG15 open item 5: the `ConstantInt` routing is ARITY-PRESERVING, as
    /// [`constant_uint_routing_preserves_arity`] pins `ConstantUint`'s.
    ///
    /// `fn neg1(flag: bool) -> i64 { -1 }` reports the same `ConstantInt` a
    /// nullary `fn neg1() -> i64 { -1 }` does, and used to mint the nullary
    /// `BitVec 64` constant, so every clause naming `neg1(flag)` was refused
    /// for arity. Pinned at the routing itself:
    ///
    ///  1. the unary body mints at arity 1 with each parameter at its OWN
    ///     carrier (`Bool → BitVec 64`, which `ConstantUint`'s single-domain
    ///     route refuses), and its image at an opaque `flag` is `-1`, not `1`;
    ///  2. `ensures result == neg1_isl(flag)` discharges end to end by kernel
    ///     defeq, and the wrong-value twin does not;
    ///  3. the carrier-faithfulness gate's frozen lane does not take the new
    ///     route, measured in a FRESH environment (so a duplicate-declaration
    ///     refusal cannot answer for the guard) beside an `All`-lane control.
    ///
    /// The nullary path is [`admit_function_into_mints_signed_constants`]'s.
    #[test]
    fn signed_constant_routing_preserves_arity() {
        use trust_spec_elab::{Domain, FacetTable, MachineSIntWidth};
        use trust_types::{
            BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
            Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let i64_ty = Ty::Int { width: 64, signed: true };
        let neg1 = VerifiableFunction {
            name: "neg1".into(),
            def_path: "crate::neg1".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: i64_ty.clone(), name: None },
                    LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(-1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: i64_ty,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        // Under the def-path AND the bare name, as the compiler dual-keys them
        // (the ensures self-call resolves the bare name).
        let table = FacetTable::from_structural_facets([
            ("crate::neg1", true, true, true, true),
            ("neg1", true, true, true, true),
        ]);
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def neg1_isl (flag : Bool) : BitVec 64 := BitVec.ofNat 64 18446744073709551615\n\n\
             def one_isl (flag : Bool) : BitVec 64 := BitVec.ofNat 64 1",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);

        // (1) Arity 1, per-parameter carriers, the right value.
        let (path, admission) = admit_function_into(&mut env, &neg1, &table).expect(
            "a signed constant behind a parameter must mint through the arity-preserving route",
        );
        assert_eq!(path, "crate::neg1");
        assert_eq!(admission.arity, 1, "the routing must preserve the arity; 0 is the erased mint");
        assert_eq!(
            admission.return_domain().cloned(),
            Some(Domain::Signed(MachineSIntWidth::I64)),
            "the signed carrier must be recorded"
        );
        let tc = clean_kernel::TypeChecker::new(&env);
        let konst =
            |n: &str| clean_kernel::Expr::const_(clean_kernel::Name::from_string(n), vec![]);
        let image = konst(admission.kernel_const.as_str());
        let bool_to_bv64 = clean_kernel::Expr::arrow(
            konst("Bool"),
            clean_kernel::Expr::app(konst("BitVec"), clean_kernel::Expr::nat_lit(64)),
        );
        tc.check_type(&image, &bool_to_bv64)
            .unwrap_or_else(|e| panic!("the image must be `Bool → BitVec 64`: {e:?}"));
        let flag = clean_kernel::Expr::fvar(clean_kernel::FVarId::new(0));
        let at = |f: clean_kernel::Expr| clean_kernel::Expr::app(f, flag.clone());
        assert!(
            tc.is_def_eq(&at(image.clone()), &at(konst("neg1_isl"))),
            "the image applied to any `flag` must be the island's `-1`"
        );
        assert!(!tc.is_def_eq(&at(image), &at(konst("one_isl"))), "`-1` must not be `1`");
        drop(tc);

        // (2) End to end: the clause that was refused for arity discharges by
        // kernel defeq, and the wrong-value twin does not.
        let params: &[(&str, &str)] = &[("flag", "bool")];
        let mut discharge = table.clone();
        discharge.admit("neg1", admission);
        for island in ["neg1_isl", "one_isl"] {
            admit_certified_island_definition(&env, island, &mut discharge)
                .unwrap_or_else(|e| panic!("island `{island}` must admit for citation: {e}"));
        }
        let verdict = kernel_prove_ensures_by_defeq(
            &env,
            "result == neg1_isl(flag)",
            params,
            "neg1",
            &discharge,
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "a clause naming `neg1(flag)` must discharge by kernel defeq; got {verdict:?}"
        );
        let wrong = kernel_prove_ensures_by_defeq(
            &env,
            "result == one_isl(flag)",
            params,
            "neg1",
            &discharge,
        );
        assert!(
            !matches!(wrong, CitationVerdict::KernelStatementMatchCertified),
            "`-1 == 1` must not certify; got {wrong:?}"
        );

        // (3) The frozen lane refuses the route; the `All` lane, in the same
        // fresh environment, is the control that the guard is what refused.
        let mut fresh = Environment::with_prelude();
        assert!(
            admit_function_into_lanes(&mut fresh, &neg1, &table, AdmissionLanes::FrozenShapes)
                .is_none(),
            "the carrier-faithfulness gate's frozen lane must not take the tree producer"
        );
        assert!(
            admit_function_into_lanes(&mut fresh, &neg1, &table, AdmissionLanes::All).is_some(),
            "control: the same body mints on the `All` lane"
        );
    }

    /// The wiring arm for the WIDENING-CAST comparison lane: the measured
    /// `eq_ok` body with certified facets mints through [`admit_function_into`]
    /// with the `Bool` return domain recorded; uncertified facets mint
    /// nothing, and the two faithfulness hazards — a TRUNCATING cast and an
    /// UNSIGNED (zero-extending) source — mint nothing even with every facet
    /// certified.
    #[test]
    fn admit_function_into_mints_widened_eq() {
        use trust_types::{
            BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let i64_ty = Ty::Int { width: 64, signed: true };
        let i128_ty = Ty::Int { width: 128, signed: true };
        let stmt = |place: Place, rvalue: Rvalue| Statement::Assign {
            place,
            rvalue,
            span: SourceSpan::default(),
        };
        // The measured `-O` body of `veripb_core_proved::guard::eq_ok`.
        let eq_ok = |narrow: Ty, wide: Ty, cast_to: Ty| VerifiableFunction {
            name: "eq_ok".into(),
            def_path: "crate::eq_ok".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: None },
                    LocalDecl { index: 1, ty: narrow, name: Some("machine".into()) },
                    LocalDecl { index: 2, ty: wide, name: Some("truth".into()) },
                    LocalDecl { index: 3, ty: cast_to.clone(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::StorageLive(3),
                        stmt(
                            Place::local(3),
                            Rvalue::Cast(Operand::Copy(Place::local(1)), cast_to),
                        ),
                        stmt(
                            Place::local(0),
                            Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Move(Place::local(3)),
                                Operand::Copy(Place::local(2)),
                            ),
                        ),
                        Statement::StorageDead(3),
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Bool,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let certified = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::eq_ok",
            true,
            true,
            true,
            true,
        )]);
        let good = eq_ok(i64_ty.clone(), i128_ty.clone(), i128_ty.clone());
        let mut env = Environment::with_prelude();
        let (path, admission) = admit_function_into(&mut env, &good, &certified)
            .expect("certified + recognized must mint");
        assert_eq!(path, "crate::eq_ok");
        assert_eq!(admission.arity, 2);
        assert_eq!(
            admission.return_domain().cloned(),
            Some(trust_spec_elab::Domain::Bool),
            "a decision function records the `Bool` codomain"
        );
        assert_eq!(admission.param_names, None);

        let uncertified = trust_spec_elab::FacetTable::from_structural_facets([(
            "crate::eq_ok",
            true,
            false,
            true,
            true,
        )]);
        let mut env2 = Environment::with_prelude();
        assert!(
            admit_function_into(&mut env2, &good, &uncertified).is_none(),
            "uncertified facets must not mint"
        );

        // The two faithfulness hazards, each at the SAME MIR spelling as the
        // admitted body. If either ever mints, a cast has been modeled as
        // something it is not.
        let mut env3 = Environment::with_prelude();
        for (narrow, wide, cast_to, why) in [
            (i128_ty.clone(), i64_ty.clone(), i64_ty.clone(), "a TRUNCATING cast"),
            (
                Ty::Int { width: 64, signed: false },
                i128_ty.clone(),
                i128_ty.clone(),
                "a ZERO-extending unsigned source",
            ),
            (
                i64_ty.clone(),
                Ty::Int { width: 128, signed: false },
                Ty::Int { width: 128, signed: false },
                "an unsigned target carrier",
            ),
        ] {
            assert!(
                admit_function_into(&mut env3, &eq_ok(narrow, wide, cast_to), &certified).is_none(),
                "{why} must never mint through the sign-extension lane"
            );
        }
    }

    /// Trust (#63, R3) — THE RED CASE, written before the green one per the
    /// plan's own acceptance: a generated carrier whose body does NOT match its
    /// Clean definition must be REJECTED, with the kernel as the only judge.
    ///
    /// The carrier here is an E6-recognizable IDENTITY body, so admission
    /// succeeds and the refusal comes from the DEFEQ GATE itself — the test
    /// exercises the gate, not the admission filter in front of it.
    #[test]
    fn r3_diverging_generated_carrier_is_rejected() {
        use trust_types::{
            BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let identity_carrier = |def_path: &str| VerifiableFunction {
            name: "gen".into(),
            def_path: def_path.into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Int { width: 64, signed: false }, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 64, signed: false },
                        name: Some("x0".into()),
                    },
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
                arg_count: 1,
                return_ty: Ty::Int { width: 64, signed: false },
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def r3_same (x : UInt64) : UInt64 := x

\
             def r3_diff (x : UInt64) : UInt64 := UInt64.add x 1",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);

        let mut facets = trust_spec_elab::FacetTable::from_structural_facets([
            ("gen::same_carrier", true, true, true, true),
            ("gen::diff_carrier", true, true, true, true),
        ]);

        // RED: the identity carrier does NOT compute `x + 1`. The kernel must
        // refuse, and the refusal must be the defeq gate (not admission).
        let carrier = identity_carrier("gen::diff_carrier");
        let verdict =
            check_generated_carrier_faithfulness(&mut env, "r3_diff", &carrier, &mut facets);
        match &verdict {
            Err(CarrierFaithfulnessRejection::NotDefinitionallyEqual { detail, .. }) => {
                // The refusal must come from the KERNEL's defeq judgment, not
                // from a failed elaboration in front of it — the gate's first
                // draft passed this test for the wrong reason (an unrecorded
                // admission failed elaboration, which also maps to this
                // variant), and the GREEN control below is what exposed it.
                assert!(
                    detail.contains("kernel refused definitional equality"),
                    "the RED case must be the kernel's judgment, not a gate in \
                     front of it: {detail}"
                );
            }
            other => panic!(
                "a diverging generated carrier MUST be rejected by the kernel's \
                 defeq judgment — a green here is a miscompiler: {other:?}"
            ),
        }

        // GREEN CONTROL: the SAME carrier against the definition it faithfully
        // implements passes — so the red above is discrimination, not a gate
        // that refuses everything.
        let carrier = identity_carrier("gen::same_carrier");
        let verdict =
            check_generated_carrier_faithfulness(&mut env, "r3_same", &carrier, &mut facets);
        assert!(verdict.is_ok(), "the faithful carrier must pass: {verdict:?}");
    }

    /// Trust (#63, R3) — fail-closed controls on the gates IN FRONT of the
    /// kernel: a carrier outside the E6 fragment is REFUSED (R2 may only emit
    /// what this gate can check), and an arity mismatch never reaches defeq.
    #[test]
    fn r3_gate_refuses_what_it_cannot_check() {
        use trust_types::{
            BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into("def r3_tgt (x : UInt64) : UInt64 := x", &mut env);
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let mut facets = trust_spec_elab::FacetTable::from_structural_facets([(
            "gen::opaque",
            true,
            true,
            true,
            true,
        )]);
        // A body the E6 recognizer cannot elaborate (raw pointer cast shape):
        // the gate must refuse rather than skip the check.
        let opaque = VerifiableFunction {
            name: "gen".into(),
            def_path: "gen::opaque".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Int { width: 64, signed: false }, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 64, signed: false },
                        name: Some("x0".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Cast(
                            Operand::Copy(Place::local(1)),
                            Ty::Int { width: 32, signed: false },
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Int { width: 64, signed: false },
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let verdict =
            check_generated_carrier_faithfulness(&mut env, "r3_tgt", &opaque, &mut facets);
        assert!(
            matches!(
                verdict,
                Err(CarrierFaithfulnessRejection::CarrierOutsideCheckedFragment { .. })
                    | Err(CarrierFaithfulnessRejection::NotDefinitionallyEqual { .. })
            ),
            "an uncheckable carrier must be refused, never skipped: {verdict:?}"
        );
    }

    // ---------------------------------------------------------------------
    // Joint Rust+Lean cited lane (2026-09-15): a Rust contract clause discharged
    // by CITING a Lean theorem ABOUT the Lean (island) function the body calls.
    // ---------------------------------------------------------------------

    /// The v2 reproduction island: `pb_max` and a tactic theorem about it, plus
    /// a second definition for the wrong-callee control.
    const PB_ISLAND: &str = "\
def pb_max (lhs : UInt64) (rhs : UInt64) : UInt64 := if rhs < lhs then lhs else rhs
theorem pb_max_ge_left (lhs rhs : UInt64) : lhs <= pb_max lhs rhs := by
  unfold pb_max
  split <;> omega
def pb_min (lhs : UInt64) (rhs : UInt64) : UInt64 := if rhs < lhs then rhs else lhs
";

    /// The extracted shape of `fn <name>(<params>) -> <ret> { <callee>(<args>) }`:
    /// one call block writing `_0`, one return block — what the compiler's
    /// extractor produces for a body that forwards its parameters (measured
    /// `shape=bb0[|call] bb1[|ret]` under `TRUST_E6_DEBUG`).
    fn forwarding_verifiable_function(
        name: &str,
        callee: &str,
        params: &[(&str, trust_types::Ty)],
        arg_params: &[usize],
        ret: trust_types::Ty,
    ) -> trust_types::VerifiableFunction {
        use trust_types::{
            BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, VerifiableBody,
            VerifiableFunction,
        };
        let mut locals = vec![LocalDecl { index: 0, ty: ret.clone(), name: None }];
        for (i, (pname, ty)) in params.iter().enumerate() {
            locals.push(LocalDecl {
                index: i + 1,
                ty: ty.clone(),
                name: Some((*pname).to_string()),
            });
        }
        VerifiableFunction {
            name: name.into(),
            def_path: format!("crate::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: callee.to_string(),
                            args: arg_params
                                .iter()
                                .map(|&p| Operand::Copy(Place::local(p + 1)))
                                .collect(),
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                            is_foreign: false,
                            is_unsafe_sig: false,
                            unwind: Default::default(),
                            callee_identity: None,
                            callee_key: None,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: params.len(),
                return_ty: ret,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    /// The compiler's structural facet record for a body whose only callee it
    /// never walked: every facet `Undetermined`.
    fn undetermined_record() -> trust_spec_elab::FnFacets {
        trust_spec_elab::FnFacets::from_structural_certificates(
            false,
            false,
            false,
            false,
            "structural",
        )
    }

    /// v2 END TO END through the kernel: `ensures result >= lhs by
    /// pb_max_ge_left` on `fn pb_max_r(lhs, rhs) { pb_max(lhs, rhs) }`.
    ///
    /// `result` denotes the body's admitted defining equation `pb_max lhs rhs`
    /// (the forwarding mint), the goal is `∀ lhs rhs, lhs ≤ pb_max lhs rhs` at
    /// the UInt64 carrier, and the cited theorem's proof term is re-checked by
    /// the kernel against exactly that goal — `KernelStatementMatchCertified`.
    /// Every control below is a statement the theorem does NOT prove and must
    /// be refused by the same audit.
    #[test]
    fn cited_theorem_about_an_island_callee_discharges_a_forwarding_body() {
        use trust_spec_elab::{Admission, FacetTable};
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(PB_ISLAND, &mut env);
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let u64 = trust_types::Ty::u64();
        let params2 = [("lhs", u64.clone()), ("rhs", u64.clone())];
        let pb_max_r = forwarding_verifiable_function(
            "pb_max_r",
            "crate::pb_max",
            &params2,
            &[0, 1],
            u64.clone(),
        );
        let mut table = FacetTable::new();
        table.insert("crate::pb_max_r", undetermined_record());

        // CONTROL — with no identity row for the callee nothing moves: no facet
        // is certified and the body is not admitted. Its bare name IS `pb_max`,
        // and that is not evidence.
        assert!(certify_clean_origin_forwarding_facets(&[pb_max_r.clone()], &mut table).is_empty());
        assert!(!table.get("crate::pb_max_r").expect("record").admissible());
        assert!(admit_function_into(&mut env.clone(), &pb_max_r, &table).is_none());

        // The compiler's identity row: `crate::pb_max` IS the kernel constant `pb_max`.
        admit_clean_origin_callee_identity(
            &env,
            &clean_kernel::Name::from_string("pb_max"),
            "crate::pb_max",
            &[],
            &mut table,
        )
        .expect("identity row");
        let identity = table.admitted("crate::pb_max").expect("row is admissible");
        assert_eq!(identity.kernel_const, "pb_max");
        identity.require_kernel_check().expect("row is KernelChecked");

        // Facets close over the callee; the body becomes admissible.
        assert_eq!(
            certify_clean_origin_forwarding_facets(&[pb_max_r.clone()], &mut table),
            vec!["crate::pb_max_r".to_string()]
        );
        assert!(table.get("crate::pb_max_r").expect("record").admissible());
        // Idempotent: a second pass certifies nothing new and changes nothing.
        assert!(certify_clean_origin_forwarding_facets(&[pb_max_r.clone()], &mut table).is_empty());

        // The self-admission: `trust_import_…pb_max_r := fun p0 p1 => pb_max p0 p1`.
        let (path, admission) =
            admit_function_into(&mut env, &pb_max_r, &table).expect("forwarding mint");
        assert_eq!(path, "crate::pb_max_r");
        assert_eq!(admission.arity, 2);
        assert!(admission.kernel_const.starts_with(KERNEL_IMPORT_PREFIX));
        table.admit(path, admission);

        let params: &[(&str, &str)] = &[("lhs", "u64"), ("rhs", "u64")];
        let verdict = kernel_discharge_ensures_citation(
            &env,
            "pb_max_ge_left",
            "result >= lhs",
            params,
            "crate::pb_max_r",
            &table,
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the cited theorem about the island callee must discharge: {verdict:?}"
        );
        // The same clause spelled from the other side.
        let flipped = kernel_discharge_ensures_citation(
            &env,
            "pb_max_ge_left",
            "lhs <= result",
            params,
            "crate::pb_max_r",
            &table,
        );
        assert!(matches!(flipped, CitationVerdict::KernelStatementMatchCertified), "{flipped:?}");

        // NEGATIVE 1 — a different inequality (about `rhs`) under the same
        // citation: the theorem does not prove `∀ lhs rhs, rhs ≤ pb_max lhs rhs`.
        let wrong_side = kernel_discharge_ensures_citation(
            &env,
            "pb_max_ge_left",
            "result >= rhs",
            params,
            "crate::pb_max_r",
            &table,
        );
        assert!(
            matches!(wrong_side, CitationVerdict::StatementOrCertificationRejected { .. }),
            "a theorem about `lhs` must not discharge a clause about `rhs`: {wrong_side:?}"
        );
        // NEGATIVE 2 — the strict direction.
        let strict = kernel_discharge_ensures_citation(
            &env,
            "pb_max_ge_left",
            "result > lhs",
            params,
            "crate::pb_max_r",
            &table,
        );
        assert!(
            matches!(strict, CitationVerdict::StatementOrCertificationRejected { .. }),
            "a `<=` theorem must not discharge a strict clause: {strict:?}"
        );
        // NEGATIVE 3 — the inverted direction (`result <= lhs`), which is FALSE.
        let inverted = kernel_discharge_ensures_citation(
            &env,
            "pb_max_ge_left",
            "result <= lhs",
            params,
            "crate::pb_max_r",
            &table,
        );
        assert!(
            matches!(inverted, CitationVerdict::StatementOrCertificationRejected { .. }),
            "{inverted:?}"
        );

        // NEGATIVE 4 — a body forwarding to a DIFFERENT island definition
        // (`pb_min`) with the same clause and the same citation. The identity
        // row and the mint both succeed (the shape is honest); the AUDIT refuses,
        // because `result` now denotes `pb_min lhs rhs` and the theorem is about
        // `pb_max`.
        let pb_min_r = forwarding_verifiable_function(
            "pb_min_r",
            "crate::pb_min",
            &params2,
            &[0, 1],
            u64.clone(),
        );
        table.insert("crate::pb_min_r", undetermined_record());
        admit_clean_origin_callee_identity(
            &env,
            &clean_kernel::Name::from_string("pb_min"),
            "crate::pb_min",
            &[],
            &mut table,
        )
        .expect("pb_min identity row");
        assert_eq!(
            certify_clean_origin_forwarding_facets(&[pb_min_r.clone()], &mut table),
            vec!["crate::pb_min_r".to_string()]
        );
        let (path, admission) =
            admit_function_into(&mut env, &pb_min_r, &table).expect("pb_min_r mint");
        table.admit(path, admission);
        let other_callee = kernel_discharge_ensures_citation(
            &env,
            "pb_max_ge_left",
            "result >= lhs",
            params,
            "crate::pb_min_r",
            &table,
        );
        assert!(
            matches!(other_callee, CitationVerdict::StatementOrCertificationRejected { .. }),
            "a theorem about `pb_max` must not discharge a body that calls `pb_min`: {other_callee:?}"
        );

        // NEGATIVE 5 — ARGUMENT ORDER. `fn pb_max_s(lhs, rhs) { pb_max(rhs, lhs) }`
        // denotes `pb_max rhs lhs`, so the goal is `∀ lhs rhs, lhs ≤ pb_max rhs
        // lhs`. That proposition happens to be TRUE, and the cited theorem still
        // does not prove it — its statement is about `pb_max lhs rhs`, and the two
        // are not definitionally equal on neutral arguments. Refused: the binders
        // are instantiated from the call's actual argument order, never guessed.
        let pb_max_s = forwarding_verifiable_function(
            "pb_max_s",
            "crate::pb_max",
            &params2,
            &[1, 0],
            u64.clone(),
        );
        table.insert("crate::pb_max_s", undetermined_record());
        assert_eq!(
            certify_clean_origin_forwarding_facets(&[pb_max_s.clone()], &mut table),
            vec!["crate::pb_max_s".to_string()]
        );
        let (path, admission) =
            admit_function_into(&mut env, &pb_max_s, &table).expect("pb_max_s mint");
        table.admit(path, admission);
        let swapped = kernel_discharge_ensures_citation(
            &env,
            "pb_max_ge_left",
            "result >= lhs",
            params,
            "crate::pb_max_s",
            &table,
        );
        assert!(
            matches!(swapped, CitationVerdict::StatementOrCertificationRejected { .. }),
            "a theorem about `pb_max lhs rhs` must not discharge a body computing `pb_max rhs lhs`: {swapped:?}"
        );
        // ...while the SAME theorem discharges the clause that IS about the
        // swapped call's first argument (`result >= rhs` on `pb_max(rhs, lhs)`
        // is `∀ lhs rhs, rhs ≤ pb_max rhs lhs`) — the theorem's binders are
        // (lhs rhs) in the FUNCTION's parameter order, and the kernel
        // alpha-renames: `∀ a b, a ≤ pb_max a b` vs `∀ a b, b ≤ pb_max b a`
        // differ, so this must ALSO refuse. Pinned so the rule is explicit: a
        // cited theorem is stated over the function's parameters in declaration
        // order; nothing here reorders binders for the author.
        let swapped_rhs = kernel_discharge_ensures_citation(
            &env,
            "pb_max_ge_left",
            "result >= rhs",
            params,
            "crate::pb_max_s",
            &table,
        );
        assert!(
            matches!(swapped_rhs, CitationVerdict::StatementOrCertificationRejected { .. }),
            "{swapped_rhs:?}"
        );

        // NEGATIVE 6 — a CARRIER mismatch: `u32` parameters forwarded into the
        // UInt64 definition. The shape is pure (facets certify), but the mint
        // refuses at the declared-carrier check, so the body stays unadmitted
        // and `result` unbound.
        let u32 = trust_types::Ty::u32();
        let narrow = forwarding_verifiable_function(
            "pb_max_n",
            "crate::pb_max",
            &[("lhs", u32.clone()), ("rhs", u32.clone())],
            &[0, 1],
            u32,
        );
        table.insert("crate::pb_max_n", undetermined_record());
        certify_clean_origin_forwarding_facets(&[narrow.clone()], &mut table);
        assert!(admit_function_into(&mut env, &narrow, &table).is_none());

        // NEGATIVE 7 — a NAME-ONLY match: a callee whose last segment is
        // `pb_max` but whose def-path has no identity row. Nothing happens.
        let fake = forwarding_verifiable_function(
            "fake_r",
            "crate::other::pb_max",
            &params2,
            &[0, 1],
            u64.clone(),
        );
        table.insert("crate::fake_r", undetermined_record());
        assert!(certify_clean_origin_forwarding_facets(&[fake.clone()], &mut table).is_empty());
        assert!(admit_function_into(&mut env, &fake, &table).is_none());

        // NEGATIVE 8 — a REFLECTED Rust callee under the def-path is not an
        // island identity: the forwarding arm declines, and so does the facet
        // closure (a Rust→Rust forwarding body belongs to the structural lane).
        let mut rust_table = FacetTable::new();
        rust_table.insert("crate::fwd", undetermined_record());
        rust_table.insert(
            "crate::rust_id",
            trust_spec_elab::FnFacets::from_structural_certificates(
                true,
                true,
                true,
                true,
                "structural",
            ),
        );
        rust_table.admit("crate::rust_id", Admission::reflected("trust_import_crate__rust_id", 2));
        let fwd =
            forwarding_verifiable_function("fwd", "crate::rust_id", &params2, &[0, 1], u64.clone());
        assert!(certify_clean_origin_forwarding_facets(&[fwd.clone()], &mut rust_table).is_empty());
        assert!(!rust_table.get("crate::fwd").expect("record").admissible());
        assert!(admit_function_into(&mut env, &fwd, &rust_table).is_none());

        // NEGATIVE 9 — a REFUTED facet is never promoted, identity row or not.
        let mut refuted = undetermined_record();
        refuted.no_panic = trust_spec_elab::FacetStatus::Refuted { reason: "test".into() };
        table.insert("crate::pb_max_r", refuted);
        assert!(certify_clean_origin_forwarding_facets(&[pb_max_r.clone()], &mut table).is_empty());
        assert!(!table.get("crate::pb_max_r").expect("record").admissible());
    }

    /// The UNCITED defeq route over the same forwarding body: `ensures result ==
    /// pb_max(lhs, rhs)` closes by `Eq.refl` (the self constant unfolds to the
    /// island call), while a swapped or different-callee spelling does not.
    #[test]
    fn uncited_defeq_closes_a_forwarding_body_against_its_own_island_callee() {
        use trust_spec_elab::FacetTable;
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(PB_ISLAND, &mut env);
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let u64 = trust_types::Ty::u64();
        let params2 = [("lhs", u64.clone()), ("rhs", u64.clone())];
        let pb_max_r = forwarding_verifiable_function(
            "pb_max_r",
            "crate::pb_max",
            &params2,
            &[0, 1],
            u64.clone(),
        );
        let mut table = FacetTable::new();
        table.insert("crate::pb_max_r", undetermined_record());
        admit_clean_origin_callee_identity(
            &env,
            &clean_kernel::Name::from_string("pb_max"),
            "crate::pb_max",
            &[],
            &mut table,
        )
        .expect("identity row");
        certify_clean_origin_forwarding_facets(&[pb_max_r.clone()], &mut table);
        let (path, admission) = admit_function_into(&mut env, &pb_max_r, &table).expect("mint");
        table.admit(path, admission);
        // The clause names the island definitions by their Clean spelling, as
        // the uncited in-walk route admits them (clause-local table).
        let mut clause_table = table.clone();
        admit_certified_island_definition(&env, "pb_max", &mut clause_table).expect("pb_max");
        admit_certified_island_definition(&env, "pb_min", &mut clause_table).expect("pb_min");
        let params: &[(&str, &str)] = &[("lhs", "u64"), ("rhs", "u64")];
        let same = kernel_prove_ensures_by_defeq(
            &env,
            "result == pb_max(lhs, rhs)",
            params,
            "crate::pb_max_r",
            &clause_table,
        );
        assert!(matches!(same, CitationVerdict::KernelStatementMatchCertified), "{same:?}");
        let swapped = kernel_prove_ensures_by_defeq(
            &env,
            "result == pb_max(rhs, lhs)",
            params,
            "crate::pb_max_r",
            &clause_table,
        );
        assert!(
            matches!(swapped, CitationVerdict::StatementOrCertificationRejected { .. }),
            "{swapped:?}"
        );
        let other = kernel_prove_ensures_by_defeq(
            &env,
            "result == pb_min(lhs, rhs)",
            params,
            "crate::pb_max_r",
            &clause_table,
        );
        assert!(
            matches!(other, CitationVerdict::StatementOrCertificationRejected { .. }),
            "{other:?}"
        );
    }

    /// The identity row is keyed by the materialized item's def-path, mints
    /// the same audited `KernelChecked` admission the Clean-spelling admitter
    /// does, and refuses every collision and reserved key without touching the
    /// table.
    #[test]
    fn clean_origin_identity_row_is_keyed_by_def_path_and_refuses_collisions() {
        use trust_spec_elab::FacetTable;
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(PB_ISLAND, &mut env);
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let pb_max = clean_kernel::Name::from_string("pb_max");
        let mut table = FacetTable::new();
        let row =
            admit_clean_origin_callee_identity(&env, &pb_max, "crate::m::pb_max", &[], &mut table)
                .expect("row");
        // Same admission as the Clean-spelling admitter, under a different key.
        let mut spelled = FacetTable::new();
        let by_spelling =
            admit_certified_island_definition(&env, "pb_max", &mut spelled).expect("spelled");
        assert_eq!(row, by_spelling);
        assert!(table.admitted("crate::m::pb_max").is_some());
        assert!(
            table.admitted("pb_max").is_none(),
            "the def-path row does not key the bare spelling"
        );
        // Idempotent.
        assert_eq!(
            admit_clean_origin_callee_identity(&env, &pb_max, "crate::m::pb_max", &[], &mut table)
                .expect("again"),
            row
        );
        // Both keys may coexist in one table: the I2 status query answers
        // KernelChecked for the constant either way.
        admit_certified_island_definition(&env, "pb_max", &mut table)
            .expect("spelling beside def-path");
        // Collision with a Rust program-function record under the key: refused,
        // and the existing record is untouched.
        let mut busy = FacetTable::new();
        busy.insert("crate::pb_max", undetermined_record());
        assert!(
            admit_clean_origin_callee_identity(&env, &pb_max, "crate::pb_max", &[], &mut busy)
                .is_err()
        );
        assert!(busy.admitted("crate::pb_max").is_none());
        assert!(!busy.get("crate::pb_max").expect("record").admissible());
        // Reserved namespace and empty key.
        assert!(
            admit_clean_origin_callee_identity(
                &env,
                &pb_max,
                "trust_import_x",
                &[],
                &mut FacetTable::new()
            )
            .is_err()
        );
        assert!(
            admit_clean_origin_callee_identity(&env, &pb_max, "", &[], &mut FacetTable::new())
                .is_err()
        );
        // A theorem is not an unfoldable definition.
        assert!(
            admit_clean_origin_callee_identity(
                &env,
                &clean_kernel::Name::from_string("pb_max_ge_left"),
                "crate::pb_max_ge_left",
                &[],
                &mut FacetTable::new()
            )
            .is_err()
        );
        // An unregistered name.
        assert!(
            admit_clean_origin_callee_identity(
                &env,
                &clean_kernel::Name::from_string("nope"),
                "crate::nope",
                &[],
                &mut FacetTable::new()
            )
            .is_err()
        );
    }

    /// Trust (GREEN THAT LIES, `docs/KNOWN_HAZARDS.md` 2026-09-18): a
    /// Clean-origin row carries the stand-in qualification of the session that
    /// registered its declaration, the forwarding body inherits it, and the
    /// qualification can only ever GROW.
    ///
    /// The two halves of the hazard entry, as assertions: nothing about the
    /// VERDICT moves (the row is minted, admissible and `KernelChecked`
    /// exactly as with no substitution — a stand-in-served island stays
    /// admissible), and the row no longer reads as an unqualified green.
    #[test]
    fn a_clean_origin_row_carries_its_islands_standin_qualification() {
        use trust_spec_elab::FacetTable;
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(PB_ISLAND, &mut env);
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let pb_max = clean_kernel::Name::from_string("pb_max");
        let mathlib = CleanIslandStandinImport { start: 0, end: 14, module: "Mathlib".to_string() };
        let lean_meta =
            CleanIslandStandinImport { start: 15, end: 31, module: "Lean.Meta".to_string() };

        // CONTROL — with no substitution the row records no qualification.
        let mut plain = FacetTable::new();
        let plain_row =
            admit_clean_origin_callee_identity(&env, &pb_max, "crate::pb_max", &[], &mut plain)
                .expect("identity row");
        assert!(plain_row.standin_disclosures().is_empty());

        // The same declaration, in a session one of whose islands had `import
        // Mathlib` served by the built-in prelude stand-in: SAME verdict, plus
        // the qualification, in the one wording every seam reports it in.
        let mut table = FacetTable::new();
        let row = admit_clean_origin_callee_identity(
            &env,
            &pb_max,
            "crate::pb_max",
            std::slice::from_ref(&mathlib),
            &mut table,
        )
        .expect("a stand-in-served island is still admissible");
        row.require_kernel_check().expect("row is still KernelChecked");
        assert!(table.admitted("crate::pb_max").is_some(), "the row is still admissible");
        assert_eq!(row.standin_disclosures(), &[mathlib.disclosure()]);
        assert!(
            row.standin_disclosures()[0].contains("`import Mathlib` was served by Clean's"),
            "the row repeats the disclosure verbatim: {:?}",
            row.standin_disclosures()
        );
        // The qualification is the ONLY difference from the unqualified row.
        assert_eq!(plain_row, row.clone().with_standin_disclosures(Vec::<String>::new()));

        // A forwarding body inherits its callee's qualification: the row a
        // postcondition actually rests on is qualified too, one hop removed.
        let u64 = trust_types::Ty::u64();
        let params2 = [("lhs", u64.clone()), ("rhs", u64.clone())];
        let pb_max_r = forwarding_verifiable_function(
            "pb_max_r",
            "crate::pb_max",
            &params2,
            &[0, 1],
            u64.clone(),
        );
        table.insert("crate::pb_max_r", undetermined_record());
        assert_eq!(
            certify_clean_origin_forwarding_facets(&[pb_max_r.clone()], &mut table),
            vec!["crate::pb_max_r".to_string()],
            "a stand-in-served callee still closes the forwarding facets"
        );
        let (path, forwarded) =
            admit_function_into(&mut env, &pb_max_r, &table).expect("forwarding mint");
        assert_eq!(path, "crate::pb_max_r");
        assert_eq!(forwarded.standin_disclosures(), &[mathlib.disclosure()]);

        // MONOTONE. Re-recording the same identity with the SAME set is
        // idempotent; with a WIDER set it widens (the deferred island suffix is
        // checked after the first recording, and may be where the `import` was
        // spelled); with a NARROWER set it never loses what it already carries.
        assert_eq!(
            admit_clean_origin_callee_identity(
                &env,
                &pb_max,
                "crate::pb_max",
                std::slice::from_ref(&mathlib),
                &mut table
            )
            .expect("idempotent"),
            row
        );
        let widened = admit_clean_origin_callee_identity(
            &env,
            &pb_max,
            "crate::pb_max",
            &[mathlib.clone(), lean_meta.clone()],
            &mut table,
        )
        .expect("a wider disclosure set is not a collision");
        assert_eq!(widened.standin_disclosures(), &[mathlib.disclosure(), lean_meta.disclosure()]);
        assert_eq!(
            table.admitted("crate::pb_max").expect("row").standin_disclosures(),
            &[mathlib.disclosure(), lean_meta.disclosure()],
            "the widened qualification is what the table now hands a consumer"
        );
        let narrowed =
            admit_clean_origin_callee_identity(&env, &pb_max, "crate::pb_max", &[], &mut table)
                .expect("an empty set is not a collision either");
        assert_eq!(
            narrowed.standin_disclosures(),
            &[mathlib.disclosure(), lean_meta.disclosure()],
            "a disclosure is never dropped"
        );
    }

    /// The session, not the island, is what accumulates the substitution: one
    /// crate gets one `FileContext`, so an `import` any island had served by
    /// the stand-in qualifies every row the session's environment backs.
    #[test]
    fn a_session_accumulates_every_islands_standin_import() {
        let mut session = CleanIslandSession::new();
        assert!(session.standin_imports().is_empty());
        let first = session.check("def id1 (x : UInt64) : UInt64 := x\n");
        assert!(!first.is_rejected(), "island: {:?}", first.errors);
        assert!(
            session.standin_imports().is_empty(),
            "an island with no `import` substitutes nothing"
        );
        let second = session.check("import Lean\ndef id2 (x : UInt64) : UInt64 := x\n");
        assert!(!second.is_rejected(), "island: {:?}", second.errors);
        assert_eq!(second.standin_imports.len(), 1, "the outcome reports the substitution");
        let modules: Vec<&str> =
            session.standin_imports().iter().map(|i| i.module.as_str()).collect();
        assert_eq!(modules, vec!["Lean"]);
        // Repeating the same module adds no second entry, and the session keeps
        // what earlier islands established.
        let third = session.check("import Lean\ndef id3 (x : UInt64) : UInt64 := x\n");
        assert!(!third.is_rejected(), "island: {:?}", third.errors);
        assert_eq!(session.standin_imports().len(), 1);
        assert_eq!(session.standin_disclosures().len(), 1);
        assert!(session.standin_disclosures()[0].contains("import Lean"));
    }

    #[test]
    fn a_session_discloses_imports_inside_command_wrappers() {
        for source in [
            "set_option maxHeartbeats 400000 in import Lean\n",
            "open Nat in import Lean\n",
            "set_option maxHeartbeats 400000 in open Nat in import Lean\n",
        ] {
            let mut session = CleanIslandSession::new();
            let outcome = session.check(source);
            assert!(!outcome.is_rejected(), "{source}: {:?}", outcome.errors);
            assert_eq!(outcome.standin_imports.len(), 1, "{source}");
            let import = &outcome.standin_imports[0];
            assert_eq!(import.module, "Lean");
            assert_eq!(&source[import.start..import.end], "import", "{source}");
            assert_eq!(session.standin_imports().len(), 1);
        }

        let mut session = CleanIslandSession::new();
        let commented = session.check(
            "/- set_option maxHeartbeats 400000 in import Lean -/\n\
             -- open Nat in import Lean\ndef plain : Nat := 1\n",
        );
        assert!(!commented.is_rejected(), "{:?}", commented.errors);
        assert!(commented.standin_imports.is_empty());
        assert!(session.standin_imports().is_empty());
    }

    // -----------------------------------------------------------------------
    // A1 — `requires` as kernel hypotheses (design revision 2 `requires-hyps`).
    //
    // These run at crates level on purpose: the design's gate to start A1 is a
    // MEASUREMENT of whether the kernel converts the goal shape at all, and that
    // measurement must not cost a stage build.
    // -----------------------------------------------------------------------

    /// One candidate hypothesis over `u64` parameters `a`, `b` (and optionally
    /// `c`), with the query view that agrees with the signature.
    fn u64_hyp(index: usize, text: &str, names: &[&str]) -> trust_spec_elab::HypothesisInput {
        trust_spec_elab::HypothesisInput {
            contract_index: index,
            canonical_text: text.to_string(),
            authored_text: text.to_string(),
            query_bindings: names.iter().map(|n| ((*n).to_string(), "u64".to_string())).collect(),
        }
    }

    // -----------------------------------------------------------------------
    // OR-A1 (Inc 0 + Inc 1a): the lifted conclusion reaches the ladder, and a
    // conditional discharge reports WHICH link carried it.
    // Predicted from the code and the r2/r4/r5 goal measurements; MEASURED
    // passing 2026-09-28 on `ora1-land` (all four `or_a1_*`).
    // -----------------------------------------------------------------------

    /// `b <= a` over `u64`: the lifted reading and the Clean reading are the
    /// SAME term (measured goal strings, probe r4), so the one grade certifies
    /// `G1★` and the link is kernel-canonical.
    #[test]
    fn or_a1_an_unsigned_order_precondition_is_a_kernel_canonical_link() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let mut env = Environment::with_prelude();
        let ok = check_clean_island_into(
            "def pick (a : UInt64) (b : UInt64) : UInt64 := b\n\n\
             theorem pick_le : forall (a : UInt64) (b : UInt64), \
                 Nat.le (UInt64.toNat b) (UInt64.toNat a) -> \
                 Nat.le (UInt64.toNat b) (UInt64.toNat a) := fun a b h => h",
            &mut env,
        );
        assert!(!ok.is_rejected(), "setup island: {:?}", ok.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "pick", &mut facets).expect("pick must admit");
        let ladder = kernel_discharge_ensures_citation_under(
            &env,
            "pick_le",
            "result <= a",
            params,
            "pick",
            &facets,
            &[u64_hyp(0, "b <= a", &["a", "b"])],
        );
        assert_eq!(ladder.conditional_link(), Some(RequiresLink::KernelCanonical), "{ladder:#?}");
        assert_eq!(
            ladder.goal_under_requires_canonical, ladder.goal_under_requires,
            "for an unsigned order the two readings are one term"
        );
        // The conditional-only entry grades the same goals and agrees.
        let conditional = kernel_discharge_ensures_citation_conditional_in(
            &env,
            "pick_le",
            "result <= a",
            params,
            "pick",
            &facets,
            &[u64_hyp(0, "b <= a", &["a", "b"])],
            &trust_spec_elab::ProofClauseInputs::strict(),
        );
        assert_eq!(conditional.conditional_link(), Some(RequiresLink::KernelCanonical));
        assert!(conditional.goal_unconditional.is_none(), "the conditional entry builds no G0");
    }

    /// `a == b` over `u64` with a theorem that consumes `Eq a b` (probe r5's
    /// `eq_keep`, measured to discharge `G1`): the Clean reading is `Eq UInt64
    /// a b`, the lifted reading `Eq Nat (toNat a) (toNat b)`, and the theorem
    /// states only the former — so the discharge is ALLOW-LISTED, never
    /// kernel-canonical.
    #[test]
    fn or_a1_an_equality_stated_on_the_machine_carrier_is_allow_listed() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let mut env = Environment::with_prelude();
        let ok = check_clean_island_into(
            "def keepa (a : UInt64) (b : UInt64) : UInt64 := a\n\n\
             theorem eq_keep : forall (a : UInt64) (b : UInt64), Eq a b -> Eq a b := \
                 fun a b h => h",
            &mut env,
        );
        assert!(!ok.is_rejected(), "setup island: {:?}", ok.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "keepa", &mut facets).expect("keepa must admit");
        let ladder = kernel_discharge_ensures_citation_under(
            &env,
            "eq_keep",
            "result == b",
            params,
            "keepa",
            &facets,
            &[u64_hyp(0, "a == b", &["a", "b"])],
        );
        assert_eq!(ladder.conditional_link(), Some(RequiresLink::AllowListed), "{ladder:#?}");
        assert_ne!(
            ladder.goal_under_requires_canonical, ladder.goal_under_requires,
            "the two readings of `a == b` are different terms"
        );
        assert!(ladder.goal_under_requires_canonical.is_some(), "G1★ was built and graded");
    }

    /// Inc 0 (probe r1's shape): a LIFTED conclusion under a precondition. At
    /// the strict mode the ladder refuses the clause outright (what r1
    /// measured); with the proof-lift inputs the conclusion elaborates on every
    /// rung and the conditional one certifies.
    #[test]
    fn or_a1_a_lifted_conclusion_reaches_the_conditional_rung() {
        let params: &[(&str, &str)] = &[("k", "u64")];
        let mut env = Environment::with_prelude();
        let ok = check_clean_island_into(
            "def spec (n : Nat) : Nat := n\n\n\
             def keep (k : UInt64) : UInt64 := k\n\n\
             theorem keep_spec : forall (k : UInt64), \
                 Nat.lt 0 (UInt64.toNat k) -> \
                 Eq (UInt64.toNat k) (spec (UInt64.toNat k)) := \
                 fun k h => Eq.refl (UInt64.toNat k)",
            &mut env,
        );
        assert!(!ok.is_rejected(), "setup island: {:?}", ok.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "keep", &mut facets).expect("keep must admit");
        admit_certified_island_definition(&env, "spec", &mut facets).expect("spec must admit");
        let hyps = [u64_hyp(0, "k > 0", &["k"])];
        let strict = kernel_discharge_ensures_citation_under(
            &env,
            "keep_spec",
            "(result as nat) == spec(k as nat)",
            params,
            "keep",
            &facets,
            &hyps,
        );
        assert!(
            matches!(strict.verdict, CitationVerdict::ClauseOutsideFragment { .. }),
            "the strict ladder refuses a cast, as before: {strict:#?}"
        );
        let lifted = kernel_discharge_ensures_citation_under_in(
            &env,
            "keep_spec",
            "(result as nat) == spec(k as nat)",
            params,
            "keep",
            &facets,
            &hyps,
            &trust_spec_elab::ProofClauseInputs::proof_lift(Some("u64")),
        );
        assert_eq!(
            lifted.discharged_rung(),
            Some(CitationRung::UnderRequires),
            "the lifted conclusion must reach the conditional rung: {lifted:#?}"
        );
        assert!(lifted.conditional_link().is_some(), "{lifted:#?}");
    }

    /// A tainted session mints nothing on any rung, conditional-only included.
    #[test]
    fn or_a1_a_tainted_session_grades_no_conditional_rung() {
        let mut session = CleanIslandSession::new();
        // The measured tainting shape (`island_definition_value`'s taint test).
        let _ = session.check("theorem bad_pin : True := sorry");
        assert!(session.is_tainted(), "setup must taint");
        let ladder = session.check_ensures_discharge_conditional_in(
            "anything",
            "a <= a",
            &[("a", "u64")],
            "irrelevant_self",
            &trust_spec_elab::FacetTable::new(),
            &[u64_hyp(0, "a <= a", &["a"])],
            &trust_spec_elab::ProofClauseInputs::strict(),
        );
        assert!(matches!(ladder.verdict, CitationVerdict::SessionTainted));
        assert_eq!(ladder.conditional_link(), None);
    }

    /// A-PROBE (design revision 2 §2.9 "gate to start A1"; open risk 1).
    ///
    /// MEASURED, not predicted: does the kernel actually discharge the
    /// under-`requires` goal this lane builds? The fixture is 66b's shape
    /// reduced to a trivial body so the measurement is about the GOAL, not
    /// about how hard the theorem is: `pick a b = b`, `requires b <= a`,
    /// `ensures result <= a`, proof `fun a b h => h`.
    ///
    /// If this fails, A1's whole shape is wrong and nothing downstream of it is
    /// worth building.
    #[test]
    fn a_probe_the_kernel_discharges_the_under_requires_goal() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let mut env = Environment::with_prelude();
        let ok = check_clean_island_into(
            "def pick (a : UInt64) (b : UInt64) : UInt64 := b\n\n\
             theorem pick_le : forall (a : UInt64) (b : UInt64), \
                 Nat.le (UInt64.toNat b) (UInt64.toNat a) -> \
                 Nat.le (UInt64.toNat b) (UInt64.toNat a) := fun a b h => h",
            &mut env,
        );
        assert!(!ok.is_rejected(), "setup island: {:?}", ok.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "pick", &mut facets).expect("pick must admit");

        let hyps = [u64_hyp(0, "b <= a", &["a", "b"])];
        let ladder = kernel_discharge_ensures_citation_under(
            &env,
            "pick_le",
            "result <= a",
            params,
            "pick",
            &facets,
            &hyps,
        );
        assert_eq!(
            ladder.discharged_rung(),
            Some(CitationRung::UnderRequires),
            "the under-`requires` rung must discharge 66b's shape: {ladder:#?}"
        );

        // N-A1: the SAME theorem with no `requires` offered must NOT discharge —
        // otherwise the hypothesis was never load bearing.
        let bare = kernel_discharge_ensures_citation_under(
            &env,
            "pick_le",
            "result <= a",
            params,
            "pick",
            &facets,
            &[],
        );
        assert_eq!(
            bare.discharged_rung(),
            None,
            "with no `requires` there is no second rung to climb: {bare:#?}"
        );
        assert!(
            bare.g1_refusal.is_some(),
            "the absence of goal (2) must be explained, not silent: {bare:#?}"
        );
    }

    /// P-A1 — THE FLAGSHIP CASE, at full strength: probe 66b's program, with a
    /// real case-split proof rather than a trivial one.
    ///
    /// `rmax a b = if a < b then b else a`, `requires b <= a`, `ensures result
    /// <= a`. The theorem is true ONLY under the precondition (drop it and
    /// `rmax 0 5 = 5 > 0` refutes it), and its proof uses the hypothesis in
    /// exactly one branch of the `Decidable` case split. This is the program
    /// the owner's repos are full of and the one the unconditional goal cannot
    /// express.
    ///
    /// N-A2 (the close negative twin) is the same theorem against the SWAPPED
    /// precondition `a <= b`: it must stay refused, because a hypothesis the
    /// function does not declare is exactly the false accept this lane hunts.
    #[test]
    fn p_a1_a_case_split_proof_under_a_real_precondition_discharges() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let mut env = Environment::with_prelude();
        let ok = check_clean_island_into(
            "def rmax (a : UInt64) (b : UInt64) : UInt64 := if a < b then b else a\n\n\
             theorem rmax_le_left : forall (a : UInt64) (b : UInt64), \
                 Nat.le (UInt64.toNat b) (UInt64.toNat a) -> \
                 Nat.le (UInt64.toNat (if a < b then b else a)) (UInt64.toNat a) := \
                 fun a b h => Decidable.casesOn \
                     (motive := fun (d : Decidable (LT.lt a b)) => \
                         Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64) \
                             d (fun _ => a) (fun _ => b))) (UInt64.toNat a)) \
                     (instDecidableUInt64Lt a b) \
                     (fun _ => Nat.le.refl (UInt64.toNat a)) \
                     (fun _ => h)",
            &mut env,
        );
        assert!(!ok.is_rejected(), "setup island: {:?}", ok.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "rmax", &mut facets).expect("rmax must admit");

        let ladder = kernel_discharge_ensures_citation_under(
            &env,
            "rmax_le_left",
            "result <= a",
            params,
            "rmax",
            &facets,
            &[u64_hyp(0, "b <= a", &["a", "b"])],
        );
        assert_eq!(
            ladder.discharged_rung(),
            Some(CitationRung::UnderRequires),
            "the declared precondition must discharge the case-split proof: {ladder:#?}"
        );

        // N-A2: the SWAPPED precondition. The theorem needs `b <= a`; a function
        // that declares `a <= b` does not enforce it, and handing the theorem a
        // hypothesis the function never charges callers is the false accept.
        let swapped = kernel_discharge_ensures_citation_under(
            &env,
            "rmax_le_left",
            "result <= a",
            params,
            "rmax",
            &facets,
            &[u64_hyp(0, "a <= b", &["a", "b"])],
        );
        assert_eq!(
            swapped.discharged_rung(),
            None,
            "a precondition the function does not declare must never reach the theorem: \
             {swapped:#?}"
        );

        // And with NO precondition the same theorem is refused, which is what
        // makes the hypothesis load bearing rather than decorative.
        let bare = kernel_discharge_ensures_citation_under(
            &env,
            "rmax_le_left",
            "result <= a",
            params,
            "rmax",
            &facets,
            &[],
        );
        assert_eq!(bare.discharged_rung(), None, "{bare:#?}");
    }

    /// N-A4 — WHY THE NON-VACUITY GUARD IS LOAD BEARING.
    ///
    /// `requires a < a` admits no input, so `∀ a b, a < a → anything` is
    /// provable and the kernel certifies it. This is not a soundness failure —
    /// the statement is true — but reporting "your postcondition is discharged
    /// under `requires`" for it would be a green that lies: the row constrains
    /// no reachable call.
    ///
    /// The ladder deliberately does NOT decide this: it answers the kernel
    /// question it was asked. The guard lives at the consumer
    /// (`bound_hypotheses_have_ground_witness` in the verify pass), which
    /// searches the exact query-owned carriers for a satisfying assignment and
    /// withholds the positive note when it finds none. This test pins the half
    /// that makes the guard necessary: without it, the conditional discharge
    /// below is reported.
    #[test]
    fn n_a4_a_contradictory_precondition_discharges_anything() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let mut env = Environment::with_prelude();
        let ok = check_clean_island_into(
            "def rmax (a : UInt64) (b : UInt64) : UInt64 := if a < b then b else a\n\n\
             theorem vacuous_le : forall (a : UInt64) (b : UInt64), \
                 Nat.lt (UInt64.toNat a) (UInt64.toNat a) -> \
                 Nat.le (UInt64.toNat (if a < b then b else a)) (UInt64.toNat a) := \
                 fun a b h => False.elim (Nat.lt_irrefl (UInt64.toNat a) h)",
            &mut env,
        );
        assert!(!ok.is_rejected(), "setup island: {:?}", ok.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "rmax", &mut facets).expect("rmax must admit");
        let ladder = kernel_discharge_ensures_citation_under(
            &env,
            "vacuous_le",
            "result <= a",
            params,
            "rmax",
            &facets,
            &[u64_hyp(0, "a < a", &["a"])],
        );
        assert_eq!(
            ladder.discharged_rung(),
            Some(CitationRung::UnderRequires),
            "the kernel answers the question it was asked; vacuity is the consumer's guard, not \
             the ladder's: {ladder:#?}"
        );
    }

    /// M-A3 — THE SEMANTIC OFFSET CONTROL, and the reason the binder shift goes
    /// through the kernel's own `Expr::lift` rather than a hand-computed offset.
    ///
    /// Three same-carrier binders `(a b c : UInt64)`. An off-by-one shift of a
    /// hypothesis over same-typed binders is WELL-TYPED, so `reject_untyped_goal`
    /// cannot catch it; only a semantic control can. Here `requires b <= c`
    /// under a +1 shift would read `a <= b`, which is exactly the hypothesis the
    /// theorem `shifted_ok` consumes. The theorem must therefore discharge
    /// `requires a <= b` and must NOT discharge `requires b <= c`.
    #[test]
    fn g1_hypothesis_binds_the_authored_parameters() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64"), ("c", "u64")];
        let mut env = Environment::with_prelude();
        let ok = check_clean_island_into(
            "def pick3 (a : UInt64) (b : UInt64) (c : UInt64) : UInt64 := a\n\n\
             theorem shifted_ok : forall (a : UInt64) (b : UInt64) (c : UInt64), \
                 Nat.le (UInt64.toNat a) (UInt64.toNat b) -> \
                 Nat.le (UInt64.toNat a) (UInt64.toNat b) := fun a b c h => h",
            &mut env,
        );
        assert!(!ok.is_rejected(), "setup island: {:?}", ok.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "pick3", &mut facets).expect("pick3 must admit");

        let right = kernel_discharge_ensures_citation_under(
            &env,
            "shifted_ok",
            "result <= b",
            params,
            "pick3",
            &facets,
            &[u64_hyp(0, "a <= b", &["a", "b"])],
        );
        assert_eq!(
            right.discharged_rung(),
            Some(CitationRung::UnderRequires),
            "the authored hypothesis must discharge: {right:#?}"
        );

        let shifted = kernel_discharge_ensures_citation_under(
            &env,
            "shifted_ok",
            "result <= b",
            params,
            "pick3",
            &facets,
            &[u64_hyp(0, "b <= c", &["b", "c"])],
        );
        assert_eq!(
            shifted.discharged_rung(),
            None,
            "a hypothesis about `b <= c` must not be satisfied by a theorem about `a <= b`; a \
             discharge here is a de Bruijn shift the type checker cannot see: {shifted:#?}"
        );
    }

    /// N-A3 — THE FALSE-ACCEPT GUARD. A `requires` whose canonical text uses
    /// machine arithmetic must never become a hypothesis: Clean reads `+` on
    /// `UInt64` as WRAPPING while callers are charged the non-wrapping reading,
    /// so `a = u64::MAX, b = 1` satisfies the charged reading and refutes the
    /// Clean one. The clause is OMITTED (naming `+`), and with nothing else to
    /// carry there is no second rung at all.
    #[test]
    fn n_a3_a_wrapping_arithmetic_requires_is_never_a_hypothesis() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        // (The un-admitted arm this test used to open with asserted `is_err()`
        // on a build whose `result` was unbindable anyway, so it measured the
        // self-admission gate rather than the allow-list. It is gone; every arm
        // below runs against an ADMITTED `pick`.)
        let mut env = Environment::with_prelude();
        let ok =
            check_clean_island_into("def pick (a : UInt64) (b : UInt64) : UInt64 := b", &mut env);
        assert!(!ok.is_rejected(), "setup island: {:?}", ok.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "pick", &mut facets).expect("pick must admit");
        let alone = trust_spec_elab::elaborate_ensures_under_requires(
            "result <= a",
            params,
            "pick",
            &facets,
            &[u64_hyp(0, "a + b > 10", &["a", "b"])],
        );
        let err = alone.err().expect("an arithmetic-only candidate leaves no eligible hypothesis");
        assert!(err.contains("eligible"), "the refusal must say no clause was eligible; got {err}");

        // The same clause with a companion that IS eligible keeps the omission
        // visible rather than silently dropping it.
        let mixed = trust_spec_elab::elaborate_ensures_under_requires(
            "result <= a",
            params,
            "pick",
            &facets,
            &[u64_hyp(0, "a + b > 10", &["a", "b"]), u64_hyp(1, "b <= a", &["a", "b"])],
        )
        .expect("the eligible companion still builds a goal");
        assert_eq!(mixed.bound_count(), 1, "exactly the eligible clause is carried");
        let arith = &mixed.hypotheses[0];
        match &arith.disposition {
            trust_spec_elab::HypothesisDisposition::Omitted { reason } => assert!(
                reason.contains("`+`"),
                "the omission must name the operator that caused it; got {reason}"
            ),
            other => panic!("machine arithmetic must be omitted, got {other:?}"),
        }
    }

    /// M-A1 — the MUTATION CONTROL for N-A3: the elaborator itself is perfectly
    /// happy to build `a + b > 10`. So what refuses the wrapping attack is the
    /// E-allow filter, not a happy accident of the kernel fragment — remove the
    /// filter and the attack is expressible.
    #[test]
    fn m_a1_the_allow_list_not_the_elaborator_refuses_wrapping_arithmetic() {
        let goal =
            trust_spec_elab::elaborate_goal_typed("a + b > 10", &[("a", "u64"), ("b", "u64")]);
        assert!(
            goal.is_ok(),
            "if the elaborator refused this on its own, N-A3 would prove nothing: {goal:?}"
        );
    }

    /// M-A2 — binder order is load bearing. Two carried hypotheses in contract
    /// order `#0, #1`; a theorem that consumes them in the other order states a
    /// different Pi type and must not discharge.
    #[test]
    fn m_a2_hypothesis_order_is_contract_order() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64"), ("c", "u64")];
        let mut env = Environment::with_prelude();
        let ok = check_clean_island_into(
            "def pick3 (a : UInt64) (b : UInt64) (c : UInt64) : UInt64 := a\n\n\
             theorem in_order : forall (a : UInt64) (b : UInt64) (c : UInt64), \
                 Nat.le (UInt64.toNat a) (UInt64.toNat b) -> \
                 Nat.le (UInt64.toNat b) (UInt64.toNat c) -> \
                 Nat.le (UInt64.toNat a) (UInt64.toNat b) := fun a b c h1 h2 => h1\n\n\
             theorem swapped : forall (a : UInt64) (b : UInt64) (c : UInt64), \
                 Nat.le (UInt64.toNat b) (UInt64.toNat c) -> \
                 Nat.le (UInt64.toNat a) (UInt64.toNat b) -> \
                 Nat.le (UInt64.toNat a) (UInt64.toNat b) := fun a b c h1 h2 => h2",
            &mut env,
        );
        assert!(!ok.is_rejected(), "setup island: {:?}", ok.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "pick3", &mut facets).expect("pick3 must admit");
        let hyps = [u64_hyp(0, "a <= b", &["a", "b"]), u64_hyp(1, "b <= c", &["b", "c"])];

        let ordered = kernel_discharge_ensures_citation_under(
            &env,
            "in_order",
            "result <= b",
            params,
            "pick3",
            &facets,
            &hyps,
        );
        assert_eq!(
            ordered.discharged_rung(),
            Some(CitationRung::UnderRequires),
            "contract order is the goal's order: {ordered:#?}"
        );
        let swapped = kernel_discharge_ensures_citation_under(
            &env,
            "swapped",
            "result <= b",
            params,
            "pick3",
            &facets,
            &hyps,
        );
        assert_eq!(
            swapped.discharged_rung(),
            None,
            "a theorem that consumes the hypotheses in the other order states a different \
             proposition: {swapped:#?}"
        );
    }

    /// N-A8 — a theorem of the RIGHT (G1) type whose proof rests on an axiom is
    /// a CERTIFICATION failure on that rung, never "it states neither goal".
    /// The rung selector exists for exactly this: the author needs to be told
    /// their statement is right and their proof is not.
    #[test]
    fn n_a8_an_axiom_tainted_proof_of_the_right_statement_names_its_rung() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let mut env = Environment::with_prelude();
        // The strict island policy ALSO refuses this island (an `axiom` leaf is
        // not a checked proof term), which is the outer defence and is asserted
        // elsewhere. The declarations are registered before that policy runs, so
        // this unit can still exercise the grading path the policy would never
        // let a user reach — which is the point: even if it were reachable, the
        // ladder must report a CERTIFICATION failure on the stated rung.
        let ok = check_clean_island_into(
            "def pick (a : UInt64) (b : UInt64) : UInt64 := b\n\n\
             axiom cheat : forall (a : UInt64) (b : UInt64), \
                 Nat.le (UInt64.toNat b) (UInt64.toNat a) -> \
                 Nat.le (UInt64.toNat b) (UInt64.toNat a)\n\n\
             theorem pick_le_cheat : forall (a : UInt64) (b : UInt64), \
                 Nat.le (UInt64.toNat b) (UInt64.toNat a) -> \
                 Nat.le (UInt64.toNat b) (UInt64.toNat a) := fun a b h => cheat a b h",
            &mut env,
        );
        assert!(
            ok.errors.iter().any(|e| e.message.contains("axiom")),
            "the island policy must independently refuse the axiom: {:?}",
            ok.errors
        );
        assert!(
            env.get_const(&clean_kernel::Name::from_string("pick_le_cheat")).is_some(),
            "the tainted theorem must be registered for this unit to measure anything"
        );
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "pick", &mut facets).expect("pick must admit");
        let ladder = kernel_discharge_ensures_citation_under(
            &env,
            "pick_le_cheat",
            "result <= a",
            params,
            "pick",
            &facets,
            &[u64_hyp(0, "b <= a", &["a", "b"])],
        );
        assert_eq!(ladder.discharged_rung(), None, "an axiom closure never discharges");
        assert_eq!(
            ladder.rung,
            CitationRung::UnderRequires,
            "the reported rung must be the one the theorem STATES: {ladder:#?}"
        );
        assert!(
            matches!(
                ladder.verdict,
                CitationVerdict::KernelStatementMatchTrusted { .. }
                    | CitationVerdict::StatementOrCertificationRejected { .. }
            ),
            "the verdict must be the certification failure, not a statement mismatch: {ladder:#?}"
        );
    }

    /// R-A — no program that is green today changes. When the unconditional goal
    /// certifies, the ladder stops on rung (1) and never consults the
    /// hypotheses, whatever `requires` the function carries.
    #[test]
    fn r_a_an_unconditional_theorem_still_discharges_on_rung_one() {
        let params: &[(&str, &str)] = &[("x", "u64")];
        let mut env = Environment::with_prelude();
        let ok = check_clean_island_into(
            "def self_id (x : UInt64) : UInt64 := x\n\n\
             theorem t : forall (x : UInt64), Nat.le (UInt64.toNat x) (UInt64.toNat x) := \
                 fun x => Nat.le.refl (UInt64.toNat x)",
            &mut env,
        );
        assert!(!ok.is_rejected(), "setup island: {:?}", ok.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        admit_certified_island_definition(&env, "self_id", &mut facets)
            .expect("self_id must admit");
        let ladder = kernel_discharge_ensures_citation_under(
            &env,
            "t",
            "result >= x",
            params,
            "self_id",
            &facets,
            &[trust_spec_elab::HypothesisInput {
                contract_index: 0,
                canonical_text: "x <= 5".to_string(),
                authored_text: "x <= 5".to_string(),
                query_bindings: vec![("x".to_string(), "u64".to_string())],
            }],
        );
        assert_eq!(
            ladder.discharged_rung(),
            Some(CitationRung::Unconditional),
            "an unconditional theorem must keep its unconditional grade: {ladder:#?}"
        );
    }
}

/// TG9: raw trustc calls the defeq grader without the payload producer's
/// independent audit. Its authority must be fenced at this very entry.
#[cfg(test)]
mod tg9_defeq_audit_tests {
    use super::*;

    #[test]
    fn defeq_refuses_a_structural_closure_the_old_typecheck_accepts() {
        use clean_kernel::{Declaration, Name, TypeChecker};
        use trust_spec_elab::{FacetTable, ProofClauseInputs};

        let mut honest = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def tg9_self (x : UInt64) : UInt64 := x\n\
             def tg9_spec (x : UInt64) : UInt64 := x",
            &mut honest,
        );
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        let mut facets = FacetTable::new();
        for name in ["tg9_self", "tg9_spec"] {
            admit_certified_island_definition(&honest, name, &mut facets)
                .expect("honest admission");
        }
        let clause = "result == tg9_spec(x)";
        let params = &[("x", "u64")];
        assert!(matches!(
            kernel_prove_ensures_by_defeq(&honest, clause, params, "tg9_self", &facets),
            CitationVerdict::KernelStatementMatchCertified
        ));

        // Same names, types and VALUES, but only structural registration in
        // the current environment. A facet from a checked environment cannot
        // stand in for the audit of this goal's actual reachable closure.
        let mut structural = Environment::with_prelude();
        for name in ["tg9_self", "tg9_spec"] {
            let info = honest.get_const(&Name::from_string(name)).expect("honest definition");
            structural
                .add_decl_structural(Declaration::Definition {
                    name: info.name.clone(),
                    level_params: info.level_params.clone(),
                    type_: info.type_.clone(),
                    value: info.value.clone().expect("definition value"),
                    is_reducible: info.is_reducible,
                })
                .expect("structural registration");
        }
        let (goal, seeded) = lifted_ensures_goal(
            &structural,
            clause,
            params,
            "tg9_self",
            &facets,
            &ProofClauseInputs::strict(),
        )
        .expect("the same well-typed goal");
        let env = seeded.as_ref().unwrap_or(&structural);
        assert!(reject_untyped_goal(env, &goal).is_none());
        let proof = defeq_closed_proof(&goal).expect("closed reflexivity candidate");
        assert!(
            TypeChecker::new(env).check_type(&proof, &goal).is_ok(),
            "negative control: the exact old defeq route accepts this certificate"
        );
        assert!(
            !env.audit_certification(&goal, &proof).is_certified(),
            "the full audit must independently refuse the certificate"
        );
        assert!(
            matches!(
                kernel_prove_ensures_by_defeq(env, clause, params, "tg9_self", &facets),
                CitationVerdict::StatementOrCertificationRejected { .. }
            ),
            "raw defeq must refuse the same certificate"
        );
    }
}

/// Trust (nat-lift): the lift ON THE WIRE — an island `def` over `Nat`, a real
/// compiler mint of a `u64` Rust function, and the actual discharge lanes.
///
/// The unit tests in `trust-spec-elab` pin the goal SHAPE. These pin that the
/// shape survives the whole path the compiler takes: the island admitter's
/// carrier read-back, the mint's recorded return domain, the seeding
/// obligation, `reject_untyped_goal`, and the kernel judgment. A lift that is
/// right in the elaborator and wrong at any of those is still a lift that does
/// not work.
#[cfg(test)]
mod nat_lift_wire_tests {
    use trust_spec_elab::{FacetTable, ProofClauseInputs};

    use super::*;

    /// `fn c6(a: u64) -> u64 { 6 }`, as the extracted IR the compiler mints
    /// from.
    fn c6_function(name: &str) -> trust_types::VerifiableFunction {
        use trust_types::{
            BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
            Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
        };
        VerifiableFunction {
            name: name.into(),
            def_path: format!("crate::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u64(), name: None },
                    LocalDecl { index: 1, ty: Ty::u64(), name: Some("a0".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(6, 64))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u64(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn wire_table(island: &str, name: &str) -> (Environment, FacetTable) {
        let table = FacetTable::from_structural_facets([
            (format!("crate::{name}").as_str(), true, true, true, true),
            (name, true, true, true, true),
        ]);
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(island, &mut env);
        assert!(!outcome.is_rejected(), "island must check: {:?}", outcome.errors);
        (env, table)
    }

    /// THE POINT OF THE WHOLE LANE: a `u64` Rust function discharges a
    /// postcondition stated over an island definition written in `Nat` — the
    /// carrier every owner Lean model is already written in. Before this the
    /// clause could not even be stated.
    #[test]
    fn a_u64_function_discharges_a_nat_level_island_definition() {
        let (mut env, table) = wire_table("def c6_nat (x : Nat) : Nat := 6", "c6u");
        let (path, admission) = admit_function_into(&mut env, &c6_function("c6u"), &table)
            .expect("the Rust function must mint");
        assert_eq!(path, "crate::c6u");
        let mut discharge = table.clone();
        discharge.admit("c6u", admission);
        admit_certified_island_definition(&env, "c6_nat", &mut discharge)
            .expect("the Nat-carrier island definition must admit for citation");

        let verdict = kernel_prove_ensures_by_defeq_in(
            &env,
            "(result as nat) == c6_nat(a as nat)",
            &[("a", "u64")],
            "c6u",
            &discharge,
            &ProofClauseInputs::proof_lift(Some("u64")),
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the lifted clause must discharge end-to-end by kernel defeq; got {verdict:?}"
        );
    }

    /// The CLOSE NEGATIVE TWIN: the same wiring against a definition with a
    /// different value. The lift is exact, so `6 = 7` is not definitional and
    /// the discharge must fail. (If the lift were lossy — e.g. if the compiler
    /// narrowed the Lean side — twins like this are where that shows.)
    #[test]
    fn the_wrong_nat_value_does_not_discharge() {
        let (mut env, table) = wire_table("def c7_nat (x : Nat) : Nat := 7", "c6u");
        let (_, admission) =
            admit_function_into(&mut env, &c6_function("c6u"), &table).expect("mints");
        let mut discharge = table.clone();
        discharge.admit("c6u", admission);
        admit_certified_island_definition(&env, "c7_nat", &mut discharge).expect("admits");

        let verdict = kernel_prove_ensures_by_defeq_in(
            &env,
            "(result as nat) == c7_nat(a as nat)",
            &[("a", "u64")],
            "c6u",
            &discharge,
            &ProofClauseInputs::proof_lift(Some("u64")),
        );
        assert!(
            !matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "a false lifted clause must NOT discharge; got {verdict:?}"
        );
    }

    /// CORPUS CONTROL on the wire: the same clause at `Strict` — which is what
    /// every lane that has not opted in still passes — is refused, with the
    /// clause reported as outside the fragment. No lane acquires the lift by
    /// accident.
    #[test]
    fn the_same_clause_at_strict_is_outside_the_fragment() {
        let (mut env, table) = wire_table("def c6_nat (x : Nat) : Nat := 6", "c6u");
        let (_, admission) =
            admit_function_into(&mut env, &c6_function("c6u"), &table).expect("mints");
        let mut discharge = table.clone();
        discharge.admit("c6u", admission);
        admit_certified_island_definition(&env, "c6_nat", &mut discharge).expect("admits");

        let verdict = kernel_prove_ensures_by_defeq(
            &env,
            "(result as nat) == c6_nat(a as nat)",
            &[("a", "u64")],
            "c6u",
            &discharge,
        );
        assert!(
            matches!(verdict, CitationVerdict::ClauseOutsideFragment { .. }),
            "Strict must still refuse the cast; got {verdict:?}"
        );
    }

    /// The UNLIFTED clause still discharges through the same lane at
    /// `ProofLift`: turning the mode on does not change a clause that has no
    /// cast in it.
    #[test]
    fn an_unlifted_clause_is_unaffected_by_the_mode() {
        let (mut env, table) = wire_table("def c6_isl (x : UInt64) : UInt64 := 6", "c6u");
        let (_, admission) =
            admit_function_into(&mut env, &c6_function("c6u"), &table).expect("mints");
        let mut discharge = table.clone();
        discharge.admit("c6u", admission);
        admit_certified_island_definition(&env, "c6_isl", &mut discharge).expect("admits");

        for inputs in [ProofClauseInputs::strict(), ProofClauseInputs::proof_lift(Some("u64"))] {
            let verdict = kernel_prove_ensures_by_defeq_in(
                &env,
                "result == c6_isl(a)",
                &[("a", "u64")],
                "c6u",
                &discharge,
                &inputs,
            );
            assert!(
                matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
                "the machine-carrier clause must discharge in BOTH modes; got {verdict:?}"
            );
        }
    }

    /// Trust (nat-lift §3.1) name capture, check 1: an island may not declare
    /// into the seeded-model namespace. Without this an island could define
    /// `trust_checked_toInt64 := fun _ => 0` and turn every signed lift into
    /// `0 = 0`.
    #[test]
    fn an_island_may_not_declare_into_the_seeded_model_namespace() {
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def trust_checked_toInt64 (v : BitVec 64) : Int := Int.ofNat 0",
            &mut env,
        );
        assert!(outcome.is_rejected(), "the capture must be refused at declaration");
        let joined: String =
            outcome.errors.iter().map(|e| e.message.clone()).collect::<Vec<_>>().join(" | ");
        assert!(
            joined.contains("seeded-model namespace"),
            "the refusal must name the namespace: {joined}"
        );
        assert!(joined.contains("Rename"), "and offer the option: {joined}");
    }

    /// `fn ident(a: T) -> T { a }`, as the extracted IR the compiler mints
    /// from — the shape that actually exercises the ARGUMENT lift.
    fn identity_function(name: &str, ty: trust_types::Ty) -> trust_types::VerifiableFunction {
        use trust_types::{
            BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, VerifiableBody, VerifiableFunction,
        };
        VerifiableFunction {
            name: name.into(),
            def_path: format!("crate::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: ty.clone(), name: None },
                    LocalDecl { index: 1, ty: ty.clone(), name: Some("a0".into()) },
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
                arg_count: 1,
                return_ty: ty,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    /// The ARGUMENT lift, on the wire. `c6_nat`'s body is the constant `6`, so
    /// that test stays green even if the argument were built over the wrong
    /// variable or over any other well-typed `Nat` term. This one cannot: both
    /// sides are the identity, so the goal closes only if
    /// `UInt64.toNat (idu a) ≡ UInt64.toNat a` — the argument's own lift.
    #[test]
    fn the_argument_lift_is_exercised_end_to_end_by_an_identity() {
        let (mut env, table) = wire_table("def nat_id (x : Nat) : Nat := x", "idu");
        let (_, admission) = admit_function_into(
            &mut env,
            &identity_function("idu", trust_types::Ty::u64()),
            &table,
        )
        .expect("the Rust function must mint");
        let mut discharge = table.clone();
        discharge.admit("idu", admission);
        admit_certified_island_definition(&env, "nat_id", &mut discharge).expect("admits");

        let verdict = kernel_prove_ensures_by_defeq_in(
            &env,
            "(result as nat) == nat_id(a as nat)",
            &[("a", "u64")],
            "idu",
            &discharge,
            &ProofClauseInputs::proof_lift(Some("u64")),
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the identity shape must discharge; got {verdict:?}"
        );
    }

    /// THE SIGNED HALF, end to end — previously measured only in isolation, so
    /// `env_for_lifted_goal`'s seeding branch (the clone, the
    /// `seed_signed_lift_model` call, and the refusal path below) was dead in
    /// every wire test.
    #[test]
    fn an_i64_function_discharges_an_int_level_island_definition() {
        let (mut env, table) = wire_table("def int_id (x : Int) : Int := x", "idi");
        let (_, admission) = admit_function_into(
            &mut env,
            &identity_function("idi", trust_types::Ty::i64()),
            &table,
        )
        .expect("the Rust function must mint");
        let mut discharge = table.clone();
        discharge.admit("idi", admission);
        admit_certified_island_definition(&env, "int_id", &mut discharge)
            .expect("the Int-carrier island definition must admit for citation");

        let verdict = kernel_prove_ensures_by_defeq_in(
            &env,
            "(result as int) == int_id(a as int)",
            &[("a", "i64")],
            "idi",
            &discharge,
            &ProofClauseInputs::proof_lift(Some("i64")),
        );
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "the signed lift must discharge end-to-end through the SEEDED model; got {verdict:?}"
        );
        // The seeding really happened, and into a CLONE: the session
        // environment the caller still holds has no lift constant in it.
        assert!(
            env.get_const(&clean_kernel::Name::from_string(
                &trust_spec_elab::signed_lift_const_name(trust_spec_elab::MachineSIntWidth::I64)
            ))
            .is_none(),
            "the common path must not mutate the caller's environment"
        );
    }

    /// Trust (nat-lift §3.1) name capture, check 2 — the one that runs when an
    /// island reaches the environment by a path the declaration-time
    /// reservation does not cover. A FOREIGN `trust_checked_toInt64` in the
    /// session environment must make the CLAUSE fail closed, not capture the
    /// lift.
    ///
    /// The control is the test above: the identical wiring without the planted
    /// homonym certifies, so this refusal is the guard and not the clause.
    #[test]
    fn a_foreign_seeded_model_homonym_refuses_the_clause_on_the_wire() {
        let (mut env, table) = wire_table("def int_id (x : Int) : Int := x", "idi");
        let (_, admission) = admit_function_into(
            &mut env,
            &identity_function("idi", trust_types::Ty::i64()),
            &table,
        )
        .expect("mints");
        let mut discharge = table.clone();
        discharge.admit("idi", admission);
        admit_certified_island_definition(&env, "int_id", &mut discharge).expect("admits");

        // Plant the capture DIRECTLY in the kernel environment, i.e. past the
        // island declaration gate the previous test pins.
        let bv64 = clean_kernel::Expr::app(
            clean_kernel::Expr::const_str("BitVec"),
            clean_kernel::Expr::nat_lit(64),
        );
        env.add_decl(clean_kernel::Declaration::Definition {
            name: clean_kernel::Name::from_string(&trust_spec_elab::signed_lift_const_name(
                trust_spec_elab::MachineSIntWidth::I64,
            )),
            level_params: vec![],
            type_: clean_kernel::Expr::arrow(bv64.clone(), clean_kernel::Expr::const_str("Int")),
            value: clean_kernel::Expr::lam(
                clean_kernel::BinderInfo::Default,
                bv64,
                clean_kernel::Expr::app(
                    clean_kernel::Expr::const_str("Int.ofNat"),
                    clean_kernel::Expr::nat_lit(0),
                ),
            ),
            is_reducible: true,
        })
        .expect("the planted homonym must itself be well-typed, or this measures nothing");

        let verdict = kernel_prove_ensures_by_defeq_in(
            &env,
            "(result as int) == int_id(a as int)",
            &[("a", "i64")],
            "idi",
            &discharge,
            &ProofClauseInputs::proof_lift(Some("i64")),
        );
        let CitationVerdict::ClauseOutsideFragment { reason } = &verdict else {
            panic!("a captured lift constant must refuse the clause; got {verdict:?}");
        };
        assert!(
            reason.contains("foreign homonym"),
            "and the REASON must be the capture, not some later mismatch: {reason}"
        );
    }

    // ------------------------------------------------------------------ d1
    //
    // Trust (d1, 2026-09-28): the E9 sweep's ∀-`result` FALLBACK — the reading
    // a cited `ensures` gets when the postcondition goal cannot be built, which
    // with verification off is every clause that binds `result`. It used to be
    // fixed at `Strict` while the discharge rung ran at `ProofLift`, so a lifted
    // clause the verified lane certifies was a hard `ClauseOutsideFragment` in
    // the unverified lane (measured: `apdf-lzw-width`, six citations).

    /// The measured d1 island: `spec_ge` over `Nat`, `dec_ge` over `UInt16`,
    /// and the bridge theorem the verified lane kernel-discharges.
    const D1_ISLAND: &str = "def spec_ge (n : Nat) : Bool := \
             Decidable.decide (Nat.le 512 n) (Nat.decLe 512 n)\n\n\
         def dec_ge (n : UInt16) : Bool := \
             Decidable.decide (LE.le (UInt16.ofNat 512) n) \
                 (instDecidableUInt16Le (UInt16.ofNat 512) n)\n\n\
         theorem dec_is_spec : forall (n : UInt16), \
             Eq (dec_ge n) (spec_ge (UInt16.toNat n)) := \
             fun n => Eq.refl (dec_ge n)\n\n\
         theorem toNat_self : forall (r : UInt16), \
             Eq (UInt16.toNat r) (UInt16.toNat r) := \
             fun r => Eq.refl (UInt16.toNat r)";

    fn d1_env() -> (Environment, FacetTable) {
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(D1_ISLAND, &mut env);
        assert!(!outcome.is_rejected(), "the d1 island must check: {:?}", outcome.errors);
        let mut facets = FacetTable::new();
        admit_certified_island_definition(&env, "spec_ge", &mut facets)
            .expect("the Nat-carrier island definition must admit for citation");
        (env, facets)
    }

    /// THE REPRO, at the kernel entry. `Strict` refuses the clause before any
    /// theorem is consulted — the verdict the unverified-lane allowance does
    /// not (and must not) relax — and names the CAST rather than calling
    /// `x as nat` "a `u16` term" (B2). `ProofLift` elaborates it and grades the
    /// ∀-`result` reading, which `dec_is_spec` does not prove: a statement
    /// mismatch, exactly the arm the allowance answers with "NOT checked".
    #[test]
    fn d1_the_forall_result_fallback_speaks_the_mode_it_is_given() {
        let (env, facets) = d1_env();
        let clause = "result == spec_ge(x as nat)";
        let var_types = [("result", "bool"), ("x", "u16")];

        let strict = kernel_unify_citation_typed_with_facets_in(
            &env,
            "dec_is_spec",
            clause,
            &var_types,
            &facets,
            &ProofClauseInputs::strict(),
        );
        let CitationVerdict::ClauseOutsideFragment { reason } = &strict else {
            panic!("Strict must refuse the lift before grading; got {strict:?}");
        };
        assert!(
            !reason.contains("`u16` term"),
            "B2: `x as nat` is not a `u16` term, whatever the mode: {reason}"
        );

        let lifted = kernel_unify_citation_typed_with_facets_in(
            &env,
            "dec_is_spec",
            clause,
            &var_types,
            &facets,
            &ProofClauseInputs::proof_lift(Some("bool")),
        );
        assert!(
            matches!(lifted, CitationVerdict::StatementOrCertificationRejected { .. }),
            "ProofLift must reach the STATEMENT judgment (the theorem proves the clause with \
             `result` bound to the body, not for every `result`); got {lifted:?}"
        );

        // The session entry threads the same mode through the same gate.
        let mut session = CleanIslandSession::new();
        assert!(!session.check(D1_ISLAND).is_rejected(), "the session island must check");
        let mut session_facets = FacetTable::new();
        admit_certified_island_definition(
            session.environment().expect("an untainted session has an environment"),
            "spec_ge",
            &mut session_facets,
        )
        .expect("admits");
        let via_session = session.check_citation_typed_with_facets_in(
            "dec_is_spec",
            clause,
            &var_types,
            &session_facets,
            &ProofClauseInputs::proof_lift(Some("bool")),
        );
        assert!(
            matches!(via_session, CitationVerdict::StatementOrCertificationRejected { .. }),
            "the session entry must agree with the kernel entry; got {via_session:?}"
        );
    }

    /// The case the mode change turns from an error into a statement MATCH
    /// (report variant j): a lifted clause the ∀-`result` reading does prove.
    /// No row is credited by this entry — it is the sweep's diagnostic reading
    /// — and the unlifted twin (`result == result`) already reached this
    /// verdict at `Strict`.
    #[test]
    fn d1_a_lifted_clause_the_forall_reading_proves_matches_only_in_proof_lift() {
        let (env, facets) = d1_env();
        let clause = "(result as nat) == (result as nat)";
        let var_types = [("result", "u16")];
        let strict = kernel_unify_citation_typed_with_facets_in(
            &env,
            "toNat_self",
            clause,
            &var_types,
            &facets,
            &ProofClauseInputs::strict(),
        );
        assert!(
            matches!(strict, CitationVerdict::ClauseOutsideFragment { .. }),
            "Strict refuses the cast, as before; got {strict:?}"
        );
        let lifted = kernel_unify_citation_typed_with_facets_in(
            &env,
            "toNat_self",
            clause,
            &var_types,
            &facets,
            &ProofClauseInputs::proof_lift(Some("u16")),
        );
        assert!(
            matches!(lifted, CitationVerdict::KernelStatementMatchCertified),
            "the ∀-`result` reading of a reflexive lifted clause is what the theorem states; \
             got {lifted:?}"
        );
    }

    /// SIGNED-LIFT SEEDING in the fallback (critique MUST-FIX 2). `x as int`
    /// over `i32` names `trust_checked_toInt32`; unseeded, the goal does not
    /// type and the verdict is a `ClauseOutsideFragment` "does not typecheck".
    /// Seeded into a CLONE, the goal types and is judged by statement — and the
    /// caller's environment is untouched. A foreign homonym of the lift
    /// constant refuses the clause as `ClauseOutsideFragment`, never as a
    /// mismatch the unverified-lane allowance could relax.
    #[test]
    fn d1_the_fallback_seeds_a_signed_lift_into_a_clone_and_refuses_a_homonym() {
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def spec_nonneg (n : Int) : Bool := Decidable.decide (Int.le 0 n) (Int.decLe 0 n)\n\n\
             theorem taut_bool : forall (b : Bool), Eq b b := fun b => Eq.refl b",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let mut facets = FacetTable::new();
        admit_certified_island_definition(&env, "spec_nonneg", &mut facets).expect("admits");
        let clause = "result == spec_nonneg(x as int)";
        let var_types = [("result", "bool"), ("x", "i32")];
        let lift_name = clean_kernel::Name::from_string(&trust_spec_elab::signed_lift_const_name(
            trust_spec_elab::MachineSIntWidth::I32,
        ));

        let verdict = kernel_unify_citation_typed_with_facets_in(
            &env,
            "taut_bool",
            clause,
            &var_types,
            &facets,
            &ProofClauseInputs::proof_lift(Some("bool")),
        );
        assert!(
            matches!(verdict, CitationVerdict::StatementOrCertificationRejected { .. }),
            "the seeded goal must TYPE and be judged by statement (an unseeded one is a \
             `does not typecheck` fragment refusal); got {verdict:?}"
        );
        assert!(
            env.get_const(&lift_name).is_none(),
            "seeding must happen in a clone, never in the caller's environment"
        );

        // Plant a foreign homonym directly in the kernel environment.
        let bv32 = clean_kernel::Expr::app(
            clean_kernel::Expr::const_str("BitVec"),
            clean_kernel::Expr::nat_lit(32),
        );
        env.add_decl(clean_kernel::Declaration::Definition {
            name: lift_name,
            level_params: vec![],
            type_: clean_kernel::Expr::arrow(bv32.clone(), clean_kernel::Expr::const_str("Int")),
            value: clean_kernel::Expr::lam(
                clean_kernel::BinderInfo::Default,
                bv32,
                clean_kernel::Expr::app(
                    clean_kernel::Expr::const_str("Int.ofNat"),
                    clean_kernel::Expr::nat_lit(0),
                ),
            ),
            is_reducible: true,
        })
        .expect("the planted homonym must itself be well-typed, or this measures nothing");
        let captured = kernel_unify_citation_typed_with_facets_in(
            &env,
            "taut_bool",
            clause,
            &var_types,
            &facets,
            &ProofClauseInputs::proof_lift(Some("bool")),
        );
        let CitationVerdict::ClauseOutsideFragment { reason } = &captured else {
            panic!("a captured lift constant must refuse the clause; got {captured:?}");
        };
        assert!(reason.contains("foreign homonym"), "the reason is the capture: {reason}");
    }

    /// A tainted session answers the mode-taking fallback exactly as every
    /// other citation entry does.
    #[test]
    fn d1_a_tainted_session_refuses_the_mode_taking_fallback() {
        let mut session = CleanIslandSession::new();
        let _ = session.check("theorem bad_pin : True := sorry");
        assert!(session.is_tainted(), "setup must taint");
        let verdict = session.check_citation_typed_with_facets_in(
            "bad_pin",
            "x <= x",
            &[("x", "u64")],
            &FacetTable::new(),
            &ProofClauseInputs::proof_lift(None),
        );
        assert!(matches!(verdict, CitationVerdict::SessionTainted), "got {verdict:?}");
    }
}

#[cfg(test)]
#[path = "clean_island/tg14_tests.rs"]
mod tg14_tests;
