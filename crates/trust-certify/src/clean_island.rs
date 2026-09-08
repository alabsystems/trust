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
    island_definition_value(env, name)?;
    let info = env.get_const(&clean_kernel::Name::from_string(name))?;
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
fn option_signed_width_of_codomain(ty: &clean_kernel::Expr) -> Option<trust_spec_elab::MachineSIntWidth> {
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
/// `Int`, a structure, a dependent `BitVec n` whose width is a bound variable,
/// a universe-polymorphic head — answers `None` for the WHOLE signature, and
/// [`trust_spec_elab::Admission::carriers`] being `None` puts the elaborator
/// back on its pre-increment behaviour (one ambient domain across the atom).
/// A definition whose telescope is dependent therefore cannot be read as
/// non-dependent by accident: the dependency shows up as an unreadable width
/// and the whole record is refused.
#[must_use]
pub fn island_definition_carriers(
    env: &KernelEnvironment,
    name: &str,
) -> Option<trust_spec_elab::DeclaredCarriers> {
    island_definition_value(env, name)?;
    let info = env.get_const(&clean_kernel::Name::from_string(name))?;
    // A universe-polymorphic declaration is already refused by the admission
    // path; refuse it here too so this reader is safe to call on its own.
    if !info.level_params.is_empty() {
        return None;
    }
    let mut params = Vec::new();
    let mut ty: &clean_kernel::Expr = &info.type_;
    while let clean_kernel::ExprKind::Pi(_, domain, codomain) = ty.kind() {
        params.push(carrier_of_clean_type(domain)?);
        ty = codomain;
    }
    let ret = carrier_of_clean_type(ty)?;
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
fn carrier_of_clean_type(ty: &clean_kernel::Expr) -> Option<trust_spec_elab::Carrier> {
    use clean_kernel::ExprKind;
    use trust_spec_elab::{Carrier, MachineUIntWidth};
    match ty.kind() {
        ExprKind::Const(name, _) => match name.to_string().as_str() {
            "Nat" => Some(Carrier::Nat),
            "Bool" => Some(Carrier::Bool),
            "UInt8" => Some(Carrier::UInt(MachineUIntWidth::U8)),
            "UInt16" => Some(Carrier::UInt(MachineUIntWidth::U16)),
            "UInt32" => Some(Carrier::UInt(MachineUIntWidth::U32)),
            "UInt64" => Some(Carrier::UInt(MachineUIntWidth::U64)),
            _ => None,
        },
        ExprKind::App(head, arg) => {
            let ExprKind::Const(head_name, _) = head.kind() else {
                return None;
            };
            match head_name.to_string().as_str() {
                "BitVec" => {
                    let bits = nat_literal_of(arg)?;
                    Some(Carrier::BitVec(u32::try_from(bits).ok()?))
                }
                "Option" => Some(Carrier::Option(Box::new(carrier_of_clean_type(arg)?))),
                _ => None,
            }
        }
        _ => None,
    }
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
    // ------------------------------------------------------------------
    // I2 — a REFLECTED Rust carrier may not be admitted here.
    // ------------------------------------------------------------------
    // This function is the compiler's "`KernelChecked` is required" site: it
    // exists to authenticate a Clean declaration the CIC kernel re-checked, and
    // on success it stamps four `FacetStatus::Certified { evidence:
    // "clean-island-kernel-definition" }` facets. A `trust_import_*` constant is
    // not that. It is a Rust `fn` projected into the environment by
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
    if name.starts_with(KERNEL_IMPORT_PREFIX) {
        return Err(trust_symbols::KernelStatus::Reflected
            .require_kernel_check(name)
            .expect_err("Reflected never satisfies a kernel-check requirement")
            .to_string());
    }
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
        //
        // I2 strengthens this from a string comparison to a status question:
        // the identical re-admission is the one whose recorded status says the
        // kernel re-checked it. The name equality is kept as well, so this is
        // strictly narrower than before, never wider.
        if let Some(existing) = facets.admitted(name)
            && existing.kernel_const == name
            && existing.require_kernel_check().is_ok()
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

    let (arity, ret_domain) = island_definition_signature(env, name)
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
    let carriers = island_definition_carriers(env, name).filter(|c| c.params.len() == arity);
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
    let digest = trust_symbols::TermDigest::of_bytes(
        format!(
            "clean-island-definition\n{name}\ntype={}\nvalue={}",
            info.type_,
            info.value.as_ref().expect("checked non-None above"),
        )
        .as_bytes(),
    );
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
    let admission = match island_return_domain(&info.type_) {
        Some(domain) => admission.with_return_domain(domain),
        None => admission,
    };
    facets.admit(name, admission.clone());
    Ok(admission)
}

/// The elaboration [`trust_spec_elab::Domain`] named by an island
/// definition's RETURN type — the Pi-telescope codomain of its declared
/// kernel type — or `None` when the codomain is not one of the closed
/// carriers the clause fragment supports, in which case no return domain is
/// recorded and a variable-free atom keeps its fail-closed default. `BitVec
/// _` is deliberately unanswered: `i64`, `u128`, and `usize64` all share that
/// carrier, so the codomain alone cannot name the Rust-side domain.
fn island_return_domain(ty: &clean_kernel::Expr) -> Option<trust_spec_elab::Domain> {
    use trust_spec_elab::{Domain, MachineUIntWidth};
    let mut codomain = ty;
    while let clean_kernel::ExprKind::Pi(_, _, next) = codomain.kind() {
        codomain = next;
    }
    let clean_kernel::ExprKind::Const(name, _) = codomain.kind() else {
        return None;
    };
    Some(match name.to_string().as_str() {
        "UInt8" => Domain::Machine(MachineUIntWidth::U8),
        "UInt16" => Domain::Machine(MachineUIntWidth::U16),
        "UInt32" => Domain::Machine(MachineUIntWidth::U32),
        "UInt64" => Domain::Machine(MachineUIntWidth::U64),
        "Nat" => Domain::Nat,
        "Bool" => Domain::Bool,
        _ => return None,
    })
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
    // The same ill-typed-goal gate as the citation route: `check_type` below
    // judges the PROOF term and treats the goal expression as given, so it
    // must not be handed a goal the kernel cannot type (see
    // [`reject_untyped_goal`]).
    if let Some(verdict) = reject_untyped_goal(env, &goal) {
        return verdict;
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
fn reject_untyped_goal(
    env: &Environment,
    goal: &clean_kernel::Expr,
) -> Option<CitationVerdict> {
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
    let Some((_kernel_name, carrier_admission)) = admit_function_into(env, carrier, facets) else {
        return Err(R::CarrierOutsideCheckedFragment { carrier: carrier.def_path.clone() });
    };
    facets.admit(carrier.def_path.clone(), carrier_admission);
    // 4. The goal: result == island_def(x0, .., xN) over the carrier — the SAME
    //    defeq route every uncited ensures clause takes; the kernel unfolds both
    //    constants and judges.
    let clause = format!("result == {island_def}({})", names.join(", "));
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
    let debug = std::env::var_os("TRUST_E6_DEBUG").is_some();
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
    let (domains, names): (Vec<_>, Vec<_>) =
        rows.iter().flatten().cloned().unzip::<_, _, Vec<_>, Vec<_>>();
    let trust_types::Ty::Adt { fields: declared, variants, .. } = &func.body.return_ty else {
        if debug {
            eprintln!(
                "TRUST_E6_DEBUG field-mint fn={} REFUSED: return type is not an Adt ({:?})",
                func.def_path,
                func.body.return_ty
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
                if std::env::var_os("TRUST_E6_DEBUG").is_some() {
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
    use trust_types::admissible_body::{AdmissibleBody, recognize_admissible_body};
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
                        targets.iter().map(|(v, t)| format!("{v}->{}", t.0)).collect::<Vec<_>>().join(","),
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
    let result = match recognize_admissible_body(func)? {
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
                let domain = param_domains.first().cloned()?;
                if !param_domains.iter().all(|d| *d == domain)
                    || ty_to_domain(&func.body.return_ty).as_ref() != Some(&domain)
                    || domain != trust_spec_elab::Domain::Machine(width)
                {
                    return None;
                }
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
            if ty_to_domain(&func.body.return_ty) != Some(trust_spec_elab::Domain::Signed(width)) {
                return None;
            }
            trust_spec_elab::admit_signed_constant_function(env, &kernel_const, value, width)
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
        AdmissibleBody::WidenedEq { from_bits, to_bits, narrow_param, wide_param, cast_on_left } => {
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
    pub fn mark_import_satisfied_from_source(&mut self, module: &str) {
        self.file_ctx.mark_import_satisfied_from_source(module);
    }

    pub fn check_all(&mut self, sources: &[&str]) -> crate::clean_island_batch::CleanIslandBatch {
        let batch = crate::clean_island_batch::check_islands_batched(
            &mut self.env,
            &mut self.file_ctx,
            sources,
        );
        self.tainted |= batch.is_rejected();
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
    #[must_use]
    pub fn admit_program_functions(
        &mut self,
        functions: &[trust_types::VerifiableFunction],
        facet_table: &trust_spec_elab::FacetTable,
    ) -> Vec<(String, trust_spec_elab::Admission)> {
        // A struct-returning body contributes ONE admission PER FIELD; every
        // other shape contributes at most one for the whole function.
        let mut out = Vec::new();
        for func in functions {
            out.extend(admit_function_fields_into(&mut self.env, func, facet_table));
            if let Some(one) = admit_function_into(&mut self.env, func, facet_table) {
                out.push(one);
            }
        }
        out
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
                &self.env,
                theorem,
                clause_src,
                param_types,
                self_fn_name,
                facets,
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
/// `_`, under a [`KERNEL_IMPORT_PREFIX`] prefix that namespaces these constants
/// away from prelude and island declarations.
fn mangle_kernel_const(def_path: &str) -> String {
    let sanitized: String =
        def_path.chars().map(|c| if c.is_alphanumeric() { c } else { '_' }).collect();
    format!("{KERNEL_IMPORT_PREFIX}{sanitized}")
}

/// The machine-integer width for a bit count, or `None` outside the supported
/// widths (which fails the import closed).
fn machine_width(bits: u32) -> Option<trust_spec_elab::MachineUIntWidth> {
    use trust_spec_elab::MachineUIntWidth::{U8, U16, U32, U64};
    Some(match bits {
        8 => U8,
        16 => U16,
        32 => U32,
        64 => U64,
        _ => return None,
    })
}

/// The signed sibling of [`machine_width`]: `i8`–`i128`.
///
/// `i128` joined the table on 2026-08-24 (E6 widening increment 6). Nothing
/// below the table blocked it: `MachineSIntWidth::I128` and the `BitVec 128`
/// carrier have been in the clause elaborator all along, `Domain::bitvec_bits`
/// already answers `Some(128)`, `Domain::numeral`/`negative_numeral` already
/// range-check at `2^127`, and the sign-flip order key is the same
/// `Nat.xor (BitVec.toNat v) 2^(w-1)` shape at the wider `w`. The width table
/// was the only gate, and the cost of it being closed was that every
/// `i128`-typed function stayed unadmitted, so `result` in its postcondition
/// stayed universally quantified and the citation failed with a raw
/// `TermRejected` term dump instead of a discharge.
fn signed_machine_width(bits: u32) -> Option<trust_spec_elab::MachineSIntWidth> {
    use trust_spec_elab::MachineSIntWidth::{I8, I16, I32, I64, I128};
    Some(match bits {
        8 => I8,
        16 => I16,
        32 => I32,
        64 => I64,
        128 => I128,
        _ => return None,
    })
}

/// The E6 elaboration [`trust_spec_elab::Domain`] a Rust type carries, or `None`
/// for a type outside the supported fragment (floats, references, aggregates, …)
/// — which fails the import closed. Signed `i8`–`i64` map to
/// [`trust_spec_elab::Domain::Signed`] (E6 widening increment 4): the exact
/// two's-complement `BitVec` carrier whose comparisons the clause elaborator
/// already states over the sign-flip order keys.
///
/// `i128`/`u128` map to `Signed(I128)`/`U128` (E6 widening increment 6). Note
/// `u128` is NOT a `Machine` width: `MachineUIntWidth` tops out at 64 and its
/// carrier is `UInt64`, whereas `u128`'s carrier is the exact `BitVec 128`
/// [`trust_spec_elab::Domain::U128`] already provides. Routing it through
/// `machine_width` would have been the silent wrong answer.
fn ty_to_domain(ty: &trust_types::Ty) -> Option<trust_spec_elab::Domain> {
    use trust_spec_elab::{Domain, MachineUIntWidth};
    match ty {
        trust_types::Ty::Bool => Some(Domain::Bool),
        trust_types::Ty::Int { width: 128, signed: false } => Some(Domain::U128),
        trust_types::Ty::Int { width, signed: false } => machine_width(*width).map(Domain::Machine),
        trust_types::Ty::Int { width, signed: true } => {
            signed_machine_width(*width).map(Domain::Signed)
        }
        trust_types::Ty::PtrSizedInt { signed: false } => {
            Some(Domain::Machine(MachineUIntWidth::U64))
        }
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
///   * **All-or-nothing per parameter.** A struct contributes rows only when
///     EVERY declared field maps to a supported domain; one unsupported field
///     refuses the whole parameter (and, since a projection mint needs every
///     row, the whole function). There is therefore NO per-field filter for the
///     two sides to disagree about — and they would disagree, because the two
///     type vocabularies are not identical (`isize` has a `Domain` on one side
///     and not the other). A disagreement now lands on ARITY, which makes the
///     goal ill-typed and `reject_untyped_goal` refuses it.
///   * **The names are recorded.** `Admission::param_names` carries this list
///     into `elaborate_ensures`, which refuses a clause whose own parameter
///     list differs. That is what catches a same-length REORDERING, the one
///     drift the kernel cannot see.
///
/// A parameter with no recorded local name yields `None`: without it there is
/// no clause-side spelling to record, and an unnamed row could not be checked.
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
        if name.to_string().starts_with(KERNEL_IMPORT_PREFIX) {
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
    // A name the environment does not hold cannot be graded. The caller only
    // asks about declarations the batch reported as REGISTERED, so an absent
    // constant means the batch did not commit; the uncommitted case is refused
    // by the caller's own tripwire rather than silently graded here.
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

    // See `strict_leaf_policy_error` for why the `trust_import_` namespace is
    // refused at the point of declaration rather than downstream.
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
        let outcome = check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
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
        let outcome = check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
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
                !tc.is_def_eq(
                    &app1("narrow_mint", opaque.clone()),
                    &app1(forgery, opaque.clone())
                ),
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
                                Rvalue::Aggregate(
                                    agg(1),
                                    vec![Operand::Move(Place::local(4))],
                                ),
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
            Some(trust_spec_elab::Domain::OptionSigned(
                trust_spec_elab::MachineSIntWidth::I64
            ))
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
            BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
            VariantDef, VerifiableBody, VerifiableFunction,
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
            Some(trust_spec_elab::Domain::OptionSigned(
                trust_spec_elab::MachineSIntWidth::I64
            ))
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
            admit_function_into(
                &mut env3,
                &cadd("core::num::<impl i64>::checked_add"),
                &certified
            )
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
        let term = Ty::adt("crate::Term", vec![("coeff".into(), i64t()), ("lit".into(), lit.clone())]);
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
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Goto(BlockId(3)) },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1))))],
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
                                vec![Operand::Copy(Place::local(2)), Operand::Copy(Place::local(3))],
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
        let coeff = minted
            .iter()
            .find(|(key, _)| key == "crate::sat__field_coeff")
            .unwrap_or_else(|| panic!("no coeff field admission in {:?}", minted.iter().map(|(k, _)| k).collect::<Vec<_>>()));
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
        }
    }

    fn scalar_cst_fields() -> Vec<(String, trust_types::Ty)> {
        vec![("degree".to_string(), trust_types::Ty::u64()), ("coeff".to_string(), trust_types::Ty::u64())]
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
        let goal = trust_spec_elab::elaborate_ensures(
            "result == c.degree",
            &params,
            "degree_of",
            &table,
        )
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
        let err = trust_spec_elab::elaborate_ensures(
            "result == c.degree",
            &swapped,
            "degree_of",
            &table,
        )
        .expect_err("a reordered flattening must NOT discharge");
        assert!(
            err.contains("disagrees with the parameter list"),
            "the refusal must name the real cause: {err}"
        );
    }

    /// ALL-OR-NOTHING: one field outside the supported scalar vocabulary
    /// refuses the whole parameter, and therefore the whole mint. Filtering it
    /// out instead would make this side's list disagree with the compiler's.
    #[test]
    fn a_struct_with_a_non_scalar_field_mints_nothing() {
        let fields = vec![
            ("degree".to_string(), trust_types::Ty::u64()),
            ("terms".to_string(), trust_types::Ty::Slice { elem: Box::new(trust_types::Ty::u64()) }),
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
    ///  3. a mixed-domain unary constant (u32 parameter, u64 constant) still
    ///     fails closed — `admit_expr_function` is single-domain.
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

        // (3) MIXED-DOMAIN unary constant fails closed: u32 parameter, u64
        // constant return — outside the single-domain expr fragment.
        let mixed =
            const6_verifiable_function("c6m", 1, trust_types::Ty::Int { width: 32, signed: false });
        let table_m = FacetTable::from_structural_facets([("crate::c6m", true, true, true, true)]);
        let mut env_m = Environment::with_prelude();
        assert!(
            admit_function_into(&mut env_m, &mixed, &table_m).is_none(),
            "a mixed-domain unary constant must decline (fail closed), not mint"
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
        let outcome = check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
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
        let verdict = kernel_prove_ensures_by_defeq(&env, "result == zeroI64()", &[], "zero_i64", &facets);
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
        let outcome = check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
        assert!(!outcome.is_rejected(), "the authored island must register: {outcome:?}");

        let eq_ok_w = island_definition_carriers(&env, "eqOkW").expect("eqOkW has readable carriers");
        assert_eq!(eq_ok_w.params, vec![Carrier::BitVec(64), Carrier::BitVec(128)]);
        assert_eq!(eq_ok_w.ret, Carrier::Bool);

        let zero = island_definition_carriers(&env, "zeroI64").expect("zeroI64 has readable carriers");
        assert_eq!(zero.params, Vec::new());
        assert_eq!(zero.ret, Carrier::BitVec(64));

        let checked =
            island_definition_carriers(&env, "checkedAdd64").expect("checkedAdd64 is readable");
        assert_eq!(checked.params, vec![Carrier::BitVec(64), Carrier::BitVec(64)]);
        assert_eq!(checked.ret, Carrier::Option(Box::new(Carrier::BitVec(64))));

        // `Int` is not a clause carrier, so a definition over it reports
        // NOTHING rather than an approximation.
        assert!(island_definition_carriers(&env, "toInt64").is_none(), "an `Int` codomain is unreadable");
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
        let outcome = check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
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
                trust_spec_elab::admit_signed_constant_function(
                    &mut env, "parked", value, width
                )
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
        let outcome = check_clean_island_with_context(CHECKED_MODEL_ISLAND, &mut env, &mut file_ctx);
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
        assert_eq!(adm.return_domain().cloned(), Some(Domain::Bool), "the decision's codomain is `Bool`");

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
            tc.is_def_eq(&app2("eq_ok_mint", m.clone(), t.clone()), &app2("eqOkW", m.clone(), t.clone())),
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
                    &mut env, "parked", &[i64d.clone(), i128d.clone()], from, to, 0, 1, true,
                )
                .is_err(),
                "({from:?} -> {to:?}) must park"
            );
        }
        // Parameters off their required carriers, the same index on both
        // sides, and an out-of-range index all fail closed.
        for (domains, narrow, wide, why) in [
            (vec![i128d.clone(), i128d.clone()], 0usize, 1usize, "a narrow parameter at the wide carrier"),
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
            ("veripb_core_proved::<i64 as CoeffDomain>::zero", 0i128, &i64_ty,
             trust_spec_elab::MachineSIntWidth::I64),
            ("veripb_core_proved::<i64 as CoeffDomain>::one", 1, &i64_ty,
             trust_spec_elab::MachineSIntWidth::I64),
            ("veripb_core_proved::<i128 as Exact>::zero", 0, &i128_ty,
             trust_spec_elab::MachineSIntWidth::I128),
            ("veripb_core_proved::<i128 as Exact>::one", 1, &i128_ty,
             trust_spec_elab::MachineSIntWidth::I128),
        ] {
            let func = constant_fn(path, value, ty.clone());
            let certified =
                trust_spec_elab::FacetTable::from_structural_facets([(path, true, true, true, true)]);
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
        let certified =
            trust_spec_elab::FacetTable::from_structural_facets([("crate::neg", true, true, true, true)]);
        assert!(admit_function_into(&mut env, &neg, &certified).is_some(), "a negative literal mints");

        // An UNSIGNED return at the identical body shape mints NOTHING: a
        // `ConstValue::Int` at a `uN` carrier has no signed reading, and
        // taking one would give `-1` the value `u64::MAX`.
        let unsigned = constant_fn("crate::u", -1, Ty::Int { width: 64, signed: false });
        let certified_u =
            trust_spec_elab::FacetTable::from_structural_facets([("crate::u", true, true, true, true)]);
        assert!(
            admit_function_into(&mut env_refused, &unsigned, &certified_u).is_none(),
            "a signed literal at an unsigned return must never mint"
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
                        stmt(Place::local(3), Rvalue::Cast(Operand::Copy(Place::local(1)), cast_to)),
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
}
