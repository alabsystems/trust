//! Header-first Clean island checking (Trust I1), on the Clean batch facility.
//!
//! The source-order loop this replaces fed islands to the kernel one text at a
//! time, so a declaration could only mention what an *earlier* island had
//! already registered. Rust does not work that way — items resolve from a
//! whole-crate symbol table — and Clean is the other authoritative language, so
//! the two spellings must not disagree about which names exist.
//!
//! # Where the semantics live
//!
//! Header-first elaboration is **not implemented here**. It is
//! [`clean_elab::module_batch::elaborate_module`], in the language repo, which
//! collects every declaration header across every unit before any body is
//! elaborated, with a per-declaration lexical snapshot, and publishes through a
//! separate authoritative environment that has never held a header. A second
//! implementation in this crate would be a second answer to "what does this
//! program mean", and the compiler is not allowed to have one: the elaborated
//! Clean goal is whatever the Clean elaborator says it is.
//!
//! What this module owns is the **island framing** that Clean deliberately does
//! not acquire:
//!
//! * one [`CleanIslandOutcome`] per island, with ISLAND-RELATIVE byte offsets,
//!   so `trust_verify.rs` can keep remapping them onto the enclosing rustc
//!   `content_span`;
//! * the Trust-side strict authority policy (no axioms, no valueless opaques,
//!   no `unsafe` / `partial`, no trust debt, no declaration into the
//!   `trust_import_*` namespace, and a `Certified` certification audit for
//!   every proof judgment) — Clean will happily register an axiom, Trust will
//!   not accept one;
//! * turning a [`BatchRejection`] cycle into the span-bearing shape the
//!   compiler's two-ended cycle diagnostic needs, while carrying Clean's own
//!   rendering — which names the fix WITH OPTIONS — through as the note.
//!
//! # Why not "retry whatever failed"
//!
//! Retrying unresolved declarations until a round makes no progress delivers
//! source-order independence's *purpose* without its *meaning*, and it is
//! unsound. Elaboration is not monotone: `elab(source, partial_env)` can differ
//! from `elab(source, full_env)`. An earlier island with `open Imported` and
//! `def early : Nat := pick` succeeds on the first round as `Imported.pick` and
//! is never retried — but if a later island declares `M.pick`, current-namespace
//! resolution beats an opened namespace, so `early` *means* `M.pick`. The
//! retry loop's defect is in the declarations that SUCCEED, not the ones that
//! fail, and no classifier of retryable errors can repair a success it never
//! revisits. That is first-successful-interpretation-wins — a different
//! language — not source-order independence.
//!
//! # Fail-closed
//!
//! A batch that did not commit registers nothing and must still produce at
//! least one diagnostic; [`check_islands_batched`] asserts that rather than
//! assuming it. A rejection anywhere taints the session, so
//! `CleanIslandSession::environment` returns `None` and every citation degrades
//! to `SessionTainted`.

use clean_elab::FileContext;
use clean_elab::module_batch::{
    self, BatchOptions, BatchRejection, DeclStatus, PublishAuditIssue, Site, SourceUnit, UnitId,
};
use clean_kernel::{Environment, Name};
use clean_parser::SurfaceDecl;

use crate::clean_island::{
    CleanIslandDeclaration, CleanIslandDiagnostic, CleanIslandOutcome, point_diagnostic_span,
    reserved_namespace_error, standin_imports_in, strict_registered_declaration_policy_error,
    strict_registered_pre_reference_error,
};

/// One declaration on a dependency cycle, with the island it was written in.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CleanIslandCycleSite {
    /// Index into the `sources` slice that was checked.
    pub island: usize,
    /// Byte offsets into THAT island's text.
    pub start: usize,
    pub end: usize,
    /// The declaration's name, as the scheduler knows it.
    pub name: String,
}

/// A dependency cycle among island declarations. Detected before any body is
/// registered, so it is reported instead of being discovered by the kernel
/// diverging.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CleanIslandCycle {
    /// The members, rotated so the earliest-authored one leads.
    pub sites: Vec<CleanIslandCycleSite>,
    /// Clean's own rendering of the refusal. It names the ways forward, in
    /// order of preference, and says what each one costs — the compiler emits
    /// it verbatim as a note rather than paraphrasing it, so the options do not
    /// drift between the two repos.
    pub message: String,
}

impl CleanIslandCycle {
    /// The cycle rendered as `a -> b -> a`, for a diagnostic message.
    #[must_use]
    pub fn render(&self) -> String {
        let mut names: Vec<&str> = self.sites.iter().map(|s| s.name.as_str()).collect();
        if let Some(first) = names.first().copied() {
            names.push(first);
        }
        names.join(" -> ")
    }
}

/// The result of checking every island in a crate together.
#[derive(Debug, Clone, Default)]
pub struct CleanIslandBatch {
    /// One outcome per input island, in input order, with island-relative
    /// byte offsets — so the caller's existing span arithmetic is unchanged.
    pub outcomes: Vec<CleanIslandOutcome>,
    /// Dependency cycles. Non-empty ⇒ NOTHING from the batch was registered.
    pub cycles: Vec<CleanIslandCycle>,
    /// Optional independent kernel-roster measurement, never producer authority.
    pub census: Option<crate::clean_census::LeanKernelRoster>,
}

impl CleanIslandBatch {
    pub(crate) fn has_anonymous_judgments(&self) -> bool {
        self.outcomes.iter().any(|outcome| outcome.anonymous_judgments != 0)
    }

    #[must_use]
    pub fn is_rejected(&self) -> bool {
        !self.cycles.is_empty() || self.outcomes.iter().any(CleanIslandOutcome::is_rejected)
    }
}

/// Check every island of a crate as ONE header-first Clean module.
pub(crate) fn check_islands_batched(
    env: &mut Environment,
    file_ctx: &mut FileContext,
    sources: &[&str],
) -> CleanIslandBatch {
    check_islands_batched_impl(env, file_ctx, sources, &[], false, None)
}

/// [`check_islands_batched`] with a PARSER PRELUDE per island (empty for
/// none): already-checked Clean source — the served modules of Trust's
/// temporal vocabulary an island imports — parsed in front of that island so
/// their parse-time notation (`□`, `◇`, `~>`, `⊨`) is in scope. Only the
/// island's own declarations are scheduled and elaborated, and every span is
/// reported relative to the island's text. (The optional census is not asked
/// for on this path: its roster attribution reads island-relative spans.)
pub(crate) fn check_islands_batched_with_preludes(
    env: &mut Environment,
    file_ctx: &mut FileContext,
    sources: &[&str],
    parser_preludes: &[String],
) -> CleanIslandBatch {
    check_islands_batched_impl(env, file_ctx, sources, parser_preludes, false, None)
}

pub(crate) fn check_islands_batched_with_census(
    env: &mut Environment,
    file_ctx: &mut FileContext,
    sources: &[&str],
) -> CleanIslandBatch {
    check_islands_batched_impl(env, file_ctx, sources, &[], true, None)
}

/// The opt-in source path retains its genuine producer baseline separately.
/// It closes every actual eager addition and original anonymous judgment;
/// ordinary Rust islands keep their existing whole-base reference entry.
pub(crate) fn check_pinned_sources_batched(
    env: &mut Environment,
    file_ctx: &mut FileContext,
    sources: &[&str],
    parser_preludes: &[String],
    collect_census: bool,
    baseline: &std::collections::BTreeSet<Name>,
) -> CleanIslandBatch {
    check_islands_batched_impl(
        env,
        file_ctx,
        sources,
        parser_preludes,
        collect_census,
        Some(baseline),
    )
}

enum BatchReference<'a> {
    Island(crate::reference_mint::IslandReference),
    PinnedSource(crate::lean_source_batch::pinned_reference::PinnedSourceReference<'a>),
}

impl BatchReference<'_> {
    fn base_error(&self) -> Option<String> {
        match self {
            Self::Island(reference) => reference.base_error(),
            Self::PinnedSource(reference) => reference.base_error(),
        }
    }

    fn check_registered(&self, name: &Name) -> Result<(), String> {
        match self {
            Self::Island(reference) => reference.check_registered(name).map(|_| ()),
            Self::PinnedSource(reference) => reference.check_registered(name),
        }
    }

    fn check_judgment(
        &self,
        goal: &clean_kernel::Expr,
        value: &clean_kernel::Expr,
    ) -> Result<(), String> {
        match self {
            Self::Island(reference) => reference.check_judgment(goal, value).map(|_| ()),
            Self::PinnedSource(reference) => reference.check_judgment(goal, value),
        }
    }
}

fn check_islands_batched_impl(
    env: &mut Environment,
    file_ctx: &mut FileContext,
    sources: &[&str],
    parser_preludes: &[String],
    collect_census: bool,
    source_baseline: Option<&std::collections::BTreeSet<Name>>,
) -> CleanIslandBatch {
    let before = collect_census.then(|| crate::clean_census::owned_names(env));
    let mut outcomes = vec![CleanIslandOutcome::default(); sources.len()];

    // Island framing is this crate's job, not Clean's: parse each island on its
    // own so a parse failure is reported against the island that contains it
    // and the rest of the crate is still checked.
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let mut parsed: Vec<(usize, Vec<SurfaceDecl>)> = Vec::new();
    // Where each island's own text starts in what was parsed (its parser
    // prelude's length plus a newline; 0 without one): every span Clean
    // reports for that island is shifted back by it.
    let mut bases = vec![0usize; sources.len()];
    for (island, source) in sources.iter().enumerate() {
        let prelude = parser_preludes.get(island).map_or("", String::as_str);
        let combined;
        let text = if prelude.is_empty() {
            *source
        } else {
            combined = format!("{prelude}\n{source}");
            bases[island] = prelude.len() + 1;
            combined.as_str()
        };
        let base = bases[island];
        match clean_parser::parse_file_with_tactics_located(text, &patterns) {
            Ok(decls) => parsed.push((
                island,
                decls.into_iter().filter(|decl| decl.span().start >= base).collect(),
            )),
            Err(err) => {
                let (start, end) =
                    point_diagnostic_span(source, err.byte_offset.saturating_sub(base));
                outcomes[island].errors.push(CleanIslandDiagnostic {
                    start,
                    end,
                    message: format!("Clean island failed to parse: {err}"),
                });
            }
        }
    }

    let units: Vec<SourceUnit<'_>> = parsed
        .iter()
        .map(|(island, decls)| SourceUnit {
            // The island index IS the unit id, so every site Clean reports maps
            // straight back to the island whose text it points into.
            id: UnitId(u32::try_from(*island).unwrap_or(u32::MAX)),
            decls,
        })
        .collect();

    if units.is_empty() {
        let rejected = outcomes.iter().any(CleanIslandOutcome::is_rejected);
        let census = before.as_ref().map(|before| {
            crate::clean_census::LeanKernelRoster::capture(before, env, sources, None, rejected)
        });
        return CleanIslandBatch { outcomes, cycles: Vec::new(), census };
    }

    // `BatchOptions::islands()`: a refusal commits NOTHING (an island either
    // means what it says or it is not there) and header agreement is enforced,
    // so no declaration is elaborated against a signature the kernel does not
    // hold.
    let module = module_batch::elaborate_module(env, file_ctx, &units, BatchOptions::islands());

    let mut cycles = Vec::new();
    // `all_rejections` unions the batch-level list with the per-declaration
    // ones. `publish` records some refusals in BOTH, so identical diagnostics
    // are dropped rather than emitted twice; taking the union is the
    // fail-closed direction, since a refusal recorded in only one place must
    // still reach the author.
    for rejection in module.all_rejections() {
        route_rejection(rejection, sources, &bases, &mut outcomes, &mut cycles);
    }

    for decl in &module.decls {
        let island = decl.unit.0 as usize;
        let Some(source) = sources.get(island) else { continue };
        // Command nodes (including `example` and `#guard`) register no name.
        // Clean carries their original checked judgments, not re-elaborated text.
        outcomes[island].anonymous_judgments += decl.checked_judgments.len();
        match &decl.status {
            DeclStatus::Registered => {
                // Registration means the Clean kernel accepted it. Trust's
                // island policy is STRICTER than that, and it is applied to the
                // constant the kernel actually stored.
                let checked: Vec<Name> = match &decl.name {
                    Some(name) => vec![name.clone()],
                    None => decl.introduces.iter().cloned().collect(),
                };
                let mut refused = false;
                let mut messages: Vec<String> = checked
                    .iter()
                    .filter_map(|name| {
                        if source_baseline.is_some() {
                            strict_registered_declaration_policy_error(env, name)
                        } else {
                            strict_registered_pre_reference_error(env, name)
                        }
                    })
                    .collect();
                // TG16: the compiler's reserved namespaces are refused for EVERY constant the
                // declaration introduced (an inductive's constructors, recursors and
                // projections, a mutual block's members), not only its head name. The
                // certification grade stays per head name.
                if messages.is_empty() && decl.name.is_some() {
                    messages.extend(decl.introduces.iter().find_map(reserved_namespace_error));
                }
                for message in messages {
                    push_unique(
                        &mut outcomes[island],
                        CleanIslandDiagnostic {
                            start: decl.span.start.saturating_sub(bases[island]).min(source.len()),
                            end: decl.span.end.saturating_sub(bases[island]).min(source.len()),
                            message,
                        },
                    );
                    refused = true;
                }
                if !refused {
                    if let Some(name) = &decl.name {
                        outcomes[island].registered.push(name.to_string());
                    }
                }
            }
            // Every other status is either already covered by a rejection
            // routed above (`Refused`, and `NoHeader` for a node the scheduler
            // could not reach) or registers nothing by design
            // (`LexicalOrCommand`).
            DeclStatus::Refused(_) | DeclStatus::NoHeader { .. } | DeclStatus::LexicalOrCommand => {
            }
        }
    }

    let mut batch = CleanIslandBatch { outcomes, cycles, census: None };

    // Fail-closed tripwire. `committed == false` means the caller's environment
    // is byte-identical to what it was, so the crate holds nothing from these
    // islands; that MUST be a build error, never a silent no-op. It is
    // unreachable — Clean does not decline to commit without a rejection — so
    // if a future Clean release adds a reason, this fails loudly instead of
    // accepting a crate whose Clean half was dropped.
    if !module.committed && !batch.is_rejected() {
        if let Some(first) = batch.outcomes.first_mut() {
            first.errors.push(CleanIslandDiagnostic {
                start: 0,
                end: sources.first().map_or(0, |source| source.len().min(1)),
                message: format!(
                    "{UNRECOVERABLE_BATCH_PREFIX} Clean island batch was not committed and \
                     reported no reason; nothing was registered, so the crate is refused \
                     rather than built against an empty Clean environment"
                ),
            });
        }
    }
    debug_assert!(
        module.committed || batch.is_rejected(),
        "an uncommitted Clean island batch produced no diagnostic"
    );
    // The acceptance gate runs only for an otherwise successful committed
    // batch, exactly as the sequential path does. A rejected batch provides
    // progress diagnostics, not authority: provisional headers from a cycle or
    // failed body must not turn every independent sibling into a fresh refusal.
    // Transactional import recovery reruns ALL survivors against its restored
    // base; that final batch cannot succeed without passing this gate.
    if !batch.is_rejected() {
        let reference = if let Some(baseline) = source_baseline {
            let current = crate::clean_census::owned_names(env);
            let owned = current.difference(baseline).cloned().collect();
            // This denominator comes from actual kernel records, independently
            // of the lossy registered-head list and optional diagnostic census.
            for name in &owned {
                if let Some(error) = strict_registered_declaration_policy_error(env, name) {
                    if let Some(outcome) = batch.outcomes.first_mut() {
                        outcome.errors.push(CleanIslandDiagnostic {
                            start: 0, end: 0,
                            message: format!("{UNRECOVERABLE_BATCH_PREFIX} source policy refused `{name}`: {error}"),
                        });
                    }
                }
            }
            let judgments: Vec<_> = module
                .decls
                .iter()
                .flat_map(|decl| decl.checked_judgments.iter())
                .map(|judgment| (&judgment.type_, &judgment.value))
                .collect();
            BatchReference::PinnedSource(
                crate::lean_source_batch::pinned_reference::PinnedSourceReference::new(
                    env, &owned, &judgments,
                ),
            )
        } else {
            BatchReference::Island(crate::reference_mint::IslandReference::new(env))
        };
        // Even an import-only batch must not silently accept an ineligible
        // base. Such a whole-base refusal cannot be attributed to one proof;
        // recovery must not turn it into an accepted partial environment.
        if let Some(error) = reference.base_error() {
            if let Some(outcome) = batch.outcomes.first_mut() {
                outcome.errors.push(CleanIslandDiagnostic {
                    start: 0,
                    end: 0,
                    message: format!(
                        "{UNRECOVERABLE_BATCH_PREFIX} reference base refused: {error}"
                    ),
                });
            }
        }
        for decl in &module.decls {
            let island = decl.unit.0 as usize;
            let Some(source) = sources.get(island) else { continue };
            let mut errors = Vec::new();
            if matches!(decl.status, DeclStatus::Registered) {
                let names: Vec<&Name> = match &decl.name {
                    Some(name) => vec![name],
                    None => decl.introduces.iter().collect(),
                };
                for name in names {
                    if let Err(error) = reference.check_registered(name) {
                        errors.push(format!("Clean island declaration `{name}` failed the reference kernel recheck: {error}"));
                    }
                }
            }
            for judgment in &decl.checked_judgments {
                if let Err(error) = reference.check_judgment(&judgment.type_, &judgment.value) {
                    errors.push(format!("Clean island anonymous judgment failed the reference kernel recheck: {error}"));
                }
            }
            if !errors.is_empty() {
                if let Some(name) = &decl.name {
                    batch.outcomes[island]
                        .registered
                        .retain(|registered| *registered != name.to_string());
                }
            }
            for message in errors {
                push_unique(
                    &mut batch.outcomes[island],
                    CleanIslandDiagnostic {
                        start: decl.span.start.saturating_sub(bases[island]).min(source.len()),
                        end: decl.span.end.saturating_sub(bases[island]).min(source.len()),
                        message,
                    },
                );
            }
        }
    }
    // Disclose, per ACCEPTED island, every `import` Clean's built-in prelude
    // stand-in served (`CleanIslandStandinImport`). Placed after every refusal
    // — routed rejections, the strict registered-policy audit and the tripwire
    // above — has landed, so an island that reports an error reports no
    // stand-in: it reports no green for the disclosure to qualify. An accepted
    // island beside a rejected sibling still discloses, because its
    // registered-declaration note is still rendered.
    for (island, decls) in &parsed {
        if !batch.outcomes[*island].is_rejected() {
            batch.outcomes[*island].standin_imports = standin_imports_in(decls, file_ctx);
        }
    }
    record_declarations(&mut batch, &module, &parsed, sources, &bases);
    batch.census = before.as_ref().map(|before| {
        crate::clean_census::LeanKernelRoster::capture(
            before,
            env,
            sources,
            Some(&module),
            batch.is_rejected(),
        )
    });
    batch
}

/// Fill each parsed island's [`CleanIslandOutcome::declarations`] from Clean's
/// own per-command outcomes, after every refusal has landed: the spans and
/// canonical names are Clean's, never a second reading of the source.
fn record_declarations(
    batch: &mut CleanIslandBatch,
    module: &module_batch::ModuleOutcome,
    parsed: &[(usize, Vec<SurfaceDecl>)],
    sources: &[&str],
    bases: &[usize],
) {
    // The declarations the publish audit names: it refuses the whole batch,
    // but it says which declaration reached the marker.
    let mut audited: Vec<&Name> = Vec::new();
    for rejection in &module.rejections {
        if let BatchRejection::PublishAudit { issues, .. } = rejection {
            for issue in issues {
                match issue {
                    PublishAuditIssue::TrustDebt { name, .. } => audited.push(name),
                    PublishAuditIssue::StagedHeaderInPublishEnv { names, .. } => {
                        audited.extend(names.iter());
                    }
                    _ => {}
                }
            }
        }
    }
    for (island, _) in parsed {
        let island = *island;
        let (Some(source), Some(&base)) = (sources.get(island), bases.get(island)) else {
            continue;
        };
        let outcome = &batch.outcomes[island];
        let cycle_starts: Vec<usize> = batch
            .cycles
            .iter()
            .flat_map(|cycle| &cycle.sites)
            .filter(|site| site.island == island)
            .map(|site| site.start)
            .collect();
        let declarations = module
            .decls
            .iter()
            .filter(|decl| decl.unit.0 as usize == island && decl.span.start >= base)
            .map(|decl| {
                let start = (decl.span.start - base).min(source.len());
                let end = decl.span.end.saturating_sub(base).min(source.len()).max(start);
                // Clean's span is the keyword (`CleanIslandDeclaration::start`).
                let inside = |at: usize| at >= start && (at < end || at == start);
                let named = |name: &Name| {
                    decl.name.as_ref() == Some(name) || decl.introduces.contains(name)
                };
                let refused = matches!(decl.status, DeclStatus::Refused(_))
                    || audited.iter().any(|name| named(name))
                    || cycle_starts.iter().any(|&at| inside(at))
                    || outcome
                        .errors
                        .iter()
                        .any(|error| !error.is_whole_batch() && inside(error.start));
                CleanIslandDeclaration {
                    start,
                    end,
                    name: decl.name.as_ref().map(ToString::to_string),
                    refused,
                }
            })
            .collect();
        batch.outcomes[island].declarations = Some(declarations);
    }
}

/// Route one Clean refusal to the island it belongs to.
///
/// Cycles become [`CleanIslandCycle`]s, because the compiler renders those with
/// a span at every member so the author sees both ends of a cross-island cycle.
/// Everything else becomes an ordinary island diagnostic at the site Clean
/// reported, carrying Clean's own rendering — which names the fix WITH OPTIONS
/// — rather than a paraphrase of it.
fn route_rejection(
    rejection: &BatchRejection,
    sources: &[&str],
    bases: &[usize],
    outcomes: &mut [CleanIslandOutcome],
    cycles: &mut Vec<CleanIslandCycle>,
) {
    let message = without_cli_severity(module_batch::render::rejection(rejection));
    match rejection {
        BatchRejection::ProofCycle { witness, names }
        | BatchRejection::SignatureCycle { witness, names }
        | BatchRejection::UnsupportedScc { witness, names, .. } => {
            let sites = cycle_sites(witness, names, sources, bases);
            if sites.is_empty() {
                return;
            }
            let cycle = CleanIslandCycle { sites, message };
            if !cycles.iter().any(|existing| existing.message == cycle.message) {
                cycles.push(cycle);
            }
        }
        BatchRejection::NameCollision { first, second, .. } => {
            // Both ends, so the author is not sent to one arbitrary half of a
            // collision that spans two islands.
            for site in [first, second] {
                emit_at(*site, &message, sources, bases, outcomes);
            }
        }
        BatchRejection::HeaderTypeDivergence { site, .. }
        | BatchRejection::StagedReference { site, .. }
        | BatchRejection::Elaboration { site, .. } => {
            emit_at(*site, &message, sources, bases, outcomes);
        }
        // No site: a fixed-point failure is a property of the whole index, and
        // a publish-audit refusal is a property of the whole environment.
        BatchRejection::HeaderNotStable { .. } | BatchRejection::PublishAudit { .. } => {
            emit_whole_batch(&message, sources, outcomes);
        }
        // `BatchRejection` is `#[non_exhaustive]`. A refusal this build does not
        // recognize is still a refusal: report it against the batch rather than
        // dropping it, so a Clean upgrade cannot silently open a hole.
        _ => emit_whole_batch(&message, sources, outcomes),
    }
}

/// Clean's rejection rendering is its CLI text, which opens with Clean's own
/// `error: ` severity tag. Every consumer of a routed message is a compiler
/// diagnostic that states its own severity (an island error, or a note on the
/// cycle error), so carrying the tag printed `error: error: …` and
/// `note: error: …` (CLEAN-ISLAND-DOUBLED-SEVERITY-1). Only that leading tag
/// goes; Clean's wording, notes and options are carried unchanged.
fn without_cli_severity(rendered: String) -> String {
    match rendered.strip_prefix("error: ") {
        Some(body) => body.to_string(),
        None => rendered,
    }
}

/// Push a diagnostic at a Clean [`Site`], clamped to that island's text.
fn emit_at(
    site: Site,
    message: &str,
    sources: &[&str],
    bases: &[usize],
    outcomes: &mut [CleanIslandOutcome],
) {
    let island = site.unit.0 as usize;
    let base = bases.get(island).copied().unwrap_or(0);
    let Some(len) = sources.get(island).map(|source| source.len()) else {
        // A site outside the islands this call was given cannot be pointed at,
        // but it is still a refusal — report it against the batch.
        emit_whole_batch(message, sources, outcomes);
        return;
    };
    let Some(outcome) = outcomes.get_mut(island) else { return };
    push_unique(
        outcome,
        CleanIslandDiagnostic {
            start: site.span.start.saturating_sub(base).min(len),
            end: site.span.end.saturating_sub(base).min(len),
            message: message.to_string(),
        },
    );
}

/// A whole-environment/header-index refusal cannot be isolated as one bad
/// import unit. Share this tag with the transactional recovery guard.
pub(crate) const UNRECOVERABLE_BATCH_PREFIX: &str =
    "Clean island batch has no source-local recovery boundary:";

/// Push a diagnostic that belongs to no single declaration onto the first
/// island, which is where the batch begins.
fn emit_whole_batch(message: &str, sources: &[&str], outcomes: &mut [CleanIslandOutcome]) {
    let Some(outcome) = outcomes.first_mut() else { return };
    let len = sources.first().map_or(0, |source| source.len());
    push_unique(
        outcome,
        CleanIslandDiagnostic {
            start: 0,
            end: len.min(1),
            message: format!("{UNRECOVERABLE_BATCH_PREFIX} {message}"),
        },
    );
}

fn push_unique(outcome: &mut CleanIslandOutcome, diagnostic: CleanIslandDiagnostic) {
    if outcome.errors.iter().any(|existing| {
        existing.start == diagnostic.start
            && existing.end == diagnostic.end
            && existing.message == diagnostic.message
    }) {
        return;
    }
    outcome.errors.push(diagnostic);
}

/// Normalize a cycle witness into island-relative sites.
///
/// Clean's witness is a walk that revisits its entry point, so the same member
/// can appear twice; and the walk starts wherever the search happened to begin,
/// which is not necessarily where the author would look first. Collapsing the
/// repeat and rotating to the earliest-authored member makes the rendered cycle
/// a function of the program rather than of the search, which is what a
/// diagnostic pinned by a test needs.
fn cycle_sites(
    witness: &[Site],
    names: &[Name],
    sources: &[&str],
    bases: &[usize],
) -> Vec<CleanIslandCycleSite> {
    let mut walk: Vec<(Site, String)> =
        witness.iter().copied().zip(names.iter().map(ToString::to_string)).collect();
    walk.dedup_by(|later, earlier| later.1 == earlier.1);
    if walk.len() > 1 && walk.first().map(|entry| &entry.1) == walk.last().map(|entry| &entry.1) {
        walk.pop();
    }
    if let Some(lead) = walk
        .iter()
        .enumerate()
        .min_by_key(|(_, (site, _))| (site.unit.0, site.span.start, site.span.end))
        .map(|(index, _)| index)
    {
        walk.rotate_left(lead);
    }
    walk.into_iter()
        .map(|(site, name)| {
            let island = site.unit.0 as usize;
            let len = sources.get(island).map_or(0, |source| source.len());
            let base = bases.get(island).copied().unwrap_or(0);
            CleanIslandCycleSite {
                island,
                start: site.span.start.saturating_sub(base).min(len),
                end: site.span.end.saturating_sub(base).min(len),
                name,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::clean_island::CleanIslandSession;

    /// GREEN-THAT-LIES (measured 2026-09-16, `clean { import Mathlib … }`
    /// printed only "kernel-checked"): an ACCEPTED island whose `import` the
    /// built-in prelude stand-in served says so on its outcome, at the
    /// `import` command's own span, and ONLY on the island that wrote it.
    #[test]
    fn test_check_all_discloses_a_prelude_stand_in_import_on_the_accepted_island() {
        // `Lean`, not `Mathlib`: Mathlib's stand-in installs a structural
        // `IsClosed` and is an ineligible reference base since fa2aed4b4aa
        // (tests/ui/trust/tg8_reference_base_standin_refused.rs pins that
        // refusal). The disclosure under test is the same for any stand-in.
        let importing = "import Lean\ndef six : UInt64 := 6\n";
        let plain = "def seven : UInt64 := 7\n";

        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[importing, plain]);

        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let disclosed = &batch.outcomes[0].standin_imports;
        assert_eq!(disclosed.len(), 1, "{disclosed:?}");
        assert_eq!(disclosed[0].module, "Lean");
        assert!(
            importing[disclosed[0].start.min(importing.len())..].starts_with("import"),
            "the disclosure must point at the `import` command: {disclosed:?}"
        );
        assert!(batch.outcomes[0].registered.contains(&"six".to_string()));
        assert!(
            batch.outcomes[1].standin_imports.is_empty(),
            "an island that imports nothing disclosed a stand-in: {:?}",
            batch.outcomes[1].standin_imports
        );
        // The v7/D3 shape: what was substituted, and the ways forward.
        let note = disclosed[0].disclosure();
        assert!(note.contains("`import Lean`") && note.contains("NOT by the library"), "{note}");
        let options = disclosed[0].options();
        assert!(options.starts_with("options:\n- "), "{options}");
        assert!(options.matches("\n- ").count() >= 2, "one option is an ultimatum: {options}");

        // The measured island itself (TG8, 6411a62394): refused, and a refused
        // island reports no green, so it discloses nothing.
        let mut session = CleanIslandSession::new();
        let measured = session.check_all(&["import Mathlib\ndef six : UInt64 := 6\n"]);
        assert!(
            measured.is_rejected(),
            "the Mathlib stand-in was ACCEPTED: {:?}",
            measured.outcomes
        );
        assert!(
            measured.outcomes[0]
                .errors
                .iter()
                .any(|e| e.message.contains("reference base refused")),
            "{:?}",
            measured.outcomes[0].errors
        );
        assert!(measured.outcomes[0].standin_imports.is_empty());
    }

    /// Each island lists its top-level commands with Clean's own spans and
    /// canonical names (namespaces applied, `set_option … in` seen through),
    /// and a command is marked refused only when something names it: the
    /// publish audit's `sorry` finding names its declaration, while the
    /// whole-batch diagnostic it produces (placed at byte 0) marks nothing.
    #[test]
    fn test_check_all_lists_each_command_and_marks_only_the_refused_one() {
        let accepted = "namespace N\ntheorem a : 1 = 1 := rfl\nend N\n\
                        set_option pp.all true in\ntheorem c : 3 = 3 := rfl\n\
                        @[simp] def d (n : Nat) : Nat := n + n\nexample : 2 = 2 := by rfl\n\
                        #check d\ninstance : Inhabited Nat := ⟨0⟩\n\
                        inductive Color\n| red\n| green\n";
        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[accepted]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let listed = batch.outcomes[0].declarations.clone().expect("a parsed island");
        let named: Vec<&str> = listed.iter().filter_map(|d| d.name.as_deref()).collect();
        assert!(named.contains(&"N.a") && named.contains(&"c"), "{listed:?}");
        assert!(listed.iter().all(|d| !d.refused), "{listed:?}");
        // Clean's span of a command is its keyword, through `set_option … in`
        // and attributes; `namespace`, `end` and `set_option` are not listed.
        let c = listed.iter().find(|d| d.name.as_deref() == Some("c")).expect("c");
        assert_eq!(&accepted[c.start..c.end], "theorem", "{c:?}");
        let d = listed.iter().find(|d| d.name.as_deref() == Some("d")).expect("d");
        assert_eq!(&accepted[d.start..d.end], "def", "{d:?}");
        let keywords: Vec<&str> = listed.iter().map(|d| &accepted[d.start..d.end]).collect();
        assert_eq!(
            keywords,
            ["theorem", "theorem", "def", "example", "#", "instance", "inductive"]
        );

        // An error inside a proof is placed at its declaration's keyword, so
        // each broken declaration, and only it, is refused.
        let broken = "theorem a : 1 = 1 := rfl\ntheorem b : 2 = 3 := by\n  simp\n\
                      theorem e : 1 = 1 := Nat.le_refl 3\ntheorem f : 1 = 1 := by\n  \
                      exact (rfl : 2 = 2)\n";
        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[broken]);
        let refused: Vec<(Option<String>, bool)> = batch.outcomes[0]
            .declarations
            .clone()
            .expect("a parsed island")
            .into_iter()
            .map(|d| (d.name, d.refused))
            .collect();
        let expected = [("a", false), ("b", true), ("e", true), ("f", true)]
            .map(|(name, refused)| (Some(name.to_string()), refused));
        assert_eq!(refused, expected);

        // `ok` first, so the whole-batch diagnostic at byte 0 lies in its span.
        let sorry = "theorem ok : 1 = 1 := rfl\ntheorem s : 2 = 2 := sorry\n";
        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[sorry]);
        assert!(batch.is_rejected(), "a sorry was accepted: {:?}", batch.outcomes);
        let listed = batch.outcomes[0].declarations.clone().expect("a parsed island");
        let refused: Vec<(Option<&str>, bool)> =
            listed.iter().map(|d| (d.name.as_deref(), d.refused)).collect();
        assert_eq!(refused, [(Some("ok"), false), (Some("s"), true)], "{listed:?}");

        // An island that does not parse lists nothing: its commands are unknown.
        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&["theorem broken : := (\n"]);
        assert!(batch.is_rejected());
        assert_eq!(batch.outcomes[0].declarations, None);
    }

    /// CLOSE NEGATIVE TWIN. A dotted import no provider names verbatim is
    /// still REFUSED — the disclosure is not an acceptance path — and a
    /// refused island discloses nothing, because it reports no green.
    #[test]
    fn test_check_all_still_refuses_an_unresolved_import_and_discloses_nothing_for_it() {
        let importing = "import Mathlib.Utterly.Fake.Nonsense\ndef six : UInt64 := 6\n";

        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[importing]);

        assert!(batch.is_rejected(), "an unresolvable import was ACCEPTED: {:?}", batch.outcomes);
        assert!(
            batch.outcomes[0].errors.iter().any(|e| e.message.contains("unresolved import")),
            "{:?}",
            batch.outcomes[0].errors
        );
        assert!(batch.outcomes[0].standin_imports.is_empty());
        // (`registered` is deliberately not asserted empty: the batch reports a
        // declaration's per-declaration status even when the refusal commits
        // nothing, and no renderer prints `registered` for a rejected island.)
        assert!(session.environment().is_none(), "a rejected batch must taint the session");
    }

    /// THE RESOLVER SEAM'S CASE. When a SIBLING island is rejected the batch is
    /// rejected, the resolver reports it, and the build never reaches the verify
    /// pass — yet the resolver still renders the green of each island that was
    /// individually accepted (measured at HEAD 9b4c6b3ab). So the accepted
    /// island must carry its disclosure on a REJECTED batch too, and the
    /// rejected sibling must carry none.
    #[test]
    fn test_check_all_discloses_on_the_accepted_island_of_a_rejected_batch() {
        let importing = "import Mathlib\ndef six : UInt64 := 6\n";
        let broken = "def bad : UInt64 := no_such_name\n";

        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[importing, broken]);

        assert!(batch.is_rejected(), "{:?}", batch.outcomes);
        assert!(!batch.outcomes[0].is_rejected(), "{:?}", batch.outcomes[0].errors);
        let modules: Vec<&str> =
            batch.outcomes[0].standin_imports.iter().map(|i| i.module.as_str()).collect();
        assert_eq!(modules, ["Mathlib"]);
        assert!(batch.outcomes[1].is_rejected());
        assert!(batch.outcomes[1].standin_imports.is_empty());
    }

    /// CONTROL: a module this run elaborates from source (the `.lean` front
    /// door's sibling operand) is NOT a stand-in, so marking it removes it
    /// from the disclosure while `Lean` beside it stays disclosed. Without
    /// this the disclosure would cry wolf on every sibling import.
    #[test]
    fn test_check_all_does_not_disclose_an_import_satisfied_from_source() {
        let main = "import Helper\nimport Lean\ndef uses : UInt64 := helper_six\n";
        let helper = "def helper_six : UInt64 := 6\n";

        let mut session = CleanIslandSession::new();
        session.mark_import_satisfied_from_source(&clean_kernel::Name::from_string("Helper"));
        let batch = session.check_all(&[main, helper]);

        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let modules: Vec<&str> =
            batch.outcomes[0].standin_imports.iter().map(|i| i.module.as_str()).collect();
        assert_eq!(modules, ["Lean"]);
    }

    /// The sequential checker and the header-first batch disclose identically,
    /// so callers cannot disagree about the same import. Deferred imports use
    /// a transactional singleton batch (TG14).
    #[test]
    fn test_sequential_check_discloses_the_same_stand_in_import() {
        let mut session = CleanIslandSession::new();
        let accepted = session.check("import Lean\ndef six : UInt64 := 6\n");
        assert!(!accepted.is_rejected(), "{:?}", accepted.errors);
        let modules: Vec<&str> =
            accepted.standin_imports.iter().map(|i| i.module.as_str()).collect();
        assert_eq!(modules, ["Lean"]);

        let mut session = CleanIslandSession::new();
        let refused = session.check("import Lean\ndef bad : UInt64 := no_such_name\n");
        assert!(refused.is_rejected());
        assert!(refused.standin_imports.is_empty(), "{:?}", refused.standin_imports);
    }

    /// SILENT-PRECEDENCE HAZARD (probe 16c): the question the mint asks before
    /// it warns that an island's `inc` means another module's `def inc` and not
    /// the sibling Rust `fn inc` — did a declaration of THAT island use the
    /// name? Answered from the kernel's own terms.
    #[test]
    fn test_island_declarations_naming_finds_direct_uses_and_only_those() {
        let other_module = "def inc (x : UInt64) : UInt64 := x + 2\n";
        let root = "def twice_inc (x : UInt64) : UInt64 := inc (inc x)\n\
                    def unrelated (x : UInt64) : UInt64 := x + 1\n";

        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[other_module, root]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let env = session.environment().expect("an accepted batch leaves an environment");

        let users = crate::clean_island::island_declarations_naming(
            env,
            &batch.outcomes[1].registered,
            "inc",
        );
        assert_eq!(users, ["twice_inc"], "registered: {:?}", batch.outcomes[1].registered);

        // NEGATIVE TWIN: the declaring island does not "use" its own name, and
        // a name nobody wrote is used by nobody — no warning without a use.
        assert!(
            crate::clean_island::island_declarations_naming(
                env,
                &batch.outcomes[0].registered,
                "inc"
            )
            .is_empty()
        );
        assert!(
            crate::clean_island::island_declarations_naming(
                env,
                &batch.outcomes[1].registered,
                "dec"
            )
            .is_empty()
        );
    }

    /// The I1 acceptance shape: an EARLIER island names a `def` and a `theorem`
    /// that a LATER island declares. Source order must not decide whether this
    /// resolves.
    #[test]
    fn test_check_all_forward_reference_across_islands_is_accepted() {
        let earlier = "set_option autoImplicit false\n\
                       theorem earlier_uses_later (p : Nat -> Prop) : \
                       later_always p = later_always p := later_always_refl p\n";
        let later = "def later_always (p : Nat -> Prop) : Prop := forall (n : Nat), p n\n\
                     theorem later_always_refl (p : Nat -> Prop) : \
                     later_always p = later_always p := rfl\n";

        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[earlier, later]);

        assert!(batch.cycles.is_empty(), "unexpected cycle: {:?}", batch.cycles);
        for (index, outcome) in batch.outcomes.iter().enumerate() {
            assert!(!outcome.is_rejected(), "island {index} rejected: {:?}", outcome.errors);
        }
        let registered: Vec<&str> =
            batch.outcomes.iter().flat_map(|o| o.registered.iter().map(String::as_str)).collect();
        assert!(
            registered.contains(&"earlier_uses_later"),
            "the forward-referencing theorem was not registered: {registered:?}"
        );
    }

    /// The control that makes the acceptance mean something. Two theorems state
    /// the SAME false proposition and each is "proved" by the other. Header-first
    /// resolution puts both names in scope, so this is exactly the shape that a
    /// declare-then-elaborate environment must refuse: if it did not, the kernel
    /// would end up holding a proof of `0 = 1`.
    #[test]
    fn test_check_all_proof_cycle_across_islands_is_refused() {
        let earlier = "set_option autoImplicit false\n\
                       theorem false_via_a : 0 = 1 := false_via_b\n";
        let later = "set_option autoImplicit false\n\
                     theorem false_via_b : 0 = 1 := false_via_a\n";

        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[earlier, later]);

        // The REASON matters, not merely the rejection: today's source-order
        // loop already rejects this file with four `UnknownIdent`s, which is a
        // rejection for the wrong reason. I1 must name the cycle, and must find
        // it STRUCTURALLY — before elaboration — so the kernel is never asked to
        // check a mutual proof and never has the chance to diverge instead.
        assert!(
            !batch.cycles.is_empty(),
            "the proof cycle was not detected structurally; rejection reason was: {:?}",
            batch.outcomes.iter().map(|o| &o.errors).collect::<Vec<_>>()
        );
        let members = batch.cycles[0].render();
        assert!(
            members.contains("false_via_a") && members.contains("false_via_b"),
            "the cycle diagnostic does not name both declarations: {members}"
        );
        assert!(batch.is_rejected(), "a mutual proof cycle was ACCEPTED");
        // Nothing from the batch may reach the kernel.
        let registered: Vec<&str> =
            batch.outcomes.iter().flat_map(|o| o.registered.iter().map(String::as_str)).collect();
        assert!(
            registered.is_empty(),
            "a declaration on a proof cycle was registered: {registered:?}"
        );
    }

    /// The cycle is rendered from the PROGRAM, not from the search that found
    /// it: it starts at the earliest-authored member and closes on it. The
    /// compiler's `//~ ERROR` annotations in
    /// `tests/ui/trust/clean_symbol_graph_forward_reference_cycle.rs` pin this
    /// exact string, so a witness that began wherever breadth-first search
    /// happened to start would be a silent test break.
    #[test]
    fn test_check_all_cycle_render_starts_at_the_earliest_authored_member() {
        let earlier = "set_option autoImplicit false\n\
                       def ping (n : Nat) : Nat := pong n\n";
        let later = "set_option autoImplicit false\n\
                     def pong (n : Nat) : Nat := ping n\n";

        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[earlier, later]);

        assert_eq!(batch.cycles.len(), 1, "expected exactly one cycle: {:?}", batch.cycles);
        assert_eq!(batch.cycles[0].render(), "ping -> pong -> ping");
        assert_eq!(batch.cycles[0].sites[0].island, 0, "the cycle must lead with the first island");
    }

    /// Clean's refusal is carried through verbatim, so the author is told what
    /// to DO. A cycle diagnostic that only states the fact is a regression.
    #[test]
    fn test_check_all_cycle_message_names_the_options() {
        let earlier = "set_option autoImplicit false\n\
                       theorem false_via_a : 0 = 1 := false_via_b\n";
        let later = "set_option autoImplicit false\n\
                     theorem false_via_b : 0 = 1 := false_via_a\n";

        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[earlier, later]);

        let message = &batch.cycles[0].message;
        assert!(
            message.contains("ways forward, in order of preference"),
            "the cycle refusal does not offer options: {message}"
        );
        assert!(
            message.contains("axiom"),
            "the cycle refusal does not name the disclosure option: {message}"
        );
    }

    /// CLEAN-ISLAND-DOUBLED-SEVERITY-1. Every routed refusal reaches the compiler
    /// as the body of a diagnostic whose severity the compiler states, so none
    /// may carry Clean's CLI `error:` tag: an elaboration failure, a duplicate
    /// declaration and a proof cycle each come from a different rendering arm.
    /// The control: each still says what Clean said.
    #[test]
    fn test_check_all_routed_refusals_carry_no_cli_severity_tag() {
        let mut session = CleanIslandSession::new();
        let mismatch = session.check_all(&["theorem bad : 1 = 2 := rfl\n"]);
        let mut duplicate = CleanIslandSession::new();
        let twice = duplicate.check_all(&["def dup : Nat := 1\ndef dup : Nat := 2\n"]);
        let mut cyclic = CleanIslandSession::new();
        let cycle = cyclic.check_all(&[
            "set_option autoImplicit false\ntheorem false_via_a : 0 = 1 := false_via_b\n",
            "set_option autoImplicit false\ntheorem false_via_b : 0 = 1 := false_via_a\n",
        ]);

        let island = |batch: &super::CleanIslandBatch| -> Vec<String> {
            batch.outcomes.iter().flat_map(|o| o.errors.iter().map(|e| e.message.clone())).collect()
        };
        let routed = [
            ("elaboration", island(&mismatch), "`bad` did not elaborate"),
            ("duplicate", island(&twice), "`dup` is declared twice"),
            ("cycle", cycle.cycles.iter().map(|c| c.message.clone()).collect(), "ways forward"),
        ];
        for (arm, messages, says) in routed {
            assert!(
                messages.iter().any(|m| m.contains(says)),
                "the {arm} refusal no longer says {says:?}: {messages:?}"
            );
            for message in &messages {
                assert!(
                    !message.trim_start().starts_with("error:"),
                    "the {arm} refusal carries Clean's CLI severity tag: {message}"
                );
            }
        }
    }

    /// The totality half of the control: `ping`/`pong` have consistent HEADERS
    /// and a cycle only in their bodies, so it proves bodies are still checked
    /// after the header phase succeeded rather than trusted from a header graph.
    #[test]
    fn test_check_all_definitional_cycle_across_islands_is_refused() {
        let earlier = "set_option autoImplicit false\n\
                       def ping (n : Nat) : Nat := pong n\n";
        let later = "set_option autoImplicit false\n\
                     def pong (n : Nat) : Nat := ping n\n";

        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[earlier, later]);

        assert!(
            !batch.cycles.is_empty(),
            "the definitional cycle was not detected structurally; errors: {:?}",
            batch.outcomes.iter().map(|o| &o.errors).collect::<Vec<_>>()
        );
        assert!(batch.is_rejected(), "a non-terminating definitional cycle was ACCEPTED");
    }

    /// Islands still form ONE ordered Clean file session. `namespace` and `open`
    /// state is contributed by ELABORATION, not preprocessing, so a context
    /// snapshot taken after preprocessing alone would lose it and this would
    /// regress — which is what `tests/ui/trust/clean_island_stateful.rs` pins.
    #[test]
    fn test_check_all_namespace_and_open_state_crosses_islands() {
        let first = "namespace Shared\n                     theorem zero_eq : 0 = 0 := rfl\n                     end Shared\n";
        let second = "open Shared\n                      theorem reused : 0 = 0 := zero_eq\n";

        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[first, second]);

        assert!(batch.cycles.is_empty(), "unexpected cycle: {:?}", batch.cycles);
        for (index, outcome) in batch.outcomes.iter().enumerate() {
            assert!(!outcome.is_rejected(), "island {index} rejected: {:?}", outcome.errors);
        }
        let registered: Vec<&str> =
            batch.outcomes.iter().flat_map(|o| o.registered.iter().map(String::as_str)).collect();
        assert!(
            registered.contains(&"reused"),
            "`open Shared` from the first island did not reach the second: {registered:?}"
        );
    }

    /// Ordinary source-order code must be unaffected: a later declaration using
    /// an earlier one still works, and both register.
    #[test]
    fn test_check_all_source_order_dependencies_still_register() {
        let island = "def base (n : Nat) : Nat := n\n\
                      theorem base_eq (n : Nat) : base n = n := rfl\n";
        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[island]);

        assert!(batch.cycles.is_empty(), "unexpected cycle: {:?}", batch.cycles);
        assert!(
            !batch.outcomes[0].is_rejected(),
            "island rejected: {:?}",
            batch.outcomes[0].errors
        );
        assert_eq!(batch.outcomes[0].registered.len(), 2);
    }

    /// Clean registers an axiom happily; a strict Trust island does not. The
    /// refusal must NAME the axiom — `tests/ui/trust/clean_symbol_graph_axiom_
    /// disclosed.rs` pins both halves, and an anonymous "depends on trust
    /// provenance" would not satisfy the disclosure rule.
    #[test]
    fn test_check_all_axiom_is_refused_and_the_dependent_proof_discloses_it() {
        let island = "axiom assumed_le : forall (n : Nat), Nat.le n n\n\
                      theorem le_self (n : Nat) : Nat.le n n := assumed_le n\n";
        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[island]);

        assert!(batch.is_rejected(), "an axiom-bearing island was ACCEPTED");
        let messages: Vec<&str> =
            batch.outcomes[0].errors.iter().map(|e| e.message.as_str()).collect();
        assert!(
            messages.iter().any(|m| m.contains("`assumed_le` is an axiom")),
            "the axiom itself was not refused: {messages:?}"
        );
        assert!(
            messages.iter().any(|m| m.contains("le_self")
                && m.contains("trust provenance")
                && m.contains("assumed_le")),
            "the dependent proof did not disclose the assumption by name: {messages:?}"
        );
        assert!(
            batch.outcomes[0].registered.is_empty(),
            "an assumption-bearing declaration was reported as registered: {:?}",
            batch.outcomes[0].registered
        );
    }

    /// The control that keeps the disclosure above from being inert: the same
    /// proposition with a real kernel term registers, with no error.
    #[test]
    fn test_check_all_axiom_free_proof_registers() {
        let island = "theorem le_self (n : Nat) : Nat.le n n := @Nat.le.refl n\n";
        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[island]);

        assert!(
            !batch.outcomes[0].is_rejected(),
            "the axiom-free control was rejected: {:?}",
            batch.outcomes[0].errors
        );
        assert_eq!(batch.outcomes[0].registered, vec!["le_self".to_string()]);
    }
}
