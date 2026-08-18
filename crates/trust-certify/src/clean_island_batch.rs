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
    self, BatchOptions, BatchRejection, DeclStatus, Site, SourceUnit, UnitId,
};
use clean_kernel::{Environment, Name};
use clean_parser::SurfaceDecl;

use crate::clean_island::{
    CleanIslandDiagnostic, CleanIslandOutcome, point_diagnostic_span,
    strict_registered_policy_error,
};

/// One declaration on a dependency cycle, with the island it was written in.
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
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
}

impl CleanIslandBatch {
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
    let mut outcomes = vec![CleanIslandOutcome::default(); sources.len()];

    // Island framing is this crate's job, not Clean's: parse each island on its
    // own so a parse failure is reported against the island that contains it
    // and the rest of the crate is still checked.
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let mut parsed: Vec<(usize, Vec<SurfaceDecl>)> = Vec::new();
    for (island, source) in sources.iter().enumerate() {
        match clean_parser::parse_file_with_tactics_located(source, &patterns) {
            Ok(decls) => parsed.push((island, decls)),
            Err(err) => {
                let (start, end) = point_diagnostic_span(source, err.byte_offset);
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
        return CleanIslandBatch { outcomes, cycles: Vec::new() };
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
        route_rejection(rejection, sources, &mut outcomes, &mut cycles);
    }

    for decl in &module.decls {
        let island = decl.unit.0 as usize;
        let Some(source) = sources.get(island) else { continue };
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
                for name in &checked {
                    if let Some(message) = strict_registered_policy_error(env, name) {
                        push_unique(
                            &mut outcomes[island],
                            CleanIslandDiagnostic {
                                start: decl.span.start.min(source.len()),
                                end: decl.span.end.min(source.len()),
                                message,
                            },
                        );
                        refused = true;
                    }
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

    let mut batch = CleanIslandBatch { outcomes, cycles };

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
                message: "Clean island batch was not committed and reported no reason; nothing \
                          was registered, so the crate is refused rather than built against an \
                          empty Clean environment"
                    .to_string(),
            });
        }
    }
    debug_assert!(
        module.committed || batch.is_rejected(),
        "an uncommitted Clean island batch produced no diagnostic"
    );
    batch
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
    outcomes: &mut [CleanIslandOutcome],
    cycles: &mut Vec<CleanIslandCycle>,
) {
    let message = module_batch::render::rejection(rejection);
    match rejection {
        BatchRejection::ProofCycle { witness, names }
        | BatchRejection::SignatureCycle { witness, names }
        | BatchRejection::UnsupportedScc { witness, names, .. } => {
            let sites = cycle_sites(witness, names, sources);
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
                emit_at(*site, &message, sources, outcomes);
            }
        }
        BatchRejection::HeaderTypeDivergence { site, .. }
        | BatchRejection::StagedReference { site, .. }
        | BatchRejection::Elaboration { site, .. } => {
            emit_at(*site, &message, sources, outcomes);
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

/// Push a diagnostic at a Clean [`Site`], clamped to that island's text.
fn emit_at(site: Site, message: &str, sources: &[&str], outcomes: &mut [CleanIslandOutcome]) {
    let island = site.unit.0 as usize;
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
            start: site.span.start.min(len),
            end: site.span.end.min(len),
            message: message.to_string(),
        },
    );
}

/// Push a diagnostic that belongs to no single declaration onto the first
/// island, which is where the batch begins.
fn emit_whole_batch(message: &str, sources: &[&str], outcomes: &mut [CleanIslandOutcome]) {
    let Some(outcome) = outcomes.first_mut() else { return };
    let len = sources.first().map_or(0, |source| source.len());
    push_unique(
        outcome,
        CleanIslandDiagnostic { start: 0, end: len.min(1), message: message.to_string() },
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
            CleanIslandCycleSite {
                island,
                start: site.span.start.min(len),
                end: site.span.end.min(len),
                name,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::clean_island::CleanIslandSession;

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
        let island = "theorem le_self (n : Nat) : Nat.le n n := Nat.le.refl n\n";
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
