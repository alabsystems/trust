// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Checked, owned Lean source snapshots for the standalone compiler lane.
//!
//! The only constructor performs a fresh strict kernel batch check. Its
//! accepted context binds the supplied module/path labels and exact UTF-8
//! source bytes to that session and its independently enumerated eager
//! declaration delta. Neither caller-authored hashes, diagnostic census JSON,
//! nor the lossy `registered` name list can construct this context.
//! The kernel builtin PProd prologue is materialized before the baseline: it
//! belongs to the initial trusted environment, not to whichever source import
//! first happens to trigger the elaborator's unconditional initialization.
//! This does not exclude runtime dependencies on those builtins or establish
//! runtime-body completeness; every subsequent eager addition is still owned.
//!
//! This is NOT a filesystem resolver or a claim of full Lean/runtime closure.
//! Labels identify supplied snapshots; no path is opened or attested here.
//! Exactly the supplied module keys and explicitly indexed aliases are marked
//! satisfied-from-source. An alias names one checked snapshot, never an
//! additional unchecked input or an external module. External
//! source-driven `.olean` loading remains disabled. The opt-in initializer
//! separately materializes configured pinned Init; lazy enumeration is not certified
//! exhaustive; added eager declarations include proofs and generated kernel
//! helpers, not a complete erased/specialized runtime-body universe. A consumer
//! must separately establish carrier refinement, reachability, and codegen
//! authority. Source checking alone establishes none of those judgments.
//!
//! TIMING. Each check measures what it spent ([`LeanBatchTiming`]): the fresh
//! session's start (the kernel prelude and the PProd prologue, before any
//! source), the whole check, and whatever Clean's own per-declaration recorder
//! (`clean_elab::begin_decl_timing`) records while the batch runs. That
//! recorder sits on Clean's per-declaration registration entry, which the
//! module batch reaches only for lexical commands (`open`, `import`, …): the
//! batch elaborates and registers declarations through its own path
//! (`module_batch::exec::{elaborate_node, register_node}`), which times
//! nothing yet, so a declaration's elaboration and kernel check have no
//! value here until Clean's batch records one. Wall time, read by
//! `targo trust meter`; no verdict, binding or digest reads it.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::time::{Duration, Instant};

use clean_kernel::{Environment, Name};
use trust_types::digest::canonical_json_sha256;

use crate::clean_census::owned_names;
use crate::clean_island::CleanIslandSession;
use crate::clean_island_batch::CleanIslandBatch;

pub(crate) mod pinned_reference;

#[cfg(test)]
mod pinned_tests;

/// An owned, explicitly selected compiler-world source initializer. Its Init
/// snapshot is producer DATA, never a cached verdict. Each check starts from
/// a fresh clone and replays the complete owned/judgment cone from empty.
///
/// This is opt-in: existing constructors and Rust islands retain their current
/// environment. It requires the configured/bundled pinned library DATA and
/// never executes Lean or interprets diagnostic paths as project provenance.
pub struct PinnedLeanSourceWorld {
    decision: clean_olean::SourceWorldDecision,
    setup: clean_elab::module_driver::SourceModuleSetup,
}

/// Only the initializer above can produce this context. No public arbitrary
/// environment, digest, deserializer or assertion can seed a source session.
pub(crate) struct ProducedSourcePrelude {
    environment: Environment,
    file_context: clean_elab::FileContext,
}

impl ProducedSourcePrelude {
    pub(crate) fn into_parts(self) -> (Environment, clean_elab::FileContext) {
        (self.environment, self.file_context)
    }
}

impl PinnedLeanSourceWorld {
    /// Select existing pinned library DATA and materialize genuine Init with
    /// Clean's maintained source-module producer. Missing/foreign inputs fail;
    /// there is no fallback to the legacy built-in context.
    pub fn new() -> Result<Self, String> {
        let decision =
            clean_olean::source_world_for_snapshot().map_err(|error| error.to_string())?;
        Self::from_decision(decision)
    }

    fn from_decision(decision: clean_olean::SourceWorldDecision) -> Result<Self, String> {
        // Clean's general source setup deliberately supports an Oracle
        // bootstrap when project artifact imports are denied. This opt-in
        // genuine-Init path must refuse that decision before any setup.
        decision.imports().map_err(|error| {
            format!("compiler-world source initializer refuses artifact inputs: {error}")
        })?;
        let mut setup = clean_elab::module_driver::SourceModuleSetup::new(
            clean_elab::module_driver::EnvironmentSetup::default(),
            &decision,
        )
        .map_err(|error| error.to_string())?;
        setup
            .initial_environment(&clean_parser::FileHeader::default())
            .map_err(|error| error.to_string())?;
        Ok(Self { decision, setup })
    }

    /// Read-only selection DATA. It authenticates neither all library bytes
    /// nor external search paths and supplies no source/proof/codegen grade.
    #[must_use]
    pub fn decision(&self) -> &clean_olean::SourceWorldDecision {
        &self.decision
    }

    #[must_use]
    pub fn check(
        &mut self,
        sources: Vec<LeanSourceInput>,
        collect_census: bool,
    ) -> CheckedLeanSourceBatch {
        self.check_with_aliases(sources, Vec::new(), collect_census)
    }

    #[must_use]
    pub fn check_with_aliases(
        &mut self,
        sources: Vec<LeanSourceInput>,
        aliases: Vec<LeanSourceAlias>,
        collect_census: bool,
    ) -> CheckedLeanSourceBatch {
        CheckedLeanSourceBatch::check_impl(sources, aliases, collect_census, false, Some(self))
    }

    #[must_use]
    pub fn check_with_aliases_and_runtime_baseline(
        &mut self,
        sources: Vec<LeanSourceInput>,
        aliases: Vec<LeanSourceAlias>,
        collect_census: bool,
    ) -> CheckedLeanSourceBatch {
        CheckedLeanSourceBatch::check_impl(sources, aliases, collect_census, true, Some(self))
    }

    #[must_use]
    pub fn check_with_runtime_baseline(
        &mut self,
        sources: Vec<LeanSourceInput>,
        collect_census: bool,
    ) -> CheckedLeanSourceBatch {
        self.check_with_aliases_and_runtime_baseline(sources, Vec::new(), collect_census)
    }

    fn fresh_prelude(&self, sources: &[LeanSourceInput]) -> Result<ProducedSourcePrelude, String> {
        for source in sources {
            let header = clean_parser::Parser::parse_header(&source.source)
                .map_err(|error| format!("source `{}` header: {error}", source.module))?;
            if header.is_prelude {
                return Err(
                    "the opt-in pinned Init source API does not yet support prelude modules".into(),
                );
            }
        }
        let mut fresh = self.setup.isolated();
        let (environment, file_context) = fresh
            .initial_environment_and_file_context(&clean_parser::FileHeader::default())
            .map_err(|error| error.to_string())?;
        Ok(ProducedSourcePrelude { environment, file_context })
    }
}

/// Untrusted inputs, not evidence. The constructor checks these actual bytes;
/// labels are retained verbatim and do not assert filesystem provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanSourceInput {
    /// Exact module key supplied by this snapshot, including dotted names.
    pub module: String,
    /// Caller-provided diagnostic path label; this module never opens it.
    pub path: String,
    /// Complete UTF-8 source snapshot, not a digest or a declaration summary.
    pub source: String,
}

/// An additional exact module key for one supplied source snapshot. Like the
/// primary module/path labels, this is untrusted resolution input, not a
/// filesystem attestation. A filesystem caller must establish that the alias
/// resolves to this same source; the checked context retains the exact mapping.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanSourceAlias {
    pub module: String,
    pub source_index: usize,
}

/// Where one check's wall time went. Not a function of the inputs: in no
/// digest, binding or verdict.
#[derive(Debug, Clone, Default)]
pub struct LeanBatchTiming {
    /// Starting the fresh strict session: the kernel prelude and the builtin
    /// PProd prologue, measured before any source is elaborated. `None` when
    /// the batch was refused before a session started. The opt-in world
    /// owner's initial Init import occurs in `PinnedLeanSourceWorld::new`;
    /// its subsequent checks measure the fresh snapshot clone here.
    pub session_start: Option<Duration>,
    /// Clean's per-declaration records, in elaboration order (see the module
    /// doc: the batch records lexical commands through it, not declarations).
    pub declarations: Vec<clean_elab::DeclTiming>,
    /// The whole check, from the first refusal test to the bound outcome.
    pub total: Duration,
}

/// Private construction binds this opaque custody value to one successfully
/// accepted source batch. Cloning preserves that same owner; independent
/// checks always receive a distinct owner even when all disclosed data match.
///
/// This is in-memory identity only, never a semantic checker, source hash,
/// serialized certificate or permission to compile a function.
#[derive(Clone)]
pub struct AcceptedSourceContextCustody {
    identity: Arc<()>,
}

impl std::fmt::Debug for AcceptedSourceContextCustody {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("AcceptedSourceContextCustody").finish_non_exhaustive()
    }
}

impl AcceptedSourceContextCustody {
    /// Compare retained ownership, not source/library equality or proof truth.
    /// The Arc allocation remains live while any token holds this custody.
    #[must_use]
    pub fn same_context(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.identity, &other.identity)
    }
}

struct AcceptedBinding {
    custody: AcceptedSourceContextCustody,
    source_closure_sha256: String,
    owned_declarations: BTreeSet<Name>,
    owned_declarations_sha256: String,
}

/// Own one fresh attempted check and its exact sources. Failed outcomes remain
/// available for the CLI's real-elaborator-driven import discovery, but only
/// [`Self::accepted_context`] can expose a kernel environment or sealed roots.
pub struct CheckedLeanSourceBatch {
    sources: Vec<LeanSourceInput>,
    aliases: Vec<LeanSourceAlias>,
    session: Option<CleanIslandSession>,
    attempt: Option<CleanIslandBatch>,
    errors: Vec<String>,
    binding: Option<AcceptedBinding>,
    runtime_baseline: Option<Environment>,
    timing: LeanBatchTiming,
    source_world: Option<clean_olean::SourceWorldDecision>,
}

impl CheckedLeanSourceBatch {
    /// Check exactly the supplied resolution unit in a new strict session.
    /// Empty batches and duplicate module keys are refused before elaboration;
    /// all other kernel/source-policy failures retain their attempted outcomes.
    /// `collect_census` controls diagnostic measurement only, never acceptance.
    #[must_use]
    pub fn check(sources: Vec<LeanSourceInput>, collect_census: bool) -> Self {
        Self::check_with_aliases(sources, Vec::new(), collect_census)
    }

    /// Check a supplied resolution unit with additional keys for its snapshots.
    /// Empty/duplicate keys, primary-key collisions and out-of-range indices
    /// refuse before elaboration. Aliases do not add source/outcome/census rows:
    /// each supplied snapshot is still elaborated exactly once in this session.
    #[must_use]
    pub fn check_with_aliases(
        sources: Vec<LeanSourceInput>,
        aliases: Vec<LeanSourceAlias>,
        collect_census: bool,
    ) -> Self {
        Self::check_impl(sources, aliases, collect_census, false, None)
    }

    /// The identical strict checker with an opt-in read-only pre-source
    /// environment observation. It neither accepts imports nor grants runtime
    /// refinement; only an accepted context can borrow this baseline later.
    #[must_use]
    pub fn check_with_runtime_baseline(
        sources: Vec<LeanSourceInput>,
        collect_census: bool,
    ) -> Self {
        Self::check_with_aliases_and_runtime_baseline(sources, Vec::new(), collect_census)
    }

    /// Retain the pre-source observation while checking the same exact alias
    /// mapping as the ordinary source path. Aliases remain bound resolution
    /// inputs, never additional declarations or unchecked source admission.
    #[must_use]
    pub fn check_with_aliases_and_runtime_baseline(
        sources: Vec<LeanSourceInput>,
        aliases: Vec<LeanSourceAlias>,
        collect_census: bool,
    ) -> Self {
        Self::check_impl(sources, aliases, collect_census, true, None)
    }

    fn check_impl(
        sources: Vec<LeanSourceInput>,
        aliases: Vec<LeanSourceAlias>,
        collect_census: bool,
        retain_runtime_baseline: bool,
        pinned_world: Option<&mut PinnedLeanSourceWorld>,
    ) -> Self {
        let started = Instant::now();
        let mut checked = Self::check_untimed(
            sources,
            aliases,
            collect_census,
            retain_runtime_baseline,
            pinned_world,
        );
        checked.timing.total = started.elapsed();
        checked
    }

    fn check_untimed(
        sources: Vec<LeanSourceInput>,
        aliases: Vec<LeanSourceAlias>,
        collect_census: bool,
        retain_runtime_baseline: bool,
        pinned_world: Option<&mut PinnedLeanSourceWorld>,
    ) -> Self {
        let mut checked = Self {
            sources,
            aliases,
            session: None,
            attempt: None,
            errors: Vec::new(),
            binding: None,
            runtime_baseline: None,
            timing: LeanBatchTiming::default(),
            source_world: pinned_world.as_ref().map(|world| world.decision.clone()),
        };
        if checked.sources.is_empty() {
            checked
                .errors
                .push("empty Lean source batch: supply at least one source snapshot".into());
        }
        let mut modules = BTreeMap::<&str, usize>::new();
        for (index, source) in checked.sources.iter().enumerate() {
            if source.module.is_empty() {
                checked.errors.push(format!("source {index} has an empty module key"));
            }
            if let Some(previous) = modules.insert(&source.module, index) {
                checked.errors.push(format!(
                    "duplicate module key `{}` at source indices {previous} and {index}",
                    source.module
                ));
            }
        }
        for alias in &checked.aliases {
            if alias.module.is_empty() {
                checked.errors.push("source alias has an empty module key".into());
            }
            if alias.source_index >= checked.sources.len() {
                checked.errors.push(format!(
                    "source alias `{}` has out-of-range source index {} for {} snapshots",
                    alias.module,
                    alias.source_index,
                    checked.sources.len()
                ));
            }
            if let Some(previous) = modules.insert(&alias.module, alias.source_index) {
                checked.errors.push(format!(
                    "duplicate or primary-colliding alias key `{}` at source indices {previous} and {}",
                    alias.module, alias.source_index
                ));
            }
        }
        if !checked.errors.is_empty() {
            return checked;
        }

        let session_started = Instant::now();
        let produced_session = match pinned_world.as_ref() {
            Some(world) => world
                .fresh_prelude(&checked.sources)
                .map(CleanIslandSession::new_for_pinned_source_batch),
            None => CleanIslandSession::new_for_source_batch(),
        };
        let mut session = match produced_session {
            Ok(session) => session,
            Err(error) => {
                checked.timing.session_start = Some(session_started.elapsed());
                checked.errors.push(error);
                return checked;
            }
        };
        // Before ANY source is elaborated, and independent of producer,
        // registered-name, or optional diagnostic-census admission.
        let before = owned_names(session.environment().expect("fresh session is untainted"));
        checked.timing.session_start = Some(session_started.elapsed());
        if retain_runtime_baseline {
            checked.runtime_baseline = session.environment().cloned();
        }
        for module in modules.keys() {
            // These are dotted source-path keys, whose components are strings,
            // including numeric file names. Declaration identities come from
            // the elaborator and are never reconstructed from these labels.
            let name = module.split('.').fold(Name::anon(), |name, part| name.str(part));
            session.mark_import_satisfied_from_source(&name);
        }
        let sources: Vec<&str> =
            checked.sources.iter().map(|source| source.source.as_str()).collect();
        // Clean's recorder is per thread and the batch elaborates on this
        // one; arming it only records.
        clean_elab::begin_decl_timing();
        let mut attempt = if checked.source_world.is_some() {
            session.check_all_pinned_source(&sources, collect_census, &before)
        } else if collect_census {
            session.check_all_with_census(&sources)
        } else {
            session.check_all(&sources)
        };
        checked.timing.declarations = clean_elab::take_decl_timings();
        if attempt.outcomes.len() != checked.sources.len() {
            checked.errors.push(format!(
                "incomplete Lean check outcomes: {} for {} supplied snapshots",
                attempt.outcomes.len(),
                checked.sources.len()
            ));
        }
        if !attempt.is_rejected() && checked.errors.is_empty() {
            match session.environment() {
                Some(env) => {
                    match bind_accepted_sources(
                        env,
                        &before,
                        &checked.sources,
                        &checked.aliases,
                        checked.source_world.as_ref(),
                    ) {
                        Ok(binding) => checked.binding = Some(binding),
                        Err(error) => checked.errors.push(error),
                    }
                }
                None => checked
                    .errors
                    .push("accepted outcomes have no untainted kernel environment".into()),
            }
        }
        // Label the diagnostic copy AFTER the independent binding is minted.
        // This JSON is never read back as source identity or acceptance state.
        if let Some(census) = &mut attempt.census {
            if let Some(inputs) = census.report["inputs"].as_array_mut() {
                for (input, source) in inputs.iter_mut().zip(&checked.sources) {
                    input["path"] = serde_json::json!(source.path);
                    input["module"] = serde_json::json!(source.module);
                }
            }
        }
        checked.session = Some(session);
        checked.attempt = Some(attempt);
        checked
    }

    #[must_use]
    pub fn sources(&self) -> &[LeanSourceInput] {
        &self.sources
    }

    /// Retained resolution input, including when its preflight was refused.
    #[must_use]
    pub fn aliases(&self) -> &[LeanSourceAlias] {
        &self.aliases
    }

    /// None means preflight refused the supplied batch before elaboration.
    /// A rejected attempt still carries every per-source diagnostic and cycle.
    #[must_use]
    pub fn attempt(&self) -> Option<&CleanIslandBatch> {
        self.attempt.as_ref()
    }

    /// Where this check's wall time went ([`LeanBatchTiming`]).
    #[must_use]
    pub fn timing(&self) -> &LeanBatchTiming {
        &self.timing
    }

    /// Framing/identity errors, additional to the attempted kernel diagnostics.
    #[must_use]
    pub fn errors(&self) -> &[String] {
        &self.errors
    }

    #[must_use]
    pub fn accepted_context(&self) -> Option<AcceptedLeanSourceContext<'_>> {
        if !self.errors.is_empty() || self.attempt.as_ref()?.is_rejected() {
            return None;
        }
        Some(AcceptedLeanSourceContext {
            sources: &self.sources,
            aliases: &self.aliases,
            environment: self.session.as_ref()?.environment()?,
            binding: self.binding.as_ref()?,
            runtime_baseline: self.runtime_baseline.as_ref(),
            source_world: self.source_world.as_ref(),
        })
    }
}

/// A borrow of a successfully checked batch, never constructible from labels,
/// hashes, JSON, a caller-owned environment, or a selected declaration list.
/// No mutable environment or source reference escapes this sealed boundary.
pub struct AcceptedLeanSourceContext<'a> {
    sources: &'a [LeanSourceInput],
    aliases: &'a [LeanSourceAlias],
    environment: &'a Environment,
    binding: &'a AcceptedBinding,
    runtime_baseline: Option<&'a Environment>,
    source_world: Option<&'a clean_olean::SourceWorldDecision>,
}

impl AcceptedLeanSourceContext<'_> {
    /// Opaque custody of this actual accepted batch. Reborrows and legitimate
    /// lazy materialization keep the same owner; no digest can reconstruct it.
    #[must_use]
    pub fn custody(&self) -> &AcceptedSourceContextCustody {
        &self.binding.custody
    }

    /// The privately retained opt-in world selection, if used. DATA only;
    /// the complete source check and closed judgments supply acceptance.
    #[must_use]
    pub fn source_world(&self) -> Option<&clean_olean::SourceWorldDecision> {
        self.source_world
    }
    #[must_use]
    pub fn environment(&self) -> &Environment {
        self.environment
    }

    /// Actual pre-source environment from the same strict session, present
    /// only when explicitly requested. Read-only; not an admission capability.
    #[must_use]
    pub fn runtime_baseline_environment(&self) -> Option<&Environment> {
        self.runtime_baseline
    }

    #[must_use]
    pub fn sources(&self) -> &[LeanSourceInput] {
        self.sources
    }

    /// Exact additional module-key to checked-snapshot mapping supplied to the
    /// final session. These are resolution labels, not extra checked sources.
    #[must_use]
    pub fn aliases(&self) -> &[LeanSourceAlias] {
        self.aliases
    }

    /// Canonical JSON SHA-256 of `("trust.lean.supplied-source-batch/v1",
    /// [(module, path, actual_source_text), ...])`, in supplied input order.
    /// With aliases, the version is `trust.lean.supplied-source-batch/v2` and
    /// the tuple additionally contains the ordered `(module, source_index)`
    /// alias rows. Alias-free v1 identities remain unchanged.
    /// The opt-in compiler-world domain additionally binds the selected world
    /// label. None of these digests authenticates every Init/import byte:
    /// the retained actual environment and closed replay carry that context.
    /// It binds actual bytes, not caller-provided source digests. Path labels
    /// are identities within this snapshot bundle, NOT filesystem attestation.
    #[must_use]
    pub fn source_closure_sha256(&self) -> &str {
        &self.binding.source_closure_sha256
    }

    /// Exact added EAGER names, including generated helpers omitted from
    /// `registered`. Prelude/preexisting names are not owned by this batch.
    /// This is not an enumeration of reachable runtime bodies or lazy imports.
    #[must_use]
    pub fn owned_declarations(&self) -> &BTreeSet<Name> {
        &self.binding.owned_declarations
    }

    #[must_use]
    pub fn owns_declaration(&self, name: &Name) -> bool {
        self.binding.owned_declarations.contains(name)
    }

    /// Canonical JSON SHA-256 of `("trust.lean.added-eager-payloads/v1", rows)`.
    /// Rows are Name-sorted full tuples `(ConstantInfo, InductiveVal?,
    /// ConstructorVal?, RecursorVal?, QuotVal?)`, NOT only declaration names.
    #[must_use]
    pub fn owned_declarations_sha256(&self) -> &str {
        &self.binding.owned_declarations_sha256
    }
}

fn bind_accepted_sources(
    env: &Environment,
    before: &BTreeSet<Name>,
    sources: &[LeanSourceInput],
    aliases: &[LeanSourceAlias],
    source_world: Option<&clean_olean::SourceWorldDecision>,
) -> Result<AcceptedBinding, String> {
    let after = owned_names(env);
    if !before.is_subset(&after) {
        return Err("Lean source check removed preexisting eager kernel identities".into());
    }
    let owned_declarations: BTreeSet<_> = after.difference(before).cloned().collect();
    let payloads: Vec<_> = owned_declarations
        .iter()
        .map(|name| {
            let info = env
                .get_const(name)
                .ok_or_else(|| format!("missing added kernel payload `{name}`"))?;
            Ok((
                info,
                env.get_inductive(name),
                env.get_constructor(name),
                env.get_recursor(name),
                env.quotients().find(|value| &value.name == name),
            ))
        })
        .collect::<Result<_, String>>()?;
    let owned_declarations_sha256 =
        canonical_json_sha256(&("trust.lean.added-eager-payloads/v1", payloads))
            .map_err(|error| format!("cannot bind added Lean kernel payloads: {error}"))?;
    let inputs: Vec<_> =
        sources.iter().map(|source| (&source.module, &source.path, &source.source)).collect();
    let source_closure_sha256 = if let Some(world) = source_world {
        let aliases: Vec<_> =
            aliases.iter().map(|alias| (&alias.module, alias.source_index)).collect();
        canonical_json_sha256(&(
            "trust.lean.compiler-world-source-batch/v1",
            world.world().to_string(),
            inputs,
            aliases,
        ))
    } else if aliases.is_empty() {
        canonical_json_sha256(&("trust.lean.supplied-source-batch/v1", inputs))
    } else {
        let aliases: Vec<_> =
            aliases.iter().map(|alias| (&alias.module, alias.source_index)).collect();
        canonical_json_sha256(&("trust.lean.supplied-source-batch/v2", inputs, aliases))
    }
    .map_err(|error| format!("cannot bind Lean source snapshots: {error}"))?;
    Ok(AcceptedBinding {
        custody: AcceptedSourceContextCustody { identity: Arc::new(()) },
        source_closure_sha256,
        owned_declarations,
        owned_declarations_sha256,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source(module: &str, text: &str) -> LeanSourceInput {
        LeanSourceInput {
            module: module.into(),
            path: format!("{module}.lean"),
            source: text.into(),
        }
    }

    #[test]
    fn accepted_context_custody_survives_reborrows_clones_and_owner_moves() {
        let inputs = vec![source("Custody", "def identity (x : UInt64) : UInt64 := x")];
        let first = CheckedLeanSourceBatch::check(inputs.clone(), false);
        let custody = first.accepted_context().unwrap().custody().clone();
        let cloned = custody.clone();
        assert!(custody.same_context(&cloned));
        assert!(custody.same_context(first.accepted_context().unwrap().custody()));
        let moved = first;
        assert!(custody.same_context(moved.accepted_context().unwrap().custody()));
        drop(moved);
        // The retained Arc keeps the old allocation alive after the batch is
        // gone, so a subsequent owner cannot authenticate by address reuse.
        for _ in 0..4 {
            let next = CheckedLeanSourceBatch::check(inputs.clone(), false);
            assert!(!custody.same_context(next.accepted_context().unwrap().custody()));
        }
    }

    #[test]
    fn pinned_source_initializer_refuses_actual_denied_import_decision_before_bootstrap() {
        let root = tempfile::tempdir().unwrap();
        let file = root.path().join("Main.lean");
        std::fs::write(&file, "def value : Nat := 0\n").unwrap();
        std::fs::write(root.path().join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        // Clean's maintained producer returns a decision whose source world
        // is Oracle but whose measured project's artifact imports are denied.
        // Its general source setup would intentionally build a bootstrap.
        let decision = clean_olean::source_world_for_file(&file, None).unwrap();
        assert!(decision.imports().is_err(), "real denied artifact decision required");
        let refusal = match PinnedLeanSourceWorld::from_decision(decision) {
            Ok(_) => panic!("denied imports created a genuine-Init source owner"),
            Err(refusal) => refusal,
        };
        assert!(refusal.contains("refuses artifact inputs"), "{refusal}");
        assert!(refusal.contains("measured"), "{refusal}");
    }

    #[test]
    fn runtime_baseline_opt_in_preserves_acceptance_owned_delta_and_provenance() {
        for census in [false, true] {
            let inputs = vec![
                source("Main", "import Helper\ndef twice : Nat := value + value"),
                source("Helper", "def value : Nat := 7"),
            ];
            let old = CheckedLeanSourceBatch::check(inputs.clone(), census);
            let runtime = CheckedLeanSourceBatch::check_with_runtime_baseline(inputs, census);
            let old = old.accepted_context().expect("ordinary accepted source graph");
            let runtime = runtime.accepted_context().expect("same runtime-observed source graph");
            assert!(old.runtime_baseline_environment().is_none());
            let baseline = runtime.runtime_baseline_environment().unwrap();
            assert_eq!(old.sources(), runtime.sources());
            assert_eq!(old.source_closure_sha256(), runtime.source_closure_sha256());
            assert_eq!(old.owned_declarations_sha256(), runtime.owned_declarations_sha256());
            assert_eq!(old.owned_declarations(), runtime.owned_declarations());
            let before = owned_names(baseline);
            let after = owned_names(runtime.environment());
            assert_eq!(
                &after.difference(&before).cloned().collect::<BTreeSet<_>>(),
                runtime.owned_declarations()
            );
            for name in &after {
                assert_eq!(
                    old.environment().declaration_verification(name),
                    runtime.environment().declaration_verification(name)
                );
                assert_eq!(
                    old.environment().get_constant_origin(name),
                    runtime.environment().get_constant_origin(name)
                );
            }
        }
    }

    #[test]
    fn runtime_baseline_preserves_alias_binding_and_refusals() {
        let inputs = vec![
            source("Main", "import Sub.Leaf\ndef uses : Nat := leaf"),
            source("Leaf", "def leaf : Nat := 7"),
        ];
        let aliases = vec![LeanSourceAlias { module: "Sub.Leaf".into(), source_index: 1 }];
        for census in [false, true] {
            let ordinary =
                CheckedLeanSourceBatch::check_with_aliases(inputs.clone(), aliases.clone(), census);
            let runtime = CheckedLeanSourceBatch::check_with_aliases_and_runtime_baseline(
                inputs.clone(),
                aliases.clone(),
                census,
            );
            let original = ordinary.accepted_context().expect("ordinary alias check");
            let observed = runtime.accepted_context().expect("runtime alias check");
            assert_eq!(observed.sources(), original.sources());
            assert_eq!(observed.aliases(), aliases);
            assert_eq!(observed.aliases(), original.aliases());
            assert_eq!(observed.source_closure_sha256(), original.source_closure_sha256());
            assert_eq!(observed.owned_declarations_sha256(), original.owned_declarations_sha256());
            assert_eq!(observed.owned_declarations(), original.owned_declarations());
            assert!(original.runtime_baseline_environment().is_none());
            let baseline = observed.runtime_baseline_environment().unwrap();
            assert_eq!(
                &owned_names(observed.environment())
                    .difference(&owned_names(baseline))
                    .cloned()
                    .collect::<BTreeSet<_>>(),
                observed.owned_declarations(),
            );
            assert_eq!(runtime.attempt().unwrap().outcomes.len(), inputs.len());
            // The runtime opt-in cannot turn a missing resolution alias into
            // an admitted external module or borrow a failed session's context.
            let missing =
                CheckedLeanSourceBatch::check_with_runtime_baseline(inputs.clone(), census);
            assert!(missing.accepted_context().is_none());
            for invalid in [
                vec![LeanSourceAlias { module: "Sub.Leaf".into(), source_index: 2 }],
                vec![LeanSourceAlias { module: "Main".into(), source_index: 1 }],
            ] {
                let ordinary = CheckedLeanSourceBatch::check_with_aliases(
                    inputs.clone(),
                    invalid.clone(),
                    census,
                );
                let runtime = CheckedLeanSourceBatch::check_with_aliases_and_runtime_baseline(
                    inputs.clone(),
                    invalid,
                    census,
                );
                assert!(ordinary.accepted_context().is_none());
                assert!(runtime.accepted_context().is_none());
                assert_eq!(runtime.errors(), ordinary.errors());
                assert!(runtime.attempt().is_none());
            }
        }
    }

    #[test]
    fn runtime_baseline_does_not_expose_rejected_or_partial_source_context() {
        for inputs in [
            vec![],
            vec![source("Missing", "import Unavailable\ndef value : Nat := 1")],
            vec![source("Bad", "theorem falseProof : 0 = 1 := rfl")],
        ] {
            let old = CheckedLeanSourceBatch::check(inputs.clone(), true);
            let runtime = CheckedLeanSourceBatch::check_with_runtime_baseline(inputs, true);
            assert!(old.accepted_context().is_none());
            assert!(runtime.accepted_context().is_none());
            assert_eq!(old.errors(), runtime.errors());
            assert_eq!(
                old.attempt().map(|a| a.outcomes.len()),
                runtime.attempt().map(|a| a.outcomes.len())
            );
            assert_eq!(
                old.attempt().map(|a| a.is_rejected()),
                runtime.attempt().map(|a| a.is_rejected())
            );
        }
    }

    #[test]
    fn accepts_exact_supplied_import_closure_and_excludes_prelude_ownership() {
        let inputs = vec![
            source("Main", "import Helper\ndef uses : Nat := base"),
            source("Helper", "def base : Nat := 7"),
        ];
        let checked = CheckedLeanSourceBatch::check(inputs.clone(), true);
        let context = checked.accepted_context().expect("whole supplied batch checks");
        assert_eq!(context.sources(), inputs);
        for name in ["uses", "base"] {
            let name = Name::from_string(name);
            assert!(context.owns_declaration(&name));
            assert!(context.environment().get_const(&name).unwrap().value.is_some());
        }
        let prelude = Name::from_string("Nat.add");
        assert!(context.environment().get_const(&prelude).is_some());
        assert!(!context.owns_declaration(&prelude));
        assert_eq!(
            context.source_closure_sha256(),
            canonical_json_sha256(&(
                "trust.lean.supplied-source-batch/v1",
                inputs
                    .iter()
                    .map(|source| (&source.module, &source.path, &source.source))
                    .collect::<Vec<_>>()
            ))
            .unwrap()
        );
        let census = &checked.attempt().unwrap().census.as_ref().unwrap().report;
        assert_eq!(census["inputs"][1]["module"], "Helper");
        assert_eq!(census["denominator_status"], "denominator_unverified");
    }

    #[test]
    fn generated_helpers_are_owned_independently_of_registered_names() {
        let checked = CheckedLeanSourceBatch::check(
            vec![source(
                "Choice",
                "inductive SourceChoice where\n| first : SourceChoice\n| second : SourceChoice",
            )],
            false,
        );
        let context = checked.accepted_context().expect("inductive checks");
        let helper = Name::from_string("SourceChoice.recOn");
        assert!(context.owns_declaration(&helper));
        assert!(context.environment().get_recursor(&helper).is_some());
        assert!(!checked.attempt().unwrap().outcomes[0].registered.contains(&helper.to_string()));
        assert!(
            context.owned_declarations().len()
                > checked.attempt().unwrap().outcomes[0].registered.len()
        );
    }

    #[test]
    fn local_source_imports_do_not_own_materialized_builtin_families() {
        let checked = CheckedLeanSourceBatch::check(
            vec![
                source("Main", "import Helper\ndef add8 (a b : UInt8) : UInt8 := a + b"),
                source("Helper", "def sub8 (a b : UInt8) : UInt8 := a - b"),
            ],
            true,
        );
        let context = checked.accepted_context().expect("both local sources check");
        let expected = BTreeSet::from([Name::from_string("add8"), Name::from_string("sub8")]);
        assert_eq!(context.owned_declarations(), &expected);
        // Builtins remain in the actual environment. They are present BEFORE
        // the baseline, not deleted from it or filtered from the final delta.
        for name in ["PProd", "PProd.mk", "PProd.fst", "PProd.snd", "PProd.rec", "PProd.swap"] {
            let name = Name::from_string(name);
            assert!(context.environment().get_const(&name).is_some());
            assert!(!context.owns_declaration(&name));
        }
        let census = &checked.attempt().unwrap().census.as_ref().unwrap().report;
        let measured: BTreeSet<Name> = census["declarations"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| serde_json::from_value(row["identity"].clone()).unwrap())
            .collect();
        assert_eq!(measured, expected, "optional census uses the same prepared baseline");
        assert_eq!(census["denominator_status"], "denominator_unverified");
    }

    #[test]
    fn imported_generated_helpers_and_builtin_prefixed_user_names_remain_owned() {
        let checked = CheckedLeanSourceBatch::check(
            vec![
                source("Main", "import Helper\ndef mainValue : Nat := 1"),
                source(
                    "Helper",
                    "inductive LocalPProd where\n| mk : Nat → LocalPProd\ndef PProd.userValue : Nat := 2",
                ),
            ],
            false,
        );
        let context =
            checked.accepted_context().expect("local generated source declarations check");
        for name in [
            "mainValue",
            "LocalPProd",
            "LocalPProd.mk",
            "LocalPProd.rec",
            "LocalPProd.recOn",
            "PProd.userValue",
        ] {
            assert!(
                context.owns_declaration(&Name::from_string(name)),
                "never filter `{name}` by prefix or registration summary"
            );
        }
        assert!(
            context.environment().get_recursor(&Name::from_string("LocalPProd.recOn")).is_some()
        );
        assert!(
            !checked.attempt().unwrap().outcomes[1]
                .registered
                .contains(&"LocalPProd.recOn".to_string())
        );
        assert!(checked.attempt().unwrap().census.is_none());
    }

    #[test]
    fn census_cannot_mint_or_modify_checked_identity() {
        let inputs = vec![source("Value", "def boundValue : Nat := 3")];
        let plain = CheckedLeanSourceBatch::check(inputs.clone(), false);
        let mut measured = CheckedLeanSourceBatch::check(inputs, true);
        assert!(plain.attempt().unwrap().census.is_none());
        let expected = plain.accepted_context().unwrap();
        measured.attempt.as_mut().unwrap().census.as_mut().unwrap().report =
            serde_json::json!({"batch_rejected": true, "declarations": [], "inputs": ["forged"]});
        let actual = measured.accepted_context().unwrap();
        assert_eq!(expected.source_closure_sha256(), actual.source_closure_sha256());
        assert_eq!(expected.owned_declarations_sha256(), actual.owned_declarations_sha256());
        assert_eq!(expected.owned_declarations(), actual.owned_declarations());

        let mut rejected =
            CheckedLeanSourceBatch::check(vec![source("Bad", "axiom assumed : True")], true);
        rejected.attempt.as_mut().unwrap().census.as_mut().unwrap().report =
            serde_json::json!({"batch_rejected": false, "denominator_status": "complete"});
        assert!(rejected.accepted_context().is_none());
    }

    #[test]
    fn source_module_path_and_payload_changes_bind_distinct_identities() {
        let original = source("Value", "def changed : Nat := 1");
        let baseline = CheckedLeanSourceBatch::check(vec![original.clone()], false);
        let baseline = baseline.accepted_context().unwrap();
        for changed in [
            LeanSourceInput { source: "def changed : Nat := 2".into(), ..original.clone() },
            LeanSourceInput {
                source: "def changed : Nat := 1\n-- exact bytes differ".into(),
                ..original.clone()
            },
            LeanSourceInput { module: "OtherModule".into(), ..original.clone() },
            LeanSourceInput { path: "elsewhere/Value.lean".into(), ..original.clone() },
        ] {
            let batch = CheckedLeanSourceBatch::check(vec![changed.clone()], false);
            let context = batch.accepted_context().unwrap();
            assert_ne!(baseline.source_closure_sha256(), context.source_closure_sha256());
            if changed.source == "def changed : Nat := 2" {
                assert_ne!(
                    baseline.owned_declarations_sha256(),
                    context.owned_declarations_sha256()
                );
            }
        }
    }

    #[test]
    fn dropping_a_supplied_source_changes_roots_and_ownership() {
        let main = source("Main", "def mainValue : Nat := 1");
        let helper = source("Helper", "def helperValue : Nat := 2");
        let full = CheckedLeanSourceBatch::check(vec![main.clone(), helper], false);
        let dropped = CheckedLeanSourceBatch::check(vec![main], false);
        let full = full.accepted_context().unwrap();
        let dropped = dropped.accepted_context().unwrap();
        assert_ne!(full.source_closure_sha256(), dropped.source_closure_sha256());
        assert_ne!(full.owned_declarations_sha256(), dropped.owned_declarations_sha256());
        assert!(full.owns_declaration(&Name::from_string("helperValue")));
        assert!(!dropped.owns_declaration(&Name::from_string("helperValue")));
    }

    #[test]
    fn duplicate_or_empty_module_batches_never_expose_context() {
        for inputs in [
            Vec::new(),
            vec![source("", "def x : Nat := 1")],
            vec![source("Same", "def x : Nat := 1"), source("Same", "def y : Nat := 2")],
        ] {
            let checked = CheckedLeanSourceBatch::check(inputs, true);
            assert!(!checked.errors().is_empty());
            assert!(checked.attempt().is_none());
            assert!(checked.accepted_context().is_none());
        }
    }

    #[test]
    fn indexed_alias_checks_one_snapshot_and_binds_the_exact_mapping() {
        let inputs = vec![
            source("Main", "import Sub.Leaf\ndef uses : Nat := leaf"),
            source("Leaf", "def leaf : Nat := 7"),
        ];
        let aliases = vec![LeanSourceAlias { module: "Sub.Leaf".into(), source_index: 1 }];
        let checked =
            CheckedLeanSourceBatch::check_with_aliases(inputs.clone(), aliases.clone(), true);
        let context = checked.accepted_context().expect("alias is checked with its source");
        assert_eq!(context.sources(), inputs);
        assert_eq!(context.aliases(), aliases);
        assert_eq!(checked.attempt().unwrap().outcomes.len(), 2);
        let census = &checked.attempt().unwrap().census.as_ref().unwrap().report;
        assert_eq!(census["inputs"].as_array().unwrap().len(), 2);
        for name in ["uses", "leaf"] {
            assert_eq!(
                census["declarations"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .filter(|row| row["name"] == name)
                    .count(),
                1
            );
        }
        assert_eq!(
            context.source_closure_sha256(),
            canonical_json_sha256(&(
                "trust.lean.supplied-source-batch/v2",
                inputs.iter().map(|s| (&s.module, &s.path, &s.source)).collect::<Vec<_>>(),
                vec![("Sub.Leaf", 1usize)]
            ))
            .unwrap()
        );
        // The digest does not derive aliases from final declarations or from
        // the optional census. A missing alias still leaves the import refused.
        let absent = CheckedLeanSourceBatch::check(inputs, false);
        assert!(absent.accepted_context().is_none());
        assert!(absent.attempt().unwrap().is_rejected());
    }

    #[test]
    fn alias_name_and_source_index_changes_have_distinct_source_identities() {
        let inputs = vec![
            source("First", "def first : Nat := 1"),
            source("Second", "def second : Nat := 2"),
        ];
        let original = CheckedLeanSourceBatch::check_with_aliases(
            inputs.clone(),
            vec![LeanSourceAlias { module: "Sub.Leaf".into(), source_index: 0 }],
            false,
        );
        let original = original.accepted_context().unwrap();
        for aliases in [
            Vec::new(),
            vec![LeanSourceAlias { module: "Other.Leaf".into(), source_index: 0 }],
            vec![LeanSourceAlias { module: "Sub.Leaf".into(), source_index: 1 }],
        ] {
            let changed = CheckedLeanSourceBatch::check_with_aliases(inputs.clone(), aliases, true);
            let changed = changed.accepted_context().unwrap();
            assert_ne!(original.source_closure_sha256(), changed.source_closure_sha256());
            assert_eq!(original.owned_declarations_sha256(), changed.owned_declarations_sha256());
        }
    }

    #[test]
    fn malformed_alias_keys_or_indices_refuse_before_any_kernel_attempt() {
        for aliases in [
            vec![LeanSourceAlias { module: "".into(), source_index: 0 }],
            vec![LeanSourceAlias { module: "Alias".into(), source_index: 1 }],
            vec![LeanSourceAlias { module: "Alias".into(), source_index: usize::MAX }],
            vec![LeanSourceAlias { module: "Main".into(), source_index: 0 }],
            vec![
                LeanSourceAlias { module: "Alias".into(), source_index: 0 },
                LeanSourceAlias { module: "Alias".into(), source_index: 0 },
            ],
        ] {
            let checked = CheckedLeanSourceBatch::check_with_aliases(
                vec![source("Main", "def value : Nat := 1")],
                aliases.clone(),
                true,
            );
            assert_eq!(checked.aliases(), aliases);
            assert!(!checked.errors().is_empty());
            assert!(checked.attempt().is_none());
            assert!(checked.accepted_context().is_none());
        }
    }

    #[test]
    fn an_alias_does_not_accept_rejected_source_or_forged_census() {
        let mut checked = CheckedLeanSourceBatch::check_with_aliases(
            vec![
                source("Main", "import Sub.Leaf\ndef value : Nat := 1"),
                source("Leaf", "axiom debt : False"),
            ],
            vec![LeanSourceAlias { module: "Sub.Leaf".into(), source_index: 1 }],
            true,
        );
        assert!(checked.attempt().unwrap().is_rejected());
        assert!(checked.accepted_context().is_none());
        checked.attempt.as_mut().unwrap().census.as_mut().unwrap().report =
            serde_json::json!({"batch_rejected": false, "source_aliases": [], "declarations": []});
        assert!(checked.accepted_context().is_none());
    }

    #[test]
    fn unresolved_import_attempts_are_retained_without_marking_missing_keys() {
        let checked = CheckedLeanSourceBatch::check(
            vec![source("Main", "import NotSupplied\ndef ok : Nat := 1")],
            false,
        );
        assert!(checked.accepted_context().is_none());
        let attempt = checked.attempt().unwrap();
        assert_eq!(attempt.outcomes.len(), 1);
        assert!(
            attempt.outcomes[0]
                .errors
                .iter()
                .any(|error| error.message.contains("unresolved import `NotSupplied`"))
        );
    }

    #[test]
    fn false_theorem_keeps_all_attempted_outcomes_but_no_partial_context() {
        let inputs = vec![
            source("Good", "def valid : Nat := 1"),
            source("Bad", "theorem falseProof : 0 = 1 := rfl"),
        ];
        let checked = CheckedLeanSourceBatch::check(inputs.clone(), true);
        assert_eq!(checked.sources(), inputs);
        let attempt = checked.attempt().unwrap();
        assert_eq!(attempt.outcomes.len(), 2);
        assert!(!attempt.outcomes[0].is_rejected());
        assert!(attempt.outcomes[1].is_rejected());
        assert!(checked.session.as_ref().unwrap().is_tainted());
        assert!(checked.accepted_context().is_none());
    }

    #[test]
    fn cycle_refusal_retains_attempted_diagnostics_without_context() {
        let checked = CheckedLeanSourceBatch::check(
            vec![source("Cycle", "def x : Nat := y\ndef y : Nat := x")],
            true,
        );
        assert!(!checked.attempt().unwrap().cycles.is_empty());
        assert!(checked.accepted_context().is_none());
    }

    #[test]
    fn caller_input_mutation_cannot_change_owned_checked_snapshots() {
        let mut inputs = vec![source("Value", "def value : Nat := 1")];
        let checked = CheckedLeanSourceBatch::check(inputs.clone(), false);
        let context = checked.accepted_context().unwrap();
        let root = context.source_closure_sha256().to_string();
        inputs[0].source = "axiom unchecked : False".into();
        inputs[0].module = "Spoofed".into();
        assert_eq!(context.sources()[0].source, "def value : Nat := 1");
        assert_eq!(context.source_closure_sha256(), root);
        assert!(!context.owns_declaration(&Name::from_string("unchecked")));
    }
}
