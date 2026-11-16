// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! One-use continuation of an actual ordinary declaration batch. The original
//! session, lexical context and pre-elaboration model baseline stay together;
//! a final environment and a caller-supplied key cannot construct this product.
//!
//! TG6: each phase is a LOCAL KERNEL FACT of its session. The declaration
//! phase is a `Prepare` fact, keyed by the sources and the session before it.
//! The reporting phase is a `Report` fact: its declarations are the ones the
//! `Prepare` folded into the chain just before it, and its report policy is in
//! the session parameters. So the resolver's preview, which reads bindings,
//! and the HIR owner's finish, which checks models, are two facts of one
//! preparation.

use super::model_check::ModelWatch;
use super::{
    CleanIslandSession, decode_batch, encode_batch, failed_batch, keyed_env, served_parser_prelude,
};
use crate::clean_island_batch::CleanIslandBatch;

#[derive(Clone)]
pub(super) struct PreparedDeclarations {
    batch: CleanIslandBatch,
    preludes: Vec<String>,
    models: Option<ModelWatch>,
}

impl PreparedDeclarations {
    fn failed(islands: usize, why: &str) -> Self {
        Self {
            batch: failed_batch(islands, why),
            preludes: vec![String::new(); islands],
            models: None,
        }
    }

    /// The stored form of a `Prepare` fact's outcome.
    pub(super) fn encode(&self) -> Option<Vec<u8>> {
        let batch = encode_batch(&self.batch)?;
        crate::clean_fact::encode(&(
            batch,
            &self.preludes,
            self.models.as_ref().map(ModelWatch::names),
        ))
    }

    fn decode(bytes: &[u8], islands: usize) -> Self {
        type Stored = (Vec<u8>, Vec<String>, Option<Vec<clean_kernel::Name>>);
        match crate::clean_fact::decode::<Stored>(bytes) {
            Ok((batch, preludes, models)) if preludes.len() == islands => Self {
                batch: decode_batch(&batch, islands),
                preludes,
                models: models.map(ModelWatch::from_names),
            },
            Ok(_) => Self::failed(islands, "a stored preparation has another island count"),
            Err(error) => {
                Self::failed(islands, &format!("a stored preparation does not decode: {error}"))
            }
        }
    }

    pub(super) fn has_anonymous_judgments(&self) -> bool {
        self.batch.has_anonymous_judgments()
    }

    pub(super) fn is_rejected(&self) -> bool {
        self.batch.is_rejected()
    }
}

/// Declarations checked by the kernel, with their reporting still pending.
///
/// This owns the exact source bytes and original session. It cannot be cloned,
/// reseeded from an environment, or applied to another session. Declaration
/// acceptance is not a finite-model verdict. Only [`Self::finish`] runs the
/// selected report policy, updates taint and returns the ordinary completed
/// batch. Census uses its separate checking path.
pub struct PreparedCleanIslandBatch {
    session: CleanIslandSession,
    sources: Vec<String>,
    declarations: PreparedDeclarations,
}

impl PreparedCleanIslandBatch {
    /// Declaration outcomes only: no model or binding report has run yet.
    #[must_use]
    pub fn declarations(&self) -> &CleanIslandBatch {
        &self.declarations.batch
    }

    /// Produce ordinary resolver metadata on a private copy of the actual
    /// declaration state. No model check or declaration elaboration runs, and
    /// neither caller mutation nor metadata reporting consumes this product's
    /// original session, model baseline or one-use reporting continuation.
    #[must_use]
    pub fn declaration_preview(
        &self,
        read_bindings: bool,
    ) -> (CleanIslandSession, CleanIslandBatch) {
        // TG6: the copy forks the keyed session (its chain, log and facts), so
        // its report is a `Report` fact under the preview's own policy.
        let mut session = CleanIslandSession {
            keyed: self.session.keyed.clone(),
            tainted: self.session.tainted,
            model_metadata_reads: Vec::new(),
            model_baseline_read: false,
            model_checks: false,
            binding_reads: read_bindings,
            model_state_budget: self.session.model_state_budget,
            model_work_limit: self.session.model_work_limit,
            model_heartbeats_per_work: self.session.model_heartbeats_per_work,
            standin_imports: self.session.standin_imports.clone(),
        };
        let source_refs: Vec<&str> = self.sources.iter().map(String::as_str).collect();
        let batch = session.report(&source_refs, self.declarations.clone());
        (session, batch)
    }

    /// Select the ordinary finite-model report policy before finishing.
    pub fn enable_model_checks(&mut self) {
        self.session.enable_model_checks();
    }

    /// Select binding/seal reads without enabling finite-model checking.
    pub fn enable_binding_reads(&mut self) {
        self.session.enable_binding_reads();
    }

    /// Apply the same default state budget as an ordinary checking session.
    pub fn set_model_state_budget(&mut self, states: u64) {
        self.session.set_model_state_budget(states);
    }

    /// Apply the ordinary model work and heartbeat limits without changing
    /// either the source inventory or its already checked declarations.
    pub fn set_model_kernel_limits(&mut self, work_limit: u64, heartbeats_per_work: u64) {
        self.session.set_model_kernel_limits(work_limit, heartbeats_per_work);
    }

    /// Finish once using the original pre-elaboration delta. This performs no
    /// declaration elaboration. Unsafe models or unreadable binding data retain
    /// the ordinary rejection, taint and disclosure rules.
    #[must_use]
    pub fn finish(self) -> (CleanIslandSession, CleanIslandBatch) {
        let Self { mut session, sources, declarations } = self;
        let source_refs: Vec<&str> = sources.iter().map(String::as_str).collect();
        let batch = session.report(&source_refs, declarations);
        (session, batch)
    }
}

impl CleanIslandSession {
    /// Check the complete ordinary header-first declaration batch and retain
    /// its actual continuation for a later reporting owner. No census or
    /// arbitrary environment can be supplied as an equivalent producer.
    #[must_use]
    pub fn prepare_all(mut self, sources: &[&str]) -> PreparedCleanIslandBatch {
        let declarations = self.prepare(sources);
        PreparedCleanIslandBatch {
            session: self,
            sources: sources.iter().map(|source| (*source).to_owned()).collect(),
            declarations,
        }
    }

    /// The declaration phase as a `Prepare` fact (TG6).
    fn prepare(&mut self, sources: &[&str]) -> PreparedDeclarations {
        let op = keyed_env::LoggedOp::Prepare(sources.iter().map(|s| (*s).to_string()).collect());
        let declarations = match self.keyed.lookup(op, &self.params()) {
            keyed_env::Lookup::Hit(stored) => PreparedDeclarations::decode(&stored, sources.len()),
            keyed_env::Lookup::Miss(mut pending) => {
                if let Err(why) = self.ensure_live() {
                    PreparedDeclarations::failed(sources.len(), &why)
                } else {
                    self.keyed.begin(&mut pending);
                    let declarations = self.prepare_declarations(sources, true);
                    let rejected = declarations.is_rejected();
                    self.keyed.finish(
                        *pending,
                        declarations.encode(),
                        rejected,
                        declarations.has_anonymous_judgments(),
                        &self.model_metadata_reads,
                        self.model_baseline_read,
                    );
                    declarations
                }
            }
        };
        self.tainted |= declarations.is_rejected();
        declarations
    }

    /// The reporting phase of `declarations` as a `Report` fact (TG6): they
    /// are the outcome of the `Prepare` fact the chain folded last, and the
    /// report policy is in the session parameters.
    fn report(&mut self, sources: &[&str], declarations: PreparedDeclarations) -> CleanIslandBatch {
        let op = keyed_env::LoggedOp::Report(sources.iter().map(|s| (*s).to_string()).collect());
        let batch = match self.keyed.lookup(op, &self.params()) {
            keyed_env::Lookup::Hit(stored) => decode_batch(&stored, sources.len()),
            keyed_env::Lookup::Miss(mut pending) => {
                if let Err(why) = self.ensure_live() {
                    failed_batch(sources.len(), &why)
                } else {
                    self.keyed.begin(&mut pending);
                    let batch = self.finish_declarations(sources, declarations);
                    let rejected = batch.is_rejected();
                    self.keyed.finish(
                        *pending,
                        encode_batch(&batch),
                        rejected,
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

    pub(super) fn prepare_declarations(
        &mut self,
        sources: &[&str],
        defer_reporting: bool,
    ) -> PreparedDeclarations {
        self.model_metadata_reads.clear();
        self.model_baseline_read = false;
        let (served, imported) = self.serve_trust_imports_named(sources);
        let preludes: Vec<String> =
            imported.iter().map(|modules| served_parser_prelude(modules)).collect();
        let models = if defer_reporting { self.deferred_model_watch() } else { self.model_watch() };
        self.model_baseline_read = defer_reporting && models.is_some();
        // Inside a keyed operation (`CheckAll` or `Prepare`, or their replay),
        // so this is that operation's own environment.
        let (env, file_ctx, _) = self.keyed.parts_mut();
        let mut batch = if preludes.iter().all(String::is_empty) {
            crate::clean_island_batch::check_islands_batched(env, file_ctx, sources)
        } else {
            crate::clean_island_batch::check_islands_batched_with_preludes(
                env, file_ctx, sources, &preludes,
            )
        };
        for (island, diagnostic) in served {
            if let Some(outcome) = batch.outcomes.get_mut(island) {
                outcome.standin_imports.clear();
                outcome.errors.push(diagnostic);
            }
        }
        self.tainted |= batch.is_rejected();
        PreparedDeclarations { batch, preludes, models }
    }

    pub(super) fn finish_declarations(
        &mut self,
        sources: &[&str],
        declarations: PreparedDeclarations,
    ) -> CleanIslandBatch {
        self.model_metadata_reads.clear();
        self.model_baseline_read = false;
        let PreparedDeclarations { mut batch, preludes, models } = declarations;
        // Capturing a deferred baseline never opts into reporting. In
        // particular a binding-only import must not become a report merely
        // because the continuation retained its pre-elaboration names.
        let models = if self.model_watch_enabled() { models } else { None };
        if batch.cycles.is_empty() {
            self.check_declared_models(models, sources, &preludes, &mut batch.outcomes);
        }
        self.tainted |= batch.is_rejected();
        self.record_standin_imports(&batch.outcomes);
        batch
    }
}

#[cfg(test)]
mod tests;
