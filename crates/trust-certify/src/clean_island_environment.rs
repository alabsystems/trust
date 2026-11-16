// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! A compiler invocation's immutable checked-island environment handoff.
//!
//! The producer checks the same sources and callees it records. There is no
//! constructor accepting an arbitrary environment plus a claimed key. The
//! compiler stores this type on its Session, never in a process-global cache.
//! Its one-use ordinary reporting continuation retains the actual FileContext
//! in this invocation. This is not a cache of body faithfulness, program
//! admissions or finite-model verdicts. Cross-build reuse is not this type's:
//! the producer's session reads LOCAL KERNEL FACTS when the compiler hands it a
//! context (TG6, [`crate::clean_fact`]), so its declaration and reporting
//! phases may each import a fact; the handoff below is the same either way.

use std::sync::{Arc, Mutex};

use crate::clean_island::{
    CleanIslandSession, KernelEnvironment, PreparedCleanIslandBatch, RustCallee,
    RustCalleeDeclRefusal,
};
use crate::clean_island_batch::CleanIslandBatch;

struct Entry {
    sources: Vec<String>,
    callees: Vec<RustCallee>,
    environment: Option<Arc<KernelEnvironment>>,
    reporting: Mutex<Option<PreparedCleanIslandBatch>>,
}

/// Share only within one compiler Session. The exact ordered input inventory
/// determines a hit; an additional macro island or deferred suffix is a miss.
#[derive(Default)]
pub struct CheckedIslandEnvironment {
    entry: Option<Entry>,
}

impl CheckedIslandEnvironment {
    /// Check an ordinary fresh batch and capture its exact inputs and result.
    ///
    /// `read_bindings` enables the resolver's metadata extraction only; it
    /// never enables model checking. The returned private declaration preview
    /// keeps diagnostics and binding/seal metadata available without consuming
    /// the original reporting continuation. Only an accepted, untainted
    /// environment enters the immutable snapshot and retains a continuation.
    /// Census checking has a different recipe and must not use this producer.
    ///
    /// `facts` is the compiler's local kernel fact context (TG6), or `None`
    /// for a session that checks afresh.
    pub fn check(
        sources: &[String],
        callees: &[RustCallee],
        read_bindings: bool,
        facts: Option<Arc<crate::clean_fact::FactContext>>,
    ) -> Result<(Self, CleanIslandSession, CleanIslandBatch), RustCalleeDeclRefusal> {
        let mut session = CleanIslandSession::new();
        if let Some(facts) = facts {
            session.enable_facts(facts);
        }
        session.declare_rust_callees(callees)?;
        let source_refs: Vec<&str> = sources.iter().map(String::as_str).collect();
        let prepared = session.prepare_all(&source_refs);
        let (session, batch) = prepared.declaration_preview(read_bindings);
        let environment = if batch.is_rejected() || session.is_tainted() {
            None
        } else {
            session.environment().cloned().map(Arc::new)
        };
        let reporting = environment.is_some().then_some(prepared);
        let checked = Self {
            entry: Some(Entry {
                sources: sources.to_vec(),
                callees: callees.to_vec(),
                environment,
                reporting: Mutex::new(reporting),
            }),
        };
        Ok((checked, session, batch))
    }

    /// Outer `None` is a miss; `Some(None)` is an exactly matching rejection.
    /// A hit clones the same immutable Arc and performs no elaboration.
    #[must_use]
    pub fn lookup(
        &self,
        sources: &[String],
        callees: &[RustCallee],
    ) -> Option<Option<Arc<KernelEnvironment>>> {
        self.entry
            .as_ref()
            .filter(|entry| entry.sources == sources && entry.callees == callees)
            .map(|entry| entry.environment.clone())
    }

    /// Take the actual original reporting session once, for an exact accepted
    /// declaration inventory. Immutable MIR snapshots remain available after
    /// this handoff. A poisoned or already-consumed continuation is a miss.
    #[must_use]
    pub fn take_for_reporting(
        &mut self,
        sources: &[String],
        callees: &[RustCallee],
    ) -> Option<PreparedCleanIslandBatch> {
        let entry = self.entry.as_mut()?;
        if entry.sources != sources || entry.callees != callees || entry.environment.is_none() {
            return None;
        }
        entry.reporting.get_mut().ok()?.take()
    }
}

#[cfg(test)]
mod tests {
    use clean_kernel::Name;

    use super::*;

    fn sources(texts: &[&str]) -> Vec<String> {
        texts.iter().map(|text| (*text).to_owned()).collect()
    }

    fn callee() -> RustCallee {
        RustCallee {
            clean_name: "rust_value".into(),
            params: vec![trust_types::Ty::Bool],
            result: trust_types::Ty::Bool,
        }
    }

    #[test]
    fn exact_inputs_reuse_the_checked_environment_and_preserve_file_state() {
        let input = sources(&[
            "namespace Shared\ndef value : Bool := true\nend Shared\n",
            "open Shared\ntheorem exact : value = true := rfl\n",
        ]);
        let callees = vec![callee()];
        let (checked, mut session, batch) =
            CheckedIslandEnvironment::check(&input, &callees, true, None).unwrap();
        assert!(!batch.is_rejected(), "{batch:?}");
        assert!(!session.is_tainted());
        let first = checked.lookup(&input, &callees).unwrap().unwrap();
        let again = checked.lookup(&input, &callees).unwrap().unwrap();
        assert!(Arc::ptr_eq(&first, &again));
        assert!(first.get_const(&Name::from_string("exact")).is_some());
        assert!(!session.check("def later : Bool := false").is_rejected());
        assert!(first.get_const(&Name::from_string("later")).is_none());
        assert!(Arc::ptr_eq(&first, &checked.lookup(&input, &callees).unwrap().unwrap()));

        let mut changed = input.clone();
        changed.reverse();
        assert!(checked.lookup(&changed, &callees).is_none());
        let mut changed = input.clone();
        changed[0] = changed[0].replace("true", "false");
        assert!(checked.lookup(&changed, &callees).is_none());
        for extra in
            ["theorem macro_added : true = true := rfl", "theorem deferred := trust_import_body"]
        {
            let mut changed = input.clone();
            changed.push(extra.into());
            assert!(checked.lookup(&changed, &callees).is_none());
        }
        assert!(checked.lookup(&input[..1], &callees).is_none());
        assert!(checked.lookup(&input, &[]).is_none());
        let mut changed = callees.clone();
        changed[0].params = vec![trust_types::Ty::u64()];
        assert!(checked.lookup(&input, &changed).is_none());
        let mut changed = callees.clone();
        changed[0].result = trust_types::Ty::u64();
        assert!(checked.lookup(&input, &changed).is_none());
        let mut changed = callees.clone();
        changed[0].clean_name.push_str("_other");
        assert!(checked.lookup(&input, &changed).is_none());
    }

    #[test]
    fn the_pre_admission_prefix_is_checkable_where_its_deferred_suffix_is_not() {
        // E9-DEFERRED-SUFFIX-ENV-1. The second island names an E6 import, so it
        // is checked only after program admissions exist. A fresh producer
        // declares none, so the whole inventory is rejected: the environment
        // the code-generation re-check used to ask for. The mint's prefix is
        // accepted and holds the minted declaration and nothing deferred.
        let input = sources(&[
            "def spec_same_code (a b : UInt8) : Bool := decide (a = b)",
            "theorem same_code_is_exact (a b : UInt8) :\n    \
             trust_import_k__same_code a b = spec_same_code a b := rfl",
        ]);
        let prefix = crate::clean_island::pre_admission_island_count(input.as_slice());
        assert_eq!(prefix, 1);
        let (whole, _, batch) = CheckedIslandEnvironment::check(&input, &[], false, None).unwrap();
        assert!(batch.is_rejected(), "{batch:?}");
        assert!(matches!(whole.lookup(&input, &[]), Some(None)));
        let mint = &input[..prefix];
        let (checked, session, batch) =
            CheckedIslandEnvironment::check(mint, &[], false, None).unwrap();
        assert!(!batch.is_rejected(), "{batch:?}");
        assert!(!session.is_tainted());
        let env = checked.lookup(mint, &[]).unwrap().unwrap();
        assert!(env.get_const(&Name::from_string("spec_same_code")).is_some());
        assert!(env.get_const(&Name::from_string("same_code_is_exact")).is_none());
    }

    #[test]
    fn a_rejected_sibling_never_exports_a_partial_environment() {
        let input = sources(&["def good : Bool := true", "theorem bad : true = false := rfl"]);
        let (checked, session, batch) =
            CheckedIslandEnvironment::check(&input, &[], false, None).unwrap();
        assert!(batch.is_rejected());
        assert!(session.is_tainted());
        assert!(session.environment().is_none());
        assert!(matches!(checked.lookup(&input, &[]), Some(None)));
        assert!(checked.lookup(&input[..1], &[]).is_none());
        let other = CheckedIslandEnvironment::default();
        assert!(other.lookup(&input, &[]).is_none());
    }

    #[test]
    fn binding_metadata_stays_with_the_producer_and_its_environment_is_checked() {
        let input = sources(&[
            "import Trust.Binding\nopen Trust.Protocol\ndef policy : Trust.Protocol.Binding := binds \"n\" [\"Tick\"] []\n",
        ]);
        let (checked, _, batch) = CheckedIslandEnvironment::check(&input, &[], true, None).unwrap();
        assert!(!batch.is_rejected(), "{batch:?}");
        assert_eq!(batch.outcomes[0].bindings.len(), 1);
        assert!(batch.outcomes[0].model_checks.is_empty());
        let env = checked.lookup(&input, &[]).unwrap().unwrap();
        assert!(env.get_const(&Name::from_string("policy")).is_some());
        let (plain, _, batch) = CheckedIslandEnvironment::check(&input, &[], false, None).unwrap();
        assert!(!batch.is_rejected(), "{batch:?}");
        assert!(batch.outcomes[0].bindings.is_empty());
        let plain = plain.lookup(&input, &[]).unwrap().unwrap();
        let name = Name::from_string("policy");
        assert_eq!(
            env.get_const(&name).map(|constant| (&constant.type_, &constant.value)),
            plain.get_const(&name).map(|constant| (&constant.type_, &constant.value)),
        );
    }

    #[test]
    fn invalid_callee_declarations_cannot_produce_a_cache_entry() {
        let input = sources(&["def value : Bool := true"]);
        let mut collision = callee();
        collision.clean_name = "Bool".into();
        assert!(CheckedIslandEnvironment::check(&input, &[collision], false, None).is_err());
    }

    #[test]
    fn reporting_token_is_exact_one_use_and_independent_of_preview_and_snapshot() {
        fn send_and_sync<T: Send + Sync>() {}
        send_and_sync::<CheckedIslandEnvironment>();
        let input = sources(&[
            "namespace Shared\ndef value : Bool := true\nend Shared\nopen Shared\n",
            "theorem exact : value = true := rfl\n",
        ]);
        let callees = vec![callee()];
        let (mut checked, mut preview, batch) =
            CheckedIslandEnvironment::check(&input, &callees, true, None).unwrap();
        assert!(!batch.is_rejected());
        let snapshot = checked.lookup(&input, &callees).unwrap().unwrap();
        assert!(!preview.check("def preview_only : Bool := true").is_rejected());
        let mut changed = input.clone();
        changed.reverse();
        assert!(checked.take_for_reporting(&changed, &callees).is_none());
        assert!(checked.take_for_reporting(&input, &[]).is_none());
        let mut prepared = checked.take_for_reporting(&input, &callees).unwrap();
        prepared.enable_model_checks();
        prepared.enable_binding_reads();
        let (mut continued, batch) = prepared.finish();
        assert!(!batch.is_rejected());
        assert!(
            continued
                .environment()
                .unwrap()
                .get_const(&Name::from_string("preview_only"))
                .is_none()
        );
        assert!(!continued.check("theorem still_open : value = true := rfl").is_rejected());
        assert!(checked.take_for_reporting(&input, &callees).is_none());
        assert!(Arc::ptr_eq(&snapshot, &checked.lookup(&input, &callees).unwrap().unwrap()));
        assert!(snapshot.get_const(&Name::from_string("still_open")).is_none());
    }

    #[test]
    fn rejected_preview_never_publishes_a_reporting_token() {
        let input = sources(&["import Trust.Binding\nopen Trust.Protocol\n\
             def cell : Trust.Protocol.Seal := seals \"\" [] [] [] []\n"]);
        let (mut checked, preview, batch) =
            CheckedIslandEnvironment::check(&input, &[], true, None).unwrap();
        assert!(batch.is_rejected());
        assert!(preview.is_tainted());
        assert!(checked.take_for_reporting(&input, &[]).is_none());
        assert!(matches!(checked.lookup(&input, &[]), Some(None)));

        // A MIR declaration producer checks no metadata, but its actual HIR
        // finisher still rejects the unreadable data under the HIR policy.
        let (mut checked, _, batch) =
            CheckedIslandEnvironment::check(&input, &[], false, None).unwrap();
        assert!(!batch.is_rejected());
        let mut prepared = checked.take_for_reporting(&input, &[]).unwrap();
        prepared.enable_model_checks();
        prepared.enable_binding_reads();
        let (session, batch) = prepared.finish();
        assert!(batch.is_rejected());
        assert!(session.is_tainted());
        assert!(session.environment().is_none());
    }
}
