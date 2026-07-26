// trust_vcgen/memory_ordering/aarch64.rs: AArch64 atomic proof-obligation consumers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::{
    Aarch64AtomicSemanticFact, Aarch64ExclusiveMonitorSemantics, Aarch64SyncBoundarySemanticFact,
    MemoryAccessKind, MemoryOrderingSemantics,
};

use super::atomic_access::AtomicAccessEntry;
use super::checker::MemoryModelChecker;
use crate::data_race::{AccessKind, MemoryOrdering};

/// Access-log indices that witness one AArch64 release/acquire synchronization pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Aarch64ReleaseAcquireWitness {
    /// Atomic write with release-or-stronger ordering.
    pub release_access_index: usize,
    /// Atomic read with acquire-or-stronger ordering.
    pub acquire_access_index: usize,
}

/// Observed result reported by an AArch64 store-exclusive instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Aarch64StoreConditionalStatus {
    /// The conditional store committed.
    Succeeded,
    /// The conditional store did not commit.
    Failed,
}

/// Evidence for one load-exclusive/store-exclusive monitor boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Aarch64ExclusiveMonitorWitness {
    /// Atomic read that establishes the local exclusive-monitor reservation.
    pub load_reserve_access_index: usize,
    /// Atomic write attempted by the store-conditional instruction.
    pub store_conditional_access_index: usize,
    /// True only when proof input ties the store-conditional to the reservation.
    pub reservation_observed: bool,
    /// True only when invalidation semantics were checked and no intervening
    /// invalidation defeats a successful store-conditional.
    pub no_intervening_invalidation: bool,
    /// Status result reported by the store-conditional instruction.
    pub store_status: Option<Aarch64StoreConditionalStatus>,
}

/// AArch64 barrier shareability domain for DMB/DSB-style memory barriers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Aarch64BarrierDomain {
    FullSystem,
    InnerShareable,
    OuterShareable,
    NonShareable,
}

/// AArch64 barrier access class.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Aarch64BarrierEffect {
    Full,
    Loads,
    Stores,
}

/// Typed proof fact for one AArch64 memory barrier boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Aarch64BarrierSemanticFact {
    /// Barrier opcode such as DMB or DSB.
    pub opcode: String,
    /// Required shareability domain decoded from the barrier option.
    pub domain: Aarch64BarrierDomain,
    /// Required load/store/full barrier effect decoded from the barrier option.
    pub effect: Aarch64BarrierEffect,
    /// Required ordering strength for the proof model.
    pub ordering: MemoryOrderingSemantics,
    /// Witnesses still carried by the source fact. Any entry not consumed by the
    /// proof model keeps the boundary rejected.
    pub missing_witnesses: Vec<String>,
}

/// Access-log indices and decoded option evidence for one AArch64 barrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Aarch64BarrierWitness {
    /// Access before the barrier in the same thread's program order.
    pub before_access_index: usize,
    /// Fence entry representing the barrier instruction.
    pub barrier_access_index: usize,
    /// Access after the barrier in the same thread's program order.
    pub after_access_index: usize,
    /// Decoded shareability domain observed by the proof input.
    pub observed_domain: Option<Aarch64BarrierDomain>,
    /// Decoded barrier effect observed by the proof input.
    pub observed_effect: Option<Aarch64BarrierEffect>,
}

/// Narrow AArch64 boundary for which witness production was attempted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Aarch64WitnessBoundary {
    /// STLR/LDAR-style release/acquire synchronization.
    ReleaseAcquire,
    /// LDAXR/STLXR-style exclusive-monitor success boundary.
    ExclusiveMonitor,
}

/// Reviewed certificate that no producer-side witness exists inside the narrow
/// supported AArch64 boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Aarch64WitnessAbsenceCertificate {
    /// Boundary whose witness was requested.
    pub boundary: Aarch64WitnessBoundary,
    /// Candidate access-log indices inspected while producing the certificate.
    pub candidate_access_indices: Vec<usize>,
    /// Evidence that was present but insufficient for a proof-grade witness.
    pub available_evidence: Vec<String>,
    /// Evidence still missing; any entry keeps the boundary fail-closed.
    pub missing_witnesses: Vec<String>,
    /// Stable human-readable diagnostic for VCs, reports, and tests.
    pub diagnostic: String,
}

impl Aarch64WitnessAbsenceCertificate {
    #[must_use]
    pub fn is_fail_closed(&self) -> bool {
        !self.missing_witnesses.is_empty()
    }
}

/// Producer-side evidence for one AArch64 release/acquire boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Aarch64ReleaseAcquireWitnessEvidence {
    /// A witness was produced inside the narrow supported boundary.
    Produced { witness: Aarch64ReleaseAcquireWitness, evidence: Vec<String> },
    /// No witness is available; the certificate explains what is absent.
    Absent { certificate: Aarch64WitnessAbsenceCertificate },
}

impl Aarch64ReleaseAcquireWitnessEvidence {
    #[must_use]
    pub fn witness(&self) -> Option<Aarch64ReleaseAcquireWitness> {
        match self {
            Self::Produced { witness, .. } => Some(*witness),
            Self::Absent { .. } => None,
        }
    }

    #[must_use]
    pub fn absence_certificate(&self) -> Option<&Aarch64WitnessAbsenceCertificate> {
        match self {
            Self::Produced { .. } => None,
            Self::Absent { certificate } => Some(certificate),
        }
    }
}

/// Producer-side evidence for one AArch64 exclusive-monitor boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Aarch64ExclusiveMonitorWitnessEvidence {
    /// A witness was produced inside the narrow supported boundary.
    Produced { witness: Aarch64ExclusiveMonitorWitness, evidence: Vec<String> },
    /// No witness is available; the certificate explains what is absent.
    Absent { certificate: Aarch64WitnessAbsenceCertificate },
}

impl Aarch64ExclusiveMonitorWitnessEvidence {
    #[must_use]
    pub fn witness(&self) -> Option<Aarch64ExclusiveMonitorWitness> {
        match self {
            Self::Produced { witness, .. } => Some(*witness),
            Self::Absent { .. } => None,
        }
    }

    #[must_use]
    pub fn absence_certificate(&self) -> Option<&Aarch64WitnessAbsenceCertificate> {
        match self {
            Self::Produced { .. } => None,
            Self::Absent { certificate } => Some(certificate),
        }
    }
}

/// Result of attempting to consume an AArch64 memory-order proof obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Aarch64ProofObligationConsumption {
    /// True only when every required witness for the narrow obligation was consumed.
    pub accepted_for_proof_grade: bool,
    /// Witnesses matched against the checker state.
    pub consumed_witnesses: Vec<String>,
    /// Witnesses still missing; any entry keeps the obligation fail-closed.
    pub missing_witnesses: Vec<String>,
    /// Human-readable diagnostic for release gates and tests.
    pub diagnostic: String,
}

impl Aarch64ProofObligationConsumption {
    #[must_use]
    pub fn is_accepted(&self) -> bool {
        self.accepted_for_proof_grade
    }
}

impl MemoryModelChecker {
    /// Produce a witness for the narrow STLR/LDAR-style release/acquire
    /// boundary, or return a fail-closed absence certificate.
    #[must_use]
    pub fn produce_aarch64_release_acquire_witness(
        &self,
        release_fact: &Aarch64AtomicSemanticFact,
        acquire_fact: &Aarch64AtomicSemanticFact,
    ) -> Aarch64ReleaseAcquireWitnessEvidence {
        let mut shape_missing = Vec::new();
        collect_fact_shape_requirements(release_fact, FactRole::Release, &mut shape_missing);
        collect_fact_shape_requirements(acquire_fact, FactRole::Acquire, &mut shape_missing);

        if release_fact.exclusive_monitor != Aarch64ExclusiveMonitorSemantics::None {
            collect_monitor_witnesses(release_fact, &mut shape_missing);
        }
        if acquire_fact.exclusive_monitor != Aarch64ExclusiveMonitorSemantics::None {
            collect_monitor_witnesses(acquire_fact, &mut shape_missing);
        }

        collect_out_of_boundary_fact_witnesses(
            release_fact,
            RELEASE_ACQUIRE_PRODUCIBLE_WITNESSES,
            &mut shape_missing,
        );
        collect_out_of_boundary_fact_witnesses(
            acquire_fact,
            RELEASE_ACQUIRE_PRODUCIBLE_WITNESSES,
            &mut shape_missing,
        );

        let release_candidates = self.aarch64_candidate_accesses(
            release_fact,
            MemoryAccessKind::Write,
            MemoryOrdering::Release,
        );
        let acquire_candidates = self.aarch64_candidate_accesses(
            acquire_fact,
            MemoryAccessKind::Read,
            MemoryOrdering::Acquire,
        );

        if release_candidates.is_empty() {
            shape_missing.push("release ordering event".to_string());
        }
        if acquire_candidates.is_empty() {
            shape_missing.push("acquire ordering event".to_string());
        }

        let mut best_absence = None;
        for &(release_index, release_entry) in &release_candidates {
            for &(acquire_index, acquire_entry) in &acquire_candidates {
                if release_index == acquire_index {
                    continue;
                }

                let mut available = Vec::new();
                let mut missing = shape_missing.clone();
                collect_release_acquire_pair_evidence(
                    release_index,
                    release_entry,
                    acquire_index,
                    acquire_entry,
                    self,
                    &mut available,
                    &mut missing,
                );

                sort_dedup(&mut available);
                sort_dedup(&mut missing);

                if missing.is_empty() {
                    return Aarch64ReleaseAcquireWitnessEvidence::Produced {
                        witness: Aarch64ReleaseAcquireWitness {
                            release_access_index: release_index,
                            acquire_access_index: acquire_index,
                        },
                        evidence: available,
                    };
                }

                remember_best_absence(
                    &mut best_absence,
                    vec![release_index, acquire_index],
                    available,
                    missing,
                );
            }
        }

        let (candidate_access_indices, available_evidence, missing_witnesses) =
            best_absence.unwrap_or_else(|| (Vec::new(), Vec::new(), sorted_deduped(shape_missing)));

        Aarch64ReleaseAcquireWitnessEvidence::Absent {
            certificate: absence_certificate(
                Aarch64WitnessBoundary::ReleaseAcquire,
                candidate_access_indices,
                available_evidence,
                missing_witnesses,
            ),
        }
    }

    /// Produce a witness for the narrow LDAXR/STLXR success boundary, or return
    /// a fail-closed absence certificate.
    ///
    /// The producer only certifies a minimal in-log monitor success: same
    /// location, same non-empty thread, load-exclusive before store-exclusive,
    /// adjacent access-log entries, an explicit synchronization edge/HB path, and
    /// a successful store-conditional status.
    #[must_use]
    pub fn produce_aarch64_exclusive_monitor_witness(
        &self,
        load_reserve_fact: &Aarch64AtomicSemanticFact,
        store_conditional_fact: &Aarch64AtomicSemanticFact,
        store_status: Option<Aarch64StoreConditionalStatus>,
    ) -> Aarch64ExclusiveMonitorWitnessEvidence {
        let mut shape_missing = Vec::new();
        collect_fact_shape_requirements(load_reserve_fact, FactRole::Acquire, &mut shape_missing);
        collect_fact_shape_requirements(
            store_conditional_fact,
            FactRole::Release,
            &mut shape_missing,
        );
        collect_exclusive_pair_shape_requirements(
            load_reserve_fact,
            store_conditional_fact,
            &mut shape_missing,
        );

        collect_out_of_boundary_fact_witnesses(
            load_reserve_fact,
            EXCLUSIVE_MONITOR_PRODUCIBLE_WITNESSES,
            &mut shape_missing,
        );
        collect_out_of_boundary_fact_witnesses(
            store_conditional_fact,
            EXCLUSIVE_MONITOR_PRODUCIBLE_WITNESSES,
            &mut shape_missing,
        );

        let load_candidates = self.aarch64_candidate_accesses(
            load_reserve_fact,
            MemoryAccessKind::Read,
            MemoryOrdering::Acquire,
        );
        let store_candidates = self.aarch64_candidate_accesses(
            store_conditional_fact,
            MemoryAccessKind::Write,
            MemoryOrdering::Release,
        );

        if load_candidates.is_empty() {
            shape_missing.push("acquire ordering event".to_string());
        }
        if store_candidates.is_empty() {
            shape_missing.push("release ordering event".to_string());
        }

        let mut best_absence = None;
        for &(load_index, load_entry) in &load_candidates {
            for &(store_index, store_entry) in &store_candidates {
                if load_index == store_index {
                    continue;
                }

                let mut available = Vec::new();
                let mut missing = shape_missing.clone();
                collect_exclusive_monitor_pair_evidence(
                    ExclusiveMonitorPairEvidence {
                        load_index,
                        load_entry,
                        store_index,
                        store_entry,
                        store_status,
                    },
                    self,
                    &mut available,
                    &mut missing,
                );

                sort_dedup(&mut available);
                sort_dedup(&mut missing);

                if missing.is_empty() {
                    return Aarch64ExclusiveMonitorWitnessEvidence::Produced {
                        witness: Aarch64ExclusiveMonitorWitness {
                            load_reserve_access_index: load_index,
                            store_conditional_access_index: store_index,
                            reservation_observed: true,
                            no_intervening_invalidation: true,
                            store_status,
                        },
                        evidence: available,
                    };
                }

                remember_best_absence(
                    &mut best_absence,
                    vec![load_index, store_index],
                    available,
                    missing,
                );
            }
        }

        let (candidate_access_indices, available_evidence, missing_witnesses) =
            best_absence.unwrap_or_else(|| (Vec::new(), Vec::new(), sorted_deduped(shape_missing)));

        Aarch64ExclusiveMonitorWitnessEvidence::Absent {
            certificate: absence_certificate(
                Aarch64WitnessBoundary::ExclusiveMonitor,
                candidate_access_indices,
                available_evidence,
                missing_witnesses,
            ),
        }
    }

    /// Consume the narrow STLR/LDAR-style release/acquire proof obligation.
    ///
    /// This intentionally does not accept exclusive-monitor instructions. LDAXR,
    /// STLXR, LDXR, and STXR require monitor-reservation, invalidation, thread,
    /// and status witnesses that are not represented by the scalar atomic log.
    #[must_use]
    pub fn consume_aarch64_release_acquire_obligation(
        &self,
        release_fact: &Aarch64AtomicSemanticFact,
        acquire_fact: &Aarch64AtomicSemanticFact,
        witness: Aarch64ReleaseAcquireWitness,
    ) -> Aarch64ProofObligationConsumption {
        let mut consumed = Vec::new();
        let mut missing = Vec::new();

        collect_fact_shape_requirements(release_fact, FactRole::Release, &mut missing);
        collect_fact_shape_requirements(acquire_fact, FactRole::Acquire, &mut missing);

        if release_fact.exclusive_monitor != Aarch64ExclusiveMonitorSemantics::None {
            collect_monitor_witnesses(release_fact, &mut missing);
        }
        if acquire_fact.exclusive_monitor != Aarch64ExclusiveMonitorSemantics::None {
            collect_monitor_witnesses(acquire_fact, &mut missing);
        }

        let release_entry = self.log.entries().get(witness.release_access_index);
        let acquire_entry = self.log.entries().get(witness.acquire_access_index);

        match release_entry {
            Some(entry)
                if access_consumes_ordering(
                    entry.access_kind,
                    MemoryAccessKind::Write,
                    MemoryOrdering::Release,
                ) =>
            {
                consumed.push("release ordering event".to_string());
            }
            Some(_) => missing.push("release ordering event".to_string()),
            None => missing.push("release access-log event".to_string()),
        }

        match acquire_entry {
            Some(entry)
                if access_consumes_ordering(
                    entry.access_kind,
                    MemoryAccessKind::Read,
                    MemoryOrdering::Acquire,
                ) =>
            {
                consumed.push("acquire ordering event".to_string());
            }
            Some(_) => missing.push("acquire ordering event".to_string()),
            None => missing.push("acquire access-log event".to_string()),
        }

        if let (Some(release), Some(acquire)) = (release_entry, acquire_entry) {
            if release.location == acquire.location {
                consumed.push("same atomic location witness".to_string());
            } else {
                missing.push("same atomic location witness".to_string());
            }

            if !release.thread_id.is_empty()
                && !acquire.thread_id.is_empty()
                && release.thread_id != acquire.thread_id
            {
                consumed.push("thread identity".to_string());
            } else {
                missing.push("cross-thread identity witness".to_string());
            }
        }

        if self.hb.successors(witness.release_access_index).contains(&witness.acquire_access_index)
        {
            consumed.push("synchronization edge".to_string());
        } else {
            missing.push("synchronization edge".to_string());
        }

        if self.hb.happens_before(witness.release_access_index, witness.acquire_access_index) {
            consumed.push("happens-before witness".to_string());
        } else {
            missing.push("happens-before witness".to_string());
        }

        carry_unconsumed_fact_witnesses(release_fact, &consumed, &mut missing);
        carry_unconsumed_fact_witnesses(acquire_fact, &consumed, &mut missing);

        sort_dedup(&mut consumed);
        sort_dedup(&mut missing);

        let accepted = missing.is_empty();
        let diagnostic = if accepted {
            format!(
                "AArch64 release/acquire proof-grade accepted after consuming witnesses: {}",
                consumed.join(", ")
            )
        } else {
            format!(
                "AArch64 release/acquire obligation remains fail-closed; missing witnesses: {}; consumed witnesses: {}",
                missing.join(", "),
                if consumed.is_empty() { "none".to_string() } else { consumed.join(", ") }
            )
        };

        Aarch64ProofObligationConsumption {
            accepted_for_proof_grade: accepted,
            consumed_witnesses: consumed,
            missing_witnesses: missing,
            diagnostic,
        }
    }

    /// Consume a narrow LDAXR/STLXR-style exclusive-monitor proof boundary.
    ///
    /// This is a success-only boundary. A failed store-conditional status can be
    /// observed, but it does not establish a committed release write and remains
    /// fail-closed for proof-grade synchronization.
    #[must_use]
    pub fn consume_aarch64_exclusive_monitor_obligation(
        &self,
        load_reserve_fact: &Aarch64AtomicSemanticFact,
        store_conditional_fact: &Aarch64AtomicSemanticFact,
        witness: Aarch64ExclusiveMonitorWitness,
    ) -> Aarch64ProofObligationConsumption {
        let mut consumed = Vec::new();
        let mut missing = Vec::new();

        collect_fact_shape_requirements(load_reserve_fact, FactRole::Acquire, &mut missing);
        collect_fact_shape_requirements(store_conditional_fact, FactRole::Release, &mut missing);
        collect_exclusive_pair_shape_requirements(
            load_reserve_fact,
            store_conditional_fact,
            &mut missing,
        );

        let load_entry = self.log.entries().get(witness.load_reserve_access_index);
        let store_entry = self.log.entries().get(witness.store_conditional_access_index);

        match load_entry {
            Some(entry)
                if access_consumes_ordering(
                    entry.access_kind,
                    MemoryAccessKind::Read,
                    MemoryOrdering::Acquire,
                ) =>
            {
                consumed.push("acquire ordering event".to_string());
            }
            Some(_) => missing.push("acquire ordering event".to_string()),
            None => missing.push("load-exclusive access-log event".to_string()),
        }

        match store_entry {
            Some(entry)
                if access_consumes_ordering(
                    entry.access_kind,
                    MemoryAccessKind::Write,
                    MemoryOrdering::Release,
                ) =>
            {
                consumed.push("release ordering event".to_string());
            }
            Some(_) => missing.push("release ordering event".to_string()),
            None => missing.push("store-conditional access-log event".to_string()),
        }

        if let (Some(load), Some(store)) = (load_entry, store_entry) {
            if witness.reservation_observed
                && load.location == store.location
                && load_reserve_fact.exclusive_monitor
                    == Aarch64ExclusiveMonitorSemantics::LoadReserve
                && store_conditional_fact.exclusive_monitor
                    == Aarch64ExclusiveMonitorSemantics::StoreConditional
            {
                consumed.push("exclusive-monitor reservation state".to_string());
            } else {
                missing.push("exclusive-monitor reservation state".to_string());
            }

            if !load.thread_id.is_empty()
                && !store.thread_id.is_empty()
                && load.thread_id == store.thread_id
            {
                consumed.push("thread identity".to_string());
            } else {
                missing.push("thread identity".to_string());
            }
        } else {
            missing.push("exclusive-monitor reservation state".to_string());
            missing.push("thread identity".to_string());
        }

        if witness.no_intervening_invalidation {
            consumed.push("exclusive-monitor invalidation".to_string());
        } else {
            missing.push("exclusive-monitor invalidation".to_string());
        }

        match witness.store_status {
            Some(Aarch64StoreConditionalStatus::Succeeded)
                if store_conditional_fact.reports_status =>
            {
                consumed.push("store-conditional status result".to_string());
            }
            Some(Aarch64StoreConditionalStatus::Failed)
                if store_conditional_fact.reports_status =>
            {
                consumed.push("store-conditional status result".to_string());
                missing.push("successful store-conditional status result".to_string());
            }
            Some(_) | None => missing.push("store-conditional status result".to_string()),
        }

        if self
            .hb
            .successors(witness.load_reserve_access_index)
            .contains(&witness.store_conditional_access_index)
        {
            consumed.push("synchronization edge".to_string());
        } else {
            missing.push("synchronization edge".to_string());
        }

        if self.hb.happens_before(
            witness.load_reserve_access_index,
            witness.store_conditional_access_index,
        ) {
            consumed.push("happens-before witness".to_string());
        } else {
            missing.push("happens-before witness".to_string());
        }

        carry_unconsumed_fact_witnesses(load_reserve_fact, &consumed, &mut missing);
        carry_unconsumed_fact_witnesses(store_conditional_fact, &consumed, &mut missing);
        require_consumed_witnesses(
            &[
                "exclusive-monitor reservation state",
                "exclusive-monitor invalidation",
                "thread identity",
                "store-conditional status result",
                "acquire ordering event",
                "release ordering event",
                "synchronization edge",
                "happens-before witness",
            ],
            &consumed,
            &mut missing,
        );

        sort_dedup(&mut consumed);
        sort_dedup(&mut missing);

        let accepted = missing.is_empty();
        let diagnostic = if accepted {
            format!(
                "AArch64 exclusive-monitor proof-grade accepted after consuming witnesses: {}",
                consumed.join(", ")
            )
        } else {
            format!(
                "AArch64 exclusive-monitor obligation remains fail-closed; missing witnesses: {}; consumed witnesses: {}",
                missing.join(", "),
                if consumed.is_empty() { "none".to_string() } else { consumed.join(", ") }
            )
        };

        Aarch64ProofObligationConsumption {
            accepted_for_proof_grade: accepted,
            consumed_witnesses: consumed,
            missing_witnesses: missing,
            diagnostic,
        }
    }

    /// Consume a narrow DMB/DSB-style barrier proof boundary.
    ///
    /// The consumer accepts only when the access log contains a matching fence,
    /// the barrier option's domain and effect are explicitly witnessed, and the
    /// neighboring events are ordered through the barrier in one thread.
    #[must_use]
    pub fn consume_aarch64_barrier_obligation(
        &self,
        barrier_fact: &Aarch64BarrierSemanticFact,
        witness: Aarch64BarrierWitness,
    ) -> Aarch64ProofObligationConsumption {
        let mut consumed = Vec::new();
        let mut missing = Vec::new();

        collect_barrier_shape_requirements(barrier_fact, &mut missing);

        let before_entry = self.log.entries().get(witness.before_access_index);
        let barrier_entry = self.log.entries().get(witness.barrier_access_index);
        let after_entry = self.log.entries().get(witness.after_access_index);

        if let Some(required_ordering) = barrier_required_ordering(barrier_fact) {
            match barrier_entry {
                Some(entry)
                    if matches!(
                        entry.access_kind,
                        AccessKind::Fence(actual) if actual.is_at_least(required_ordering)
                    ) =>
                {
                    consumed.push("barrier ordering event".to_string());
                }
                Some(_) => missing.push("barrier ordering event".to_string()),
                None => missing.push("barrier access-log event".to_string()),
            }
        } else {
            missing.push("barrier ordering fact".to_string());
        }

        if witness.observed_domain == Some(barrier_fact.domain) {
            consumed.push("barrier domain witness".to_string());
        } else {
            missing.push("barrier domain witness".to_string());
        }

        if witness.observed_effect == Some(barrier_fact.effect) {
            consumed.push("barrier effect witness".to_string());
        } else {
            missing.push("barrier effect witness".to_string());
        }

        if let (Some(before), Some(barrier), Some(after)) =
            (before_entry, barrier_entry, after_entry)
        {
            if !before.thread_id.is_empty()
                && before.thread_id == barrier.thread_id
                && barrier.thread_id == after.thread_id
            {
                consumed.push("barrier thread identity".to_string());
            } else {
                missing.push("barrier thread identity".to_string());
            }
        } else {
            if before_entry.is_none() {
                missing.push("pre-barrier access-log event".to_string());
            }
            if after_entry.is_none() {
                missing.push("post-barrier access-log event".to_string());
            }
            missing.push("barrier thread identity".to_string());
        }

        if self.hb.successors(witness.before_access_index).contains(&witness.barrier_access_index) {
            consumed.push("pre-barrier program-order edge".to_string());
        } else {
            missing.push("pre-barrier program-order edge".to_string());
        }

        if self.hb.successors(witness.barrier_access_index).contains(&witness.after_access_index) {
            consumed.push("post-barrier program-order edge".to_string());
        } else {
            missing.push("post-barrier program-order edge".to_string());
        }

        if self.hb.happens_before(witness.before_access_index, witness.after_access_index) {
            consumed.push("barrier happens-before witness".to_string());
        } else {
            missing.push("barrier happens-before witness".to_string());
        }

        carry_unconsumed_witness_names(&barrier_fact.missing_witnesses, &consumed, &mut missing);
        require_consumed_witnesses(
            &[
                "barrier ordering event",
                "barrier domain witness",
                "barrier effect witness",
                "barrier thread identity",
                "pre-barrier program-order edge",
                "post-barrier program-order edge",
                "barrier happens-before witness",
            ],
            &consumed,
            &mut missing,
        );

        sort_dedup(&mut consumed);
        sort_dedup(&mut missing);

        let accepted = missing.is_empty();
        let diagnostic = if accepted {
            format!(
                "AArch64 barrier proof-grade accepted after consuming witnesses: {}",
                consumed.join(", ")
            )
        } else {
            format!(
                "AArch64 barrier obligation remains fail-closed; missing witnesses: {}; consumed witnesses: {}",
                missing.join(", "),
                if consumed.is_empty() { "none".to_string() } else { consumed.join(", ") }
            )
        };

        Aarch64ProofObligationConsumption {
            accepted_for_proof_grade: accepted,
            consumed_witnesses: consumed,
            missing_witnesses: missing,
            diagnostic,
        }
    }

    /// Consume a typed AArch64 synchronization-boundary fact.
    ///
    /// Barrier and CLREX facts are explicit proof boundaries. This consumer
    /// accepts only facts already marked as proof-consumed with an empty witness
    /// set by a downstream model; raw lift-derived facts remain fail-closed.
    #[must_use]
    pub fn consume_aarch64_sync_boundary_obligation(
        &self,
        fact: &Aarch64SyncBoundarySemanticFact,
    ) -> Aarch64ProofObligationConsumption {
        let mut consumed = Vec::new();
        let mut missing = fact.missing_witnesses.clone();

        if fact.consumed_by_proof_model {
            consumed.push("sync boundary proof model consumption".to_string());
        } else {
            missing.push("proof model consumption".to_string());
        }

        sort_dedup(&mut consumed);
        sort_dedup(&mut missing);

        let accepted = fact.proof_grade_gate_accepted() && missing.is_empty();
        let diagnostic = if accepted {
            format!(
                "AArch64 sync-boundary proof-grade accepted after consuming witnesses: {}",
                consumed.join(", ")
            )
        } else {
            format!(
                "AArch64 sync-boundary obligation remains fail-closed; opcode={}; missing witnesses: {}; consumed witnesses: {}",
                fact.opcode,
                missing.join(", "),
                if consumed.is_empty() { "none".to_string() } else { consumed.join(", ") }
            )
        };

        Aarch64ProofObligationConsumption {
            accepted_for_proof_grade: accepted,
            consumed_witnesses: consumed,
            missing_witnesses: missing,
            diagnostic,
        }
    }
}

const RELEASE_ACQUIRE_PRODUCIBLE_WITNESSES: &[&str] = &[
    "release ordering event",
    "acquire ordering event",
    "same atomic location witness",
    "synchronization edge",
    "thread identity",
    "happens-before witness",
];

const EXCLUSIVE_MONITOR_PRODUCIBLE_WITNESSES: &[&str] = &[
    "acquire ordering event",
    "release ordering event",
    "exclusive-monitor reservation state",
    "exclusive-monitor invalidation",
    "thread identity",
    "store-conditional status result",
    "synchronization edge",
    "happens-before witness",
];

type AbsenceParts = (Vec<usize>, Vec<String>, Vec<String>);

#[derive(Debug, Clone, Copy)]
enum FactRole {
    Release,
    Acquire,
}

fn collect_fact_shape_requirements(
    fact: &Aarch64AtomicSemanticFact,
    role: FactRole,
    missing: &mut Vec<String>,
) {
    match role {
        FactRole::Release => {
            if fact.access != MemoryAccessKind::Write {
                missing.push("release write access fact".to_string());
            }
            if fact.ordering != MemoryOrderingSemantics::Release
                && fact.ordering != MemoryOrderingSemantics::AcquireRelease
                && fact.ordering != MemoryOrderingSemantics::SeqCst
            {
                missing.push("release ordering fact".to_string());
            }
        }
        FactRole::Acquire => {
            if fact.access != MemoryAccessKind::Read {
                missing.push("acquire read access fact".to_string());
            }
            if fact.ordering != MemoryOrderingSemantics::Acquire
                && fact.ordering != MemoryOrderingSemantics::AcquireRelease
                && fact.ordering != MemoryOrderingSemantics::SeqCst
            {
                missing.push("acquire ordering fact".to_string());
            }
        }
    }
}

fn collect_monitor_witnesses(fact: &Aarch64AtomicSemanticFact, missing: &mut Vec<String>) {
    match fact.exclusive_monitor {
        Aarch64ExclusiveMonitorSemantics::None => {}
        Aarch64ExclusiveMonitorSemantics::LoadReserve => {
            missing.push("exclusive-monitor reservation state".to_string());
            missing.push("exclusive-monitor invalidation".to_string());
            missing.push("exclusive-monitor thread identity".to_string());
        }
        Aarch64ExclusiveMonitorSemantics::StoreConditional => {
            missing.push("exclusive-monitor reservation state".to_string());
            missing.push("exclusive-monitor invalidation".to_string());
            missing.push("exclusive-monitor thread identity".to_string());
            missing.push("store-conditional status result".to_string());
        }
        _ => missing.push("unknown exclusive-monitor semantics".to_string()),
    }
}

fn collect_exclusive_pair_shape_requirements(
    load_reserve_fact: &Aarch64AtomicSemanticFact,
    store_conditional_fact: &Aarch64AtomicSemanticFact,
    missing: &mut Vec<String>,
) {
    if load_reserve_fact.exclusive_monitor != Aarch64ExclusiveMonitorSemantics::LoadReserve {
        missing.push("exclusive-monitor reservation state".to_string());
    }
    if store_conditional_fact.exclusive_monitor
        != Aarch64ExclusiveMonitorSemantics::StoreConditional
    {
        missing.push("store-conditional monitor fact".to_string());
    }
    if !store_conditional_fact.reports_status {
        missing.push("store-conditional status result".to_string());
    }
}

fn collect_barrier_shape_requirements(
    fact: &Aarch64BarrierSemanticFact,
    missing: &mut Vec<String>,
) {
    let opcode = fact.opcode.to_ascii_lowercase();
    if opcode != "dmb" && opcode != "dsb" {
        missing.push("barrier opcode witness".to_string());
    }
    if barrier_required_ordering(fact).is_none() {
        missing.push("barrier ordering fact".to_string());
    }
}

fn barrier_required_ordering(fact: &Aarch64BarrierSemanticFact) -> Option<MemoryOrdering> {
    match (fact.ordering, fact.effect) {
        (MemoryOrderingSemantics::SeqCst, _) => Some(MemoryOrdering::SeqCst),
        (MemoryOrderingSemantics::AcquireRelease, Aarch64BarrierEffect::Full) => {
            Some(MemoryOrdering::AcqRel)
        }
        (MemoryOrderingSemantics::AcquireRelease, _) => Some(MemoryOrdering::AcqRel),
        (MemoryOrderingSemantics::Acquire, Aarch64BarrierEffect::Loads) => {
            Some(MemoryOrdering::Acquire)
        }
        (MemoryOrderingSemantics::Release, Aarch64BarrierEffect::Stores) => {
            Some(MemoryOrdering::Release)
        }
        _ => None,
    }
}

fn carry_unconsumed_fact_witnesses(
    fact: &Aarch64AtomicSemanticFact,
    consumed: &[String],
    missing: &mut Vec<String>,
) {
    carry_unconsumed_witness_names(&fact.missing_witnesses, consumed, missing);
}

fn carry_unconsumed_witness_names(
    witnesses: &[String],
    consumed: &[String],
    missing: &mut Vec<String>,
) {
    for witness in witnesses {
        if !consumed.iter().any(|consumed| consumed == witness) {
            missing.push(witness.clone());
        }
    }
}

fn collect_out_of_boundary_fact_witnesses(
    fact: &Aarch64AtomicSemanticFact,
    producible_witnesses: &[&str],
    missing: &mut Vec<String>,
) {
    for witness in &fact.missing_witnesses {
        if !producible_witnesses.iter().any(|producible| producible == witness) {
            missing.push(witness.clone());
        }
    }
}

fn require_consumed_witnesses(required: &[&str], consumed: &[String], missing: &mut Vec<String>) {
    for witness in required {
        if !consumed.iter().any(|consumed| consumed == witness) {
            missing.push((*witness).to_string());
        }
    }
}

impl MemoryModelChecker {
    fn aarch64_candidate_accesses(
        &self,
        fact: &Aarch64AtomicSemanticFact,
        expected_access: MemoryAccessKind,
        required_ordering: MemoryOrdering,
    ) -> Vec<(usize, &AtomicAccessEntry)> {
        self.log
            .entries()
            .iter()
            .enumerate()
            .filter(|(_, entry)| {
                fact_origin_matches_entry(fact, entry)
                    && access_consumes_ordering(
                        entry.access_kind,
                        expected_access,
                        required_ordering,
                    )
            })
            .collect()
    }
}

fn fact_origin_matches_entry(fact: &Aarch64AtomicSemanticFact, entry: &AtomicAccessEntry) -> bool {
    fact.origin.as_ref().is_none_or(|origin| origin.span() == entry.span)
}

fn collect_release_acquire_pair_evidence(
    release_index: usize,
    release_entry: &AtomicAccessEntry,
    acquire_index: usize,
    acquire_entry: &AtomicAccessEntry,
    checker: &MemoryModelChecker,
    available: &mut Vec<String>,
    missing: &mut Vec<String>,
) {
    available.push("release ordering event".to_string());
    available.push("acquire ordering event".to_string());

    if release_entry.location == acquire_entry.location {
        available.push("same atomic location witness".to_string());
    } else {
        missing.push("same atomic location witness".to_string());
    }

    if !release_entry.thread_id.is_empty()
        && !acquire_entry.thread_id.is_empty()
        && release_entry.thread_id != acquire_entry.thread_id
    {
        available.push("thread identity".to_string());
    } else {
        missing.push("cross-thread identity witness".to_string());
    }

    if checker.hb.successors(release_index).contains(&acquire_index) {
        available.push("synchronization edge".to_string());
    } else {
        missing.push("synchronization edge".to_string());
    }

    if checker.hb.happens_before(release_index, acquire_index) {
        available.push("happens-before witness".to_string());
    } else {
        missing.push("happens-before witness".to_string());
    }
}

struct ExclusiveMonitorPairEvidence<'a> {
    load_index: usize,
    load_entry: &'a AtomicAccessEntry,
    store_index: usize,
    store_entry: &'a AtomicAccessEntry,
    store_status: Option<Aarch64StoreConditionalStatus>,
}

fn collect_exclusive_monitor_pair_evidence(
    pair: ExclusiveMonitorPairEvidence<'_>,
    checker: &MemoryModelChecker,
    available: &mut Vec<String>,
    missing: &mut Vec<String>,
) {
    let ExclusiveMonitorPairEvidence {
        load_index,
        load_entry,
        store_index,
        store_entry,
        store_status,
    } = pair;

    available.push("acquire ordering event".to_string());
    available.push("release ordering event".to_string());

    if load_index < store_index
        && load_entry.location == store_entry.location
        && load_entry.thread_id == store_entry.thread_id
        && !load_entry.thread_id.is_empty()
    {
        available.push("exclusive-monitor reservation state".to_string());
    } else {
        missing.push("exclusive-monitor reservation state".to_string());
    }

    if no_logged_intervening_monitor_invalidation(load_index, store_index) {
        available.push("exclusive-monitor invalidation".to_string());
    } else {
        missing.push("exclusive-monitor invalidation".to_string());
    }

    if !load_entry.thread_id.is_empty()
        && !store_entry.thread_id.is_empty()
        && load_entry.thread_id == store_entry.thread_id
    {
        available.push("thread identity".to_string());
    } else {
        missing.push("thread identity".to_string());
    }

    match store_status {
        Some(Aarch64StoreConditionalStatus::Succeeded) => {
            available.push("store-conditional status result".to_string());
        }
        Some(Aarch64StoreConditionalStatus::Failed) => {
            available.push("store-conditional status result".to_string());
            missing.push("successful store-conditional status result".to_string());
        }
        None => missing.push("store-conditional status result".to_string()),
    }

    if checker.hb.successors(load_index).contains(&store_index) {
        available.push("synchronization edge".to_string());
    } else {
        missing.push("synchronization edge".to_string());
    }

    if checker.hb.happens_before(load_index, store_index) {
        available.push("happens-before witness".to_string());
    } else {
        missing.push("happens-before witness".to_string());
    }
}

fn no_logged_intervening_monitor_invalidation(load_index: usize, store_index: usize) -> bool {
    load_index.checked_add(1) == Some(store_index)
}

fn remember_best_absence(
    best: &mut Option<AbsenceParts>,
    mut candidate_access_indices: Vec<usize>,
    available_evidence: Vec<String>,
    missing_witnesses: Vec<String>,
) {
    candidate_access_indices.sort();
    candidate_access_indices.dedup();

    let replace = best
        .as_ref()
        .is_none_or(|(_, _, best_missing)| missing_witnesses.len() < best_missing.len());
    if replace {
        *best = Some((candidate_access_indices, available_evidence, missing_witnesses));
    }
}

fn absence_certificate(
    boundary: Aarch64WitnessBoundary,
    mut candidate_access_indices: Vec<usize>,
    mut available_evidence: Vec<String>,
    mut missing_witnesses: Vec<String>,
) -> Aarch64WitnessAbsenceCertificate {
    candidate_access_indices.sort();
    candidate_access_indices.dedup();
    sort_dedup(&mut available_evidence);
    sort_dedup(&mut missing_witnesses);

    Aarch64WitnessAbsenceCertificate {
        boundary,
        candidate_access_indices,
        diagnostic: format!(
            "AArch64 {boundary:?} witness absent; missing witnesses: {}; available evidence: {}",
            witness_list(&missing_witnesses),
            witness_list(&available_evidence),
        ),
        available_evidence,
        missing_witnesses,
    }
}

fn sorted_deduped(mut values: Vec<String>) -> Vec<String> {
    sort_dedup(&mut values);
    values
}

fn witness_list(witnesses: &[String]) -> String {
    if witnesses.is_empty() { "none".to_string() } else { witnesses.join(", ") }
}

fn access_consumes_ordering(
    access_kind: AccessKind,
    expected_access: MemoryAccessKind,
    required_ordering: MemoryOrdering,
) -> bool {
    match (access_kind, expected_access) {
        (AccessKind::AtomicRead(actual), MemoryAccessKind::Read)
        | (AccessKind::AtomicWrite(actual), MemoryAccessKind::Write) => {
            actual.is_at_least(required_ordering)
        }
        _ => false,
    }
}

fn sort_dedup(values: &mut Vec<String>) {
    values.sort();
    values.dedup();
}
