// trust_vcgen/memory_ordering: Memory ordering verification for concurrent programs
//
// Provides a structured model for reasoning about the C11/Rust memory model:
// - HappensBefore: partial order representing the happens-before relation
// - DataRaceDetector: checks if two memory accesses can race
// - AtomicAccessLog: records atomic operations with their orderings
// - RaceCondition: describes a detected race with conflicting accesses
// - MemoryModelChecker: verifies memory ordering constraints are sufficient
//
// Builds on the low-level primitives in data_race.rs (MemoryOrdering,
// AccessKind, SharedAccess) and provides higher-level analysis.
//
// Part of #203: Data race / atomics / memory ordering verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod aarch64;
mod atomic_access;
mod checker;
mod detector;
mod happens_before;
mod hb_graph;
mod race_condition;

#[cfg(test)]
mod tests;

pub use aarch64::{
    Aarch64BarrierDomain, Aarch64BarrierEffect, Aarch64BarrierSemanticFact, Aarch64BarrierWitness,
    Aarch64ExclusiveMonitorWitness, Aarch64ExclusiveMonitorWitnessEvidence,
    Aarch64ProofObligationConsumption, Aarch64ReleaseAcquireWitness,
    Aarch64ReleaseAcquireWitnessEvidence, Aarch64StoreConditionalStatus,
    Aarch64WitnessAbsenceCertificate, Aarch64WitnessBoundary,
};
pub use atomic_access::{AtomicAccessEntry, AtomicAccessLog};
pub use checker::{
    MemoryModelCheckResult, MemoryModelChecker, OrderingCoverageGap, OrderingRequirement,
    OrderingViolation,
};
pub use detector::DataRaceDetector;
pub use happens_before::HappensBefore;
pub use hb_graph::HappensBeforeGraph;
pub use race_condition::RaceCondition;
