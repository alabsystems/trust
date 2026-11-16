// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Historical strategy labels retained by per-obligation report descriptors.
//! This module defines no MIR traversal, verification questions or dispatch.

/// MIR-level verification strategy.
///
/// Determines how a function should be verified based on its MIR properties.
/// Ordered roughly by specificity: more specialized strategies are preferred
/// over generic ones.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MirStrategy {
    /// trust_mc safety/reachability. Current compatibility path is BMC-shaped;
    /// target tRustc integration can select BMC, CHC, or PDR/IC3.
    BoundedModelCheck,
    /// Retired TrustWP contract classification; diagnostic-only and always Unknown.
    ContractVerification,
    /// Unsafe audit — active TrustMC plus a non-authoritative contract diagnostic.
    UnsafeAudit,
    /// Ownership/separation logic — v1 pipeline.
    SeparationLogic,
    /// Data race detection — v1 pipeline + TY.
    DataRace,
    /// FFI boundary — v1 pipeline.
    FFIBoundary,
    /// Run multiple strategies in parallel, take first definitive result.
    Portfolio(Vec<MirStrategy>),
    /// trust_cg verified codegen — lower to LIR, optionally validate.
    #[cfg(feature = "trust-cg-backend")]
    TrustCgCodegen,
    /// Fall through to v1 Formula-based pipeline.
    V1Fallback,
}

impl std::fmt::Display for MirStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MirStrategy::BoundedModelCheck => f.write_str("BoundedModelCheck"),
            MirStrategy::ContractVerification => f.write_str("ContractVerification"),
            MirStrategy::UnsafeAudit => f.write_str("UnsafeAudit"),
            MirStrategy::SeparationLogic => f.write_str("SeparationLogic"),
            MirStrategy::DataRace => f.write_str("DataRace"),
            MirStrategy::FFIBoundary => f.write_str("FFIBoundary"),
            MirStrategy::Portfolio(strategies) => {
                write!(f, "Portfolio(")?;
                for (i, s) in strategies.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{s}")?;
                }
                write!(f, ")")
            }
            #[cfg(feature = "trust-cg-backend")]
            MirStrategy::TrustCgCodegen => f.write_str("TrustCgCodegen"),
            MirStrategy::V1Fallback => f.write_str("V1Fallback"),
        }
    }
}
