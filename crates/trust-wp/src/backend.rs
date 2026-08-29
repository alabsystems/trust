// trust_wp backend trait
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Backend trait for pluggable trust_wp verification implementations.
//!
//! The `TrustWpBackend` trait defines a standalone compatibility interface for
//! explicit diagnostic callers. It is not registered with the compiler or the
//! full-verifier fleet and grants no publication authority.

use crate::contract::ContractSet;
use crate::error::TrustWpLibError;
use crate::result::{LoopInvariant, TrustWpResult};

/// Backend trait for trust_wp verification.
///
/// The retained `CliBackend` invokes the trust_wp CLI for explicit standalone
/// compatibility runs. No compiler/full-verifier backend implements this trait.
pub trait TrustWpBackend {
    /// Verify a function's contracts.
    ///
    /// # Arguments
    ///
    /// * `function_name` - The fully qualified function name to verify
    /// * `contracts` - The contract set (requires/ensures/invariants)
    ///
    /// # Errors
    ///
    /// Returns `TrustWpLibError` if verification fails due to infrastructure issues.
    fn verify(
        &self,
        function_name: &str,
        contracts: &ContractSet,
    ) -> Result<TrustWpResult, TrustWpLibError>;

    /// Infer loop invariants for a function.
    ///
    /// # Arguments
    ///
    /// * `function_name` - The fully qualified function name
    ///
    /// # Errors
    ///
    /// Returns `TrustWpLibError` if invariant inference fails.
    fn infer_invariants(&self, function_name: &str) -> Result<Vec<LoopInvariant>, TrustWpLibError>;
}
