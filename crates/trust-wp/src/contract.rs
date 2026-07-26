// trust_wp contract types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Contract types for trust_wp verification.
//!
//! These are standalone types that mirror trust-wp's contract representation
//! without depending on trust-wp-core (which requires nightly). In Phase 2,
//! these will bridge to trust-wp-core's native `Formula` / `PureExpr` types.

use serde::{Deserialize, Serialize};

/// A set of contracts for a function.
///
/// Corresponds to trust-wp's notion of a verified function: preconditions,
/// postconditions, and loop invariants extracted from `#[requires]`,
/// `#[ensures]`, and `#[invariant]` attributes.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ContractSet {
    /// Preconditions (`#[requires(...)]`).
    pub requires: Vec<Contract>,

    /// Postconditions (`#[ensures(...)]`).
    pub ensures: Vec<Contract>,

    /// Loop invariants (`#[invariant(...)]`).
    pub invariants: Vec<Contract>,

    /// Whether the function is marked `#[trusted]` (skip verification).
    pub trusted: bool,
}

impl ContractSet {
    /// Create an empty contract set.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a precondition.
    #[must_use]
    pub fn with_requires(mut self, contract: Contract) -> Self {
        self.requires.push(contract);
        self
    }

    /// Add a postcondition.
    #[must_use]
    pub fn with_ensures(mut self, contract: Contract) -> Self {
        self.ensures.push(contract);
        self
    }

    /// Add a loop invariant.
    #[must_use]
    pub fn with_invariant(mut self, contract: Contract) -> Self {
        self.invariants.push(contract);
        self
    }

    /// Mark the function as trusted.
    #[must_use]
    pub fn with_trusted(mut self, trusted: bool) -> Self {
        self.trusted = trusted;
        self
    }

    /// Returns `true` if no contracts are specified and the function is not trusted.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.requires.is_empty()
            && self.ensures.is_empty()
            && self.invariants.is_empty()
            && !self.trusted
    }

    /// Total number of contract clauses.
    #[must_use]
    pub fn len(&self) -> usize {
        self.requires.len() + self.ensures.len() + self.invariants.len()
    }
}

/// A single contract clause.
///
/// In Phase 1, contracts are represented as string expressions matching
/// trust-wp's attribute syntax. In Phase 2, these will carry parsed
/// `PureExpr` trees from trust-wp-core.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Contract {
    /// The kind of contract.
    pub kind: ContractKind,

    /// The contract expression as a string.
    /// Matches the syntax accepted by trust-wp's `#[requires]`/`#[ensures]` attributes.
    pub expression: String,

    /// Optional source location for error reporting.
    pub location: Option<String>,
}

impl Contract {
    /// Create a new contract.
    pub fn new(kind: ContractKind, expression: impl Into<String>) -> Self {
        Self { kind, expression: expression.into(), location: None }
    }

    /// Create a precondition contract.
    pub fn requires(expression: impl Into<String>) -> Self {
        Self::new(ContractKind::Requires, expression)
    }

    /// Create a postcondition contract.
    pub fn ensures(expression: impl Into<String>) -> Self {
        Self::new(ContractKind::Ensures, expression)
    }

    /// Create a loop invariant contract.
    pub fn invariant(expression: impl Into<String>) -> Self {
        Self::new(ContractKind::Invariant, expression)
    }

    /// Set the source location.
    #[must_use]
    pub fn with_location(mut self, location: impl Into<String>) -> Self {
        self.location = Some(location.into());
        self
    }
}

/// The kind of contract clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ContractKind {
    /// Precondition (`#[requires]`).
    Requires,
    /// Postcondition (`#[ensures]`).
    Ensures,
    /// Functional refinement predicate.
    Refinement,
    /// Loop invariant (`#[invariant]`).
    Invariant,
}
