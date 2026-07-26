// trust-types/formula/borrow_encoding: RustHorn borrow encoding types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use super::{Formula, Sort};

// ---------------------------------------------------------------------------
// RustHorn borrow encoding types for trust_wp CHC-based verification.
//
// RustHorn (Matsushita et al., ESOP 2020) models Rust borrows as prophecy
// variables. For a mutable reference `&'a mut T`:
//   - `*v` is the **current value** of the referenced place (read projection)
//   - `^v` is the **final value** returned to the owner when the borrow expires
//          (prophecy -- set at borrow creation, resolved at borrow end)
//
// This encoding turns borrow-passing code into pure first-order logic over
// value snapshots, eliminating the need for separation logic for safe Rust.
//
// For CHC solving, each function becomes a set of Horn clauses where:
//   - Mutable borrows introduce prophecy variables in preconditions
//   - Borrow expiry equates the prophecy variable with the actual final value
//   - The CHC solver (Spacer/trust-wp) infers the prophecy interpretations
// ---------------------------------------------------------------------------

/// A prophecy variable introduced by a mutable borrow.
///
/// When `&'a mut T` is created for a place, two logical variables appear:
///   - `current`: the value at borrow creation (`*v` in RustHorn notation)
///   - `prophecy`: the value returned to the owner at borrow expiry (`^v`)
///
/// The prophecy is unconstrained at creation and resolved when the borrow ends.
/// CHC solvers infer the prophecy interpretation that satisfies all clauses.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProphecyVar {
    /// Name of the source place being borrowed (e.g., "x").
    pub place: String,
    /// Logical variable for the current value at borrow creation (`*v`).
    pub current_var: String,
    /// Logical variable for the final value at borrow expiry (`^v`).
    pub prophecy_var: String,
    /// SMT sort of the borrowed value.
    pub sort: Sort,
    /// Whether this is a mutable borrow (true) or shared borrow (false).
    /// Shared borrows use identity prophecy: `^v = *v` (value unchanged).
    pub mutable: bool,
}

impl ProphecyVar {
    /// Create a prophecy variable pair for a mutable borrow.
    #[must_use]
    pub fn mutable_borrow(place: &str, sort: Sort) -> Self {
        Self {
            place: place.to_string(),
            current_var: format!("{place}__curr"),
            prophecy_var: format!("{place}__final"),
            sort,
            mutable: true,
        }
    }

    /// Create a prophecy variable pair for a shared borrow.
    /// The prophecy is trivially `^v = *v` (value unchanged).
    #[must_use]
    pub fn shared_borrow(place: &str, sort: Sort) -> Self {
        Self {
            place: place.to_string(),
            current_var: format!("{place}__curr"),
            prophecy_var: format!("{place}__final"),
            sort,
            mutable: false,
        }
    }

    /// The identity constraint for shared borrows: `^v = *v`.
    #[must_use]
    pub fn identity_constraint(&self) -> Formula {
        Formula::Eq(
            Box::new(Formula::Var(self.current_var.clone(), self.sort.clone())),
            Box::new(Formula::Var(self.prophecy_var.clone(), self.sort.clone())),
        )
    }

    /// Formula asserting the prophecy is resolved: the final value equals
    /// the given expression (used at borrow expiry).
    #[must_use]
    pub fn resolve(&self, final_value: Formula) -> Formula {
        Formula::Eq(
            Box::new(Formula::Var(self.prophecy_var.clone(), self.sort.clone())),
            Box::new(final_value),
        )
    }
}

/// A complete RustHorn borrow encoding for a function.
///
/// Collects all prophecy variables introduced by borrow operations in the MIR
/// and the constraints needed for CHC encoding. The trust_wp backend consumes
/// this to generate proper CHC clauses with prophecy-aware predicate signatures.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct BorrowEncoding {
    /// Prophecy variables for each borrow in the function.
    pub prophecies: Vec<ProphecyVar>,
    /// Constraints from borrow creation (prophecy introduction).
    /// For shared borrows, includes identity `^v = *v`.
    pub creation_constraints: Vec<Formula>,
    /// Constraints from borrow expiry (prophecy resolution).
    /// Each entry equates a prophecy var with the actual final value.
    pub expiry_constraints: Vec<Formula>,
    /// Non-aliasing constraints between active borrows.
    /// Mutable borrows are exclusive; shared borrows may coexist.
    pub aliasing_constraints: Vec<Formula>,
}

impl BorrowEncoding {
    /// Returns true if no borrows were encoded.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.prophecies.is_empty()
    }

    /// Number of prophecy variables (= number of borrow operations).
    #[must_use]
    pub fn prophecy_count(&self) -> usize {
        self.prophecies.len()
    }

    /// All prophecy parameters as (name, sort) pairs for CHC predicate signatures.
    /// Includes both current and prophecy variables for each borrow.
    #[must_use]
    pub fn predicate_params(&self) -> Vec<(String, Sort)> {
        let mut params = Vec::new();
        for p in &self.prophecies {
            params.push((p.current_var.clone(), p.sort.clone()));
            params.push((p.prophecy_var.clone(), p.sort.clone()));
        }
        params
    }

    /// Conjunction of all creation constraints (for entry clauses).
    #[must_use]
    pub fn creation_formula(&self) -> Formula {
        match self.creation_constraints.len() {
            0 => Formula::Bool(true),
            1 => self.creation_constraints[0].clone(),
            _ => Formula::And(self.creation_constraints.clone()),
        }
    }

    /// Conjunction of all expiry constraints (for exit clauses).
    #[must_use]
    pub fn expiry_formula(&self) -> Formula {
        match self.expiry_constraints.len() {
            0 => Formula::Bool(true),
            1 => self.expiry_constraints[0].clone(),
            _ => Formula::And(self.expiry_constraints.clone()),
        }
    }

    /// Conjunction of all aliasing constraints (for all clauses).
    #[must_use]
    pub fn aliasing_formula(&self) -> Formula {
        match self.aliasing_constraints.len() {
            0 => Formula::Bool(true),
            1 => self.aliasing_constraints[0].clone(),
            _ => Formula::And(self.aliasing_constraints.clone()),
        }
    }

    /// Full encoding constraint: creation AND aliasing AND expiry.
    #[must_use]
    pub fn full_constraint(&self) -> Formula {
        let parts: Vec<Formula> =
            [self.creation_formula(), self.aliasing_formula(), self.expiry_formula()]
                .into_iter()
                .filter(|f| *f != Formula::Bool(true))
                .collect();

        match parts.len() {
            0 => Formula::Bool(true),
            1 => parts.into_iter().next().expect("len == 1"),
            _ => Formula::And(parts),
        }
    }
}
