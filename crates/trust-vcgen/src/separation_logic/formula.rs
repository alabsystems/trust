// trust_vcgen/separation_logic/formula.rs: Separation logic formula types
//
// Defines the core SepFormula enum representing separation logic assertions
// over a symbolic heap: PointsTo, SepStar, SepWand, Emp, Pure.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Formula;

// ────────────────────────────────────────────────────────────────────────────
// Separation logic formulas
// ────────────────────────────────────────────────────────────────────────────

/// A separation logic formula over a symbolic heap.
///
/// These formulas describe heap shapes and ownership. They are translated
/// to first-order logic (FOL) with explicit heap arrays for SMT solving
/// via [`sep_to_formula`](super::sep_to_formula).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SepFormula {
    /// `addr |-> value`: address `addr` points to `value` in the heap.
    PointsTo { addr: Formula, value: Formula },
    /// `P * Q`: separating conjunction -- P and Q hold on disjoint heaps.
    SepStar(Box<SepFormula>, Box<SepFormula>),
    /// `P -* Q`: magic wand -- if P is added to the current heap, then Q holds.
    SepWand(Box<SepFormula>, Box<SepFormula>),
    /// `emp`: the empty heap (no allocated cells).
    Emp,
    /// `Pure(phi)`: a pure (heap-independent) assertion lifted into separation logic.
    Pure(Formula),
}

impl SepFormula {
    /// Convenience: create a PointsTo formula.
    #[must_use]
    pub fn points_to(addr: Formula, value: Formula) -> Self {
        Self::PointsTo { addr, value }
    }

    /// Convenience: create a separating conjunction.
    #[must_use]
    pub fn star(lhs: SepFormula, rhs: SepFormula) -> Self {
        Self::SepStar(Box::new(lhs), Box::new(rhs))
    }

    /// Convenience: create a magic wand.
    #[must_use]
    pub fn wand(lhs: SepFormula, rhs: SepFormula) -> Self {
        Self::SepWand(Box::new(lhs), Box::new(rhs))
    }

    /// Convenience: lift a pure formula.
    #[must_use]
    pub fn pure(f: Formula) -> Self {
        Self::Pure(f)
    }

    /// Returns true if this is the empty heap.
    #[must_use]
    pub fn is_emp(&self) -> bool {
        matches!(self, Self::Emp)
    }

    /// Count the number of PointsTo cells in this formula.
    #[must_use]
    pub fn cell_count(&self) -> usize {
        match self {
            Self::PointsTo { .. } => 1,
            Self::SepStar(lhs, rhs) | Self::SepWand(lhs, rhs) => {
                lhs.cell_count() + rhs.cell_count()
            }
            Self::Emp | Self::Pure(_) => 0,
        }
    }

    /// Create a separating conjunction of multiple formulas.
    ///
    /// `star_many([P, Q, R])` produces `P * Q * R`. An empty list
    /// produces `emp`. A single element produces that element directly.
    #[must_use]
    pub fn star_many(formulas: Vec<SepFormula>) -> Self {
        let mut iter = formulas.into_iter();
        let Some(first) = iter.next() else {
            return Self::Emp;
        };
        iter.fold(first, Self::star)
    }
}
