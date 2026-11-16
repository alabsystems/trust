// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The caller-side precondition a Clean-origin minted `def` carries.**
//!
//! Commit `fa788aab89` named this shape and nothing else: the zero-divisor
//! obligation a symbolic-divisor `Rem` needs is *"a PLAN-lane obligation, not a
//! kernel one: it must constrain which MIR gets built (a caller-side
//! precondition on the minted `DefId`, or an emitted `Assert`), and its
//! discharge is an ordinary Rust obligation, never a `Faithful` token."*
//!
//! This module is the **portable vocabulary** for that obligation — the one
//! thing the producer (`trust-clean-carrier` reading a Clean `Pi`) and the
//! consumer (`trust-vcgen` minting a call-site `VcKind::Precondition`) must
//! agree on. It lives in `trust-types` because that is the only crate both of
//! them depend on: `trust-vcgen` does not depend on `trust-clean-origin` and
//! must not start (the dependency graph is acyclic and the producer is on the
//! Clean side of the boundary).
//!
//! # What it deliberately CANNOT express
//!
//! There is no `assume`, no `ensures`, no "the callee guarantees" — every
//! value here is a **demand on the caller**. That asymmetry is the soundness
//! argument for the vocabulary being plain public data rather than a sealed
//! type:
//!
//! * **Adding** a precondition can only ADD a call-site obligation. A forged or
//!   mistaken atom over-rejects; it can never manufacture a `PROVE`.
//! * **Dropping** one is the hazard, and it is closed on the two sides that can
//!   drop it: `trust-clean-carrier` refuses to carry a hypothesis binder it
//!   cannot recognise (no signature, so no mint), and the `trust-vcgen`
//!   renderer is all-or-nothing (a summary that cannot carry every precondition
//!   publishes NO fact either — the rule `650674bc71` restored).
//!
//! So a public constructor is safe here in a way it is not for `Carrier` or
//! `MintGrant`, whose existence is *evidence*. A `CleanOriginPrecondition` is
//! not evidence; it is a bill.
//!
//! # The vocabulary is CLOSED and small on purpose
//!
//! One relation ([`PreconditionRelation::NotEqual`]) and two operand forms.
//! That is exactly what `b ≠ 0` needs — the hypothesis the ratified gcd route
//! wants — and nothing else. Widening it is a capability extension (v7/D2:
//! extending capability extends the CHECK, never trust), and every widening
//! must land with the matching renderer arm in `trust-vcgen`, because an atom
//! the renderer cannot spell makes the whole summary vanish.

use serde::{Deserialize, Serialize};

/// One side of a Clean-origin precondition.
///
/// Deliberately NOT a `Formula`: the producer runs in the Clean-side crates,
/// which have no reason to depend on the VC formula language, and an operand
/// that can only be an argument index or a literal is one a renderer can always
/// check (`Argument` in range, `Literal` in range) before it spells anything.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PreconditionOperand {
    /// The value argument at this 0-based index, counting **carried arguments
    /// only** — proof/hypothesis binders are erased and are not counted.
    Argument(usize),
    /// A numeral, already range-checked against the declaration's carrier width
    /// by the producer, and re-checked by the renderer.
    Literal(u128),
}

/// The relation a Clean-origin precondition asserts.
///
/// `#[non_exhaustive]`: a consumer that grows a new arm must do so explicitly,
/// and a consumer that has not grown one falls into its own fail-closed default
/// (which, for the renderer, is "publish nothing").
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum PreconditionRelation {
    /// `left != right`. The divisor guard, and the only relation today.
    NotEqual,
}

/// A single caller obligation carried by a minted Clean-origin `def`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CleanOriginPrecondition {
    relation: PreconditionRelation,
    left: PreconditionOperand,
    right: PreconditionOperand,
    /// The carrier width the operands live at, in bits (`1..=64`). Carried so
    /// the renderer can re-check a `Literal` against it rather than trusting
    /// the producer's own range check.
    width: u32,
    /// How the Clean source spelled it, for diagnostics only. Never parsed.
    rendered: String,
}

impl CleanOriginPrecondition {
    /// Build a `left != right` obligation at `width` bits.
    ///
    /// `rendered` is diagnostic text (`"b ≠ 0"`); it carries no authority and
    /// is never read back.
    #[must_use]
    pub fn not_equal(
        left: PreconditionOperand,
        right: PreconditionOperand,
        width: u32,
        rendered: impl Into<String>,
    ) -> Self {
        Self {
            relation: PreconditionRelation::NotEqual,
            left,
            right,
            width,
            rendered: rendered.into(),
        }
    }

    /// The relation.
    #[must_use]
    pub fn relation(&self) -> PreconditionRelation {
        self.relation
    }

    /// The left operand.
    #[must_use]
    pub fn left(&self) -> PreconditionOperand {
        self.left
    }

    /// The right operand.
    #[must_use]
    pub fn right(&self) -> PreconditionOperand {
        self.right
    }

    /// The carrier width the operands live at, in bits.
    #[must_use]
    pub fn width(&self) -> u32 {
        self.width
    }

    /// The source spelling, for diagnostics.
    #[must_use]
    pub fn rendered(&self) -> &str {
        &self.rendered
    }

    /// The largest **carried argument index** this obligation mentions, or
    /// `None` when it mentions no argument at all.
    ///
    /// A renderer uses this to reject an obligation whose arguments the call
    /// site cannot supply, BEFORE spelling anything — an out-of-range index
    /// substituted positionally would silently bind the wrong actual.
    #[must_use]
    pub fn max_argument_index(&self) -> Option<usize> {
        let of = |operand: PreconditionOperand| match operand {
            PreconditionOperand::Argument(i) => Some(i),
            PreconditionOperand::Literal(_) => None,
        };
        match (of(self.left), of(self.right)) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (Some(a), None) | (None, Some(a)) => Some(a),
            (None, None) => None,
        }
    }
}

impl core::fmt::Display for CleanOriginPrecondition {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let operand = |o: PreconditionOperand| match o {
            PreconditionOperand::Argument(i) => format!("arg{i}"),
            PreconditionOperand::Literal(v) => v.to_string(),
        };
        match self.relation {
            PreconditionRelation::NotEqual => {
                write!(f, "{} != {} (u{})", operand(self.left), operand(self.right), self.width)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn max_argument_index_reads_both_sides() {
        let a = PreconditionOperand::Argument(1);
        let z = PreconditionOperand::Literal(0);
        assert_eq!(
            CleanOriginPrecondition::not_equal(a, z, 64, "b ≠ 0").max_argument_index(),
            Some(1)
        );
        assert_eq!(
            CleanOriginPrecondition::not_equal(z, a, 64, "0 ≠ b").max_argument_index(),
            Some(1)
        );
        assert_eq!(
            CleanOriginPrecondition::not_equal(
                PreconditionOperand::Argument(0),
                PreconditionOperand::Argument(3),
                8,
                "a ≠ d"
            )
            .max_argument_index(),
            Some(3)
        );
        assert_eq!(
            CleanOriginPrecondition::not_equal(z, z, 8, "0 ≠ 0").max_argument_index(),
            None,
            "a ground obligation mentions no argument; it is unsatisfiable, which \
             over-rejects — the safe direction"
        );
    }

    #[test]
    fn display_names_the_width_so_two_widths_never_read_alike() {
        let p = CleanOriginPrecondition::not_equal(
            PreconditionOperand::Argument(1),
            PreconditionOperand::Literal(0),
            8,
            "b ≠ 0",
        );
        assert_eq!(p.to_string(), "arg1 != 0 (u8)");
    }
}
