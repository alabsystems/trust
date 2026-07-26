// trust-symex path constraints
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::BinOp;
use trust_types::{Formula, Sort};

use crate::state::SymbolicValue;

/// A single branch decision along an execution path.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BranchDecision {
    /// The condition that was evaluated at the branch point.
    pub condition: SymbolicValue,
    /// Whether the branch was taken (true) or not (false).
    pub taken: bool,
}

/// Accumulated path constraints for a single execution path.
///
/// Each branch decision adds a constraint. The conjunction of all
/// constraints characterizes the set of inputs that follow this path.
///
/// Auxiliary formulas (e.g., from path merges) are also included in the
/// conjunction. These encode constraints that cannot be represented as
/// simple branch decisions, such as the disjunction of divergent path
/// constraints at merge points.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PathConstraint {
    decisions: Vec<BranchDecision>,
    /// Additional formula constraints (e.g., merge disjunctions).
    ///
    /// These are ANDed together with the branch decisions when
    /// converting to a formula via [`to_formula`](Self::to_formula).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    auxiliary: Vec<Formula>,
}

impl PathConstraint {
    /// Create an empty path constraint (unconstrained).
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a branch decision to the path.
    ///
    /// If `branch_taken` is true, the condition itself is asserted.
    /// If false, the negation of the condition is asserted.
    pub fn add_constraint(&mut self, cond: SymbolicValue, branch_taken: bool) {
        self.decisions.push(BranchDecision { condition: cond, taken: branch_taken });
    }

    /// Returns the number of branch decisions on this path.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.decisions.len()
    }

    /// Returns `true` if no constraints have been collected.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.decisions.is_empty() && self.auxiliary.is_empty()
    }

    /// Iterate over branch decisions.
    pub fn decisions(&self) -> &[BranchDecision] {
        &self.decisions
    }

    /// Convert all path constraints to a single `Formula` (conjunction).
    ///
    /// Each branch decision becomes either the condition or its negation,
    /// and all are ANDed together, along with any auxiliary formulas.
    #[must_use]
    pub fn to_formula(&self) -> Formula {
        let mut clauses: Vec<Formula> = self
            .decisions
            .iter()
            .map(|d| {
                let f = symbolic_to_formula(&d.condition);
                if d.taken { f } else { Formula::Not(Box::new(f)) }
            })
            .collect();

        // Include auxiliary formulas (e.g., merge disjunctions).
        clauses.extend(self.auxiliary.iter().cloned());

        if clauses.is_empty() {
            Formula::Bool(true)
        } else if clauses.len() == 1 {
            // SAFETY: len == 1 guarantees .next() returns Some.
            clauses
                .into_iter()
                .next()
                .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
        } else {
            Formula::And(clauses)
        }
    }

    /// Add an auxiliary formula constraint.
    ///
    /// Auxiliary formulas are ANDed with branch decisions when converting
    /// to a formula. Used by path merging to encode disjunctions of
    /// divergent path constraints.
    pub fn add_auxiliary(&mut self, formula: Formula) {
        self.auxiliary.push(formula);
    }

    /// Returns the auxiliary formula constraints.
    #[must_use]
    pub fn auxiliary(&self) -> &[Formula] {
        &self.auxiliary
    }

    /// Negate the last decision to explore the other branch.
    ///
    /// Returns `None` if the path is empty.
    #[must_use]
    pub fn negate_last(&self) -> Option<PathConstraint> {
        if self.decisions.is_empty() {
            return None;
        }
        let mut new = self.clone();
        // SAFETY: We checked is_empty() above and returned None.
        let last = new
            .decisions
            .last_mut()
            .unwrap_or_else(|| unreachable!("decisions empty after non-empty check"));
        last.taken = !last.taken;
        Some(new)
    }
}

/// Convert a `SymbolicValue` to a trust-types `Formula`.
///
/// Defaults to unsigned semantics for right-shift operations.
/// Use [`symbolic_to_formula_with_signedness`] when the operand type is known
/// to be signed.
#[must_use]
pub fn symbolic_to_formula(val: &SymbolicValue) -> Formula {
    symbolic_to_formula_with_signedness(val, false)
}

/// Convert a `SymbolicValue` to a trust-types `Formula` with explicit signedness.
///
/// When `signed` is true, `BinOp::Shr` maps to `Formula::BvAShr` (arithmetic
/// right shift, sign-extending). When false, it maps to `Formula::BvLShr`
/// (logical right shift, zero-extending).
///
/// # Correctness
///
/// Rust's `>>` operator performs arithmetic right shift on signed integer types
/// (e.g., `i32`, `i64`) and logical right shift on unsigned types (`u32`, `u64`).
/// For negative values, using the wrong shift produces incorrect results:
/// `-8i32 >> 1` should be `-4` (arithmetic), not `2147483644` (logical).
// Fix signed right-shift producing incorrect results for negatives.
#[must_use]
pub fn symbolic_to_formula_with_signedness(val: &SymbolicValue, signed: bool) -> Formula {
    match val {
        SymbolicValue::Concrete(n) => Formula::Int(*n),
        SymbolicValue::Symbol(name) => Formula::Var(name.clone(), Sort::Int),
        SymbolicValue::BinOp(lhs, op, rhs) => {
            let l = Box::new(symbolic_to_formula_with_signedness(lhs, signed));
            let r = Box::new(symbolic_to_formula_with_signedness(rhs, signed));
            match op {
                BinOp::Add => Formula::Add(l, r),
                BinOp::Sub => Formula::Sub(l, r),
                BinOp::Mul => Formula::Mul(l, r),
                BinOp::Div => Formula::Div(l, r),
                BinOp::Rem => Formula::Rem(l, r),
                BinOp::Eq => Formula::Eq(l, r),
                BinOp::Ne => Formula::Not(Box::new(Formula::Eq(l, r))),
                BinOp::Lt => Formula::Lt(l, r),
                BinOp::Le => Formula::Le(l, r),
                BinOp::Gt => Formula::Gt(l, r),
                BinOp::Ge => Formula::Ge(l, r),
                // Three-way comparison: ITE(a < b, -1, ITE(a == b, 0, 1))
                BinOp::Cmp => Formula::Ite(
                    Box::new(Formula::Lt(l.clone(), r.clone())),
                    Box::new(Formula::Int(-1)),
                    Box::new(Formula::Ite(
                        Box::new(Formula::Eq(l, r)),
                        Box::new(Formula::Int(0)),
                        Box::new(Formula::Int(1)),
                    )),
                ),
                BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                    // Emit proper bitvector formulas. SymbolicValue
                    // does not carry type info, so we default to 64-bit width
                    // (conservative: wider than needed but never narrower).
                    let w = 64u32;
                    let lhs_bv = Box::new(Formula::IntToBv(l, w));
                    let rhs_bv = Box::new(Formula::IntToBv(r, w));
                    let bv_result = match op {
                        BinOp::BitAnd => Formula::BvAnd(lhs_bv, rhs_bv, w),
                        BinOp::BitOr => Formula::BvOr(lhs_bv, rhs_bv, w),
                        BinOp::BitXor => Formula::BvXor(lhs_bv, rhs_bv, w),
                        BinOp::Shl => Formula::BvShl(lhs_bv, rhs_bv, w),
                        // Use arithmetic right shift for signed types,
                        // logical right shift for unsigned.
                        BinOp::Shr if signed => Formula::BvAShr(lhs_bv, rhs_bv, w),
                        BinOp::Shr => Formula::BvLShr(lhs_bv, rhs_bv, w),
                        _ => unreachable!(
                            "bitvector BinOp branch only handles BitAnd, BitOr, BitXor, Shl, and Shr"
                        ),
                    };
                    Formula::BvToInt(Box::new(bv_result), w, signed)
                }
                _ => unreachable!("unhandled BinOp variant"),
            }
        }
        SymbolicValue::Ite(cond, then_val, else_val) => Formula::Ite(
            Box::new(symbolic_to_formula_with_signedness(cond, signed)),
            Box::new(symbolic_to_formula_with_signedness(then_val, signed)),
            Box::new(symbolic_to_formula_with_signedness(else_val, signed)),
        ),
        SymbolicValue::Not(inner) => {
            Formula::Not(Box::new(symbolic_to_formula_with_signedness(inner, signed)))
        }
        SymbolicValue::BitwiseNot(inner) => {
            let w = 64u32;
            let inner_bv =
                Formula::IntToBv(Box::new(symbolic_to_formula_with_signedness(inner, signed)), w);
            Formula::BvToInt(Box::new(Formula::BvNot(Box::new(inner_bv), w)), w, signed)
        }
        SymbolicValue::Neg(inner) => Formula::Sub(
            Box::new(Formula::Int(0)),
            Box::new(symbolic_to_formula_with_signedness(inner, signed)),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path_empty_to_formula() {
        let pc = PathConstraint::new();
        assert_eq!(pc.to_formula(), Formula::Bool(true));
    }

    #[test]
    fn test_path_single_taken_constraint() {
        let mut pc = PathConstraint::new();
        pc.add_constraint(
            SymbolicValue::bin_op(
                SymbolicValue::Symbol("x".into()),
                BinOp::Lt,
                SymbolicValue::Concrete(10),
            ),
            true,
        );
        let f = pc.to_formula();
        // Should be: x < 10
        match &f {
            Formula::Lt(_, _) => {} // correct
            other => panic!("expected Lt, got {other:?}"),
        }
    }

    #[test]
    fn test_path_single_not_taken_constraint() {
        let mut pc = PathConstraint::new();
        pc.add_constraint(
            SymbolicValue::bin_op(
                SymbolicValue::Symbol("x".into()),
                BinOp::Lt,
                SymbolicValue::Concrete(10),
            ),
            false,
        );
        let f = pc.to_formula();
        // Should be: NOT(x < 10)
        match &f {
            Formula::Not(_) => {}
            other => panic!("expected Not, got {other:?}"),
        }
    }

    #[test]
    fn test_path_multiple_constraints_and() {
        let mut pc = PathConstraint::new();
        pc.add_constraint(SymbolicValue::Symbol("a".into()), true);
        pc.add_constraint(SymbolicValue::Symbol("b".into()), false);
        let f = pc.to_formula();
        match &f {
            Formula::And(clauses) => assert_eq!(clauses.len(), 2),
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_path_negate_last() {
        let mut pc = PathConstraint::new();
        pc.add_constraint(SymbolicValue::Symbol("a".into()), true);
        pc.add_constraint(SymbolicValue::Symbol("b".into()), true);
        let negated = pc.negate_last().expect("should produce negated path");
        assert_eq!(negated.depth(), 2);
        assert!(negated.decisions()[0].taken);
        assert!(!negated.decisions()[1].taken);
    }

    #[test]
    fn test_path_negate_last_empty_returns_none() {
        let pc = PathConstraint::new();
        assert!(pc.negate_last().is_none());
    }

    #[test]
    fn test_path_depth() {
        let mut pc = PathConstraint::new();
        assert_eq!(pc.depth(), 0);
        pc.add_constraint(SymbolicValue::Concrete(1), true);
        assert_eq!(pc.depth(), 1);
        pc.add_constraint(SymbolicValue::Concrete(0), false);
        assert_eq!(pc.depth(), 2);
    }

    #[test]
    fn test_symbolic_to_formula_concrete() {
        assert_eq!(symbolic_to_formula(&SymbolicValue::Concrete(42)), Formula::Int(42));
    }

    #[test]
    fn test_symbolic_to_formula_symbol() {
        assert_eq!(
            symbolic_to_formula(&SymbolicValue::Symbol("x".into())),
            Formula::Var("x".into(), Sort::Int)
        );
    }

    #[test]
    fn test_symbolic_to_formula_binop_add() {
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Concrete(1),
            BinOp::Add,
            SymbolicValue::Concrete(2),
        );
        assert_eq!(
            symbolic_to_formula(&expr),
            Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(2)))
        );
    }

    #[test]
    fn test_symbolic_to_formula_ne() {
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Concrete(1),
            BinOp::Ne,
            SymbolicValue::Concrete(2),
        );
        assert_eq!(
            symbolic_to_formula(&expr),
            Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Int(1)),
                Box::new(Formula::Int(2))
            )))
        );
    }

    #[test]
    fn test_symbolic_to_formula_ite() {
        let expr = SymbolicValue::ite(
            SymbolicValue::Symbol("cond".into()),
            SymbolicValue::Concrete(1),
            SymbolicValue::Concrete(0),
        );
        assert_eq!(
            symbolic_to_formula(&expr),
            Formula::Ite(
                Box::new(Formula::Var("cond".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
                Box::new(Formula::Int(0))
            )
        );
    }

    #[test]
    fn test_symbolic_to_formula_not() {
        let expr = SymbolicValue::Not(Box::new(SymbolicValue::Symbol("flag".into())));
        assert_eq!(
            symbolic_to_formula(&expr),
            Formula::Not(Box::new(Formula::Var("flag".into(), Sort::Int)))
        );
    }

    // Bitwise ops now emit proper bitvector formulas.
    #[test]
    fn test_symbolic_to_formula_bitwise() {
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Concrete(0b1010),
            BinOp::BitAnd,
            SymbolicValue::Concrete(0b1100),
        );
        match symbolic_to_formula(&expr) {
            Formula::BvToInt(_, 64, false) => {} // Correct: BvToInt(BvAnd(...), 64, false)
            other => panic!("expected BvToInt bitvector formula, got {other:?}"),
        }
    }

    // Unsigned right-shift (default) produces BvLShr.
    #[test]
    fn test_symbolic_to_formula_shr_unsigned() {
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Concrete(-8),
            BinOp::Shr,
            SymbolicValue::Concrete(1),
        );
        // Default (unsigned): should produce BvLShr
        match symbolic_to_formula(&expr) {
            Formula::BvToInt(inner, 64, false) => match *inner {
                Formula::BvLShr(_, _, 64) => {} // Correct: logical shift right
                other => panic!("expected BvLShr inside BvToInt, got {other:?}"),
            },
            other => panic!("expected BvToInt(BvLShr(...)), got {other:?}"),
        }
    }

    // Signed right-shift produces BvAShr (arithmetic, sign-extending).
    #[test]
    fn test_symbolic_to_formula_shr_signed() {
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Concrete(-8),
            BinOp::Shr,
            SymbolicValue::Concrete(1),
        );
        // Signed: should produce BvAShr (arithmetic shift right) with signed=true
        // in BvToInt. P0-6: BvToInt propagates the signedness flag.
        match symbolic_to_formula_with_signedness(&expr, true) {
            Formula::BvToInt(inner, 64, true) => match *inner {
                Formula::BvAShr(_, _, 64) => {} // Correct: arithmetic shift right
                other => panic!("expected BvAShr inside BvToInt, got {other:?}"),
            },
            other => panic!("expected BvToInt(BvAShr(...)), got {other:?}"),
        }
    }

    // Non-shift operations are unaffected by signedness flag.
    #[test]
    fn test_symbolic_to_formula_add_unaffected_by_signedness() {
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Concrete(3),
            BinOp::Add,
            SymbolicValue::Concrete(4),
        );
        assert_eq!(symbolic_to_formula(&expr), symbolic_to_formula_with_signedness(&expr, true),);
    }

    #[test]
    fn test_path_is_empty() {
        let mut pc = PathConstraint::new();
        assert!(pc.is_empty());
        pc.add_constraint(SymbolicValue::Concrete(1), true);
        assert!(!pc.is_empty());
    }
}
