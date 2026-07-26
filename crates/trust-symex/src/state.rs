// trust-symex symbolic state
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use trust_types::BinOp;

use crate::error::SymexError;

/// A symbolic value in the execution state.
///
/// Values are either concrete (known at execution time), symbolic (unknown,
/// representing an input), or compound expressions built from operations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SymbolicValue {
    /// A concrete integer value.
    Concrete(i128),
    /// A named symbolic variable (unknown input).
    Symbol(String),
    /// A binary operation on two symbolic values.
    BinOp(Box<SymbolicValue>, BinOp, Box<SymbolicValue>),
    /// If-then-else: `Ite(cond, then_val, else_val)`.
    Ite(Box<SymbolicValue>, Box<SymbolicValue>, Box<SymbolicValue>),
    /// Boolean negation of a symbolic value.
    Not(Box<SymbolicValue>),
    /// Bitwise NOT of a symbolic value (`!x`).
    BitwiseNot(Box<SymbolicValue>),
    /// Arithmetic negation of a symbolic value (`-x`).
    Neg(Box<SymbolicValue>),
}

impl SymbolicValue {
    /// Create a binary operation node.
    #[must_use]
    pub fn bin_op(lhs: SymbolicValue, op: BinOp, rhs: SymbolicValue) -> Self {
        Self::BinOp(Box::new(lhs), op, Box::new(rhs))
    }

    /// Create an if-then-else node.
    #[must_use]
    pub fn ite(cond: SymbolicValue, then_val: SymbolicValue, else_val: SymbolicValue) -> Self {
        Self::Ite(Box::new(cond), Box::new(then_val), Box::new(else_val))
    }

    /// Returns `true` if the value is fully concrete (no symbols).
    #[must_use]
    pub fn is_concrete(&self) -> bool {
        match self {
            Self::Concrete(_) => true,
            Self::Symbol(_) => false,
            Self::BinOp(l, _, r) => l.is_concrete() && r.is_concrete(),
            Self::Ite(c, t, e) => c.is_concrete() && t.is_concrete() && e.is_concrete(),
            Self::Not(inner) | Self::BitwiseNot(inner) | Self::Neg(inner) => inner.is_concrete(),
        }
    }

    /// Collect all symbol names referenced in this value.
    #[must_use]
    pub fn symbols(&self) -> Vec<String> {
        let mut out = Vec::new();
        self.collect_symbols(&mut out);
        out.sort();
        out.dedup();
        out
    }

    fn collect_symbols(&self, out: &mut Vec<String>) {
        match self {
            Self::Concrete(_) => {}
            Self::Symbol(name) => out.push(name.clone()),
            Self::BinOp(l, _, r) => {
                l.collect_symbols(out);
                r.collect_symbols(out);
            }
            Self::Ite(c, t, e) => {
                c.collect_symbols(out);
                t.collect_symbols(out);
                e.collect_symbols(out);
            }
            Self::Not(inner) | Self::BitwiseNot(inner) | Self::Neg(inner) => {
                inner.collect_symbols(out);
            }
        }
    }
}

/// Mapping from variable names to their symbolic values.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SymbolicState {
    vars: BTreeMap<String, SymbolicValue>,
}

impl SymbolicState {
    /// Create an empty symbolic state.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Bind a variable to a symbolic value.
    pub fn set(&mut self, name: impl Into<String>, value: SymbolicValue) {
        self.vars.insert(name.into(), value);
    }

    /// Look up a variable's symbolic value.
    pub fn get(&self, name: &str) -> Result<&SymbolicValue, SymexError> {
        self.vars.get(name).ok_or_else(|| SymexError::UndefinedVariable(name.to_owned()))
    }

    /// Look up a variable, returning `None` if absent.
    #[must_use]
    pub fn try_get(&self, name: &str) -> Option<&SymbolicValue> {
        self.vars.get(name)
    }

    /// Returns the number of bindings in the state.
    #[must_use]
    pub fn len(&self) -> usize {
        self.vars.len()
    }

    /// Returns `true` if no variables are bound.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }

    /// Iterate over all variable bindings.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &SymbolicValue)> {
        self.vars.iter().map(|(k, v)| (k.as_str(), v))
    }
}

/// Attempt concrete evaluation of a symbolic value.
///
/// Returns `Some(value)` if the entire expression tree is concrete,
/// `None` if any symbol is encountered.
#[must_use]
pub fn eval(state: &SymbolicState, expr: &SymbolicValue) -> Option<i128> {
    eval_inner(state, expr)
}

fn eval_inner(state: &SymbolicState, expr: &SymbolicValue) -> Option<i128> {
    match expr {
        SymbolicValue::Concrete(v) => Some(*v),
        SymbolicValue::Symbol(name) => {
            let val = state.try_get(name)?;
            eval_inner(state, val)
        }
        SymbolicValue::BinOp(lhs, op, rhs) => {
            let l = eval_inner(state, lhs)?;
            let r = eval_inner(state, rhs)?;
            eval_binop(l, *op, r)
        }
        SymbolicValue::Ite(cond, then_val, else_val) => {
            let c = eval_inner(state, cond)?;
            if c != 0 { eval_inner(state, then_val) } else { eval_inner(state, else_val) }
        }
        SymbolicValue::Not(inner) => {
            let v = eval_inner(state, inner)?;
            Some(if v == 0 { 1 } else { 0 })
        }
        SymbolicValue::BitwiseNot(inner) => {
            let v = eval_inner(state, inner)?;
            Some(!v)
        }
        SymbolicValue::Neg(inner) => {
            let v = eval_inner(state, inner)?;
            v.checked_neg()
        }
    }
}

fn eval_binop(l: i128, op: BinOp, r: i128) -> Option<i128> {
    match op {
        BinOp::Add => l.checked_add(r),
        BinOp::Sub => l.checked_sub(r),
        BinOp::Mul => l.checked_mul(r),
        BinOp::Div => {
            if r == 0 {
                None
            } else {
                l.checked_div(r)
            }
        }
        BinOp::Rem => {
            if r == 0 {
                None
            } else {
                l.checked_rem(r)
            }
        }
        BinOp::Eq => Some(i128::from(l == r)),
        BinOp::Ne => Some(i128::from(l != r)),
        BinOp::Lt => Some(i128::from(l < r)),
        BinOp::Le => Some(i128::from(l <= r)),
        BinOp::Gt => Some(i128::from(l > r)),
        BinOp::Ge => Some(i128::from(l >= r)),
        BinOp::BitAnd => Some(l & r),
        BinOp::BitOr => Some(l | r),
        BinOp::BitXor => Some(l ^ r),
        // Clamp shift amount to 127 to prevent panic on large values.
        BinOp::Shl => {
            let shift = u32::try_from(r).unwrap_or(128).min(127);
            Some(l.wrapping_shl(shift))
        }
        BinOp::Shr => {
            let shift = u32::try_from(r).unwrap_or(128).min(127);
            Some(l.wrapping_shr(shift))
        }
        // Three-way comparison returns -1 (Less), 0 (Equal), or 1 (Greater).
        BinOp::Cmp => Some(if l < r {
            -1
        } else if l == r {
            0
        } else {
            1
        }),
        _ => None, // Unhandled BinOp variant — return None to signal non-evaluability.
    }
}

#[cfg(test)]
mod tests {
    use crate::error::SymexError;

    use super::*;

    #[test]
    fn test_state_concrete_eval_addition() {
        let mut state = SymbolicState::new();
        state.set("x", SymbolicValue::Concrete(10));
        state.set("y", SymbolicValue::Concrete(20));
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Symbol("x".into()),
            BinOp::Add,
            SymbolicValue::Symbol("y".into()),
        );
        assert_eq!(eval(&state, &expr), Some(30));
    }

    #[test]
    fn test_state_symbolic_eval_returns_none() {
        let state = SymbolicState::new();
        let expr = SymbolicValue::Symbol("unknown".into());
        assert_eq!(eval(&state, &expr), None);
    }

    #[test]
    fn test_state_nested_binop_eval() {
        let state = SymbolicState::new();
        // (3 + 4) * 2 = 14
        let expr = SymbolicValue::bin_op(
            SymbolicValue::bin_op(
                SymbolicValue::Concrete(3),
                BinOp::Add,
                SymbolicValue::Concrete(4),
            ),
            BinOp::Mul,
            SymbolicValue::Concrete(2),
        );
        assert_eq!(eval(&state, &expr), Some(14));
    }

    #[test]
    fn test_state_ite_true_branch() {
        let state = SymbolicState::new();
        let expr = SymbolicValue::ite(
            SymbolicValue::Concrete(1), // truthy
            SymbolicValue::Concrete(42),
            SymbolicValue::Concrete(0),
        );
        assert_eq!(eval(&state, &expr), Some(42));
    }

    #[test]
    fn test_state_ite_false_branch() {
        let state = SymbolicState::new();
        let expr = SymbolicValue::ite(
            SymbolicValue::Concrete(0), // falsy
            SymbolicValue::Concrete(42),
            SymbolicValue::Concrete(99),
        );
        assert_eq!(eval(&state, &expr), Some(99));
    }

    #[test]
    fn test_state_is_concrete() {
        assert!(SymbolicValue::Concrete(5).is_concrete());
        assert!(!SymbolicValue::Symbol("x".into()).is_concrete());
        let compound = SymbolicValue::bin_op(
            SymbolicValue::Concrete(1),
            BinOp::Add,
            SymbolicValue::Concrete(2),
        );
        assert!(compound.is_concrete());
    }

    #[test]
    fn test_state_symbols_collection() {
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Symbol("a".into()),
            BinOp::Add,
            SymbolicValue::bin_op(
                SymbolicValue::Symbol("b".into()),
                BinOp::Mul,
                SymbolicValue::Symbol("a".into()),
            ),
        );
        assert_eq!(expr.symbols(), vec!["a", "b"]);
    }

    #[test]
    fn test_state_div_by_zero_returns_none() {
        let state = SymbolicState::new();
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Concrete(10),
            BinOp::Div,
            SymbolicValue::Concrete(0),
        );
        assert_eq!(eval(&state, &expr), None);
    }

    #[test]
    fn test_state_comparison_ops() {
        let state = SymbolicState::new();
        let lt = SymbolicValue::bin_op(
            SymbolicValue::Concrete(3),
            BinOp::Lt,
            SymbolicValue::Concrete(5),
        );
        assert_eq!(eval(&state, &lt), Some(1));

        let ge = SymbolicValue::bin_op(
            SymbolicValue::Concrete(3),
            BinOp::Ge,
            SymbolicValue::Concrete(5),
        );
        assert_eq!(eval(&state, &ge), Some(0));
    }

    #[test]
    fn test_state_not_evaluation() {
        let state = SymbolicState::new();
        let not_true = SymbolicValue::Not(Box::new(SymbolicValue::Concrete(1)));
        assert_eq!(eval(&state, &not_true), Some(0));
        let not_false = SymbolicValue::Not(Box::new(SymbolicValue::Concrete(0)));
        assert_eq!(eval(&state, &not_false), Some(1));
    }

    #[test]
    fn test_state_set_and_get() {
        let mut state = SymbolicState::new();
        state.set("x", SymbolicValue::Concrete(5));
        assert_eq!(state.get("x").expect("x should be defined"), &SymbolicValue::Concrete(5));
    }

    #[test]
    fn test_state_get_undefined() {
        let state = SymbolicState::new();
        let err = state.get("missing").expect_err("missing variable should error");
        assert!(matches!(err, SymexError::UndefinedVariable(name) if name == "missing"));
    }

    #[test]
    fn test_state_try_get_some() {
        let mut state = SymbolicState::new();
        state.set("x", SymbolicValue::Concrete(5));
        assert_eq!(state.try_get("x"), Some(&SymbolicValue::Concrete(5)));
    }

    #[test]
    fn test_state_try_get_none() {
        let state = SymbolicState::new();
        assert_eq!(state.try_get("missing"), None);
    }

    #[test]
    fn test_state_len_and_is_empty() {
        let mut state = SymbolicState::new();
        assert!(state.is_empty());
        assert_eq!(state.len(), 0);

        state.set("x", SymbolicValue::Concrete(5));

        assert!(!state.is_empty());
        assert_eq!(state.len(), 1);
    }

    #[test]
    fn test_state_iter() {
        let mut state = SymbolicState::new();
        state.set("x", SymbolicValue::Concrete(5));
        state.set("y", SymbolicValue::Symbol("sym_y".into()));

        let mut bindings: Vec<_> =
            state.iter().map(|(name, value)| (name.to_owned(), value.clone())).collect();
        bindings.sort_by(|lhs, rhs| lhs.0.cmp(&rhs.0));

        assert_eq!(
            bindings,
            vec![
                ("x".into(), SymbolicValue::Concrete(5)),
                ("y".into(), SymbolicValue::Symbol("sym_y".into()))
            ]
        );
    }

    #[test]
    fn test_state_eval_rem() {
        let state = SymbolicState::new();
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Concrete(10),
            BinOp::Rem,
            SymbolicValue::Concrete(3),
        );
        assert_eq!(eval(&state, &expr), Some(1));
    }

    #[test]
    fn test_state_eval_rem_by_zero() {
        let state = SymbolicState::new();
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Concrete(10),
            BinOp::Rem,
            SymbolicValue::Concrete(0),
        );
        assert_eq!(eval(&state, &expr), None);
    }

    #[test]
    fn test_state_eval_bitwise_and() {
        let state = SymbolicState::new();
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Concrete(0b1010),
            BinOp::BitAnd,
            SymbolicValue::Concrete(0b1100),
        );
        assert_eq!(eval(&state, &expr), Some(0b1000));
    }

    #[test]
    fn test_state_eval_shift_left() {
        let state = SymbolicState::new();
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Concrete(1),
            BinOp::Shl,
            SymbolicValue::Concrete(3),
        );
        assert_eq!(eval(&state, &expr), Some(8));
    }

    #[test]
    fn test_state_is_concrete_not() {
        let expr = SymbolicValue::Not(Box::new(SymbolicValue::Concrete(1)));
        assert!(expr.is_concrete());
    }

    #[test]
    fn test_state_symbols_ite() {
        let expr = SymbolicValue::ite(
            SymbolicValue::Symbol("cond".into()),
            SymbolicValue::Symbol("then_branch".into()),
            SymbolicValue::Symbol("else_branch".into()),
        );
        assert_eq!(expr.symbols(), vec!["cond", "else_branch", "then_branch"]);
    }
}
