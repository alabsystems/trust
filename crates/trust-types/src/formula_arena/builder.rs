// trust-types/formula_arena/builder.rs: Convenience builder methods
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::formula::Sort;

use super::arena::FormulaArena;
use super::types::{FormulaNode, FormulaRef};

// -----------------------------------------------------------------------
// Builder helpers: construct formulas directly in the arena
// -----------------------------------------------------------------------

impl FormulaArena {
    /// Push a boolean literal.
    pub fn bool(&mut self, v: bool) -> FormulaRef {
        self.push(FormulaNode::Bool(v))
    }

    /// Push an integer literal.
    pub fn int(&mut self, v: i128) -> FormulaRef {
        self.push(FormulaNode::Int(v))
    }

    /// Push an unsigned integer literal.
    pub fn uint(&mut self, v: u128) -> FormulaRef {
        self.push(FormulaNode::UInt(v))
    }

    /// Push a bitvector literal.
    pub fn bitvec(&mut self, value: i128, width: u32) -> FormulaRef {
        self.push(FormulaNode::BitVec { value, width })
    }

    /// Push a variable.
    pub fn var(&mut self, name: impl Into<String>, sort: Sort) -> FormulaRef {
        self.push(FormulaNode::Var(name.into(), sort))
    }

    /// Push a Not node.
    pub fn not(&mut self, a: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Not(a))
    }

    /// Push an And node (with hash-consing deduplication).
    pub fn and(&mut self, terms: &[FormulaRef]) -> FormulaRef {
        self.push_nary(terms, true)
    }

    /// Push an Or node (with hash-consing deduplication).
    pub fn or(&mut self, terms: &[FormulaRef]) -> FormulaRef {
        self.push_nary(terms, false)
    }

    /// Push an Implies node.
    pub fn implies(&mut self, a: FormulaRef, b: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Implies(a, b))
    }

    /// Push an Eq node.
    pub fn eq(&mut self, a: FormulaRef, b: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Eq(a, b))
    }

    /// Push an Add node.
    pub fn add(&mut self, a: FormulaRef, b: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Add(a, b))
    }

    /// Push a Sub node.
    pub fn sub(&mut self, a: FormulaRef, b: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Sub(a, b))
    }

    /// Push a Mul node.
    pub fn mul(&mut self, a: FormulaRef, b: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Mul(a, b))
    }

    /// Push a Lt node.
    pub fn lt(&mut self, a: FormulaRef, b: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Lt(a, b))
    }

    /// Push a Le node.
    pub fn le(&mut self, a: FormulaRef, b: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Le(a, b))
    }

    /// Push a Gt node.
    pub fn gt(&mut self, a: FormulaRef, b: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Gt(a, b))
    }

    /// Push a Ge node.
    pub fn ge(&mut self, a: FormulaRef, b: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Ge(a, b))
    }

    /// Push an Ite (if-then-else) node.
    pub fn ite(&mut self, cond: FormulaRef, then: FormulaRef, els: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Ite(cond, then, els))
    }

    /// Push a BvAdd node.
    pub fn bv_add(&mut self, a: FormulaRef, b: FormulaRef, w: u32) -> FormulaRef {
        self.push(FormulaNode::BvAdd(a, b, w))
    }

    /// Push a Forall quantifier.
    // Bindings use interned Symbol.
    pub fn forall(&mut self, bindings: Vec<(crate::Symbol, Sort)>, body: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Forall(bindings, body))
    }

    /// Push an Exists quantifier.
    // Bindings use interned Symbol.
    pub fn exists(&mut self, bindings: Vec<(crate::Symbol, Sort)>, body: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Exists(bindings, body))
    }

    /// Push a Select (array read) node.
    pub fn select(&mut self, arr: FormulaRef, idx: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Select(arr, idx))
    }

    /// Push a Store (array write) node.
    pub fn store(&mut self, arr: FormulaRef, idx: FormulaRef, val: FormulaRef) -> FormulaRef {
        self.push(FormulaNode::Store(arr, idx, val))
    }
}
