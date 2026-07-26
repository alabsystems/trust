// trust-types/formula_arena/structural.rs: Deep structural equality and hashing
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::FxHashMap;
use std::hash::{Hash, Hasher};

use super::arena::FormulaArena;
use super::types::{FormulaNode, FormulaRef};

impl FormulaArena {
    // -----------------------------------------------------------------------
    // Structural equality and hashing (deep comparison with memoization)
    // -----------------------------------------------------------------------

    /// Deep structural equality test between two formula refs in this arena.
    ///
    /// Unlike `FormulaRef::eq` (which compares indices), this compares the
    /// actual formula structure recursively. Memoized to avoid exponential
    /// blowup on DAGs with sharing.
    #[must_use]
    pub fn structural_eq(&self, a: FormulaRef, b: FormulaRef) -> bool {
        if a == b {
            return true;
        }
        let mut memo: FxHashMap<(FormulaRef, FormulaRef), bool> = FxHashMap::default();
        self.structural_eq_inner(a, b, &mut memo)
    }

    fn structural_eq_inner(
        &self,
        a: FormulaRef,
        b: FormulaRef,
        memo: &mut FxHashMap<(FormulaRef, FormulaRef), bool>,
    ) -> bool {
        if a == b {
            return true;
        }
        // Normalize the key so (a, b) and (b, a) share a memo entry
        let key = if a <= b { (a, b) } else { (b, a) };
        if let Some(&result) = memo.get(&key) {
            return result;
        }

        let na = self.get(a);
        let nb = self.get(b);
        let result = self.nodes_structurally_eq(na, nb, memo);
        memo.insert(key, result);
        result
    }

    fn nodes_structurally_eq(
        &self,
        na: &FormulaNode,
        nb: &FormulaNode,
        memo: &mut FxHashMap<(FormulaRef, FormulaRef), bool>,
    ) -> bool {
        match (na, nb) {
            // Leaves
            (FormulaNode::Bool(a), FormulaNode::Bool(b)) => a == b,
            (FormulaNode::Int(a), FormulaNode::Int(b)) => a == b,
            (FormulaNode::UInt(a), FormulaNode::UInt(b)) => a == b,
            (
                FormulaNode::BitVec { value: va, width: wa },
                FormulaNode::BitVec { value: vb, width: wb },
            ) => va == vb && wa == wb,
            (FormulaNode::Var(na, sa), FormulaNode::Var(nb, sb)) => na == nb && sa == sb,

            // Unary
            (FormulaNode::Not(a), FormulaNode::Not(b))
            | (FormulaNode::Neg(a), FormulaNode::Neg(b)) => self.structural_eq_inner(*a, *b, memo),
            (FormulaNode::BvNot(a, wa), FormulaNode::BvNot(b, wb)) => {
                wa == wb && self.structural_eq_inner(*a, *b, memo)
            }
            (FormulaNode::BvToInt(a, wa, sa), FormulaNode::BvToInt(b, wb, sb)) => {
                wa == wb && sa == sb && self.structural_eq_inner(*a, *b, memo)
            }
            (FormulaNode::IntToBv(a, wa), FormulaNode::IntToBv(b, wb)) => {
                wa == wb && self.structural_eq_inner(*a, *b, memo)
            }
            (FormulaNode::BvZeroExt(a, ba), FormulaNode::BvZeroExt(b, bb)) => {
                ba == bb && self.structural_eq_inner(*a, *b, memo)
            }
            (FormulaNode::BvSignExt(a, ba), FormulaNode::BvSignExt(b, bb)) => {
                ba == bb && self.structural_eq_inner(*a, *b, memo)
            }
            (
                FormulaNode::BvExtract { inner: ia, high: ha, low: la },
                FormulaNode::BvExtract { inner: ib, high: hb, low: lb },
            ) => ha == hb && la == lb && self.structural_eq_inner(*ia, *ib, memo),

            // N-ary
            (FormulaNode::And(sa, ca), FormulaNode::And(sb, cb)) => {
                if ca != cb {
                    return false;
                }
                let refs_a = self.get_refs(*sa, *ca).to_vec();
                let refs_b = self.get_refs(*sb, *cb).to_vec();
                refs_a
                    .iter()
                    .zip(refs_b.iter())
                    .all(|(a, b)| self.structural_eq_inner(*a, *b, memo))
            }
            (FormulaNode::Or(sa, ca), FormulaNode::Or(sb, cb)) => {
                if ca != cb {
                    return false;
                }
                let refs_a = self.get_refs(*sa, *ca).to_vec();
                let refs_b = self.get_refs(*sb, *cb).to_vec();
                refs_a
                    .iter()
                    .zip(refs_b.iter())
                    .all(|(a, b)| self.structural_eq_inner(*a, *b, memo))
            }

            // Binary (no width)
            (FormulaNode::Implies(a1, a2), FormulaNode::Implies(b1, b2))
            | (FormulaNode::Eq(a1, a2), FormulaNode::Eq(b1, b2))
            | (FormulaNode::Lt(a1, a2), FormulaNode::Lt(b1, b2))
            | (FormulaNode::Le(a1, a2), FormulaNode::Le(b1, b2))
            | (FormulaNode::Gt(a1, a2), FormulaNode::Gt(b1, b2))
            | (FormulaNode::Ge(a1, a2), FormulaNode::Ge(b1, b2))
            | (FormulaNode::Add(a1, a2), FormulaNode::Add(b1, b2))
            | (FormulaNode::Sub(a1, a2), FormulaNode::Sub(b1, b2))
            | (FormulaNode::Mul(a1, a2), FormulaNode::Mul(b1, b2))
            | (FormulaNode::Div(a1, a2), FormulaNode::Div(b1, b2))
            | (FormulaNode::Rem(a1, a2), FormulaNode::Rem(b1, b2))
            | (FormulaNode::BvConcat(a1, a2), FormulaNode::BvConcat(b1, b2))
            | (FormulaNode::Select(a1, a2), FormulaNode::Select(b1, b2)) => {
                self.structural_eq_inner(*a1, *b1, memo) && self.structural_eq_inner(*a2, *b2, memo)
            }

            // Binary with width -- check variant discriminant and width
            (FormulaNode::BvAdd(a1, a2, wa), FormulaNode::BvAdd(b1, b2, wb))
            | (FormulaNode::BvSub(a1, a2, wa), FormulaNode::BvSub(b1, b2, wb))
            | (FormulaNode::BvMul(a1, a2, wa), FormulaNode::BvMul(b1, b2, wb))
            | (FormulaNode::BvUDiv(a1, a2, wa), FormulaNode::BvUDiv(b1, b2, wb))
            | (FormulaNode::BvSDiv(a1, a2, wa), FormulaNode::BvSDiv(b1, b2, wb))
            | (FormulaNode::BvURem(a1, a2, wa), FormulaNode::BvURem(b1, b2, wb))
            | (FormulaNode::BvSRem(a1, a2, wa), FormulaNode::BvSRem(b1, b2, wb))
            | (FormulaNode::BvAnd(a1, a2, wa), FormulaNode::BvAnd(b1, b2, wb))
            | (FormulaNode::BvOr(a1, a2, wa), FormulaNode::BvOr(b1, b2, wb))
            | (FormulaNode::BvXor(a1, a2, wa), FormulaNode::BvXor(b1, b2, wb))
            | (FormulaNode::BvShl(a1, a2, wa), FormulaNode::BvShl(b1, b2, wb))
            | (FormulaNode::BvLShr(a1, a2, wa), FormulaNode::BvLShr(b1, b2, wb))
            | (FormulaNode::BvAShr(a1, a2, wa), FormulaNode::BvAShr(b1, b2, wb))
            | (FormulaNode::BvULt(a1, a2, wa), FormulaNode::BvULt(b1, b2, wb))
            | (FormulaNode::BvULe(a1, a2, wa), FormulaNode::BvULe(b1, b2, wb))
            | (FormulaNode::BvSLt(a1, a2, wa), FormulaNode::BvSLt(b1, b2, wb))
            | (FormulaNode::BvSLe(a1, a2, wa), FormulaNode::BvSLe(b1, b2, wb)) => {
                wa == wb
                    && self.structural_eq_inner(*a1, *b1, memo)
                    && self.structural_eq_inner(*a2, *b2, memo)
            }

            // Ternary
            (FormulaNode::Ite(a1, a2, a3), FormulaNode::Ite(b1, b2, b3))
            | (FormulaNode::Store(a1, a2, a3), FormulaNode::Store(b1, b2, b3)) => {
                self.structural_eq_inner(*a1, *b1, memo)
                    && self.structural_eq_inner(*a2, *b2, memo)
                    && self.structural_eq_inner(*a3, *b3, memo)
            }

            // Quantifiers
            (FormulaNode::Forall(ba, bodya), FormulaNode::Forall(bb, bodyb))
            | (FormulaNode::Exists(ba, bodya), FormulaNode::Exists(bb, bodyb)) => {
                ba == bb && self.structural_eq_inner(*bodya, *bodyb, memo)
            }

            // Different variant tags
            _ => false,
        }
    }

    /// Compute a structural hash of the formula rooted at `r`.
    ///
    /// Two formulas that are `structural_eq` will produce the same hash.
    /// Uses memoization for DAG-safe computation.
    #[must_use]
    pub fn structural_hash(&self, r: FormulaRef) -> u64 {
        let mut memo: FxHashMap<FormulaRef, u64> = FxHashMap::default();
        self.structural_hash_inner(r, &mut memo)
    }

    fn structural_hash_inner(&self, r: FormulaRef, memo: &mut FxHashMap<FormulaRef, u64>) -> u64 {
        if let Some(&h) = memo.get(&r) {
            return h;
        }

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        let node = self.get(r);

        // Hash a discriminant tag for the variant
        std::mem::discriminant(node).hash(&mut hasher);

        match node {
            FormulaNode::Bool(v) => v.hash(&mut hasher),
            FormulaNode::Int(v) => v.hash(&mut hasher),
            FormulaNode::UInt(v) => v.hash(&mut hasher),
            FormulaNode::BitVec { value, width } => {
                value.hash(&mut hasher);
                width.hash(&mut hasher);
            }
            FormulaNode::Var(name, sort) => {
                name.hash(&mut hasher);
                sort.hash(&mut hasher);
            }
            _ => {
                // Hash metadata (widths, bindings) for specific variants
                match node {
                    FormulaNode::BvNot(_, w)
                    | FormulaNode::BvAdd(_, _, w)
                    | FormulaNode::BvSub(_, _, w)
                    | FormulaNode::BvMul(_, _, w)
                    | FormulaNode::BvUDiv(_, _, w)
                    | FormulaNode::BvSDiv(_, _, w)
                    | FormulaNode::BvURem(_, _, w)
                    | FormulaNode::BvSRem(_, _, w)
                    | FormulaNode::BvAnd(_, _, w)
                    | FormulaNode::BvOr(_, _, w)
                    | FormulaNode::BvXor(_, _, w)
                    | FormulaNode::BvShl(_, _, w)
                    | FormulaNode::BvLShr(_, _, w)
                    | FormulaNode::BvAShr(_, _, w)
                    | FormulaNode::BvULt(_, _, w)
                    | FormulaNode::BvULe(_, _, w)
                    | FormulaNode::BvSLt(_, _, w)
                    | FormulaNode::BvSLe(_, _, w) => w.hash(&mut hasher),
                    FormulaNode::BvToInt(_, w, s) => {
                        w.hash(&mut hasher);
                        s.hash(&mut hasher);
                    }
                    FormulaNode::IntToBv(_, w)
                    | FormulaNode::BvZeroExt(_, w)
                    | FormulaNode::BvSignExt(_, w) => w.hash(&mut hasher),
                    FormulaNode::BvExtract { high, low, .. } => {
                        high.hash(&mut hasher);
                        low.hash(&mut hasher);
                    }
                    FormulaNode::Forall(bindings, _) | FormulaNode::Exists(bindings, _) => {
                        bindings.hash(&mut hasher);
                    }
                    _ => {}
                }
                // Hash children recursively
                let children = self.children(r);
                children.len().hash(&mut hasher);
                for child in &children {
                    let child_hash = self.structural_hash_inner(*child, memo);
                    child_hash.hash(&mut hasher);
                }
            }
        }

        let h = hasher.finish();
        memo.insert(r, h);
        h
    }
}
