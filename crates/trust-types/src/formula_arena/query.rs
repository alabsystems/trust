// trust-types/formula_arena/query.rs: Query helpers and DAG traversal
//
// free_variables, has_bitvectors, has_arrays, has_large_integers,
// rename_var, topological_order.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::FxHashSet;

use crate::formula::Sort;

use super::arena::FormulaArena;
use super::types::{FormulaNode, FormulaRef};

impl FormulaArena {
    // -----------------------------------------------------------------------
    // Query helpers: free_variables, has_bitvectors, has_arrays, etc.
    // -----------------------------------------------------------------------

    /// Collect all free variable names in the formula rooted at `r`.
    ///
    /// Variables bound by `Forall`/`Exists` are excluded.
    #[must_use]
    pub fn free_variables(&self, root: FormulaRef) -> FxHashSet<String> {
        let mut free = FxHashSet::default();
        self.free_variables_inner(root, &mut free, &FxHashSet::default());
        free
    }

    fn free_variables_inner(
        &self,
        r: FormulaRef,
        free: &mut FxHashSet<String>,
        bound: &FxHashSet<String>,
    ) {
        match self.get(r) {
            FormulaNode::Var(name, _) => {
                if !bound.contains(name) {
                    free.insert(name.clone());
                }
            }
            // Quantifier bindings use Symbol; convert to String for tracking.
            FormulaNode::Forall(bindings, body) | FormulaNode::Exists(bindings, body) => {
                let mut new_bound = bound.clone();
                for (sym, _) in bindings {
                    new_bound.insert(sym.as_str().to_string());
                }
                self.free_variables_inner(*body, free, &new_bound);
            }
            _ => {
                for child in self.children(r) {
                    self.free_variables_inner(child, free, bound);
                }
            }
        }
    }

    /// Check if the formula rooted at `r` contains bitvector operations or types.
    #[must_use]
    pub fn has_bitvectors(&self, root: FormulaRef) -> bool {
        let mut found = false;
        self.visit(root, &mut |_, node| {
            if found {
                return;
            }
            match node {
                FormulaNode::BitVec { .. }
                | FormulaNode::BvAdd(..)
                | FormulaNode::BvSub(..)
                | FormulaNode::BvMul(..)
                | FormulaNode::BvUDiv(..)
                | FormulaNode::BvSDiv(..)
                | FormulaNode::BvURem(..)
                | FormulaNode::BvSRem(..)
                | FormulaNode::BvAnd(..)
                | FormulaNode::BvOr(..)
                | FormulaNode::BvXor(..)
                | FormulaNode::BvNot(..)
                | FormulaNode::BvShl(..)
                | FormulaNode::BvLShr(..)
                | FormulaNode::BvAShr(..)
                | FormulaNode::BvULt(..)
                | FormulaNode::BvULe(..)
                | FormulaNode::BvSLt(..)
                | FormulaNode::BvSLe(..)
                | FormulaNode::BvToInt(..)
                | FormulaNode::IntToBv(..)
                | FormulaNode::BvExtract { .. }
                | FormulaNode::BvConcat(..)
                | FormulaNode::BvZeroExt(..)
                | FormulaNode::BvSignExt(..) => found = true,
                FormulaNode::Var(_, Sort::BitVec(_)) => found = true,
                _ => {}
            }
        });
        found
    }

    /// Check if the formula rooted at `r` contains array operations (Select/Store).
    #[must_use]
    pub fn has_arrays(&self, root: FormulaRef) -> bool {
        let mut found = false;
        self.visit(root, &mut |_, node| {
            if found {
                return;
            }
            match node {
                FormulaNode::Select(..) | FormulaNode::Store(..) => found = true,
                FormulaNode::Var(_, Sort::Array(_, _)) => found = true,
                _ => {}
            }
        });
        found
    }

    /// Check if the formula contains integer literals outside the i64 range.
    #[must_use]
    pub fn has_large_integers(&self, root: FormulaRef) -> bool {
        let mut found = false;
        self.visit(root, &mut |_, node| {
            if found {
                return;
            }
            match node {
                FormulaNode::Int(n) if i64::try_from(*n).is_err() => {
                    found = true;
                }
                FormulaNode::UInt(n) if i64::try_from(*n).is_err() => {
                    found = true;
                }
                _ => {}
            }
        });
        found
    }

    /// Rename a variable throughout the formula (syntactic rename, ignores
    /// quantifier bindings per `Formula::rename_var` semantics).
    pub fn rename_var(&mut self, root: FormulaRef, from: &str, to: &str) -> FormulaRef {
        let node = self.get(root).clone();
        match &node {
            FormulaNode::Var(name, sort) if name == from => {
                self.push(FormulaNode::Var(to.to_string(), sort.clone()))
            }
            // Leaves that don't match: return unchanged
            FormulaNode::Bool(_)
            | FormulaNode::Int(_)
            | FormulaNode::UInt(_)
            | FormulaNode::BitVec { .. }
            | FormulaNode::Var(..) => root,
            // Recurse through children
            _ => {
                let children = self.children(root);
                let new_children: Vec<FormulaRef> =
                    children.iter().map(|c| self.rename_var(*c, from, to)).collect();
                if new_children == children {
                    root
                } else {
                    self.rebuild_with_children(root, &new_children)
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // DAG traversal: topological order
    // -----------------------------------------------------------------------

    /// Return all nodes reachable from `root` in topological order
    /// (children before parents). Each node appears exactly once, even if
    /// shared via DAG structure.
    ///
    /// This is useful for bottom-up passes that need to process each node
    /// once without exponential blowup on shared subgraphs.
    #[must_use]
    pub fn topological_order(&self, root: FormulaRef) -> Vec<FormulaRef> {
        let mut visited = FxHashSet::default();
        let mut order = Vec::new();
        self.topo_dfs(root, &mut visited, &mut order);
        order
    }

    fn topo_dfs(
        &self,
        r: FormulaRef,
        visited: &mut FxHashSet<FormulaRef>,
        order: &mut Vec<FormulaRef>,
    ) {
        if !visited.insert(r) {
            return;
        }
        for child in self.children(r) {
            self.topo_dfs(child, visited, order);
        }
        order.push(r);
    }
}
