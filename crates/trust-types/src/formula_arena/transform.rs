// trust-types/formula_arena/transform.rs: Arena-native substitution, map, and rebuild
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::{FxHashMap, FxHashSet};

use super::arena::FormulaArena;
use super::types::{FormulaNode, FormulaRef};

impl FormulaArena {
    // -----------------------------------------------------------------------
    // Substitute: arena-native variable substitution
    // -----------------------------------------------------------------------

    /// Substitute a single variable with a replacement formula.
    ///
    /// Handles quantifier-bound variable shadowing: if `var` is bound by an
    /// enclosing `Forall`/`Exists`, substitution stops within that scope.
    /// Returns the original ref when nothing changes (sharing-preserving).
    pub fn substitute(
        &mut self,
        root: FormulaRef,
        var: &str,
        replacement: FormulaRef,
    ) -> FormulaRef {
        self.substitute_inner(root, var, replacement, &FxHashSet::default())
    }

    fn substitute_inner(
        &mut self,
        root: FormulaRef,
        var: &str,
        replacement: FormulaRef,
        bound: &FxHashSet<String>,
    ) -> FormulaRef {
        // Clone the node to release the immutable borrow on self.
        let node = self.get(root).clone();
        match &node {
            FormulaNode::Var(name, _) if name == var && !bound.contains(var) => replacement,

            // Quantifier bindings use Symbol; convert to String for tracking.
            FormulaNode::Forall(bindings, body) | FormulaNode::Exists(bindings, body) => {
                let mut new_bound = bound.clone();
                for (sym, _) in bindings {
                    new_bound.insert(sym.as_str().to_string());
                }
                let new_body = self.substitute_inner(*body, var, replacement, &new_bound);
                if new_body == *body {
                    root // unchanged -- share
                } else {
                    let bindings = bindings.clone();
                    match &node {
                        FormulaNode::Forall(..) => {
                            self.push(FormulaNode::Forall(bindings, new_body))
                        }
                        FormulaNode::Exists(..) => {
                            self.push(FormulaNode::Exists(bindings, new_body))
                        }
                        _ => unreachable!(
                            "quantifier reconstruction only runs for FormulaNode::Forall/Exists"
                        ),
                    }
                }
            }

            // Leaves that don't match the variable: return unchanged
            FormulaNode::Bool(_)
            | FormulaNode::Int(_)
            | FormulaNode::UInt(_)
            | FormulaNode::BitVec { .. }
            | FormulaNode::Var(..) => root,

            // Recurse through children, preserve sharing when unchanged
            _ => {
                let children = self.children(root);
                let new_children: Vec<FormulaRef> = children
                    .iter()
                    .map(|c| self.substitute_inner(*c, var, replacement, bound))
                    .collect();
                if new_children == children {
                    root // nothing changed -- share
                } else {
                    self.rebuild_with_children(root, &new_children)
                }
            }
        }
    }

    /// Substitute multiple variables simultaneously.
    ///
    /// All substitutions use the original formula values (not intermediate
    /// results), so order does not matter. Respects quantifier shadowing.
    pub fn substitute_all(
        &mut self,
        root: FormulaRef,
        mapping: &FxHashMap<String, FormulaRef>,
    ) -> FormulaRef {
        self.substitute_all_inner(root, mapping, &FxHashSet::default())
    }

    fn substitute_all_inner(
        &mut self,
        root: FormulaRef,
        mapping: &FxHashMap<String, FormulaRef>,
        bound: &FxHashSet<String>,
    ) -> FormulaRef {
        let node = self.get(root).clone();
        match &node {
            FormulaNode::Var(name, _) if !bound.contains(name) => {
                if let Some(&replacement) = mapping.get(name) {
                    return replacement;
                }
                root
            }

            // Quantifier bindings use Symbol; convert to String for tracking.
            FormulaNode::Forall(bindings, body) | FormulaNode::Exists(bindings, body) => {
                let mut new_bound = bound.clone();
                for (sym, _) in bindings {
                    new_bound.insert(sym.as_str().to_string());
                }
                let new_body = self.substitute_all_inner(*body, mapping, &new_bound);
                if new_body == *body {
                    root
                } else {
                    let bindings = bindings.clone();
                    match &node {
                        FormulaNode::Forall(..) => {
                            self.push(FormulaNode::Forall(bindings, new_body))
                        }
                        FormulaNode::Exists(..) => {
                            self.push(FormulaNode::Exists(bindings, new_body))
                        }
                        _ => unreachable!(
                            "quantifier reconstruction only runs for FormulaNode::Forall/Exists"
                        ),
                    }
                }
            }

            FormulaNode::Bool(_)
            | FormulaNode::Int(_)
            | FormulaNode::UInt(_)
            | FormulaNode::BitVec { .. }
            | FormulaNode::Var(..) => root,

            _ => {
                let children = self.children(root);
                let new_children: Vec<FormulaRef> = children
                    .iter()
                    .map(|c| self.substitute_all_inner(*c, mapping, bound))
                    .collect();
                if new_children == children {
                    root
                } else {
                    self.rebuild_with_children(root, &new_children)
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Map: arena-native bottom-up transform
    // -----------------------------------------------------------------------

    /// Bottom-up map: transform children first, then apply `f` to the result.
    ///
    /// The closure receives the arena and a `FormulaRef` whose children have
    /// already been mapped, and returns the new `FormulaRef`.
    pub fn map(
        &mut self,
        root: FormulaRef,
        f: &mut impl FnMut(&mut FormulaArena, FormulaRef) -> FormulaRef,
    ) -> FormulaRef {
        let mapped = self.map_children(root, f);
        f(self, mapped)
    }

    /// Map only the direct children of `root`, then rebuild the node.
    ///
    /// Does not recurse into grandchildren. For full bottom-up recursion,
    /// use [`Self::map`].
    pub fn map_children(
        &mut self,
        root: FormulaRef,
        f: &mut impl FnMut(&mut FormulaArena, FormulaRef) -> FormulaRef,
    ) -> FormulaRef {
        let node = self.get(root).clone();
        match &node {
            // Leaves have no children to map
            FormulaNode::Bool(_)
            | FormulaNode::Int(_)
            | FormulaNode::UInt(_)
            | FormulaNode::BitVec { .. }
            | FormulaNode::Var(..) => root,

            // Quantifiers: recurse into body only
            FormulaNode::Forall(bindings, body) => {
                let new_body = self.map(*body, f);
                if new_body == *body {
                    root
                } else {
                    let bindings = bindings.clone();
                    self.push(FormulaNode::Forall(bindings, new_body))
                }
            }
            FormulaNode::Exists(bindings, body) => {
                let new_body = self.map(*body, f);
                if new_body == *body {
                    root
                } else {
                    let bindings = bindings.clone();
                    self.push(FormulaNode::Exists(bindings, new_body))
                }
            }

            // All other nodes: map children then rebuild
            _ => {
                let children = self.children(root);
                let new_children: Vec<FormulaRef> =
                    children.iter().map(|c| self.map(*c, f)).collect();
                if new_children == children {
                    root
                } else {
                    self.rebuild_with_children(root, &new_children)
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Rebuild: construct a new node with the same variant but new children
    // -----------------------------------------------------------------------

    /// Rebuild a node with new children, preserving variant and metadata.
    ///
    /// The `new_children` slice must have the same length as `self.children(original)`.
    pub(crate) fn rebuild_with_children(
        &mut self,
        original: FormulaRef,
        new_children: &[FormulaRef],
    ) -> FormulaRef {
        let node = self.get(original).clone();
        match node {
            // Leaves: no children, return as-is. `Opaque` stores its sub-tree
            // boxed (not as arena children), so it has no children to rebuild.
            FormulaNode::Bool(_)
            | FormulaNode::Int(_)
            | FormulaNode::UInt(_)
            | FormulaNode::BitVec { .. }
            | FormulaNode::Var(..)
            | FormulaNode::Opaque(_) => original,

            // Unary
            FormulaNode::Not(_) => self.push(FormulaNode::Not(new_children[0])),
            FormulaNode::Neg(_) => self.push(FormulaNode::Neg(new_children[0])),
            FormulaNode::BvNot(_, w) => self.push(FormulaNode::BvNot(new_children[0], w)),
            FormulaNode::BvToInt(_, w, s) => self.push(FormulaNode::BvToInt(new_children[0], w, s)),
            FormulaNode::IntToBv(_, w) => self.push(FormulaNode::IntToBv(new_children[0], w)),
            FormulaNode::BvZeroExt(_, bits) => {
                self.push(FormulaNode::BvZeroExt(new_children[0], bits))
            }
            FormulaNode::BvSignExt(_, bits) => {
                self.push(FormulaNode::BvSignExt(new_children[0], bits))
            }
            FormulaNode::BvExtract { high, low, .. } => {
                self.push(FormulaNode::BvExtract { inner: new_children[0], high, low })
            }

            // N-ary (use push_nary for hash-consing)
            FormulaNode::And(..) => self.push_nary(new_children, true),
            FormulaNode::Or(..) => self.push_nary(new_children, false),

            // Binary
            FormulaNode::Implies(..) => {
                self.push(FormulaNode::Implies(new_children[0], new_children[1]))
            }
            FormulaNode::Eq(..) => self.push(FormulaNode::Eq(new_children[0], new_children[1])),
            FormulaNode::Lt(..) => self.push(FormulaNode::Lt(new_children[0], new_children[1])),
            FormulaNode::Le(..) => self.push(FormulaNode::Le(new_children[0], new_children[1])),
            FormulaNode::Gt(..) => self.push(FormulaNode::Gt(new_children[0], new_children[1])),
            FormulaNode::Ge(..) => self.push(FormulaNode::Ge(new_children[0], new_children[1])),
            FormulaNode::Add(..) => self.push(FormulaNode::Add(new_children[0], new_children[1])),
            FormulaNode::Sub(..) => self.push(FormulaNode::Sub(new_children[0], new_children[1])),
            FormulaNode::Mul(..) => self.push(FormulaNode::Mul(new_children[0], new_children[1])),
            FormulaNode::Div(..) => self.push(FormulaNode::Div(new_children[0], new_children[1])),
            FormulaNode::Rem(..) => self.push(FormulaNode::Rem(new_children[0], new_children[1])),
            FormulaNode::BvConcat(..) => {
                self.push(FormulaNode::BvConcat(new_children[0], new_children[1]))
            }
            FormulaNode::Select(..) => {
                self.push(FormulaNode::Select(new_children[0], new_children[1]))
            }

            // Binary with width
            FormulaNode::BvAdd(_, _, w) => {
                self.push(FormulaNode::BvAdd(new_children[0], new_children[1], w))
            }
            FormulaNode::BvSub(_, _, w) => {
                self.push(FormulaNode::BvSub(new_children[0], new_children[1], w))
            }
            FormulaNode::BvMul(_, _, w) => {
                self.push(FormulaNode::BvMul(new_children[0], new_children[1], w))
            }
            FormulaNode::BvUDiv(_, _, w) => {
                self.push(FormulaNode::BvUDiv(new_children[0], new_children[1], w))
            }
            FormulaNode::BvSDiv(_, _, w) => {
                self.push(FormulaNode::BvSDiv(new_children[0], new_children[1], w))
            }
            FormulaNode::BvURem(_, _, w) => {
                self.push(FormulaNode::BvURem(new_children[0], new_children[1], w))
            }
            FormulaNode::BvSRem(_, _, w) => {
                self.push(FormulaNode::BvSRem(new_children[0], new_children[1], w))
            }
            FormulaNode::BvAnd(_, _, w) => {
                self.push(FormulaNode::BvAnd(new_children[0], new_children[1], w))
            }
            FormulaNode::BvOr(_, _, w) => {
                self.push(FormulaNode::BvOr(new_children[0], new_children[1], w))
            }
            FormulaNode::BvXor(_, _, w) => {
                self.push(FormulaNode::BvXor(new_children[0], new_children[1], w))
            }
            FormulaNode::BvShl(_, _, w) => {
                self.push(FormulaNode::BvShl(new_children[0], new_children[1], w))
            }
            FormulaNode::BvLShr(_, _, w) => {
                self.push(FormulaNode::BvLShr(new_children[0], new_children[1], w))
            }
            FormulaNode::BvAShr(_, _, w) => {
                self.push(FormulaNode::BvAShr(new_children[0], new_children[1], w))
            }
            FormulaNode::BvULt(_, _, w) => {
                self.push(FormulaNode::BvULt(new_children[0], new_children[1], w))
            }
            FormulaNode::BvULe(_, _, w) => {
                self.push(FormulaNode::BvULe(new_children[0], new_children[1], w))
            }
            FormulaNode::BvSLt(_, _, w) => {
                self.push(FormulaNode::BvSLt(new_children[0], new_children[1], w))
            }
            FormulaNode::BvSLe(_, _, w) => {
                self.push(FormulaNode::BvSLe(new_children[0], new_children[1], w))
            }

            // Ternary
            FormulaNode::Ite(..) => {
                self.push(FormulaNode::Ite(new_children[0], new_children[1], new_children[2]))
            }
            FormulaNode::Store(..) => {
                self.push(FormulaNode::Store(new_children[0], new_children[1], new_children[2]))
            }

            // Quantifiers
            FormulaNode::Forall(bindings, _) => {
                self.push(FormulaNode::Forall(bindings, new_children[0]))
            }
            FormulaNode::Exists(bindings, _) => {
                self.push(FormulaNode::Exists(bindings, new_children[0]))
            }
            // Uninterpreted predicate: the new children are the new arg refs.
            FormulaNode::Pred(name, _) => self.push(FormulaNode::Pred(name, new_children.to_vec())),
        }
    }
}
