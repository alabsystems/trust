// trust-types/formula_arena/arena.rs: FormulaArena struct and core operations
//
// Intern (Formula -> FormulaRef), reconstruct (FormulaRef -> Formula),
// children, visit, size, depth, and to_smtlib.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::formula::Formula;
use crate::fx::FxHashMap;

use super::types::{FormulaNode, FormulaRef};

/// Hash-consing key for N-ary nodes (And/Or).
///
/// And/Or nodes store `(start, count)` indices into the arena's refs vec,
/// which are arena-internal and differ for structurally identical nodes.
/// This key captures the variant tag and actual child FormulaRefs so that
/// identical And/Or expressions hash-cons correctly.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum NaryKey {
    And(Vec<FormulaRef>),
    Or(Vec<FormulaRef>),
}

/// Arena-allocated formula storage. All nodes in a formula tree live in
/// contiguous memory, addressed by `FormulaRef` indices.
///
/// # Usage
///
/// ```
/// use trust_types::{Formula, Sort};
/// use trust_types::formula_arena::FormulaArena;
///
/// let f = Formula::Add(
///     Box::new(Formula::Var("x".into(), Sort::Int)),
///     Box::new(Formula::Int(1)),
/// );
///
/// let mut arena = FormulaArena::new();
/// let root = arena.intern(&f);
///
/// // Convert back to owned Formula
/// let roundtrip = arena.to_formula(root);
/// assert_eq!(roundtrip, f);
/// ```
/// Hash-consing deduplication metrics.
#[derive(Debug, Clone, Default)]
pub struct HashConsMetrics {
    /// Number of times a node was found in the dedup table (avoided allocation).
    pub hits: u64,
    /// Number of times a node was NOT in the table (new allocation).
    pub misses: u64,
}

impl HashConsMetrics {
    /// Total lookup attempts (hits + misses).
    #[must_use]
    pub fn total(&self) -> u64 {
        self.hits + self.misses
    }

    /// Hit rate as a fraction in [0.0, 1.0]. Returns 0.0 if no lookups.
    #[must_use]
    pub fn hit_rate(&self) -> f64 {
        let total = self.total();
        if total == 0 { 0.0 } else { self.hits as f64 / total as f64 }
    }
}

#[derive(Debug, Clone)]
pub struct FormulaArena {
    /// All formula nodes, indexed by `FormulaRef`.
    pub(crate) nodes: Vec<FormulaNode>,
    /// Flat storage for N-ary children (And/Or operands).
    /// `FormulaNode::And(start, count)` indexes into this vec.
    pub(crate) refs: Vec<FormulaRef>,

    // -- Hash-consing tables --
    /// Dedup table for non-N-ary nodes. Keyed by the `FormulaNode` itself
    /// (which includes `FormulaRef` children that have identity semantics).
    dedup: FxHashMap<FormulaNode, FormulaRef>,
    /// Dedup table for N-ary nodes (And/Or), keyed by actual children
    /// since the `(start, count)` indices are arena-internal.
    nary_dedup: FxHashMap<NaryKey, FormulaRef>,
    /// Deduplication hit/miss counters.
    metrics: HashConsMetrics,
}

impl FormulaArena {
    /// Create an empty arena.
    #[must_use]
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            refs: Vec::new(),
            dedup: FxHashMap::default(),
            nary_dedup: FxHashMap::default(),
            metrics: HashConsMetrics::default(),
        }
    }

    /// Create an arena with pre-allocated capacity for `node_cap` nodes
    /// and `ref_cap` N-ary children references.
    #[must_use]
    pub fn with_capacity(node_cap: usize, ref_cap: usize) -> Self {
        Self {
            nodes: Vec::with_capacity(node_cap),
            refs: Vec::with_capacity(ref_cap),
            dedup: FxHashMap::with_capacity_and_hasher(node_cap, Default::default()),
            nary_dedup: FxHashMap::default(),
            metrics: HashConsMetrics::default(),
        }
    }

    /// Number of nodes in the arena.
    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the arena is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Access hash-consing deduplication metrics.
    #[must_use]
    pub fn metrics(&self) -> &HashConsMetrics {
        &self.metrics
    }

    /// Push a non-N-ary node with hash-consing deduplication.
    ///
    /// If an identical node already exists, returns the existing `FormulaRef`
    /// without allocating. This is the primary allocation entry point for all
    /// node types except And/Or (which use `push_nary`).
    pub(crate) fn push(&mut self, node: FormulaNode) -> FormulaRef {
        debug_assert!(
            !matches!(node, FormulaNode::And(_, _) | FormulaNode::Or(_, _)),
            "And/Or nodes must use push_nary for correct hash-consing"
        );
        if let Some(&existing) = self.dedup.get(&node) {
            self.metrics.hits += 1;
            return existing;
        }
        self.metrics.misses += 1;
        let idx = self.nodes.len();
        assert!(idx <= u32::MAX as usize, "FormulaArena: too many nodes (>4B)");
        let r = FormulaRef(idx as u32);
        self.dedup.insert(node.clone(), r);
        self.nodes.push(node);
        r
    }

    /// Push an N-ary node (And/Or) with hash-consing deduplication.
    ///
    /// And/Or nodes store children as `(start, count)` indices into the refs
    /// vec, which differ for structurally identical nodes. This method deduplicates
    /// by the actual child `FormulaRef` list.
    pub(crate) fn push_nary(&mut self, children: &[FormulaRef], is_and: bool) -> FormulaRef {
        let key =
            if is_and { NaryKey::And(children.to_vec()) } else { NaryKey::Or(children.to_vec()) };
        if let Some(&existing) = self.nary_dedup.get(&key) {
            self.metrics.hits += 1;
            return existing;
        }
        self.metrics.misses += 1;
        let start = self.refs.len();
        assert!(start <= u32::MAX as usize, "FormulaArena: too many refs");
        self.refs.extend_from_slice(children);
        let node = if is_and {
            FormulaNode::And(start as u32, children.len() as u32)
        } else {
            FormulaNode::Or(start as u32, children.len() as u32)
        };
        let idx = self.nodes.len();
        assert!(idx <= u32::MAX as usize, "FormulaArena: too many nodes (>4B)");
        let r = FormulaRef(idx as u32);
        self.nary_dedup.insert(key, r);
        self.nodes.push(node);
        r
    }

    /// Look up a node by reference.
    #[must_use]
    pub fn get(&self, r: FormulaRef) -> &FormulaNode {
        &self.nodes[r.index()]
    }

    /// Get the N-ary children slice for an `And`/`Or` node.
    #[must_use]
    pub fn get_refs(&self, start: u32, count: u32) -> &[FormulaRef] {
        let s = start as usize;
        let c = count as usize;
        &self.refs[s..s + c]
    }

    // -----------------------------------------------------------------------
    // Intern: Formula -> FormulaRef (recursive tree walk)
    // -----------------------------------------------------------------------

    /// Intern a `Formula` tree into this arena, returning the root `FormulaRef`.
    ///
    /// This recursively walks the formula tree and allocates all nodes in the
    /// arena. Each `Box<Formula>` child becomes a `FormulaRef` index.
    pub fn intern(&mut self, formula: &Formula) -> FormulaRef {
        match formula {
            // Leaves
            Formula::Bool(v) => self.push(FormulaNode::Bool(*v)),
            Formula::Int(v) => self.push(FormulaNode::Int(*v)),
            Formula::UInt(v) => self.push(FormulaNode::UInt(*v)),
            Formula::BitVec { value, width } => {
                self.push(FormulaNode::BitVec { value: *value, width: *width })
            }
            Formula::Var(name, sort) => self.push(FormulaNode::Var(name.clone(), sort.clone())),
            // SymVar resolves symbol to string for arena interning.
            Formula::SymVar(sym, sort) => {
                self.push(FormulaNode::Var(sym.as_str().to_string(), sort.clone()))
            }

            // Unary
            Formula::Not(a) => {
                let a = self.intern(a);
                self.push(FormulaNode::Not(a))
            }
            Formula::Neg(a) => {
                let a = self.intern(a);
                self.push(FormulaNode::Neg(a))
            }
            Formula::BvNot(a, w) => {
                let a = self.intern(a);
                self.push(FormulaNode::BvNot(a, *w))
            }
            Formula::BvToInt(a, w, s) => {
                let a = self.intern(a);
                self.push(FormulaNode::BvToInt(a, *w, *s))
            }
            Formula::IntToBv(a, w) => {
                let a = self.intern(a);
                self.push(FormulaNode::IntToBv(a, *w))
            }
            Formula::BvZeroExt(a, bits) => {
                let a = self.intern(a);
                self.push(FormulaNode::BvZeroExt(a, *bits))
            }
            Formula::BvSignExt(a, bits) => {
                let a = self.intern(a);
                self.push(FormulaNode::BvSignExt(a, *bits))
            }
            Formula::BvExtract { inner, high, low } => {
                let inner = self.intern(inner);
                self.push(FormulaNode::BvExtract { inner, high: *high, low: *low })
            }

            // N-ary (use push_nary for hash-consing)
            Formula::And(terms) => {
                let child_refs: Vec<FormulaRef> = terms.iter().map(|t| self.intern(t)).collect();
                self.push_nary(&child_refs, true)
            }
            Formula::Or(terms) => {
                let child_refs: Vec<FormulaRef> = terms.iter().map(|t| self.intern(t)).collect();
                self.push_nary(&child_refs, false)
            }

            // Binary
            Formula::Implies(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Implies(a, b))
            }
            Formula::Eq(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Eq(a, b))
            }
            Formula::Lt(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Lt(a, b))
            }
            Formula::Le(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Le(a, b))
            }
            Formula::Gt(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Gt(a, b))
            }
            Formula::Ge(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Ge(a, b))
            }
            Formula::Add(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Add(a, b))
            }
            Formula::Sub(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Sub(a, b))
            }
            Formula::Mul(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Mul(a, b))
            }
            Formula::Div(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Div(a, b))
            }
            Formula::Rem(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Rem(a, b))
            }
            Formula::BvConcat(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvConcat(a, b))
            }
            Formula::Select(a, b) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::Select(a, b))
            }

            // Binary with width
            Formula::BvAdd(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvAdd(a, b, *w))
            }
            Formula::BvSub(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvSub(a, b, *w))
            }
            Formula::BvMul(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvMul(a, b, *w))
            }
            Formula::BvUDiv(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvUDiv(a, b, *w))
            }
            Formula::BvSDiv(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvSDiv(a, b, *w))
            }
            Formula::BvURem(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvURem(a, b, *w))
            }
            Formula::BvSRem(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvSRem(a, b, *w))
            }
            Formula::BvAnd(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvAnd(a, b, *w))
            }
            Formula::BvOr(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvOr(a, b, *w))
            }
            Formula::BvXor(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvXor(a, b, *w))
            }
            Formula::BvShl(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvShl(a, b, *w))
            }
            Formula::BvLShr(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvLShr(a, b, *w))
            }
            Formula::BvAShr(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvAShr(a, b, *w))
            }
            Formula::BvULt(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvULt(a, b, *w))
            }
            Formula::BvULe(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvULe(a, b, *w))
            }
            Formula::BvSLt(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvSLt(a, b, *w))
            }
            Formula::BvSLe(a, b, w) => {
                let a = self.intern(a);
                let b = self.intern(b);
                self.push(FormulaNode::BvSLe(a, b, *w))
            }
            // BvBinary/BvCompare unified variants not yet in Formula

            // Ternary
            Formula::Ite(a, b, c) => {
                let a = self.intern(a);
                let b = self.intern(b);
                let c = self.intern(c);
                self.push(FormulaNode::Ite(a, b, c))
            }
            Formula::Store(a, b, c) => {
                let a = self.intern(a);
                let b = self.intern(b);
                let c = self.intern(c);
                self.push(FormulaNode::Store(a, b, c))
            }

            // Quantifiers
            Formula::Forall(bindings, body) => {
                let body = self.intern(body);
                self.push(FormulaNode::Forall(bindings.clone(), body))
            }
            Formula::Exists(bindings, body) => {
                let body = self.intern(body);
                self.push(FormulaNode::Exists(bindings.clone(), body))
            }

            // Uninterpreted predicate: intern each argument term.
            Formula::Pred(name, args) => {
                let arg_refs: Vec<FormulaRef> = args.iter().map(|a| self.intern(a)).collect();
                self.push(FormulaNode::Pred(*name, arg_refs))
            }
            // The IEEE-754 floating-point family is not (yet) structurally
            // interned; store it losslessly as an opaque boxed sub-tree that
            // round-trips verbatim through `to_formula`. (`Formula` is
            // #[non_exhaustive] from trust-ir-contract; any genuinely-future
            // variant also lands here and round-trips rather than panicking.)
            other => self.push(FormulaNode::Opaque(Box::new(other.clone()))),
        }
    }

    // -----------------------------------------------------------------------
    // To Formula: FormulaRef -> owned Formula (recursive reconstruction)
    // -----------------------------------------------------------------------

    /// Convert an arena-allocated formula back to an owned `Formula` tree.
    ///
    /// This reconstructs the `Box<Formula>` representation from arena indices.
    #[must_use]
    pub fn to_formula(&self, r: FormulaRef) -> Formula {
        match self.get(r) {
            // Leaves
            FormulaNode::Bool(v) => Formula::Bool(*v),
            FormulaNode::Int(v) => Formula::Int(*v),
            FormulaNode::UInt(v) => Formula::UInt(*v),
            FormulaNode::BitVec { value, width } => {
                Formula::BitVec { value: *value, width: *width }
            }
            FormulaNode::Var(name, sort) => Formula::Var(name.clone(), sort.clone()),

            // Unary
            FormulaNode::Not(a) => Formula::Not(Box::new(self.to_formula(*a))),
            FormulaNode::Neg(a) => Formula::Neg(Box::new(self.to_formula(*a))),
            FormulaNode::BvNot(a, w) => Formula::BvNot(Box::new(self.to_formula(*a)), *w),
            FormulaNode::BvToInt(a, w, s) => {
                Formula::BvToInt(Box::new(self.to_formula(*a)), *w, *s)
            }
            FormulaNode::IntToBv(a, w) => Formula::IntToBv(Box::new(self.to_formula(*a)), *w),
            FormulaNode::BvZeroExt(a, bits) => {
                Formula::BvZeroExt(Box::new(self.to_formula(*a)), *bits)
            }
            FormulaNode::BvSignExt(a, bits) => {
                Formula::BvSignExt(Box::new(self.to_formula(*a)), *bits)
            }
            FormulaNode::BvExtract { inner, high, low } => Formula::BvExtract {
                inner: Box::new(self.to_formula(*inner)),
                high: *high,
                low: *low,
            },

            // N-ary
            FormulaNode::And(start, count) => {
                let terms: Vec<Formula> =
                    self.get_refs(*start, *count).iter().map(|r| self.to_formula(*r)).collect();
                Formula::And(terms)
            }
            FormulaNode::Or(start, count) => {
                let terms: Vec<Formula> =
                    self.get_refs(*start, *count).iter().map(|r| self.to_formula(*r)).collect();
                Formula::Or(terms)
            }

            // Binary
            FormulaNode::Implies(a, b) => {
                Formula::Implies(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::Eq(a, b) => {
                Formula::Eq(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::Lt(a, b) => {
                Formula::Lt(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::Le(a, b) => {
                Formula::Le(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::Gt(a, b) => {
                Formula::Gt(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::Ge(a, b) => {
                Formula::Ge(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::Add(a, b) => {
                Formula::Add(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::Sub(a, b) => {
                Formula::Sub(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::Mul(a, b) => {
                Formula::Mul(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::Div(a, b) => {
                Formula::Div(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::Rem(a, b) => {
                Formula::Rem(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::BvConcat(a, b) => {
                Formula::BvConcat(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }
            FormulaNode::Select(a, b) => {
                Formula::Select(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)))
            }

            // Binary with width
            FormulaNode::BvAdd(a, b, w) => {
                Formula::BvAdd(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvSub(a, b, w) => {
                Formula::BvSub(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvMul(a, b, w) => {
                Formula::BvMul(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvUDiv(a, b, w) => {
                Formula::BvUDiv(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvSDiv(a, b, w) => {
                Formula::BvSDiv(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvURem(a, b, w) => {
                Formula::BvURem(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvSRem(a, b, w) => {
                Formula::BvSRem(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvAnd(a, b, w) => {
                Formula::BvAnd(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvOr(a, b, w) => {
                Formula::BvOr(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvXor(a, b, w) => {
                Formula::BvXor(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvShl(a, b, w) => {
                Formula::BvShl(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvLShr(a, b, w) => {
                Formula::BvLShr(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvAShr(a, b, w) => {
                Formula::BvAShr(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvULt(a, b, w) => {
                Formula::BvULt(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvULe(a, b, w) => {
                Formula::BvULe(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvSLt(a, b, w) => {
                Formula::BvSLt(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }
            FormulaNode::BvSLe(a, b, w) => {
                Formula::BvSLe(Box::new(self.to_formula(*a)), Box::new(self.to_formula(*b)), *w)
            }

            // Ternary
            FormulaNode::Ite(a, b, c) => Formula::Ite(
                Box::new(self.to_formula(*a)),
                Box::new(self.to_formula(*b)),
                Box::new(self.to_formula(*c)),
            ),
            FormulaNode::Store(a, b, c) => Formula::Store(
                Box::new(self.to_formula(*a)),
                Box::new(self.to_formula(*b)),
                Box::new(self.to_formula(*c)),
            ),

            // Quantifiers
            FormulaNode::Forall(bindings, body) => {
                Formula::Forall(bindings.clone(), Box::new(self.to_formula(*body)))
            }
            FormulaNode::Exists(bindings, body) => {
                Formula::Exists(bindings.clone(), Box::new(self.to_formula(*body)))
            }
            FormulaNode::Pred(name, args) => {
                Formula::Pred(*name, args.iter().map(|a| self.to_formula(*a)).collect())
            }
            // Opaque escape: the original sub-tree was stored verbatim.
            FormulaNode::Opaque(f) => (**f).clone(),
        }
    }

    // -----------------------------------------------------------------------
    // Arena-native operations (avoid converting back to Formula)
    // -----------------------------------------------------------------------

    /// Collect direct child references of a node.
    #[must_use]
    pub fn children(&self, r: FormulaRef) -> Vec<FormulaRef> {
        match self.get(r) {
            // Leaves
            FormulaNode::Bool(_)
            | FormulaNode::Int(_)
            | FormulaNode::UInt(_)
            | FormulaNode::BitVec { .. }
            | FormulaNode::Var(..) => vec![],

            // Unary
            FormulaNode::Not(a)
            | FormulaNode::Neg(a)
            | FormulaNode::BvNot(a, _)
            | FormulaNode::BvToInt(a, _, _)
            | FormulaNode::IntToBv(a, _)
            | FormulaNode::BvZeroExt(a, _)
            | FormulaNode::BvSignExt(a, _) => vec![*a],
            FormulaNode::BvExtract { inner, .. } => vec![*inner],

            // N-ary
            FormulaNode::And(start, count) | FormulaNode::Or(start, count) => {
                self.get_refs(*start, *count).to_vec()
            }

            // Binary
            FormulaNode::Implies(a, b)
            | FormulaNode::Eq(a, b)
            | FormulaNode::Lt(a, b)
            | FormulaNode::Le(a, b)
            | FormulaNode::Gt(a, b)
            | FormulaNode::Ge(a, b)
            | FormulaNode::Add(a, b)
            | FormulaNode::Sub(a, b)
            | FormulaNode::Mul(a, b)
            | FormulaNode::Div(a, b)
            | FormulaNode::Rem(a, b)
            | FormulaNode::BvConcat(a, b)
            | FormulaNode::Select(a, b) => vec![*a, *b],

            // Binary with width
            FormulaNode::BvAdd(a, b, _)
            | FormulaNode::BvSub(a, b, _)
            | FormulaNode::BvMul(a, b, _)
            | FormulaNode::BvUDiv(a, b, _)
            | FormulaNode::BvSDiv(a, b, _)
            | FormulaNode::BvURem(a, b, _)
            | FormulaNode::BvSRem(a, b, _)
            | FormulaNode::BvAnd(a, b, _)
            | FormulaNode::BvOr(a, b, _)
            | FormulaNode::BvXor(a, b, _)
            | FormulaNode::BvShl(a, b, _)
            | FormulaNode::BvLShr(a, b, _)
            | FormulaNode::BvAShr(a, b, _)
            | FormulaNode::BvULt(a, b, _)
            | FormulaNode::BvULe(a, b, _)
            | FormulaNode::BvSLt(a, b, _)
            | FormulaNode::BvSLe(a, b, _) => vec![*a, *b],

            // Ternary
            FormulaNode::Ite(a, b, c) | FormulaNode::Store(a, b, c) => {
                vec![*a, *b, *c]
            }

            // Quantifiers
            FormulaNode::Forall(_, body) | FormulaNode::Exists(_, body) => vec![*body],

            // Uninterpreted predicate: argument terms are the children.
            FormulaNode::Pred(_, args) => args.clone(),

            // Opaque escape stores its sub-tree boxed, not as arena children.
            FormulaNode::Opaque(_) => vec![],
        }
    }

    /// Visit all nodes depth-first, pre-order.
    pub fn visit(&self, root: FormulaRef, f: &mut impl FnMut(FormulaRef, &FormulaNode)) {
        f(root, self.get(root));
        for child in self.children(root) {
            self.visit(child, f);
        }
    }

    /// Count total nodes reachable from `root`.
    #[must_use]
    pub fn size(&self, root: FormulaRef) -> usize {
        let mut count = 0;
        self.visit(root, &mut |_, _| count += 1);
        count
    }

    /// Maximum depth of the formula tree from `root`.
    #[must_use]
    pub fn depth(&self, root: FormulaRef) -> usize {
        let children = self.children(root);
        if children.is_empty() {
            0
        } else {
            1 + children.iter().map(|c| self.depth(*c)).max().unwrap_or(0)
        }
    }

    /// Convert an arena-allocated formula to SMT-LIB2 text without
    /// reconstructing the `Formula` tree.
    #[must_use]
    pub fn to_smtlib(&self, r: FormulaRef) -> String {
        // Delegate to the owned Formula's to_smtlib for correctness.
        // A fully arena-native SMT-LIB printer can be added later for
        // maximum performance, but the conversion cost is minimal compared
        // to solver invocation.
        self.to_formula(r).to_smtlib()
    }
}

impl Default for FormulaArena {
    fn default() -> Self {
        Self::new()
    }
}
