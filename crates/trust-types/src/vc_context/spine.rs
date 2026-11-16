//! Block-def recipes ([`Spine`]), the sequences they are made of, and the relevance rule
//! that decides which candidate facts a spine keeps (D-VC-3, L4-SPINE-ID-1).
//!
//! # The relevance rule
//!
//! [`RelevanceRule::BlockDefs`] is the rule of trust-vcgen's
//! `combine_relevant_block_defs_recorded` (`generate/block_defs.rs`), read as a closure
//! over this context:
//!
//! 1. `needed` is the relevance names of the body;
//! 2. the candidates are walked LAST FIRST: a candidate whose relevance names meet
//!    `needed` is kept, and all of its names join `needed`;
//! 3. the kept candidates, in their original order, are the kept list. No candidates, or
//!    none kept, is the empty kept list, and the spine's formula is then its body.
//!
//! A formula's names are those vcgen's `collect_formula_var_names` collects, walked here
//! over DAG nodes: a `Var` leaf's name; the union of the children's names for the
//! operators that function descends into; a quantifier's body names minus the names it
//! binds; and NOTHING for every other node (a `SymVar`, `Pred`, `Ctor`, `Sel`, `IsCtor`,
//! `FnApp`, `Rat`, and the float conversions it does not descend into), exactly as that
//! function's wildcard arm. A name's relevance name is the per-function data vcgen
//! supplies ([`RelevanceVars`], the collapse its `relevance_var_name` computes); a name it
//! does not list is its own. trust-vcgen's tests pin both halves against its own
//! functions.
//!
//! # The walk and its cache (D-VC-6)
//!
//! A formula's names are collected by one walk of the DAG under it, which visits each node
//! once (a quantifier's body is walked on its own, since its bound names leave only its own
//! set): linear in the formula's distinct nodes, as vcgen's walk is in its tree. The context
//! caches the names of every node a walk started at (a spine's candidates and body) or met
//! as a quantifier, and each spine's kept list; a formula's names do not depend on the
//! relevance names, a kept list does, so [`VcContext::vars_mut`] forgets the kept lists.
//! The work is counted ([`super::ContextStats::relevance`]).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::sync::{Arc, Mutex, MutexGuard, OnceLock, PoisonError};

use trust_ir_contract::formula_dag::{FormulaDag, NodeId};

use super::{SeqId, SpineId, VcContext, VcContextError};
use crate::fx::{FxHashMap, FxHashSet};
use crate::{Formula, Sort, Symbol};

/// The closure rule a spine's kept list is computed by (module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum RelevanceRule {
    /// trust-vcgen's block-def relevance closure.
    BlockDefs,
}

/// A block-def recipe: the candidate facts of a block, the row's body, and the rule that
/// keeps the relevant candidates. Hash-consed per context by all three; its root is never
/// interned.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Spine {
    /// The block's candidate facts, in order.
    pub candidates: SeqId,
    /// The row's body.
    pub body: NodeId,
    /// The relevance rule.
    pub rule: RelevanceRule,
}

/// The per-function relevance names: a variable name to the name the relevance rule
/// compares it by. A name not listed is its own.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RelevanceVars {
    names: FxHashMap<String, String>,
}

impl RelevanceVars {
    /// Compare `name` as `relevance`.
    pub fn insert(&mut self, name: impl Into<String>, relevance: impl Into<String>) {
        self.names.insert(name.into(), relevance.into());
    }

    /// The name `name` is compared as.
    #[must_use]
    pub fn relevance<'a>(&'a self, name: &'a str) -> &'a str {
        self.names.get(name).map_or(name, String::as_str)
    }

    /// The name `name` is compared as, when it is listed (an entry that maps a name to
    /// itself is listed too): what a supplier reads before it lists a name, so that a
    /// name a spine was already closed under never changes its relevance (trust-vcgen's
    /// row sink, C08).
    #[must_use]
    pub fn listed(&self, name: &str) -> Option<&str> {
        self.names.get(name).map(String::as_str)
    }

    /// The number of listed names.
    #[must_use]
    pub fn len(&self) -> usize {
        self.names.len()
    }

    /// Whether no name is listed.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

/// One cell of a sequence: its last node, the cell before it, and its length.
#[derive(Debug, Clone, Copy)]
struct SeqCell {
    parent: Option<u32>,
    node: NodeId,
    len: u32,
}

/// Persistent, prefix-shared, hash-consed node sequences: a sequence is its last node
/// after the sequence before it, so two sequences with a common prefix share its cells,
/// and an equal sequence is the same [`SeqId`].
#[derive(Debug)]
pub(super) struct SeqStore {
    brand: u64,
    cells: Vec<SeqCell>,
    index: FxHashMap<(Option<u32>, NodeId), u32>,
}

impl SeqStore {
    pub(super) fn new(brand: u64) -> Self {
        SeqStore { brand, cells: Vec::new(), index: FxHashMap::default() }
    }

    fn check(&self, seq: SeqId) -> Result<Option<u32>, VcContextError> {
        let known = seq.brand == self.brand
            && seq.cell.is_none_or(|cell| (cell as usize) < self.cells.len());
        if known { Ok(seq.cell) } else { Err(VcContextError::UnknownSeq(seq)) }
    }

    pub(super) fn validate(&self, seq: SeqId) -> Result<(), VcContextError> {
        self.check(seq).map(|_| ())
    }

    pub(super) fn push(&mut self, seq: SeqId, node: NodeId) -> Result<SeqId, VcContextError> {
        let parent = self.check(seq)?;
        self.push_checked(parent, node)
    }

    pub(super) fn push_checked(
        &mut self,
        parent: Option<u32>,
        node: NodeId,
    ) -> Result<SeqId, VcContextError> {
        if let Some(&cell) = self.index.get(&(parent, node)) {
            return Ok(SeqId { brand: self.brand, cell: Some(cell) });
        }
        let len = parent
            .and_then(|parent| self.cells.get(parent as usize))
            .map_or(1, |cell| cell.len.saturating_add(1));
        let cell = super::next_index(self.cells.len(), "sequence cell")?;
        self.cells.push(SeqCell { parent, node, len });
        self.index.insert((parent, node), cell);
        Ok(SeqId { brand: self.brand, cell: Some(cell) })
    }

    pub(super) fn from_nodes(&mut self, nodes: &[NodeId]) -> Result<SeqId, VcContextError> {
        let mut parent = None;
        for &node in nodes {
            parent = self.push_checked(parent, node)?.cell;
        }
        Ok(SeqId { brand: self.brand, cell: parent })
    }

    pub(super) fn nodes(&self, seq: SeqId) -> Result<Vec<NodeId>, VcContextError> {
        let mut at = self.check(seq)?;
        let cap = at
            .and_then(|cell| self.cells.get(cell as usize))
            .map_or(0, |cell| cell.len as usize);
        let mut nodes = Vec::with_capacity(cap);
        while let Some(cell) = at.and_then(|cell| self.cells.get(cell as usize)) {
            nodes.push(cell.node);
            at = cell.parent;
        }
        nodes.reverse();
        Ok(nodes)
    }

    pub(super) fn cells(&self) -> usize {
        self.cells.len()
    }
}

/// The spines of a context, hash-consed.
#[derive(Debug)]
pub(super) struct SpineStore {
    brand: u64,
    spines: Vec<Spine>,
    index: FxHashMap<Spine, u32>,
}

impl SpineStore {
    pub(super) fn new(brand: u64) -> Self {
        SpineStore { brand, spines: Vec::new(), index: FxHashMap::default() }
    }

    pub(super) fn intern(&mut self, spine: Spine) -> Result<SpineId, VcContextError> {
        if let Some(&index) = self.index.get(&spine) {
            return Ok(SpineId { brand: self.brand, index });
        }
        let index = super::next_index(self.spines.len(), "spine")?;
        self.spines.push(spine);
        self.index.insert(spine, index);
        Ok(SpineId { brand: self.brand, index })
    }

    pub(super) fn get(&self, id: SpineId) -> Result<&Spine, VcContextError> {
        if id.brand != self.brand {
            return Err(VcContextError::UnknownSpine(id));
        }
        self.spines.get(id.index()).ok_or(VcContextError::UnknownSpine(id))
    }

    pub(super) fn len(&self) -> usize {
        self.spines.len()
    }
}

/// How the relevance walk reads one node (module docs).
enum NameClass<'a> {
    /// A variable leaf.
    Var(&'a str),
    /// The union of the children's names.
    Descend,
    /// The body's names minus these.
    Binder(&'a [(Symbol, Sort)]),
    /// No name, and no descent.
    Opaque,
}

/// The class of a node, by its operator, exactly as trust-vcgen's
/// `collect_formula_var_names` matches it.
fn name_class(node: &Formula) -> NameClass<'_> {
    match node {
        Formula::Var(name, _) => NameClass::Var(name.as_str()),
        Formula::Not(_)
        | Formula::Neg(_)
        | Formula::BvNot(..)
        | Formula::BvToInt(..)
        | Formula::IntToBv(..)
        | Formula::BvZeroExt(..)
        | Formula::BvSignExt(..)
        | Formula::BvExtract { .. }
        | Formula::And(_)
        | Formula::Or(_)
        | Formula::Implies(..)
        | Formula::Eq(..)
        | Formula::Lt(..)
        | Formula::Le(..)
        | Formula::Gt(..)
        | Formula::Ge(..)
        | Formula::Add(..)
        | Formula::Sub(..)
        | Formula::Mul(..)
        | Formula::Div(..)
        | Formula::Rem(..)
        | Formula::Select(..)
        | Formula::BvConcat(..)
        | Formula::BvAdd(..)
        | Formula::BvSub(..)
        | Formula::BvMul(..)
        | Formula::BvUDiv(..)
        | Formula::BvSDiv(..)
        | Formula::BvURem(..)
        | Formula::BvSRem(..)
        | Formula::BvAnd(..)
        | Formula::BvOr(..)
        | Formula::BvXor(..)
        | Formula::BvShl(..)
        | Formula::BvLShr(..)
        | Formula::BvAShr(..)
        | Formula::BvULt(..)
        | Formula::BvULe(..)
        | Formula::BvSLt(..)
        | Formula::BvSLe(..)
        | Formula::Ite(..)
        | Formula::Store(..)
        | Formula::FpNeg(_)
        | Formula::FpAbs(_)
        | Formula::FpIsNaN(_)
        | Formula::FpIsInfinite(_)
        | Formula::FpIsZero(_)
        | Formula::FpIsNormal(_)
        | Formula::FpIsSubnormal(_)
        | Formula::FpIsNegative(_)
        | Formula::FpIsPositive(_)
        | Formula::FpFromBits { .. }
        | Formula::FpRem(..)
        | Formula::FpMin(..)
        | Formula::FpMax(..)
        | Formula::FpEq(..)
        | Formula::FpLt(..)
        | Formula::FpLe(..)
        | Formula::FpGt(..)
        | Formula::FpGe(..)
        | Formula::FpSqrt(..)
        | Formula::FpAdd(..)
        | Formula::FpSub(..)
        | Formula::FpMul(..)
        | Formula::FpDiv(..)
        | Formula::FpFma(..)
        | Formula::ConstArray { .. } => NameClass::Descend,
        Formula::Forall(bindings, _) | Formula::Exists(bindings, _) => NameClass::Binder(bindings),
        _ => NameClass::Opaque,
    }
}

/// The names already known: a node's names do not depend on where it is reached from.
type NameCache = FxHashMap<usize, Arc<BTreeSet<String>>>;

/// The relevance walk's cache (module docs).
#[derive(Debug, Default)]
pub(super) struct RelevanceCache {
    state: Mutex<RelevanceState>,
}

#[derive(Debug, Default)]
struct RelevanceState {
    /// The names of each node a walk started at or met as a quantifier, by node index.
    names: NameCache,
    /// Each spine's kept list, under the relevance names as they were when it was computed.
    kept: FxHashMap<Spine, Arc<[NodeId]>>,
}

impl RelevanceCache {
    fn state(&self) -> MutexGuard<'_, RelevanceState> {
        // A poisoned cache still holds correct entries: each is inserted whole.
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Forget every kept list (the relevance names are about to change).
    pub(super) fn forget_kept(&mut self) {
        self.state.get_mut().unwrap_or_else(PoisonError::into_inner).kept.clear();
    }
}

/// One walk in progress: the names collected so far, the nodes visited, and the nodes
/// left; a quantifier's body is walked in a frame of its own.
struct Frame<'a> {
    /// The quantifier this frame walks the body of, and the names it binds; `None` for
    /// the walk's root.
    binder: Option<(NodeId, &'a [(Symbol, Sort)])>,
    names: BTreeSet<String>,
    visited: FxHashSet<usize>,
    pending: Vec<NodeId>,
}

impl<'a> Frame<'a> {
    fn new(binder: Option<(NodeId, &'a [(Symbol, Sort)])>, pending: Vec<NodeId>) -> Self {
        Frame { binder, names: BTreeSet::new(), visited: FxHashSet::default(), pending }
    }
}

/// The names of `root` (module docs), from `cache` or by one walk whose quantifiers and
/// root join it; iterative. `walked` counts the nodes visited and `reached` collects them.
fn names_of(
    dag: &FormulaDag,
    root: NodeId,
    cache: &mut NameCache,
    walked: &mut u64,
    reached: &mut FxHashSet<usize>,
) -> Arc<BTreeSet<String>> {
    if let Some(names) = cache.get(&root.index()) {
        *walked = walked.saturating_add(1);
        return Arc::clone(names);
    }
    let mut frames = vec![Frame::new(None, vec![root])];
    while let Some(frame) = frames.last_mut() {
        let Some(id) = frame.pending.pop() else {
            let Some(done) = frames.pop() else { break };
            let mut names = done.names;
            match done.binder {
                None => {
                    let names = Arc::new(names);
                    cache.insert(root.index(), Arc::clone(&names));
                    return names;
                }
                Some((binder, bindings)) => {
                    for (bound, _) in bindings {
                        names.remove(bound.as_str());
                    }
                    if let Some(outer) = frames.last_mut() {
                        outer.names.extend(names.iter().cloned());
                    }
                    cache.insert(binder.index(), Arc::new(names));
                }
            }
            continue;
        };
        if !dag.contains(id) || !frame.visited.insert(id.index()) {
            continue;
        }
        *walked = walked.saturating_add(1);
        reached.insert(id.index());
        if let Some(known) = cache.get(&id.index()) {
            frame.names.extend(known.iter().cloned());
            continue;
        }
        match name_class(dag.shell(id).payload()) {
            NameClass::Var(name) => {
                frame.names.insert(name.to_string());
            }
            NameClass::Opaque => {}
            NameClass::Descend => frame.pending.extend(dag.kids(id)),
            NameClass::Binder(bindings) => {
                frames.push(Frame::new(Some((id, bindings)), dag.kids(id).collect()));
            }
        }
    }
    Arc::new(BTreeSet::new())
}

impl VcContext {
    /// The names the relevance walk collects for `node` (module docs), before the
    /// relevance names apply: what trust-vcgen's `collect_formula_var_names` collects for
    /// the tree `node` stands for.
    ///
    /// # Errors
    ///
    /// [`VcContextError::UnknownNode`] for a node of another DAG.
    pub fn formula_var_names(&self, node: NodeId) -> Result<BTreeSet<String>, VcContextError> {
        if !self.dag.contains(node) {
            return Err(VcContextError::UnknownNode(node));
        }
        let mut state = self.relevance.state();
        let (mut walked, mut reached) = (0, FxHashSet::default());
        Ok(names_of(&self.dag, node, &mut state.names, &mut walked, &mut reached).as_ref().clone())
    }

    /// The facts `spine` keeps, in order (module docs): computed once per spine and
    /// relevance names, never stored in a row.
    ///
    /// # Errors
    ///
    /// [`VcContextError::UnknownSeq`] or [`VcContextError::UnknownNode`] for a spine whose
    /// ids are not this context's.
    pub fn kept(&self, spine: &Spine) -> Result<Vec<NodeId>, VcContextError> {
        self.kept_arc(spine).map(|kept| kept.to_vec())
    }

    pub(super) fn kept_arc(&self, spine: &Spine) -> Result<Arc<[NodeId]>, VcContextError> {
        static EMPTY_NODES: OnceLock<Arc<[NodeId]>> = OnceLock::new();
        self.seqs.validate(spine.candidates)?;
        if !self.dag.contains(spine.body) {
            return Err(VcContextError::UnknownNode(spine.body));
        }
        if spine.candidates.cell.is_none() {
            return Ok(Arc::clone(EMPTY_NODES.get_or_init(|| Arc::from(&[][..]))));
        }
        let mut state = self.relevance.state();
        if let Some(kept) = state.kept.get(spine) {
            return Ok(Arc::clone(kept));
        }
        let candidates = self.seqs.nodes(spine.candidates)?;
        if candidates.is_empty() {
            return Ok(Arc::clone(EMPTY_NODES.get_or_init(|| Arc::from(&[][..]))));
        }
        let kept = match spine.rule {
            RelevanceRule::BlockDefs => {
                self.block_defs_closure(&mut state.names, &candidates, spine.body)
            }
        };
        let kept: Arc<[NodeId]> = Arc::from(kept);
        state.kept.insert(*spine, Arc::clone(&kept));
        Ok(kept)
    }

    fn block_defs_closure(
        &self,
        cache: &mut NameCache,
        candidates: &[NodeId],
        body: NodeId,
    ) -> Vec<NodeId> {
        let (mut walked, mut reached) = (0u64, FxHashSet::default());
        let mut names_of_root =
            |root: NodeId| names_of(&self.dag, root, cache, &mut walked, &mut reached);
        let body_names = names_of_root(body);
        let candidate_names: Vec<Arc<BTreeSet<String>>> =
            candidates.iter().map(|&candidate| names_of_root(candidate)).collect();
        let mut compared = body_names.len() as u64;
        let mut keep_rev = Vec::new();
        if self.vars.is_empty() {
            let mut needed: FxHashSet<&str> = body_names.iter().map(String::as_str).collect();
            for (&candidate, names) in candidates.iter().zip(&candidate_names).rev() {
                compared = compared.saturating_add(names.len() as u64);
                if names.iter().any(|name| needed.contains(name.as_str())) {
                    needed.extend(names.iter().map(String::as_str));
                    keep_rev.push(candidate);
                }
            }
        } else {
            let mut needed: FxHashSet<&str> =
                body_names.iter().map(|name| self.vars.relevance(name)).collect();
            for (&candidate, names) in candidates.iter().zip(&candidate_names).rev() {
                compared = compared.saturating_add(names.len() as u64);
                if names.iter().any(|name| needed.contains(self.vars.relevance(name))) {
                    needed.extend(names.iter().map(|name| self.vars.relevance(name)));
                    keep_rev.push(candidate);
                }
            }
        }
        keep_rev.reverse();
        let size = (reached.len() + candidates.len() + 1) as u64;
        self.stats.record_relevance(walked.saturating_add(compared), size);
        keep_rev
    }
}
