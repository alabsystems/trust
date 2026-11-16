//! Row identity inside one context (D-VC-5, L4-SPINE-ID-1, design §8): the exact key of a
//! row's formula ([`FormulaKey`]), the row's whole identity ([`RowIdentity`]), its Merkle
//! digest, and its node count (I4).
//!
//! # Exact identity
//!
//! A Node row's formula is its node. A Spine row's is its kept facts followed by its body,
//! computed when asked ([`VcContext::kept`]); with nothing kept it is the body's node, so
//! the empty kept list reproduces the eager rule (the formula IS the body). Two formulas
//! are the same when their keys are: equal nodes, equal lists, or a list equal to the
//! children of an `And` node, found with `FormulaDag::get`, which interns nothing.
//! [`RowIdentity`] adds every other field of the row; two identities are the same only
//! when every field is, so rows that differ only in span, kind, metadata or record are
//! never the same (ROW-IDENTITY-1). The digest only selects candidates.
//!
//! A VC that is no row of the context has an identity too ([`VcContext::identity_of`],
//! T3 L4 C09): its span, formula and record are interned as [`VcContext::push_node_row`]
//! interns them, and no row is pushed, so it is the identity of any Node row pushed from an
//! equal VC. The compiler's identity oracle identifies the rows its exact sites compare
//! this way, in a context of its own.
//!
//! # Digest and count of a spine
//!
//! A spine's root is never interned. Its Merkle digest is computed from its children's
//! digests by [`MerkleCache::digest_shell`] over an `And` shell, the same preimage an
//! interned node would have, so it equals `formula_digest` of the materialized tree (I5).
//! Its node count is one (the root) plus the distinct nodes its kept facts and body reach,
//! so it equals `query_size` of the materialized tree (I4); with nothing kept it is the
//! body's count.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::OnceLock;

use trust_ir_contract::formula_dag::{NodeId, Shell};

use super::{
    PathGuardRef, RecordRef, RowFormula, RowId, SpanId, SpineId, VcContext, VcContextError,
    WrapperRef,
};
use crate::formula_merkle::{FormulaDigest, MerkleCache, row_node_count};
use crate::{ContractMetadata, Formula, Symbol, VcKind, VerificationCondition};

/// The exact key of a row's formula (module docs).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FormulaKey {
    /// The formula is this node.
    Node(NodeId),
    /// The formula is the conjunction of these nodes, in order: a spine's kept facts and
    /// its body, transient and never interned.
    Conjunction(Vec<NodeId>),
}

/// A record over node lists: a [`super::RecordRef`] with every sequence read and a
/// spine's kept facts resolved, so two records are the same exactly when they are equal.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordKey {
    /// The raw violation predicate.
    pub body: NodeId,
    /// The wrappers, innermost-first.
    pub wrappers: Vec<WrapperKey>,
    /// The negated or shifted operand.
    pub subject: Option<NodeId>,
    /// The UB width.
    pub width: Option<u32>,
}

/// A wrapper over node lists.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum WrapperKey {
    /// `inner ↦ And([facts.., inner])`.
    ConjoinFactsLast(Vec<NodeId>),
    /// `inner ↦ Or([per-path term..])`.
    PathGuardOr(Vec<PathGuardKey>),
}

/// A path term over node lists.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PathGuardKey {
    /// The body whole.
    Raw,
    /// The body whole, over a collapsed path list ([`PathGuardRef::Collapsed`]).
    Collapsed,
    /// The guards, then the body spliced flat.
    Guarded(Vec<NodeId>),
}

/// Every field of a row, as compared inside one context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactIdentity {
    /// The row's kind.
    pub kind: VcKind,
    /// The row's function.
    pub function: Symbol,
    /// The row's span, interned by value.
    pub location: SpanId,
    /// The row's contract metadata.
    pub contract_metadata: Option<ContractMetadata>,
    /// The row's record.
    pub obligation: Option<RecordKey>,
    /// The row's formula.
    pub formula: FormulaKey,
}

/// A row's identity: every field exactly, and the formula's Merkle digest, which only
/// selects candidates ([`VcContext::same_identity`]).
#[derive(Debug, Clone)]
pub struct RowIdentity {
    /// Every field, compared exactly.
    pub exact: ExactIdentity,
    /// The formula's Merkle digest.
    pub digest: FormulaDigest,
}

/// The `And` shell of `arity` children.
fn and_shell(arity: usize) -> Shell {
    static CACHED_AND_SHELLS: OnceLock<[Shell; 17]> = OnceLock::new();
    if arity <= 16 {
        let shells = CACHED_AND_SHELLS.get_or_init(|| {
            std::array::from_fn(|k| Shell::split(Formula::And(vec![Formula::Bool(true); k])).0)
        });
        return shells[arity].clone();
    }
    Shell::split(Formula::And(vec![Formula::Bool(true); arity])).0
}

impl VcContext {
    /// The exact key of row `id`'s formula (module docs).
    ///
    /// # Errors
    ///
    /// An id of another context.
    pub fn formula_key(&self, id: RowId) -> Result<FormulaKey, VcContextError> {
        match self.row(id)?.formula {
            RowFormula::Node(node) => Ok(FormulaKey::Node(node)),
            RowFormula::Spine(spine) => {
                let spine = *self.spines.get(spine)?;
                let kept = self.kept_arc(&spine)?;
                if kept.is_empty() {
                    return Ok(FormulaKey::Node(spine.body));
                }
                let mut nodes = Vec::with_capacity(kept.len() + 1);
                nodes.extend_from_slice(&kept);
                nodes.push(spine.body);
                Ok(FormulaKey::Conjunction(nodes))
            }
        }
    }

    /// Whether two keys name one formula (module docs). Interns nothing.
    #[must_use]
    pub fn key_eq(&self, a: &FormulaKey, b: &FormulaKey) -> bool {
        match (a, b) {
            (FormulaKey::Node(a), FormulaKey::Node(b)) => a == b,
            (FormulaKey::Conjunction(a), FormulaKey::Conjunction(b)) => a == b,
            (FormulaKey::Conjunction(children), FormulaKey::Node(node))
            | (FormulaKey::Node(node), FormulaKey::Conjunction(children)) => {
                self.dag.get(&and_shell(children.len()), children) == Some(*node)
            }
        }
    }

    /// Whether rows `a` and `b` have one formula: the same row, the same node, or keys
    /// that name one formula ([`Self::key_eq`]). A row of another context is never equal.
    #[must_use]
    pub fn formula_eq(&self, a: RowId, b: RowId) -> bool {
        if a == b && self.row(a).is_ok() {
            return true;
        }
        match (self.formula_key(a), self.formula_key(b)) {
            (Ok(a), Ok(b)) => self.key_eq(&a, &b),
            _ => false,
        }
    }

    /// Row `id`'s record over node lists, if it has one.
    ///
    /// # Errors
    ///
    /// An id of another context, or a Node row whose record names kept facts.
    pub fn record_key(&self, id: RowId) -> Result<Option<RecordKey>, VcContextError> {
        let row = self.row(id)?;
        let Some(record) = &row.obligation else {
            return Ok(None);
        };
        let spine = match row.formula {
            RowFormula::Spine(spine) => Some(spine),
            RowFormula::Node(_) => None,
        };
        self.key_of_record(record, spine, VcContextError::KeptOutsideSpine(id)).map(Some)
    }

    /// `record` over node lists: its sequences read and, when it names a spine's kept
    /// facts, those of `spine`. `outside` is the refusal of a record that names kept facts
    /// with no spine to read them from.
    fn key_of_record(
        &self,
        record: &RecordRef,
        spine: Option<SpineId>,
        outside: VcContextError,
    ) -> Result<RecordKey, VcContextError> {
        let mut wrappers = Vec::with_capacity(record.wrappers.len());
        for wrapper in &record.wrappers {
            match wrapper {
                WrapperRef::ConjoinFactsLast { facts } => {
                    wrappers.push(WrapperKey::ConjoinFactsLast(self.seqs.nodes(*facts)?));
                }
                WrapperRef::PathGuardOr { paths } => {
                    let mut keys = Vec::with_capacity(paths.len());
                    for path in paths {
                        keys.push(match path {
                            PathGuardRef::Raw => PathGuardKey::Raw,
                            PathGuardRef::Collapsed => PathGuardKey::Collapsed,
                            PathGuardRef::Guarded { guards } => {
                                PathGuardKey::Guarded(self.seqs.nodes(*guards)?)
                            }
                        });
                    }
                    wrappers.push(WrapperKey::PathGuardOr(keys));
                }
                WrapperRef::SpineKept => {
                    let Some(spine) = spine else {
                        return Err(outside);
                    };
                    let kept = self.kept_arc(self.spines.get(spine)?)?;
                    if !kept.is_empty() {
                        wrappers.push(WrapperKey::ConjoinFactsLast(kept.to_vec()));
                    }
                }
            }
        }
        Ok(RecordKey { body: record.body, wrappers, subject: record.subject, width: record.width })
    }

    /// Row `id`'s identity (module docs).
    ///
    /// # Errors
    ///
    /// An id of another context, or a digest the Merkle cache refuses.
    pub fn identity(&mut self, id: RowId) -> Result<RowIdentity, VcContextError> {
        let digest = self.digest(id)?;
        let row = self.row(id)?;
        let exact = ExactIdentity {
            kind: row.kind.clone(),
            function: row.function,
            location: row.location,
            contract_metadata: row.contract_metadata,
            obligation: self.record_key(id)?,
            formula: self.formula_key(id)?,
        };
        Ok(RowIdentity { exact, digest })
    }

    /// The identity `vc` has as a Node row of this context, without pushing a row (module
    /// docs; T3 L4, C09): its span, formula and record are interned as
    /// [`Self::push_node_row`] interns them, so it is [`Self::same_identity`] as the
    /// identity of every Node row pushed from an equal VC, and of none other. The context's
    /// row list does not change; its DAG, spans and sequences grow by what `vc` adds.
    ///
    /// # Errors
    ///
    /// [`VcContextError::Full`] when a table it needs is full, or a digest the Merkle cache
    /// refuses.
    pub fn identity_of(
        &mut self,
        vc: &VerificationCondition,
    ) -> Result<RowIdentity, VcContextError> {
        let location = self.spans.intern(&vc.location)?;
        let node = self.dag.intern(&vc.formula);
        let obligation = match &vc.obligation {
            Some(record) => {
                let record = self.intern_record(record)?;
                Some(self.key_of_record(&record, None, VcContextError::KeptOutsideRow)?)
            }
            None => None,
        };
        let digest = self.merkle.digest(&self.dag, node)?;
        let exact = ExactIdentity {
            kind: vc.kind.clone(),
            function: vc.function,
            location,
            contract_metadata: vc.contract_metadata,
            obligation,
            formula: FormulaKey::Node(node),
        };
        Ok(RowIdentity { exact, digest })
    }

    /// Whether `identity` is an identity of this context: its span is one of this
    /// context's. An identity of another context names nodes of another DAG, so it is
    /// never compared here (T3 L4, C09).
    #[must_use]
    pub fn holds_identity(&self, identity: &RowIdentity) -> bool {
        self.spans.get(identity.exact.location).is_ok()
    }

    /// Whether two identities of this context are the same row: every field equal, the
    /// formula by [`Self::key_eq`]. The digests are not compared.
    #[must_use]
    pub fn same_identity(&self, a: &RowIdentity, b: &RowIdentity) -> bool {
        let (a, b) = (&a.exact, &b.exact);
        a.kind == b.kind
            && a.function == b.function
            && a.location == b.location
            && a.contract_metadata == b.contract_metadata
            && a.obligation == b.obligation
            && self.key_eq(&a.formula, &b.formula)
    }

    /// The Merkle digest of row `id`'s formula, memoized per row (module docs): equal to
    /// `formula_digest` of the materialized formula (I5).
    ///
    /// # Errors
    ///
    /// An id of another context, or a payload the Merkle cache refuses.
    pub fn digest(&mut self, id: RowId) -> Result<FormulaDigest, VcContextError> {
        let formula = self.row(id)?.formula;
        if let Some(Some(digest)) = self.row_digests.get(id.index()) {
            return Ok(*digest);
        }
        let digest = match formula {
            RowFormula::Node(node) => self.merkle.digest(&self.dag, node)?,
            RowFormula::Spine(spine) => {
                let spine = *self.spines.get(spine)?;
                let kept = self.kept_arc(&spine)?;
                let body = self.merkle.digest(&self.dag, spine.body)?;
                if kept.is_empty() {
                    body
                } else {
                    let mut children = Vec::with_capacity(kept.len() + 1);
                    for node in kept.iter() {
                        children.push(self.merkle.digest(&self.dag, *node)?);
                    }
                    children.push(body);
                    MerkleCache::digest_shell(&and_shell(children.len()), &children)?
                }
            }
        };
        if let Some(slot) = self.row_digests.get_mut(id.index()) {
            *slot = Some(digest);
        }
        Ok(digest)
    }

    /// The number of distinct nodes row `id`'s formula reaches (module docs): equal to
    /// `query_size` of its materialized formula (I4).
    ///
    /// # Errors
    ///
    /// An id of another context.
    pub fn row_node_count(&self, id: RowId) -> Result<u64, VcContextError> {
        match self.formula_key(id)? {
            FormulaKey::Node(node) => Ok(row_node_count(&self.dag, &[node])?),
            FormulaKey::Conjunction(children) => {
                Ok(row_node_count(&self.dag, &children)?.saturating_add(1))
            }
        }
    }
}
