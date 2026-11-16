//! The retained row ([`VcRow`]), which holds no tree, and the span table.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_ir_contract::formula_dag::NodeId;

use super::{RecordRef, SpanId, Spine, SpineId, VcContextError};
use crate::fx::FxHashMap;
use crate::{ContractMetadata, SourceSpan, Symbol, VcKind};

/// What a row's formula is: a node of the context's DAG, or a block-def recipe whose
/// root is never interned (D-VC-3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RowFormula {
    /// The formula is this node.
    Node(NodeId),
    /// The formula is this spine's kept facts conjoined before its body (its body alone
    /// when nothing is kept).
    Spine(SpineId),
}

/// One retained row (D-VC-2): every field of a `VerificationCondition`, with the formula
/// and the record's formulas as ids into the context and the span interned. Immutable: a
/// rewrite pushes a new row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VcRow {
    pub(super) kind: VcKind,
    pub(super) function: Symbol,
    pub(super) location: SpanId,
    pub(super) formula: RowFormula,
    pub(super) contract_metadata: Option<ContractMetadata>,
    pub(super) obligation: Option<RecordRef>,
}

impl VcRow {
    /// The row's kind.
    #[must_use]
    pub fn kind(&self) -> &VcKind {
        &self.kind
    }

    /// The function the row belongs to.
    #[must_use]
    pub fn function(&self) -> Symbol {
        self.function
    }

    /// The row's span, interned.
    #[must_use]
    pub fn location(&self) -> SpanId {
        self.location
    }

    /// The row's formula.
    #[must_use]
    pub fn formula(&self) -> RowFormula {
        self.formula
    }

    /// The row's contract metadata.
    #[must_use]
    pub fn contract_metadata(&self) -> Option<ContractMetadata> {
        self.contract_metadata
    }

    /// The row's authenticated-obligation record, over the context's ids.
    #[must_use]
    pub fn obligation(&self) -> Option<&RecordRef> {
        self.obligation.as_ref()
    }
}

/// The parts of a Spine row ([`super::VcContext::push_spine_row`]).
#[derive(Debug, Clone)]
pub struct SpineRow {
    /// The row's kind.
    pub kind: VcKind,
    /// The function the row belongs to.
    pub function: Symbol,
    /// The row's span.
    pub location: SourceSpan,
    /// The recipe of the row's formula.
    pub spine: Spine,
    /// The row's contract metadata.
    pub contract_metadata: Option<ContractMetadata>,
    /// The row's record, which may name the spine's kept facts.
    pub obligation: Option<RecordRef>,
}

/// Spans interned by their full value: two rows have one [`SpanId`] exactly when their
/// spans are equal in every field.
#[derive(Debug)]
pub(super) struct SpanTable {
    brand: u64,
    spans: Vec<SourceSpan>,
    index: FxHashMap<SourceSpan, u32>,
}

impl SpanTable {
    pub(super) fn new(brand: u64) -> Self {
        SpanTable { brand, spans: Vec::new(), index: FxHashMap::default() }
    }

    pub(super) fn intern(&mut self, span: &SourceSpan) -> Result<SpanId, VcContextError> {
        if let Some(&index) = self.index.get(span) {
            return Ok(SpanId { brand: self.brand, index });
        }
        let index = super::next_index(self.spans.len(), "span")?;
        self.spans.push(span.clone());
        self.index.insert(span.clone(), index);
        Ok(SpanId { brand: self.brand, index })
    }

    pub(super) fn get(&self, id: SpanId) -> Result<&SourceSpan, VcContextError> {
        if id.brand != self.brand {
            return Err(VcContextError::UnknownSpan(id));
        }
        self.spans.get(id.index()).ok_or(VcContextError::UnknownSpan(id))
    }

    pub(super) fn len(&self) -> usize {
        self.spans.len()
    }
}
