//! The authenticated-obligation record over a context's ids ([`RecordRef`]): it mirrors
//! `ObligationRecord`, `ObligationWrapper` and `PathGuardTerm` with every formula a node
//! and every formula list a hash-consed sequence.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_ir_contract::formula_dag::{FormulaDag, NodeId};

use super::spine::SeqStore;
use super::{SeqId, VcContext, VcContextError};
use crate::{ObligationRecord, ObligationWrapper, PathGuardTerm};

/// `ObligationRecord` over a context's ids.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordRef {
    /// The raw violation predicate.
    pub body: NodeId,
    /// The wrappers, innermost-first.
    pub wrappers: Vec<WrapperRef>,
    /// The negated or shifted operand, where the kind implies one.
    pub subject: Option<NodeId>,
    /// The UB width, where the kind implies one.
    pub width: Option<u32>,
}

/// `ObligationWrapper` over a context's ids, and the one wrapper a Spine row derives.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum WrapperRef {
    /// `inner ↦ And([facts.., inner])`.
    ConjoinFactsLast {
        /// The facts, in order.
        facts: SeqId,
    },
    /// `inner ↦ Or([per-path term..])`.
    PathGuardOr {
        /// The path terms, in order.
        paths: Vec<PathGuardRef>,
    },
    /// A Spine row's `ConjoinFactsLast { kept }`: the facts its spine keeps, derived when
    /// the row is read and never stored. A spine that keeps nothing records no wrapper
    /// here, as the eager recorder records none for an empty kept list.
    SpineKept,
}

/// `PathGuardTerm` over a context's ids.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PathGuardRef {
    /// The body whole.
    Raw,
    /// [`PathGuardTerm::Collapsed`]: the body whole, over a collapsed path list (S1). Kept
    /// distinct from [`Self::Raw`] so a materialized record carries the marker the
    /// generic refutation scope reads.
    Collapsed,
    /// `And([guards.., <body spliced flat>])`.
    Guarded {
        /// The guards, in order.
        guards: SeqId,
    },
}

impl RecordRef {
    /// Every node and sequence of the record belongs to `dag` and `seqs`.
    pub(super) fn validate(&self, dag: &FormulaDag, seqs: &SeqStore) -> Result<(), VcContextError> {
        for node in std::iter::once(self.body).chain(self.subject) {
            if !dag.contains(node) {
                return Err(VcContextError::UnknownNode(node));
            }
        }
        for wrapper in &self.wrappers {
            match wrapper {
                WrapperRef::ConjoinFactsLast { facts } => {
                    seqs.validate(*facts)?;
                }
                WrapperRef::PathGuardOr { paths } => {
                    for path in paths {
                        if let PathGuardRef::Guarded { guards } = path {
                            seqs.validate(*guards)?;
                        }
                    }
                }
                WrapperRef::SpineKept => {}
            }
        }
        Ok(())
    }
}

impl VcContext {
    /// Intern `record`'s formulas and lists ([`RecordRef`]).
    ///
    /// # Errors
    ///
    /// [`VcContextError::Full`] when the sequence table is full.
    pub fn intern_record(
        &mut self,
        record: &ObligationRecord,
    ) -> Result<RecordRef, VcContextError> {
        let body = self.dag.intern(&record.body);
        let subject = record.subject.as_ref().map(|subject| self.dag.intern(subject));
        let mut wrappers = Vec::with_capacity(record.wrappers.len());
        for wrapper in &record.wrappers {
            wrappers.push(match wrapper {
                ObligationWrapper::ConjoinFactsLast { facts } => {
                    WrapperRef::ConjoinFactsLast { facts: self.intern_seq(facts)? }
                }
                ObligationWrapper::PathGuardOr { paths } => {
                    let mut terms = Vec::with_capacity(paths.len());
                    for path in paths {
                        terms.push(match path {
                            PathGuardTerm::Raw => PathGuardRef::Raw,
                            PathGuardTerm::Collapsed => PathGuardRef::Collapsed,
                            PathGuardTerm::Guarded { guards } => {
                                PathGuardRef::Guarded { guards: self.intern_seq(guards)? }
                            }
                        });
                    }
                    WrapperRef::PathGuardOr { paths: terms }
                }
            });
        }
        Ok(RecordRef { body, wrappers, subject, width: record.width })
    }

    /// Intern `formulas` and the sequence of their nodes.
    fn intern_seq(&mut self, formulas: &[crate::Formula]) -> Result<SeqId, VcContextError> {
        let mut parent = None;
        for formula in formulas {
            let node = self.dag.intern(formula);
            parent = self.seqs.push_checked(parent, node)?.cell;
        }
        Ok(SeqId { brand: self.brand, cell: parent })
    }
}
