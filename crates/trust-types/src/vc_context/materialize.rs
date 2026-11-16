//! Reading a row as a tree ([`MaterializedVc`], D-VC-2, L4-MAT-1).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;

use trust_ir_contract::formula_dag::NodeId;

use super::stats::TreeCount;
use super::{PathGuardRef, RowFormula, RowId, VcContext, VcContextError, WrapperRef};
use crate::{Formula, ObligationRecord, ObligationWrapper, PathGuardTerm, VerificationCondition};

/// One row as the `VerificationCondition` it denotes (I1), owned for one use.
///
/// It lends the tree by [`MaterializedVc::vc`] and has neither `Clone` nor `Deref`, so a
/// consumer cannot keep a tree it materialized for one dispatch; dropping it decrements
/// the context's `trees_alive`. `VerificationCondition` itself keeps `Clone` (L4-MAT-1);
/// what polices retention is `trees_alive` and, from C10a, the field and `.vc().clone()`
/// censuses.
///
/// ```compile_fail,E0277
/// fn needs_clone<T: Clone>() {}
/// needs_clone::<trust_types::vc_context::MaterializedVc>();
/// ```
///
/// ```compile_fail,E0614
/// fn tree(m: &trust_types::vc_context::MaterializedVc) -> &trust_types::VerificationCondition {
///     &**m
/// }
/// ```
#[derive(Debug)]
pub struct MaterializedVc {
    vc: VerificationCondition,
    trees: Arc<TreeCount>,
}

impl MaterializedVc {
    /// The row's tree, borrowed.
    #[must_use]
    pub fn vc(&self) -> &VerificationCondition {
        &self.vc
    }
}

impl Drop for MaterializedVc {
    fn drop(&mut self) {
        self.trees.release();
    }
}

/// The number of nodes of `formula` as a tree; iterative.
fn tree_nodes(formula: &Formula) -> u64 {
    let (mut nodes, mut pending) = (0u64, vec![formula]);
    while let Some(node) = pending.pop() {
        nodes = nodes.saturating_add(1);
        crate::for_each_formula_child(node, |child| pending.push(child));
    }
    nodes
}

impl VcContext {
    fn expand_seq(&self, nodes: &[NodeId]) -> Result<Vec<Formula>, VcContextError> {
        nodes.iter().map(|&node| self.expand(node)).collect()
    }

    fn expand(&self, node: NodeId) -> Result<Formula, VcContextError> {
        if self.dag.contains(node) {
            Ok(self.dag.expand(node))
        } else {
            Err(VcContextError::UnknownNode(node))
        }
    }

    /// Row `id` as the `VerificationCondition` it denotes, in every field (I1): the
    /// formula and record expanded from the DAG, a spine's kept facts conjoined before its
    /// body (its body alone when nothing is kept), and the span read back by value.
    ///
    /// # Errors
    ///
    /// An id of another context.
    pub fn materialize(&self, id: RowId) -> Result<MaterializedVc, VcContextError> {
        let row = self.row(id)?;
        let (formula, kept) = match row.formula {
            RowFormula::Node(node) => (self.expand(node)?, None),
            RowFormula::Spine(spine) => {
                let spine = *self.spines.get(spine)?;
                let kept = self.kept_arc(&spine)?;
                let body = self.expand(spine.body)?;
                let formula = if kept.is_empty() {
                    body
                } else {
                    let mut conjuncts = self.expand_seq(&kept)?;
                    conjuncts.push(body);
                    Formula::And(conjuncts)
                };
                (formula, Some(kept))
            }
        };
        let obligation = match &row.obligation {
            None => None,
            Some(record) => {
                let mut wrappers = Vec::with_capacity(record.wrappers.len());
                for wrapper in &record.wrappers {
                    match wrapper {
                        WrapperRef::ConjoinFactsLast { facts } => {
                            wrappers.push(ObligationWrapper::ConjoinFactsLast {
                                facts: self.expand_seq(&self.seqs.nodes(*facts)?)?,
                            });
                        }
                        WrapperRef::PathGuardOr { paths } => {
                            let mut terms = Vec::with_capacity(paths.len());
                            for path in paths {
                                terms.push(match path {
                                    PathGuardRef::Raw => PathGuardTerm::Raw,
                                    PathGuardRef::Collapsed => PathGuardTerm::Collapsed,
                                    PathGuardRef::Guarded { guards } => PathGuardTerm::Guarded {
                                        guards: self.expand_seq(&self.seqs.nodes(*guards)?)?,
                                    },
                                });
                            }
                            wrappers.push(ObligationWrapper::PathGuardOr { paths: terms });
                        }
                        WrapperRef::SpineKept => match &kept {
                            None => return Err(VcContextError::KeptOutsideSpine(id)),
                            Some(kept) if kept.is_empty() => {}
                            Some(kept) => wrappers.push(ObligationWrapper::ConjoinFactsLast {
                                facts: self.expand_seq(kept)?,
                            }),
                        },
                    }
                }
                Some(ObligationRecord {
                    body: self.expand(record.body)?,
                    wrappers,
                    subject: record.subject.map(|subject| self.expand(subject)).transpose()?,
                    width: record.width,
                })
            }
        };
        let vc = VerificationCondition {
            kind: row.kind.clone(),
            function: row.function,
            location: self.spans.get(row.location)?.clone(),
            formula,
            contract_metadata: row.contract_metadata,
            obligation,
        };
        let formula_nodes = tree_nodes(&vc.formula);
        let record_nodes = vc.obligation.as_ref().map_or(0, |record| {
            let mut nodes = tree_nodes(&record.body)
                .saturating_add(record.subject.as_ref().map_or(0, tree_nodes));
            for wrapper in &record.wrappers {
                match wrapper {
                    ObligationWrapper::ConjoinFactsLast { facts } => {
                        nodes = facts.iter().map(tree_nodes).fold(nodes, u64::saturating_add);
                    }
                    ObligationWrapper::PathGuardOr { paths } => {
                        for path in paths {
                            if let PathGuardTerm::Guarded { guards } = path {
                                nodes =
                                    guards.iter().map(tree_nodes).fold(nodes, u64::saturating_add);
                            }
                        }
                    }
                }
            }
            nodes
        });
        let size = self.row_node_count(id)?;
        self.stats.record_materialization(formula_nodes, record_nodes, size);
        let trees = self.stats.trees();
        trees.acquire();
        Ok(MaterializedVc { vc, trees })
    }
}
