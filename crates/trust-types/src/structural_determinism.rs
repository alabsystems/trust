//! Structural determinism evidence — the own-nondeterminism half of the E6
//! `Deterministic` facet.
//!
//! A function introduces no nondeterminism OF ITS OWN when, along every block
//! reachable from its entry, it performs no ATOMIC operation (an atomic load
//! observes another thread's writes) and no VOLATILE intrinsic (a volatile read
//! may change under the abstract machine). Ordinary nondeterministic *calls*
//! (`rand`, `SystemTime::now`, …) are NOT own nondeterminism here — they are
//! plain callees, ruled out by the all-callees composition (such a callee is
//! external and absent from the deterministic allowlist, so its caller fails
//! closed). A pure, `rustc`-free CFG analysis, unit-testable in isolation.
//!
//! SCOPE. The intra-function half of `Deterministic`, and deliberately THIN:
//! almost all real functions have no atomics/volatiles and so are intrinsically
//! determinism-neutral, which is exactly right — the facet's real force is the
//! composition ([`crate::facet_propagation::greatest_facet_closure`]) over a
//! base of these functions with `trusted_external` = a sound allowlist of
//! deterministic external calls. Conservative: an empty body, or any reachable
//! atomic / volatile / `Unsupported` statement, yields `false`.

use std::collections::HashSet;

use crate::structural_termination::terminator_successors;
use crate::{BasicBlock, BlockId, Rvalue, Statement, Terminator, VerifiableFunction};

/// Whether a statement is an OWN nondeterminism source: a volatile or atomic
/// intrinsic, an `Assign` of an UNMODELED rvalue, or an unmodeled
/// (`Unsupported`) statement (both fail closed).
fn statement_is_nondeterministic(stmt: &Statement) -> bool {
    match stmt {
        Statement::Intrinsic { name, .. } => {
            let n = name.to_ascii_lowercase();
            n.contains("volatile") || n.contains("atomic")
        }
        // An unmodeled rvalue may READ a nondeterministic source that has no
        // dedicated `Rvalue` variant — e.g. a `ThreadLocalRef` (per-thread
        // address) or an unrecognized machine read. We cannot rule that out, so
        // fail closed, matching the `UnsupportedMir` obligation vcgen already
        // raises for such an rvalue (and matching the `Statement::Unsupported`
        // arm below).
        Statement::Assign { rvalue: Rvalue::Unsupported { .. }, .. } => true,
        Statement::Unsupported { .. } => true,
        _ => false,
    }
}

/// Whether a terminator is an OWN nondeterminism source: an atomic operation
/// (the `atomic` annotation set on a `Call`, e.g. an atomic load), or unmodeled
/// (`Opaque`) control flow — which may hide a nondeterministic read (inline asm
/// observing a hardware source, an unmodeled terminator), so it fails closed.
fn terminator_is_nondeterministic(t: &Terminator) -> bool {
    matches!(t, Terminator::Call { atomic: Some(_), .. } | Terminator::Opaque { .. })
}

/// Whether no block REACHABLE from the entry introduces own nondeterminism (see
/// the module docs). An empty block list fails closed.
#[must_use]
pub fn blocks_have_no_reachable_nondeterminism(blocks: &[BasicBlock]) -> bool {
    let Some(entry) = blocks.first().map(|b| b.id) else {
        return false;
    };
    let by_id: std::collections::HashMap<BlockId, &BasicBlock> =
        blocks.iter().map(|b| (b.id, b)).collect();

    let mut seen: HashSet<BlockId> = HashSet::new();
    seen.insert(entry);
    let mut stack = vec![entry];
    while let Some(bid) = stack.pop() {
        let Some(block) = by_id.get(&bid) else {
            continue;
        };
        if block.stmts.iter().any(statement_is_nondeterministic)
            || terminator_is_nondeterministic(&block.terminator)
        {
            return false;
        }
        for s in terminator_successors(&block.terminator) {
            if seen.insert(s) {
                stack.push(s);
            }
        }
    }
    true
}

/// [`blocks_have_no_reachable_nondeterminism`] over a whole function body — the
/// intrinsic base for its `Deterministic` facet (composed with all callees; see
/// the module docs).
#[must_use]
pub fn is_structurally_deterministic(func: &VerifiableFunction) -> bool {
    blocks_have_no_reachable_nondeterminism(&func.body.blocks)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AtomicOpKind, AtomicOperation, AtomicOrdering, Place, SourceSpan, UnwindEdge};

    fn block(id: usize, stmts: Vec<Statement>, t: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator: t }
    }

    fn an_atomic() -> AtomicOperation {
        AtomicOperation {
            place: Place::local(1),
            dest: Some(Place::local(0)),
            op_kind: AtomicOpKind::Load,
            ordering: AtomicOrdering::SeqCst,
            failure_ordering: None,
            span: SourceSpan::default(),
        }
    }

    fn plain_call(func: &str, target: usize) -> Terminator {
        Terminator::Call {
            func: func.to_string(),
            args: Vec::new(),
            dest: Place::local(0),
            target: Some(BlockId(target)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: UnwindEdge::Unreachable,
        }
    }

    #[test]
    fn atomic_free_body_is_deterministic() {
        // A plain call is NOT own nondeterminism — its determinism is the
        // all-callees composition, not this intra check.
        let blocks = vec![
            block(0, Vec::new(), plain_call("crate::helper", 1)),
            block(1, Vec::new(), Terminator::Return),
        ];
        assert!(blocks_have_no_reachable_nondeterminism(&blocks));
    }

    #[test]
    fn an_atomic_call_is_own_nondeterminism() {
        let atomic = Terminator::Call {
            func: "core::sync::atomic::AtomicUsize::load".to_string(),
            args: Vec::new(),
            dest: Place::local(0),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: Some(an_atomic()),
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: UnwindEdge::Unreachable,
        };
        let blocks = vec![block(0, Vec::new(), atomic), block(1, Vec::new(), Terminator::Return)];
        assert!(!blocks_have_no_reachable_nondeterminism(&blocks));
    }

    #[test]
    fn a_volatile_intrinsic_is_own_nondeterminism() {
        let blocks = vec![block(
            0,
            vec![Statement::Intrinsic { name: "volatile_load".into(), args: Vec::new() }],
            Terminator::Return,
        )];
        assert!(!blocks_have_no_reachable_nondeterminism(&blocks));
    }

    #[test]
    fn an_atomic_op_in_dead_code_is_ignored() {
        let atomic = Terminator::Call {
            func: "atomic_load".to_string(),
            args: Vec::new(),
            dest: Place::local(0),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: Some(an_atomic()),
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: UnwindEdge::Unreachable,
        };
        // bb0 returns; the atomic op in the unreachable bb1 cannot execute.
        let blocks = vec![block(0, Vec::new(), Terminator::Return), block(1, Vec::new(), atomic)];
        assert!(blocks_have_no_reachable_nondeterminism(&blocks));
    }

    #[test]
    fn an_assign_of_an_unmodeled_rvalue_fails_closed() {
        use crate::{Operand, Place, Rvalue};
        // An unmodeled rvalue (e.g. a lowered `ThreadLocalRef`) may read a
        // nondeterministic source → fail closed …
        let unsup = block(
            0,
            vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Unsupported {
                    kind: "ThreadLocalRef".into(),
                    detail: "T".into(),
                    operands: Vec::new(),
                },
                span: SourceSpan::default(),
            }],
            Terminator::Return,
        );
        assert!(!blocks_have_no_reachable_nondeterminism(&[unsup]));
        // … while an assign of a MODELED rvalue (a plain use) stays deterministic.
        let modeled = block(
            0,
            vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Move(Place::local(2))),
                span: SourceSpan::default(),
            }],
            Terminator::Return,
        );
        assert!(blocks_have_no_reachable_nondeterminism(&[modeled]));
    }

    #[test]
    fn an_opaque_terminator_fails_closed() {
        // Unmodeled control flow may hide a nondeterministic read → fail closed.
        let blocks = vec![
            block(
                0,
                Vec::new(),
                Terminator::Opaque {
                    kind: "InlineAsm".into(),
                    targets: vec![BlockId(1)],
                    span: SourceSpan::default(),
                },
            ),
            block(1, Vec::new(), Terminator::Return),
        ];
        assert!(!blocks_have_no_reachable_nondeterminism(&blocks));
    }

    #[test]
    fn unsupported_statement_fails_closed() {
        let blocks = vec![block(
            0,
            vec![Statement::Unsupported {
                kind: "k".into(),
                detail: "d".into(),
                operands: Vec::new(),
                span: SourceSpan::default(),
            }],
            Terminator::Return,
        )];
        assert!(!blocks_have_no_reachable_nondeterminism(&blocks));
    }

    #[test]
    fn empty_body_fails_closed() {
        assert!(!blocks_have_no_reachable_nondeterminism(&[]));
    }
}
