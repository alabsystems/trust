//! Structural panic-freedom evidence — the CFG half of the E6 `NoPanic` facet.
//!
//! A function has no panic SITE of its own when no block reachable from its
//! entry can panic: no reachable `Assert` terminator (the compiler's implicit
//! bounds / arithmetic-overflow / div-by-zero panics) and no reachable direct
//! call to a panic runtime entrypoint (`core::panicking::…`, `begin_panic`, …).
//! This is a pure, `rustc`-free analysis over the [`VerifiableFunction`] CFG, so
//! it lives in the clean IR crate and is unit-testable in isolation.
//!
//! SCOPE. This is the INTRA-function half of `NoPanic`, and it is a solver-free
//! FAST PATH: most real functions carry bounds/overflow `Assert`s and so are
//! (correctly) not structurally panic-free — establishing their panic-freedom
//! needs the L0 aggregate that proves each assertion discharges. What this
//! certifies is the genuinely trivial case (getters, moves, constant returns)
//! with no own panic site at all. Sufficiency for the whole `NoPanic` facet also
//! needs every CALLEE to be `NoPanic` (an ordinary call to a panicking function
//! is not an own panic site here); this composes with an all-callees-`NoPanic`
//! pass, exactly as the structural `Total` halves compose. Conservative: an
//! empty body, or any reachable `Assert` / panic call, yields `false`.

use std::collections::HashSet;

use crate::structural_termination::terminator_successors;
use crate::{BasicBlock, BlockId, Terminator, VerifiableFunction};

/// The panic runtime entrypoints the compiler lowers an explicit `panic!` /
/// `unwrap` / bounds failure into. A direct call to one is an own panic site.
/// These are stable compiler internals; matching by substring tolerates the
/// monomorphized / path-qualified spellings the extractor records.
const PANIC_ENTRYPOINTS: &[&str] = &[
    "core::panicking",
    "std::panicking",
    "begin_panic",
    "rust_begin_unwind",
    "panic_fmt",
    "panic_bounds_check",
    "panic_misaligned_pointer_dereference",
];

fn is_panic_entrypoint(name: &str) -> bool {
    PANIC_ENTRYPOINTS.iter().any(|m| name.contains(m))
}

/// Whether a terminator is an OWN panic site: an `Assert` (implicit panic on
/// failure), a direct call to a panic runtime entrypoint, a `Drop` (its
/// destructor may panic), or unmodeled (`Opaque`) control flow (may hide a
/// panic).
fn is_own_panic_site(t: &Terminator) -> bool {
    match t {
        Terminator::Assert { .. } => true,
        Terminator::Call { func, .. } => is_panic_entrypoint(func),
        // A `Drop` runs the value's destructor (`Drop::drop`) — an uninspected
        // callee that is named by no `func`, so it is invisible to the
        // all-callees composition — and a destructor may panic. Fail closed.
        // Trivial fast-path functions (getters, moves, constant returns) move
        // their results out and carry no `Drop`, so this does not shrink the
        // intended certified set.
        Terminator::Drop { .. } => true,
        // Unmodeled control flow may hide a panic; fail closed, matching how the
        // other facets treat their unmodeled constructs.
        Terminator::Opaque { .. } => true,
        _ => false,
    }
}

/// Whether no block REACHABLE from the entry is an own panic site (see the
/// module docs). An empty block list fails closed.
#[must_use]
pub fn blocks_have_no_reachable_panic_site(blocks: &[BasicBlock]) -> bool {
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
            // A dangling successor references no block: it cannot execute a
            // panic site, so it is a leaf.
            continue;
        };
        if is_own_panic_site(&block.terminator) {
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

/// [`blocks_have_no_reachable_panic_site`] over a whole function body — one
/// sound INPUT to its `NoPanic` facet (see the module docs for what it does NOT
/// establish).
#[must_use]
pub fn is_structurally_panic_free(func: &VerifiableFunction) -> bool {
    blocks_have_no_reachable_panic_site(&func.body.blocks)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AssertMessage, Operand, Place, SourceSpan, UnwindEdge};

    fn block(id: usize, t: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts: Vec::new(), terminator: t }
    }

    fn call(func: &str, target: usize) -> Terminator {
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
    fn assert_free_straight_line_is_panic_free() {
        // bb0 → return, no assert, no panic call.
        let blocks = vec![block(0, Terminator::Goto(BlockId(1))), block(1, Terminator::Return)];
        assert!(blocks_have_no_reachable_panic_site(&blocks));
    }

    #[test]
    fn reachable_assert_is_a_panic_site() {
        let blocks = vec![block(
            0,
            Terminator::Assert {
                cond: Operand::Move(Place::local(0)),
                expected: true,
                msg: AssertMessage::BoundsCheck,
                target: BlockId(1),
                span: SourceSpan::default(),
                unwind: UnwindEdge::Unreachable,
            },
        )];
        assert!(!blocks_have_no_reachable_panic_site(&blocks));
    }

    #[test]
    fn direct_panic_call_is_a_panic_site() {
        let blocks =
            vec![block(0, call("core::panicking::panic", 1)), block(1, Terminator::Return)];
        assert!(!blocks_have_no_reachable_panic_site(&blocks));
    }

    #[test]
    fn an_ordinary_call_is_not_an_own_panic_site() {
        // Calling a non-panic function is not an OWN panic site (its NoPanic is
        // the all-callees composition, not this intra-function check).
        let blocks = vec![block(0, call("crate::helper", 1)), block(1, Terminator::Return)];
        assert!(blocks_have_no_reachable_panic_site(&blocks));
    }

    #[test]
    fn a_reachable_drop_is_a_panic_site() {
        // A `Drop` runs a destructor that may panic and names no callee, so it
        // is invisible to the all-callees composition → fail closed.
        let blocks = vec![
            block(
                0,
                Terminator::Drop {
                    place: Place::local(1),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Unreachable,
                },
            ),
            block(1, Terminator::Return),
        ];
        assert!(!blocks_have_no_reachable_panic_site(&blocks));
    }

    #[test]
    fn an_opaque_terminator_is_a_panic_site() {
        // Unmodeled control flow may hide a panic → fail closed.
        let blocks = vec![
            block(
                0,
                Terminator::Opaque {
                    kind: "InlineAsm".into(),
                    targets: vec![BlockId(1)],
                    span: SourceSpan::default(),
                },
            ),
            block(1, Terminator::Return),
        ];
        assert!(!blocks_have_no_reachable_panic_site(&blocks));
    }

    #[test]
    fn a_drop_in_dead_code_is_ignored() {
        // bb0 returns; the drop in the unreachable bb1 cannot run.
        let blocks = vec![
            block(0, Terminator::Return),
            block(
                1,
                Terminator::Drop {
                    place: Place::local(1),
                    target: BlockId(2),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Unreachable,
                },
            ),
        ];
        assert!(blocks_have_no_reachable_panic_site(&blocks));
    }

    #[test]
    fn an_assert_in_dead_code_is_ignored() {
        // bb0 returns; the assert in bb1 is unreachable, so it cannot panic.
        let blocks = vec![
            block(0, Terminator::Return),
            block(
                1,
                Terminator::Assert {
                    cond: Operand::Move(Place::local(0)),
                    expected: true,
                    msg: AssertMessage::BoundsCheck,
                    target: BlockId(2),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Unreachable,
                },
            ),
        ];
        assert!(blocks_have_no_reachable_panic_site(&blocks));
    }

    #[test]
    fn empty_body_fails_closed() {
        assert!(!blocks_have_no_reachable_panic_site(&[]));
    }
}
