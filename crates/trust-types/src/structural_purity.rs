//! Structural purity evidence — the own-memory-effect half of the E6 `Pure`
//! facet.
//!
//! A function has no memory EFFECT of its own when no statement reachable from
//! its entry writes through a reference. In this IR a write reaches caller
//! memory (or a `static`) only through a `Deref` projection — a bare local write
//! stays on the function's own stack frame — so "no reachable `Deref`-write" is
//! exactly "no own memory effect". Two statement classes fail closed as
//! potentially effectful without carrying a written place we can inspect:
//! `Intrinsic` (may store through a pointer argument, e.g. `volatile_store`) and
//! `Unsupported` (unmodeled MIR). This is a pure, `rustc`-free CFG/statement
//! analysis, unit-testable in isolation.
//!
//! SCOPE. This is the INTRA-function, memory-WRITE half of `Pure`. Sufficiency
//! for the whole facet also needs every CALLEE to be `Pure` (an ordinary call is
//! not inspected here) — the all-callees composition — and the READ-of-a-
//! nondeterministic-source dimension belongs to the `Deterministic` facet.
//! Conservative: an empty body, or any reachable `Deref`-write / intrinsic /
//! unsupported statement, yields `false`. It never reports an impure function as
//! pure.

use crate::structural_termination::terminator_successors;
use crate::{BasicBlock, BlockId, Place, Projection, Statement, Terminator, VerifiableFunction};
use std::collections::HashSet;

/// Whether a written place reaches memory OUTSIDE the current stack frame — i.e.
/// through a `Deref` projection (a `&mut`, a raw pointer, or a `static`'s
/// address). A bare local (possibly with `Field`/`Index`/`Downcast`
/// projections, but no `Deref`) writes only the function's own frame.
fn writes_through_reference(place: &Place) -> bool {
    place.projections.iter().any(|p| matches!(p, Projection::Deref))
}

/// Whether a statement is a potential OWN memory effect.
/// Computational intrinsics with NO memory access — pure by construction, so
/// they do not deny purity. Anything NOT on this list (a memory `volatile_*` /
/// `copy*` / `write_bytes`, an atomic, or any unrecognized intrinsic) fails
/// closed. Matched by substring on the intrinsic name.
const PURE_INTRINSICS: &[&str] = &[
    "ctpop",
    "ctlz",
    "cttz",
    "bswap",
    "bitreverse",
    "add_with_overflow",
    "sub_with_overflow",
    "mul_with_overflow",
    "wrapping_add",
    "wrapping_sub",
    "wrapping_mul",
    "saturating_add",
    "saturating_sub",
    "rotate_left",
    "rotate_right",
    "abs",
    "min",
    "max",
    "fabs",
    "sqrtf",
    "likely",
    "unlikely",
    "black_box",
];

fn is_pure_intrinsic(name: &str) -> bool {
    // Deny memory-touching families FIRST. An `atomic_*` / `volatile_*`
    // intrinsic always accesses memory, and `atomic_min*` / `atomic_max*` /
    // `atomic_umax*` even ALIAS the pure `min`/`max` substrings below — so a
    // bare allow-list check would wrongly admit them. Rejecting the atomic and
    // volatile prefixes up front closes that hole (and no pure intrinsic name
    // contains either word).
    if name.contains("atomic") || name.contains("volatile") {
        return false;
    }
    PURE_INTRINSICS.iter().any(|p| name.contains(p))
}

fn statement_is_effectful(stmt: &Statement) -> bool {
    match stmt {
        Statement::Assign { place, .. }
        | Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place } => writes_through_reference(place),
        // A pure computational intrinsic has no memory effect; any other
        // intrinsic (memory `volatile_*`/`copy*`, atomics, unrecognized) may
        // write through a pointer argument and fails closed — as does an
        // unmodeled `Unsupported` statement.
        Statement::Intrinsic { name, .. } => !is_pure_intrinsic(name),
        Statement::Unsupported { .. } => true,
        // Storage markers, retag, place mentions, coverage, counters, nop:
        // no memory-content write.
        _ => false,
    }
}

/// Whether a terminator is an OWN memory effect. Unmodeled (`Opaque`) control
/// flow may perform a write with no place we can inspect (e.g. inline asm with a
/// memory clobber), so it fails closed. Ordinary `Call` effects are the
/// all-callees composition and `Drop`'s destructor effect defers to it / a
/// deeper lane, so neither is an OWN effect here.
fn terminator_is_effectful(t: &Terminator) -> bool {
    matches!(t, Terminator::Opaque { .. })
}

/// Whether no statement in a block REACHABLE from the entry is an own memory
/// effect (see the module docs). An empty block list fails closed.
#[must_use]
pub fn blocks_have_no_reachable_own_effect(blocks: &[BasicBlock]) -> bool {
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
        if block.stmts.iter().any(statement_is_effectful)
            || terminator_is_effectful(&block.terminator)
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

/// [`blocks_have_no_reachable_own_effect`] over a whole function body — one sound
/// INPUT to its `Pure` facet (see the module docs for what it does NOT
/// establish).
#[must_use]
pub fn is_structurally_pure(func: &VerifiableFunction) -> bool {
    blocks_have_no_reachable_own_effect(&func.body.blocks)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Operand, Rvalue, SourceSpan, Terminator};

    fn block(id: usize, stmts: Vec<Statement>, t: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator: t }
    }

    fn deref_place(local: usize) -> Place {
        Place { local, projections: vec![Projection::Deref] }
    }

    fn field_place(local: usize) -> Place {
        Place { local, projections: vec![Projection::Field(0)] }
    }

    fn assign(place: Place) -> Statement {
        Statement::Assign {
            place,
            rvalue: Rvalue::Use(Operand::Move(Place::local(9))),
            span: SourceSpan::default(),
        }
    }

    #[test]
    fn local_writes_are_pure() {
        // Writes to a bare local and to a local's field (no Deref) are on the
        // function's own frame.
        let blocks = vec![block(
            0,
            vec![assign(Place::local(1)), assign(field_place(2))],
            Terminator::Return,
        )];
        assert!(blocks_have_no_reachable_own_effect(&blocks));
    }

    #[test]
    fn a_write_through_a_reference_is_an_effect() {
        // `*_1 = …` mutates caller memory.
        let blocks = vec![block(0, vec![assign(deref_place(1))], Terminator::Return)];
        assert!(!blocks_have_no_reachable_own_effect(&blocks));
    }

    #[test]
    fn intrinsic_and_unsupported_statements_fail_closed() {
        let intr = block(
            0,
            vec![Statement::Intrinsic { name: "volatile_store".into(), args: Vec::new() }],
            Terminator::Return,
        );
        assert!(!blocks_have_no_reachable_own_effect(&[intr]));
        let unsup = block(
            0,
            vec![Statement::Unsupported {
                kind: "k".into(),
                detail: "d".into(),
                operands: Vec::new(),
                span: SourceSpan::default(),
            }],
            Terminator::Return,
        );
        assert!(!blocks_have_no_reachable_own_effect(&[unsup]));
    }

    #[test]
    fn a_pure_computational_intrinsic_is_not_an_effect() {
        // `ctpop` (population count) reads a value and returns one — no memory
        // access — so it does not deny purity, while a memory intrinsic
        // (`copy_nonoverlapping`) may store through a pointer and fails closed.
        for name in ["ctpop", "wrapping_add", "core::intrinsics::bswap"] {
            let b = block(
                0,
                vec![Statement::Intrinsic { name: name.into(), args: Vec::new() }],
                Terminator::Return,
            );
            assert!(blocks_have_no_reachable_own_effect(&[b]), "{name} is pure");
        }
        // `atomic_min*`/`atomic_max*`/`atomic_umax*` alias the pure `min`/`max`
        // substrings but are memory RMWs — the atomic/volatile deny-guard must
        // reject them before the allow-list is consulted.
        for name in [
            "copy_nonoverlapping",
            "write_bytes",
            "atomic_store_seqcst",
            "atomic_min_seqcst",
            "atomic_max_seqcst",
            "atomic_umax_relaxed",
            "volatile_load",
            "some_unknown",
        ] {
            let b = block(
                0,
                vec![Statement::Intrinsic { name: name.into(), args: Vec::new() }],
                Terminator::Return,
            );
            assert!(!blocks_have_no_reachable_own_effect(&[b]), "{name} fails closed");
        }
    }

    #[test]
    fn an_opaque_terminator_is_an_effect() {
        // Unmodeled control flow may perform a write we cannot inspect → fail
        // closed; a modeled effect-free terminator (Return) stays pure.
        let opaque = vec![
            block(0, Vec::new(), Terminator::Opaque {
                kind: "InlineAsm".into(),
                targets: vec![BlockId(1)],
                span: SourceSpan::default(),
            }),
            block(1, Vec::new(), Terminator::Return),
        ];
        assert!(!blocks_have_no_reachable_own_effect(&opaque));
    }

    #[test]
    fn an_effect_in_dead_code_is_ignored() {
        // bb0 returns; the deref-write in bb1 is unreachable.
        let blocks = vec![
            block(0, Vec::new(), Terminator::Return),
            block(1, vec![assign(deref_place(1))], Terminator::Goto(BlockId(1))),
        ];
        assert!(blocks_have_no_reachable_own_effect(&blocks));
    }

    #[test]
    fn empty_body_fails_closed() {
        assert!(!blocks_have_no_reachable_own_effect(&[]));
    }
}
