//! census-vcgen-hang (2026-10-02): the compiler's `Vec`-forwarder gate replays the
//! root's owned-`Vec` index row at EVERY root call site of a forwarder
//! (`charge_vec_index_forwarders` -> [`super::owned_vec_scalar_index_row`]). Outside a
//! VC-gen scope each replay rebuilt the whole-function statement-version oracle, so
//! the gate cost O(sites x body); on aterm-census `run_lock_order_census` (1114 blocks,
//! 24 sites) it ran minutes past the function's budget. [`super::row_replay_scope`]
//! holds one memo scope across the batch. These tests pin that the scope changes no
//! row (byte-identical to the unscoped replays) and that it builds the oracle once,
//! with the deterministic oracle-build counter, not a clock.

use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty,
    UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::{owned_vec_scalar_index_row, row_replay_scope};

const INDEX: &str = "<std::vec::Vec<u32> as core::ops::index::Index<usize>>::index";

fn usize_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn elem_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(Ty::Int { width: 32, signed: false }) }
}

/// `fn f(v: &Vec<u32>, i: usize)` with `sites` calls `<Vec<u32> as Index>::index(v, _k)`,
/// each through its own index temp `_k = i` and its own destination, one call per
/// block, chained, then `return`.
fn sites_func(sites: usize) -> VerifiableFunction {
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
        LocalDecl {
            index: 1,
            ty: Ty::Ref { mutable: false, inner: Box::new(Ty::adt("std::vec::Vec<u32>", vec![])) },
            name: Some("v".into()),
        },
        LocalDecl { index: 2, ty: usize_ty(), name: Some("i".into()) },
    ];
    let mut blocks = Vec::new();
    for k in 0..sites {
        let idx = locals.len();
        locals.push(LocalDecl { index: idx, ty: usize_ty(), name: None });
        let dest = locals.len();
        locals.push(LocalDecl { index: dest, ty: elem_ref(), name: None });
        blocks.push(BasicBlock {
            id: BlockId(k),
            stmts: vec![Statement::Assign {
                place: Place::local(idx),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                func: INDEX.to_string(),
                args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(idx))],
                dest: Place::local(dest),
                target: Some(BlockId(k + 1)),
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: crate::sep_engine::tests::fixture_key(INDEX),
                is_foreign: false,
            },
        });
    }
    blocks.push(BasicBlock { id: BlockId(sites), stmts: vec![], terminator: Terminator::Return });
    VerifiableFunction {
        name: "sites".to_string(),
        def_path: "test::sites".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Replay every site's row, reporting the rows and how many statement-version
/// oracles were built doing it.
fn replay_all(
    func: &VerifiableFunction,
    sites: usize,
) -> (Vec<Option<(trust_types::VcKind, trust_types::Formula)>>, u64) {
    crate::reset_analysis_memo_stats();
    let rows = (0..sites).map(|k| owned_vec_scalar_index_row(func, BlockId(k))).collect();
    (rows, crate::analysis_memo_stats().entry_versions_computed)
}

#[test]
fn row_replay_scope_changes_no_row_and_builds_the_oracle_once() {
    const SITES: usize = 16;
    let func = sites_func(SITES);

    let (unscoped, unscoped_builds) = replay_all(&func, SITES);
    // The fixture must reach the expensive half of the replay, or this pins nothing.
    assert!(
        unscoped.iter().all(Option::is_some),
        "every site is an owned-Vec scalar index row: {unscoped:?}"
    );
    // The defect: one whole-function oracle per replayed site.
    assert!(
        unscoped_builds >= SITES as u64,
        "unscoped replays rebuild the oracle per site: {unscoped_builds} builds for {SITES} sites"
    );

    let (scoped, scoped_builds) = {
        let _replay = row_replay_scope();
        replay_all(&func, SITES)
    };
    assert_eq!(scoped, unscoped, "the scope must change no row");
    assert_eq!(scoped_builds, 1, "one oracle for the whole batch");

    // The scope ends with its guard: a later unscoped replay is back to computing
    // (nothing memoized leaks out of the scope).
    let (after, after_builds) = replay_all(&func, 1);
    assert_eq!(after[0], unscoped[0]);
    assert_eq!(after_builds, 1);
}

/// The scope's cost is linear in the sites: doubling them does not add an oracle.
#[test]
fn row_replay_scope_oracle_builds_do_not_grow_with_the_sites() {
    for sites in [1usize, 8, 32] {
        let func = sites_func(sites);
        let _replay = row_replay_scope();
        let (rows, builds) = replay_all(&func, sites);
        assert!(rows.iter().all(Option::is_some));
        assert_eq!(builds, 1, "{sites} sites");
    }
}

/// Inside an enclosing METERED generation scope bound to another function, the
/// replay scope still returns the unscoped rows: memos are keyed on the function,
/// and the meter is off for the replay and restored afterwards. Every function
/// queried inside the scopes outlives them (the holder's contract).
#[test]
fn row_replay_scope_inside_an_enclosing_scope_changes_no_row() {
    const SITES: usize = 4;
    let func = sites_func(SITES);
    let other = sites_func(2);
    let (unscoped, _) = replay_all(&func, SITES);
    let (other_unscoped, _) = replay_all(&other, 2);
    let _outer = crate::gen_work_scope();
    assert_eq!(owned_vec_scalar_index_row(&other, BlockId(0)), other_unscoped[0]);
    let scoped = {
        let _replay = row_replay_scope();
        replay_all(&func, SITES).0
    };
    assert_eq!(scoped, unscoped);
    // The enclosing scope's function answers as before.
    assert_eq!(owned_vec_scalar_index_row(&other, BlockId(1)), other_unscoped[1]);
}
