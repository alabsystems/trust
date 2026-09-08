//! The EDGE-SET premises under the entry-sentinel tie — re-derived 2026-08-29,
//! when the whole-function quantifier and its "mint-side ⟹ consumer-side"
//! `debug_assert!` were retired in favor of the MINT GATE
//! (`full_graph_union_is_entry_only` in `pin_in_place_update_reads`).
//!
//! The division of labor is now: the mint gate owns "`#e` denotes the entry
//! value" (checked at the ONE mint site, over the UNWIND-INCLUSIVE map), and the
//! consumer-side clause of `entry_sentinel_tie_is_sound` owns "bare means entry
//! where the tie lands" (`version_token_at(..).is_some()`, promoted from
//! documented-dead to load-bearing). Both rest on EDGE-SET premises that live
//! here, because they need the crate internals the argument is stated over —
//! `v2_terminator_targets`, `full_graph_terminator_targets`, `StmtVersionCtx`,
//! `v2_path_def_fixpoint` — so no oracle is a reimplementation:
//!
//!  * step (1), unchanged: every edge `v2_terminator_targets` follows is also
//!    explored by `v2_path_def_fixpoint`, so a consumer's mandatory v2 in-edge
//!    is always intersected in. Guarded twice — edge-wise against the two
//!    production successor functions the fixpoint dispatches on, and coarsely
//!    against the real fixpoint's own reachability.
//!  * step (1'), NEW with the gate: every edge the fixpoint can transport a
//!    fact across is a predecessor edge of the full-graph entry-version map, so
//!    a `{e}`-exactly union at a mint block really means "no writer on ANY
//!    delivery path". Guarded edge-wise below; a future `Terminator` variant
//!    whose facts travel an edge the map ignores would re-open the mixed-shape
//!    false proof (`no_entry_sentinel_when_an_unwind_path_can_deliver_a_write`).
//!
//! HISTORY, kept because the corrections carry the lesson: this module
//! previously argued the consumer-side clause dead. The death certificate's
//! step (3) assumed the kill's gen-set key equals the pin's subject;
//! `split_subject_escape` retired that. The clause then survived on premise (0)
//! (gen-key == subject, enforced at the mint site) — until the quantifier
//! itself was retired, which INVERTED the relationship: the clause became the
//! LIVE refusal on the legitimate-mint/cleanup-consumer shape. Since
//! 2026-08-30 (unwind-inclusive `block_entry_versions`) that shape versions
//! its consumer read and the clause legitimately ADMITS there — the clause is
//! kept fail-closed for the step-cap/unreachable corners, and the shape's new
//! adjudication lives in
//! `the_tie_at_a_cleanup_consumer_is_sound_and_the_stale_sibling_degrades`.
//!
//! NOT because nothing else would notice: dropping the `otherwise` arm of
//! `discovered_clauses` reddens 60 lib tests, 57 of them pre-existing
//! (`path_definition_map_tests`, `path_guard_collapse_tests`, `float_range_tests`).
//! MEASURED 2026-08-28 — an earlier draft of this comment claimed the premise was
//! otherwise unwatched, and that was false. What these two add is DIRECTIONALITY:
//! they name the lost edge instead of leaving 57 unexplained failures, and they
//! catch a break originating on the `v2_terminator_targets` side, which the
//! pre-existing 57 do not distinguish.
//!
//! PLANTED AND WATCHED, both violations seen failing:
//!
//!  * drop `otherwise` from the `SwitchInt` arm of `Terminator::discovered_clauses`
//!    (`trust-types/src/model.rs`) and the two edge guards go red naming the exact
//!    lost edge (`guarded_signed_division bb0: v2 follows bb[1]`);
//!  * replace `v2_path_def_fixpoint`'s join INTERSECTION with a union and the
//!    unwind shapes go red carrying the danger shape itself to bb4
//!    (`Eq(Var("n"), Div(Var("n#e"), Int(3)))`) — which is what makes their
//!    "removed by the join, not by the mint-side clause" claim falsifiable.

use std::collections::HashSet;

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ClauseTarget, ConstValue, Formula, LocalDecl,
    Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VerifiableBody,
    VerifiableFunction,
};

use super::StmtVersionCtx;
use super::assert_refutation::v2_terminator_targets;
use super::path_defs::{full_graph_terminator_targets, v2_path_def_fixpoint};

/// Every `tests/data/*.json` body — the real-MIR corpus the argument was measured
/// over. Non-`.json` entries there are the Rust sources the fixtures were captured
/// from and carry no MIR.
fn corpus() -> Vec<(String, VerifiableFunction)> {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");
    let mut out = Vec::new();
    for entry in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("{dir} must be readable: {e}")) {
        let path = entry.expect("readable dir entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("MIR fixture {} must be readable: {e}", path.display()));
        let func: VerifiableFunction = serde_json::from_str(&text)
            .unwrap_or_else(|e| panic!("MIR fixture {} must deserialize: {e}", path.display()));
        out.push((path.file_stem().unwrap().to_string_lossy().into_owned(), func));
    }
    assert!(
        out.len() >= 50,
        "the corpus carried 57 bodies when the argument was measured; {} now — \
         re-measure before trusting the coverage claim",
        out.len()
    );
    out
}

/// The blocks `v2_path_def_fixpoint` enqueues from `terminator`, expressed in the
/// two production successor functions it dispatches on. Its `_` fallback arm routes
/// unknown variants through `unguarded_successors`, so this union is the enqueue set
/// for every variant, present and future.
fn fixpoint_enqueue_targets(terminator: &Terminator, source: BlockId) -> HashSet<BlockId> {
    let mut targets: HashSet<BlockId> = terminator.unguarded_successors().into_iter().collect();
    for clause in terminator.discovered_clauses(source) {
        if let ClauseTarget::Block(target) = clause.target {
            targets.insert(target);
        }
    }
    targets
}

/// Blocks reachable from bb0 across `v2_terminator_targets` edges alone.
fn v2_reachable(func: &VerifiableFunction) -> HashSet<BlockId> {
    let mut seen = HashSet::new();
    let mut stack = vec![BlockId(0)];
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(block) = func.body.blocks.iter().find(|b| b.id == id) else { continue };
        stack.extend(v2_terminator_targets(&block.terminator));
    }
    seen
}

/// STEP (1), edge-wise. Every successor `block_entry_versions` builds a predecessor
/// link from is one `v2_path_def_fixpoint` also enqueues, so `result[C]` is the
/// intersection over at least C's v2 in-edges.
#[test]
fn every_v2_edge_is_also_a_fixpoint_edge() {
    for (name, func) in corpus().into_iter().chain(unwind_shapes()) {
        for block in &func.body.blocks {
            let fixpoint = fixpoint_enqueue_targets(&block.terminator, block.id);
            let mut missed: Vec<usize> = v2_terminator_targets(&block.terminator)
                .into_iter()
                .filter(|t| !fixpoint.contains(t))
                .map(|t| t.0)
                .collect();
            missed.sort_unstable();
            missed.dedup();
            assert!(
                missed.is_empty(),
                "{name} {:?}: v2 follows bb{missed:?}, which the fixpoint never enqueues. \
                 The consumer-side clause of `entry_sentinel_tie_is_sound` is LIVE again: \
                 a `base#e` can now reach a consumer across an edge whose outflow is \
                 never intersected in.",
                block.id
            );
        }
    }
}

/// STEP (1'). Every edge the fixpoint can transport a fact across must be a
/// predecessor edge of the FULL-GRAPH entry-version map the `#e` mint gate
/// consults. If a future `Terminator` variant's facts travel an edge the map
/// ignores, a mint block's `{e}`-exactly union stops meaning "no writer on any
/// delivery path" and the mixed-shape false proof re-opens.
///
/// PLANTED AND WATCHED: drop the `unguarded_successors` union from
/// `full_graph_terminator_targets` and this goes red naming the lost unwind
/// edge on all three unwind shapes.
#[test]
fn every_fixpoint_edge_is_a_full_graph_map_edge() {
    for (name, func) in corpus().into_iter().chain(unwind_shapes()) {
        for block in &func.body.blocks {
            let full: HashSet<BlockId> =
                full_graph_terminator_targets(&block.terminator, block.id).into_iter().collect();
            let mut missed: Vec<usize> = fixpoint_enqueue_targets(&block.terminator, block.id)
                .into_iter()
                .filter(|t| !full.contains(t))
                .map(|t| t.0)
                .collect();
            missed.sort_unstable();
            missed.dedup();
            assert!(
                missed.is_empty(),
                "{name} {:?}: the fixpoint can deliver facts to bb{missed:?}, which \
                 the full-graph entry-version map has no predecessor edge for — \
                 the `#e` mint gate's `{{e}}`-union no longer proves \
                 entry-denotation.",
                block.id
            );
        }
    }
}

/// STEP (1) again, against the REAL fixpoint rather than a reconstruction of its
/// dispatch. Coarser — reachability, not per-edge — but it is the only check that
/// runs the function the argument is actually about.
#[test]
fn the_fixpoint_reaches_every_v2_reachable_block() {
    for (name, func) in corpus().into_iter().chain(unwind_shapes()) {
        if func.body.blocks.is_empty() {
            continue;
        }
        let result = v2_path_def_fixpoint(&func, &Default::default());
        assert!(
            !result.is_empty(),
            "{name}: the fixpoint returned its empty step-budget fallback, so this \
             guard would pass vacuously"
        );
        for id in v2_reachable(&func) {
            if id.0 >= func.body.blocks.len() {
                continue; // v2 target past the end; the fixpoint skips it too
            }
            assert!(
                result.contains_key(&id),
                "{name}: {id:?} is v2-reachable from bb0 but the fixpoint never visited it"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// The three unwind shapes: NEGATIVE CONTROLS for the consumer-side clause.
// ---------------------------------------------------------------------------

fn u32_local(index: usize, name: &str) -> LocalDecl {
    LocalDecl { index, ty: Ty::u32(), name: Some(name.into()) }
}

/// bb0 switches on `c` to the WRITER bb1 (`n = n / 3`, whose read renders bare and
/// so is pinned — bb1's unwind-inclusive union is `{e}`, so the mint gate still
/// stamps `n#e`) or to bb2, which never writes `n` and gotos the consumer bb4.
/// bb1 reaches bb4 ONLY across its unwind edge.
///
/// The historical role: this shape could not isolate the (then believed dead)
/// consumer-side clause — every block has a v2 in-edge, so the retired
/// whole-function quantifier passed, bb4 renders `n` bare, and yet the pinned def
/// never arrives, because bb4's v2 in-edge from bb2 carries no `n` fact and the
/// fixpoint intersects it against the unwind delivery. Post-narrowing it stays as
/// the negative control for THAT join-intersection premise. Only the terminator
/// varies, so all three unwind-bearing terminators are covered by one shape.
fn unwind_only_writer(label: &str, terminator: Terminator) -> VerifiableFunction {
    VerifiableFunction {
        name: label.to_string(),
        def_path: format!("tie_subsumption::{label}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: Ty::u32(),
            locals: vec![
                u32_local(0, "__ret"),
                u32_local(1, "n"),
                u32_local(2, "c"),
                LocalDecl { index: 3, ty: Ty::bool_ty(), name: Some("ok".into()) },
                u32_local(4, "out"),
                u32_local(5, "tmp"),
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(3, 32)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(10, 32)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Constant(ConstValue::Uint(100, 32)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn unwind_shapes() -> Vec<(String, VerifiableFunction)> {
    let cleanup = UnwindEdge::Cleanup(BlockId(4));
    vec![
        (
            "unwind_assert".to_string(),
            unwind_only_writer(
                "unwind_assert",
                Terminator::Assert {
                    cond: Operand::Copy(Place::local(3)),
                    expected: true,
                    msg: AssertMessage::Custom("bound".into()),
                    target: BlockId(3),
                    span: SourceSpan::default(),
                    unwind: cleanup.clone(),
                },
            ),
        ),
        (
            "unwind_drop".to_string(),
            unwind_only_writer(
                "unwind_drop",
                Terminator::Drop {
                    place: Place::local(5),
                    target: BlockId(3),
                    unwind: cleanup.clone(),
                    span: SourceSpan::default(),
                },
            ),
        ),
        (
            "unwind_call".to_string(),
            unwind_only_writer(
                "unwind_call",
                Terminator::Call {
                    func: "ext::sink".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(5),
                    target: Some(BlockId(3)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: cleanup,
                    callee_identity: None,
                },
            ),
        ),
    ]
}

fn mentions_entry_sentinel(f: &Formula) -> bool {
    f.free_variables().iter().any(|v| v.as_str() == "n#e")
}

/// The negative result, asserted rather than described: on all three unwind
/// terminators the mint is gate-ADMITTED (`n#e` genuinely denotes entry at bb1)
/// and the pinned def is gone anyway, removed by the fixpoint's JOIN
/// INTERSECTION before any tie question arises. (Re-adjudicated 2026-08-30:
/// the consumer used to render `n` bare — the unwind-blind rendering — which
/// made the consumer-side clause the only refusal left; the unwind-inclusive
/// entry map now versions the cleanup consumer's read, adding a second,
/// earlier severance. The join-intersection loss is what remains isolated.)
///
/// Each precondition is asserted so the fixture cannot pass for the wrong reason:
/// without them "no `#e` at bb4" is equally consistent with the mint gate having
/// refused, which is exactly the confusion this file exists to end.
#[test]
fn the_unwind_shapes_lose_the_pinned_def_to_the_join_not_to_the_mint_side_clause() {
    for (label, func) in unwind_shapes() {
        let sv = StmtVersionCtx::build(&func);

        assert!(
            func.body.blocks.iter().all(|b| sv.entry_map_covers(b.id, "n")),
            "{label}: every block must be v2-covered — the RETIRED whole-function \
             quantifier would have passed here, which is what made this shape \
             unable to isolate the consumer-side clause; if coverage changes, \
             the shape no longer records what it was measured to record"
        );
        assert!(
            sv.full_graph_union_is_entry_only(BlockId(1), "n"),
            "{label}: the mint gate must ADMIT bb1's pin (its unwind-inclusive \
             union is the entry seed), or the `n#e` asserted at bb3 below is \
             minted by nothing"
        );
        // RE-ADJUDICATED 2026-08-30 (dropped-def write-visibility fix): bb4 used
        // to render `n` BARE because `block_entry_versions` had no unwind arm —
        // the exact rendering that let a rename-exempt bare fact unify across a
        // write on the unwind shape (`tests/dropped_def_write_visibility.rs`).
        // With the unwind-inclusive predecessor relation, the cleanup-only
        // block versions its reads like any other, so the consumer-side clause
        // is no longer the lone refusal on this shape — the versioned read
        // severs the unification before the clause is even consulted. What this
        // fixture still isolates is the JOIN-INTERSECTION loss below.
        assert!(
            sv.version_token_at(&func, BlockId(4), 1, "n").is_some(),
            "{label}: bb4 is reached across bb1's cleanup edge downstream of the \
             write, so its read of `n` must carry bb1's write token — bare here \
             would resurrect the unwind-blind rendering"
        );

        let defs = v2_path_def_fixpoint(&func, &Default::default());
        assert!(
            defs.get(&BlockId(3)).is_some_and(|fs| fs.iter().any(mentions_entry_sentinel)),
            "{label}: the pin must actually mint `n#e` on the writer's normal edge, \
             or the absence at bb4 is vacuous; bb3 carried {:?}",
            defs.get(&BlockId(3))
        );
        assert!(
            !defs.get(&BlockId(4)).is_some_and(|fs| fs.iter().any(mentions_entry_sentinel)),
            "{label}: bb4 received the pinned def across the unwind edge — the join \
             intersection against bb2's `n`-free outflow no longer removes it, and \
             the consumer-side clause has become load-bearing: {:?}",
            defs.get(&BlockId(4))
        );

        // Laundering control: the refusal costs a hypothesis, never the obligation.
        let vcs = crate::generate_vcs(&func);
        assert!(
            !vcs.iter().any(|vc| mentions_entry_sentinel(&vc.formula)),
            "{label}: no shipped VC may carry `n#e` here"
        );
        assert!(!vcs.is_empty(), "{label}: bb4's `100 / n` must still raise an obligation");
    }
}
