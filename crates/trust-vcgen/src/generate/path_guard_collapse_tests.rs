//! ANTI-VACUITY guards for the two path-guard COLLAPSE repairs.
//!
//! `v2_build_path_guard_map` degrades in two ways, and each one leaves a block
//! with a single UNGUARDED path — no reachability condition at all:
//!
//!  * MODE 1, `MAX_PATHS_PER_BLOCK`: the block itself was reached by too many
//!    routes;
//!  * MODE 2, the global step budget: EVERY block of the function at once.
//!
//! `v2_reachability_for_collapsed` answers both with the weakest still-valid
//! condition (the disjunction of the block's in-edge guards), and the COLLAPSE
//! INVARIANT in `generate_v2_safety_vcs` is what turns that answer — or its
//! absence — into a verdict. The regression tests that matter are in
//! `tests/path_guard_collapse_repair_real_mir.rs` — they assert real extracted
//! MIR is not falsely refuted. This module asserts the property those tests
//! DEPEND ON and cannot see: that the fixtures still take the collapse they were
//! captured for.
//!
//! Both collapses trigger on SIZE. A change to the cap, to the step budget, or
//! to the MIR rustc lowers a fixture into can quietly move a fixture off the
//! path it guards, and the refutation test would then pass for a reason that has
//! nothing to do with the repair. That is the exact failure mode a saturation
//! guard cannot afford, so the mode is asserted by name here.

use trust_types::{BlockId, Terminator, VerifiableFunction};

use super::{PathGuardCollapse, ReachSummary, v2_analyze_path_guards};

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/data/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("MIR fixture {path} must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("MIR fixture {path} must deserialize: {e}"))
}

/// MODE 2 — the global step budget, on a NON-coroutine body. This return path is
/// not coroutine-specific: it collapses every function whose path walk outruns
/// the budget, so the plain `fn` case is the one that pins the scope.
///
/// The arithmetic that puts it on this side of the cliff is asserted in
/// `walk_arithmetic`, not described here.
#[test]
fn the_non_async_budget_fixture_still_trips_the_step_budget() {
    let func = load("path_budget_nonasync_merged_unreachable");
    let collapse = v2_analyze_path_guards(&func).collapse;
    assert_eq!(
        collapse,
        PathGuardCollapse::BudgetTripped,
        "the fixture's whole value is that its path walk outruns the STEP BUDGET. \
         If this drifts, re-capture it — the refutation guard in \
         tests/path_guard_collapse_repair_real_mir.rs would otherwise pass vacuously"
    );
}

/// MODE 2 on a recognized `async fn` resume body — the shape that also carries a
/// `ResumedAfter*` sentinel, i.e. the D1b row class.
#[test]
fn the_async_budget_fixture_still_trips_the_step_budget() {
    let func = load("path_budget_async_sentinel");
    let collapse = v2_analyze_path_guards(&func).collapse;
    assert_eq!(
        collapse,
        PathGuardCollapse::BudgetTripped,
        "the fixture's whole value is that its path walk outruns the STEP BUDGET"
    );
    assert!(
        trust_types::coroutine_resume_state_contract(&func.body).is_some(),
        "and that it is still a RECOGNIZED resume body"
    );
}

/// MODE 1 — the per-block cap, on the fixture the earlier repair was written
/// for. It must still be mode 1 and NOT mode 2, or the two repairs are no longer
/// covered separately.
#[test]
fn the_saturated_fixture_still_takes_the_per_block_cap_and_not_the_budget() {
    let func = load("coroutine_resume_saturated_unreachable");
    let collapse = v2_analyze_path_guards(&func).collapse;
    assert_eq!(
        collapse,
        PathGuardCollapse::SaturatedBlocks,
        "the fixture must still overflow MAX_PATHS_PER_BLOCK without reaching the \
         step budget; if it now trips the budget the two modes share one fixture \
         and mode 1 is untested"
    );
}

/// The control: a body small enough to take NEITHER collapse. Without it,
/// "asserts the mode" would be satisfied by a reporter that always says the same
/// thing.
#[test]
fn the_small_fixture_takes_no_collapse_at_all() {
    for name in ["coroutine_resume_zero_await_widen", "coroutine_resume_merged_unreachable"] {
        let func = load(name);
        let collapse = v2_analyze_path_guards(&func).collapse;
        assert_eq!(collapse, PathGuardCollapse::None, "{name} must keep its full path map");
    }
}

/// THE WALK'S ARITHMETIC, as assertions rather than as prose.
///
/// Which collapse a body takes is decided by three numbers — its block count,
/// the step cap derived from it, and how many queue pops the walk makes. The
/// last two are not on the `PathGuardAnalysis` surface, so a comment quoting
/// them is never re-checked. [`walk`] re-derives all three by re-walking the CFG
/// exactly as `v2_analyze_path_guards` does.
///
/// A reimplementation proves nothing on its own, so it is used DIFFERENTIALLY:
/// every test below asserts the prediction against the real analysis, on the
/// fixtures and on a synthetic family that straddles the budget cliff. The
/// `MAX_PATHS_PER_BLOCK` and step-cap constants are deliberately COPIES rather
/// than imports — perturbing either constant in `safety.rs` then makes the two
/// disagree, which is the failure this file is for.
mod walk_arithmetic {
    use std::collections::{HashMap, HashSet, VecDeque};

    use trust_types::VerifiableFunction;

    use super::{BlockId, PathGuardCollapse, Terminator, load, v2_analyze_path_guards};

    /// A copy of `safety.rs`'s per-block path cap. See the module doc: this is a
    /// copy on purpose.
    const MAX_PATHS_PER_BLOCK: usize = 64;

    pub(super) struct Walk {
        pub(super) blocks: usize,
        pub(super) cap: usize,
        pub(super) steps: usize,
        pub(super) pops: HashMap<BlockId, usize>,
        pub(super) collapse: PathGuardCollapse,
    }

    /// Re-walk `func` the way `v2_analyze_path_guards` does: BFS from `BlockId(0)`
    /// carrying the visited-block list, one step per POP (counted before the
    /// budget check, so a tripped walk reports `cap + 1`), a per-block path
    /// counter that saturates at [`MAX_PATHS_PER_BLOCK`], and both successor
    /// enumerations.
    pub(super) fn walk(func: &VerifiableFunction) -> Walk {
        let n = func.body.blocks.len();
        let cap = n.saturating_mul(n).saturating_add(n).saturating_mul(16).saturating_add(4096);
        let mut pops: HashMap<BlockId, usize> = HashMap::new();
        if n == 0 {
            return Walk { blocks: 0, cap, steps: 0, pops, collapse: PathGuardCollapse::None };
        }
        let mut steps = 0usize;
        let mut saturated: HashSet<BlockId> = HashSet::new();
        let mut paths: HashMap<BlockId, usize> = HashMap::new();
        let mut queue: VecDeque<(BlockId, Vec<BlockId>)> =
            VecDeque::from([(BlockId(0), Vec::new())]);
        while let Some((block_id, mut path_blocks)) = queue.pop_front() {
            steps += 1;
            *pops.entry(block_id).or_default() += 1;
            if steps > cap {
                return Walk {
                    blocks: n,
                    cap,
                    steps,
                    pops,
                    collapse: PathGuardCollapse::BudgetTripped,
                };
            }
            if block_id.0 >= n || path_blocks.contains(&block_id) {
                continue;
            }
            path_blocks.push(block_id);
            let slot = paths.entry(block_id).or_insert(0usize);
            if saturated.contains(&block_id) {
                // already weakened to one unguarded path
            } else if *slot < MAX_PATHS_PER_BLOCK {
                *slot += 1;
            } else {
                *slot = 1;
                saturated.insert(block_id);
            }
            let block = &func.body.blocks[block_id.0];
            for guarded in block.terminator.discovered_clauses(block_id) {
                if let trust_types::ClauseTarget::Block(target) = guarded.target {
                    queue.push_back((target, path_blocks.clone()));
                }
            }
            for target in block.terminator.unguarded_successors() {
                queue.push_back((target, path_blocks.clone()));
            }
        }
        let collapse = if saturated.is_empty() {
            PathGuardCollapse::None
        } else {
            PathGuardCollapse::SaturatedBlocks
        };
        Walk { blocks: n, cap, steps, pops, collapse }
    }

    /// A chain of `stages` two-way branches that all reconverge, plus a `Return`
    /// and an orphan `Unreachable`. Every stage doubles the path count, so the
    /// walk's pop count doubles per stage while the cap grows only quadratically
    /// in the block count — one extra stage is what carries a body across the
    /// budget cliff.
    fn chain(stages: usize) -> VerifiableFunction {
        super::the_collapse_invariant::budget_tripping_chain_with_orphan(stages)
    }

    /// THE FIXTURES' NUMBERS. Each row is `(blocks, cap, steps, mode)`, and the
    /// mode is cross-checked against the real analysis so the reimplementation
    /// cannot drift away from it silently.
    #[test]
    fn every_fixture_sits_where_the_walk_arithmetic_says_it_does() {
        let expected: &[(&str, usize, usize, usize, PathGuardCollapse)] = &[
            (
                "path_budget_nonasync_merged_unreachable",
                57,
                56992,
                56993,
                PathGuardCollapse::BudgetTripped,
            ),
            ("path_budget_async_sentinel", 43, 34368, 34369, PathGuardCollapse::BudgetTripped),
            (
                "coroutine_resume_saturated_unreachable",
                25,
                14496,
                640,
                PathGuardCollapse::SaturatedBlocks,
            ),
            ("coroutine_resume_merged_unreachable", 10, 5856, 14, PathGuardCollapse::None),
            ("coroutine_resume_zero_await_widen", 7, 4992, 9, PathGuardCollapse::None),
            (
                "switch_arms_shared_target_mul_overflow",
                5,
                4576,
                198,
                PathGuardCollapse::SaturatedBlocks,
            ),
        ];
        for (name, blocks, cap, steps, mode) in expected {
            let func = load(name);
            let w = walk(&func);
            assert_eq!(
                (w.blocks, w.cap, w.steps, w.collapse),
                (*blocks, *cap, *steps, *mode),
                "{name}: the fixture moved. Re-capture it and re-pin these numbers — \
                 the regression guards that use it assume the collapse it takes"
            );
            assert_eq!(
                v2_analyze_path_guards(&func).collapse,
                w.collapse,
                "{name}: the real analysis and this re-walk disagree, so one of them \
                 changed and the numbers above describe nothing"
            );
        }
    }

    /// A TRIPPED walk stops at exactly one step past its cap — the step is
    /// counted before the budget check — which is why the two budget fixtures'
    /// `steps` values above are `cap + 1` rather than a count of their own.
    #[test]
    fn a_tripped_walk_stops_one_step_past_the_cap() {
        for name in ["path_budget_nonasync_merged_unreachable", "path_budget_async_sentinel"] {
            let w = walk(&load(name));
            assert_eq!(w.collapse, PathGuardCollapse::BudgetTripped, "{name}");
            assert_eq!(w.steps, w.cap + 1, "{name}");
        }
        for name in
            ["coroutine_resume_saturated_unreachable", "coroutine_resume_merged_unreachable"]
        {
            let w = walk(&load(name));
            assert_ne!(w.collapse, PathGuardCollapse::BudgetTripped, "{name}");
            assert!(w.steps <= w.cap, "{name}: {} vs {}", w.steps, w.cap);
        }
    }

    /// MODE 1's cause, counted. What saturates a block is the number of ROUTES
    /// from the entry that reach it — one queue pop each — not its in-degree, and
    /// on this fixture that count exceeds [`MAX_PATHS_PER_BLOCK`] many times
    /// over.
    #[test]
    fn the_saturated_fixtures_merged_unreachable_is_popped_128_times() {
        let func = load("coroutine_resume_saturated_unreachable");
        let merged: Vec<BlockId> = func
            .body
            .blocks
            .iter()
            .filter(|b| matches!(b.terminator, Terminator::Unreachable))
            .map(|b| b.id)
            .collect();
        assert_eq!(merged.len(), 1, "the fixture's value is its ONE merged block: {merged:?}");
        let w = walk(&func);
        assert_eq!(
            w.pops.get(&merged[0]).copied(),
            Some(128),
            "the seven sequential matches route 2^7 routes into it; that count, not \
             its in-degree, is what overflows MAX_PATHS_PER_BLOCK"
        );
        assert!(128 > MAX_PATHS_PER_BLOCK);
        assert_eq!(v2_analyze_path_guards(&func).collapse, PathGuardCollapse::SaturatedBlocks);
    }

    /// THE CLIFF, one step wide. A chain of 11 branch stages saturates blocks but
    /// stays inside its budget; 12 stages trips it. Both numbers come from the
    /// COPIED constants above, so perturbing either constant in `safety.rs` moves
    /// the real analysis off this prediction and fails the cross-check.
    #[test]
    fn one_more_stage_moves_a_body_from_mode_1_to_mode_2() {
        let below = walk(&chain(11));
        assert_eq!(
            (below.blocks, below.cap, below.steps, below.collapse),
            (13, 7008, 4095, PathGuardCollapse::SaturatedBlocks)
        );
        let above = walk(&chain(12));
        assert_eq!(
            (above.blocks, above.cap, above.steps, above.collapse),
            (14, 7456, 7457, PathGuardCollapse::BudgetTripped)
        );
        for stages in 8..=14usize {
            let func = chain(stages);
            assert_eq!(
                v2_analyze_path_guards(&func).collapse,
                walk(&func).collapse,
                "{stages} stages: the re-walk and the real analysis disagree, so a \
                 constant or the walk itself moved"
            );
        }
    }
}

/// THE REPAIR ITSELF, read off the analysis rather than inferred from a verdict:
/// in the budget-tripped body every `Unreachable` block that has only guarded
/// in-edges is reported DEGRADED and carries a real in-edge disjunction. The
/// PATH MAP is deliberately left alone (that is what keeps every other consumer
/// of `v2_build_path_guard_map` byte-identical); the condition rides in
/// `reachability`, and `generate_v2_safety_vcs` splices it onto exactly the rows
/// whose entire meaning is the path condition.
#[test]
fn the_budget_trip_restores_a_reachability_condition_on_the_unreachable_blocks() {
    for name in ["path_budget_nonasync_merged_unreachable", "path_budget_async_sentinel"] {
        let func = load(name);
        let analysis = v2_analyze_path_guards(&func);
        assert_eq!(analysis.collapse, PathGuardCollapse::BudgetTripped, "{name}");
        let unreachable: Vec<_> = func
            .body
            .blocks
            .iter()
            .filter(|b| matches!(b.terminator, Terminator::Unreachable))
            .map(|b| b.id)
            .collect();
        assert!(!unreachable.is_empty(), "{name} must have an `Unreachable` block");
        for id in unreachable {
            assert!(
                analysis.degraded.contains(&id),
                "{name}: bb{} must be reported degraded — the budget trip collapses \
                 every block",
                id.0
            );
            let Some(ReachSummary::Guards(edges)) = analysis.reachability.get(&id) else {
                panic!(
                    "{name}: bb{} must carry a real in-edge disjunction; without one its \
                     `Bool(true)` row has no reachability condition at all: {:?}",
                    id.0,
                    analysis.reachability.get(&id)
                );
            };
            assert!(!edges.is_empty(), "{name}: bb{} disjunction must be non-empty", id.0);
        }
    }
}

/// THE INVARIANT, end to end, on the two shapes that make it necessary and the
/// two that must not trigger it.
///
/// A block is built with `arms` guarded in-edges into an `Unreachable` — the
/// `Bool(true)`-bodied row whose ENTIRE meaning is its path condition — plus
/// whatever extra edges the case needs.
mod the_collapse_invariant {
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Ty, VcKind, VerifiableBody,
    };

    use super::*;

    /// bb0 switches `arms` ways into bb1 (`Unreachable`), otherwise bb2
    /// (`Return`). `arms > MAX_PATHS_PER_BLOCK` saturates bb1.
    fn unreachable_target(arms: u128) -> VerifiableFunction {
        VerifiableFunction {
            name: "collapse_invariant".to_string(),
            def_path: "collapse_invariant".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: (0..arms).map(|v| (v, BlockId(1))).collect(),
                            otherwise: BlockId(2),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Unreachable,
                    },
                    BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// The same shape, but the collapsed target is a PANIC CALL rather than
    /// `Terminator::Unreachable` — the `v2_build_terminator_vc` arm that emits
    /// the identical `Formula::Bool(true)` core under a `VcKind::Assertion`.
    ///
    /// Built by hand so the panic call sits DIRECTLY behind the guarded in-edges
    /// and the restore lane is exercised on a non-`Unreachable` row kind.
    fn panic_call_target(arms: u128) -> VerifiableFunction {
        let mut func = unreachable_target(arms);
        func.name = "collapse_invariant_panic".to_string();
        func.def_path = "collapse_invariant_panic".to_string();
        func.body.blocks[1].terminator = Terminator::Call {
            unwind: trust_types::UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "core::panicking::panic_fmt".to_string(),
            args: vec![],
            dest: Place::local(0),
            target: None,
            span: SourceSpan::default(),
            atomic: None,
            callee_identity: None,
        };
        func
    }

    /// A `stages`-long chain of two-way branches that all reconverge, plus a
    /// FINAL ORPHAN `Unreachable` block nothing branches to.
    ///
    /// The chain doubles the path count per stage, so the walk outruns the
    /// global step budget and takes COLLAPSE MODE 2, which degrades every block
    /// of the function — including the orphan. That is the only way to get a
    /// DEGRADED block with no in-edge, i.e. the one input that still makes the
    /// reachability summary genuinely `Unavailable` now that there is no size
    /// budget.
    pub(super) fn budget_tripping_chain_with_orphan(stages: usize) -> VerifiableFunction {
        let mut blocks: Vec<BasicBlock> = (0..stages)
            .map(|i| BasicBlock {
                id: BlockId(i),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(1)),
                    targets: vec![(0, BlockId(i + 1))],
                    otherwise: BlockId(i + 1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            })
            .collect();
        blocks.push(BasicBlock {
            id: BlockId(stages),
            stmts: vec![],
            terminator: Terminator::Return,
        });
        blocks.push(BasicBlock {
            id: BlockId(stages + 1),
            stmts: vec![],
            terminator: Terminator::Unreachable,
        });
        VerifiableFunction {
            name: "collapse_invariant_orphan".to_string(),
            def_path: "collapse_invariant_orphan".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks,
                arg_count: 1,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn kinds(func: &VerifiableFunction) -> Vec<VcKind> {
        super::super::generate_v2_safety_vcs(func).into_iter().map(|vc| vc.kind).collect()
    }

    fn nodes(f: &trust_types::Formula) -> usize {
        1 + f.children().into_iter().map(nodes).sum::<usize>()
    }

    fn is_degraded_decline(kind: &VcKind) -> bool {
        matches!(kind, VcKind::UnsupportedMir { kind, .. } if kind == "PathConditionDegraded")
    }

    /// A sound in-edge disjunction exists, so the row keeps its `Unreachable`
    /// kind and is decided by the restored condition — no decline.
    #[test]
    fn a_summarisable_collapsed_block_keeps_its_unreachable_row() {
        let kinds = kinds(&unreachable_target(65));
        assert!(
            kinds.iter().any(|k| matches!(k, VcKind::Unreachable)),
            "the row must survive as a real obligation: {kinds:?}"
        );
        assert!(
            !kinds.iter().any(is_degraded_decline),
            "nothing to decline — the disjunction is available: {kinds:?}"
        );
    }

    /// THERE IS NO IN-EDGE BUDGET, and this is the test that used to say there
    /// was: an earlier `MAX_RESTORED_IN_EDGE_GUARDS` cap made the summary ABSENT
    /// past a fixed in-degree, and an absent summary declines.
    ///
    /// A decline is for a row that is UNDECIDABLE. A large disjunction with a
    /// witness is not undecidable, it is merely large, and the two must not be
    /// confused: declining on SIZE demotes a genuinely reachable trap to Unknown,
    /// which is a real bug shipping undetected, at a threshold nobody can
    /// justify. Absence of a summary is still a decline — see
    /// `a_degraded_block_with_no_in_edge_at_all_still_declines`, which is now the
    /// ONLY way to reach it.
    #[test]
    fn past_the_old_in_edge_budget_the_tautology_row_still_refutes() {
        let summarised = kinds(&unreachable_target(65));
        for arms in [513u128, 600, 1024, 4096] {
            let kinds = kinds(&unreachable_target(arms));
            assert!(
                kinds.iter().any(|k| matches!(k, VcKind::Unreachable)),
                "in-degree {arms}: the row must stay a refutable obligation — a big \
                 disjunction is inconvenient, not undecidable: {kinds:?}"
            );
            assert!(
                !kinds.iter().any(is_degraded_decline),
                "in-degree {arms}: the disjunction IS available, so there is nothing \
                 to decline; declining here demotes a genuinely reachable trap to \
                 Unknown: {kinds:?}"
            );
            assert_eq!(
                kinds.len(),
                summarised.len(),
                "in-degree {arms}: the invariant CONDITIONS a row; it never adds or \
                 removes one"
            );
        }
    }

    /// And the restored condition really is the block's whole in-edge set at
    /// those sizes — not a truncated prefix, which would be a silently weaker
    /// (still sound, but less useful) condition.
    #[test]
    fn the_restored_disjunction_is_complete_at_every_in_degree() {
        for arms in [65usize, 513, 1024, 4096] {
            let func = unreachable_target(arms as u128);
            let analysis = v2_analyze_path_guards(&func);
            assert!(
                analysis.degraded.contains(&BlockId(1)),
                "in-degree {arms}: bb1 must still be degraded or this proves nothing"
            );
            match analysis.reachability.get(&BlockId(1)) {
                Some(ReachSummary::Guards(edges)) => assert_eq!(
                    edges.len(),
                    arms,
                    "in-degree {arms}: every in-edge must be in the disjunction"
                ),
                other => panic!("in-degree {arms}: expected Guards, got {other:?}"),
            }
        }
    }

    /// ONE ROW KIND WIDER. The content-free class is not two special rows:
    /// `v2_build_terminator_vc` hands the same `Formula::Bool(true)` to every
    /// panic SITE it recognises, whatever `VcKind` it gives the row. A reachable
    /// panic behind N guarded in-edges is therefore the SAME defect as the
    /// `unreachable!()` one, and a size cap would lose it for the same reason.
    #[test]
    fn a_collapsed_panic_call_is_carried_at_every_in_degree_too() {
        for arms in [65u128, 513, 1024] {
            let func = panic_call_target(arms);
            let analysis = v2_analyze_path_guards(&func);
            assert!(
                analysis.degraded.contains(&BlockId(1)),
                "in-degree {arms}: bb1 must be degraded or this proves nothing"
            );
            match analysis.reachability.get(&BlockId(1)) {
                Some(ReachSummary::Guards(edges)) => assert_eq!(edges.len(), arms as usize),
                other => panic!("in-degree {arms}: expected Guards, got {other:?}"),
            }
            let vcs = super::super::generate_v2_safety_vcs(&func);
            let row = vcs
                .iter()
                .find(|vc| matches!(&vc.kind, VcKind::Assertion { .. }))
                .unwrap_or_else(|| {
                    panic!(
                        "in-degree {arms}: the panic site must still carry an Assertion \
                         row: {:?}",
                        vcs.iter().map(|vc| format!("{:?}", vc.kind)).collect::<Vec<_>>()
                    )
                });
            assert!(
                !vcs.iter().any(|vc| is_degraded_decline(&vc.kind)),
                "in-degree {arms}: a reachable panic behind a real in-edge disjunction \
                 must not be declined: {:?}",
                vcs.iter().map(|vc| format!("{:?}", vc.kind)).collect::<Vec<_>>()
            );
            // The restore actually happened: the row's formula carries one
            // disjunct per in-edge rather than the bare `Bool(true)` core.
            let size = nodes(&row.formula);
            assert!(
                size > arms as usize,
                "in-degree {arms}: the restored condition must be ON the row \
                 (got {size} nodes)"
            );
        }
    }

    /// THE DECLINE LANE, still live and now reached ONLY by genuine ABSENCE: a
    /// block that no in-edge points at. `v2_build_in_edge_guard_map` leaves such
    /// a block out of the map entirely (it must never be recorded as the EMPTY
    /// disjunction, which is `false` and would vacuously prove every row), so the
    /// summary is `Unavailable` and the content-free row declines — still
    /// EMITTED, as an explicit `PathConditionDegraded` proof gap, because an
    /// obligation that vanishes is the other way to ship a bug.
    #[test]
    fn a_degraded_block_with_no_in_edge_at_all_still_declines() {
        let func = budget_tripping_chain_with_orphan(25);
        let analysis = v2_analyze_path_guards(&func);
        // ANTI-VACUITY: the orphan is only DEGRADED because mode 2 degrades
        // every block at once. If the walk stopped tripping the budget this test
        // would pass for a reason unrelated to what it guards.
        assert_eq!(
            analysis.collapse,
            PathGuardCollapse::BudgetTripped,
            "the chain's whole value is that its path walk outruns the STEP BUDGET"
        );
        let orphan = BlockId(func.body.blocks.len() - 1);
        assert!(analysis.degraded.contains(&orphan));
        assert!(
            matches!(analysis.reachability.get(&orphan), Some(ReachSummary::Unavailable)),
            "a block with no in-edge has no disjunction at all: {:?}",
            analysis.reachability.get(&orphan)
        );
        let kinds = kinds(&func);
        assert!(
            kinds.iter().any(is_degraded_decline),
            "absent reachability information is not evidence of reachability: {kinds:?}"
        );
    }

    /// NEVER BLESS UB. An UNGUARDED in-edge means the disjunction is `true` —
    /// POSITIVE information that the block is reachable, not absence — so the
    /// row must stay a refutable `Unreachable`, never a decline.
    #[test]
    fn an_unguarded_in_edge_is_information_and_must_not_decline() {
        let mut func = unreachable_target(65);
        func.body.blocks.push(BasicBlock {
            id: BlockId(3),
            stmts: vec![],
            terminator: Terminator::Goto(BlockId(1)),
        });
        let kinds = kinds(&func);
        assert!(
            kinds.iter().any(|k| matches!(k, VcKind::Unreachable)),
            "a block a `Goto` reaches unconditionally is genuinely reachable; \
             declining here would bless real UB: {kinds:?}"
        );
        assert!(!kinds.iter().any(is_degraded_decline), "{kinds:?}");
    }

    /// SCOPE. The invariant touches ONLY rows with no violation condition of
    /// their own. `v2_violation_is_content_free` says so structurally, and this
    /// pins the two spellings that exist today plus the negative cases.
    #[test]
    fn content_free_is_recognised_structurally_and_narrowly() {
        use trust_types::{Formula, Sort};

        use super::super::v2_violation_is_content_free;
        let var = || Formula::Var("x".into(), Sort::Int);
        // `Terminator::Unreachable` / the `unreachable!()` recognizers.
        assert!(v2_violation_is_content_free(&Formula::Bool(true)));
        // rustc's `assert(const false, ResumedAfter*)` sentinel.
        assert!(v2_violation_is_content_free(&Formula::Not(Box::new(Formula::Bool(false)))));
        // A DEFINITIONAL prefix is NOT looked through, deliberately: looking
        // through it would misread a row whose real violation condition IS an
        // equality — `DivisionByZero` is `Eq(d, 0)` — as a row with nothing to
        // say, and misclassifying toward "content-free" is the defect class that
        // loses real bugs.
        assert!(!v2_violation_is_content_free(&Formula::And(vec![
            Formula::Eq(Box::new(var()), Box::new(Formula::Int(3))),
            Formula::Not(Box::new(Formula::Bool(false))),
        ])));
        // A real violation condition is NOT content-free, however it is wrapped.
        assert!(!v2_violation_is_content_free(&Formula::Gt(
            Box::new(var()),
            Box::new(Formula::Int(0))
        )));
        assert!(!v2_violation_is_content_free(&Formula::And(vec![
            Formula::Bool(true),
            Formula::Gt(Box::new(var()), Box::new(Formula::Int(0))),
        ])));
        assert!(!v2_violation_is_content_free(&Formula::Bool(false)));
    }

    /// The same body with `extra` entry preconditions conjoined onto every row.
    /// Preconditions are conjoined before the enforcement step, so this is a
    /// direct handle on the SIZE of the `body` the splice clones per in-edge.
    fn unreachable_target_with_facts(arms: u128, extra: usize) -> VerifiableFunction {
        use trust_types::{Formula, Sort};
        let mut func = unreachable_target(arms);
        for k in 0..extra {
            func.preconditions.push(Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(k as i128)),
            ));
        }
        func
    }

    fn restored_row_nodes(arms: u128, extra: usize) -> usize {
        let func = unreachable_target_with_facts(arms, extra);
        let vcs = super::super::generate_v2_safety_vcs(&func);
        let row = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::Unreachable))
            .unwrap_or_else(|| panic!("in-degree {arms}: the `Unreachable` row must survive"));
        nodes(&row.formula)
    }

    /// THE SIZE RULE, as an assertion instead of a table.
    ///
    /// `v2_formula_with_path_guards_recorded` lowers one single-guard path per
    /// in-edge to `Or([And([g_e, body..]) ..])`, cloning the body per disjunct,
    /// so a restored row is EXACTLY LINEAR in the in-degree:
    ///
    /// ```text
    /// nodes(row) = 1 + in_degree * slope        slope = |g_e| + |body|
    /// ```
    ///
    /// The `1` is the `Or`. The slope belongs to the BODY — the row's formula as
    /// it stands at the splice, after every fact-conjoining pass — and NOT to
    /// this mechanism, which is the part a single quoted slope always loses.
    ///
    /// Asserted on three bodies whose fact sets differ, so no one slope can be
    /// mistaken for a law: each must fit its own line exactly at four in-degrees,
    /// and the three slopes must all differ. It fails if the lowering stops
    /// cloning per in-edge (slope collapses), if the restore is stubbed out (the
    /// row stays its bare size), or if the intercept stops being the single `Or`.
    #[test]
    fn a_restored_row_is_exactly_linear_in_the_in_degree() {
        let mut slopes = Vec::new();
        for extra in [0usize, 1, 4] {
            let sizes: Vec<usize> =
                [65u128, 130, 260, 520].iter().map(|n| restored_row_nodes(*n, extra)).collect();
            let slope = (sizes[1] - sizes[0]) / 65;
            for (arms, size) in [65usize, 130, 260, 520].iter().zip(&sizes) {
                assert_eq!(
                    *size,
                    1 + arms * slope,
                    "{extra} extra facts, in-degree {arms}: the restored row must be \
                     `1 + in_degree * {slope}`; the lowering clones the body once per \
                     in-edge and adds one `Or`. Sizes were {sizes:?}"
                );
            }
            slopes.push(slope);
        }
        assert_eq!(
            slopes,
            vec![5usize, 8, 17],
            "the slope is `|g_e| + |body|` and must move with the BODY: a 3-node \
             switch guard over a bare `Bool(true)` core, then that core conjoined \
             with one and with four extra facts. If the fact set these bodies \
             accumulate changed, re-measure — but a slope that stopped moving with \
             the body would mean the size rule is wrong"
        );
        let mut sorted = slopes.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), slopes.len(), "no two bodies may share a slope: {slopes:?}");
    }
}
