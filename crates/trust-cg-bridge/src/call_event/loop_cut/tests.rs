//! PKG-C5c-L0 unit pins: the measurement's Formula helpers, its record shape against L1's
//! `LoopPair`, its deterministic query, machine-step and node caps, the entry-arrival leaf
//! check, the pinned-register path, and its absence from observe-only gates.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use super::super::{CerReport, verify_compiled_module_inner};
use super::*;
#[path = "../../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::Linkage;

use crate::compiled_object::ObjectRefusal;
use crate::verify_output_instantiate::loop_sim;

/// One gate run on the 8 MiB gate thread with the recorder installed THERE.
fn gate(fx: &Fixture, observe_only: bool) -> (Result<CerReport, ObjectRefusal>, Vec<LoopRecord>) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn_scoped(scope, || {
                record_loop_segments(|| {
                    verify_compiled_module_inner(
                        &CerInput {
                            m_cg: &fx.m_cg,
                            producers: &fx.producers,
                            bodies: &fx.bodies,
                            placements: &fx.placements,
                            object: &fx.object,
                            relocation_model: fx.model,
                        },
                        None,
                        None,
                        observe_only,
                    )
                })
            })
            .expect("spawn the gate thread")
            .join()
            .expect("the gate thread panicked")
    })
}

fn measurement(records: &[LoopRecord]) -> &Measurement {
    let [record] = records else { panic!("{} records, not one: {records:#?}", records.len()) };
    match &record.outcome {
        LoopOutcome::Measured(m) => m,
        LoopOutcome::Declined(why) => panic!("declined: {why}"),
    }
}

fn s06(triple: &str, opt: OptLevel) -> Fixture {
    Fixture::new(loop_rung_module(LoopRung::S06, Linkage::External), triple, opt)
}

/// The record converted to L1's pair (`Pinned` has no L1 role yet: PKG-C5c-L2 gap (a)).
fn to_pair(s: &LoopSegments) -> loop_sim::LoopPair {
    let regs = s
        .regs
        .iter()
        .map(|r| loop_sim::Reg {
            name: r.name.clone(),
            width: r.width,
            role: match &r.role {
                SegRole::Coupled(j) => loop_sim::Role::Coupled(*j),
                SegRole::Frame { arch, entry } => {
                    loop_sim::Role::Frame { arch: arch.clone(), entry: entry.clone() }
                }
                SegRole::Pinned(_) | SegRole::Havoc => loop_sim::Role::Havoc,
            },
        })
        .collect();
    loop_sim::LoopPair {
        ir_vars: s.ir_vars.clone(),
        entry_ir: s.entry_ir.clone(),
        step_ir: s.step_ir.clone(),
        reach_ret_ir: s.reach_ret_ir.clone(),
        ret_ir: s.ret_ir.clone(),
        regs,
        entry_m: s.entry_m.clone(),
        step_m: s.step_m.clone(),
        reach_ret_m: s.reach_ret_m.clone(),
        ret_m: s.ret_m.clone(),
        exit_frame_m: s.exit_frame_m.clone(),
        entry: loop_sim::EntryPath {
            reach_ir: s.entry_reach_ir.clone(),
            reach_m: s.entry_reach_m.clone(),
            ret_ir: s.entry_ret_ir.clone(),
            ret_m: s.entry_ret_m.clone(),
            frame_m: s.entry_frame_m.clone(),
        },
    }
}

/// s06 at O0: the recorded segments have L1's pair shape. The IR shared variables are bb1's
/// parameters sorted by value id, then its other live-ins sorted by id (the legacy order,
/// verify_output_trust_ir.rs's `ev.shared`): `i` (v1), `s` (v2), then `x` (v0). Converted to
/// `loop_sim::LoopPair`, `goal_of`'s answer is printed and pinned as measured (an L2
/// pre-measurement; L0 asserts no proof).
#[test]
fn l0_s06_segments_take_the_loop_sim_pair_shape() {
    for triple in BOTH {
        let fx = s06(triple, OptLevel::O0);
        let (report, records) = gate(&fx, false);
        let report = report.expect("object binds");
        let m = measurement(&records);
        assert!(m.all_discharged(), "{triple}: {}\n{:#?}", m.text, m.items);
        let segs = m.segments.as_ref().expect("segments recorded");
        let names: Vec<&str> = segs.ir_vars.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, ["CUT_bb1_v1", "CUT_bb1_v2", "CUT_bb1_v0"], "{triple}");
        assert!(segs.ir_vars.iter().all(|(_, w)| *w == 64));
        // Every register name obeys L1's role rule: a coupled register by its IR cut name, a
        // frame register `CUT_M_*`, a scratch register ending `_HAVOC` and not `CUT_`.
        for r in &segs.regs {
            match &r.role {
                SegRole::Coupled(j) => {
                    assert_eq!(Some(&r.name), segs.ir_vars.get(*j).map(|v| &v.0))
                }
                SegRole::Frame { .. } => assert!(r.name.starts_with("CUT_M_"), "{}", r.name),
                SegRole::Havoc => {
                    assert!(r.name.ends_with("_HAVOC") && !r.name.starts_with("CUT_"), "{}", r.name)
                }
                SegRole::Pinned(_) => panic!("{triple}: s06 at O0 pins nothing"),
            }
        }
        assert_eq!(
            segs.regs.iter().filter(|r| matches!(r.role, SegRole::Frame { .. })).count(),
            21,
            "{triple}: X19-X29, SP, D8-D15 and X30"
        );
        let pair = to_pair(segs);
        // MEASURED (an L2 pre-measurement, PKG-C5c-L2 gap (k)): L1 declines the pair. A
        // machine path that ARRIVES at the cut returns `AbiExit::entry()`, so the merged exit
        // frame reads the entry leaf `X19` where L1 allows only the loop segment's own
        // `CUT_M_X19` (L0's `exit.frame` items are unaffected: an arriving path does not
        // return, and the entry leaf equals the frame's entry value).
        let goal = loop_sim::goal_of(&pair).map(|_| ());
        assert_eq!(goal, Err("loop: X19 is not a leaf of this segment".to_string()), "{triple}");
        let c = report.certificate("rung").expect("rung");
        assert_eq!(c.obligations.o4_return.detail, "spec side: loop/backedge at bb1 (fail-closed)");
    }
}

/// The pure helpers: the non-register leaf rule (flag, memory and high-half havocs, which L1's
/// `within` rejects), every scratch register name obeying L1's `Role::Havoc` rule, ground
/// folding, the text cap and the injective assignment order.
#[test]
fn l0_items_are_named_and_counted_per_segment() {
    for leaf in ["bb1_HAVOC_N", "bb3_HAVOC_Z", "MEM@bb1_HAVOC", "D8@bb1_HI_HAVOC"] {
        assert!(non_register_leaf(leaf), "{leaf}");
    }
    for name in ["X3@bb1_HAVOC", "V0@bb1_HAVOC", "CUT_bb1_v2", "CUT_M_X19", "X0"] {
        assert!(!non_register_leaf(name), "{name}");
    }
    for r in 0..31 {
        let Formula::Var(name, _) = havoc_gpr(4, r) else { panic!() };
        assert!(name.ends_with("_HAVOC") && !name.starts_with("CUT_"), "{name}");
    }
    // A loop item mentioning a non-register leaf is never posed to ay.
    let mut d = Decider { cap: 8, nodes: MAX_QUERY_NODES, queries: 0, refl: 0 };
    let flag = Formula::Var("bb1_HAVOC_Z".into(), Sort::Bool);
    let item = Item { name: "exit.cond".into(), m: bit(&flag), s: bv(1, 1), in_loop: true };
    assert_eq!(
        d.decide_one(&item),
        Some(ItemOutcome::Unknown("reads the non-register leaf bb1_HAVOC_Z".into()))
    );
    assert_eq!(d.queries, 0);
    // Equal sides are refl, with no query; a query past the cap is not posed.
    let same = Item {
        name: "x".into(),
        m: var64("CUT_bb1_v1".into()),
        s: var64("CUT_bb1_v1".into()),
        in_loop: true,
    };
    assert_eq!(d.decide_one(&same), Some(ItemOutcome::Refl));
    let mut capped = Decider { cap: 0, nodes: MAX_QUERY_NODES, queries: 0, refl: 0 };
    let differ =
        Item { name: "y".into(), m: var64("A".into()), s: var64("B".into()), in_loop: false };
    assert_eq!(capped.decide_one(&differ), None);
    // Ground folding: and(sxtw(3), 63) is 3, and every literal is canonical.
    let amount = Formula::BvAnd(b(Formula::BvSignExt(b(bv(3, 32)), 32)), b(bv(63, 64)), 64);
    assert_eq!(norm(&amount), bv(3, 64));
    assert_eq!(norm(&bv(-1, 64)), bv(i128::from(u64::MAX), 64));
    assert_eq!(
        norm(&Formula::BvSignExt(b(bv(0x8000_0000, 32)), 32)),
        bv(0xffff_ffff_8000_0000, 64)
    );
    assert_eq!(norm(&Formula::BvLShr(b(bv(12, 64)), b(bv(64, 64)), 64)), bv(0, 64));
    // Identity folding: `mov x3, x0` is `orr x3, xzr, x0`.
    let x0 = var64("X0".into());
    assert_eq!(norm(&Formula::BvOr(b(bv(0, 64)), b(x0.clone()), 64)), x0);
    assert_eq!(norm(&Formula::BvAnd(b(x0.clone()), b(bv(-1, 64)), 64)), x0);
    assert_eq!(norm(&Formula::BvAdd(b(x0.clone()), b(bv(0, 64)), 64)), x0);
    assert_eq!(
        norm(&Formula::BvSub(b(bv(0, 64)), b(x0.clone()), 64)),
        Formula::BvSub(b(bv(0, 64)), b(x0.clone()), 64)
    );
    // A literal of another width is no identity.
    let narrow = Formula::BvOr(b(bv(0, 32)), b(x0.clone()), 64);
    assert_eq!(norm(&narrow), narrow);
    // The text cap keeps the prefix and the suffix.
    let long = format!("{PREFIX}{}{SUFFIX}", "y".repeat(900));
    let capped_text = cap_text(&long);
    assert!(capped_text.len() <= MAX_TEXT_BYTES, "{}", capped_text.len());
    assert!(capped_text.starts_with(PREFIX) && capped_text.ends_with(&format!("…{SUFFIX}")));
    assert_eq!(cap_text("short"), "short");
    // Injective assignments, candidate order.
    assert_eq!(
        assignments(&[vec![2, 3], vec![2, 3], vec![4, 5]]),
        vec![vec![2, 3, 4], vec![2, 3, 5], vec![3, 2, 4], vec![3, 2, 5]]
    );
    assert!(assignments(&[vec![1], vec![1]]).is_empty());
}

/// The bound is deterministic: with the query cap at 0 the s06 shape records the effort text
/// (no wall clock is read to decide), and stays Unknown with today's reason. With the default
/// cap its query count is printed.
#[test]
fn l0_the_query_cap_bounds_a_measurement() {
    for triple in BOTH {
        let fx = s06(triple, OptLevel::O0);
        // The cap is thread-local: set on the gate thread itself.
        let (report, records) = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(8 << 20)
                .spawn_scoped(scope, || with_loop_cut_query_cap(0, || gate_here(&fx)))
                .expect("spawn")
                .join()
                .expect("the gate thread panicked")
        });
        let m = measurement(&records);
        assert!(
            m.text.starts_with("loop cut points: effort bound reached (0 solver queries of 0,"),
            "{triple}: {}",
            m.text
        );
        assert!(m.text.ends_with(SUFFIX));
        let c = report.certificate("rung").expect("rung").clone();
        assert_eq!(c.obligations.o4_return.detail, "spec side: loop/backedge at bb1 (fail-closed)");
        let (_, records) = gate(&fx, false);
        let m = measurement(&records);
        println!(
            "{triple}: default cap {MAX_L0_QUERIES}: {} queries, {} refl, {} ms",
            m.queries, m.refl, m.ms
        );
        assert!(m.queries > 0 && m.queries <= MAX_L0_QUERIES, "{triple}: {}", m.queries);
    }
}

/// The gate on THIS thread, recorder installed (the caller is on a big-stack thread).
fn gate_here(fx: &Fixture) -> (CerReport, Vec<LoopRecord>) {
    let (report, records) = record_loop_segments(|| {
        verify_compiled_module_inner(
            &CerInput {
                m_cg: &fx.m_cg,
                producers: &fx.producers,
                bodies: &fx.bodies,
                placements: &fx.placements,
                object: &fx.object,
                relocation_model: fx.model,
            },
            None,
            None,
            false,
        )
    });
    (report.expect("object binds"), records)
}

/// Observe-only (the conditional frame replay's observation) never measures: with a recorder
/// installed and every solver call made a panic (`without_production`), the s06 shape still
/// stops at the spec side with today's reason, records nothing and calls no solver.
#[test]
fn l0_observe_only_measures_nothing_and_calls_no_solver() {
    for triple in BOTH {
        let fx = s06(triple, OptLevel::O0);
        let (report, records) = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(8 << 20)
                .spawn_scoped(scope, || {
                    crate::original_conjunction_certificate::without_production(|| {
                        record_loop_segments(|| {
                            verify_compiled_module_inner(
                                &CerInput {
                                    m_cg: &fx.m_cg,
                                    producers: &fx.producers,
                                    bodies: &fx.bodies,
                                    placements: &fx.placements,
                                    object: &fx.object,
                                    relocation_model: fx.model,
                                },
                                None,
                                None,
                                true,
                            )
                        })
                    })
                })
                .expect("spawn")
                .join()
                .expect("the gate thread panicked (a solver call under without_production?)")
        });
        assert!(records.is_empty(), "{triple}: {records:#?}");
        let report = report.expect("object binds");
        let c = report.certificate("rung").expect("rung");
        assert_eq!(c.obligations.o4_return.detail, "spec side: loop/backedge at bb1 (fail-closed)");
        // The control: the same object measured in Produce mode does call the solver.
        let (_, records) = gate(&fx, false);
        assert!(measurement(&records).queries > 0, "{triple}");
    }
}

/// `f` on a fresh 8 MiB thread (the caps are thread-local: set on the gate thread itself).
fn on_gate_thread<R: Send>(f: impl FnOnce() -> R + Send) -> R {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn_scoped(scope, f)
            .expect("spawn")
            .join()
            .expect("the gate thread panicked")
    })
}

/// The machine-step cap is a true bound on the total: a run starts only when its worst case
/// (`MAX_MACHINE_STEPS` + 1, since `CerExec` counts a step before refusing) still fits. At one
/// step under that no run starts; at exactly that the entry run starts and the first loop run
/// does not. Each records the effort text naming the cap, and the grade is today's Unknown.
#[test]
fn l0_the_step_cap_bounds_the_total() {
    assert_eq!(RUN_STEPS, 4097);
    for triple in BOTH {
        let fx = s06(triple, OptLevel::O0);
        let (report, records) =
            on_gate_thread(|| with_loop_cut_step_cap(RUN_STEPS - 1, || gate_here(&fx)));
        let m = measurement(&records);
        assert_eq!(
            m.text,
            format!(
                "loop cut points: effort bound reached (0 solver queries of {MAX_L0_QUERIES}, 0 \
                 machine steps of 4096){SUFFIX}"
            ),
            "{triple}"
        );
        assert_eq!((m.machine_steps, m.queries), (0, 0), "{triple}");
        let c = report.certificate("rung").expect("rung");
        assert_eq!(c.obligations.o4_return.detail, "spec side: loop/backedge at bb1 (fail-closed)");

        let (_, records) = on_gate_thread(|| with_loop_cut_step_cap(RUN_STEPS, || gate_here(&fx)));
        let m = measurement(&records);
        assert!(m.machine_steps > 0 && m.machine_steps <= RUN_STEPS, "{triple}: {}", m.text);
        assert_eq!(
            m.text,
            format!(
                "loop cut points: effort bound reached (0 solver queries of {MAX_L0_QUERIES}, {} \
                 machine steps of 4097){SUFFIX}",
                m.machine_steps
            ),
            "{triple}"
        );
        assert!(m.items.is_empty() && m.tried.len() == 1, "{triple}: {:?}", m.tried);
    }
}

/// The node cap: at 0 every item that is not refl is Unknown with the cap's reason and no
/// query is posed, so nothing discharges past the refl items.
#[test]
fn l0_the_node_cap_leaves_large_items_unknown() {
    for triple in BOTH {
        let fx = s06(triple, OptLevel::O0);
        let (report, records) = on_gate_thread(|| with_loop_cut_node_cap(0, || gate_here(&fx)));
        let m = measurement(&records);
        assert_eq!(m.queries, 0, "{triple}: {}", m.text);
        assert!(!m.all_discharged(), "{triple}: {}", m.text);
        let capped: Vec<&str> = m
            .items
            .iter()
            .filter_map(|(n, o)| match o {
                ItemOutcome::Unknown(why)
                    if why.starts_with("the query has ")
                        && why.ends_with(" nodes, over the cap of 0") =>
                {
                    Some(n.as_str())
                }
                _ => None,
            })
            .collect();
        assert!(!capped.is_empty(), "{triple}: {:#?}", m.items);
        assert!(
            m.items.iter().all(|(_, o)| matches!(o, ItemOutcome::Refl | ItemOutcome::Unknown(_))),
            "{triple}: {:#?}",
            m.items
        );
        assert!(m.text.contains("` did not conclude: the query has "), "{triple}: {}", m.text);
        let c = report.certificate("rung").expect("rung");
        assert_eq!(c.obligations.o4_return.detail, "spec side: loop/backedge at bb1 (fail-closed)");
    }
}

/// The entry-arrival leaf check: an arrival whose value or path mentions a loop-segment or
/// havoc variable is refused, one over entry leaves (`X{n}`, `V{n}`, `SP`) only is admitted.
#[test]
fn l0_entry_arrivals_mention_entry_leaves_only() {
    let x0 = var64("X0".into());
    let ok = vec![(Formula::Bool(true), vec![x0.clone(), var64("SP".into()), var64("V3".into())])];
    assert_eq!(entry_arrivals_closed(&ok), Ok(()));
    let refused = Err("entry: an entry-arrival value mentions a non-entry variable".to_string());
    for leaf in ["CUT_bb1_v0", "X3@bb1_HAVOC", "CER_S#bb2.0", "X", "Xa", "MEM"] {
        let value = vec![(Formula::Bool(true), vec![x0.clone(), var64(leaf.into())])];
        assert_eq!(entry_arrivals_closed(&value), refused, "{leaf}");
        let path =
            vec![(bit(&Formula::Eq(b(var64(leaf.into())), b(x0.clone()))), vec![x0.clone()])];
        assert_eq!(entry_arrivals_closed(&path), refused, "{leaf} in the path");
    }
}

/// The offset of the one word of `rung` equal to `word`.
#[track_caller]
fn the_word(fx: &Fixture, word: u32) -> u64 {
    let hits: Vec<u64> = function_words(&fx.object, "rung")
        .into_iter()
        .filter(|(_, w)| *w == word)
        .map(|(off, _)| off)
        .collect();
    let [off] = hits.as_slice() else { panic!("{}: {word:#010x} is at {hits:x?}", fx.triple) };
    *off
}

/// The exhaustive hook (every formed pair decided item by item) on s06 at O0.
///
/// - The clean object: the report is the ordinary one, and the FIRST pair tried, `%0 in X0`,
///   runs the pinned-register path: X3 (the copy of `x` the loop compares against and never
///   writes) is pinned to its entry-arrival value and its `step.pinned(X3)` item discharges.
///   That pair fails elsewhere (the loop reuses X0), so it is not reported.
/// - The wrong-exit mutant (`b.lo` -> `b.ls`): on the CORRECT assignment
///   (`%1 in X1, %2 in X2, %0 in X3`, no pin), `exit.cond` is a counterexample: the machine
///   loops at `i == x` and the IR does not. The ordinary report names another pair (the
///   longest first-fail prefix ties and the first pair tried wins).
#[test]
fn l0_exhaustive_pairs_pin_the_pinned_path_and_the_exit_condition() {
    let correct: &[(u32, u8)] = &[(1, 1), (2, 2), (0, 3)];
    for triple in BOTH {
        let fx = s06(triple, OptLevel::O0);
        let (_, plain) = on_gate_thread(|| gate_here(&fx));
        let (report, records) = on_gate_thread(|| with_loop_cut_exhaustive(|| gate_here(&fx)));
        let (plain, m) = (measurement(&plain), measurement(&records));
        assert!(plain.pairs.is_empty());
        assert_eq!((&m.text, &m.items), (&plain.text, &plain.items), "{triple}");
        assert_eq!(m.live_ins, correct, "{triple}");
        let first = m.pairs.first().expect("a pair");
        assert_eq!((first.block, first.live_ins.as_slice()), (1, &[(1, 1), (2, 2), (0, 0)][..]));
        assert_eq!(first.pinned, [3], "{triple}");
        let pinned = first.items.iter().find(|(n, _)| n == "step.pinned(X3)").map(|i| &i.1);
        assert!(pinned.is_some_and(ItemOutcome::discharged), "{triple}: {:#?}", first.items);
        assert!(first.items.iter().any(|(_, o)| !o.discharged()), "{triple}");
        let last = m.pairs.last().expect("the reported pair");
        assert_eq!(last.live_ins, correct);
        assert!(last.items.iter().all(|(_, o)| o.discharged()), "{triple}");
        let c = report.certificate("rung").expect("rung");
        assert_eq!(c.obligations.o4_return.detail, "spec side: loop/backedge at bb1 (fail-closed)");

        // `b.lo` -> `b.ls`.
        let at = the_word(&fx, 0x5400_0043);
        let wrong = fx.patched(|o| patch_word(o, at, 0x5400_0049));
        let (_, records) = on_gate_thread(|| with_loop_cut_exhaustive(|| gate_here(&wrong)));
        let m = measurement(&records);
        let pair = m
            .pairs
            .iter()
            .find(|p| p.block == 1 && p.live_ins == correct)
            .unwrap_or_else(|| panic!("{triple}: {:#?}", m.pairs));
        assert!(pair.pinned.is_empty(), "{triple}");
        let exit = pair.items.iter().find(|(n, _)| n == "exit.cond").map(|i| &i.1);
        assert_eq!(exit, Some(&ItemOutcome::CounterExample), "{triple}: {:#?}", pair.items);
        let failing: Vec<&str> =
            pair.items.iter().filter(|(_, o)| !o.discharged()).map(|i| i.0.as_str()).collect();
        assert_eq!(
            failing,
            ["step(%1 in X1)", "step(%2 in X2)", "exit.cond", "exit.return"],
            "{triple}: {:#?}",
            pair.items
        );
    }
}

/// Each ay query of the measurement sends exactly one `:rlimit`: the output gate's effort count
/// (`verify_output::gate_query_effort`, DECISION_QUEUE BUDGET-1), sized by the scale in force over
/// `NOT (m == s)`, the one formula `solve` asserts, on a proof and on a counterexample alike.
#[test]
fn l0_each_query_sends_the_gate_count_over_not_m_equals_s() {
    use trust_types::determinism::EffortScale;

    use crate::verify_output::{record_gate_efforts, with_gate_effort};

    let x = var64("X0".into());
    let s = x.clone();
    let cases = [
        (Formula::BvAdd(Box::new(x.clone()), Box::new(bv(0, 64)), 64), ItemOutcome::Proven),
        (Formula::BvAdd(Box::new(x.clone()), Box::new(bv(1, 64)), 64), ItemOutcome::CounterExample),
    ];
    for k in [None, Some(1), Some(7)] {
        let scale = k.map_or(EffortScale::BUILTIN, |k: u64| {
            EffortScale::parse(&k.to_string()).expect("a valid k")
        });
        for (m, want) in &cases {
            let run = || record_gate_efforts(|| solve(m, &s));
            let (outcome, sent) = match k {
                Some(_) => with_gate_effort(scale, run),
                None => run(),
            };
            assert_eq!(&outcome, want, "k = {k:?}: {m:?}");
            let asserted =
                Formula::Not(Box::new(Formula::Eq(Box::new(m.clone()), Box::new(s.clone()))));
            let effort = scale.for_query(&[&asserted]);
            assert!(effort.conflicts < EffortScale::CEILING, "{effort:?}");
            assert_eq!(sent, vec![effort], "k = {k:?}: {m:?}");
        }
    }
}
