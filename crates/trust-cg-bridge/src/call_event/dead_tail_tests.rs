//! PKG-C5c S2a unit pins (docs/DECISION_QUEUE.md PKG-C5c-DEAD-TAIL-1): the reader's trap-tail
//! set (`FunctionWindow::trap_tail`) and the executor's (`CerExec::new`) are one set, and
//! `DeadTails::read` admits exactly the lowered pair of a sited division check.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;
#[path = "../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;
use trust_cg_codegen::pipeline::OptLevel;

/// `M_cg` and its bound layout for ladder rung s21's shape.
fn bound(guarded: bool, triple: &str, opt: OptLevel) -> (Module, Vec<u8>, ObjectLayout) {
    let (m_cg, _) = sited_div(guarded, DivRecord::Pointer);
    let m_cg = targeted(&m_cg, triple);
    let object = compile(&m_cg, triple, opt);
    let parsed = CompiledObject::parse(&object).expect("parses");
    let expect = ObjectExpectations::from_module(&m_cg, parsed.format, RelocationModel::Static)
        .expect("expectations");
    let layout = ObjectLayout::bind(parsed, &expect).expect("binds");
    (m_cg, object, layout)
}

/// The two trap-tail sets, computed twice (compiled_object.rs `walk_window` and
/// `CerExec::new`), agree on every window of the dead and the live s21 shape, both triples, O0
/// and O2, and are non-empty where a tail was emitted. If they diverged, the admission would
/// still fail closed (an admitted `adrp` the executor does not treat as tail reaches `decode`,
/// which refuses it), but this pins that they do not.
#[test]
fn the_reader_and_the_executor_read_one_trap_tail_set() {
    let mut tails = 0;
    for triple in BOTH {
        for guarded in [true, false] {
            for opt in [OptLevel::O0, OptLevel::O2] {
                let (_, _, layout) = bound(guarded, triple, opt);
                for window in layout.windows.values() {
                    let places = BTreeMap::new();
                    let exec = CerExec::new(window, &places, &ReturnPlace::Void, false);
                    assert_eq!(exec.trap, window.trap_tail, "{triple} {guarded} {opt:?}");
                    tails += usize::from(!window.trap_tail.is_empty());
                }
            }
        }
    }
    // The dead tail at O0 (both triples) and the live tail at O0 and O2 (both triples).
    assert_eq!(tails, 6);
}

/// `DeadTails::read` on s21 at O0: one pair, the `adrp` at the run's first word, the record
/// `rung_location`, the entry `panic_const_div_by_zero`, both lines the walk's own; the tail's
/// `bl` is admitted with that run. An `M_cg` whose `Assert` is unsited admits nothing.
#[test]
fn the_lowered_pair_of_a_sited_check_is_the_one_admitted() {
    for triple in BOTH {
        let (m_cg, object, layout) = bound(true, triple, OptLevel::O0);
        let window = &layout.windows["rung"];
        let (bodies, places) = (BTreeMap::new(), BTreeMap::new());
        let input = CerInput {
            m_cg: &m_cg,
            producers: &[],
            bodies: &bodies,
            placements: &places,
            object: &object,
            relocation_model: RelocationModel::Static,
        };
        let dead = DeadTails::read(&input, &layout, window);
        let [pair] = &dead.pairs[..] else { panic!("{triple}: {:?}", dead.pairs) };
        assert_eq!(pair.symbol, DIV_LOCATION, "{triple}");
        assert_eq!(pair.entries, BTreeSet::from([DIV_ENTRY.to_string()]), "{triple}");
        assert_eq!(pair.tail.0, pair.adrp, "{triple}");
        let lines: BTreeSet<&str> = window.unknown.iter().map(String::as_str).collect();
        assert_eq!(dead.lines(), lines, "{triple}");
        let site = window.sites.iter().find(|s| s.in_trap_tail).expect("the tail's `bl`");
        assert_eq!(dead.admit_call(window, site), Some(pair.tail), "{triple}");

        let mut unsited = m_cg.clone();
        for node in
            unsited.functions.iter_mut().flat_map(|f| &mut f.blocks).flat_map(|b| &mut b.body)
        {
            if let Inst::Assert { site, .. } = &mut node.inst {
                *site = None;
            }
        }
        let input = CerInput { m_cg: &unsited, ..input };
        assert!(DeadTails::read(&input, &layout, window).pairs.is_empty(), "{triple}");
    }
}

/// The admission is the whole run or nothing (`DeadTails::read`, `entry_call`): on s21's O0
/// window, each edit of the RECORD the walk produced keeps the pair's shape and drops it, so
/// its two lines stay in O1's account: the run's `bl` removed (a run with no call); made a
/// `b` (tail jump); naming `rung`; moved one word back (not followed by the trap); a second
/// site in the run; a second shaped pair in the run (copies of both halves at the `mov` and
/// the `bl`). The unedited window admits the one pair.
#[test]
fn a_run_is_admitted_whole_or_not_at_all() {
    for triple in BOTH {
        let (m_cg, object, layout) = bound(true, triple, OptLevel::O0);
        let base = &layout.windows["rung"];
        let (bodies, places) = (BTreeMap::new(), BTreeMap::new());
        let input = CerInput {
            m_cg: &m_cg,
            producers: &[],
            bodies: &bodies,
            placements: &places,
            object: &object,
            relocation_model: RelocationModel::Static,
        };
        let admitted = |w: &FunctionWindow| DeadTails::read(&input, &layout, w).pairs.len();
        assert_eq!(admitted(base), 1, "{triple}: the twin");
        let bl = base.sites.iter().position(|s| s.in_trap_tail).expect("the tail's `bl`");
        let at = base.sites[bl].offset;
        let edit = |f: &dyn Fn(&mut FunctionWindow)| {
            let mut w = base.clone();
            f(&mut w);
            w
        };
        let adrp = *base.page_halves.keys().next().expect("the pair");
        let cells: Vec<(&str, FunctionWindow)> = vec![
            (
                "no call",
                edit(&|w| {
                    w.sites.remove(bl);
                }),
            ),
            ("a tail jump", edit(&|w| w.sites[bl].kind = MachineSiteKind::Tail)),
            ("naming rung", edit(&|w| w.sites[bl].callee = Some("rung".into()))),
            ("not followed by the trap", edit(&|w| w.sites[bl].offset = at - 4)),
            (
                "a second site",
                edit(&|w| {
                    let mut s = w.sites[bl].clone();
                    s.offset = at - 4;
                    w.sites.push(s);
                }),
            ),
            (
                "a second pair",
                edit(&|w| {
                    let (hi, lo) =
                        (w.page_halves[&adrp].clone(), w.page_halves[&(adrp + 4)].clone());
                    w.page_halves.insert(
                        adrp + 8,
                        crate::compiled_object::PageHalf { offset: adrp + 8, ..hi },
                    );
                    w.page_halves.insert(
                        adrp + 12,
                        crate::compiled_object::PageHalf { offset: adrp + 12, ..lo },
                    );
                }),
            ),
        ];
        for (what, w) in &cells {
            assert_eq!(admitted(w), 0, "{triple}: {what}");
        }
    }
}
