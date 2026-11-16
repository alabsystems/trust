//! Trust (R8-SEAM, `docs/DECISION_QUEUE.md`, taken 2026-10-05): the crate seam's ONE working copy
//! ([`SeamScratch`]) against the whole-module copies it replaced.
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//!
//! Each test runs the live spelling and the pre-R8-SEAM one (`module_without_drops`, and the
//! verbatim `seam_reference::row1_uc_probe`) on the same module and requires the same module, the
//! same report and the same traced outcomes, and a working copy that is the base again afterwards.
//! The end-to-end pin over real crates is `tests/run-make/trust-ir-seam-one-working-copy`, which
//! runs the whole seam both ways under the TEST-ONLY `-Ztrust-ir-seam-reference` option — the old
//! seam over the old differential against the new seam over the new one (the last two tests below
//! pin that routing and that the hook is a tracked option).

use std::cell::RefCell;

use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

use super::authority_tests::lineage_body_record;
use super::*;
use crate::differential::{DiffMode, compare_entries, compare_entries_in_place};

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}

/// A function `fid` of type `ty` with one block holding `body`, the block taking `params`.
fn function(
    fid: u32,
    name: &str,
    ty: FuncTyId,
    params: &[(u32, Ty)],
    body: Vec<InstrNode>,
) -> Function {
    let mut f = Function::new(FuncId::new(fid), name, ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    for (p, t) in params {
        b = b.with_param(v(*p), t.clone());
    }
    b.body = body;
    f.blocks.push(b);
    f
}

/// `spill x; drop the slot` — the producer's drop shape (`drops.rs`).
fn spill_and_drop(x: u32, slot: u32) -> Vec<InstrNode> {
    vec![
        InstrNode::new(Inst::Alloca { ty: Ty::I64, count: None, align: None }).with_result(v(slot)),
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(slot),
            value: v(x),
            volatile: false,
            align: None,
        }),
        InstrNode::new(Inst::Drop { ty: Ty::I64, ptr: v(slot) }),
    ]
}

/// Four functions over `(i64) -> i64`: 0 and 1 carry drops (1 in its second block), 2 none, and
/// 3 a SECOND function under id 2 that carries one — the duplicate-id shape `function_by_id`
/// resolves to its first holder while `module_without_drops` strips every holder.
fn drop_module() -> Module {
    let mut m = Module::new("seam_scratch_drops");
    let ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let ret = |x: u32| InstrNode::new(Inst::Return { values: vec![v(x)] });
    let mut body0 = spill_and_drop(0, 1);
    body0.push(ret(0));
    m.try_add_function(function(0, "f0", ty, &[(0, Ty::I64)], body0))
        .expect("Module::try_add_function: test fixture");
    let mut f1 = function(
        1,
        "f1",
        ty,
        &[(0, Ty::I64)],
        vec![InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![v(0)] })],
    );
    let mut b1 = Block::new(BlockId::new(1)).with_param(v(2), Ty::I64);
    b1.body = spill_and_drop(2, 3);
    b1.body.push(ret(2));
    f1.blocks.push(b1);
    m.try_add_function(f1).expect("Module::try_add_function: test fixture");
    m.try_add_function(function(2, "f2", ty, &[(0, Ty::I64)], vec![ret(0)]))
        .expect("Module::try_add_function: test fixture");
    let mut dup = spill_and_drop(0, 1);
    dup.push(ret(0));
    m.try_add_function(function(2, "f2_dup", ty, &[(0, Ty::I64)], dup))
        .expect("Module::try_add_function: test fixture");
    m
}

/// THE DROP SITE. For every closure — drop-bearing, drop-free, empty, duplicated, naming an
/// absent id, and naming the duplicate-id pair both ways — the working copy with
/// `drop_patches(closure)` installed is exactly `module_without_drops(base, closure)` (the base
/// itself when that returns `None`), and it is the base again after every comparison.
#[test]
fn the_working_copy_with_drop_patches_is_module_without_drops() {
    let base = drop_module();
    let mut scratch = SeamScratch::new(&base);
    let f = FuncId::new;
    let closures: [&[FuncId]; 8] = [
        &[f(0)],
        &[f(1), f(2)],
        &[f(2)],
        &[],
        &[f(0), f(1), f(0)],
        &[f(9)],
        &[f(0), f(2)],
        &[f(1)],
    ];
    for closure in closures {
        let expected = module_without_drops(&base, closure);
        let patches = scratch.drop_patches(closure);
        assert_eq!(patches.is_empty(), expected.is_none(), "closure {closure:?}");
        let seen = scratch.compare_patched(patches, |work| work.clone());
        assert!(seen == *expected.as_ref().unwrap_or(&base), "closure {closure:?}");
        assert!(scratch.work.as_ref() == Some(&base), "restored after closure {closure:?}");
    }
    assert_eq!(scratch.stats.copies, 1, "one copy for the whole pass");
    assert_eq!(scratch.stats.comparisons, closures.len());
}

/// The drop site's COMPARISON: the report from the working copy (with the in-place comparison)
/// is the report from `module_without_drops`'s copy (with the copying one), field for field.
#[test]
fn the_drop_comparison_on_the_working_copy_is_the_one_on_a_copy() {
    let base = drop_module();
    let mut oracle = Module::new("oracle");
    let ty = oracle
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    oracle
        .try_add_function(function(
            0,
            "f0",
            ty,
            &[(0, Ty::I64)],
            vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
        ))
        .expect("Module::try_add_function: test fixture");
    let key =
        |r: &crate::differential::DiffReport| (r.equal, r.notes.clone(), r.samples_checked, r.mode);
    let mut scratch = SeamScratch::new(&base);
    for (entry, closure) in [(0, vec![0]), (1, vec![1]), (2, vec![2]), (0, vec![0, 2])] {
        let closure: Vec<FuncId> = closure.into_iter().map(FuncId::new).collect();
        let copy = module_without_drops(&base, &closure);
        let old = compare_entries(
            copy.as_ref().unwrap_or(&base),
            FuncId::new(entry),
            &oracle,
            FuncId::new(0),
        );
        let patches = scratch.drop_patches(&closure);
        let (new, wrapped) = scratch.compare_patched(patches, |work| {
            compare_entries_in_place(work, FuncId::new(entry), &mut oracle, FuncId::new(0))
        });
        assert_eq!(key(&new), key(&old), "entry {entry}, closure {closure:?}");
        assert!(!wrapped);
        assert!(scratch.work.as_ref() == Some(&base));
    }
}

/// One UC probe subject: `entry(x: i64) -> i64 { let r = d(x); u(); r }` with `d: (i64) -> i64`
/// and `u: ()` bodyless, plus `other`, OUTSIDE the entry's closure, which calls `u` too when
/// `outside_site` — the pre-R8-SEAM producer walk counted every call site in the WHOLE module.
/// `d_results` is the result count of the call to `d` (1 is well formed).
struct UcSubject {
    assembled: Assembled,
    oracle: Module,
    declarations: Vec<FuncId>,
}

fn uc_subject(outside_site: bool, d_results: usize, oracle_returns_input: bool) -> UcSubject {
    let mut m = Module::new("seam_scratch_uc");
    let unary = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let unit = m
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let call_d = InstrNode::new(Inst::Call { callee: FuncId::new(2), args: vec![v(0)] })
        .with_results((0..d_results as u32).map(|i| v(1 + i)));
    let call_u = InstrNode::new(Inst::Call { callee: FuncId::new(3), args: Vec::new() });
    m.try_add_function(function(
        0,
        "entry",
        unary,
        &[(0, Ty::I64)],
        vec![call_d, call_u.clone(), InstrNode::new(Inst::Return { values: vec![v(1)] })],
    ))
    .expect("Module::try_add_function: test fixture");
    let mut other = vec![InstrNode::new(Inst::Return { values: Vec::new() })];
    if outside_site {
        other.insert(0, call_u);
    }
    m.try_add_function(function(1, "other", unit, &[], other))
        .expect("Module::try_add_function: test fixture");
    m.try_add_function(Function::new(FuncId::new(2), "d", unary, BlockId::new(0)))
        .expect("Module::try_add_function: test fixture");
    m.try_add_function(Function::new(FuncId::new(3), "u", unit, BlockId::new(0)))
        .expect("Module::try_add_function: test fixture");

    // The oracle's absent-callee encoding: `Assert(const false)` per site, plus the `Undef`
    // standing for `d`'s result.
    let mut oracle = Module::new("seam_scratch_uc::row1probe");
    let oty = oracle
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let ret = if oracle_returns_input { v(0) } else { v(2) };
    oracle
        .try_add_function(function(
            0,
            "entry",
            oty,
            &[(0, Ty::I64)],
            vec![
                InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
                    .with_result(v(1)),
                InstrNode::new(Inst::Assert {
                    cond: v(1),
                    kind: trust_ir::AssertKind::Unspecified,
                    site: None,
                }),
                InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(2)),
                InstrNode::new(Inst::Assert {
                    cond: v(1),
                    kind: trust_ir::AssertKind::Unspecified,
                    site: None,
                }),
                InstrNode::new(Inst::Return { values: vec![ret] }),
            ],
        ))
        .expect("Module::try_add_function: test fixture");
    let assembled = Assembled {
        module: m,
        errors: Vec::new(),
        coverage_rows: Vec::new(),
        lowered: 1,
        spliced: 2,
        declarations: 2,
        assigned: vec![(10, FuncId::new(0)), (11, FuncId::new(1))],
        decl_keys: Vec::new(),
        codegen_declarations: Vec::new(),
        unsignable_declarations: Vec::new(),
    };
    // The step-1 walk's order: `entry`, then its callees popped last-pushed first.
    UcSubject { assembled, oracle, declarations: vec![FuncId::new(3), FuncId::new(2)] }
}

/// THE UC SITE. For an agreeing subject, one whose whole-module site count does not pair, one that
/// diverges, and one with an ill-formed call, the live `row1_uc_probe` on the working copy returns
/// what the pre-R8-SEAM one (verbatim, copying the whole module per leg) returns and traces the
/// same outcome; the working copy is the base again afterwards.
#[test]
fn the_uc_probe_on_the_working_copy_is_the_uc_probe_on_copies() {
    let record = lineage_body_record(10, "probe::entry");
    let cases = [
        ("uc-agreed", uc_subject(false, 1, false)),
        ("uc-unpaired", uc_subject(true, 1, false)),
        ("uc-diverged", uc_subject(false, 1, true)),
        ("uc-unfenced", uc_subject(false, 0, false)),
    ];
    for (outcome, subject) in &cases {
        let UcSubject { assembled, oracle, declarations } = subject;
        let entry = FuncId::new(0);
        let live_events = RefCell::new(Vec::new());
        let mut scratch = SeamScratch::new(&assembled.module);
        let live = row1_uc_probe(
            &record,
            entry,
            declarations,
            assembled,
            &mut scratch,
            oracle,
            0,
            Some(&live_events),
        );
        let reference_events = RefCell::new(Vec::new());
        let reference = seam_reference::row1_uc_probe(
            &record,
            entry,
            declarations,
            assembled,
            oracle,
            0,
            &reference_events,
        );
        assert_eq!(live, reference, "{outcome}");
        let live_events = live_events.into_inner();
        assert_eq!(live_events, reference_events.into_inner(), "{outcome}");
        assert_eq!(live_events.len(), 1, "{outcome}: one traced outcome");
        assert_eq!(live_events[0].outcome, *outcome, "{outcome}: the case reaches its outcome");
        assert!(scratch.work.as_ref().is_none_or(|work| *work == assembled.module), "{outcome}");
        if *outcome == "uc-agreed" {
            assert!(scratch.stats.uc_legs > 1, "several legs ran on the one copy");
            assert_eq!(scratch.stats.copies, 1);
        }
    }
}

/// The producer side's index holds exactly the call sites of bodyless functions, in module order,
/// and a site outside the entry's closure is in it (the walk it replaces counted the whole module).
#[test]
fn the_declaration_call_index_is_the_whole_module_in_module_order() {
    let UcSubject { assembled, .. } = uc_subject(true, 1, false);
    let mut scratch = SeamScratch::new(&assembled.module);
    let sites = scratch.decl_call_sites(&[FuncId::new(2), FuncId::new(3), FuncId::new(2)]);
    let at: Vec<(usize, usize, usize, u32, usize)> =
        sites.iter().map(|s| (s.func, s.block, s.node, s.callee.index(), s.results)).collect();
    assert_eq!(at, vec![(0, 0, 0, 2, 1), (0, 0, 1, 3, 0), (1, 0, 0, 3, 0)]);
    assert_eq!(scratch.decl_call_sites(&[FuncId::new(3)]).len(), 2);
    assert!(scratch.decl_call_sites(&[FuncId::new(0)]).is_empty(), "a bodyful callee is no site");
}

/// The cross-check is not vacuous: a verdict, a traced outcome or an unrestored copy that differs
/// is a difference.
#[test]
fn the_cross_check_names_every_difference() {
    let verdict = |note: &str| SeamVerdict {
        def_index: 7,
        equal: false,
        samples: 0,
        mode: DiffMode::NotRun,
        note: note.to_string(),
    };
    let event = |outcome: &str| UcProbeEvent {
        def_index: 7,
        outcome: outcome.to_string(),
        samples: 0,
        detail: String::new(),
    };
    let restored = SeamScratchStats { restored: true, ..SeamScratchStats::default() };
    let same = seam_reference::differences(
        &[verdict("a")],
        &[verdict("a")],
        &[event("uc-agreed")],
        &[event("uc-agreed")],
        &restored,
    );
    assert!(same.is_empty(), "{same:?}");
    let notes = seam_reference::differences(&[verdict("a")], &[verdict("b")], &[], &[], &restored);
    assert_eq!(notes.len(), 1);
    let outcomes = seam_reference::differences(
        &[],
        &[],
        &[event("uc-agreed")],
        &[event("uc-unpaired")],
        &restored,
    );
    assert_eq!(outcomes.len(), 1);
    let counts = seam_reference::differences(&[verdict("a")], &[], &[], &[], &restored);
    assert_eq!(counts.len(), 1);
    let unrestored = seam_reference::differences(&[], &[], &[], &[], &SeamScratchStats::default());
    assert_eq!(unrestored.len(), 1);
}

/// The code lines of a source file: every line whose first non-blank characters are not `//`.
fn code_lines(source: &str) -> Vec<&str> {
    source.lines().filter(|line| !line.trim_start().starts_with("//")).collect()
}

/// THE REFERENCE IS THE OLD SEAM OVER THE OLD DIFFERENTIAL. The pre-R8-SEAM seam compares through
/// the pre-R8-SEAM `compare_entries` (`differential/compare_entries_reference.rs`, verbatim), not
/// through `differential::compare_entries`, which R8-SEAM split at its step boundaries and whose
/// promoted-global pairing it re-enumerated: a reference that ran the NEW differential on both
/// sides could not see a fault in differential.rs's movement. And that verbatim module is compiled
/// into every build, not only test builds, so the production compiler's hook can reach it.
#[test]
fn the_reference_seam_compares_through_the_pre_r8_seam_differential() {
    let reference = code_lines(include_str!("seam_reference.rs"));
    let calls = |needle: &str| reference.iter().filter(|line| line.contains(needle)).count();
    assert_eq!(
        calls("differential::compare_entries("),
        0,
        "the reference seam runs the new differential"
    );
    assert_eq!(
        calls("differential::compare_entries_reference::compare_entries("),
        2,
        "both reference comparisons (step 8 and the UC probe's legs) run the verbatim differential"
    );
    let differential = include_str!("../differential.rs");
    let declaration = "#[path = \"differential/compare_entries_reference.rs\"]\npub(crate) mod compare_entries_reference;";
    let at = differential
        .find(declaration)
        .expect("the reference differential is a crate-visible module");
    let above = differential[..at].lines().last().unwrap_or_default();
    assert!(
        !above.contains("cfg(test)"),
        "the reference differential must be in production builds"
    );
}

/// THE HOOK IS A TRACKED OPTION. `-Ztrust-ir-seam-reference` (`TRUST_AUTHORITY: EvidenceControl`,
/// in rustc_session's option table, where the authority inventory test observes it) gates the
/// cross-check; no environment variable reaches it, so a hooked compile cannot share an artifact
/// or incremental identity with an unhooked one.
#[test]
fn the_seam_reference_hook_is_a_tracked_option_not_an_environment_variable() {
    assert_eq!(seam_reference::OPTION, "-Ztrust-ir-seam-reference");
    let crate_module = code_lines(include_str!("../crate_module.rs"));
    let gate =
        crate_module.iter().filter(|line| line.contains("seam_reference::cross_checked(")).count();
    assert_eq!(gate, 1, "one call site runs the cross-check");
    assert!(
        crate_module
            .iter()
            .any(|line| line.contains("tcx.sess.opts.unstable_opts.trust_ir_seam_reference")),
        "the cross-check is gated by the tracked option"
    );
    assert!(
        !crate_module.iter().any(|line| line.contains("var_os(seam_reference")),
        "no environment variable gates the cross-check"
    );
    let reference = code_lines(include_str!("seam_reference.rs"));
    assert!(
        !reference.iter().any(|line| line.contains("std::env")),
        "the reference reads no environment"
    );
}
