//! R1 harvest (2026-10-19): the call-site precondition producers open their own memo
//! scopes ([`super::EntryScope`]). The compiler's R1 harvest asks the attributed
//! producer once per (callee, caller), outside any scope, and outside a scope every
//! whole-body analysis was rebuilt per ask: the local-name table per minted name, the
//! laundered alias roots per written place of every statement-version oracle. These
//! tests pin, with the deterministic `AnalysisMemoStats` counters and never a clock,
//! that the scope builds those analyses a number of times that does not grow with the
//! call sites; that below every budget it changes no row (bare, nested in a metered
//! generation of another function, nested in the function's own analysis scope, and in
//! a row-replay scope, the rows are byte-identical, by `Debug`, to an unscoped call's;
//! at a budget it can change one, toward fewer trips: see `EntryScope`); and that its work
//! half joins an enclosing meter and meters nothing outermost. The negative control
//! throughout is [`super::without_entry_scope`]: the code as it was before the scope.

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
};

use super::{
    generate_callsite_precondition_vcs, generate_callsite_precondition_vcs_attributed,
    without_entry_scope,
};
use crate::AnalysisMemoStats;
use crate::modular::{FunctionSummary, SummaryDatabase};

const CALLEE: &str = "example::positive";

/// `positive(n)` requires `n > 0`.
fn summaries() -> SummaryDatabase {
    let mut summaries = SummaryDatabase::new();
    summaries.insert(
        FunctionSummary::new(CALLEE).with_param_names(vec!["n".to_string()]).with_precondition(
            Formula::Gt(Box::new(Formula::var("n", Sort::Int)), Box::new(Formula::Int(0))),
        ),
    );
    summaries
}

/// `fn caller(x: u32)` with `sites` chained calls `positive(_t)`, each through its own
/// temp `_t = x + k` and its own destination, one call per block, then `return`.
fn caller(sites: usize) -> VerifiableFunction {
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
    ];
    let mut blocks = Vec::new();
    for k in 0..sites {
        let temp = locals.len();
        locals.push(LocalDecl { index: temp, ty: Ty::u32(), name: None });
        let dest = locals.len();
        locals.push(LocalDecl { index: dest, ty: Ty::u32(), name: None });
        blocks.push(BasicBlock {
            id: BlockId(k),
            stmts: vec![Statement::Assign {
                place: Place::local(temp),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(k as u128, 32)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: crate::sep_engine::tests::fixture_key(CALLEE),
                is_foreign: false,
                func: CALLEE.to_string(),
                args: vec![Operand::Move(Place::local(temp))],
                dest: Place::local(dest),
                target: Some(BlockId(k + 1)),
                span: SourceSpan::default(),
                atomic: None,
            },
        });
    }
    blocks.push(BasicBlock { id: BlockId(sites), stmts: vec![], terminator: Terminator::Return });
    VerifiableFunction {
        name: "caller".to_string(),
        def_path: "example::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
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

/// Both producers' rows for `func`, rendered (`VerificationCondition` has no
/// `PartialEq`; `Debug` is what `tests/vcgen_budget_realmir.rs` compares too).
fn render(func: &VerifiableFunction, summaries: &SummaryDatabase) -> (String, String) {
    let plain = generate_callsite_precondition_vcs(func, summaries);
    let attributed = generate_callsite_precondition_vcs_attributed(func, summaries);
    (format!("{plain:?}"), format!("{attributed:?}"))
}

/// The work counters of one attributed-producer call (the R1 harvest's).
fn attributed_work(func: &VerifiableFunction, summaries: &SummaryDatabase) -> AnalysisMemoStats {
    crate::reset_analysis_memo_stats();
    let rows = generate_callsite_precondition_vcs_attributed(func, summaries);
    // The fixture must reach the call-site assembly, or this counts nothing.
    assert!(
        rows.iter().any(|(vc, _, _)| matches!(vc.kind, VcKind::Precondition { .. })),
        "the fixture yields call-site precondition rows: {rows:?}"
    );
    crate::analysis_memo_stats()
}

#[test]
fn the_attributed_producer_builds_its_whole_body_analyses_independent_of_the_sites() {
    let summaries = summaries();
    let (small, large) = (caller(4), caller(32));

    // The defect: unscoped, both analyses are rebuilt per ask, so their builds grow with
    // the call sites (at least one more local-name table per added site: its temp's
    // and its destination's names are minted uncached).
    let (unscoped_small, unscoped_large) = without_entry_scope(|| {
        (attributed_work(&small, &summaries), attributed_work(&large, &summaries))
    });
    assert!(
        unscoped_large.local_name_tables_computed >= unscoped_small.local_name_tables_computed + 28,
        "unscoped, the tables grow with the sites: {} for 4 sites, {} for 32",
        unscoped_small.local_name_tables_computed,
        unscoped_large.local_name_tables_computed
    );
    assert!(
        unscoped_large.laundered_alias_roots_computed
            > unscoped_small.laundered_alias_roots_computed,
        "unscoped, the alias-root walks grow with the sites: {} for 4 sites, {} for 32",
        unscoped_small.laundered_alias_roots_computed,
        unscoped_large.laundered_alias_roots_computed
    );

    // The scope: as many builds for 32 sites as for 4.
    let (scoped_small, scoped_large) =
        (attributed_work(&small, &summaries), attributed_work(&large, &summaries));
    assert_eq!(
        scoped_large.local_name_tables_computed, scoped_small.local_name_tables_computed,
        "scoped, the local-name tables do not grow with the sites"
    );
    assert_eq!(
        scoped_large.laundered_alias_roots_computed, scoped_small.laundered_alias_roots_computed,
        "scoped, the alias-root walks do not grow with the sites"
    );
    assert!(
        scoped_large.local_name_tables_computed < unscoped_large.local_name_tables_computed,
        "the scope builds fewer tables than the unscoped call"
    );
}

#[test]
fn the_entry_scope_changes_no_callsite_row() {
    let summaries = summaries();
    let func = caller(6);
    let other = caller(3);
    let unscoped = without_entry_scope(|| render(&func, &summaries));
    assert!(unscoped.0.contains("Precondition"), "the fixture yields rows: {}", unscoped.0);

    assert_eq!(render(&func, &summaries), unscoped, "bare");
    {
        // The per-body lane's shape: a metered generation, its memos bound to another
        // function first.
        let _outer = crate::gen_work_scope();
        let _other_rows = render(&other, &summaries);
        assert_eq!(render(&func, &summaries), unscoped, "nested in a metered generation");
        assert!(!crate::gen_work_tripped(), "the fixture is far under the budget");
    }
    {
        // The function's own analysis frame is reused, not stacked.
        let _analysis = super::FuncAnalysisScope::enter(&func);
        assert_eq!(render(&func, &summaries), unscoped, "nested in the function's own frame");
    }
    {
        let _replay = super::row_replay_scope();
        assert_eq!(render(&func, &summaries), unscoped, "in a row-replay scope");
    }
    // Nothing memoized outlives a scope: a later unscoped call answers alike.
    assert_eq!(without_entry_scope(|| render(&func, &summaries)), unscoped, "after the scopes");
}

/// The producer's work is charged to an enclosing generation's meter, with the scope as
/// without it: the scope must neither hide that work (an unmetered scope nested there
/// restores the enclosing meter on exit) nor meter it twice.
#[test]
fn a_nested_producer_is_charged_to_the_enclosing_meter() {
    let summaries = summaries();
    let func = caller(4);
    let charged = |scoped: bool| {
        let _outer = crate::gen_work_scope();
        let run = || generate_callsite_precondition_vcs_attributed(&func, &summaries);
        let _rows = if scoped { run() } else { without_entry_scope(run) };
        crate::gen_work_used()
    };
    let unscoped = charged(false);
    assert!(unscoped > 0, "the fixture charges the enclosing meter: {unscoped}");
    let scoped = charged(true);
    assert!(scoped > 0, "scoped, the work is still charged to the enclosing meter: {scoped}");
}

/// Restores the default work budget on drop.
struct DefaultBudget;

impl Drop for DefaultBudget {
    fn drop(&mut self) {
        crate::gen_work::set_test_budget(None);
    }
}

/// `gen_work::enter_joined`: outermost the scope is unmetered (a budget of 1 cannot
/// trip it, and it records nothing), nested it is a depth increment that charges the
/// enclosing meter, whose trip and work outlive it.
#[test]
fn the_joined_work_scope_is_unmetered_outermost_and_joins_when_nested() {
    crate::gen_work::set_test_budget(Some(1));
    let _restore = DefaultBudget;
    {
        let _joined = crate::gen_work_scope_joined();
        assert!(!crate::gen_work::record(5), "outermost, nothing trips");
        assert!(!crate::gen_work_tripped());
        assert_eq!(crate::gen_work_used(), 0, "outermost, nothing is recorded");
    }
    {
        let _outer = crate::gen_work_scope();
        assert!(!crate::gen_work::record(1), "1 is within a budget of 1");
        {
            let _joined = crate::gen_work_scope_joined();
            assert!(crate::gen_work::record(1), "nested, the enclosing meter is charged");
        }
        assert!(crate::gen_work_tripped(), "the trip is the enclosing generation's");
        assert_eq!(crate::gen_work_used(), 2, "and so is the work");
    }
    // The negative control: an unmetered scope in the same place hides the work.
    {
        let _outer = crate::gen_work_scope();
        assert!(!crate::gen_work::record(1));
        {
            let _unmetered = crate::gen_work_scope_unmetered();
            assert!(!crate::gen_work::record(1));
        }
        assert!(!crate::gen_work_tripped(), "the unmetered scope's work is not charged");
        assert_eq!(crate::gen_work_used(), 1);
    }
}

/// The compiler's standalone assertion-refutation entry also visits every call
/// destination while assembling exact wrapping-result definitions. Its lowered final assert
/// gives this scaling fixture a real candidate and a target coverage record.
fn refutation_caller(sites: usize) -> VerifiableFunction {
    let mut func = caller(sites);
    let cond = func.body.locals.len();
    func.body.locals.push(LocalDecl { index: cond, ty: Ty::Bool, name: None });
    let last = func.body.blocks.last_mut().unwrap();
    last.stmts.push(Statement::Assign {
        place: Place::local(cond),
        rvalue: Rvalue::BinaryOp(
            BinOp::Gt,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(0, 32)),
        ),
        span: SourceSpan::default(),
    });
    last.terminator = Terminator::SwitchInt {
        discr: Operand::Move(Place::local(cond)),
        targets: vec![(0, BlockId(sites + 1))],
        otherwise: BlockId(sites + 2),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    func.body.blocks.push(BasicBlock {
        id: BlockId(sites + 1),
        stmts: vec![],
        terminator: Terminator::Call {
            func: "core::panicking::panic".into(),
            args: vec![],
            dest: Place::local(0),
            target: None,
            unwind: UnwindEdge::Unreachable,
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: crate::sep_engine::tests::fixture_key("core::panicking::panic"),
        },
    });
    func.body.blocks.push(BasicBlock {
        id: BlockId(sites + 2),
        stmts: vec![],
        terminator: Terminator::Return,
    });
    func
}

fn refutation(func: &VerifiableFunction) -> super::AssertRefutationCandidates {
    let context = crate::VcgenContext::for_function(func.def_path.clone());
    super::generate_full_assert_refutation_candidates_with_context(func, &context)
}

fn refutation_work(func: &VerifiableFunction) -> AnalysisMemoStats {
    // Production has no retired-oracle/uncached-scan differential. Keep that witness
    // enabled in the parity tests; omit it only when counting production work here.
    super::legacy_version_oracle::without_differential(|| {
        crate::reset_analysis_memo_stats();
        let found = refutation(func);
        assert!(!found.vcs().is_empty(), "the fixture must emit actual refutation candidates");
        assert_eq!(found.coverage().target_blocks().count(), 1);
        assert!(found.coverage().declined_target_blocks().is_empty());
        crate::analysis_memo_stats()
    })
}

#[test]
fn standalone_refutation_memo_reduces_whole_body_work() {
    let (small, large) = (refutation_caller(4), refutation_caller(32));
    let (old_small, old_large) =
        without_entry_scope(|| (refutation_work(&small), refutation_work(&large)));
    let (new_small, new_large) = (refutation_work(&small), refutation_work(&large));
    eprintln!(
        "standalone refutation work: old4={old_small:?} old32={old_large:?} new4={new_small:?} new32={new_large:?}"
    );
    assert!(old_small.body_scan_items > 0, "the negative control must scan the body");
    assert!(
        new_large.body_scan_items < old_large.body_scan_items,
        "the standalone entry must avoid the per-question whole-body scans"
    );
    assert!(
        u128::from(new_large.body_scan_items) * u128::from(old_small.body_scan_items)
            < u128::from(old_large.body_scan_items) * u128::from(new_small.body_scan_items),
        "the scoped scan work must grow more slowly than the unscoped negative control"
    );
}

#[test]
fn standalone_refutation_memo_preserves_candidates_coverage_and_effective_views() {
    let plain = refutation_caller(6);
    let mut projected = plain.clone();
    projected.preconditions.push(Formula::Gt(
        Box::new(Formula::Add(Box::new(Formula::var("x", Sort::Int)), Box::new(Formula::Int(1)))),
        Box::new(Formula::Int(0)),
    ));
    projected.body.blocks.last_mut().unwrap().terminator = Terminator::TailCall {
        func: "example::finish".into(),
        args: vec![],
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key("example::finish"),
    };
    assert!(matches!(projected.with_tail_calls_expanded(), std::borrow::Cow::Owned(_)));
    for func in [&plain, &projected] {
        let expected = without_entry_scope(|| format!("{:?}", refutation(func)));
        assert!(!refutation(func).vcs().is_empty());
        // The cost control must also cover owned semantic projections, not only
        // the original function address. Otherwise a frame opened too early could
        // pass formula parity while quietly falling back to whole-body scans.
        let unscoped_work = without_entry_scope(|| refutation_work(func));
        let scoped_work = refutation_work(func);
        assert!(scoped_work.body_scan_items < unscoped_work.body_scan_items);
        assert_eq!(format!("{:?}", refutation(func)), expected, "standalone");
        {
            let other = refutation_caller(2);
            let _other = super::FuncAnalysisScope::enter(&other);
            assert_eq!(format!("{:?}", refutation(func)), expected, "foreign outer frame");
        }
        {
            let _own = super::FuncAnalysisScope::enter(func);
            assert_eq!(format!("{:?}", refutation(func)), expected, "own original frame");
        }
        {
            let _outer = crate::gen_work_scope();
            assert_eq!(format!("{:?}", refutation(func)), expected, "nested meter");
            assert!(!crate::gen_work_tripped());
            assert!(crate::gen_work_used() > 0, "the existing meter must still be charged");
        }
        {
            let _replay = super::row_replay_scope();
            assert_eq!(format!("{:?}", refutation(func)), expected, "row replay");
        }
        let context = crate::VcgenContext::for_function(func.def_path.clone());
        let mut rows = trust_types::vc_context::VcContext::default();
        let found = super::generate_full_assert_refutation_candidates_with_context_rows(
            func, &context, &mut rows,
        );
        assert_eq!(format!("{found:?}"), expected, "compiler-facing row entry");
        assert_eq!(without_entry_scope(|| format!("{:?}", refutation(func))), expected);
    }
}

#[test]
fn standalone_refutation_memo_keeps_budget_refusal_and_drops_its_frame() {
    let mut func = refutation_caller(6);
    let original = format!("{:?}", refutation(&func));
    crate::gen_work::set_test_budget(Some(1));
    {
        let _restore = DefaultBudget;
        let found = refutation(&func);
        assert!(found.vcs().is_empty(), "the existing drop-only work trip must still refuse");
        assert_eq!(found.coverage().declined_target_blocks(), vec![BlockId(7)]);
    }
    // Mutation is legal again only after the borrowed entry guard was dropped. A
    // same-address function with a changed body must not inherit its previous memo.
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
        span: SourceSpan::default(),
    });
    let expected = without_entry_scope(|| format!("{:?}", refutation(&func)));
    assert_ne!(expected, original, "the changed input must alter a real candidate/coverage");
    assert_eq!(format!("{:?}", refutation(&func)), expected, "no stale analysis after return");
}
