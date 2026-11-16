//! The production generation's overflow-check origins (T3 C05, `super::overflow_origins`).
//!
//! WHAT THE CONSUMER DOES WITH THE INVENTORY, and therefore what these tests defend.
//! `rustc_mir_transform::trust_verify::elide_kernel_certified_checks` looks a
//! KernelCertified row's own sealed canonical string up in a table built from this
//! inventory and, on a `Unique(bb)` hit, REWRITES `bb`'s `Assert(Overflow)` terminator to
//! a `Goto`, deleting a live runtime overflow check. Three properties make that safe:
//!
//!   (O) ORIGIN. Each row is paired with the block that produced it, through the sort
//!       and the splice that move rows after the walk.
//!   (E) EXACTNESS. Each row is the row the generation returned, byte for byte: the
//!       join key is the formula-inclusive canonical JSON of the whole row.
//!   (C) COMPLETENESS. `Unique` is a claim about the whole enumeration, so a walk cut
//!       short, a work-meter trip or a refused body gives no table, never a prefix.
//!   (S) SITE. Only a row an overflow `Assert` minted names its block as the origin of
//!       a check; a row an arithmetic statement minted in the same block is listed as
//!       a statement, so the compiler never resolves its key to that block.

use std::time::Instant;

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::vc_context::{Oracle, ParityCount, VcContext};
use trust_types::verify_budget::{VerifyBudgetGuard, WALL_POLL_INTERVAL};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
    VerificationCondition, VerificationResult,
};

use super::overflow_origins::{OriginSite, RowOrigins};
use super::safety::SafetyWalk;

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

/// A source span of its own for block `i`: line `line`, so the generation's sort by
/// location can move the block's row away from its walk position.
fn span(line: u32) -> SourceSpan {
    SourceSpan {
        file: "origins.rs".into(),
        line_start: line,
        col_start: 1,
        line_end: line,
        col_end: 9,
    }
}

/// A chain of `n` checked adds, each in its own block with its own `Assert(Overflow(Add))`,
/// the MIR shape the elision seam rewrites:
///
/// ```text
/// bb0: _t0 = CheckedAdd(_1, _2);  assert(!_t0.1, Overflow(Add)) -> bb1
/// ...
/// bbn: return
/// ```
///
/// `spans(i)` is block `i`'s span (`None`: the default span every synthetic body shares).
fn checked_add_chain(n: usize, spans: impl Fn(usize) -> Option<SourceSpan>) -> VerifiableFunction {
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
        LocalDecl { index: 1, ty: u32_ty(), name: Some("a".into()) },
        LocalDecl { index: 2, ty: u32_ty(), name: Some("b".into()) },
    ];
    for i in 0..n {
        locals.push(LocalDecl {
            index: 3 + i,
            ty: Ty::Tuple(vec![u32_ty(), Ty::Bool]),
            name: None,
        });
    }
    let mut blocks = Vec::with_capacity(n + 1);
    for i in 0..n {
        let tmp = 3 + i;
        let span = spans(i).unwrap_or_default();
        blocks.push(BasicBlock {
            id: BlockId(i),
            stmts: vec![Statement::Assign {
                place: Place::local(tmp),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: span.clone(),
            }],
            terminator: Terminator::Assert {
                unwind: UnwindEdge::Unreachable,
                cond: Operand::Copy(Place { local: tmp, projections: vec![Projection::Field(1)] }),
                expected: false,
                msg: trust_types::AssertMessage::Overflow(BinOp::Add),
                target: BlockId(i + 1),
                span,
            },
        });
    }
    blocks.push(BasicBlock { id: BlockId(n), stmts: vec![], terminator: Terminator::Return });
    VerifiableFunction {
        name: format!("chain{n}"),
        def_path: format!("test::chain{n}"),
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

/// Block `i` on line `100 - i`: the sort by location reverses the walk's block order.
fn reversed_spans(n: usize) -> impl Fn(usize) -> Option<SourceSpan> {
    move |i| Some(span(u32::try_from(100 - i.min(n)).unwrap_or(0)))
}

/// An inventory row with its row read back from the generation's context. Since T3 C07
/// the inventory names a row by its `RowId`; the compiler's table materializes each one
/// for its key, and so do these tests.
#[derive(Debug)]
struct OriginRow {
    block: BlockId,
    site: OriginSite,
    vc: VerificationCondition,
}

/// The inventory as these tests read it: `None` when there is no table.
struct Origins(Option<Vec<OriginRow>>);

impl Origins {
    fn complete(&self) -> Option<&[OriginRow]> {
        self.0.as_deref()
    }
}

type Generated =
    (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>, Origins);

/// The compiler's consumed generation, as the compiler calls it: into a fresh body
/// context.
fn consumed(func: &VerifiableFunction, rows: &mut VcContext) -> super::ConsumedGeneration {
    let context = crate::VcgenContext::for_function(func.def_path.clone());
    super::generate_vcs_with_discharge_and_overflow_origins(
        func,
        &crate::modular::SummaryDatabase::new(),
        false,
        &context,
        &FxHashSet::<(BlockId, usize)>::default(),
        rows,
    )
}

/// [`consumed`], with each inventory row read back from the context.
fn generate(func: &VerifiableFunction) -> Generated {
    let mut rows = VcContext::new();
    let generation = consumed(func, &mut rows);
    let origins = Origins(generation.overflow_origins.complete().map(|listed| {
        listed
            .iter()
            .map(|row| OriginRow {
                block: row.block,
                site: row.site,
                vc: rows
                    .materialize(row.vc)
                    .expect("an inventory row names a row of its generation's context")
                    .vc()
                    .clone(),
            })
            .collect()
    }));
    (generation.solver_vcs, generation.discharged, origins)
}

fn canonical(vc: &VerificationCondition) -> String {
    let value = trust_types::canonical_digest_json_value(vc).expect("a VC must canonicalize");
    serde_json::to_string(&value).expect("canonical JSON")
}

/// `bb<N>|<site>|<canonical row>` for each inventory row, sorted.
fn inventory_digests(rows: &[OriginRow]) -> Vec<String> {
    let mut out: Vec<String> = rows
        .iter()
        .map(|row| format!("bb{}|{:?}|{}", row.block.0, row.site, canonical(&row.vc)))
        .collect();
    out.sort();
    out
}

/// A walk whose rows an overflow `Assert` each minted, for the `RowOrigins` unit tests.
fn assert_walk(rows: Vec<(BlockId, VerificationCondition)>) -> SafetyWalk {
    let overflow_assert_rows = (0..rows.len()).collect();
    SafetyWalk { rows, overflow_assert_rows, truncated: false, row_capped: false }
}

fn is_add_overflow(vc: &VerificationCondition) -> bool {
    matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })
}

/// (O) and (E): every Add overflow row the generation returned is in the inventory,
/// byte for byte, paired with the block whose span it carries. The spans run against
/// the block order, so the generation's sort moves every row: an origin carried by
/// position and not moved with its row would land on the wrong block.
#[test]
fn each_emitted_overflow_row_is_paired_with_its_own_block() {
    let n = 12;
    let func = checked_add_chain(n, reversed_spans(n));
    let (solver_vcs, discharged, origins) = generate(&func);
    let rows = origins.complete().expect("an unbudgeted generation is complete");
    assert_eq!(rows.len(), n, "one Add-overflow origin per block");

    let mut emitted: Vec<String> = solver_vcs
        .iter()
        .chain(discharged.iter().map(|(vc, _)| vc))
        .filter(|vc| is_add_overflow(vc))
        .map(canonical)
        .collect();
    emitted.sort();
    let mut listed: Vec<String> = rows.iter().map(|row| canonical(&row.vc)).collect();
    listed.sort();
    assert_eq!(listed, emitted, "the inventory must hold exactly the rows the generation returned");

    for row in rows {
        assert_eq!(
            row.vc.location,
            span(u32::try_from(100 - row.block.0).expect("small")),
            "bb{} was paired with a row of another block",
            row.block.0
        );
        assert_eq!(row.site, OriginSite::Assert, "each row is its block's overflow Assert's");
    }
    let blocks: FxHashSet<usize> = rows.iter().map(|row| row.block.0).collect();
    assert_eq!(blocks.len(), n, "every block appears once");

    // Control: the sort really moved the rows. The walk emits bb0 first; after the sort
    // by location the first Add row is bb(n-1)'s.
    let first = solver_vcs.iter().find(|vc| is_add_overflow(vc)).expect("an Add row");
    assert_eq!(first.location, span(u32::try_from(100 - (n - 1)).expect("small")));
}

/// `RowOrigins::sort_by` leaves the rows in exactly the order `Vec::sort_by` does, ties
/// included (both are stable, and the comparator reads only the row).
#[test]
fn sorting_with_origins_is_the_plain_stable_sort() {
    // Lines with ties, out of order; blocks 0..8.
    let lines = [5, 3, 5, 1, 3, 5, 2, 1];
    let walk: Vec<_> = lines.iter().enumerate().map(|(block, line)| row(block, *line)).collect();
    let compare = |a: &VerificationCondition, b: &VerificationCondition| {
        a.location.line_start.cmp(&b.location.line_start)
    };
    let mut plain: Vec<VerificationCondition> = walk.iter().map(|(_, vc)| vc.clone()).collect();
    plain.sort_by(compare);
    // Tell the tied rows apart by their formula, so a reordering among ties shows.
    let walk: Vec<_> = walk
        .into_iter()
        .map(|(block, mut vc)| {
            vc.formula = trust_types::Formula::Int(i128::try_from(block.0).expect("small"));
            (block, vc)
        })
        .collect();
    let mut expected: Vec<VerificationCondition> = walk.iter().map(|(_, vc)| vc.clone()).collect();
    expected.sort_by(compare);
    let (mut vcs, mut origins) = RowOrigins::from_walk(assert_walk(walk));
    origins.sort_by(&mut vcs, compare);
    assert_eq!(format!("{vcs:?}"), format!("{expected:?}"));
    assert_eq!(plain.len(), vcs.len());
    let inventory = origins.finish(&vcs);
    for (index, vc) in vcs.iter().enumerate() {
        let trust_types::Formula::Int(block) = vc.formula else { panic!("tagged above") };
        let block = BlockId(usize::try_from(block).expect("small"));
        assert_eq!(inventory.origin(index), Some((block, OriginSite::Assert)));
    }
}

/// `diamonds` diamonds on the Bool argument `c`, then one more split on `c` into two
/// blocks that each `CheckedAdd(a, b)` at one span and `Assert(Overflow(Add))` it, the
/// shape one macro expanded in both arms of a match leaves:
///
/// ```text
/// bb(3k):   switchInt(c) -> [0: bb(3k+1), otherwise: bb(3k+2)]   (k < diamonds)
/// bb(3k+1), bb(3k+2): goto bb(3k+3)
/// bbH:      switchInt(c) -> [0: bbH+1, otherwise: bbH+2]           (H = 3 * diamonds)
/// bbH+1: goto bbH+3       bbH+2: goto bbH+4
/// bbH+3: _4 = CheckedAdd(a, b); assert(!_4.1, Overflow(Add)) -> bbH+5
/// bbH+4: _5 = CheckedAdd(a, b); assert(!_5.1, Overflow(Add)) -> bbH+5
/// bbH+5: return
/// ```
///
/// Each twin is reached by 2^(diamonds+1) routes. Past the walk's per-block path cap
/// (64) its guard collapses to the in-edge reachability, which for both twins is the
/// unguarded `goto`: the two rows then carry no path condition that tells them apart.
fn macro_twins(diamonds: usize) -> (VerifiableFunction, [usize; 2]) {
    let checked_add = |id: usize, tmp: usize, next: usize| BasicBlock {
        id: BlockId(id),
        stmts: vec![Statement::Assign {
            place: Place::local(tmp),
            rvalue: Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: span(7),
        }],
        terminator: Terminator::Assert {
            unwind: UnwindEdge::Unreachable,
            cond: Operand::Copy(Place { local: tmp, projections: vec![Projection::Field(1)] }),
            expected: false,
            msg: trust_types::AssertMessage::Overflow(BinOp::Add),
            target: BlockId(next),
            span: span(7),
        },
    };
    let split = |id: usize, on_zero: usize, otherwise: usize| BasicBlock {
        id: BlockId(id),
        stmts: vec![],
        terminator: Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(3)),
            targets: vec![(0, BlockId(on_zero))],
            otherwise: BlockId(otherwise),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    };
    let goto = |id: usize, to: usize| BasicBlock {
        id: BlockId(id),
        stmts: vec![],
        terminator: Terminator::Goto(BlockId(to)),
    };
    let mut blocks = Vec::new();
    for k in 0..diamonds {
        blocks.extend([split(3 * k, 3 * k + 1, 3 * k + 2), goto(3 * k + 1, 3 * k + 3)]);
        blocks.push(goto(3 * k + 2, 3 * k + 3));
    }
    let h = 3 * diamonds;
    blocks.extend([split(h, h + 1, h + 2), goto(h + 1, h + 3), goto(h + 2, h + 4)]);
    blocks.extend([checked_add(h + 3, 4, h + 5), checked_add(h + 4, 5, h + 5)]);
    blocks.push(BasicBlock { id: BlockId(h + 5), stmts: vec![], terminator: Terminator::Return });
    let pair = Ty::Tuple(vec![u32_ty(), Ty::Bool]);
    let func = VerifiableFunction {
        name: "twins".into(),
        def_path: "test::twins".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: u32_ty(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: u32_ty(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("c".into()) },
                LocalDecl { index: 4, ty: pair.clone(), name: None },
                LocalDecl { index: 5, ty: pair, name: None },
            ],
            blocks,
            arg_count: 3,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    (func, [h + 3, h + 4])
}

/// Byte-identical rows from distinct blocks, produced by the REAL generation, are BOTH
/// listed, each under its own block: the compiler's table marks a key `Ambiguous` only
/// if it is shown both (`OverflowCheckOrigins::from_pairs`, whose own test
/// `overflow_check_origins_fail_closed_for_identical_vcs_from_distinct_blocks` pins
/// that two blocks under one key resolve to nothing). A pass that merged identical rows,
/// or dropped a twin's origin, would leave the survivor `Unique` and license deleting
/// the other block's check on its proof.
#[test]
fn identical_rows_from_distinct_blocks_are_all_listed() {
    // Key -> the blocks the inventory lists under it, as the compiler's table groups it.
    let by_key = |rows: &[OriginRow]| -> FxHashMap<String, Vec<usize>> {
        let mut out: FxHashMap<String, Vec<usize>> = FxHashMap::default();
        for row in rows {
            out.entry(canonical(&row.vc)).or_default().push(row.block.0);
        }
        out
    };

    let (func, twins) = macro_twins(7);
    let (solver_vcs, discharged, origins) = generate(&func);
    let rows = origins.complete().expect("an unbudgeted generation is complete");
    let emitted: Vec<String> = solver_vcs
        .iter()
        .chain(discharged.iter().map(|(vc, _)| vc))
        .filter(|vc| is_add_overflow(vc))
        .map(canonical)
        .collect();
    assert_eq!(emitted.len(), 2, "the generation returns both twins' rows");
    assert_eq!(emitted[0], emitted[1], "the twins' rows are byte-identical");
    let keys = by_key(rows);
    assert_eq!(keys.len(), 1, "one key: {keys:?}");
    let mut blocks = keys.into_values().next().expect("one key");
    blocks.sort_unstable();
    assert_eq!(blocks, twins, "both twins are listed, each under its own block");
    assert!(rows.iter().all(|row| row.site == OriginSite::Assert));

    // Control: below the path cap each twin keeps its own path condition, the rows
    // differ, and each key has one block. So the fixture above shares a key because the
    // generation made the rows identical, not because of how this test reads them.
    let (func, twins) = macro_twins(6);
    let (_, _, origins) = generate(&func);
    let keys = by_key(origins.complete().expect("complete"));
    assert_eq!(keys.len(), 2, "control: below the cap the twins' rows differ");
    let mut blocks: Vec<usize> = keys.into_values().flatten().collect();
    blocks.sort_unstable();
    assert_eq!(blocks, twins);
}

/// (C) under EVERY step budget the inventory is either the complete one or no table,
/// never a proper prefix. The dense low range lands the cut at every position in the
/// walk; the geometric tail makes the sweep straddle the boundary.
#[test]
fn a_budgeted_generation_is_complete_or_absent_never_a_prefix() {
    let n = 24;
    let func = checked_add_chain(n, reversed_spans(n));
    let complete = {
        let (_, _, origins) = generate(&func);
        inventory_digests(origins.complete().expect("unbudgeted is complete"))
    };
    assert_eq!(complete.len(), n);

    let mut saw_refusal = false;
    let mut saw_completion = false;
    let ladder = (1u64..400).chain([1_000, 4_000, 16_000, 64_000, 256_000, 1_048_576, 4_194_304]);
    for steps in ladder {
        let _budget = VerifyBudgetGuard::install(None, steps);
        let (_, _, origins) = generate(&func);
        match origins.complete() {
            None => saw_refusal = true,
            Some(rows) => {
                saw_completion = true;
                assert_eq!(
                    inventory_digests(rows),
                    complete,
                    "steps={steps}: a table was returned that is not the complete one ({} of \
                     {n} rows)",
                    rows.len(),
                );
            }
        }
    }
    // Control: the sweep must straddle the boundary, or the assertions above are vacuous.
    assert!(saw_refusal, "the step sweep never truncated the generation: the pin is vacuous");
    assert!(saw_completion, "the step sweep never completed the generation: the pin is vacuous");
}

/// (C) against a trip no later poll observes: the clock is read only every
/// `WALL_POLL_INTERVAL` charged steps, so after a clock trip at the walk's first poll the
/// next polls answer `false` and the walk carries on. The walk ORs a latched read into
/// its flag, and the inventory must be refused. Control: the same steps with no deadline
/// complete, so the trip below is the clock read.
#[test]
fn a_trip_no_later_poll_observes_gives_no_table() {
    let func = checked_add_chain(4, reversed_spans(4));
    {
        let _budget = VerifyBudgetGuard::install(None, WALL_POLL_INTERVAL);
        let (_, _, origins) = generate(&func);
        assert!(
            origins.complete().is_some_and(|rows| rows.len() == 4),
            "control: {WALL_POLL_INTERVAL} steps must complete this generation"
        );
    }
    let _budget = VerifyBudgetGuard::install(Some(Instant::now()), WALL_POLL_INTERVAL);
    let (_, _, origins) = generate(&func);
    assert!(origins.complete().is_none(), "a table built over a tripped budget must be refused");
}

/// (C) against a trip INSIDE the interval environment the generation discharges and
/// augments its rows with (trust-fixpoint-deadline).
///
/// The interval fixpoint behind `merged_interval_environment` polls the ambient budget
/// and answers a trip with its refusal (every block Top). The walk's `truncated` flag is
/// read before that fixpoint runs, so a trip there is invisible to it: what refuses the
/// table is the read made when the generation returns. A table that came back from such
/// a generation would hold rows augmented with the refused environment, which are not
/// the rows of a generation that fitted its budget. The ladder of
/// `a_budgeted_generation_is_complete_or_absent_never_a_prefix` need not land a budget
/// in that window, so this test finds the first budget the whole generation fits in and
/// walks EVERY budget below it down through the fixpoint: each one trips, and each one
/// must give no table.
#[test]
fn a_trip_inside_the_interval_environment_gives_no_table() {
    use trust_types::verify_budget::exhausted_readonly;

    use crate::fn_memo::{analysis_memo_stats, reset_analysis_memo_stats};

    let func = checked_add_chain(4, reversed_spans(4));
    let complete = {
        let (_, _, origins) = generate(&func);
        inventory_digests(origins.complete().expect("unbudgeted is complete"))
    };
    // (tripped, the table's digests, interval-fixpoint units done) under a `steps` budget.
    let run = |steps: u64| {
        let _budget = VerifyBudgetGuard::install(None, steps);
        reset_analysis_memo_stats();
        let (_, _, origins) = generate(&func);
        let table = origins.complete().map(inventory_digests);
        (exhausted_readonly(), table, analysis_memo_stats().interval_fixpoint_units)
    };
    // The first budget the whole generation fits in; tripping is monotone in the budget.
    let mut hi = 1u64;
    while run(hi).0 {
        hi *= 2;
        assert!(hi < 1 << 40, "the generation never fits a budget");
    }
    let mut lo = hi / 2;
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if run(mid).0 {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    let first_untripped = hi;
    let (tripped, table, control_units) = run(first_untripped);
    assert!(!tripped);
    assert_eq!(table.expect("an untripped generation is complete"), complete);
    assert!(control_units > 0, "the generation must run the interval fixpoint");

    // Walk down until the trip lands before the fixpoint's first unit: from there on it
    // is the walk's own flag that refuses.
    let mut inside_environment = 0u64;
    let mut steps = first_untripped - 1;
    while steps > 0 {
        let (tripped, table, units) = run(steps);
        assert!(tripped, "steps={steps}: below the first untripped budget every run trips");
        assert!(
            table.is_none(),
            "steps={steps}: a generation whose budget tripped returned a table of {} rows \
             ({units} of {control_units} interval-fixpoint units done)",
            table.map_or(0, |rows| rows.len()),
        );
        if units == 0 {
            break;
        }
        if units < control_units {
            inside_environment += 1;
        }
        steps -= 1;
    }
    // ANTI-VACUITY: a poll that trips is not counted as a unit, so a run that did some
    // but not all of the control's units tripped in one of the fixpoint's own polls.
    assert!(
        inside_environment > 0,
        "ANTI-VACUITY: no budget tripped inside the interval fixpoint ({control_units} \
         units in the control); the pin above never saw the window it is for"
    );
}

struct WorkBudget;

impl WorkBudget {
    fn install(budget: usize) -> Self {
        crate::gen_work::set_test_budget(Some(budget));
        Self
    }
}

impl Drop for WorkBudget {
    fn drop(&mut self) {
        crate::gen_work::set_test_budget(None);
    }
}

/// A work-meter trip degrades the whole function to one `Unknown` row, and the
/// inventory to no table: a table may not be built from leaf-degraded rows.
#[test]
fn a_work_meter_trip_gives_no_table() {
    let func = checked_add_chain(16, reversed_spans(16));
    let _work = WorkBudget::install(1);
    let (solver_vcs, discharged, origins) = generate(&func);
    // Control: the meter tripped (the degraded function has no solver row).
    assert!(solver_vcs.is_empty(), "control: a 1-node work budget must trip: {solver_vcs:?}");
    assert!(
        discharged.iter().any(|(vc, _)| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "TrustVcGenWorkBudgetExceeded"
        )),
        "control: the degraded function carries the work-budget row"
    );
    assert!(origins.complete().is_none());
}

/// An honestly EMPTY table (`Some(&[])`) is not a refused one (`None`). Collapsing the
/// two would turn "could not enumerate" into "there is nothing to elide".
#[test]
fn an_empty_table_is_distinguishable_from_a_refused_one() {
    let no_arithmetic = checked_add_chain(0, |_| None);
    let (_, _, origins) = generate(&no_arithmetic);
    assert!(
        origins.complete().is_some_and(<[_]>::is_empty),
        "a function with no overflow assert has an EMPTY table, not an absent one"
    );

    let func = checked_add_chain(24, reversed_spans(24));
    let _budget = VerifyBudgetGuard::install(None, 1);
    let (_, _, origins) = generate(&func);
    assert!(origins.complete().is_none(), "a generation cut short must refuse, not report empty");
}

/// A row the interval analysis discharges is listed too, as it was discharged: the
/// table's ambiguity rule must see every row that can share a key, whichever bucket
/// it left in. `_t = CheckedAdd(const 5, const 7)` cannot overflow, and the interval
/// pre-pass proves it.
#[test]
fn a_discharged_row_is_listed_as_it_left() {
    let mut func = checked_add_chain(2, reversed_spans(2));
    let BasicBlock { stmts, .. } = &mut func.body.blocks[1];
    let Statement::Assign { rvalue, .. } = &mut stmts[0] else { panic!("the chain's add") };
    *rvalue = Rvalue::CheckedBinaryOp(
        BinOp::Add,
        Operand::Constant(ConstValue::Uint(5, 32)),
        Operand::Constant(ConstValue::Uint(7, 32)),
    );
    let (solver_vcs, discharged, origins) = generate(&func);
    let rows = origins.complete().expect("complete");
    let bb1: Vec<&VerificationCondition> =
        rows.iter().filter(|row| row.block.0 == 1).map(|row| &row.vc).collect();
    let [row] = bb1.as_slice() else { panic!("bb1 listed {} times: {rows:?}", bb1.len()) };
    assert!(
        discharged.iter().any(|(vc, _)| canonical(vc) == canonical(row)),
        "bb1's row must leave in the discharged bucket, as listed: {discharged:?}"
    );
    assert!(!solver_vcs.iter().any(|vc| vc.location == span(99)), "control: bb1 is discharged");
    // bb0's row is not dischargeable and leaves augmented, as listed.
    let bb0 = rows.iter().find(|row| row.block.0 == 0).expect("bb0 listed");
    assert!(solver_vcs.iter().any(|vc| canonical(vc) == canonical(&bb0.vc)));
}

/// A body the generator refuses (here: no blocks, so it is malformed) has no table.
#[test]
fn a_refused_body_has_no_table() {
    let mut func = checked_add_chain(2, reversed_spans(2));
    func.body.blocks.clear();
    let (_, _, origins) = generate(&func);
    assert!(origins.complete().is_none());
}

fn row(block: usize, line: u32) -> (BlockId, VerificationCondition) {
    (
        BlockId(block),
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (u32_ty(), u32_ty()) },
            function: trust_types::Symbol::intern("f"),
            location: span(line),
            formula: trust_types::Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
    )
}

/// The alignment guard: a tagged row that is still an Add row but now carries another
/// location means the origins no longer line up with the rows, and there is no table.
#[test]
fn a_misaligned_origin_gives_no_table() {
    let (mut vcs, origins) = RowOrigins::from_walk(assert_walk(vec![row(0, 1), row(1, 2)]));
    vcs.swap(0, 1);
    let inventory = origins.finish(&vcs);
    assert!(inventory.is_truncated(), "a row moved without its origin must refuse the table");

    // Control: the same rows, moved through `sort_by`, keep their origins.
    let (mut vcs, mut origins) = RowOrigins::from_walk(assert_walk(vec![row(0, 1), row(1, 2)]));
    origins.sort_by(&mut vcs, |a, b| b.location.line_start.cmp(&a.location.line_start));
    let inventory = origins.finish(&vcs);
    assert!(!inventory.is_truncated());
    assert_eq!(inventory.origin(0), Some((BlockId(1), OriginSite::Assert)));
    assert_eq!(inventory.origin(1), Some((BlockId(0), OriginSite::Assert)));
}

/// Rows inserted before a tagged row shift its origin with it; a row rewritten out of
/// the elision kinds loses its origin without refusing the table.
#[test]
fn inserted_rows_shift_origins_and_rewritten_rows_drop_theirs() {
    let (mut vcs, mut origins) = RowOrigins::from_walk(assert_walk(vec![row(0, 1), row(1, 2)]));
    let filler = VerificationCondition { kind: VcKind::DivisionByZero, ..row(9, 50).1 };
    origins.inserted(1, 2);
    vcs.splice(1..1, [filler.clone(), filler]);
    vcs[0].kind = VcKind::UnsupportedMir { kind: "Rewritten".into(), detail: String::new() };
    let inventory = origins.finish(&vcs);
    assert!(!inventory.is_truncated());
    assert_eq!(inventory.origin(0), None, "a rewritten row is no longer joinable");
    assert_eq!(inventory.origin(1), None);
    assert_eq!(inventory.origin(2), None);
    assert_eq!(
        inventory.origin(3),
        Some((BlockId(1), OriginSite::Assert)),
        "bb1's row moved two places down"
    );

    // More origins than rows: a pass dropped a row, so the origins cannot be trusted.
    let (mut vcs, origins) = RowOrigins::from_walk(assert_walk(vec![row(0, 1), row(1, 2)]));
    vcs.pop();
    assert!(origins.finish(&vcs).is_truncated());
}

/// An origin that lands on a row of another kind than `UnsupportedMir`, or on a demoted
/// row at another location, is a misalignment too: dropping that origin quietly could
/// leave the twin of the row it belonged to `Unique`.
#[test]
fn an_origin_on_a_row_it_cannot_have_tagged_gives_no_table() {
    let (mut vcs, origins) = RowOrigins::from_walk(assert_walk(vec![row(0, 1), row(1, 2)]));
    vcs[1].kind = VcKind::DivisionByZero;
    assert!(origins.finish(&vcs).is_truncated(), "an origin on a division row");

    let (mut vcs, origins) = RowOrigins::from_walk(assert_walk(vec![row(0, 1), row(1, 2)]));
    vcs[1].kind = VcKind::UnsupportedMir { kind: "Rewritten".into(), detail: String::new() };
    vcs[1].location = span(7);
    assert!(origins.finish(&vcs).is_truncated(), "a demoted row that moved");

    // Control: demoted in place, it only loses its origin.
    let (mut vcs, origins) = RowOrigins::from_walk(assert_walk(vec![row(0, 1), row(1, 2)]));
    vcs[1].kind = VcKind::UnsupportedMir { kind: "Rewritten".into(), detail: String::new() };
    let inventory = origins.finish(&vcs);
    assert!(!inventory.is_truncated());
    assert_eq!(inventory.origin(0), Some((BlockId(0), OriginSite::Assert)));
    assert_eq!(inventory.origin(1), None);
}

/// (S) A block that ends in `Assert(Overflow(Add))` and also holds a PLAIN integer
/// `Add` (the shape an operation inlined from a crate built without overflow checks
/// leaves) emits two Add-overflow rows. Both are listed, so both count toward
/// `Ambiguous`, but only the Assert's row is listed as the Assert's: the plain
/// operation's proof never licenses removing the block's check.
#[test]
fn an_arithmetic_statement_row_is_listed_as_a_statement() {
    let mut func = checked_add_chain(1, |_| Some(span(21)));
    func.body.locals.push(LocalDecl { index: 4, ty: u32_ty(), name: Some("sum".into()) });
    func.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: span(20),
        },
    );
    let (_, _, origins) = generate(&func);
    let rows = origins.complete().expect("complete");
    let mut listed: Vec<(usize, OriginSite, u32)> =
        rows.iter().map(|row| (row.block.0, row.site, row.vc.location.line_start)).collect();
    listed.sort_by_key(|(_, _, line)| *line);
    assert_eq!(
        listed,
        [(0, OriginSite::Statement, 20), (0, OriginSite::Assert, 21)],
        "the plain Add's row is a statement's, the checked Add's the Assert's: {rows:?}"
    );
}

/// (S) The walk's list of Assert rows must describe the walk's own rows: an index past
/// the rows (or out of order) gives no table, never a guessed site.
#[test]
fn an_assert_index_that_names_no_row_gives_no_table() {
    let mut walk = assert_walk(vec![row(0, 1), row(1, 2)]);
    walk.overflow_assert_rows.push(7);
    let (vcs, origins) = RowOrigins::from_walk(walk);
    assert!(origins.finish(&vcs).is_truncated());

    let mut walk = assert_walk(vec![row(0, 1), row(1, 2)]);
    walk.overflow_assert_rows = vec![1, 0];
    let (vcs, origins) = RowOrigins::from_walk(walk);
    assert!(origins.finish(&vcs).is_truncated(), "an index list out of order");

    // Control: the same rows with an ascending list in range keep their table.
    let (vcs, origins) = RowOrigins::from_walk(assert_walk(vec![row(0, 1), row(1, 2)]));
    assert!(!origins.finish(&vcs).is_truncated());
}

/// (E) through a term-`Ite` rewrite, the class the replay mis-rendered (C05-GATE-1):
/// the walk emits `signed_clamp::c2_add`'s Add row with a term-level `Ite`, and
/// `generate_vcs_impl` lifts it to guards. The inventory holds the row as EMITTED, so
/// the key the compiler joins is the one a `KernelCertified` row seals. Control: the
/// walk's own row for that block does carry an `Ite`, and differs from the emitted one.
#[test]
fn a_row_rewritten_through_a_term_ite_is_listed_as_emitted() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("../../tests/data/signed_clamp_cast_c2_add.json"))
            .expect("the captured MIR fixture must deserialize");
    let (solver_vcs, discharged, origins) = generate(&func);
    let rows = origins.complete().expect("complete");
    let [row] = rows else { panic!("one Add row expected: {rows:?}") };
    assert_eq!(row.site, OriginSite::Assert);
    let emitted: Vec<String> = solver_vcs
        .iter()
        .chain(discharged.iter().map(|(vc, _)| vc))
        .filter(|vc| is_add_overflow(vc))
        .map(canonical)
        .collect();
    assert_eq!(emitted, [canonical(&row.vc)], "the inventory row is the emitted row");
    assert!(!super::formula_contains_ite(&row.vc.formula), "the emitted row has no term Ite");

    let walk = super::safety::generate_v2_safety_vcs_impl_with_origins_checked(&func, None);
    let raw: Vec<&VerificationCondition> = walk
        .rows
        .iter()
        .filter(|(block, vc)| *block == row.block && is_add_overflow(vc))
        .map(|(_, vc)| vc)
        .collect();
    let [raw] = raw.as_slice() else { panic!("control: one walk row for bb{}", row.block.0) };
    assert!(super::formula_contains_ite(&raw.formula), "control: the walk's row has a term Ite");
    assert_ne!(canonical(raw), canonical(&row.vc), "control: the rewrite changed the row");
}

/// The lines of `body` that name the identifier `word` (comments stripped) and are not one
/// of `shapes`, and the shapes no line had. With `checked = Some((first, before))`, a line
/// starting with `first` must follow the code line `before`.
fn census<'a>(
    body: &str,
    word: &str,
    shapes: &[(&'a str, &str)],
    checked: Option<(&str, &str)>,
) -> (Vec<String>, Vec<&'a str>) {
    let names_word = |code: &str| {
        let bytes = code.as_bytes();
        let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
        code.match_indices(word).any(|(at, _)| {
            (at == 0 || !is_word(bytes[at - 1]))
                && bytes.get(at + word.len()).is_none_or(|next| !is_word(*next))
        })
    };
    let mut seen = vec![0usize; shapes.len()];
    let mut unclassified = Vec::new();
    let mut previous = "";
    for line in body.lines() {
        let code = line.split("//").next().unwrap_or_default().trim();
        if code.is_empty() {
            continue;
        }
        if names_word(code) {
            match shapes.iter().position(|(shape, _)| code.starts_with(shape)) {
                Some(index) => {
                    seen[index] += 1;
                    if let Some((first, before)) = checked
                        && code.starts_with(first)
                    {
                        assert_eq!(previous, before, "`{code}` must follow `{before}`");
                    }
                }
                None => unclassified.push(code.to_string()),
            }
        }
        previous = code;
    }
    let stale =
        shapes.iter().zip(&seen).filter(|(_, n)| **n == 0).map(|((shape, _), _)| *shape).collect();
    (unclassified, stale)
}

/// (O) by construction of the source. The origins ride beside the generation's rows by
/// index, in its row sink (`super::row_sink`, T3 C08s), and `RowOrigins::finish`'s
/// alignment guard compares only a row's span and op, so it cannot see two rows of one
/// macro expansion trade places. What keeps them in place is that nothing moves a row but
/// the sink's tracked sort and splice. This census reads both sides and requires every line
/// that names the rows to be one of the shapes below, each with why it keeps the alignment:
/// `generate_vcs_impl_with_origins` (entry.rs) names the rows only through its sink, whose
/// every call is listed (and no line of it names a `vcs` list), and the sink (row_sink.rs)
/// touches its `entries` only as listed. A new use (a `retain`, a `sort`, an `insert`, a
/// callee given the rows) fails here until it is classified, and one that moves rows needs a
/// `RowOrigins` counterpart first. A shape that no longer occurs fails too, so the lists
/// cannot go stale. C08s moved the C05 census from `vcs` in entry.rs onto the sink: the
/// passes that were `&mut vcs` shapes are per-row calls inside the sink, which no longer
/// sees the list while they run.
#[test]
fn every_use_of_the_row_list_keeps_the_origins_aligned() {
    const ENTRY: &str = include_str!("entry.rs");
    const SINK: &str = include_str!("row_sink.rs");
    const ENTRY_SHAPES: &[(&str, &str)] = &[
        ("let mut sink = RowSink::new(func, rows);", "the generation's one sink"),
        ("sink.walk(walk, keep);", "the walk's rows and origins, first (a late walk is counted)"),
        ("sink.lane(", "a lane the sort orders: joins after every tagged row, with no origin"),
        ("sink.sort_by_location();", "the tracked stable sort: each origin moves with its row"),
        ("sink.append(", "appends after the sort, with no origin"),
        ("let unsafe_rows_at = sink.mark();", "reads the length"),
        (
            "sink.append_sep(vc, &sep_facts, block_id, sep_op, &mut unsafe_coverage);",
            "appends one wrapped separation row, with no origin",
        ),
        (
            "sink.splice_at(unsafe_rows_at, unsafe_rows);",
            "the tracked insertion (`RowSink::splice_at` records it in the origins)",
        ),
        ("return sink.refuse(vc);", "the refusal: one row and no table"),
        ("sink.finish()", "the return"),
    ];
    const SINK_SHAPES: &[(&str, &str)] = &[
        ("entries: Vec<SinkRow>,", "the field"),
        ("entries: Vec::new(),", "starts empty"),
        (
            "if self.entries.is_empty() && self.phase == Phase::BeforeSort {",
            "reads: a walk keeps its origins only when it joins first",
        ),
        ("self.origins.sort_by(&mut self.entries,", "the tracked stable sort"),
        ("self.entries.len()", "reads the length (`mark`)"),
        ("let at = at.min(self.entries.len());", "reads the length"),
        (
            "self.entries.splice(at..at, taken);",
            "an insertion; `self.origins.inserted` records it on the line before (checked)",
        ),
        (
            "let RowSink { entries, mut origins, out_of_phase, .. } = self;",
            "takes the rows to return them",
        ),
        ("entries.into_iter().map(|row| (row.vc, row.id)).unzip();", "the rows, in their order"),
        ("self.entries.push(row);", "appends; an appended row has no origin"),
    ];
    let start = ENTRY
        .find("pub(super) fn generate_vcs_impl_with_origins(")
        .expect("entry.rs defines generate_vcs_impl_with_origins");
    let body = &ENTRY[start..];
    let body = &body[..body.find("\n}\n").expect("the function ends at a closing brace")];
    let body = body.split_once('\n').map_or("", |(_, rest)| rest);

    let (unclassified, stale) = census(body, "sink", ENTRY_SHAPES, None);
    assert!(
        unclassified.is_empty(),
        "uses of the sink in generate_vcs_impl_with_origins that the census does not classify; \
         say why each keeps the origins aligned (or track it in RowOrigins): {unclassified:#?}"
    );
    assert!(stale.is_empty(), "entry census shapes that no longer occur: {stale:?}");
    let (lists, _) = census(body, "vcs", &[], None);
    assert!(lists.is_empty(), "generate_vcs_impl_with_origins names a row list: {lists:#?}");

    let (unclassified, stale) = census(
        SINK,
        "entries",
        SINK_SHAPES,
        Some(("self.entries.splice(", "self.origins.inserted(at, taken.len());")),
    );
    assert!(
        unclassified.is_empty(),
        "uses of the sink's entries that the census does not classify: {unclassified:#?}"
    );
    assert!(stale.is_empty(), "sink census shapes that no longer occur: {stale:?}");
}

/// The row cap latches no budget, so the compiler's checkpoint never sees it. A capped
/// walk is refused where it is read: the generation is one fail-closed `Unknown` row
/// and has no table, never a prefix of the function's rows posing as its obligation
/// set (which could report it proved by omission). Control: the same body under a cap
/// it does not reach keeps every row and its table.
#[test]
fn a_row_capped_walk_is_one_unknown_row_and_no_table() {
    let func = checked_add_chain(6, reversed_spans(6));
    let capped = {
        let _cap = super::safety::TestRowCap::install(3);
        let walk = super::safety::generate_v2_safety_vcs_impl_with_origins_checked(&func, None);
        assert!(walk.row_capped && walk.truncated, "control: a cap of 3 rows stops a 6-row walk");
        assert!(
            !trust_types::verify_budget::exhausted_readonly(),
            "control: the cap latches no budget, so no checkpoint would see it"
        );
        generate(&func)
    };
    let (solver_vcs, discharged, origins) = capped;
    assert!(solver_vcs.is_empty(), "no solver row survives a capped walk: {solver_vcs:?}");
    let [(vc, result)] = discharged.as_slice() else {
        panic!("one refusal row expected: {discharged:?}")
    };
    assert!(
        matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "TrustVcGenRowCapExceeded"),
        "{vc:?}"
    );
    assert!(!result.is_proved());
    assert!(origins.complete().is_none());

    let _cap = super::safety::TestRowCap::install(7);
    let (solver_vcs, discharged, origins) = generate(&func);
    let add_rows = solver_vcs
        .iter()
        .chain(discharged.iter().map(|(vc, _)| vc))
        .filter(|vc| is_add_overflow(vc));
    assert_eq!(add_rows.count(), 6, "control: a cap the walk does not reach changes nothing");
    assert_eq!(origins.complete().map(<[_]>::len), Some(6));
}

/// T3 C07: every inventory row names, by id, a row the generation returned, and that id
/// reads back as the returned row; every returned row went through the row oracle, which
/// agreed on each. T3 C08s: the ids are the ones the rows got at the generation's sink and
/// carried through the discharge split, each returned row has its own, and every row the
/// context holds (the returned rows, and the pre-augment row of each augmented solver row)
/// went through the oracle.
#[test]
fn origins_by_row_id_name_the_returned_rows() {
    let func = checked_add_chain(4, |_| None);
    let mut rows = VcContext::new();
    let generation = consumed(&func, &mut rows);
    assert_eq!(generation.solver_rows.len(), generation.solver_vcs.len());
    assert_eq!(generation.discharged_rows.len(), generation.discharged.len());
    let listed =
        generation.overflow_origins.complete().expect("an unbudgeted generation is complete");
    assert!(!listed.is_empty(), "the chain emits overflow rows");
    for origin in listed {
        let returned = generation
            .solver_rows
            .iter()
            .zip(&generation.solver_vcs)
            .chain(
                generation
                    .discharged_rows
                    .iter()
                    .zip(generation.discharged.iter().map(|(vc, _)| vc)),
            )
            .find(|(id, _)| **id == Some(origin.vc))
            .map(|(_, vc)| vc)
            .expect("an origin's id is the id of a returned row");
        let read_back = rows.materialize(origin.vc).expect("a row of this context");
        assert_eq!(canonical(read_back.vc()), canonical(returned));
    }
    let discharged = generation.discharged.iter().map(|(vc, _)| vc);
    let returned: Vec<_> = generation
        .solver_rows
        .iter()
        .zip(&generation.solver_vcs)
        .chain(generation.discharged_rows.iter().zip(discharged))
        .collect();
    let mut distinct = FxHashSet::default();
    for (id, vc) in &returned {
        let id = id.expect("every returned row has an id in its context");
        assert!(distinct.insert(id), "two returned rows share {id:?}");
        let read_back = rows.materialize(id).expect("a row of this context");
        assert_eq!(canonical(read_back.vc()), canonical(vc));
    }
    let parity = rows.parity(Oracle::Row);
    assert_eq!(parity, ParityCount { rows: rows.len() as u64, mismatches: 0 });
    assert!(parity.rows >= returned.len() as u64, "{parity:?} for {} rows", returned.len());
    // The same table, keyed as the compiler keys it, as the tree-carrying inventory gave.
    let (_, _, origins) = generate(&func);
    let by_tree = inventory_digests(origins.complete().expect("complete"));
    let mut by_id: Vec<String> = listed
        .iter()
        .map(|row| {
            let vc = rows.materialize(row.vc).expect("a row of this context");
            format!("bb{}|{:?}|{}", row.block.0, row.site, canonical(vc.vc()))
        })
        .collect();
    by_id.sort();
    assert_eq!(by_id, by_tree);
}

/// T3 C07p: `generate_vcs_rows` and its extra-precondition variant write every row they
/// return into the caller's context through the row oracle, and return the rows the
/// tree-only entries return. A regeneration of the same function into the same context
/// is the first generation's rows again, node for node.
#[test]
fn generations_into_one_context_share_their_rows_nodes() {
    let func = checked_add_chain(4, |_| None);
    let tree = super::generate_vcs(&func);
    let mut rows = VcContext::new();
    let first = super::generate_vcs_rows(&func, &mut rows);
    let second = super::generate_vcs_rows(&func, &mut rows);
    assert!(!tree.is_empty());
    assert_eq!((first.len(), second.len()), (tree.len(), tree.len()));
    for (vc, tree_vc) in first.iter().chain(&second).zip(tree.iter().chain(&tree)) {
        assert_eq!(canonical(vc), canonical(tree_vc));
    }
    let n = tree.len();
    assert_eq!(rows.parity(Oracle::Row), ParityCount { rows: 2 * n as u64, mismatches: 0 });
    let ids: Vec<_> = rows.row_ids().collect();
    assert_eq!(ids.len(), 2 * n);
    for (a, b) in ids[..n].iter().zip(&ids[n..]) {
        let first_row = rows.row(*a).expect("a row of this context");
        let second_row = rows.row(*b).expect("a row of this context");
        assert_eq!(first_row, second_row);
    }

    let extra = trust_types::Formula::Bool(true);
    let strengthened = super::generate_vcs_with_extra_precondition_rows(&func, &extra, &mut rows);
    let strengthened_tree = super::generate_vcs_with_extra_precondition(&func, &extra);
    assert_eq!(strengthened.len(), strengthened_tree.len());
    for (vc, tree_vc) in strengthened.iter().zip(&strengthened_tree) {
        assert_eq!(canonical(vc), canonical(tree_vc));
    }
    let total = (2 * n + strengthened.len()) as u64;
    assert_eq!(rows.parity(Oracle::Row), ParityCount { rows: total, mismatches: 0 });
}
