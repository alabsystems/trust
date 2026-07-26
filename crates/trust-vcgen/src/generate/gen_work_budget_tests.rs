use std::sync::Mutex;

use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Rvalue, Sort, SourceSpan,
    Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

/// Serialize overrides on test-harness threads that may be reused.
static GEN_WORK_TEST_LOCK: Mutex<()> = Mutex::new(());

/// Test budget sized so the deliberately-HUGE fixture trips while no ordinary parallel
/// test function (a handful of small `Ty` nodes) can trip on a leaked env value.
const GEN_WORK_TEST_BUDGET: usize = 10_000;
const GEN_WORK_FAT_FIELDS: usize = 20_000; // ~20_001 ty nodes, well over the budget

struct GenWorkBudgetGuard;

impl GenWorkBudgetGuard {
    fn new(budget: usize) -> Self {
        crate::gen_work::set_test_budget(Some(budget));
        Self
    }
}

impl Drop for GenWorkBudgetGuard {
    fn drop(&mut self) {
        crate::gen_work::set_test_budget(None);
    }
}

struct BundleBudgetGuard;

impl BundleBudgetGuard {
    fn new(budget: usize) -> Self {
        crate::set_bundle_adt_test_budget(Some(budget));
        Self
    }
}

impl Drop for BundleBudgetGuard {
    fn drop(&mut self) {
        crate::set_bundle_adt_test_budget(None);
    }
}

/// A fat struct `Ty::Adt` with `n` scalar fields — `n + 1` structural `Ty` nodes.
/// This is the on-main shape of the kernel's recursive `Expr`/`ExprKind` clusters
/// (deeply-nested `Ty::Adt`, NOT a `Ty::Datatype` variant — that does not exist here).
fn fat_adt_ty(n: usize) -> Ty {
    let fields: Vec<(String, Ty)> =
        (0..n).map(|i| (format!("f{i}"), Ty::Int { width: 64, signed: true })).collect();
    Ty::adt("Fat", fields)
}

fn func_with_locals(name: &str, locals: Vec<LocalDecl>, return_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: name.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `gen_work_scope` resets the meter on the outermost entry and `place_ty` meters each
/// materialized clone; once the cumulative work crosses an (overridden tiny) budget the
/// meter trips and `place_ty` returns the cheap fail-closed leaf instead of cloning the
/// fat tree. SOUNDNESS of the leaf: it is the recursive-ADT `Unsupported` marker (never
/// a provable type).
#[test]
fn gen_work_meter_trips_and_place_ty_degrades_to_leaf() {
    let _guard = GEN_WORK_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let _budget = GenWorkBudgetGuard::new(GEN_WORK_TEST_BUDGET);
    let func = func_with_locals(
        "explode",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: fat_adt_ty(GEN_WORK_FAT_FIELDS), name: Some("e".into()) },
        ],
        Ty::Unit,
    );
    {
        let _scope = crate::gen_work_scope();
        assert!(!crate::gen_work_tripped(), "fresh scope must start un-tripped");
        // First materialization of the fat local (>budget nodes) blows the budget: the
        // meter trips and the result is the fail-closed leaf.
        let ty = crate::place_ty(&func, &Place::local(1)).expect("local exists");
        assert!(crate::gen_work_tripped(), "fat clone over the budget must trip the meter");
        match ty {
            Ty::Unsupported { kind, detail } => {
                assert_eq!(kind, "TyKind::Adt");
                assert!(
                    detail.starts_with("recursive"),
                    "leaf must be the fail-closed recursive-ADT marker: {detail}"
                );
            }
            other => panic!("tripped place_ty must return the fail-closed leaf, got {other:?}"),
        }
    }
    // A FRESH scope resets the meter (per-function independence).
    {
        let _scope = crate::gen_work_scope();
        assert!(!crate::gen_work_tripped(), "a new outermost scope must reset the meter");
    }
}

/// A function whose generation explodes past the work budget degrades WHOLESALE to a
/// single fail-closed `UnsupportedMir` obligation (which preclassifies to Unknown,
/// never Proved). This is the SOUNDNESS core: the bound only ADDS Unknown — it never
/// manufactures a PROVE and never a guaranteed-violation.
#[test]
fn generate_vcs_degrades_whole_function_on_work_budget_trip() {
    let _guard = GEN_WORK_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let _budget = GenWorkBudgetGuard::new(GEN_WORK_TEST_BUDGET);
    let mut func = func_with_locals(
        "gen_explode",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: fat_adt_ty(GEN_WORK_FAT_FIELDS), name: Some("e".into()) },
            LocalDecl { index: 2, ty: fat_adt_ty(GEN_WORK_FAT_FIELDS), name: Some("f".into()) },
        ],
        Ty::Unit,
    );
    // Statements that read the fat-Adt locals so the VC-gen walk materializes
    // their types through `place_ty` (driving the meter over budget).
    func.body.blocks[0].stmts = vec![
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
            span: SourceSpan::default(),
        },
    ];
    let vcs = super::generate_vcs(&func);
    assert_eq!(vcs.len(), 1, "a tripped function degrades to a SINGLE obligation");
    match &vcs[0].kind {
        VcKind::UnsupportedMir { kind, .. } => {
            assert_eq!(
                kind, "TrustVcGenWorkBudgetExceeded",
                "the degrade must be the work-budget marker"
            );
        }
        other => panic!("tripped function must degrade to UnsupportedMir, got {other:?}"),
    }
    // SOUNDNESS: the degraded obligation's formula is `true` — SAT, so it can NEVER be
    // reported Proved (UNSAT); the compiler preclassifies it Unknown.
    assert!(
        matches!(vcs[0].formula, Formula::Bool(true)),
        "the fail-closed degrade formula must be Bool(true) (never provable)"
    );
}

/// With the work budget explicitly disabled (`0`) the meter never trips and
/// `place_ty` returns the real (modeled) type — byte-identical to the pre-bound
/// behavior. The bound is therefore opt-outable and verdict-neutral when off.
#[test]
fn gen_work_budget_zero_disables_the_bound() {
    let _guard = GEN_WORK_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let _budget = GenWorkBudgetGuard::new(0);
    let func = func_with_locals(
        "no_bound",
        vec![LocalDecl { index: 0, ty: fat_adt_ty(40), name: None }],
        Ty::Unit,
    );
    let _scope = crate::gen_work_scope();
    let ty = crate::place_ty(&func, &Place::local(0)).expect("local exists");
    assert!(!crate::gen_work_tripped(), "budget=0 disables the bound — never trips");
    assert!(
        matches!(ty, Ty::Adt { .. }),
        "with the bound off, place_ty returns the real modeled Adt"
    );
}

/// The OTHER metered hot path: `place_sort` → `place_sort_from_declared_type` →
/// `sort_for_ty` builds an O(datatype-size) `Sort` WITHOUT cloning the `Ty` (it
/// bypasses `place_ty`). It must ALSO meter the modeled-type work and, once tripped,
/// hand back the cheap fail-closed `Sort::Int` — this is the path that actually drives
/// the `build_ind_app` stall (O(places × statements) `place_sort` queries over the fat
/// `Adt` sort).
#[test]
fn gen_work_meter_trips_via_place_sort_sort_build() {
    let _guard = GEN_WORK_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let _budget = GenWorkBudgetGuard::new(GEN_WORK_TEST_BUDGET);
    let func = func_with_locals(
        "sort_explode",
        vec![LocalDecl {
            index: 0,
            ty: fat_adt_ty(GEN_WORK_FAT_FIELDS),
            name: Some("e".into()),
        }],
        Ty::Unit,
    );
    {
        let _scope = crate::gen_work_scope();
        // place_sort on the fat-Adt local builds an O(datatype-size) Sort; metered
        // against the budget, it trips and returns the cheap Int sort.
        let sort = crate::place_sort(&func, &Place::local(0));
        assert!(
            crate::gen_work_tripped(),
            "building a fat Adt Sort over a tiny budget must trip the meter"
        );
        assert_eq!(
            sort,
            Some(Sort::Int),
            "a tripped place_sort must return the cheap fail-closed Int sort"
        );
    }
}

/// T2 CORE PROPERTY (peak-vs-cumulative metering): a single MODEST local (well
/// under budget) re-queried many times — the real shape that stalled `eval`, where
/// the VC walk calls `local_ty` / `place_sort` / `place_ty` on the same handful of
/// locals across every statement — must NOT trip. Under the OLD cumulative meter,
/// `reps × nodes` blew the budget and the whole function degraded to Unknown (a
/// spurious drop); with the per-function place memo each repeat replays the cached
/// result for an O(1) charge and the function stays proved. Uses the module's
/// serialized `GenWorkBudgetGuard` budget override (thread-local, not ambient env).
#[test]
fn many_reclones_of_one_modest_local_does_not_trip() {
    let _guard = GEN_WORK_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let _budget = GenWorkBudgetGuard::new(GEN_WORK_TEST_BUDGET);
    // ~2001 nodes: one materialization is comfortably under the 10_000 budget, but
    // 50 cumulative re-queries (~100_050) would have tripped the OLD meter tenfold.
    const MODEST_FIELDS: usize = 2_000;
    const REPS: usize = 50;
    let func = func_with_locals(
        "reread",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: fat_adt_ty(MODEST_FIELDS), name: Some("e".into()) },
        ],
        Ty::Unit,
    );
    {
        let _scope = crate::gen_work_scope();
        for i in 0..REPS {
            // Interleave all three metered query paths on the SAME local — after the
            // first materialization every repeat must charge O(1), not the tree size.
            let ty = crate::local_ty_ref(&func, 1).expect("local exists");
            assert!(
                matches!(ty, Ty::Adt { .. }),
                "re-query {i}: modest local must return the real Adt, never the degraded leaf"
            );
            let _ = crate::place_sort(&func, &Place::local(1));
            let _ = crate::place_ty(&func, &Place::local(1));
            assert!(
                !crate::gen_work_tripped(),
                "re-query {i}: memoized repeat charges stay under budget — must not trip"
            );
        }
    }
}

/// verifier-perf (place-type memo): repeated OWNED `place_ty` queries of the SAME
/// place within one scope charge the meter the full materialization cost ONCE (the
/// first query — the real work) and O(1) per repeat (a memo HIT), and every replay
/// is byte-identical to the first result. This pins the fix for the moderate-tree ×
/// huge-query-count product (ny-cert's `crown::Relu1Problem::certify`) tripping
/// `TrustVcGenWorkBudgetExceeded` with no pathological type involved.
#[test]
fn place_ty_memo_charges_full_cost_once_then_constant() {
    let _guard = GEN_WORK_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let _budget = GenWorkBudgetGuard::new(GEN_WORK_TEST_BUDGET);
    // 2_001 structural nodes: big enough that ~5 uncached re-clones would trip the
    // 10_000 test budget, small enough to be memoized (≤ MAX_MEMOIZED_TY_NODES).
    let func = func_with_locals(
        "memo_hit",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: fat_adt_ty(2_000), name: Some("e".into()) },
        ],
        Ty::Unit,
    );
    let _scope = crate::gen_work_scope();
    let first = crate::place_ty(&func, &Place::local(1)).expect("local exists");
    assert!(matches!(first, Ty::Adt { .. }), "first query returns the real modeled Adt");
    assert_eq!(crate::gen_work_used(), 2_001, "the MISS is charged at full node cost");
    // 20 repeats: uncached these would charge 40_020 more nodes and trip the meter;
    // memoized they charge HIT_COST each and stay far under budget.
    for _ in 0..20 {
        let repeat = crate::place_ty(&func, &Place::local(1)).expect("local exists");
        assert_eq!(repeat, first, "a memo HIT must replay the byte-identical type");
    }
    assert_eq!(crate::gen_work_used(), 2_021, "each HIT charges O(1), not the tree size");
    assert!(!crate::gen_work_tripped(), "memoized repeats must not trip the meter");
}

/// The `Sort` twin: `place_sort` → `place_sort_from_declared_type` re-builds an
/// O(datatype-size) `Sort` per query (bypassing `place_ty`); the memo charges that
/// build ONCE and replays the identical Sort for a `HIT_COST` charge afterwards.
#[test]
fn place_sort_memo_charges_full_cost_once_then_constant() {
    let _guard = GEN_WORK_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let _budget = GenWorkBudgetGuard::new(GEN_WORK_TEST_BUDGET);
    let func = func_with_locals(
        "sort_memo_hit",
        vec![LocalDecl { index: 0, ty: fat_adt_ty(2_000), name: Some("e".into()) }],
        Ty::Unit,
    );
    let _scope = crate::gen_work_scope();
    let first = crate::place_sort(&func, &Place::local(0));
    assert!(first.is_some(), "declared-type sort must resolve");
    assert_eq!(crate::gen_work_used(), 2_001, "the MISS is charged at full node cost");
    let repeat = crate::place_sort(&func, &Place::local(0));
    assert_eq!(repeat, first, "a memo HIT must replay the byte-identical Sort");
    assert_eq!(crate::gen_work_used(), 2_002, "the HIT charges O(1), not the tree size");
    assert!(!crate::gen_work_tripped(), "memoized repeats must not trip the meter");
}

/// Meter fidelity: a resolved tree LARGER than the memo's node cap is never cached,
/// so the kernel-scale fat types the work budget exists for keep paying — and being
/// charged — full cost on EVERY query, and repeated materialization still trips the
/// budget exactly as pre-memo. Memoization must not un-bound the pathological shape.
#[test]
fn place_ty_memo_skips_oversized_types_so_meter_still_trips() {
    let _guard = GEN_WORK_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let _budget = GenWorkBudgetGuard::new(GEN_WORK_TEST_BUDGET);
    // TWO DISTINCT oversized locals: each 6_001 nodes, over
    // MAX_MEMOIZED_TY_NODES (4_096) so the memo SKIPS caching each, and each
    // under the 10_000 budget individually. The meter is PEAK-work: it
    // charges each LOCAL once per scope (CHARGED dedup — re-querying the SAME
    // local charges 0), so the trip must come from a SECOND DISTINCT local.
    // This proves memo-skipped oversized types are STILL charged: the first
    // local stays under budget, the second crosses it and trips.
    let func = func_with_locals(
        "memo_skip_fat",
        vec![
            LocalDecl { index: 0, ty: fat_adt_ty(6_000), name: Some("e0".into()) },
            LocalDecl { index: 1, ty: fat_adt_ty(6_000), name: Some("e1".into()) },
        ],
        Ty::Unit,
    );
    let _scope = crate::gen_work_scope();
    let first = crate::place_ty(&func, &Place::local(0)).expect("local 0 exists");
    assert!(matches!(first, Ty::Adt { .. }), "first fat local is under budget");
    assert!(!crate::gen_work_tripped(), "one fat local must not trip yet");
    let second = crate::place_ty(&func, &Place::local(1)).expect("local 1 exists");
    assert!(
        crate::gen_work_tripped(),
        "a second DISTINCT uncacheable fat local keeps full-cost metering and must trip"
    );
    assert!(
        matches!(second, Ty::Unsupported { .. }),
        "post-trip materialization must degrade to the fail-closed leaf"
    );
}

/// verifier-perf: the bundle-path fat-`Ty::Adt` budget (`enforce_datatype_budget`)
/// borrows an in-budget function unchanged and degrades an over-budget one's recursive
/// `Ty::Adt` declared types to the fail-closed recursive-ADT marker. SOUNDNESS: the
/// degraded type is the SAME `Ty::Unsupported { kind: "TyKind::Adt", detail:
/// "recursive…" }` shape the extractor already produces — drop-only, never false-prove.
#[test]
fn enforce_datatype_budget_borrows_in_budget_and_degrades_over_budget() {
    let _guard = GEN_WORK_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    // In-budget (default budget): borrowed, unchanged.
    let small = func_with_locals(
        "small",
        vec![LocalDecl { index: 0, ty: fat_adt_ty(8), name: None }],
        Ty::Unit,
    );
    let cow = crate::enforce_datatype_budget(&small);
    assert!(matches!(cow, std::borrow::Cow::Borrowed(_)), "in-budget func must be borrowed");

    // Over-budget via a tiny explicit override: owned clone, recursive Adt degraded.
    let _budget = BundleBudgetGuard::new(100);
    let big = func_with_locals(
        "big",
        vec![LocalDecl { index: 0, ty: fat_adt_ty(GEN_WORK_FAT_FIELDS), name: None }],
        Ty::Unit,
    );
    let cow = crate::enforce_datatype_budget(&big);
    assert!(matches!(cow, std::borrow::Cow::Owned(_)), "over-budget func must be owned");
    match &cow.body.locals[0].ty {
        Ty::Unsupported { kind, detail } => {
            assert_eq!(kind, "TyKind::Adt");
            assert!(
                detail.starts_with("recursive"),
                "degraded type must be the fail-closed recursive-ADT marker: {detail}"
            );
        }
        other => panic!("over-budget Adt must degrade to the recursive marker, got {other:?}"),
    }
}

/// verifier-perf (whole-function gate): a function with an aggregate-heavy block
/// (many datatype-field operands) over the `MAX_SEMANTIC_GUARD_WORK` product budget
/// is gated, and `generate_vcs` degrades it WHOLESALE to a single fail-closed
/// `UnsupportedMir` BEFORE the explosion-prone formula/guard machinery runs.
/// SOUNDNESS: DROP-ONLY — the marker preclassifies to Unknown, never Proved.
#[test]
fn func_exceeds_vcgen_budget_gates_aggregate_heavy_function() {
    // A single Aggregate rvalue with many operands drives the per-block
    // stmts × agg_operands work (1 × 450_000) over the 400_000 budget —
    // identical arithmetic under the old global product (1 × 1 × 450_000),
    // so this pin is invariant across the cost-model recalibration.
    let n_operands = 450_000usize;
    let operands: Vec<Operand> =
        (0..n_operands).map(|_| Operand::Constant(trust_types::ConstValue::Unit)).collect();
    let mut func = func_with_locals(
        "agg_explode",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) }],
        Ty::Unit,
    );
    func.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Aggregate(trust_types::AggregateKind::Tuple, operands),
        span: SourceSpan::default(),
    }];
    assert!(
        super::func_exceeds_vcgen_budget(&func),
        "an aggregate-heavy function must exceed the VC-gen budget"
    );
    let vcs = super::generate_vcs(&func);
    assert_eq!(vcs.len(), 1, "an over-budget function degrades to a SINGLE obligation");
    match &vcs[0].kind {
        VcKind::UnsupportedMir { kind, .. } => {
            assert_eq!(
                kind, "TrustVcGenBudgetExceeded",
                "the degrade must be the whole-function budget marker"
            );
        }
        other => panic!("over-budget function must degrade to UnsupportedMir, got {other:?}"),
    }
    // SOUNDNESS: the degraded obligation's formula is `Bool(true)` (SAT) — never Proved.
    assert!(
        matches!(vcs[0].formula, Formula::Bool(true)),
        "the fail-closed degrade formula must be Bool(true) (never provable)"
    );
    // A small function stays UNDER budget (gate is far above ordinary functions).
    let small = func_with_locals(
        "small",
        vec![LocalDecl { index: 0, ty: Ty::u8(), name: None }],
        Ty::Unit,
    );
    assert!(
        !super::func_exceeds_vcgen_budget(&small),
        "an ordinary small function must NOT be gated"
    );
}

/// One `stmts`-long block of `AggregateKind::Tuple` assigns, `ops_per_stmt`
/// operands each — the building block for the budget cost-model tests.
fn aggregate_block(id: usize, stmts: usize, ops_per_stmt: usize) -> BasicBlock {
    let stmt = |_i: usize| Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Aggregate(
            trust_types::AggregateKind::Tuple,
            (0..ops_per_stmt)
                .map(|_| Operand::Constant(trust_types::ConstValue::Unit))
                .collect(),
        ),
        span: SourceSpan::default(),
    };
    BasicBlock {
        id: BlockId(id),
        stmts: (0..stmts).map(stmt).collect(),
        terminator: Terminator::Return,
    }
}

/// Cost-model fix pin (reports/vcgen-budget-cost-model-2026-07-06.md): a
/// many-small-blocks builder — the aterm-spec `ty_model!` constructor shape —
/// must NOT be gated. 300 blocks × 5 stmts × 2-operand aggregates:
///   per-block sum:  Σ 5 × (5×2) = 300 × 50            = 15_000  ≤ 400_000 ✓
///   OLD global product: 300 × 1500 × 3000             = 1.35e9  > 400_000 ✗
/// so this test FAILS on the pre-fix global-triple-product formula (a 90_000×
/// over-estimate of the summed per-block work) — it pins the recalibration.
/// Blocks (300 ≤ 1600) and stmts (1500 ≤ 8000) stay under the absolute caps, so
/// only the work term is in play.
#[test]
fn many_small_blocks_builder_not_gated() {
    let mut func = func_with_locals(
        "ty_model_builder_shape",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) }],
        Ty::Unit,
    );
    func.body.blocks = (0..300).map(|i| aggregate_block(i, 5, 2)).collect();
    assert!(
        !super::func_exceeds_vcgen_budget(&func),
        "a many-small-blocks builder (Σ per-block work = 15k) must NOT be gated"
    );
}

/// The dense single-block shape the gate exists for must STILL gate under the
/// per-block-sum model: 1 block, 2000 stmts of 500-operand aggregates gives a
/// per-block product of 2000 × (2000×500) = 2e9 ≫ 400_000. Stmts (2000 ≤ 8000)
/// and blocks (1 ≤ 1600) are under the absolute caps — the WORK term gates.
/// SOUNDNESS: gating stays fail-closed (drop-only, see the fn doc).
#[test]
fn concentrated_block_still_gated() {
    let mut func = func_with_locals(
        "dense_kernel_shape",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) }],
        Ty::Unit,
    );
    func.body.blocks = vec![aggregate_block(0, 2000, 500)];
    assert!(
        super::func_exceeds_vcgen_budget(&func),
        "a concentrated aggregate-dense block (per-block work 2e9) must gate"
    );
}

/// `enum_variant_tag_set` returns the POSITIONAL tags for a `Ty::Datatype`
/// (built positionally) and the ACTUAL `VariantDef.discriminant` tags for a
/// `Ty::Adt` — including a `#[repr]` enum's NON-CONTIGUOUS discriminants. The
/// non-contiguous case is the soundness pin: a `0..n-1` interval would (false-)
/// exclude a valid `d = 10`, so the bound MUST use the real tag set.
#[test]
fn enum_variant_tag_set_uses_actual_discriminants() {
    use trust_types::VariantDef;
    // Positional datatype (Expr/Level/Name cluster): tags are 0..n.
    let dt = Ty::Datatype {
        name: "clean_kernel::Expr".into(),
        variants: vec![("App".into(), vec![]), ("Var".into(), vec![]), ("Lam".into(), vec![])],
    };
    assert_eq!(super::enum_variant_tag_set(&dt), Some(vec![0, 1, 2]));
    // #[repr] enum with explicit non-contiguous discriminants: tags are {5, 10}.
    let adt = Ty::Adt { adt_kind: None, layout: None, 
        name: "Repr".into(),
        fields: vec![],
        variants: vec![
            VariantDef { name: "A".into(), discriminant: 5, fields: vec![] },
            VariantDef { name: "B".into(), discriminant: 10, fields: vec![] },
        ],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    assert_eq!(
        super::enum_variant_tag_set(&adt),
        Some(vec![5, 10]),
        "a #[repr] enum's bound must be its REAL discriminants {{5,10}}, never 0..1 \
         (an unsound interval would false-exclude the valid d=10)"
    );
    // A struct (no variants), a by-name datatype reference (empty variants), and a
    // scalar are NOT enums — no tag set, so no (potentially-vacuous) bound.
    assert_eq!(
        super::enum_variant_tag_set(&Ty::Adt { adt_kind: None, layout: None, 
            name: "S".into(),
            fields: vec![("x".into(), Ty::Bool)],
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, }),
        None
    );
    assert_eq!(
        super::enum_variant_tag_set(&Ty::Datatype { name: "ByRef".into(), variants: vec![] }),
        None
    );
    assert_eq!(super::enum_variant_tag_set(&Ty::Int { width: 32, signed: false }), None);
}

/// A function reading an enum discriminant: `d = Discriminant(e)` where `e` is a
/// 3-variant `#[repr]` enum (`Ty::Adt`). `build_discriminant_variant_range_facts`
/// must emit `d ∈ {tags}` over the dest var — the membership fact that refutes
/// a phantom tag outside the variant range.
fn func_reading_enum_discriminant() -> VerifiableFunction {
    use trust_types::VariantDef;
    let e = Ty::Adt { adt_kind: None, layout: None, 
        name: "clean_kernel::Expr".into(),
        variants: vec![
            VariantDef { name: "App".into(), discriminant: 0, fields: vec![] },
            VariantDef { name: "Var".into(), discriminant: 1, fields: vec![] },
            VariantDef { name: "Lam".into(), discriminant: 2, fields: vec![] },
        ],
        fields: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let mut func = func_with_locals(
        "reads_discr",
        vec![
            LocalDecl { index: 0, ty: Ty::Int { width: 64, signed: true }, name: None },
            LocalDecl { index: 1, ty: e, name: Some("e".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::Int { width: 64, signed: true },
                name: Some("d".into()),
            },
        ],
        Ty::Int { width: 64, signed: true },
    );
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Discriminant(Place::local(1)),
        span: SourceSpan::default(),
    });
    func
}

#[test]
fn discriminant_range_facts_bound_the_dest_to_variant_tags() {
    let func = func_reading_enum_discriminant();
    let facts = super::build_discriminant_variant_range_facts(&func);
    assert!(
        !facts.is_empty(),
        "a `d = Discriminant(e)` read of a 3-variant enum must emit a range fact"
    );
    let dest_name = crate::place_to_var_name(&func, &Place::local(2));
    let s = format!("{facts:?}");
    assert!(
        s.contains(&dest_name),
        "the range fact must reference the discriminant dest var `{dest_name}`: {s}"
    );
    let generated_name = crate::discriminant_formula_var_name("e");
    assert!(
        facts.iter().any(|fact| fact.free_variables().contains(&generated_name)),
        "the range fact must use the same generated discriminant name as CHC lowering: {s}"
    );
    let has_membership =
        facts.iter().any(|f| matches!(f, Formula::Or(cases) if cases.len() == 3));
    assert!(
        has_membership,
        "expected a 3-way membership disjunction `d ∈ {{0,1,2}}`: {facts:?}"
    );
}

/// SOUNDNESS: a `Discriminant` read whose source is NOT a modeled enum (a struct,
/// a by-name datatype reference, or a scalar) must emit NO range fact — bounding a
/// non-enum discriminant would invent a fact the type does not justify.
#[test]
fn discriminant_range_facts_skip_non_enum_source() {
    let mut func = func_with_locals(
        "no_enum",
        vec![
            LocalDecl { index: 0, ty: Ty::Int { width: 64, signed: true }, name: None },
            // A struct ADT (variants: []) — its discriminant has no variant range.
            LocalDecl {
                index: 1,
                ty: Ty::Adt { adt_kind: None, layout: None, 
                    name: "S".into(),
                    fields: vec![("x".into(), Ty::Bool)],
                    variants: vec![],
                    disc_index_safe: false,
                    faithful_enum_repr: None, enum_layout: None, },
                name: Some("s".into()),
            },
        ],
        Ty::Int { width: 64, signed: true },
    );
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Discriminant(Place::local(1)),
        span: SourceSpan::default(),
    });
    assert!(
        super::build_discriminant_variant_range_facts(&func).is_empty(),
        "a discriminant read on a non-enum (struct) source must emit no range fact"
    );
}

/// Trust (P0 enumdisc-narrowing-cast false proof): the tag-set fact emitted
/// on a NARROWING cast destination must be the tags' IMAGE under the cast
/// (each tag folded mod 2^dest_width), never the raw declared set. For
/// `#[repr(u16)] enum E { A = 0, B = 260, C = 512 }` and `_c = _d as u8`,
/// the raw fact `_c ∈ {0, 260, 512}` intersected with the u8 type range
/// `[0, 255]` collapsed to `{0}` — a vacuous premise that false-PROVED the
/// out-of-bounds `a[(e as u8) as usize]` on `[u8; 4]` (E::B → index 4).
#[test]
fn discriminant_range_facts_fold_tags_across_narrowing_cast() {
    use trust_types::VariantDef;
    let e = Ty::Adt { adt_kind: None, layout: None, 
        name: "t::E".into(),
        variants: vec![
            VariantDef { name: "A".into(), discriminant: 0, fields: vec![] },
            VariantDef { name: "B".into(), discriminant: 260, fields: vec![] },
            VariantDef { name: "C".into(), discriminant: 512, fields: vec![] },
        ],
        fields: vec![],
        disc_index_safe: true,
        faithful_enum_repr: None, enum_layout: None, };
    let mut func = func_with_locals(
        "narrow_cast",
        vec![
            LocalDecl { index: 0, ty: Ty::Int { width: 8, signed: false }, name: None },
            LocalDecl { index: 1, ty: e, name: Some("e".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::Int { width: 16, signed: false },
                name: Some("dtemp".into()),
            },
            LocalDecl {
                index: 3,
                ty: Ty::Int { width: 8, signed: false },
                name: Some("cnarrow".into()),
            },
        ],
        Ty::Int { width: 8, signed: false },
    );
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Discriminant(Place::local(1)),
        span: SourceSpan::default(),
    });
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Cast(
            Operand::Copy(Place::local(2)),
            Ty::Int { width: 8, signed: false },
        ),
        span: SourceSpan::default(),
    });
    let facts = super::build_discriminant_variant_range_facts(&func);
    let cast_name = crate::place_to_var_name(&func, &Place::local(3));
    let cast_fact = facts
        .iter()
        .find(|f| format!("{f:?}").contains(&cast_name))
        .expect("a tag-set fact must attach to the narrowing-cast dest");
    let s = format!("{cast_fact:?}");
    // The folded image {0, 4} (260 % 256 == 4, 512 % 256 == 0, deduped) —
    // NEVER the raw tags, whose intersection with [0, 255] is vacuous.
    assert!(
        matches!(cast_fact, Formula::Or(cases) if cases.len() == 2),
        "cast-dest fact must be the deduped 2-way folded set {{0, 4}}: {s}"
    );
    assert!(
        s.contains("Int(4)") && !s.contains("Int(260)") && !s.contains("Int(512)"),
        "cast-dest fact must carry 260 % 256 == 4 and no un-folded tag: {s}"
    );
    // The discriminant temp itself (repr-typed, value-preserving read) keeps
    // the RAW declared tag set.
    let disc_name = crate::place_to_var_name(&func, &Place::local(2));
    let disc_fact = facts
        .iter()
        .find(|f| format!("{f:?}").contains(&disc_name))
        .expect("the raw tag-set fact must still attach to the discriminant temp");
    let ds = format!("{disc_fact:?}");
    assert!(
        ds.contains("Int(260)") && ds.contains("Int(512)"),
        "discriminant-temp fact must keep the raw declared tags: {ds}"
    );
}

/// `truncate_nonneg_tag_as_int` mirrors Rust `as` semantics exactly for a
/// non-negative source: identity when the value fits, mod-2^width truncation
/// when it does not, sign-bit reinterpretation for a signed destination.
#[test]
fn truncate_nonneg_tag_as_int_matches_rust_as_semantics() {
    use super::truncate_nonneg_tag_as_int as f;
    // Narrowing to u8: 260 as u8 == 4, 512 as u8 == 0.
    assert_eq!(f(0, 8, false), 0);
    assert_eq!(f(260, 8, false), 260u16 as u8 as i128);
    assert_eq!(f(512, 8, false), 512u16 as u8 as i128);
    // Non-narrowing: identity.
    assert_eq!(f(260, 16, false), 260);
    assert_eq!(f(5, 8, false), 5);
    assert_eq!(f(127, 8, true), 127);
    // Signed destination sign-bit wrap: 200 as i8 == -56, 255 as i8 == -1.
    assert_eq!(f(200, 8, true), 200u16 as i8 as i128);
    assert_eq!(f(255, 8, true), -1);
    assert_eq!(f(300, 16, true), 300);
    // Width >= 128: every non-negative i128 is value-preserving.
    assert_eq!(f(i128::MAX, 128, false), i128::MAX);
    assert_eq!(f(i128::MAX, 128, true), i128::MAX);
    // Extreme sub-128 width does not overflow the fold arithmetic:
    // 2^127 - 1 fits u127 unchanged; as a 127-bit SIGNED value its sign
    // bit is set, so it wraps to -1.
    assert_eq!(f(i128::MAX, 127, false), i128::MAX);
    assert_eq!(f(i128::MAX, 127, true), -1);
}

/// A `u32` FIELD read off a modeled `Ty::Datatype` value must be recorded with its
/// `(32, unsigned)` range so `conjoin_datatype_field_ranges` can bound it. A bare
/// `Field(0)` on a single-variant (struct-like) datatype selects variant 0's 0-th
/// field via `resolve_field_int_ty`'s datatype-aware walk.
#[test]
fn datatype_field_range_map_records_u32_field() {
    let dt = Ty::Datatype {
        name: "Level".into(),
        variants: vec![(
            "Zero".into(),
            vec![("0".into(), Ty::Int { width: 32, signed: false })],
        )],
    };
    let mut func = func_with_locals(
        "reads_field",
        vec![
            LocalDecl { index: 0, ty: Ty::Int { width: 32, signed: false }, name: None },
            LocalDecl { index: 1, ty: dt, name: Some("lv".into()) },
        ],
        Ty::Int { width: 32, signed: false },
    );
    let field_place = Place { local: 1, projections: vec![trust_types::Projection::Field(0)] };
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(field_place.clone())),
        span: SourceSpan::default(),
    });
    let map = super::datatype_field_range_map(&func);
    let key = crate::place_to_var_name(&func, &field_place);
    assert_eq!(
        map.get(&key),
        Some(&(32u32, false)),
        "a u32 field read off a modeled datatype must be recorded (32, unsigned): {map:?}"
    );
}
