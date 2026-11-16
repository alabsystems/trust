//! REAL-MIR matrix for D5-B: kernel-checked BODY-INFERRED return equalities.
//!
//! Every fixture is the compiler's OWN extracted MIR (stage-1 `4e9fe36bf`),
//! captured verbatim from `tests/fixtures/d5b_inferred_fx.rs` with
//!
//! ```text
//! trustc -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//!        --edition 2021 --crate-type lib --crate-name fxb d5b_inferred_fx.rs
//! ```
//!
//! and bundled into `d5b_inferred_fx.json` (a JSON array, sorted by def path).
//!
//! What this pins, at the layer below the compiler:
//!
//! 1. KERNEL YIELD — for every helper in the fragment `infer_return_candidate`
//!    proposes `_0 == E(params)`; the Clean CIC kernel (`trust_certify::certify_vc`,
//!    the exact admission the compiler runs) certifies every check row for the
//!    single-assignment bodies and for NONE of the branch/temp bodies. Both
//!    halves are pinned as a measurement.
//! 2. THE CHECK BITES — a deliberately WRONG `E` driven through the same check
//!    (`inferred_return_check_vcs`) is NOT certified: the synthesizer is untrusted
//!    and the kernel is what decides.
//! 3. DECLINES — helpers outside the fragment (arithmetic, a cast, a loop, a call,
//!    a reference parameter) propose nothing.
//! 4. COMPOSITION — with the inferred summary in the caller's DB, the caller's
//!    row PROVES (ay Proved AND kernel-certified) for a correct helper
//!    (`shift_via_guard`, `cell_index`, each with its without-summary control),
//!    and a GENUINE bug (`guard_bad` = `bit < 65`) is refuted by ay with
//!    `bit = 64` and is NOT held by the D5-A screen, because the destination is
//!    now pinned by an injectable summary.
//! 5. PRE-OPTIMIZATION SHAPES (2026-09-25) — the compiler mints from the
//!    crate-wide extraction, which reads `mir_drops_elaborated_and_const_checked`
//!    (PRE-optimization MIR), NOT the per-function dump the bundle above holds.
//!    There every helper routes its operands through temporaries
//!    (`guard`: `_2 = copy _1; _0 = Lt(move _2, 64)`), and until trust-certify's
//!    kernel-checked rewriting lane the check VC was not certified — D5-B was
//!    inert in the compiler. Section 5 rebuilds each fragment helper from rustc's
//!    own `runtime-post-cleanup` MIR (the output of that query; see [`preopt`])
//!    and pins the yield, the wrong candidates and the composition on THOSE
//!    shapes. `guard`'s check VC is asserted equal to the violation the lead
//!    dumped from the stage-1 compiler (`AY_CERT_DUMP=1`), the fidelity anchor.
use trust_types::fx::FxHashSet;
use trust_types::{Formula, Terminator, VerifiableFunction, VerificationResult};
use trust_vcgen::{
    GenericRefutationScope, InferredReturn, LocalCallDestScreen, SummaryDatabase, VcgenContext,
};

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn fixtures() -> Vec<VerifiableFunction> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/d5b_inferred_fx.json");
    let text = std::fs::read_to_string(path).expect("fixture bundle must be readable");
    serde_json::from_str(&text).expect("fixture bundle must deserialize")
}

fn load(def_path: &str) -> VerifiableFunction {
    fixtures()
        .into_iter()
        .find(|f| f.def_path == def_path)
        .unwrap_or_else(|| panic!("fixture `{def_path}` missing"))
}

fn on_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("analysis thread must not panic")
}

/// The compiler's admission: every check row kernel-certified.
fn kernel_certifies(inferred: &InferredReturn) -> bool {
    let vcs = inferred.check_vcs().to_vec();
    on_big_stack(move || vcs.iter().all(|vc| trust_certify::certify_vc(vc).is_some()))
}

fn infer(def_path: &str) -> InferredReturn {
    trust_vcgen::infer_return_candidate(&load(def_path))
        .unwrap_or_else(|reason| panic!("{def_path} must be in the fragment: {reason}"))
}

// ---------------------------------------------------------------------------
// 1. Kernel yield over the fragment.
// ---------------------------------------------------------------------------

/// The measured kernel yield over the per-function bundle. 2026-09-24
/// (stage-1 `4e9fe36bf` certifier): only the single-assignment bodies certified
/// (the direct disequality / propositional closure lanes). 2026-09-25: with
/// trust-certify's kernel-checked REWRITING lane (`rewrite_eval`), every helper
/// in the fragment certifies — the diamonds (`nz`, `pick`, `m`, `neg_m`, `sgn`),
/// the short-circuits (`g_or`, `g_and`) and the temporary (`g_not`), whose
/// check VCs carry `Int` aliases (`_0 = _2#s1_0`), Bool definitions
/// (`_3 ⟺ d = 0`, `_0 ⟺ _4`) and the implication pair of the generator's `Ite`
/// elimination. The synthesizer is unchanged; the certifier moved them.
const KERNEL_CERTIFIED: [&str; 16] = [
    "fxb::guard",
    "fxb::cell_width_ok",
    "fxb::guard_bad",
    "fxb::band",
    "fxb::bxor",
    "fxb::le",
    "fxb::ma::guard",
    "fxb::mb::guard",
    "fxb::nz",
    "fxb::pick",
    "fxb::m",
    "fxb::neg_m",
    "fxb::sgn",
    "fxb::g_or",
    "fxb::g_and",
    "fxb::g_not",
];

/// Fragment helpers whose (correct) candidate the kernel does NOT certify. This
/// list is a MEASUREMENT and is empty as of 2026-09-25; a certifier regression
/// that stops certifying a helper fails `fragment_helpers_kernel_yield` until it
/// is moved here deliberately.
const KERNEL_DECLINED: [&str; 0] = [];

#[test]
fn fragment_helpers_kernel_yield() {
    for helper in KERNEL_CERTIFIED.iter().chain(KERNEL_DECLINED.iter()) {
        let inferred = infer(helper);
        let started = std::time::Instant::now();
        let certified = kernel_certifies(&inferred);
        eprintln!(
            "D5B_YIELD {helper}: rows={} certified={certified} in {:?}: {:?}",
            inferred.check_vcs().len(),
            started.elapsed(),
            inferred.postcondition()
        );
        assert_eq!(
            certified,
            KERNEL_CERTIFIED.contains(helper),
            "{helper}: the measured kernel yield moved — update the lists deliberately"
        );
    }
}

// ---------------------------------------------------------------------------
// 2. The check bites: a wrong candidate is not certified.
// ---------------------------------------------------------------------------

fn wrong_candidate_is_refused(def_path: &str, wrong: Formula) {
    let func = load(def_path);
    let vcs = trust_vcgen::inferred_return_check_vcs(&func, &wrong)
        .unwrap_or_else(|reason| panic!("{def_path}: the check rows must generate: {reason}"));
    let certified =
        on_big_stack(move || vcs.iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
    assert!(!certified, "{def_path}: a WRONG return equality must not be certified: {wrong:?}");
}

fn var(name: &str, sort: trust_types::Sort) -> Box<Formula> {
    Box::new(Formula::Var(name.into(), sort))
}

#[test]
fn off_by_one_guard_is_refused() {
    use trust_types::Sort;
    // guard is `bit < 64`; claim `bit < 65`.
    wrong_candidate_is_refused(
        "fxb::guard",
        Formula::Eq(
            var("_0", Sort::Bool),
            Box::new(Formula::Lt(var("bit", Sort::Int), Box::new(Formula::Int(65)))),
        ),
    );
}

#[test]
fn swapped_diamond_is_refused() {
    use trust_types::Sort;
    // nz is `if d == 0 { 1 } else { d }`; claim the arms swapped.
    let d_eq_0 = Formula::Eq(var("d", Sort::Int), Box::new(Formula::Int(0)));
    wrong_candidate_is_refused(
        "fxb::nz",
        Formula::Eq(
            var("_0", Sort::Int),
            Box::new(Formula::Ite(
                Box::new(d_eq_0),
                var("d", Sort::Int),
                Box::new(Formula::Int(1)),
            )),
        ),
    );
}

#[test]
fn negated_guard_is_refused() {
    use trust_types::Sort;
    // g_not is `!(b < 64)`; claim `b < 64`.
    wrong_candidate_is_refused(
        "fxb::g_not",
        Formula::Eq(
            var("_0", Sort::Bool),
            Box::new(Formula::Lt(var("b", Sort::Int), Box::new(Formula::Int(64)))),
        ),
    );
}

// ---------------------------------------------------------------------------
// 3. Declines outside the fragment.
// ---------------------------------------------------------------------------

#[test]
fn non_fragment_helpers_propose_nothing() {
    for (helper, why) in [
        ("fxb::scale", "checked multiplication"),
        ("fxb::widen", "cast"),
        ("fxb::loop_helper", "loop"),
        ("fxb::ext_guard", "call"),
        ("fxb::by_ref", "reference parameter"),
    ] {
        let decline = trust_vcgen::infer_return_candidate(&load(helper));
        assert!(
            decline.is_err(),
            "{helper} ({why}) must not be inferred: {:?}",
            decline.map(|i| i.postcondition().clone())
        );
        eprintln!("D5B_DECLINE {helper}: {}", decline.err().unwrap_or_default());
    }
}

// ---------------------------------------------------------------------------
// 4. Composition through the existing postcondition lane.
// ---------------------------------------------------------------------------

fn sole_call(func: &VerifiableFunction) -> (String, (u64, u32)) {
    let calls: Vec<_> = func
        .body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator {
            Terminator::Call { func: callee, callee_identity: Some(id), .. } => {
                Some((callee.clone(), (id.stable_crate_id, id.def_index)))
            }
            _ => None,
        })
        .collect();
    assert_eq!(calls.len(), 1, "{}: exactly one identified call", func.def_path);
    calls.into_iter().next().expect("checked")
}

#[derive(Debug)]
struct Row {
    proved: bool,
    certified: bool,
    counterexample: Option<String>,
    held: Option<String>,
}

/// Generate the caller's VCs with `db` (the L0 definitional subset, as the
/// compiler hands it) and the D5-A census, then solve every row the census
/// could have screened: those mentioning the call destination or the guarded
/// operation's kind.
fn caller_rows(caller: &str, callee: &str, with_summary: bool) -> Vec<Row> {
    caller_rows_from(caller, callee, with_summary.then(|| load(callee)))
}

/// [`caller_rows`] with the summary minted from `callee_body` — the bundle's
/// per-function body, or a PRE-optimization rebuild ([`preopt`]), which is what
/// the compiler's crate-wide mint actually reads.
fn caller_rows_from(
    caller: &str,
    callee: &str,
    callee_body: Option<VerifiableFunction>,
) -> Vec<Row> {
    let func = load(caller);
    let (callee_name, key) = sole_call(&func);
    assert_eq!(callee_name, callee);
    let mut db = SummaryDatabase::new();
    if let Some(body) = callee_body {
        assert_eq!(body.def_path, callee);
        let inferred = trust_vcgen::infer_return_candidate(&body)
            .unwrap_or_else(|reason| panic!("{callee} must be in the fragment: {reason}"));
        assert!(kernel_certifies(&inferred), "{callee}: admission precondition");
        // As the compiler builds it: the lemma, plus the callee's extracted body
        // as an analysis input (`add_direct_call_contract_summaries`).
        db.insert(
            trust_vcgen::FunctionSummary::new(callee_name.clone())
                .with_body_inferred_return(&inferred)
                .with_extracted_body(std::sync::Arc::new(body)),
        );
    }
    let db = db.definitional_precondition_free_subset();
    on_big_stack(move || {
        let context = VcgenContext::for_function(func.def_path.clone())
            .with_local_call_dest_screen(LocalCallDestScreen::new([key], &db));
        let (solver_vcs, discharged) =
            trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                &func,
                &db,
                false,
                &context,
                &std::collections::HashSet::<(trust_types::BlockId, usize)>::new(),
            );
        let scope = GenericRefutationScope::for_function_with_call_dests(
            &func,
            &solver_vcs,
            &discharged,
            &context,
        );
        let router = test_router::deterministic_test_router();
        solver_vcs
            .iter()
            .filter(|vc| {
                matches!(
                    vc.kind,
                    trust_types::VcKind::ShiftOverflow { .. }
                        | trust_types::VcKind::ArithmeticOverflow { .. }
                        | trust_types::VcKind::DivisionByZero
                        | trust_types::VcKind::RemainderByZero
                )
            })
            .map(|vc| {
                let result =
                    router.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one").1;
                let counterexample = match &result {
                    VerificationResult::Failed { counterexample, .. } => {
                        Some(format!("{counterexample:?}"))
                    }
                    _ => None,
                };
                Row {
                    proved: matches!(result, VerificationResult::Proved { .. }),
                    certified: trust_certify::certify_vc(vc).is_some(),
                    held: counterexample.as_ref().and_then(|_| scope.rejection_reason(vc)),
                    counterexample,
                }
            })
            .collect()
    })
}

fn assert_proves(caller: &str, callee: &str) {
    assert_proves_from(caller, callee, load(callee));
}

fn assert_proves_from(caller: &str, callee: &str, callee_body: VerifiableFunction) {
    // Control: WITHOUT the summary the row is not proved (the destination is free).
    let before = caller_rows(caller, callee, false);
    assert!(!before.is_empty(), "{caller}: the guarded row must exist");
    assert!(
        before.iter().any(|row| !row.proved),
        "{caller}: control — unproved without the summary: {before:?}"
    );
    let after = caller_rows_from(caller, callee, Some(callee_body));
    eprintln!("D5B_COMPOSE {caller}: before={before:?} after={after:?}");
    assert!(
        after.iter().all(|row| row.proved && row.certified),
        "{caller}: with the kernel-checked summary every row proves AND certifies: {after:?}"
    );
}

#[test]
fn shift_via_guard_proves() {
    assert_proves("fxb::shift_via_guard", "fxb::guard");
}

#[test]
fn cell_index_proves() {
    assert_proves("fxb::cell_index", "fxb::cell_width_ok");
}

/// Two parameters, and the guarded operation is a subtraction (`b - a` under
/// `le(a, b)`), not a shift.
#[test]
fn sub_via_le_proves() {
    assert_proves("fxb::sub_via_le", "fxb::le");
}

/// Two same-named helpers in different modules are different `DefId`s with
/// different def paths: each caller gets ITS helper's lemma.
#[test]
fn same_named_helpers_in_two_modules_keep_their_own_lemma() {
    assert_proves("fxb::shift_ma", "fxb::ma::guard");
    assert_genuinely_refuted("fxb::shift_mb", "fxb::mb::guard");
}

fn assert_genuinely_refuted(caller: &str, callee: &str) {
    assert_genuinely_refuted_from(caller, callee, load(callee));
}

fn assert_genuinely_refuted_from(caller: &str, callee: &str, callee_body: VerifiableFunction) {
    let after = caller_rows_from(caller, callee, Some(callee_body));
    eprintln!("D5B_GENUINE {caller}: {after:?}");
    let refuted: Vec<&Row> = after.iter().filter(|row| row.counterexample.is_some()).collect();
    assert!(!refuted.is_empty(), "{caller}: a real bug must stay refuted: {after:?}");
    for row in &refuted {
        assert!(row.held.is_none(), "{caller}: a pinned destination is not held: {row:?}");
        let cx = row.counterexample.as_deref().unwrap_or_default();
        assert!(cx.contains("64"), "{caller}: the witness is bit = 64: {cx}");
        assert!(!row.proved && !row.certified, "{caller}: {row:?}");
    }
}

#[test]
fn guard_bad_stays_refuted_with_a_grounded_witness() {
    assert_genuinely_refuted("fxb::shift_bad", "fxb::guard_bad");
}

/// `let _ = guard(bit); x >> bit`: the (correct) helper's lemma is about a value
/// the shift never reads, so it must not discharge the shift — the refutation is
/// genuine and stays. Memo fixture 6 with a SUMMARIZED helper.
#[test]
fn unread_summarized_result_does_not_discharge() {
    assert_genuinely_refuted("fxb::unguarded_after_guard", "fxb::guard");
}

/// The inferred summary is what the D5-A census treats as pinned
/// (`postcondition_pinning_callees`: `_0 == E(params)`, no `requires`), and only it.
#[test]
fn inferred_summary_is_an_injecting_name() {
    let mut db = SummaryDatabase::new();
    db.insert(
        trust_vcgen::FunctionSummary::new("fxb::guard")
            .with_body_inferred_return(&infer("fxb::guard")),
    );
    db.insert(trust_vcgen::FunctionSummary::new("fxb::other"));
    let names: FxHashSet<&str> = db.postcondition_injecting_names().collect();
    assert_eq!(names, FxHashSet::from_iter(["fxb::guard"]));
    let pinning: Vec<&str> = db.postcondition_pinning_callees().map(|(name, _)| name).collect();
    assert_eq!(pinning, vec!["fxb::guard"]);
    let l0 = db.definitional_precondition_free_subset();
    assert_eq!(l0.names().collect::<Vec<_>>(), vec!["fxb::guard"]);
}

// ---------------------------------------------------------------------------
// 5. PRE-OPTIMIZATION shapes — what the compiler's crate-wide mint reads.
// ---------------------------------------------------------------------------

/// Each fragment helper rebuilt from rustc's OWN pre-optimization MIR: the
/// `runtime-post-cleanup` dump (`-Zdump-mir=all`, `trustc 1.99.0-dev
/// (321aaeda7)`, default `-Zmir-opt-level`), which is the body
/// `mir_drops_elaborated_and_const_checked` returns and the crate-wide
/// extraction in `trust_init_backing_certificates` reads. Each builder quotes
/// its MIR. Parameters, their names, types and range preconditions come from
/// the bundle (they do not change across the pipeline); locals take their
/// `var_debug_info` name where rustc records one (`g_not`'s `t`), as
/// `build_debug_name_map` does; block ids are rustc's.
///
/// These are TRANSCRIPTIONS, not compiler output. The anchor that the
/// transcription matches what the compiler extracts is
/// `preopt_guard_check_vc_is_the_measured_compiler_violation`: `guard`'s check
/// VC equals, node for node, the violation dumped from the stage-1 compiler
/// (`AY_CERT_DUMP=1`, 2026-09-25).
mod preopt {
    use trust_types::{
        BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty, UnOp, VerifiableFunction,
    };

    fn u32t() -> Ty {
        Ty::Int { width: 32, signed: false }
    }
    fn i32t() -> Ty {
        Ty::Int { width: 32, signed: true }
    }
    fn cp(local: usize) -> Operand {
        Operand::Copy(Place::local(local))
    }
    fn mv(local: usize) -> Operand {
        Operand::Move(Place::local(local))
    }
    fn u32c(value: u128) -> Operand {
        Operand::Constant(ConstValue::Uint(value, 32))
    }
    fn ic(value: i128) -> Operand {
        Operand::Constant(ConstValue::Int(value))
    }
    fn set(local: usize, rvalue: Rvalue) -> Statement {
        Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
    }
    fn bin(op: BinOp, a: Operand, b: Operand) -> Rvalue {
        Rvalue::BinaryOp(op, a, b)
    }
    fn live(local: usize) -> Statement {
        Statement::StorageLive(local)
    }
    fn dead(local: usize) -> Statement {
        Statement::StorageDead(local)
    }
    fn bb(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator }
    }
    fn goto(id: usize) -> Terminator {
        Terminator::Goto(BlockId(id))
    }
    fn switch(discr: Operand, targets: &[(u128, usize)], otherwise: usize) -> Terminator {
        Terminator::SwitchInt {
            discr,
            targets: targets.iter().map(|&(v, t)| (v, BlockId(t))).collect(),
            otherwise: BlockId(otherwise),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        }
    }

    /// The bundle's function with rustc's pre-optimization temporaries and blocks.
    fn rebuild(
        def_path: &str,
        temps: &[(usize, Ty, Option<&str>)],
        blocks: Vec<BasicBlock>,
    ) -> VerifiableFunction {
        let mut func = super::load(def_path);
        let arg_count = func.body.arg_count;
        func.body.locals.retain(|decl| decl.index <= arg_count);
        for (index, ty, name) in temps {
            func.body.locals.push(LocalDecl {
                index: *index,
                ty: ty.clone(),
                name: name.map(str::to_owned),
            });
        }
        func.body.locals.sort_by_key(|decl| decl.index);
        func.body.blocks = blocks;
        func
    }

    /// `fn(_1: u32) -> bool { _2 = copy _1; _0 = <op>(move _2, const K_u32); }`
    /// — `guard`, `ma::guard` (`Lt`, 64), `guard_bad`, `mb::guard` (`Lt`, 65),
    /// `cell_width_ok` (`Gt`, 0).
    fn compare_via_temp(def_path: &str, op: BinOp, k: u128) -> VerifiableFunction {
        rebuild(
            def_path,
            &[(2, u32t(), None)],
            vec![bb(
                0,
                vec![live(2), set(2, Rvalue::Use(cp(1))), set(0, bin(op, mv(2), u32c(k))), dead(2)],
                Terminator::Return,
            )],
        )
    }

    /// `fn(_1, _2) -> bool { _3 = copy _1; _4 = copy _2; _0 = <op>(move _3, move _4); }`
    /// — `band` (`BitAnd`), `bxor` (`BitXor`) over `bool`, `le` (`Le`) over `u32`.
    fn binary_via_temps(def_path: &str, op: BinOp, ty: Ty) -> VerifiableFunction {
        rebuild(
            def_path,
            &[(3, ty.clone(), None), (4, ty, None)],
            vec![bb(
                0,
                vec![
                    live(3),
                    set(3, Rvalue::Use(cp(1))),
                    live(4),
                    set(4, Rvalue::Use(cp(2))),
                    set(0, bin(op, mv(3), mv(4))),
                    dead(4),
                    dead(3),
                ],
                Terminator::Return,
            )],
        )
    }

    pub(super) fn build(def_path: &str) -> VerifiableFunction {
        match def_path {
            "fxb::guard" | "fxb::ma::guard" => compare_via_temp(def_path, BinOp::Lt, 64),
            "fxb::guard_bad" | "fxb::mb::guard" => compare_via_temp(def_path, BinOp::Lt, 65),
            "fxb::cell_width_ok" => compare_via_temp(def_path, BinOp::Gt, 0),
            "fxb::band" => binary_via_temps(def_path, BinOp::BitAnd, Ty::Bool),
            "fxb::bxor" => binary_via_temps(def_path, BinOp::BitXor, Ty::Bool),
            "fxb::le" => binary_via_temps(def_path, BinOp::Le, u32t()),
            // bb0: _3 = copy _1; _2 = Eq(move _3, 0); switchInt(move _2) -> [0: bb2, otherwise: bb1]
            // bb1: StorageDead(_3); _0 = const 1_u32; goto bb3
            // bb2: StorageDead(_3); _0 = copy _1; goto bb3
            // bb3: StorageDead(_2); return
            "fxb::nz" => rebuild(
                def_path,
                &[(2, Ty::Bool, None), (3, u32t(), None)],
                vec![
                    bb(
                        0,
                        vec![
                            live(2),
                            live(3),
                            set(3, Rvalue::Use(cp(1))),
                            set(2, bin(BinOp::Eq, mv(3), u32c(0))),
                        ],
                        switch(mv(2), &[(0, 2)], 1),
                    ),
                    bb(1, vec![dead(3), set(0, Rvalue::Use(u32c(1)))], goto(3)),
                    bb(2, vec![dead(3), set(0, Rvalue::Use(cp(1)))], goto(3)),
                    bb(3, vec![dead(2)], Terminator::Return),
                ],
            ),
            // bb0: _4 = copy _1; switchInt(move _4) -> [0: bb2, otherwise: bb1]
            // bb1: _0 = copy _2; bb2: _0 = copy _3; bb3: StorageDead(_4); return
            "fxb::pick" => rebuild(
                def_path,
                &[(4, Ty::Bool, None)],
                vec![
                    bb(0, vec![live(4), set(4, Rvalue::Use(cp(1)))], switch(mv(4), &[(0, 2)], 1)),
                    bb(1, vec![set(0, Rvalue::Use(cp(2)))], goto(3)),
                    bb(2, vec![set(0, Rvalue::Use(cp(3)))], goto(3)),
                    bb(3, vec![dead(4)], Terminator::Return),
                ],
            ),
            // bb0: switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1]
            // bb1: _0 = copy _1; bb2: _0 = const 7_u32; bb3: _0 = const 5_u32; bb4: return
            "fxb::m" => rebuild(
                def_path,
                &[],
                vec![
                    bb(0, vec![], switch(cp(1), &[(0, 3), (1, 2)], 1)),
                    bb(1, vec![set(0, Rvalue::Use(cp(1)))], goto(4)),
                    bb(2, vec![set(0, Rvalue::Use(u32c(7)))], goto(4)),
                    bb(3, vec![set(0, Rvalue::Use(u32c(5)))], goto(4)),
                    bb(4, vec![], Terminator::Return),
                ],
            ),
            // bb0: switchInt(copy _1) -> [255: bb3, 128: bb2, otherwise: bb1]
            // bb1: _0 = copy _1; bb2: _0 = const 4_i8; bb3: _0 = const 3_i8; bb4: return
            "fxb::neg_m" => rebuild(
                def_path,
                &[],
                vec![
                    bb(0, vec![], switch(cp(1), &[(255, 3), (128, 2)], 1)),
                    bb(1, vec![set(0, Rvalue::Use(cp(1)))], goto(4)),
                    bb(2, vec![set(0, Rvalue::Use(ic(4)))], goto(4)),
                    bb(3, vec![set(0, Rvalue::Use(ic(3)))], goto(4)),
                    bb(4, vec![], Terminator::Return),
                ],
            ),
            // bb0: _3 = copy _1; _2 = Lt(move _3, 0); switchInt(move _2) -> [0: bb2, otherwise: bb1]
            // bb1: StorageDead(_3); _0 = const -1_i32; goto bb6
            // bb2: StorageDead(_3); _5 = copy _1; _4 = Eq(move _5, 0); switchInt(move _4) -> [0: bb4, otherwise: bb3]
            // bb3: StorageDead(_5); _0 = const 0_i32; goto bb5
            // bb4: StorageDead(_5); _0 = const 1_i32; goto bb5
            // bb5: StorageDead(_4); goto bb6      bb6: StorageDead(_2); return
            "fxb::sgn" => rebuild(
                def_path,
                &[(2, Ty::Bool, None), (3, i32t(), None), (4, Ty::Bool, None), (5, i32t(), None)],
                vec![
                    bb(
                        0,
                        vec![
                            live(2),
                            live(3),
                            set(3, Rvalue::Use(cp(1))),
                            set(2, bin(BinOp::Lt, mv(3), ic(0))),
                        ],
                        switch(mv(2), &[(0, 2)], 1),
                    ),
                    bb(1, vec![dead(3), set(0, Rvalue::Use(ic(-1)))], goto(6)),
                    bb(
                        2,
                        vec![
                            dead(3),
                            live(4),
                            live(5),
                            set(5, Rvalue::Use(cp(1))),
                            set(4, bin(BinOp::Eq, mv(5), ic(0))),
                        ],
                        switch(mv(4), &[(0, 4)], 3),
                    ),
                    bb(3, vec![dead(5), set(0, Rvalue::Use(ic(0)))], goto(5)),
                    bb(4, vec![dead(5), set(0, Rvalue::Use(ic(1)))], goto(5)),
                    bb(5, vec![dead(4)], goto(6)),
                    bb(6, vec![dead(2)], Terminator::Return),
                ],
            ),
            // bb0: _3 = copy _1; _2 = Lt(move _3, 64); switchInt(move _2) -> [0: bb2, otherwise: bb1]
            // bb1: StorageDead(_3); _0 = const true; goto bb3
            // bb2: StorageDead(_3); _4 = copy _1; _0 = Eq(move _4, 64); StorageDead(_4); goto bb3
            // bb3: StorageDead(_2); return
            "fxb::g_or" => rebuild(
                def_path,
                &[(2, Ty::Bool, None), (3, u32t(), None), (4, u32t(), None)],
                vec![
                    bb(
                        0,
                        vec![
                            live(2),
                            live(3),
                            set(3, Rvalue::Use(cp(1))),
                            set(2, bin(BinOp::Lt, mv(3), u32c(64))),
                        ],
                        switch(mv(2), &[(0, 2)], 1),
                    ),
                    bb(
                        1,
                        vec![
                            dead(3),
                            set(0, Rvalue::Use(Operand::Constant(ConstValue::Bool(true)))),
                        ],
                        goto(3),
                    ),
                    bb(
                        2,
                        vec![
                            dead(3),
                            live(4),
                            set(4, Rvalue::Use(cp(1))),
                            set(0, bin(BinOp::Eq, mv(4), u32c(64))),
                            dead(4),
                        ],
                        goto(3),
                    ),
                    bb(3, vec![dead(2)], Terminator::Return),
                ],
            ),
            // bb0: _4 = copy _1; _3 = Lt(move _4, 8); switchInt(move _3) -> [0: bb2, otherwise: bb1]
            // bb1: StorageDead(_4); _5 = copy _2; _0 = Lt(move _5, 8); StorageDead(_5); goto bb3
            // bb2: StorageDead(_4); _0 = const false; goto bb3
            // bb3: StorageDead(_3); return
            "fxb::g_and" => rebuild(
                def_path,
                &[(3, Ty::Bool, None), (4, u32t(), None), (5, u32t(), None)],
                vec![
                    bb(
                        0,
                        vec![
                            live(3),
                            live(4),
                            set(4, Rvalue::Use(cp(1))),
                            set(3, bin(BinOp::Lt, mv(4), u32c(8))),
                        ],
                        switch(mv(3), &[(0, 2)], 1),
                    ),
                    bb(
                        1,
                        vec![
                            dead(4),
                            live(5),
                            set(5, Rvalue::Use(cp(2))),
                            set(0, bin(BinOp::Lt, mv(5), u32c(8))),
                            dead(5),
                        ],
                        goto(3),
                    ),
                    bb(
                        2,
                        vec![
                            dead(4),
                            set(0, Rvalue::Use(Operand::Constant(ConstValue::Bool(false)))),
                        ],
                        goto(3),
                    ),
                    bb(3, vec![dead(3)], Terminator::Return),
                ],
            ),
            // `let t = b < 64; !t` — `debug t => _2`:
            // bb0: _3 = copy _1; _2 = Lt(move _3, 64); StorageDead(_3);
            //      _4 = copy _2; _0 = Not(move _4); StorageDead(_4); StorageDead(_2); return
            "fxb::g_not" => rebuild(
                def_path,
                &[(2, Ty::Bool, Some("t")), (3, u32t(), None), (4, Ty::Bool, None)],
                vec![bb(
                    0,
                    vec![
                        live(2),
                        live(3),
                        set(3, Rvalue::Use(cp(1))),
                        set(2, bin(BinOp::Lt, mv(3), u32c(64))),
                        dead(3),
                        live(4),
                        set(4, Rvalue::Use(cp(2))),
                        set(0, Rvalue::UnaryOp(UnOp::Not, mv(4))),
                        dead(4),
                        dead(2),
                    ],
                    Terminator::Return,
                )],
            ),
            other => panic!("no pre-optimization rebuild for `{other}`"),
        }
    }
}

fn infer_preopt(def_path: &str) -> InferredReturn {
    trust_vcgen::infer_return_candidate(&preopt::build(def_path))
        .unwrap_or_else(|reason| panic!("{def_path} (pre-opt) must be in the fragment: {reason}"))
}

/// THE FIDELITY ANCHOR: `guard`'s pre-optimization check VC is exactly the
/// violation the stage-1 compiler dumped (`AY_CERT_DUMP=1`, 2026-09-25) when it
/// declined to mint — `_2 = bit ∧ (_0 ⟺ _2 < 64) ∧ ¬(_0 ⟺ bit < 64)`.
/// The current generator additionally retains its intrinsic temporary carriers
/// (aef6192a8a); pin those exact wrappers AND the unchanged archived core.
#[test]
fn preopt_guard_check_vc_is_the_measured_compiler_violation() {
    use trust_types::Sort;
    let inferred = infer_preopt("fxb::guard");
    let lt64 = |v: &str| Formula::Lt(var(v, Sort::Int), Box::new(Formula::Int(64)));
    let measured = Formula::And(vec![
        Formula::Eq(var("_2", Sort::Int), var("bit", Sort::Int)),
        Formula::Eq(var("_0", Sort::Bool), Box::new(lt64("_2"))),
        Formula::Not(Box::new(Formula::Eq(var("_0", Sort::Bool), Box::new(lt64("bit"))))),
    ]);
    assert_eq!(inferred.check_vcs().len(), 1);
    let temporary_range = Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(0)), var("_2", Sort::Int)),
        Formula::Le(var("_2", Sort::Int), Box::new(Formula::Int(u32::MAX.into()))),
    ]);
    let Formula::And(complete) = &inferred.check_vcs()[0].formula else {
        panic!("complete current violation must retain the measured core");
    };
    let Formula::And(measured_parts) = &measured else {
        panic!("the archived violation is a conjunction");
    };
    assert_eq!(
        complete,
        &[
            measured_parts[0].clone(),
            measured_parts[1].clone(),
            Formula::And(
                vec![temporary_range.clone(), temporary_range, measured_parts[2].clone(),]
            ),
        ]
    );
    let Formula::And(current_body) = &complete[2] else {
        panic!("the body retains both temporary carriers and the measured violation");
    };
    assert_eq!(
        Formula::And(vec![complete[0].clone(), complete[1].clone(), current_body[2].clone()]),
        measured
    );
    // The candidate is the optimized body's, byte for byte: only the check moved.
    assert_eq!(inferred.postcondition(), infer("fxb::guard").postcondition());
}

/// The kernel yield over the PRE-optimization shapes, pinned both ways. Before
/// the rewriting lane NONE of these certified (measured on `guard`: the
/// compiler printed `kernel did not certify every check row`); now every one
/// does. Same contract as `KERNEL_DECLINED`: a helper that stops certifying
/// fails here until it is moved to `PREOPT_KERNEL_DECLINED` deliberately.
const PREOPT_KERNEL_CERTIFIED: [&str; 16] = KERNEL_CERTIFIED;
const PREOPT_KERNEL_DECLINED: [&str; 0] = [];

#[test]
fn preopt_fragment_helpers_kernel_yield() {
    for helper in PREOPT_KERNEL_CERTIFIED.iter().chain(PREOPT_KERNEL_DECLINED.iter()) {
        let inferred = infer_preopt(helper);
        // Same candidate as the per-function body: the temporaries are the
        // check's problem, never the synthesizer's.
        assert_eq!(
            inferred.postcondition(),
            infer(helper).postcondition(),
            "{helper}: pre-opt candidate differs from the per-function one"
        );
        let started = std::time::Instant::now();
        let certified = kernel_certifies(&inferred);
        eprintln!(
            "D5B_PREOPT_YIELD {helper}: rows={} certified={certified} in {:?}",
            inferred.check_vcs().len(),
            started.elapsed(),
        );
        assert_eq!(
            certified,
            PREOPT_KERNEL_CERTIFIED.contains(helper),
            "{helper}: the measured PRE-OPT kernel yield moved — update the lists deliberately"
        );
    }
}

fn wrong_preopt_candidate_is_refused(def_path: &str, wrong: Formula) {
    let func = preopt::build(def_path);
    let vcs = trust_vcgen::inferred_return_check_vcs(&func, &wrong)
        .unwrap_or_else(|reason| panic!("{def_path}: the check rows must generate: {reason}"));
    let certified =
        on_big_stack(move || vcs.iter().all(|vc| trust_certify::certify_vc(vc).is_some()));
    assert!(!certified, "{def_path} (pre-opt): a WRONG return equality must not be certified");
}

/// The three wrong candidates of section 2, driven through the PRE-OPT bodies:
/// the rewriting lane sees through the temporaries and still refuses each.
#[test]
fn wrong_candidates_are_refused_on_preopt_bodies() {
    use trust_types::Sort;
    wrong_preopt_candidate_is_refused(
        "fxb::guard",
        Formula::Eq(
            var("_0", Sort::Bool),
            Box::new(Formula::Lt(var("bit", Sort::Int), Box::new(Formula::Int(65)))),
        ),
    );
    let d_eq_0 = Formula::Eq(var("d", Sort::Int), Box::new(Formula::Int(0)));
    wrong_preopt_candidate_is_refused(
        "fxb::nz",
        Formula::Eq(
            var("_0", Sort::Int),
            Box::new(Formula::Ite(
                Box::new(d_eq_0),
                var("d", Sort::Int),
                Box::new(Formula::Int(1)),
            )),
        ),
    );
    wrong_preopt_candidate_is_refused(
        "fxb::g_not",
        Formula::Eq(
            var("_0", Sort::Bool),
            Box::new(Formula::Lt(var("b", Sort::Int), Box::new(Formula::Int(64)))),
        ),
    );
    // `sgn` with the -1 and 1 arms swapped.
    let x = || var("x", Sort::Int);
    let swapped_sgn = Formula::Ite(
        Box::new(Formula::Not(Box::new(Formula::Lt(x(), Box::new(Formula::Int(0)))))),
        Box::new(Formula::Ite(
            Box::new(Formula::Not(Box::new(Formula::Eq(x(), Box::new(Formula::Int(0)))))),
            Box::new(Formula::Int(-1)),
            Box::new(Formula::Int(0)),
        )),
        Box::new(Formula::Int(1)),
    );
    wrong_preopt_candidate_is_refused(
        "fxb::sgn",
        Formula::Eq(var("_0", Sort::Int), Box::new(swapped_sgn)),
    );
}

/// COMPOSITION with the summary the compiler actually mints (from the PRE-OPT
/// body): the caller proves and certifies, a real bug stays a grounded
/// refutation, and a diamond helper now composes too.
#[test]
fn preopt_minted_summaries_compose() {
    assert_proves_from("fxb::shift_via_guard", "fxb::guard", preopt::build("fxb::guard"));
    assert_proves_from(
        "fxb::cell_index",
        "fxb::cell_width_ok",
        preopt::build("fxb::cell_width_ok"),
    );
    assert_proves_from("fxb::sub_via_le", "fxb::le", preopt::build("fxb::le"));
    assert_genuinely_refuted_from(
        "fxb::shift_bad",
        "fxb::guard_bad",
        preopt::build("fxb::guard_bad"),
    );
}

/// The helpers the rewriting lane MOVED, composed from their PRE-OPT bodies
/// against the bundle's own callers (the `call_dest_refutation_held.rs` rows):
/// `div_nz` now PROVES and kernel-certifies (`nz` never returns 0; the caller
/// row's refutation is a `Classical.em (d = 0)` case split over the lemma's
/// implication pair), while `shift_or` (`g_or(64)` is
/// `true`) and `shift_not` (`g_not` inverts the guard) are REAL bugs that stay
/// refuted — and are now GROUNDED refutations, not D5-A holds, because the
/// destination is pinned by a kernel-checked lemma.
#[test]
fn preopt_branchy_helpers_compose() {
    assert_proves_from("fxb::div_nz", "fxb::nz", preopt::build("fxb::nz"));
    assert_genuinely_refuted_from("fxb::shift_or", "fxb::g_or", preopt::build("fxb::g_or"));
    // `shift_not` proceeds exactly when `bit >= 64`: any such bit is a witness.
    let rows = caller_rows_from("fxb::shift_not", "fxb::g_not", Some(preopt::build("fxb::g_not")));
    eprintln!("D5B_GENUINE fxb::shift_not: {rows:?}");
    let refuted: Vec<&Row> = rows.iter().filter(|row| row.counterexample.is_some()).collect();
    assert!(!refuted.is_empty(), "shift_not: a real bug must stay refuted: {rows:?}");
    for row in refuted {
        assert!(row.held.is_none(), "shift_not: a pinned destination is not held: {row:?}");
        assert!(!row.proved && !row.certified, "shift_not: {row:?}");
    }
}
