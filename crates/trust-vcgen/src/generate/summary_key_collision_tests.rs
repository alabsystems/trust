// trust_vcgen/generate/summary_key_collision_tests.rs
//
// Trust (postcondition composition — THE KEY-COLLISION TRUST BOUNDARY).
//
// `build_semantic_guard_map_with_summaries` conjoins a callee's postcondition
// into the CALLER's VCs as an ASSUMED fact (`summaries.get(callee)` at the
// `Terminator::Call` arm). The lookup is a plain `FxHashMap<String, _>` hit on
// the extracted `Terminator::Call.func` string, and `modular::FunctionSummary`
// carries NO identity field at all — no `DefId`, no `CalleeIdentity`, no
// def-path. So if two DISTINCT callees ever reach one caller body under one
// rendered name, the first-registered summary is assumed at BOTH of them, and
// one function's `ensures` becomes a hypothesis about another function's
// result. `FunctionSummary::with_verified_callee_postcondition`'s doc states
// this as an obligation on the PRODUCER ("the summary's NAME resolves to
// exactly one callee identity in the body being summarized"); nothing in this
// crate checks it.
//
// These tests exist because that obligation was, until now, asserted in a doc
// comment and pinned nowhere. They do TWO things:
//
//   1. Show the mechanism end to end — a single summary assumed at two call
//      sites that the IR itself distinguishes — so anyone reading
//      `callee_postcondition_is_injectable` can see exactly how much of the
//      soundness argument lives outside this crate.
//   2. Enumerate what does NOT discriminate, so a future reader does not
//      mistake one of these for a defence: not `CalleeIdentity` (present on the
//      terminator, dropped by the `..` pattern at `semantic_guard.rs`'s `Call`
//      arm), not `param_types`, not the destination's type. Arity is the ONLY
//      accidental discriminator, and it is arity ALONE.
//
// WHERE THE REAL DEFENCE IS. Both production minters of an injectable
// (`postconditions_are_definitional`) summary live in
// `compiler/rustc_mir_transform/src/trust_verify.rs`:
//
//   * the authored-`ensures` lane (`with_verified_callee_postcondition`) is
//     gated by `callee_postconditions_are_reusable_reasoned`, whose
//     `identity:name-collision` conjunct pre-scans the caller body and refuses
//     the reuse bit for any `func_operand_name` owning more than one `DefId`,
//     and whose `identity:generic` conjunct (`args.is_empty()`) refuses every
//     generic instantiation;
//   * the Clean-origin lane (`clean_origin_summary` ->
//     `with_definitional_postcondition`) consults NEITHER, and is currently
//     unreachable only because a Clean-origin `def` is a non-generic local free
//     function whose rendered path is unique.
//
// MEASURED 2026-08-31 on the dependency-closed corpus `~/trust-corpora/
// mir-closed-mono` (37,612 bodies): 39 caller bodies carry one `func` string
// covering two or more distinct `callee_identity` values. 25 of them are
// `__trust_total_clone` with DIFFERENT `DefId`s (caught by BOTH conjuncts);
// the other 14 share a `DefId` and differ only in `substs_digest` — the
// name-owner pre-scan maps both to the same `DefId` and therefore does NOT
// catch them, so `identity:generic` is the sole gate standing between that
// class and the injection this file demonstrates.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, CalleeIdentity, ConstValue, Formula, LocalDecl,
    Operand, Place, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge,
    VerifiableBody, VerifiableFunction,
};

use crate::generate::build_semantic_guard_map_with_summaries;
use crate::modular::{FunctionSummary, SummaryDatabase, modular_vcgen};

/// The one rendered name both callees come out as. In production this is
/// `trust_mir_extract::func_operand_name`, which is deliberately NOT injective
/// over `DefId`s (the derived-trait / `?`-total / element-byte rewrites collapse
/// several defs onto one spelling on purpose).
const SHARED_KEY: &str = "k::Widen::<T>::widen";

/// The two callees the shared key covers. Distinct in every component the
/// compiler can distinguish — and both are carried on the terminator, where the
/// injection lane's `..` pattern drops them.
const IDENT_A: CalleeIdentity =
    CalleeIdentity { stable_crate_id: 0xA11CE, def_index: 7, substs_digest: [1, 0] };
const IDENT_B: CalleeIdentity =
    CalleeIdentity { stable_crate_id: 0xA11CE, def_index: 7, substs_digest: [2, 0] };

/// `fn caller(x: usize) { let a = <A>::widen(x); let b = <B>::widen(x);
///  let _ = a + 1; let _ = b + 1; }`
///
/// Two calls, two SSA destinations, one rendered callee name, two different
/// `callee_identity` stamps. Each destination then feeds a real
/// checked-add overflow obligation, so each call site owns something an
/// injected upper bound can discharge.
fn caller_with_two_colliding_calls(
    identity_a: Option<CalleeIdentity>,
    identity_b: Option<CalleeIdentity>,
) -> VerifiableFunction {
    let call = |identity, dest, target| Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        is_unsafe_sig: false,
        callee_identity: identity,
        callee_key: crate::sep_engine::tests::fixture_key(&SHARED_KEY.to_string()),
        is_foreign: false,
        func: SHARED_KEY.to_string(),
        args: vec![Operand::Copy(Place::local(1))],
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
    };
    let checked_add = |src: usize, dst: usize| Statement::Assign {
        place: Place::local(dst),
        rvalue: Rvalue::CheckedBinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(src)),
            Operand::Constant(ConstValue::Uint(1, 64)),
        ),
        span: SourceSpan::default(),
    };
    let overflow_assert = |tmp: usize, target: usize| Terminator::Assert {
        unwind: UnwindEdge::Unreachable,
        cond: Operand::Copy(Place::field(tmp, 1)),
        expected: false,
        msg: AssertMessage::Overflow(BinOp::Add),
        target: BlockId(target),
        span: SourceSpan::default(),
    };
    VerifiableFunction {
        name: "caller".to_string(),
        def_path: "k::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("b".into()) },
                LocalDecl { index: 4, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 5, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock { id: BlockId(0), stmts: vec![], terminator: call(identity_a, 2, 1) },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: call(identity_b, 3, 2) },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![checked_add(2, 4)],
                    terminator: overflow_assert(4, 3),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![checked_add(3, 5)],
                    terminator: overflow_assert(5, 4),
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
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

/// `ensures result <= 100` — true of callee A, stated about nothing else.
fn result_le_100() -> Formula {
    Formula::Le(Box::new(Formula::var("_0", Sort::Int)), Box::new(Formula::Int(100)))
}

/// The shape the compiler's Clean-origin minter produces: definitional
/// authority, no preconditions, one formal.
fn definitional_summary_of_a() -> FunctionSummary {
    FunctionSummary::new(SHARED_KEY)
        .with_param_names(vec!["a0".to_string()])
        .with_definitional_postcondition(result_le_100())
}

/// True iff `f` carries both a version-pinned variable and the literal `n`.
fn has_versioned_var_and_int(f: &Formula, n: i128) -> bool {
    fn walk(f: &Formula, ver: &mut bool, int: &mut bool, n: i128) {
        match f {
            Formula::Var(name, _) if name.contains('#') => *ver = true,
            Formula::Int(v) if *v == n => *int = true,
            _ => {}
        }
        for c in f.children() {
            walk(c, ver, int, n);
        }
    }
    let (mut ver, mut int) = (false, false);
    walk(f, &mut ver, &mut int, n);
    ver && int
}

fn mentions_int(f: &Formula, n: i128) -> bool {
    fn walk(f: &Formula, n: i128, found: &mut bool) {
        if matches!(f, Formula::Int(v) if *v == n) {
            *found = true;
        }
        for c in f.children() {
            walk(c, n, found);
        }
    }
    let mut found = false;
    walk(f, n, &mut found);
    found
}

/// THE MECHANISM. One summary, two callees, both assumed.
///
/// This is not a claim that the collision is reachable today — it is a
/// statement of what this crate does WHEN it is handed one, so the size of the
/// producer's obligation is visible. `assumptions_injected == 2` is the whole
/// finding: the second injection is a fact about a value the summary's function
/// never produced.
#[test]
fn one_summary_is_assumed_at_two_distinct_callees_under_one_key() {
    let caller = caller_with_two_colliding_calls(Some(IDENT_A), Some(IDENT_B));
    let mut db = SummaryDatabase::new();
    db.insert(definitional_summary_of_a());

    let r = modular_vcgen(&caller, &db);
    assert_eq!(
        r.assumptions_injected, 2,
        "the injection lane matches on the rendered name alone, so A's clause \
         is assumed at B's call site too"
    );
    assert_eq!(r.havoced_calls, 0);

    let map = build_semantic_guard_map_with_summaries(&caller, &db);
    // bb1 is A's post-call block, bb2 is B's.
    for block in [1usize, 2] {
        let facts = map.get(&BlockId(block)).cloned().unwrap_or_default();
        assert!(
            facts.iter().any(|f| has_versioned_var_and_int(f, 100)),
            "block {block} must carry the rebound, version-pinned bound: {facts:?}"
        );
    }
}

/// The un-forgeable channel that COULD discriminate is present on the
/// terminator and is inert: `Terminator::Call`'s `callee_identity` is dropped
/// by the `..` in `semantic_guard.rs`'s `Call` pattern, and
/// `modular::FunctionSummary` has nowhere to compare it to.
///
/// Three shapes, byte-identical verdicts: both sites unidentified, both sites
/// carrying the SAME identity, and the two sites carrying DIFFERENT identities.
/// If a future change teaches the lane to read the identity, this test is the
/// one that should be flipped — deliberately, with the summary side gaining an
/// identity field first.
#[test]
fn callee_identity_on_the_terminator_does_not_discriminate() {
    let mut db = SummaryDatabase::new();
    db.insert(definitional_summary_of_a());

    let shapes = [(None, None), (Some(IDENT_A), Some(IDENT_A)), (Some(IDENT_A), Some(IDENT_B))];
    let mut seen: Vec<usize> = Vec::new();
    for (a, b) in shapes {
        let caller = caller_with_two_colliding_calls(a, b);
        seen.push(modular_vcgen(&caller, &db).assumptions_injected);
    }
    assert_eq!(
        seen,
        vec![2, 2, 2],
        "identity is not read: differing `callee_identity` stamps change nothing"
    );
}

/// Arity is the ONLY accidental discriminator, and it is arity ALONE.
///
/// `summary.param_types` is never read by `callee_postcondition_is_injectable`
/// or by `rebind_callee_postconditions`, and the destination's own type is
/// never compared with the summary's return type. A summary whose declared
/// signature is `(bool) -> bool` is injected verbatim onto a `usize` call site
/// as long as the count matches; a summary of arity 2 is refused for arity
/// alone.
#[test]
fn only_arity_discriminates_never_types() {
    let caller = caller_with_two_colliding_calls(Some(IDENT_A), Some(IDENT_B));

    let mut wrong_types = SummaryDatabase::new();
    wrong_types.insert(
        FunctionSummary::new(SHARED_KEY)
            .with_param_names(vec!["a0".to_string()])
            .with_param_types(vec![Ty::Bool])
            .with_definitional_postcondition(result_le_100()),
    );
    assert_eq!(
        modular_vcgen(&caller, &wrong_types).assumptions_injected,
        2,
        "a signature that cannot belong to this call site is still injected"
    );

    let mut wrong_arity = SummaryDatabase::new();
    wrong_arity.insert(
        FunctionSummary::new(SHARED_KEY)
            .with_param_names(vec!["a0".to_string(), "a1".to_string()])
            .with_definitional_postcondition(result_le_100()),
    );
    let r = modular_vcgen(&caller, &wrong_arity);
    assert_eq!(r.assumptions_injected, 0, "arity is the one gate that fires");
    assert_eq!(r.havoced_calls, 2);
}

/// The consequence, at the obligation level: the assumption reaches the second
/// call site's OWN safety VC.
///
/// `b + 1` on a `usize` overflows exactly when `b == usize::MAX`, so with no
/// summary the violation is satisfiable (a FAIL/unknown row). The colliding
/// summary conjoins `b <= 100` — a statement about a value callee B never
/// produced — into the same block's guard set, and the violation is then
/// unsatisfiable. This test observes the FORMULA (the layer this crate owns);
/// the verdict flip is what that formula means to the solver.
#[test]
fn the_wrong_callees_bound_reaches_its_own_overflow_obligation() {
    let caller = caller_with_two_colliding_calls(Some(IDENT_A), Some(IDENT_B));

    let empty = SummaryDatabase::new();
    let without = build_semantic_guard_map_with_summaries(&caller, &empty)
        .get(&BlockId(3))
        .cloned()
        .unwrap_or_default();
    assert!(
        !without.iter().any(|f| mentions_int(f, 100)),
        "control: with no summary, callee B's dest carries no upper bound: {without:?}"
    );

    let mut db = SummaryDatabase::new();
    db.insert(definitional_summary_of_a());
    let with = build_semantic_guard_map_with_summaries(&caller, &db)
        .get(&BlockId(3))
        .cloned()
        .unwrap_or_default();
    assert!(
        with.iter().any(|f| has_versioned_var_and_int(f, 100)),
        "the colliding summary bounds callee B's dest in the block that owns \
         B's overflow obligation: {with:?}"
    );
}

/// The producer-side dedup this crate does NOT do.
///
/// `SummaryDatabase::insert` is LAST-write-wins on the name. Production never
/// reaches that path — `add_direct_call_contract_summaries` guards every insert
/// with `if db.get(&callee_name).is_some() { continue; }`, making it
/// FIRST-write-wins — so which of two colliding summaries is assumed depends
/// entirely on which side of that guard the producer sits on. Pinned so the two
/// disciplines cannot silently swap.
#[test]
fn insert_is_last_write_wins_and_carries_no_collision_signal() {
    let mut db = SummaryDatabase::new();
    db.insert(definitional_summary_of_a());
    db.insert(
        FunctionSummary::new(SHARED_KEY)
            .with_param_names(vec!["a0".to_string()])
            .with_definitional_postcondition(Formula::Le(
                Box::new(Formula::var("_0", Sort::Int)),
                Box::new(Formula::Int(7)),
            )),
    );
    assert_eq!(db.len(), 1, "two summaries, one key, no diagnostic");

    let caller = caller_with_two_colliding_calls(Some(IDENT_A), Some(IDENT_B));
    let facts = build_semantic_guard_map_with_summaries(&caller, &db)
        .get(&BlockId(1))
        .cloned()
        .unwrap_or_default();
    assert!(
        facts.iter().any(|f| has_versioned_var_and_int(f, 7)),
        "the SECOND insert silently replaced the first: {facts:?}"
    );
}
