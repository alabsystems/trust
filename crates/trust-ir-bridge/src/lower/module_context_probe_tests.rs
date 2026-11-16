//! `ModuleContextProbe` answers exactly what the per-probe rebuild answered, and
//! builds the survivor set's context once per set instead of once per probe.
//!
//! The reference below is the probe as it was before the context was shared:
//! every call rebuilds the closure-environment registry and every member's
//! name and signature from the whole set. The fixtures are chosen so that the
//! answer depends on the SET, not only on the member: a closure caller that
//! lowers only when its closure body is a candidate, a caller whose closure body
//! is missing, a call to a function outside the set, a member whose signature
//! cannot be registered (which fails every probe of its set), and closures whose
//! type is rustc's unmodeled-environment marker (`TyKind::Closure` "needs
//! captured-environment modeling"). Only the closure-environment registry
//! (`collect_closure_env_types` over the WHOLE set) can type such a closure: its
//! body lowers only when another member constructs it, and not when two members
//! construct it over contradicting captures (the registry poisons the name). A
//! registry built from part of the set changes those answers.

use std::collections::HashSet;

use trust_types::{
    AggregateKind, BasicBlock as TrustBlock, BlockId, ClosureCallKind, ConstValue, LocalDecl,
    Operand, Place, Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, UnwindEdge,
    VerifiableBody, VerifiableFunction,
};

use super::*;

fn function(
    name: &str,
    locals: Vec<LocalDecl>,
    blocks: Vec<TrustBlock>,
    arg_count: usize,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn assign(place: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(place), rvalue, span: SourceSpan::default() }
}

fn call(func: &str, args: Vec<Operand>, dest: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        is_foreign: false,
        func: func.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
    }
}

/// `fn name(x: u32) -> u32 { x }`
fn plain(name: &str) -> VerifiableFunction {
    function(
        name,
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
        ],
        vec![TrustBlock {
            id: BlockId(0),
            stmts: vec![assign(0, Rvalue::Use(Operand::Copy(Place::local(1))))],
            terminator: Terminator::Return,
        }],
        1,
    )
}

fn closure_ty(closure: &str, capture: Ty) -> Ty {
    Ty::Closure { name: closure.to_string(), upvars: vec![capture], call: None }
}

/// Builds the closure `closure` over one captured `capture` and calls it through
/// the `FnOnce::call_once` shim, which lowers only when the closure's body is a
/// registered candidate.
fn closure_caller(name: &str, closure: &str, capture: Ty) -> VerifiableFunction {
    function(
        name,
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: capture.clone(), name: Some("captured".into()) },
            LocalDecl { index: 2, ty: closure_ty(closure, capture), name: Some("closure".into()) },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32()]), name: Some("args".into()) },
            LocalDecl { index: 4, ty: Ty::u32(), name: Some("result".into()) },
        ],
        vec![
            TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(
                        2,
                        Rvalue::Aggregate(
                            AggregateKind::Closure {
                                name: closure.to_string(),
                                captures: vec![],
                                call_kind: ClosureCallKind::FnOnce,
                            },
                            vec![Operand::Copy(Place::local(1))],
                        ),
                    ),
                    assign(
                        3,
                        Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![Operand::Constant(ConstValue::Uint(7, 32))],
                        ),
                    ),
                ],
                terminator: call(
                    "core::ops::function::FnOnce::call_once",
                    vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(3))],
                    4,
                ),
            },
            TrustBlock {
                id: BlockId(1),
                stmts: vec![assign(0, Rvalue::Use(Operand::Copy(Place::local(4))))],
                terminator: Terminator::Return,
            },
        ],
        1,
    )
}

/// The body of `closure`: `|arg: u32| arg`, its environment holding `capture`.
fn closure_body(closure: &str, capture: Ty) -> VerifiableFunction {
    let mut body = function(
        closure,
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: closure_ty(closure, capture), name: Some("self".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("arg".into()) },
        ],
        vec![TrustBlock {
            id: BlockId(0),
            stmts: vec![assign(0, Rvalue::Use(Operand::Copy(Place::local(2))))],
            terminator: Terminator::Return,
        }],
        2,
    );
    body.def_path = closure.to_string();
    body
}

/// rustc's spelling of a closure type whose captured environment it could not
/// model; only the set's closure-environment registry can type it.
fn unmodeled_closure_ty(closure: &str) -> Ty {
    Ty::Unsupported {
        kind: "TyKind::Closure".into(),
        detail: format!("closure {closure} needs captured-environment modeling"),
    }
}

/// `closure_caller` whose closure local is the unmodeled-environment marker.
fn unmodeled_closure_caller(name: &str, closure: &str, capture: Ty) -> VerifiableFunction {
    let mut caller = closure_caller(name, closure, capture);
    caller.body.locals[2].ty = unmodeled_closure_ty(closure);
    caller
}

/// `closure_body` whose `self` environment is the unmodeled-environment marker:
/// it lowers only when the registry learned the environment from a member that
/// constructs the closure.
fn unmodeled_closure_body(closure: &str) -> VerifiableFunction {
    let mut body = closure_body(closure, Ty::u32());
    body.body.locals[1].ty = unmodeled_closure_ty(closure);
    body
}

/// Calls `callee`, which is not a member of any fixture set.
fn absent_caller(name: &str, callee: &str) -> VerifiableFunction {
    function(
        name,
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("result".into()) },
        ],
        vec![
            TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: call(callee, vec![Operand::Copy(Place::local(1))], 2),
            },
            TrustBlock {
                id: BlockId(1),
                stmts: vec![assign(0, Rvalue::Use(Operand::Copy(Place::local(2))))],
                terminator: Terminator::Return,
            },
        ],
        1,
    )
}

/// Declares one argument but has no local for it, so its signature cannot be
/// registered (`MissingLocal(1)`).
fn unregistrable(name: &str) -> VerifiableFunction {
    function(
        name,
        vec![LocalDecl { index: 0, ty: Ty::u32(), name: None }],
        vec![TrustBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
        1,
    )
}

/// The probe before the context was shared, rebuilt from scratch on every call.
fn reference_lowers_rebuilding(
    funcs: &[VerifiableFunction],
    index: usize,
    expected_absent_callees: &HashSet<String>,
    structural_drop_adts: &HashSet<String>,
) -> bool {
    let Some(func) = funcs.get(index) else { return false };
    let ea: FxHashSet<String> = expected_absent_callees.iter().cloned().collect();
    let sd: FxHashSet<String> = structural_drop_adts.iter().cloned().collect();
    let func_refs = funcs.iter().collect::<Vec<_>>();
    let Ok(closure_env_types) = collect_closure_env_types(&func_refs) else { return false };
    let mut known_functions = FxHashMap::default();
    let mut known_function_signatures = FxHashMap::default();
    for (i, f) in funcs.iter().enumerate() {
        let id = FuncId::new(i as u32);
        register_function_name(&mut known_functions, f, id);
        if register_function_signature(&mut known_function_signatures, f, id, &closure_env_types)
            .is_err()
        {
            return false;
        }
    }
    let mut scratch = Module::new("__trust_bundle_probe");
    let mut type_cache = FxHashMap::default();
    let mut tuple_ledger = TupleLayoutLedger::default();
    lower_function_into(
        func,
        &mut scratch,
        &known_functions,
        &known_function_signatures,
        &closure_env_types,
        &mut type_cache,
        &mut tuple_ledger,
        &ea,
        &sd,
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &crate::lower::CallReachWithdrawals::default(), // no call-reach withdrawals
        None,
        &FxHashSet::default(),
        &InstanceHypothesisSites::default(),
        &crate::lower::CompilerAllocGrowPins::default(),
    )
    .is_ok()
}

const CLOSURE_A: &str = "test::probe::{closure#0}";
const CLOSURE_B: &str = "test::probe::{closure#1}";
const CLOSURE_C: &str = "test::probe::{closure#2}";

/// The members the fixture sets are drawn from (the target is always first).
fn pool() -> Vec<VerifiableFunction> {
    vec![
        closure_caller("caller_a", CLOSURE_A, Ty::u32()),
        closure_body(CLOSURE_A, Ty::u32()),
        // Constructs CLOSURE_A over a u64 (the registry poisons CLOSURE_A's name,
        // which the explicitly typed members above do not need).
        closure_caller("caller_a_u64", CLOSURE_A, Ty::u64()),
        // CLOSURE_B's body is never a candidate.
        closure_caller("caller_b", CLOSURE_B, Ty::u32()),
        absent_caller("absent_caller", "test::not_bundled"),
        plain("helper"),
        // CLOSURE_C is typed only through the registry: its body lowers when a
        // member constructs it, and not when the two constructors contradict.
        unmodeled_closure_caller("caller_c", CLOSURE_C, Ty::u32()),
        unmodeled_closure_body(CLOSURE_C),
        closure_caller("caller_c_u64", CLOSURE_C, Ty::u64()),
    ]
}

const POOL_CALLER_C: usize = 6;
const POOL_BODY_C: usize = 7;
const POOL_CALLER_C_U64: usize = 8;

fn probe_answers(
    funcs: &[VerifiableFunction],
    ea: &HashSet<String>,
    sd: &HashSet<String>,
) -> Vec<bool> {
    let probe = ModuleContextProbe::new(funcs, ea, sd);
    // One past the end too: an out-of-range index answers false.
    (0..=funcs.len()).map(|index| probe.lowers(index)).collect()
}

fn reference_answers(
    funcs: &[VerifiableFunction],
    ea: &HashSet<String>,
    sd: &HashSet<String>,
) -> Vec<bool> {
    (0..=funcs.len()).map(|index| reference_lowers_rebuilding(funcs, index, ea, sd)).collect()
}

fn one_shot_answers(
    funcs: &[VerifiableFunction],
    ea: &HashSet<String>,
    sd: &HashSet<String>,
) -> Vec<bool> {
    (0..=funcs.len())
        .map(|index| verifiable_function_lowers_in_module_context(funcs, index, ea, sd))
        .collect()
}

/// EXACTNESS: over every subset of the pool (behind a fixed target), in both
/// member orders, with and without an expected-absent / structural-drop context,
/// the shared-context probe, the one-shot entry point and the per-probe rebuild
/// give the same answer for every index. The fixtures must also discriminate:
/// some sets keep a member the same member's absence elsewhere would drop.
#[test]
fn shared_context_probe_answers_exactly_what_the_per_probe_rebuild_answered() {
    let pool = pool();
    let empty = HashSet::new();
    let ea: HashSet<String> = ["test::not_bundled".to_string()].into_iter().collect();
    let sd: HashSet<String> = ["test::Droppy".to_string()].into_iter().collect();
    let mut compared = 0usize;
    let mut kept = 0usize;
    let mut dropped = 0usize;
    for mask in 0u32..(1 << pool.len()) {
        let chosen: Vec<VerifiableFunction> = pool
            .iter()
            .enumerate()
            .filter(|(bit, _)| mask & (1 << bit) != 0)
            .map(|(_, member)| member.clone())
            .collect();
        for reversed in [false, true] {
            let mut funcs = vec![plain("target")];
            if reversed {
                funcs.extend(chosen.iter().rev().cloned());
            } else {
                funcs.extend(chosen.iter().cloned());
            }
            for (ea, sd) in [(&empty, &empty), (&ea, &sd)] {
                let shared = probe_answers(&funcs, ea, sd);
                assert_eq!(
                    shared,
                    reference_answers(&funcs, ea, sd),
                    "shared-context probe disagrees with the per-probe rebuild on mask {mask:#b} \
                     (reversed={reversed}, members {:?})",
                    funcs.iter().map(|f| f.def_path.as_str()).collect::<Vec<_>>()
                );
                assert_eq!(shared, one_shot_answers(&funcs, ea, sd));
                assert!(!shared[funcs.len()], "an out-of-range index must answer false");
                compared += funcs.len() + 1;
                kept += shared[..funcs.len()].iter().filter(|kept| **kept).count();
                dropped += shared[..funcs.len()].iter().filter(|kept| !**kept).count();
            }
        }
    }
    assert!(compared > 1000, "the sweep compared only {compared} answers");
    assert!(kept > 0 && dropped > 0, "the fixtures must both keep and drop members");

    // `caller_a` lowers with its closure body as a candidate and, since fix6
    // CLOSURE-ABSENT-CALLEE, without it too: the shim is then the fail-closed
    // absent callee rather than an error. (That the SET decides is pinned by
    // `the_closure_environment_registry_comes_from_the_whole_set`.)
    let with_body = vec![plain("target"), pool[0].clone(), pool[1].clone()];
    let without_body = vec![plain("target"), pool[0].clone()];
    assert!(probe_answers(&with_body, &empty, &empty)[1]);
    assert!(probe_answers(&without_body, &empty, &empty)[1]);
}

/// The closure-environment registry is built from the WHOLE set, whatever the
/// order: a body whose environment is the unmodeled marker lowers only when some
/// OTHER member constructs its closure (before or after it), and not when two
/// members construct it over contradicting captures. A registry built from the
/// probed member, the target or a prefix of the set fails these.
#[test]
fn the_closure_environment_registry_comes_from_the_whole_set() {
    let pool = pool();
    let empty = HashSet::new();
    let body_c = pool[POOL_BODY_C].clone();
    let caller_c = pool[POOL_CALLER_C].clone();
    let caller_c_u64 = pool[POOL_CALLER_C_U64].clone();
    let cases: [(Vec<VerifiableFunction>, usize, bool); 5] = [
        (vec![plain("target"), body_c.clone()], 1, false),
        (vec![plain("target"), caller_c.clone(), body_c.clone()], 2, true),
        (vec![plain("target"), body_c.clone(), caller_c.clone()], 1, true),
        (vec![plain("target"), body_c.clone(), caller_c_u64.clone()], 1, true),
        (vec![plain("target"), caller_c.clone(), body_c.clone(), caller_c_u64.clone()], 2, false),
    ];
    for (funcs, body_index, lowers) in &cases {
        let members = funcs.iter().map(|f| f.def_path.as_str()).collect::<Vec<_>>();
        let shared = probe_answers(funcs, &empty, &empty);
        assert_eq!(shared, reference_answers(funcs, &empty, &empty), "members {members:?}");
        assert_eq!(shared[*body_index], *lowers, "body of CLOSURE_C in {members:?}");
    }
}

/// A member whose signature cannot be registered fails EVERY probe of its set,
/// as the per-probe rebuild did, including members that lower in any other set.
#[test]
fn an_unregistrable_member_fails_every_probe_of_its_set() {
    let empty = HashSet::new();
    let mut funcs = vec![plain("target"), plain("helper")];
    assert_eq!(probe_answers(&funcs, &empty, &empty), vec![true, true, false]);
    funcs.push(unregistrable("broken"));
    let shared = probe_answers(&funcs, &empty, &empty);
    assert_eq!(shared, vec![false; funcs.len() + 1]);
    assert_eq!(shared, reference_answers(&funcs, &empty, &empty));
}

fn context_builds() -> usize {
    MODULE_PROBE_CONTEXT_BUILDS.with(|builds| builds.get())
}

/// COST: one probe object builds the set's context once, however many members it
/// probes, and not at all when nothing is probed. The one-shot entry point still
/// builds one per call, which is the per-member cost the compiler's survivor round
/// used to pay.
#[test]
fn a_probe_builds_the_set_context_once_for_all_its_members() {
    let empty = HashSet::new();
    let mut funcs = vec![plain("target")];
    funcs.extend((0..48).map(|i| plain(&format!("member_{i}"))));
    funcs.extend(pool());

    let before = context_builds();
    let unused = ModuleContextProbe::new(&funcs, &empty, &empty);
    drop(unused);
    assert_eq!(context_builds(), before, "an unused probe must build nothing");

    let probe = ModuleContextProbe::new(&funcs, &empty, &empty);
    let answers: Vec<bool> = (0..funcs.len()).map(|index| probe.lowers(index)).collect();
    assert_eq!(context_builds(), before + 1, "one build for {} probes", funcs.len());
    assert_eq!(answers.iter().filter(|kept| **kept).count(), 48 + 1 + pool_kept(&funcs));

    let before = context_builds();
    for index in 0..funcs.len() {
        verifiable_function_lowers_in_module_context(&funcs, index, &empty, &empty);
    }
    assert_eq!(context_builds(), before + funcs.len());
}

/// How many of the pool members `funcs` (target + 48 plain + pool) keeps, from
/// the per-probe rebuild.
fn pool_kept(funcs: &[VerifiableFunction]) -> usize {
    let empty = HashSet::new();
    (funcs.len() - pool().len()..funcs.len())
        .filter(|index| reference_lowers_rebuilding(funcs, *index, &empty, &empty))
        .count()
}

// ---------------------------------------------------------------------------
// SURVIVOR-REPLAY-1: `SurvivorProbe` answers each round exactly what a fresh probe of
// that round's set answers, while lowering a member again only when one of the reads
// its last passing lowering made of the set answers differently.
// ---------------------------------------------------------------------------

const CLOSURE_D: &str = "test::probe::{closure#3}";

/// `fn name(x: u32) -> u32 { x }` plus a cast of an owned sequence's field, which no
/// lowering supports (`owned_sequence_field_read_without_an_expectation_still_fails_closed`):
/// it registers like `plain`, but its own lowering fails in every set. A cascade SEED.
fn unlowerable(name: &str) -> VerifiableFunction {
    let mut func = plain(name);
    func.body.locals.push(LocalDecl {
        index: 2,
        ty: Ty::Seq { drop_auth: None, elem: Box::new(Ty::u8()) },
        name: Some("v".into()),
    });
    func.body.locals.push(LocalDecl { index: 3, ty: Ty::u64(), name: Some("cap".into()) });
    func.body.blocks[0].stmts.insert(
        0,
        assign(
            3,
            Rvalue::Cast(
                Operand::Copy(Place { local: 2, projections: vec![Projection::Field(1)] }),
                Ty::u64(),
            ),
        ),
    );
    func
}

/// Constructs the closure `closure`, whose type is the unmodeled-environment marker
/// (so the set's registry learns its environment from this member), then calls
/// `callee`. When the cascade drops this parent, `closure`'s body loses the only
/// member that types it.
fn closure_parent(name: &str, closure: &str, callee: &str) -> VerifiableFunction {
    function(
        name,
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: unmodeled_closure_ty(closure), name: Some("closure".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: Some("result".into()) },
        ],
        vec![
            TrustBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    2,
                    Rvalue::Aggregate(
                        AggregateKind::Closure {
                            name: closure.to_string(),
                            captures: vec![],
                            call_kind: ClosureCallKind::FnOnce,
                        },
                        vec![Operand::Copy(Place::local(1))],
                    ),
                )],
                terminator: call(callee, vec![Operand::Copy(Place::local(1))], 3),
            },
            TrustBlock {
                id: BlockId(1),
                stmts: vec![assign(0, Rvalue::Use(Operand::Copy(Place::local(3))))],
                terminator: Terminator::Return,
            },
        ],
        1,
    )
}

/// `plain(name)` over `u64`: the same name as `plain(name)` with another signature.
fn plain_u64(name: &str) -> VerifiableFunction {
    let mut func = plain(name);
    func.body.locals[0].ty = Ty::u64();
    func.body.locals[1].ty = Ty::u64();
    func.body.return_ty = Ty::u64();
    func
}

/// A target and every kind of member whose answer depends on the SET, so that a member
/// that passed one round can fail a later one (and the reverse):
/// * the pool: closures typed only by the whole set's registry, with poisoning;
/// * a call chain into a SEED that never lowers (a drop cascade of depth 3);
/// * a closure whose only constructor is a parent the cascade drops;
/// * two members under one name (the name map poisons it; the signature map keeps
///   the LAST one) and a caller of that name;
/// * fillers whose answer never changes (what replay is for).
fn adversarial_candidates(fillers: usize) -> Vec<VerifiableFunction> {
    let mut candidates = vec![plain("target")];
    candidates.extend((0..fillers).map(|i| plain(&format!("filler_{i}"))));
    candidates.extend(pool());
    candidates.extend([
        closure_parent("parent_d", CLOSURE_D, "test::chain_1"),
        unmodeled_closure_body(CLOSURE_D),
        absent_caller("chain_1", "test::chain_2"),
        absent_caller("chain_2", "test::chain_3"),
        absent_caller("chain_3", "test::seed"),
        unlowerable("seed"),
        absent_caller("dup_caller", "test::dup"),
        plain("dup"),
        plain_u64("dup"),
    ]);
    candidates
}

/// The set a round of `origins` probes, as the compiler materialized it before
/// SURVIVOR-REPLAY-1 (a clone of each survivor, in order).
fn round_set(candidates: &[VerifiableFunction], origins: &[usize]) -> Vec<VerifiableFunction> {
    origins.iter().map(|&origin| candidates[origin].clone()).collect()
}

/// The compiler's dropped-candidate closure (`trust_verify.rs`, without its
/// local-member exception, which no fixture here meets): after a round's probes keep
/// `kept`, drop each non-target member that calls a candidate no longer kept.
fn dropped_candidate_closure(candidates: &[VerifiableFunction], kept: &[usize]) -> Vec<usize> {
    let pushed: HashSet<&str> = candidates.iter().map(|f| f.def_path.as_str()).collect();
    let kept_paths: HashSet<&str> =
        kept.iter().map(|&origin| candidates[origin].def_path.as_str()).collect();
    kept.iter()
        .enumerate()
        .filter(|(index, origin)| {
            *index == 0
                || !candidates[**origin].body.blocks.iter().any(|block| {
                    matches!(&block.terminator, Terminator::Call { func, .. }
                        if pushed.contains(func.as_str()) && !kept_paths.contains(func.as_str()))
                })
        })
        .map(|(_, &origin)| origin)
        .collect()
}

/// One round of a survivor loop: the set's origins and each non-target member's answer.
type LoopRound = (Vec<usize>, Vec<bool>);

/// The compiler's survivor loop, asking `lowers(set origins, index)` for each
/// non-target member of each round, to the fixed point.
fn survivor_loop(
    candidates: &[VerifiableFunction],
    mut lowers: impl FnMut(&[usize], usize) -> bool,
) -> Vec<LoopRound> {
    let mut origins: Vec<usize> = (0..candidates.len()).collect();
    let mut rounds = Vec::new();
    loop {
        let answers: Vec<bool> = (1..origins.len()).map(|index| lowers(&origins, index)).collect();
        let kept: Vec<usize> = origins
            .iter()
            .enumerate()
            .filter(|(index, _)| *index == 0 || answers[index - 1])
            .map(|(_, &origin)| origin)
            .collect();
        let closed = dropped_candidate_closure(candidates, &kept);
        rounds.push((origins.clone(), answers));
        let stabilized = closed.len() == origins.len();
        origins = closed;
        if stabilized {
            return rounds;
        }
    }
}

/// The loop before SURVIVOR-REPLAY-1: a fresh `ModuleContextProbe` of each round's
/// cloned set.
fn survivor_loop_before(
    candidates: &[VerifiableFunction],
    ea: &HashSet<String>,
    sd: &HashSet<String>,
) -> Vec<LoopRound> {
    let mut cached: Option<(Vec<usize>, Vec<VerifiableFunction>)> = None;
    survivor_loop(candidates, |origins, index| {
        if cached.as_ref().is_none_or(|(set_origins, _)| set_origins != origins) {
            cached = Some((origins.to_vec(), round_set(candidates, origins)));
        }
        let (_, set) = cached.as_ref().expect("set built above");
        ModuleContextProbe::new(set, ea, sd).lowers(index)
    })
}

/// The loop with SURVIVOR-REPLAY-1, as the compiler runs it.
fn survivor_loop_replaying(
    candidates: &[VerifiableFunction],
    ea: &HashSet<String>,
    sd: &HashSet<String>,
    audit: bool,
) -> (Vec<LoopRound>, SurvivorProbeStats) {
    let mut probe = SurvivorProbe::new(candidates, ea, sd).with_audit(audit);
    let mut origins: Vec<usize> = (0..candidates.len()).collect();
    let mut rounds = Vec::new();
    loop {
        let mut round = probe.round(&origins);
        let answers: Vec<bool> = (1..origins.len()).map(|index| round.lowers(index)).collect();
        drop(round);
        let kept: Vec<usize> = origins
            .iter()
            .enumerate()
            .filter(|(index, _)| *index == 0 || answers[index - 1])
            .map(|(_, &origin)| origin)
            .collect();
        let closed = dropped_candidate_closure(candidates, &kept);
        rounds.push((origins.clone(), answers));
        let stabilized = closed.len() == origins.len();
        origins = closed;
        if stabilized {
            return (rounds, probe.stats());
        }
    }
}

fn names(candidates: &[VerifiableFunction], origins: &[usize]) -> Vec<String> {
    origins.iter().map(|&origin| candidates[origin].def_path.clone()).collect()
}

/// EXACTNESS over the compiler's own loop: with replay (audited or not) the survivor
/// loop runs the same rounds, gets the same answer for every member of every round,
/// and keeps the same survivors as the loop that probed each round afresh — on a drop
/// cascade over several rounds and a closure whose parent the cascade drops, whose
/// body PASSES while the parent survives and must FAIL once it is gone.
#[test]
fn the_survivor_loop_keeps_exactly_the_same_members_with_replay() {
    let empty = HashSet::new();
    let ea: HashSet<String> = ["test::not_bundled".to_string()].into_iter().collect();
    for fillers in [0, 5] {
        let candidates = adversarial_candidates(fillers);
        for (ea, sd) in [(&empty, &empty), (&ea, &empty)] {
            let before = survivor_loop_before(&candidates, ea, sd);
            for audit in [true, false] {
                let (after, stats) = survivor_loop_replaying(&candidates, ea, sd, audit);
                for (round, ((before_set, before_answers), (after_set, after_answers))) in
                    before.iter().zip(&after).enumerate()
                {
                    assert_eq!(
                        (before_set, before_answers),
                        (after_set, after_answers),
                        "round {round} (audit={audit}, fillers={fillers}) of members {:?}",
                        names(&candidates, before_set)
                    );
                }
                assert_eq!(before.len(), after.len(), "the same number of rounds");
                assert_eq!(stats.rounds, after.len());
                assert_eq!(stats.audit_mismatches, 0);
                assert!(stats.replayed > 0, "replay must serve some answers: {stats:?}");
                assert!(stats.replay_misses > 0, "some reads must answer differently: {stats:?}");
            }
            // The fixtures must be adversarial: the cascade takes several rounds, and the
            // closure body that passed while its parent survived fails after the parent is
            // gone (an answer cached across rounds would keep it).
            assert!(before.len() >= 4, "a multi-round cascade: {} rounds", before.len());
            let body_d = candidates
                .iter()
                .position(|f| f.def_path == CLOSURE_D)
                .expect("CLOSURE_D's body is a candidate");
            let parent_d = candidates
                .iter()
                .position(|f| f.def_path == "test::parent_d")
                .expect("parent_d is a candidate");
            let answer_of = |(set, answers): &LoopRound, origin: usize| {
                set.iter().position(|&member| member == origin).map(|index| answers[index - 1])
            };
            let body_answers: Vec<Option<bool>> =
                before.iter().map(|round| answer_of(round, body_d)).collect();
            assert_eq!(body_answers[0], Some(true), "body_d lowers while parent_d constructs it");
            assert!(
                body_answers.contains(&Some(false)),
                "body_d must fail once parent_d is dropped: {body_answers:?}"
            );
            let last = &before.last().expect("at least one round").0;
            assert!(!last.contains(&parent_d) && !last.contains(&body_d));
            assert!(last.iter().any(|&origin| candidates[origin].def_path == "test::helper"));
        }
    }
}

/// A deterministic shrinking schedule: from the whole candidate list, drop one to
/// three non-target members per round (chosen by a linear congruential generator)
/// until only the target is left.
fn shrinking_schedule(len: usize, mut state: u64) -> Vec<Vec<usize>> {
    let mut origins: Vec<usize> = (0..len).collect();
    let mut schedule = vec![origins.clone()];
    while origins.len() > 1 {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let drops = 1 + (state >> 61) as usize % 3;
        for _ in 0..drops.min(origins.len() - 1) {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let index = 1 + (state >> 33) as usize % (origins.len() - 1);
            origins.remove(index);
        }
        schedule.push(origins.clone());
    }
    schedule
}

/// EXACTNESS for ANY shrinking sequence of sets, not only the ones the loop produces:
/// every answer of every round (each member, the target, and one index past the end)
/// equals the per-probe rebuild's answer for that round's set. The schedules drop
/// callees out from under passing callers, constructors out from under closure bodies,
/// and one of two same-named members (un-poisoning the name and changing the
/// signature it resolves to), and they renumber every member behind a drop.
#[test]
fn every_survivor_round_answers_what_a_fresh_probe_of_its_set_answers() {
    let empty = HashSet::new();
    let ea: HashSet<String> = ["test::not_bundled".to_string()].into_iter().collect();
    let candidates = adversarial_candidates(3);
    let mut total = SurvivorProbeStats::default();
    let mut compared = 0usize;
    // How often a member that passed its latest probe fails a later round: each is an
    // answer a cache that ignored the set would get wrong.
    let mut passed_then_failed = 0usize;
    for seed in 0..48u64 {
        let schedule = shrinking_schedule(candidates.len(), seed);
        for (ea, sd) in [(&empty, &empty), (&ea, &empty)] {
            for audit in [true, false] {
                let mut probe = SurvivorProbe::new(&candidates, ea, sd).with_audit(audit);
                let mut latest: Vec<Option<bool>> = vec![None; candidates.len()];
                for origins in &schedule {
                    let set = round_set(&candidates, origins);
                    let expected = reference_answers(&set, ea, sd);
                    let mut round = probe.round(origins);
                    let answers: Vec<bool> =
                        (0..=origins.len()).map(|index| round.lowers(index)).collect();
                    drop(round);
                    assert_eq!(
                        answers,
                        expected,
                        "seed {seed} (audit={audit}): members {:?}",
                        names(&candidates, origins)
                    );
                    compared += answers.len();
                    for (index, &origin) in origins.iter().enumerate() {
                        if audit && latest[origin] == Some(true) && !answers[index] {
                            passed_then_failed += 1;
                        }
                        latest[origin] = Some(answers[index]);
                    }
                }
                let stats = probe.stats();
                assert_eq!(stats.audit_mismatches, 0, "seed {seed}: {stats:?}");
                total.rounds += stats.rounds;
                total.lowered += stats.lowered;
                total.replayed += stats.replayed;
                total.replay_misses += stats.replay_misses;
            }
        }
    }
    assert!(compared > 10_000, "compared only {compared} answers");
    assert!(passed_then_failed > 0, "the schedules must fail members that passed before");
    assert!(total.replayed > total.lowered, "replay must serve most answers: {total:?}");
    assert!(total.replay_misses > 0, "{total:?}");
}

/// The renaming a replay relies on: a member's answer does not depend on its own or
/// any other member's `FuncId` NUMBER. Over every subset of the pool behind the
/// target, reversing the set (which renumbers every member) or putting fillers in
/// front (which renumbers every member behind them, as a drop does) leaves each
/// member's answer unchanged. The pool has no two members under one name, so
/// neither the name map's poisoning nor the signature map's last-wins depends on the
/// order.
#[test]
fn a_members_answer_does_not_depend_on_funcid_numbers() {
    let pool = pool();
    let empty = HashSet::new();
    let fillers: Vec<VerifiableFunction> = (0..3).map(|i| plain(&format!("filler_{i}"))).collect();
    let mut compared = 0usize;
    for mask in 0u32..(1 << pool.len()) {
        let chosen: Vec<VerifiableFunction> = pool
            .iter()
            .enumerate()
            .filter(|(bit, _)| mask & (1 << bit) != 0)
            .map(|(_, member)| member.clone())
            .collect();
        let mut forward = vec![plain("target")];
        forward.extend(chosen.iter().cloned());
        let mut reversed = vec![plain("target")];
        reversed.extend(chosen.iter().rev().cloned());
        let mut shifted = vec![plain("target")];
        shifted.extend(fillers.iter().cloned());
        shifted.extend(chosen.iter().cloned());
        let forward_answers = probe_answers(&forward, &empty, &empty);
        let reversed_answers = probe_answers(&reversed, &empty, &empty);
        let shifted_answers = probe_answers(&shifted, &empty, &empty);
        let n = chosen.len();
        for i in 0..n {
            assert_eq!(
                forward_answers[1 + i],
                reversed_answers[n - i],
                "mask {mask:#b}, member {i}"
            );
            assert_eq!(forward_answers[1 + i], shifted_answers[1 + fillers.len() + i]);
            compared += 1;
        }
    }
    assert!(compared > 2000, "compared only {compared} answers");
}

/// COST: across rounds a survivor is lowered again only when a read of its last
/// lowering answers differently. A depth-3 cascade (`chain_1 → chain_2 → chain_3 →
/// seed`) behind 40 fillers takes four rounds, one call level each; the loop used to
/// lower every non-target survivor in every round (44 + 42 + 41 + 40 = 167
/// lowerings). With replay each member is lowered once (44), plus once more for each
/// chain member whose callee was dropped (2 misses): 46 lowerings, 121 replays, and
/// one set context per round.
#[test]
fn replay_lowers_each_unchanged_survivor_once() {
    let empty = HashSet::new();
    let mut candidates = vec![plain("target")];
    candidates.extend((0..40).map(|i| plain(&format!("filler_{i}"))));
    candidates.extend([
        absent_caller("chain_1", "test::chain_2"),
        absent_caller("chain_2", "test::chain_3"),
        absent_caller("chain_3", "test::seed"),
        unlowerable("seed"),
    ]);
    let before = survivor_loop_before(&candidates, &empty, &empty);
    let probed_before: Vec<usize> = before.iter().map(|(_, answers)| answers.len()).collect();
    assert_eq!(probed_before, vec![44, 42, 41, 40]);

    let builds = context_builds();
    let (after, stats) = survivor_loop_replaying(&candidates, &empty, &empty, false);
    assert_eq!(after, before);
    assert_eq!(context_builds(), builds + 4, "one set context per round");
    assert_eq!(
        stats,
        SurvivorProbeStats {
            rounds: 4,
            lowered: 44 + 2,
            replayed: 41 + 40 + 40,
            replay_misses: 2,
            audit_mismatches: 0,
        }
    );
    let survivors = &after.last().expect("rounds").0;
    assert_eq!(survivors.len(), 41, "the target and the fillers survive");
}

/// The audit's POSITIVE CONTROL. A log that left out a read the lowering depends on
/// would replay as a pass in a set where the member now fails. `set_context` cannot
/// record such a log (every read of the set goes through a recording accessor), so
/// one is forged here: an empty log replays in any set. The member is the closure
/// body whose only constructor is `parent_d`: it lowers while `parent_d` is in the set
/// and fails once it is not. Audited, the forged replay is caught, answered with the
/// fresh lowering's `false`, counted, and its log dropped; unaudited, it is believed,
/// which is what the audit is for.
#[test]
fn the_replay_audit_catches_a_log_that_leaves_out_a_read() {
    let empty = HashSet::new();
    let candidates = adversarial_candidates(0);
    let origin_of = |path: &str| {
        candidates.iter().position(|f| f.def_path == path).unwrap_or_else(|| panic!("{path}"))
    };
    let body = origin_of(CLOSURE_D);
    let parent = origin_of("test::parent_d");
    let all: Vec<usize> = (0..candidates.len()).collect();
    let without_parent: Vec<usize> =
        all.iter().copied().filter(|&origin| origin != parent).collect();
    let index_in =
        |origins: &[usize]| origins.iter().position(|&origin| origin == body).expect("member");
    // The truth: the body lowers beside its constructor and fails without it.
    let set = round_set(&candidates, &all);
    assert!(ModuleContextProbe::new(&set, &empty, &empty).lowers(index_in(&all)));
    let set = round_set(&candidates, &without_parent);
    assert!(!ModuleContextProbe::new(&set, &empty, &empty).lowers(index_in(&without_parent)));
    for audit in [true, false] {
        let mut probe = SurvivorProbe::new(&candidates, &empty, &empty).with_audit(audit);
        assert!(probe.round(&all).lowers(index_in(&all)));
        assert!(
            probe.passed_reads[body].as_ref().is_some_and(|reads| !reads.is_empty()),
            "a passing lowering keeps the log of its reads, and this one reads the set"
        );
        probe.passed_reads[body] = Some(Vec::new());
        let answer = probe.round(&without_parent).lowers(index_in(&without_parent));
        let stats = probe.stats();
        assert_eq!((stats.lowered, stats.replayed), (1, 1), "audit={audit}");
        if audit {
            assert!(!answer, "the audit re-lowers the member and answers what that lowering did");
            assert_eq!(stats.audit_mismatches, 1);
            assert!(probe.passed_reads[body].is_none(), "the forged log is dropped");
        } else {
            assert!(answer, "unaudited, the forged log's replay is believed");
            assert_eq!(stats.audit_mismatches, 0);
        }
    }
}
