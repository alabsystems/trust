#![cfg(feature = "ay-backend")]
// Trust (derived trivial-setter summary — end-to-end oracle for the base
// verification lane of tests/trust-falsification/proved/assert_mut_setter_identity.rs):
//
//   fn set(p: &mut u32, v: u32) { *p = v; }
//   pub fn f(x: u32, v: u32) -> u32 { let mut a = x; set(&mut a, v); assert!(a == v); a }
//
// The `&mut a` argument HAVOCS `a` at the call (correct — the P0 staleness fix
// on `single_assign_names` excludes it from every stable-def channel), but the
// caller then learned NOTHING about `a`'s NEW value: the assert's panic-path
// formula stayed ungrounded, `generate_full_assert_refutation_vcs` emitted no
// claim, and the obligation demoted to runtime-checked (then failed `-full`).
// With the derived trivial-setter summary the call's effect is total and exact
// (`a == v` on the success edge), so the panic path must now GROUND and PROVE
// UNSAT — the REAL in-process solver is the oracle here, exactly like the
// guarded_mut_slice_len_tie_proves twin.
use trust_router::{InProcessAyBackend, VerificationBackend};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
    VerificationResult,
};

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

/// `fn set(p: &mut u32, v: u32) { *p = v; }` — the fixture callee.
fn setter_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "set".into(),
        def_path: "fixture::set".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(u32_ty()) },
                    name: Some("p".into()),
                },
                LocalDecl { index: 2, ty: u32_ty(), name: Some("v".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place { local: 1, projections: vec![Projection::Deref] },
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The `bump` mutant shape (`*p = <computed>` — downward_reseat_after_use /
/// converging_lo_reseat): a compute statement before the store. The recognizer
/// MUST reject it (two value writes; non-parameter source).
fn computed_setter_fn() -> VerifiableFunction {
    let mut f = setter_fn();
    f.body.locals.push(LocalDecl { index: 3, ty: u32_ty(), name: Some("_3".into()) });
    f.body.blocks[0].stmts = vec![
        Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Int(100)),
            ),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place { local: 1, projections: vec![Projection::Deref] },
            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
            span: SourceSpan::default(),
        },
    ];
    f
}

/// The fixture caller, parameterized on the local the assert compares `a`
/// against: `compare_local = 2` (`v`) is the always-true fixture assert;
/// `compare_local = 1` (`x`) asserts the STALE pre-call value — genuinely
/// refutable (any `v != x` panics).
///
/// bb0: `a = x; _5 = &mut a; set(move _5, copy v)` -> bb1
/// bb1: `_6 = copy a; _7 = Eq(move _6, copy <cmp>)` switch -> bb2 (0) / bb3
/// bb2: `core::panicking::panic("assertion failed")` (diverges)
/// bb3: `_0 = copy a; return`
fn caller_fn(compare_local: usize) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "fixture::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: u32_ty(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: u32_ty(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: u32_ty(), name: Some("v".into()) },
                LocalDecl { index: 3, ty: u32_ty(), name: Some("a".into()) },
                LocalDecl { index: 4, ty: Ty::Unit, name: Some("_4".into()) },
                LocalDecl {
                    index: 5,
                    ty: Ty::Ref { mutable: true, inner: Box::new(u32_ty()) },
                    name: Some("_5".into()),
                },
                LocalDecl { index: 6, ty: u32_ty(), name: Some("_6".into()) },
                LocalDecl { index: 7, ty: Ty::Bool, name: Some("_7".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(3) },
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Call {
                        func: "fixture::set".into(),
                        args: vec![Operand::Move(Place::local(5)), Operand::Copy(Place::local(2))],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        unwind: UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Move(Place::local(6)),
                                Operand::Copy(Place::local(compare_local)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(7)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "core::panicking::panic".into(),
                        args: vec![Operand::Constant(ConstValue::Str {
                            bytes: b"assertion failed".to_vec(),
                        })],
                        dest: Place::local(4),
                        target: None,
                        unwind: UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: u32_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Refute-lane claims for `caller` with the given callee corpus attached to
/// this invocation's explicit summary context.
fn refutation_claims(
    callees: &[VerifiableFunction],
    caller: &VerifiableFunction,
) -> Vec<trust_types::VerificationCondition> {
    let summaries = trust_vcgen::compute_trivial_setter_summaries(callees);
    let context = trust_vcgen::VcgenContext::for_function(caller.def_path.clone())
        .with_callee_summaries(
            trust_vcgen::CalleeSummaryContext::default().with_setter_summaries(summaries),
        );
    trust_vcgen::generate_full_assert_refutation_vcs_with_context(caller, &context)
}

#[test]
fn trivial_setter_assert_panic_path_proves_unsat_in_process() {
    // The fixture assert (`a == v` after `set(&mut a, v)`): the panic path must
    // GROUND (setter fact `a#s0_t == v` + copy-chain link `_6 == a#s0_t`) and
    // the real solver must prove it UNSAT — the base lane's "1 proved".
    let vcs = refutation_claims(&[setter_fn()], &caller_fn(2));
    assert_eq!(
        vcs.len(),
        1,
        "the setter fixture's assert panic path must ground into exactly one \
         refutation-lane claim; got {vcs:?}"
    );
    let backend = InProcessAyBackend::new();
    let result = backend.verify(&vcs[0]);
    assert!(
        matches!(&result, VerificationResult::Proved { .. }),
        "`assert!(a == v)` after `set(&mut a, v)` holds for ALL inputs — the \
         panic-path formula must be UNSAT (Proved), got {result:?}\nformula: {:?}",
        vcs[0].formula
    );
}

#[test]
fn trivial_setter_stale_assert_still_refutes() {
    // SOUNDNESS twin: `assert!(a == x)` after `set(&mut a, v)` asserts the
    // STALE pre-call value — genuinely violated by any `v != x`. The setter
    // fact must GROUND this panic path too and the solver must find the real
    // counterexample (Failed), never a false proof.
    let vcs = refutation_claims(&[setter_fn()], &caller_fn(1));
    assert_eq!(
        vcs.len(),
        1,
        "the stale-compare assert must ground into exactly one claim; got {vcs:?}"
    );
    let backend = InProcessAyBackend::new();
    let result = backend.verify(&vcs[0]);
    assert!(
        matches!(&result, VerificationResult::Failed { .. }),
        "`assert!(a == x)` after `set(&mut a, v)` is violated by any `v != x` — \
         the panic-path formula must be SAT (Failed / real counterexample), got \
         {result:?}\nformula: {:?}",
        vcs[0].formula
    );
}

#[test]
fn computed_setter_emits_no_refutation_claim() {
    // FAIL-CLOSED twin (the `bump` mutant shape): a callee whose store is a
    // COMPUTED value earns NO summary, so the caller's assert panic path stays
    // ungrounded — no claim in either direction (the obligation remains
    // runtime-checked, exactly the pre-existing behavior).
    let vcs = refutation_claims(&[computed_setter_fn()], &caller_fn(2));
    assert!(
        vcs.is_empty(),
        "an unrecognized (computed-store) setter must leave the assert \
         ungrounded — no refutation-lane claim; got {vcs:?}"
    );
}
