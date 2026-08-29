// Trust (2026-08-20, bare-BinaryOp wrapping): the modular-wrap value model for
// a BARE `Rvalue::BinaryOp(Add|Sub, ..)` statement — the form the MIR inliner
// leaves behind at -O when it dissolves core's `wrapping_add`/`wrapping_sub`
// CALL, and the form ALL user `+`/`-` arithmetic takes in an
// overflow-checks-OFF session.
//
// MIR reality (the discriminator these tests pin): rustc defines the plain
// integer `BinOp::Add`/`Sub`/`Mul` as WRAPPING — overflow checking is a
// DIFFERENT op (`*WithOverflow`, a (value, flag) pair consumed by an `Assert`
// terminator), and UB-on-overflow arithmetic is a third (`*Unchecked`). The
// extractor preserves all three forms distinctly
// (`trust-mir-extract/src/convert.rs::convert_supported_binop`: Plain ->
// `Rvalue::BinaryOp` "defined wrapping", Checked -> `Rvalue::CheckedBinaryOp`,
// Unchecked -> `Rvalue::UncheckedBinaryOp`). So no session overflow-checks bit
// is needed: a bare `Rvalue::BinaryOp` IS the wrapping case by construction,
// under either overflow-checks setting.
//
// THE BUG THESE TESTS PIN CLOSED (a false PROVE, not just a havoc):
// `extract_block_definitions` used to model the bare form with
// `chc::try_binop_to_formula`, i.e. the UNBOUNDED mathematical
// `dest == a + b`. That equation is FALSE of every execution that actually
// wraps, and the `-full` assert-refutation lane conjoins it into the
// panic-path feasibility formula, where an ay UNSAT verdict is consumed as
// PROVED (`rustc_mir_transform::trust_verify::refute_full_assert_obligations`).
// Concretely, for the checks-off body of
//
//     if b == 1 { assert!(a + b >= a); }      // panics at a == u64::MAX
//
// the violation formula `b == 1 && s < a && s == a + b` is UNSAT over
// unbounded integers, so the lane PROVED an assert that real execution
// refutes at `a == u64::MAX` (the wrap witness `s == 0 < a` does not satisfy
// `s == a + b`, so the only real counterexample family was excluded from the
// model set). Measured on this exact fixture before the fix:
// `wrapping_add_ge_lhs_false_prove_control` failed with the wrap witness
// EXCLUDED — that exclusion is the false-prove mechanism.
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VerifiableBody,
    VerifiableFunction,
};

use super::{
    generate_full_assert_refutation_vcs, guards, wrapping_binop_modular_ite,
    wrapping_call_assert_model,
};

// ---------------------------------------------------------------------------
// A tiny total evaluator for the formula fragment these fixtures emit. Used to
// check FEASIBILITY facts machine-checkably without a solver: a formula that a
// real execution's values FALSIFY has excluded that execution from its model
// set (the false-prove mechanism); one they SATISFY keeps the real
// counterexample representable (the honest encoding).
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq)]
enum Val {
    I(i128),
    B(bool),
}

fn eval(f: &Formula, env: &dyn Fn(&str) -> Option<Val>) -> Option<Val> {
    let int = |f: &Formula| match eval(f, env)? {
        Val::I(v) => Some(v),
        Val::B(_) => None,
    };
    let boolean = |f: &Formula| match eval(f, env)? {
        Val::B(v) => Some(v),
        Val::I(_) => None,
    };
    Some(match f {
        Formula::Bool(b) => Val::B(*b),
        Formula::Int(v) => Val::I(*v),
        Formula::UInt(v) => Val::I(i128::try_from(*v).ok()?),
        Formula::Var(name, _) => {
            let base = name.split('#').next().unwrap_or(name);
            env(base)?
        }
        Formula::Add(a, b) => Val::I(int(a)?.checked_add(int(b)?)?),
        Formula::Sub(a, b) => Val::I(int(a)?.checked_sub(int(b)?)?),
        Formula::Mul(a, b) => Val::I(int(a)?.checked_mul(int(b)?)?),
        Formula::Neg(a) => Val::I(int(a)?.checked_neg()?),
        Formula::Eq(a, b) => match (eval(a, env)?, eval(b, env)?) {
            (Val::I(x), Val::I(y)) => Val::B(x == y),
            (Val::B(x), Val::B(y)) => Val::B(x == y),
            _ => return None,
        },
        Formula::Lt(a, b) => Val::B(int(a)? < int(b)?),
        Formula::Le(a, b) => Val::B(int(a)? <= int(b)?),
        Formula::Gt(a, b) => Val::B(int(a)? > int(b)?),
        Formula::Ge(a, b) => Val::B(int(a)? >= int(b)?),
        Formula::Not(a) => Val::B(!boolean(a)?),
        Formula::And(cs) => {
            let mut acc = true;
            for c in cs {
                acc &= boolean(c)?;
            }
            Val::B(acc)
        }
        Formula::Or(cs) => {
            let mut acc = false;
            for c in cs {
                acc |= boolean(c)?;
            }
            Val::B(acc)
        }
        Formula::Ite(c, t, e) => {
            if boolean(c)? {
                eval(t, env)?
            } else {
                eval(e, env)?
            }
        }
        _ => return None,
    })
}

fn u64_local(index: usize, name: &str) -> LocalDecl {
    LocalDecl { index, ty: Ty::u64(), name: Some(name.into()) }
}

fn bool_local(index: usize, name: &str) -> LocalDecl {
    LocalDecl { index, ty: Ty::Bool, name: Some(name.into()) }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn switch(discr: usize, zero_to: BlockId, otherwise: BlockId) -> Terminator {
    Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(discr)),
        targets: vec![(0, zero_to)],
        otherwise,
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    }
}

fn panic_call() -> Terminator {
    Terminator::Call {
        func: "core::panicking::panic".into(),
        args: vec![Operand::Constant(ConstValue::Str {
            bytes: b"assertion failed: s >= a".to_vec(),
        })],
        dest: Place::local(0),
        target: None,
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        is_foreign: false,
        callee_identity: None,
        unwind: UnwindEdge::Terminate,
    }
}

/// The overflow-checks-OFF MIR of
/// `fn f(a: u64, b: u64) { if b == 1 { assert!(a + b >= a); } }`:
/// the `+` is a BARE `Rvalue::BinaryOp(Add)` (wrapping by MIR definition) —
/// no CheckedBinaryOp, no overflow Assert terminator. The assert genuinely
/// panics at `a == u64::MAX, b == 1`, where the sum wraps to 0.
fn checks_off_add_ge_lhs_fn(op: BinOp) -> VerifiableFunction {
    VerifiableFunction {
        name: "checks_off_add_ge_lhs".to_string(),
        def_path: "test::checks_off_add_ge_lhs".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                u64_local(1, "a"),
                u64_local(2, "b"),
                u64_local(3, "s"),
                bool_local(4, "ge"),
                bool_local(5, "bsel"),
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(5),
                        Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            // The audited spelling of `b == 1u64`: trust-mir-extract
                            // lowers an UNSIGNED literal to width-carrying
                            // `ConstValue::Uint`, and the admission audit
                            // (`validate_binary_assignment_types`) rejects a
                            // widthless signed `Int` against a u64 comparison
                            // input — a widthless literal cannot authenticate an
                            // unsigned carrier.
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ),
                    )],
                    terminator: switch(5, BlockId(4), BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        assign(
                            Place::local(3),
                            Rvalue::BinaryOp(
                                op,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                        ),
                        assign(
                            Place::local(4),
                            Rvalue::BinaryOp(
                                BinOp::Ge,
                                Operand::Copy(Place::local(3)),
                                Operand::Copy(Place::local(1)),
                            ),
                        ),
                    ],
                    terminator: switch(4, BlockId(2), BlockId(3)),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: panic_call() },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// (c) THE FALSE-PROVE CONTROL. `assert!(a + b >= a)` in a checks-off body
/// wraps at `a == u64::MAX, b == 1` and panics, so the panic-path feasibility
/// formula MUST be satisfiable — and in particular must be SATISFIED by the
/// real wrap witness `{a: u64::MAX, b: 1, s: 0}`.
///
/// BEFORE the fix this failed: the lane conjoined the unbounded
/// `s == a + b`, the witness evaluated the formula to FALSE (the only real
/// counterexample family excluded), and over unbounded integers
/// `b == 1 && s == a + b && s < a` is UNSAT — which
/// `refute_full_assert_obligations` consumes as PROVED. A false PROVE of a
/// panicking assert, at exactly the shapes -O / checks-off sessions emit.
#[test]
fn wrapping_add_ge_lhs_false_prove_control() {
    let func = checks_off_add_ge_lhs_fn(BinOp::Add);
    let vcs = generate_full_assert_refutation_vcs(&func);
    assert!(
        !vcs.is_empty(),
        "the checks-off wrapping assert must still ground (the modular def replaces \
         the unbounded one; dropping the def entirely would silently lose the lane)"
    );
    let max = u64::MAX as i128;
    let witness = |name: &str| -> Option<Val> {
        match name {
            "a" => Some(Val::I(max)),
            "b" => Some(Val::I(1)),
            "s" => Some(Val::I(0)),
            "ge" => Some(Val::B(false)),
            "bsel" => Some(Val::B(true)),
            "ret" => Some(Val::I(0)),
            _ => None,
        }
    };
    let satisfied = vcs.iter().any(|vc| eval(&vc.formula, &witness) == Some(Val::B(true)));
    assert!(
        satisfied,
        "the REAL wrap witness (a=u64::MAX, b=1, s=0) must satisfy some emitted \
         panic-path formula; excluding it is the false-PROVE mechanism (the pre-fix \
         unbounded `s == a + b` encoding did exactly that): {vcs:#?}"
    );
    // And no emitted formula may carry the unbounded equation itself: a formula
    // in which the witness values satisfy every conjunct EXCEPT an
    // `s == a + b` (unbounded) def is the wrong-encoding signature.
    let unbounded_witness = |name: &str| -> Option<Val> {
        match name {
            "s" => Some(Val::I(max + 1)), // the unbounded sum, representable only off-machine
            other => witness(other),
        }
    };
    assert!(
        !vcs.iter().any(|vc| eval(&vc.formula, &unbounded_witness) == Some(Val::B(true))),
        "no emitted formula may model the checks-off sum as the unbounded a + b \
         (s = 2^64 must not be a feasible destination value): {vcs:#?}"
    );
}

/// (a) ENCODING PARITY: the bare-BinaryOp statement def must be THE SAME
/// modular-Ite the marker-authenticated call form mints — one shared
/// constructor (`wrapping_binop_modular_ite`), compared here output-for-output
/// on identical operands/destination so the two spellings can never drift.
#[test]
fn bare_binop_def_equals_call_form_encoding() {
    for (op, tail) in [(BinOp::Add, "wrapping_add"), (BinOp::Sub, "wrapping_sub")] {
        // Call form: `_0 = u64::wrapping_op(_1, _2)` via the authenticated marker.
        let call_func = VerifiableFunction {
            name: "wrap_call".into(),
            def_path: "test::wrap_call".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u64(), name: Some("d".into()) },
                    u64_local(1, "a"),
                    u64_local(2, "b"),
                ],
                blocks: Vec::new(),
                arg_count: 2,
                return_ty: Ty::u64(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let marker = format!("@trust-rustc-total-primitive-method::core::num::<impl u64>::{tail}");
        let args = vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))];
        let (call_def, call_ranges) = wrapping_call_assert_model(
            &call_func,
            &marker,
            &args,
            &Place::local(0),
            true,
            false,
            false,
            false,
        )
        .expect("the authenticated call form must model");

        // Statement form: `d = BinaryOp(op, a, b)` in a block.
        let stmt_func = VerifiableFunction {
            body: VerifiableBody {
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::BinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                    )],
                    terminator: Terminator::Return,
                }],
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                    u64_local(1, "a"),
                    u64_local(2, "b"),
                    u64_local(3, "d"),
                ],
                arg_count: 2,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            ..checks_off_add_ge_lhs_fn(op)
        };
        let defs = guards::extract_block_definitions(&stmt_func, &stmt_func.body.blocks[0]);
        let stmt_def = defs
            .iter()
            .find(|d| matches!(d, Formula::Eq(l, _) if l.var_name() == Some("d")))
            .unwrap_or_else(|| panic!("the bare {op:?} statement must produce a def: {defs:?}"));
        // Same dest var name ("d"), same operand formulas ("a"/"b") — the two
        // encodings must be BYTE-IDENTICAL formulas.
        assert_eq!(
            stmt_def, &call_def,
            "bare-BinaryOp {op:?} def and the call-form encoding must be the same formula"
        );
        // The operand type-range tautologies must ride along too (they are what
        // keeps the refute direction from choosing an out-of-range operand).
        for range in &call_ranges {
            assert!(
                defs.contains(range),
                "the bare form must carry the call form's operand range fact {range:?}: {defs:?}"
            );
        }
    }
}

/// The shared constructor is signedness-complete for Add/Sub: the signed arm is
/// the same two-sided two's-complement wrap the call form used, so a bare
/// signed `Sub` def is exact as well (a checks-off `i32` subtraction wraps).
#[test]
fn signed_bare_sub_def_is_the_two_sided_wrap() {
    let ite = wrapping_binop_modular_ite(
        BinOp::Sub,
        &Formula::var("x", Sort::Int),
        &Formula::var("y", Sort::Int),
        32,
        true,
    )
    .expect("signed sub at width 32 is encodable");
    // Exactness probe at the wrap boundary: i32::MIN - 1 wraps to i32::MAX.
    let env = |name: &str| -> Option<Val> {
        match name {
            "x" => Some(Val::I(i32::MIN as i128)),
            "y" => Some(Val::I(1)),
            _ => None,
        }
    };
    assert_eq!(
        eval(&ite, &env),
        Some(Val::I(i32::MAX as i128)),
        "signed wrap-around must be exact: i32::MIN - 1 == i32::MAX"
    );
}

/// (d) MUL STAYS REFUSED, exactly as it is for the call form: no modular
/// encoding exists in this Int/LIA lane (a single Ite is WRONG for mul, which
/// can wrap more than once), and the old unbounded `Formula::Mul` def was the
/// same false-prove vector. The def must be DROPPED — and with it the assert
/// stays ungrounded in the refute lane (fail-closed: no verdict, never a
/// wrong one).
#[test]
fn bare_mul_def_stays_refused() {
    assert!(
        wrapping_binop_modular_ite(
            BinOp::Mul,
            &Formula::var("x", Sort::Int),
            &Formula::var("y", Sort::Int),
            64,
            false,
        )
        .is_none(),
        "Mul has no single-Ite modular reduction; the shared constructor must refuse it"
    );
    let func = checks_off_add_ge_lhs_fn(BinOp::Mul);
    let defs = guards::extract_block_definitions(&func, &func.body.blocks[1]);
    assert!(
        !defs.iter().any(|d| matches!(d, Formula::Eq(l, _) if l.var_name() == Some("s"))),
        "a bare Mul must emit NO value def (neither unbounded nor a wrong Ite): {defs:?}"
    );
    assert!(
        generate_full_assert_refutation_vcs(&func).is_empty(),
        "an assertion whose fail condition depends on the refused Mul result must be declined \
         in full; emitting a weakened guard-only SAT query would be a false-refutation channel"
    );
}

/// u128/i128 (width > 64) stay refused like the call form — the i128-domain
/// modulus does not fit the Int carrier.
#[test]
fn width_128_bare_add_def_stays_refused() {
    assert!(
        wrapping_binop_modular_ite(
            BinOp::Add,
            &Formula::var("x", Sort::Int),
            &Formula::var("y", Sort::Int),
            128,
            false,
        )
        .is_none()
    );
    let mut func = checks_off_add_ge_lhs_fn(BinOp::Add);
    for local in &mut func.body.locals {
        if matches!(local.ty, Ty::Int { .. }) {
            local.ty = Ty::Int { width: 128, signed: false };
        }
    }
    let defs = guards::extract_block_definitions(&func, &func.body.blocks[1]);
    assert!(
        !defs.iter().any(|d| matches!(d, Formula::Eq(l, _) if l.var_name() == Some("s"))),
        "u128 add must emit NO value def: {defs:?}"
    );
}

/// The INTERVAL lane's sibling of the same bug (`abstract_interp::transfer`):
/// for a bare (wrapping) binop, the mathematical interval is exact only when
/// it fits the destination type entirely; otherwise the machine value can
/// wrap anywhere in the type's range. Before the fix, `a ∈ [0,3] ⇒
/// a - 1 ∈ [-1,2]` EXCLUDED the wrapped `u64::MAX` at `a == 0`, and
/// `try_discharge_batch` — a DEFAULT-mode discharge authority — could prove a
/// bounds VC the runtime violates.
#[test]
fn interval_lane_bare_binop_wrap_window_widens_to_type_range() {
    use crate::abstract_interp::{AbstractDomain, Interval, IntervalDomain, transfer_function};
    let func = checks_off_add_ge_lhs_fn(BinOp::Sub);
    let mut state = IntervalDomain::top();
    state.set("a".to_string(), Interval::new(0, 3));
    state.set("b".to_string(), Interval::new(1, 1));
    // `s = Sub(a, b)` with a ∈ [0,3], b == 1: a == 0 wraps to u64::MAX.
    let stmt = assign(
        Place::local(3),
        Rvalue::BinaryOp(
            BinOp::Sub,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
    );
    let out = transfer_function(&stmt, &func, &state);
    let s = out.get("s");
    assert!(
        s.contains(u64::MAX as i128),
        "the wrap window [-1,2] must widen to the full u64 range (the real wrapped \
         value u64::MAX was excluded before the fix): got [{}, {}]",
        s.lo,
        s.hi
    );
    // Precision retained where no wrap is possible: a + b with a ∈ [0,3],
    // b == 1 fits u64 entirely, so the exact math interval survives.
    let add = assign(
        Place::local(3),
        Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
    );
    let out = transfer_function(&add, &func, &state);
    let s = out.get("s");
    assert_eq!((s.lo, s.hi), (1, 4), "a no-wrap-possible interval must stay exact");
}

/// (b) THE OVERFLOW-CHECKS-ON SHAPE IS UNTOUCHED. With checks on, user `a + b`
/// arrives as `CheckedBinaryOp` + overflow `Assert`:
///   * `extract_block_definitions` must keep SKIPPING the CheckedBinaryOp
///     statement entirely (its success-path value equation is edge-sensitive
///     and owned by the path-definition map / semantic guards);
///   * `extract_overflow_flag_semantics` must keep emitting exactly the flag
///     equation plus the two operand ranges — never a value equation for `.0`.
#[test]
fn checks_on_checked_shape_is_untouched() {
    let func = VerifiableFunction {
        name: "checked_add".into(),
        def_path: "test::checked_add".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                u64_local(1, "a"),
                u64_local(2, "b"),
                LocalDecl {
                    index: 3,
                    ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
                    name: Some("t".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                    )],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let defs = guards::extract_block_definitions(&func, &func.body.blocks[0]);
    assert!(
        !defs.iter().any(|d| d.free_variables().iter().any(|v| v.starts_with("t."))),
        "CheckedBinaryOp must stay SKIPPED by statement definition extraction: {defs:?}"
    );
    let ofs = guards::extract_overflow_flag_semantics(&func, &func.body.blocks[0]);
    assert!(
        ofs.iter().any(|d| matches!(d, Formula::Eq(l, _) if l.var_name() == Some("t.1"))),
        "the overflow-flag equation must still be emitted: {ofs:?}"
    );
    assert!(
        !ofs.iter().any(|d| matches!(d, Formula::Eq(l, _) if l.var_name() == Some("t.0"))),
        "no unconditional value equation for the checked result may appear: {ofs:?}"
    );
}
