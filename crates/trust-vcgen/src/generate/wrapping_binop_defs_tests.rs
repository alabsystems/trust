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
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, CounterexampleValue, Formula, LocalDecl,
    Operand, Place, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VcKind,
    VerifiableBody, VerifiableFunction, VerificationCondition, VerificationResult,
};

use super::ite::eliminate_term_ites;
use super::{
    ITE_ELIM_CASE_CAP, generate_full_assert_refutation_vcs, generate_v2_contract_vcs_impl, guards,
    wrapping_binop_modular_ite, wrapping_call_assert_model,
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
        Formula::Implies(a, b) => Val::B(!boolean(a)? || boolean(b)?),
        // The chc return pin's and the bitwise def's bridge (`BvToInt(IntToBv(a) op
        // IntToBv(b))`): a bit-vector is its unsigned pattern in `[0, 2^w)`; widths up
        // to 64 only, so every modulus fits the i128 carrier.
        Formula::BitVec { value, width } if *width <= 64 => {
            Val::I(value.rem_euclid(1i128 << *width))
        }
        Formula::IntToBv(a, w) if *w <= 64 => Val::I(int(a)?.rem_euclid(1i128 << *w)),
        Formula::BvAdd(a, b, w) if *w <= 64 => {
            Val::I(int(a)?.checked_add(int(b)?)?.rem_euclid(1i128 << *w))
        }
        Formula::BvSub(a, b, w) if *w <= 64 => {
            Val::I(int(a)?.checked_sub(int(b)?)?.rem_euclid(1i128 << *w))
        }
        Formula::BvXor(a, b, w) if *w <= 64 => Val::I(int(a)? ^ int(b)?),
        Formula::BvToInt(a, w, signed) if *w <= 64 => {
            let pattern = int(a)?;
            if *signed && pattern >= 1i128 << (*w - 1) {
                Val::I(pattern - (1i128 << *w))
            } else {
                Val::I(pattern)
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
        callee_key: crate::sep_engine::tests::fixture_key("core::panicking::panic"),
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
        tuple_layouts: Default::default(),
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
            tuple_layouts: Default::default(),
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
        tuple_layouts: Default::default(),
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

// ---------------------------------------------------------------------------
// BARE-BINOP-LITERAL-LHS-WIDTH-1: a width-less literal LEFT operand
// ---------------------------------------------------------------------------
//
// Trust (2026-10-13): the def above took its `(width, signed)` from the LEFT
// operand's type. `operand_ty` of a width-less `ConstValue::Int` is derived from
// its VALUE (i64 for `1`), so the checks-off `fn inc1(x: i32) -> i32 ensures
// result > x { 1 + x }` — real MIR `_0 = Add(const Int(1), copy _1)` — was
// modelled as wrapping at 2^64 with i64 operand ranges. The i32 wrap at
// `x == i32::MAX` was not representable, so the postcondition PROVED under
// `-Ztrust-policy=memory-safe -Coverflow-checks=off` (and advisory) while the
// binary returns `i32::MIN`. The `x + 1` twin read the place's type and was
// refuted. The width now comes from the DESTINATION, with both operands checked
// against it (`guards::bare_binop_machine_shape`).

/// The real MIR of `fn f(x: T) -> T ensures <clause> { <lhs> OP <rhs> }` with
/// overflow checks off: one block, `_0 = OP(lhs, rhs); return`, and the argument
/// type range as the extractor's precondition (as `-Ztrust-dump-mir` emits it for
/// `scout26/vacuouscert/witness/a_literal_lhs_wrap_family.rs`).
fn literal_op_fn(
    ty: Ty,
    op: BinOp,
    lhs: Operand,
    rhs: Operand,
    postconditions: Vec<Formula>,
) -> VerifiableFunction {
    let (width, signed) = match ty {
        Ty::Int { width, signed } => (width, signed),
        Ty::PtrSizedInt { signed } => (64, signed),
        _ => unreachable!("literal_op_fn takes a machine integer"),
    };
    VerifiableFunction {
        name: "literal_op".into(),
        def_path: "test::literal_op".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(Place::local(0), Rvalue::BinaryOp(op, lhs, rhs))],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![crate::range::input_range_constraint(&x_var(), width, signed)],
        postconditions,
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn x_var() -> Formula {
    Formula::var("x", Sort::Int)
}

fn ret_var() -> Formula {
    Formula::var("_0", Sort::Int)
}

fn x_place() -> Operand {
    Operand::Copy(Place::local(1))
}

fn lit(value: i128) -> Operand {
    Operand::Constant(ConstValue::Int(value))
}

fn ret_def(func: &VerifiableFunction) -> Option<Formula> {
    let defs = guards::extract_block_definitions(func, &func.body.blocks[0]);
    defs.iter().find_map(|d| match d {
        Formula::Eq(l, r) if l.var_name() == Some("_0") => Some(r.as_ref().clone()),
        _ => None,
    })
}

/// `1 + x` (i32), `-2147483647 - x` (i32), `100 + x` (i8) and `0 - x` (i32): the def
/// is the shared constructor's wrap at the DESTINATION width, the operand ranges ride
/// along at that width, and the machine's wrapped value is what the def evaluates to.
#[test]
fn literal_lhs_bare_binop_def_is_at_the_destination_width() {
    for (ty, op, k, width, x, machine) in [
        (Ty::i32(), BinOp::Add, 1i128, 32u32, i128::from(i32::MAX), i128::from(i32::MIN)),
        (Ty::i32(), BinOp::Sub, -2_147_483_647, 32, 2, i128::from(i32::MAX)),
        (Ty::i8(), BinOp::Add, 100, 8, 100, -56),
        (Ty::i32(), BinOp::Sub, 0, 32, i128::from(i32::MIN), i128::from(i32::MIN)),
        // the pointer-width spelling reads the pinned 64 bits, as `Ty::int_width` does
        (
            Ty::PtrSizedInt { signed: true },
            BinOp::Add,
            1,
            64,
            i128::from(i64::MAX),
            i128::from(i64::MIN),
        ),
    ] {
        let f = literal_op_fn(ty.clone(), op, lit(k), x_place(), vec![]);
        let defs = guards::extract_block_definitions(&f, &f.body.blocks[0]);
        let def = ret_def(&f).unwrap_or_else(|| panic!("{ty:?} {op:?}: no def for _0: {defs:?}"));
        let expected = wrapping_binop_modular_ite(op, &Formula::Int(k), &x_var(), width, true)
            .expect("encodable");
        assert_eq!(def, expected, "{ty:?} {k} {op:?} x: the wrap must be at width {width}");
        for operand in [Formula::Int(k), x_var()] {
            assert!(
                defs.contains(&crate::range::input_range_constraint(&operand, width, true)),
                "{ty:?}: the operand range of {operand:?} must be stated at width {width}: {defs:?}"
            );
            assert!(
                !defs.contains(&crate::range::input_range_constraint(&operand, 64, true))
                    || width == 64,
                "{ty:?}: no i64 operand range may be stated for a {width}-bit op: {defs:?}"
            );
        }
        let env = move |name: &str| (name == "x").then_some(Val::I(x));
        assert_eq!(
            eval(&def, &env),
            Some(Val::I(machine)),
            "{ty:?}: {k} {op:?} {x} must evaluate to the machine's {machine}: {def:?}"
        );
    }
}

/// The place-first twin `x + 1` is the shape the old width read got right: its def is
/// unchanged (the constructor at the place's width, operands in program order), and
/// it agrees with the literal-first `1 + x` at every edge point of the domain.
#[test]
fn place_lhs_twin_def_is_unchanged_and_agrees_with_the_literal_lhs_def() {
    let twin = literal_op_fn(Ty::i32(), BinOp::Add, x_place(), lit(1), vec![]);
    let twin_def = ret_def(&twin).expect("the x + 1 twin must keep its def");
    assert_eq!(
        twin_def,
        wrapping_binop_modular_ite(BinOp::Add, &x_var(), &Formula::Int(1), 32, true).unwrap(),
        "the `x + 1` def is the constructor's at the place's width, byte for byte"
    );
    let literal = literal_op_fn(Ty::i32(), BinOp::Add, lit(1), x_place(), vec![]);
    let literal_def = ret_def(&literal).expect("the 1 + x def");
    for x in [i128::from(i32::MIN), -1, 0, 1, i128::from(i32::MAX) - 1, i128::from(i32::MAX)] {
        let env = move |name: &str| (name == "x").then_some(Val::I(x));
        assert_eq!(eval(&literal_def, &env), eval(&twin_def, &env), "1 + x vs x + 1 at x = {x}");
    }
}

/// Shape disagreement models NOTHING (fail-closed: an exact-value def at a wrong width
/// is wrong in both directions; the write stays visible through
/// `generate::extend_with_assigned_place_dests`).
#[test]
fn literal_lhs_bare_binop_with_a_disagreeing_operand_emits_no_def() {
    let mut place_mismatch = literal_op_fn(Ty::i32(), BinOp::Add, lit(1), x_place(), vec![]);
    place_mismatch.body.locals[1].ty = Ty::i64();
    assert!(ret_def(&place_mismatch).is_none(), "an i64 place into an i32 add: no def");

    let too_wide = literal_op_fn(Ty::i32(), BinOp::Add, lit(1i128 << 40), x_place(), vec![]);
    assert!(ret_def(&too_wide).is_none(), "a literal outside i32: no def");

    let unsigned_lit_signed_dest = literal_op_fn(
        Ty::i32(),
        BinOp::Add,
        Operand::Constant(ConstValue::Uint(1, 32)),
        x_place(),
        vec![],
    );
    assert!(ret_def(&unsigned_lit_signed_dest).is_none(), "an unsigned literal in a signed add");

    let wrong_uint_width = literal_op_fn(
        Ty::u32(),
        BinOp::Add,
        Operand::Constant(ConstValue::Uint(1, 64)),
        x_place(),
        vec![],
    );
    assert!(ret_def(&wrong_uint_width).is_none(), "a u64 literal in a u32 add: no def");

    let signed_lit_unsigned_dest = literal_op_fn(Ty::u32(), BinOp::Add, lit(1), x_place(), vec![]);
    assert!(ret_def(&signed_lit_unsigned_dest).is_none(), "a width-less signed literal, u32 add");

    // The agreeing unsigned and pointer-width spellings keep their defs.
    let unsigned = literal_op_fn(
        Ty::u8(),
        BinOp::Add,
        Operand::Constant(ConstValue::Uint(200, 8)),
        x_place(),
        vec![],
    );
    assert_eq!(
        ret_def(&unsigned),
        wrapping_binop_modular_ite(
            BinOp::Add,
            &crate::operand_to_formula(&unsigned, &Operand::Constant(ConstValue::Uint(200, 8))),
            &x_var(),
            8,
            false
        ),
        "`200u8 + x` keeps its u8 def"
    );
    let mut usize_mixed = literal_op_fn(
        Ty::PtrSizedInt { signed: false },
        BinOp::Sub,
        Operand::Constant(ConstValue::Uint(1, 64)),
        x_place(),
        vec![],
    );
    usize_mixed.body.locals[1].ty = Ty::usize();
    assert!(
        ret_def(&usize_mixed).is_some(),
        "a PtrSizedInt destination and a legacy `u64`-spelled usize place share a machine shape"
    );
}

/// `1 + x` on `i128` has no modular encoding (`wrapping_binop_modular_ite` stops at 64
/// bits), so it gets NO def. The left-operand read gave it the `i64` def of the literal,
/// with an `i64` range constraint on the `i128` operand `x`: a hypothesis FALSE of every
/// `x` outside `i64`.
#[test]
fn literal_lhs_i128_add_gets_no_narrower_def() {
    let f = literal_op_fn(Ty::i128(), BinOp::Add, lit(1), x_place(), vec![]);
    let defs = guards::extract_block_definitions(&f, &f.body.blocks[0]);
    assert!(ret_def(&f).is_none(), "an i128 wrap has no encoding here: {defs:?}");
    assert!(
        !defs.contains(&crate::range::input_range_constraint(&x_var(), 64, true)),
        "no i64 range may be stated for the i128 operand: {defs:?}"
    );
}

/// A literal LEFT operand of a BITWISE op is untouched: `-1 ^ x` (i8) keeps the i64
/// bridge it always had, and that is exact, because two's-complement XOR commutes with
/// sign extension (the i64 pattern of `-1 ^ x` sign-extends the i8 `!x`).
#[test]
fn literal_lhs_bitwise_def_is_exact_at_the_value_width() {
    let f = literal_op_fn(Ty::i8(), BinOp::BitXor, lit(-1), x_place(), vec![]);
    let def = ret_def(&f).expect("`-1 ^ x` keeps its bitwise def");
    for x in [-128i128, -1, 0, 1, 127] {
        let env = move |name: &str| (name == "x").then_some(Val::I(x));
        assert_eq!(eval(&def, &env), Some(Val::I(-x - 1)), "-1 ^ {x} == !{x}: {def:?}");
    }
}

/// The Machine{w} postcondition lane recognizes the def BY CONSTRUCTION at the
/// declared width; the width-64 def of `1 + x` on `i32` was not the constructor's
/// output at 32 and fell outside the fragment.
#[test]
fn machine_lane_reads_the_literal_lhs_def_as_bv_add() {
    let f = literal_op_fn(Ty::i32(), BinOp::Add, lit(1), x_place(), vec![]);
    let def = Formula::Eq(Box::new(ret_var()), Box::new(ret_def(&f).expect("def")));
    let translated = crate::contracts::machine_faithful_vc_formula(&f, &def)
        .expect("the destination-width def must stay inside the declared-width fragment");
    assert!(
        matches!(&translated, Formula::Eq(_, rhs) if matches!(rhs.as_ref(), Formula::BvAdd(_, _, 32))),
        "the `1 + x` def reads as a 32-bit `bvadd`: {translated:?}"
    );
}

/// The contract lane's postcondition rows, with the production pipeline's general
/// term-`Ite` elimination applied (`entry.rs` runs it on every aggregated row).
fn postcondition_rows(f: &VerifiableFunction) -> Vec<VerificationCondition> {
    let rows: Vec<_> = generate_v2_contract_vcs_impl(f, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .map(|mut vc| {
            vc.formula = eliminate_term_ites(&vc.formula, ITE_ELIM_CASE_CAP);
            vc
        })
        .collect();
    assert!(!rows.is_empty(), "the clause must raise postcondition rows");
    rows
}

/// The row with every top-level conjunct that mentions the bit-vector bridge (the chc
/// return pin) replaced by `true` — `bare_neg_wrap_tests`' rule: in-process ay answers
/// the mixed Int+bridge row `unknown`, so the row is decided in pure LIA on what the
/// BLOCK DEFINITION says. Dropping a hypothesis only weakens the row (an UNSAT survives
/// to the full row), and a SAT is checked against the full row with the real witness.
fn without_bv_pins(f: &Formula) -> Formula {
    match f {
        Formula::And(conjuncts) => Formula::And(conjuncts.iter().map(without_bv_pins).collect()),
        leaf => {
            let rendered = format!("{leaf:?}");
            if rendered.contains("BvToInt") || rendered.contains("IntToBv") {
                Formula::Bool(true)
            } else {
                leaf.clone()
            }
        }
    }
}

fn lia_verdicts(f: &VerifiableFunction) -> Vec<(VerificationResult, String)> {
    use trust_router::{InProcessAyBackend, VerificationBackend};
    let backend = InProcessAyBackend::new();
    postcondition_rows(f)
        .into_iter()
        .map(|mut vc| {
            vc.formula = without_bv_pins(&vc.formula);
            assert!(backend.can_handle(&vc), "in-process ay must take the row: {:?}", vc.formula);
            (backend.verify(&vc), format!("{:?}", vc.formula))
        })
        .collect()
}

fn gt(a: Formula, b: Formula) -> Formula {
    Formula::Gt(Box::new(a), Box::new(b))
}

fn lt(a: Formula, b: Formula) -> Formula {
    Formula::Lt(Box::new(a), Box::new(b))
}

fn le(a: Formula, b: Formula) -> Formula {
    Formula::Le(Box::new(a), Box::new(b))
}

fn ge(a: Formula, b: Formula) -> Formula {
    Formula::Ge(Box::new(a), Box::new(b))
}

/// THE FALSE-PROVE CONTROL (fails before the fix). Each liar's clause is false of the
/// binary built with `-Coverflow-checks=off` (`scout26/vacuouscert/confirm`):
/// `inc1(i32::MAX) == i32::MIN`, `h_lie(100) == -56`, `s_lie(2) == i32::MAX`,
/// `neg0(i32::MIN) == i32::MIN`. So
///   * the real execution must SATISFY a full postcondition row (return pin included)
///     — before the fix no row admitted it: the def said `_0 == k OP x` without the
///     wrap while the pin said the wrapped value;
///   * on what the block definition says, in-process ay must REFUTE a row — before the
///     fix it PROVED every one.
#[test]
fn literal_lhs_checks_off_postcondition_is_refuted_by_ay() {
    let max32 = i128::from(i32::MAX);
    let min32 = i128::from(i32::MIN);
    for (name, ty, op, k, clause, x, machine) in [
        ("inc1", Ty::i32(), BinOp::Add, 1i128, gt(ret_var(), x_var()), max32, min32),
        (
            "h_lie",
            Ty::i8(),
            BinOp::Add,
            100,
            Formula::Or(vec![le(x_var(), Formula::Int(27)), gt(ret_var(), Formula::Int(0))]),
            100,
            -56,
        ),
        (
            "s_lie",
            Ty::i32(),
            BinOp::Sub,
            -2_147_483_647,
            Formula::Or(vec![le(x_var(), Formula::Int(0)), lt(ret_var(), Formula::Int(0))]),
            2,
            max32,
        ),
        (
            "neg0",
            Ty::i32(),
            BinOp::Sub,
            0,
            Formula::Or(vec![ge(x_var(), Formula::Int(0)), gt(ret_var(), Formula::Int(0))]),
            min32,
            min32,
        ),
    ] {
        let f = literal_op_fn(ty, op, lit(k), x_place(), vec![clause.clone()]);
        let witness = move |var: &str| match var {
            "x" => Some(Val::I(x)),
            "_0" => Some(Val::I(machine)),
            _ => None,
        };
        let rows = postcondition_rows(&f);
        assert!(
            rows.iter().any(|vc| eval(&vc.formula, &witness) == Some(Val::B(true))),
            "{name}: the real execution x = {x}, result = {machine} must satisfy a full row of \
             `{clause:?}` (excluding it is the false-PROVE mechanism): {rows:#?}"
        );
        let verdicts = lia_verdicts(&f);
        assert!(
            verdicts.iter().any(|(r, _)| matches!(r, VerificationResult::Failed { .. })),
            "{name}: `{clause:?}` is false of the wrapping op and must be refuted, got \
             {verdicts:#?}"
        );
        if name == "inc1" {
            // `1 + x > x` fails ONLY where `1 + x` wraps: the model is x == i32::MAX.
            for (result, _) in &verdicts {
                if let VerificationResult::Failed { counterexample: Some(cex), .. } = result
                    && let Some((_, value)) = cex.assignments.iter().find(|(n, _)| n == "x")
                {
                    assert!(
                        matches!(value, CounterexampleValue::Int(v) if *v == max32)
                            || matches!(value, CounterexampleValue::Uint(v) if *v == max32 as u128),
                        "inc1: the only refuting model is x == i32::MAX, got {value:?}"
                    );
                }
            }
        }
    }
}

/// THE TRUE TWINS (also fail before the fix: the i64-width def refuted them, the
/// over-refusal side of the same wrong width). `x <= 27 || result < 0` for `100 + x`
/// on `i8` and `x < 2147483647 || result < x` for `1 + x` on `i32` hold of the
/// wrapping op, and prove from the block definition alone.
#[test]
fn literal_lhs_checks_off_true_wrap_claims_prove() {
    for (name, ty, k, clause) in [
        (
            "h_true",
            Ty::i8(),
            100i128,
            Formula::Or(vec![le(x_var(), Formula::Int(27)), lt(ret_var(), Formula::Int(0))]),
        ),
        (
            "inc1_true",
            Ty::i32(),
            1,
            Formula::Or(vec![lt(x_var(), Formula::Int(2_147_483_647)), lt(ret_var(), x_var())]),
        ),
    ] {
        let f = literal_op_fn(ty, BinOp::Add, lit(k), x_place(), vec![clause.clone()]);
        let verdicts = lia_verdicts(&f);
        assert!(
            verdicts.iter().all(|(r, _)| r.is_proved()),
            "{name}: `{clause:?}` holds of the wrapping add: {verdicts:#?}"
        );
    }
}
