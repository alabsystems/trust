use trust_types::UnwindEdge;
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, UnOp, VcKind, VerifiableBody,
    VerifiableFunction,
};

use super::{generate_v2_safety_vcs, v2_build_overflow_vc_for_operands};

fn assign(dest: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(dest), rvalue, span: SourceSpan::default() }
}

// --- self-contained SIGNED BITVECTOR witness evaluator (refutability oracle) ---
//
// Signed 128-bit add/sub/neg overflow VCs are now emitted in pure QF_BV (the native
// typed-CHC LIA lane cannot represent ±2^127). The oracle below
// (`eval_bv` / `eval_bv_bool`) computes the EXACT two's-complement semantics of those
// formulas over a concrete witness, so a test can REFUTE the obligation (a real
// overflow makes the violation TRUE → SAT) or confirm a guarded case is UNSAT (the
// violation is FALSE for every witness in the small, structurally-constrained free
// space). It NEVER trusts the solver — it is a ground oracle. An unmodeled node
// panics, so an unexpected formula shape fails loudly rather than passing silently.

// ---- self-contained BITVECTOR witness evaluator (sound refutability oracle) ----
//
// Signed 128-bit add/sub/neg overflow VCs are now emitted in pure QF_BV (the native
// typed-CHC LIA lane cannot represent ±2^127). This evaluator computes the EXACT
// two's-complement semantics of those formulas over a concrete bit assignment
// (`(value_as_low_w_bits, width)`), so a test can:
//   * REFUTE the obligation by exhibiting a witness that makes the violation TRUE
//     (a real overflow is SAT → refutable, never vacuously proved); and
//   * confirm a guarded/safe case is UNSAT by checking the violation is FALSE for
//     EVERY witness in the (small, structurally-constrained) free-variable space.
// It NEVER trusts the solver — it is a ground oracle. A node we don't model panics
// (so an unexpected formula shape is caught, never silently mis-evaluated).
//
// BV values are carried as `u128` bit patterns masked to `width` bits.
fn bv_mask(width: u32) -> u128 {
    if width >= 128 { u128::MAX } else { (1u128 << width) - 1 }
}

// A bitvector value of width up to 129 bits: `lo` is the low 128 bits, `bit128`
// is the 129th bit (only set for width == 129). This is enough for the
// sign-extend-by-1 add/sub overflow check (`w+1` = 129 at the most).
#[derive(Clone, Copy, Debug)]
struct Bv {
    lo: u128,
    bit128: bool,
    width: u32,
}

impl Bv {
    fn new(lo: u128, bit128: bool, width: u32) -> Self {
        Bv { lo: lo & bv_mask(width.min(128)), bit128: bit128 && width >= 129, width }
    }
    // The bit at position `i` (0-based).
    fn bit(self, i: u32) -> bool {
        if i >= 128 { self.bit128 } else { (self.lo >> i) & 1 == 1 }
    }
}

// Evaluate a BV-sorted formula node. `env` maps a variable name to its raw
// low-128-bit pattern (operands are <= 128-bit).
fn eval_bv(f: &Formula, env: &dyn Fn(&str) -> u128) -> Bv {
    match f {
        Formula::BitVec { value, width } => Bv::new(*value as u128, false, *width),
        Formula::Var(name, trust_types::Sort::BitVec(w)) => {
            Bv::new(env(name.as_str()), false, *w)
        }
        Formula::BvAdd(a, b, w) => {
            let va = eval_bv(a, env);
            let vb = eval_bv(b, env);
            // 129-bit-capable add: track carry into bit 128.
            let (sum, carry) = va.lo.overflowing_add(vb.lo);
            let bit128 = (va.bit128 ^ vb.bit128) ^ carry;
            Bv::new(sum, bit128, *w)
        }
        Formula::BvSub(a, b, w) => {
            let va = eval_bv(a, env);
            let vb = eval_bv(b, env);
            let (diff, borrow) = va.lo.overflowing_sub(vb.lo);
            let bit128 = (va.bit128 ^ vb.bit128) ^ borrow;
            Bv::new(diff, bit128, *w)
        }
        Formula::BvShl(a, b, w) => {
            let va = eval_bv(a, env);
            let vb = eval_bv(b, env);
            // SMT bvshl: shift by >= width yields 0. `vb.lo >= 128` also avoids
            // the u128 `<<` overflow (shift amount must be < 128 to be in range).
            let shifted =
                if vb.lo >= u128::from(*w) || vb.lo >= 128 { 0 } else { va.lo << vb.lo };
            Bv::new(shifted, false, *w)
        }
        Formula::BvSignExt(a, extra) => {
            let va = eval_bv(a, env);
            let new_w = va.width + extra;
            let sign = va.bit(va.width - 1);
            // Sign-extend into the new high bits. The widest case here is 128->129,
            // where the extension bit becomes bit 128.
            let bit128 = if new_w >= 129 { sign } else { false };
            // For new_w <= 128, set the high bits [wa..new_w) to `sign`.
            let lo = if sign && new_w <= 128 {
                let high = bv_mask(new_w) ^ bv_mask(va.width);
                va.lo | high
            } else {
                va.lo
            };
            Bv::new(lo, bit128, new_w)
        }
        Formula::BvExtract { inner, high, low } => {
            let vi = eval_bv(inner, env);
            let w = high - low + 1;
            // Reconstruct the slice bit-by-bit (handles the bit-128 boundary).
            let mut out: u128 = 0;
            for i in 0..w {
                if vi.bit(low + i) {
                    out |= 1u128 << i;
                }
            }
            Bv::new(out, false, w)
        }
        other => panic!("eval_bv: unhandled BV node {other:?}"),
    }
}

// Signed value of a (<=128-bit) two's-complement BV.
fn bv_signed(v: Bv) -> i128 {
    let width = v.width;
    let sign = v.bit(width - 1);
    if sign {
        if width >= 128 { v.lo as i128 } else { (v.lo as i128) - ((1i128) << width) }
    } else {
        v.lo as i128
    }
}

// Is this formula node BV-sorted (a BV leaf or BV operator)?
fn is_bv_node(f: &Formula) -> bool {
    matches!(
        f,
        Formula::BitVec { .. }
            | Formula::Var(_, trust_types::Sort::BitVec(_))
            | Formula::BvAdd(..)
            | Formula::BvSub(..)
            | Formula::BvShl(..)
            | Formula::BvSignExt(..)
            | Formula::BvExtract { .. }
    )
}

// Is this formula node Bool-sorted (a bool leaf or a boolean connective /
// comparison)? Used to decide whether an `Eq` is a boolean or integer equality.
fn is_bool_node(f: &Formula) -> bool {
    matches!(
        f,
        Formula::Bool(_)
            | Formula::Var(_, trust_types::Sort::Bool)
            | Formula::And(_)
            | Formula::Or(_)
            | Formula::Not(_)
            | Formula::Lt(..)
            | Formula::Le(..)
            | Formula::Gt(..)
            | Formula::Ge(..)
            | Formula::Eq(..)
            | Formula::BvULt(..)
            | Formula::BvULe(..)
            | Formula::BvSLt(..)
            | Formula::BvSLe(..)
    )
}

// Evaluate a boolean formula whose leaves may be BV-sorted OR small-Int/Bool
// (the assert-driven neg path wraps the BV core in the shift guard's
// `Eq(_c, Lt(n, 128))` Int/Bool block-defs — the native lane handles BOTH the
// BV part and the small-constant LIA part; this oracle does too). `env` returns
// a value usable as both a BV bit pattern and (when small) a signed integer.
fn eval_bv_bool(f: &Formula, env: &dyn Fn(&str) -> u128) -> bool {
    // A signed-int interpretation of a variable (the low 64 bits, as the test
    // only feeds small shift amounts / guard constants through the Int part).
    let int_of = |name: &str| -> i128 { env(name) as i128 };
    match f {
        Formula::Bool(b) => *b,
        Formula::Var(name, trust_types::Sort::Bool) => env(name.as_str()) != 0,
        Formula::And(cs) => cs.iter().all(|c| eval_bv_bool(c, env)),
        Formula::Or(cs) => cs.iter().any(|c| eval_bv_bool(c, env)),
        Formula::Not(c) => !eval_bv_bool(c, env),
        Formula::Eq(a, b) => {
            if is_bv_node(a) || is_bv_node(b) {
                let va = eval_bv(a, env);
                let vb = eval_bv(b, env);
                va.lo == vb.lo && va.bit128 == vb.bit128
            } else if is_bool_node(a) || is_bool_node(b) {
                // Boolean equality (e.g. `Eq(_2, Le(width, 127))` — the cond
                // block-def): both sides evaluate to bools.
                eval_bv_bool(a, env) == eval_bv_bool(b, env)
            } else {
                eval_int_leaf(a, &int_of) == eval_int_leaf(b, &int_of)
            }
        }
        Formula::BvULt(a, b, _) => eval_bv(a, env).lo < eval_bv(b, env).lo,
        Formula::BvULe(a, b, _) => eval_bv(a, env).lo <= eval_bv(b, env).lo,
        Formula::BvSLt(a, b, _) => bv_signed(eval_bv(a, env)) < bv_signed(eval_bv(b, env)),
        Formula::BvSLe(a, b, _) => bv_signed(eval_bv(a, env)) <= bv_signed(eval_bv(b, env)),
        // Small-Int/LIA comparisons from the conjoined guard block-defs.
        Formula::Lt(a, b) => eval_int_leaf(a, &int_of) < eval_int_leaf(b, &int_of),
        Formula::Le(a, b) => eval_int_leaf(a, &int_of) <= eval_int_leaf(b, &int_of),
        Formula::Gt(a, b) => eval_int_leaf(a, &int_of) > eval_int_leaf(b, &int_of),
        Formula::Ge(a, b) => eval_int_leaf(a, &int_of) >= eval_int_leaf(b, &int_of),
        other => panic!("eval_bv_bool: unhandled node {other:?}"),
    }
}

// Evaluate a small Int-sorted leaf (var / constant / add / sub) used in the
// conjoined guard block-defs. Only the shapes those defs produce are handled.
fn eval_int_leaf(f: &Formula, env: &dyn Fn(&str) -> i128) -> i128 {
    match f {
        Formula::Int(n) => *n,
        Formula::UInt(n) => *n as i128,
        Formula::Var(name, _) => env(name.as_str()),
        Formula::Add(a, b) => eval_int_leaf(a, env) + eval_int_leaf(b, env),
        Formula::Sub(a, b) => eval_int_leaf(a, env) - eval_int_leaf(b, env),
        Formula::Neg(a) => -eval_int_leaf(a, env),
        other => panic!("eval_int_leaf: unhandled node {other:?}"),
    }
}

/// `fn f(a: i128, b: i128) -> i128 { a - b }`: `_3 = SubWithOverflow(a, b)`,
/// `Assert(!_3.1, Overflow(Sub))`. The block-level builder is called directly on
/// the operands (mirroring how the SubWithOverflow rvalue path drives it).
fn i128_sub_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "f".to_string(),
        def_path: "test::f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i128(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::i128(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i128(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::i128(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        3,
                        Rvalue::CheckedBinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                    )],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place {
                            local: 3,
                            projections: vec![Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        0,
                        Rvalue::Use(Operand::Copy(Place {
                            local: 3,
                            projections: vec![Projection::Field(0)],
                        })),
                    )],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::i128(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// EXHAUSTIVE w=8 cross-check: the sign-bit overflow predicate
/// (`signed_bv_addsub_overflow_sign_test`, the pure-QF_BV form that REPLACED the
/// `w+1`-bit sign-extension/extract form the native lane could not prove) must
/// agree with REAL two's-complement `i8` add/sub overflow on EVERY `(a, b)` pair.
/// This pins exactness (no false-PROVE: it never reports "safe" when a real
/// overflow exists; no false-FAIL: it never reports "overflow" on a safe op).
#[test]
fn signed_bv_addsub_overflow_sign_test_matches_real_i8() {
    use super::signed_bv_addsub_overflow_sign_test;
    let env = |_: &str| 0u128;
    for op in [BinOp::Add, BinOp::Sub] {
        for a in -128i32..=127 {
            for b in -128i32..=127 {
                let (a8, b8) = (a as i8, b as i8);
                let real = match op {
                    BinOp::Add => a8.checked_add(b8).is_none(),
                    BinOp::Sub => a8.checked_sub(b8).is_none(),
                    _ => unreachable!(),
                };
                let f = signed_bv_addsub_overflow_sign_test(
                    Formula::BitVec { value: a8 as i128, width: 8 },
                    Formula::BitVec { value: b8 as i128, width: 8 },
                    op,
                    8,
                );
                assert_eq!(
                    eval_bv_bool(&f, &env),
                    real,
                    "w=8 {op:?}: a={a8} b={b8} (formula vs real i8 overflow)"
                );
            }
        }
    }
}

/// w=128 spot checks of the sign-bit overflow predicate: the exact i128
/// boundaries, incl. `signed_max`'s guarded `(1<<126) - 1` (safe) and the
/// adversarial overflows that MUST stay refutable.
#[test]
fn signed_bv_addsub_overflow_sign_test_w128_boundaries() {
    use super::signed_bv_addsub_overflow_sign_test;
    let env = |_: &str| 0u128;
    let bv = |v: i128| Formula::BitVec { value: v, width: 128 };
    let ov = |a: i128, b: i128, op: BinOp| {
        eval_bv_bool(&signed_bv_addsub_overflow_sign_test(bv(a), bv(b), op, 128), &env)
    };
    // Safe (signed_max's `_5 - 1` with `_5 = 1<<126`, and ordinary values).
    assert!(!ov(1i128 << 126, 1, BinOp::Sub), "(1<<126) - 1 must NOT overflow");
    assert!(!ov(5, 3, BinOp::Sub), "5 - 3 must NOT overflow");
    assert!(!ov(i128::MIN, i128::MIN, BinOp::Sub), "MIN - MIN = 0 must NOT overflow");
    assert!(!ov(i128::MAX, i128::MAX, BinOp::Sub), "MAX - MAX = 0 must NOT overflow");
    // Real overflows (the adversarial guardrail: MUST be refutable / SAT).
    assert!(ov(i128::MIN, 1, BinOp::Sub), "MIN - 1 MUST overflow");
    assert!(ov(i128::MAX, -1, BinOp::Sub), "MAX - (-1) MUST overflow");
    assert!(ov(i128::MAX, 1, BinOp::Add), "MAX + 1 MUST overflow");
    assert!(ov(i128::MIN, -1, BinOp::Add), "MIN + (-1) MUST overflow");
}

/// The signed 128-bit SUB overflow obligation is now MODELED (not UNKNOWN),
/// and is the exact overflow predicate.
#[test]
fn i128_sub_overflow_is_modeled_not_unsupported() {
    let func = i128_sub_fn();
    let block = &func.body.blocks[0];
    let vc = v2_build_overflow_vc_for_operands(
        &func,
        block,
        BinOp::Sub,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
        &SourceSpan::default(),
        None,
    )
    .expect("i128 sub must emit a VC");
    assert!(
        matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }),
        "i128 sub overflow must be a real ArithmeticOverflow obligation, not UNKNOWN; got {:?}",
        vc.kind
    );

    // The signed-128 path emits the BV `w+1`-bit sign-extension overflow check;
    // operands are bare locals → fresh BV vars `__trust_ovf_bv_{role}_{base}`.
    let a_bv =
        format!("__trust_ovf_bv_lhs_{}", crate::place_to_var_name(&func, &Place::local(1)));
    let b_bv =
        format!("__trust_ovf_bv_rhs_{}", crate::place_to_var_name(&func, &Place::local(2)));

    // ADVERSARIAL: `i128::MAX - (-1)` is a genuine overflow (true result =
    // i128::MAX + 1 > i128::MAX). The violation formula MUST be satisfiable here,
    // i.e. the solver can still refute it — never a vacuous PROVE.
    let overflow_env = |name: &str| -> u128 {
        if name == a_bv {
            i128::MAX as u128
        } else if name == b_bv {
            (-1i128) as u128 // 0xFFFF...F
        } else {
            0
        }
    };
    assert!(
        eval_bv_bool(&vc.formula, &overflow_env),
        "REAL i128 overflow (i128::MAX - (-1)) must satisfy the violation formula \
         (refutable), never be vacuously proved; formula: {:?}",
        vc.formula
    );

    // SAFE: `5 - 3 = 2` is in range — the violation formula must be UNSAT for it,
    // confirming the predicate is not trivially true (which would false-FAIL safe code).
    let safe_env = |name: &str| -> u128 {
        if name == a_bv {
            5
        } else if name == b_bv {
            3
        } else {
            0
        }
    };
    assert!(
        !eval_bv_bool(&vc.formula, &safe_env),
        "SAFE i128 sub (5 - 3) must NOT satisfy the violation formula; formula: {:?}",
        vc.formula
    );
}

/// `fn g(x: i128) -> i128 { -x }`: `_2 = Neg(x)` raw rvalue → NegationOverflow VC.
fn i128_neg_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "g".to_string(),
        def_path: "test::g".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i128(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::i128(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i128(), name: Some("n".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(2, Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1)))),
                    assign(0, Rvalue::Use(Operand::Copy(Place::local(2)))),
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i128(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// i128 negation overflow (`-x` overflows iff `x == i128::MIN`) is MODELED and
/// is the exact predicate: refutable on `x = i128::MIN`, unsatisfiable on any
/// other input.
#[test]
fn i128_negation_overflow_is_modeled_and_exact() {
    let func = i128_neg_fn();
    let vcs = generate_v2_safety_vcs(&func);
    let neg = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
        .expect("i128 `-x` must emit a NegationOverflow obligation, not UNKNOWN");
    assert!(
        !matches!(neg.kind, VcKind::UnsupportedMir { .. }),
        "negation overflow must not be UnsupportedMir"
    );

    // The signed-128 neg path emits the BV failure `x == INT_MIN`; the operand is
    // a bare local → fresh BV var `__trust_ovf_bv_neg_{base}`.
    let x_bv =
        format!("__trust_ovf_bv_neg_{}", crate::place_to_var_name(&func, &Place::local(1)));

    // ADVERSARIAL: `-(i128::MIN)` genuinely overflows. The violation formula
    // (`x == i128::MIN`) must be SAT (refutable).
    let overflow_env =
        |name: &str| -> u128 { if name == x_bv { i128::MIN as u128 } else { 0 } };
    assert!(
        eval_bv_bool(&neg.formula, &overflow_env),
        "REAL i128 negation overflow (-(i128::MIN)) must satisfy the violation \
         formula (refutable); formula: {:?}",
        neg.formula
    );

    // SAFE: any non-MIN value (e.g. i128::MIN + 1, or 0) must NOT satisfy it.
    for safe in [0i128, i128::MIN + 1, i128::MAX, -1] {
        let safe_env = |name: &str| -> u128 { if name == x_bv { safe as u128 } else { 0 } };
        assert!(
            !eval_bv_bool(&neg.formula, &safe_env),
            "SAFE i128 negation (x = {safe}) must NOT satisfy the violation formula; \
             formula: {:?}",
            neg.formula
        );
    }
}

/// GUARDRAIL: signed 128-bit MUL stays fail-closed (UnsupportedMir / UNKNOWN) —
/// it is nonlinear (NIA) and the BV path declines width > 64, so modeling it on
/// the Int path would risk a NIA hang or an unsound encoding. The narrowed guard
/// must keep mul UNKNOWN even though add/sub are now modeled.
#[test]
fn i128_signed_mul_stays_unsupported() {
    let func = VerifiableFunction {
        name: "m".to_string(),
        def_path: "test::m".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i128(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::i128(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i128(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    0,
                    Rvalue::CheckedBinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                )],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i128(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let block = &func.body.blocks[0];
    let vc = v2_build_overflow_vc_for_operands(
        &func,
        block,
        BinOp::Mul,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
        &SourceSpan::default(),
        Some(0),
    )
    .expect("mul must emit a VC");
    assert!(
        matches!(vc.kind, VcKind::UnsupportedMir { .. }),
        "signed 128-bit mul must stay UNKNOWN (UnsupportedMir); got {:?}",
        vc.kind
    );
}

/// Cross-check that the unsigned 128-bit ADD path (which was never gated) is also
/// refutable on a real overflow, so the narrowing did not perturb it.
#[test]
fn u128_add_overflow_still_refutable() {
    // Sanity on the SIGNED add direction too: `i128::MAX + 1` overflows above MAX.
    let func = VerifiableFunction {
        name: "p".to_string(),
        def_path: "test::p".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i128(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::i128(), name: Some("a".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    0,
                    Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(1)),
                    ),
                )],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i128(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let block = &func.body.blocks[0];
    let vc = v2_build_overflow_vc_for_operands(
        &func,
        block,
        BinOp::Add,
        &Operand::Copy(Place::local(1)),
        &Operand::Constant(ConstValue::Int(1)),
        &SourceSpan::default(),
        Some(0),
    )
    .expect("i128 add must emit a VC");
    assert!(
        matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }),
        "i128 add must be modeled; got {:?}",
        vc.kind
    );
    // lhs `a` is a bare local → BV var `__trust_ovf_bv_lhs_a`; rhs is the
    // constant `1` (a `BitVec` literal, no var). `i128::MAX + 1` overflows.
    let a_bv =
        format!("__trust_ovf_bv_lhs_{}", crate::place_to_var_name(&func, &Place::local(1)));
    let env = |name: &str| -> u128 { if name == a_bv { i128::MAX as u128 } else { 0 } };
    assert!(
        eval_bv_bool(&vc.formula, &env),
        "REAL i128 add overflow (i128::MAX + 1) must satisfy the violation formula; \
         formula: {:?}",
        vc.formula
    );
}

// ===========================================================================
// signed_max / signed_min PROVE guardrails (the task's target obligations)
//
// signed_max's trailing `_5 - 1` (where `_5 = 1i128 << _6`, `_6 < 128`) is
// provably non-underflowing ONLY because the shift block-def + the dominating
// `_6 < 128` guard pin `_5` to a power of two in `[1, 2^127]`. The BV VC must:
//   (a) be UNSAT over the constrained witness space (`_6 in [0,127]`) — PROVE; and
//   (b) ADVERSARIALLY, with the SAME free var UNconstrained, stay refutable for a
//       real underflow witness (`_5 = i128::MIN`), so the encoding never vacuously
//       proves. We verify (b) on the UNGUARDED `fn f(x:i128)->i128{x-1}` below.
// ===========================================================================

/// The `signed_max` BB5/BB6 shape, self-contained:
///   bb0: _2 = (n < 128); assert(_2, Shl) -> bb1            // shift-amount guard
///   bb1: _5 = Shl(1i128, n); _9 = CheckedSub(_5, 1); assert(!_9.1, Sub) -> bb2
///   bb2: _0 = _9.0; return
/// (`n` plays the role of `_6 = width - 1`, already `< 128`.) The Sub overflow VC
/// for `_5 - 1` must carry the BV shift block-def + the `n < 128` bound.
fn signed_max_sub_fixture() -> VerifiableFunction {
    // Faithful two-step shape (mirrors the real `signed_max` MIR):
    //   bb0: _2 = (width <= 127); assert(_2) -> bb1            // SEMANTIC guard
    //   bb1: _6 = width - 1; _5 = Shl(1i128, _6);              // `_6 <= 126`
    //        _9 = CheckedSub(_5, 1); assert(!_9.1, Sub) -> bb2
    //   bb2: _0 = _9.0; return
    // The Sub VC for `_5 - 1` must thread `width <= 127` through `_6 = width - 1`
    // to derive `_6 <= 126`, so `_5 = 2^_6 <= 2^126` and `_5 - 1` never underflows.
    VerifiableFunction {
        name: "signed_max_sub".to_string(),
        def_path: "test::signed_max_sub".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("width".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
                LocalDecl { index: 5, ty: Ty::i128(), name: Some("_5".into()) },
                LocalDecl { index: 6, ty: Ty::u32(), name: Some("_6".into()) },
                LocalDecl {
                    index: 9,
                    ty: Ty::Tuple(vec![Ty::i128(), Ty::Bool]),
                    name: Some("_9".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        2,
                        Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(127, 32)),
                        ),
                    )],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::local(2)),
                        expected: true,
                        msg: AssertMessage::Overflow(BinOp::Shl),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        assign(
                            6,
                            Rvalue::BinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                        ),
                        assign(
                            5,
                            Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Constant(ConstValue::Int(1)),
                                Operand::Move(Place::local(6)),
                            ),
                        ),
                        assign(
                            9,
                            Rvalue::CheckedBinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(5)),
                                Operand::Constant(ConstValue::Int(1)),
                            ),
                        ),
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place {
                            local: 9,
                            projections: vec![Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        0,
                        Rvalue::Use(Operand::Copy(Place {
                            local: 9,
                            projections: vec![Projection::Field(0)],
                        })),
                    )],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i128(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// signed_max's `_5 - 1` (guarded shift block-def `_5 = 1 << _6` + threaded
/// `width <= 127` → `_6 <= 126`) yields a BV Sub overflow VC that is UNSAT
/// (PROVABLE) over the whole free-variable space.
#[test]
fn signed_max_sub_is_provable_unsat() {
    let func = signed_max_sub_fixture();
    // Build the Sub VC for `_5 - 1` (statement index 2 in block 1: `_6 = width-1`
    // at idx 0, `_5 = 1 << _6` at idx 1 — both taken BEFORE the subtraction).
    let block = &func.body.blocks[1];
    let vc = v2_build_overflow_vc_for_operands(
        &func,
        block,
        BinOp::Sub,
        &Operand::Copy(Place::local(5)),
        &Operand::Constant(ConstValue::Int(1)),
        &SourceSpan::default(),
        Some(2),
    )
    .expect("signed_max `_5 - 1` must emit a VC");
    assert!(
        matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }),
        "must be a real ArithmeticOverflow obligation; got {:?}",
        vc.kind
    );

    // The BV core carries `_5 == bvshl(1, _6) ∧ _6 < 127` (the derived bound) ∧ the
    // overflow check. We EXHAUSTIVELY sweep the shift amount `_6` in [0, 200] (incl.
    // out-of-bound values the `_6 < 127` BV guard must filter), binding ALL views —
    // Int `width`/`_6`, Bool `_2`, BV `amt`/`_5` — to a CONSISTENT witness. For every
    // witness the violation must be FALSE → UNSAT → PROVED (no underflow feasible).
    let amt_bv = "__trust_ovf_bv_amt__6";
    let _5_bv = "__trust_ovf_bv_lhs__5";
    for amt in 0u128..=200 {
        let _5_val: u128 = if amt >= 128 { 0 } else { 1u128 << amt };
        // width = amt + 1 (so `_6 = width - 1 = amt`); the guard `width <= 127` holds
        // iff amt <= 126. `_2 = (width <= 127)`.
        let width_val = amt + 1;
        let bool_true = u128::from(width_val <= 127);
        let env = |name: &str| -> u128 {
            if name == amt_bv {
                amt
            } else if name == _5_bv {
                _5_val
            } else if name == "_6" {
                amt
            } else if name == "width" {
                width_val
            } else if name == "_2" {
                bool_true
            } else {
                0
            }
        };
        assert!(
            !eval_bv_bool(&vc.formula, &env),
            "signed_max `_5 - 1` must be UNSAT (PROVED) for _6={amt} (_5={_5_val}); \
             a SAT witness here would be a false-FAIL. formula: {:?}",
            vc.formula
        );
    }

    // SANITY: the shift block-def really constrains `_5` — an INCONSISTENT witness (a
    // `_5` that is NOT `1 << _6`, e.g. `_5 = i128::MIN` with _6=5) must fail the
    // block-def equality → formula FALSE. Proves the UNSAT is REAL, not a dropped def.
    let inconsistent = |name: &str| -> u128 {
        match name {
            "__trust_ovf_bv_amt__6" | "_6" => 5,
            "__trust_ovf_bv_lhs__5" => i128::MIN as u128,
            "width" => 6,
            "_2" => 1,
            _ => 0,
        }
    };
    assert!(
        !eval_bv_bool(&vc.formula, &inconsistent),
        "inconsistent (_5 != 1<<_6) witness must fail the block-def equality \
         (formula FALSE), confirming the def constrains _5; formula: {:?}",
        vc.formula
    );
}

/// ADVERSARIAL guardrail: an UNGUARDED `fn f(x: i128) -> i128 { x - 1 }` (free `x`,
/// no block-def, no guard) yields a BV Sub overflow VC that is SAT/refutable — a
/// real underflow (`x = i128::MIN`) must still be refuted, NEVER vacuously proved.
#[test]
fn unguarded_i128_sub_one_stays_refutable() {
    let func = VerifiableFunction {
        name: "f".to_string(),
        def_path: "test::f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::i128(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i128(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let block = &func.body.blocks[0];
    let vc = v2_build_overflow_vc_for_operands(
        &func,
        block,
        BinOp::Sub,
        &Operand::Copy(Place::local(1)),
        &Operand::Constant(ConstValue::Int(1)),
        &SourceSpan::default(),
        Some(0),
    )
    .expect("unguarded i128 sub must emit a VC");
    // x = i128::MIN: `i128::MIN - 1` underflows. Must be SAT (refutable).
    let x_bv = "__trust_ovf_bv_lhs_x";
    let underflow = |name: &str| -> u128 { if name == x_bv { i128::MIN as u128 } else { 0 } };
    assert!(
        eval_bv_bool(&vc.formula, &underflow),
        "UNGUARDED `x - 1` with x = i128::MIN MUST be refutable (SAT), never \
         vacuously proved; formula: {:?}",
        vc.formula
    );
    // x = 0: `0 - 1` is in range — UNSAT (must not false-FAIL).
    let safe = |name: &str| -> u128 { if name == x_bv { 0 } else { 0 } };
    assert!(
        !eval_bv_bool(&vc.formula, &safe),
        "SAFE `0 - 1` must NOT satisfy the violation; formula: {:?}",
        vc.formula
    );
}

/// CRITICAL adversarial guardrail: a shift block-def WITHOUT a dominating bound
/// (`_5 = 1i128 << n`, `n` UNGUARDED, then `_5 - 1`) must STAY refutable. The shift
/// def alone pins `_5` to a power of two — but with `n = 127`, `_5 = 2^127 =
/// i128::MIN` (a NEGATIVE i128), so `_5 - 1` UNDERFLOWS. Emitting the shift def
/// without the `n < 127` bound must NOT vacuously prove: the violation must be SAT
/// at `n = 127`. (This proves the bound, not the def, is what discharges signed_max.)
#[test]
fn shift_def_without_bound_stays_refutable() {
    // bb0: _5 = Shl(1i128, n); _9 = CheckedSub(_5, 1); assert -> bb1 ; n is FREE.
    let func = VerifiableFunction {
        name: "h".to_string(),
        def_path: "test::h".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 5, ty: Ty::i128(), name: Some("_5".into()) },
                LocalDecl {
                    index: 9,
                    ty: Ty::Tuple(vec![Ty::i128(), Ty::Bool]),
                    name: Some("_9".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    5,
                    Rvalue::BinaryOp(
                        BinOp::Shl,
                        Operand::Constant(ConstValue::Int(1)),
                        Operand::Copy(Place::local(1)),
                    ),
                )],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i128(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let block = &func.body.blocks[0];
    // Build the `_5 - 1` Sub VC at stmt index 1 (after the `_5 = Shl` def at 0).
    let vc = v2_build_overflow_vc_for_operands(
        &func,
        block,
        BinOp::Sub,
        &Operand::Copy(Place::local(5)),
        &Operand::Constant(ConstValue::Int(1)),
        &SourceSpan::default(),
        Some(1),
    )
    .expect("`_5 - 1` must emit a VC");
    // Witness: n = 127 → _5 = 2^127 (= i128::MIN bit pattern). `_5 - 1` underflows.
    // The formula carries the shift def `_5 == bvshl(1, amt)` but NO `amt < 127`
    // bound (n is unguarded), so this witness MUST satisfy the violation (SAT).
    let amt_bv = "__trust_ovf_bv_amt_n";
    let _5_bv = "__trust_ovf_bv_lhs__5";
    let witness = |name: &str| -> u128 {
        match name {
            n if n == amt_bv => 127,
            n if n == _5_bv => 1u128 << 127, // = i128::MIN bit pattern
            "n" => 127,
            _ => 0,
        }
    };
    assert!(
        eval_bv_bool(&vc.formula, &witness),
        "UNGUARDED shift (`1 << n`, n=127) `_5 - 1` MUST be refutable (SAT) — a real \
         i128::MIN - 1 underflow must never be vacuously proved; formula: {:?}",
        vc.formula
    );
}

/// ADVERSARIAL guardrail: `i128::MAX - (-1)` (a real positive-overflow) on the
/// UNGUARDED two-operand sub must stay refutable (already covered by
/// `i128_sub_overflow_is_modeled_not_unsupported`, repeated here for the symmetric
/// `i128::MAX + 1` add direction with the BV oracle).
#[test]
fn unguarded_i128_max_plus_one_stays_refutable() {
    let func = VerifiableFunction {
        name: "p".to_string(),
        def_path: "test::p".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::i128(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i128(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i128(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let block = &func.body.blocks[0];
    let vc = v2_build_overflow_vc_for_operands(
        &func,
        block,
        BinOp::Add,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
        &SourceSpan::default(),
        Some(0),
    )
    .expect("i128 add must emit a VC");
    let a_bv = "__trust_ovf_bv_lhs_a";
    let b_bv = "__trust_ovf_bv_rhs_b";
    // i128::MAX + 1 overflows above MAX.
    let ovf = |name: &str| -> u128 {
        if name == a_bv {
            i128::MAX as u128
        } else if name == b_bv {
            1
        } else {
            0
        }
    };
    assert!(
        eval_bv_bool(&vc.formula, &ovf),
        "REAL i128 add overflow (i128::MAX + 1) must be refutable (SAT); formula: {:?}",
        vc.formula
    );
    // i128::MIN + i128::MIN underflows below MIN — the OTHER direction.
    let ovf_neg = |name: &str| -> u128 {
        if name == a_bv {
            i128::MIN as u128
        } else if name == b_bv {
            i128::MIN as u128
        } else {
            0
        }
    };
    assert!(
        eval_bv_bool(&vc.formula, &ovf_neg),
        "REAL i128 add underflow (i128::MIN + i128::MIN) must be refutable (SAT); \
         formula: {:?}",
        vc.formula
    );
    // 3 + 4 is in range — UNSAT.
    let safe = |name: &str| -> u128 {
        if name == a_bv {
            3
        } else if name == b_bv {
            4
        } else {
            0
        }
    };
    assert!(
        !eval_bv_bool(&vc.formula, &safe),
        "SAFE i128 add (3 + 4) must NOT satisfy the violation; formula: {:?}",
        vc.formula
    );
}

/// signed_min's `-(1i128 << (width-1))`: with the shift block-def + `n < 128`, the
/// negated value `_5` is a power of two in `[1, 2^127]`, NEVER `i128::MIN`, so the
/// BV neg-overflow VC (`_5 == i128::MIN`) is UNSAT (PROVED). ADVERSARIALLY, an
/// unconstrained `_5` makes it refutable (covered by
/// `i128_negation_overflow_is_modeled_and_exact`).
#[test]
fn signed_min_neg_shifted_is_provable_unsat() {
    // Faithful two-step shape (mirrors the real `signed_min` MIR):
    //   bb0: _2 = (width <= 127); assert(_2, Shl) -> bb1
    //   bb1: _6 = width - 1; _5 = Shl(1i128, _6); _0 = -_5 (raw neg); return
    let func = VerifiableFunction {
        name: "signed_min_neg".to_string(),
        def_path: "test::signed_min_neg".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("width".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
                LocalDecl { index: 5, ty: Ty::i128(), name: Some("_5".into()) },
                LocalDecl { index: 6, ty: Ty::u32(), name: Some("_6".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        2,
                        Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(127, 32)),
                        ),
                    )],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::local(2)),
                        expected: true,
                        msg: AssertMessage::Overflow(BinOp::Shl),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        assign(
                            6,
                            Rvalue::BinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                        ),
                        assign(
                            5,
                            Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Constant(ConstValue::Int(1)),
                                Operand::Move(Place::local(6)),
                            ),
                        ),
                        assign(0, Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(5)))),
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i128(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = generate_v2_safety_vcs(&func);
    let neg = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
        .expect("signed_min `-_5` must emit a NegationOverflow VC");

    // The BV core carries `_5 == bvshl(1, _6) ∧ _6 < 127` (the derived bound from
    // `width <= 127` → `_6 = width-1 <= 126`). Over EVERY consistent witness (all
    // views — Int `width`/`_6`, Bool `_2`, BV `amt`/`_5` — bound to the SAME shift
    // amount), the violation `_5 == i128::MIN` must be FALSE → UNSAT → PROVED.
    let amt_bv = "__trust_ovf_bv_amt__6";
    let _5_bv = "__trust_ovf_bv_neg__5";
    for amt in 0u128..=200 {
        let _5_val: u128 = if amt >= 128 { 0 } else { 1u128 << amt };
        let width_val = amt + 1;
        let bool_true = u128::from(width_val <= 127);
        let env = |name: &str| -> u128 {
            match name {
                n if n == amt_bv => amt,
                n if n == _5_bv => _5_val,
                "_6" => amt,
                "width" => width_val,
                "_2" => bool_true,
                _ => 0,
            }
        };
        assert!(
            !eval_bv_bool(&neg.formula, &env),
            "signed_min `-_5` must be UNSAT (PROVED) for _6={amt} (_5={_5_val}); \
             formula: {:?}",
            neg.formula
        );
    }
    // The shift block-def must actually constrain `_5` (so the prove is real, not a
    // dropped-def vacuity): an INCONSISTENT `_5 = i128::MIN` with _6=5 must fail the
    // def equality → formula FALSE.
    let inconsistent = |name: &str| -> u128 {
        match name {
            "__trust_ovf_bv_amt__6" | "_6" => 5,
            "__trust_ovf_bv_neg__5" => i128::MIN as u128,
            "width" => 6,
            "_2" => 1,
            _ => 0,
        }
    };
    assert!(
        !eval_bv_bool(&neg.formula, &inconsistent),
        "the shift block-def must constrain `_5` (inconsistent witness FALSE), \
         proving the UNSAT is real; formula: {:?}",
        neg.formula
    );
}

// ===================================================================
// Signed 128-bit MUL: bounded-corner overflow proof.
//
// Signed i128 Mul was fail-closed to UNKNOWN (nonlinear NIA / 256-bit BV
// multiplier declined). When BOTH operands have KNOWN CONSTANT bounds on
// every reaching path, the exact integer product's extremes lie at the four
// corners of the box, so all-four-corners-fit-i128 PROVES no overflow with
// pure i128 arithmetic. These tests pin: (1) both const-pinned → proved;
// (2) one operand symbolic → fail-closed kept; (3) precondition-bounded box
// whose corner overflows → fail-closed kept, and a safe box → proved;
// (4) exact boundary correctness of the corner-fit predicate.
// ===================================================================

/// bb0 { <defs>; _tuple = CheckedMul(lhs, rhs); Assert(!_tuple.1, Overflow(Mul)) -> bb1 }
/// bb1 { _0 = _tuple.0; Return }
fn i128_mul_checked_fn(
    locals: Vec<LocalDecl>,
    defs: Vec<Statement>,
    lhs: Operand,
    rhs: Operand,
    tuple_local: usize,
    arg_count: usize,
) -> VerifiableFunction {
    let mut stmts = defs;
    stmts.push(assign(tuple_local, Rvalue::CheckedBinaryOp(BinOp::Mul, lhs, rhs)));
    VerifiableFunction {
        name: "f".to_string(),
        def_path: "test::f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts,
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place {
                            local: tuple_local,
                            projections: vec![Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Mul),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        0,
                        Rvalue::Use(Operand::Copy(Place {
                            local: tuple_local,
                            projections: vec![Projection::Field(0)],
                        })),
                    )],
                    terminator: Terminator::Return,
                },
            ],
            arg_count,
            return_ty: Ty::i128(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn use_const(v: i128) -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Int(v)))
}

fn tuple_decl(idx: usize) -> LocalDecl {
    LocalDecl { index: idx, ty: Ty::Tuple(vec![Ty::i128(), Ty::Bool]), name: None }
}

/// (1) `a * b` with block-defs `a = 3`, `b = 4`: both operands pinned to
/// constants ⇒ the product provably cannot overflow ⇒ a `Bool(false)` proof
/// VC (trivially UNSAT), NOT an UnsupportedMir fail-close.
#[test]
fn i128_mul_both_const_pinned_proves_no_overflow() {
    let locals = vec![
        LocalDecl { index: 0, ty: Ty::i128(), name: Some("ret".into()) },
        LocalDecl { index: 1, ty: Ty::i128(), name: Some("a".into()) },
        LocalDecl { index: 2, ty: Ty::i128(), name: Some("b".into()) },
        tuple_decl(3),
    ];
    let defs = vec![assign(1, use_const(3)), assign(2, use_const(4))];
    let func = i128_mul_checked_fn(
        locals,
        defs,
        Operand::Copy(Place::local(1)),
        Operand::Copy(Place::local(2)),
        3,
        0,
    );

    // Direct block-level builder (the path the SubWithOverflow/assert lane drives).
    let vc = v2_build_overflow_vc_for_operands(
        &func,
        &func.body.blocks[0],
        BinOp::Mul,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
        &SourceSpan::default(),
        None,
    )
    .expect("const-pinned i128 mul must still emit a VC");
    assert!(
        matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }),
        "must be a real ArithmeticOverflow proof, not UnsupportedMir; got {:?}",
        vc.kind
    );
    assert_eq!(
        vc.formula,
        Formula::Bool(false),
        "3 * 4 provably cannot overflow i128 ⇒ Bool(false) violation (UNSAT ⇒ proved); got {:?}",
        vc.formula
    );
    // A genuine proof: the violation is UNSAT for EVERY witness (never refutable).
    assert!(
        !eval_bv_bool(&vc.formula, &|_| 0),
        "the no-overflow proof VC must be unsatisfiable (never a masked overflow)"
    );

    // End-to-end (assert terminator lane): no UnsupportedMir row; the proof row is present.
    let vcs = generate_v2_safety_vcs(&func);
    assert!(
        !vcs.iter().any(|v| matches!(v.kind, VcKind::UnsupportedMir { .. })),
        "const-pinned i128 mul must NOT leave an UnsupportedMir row; kinds: {:?}",
        vcs.iter().map(|v| &v.kind).collect::<Vec<_>>()
    );
    assert!(
        vcs.iter().any(|v| matches!(v.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. })
            && v.formula == Formula::Bool(false)),
        "the assert lane must emit the ArithmeticOverflow Bool(false) proof; kinds: {:?}",
        vcs.iter().map(|v| &v.kind).collect::<Vec<_>>()
    );
}

/// (2) `a * b` where `a = 3` is pinned but `b` is a SYMBOLIC parameter (no
/// constant bound on any reaching path): the box is incomplete ⇒ the fail-
/// closed `UnsupportedMir` runtime-check is KEPT (never a proof from a
/// symbolic / one-sided-bounded operand).
#[test]
fn i128_mul_one_operand_symbolic_fails_closed() {
    // arg_count = 1 ⇒ local 1 ("b") is the symbolic parameter; local 2 ("a") is
    // a const-pinned temp.
    let locals = vec![
        LocalDecl { index: 0, ty: Ty::i128(), name: Some("ret".into()) },
        LocalDecl { index: 1, ty: Ty::i128(), name: Some("b".into()) },
        LocalDecl { index: 2, ty: Ty::i128(), name: Some("a".into()) },
        tuple_decl(3),
    ];
    let defs = vec![assign(2, use_const(3))];
    let func = i128_mul_checked_fn(
        locals,
        defs,
        Operand::Copy(Place::local(2)), // a = 3 (pinned)
        Operand::Copy(Place::local(1)), // b (symbolic param)
        3,
        1,
    );
    let vc = v2_build_overflow_vc_for_operands(
        &func,
        &func.body.blocks[0],
        BinOp::Mul,
        &Operand::Copy(Place::local(2)),
        &Operand::Copy(Place::local(1)),
        &SourceSpan::default(),
        None,
    )
    .expect("must still emit a (fail-closed) VC");
    assert!(
        matches!(vc.kind, VcKind::UnsupportedMir { .. }),
        "a symbolic operand must keep the fail-closed UnsupportedMir runtime-check; got {:?}",
        vc.kind
    );
}

/// Build the 2-param `a * b` i128 mul function whose preconditions bound
/// `a ∈ [a_lo, a_hi]` and `b ∈ [b_lo, b_hi]` (the "dominating range guard /
/// contract precondition" bound source). Params are locals 1 (`a`) and 2 (`b`).
fn i128_mul_precond_fn(a_lo: i128, a_hi: i128, b_lo: i128, b_hi: i128) -> VerifiableFunction {
    let locals = vec![
        LocalDecl { index: 0, ty: Ty::i128(), name: Some("ret".into()) },
        LocalDecl { index: 1, ty: Ty::i128(), name: Some("a".into()) },
        LocalDecl { index: 2, ty: Ty::i128(), name: Some("b".into()) },
        tuple_decl(3),
    ];
    let mut func = i128_mul_checked_fn(
        locals,
        vec![],
        Operand::Copy(Place::local(1)),
        Operand::Copy(Place::local(2)),
        3,
        2,
    );
    let name_a = crate::place_to_var_name(&func, &Place::local(1));
    let name_b = crate::place_to_var_name(&func, &Place::local(2));
    let var = |n: &str| Box::new(Formula::Var(n.into(), trust_types::Sort::Int));
    let int = |c: i128| Box::new(Formula::Int(c));
    func.preconditions = vec![
        Formula::Ge(var(&name_a), int(a_lo)),
        Formula::Le(var(&name_a), int(a_hi)),
        Formula::Ge(var(&name_b), int(b_lo)),
        Formula::Le(var(&name_b), int(b_hi)),
    ];
    func
}

fn i128_mul_precond_vc(func: &VerifiableFunction) -> VcKind {
    v2_build_overflow_vc_for_operands(
        func,
        &func.body.blocks[0],
        BinOp::Mul,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
        &SourceSpan::default(),
        None,
    )
    .expect("must emit a VC")
    .kind
}

/// (3) Precondition-bounded boxes: `a ∈ [0, i128::MAX]`, `b ∈ [0, 2]` has the
/// corner `i128::MAX * 2` OUTSIDE i128 ⇒ overflow is possible ⇒ the fail-
/// closed UnsupportedMir is KEPT (never a false PROVE). A safe box
/// `a, b ∈ [0, 1000]` (max corner 1_000_000) PROVES.
#[test]
fn i128_mul_precond_bounded_corner_overflow_fails_closed() {
    let overflow = i128_mul_precond_fn(0, i128::MAX, 0, 2);
    assert!(
        matches!(i128_mul_precond_vc(&overflow), VcKind::UnsupportedMir { .. }),
        "a box whose corner (i128::MAX * 2) overflows must stay fail-closed, never proved"
    );

    let safe = i128_mul_precond_fn(0, 1000, 0, 1000);
    let vc = v2_build_overflow_vc_for_operands(
        &safe,
        &safe.body.blocks[0],
        BinOp::Mul,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
        &SourceSpan::default(),
        None,
    )
    .expect("must emit a VC");
    assert!(
        matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. })
            && vc.formula == Formula::Bool(false),
        "a precondition-bounded safe box (0..=1000)² must PROVE (Bool(false)); got kind {:?} formula {:?}",
        vc.kind,
        vc.formula
    );
}

/// (4) EXACT boundary correctness of the pure corner-fit predicate: a corner
/// landing exactly on `i128::MIN`/`i128::MAX` FITS; one integer past it does
/// NOT. `checked_mul` is the sound i128-overflow oracle.
#[test]
fn signed_mul_corners_fit_boundary_exactness() {
    use super::v2_signed_mul_corners_fit;
    // Corner exactly at a type extreme fits (checked_mul is Some).
    assert!(v2_signed_mul_corners_fit((i128::MAX, i128::MAX), (1, 1)), "MAX*1 == MAX fits");
    assert!(v2_signed_mul_corners_fit((i128::MIN, i128::MIN), (1, 1)), "MIN*1 == MIN fits");
    assert!(v2_signed_mul_corners_fit((0, i128::MAX), (0, 1)), "max corner MAX*1 fits");
    assert!(v2_signed_mul_corners_fit((3, 3), (4, 4)), "3*4 fits");
    assert!(v2_signed_mul_corners_fit((-100, 100), (-100, 100)), "small symmetric box fits");
    // `i128::MIN` is even, so MIN/2 * 2 == MIN exactly (fits) but one lower overflows.
    assert!(v2_signed_mul_corners_fit((i128::MIN / 2, 0), (2, 2)), "(MIN/2)*2 == MIN fits");
    assert!(
        !v2_signed_mul_corners_fit((i128::MIN / 2 - 1, 0), (2, 2)),
        "(MIN/2 - 1)*2 == MIN - 2 overflows"
    );
    // One past a type extreme does NOT fit.
    assert!(
        !v2_signed_mul_corners_fit((i128::MIN, i128::MIN), (-1, -1)),
        "MIN * -1 == MAX + 1 overflows"
    );
    assert!(!v2_signed_mul_corners_fit((i128::MAX, i128::MAX), (2, 2)), "MAX*2 overflows");
    assert!(!v2_signed_mul_corners_fit((0, i128::MAX), (0, 2)), "corner MAX*2 overflows");
    // An inconsistent (empty) box is conservatively NOT provable.
    assert!(!v2_signed_mul_corners_fit((5, 3), (1, 1)), "empty box (lo > hi) not proved");
}
