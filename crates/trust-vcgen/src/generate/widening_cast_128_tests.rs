use trust_types::{
    BasicBlock, BinOp, BlockId, Formula, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

use super::{generate_v2_safety_vcs, v2_build_cast_vc, v2_is_value_preserving_widening};
use crate::guards;

/// Single-block function over the given locals and statements (block bb0,
/// terminating in Return). `arg_count`/`return_ty` are inert for these tests.
fn single_block_fn(
    name: &str,
    locals: Vec<LocalDecl>,
    stmts: Vec<Statement>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 1,
            return_ty: Ty::u128(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn assign(dest: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(dest), rvalue, span: SourceSpan::default() }
}

/// (a) `_2 = _1 as u128` over `_1: u32` is a value-preserving widening, so:
///   * `v2_build_cast_vc` emits NO CastOverflow obligation (provably
///     non-overflowing), instead of the old "target integer range is not
///     representable" UNKNOWN; and
///   * the block definitions still carry `_2 == _1` AND the u32 SOURCE range
///     bound on `_2` (`_2 <= u32::MAX`), so downstream arithmetic on the
///     widened value stays constrained.
#[test]
fn u32_to_u128_widening_cast_is_modeled_dest_eq_src_with_source_range() {
    let func = single_block_fn(
        "widen_u32_to_u128",
        vec![
            LocalDecl { index: 0, ty: Ty::u128(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u128(), name: Some("w".into()) },
        ],
        vec![assign(2, Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u128()))],
    );
    let block = &func.body.blocks[0];

    // No CastOverflow obligation — the widening cannot overflow. (Pre-fix this
    // returned an UnsupportedMir VC, downgrading every widen-to-128 to UNKNOWN.)
    let vc = v2_build_cast_vc(
        &func,
        block,
        &Operand::Copy(Place::local(1)),
        &Ty::u128(),
        &SourceSpan::default(),
        0,
    );
    assert!(vc.is_none(), "u32 as u128 widening must produce NO cast obligation; got {vc:?}");

    // The widened value is still modeled: `_2 == _1` (identity) and the u32
    // source-width range `_2 <= u32::MAX` are both present among the block defs.
    let defs = guards::extract_block_definitions(&func, block);
    let smt: Vec<String> = defs.iter().map(|f| f.to_smtlib()).collect();
    let dest = crate::place_to_var_name(&func, &Place::local(2));
    let src = crate::place_to_var_name(&func, &Place::local(1));

    let has_identity = defs.iter().any(|f| {
        matches!(
            f,
            Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some(dest.as_str())
                    && rhs.var_name() == Some(src.as_str())
        )
    });
    assert!(
        has_identity,
        "expected `{dest} == {src}` identity def for the widening cast; defs: {smt:?}"
    );

    // The u32 source max (2^32 - 1 = 4294967295) must upper-bound the widened
    // dest — that is the exact source-range fact the prompt requires.
    let u32_max = u128::from(u32::MAX);
    let mentions_dest_and_u32_max = defs.iter().any(|f| {
        let s = f.to_smtlib();
        s.contains(&dest) && s.contains(&u32_max.to_string())
    });
    assert!(
        mentions_dest_and_u32_max,
        "expected the u32 source range (<= {u32_max}) on `{dest}`; defs: {smt:?}"
    );
}

/// The widening classifier accepts exactly the value-preserving widenings and
/// rejects the value-CHANGING 128-bit casts, so the short-circuit can never
/// drop a real obligation.
#[test]
fn value_preserving_widening_classifier_is_tight() {
    // Value-preserving widenings into 128-bit: dropped obligation is sound.
    assert!(v2_is_value_preserving_widening(&Ty::u32(), &Ty::u128()));
    assert!(v2_is_value_preserving_widening(&Ty::u64(), &Ty::u128()));
    assert!(v2_is_value_preserving_widening(&Ty::u32(), &Ty::i128())); // u32 fits i128
    assert!(v2_is_value_preserving_widening(&Ty::u64(), &Ty::i128()));
    assert!(v2_is_value_preserving_widening(&Ty::Int { width: 64, signed: true }, &Ty::i128())); // i64 -> i128 sign-extend

    // NOT value-preserving — must stay obligations (never silently dropped):
    //   * signed -> unsigned (negative wraps to a huge unsigned value);
    assert!(!v2_is_value_preserving_widening(
        &Ty::Int { width: 64, signed: true },
        &Ty::u128()
    ));
    //   * same-width 128-bit reinterpret (i128 <-> u128 changes value);
    assert!(!v2_is_value_preserving_widening(&Ty::i128(), &Ty::u128()));
    assert!(!v2_is_value_preserving_widening(&Ty::u128(), &Ty::i128()));
    //   * narrowing.
    assert!(!v2_is_value_preserving_widening(&Ty::u128(), &Ty::u32()));
}

/// A NON-value-preserving cast into u128 (`i128 as u128`, a same-width
/// signed->unsigned reinterpret) must STILL be UNKNOWN — the short-circuit
/// must not over-fire and start modeling value-changing casts as no-ops.
#[test]
fn i128_to_u128_reinterpret_is_defined_no_obligation() {
    // Drop-in (owner decision 2026-07-06): `i128 as u128` is a same-width
    // signedness reinterpret — DEFINED behavior (never UB), so it carries NO
    // cast safety obligation (no CastOverflow, no fail-closed UnsupportedMir).
    // Soundness is preserved because the result is NOT modeled as a
    // value-preserving no-op: `cast_definition_formula` still declines to emit
    // `dest == source` for this value-CHANGING reinterpret (a negative i128 maps
    // to a large u128), so the value is not falsely equated — it is instead
    // type-tracked to the target-type range by `narrowing_cast_result_range`.
    let func = single_block_fn(
        "reinterpret_i128_to_u128",
        vec![
            LocalDecl { index: 0, ty: Ty::u128(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::i128(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u128(), name: Some("r".into()) },
        ],
        vec![assign(2, Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u128()))],
    );
    let vc = v2_build_cast_vc(
        &func,
        &func.body.blocks[0],
        &Operand::Copy(Place::local(1)),
        &Ty::u128(),
        &SourceSpan::default(),
        0,
    );
    assert!(
        vc.is_none(),
        "i128 as u128 reinterpret is defined and must emit NO cast obligation; got {vc:?}"
    );
    // Guard against a false-PROVE regression: the value must NOT be modeled as
    // `dest == source` (that would credit a wrong u128 for a negative i128).
    let defs = crate::guards::extract_block_definitions(&func, &func.body.blocks[0]);
    let dest = crate::place_to_var_name(&func, &Place::local(2));
    let equated_to_source = defs.iter().any(|f| {
        matches!(f, Formula::Eq(l, r)
            if l.var_name() == Some(dest.as_str())
            && matches!(r.as_ref(), Formula::Var(n, _) if n == "x"))
    });
    assert!(
        !equated_to_source,
        "value-changing reinterpret must NOT be modeled as `dest == source`: {defs:?}"
    );
}

// ----- adversarial guardrail: widening must not vacuously prove u128 overflow -----

/// Ground value for the witness evaluator. `Wrapped` marks an addition that
/// rose above `u128::MAX` — exactly the unsigned-overflow direction the VC's
/// `result > u128::MAX` disjunct detects.
#[derive(Clone, Copy)]
enum Val {
    Fin(u128),
    AboveMax,
}

/// Evaluate `f` under the concrete model `env` (var name -> u128). Only the
/// connectives that appear in an unsigned-add overflow VC are handled; any
/// unhandled node panics so the test fails loudly rather than silently
/// passing on an unmodeled formula shape.
fn eval_bool(f: &Formula, env: &dyn Fn(&str) -> u128) -> bool {
    match f {
        Formula::Bool(b) => *b,
        Formula::And(cs) => cs.iter().all(|c| eval_bool(c, env)),
        Formula::Or(cs) => cs.iter().any(|c| eval_bool(c, env)),
        Formula::Not(c) => !eval_bool(c, env),
        Formula::Le(a, b) => le(eval_val(a, env), eval_val(b, env)),
        Formula::Lt(a, b) => lt(eval_val(a, env), eval_val(b, env)),
        Formula::Ge(a, b) => le(eval_val(b, env), eval_val(a, env)),
        Formula::Gt(a, b) => lt(eval_val(b, env), eval_val(a, env)),
        Formula::Eq(a, b) => eq(eval_val(a, env), eval_val(b, env)),
        other => panic!("eval_bool: unhandled formula node {other:?}"),
    }
}

fn eval_val(f: &Formula, env: &dyn Fn(&str) -> u128) -> Val {
    match f {
        Formula::Int(n) => Val::Fin(u128::try_from(*n).expect("non-negative int literal")),
        Formula::UInt(n) => Val::Fin(*n),
        Formula::Var(name, _) => Val::Fin(env(name.as_str())),
        Formula::Add(a, b) => match (eval_val(a, env), eval_val(b, env)) {
            (Val::Fin(x), Val::Fin(y)) => x.checked_add(y).map_or(Val::AboveMax, Val::Fin),
            _ => Val::AboveMax,
        },
        other => panic!("eval_val: unhandled formula node {other:?}"),
    }
}

fn le(a: Val, b: Val) -> bool {
    match (a, b) {
        (Val::Fin(x), Val::Fin(y)) => x <= y,
        (Val::Fin(_), Val::AboveMax) => true,
        (Val::AboveMax, Val::Fin(_)) => false,
        (Val::AboveMax, Val::AboveMax) => true,
    }
}
fn lt(a: Val, b: Val) -> bool {
    match (a, b) {
        (Val::Fin(x), Val::Fin(y)) => x < y,
        (Val::Fin(_), Val::AboveMax) => true,
        (Val::AboveMax, _) => false,
    }
}
fn eq(a: Val, b: Val) -> bool {
    matches!((a, b), (Val::Fin(x), Val::Fin(y)) if x == y)
}

/// (b) ADVERSARIAL. `_3 = _1 as u128; _5 = _3 + _4` where `_1: u64` and
/// `_4: u128` is unconstrained. The widening fact bounds the widened operand
/// `_3 <= u64::MAX`, but `_4` is a free u128, so `_3 + _4` genuinely overflows
/// — the obligation must remain refutable. We confirm the violation formula is
/// SATISFIABLE under the witness `_3 = u64::MAX, _4 = u128::MAX` (sum > u128::MAX),
/// i.e. the widening fact did NOT vacuously turn a real overflow into a PROVE.
#[test]
fn widening_does_not_vacuously_prove_real_u128_overflow() {
    // Locals MUST be declared in vector-position == local-index order, since
    // `place_to_var_name` indexes the `locals` vec by position.
    //   _0 ret, _1 x:u64, _2 w:u128 (widened), _3 y:u128 (unconstrained), _4 s:u128 (sum)
    let func = single_block_fn(
        "widen_then_add",
        vec![
            LocalDecl { index: 0, ty: Ty::u128(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u128(), name: Some("w".into()) },
            LocalDecl { index: 3, ty: Ty::u128(), name: Some("y".into()) },
            LocalDecl { index: 4, ty: Ty::u128(), name: Some("s".into()) },
        ],
        vec![
            assign(2, Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u128())),
            assign(
                4,
                Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(2)),
                    Operand::Copy(Place::local(3)),
                ),
            ),
        ],
    );

    let vcs = generate_v2_safety_vcs(&func);
    let overflow = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .expect("the u128 `_3 + _4` add must still emit an ArithmeticOverflow obligation");

    // Witness exhibiting a genuine u128 overflow that respects the widening
    // fact (`_2 <= u64::MAX`): _2 = u64::MAX, _3 = u128::MAX, and the cast
    // source `_1 == _2 = u64::MAX`. Any other free var (the redundant sum
    // local) is satisfiable at 0.
    let widened = crate::place_to_var_name(&func, &Place::local(2)); // "w"
    let src = crate::place_to_var_name(&func, &Place::local(1)); // "x"
    let unconstrained = crate::place_to_var_name(&func, &Place::local(3)); // "y"
    let env = |name: &str| -> u128 {
        // Base-name compare: the S2c flip versions the widened local
        // (`w` → `w#s0_0`); the witness binds the place, not its version.
        let base = name.split('#').next().unwrap_or(name);
        if base == widened || base == src {
            u128::from(u64::MAX)
        } else if base == unconstrained {
            u128::MAX
        } else {
            0
        }
    };

    assert!(
        eval_bool(&overflow.formula, &env),
        "the widening fact must NOT mask a real u128 overflow: the violation \
         witness (_2 = u64::MAX, _3 = u128::MAX) must satisfy the VC; formula: {:?}",
        overflow.formula
    );
}
