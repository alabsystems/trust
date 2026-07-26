use trust_types::UnwindEdge;
use super::*;
use trust_types::{BasicBlock, LocalDecl, VerifiableBody};

const TO_BITS_F64: &str = "core::f64::<impl f64>::to_bits";
const TO_BITS_F32: &str = "core::f32::<impl f32>::to_bits";
const FROM_BITS_F64: &str = "core::f64::<impl f64>::from_bits";

fn call(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        is_unsafe_sig: false,
        is_foreign: false,
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
    }
}

/// A one-block-plus-return function `dest = CALLEE(arg)` used to exercise the
/// recognizer directly and through `build_semantic_guard_map`.
fn one_call_fn(
    callee: &str,
    arg: Operand,
    dest: usize,
    locals: Vec<LocalDecl>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "test::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: call(callee, vec![arg], dest, 1),
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Float { width: 64 },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// `v: f64` (local 1) -> `bits: u64` (local 2). `_0` is the unused f64 ret.
fn to_bits_f64_fn() -> VerifiableFunction {
    one_call_fn(
        TO_BITS_F64,
        Operand::Copy(Place::local(1)),
        2,
        vec![
            LocalDecl { index: 0, ty: Ty::Float { width: 64 }, name: Some("_0".into()) },
            LocalDecl { index: 1, ty: Ty::Float { width: 64 }, name: Some("v".into()) },
            LocalDecl { index: 2, ty: Ty::u64(), name: Some("bits".into()) },
        ],
    )
}

#[test]
fn to_bits_f64_binds_dest_to_shared_operand_bitvector() {
    let func = to_bits_f64_fn();
    let fact = super::float_bits_call_dest_fact(&func, &func.body.blocks[0].terminator)
        .expect("f64::to_bits must be modeled");
    // EXACT shape: `Eq(Var("bits", Int), bv2int_u(Var("v", BitVec(64))))`.
    match &fact {
        Formula::Eq(l, r) => {
            assert_eq!(
                **l,
                Formula::Var("bits".into(), Sort::Int),
                "dest must be the u64 int-sorted `bits`, NOT a fresh symbol"
            );
            match &**r {
                Formula::BvToInt(inner, 64, false) => assert_eq!(
                    **inner,
                    Formula::Var("v".into(), Sort::BitVec(64)),
                    "operand must be the SHARED bitvector symbol `v` (BitVec 64), \
                     the same one the fp compares read under FpFromBits"
                ),
                other => panic!("expected unsigned bv2int of the operand, got {other:?}"),
            }
        }
        other => panic!("expected a definitional Eq, got {other:?}"),
    }
}

#[test]
fn to_bits_operand_symbol_is_exactly_what_fp_compare_reads() {
    // The whole point of the model: the bitvector in `to_bits(v)`'s fact is the
    // SAME `Var("v", BitVec(64))` that `guards::fp_operand` wraps in `FpFromBits`
    // for `v == 0.0` / `v > 0.0`. `operand_to_formula` yields exactly that symbol
    // for the float operand, so a guard over the fp value and the integer fact
    // share one symbol — which is what re-correlates `v != 0.0` with `bits != 0`.
    let func = to_bits_f64_fn();
    let shared = crate::operand_to_formula(&func, &Operand::Copy(Place::local(1)));
    assert_eq!(shared, Formula::Var("v".into(), Sort::BitVec(64)));
    let fact =
        super::float_bits_call_dest_fact(&func, &func.body.blocks[0].terminator).unwrap();
    let Formula::Eq(_, r) = &fact else { panic!("expected Eq") };
    let Formula::BvToInt(inner, ..) = &**r else { panic!("expected BvToInt") };
    assert_eq!(**inner, shared, "to_bits fact and fp compare must share ONE symbol");
}

#[test]
fn to_bits_f32_uses_bitvec32() {
    let func = one_call_fn(
        TO_BITS_F32,
        Operand::Copy(Place::local(1)),
        2,
        vec![
            LocalDecl { index: 0, ty: Ty::Float { width: 32 }, name: Some("_0".into()) },
            LocalDecl { index: 1, ty: Ty::Float { width: 32 }, name: Some("v".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("bits".into()) },
        ],
    );
    let fact = super::float_bits_call_dest_fact(&func, &func.body.blocks[0].terminator)
        .expect("f32::to_bits must be modeled");
    let Formula::Eq(l, r) = &fact else { panic!("expected Eq") };
    assert_eq!(**l, Formula::Var("bits".into(), Sort::Int));
    match &**r {
        Formula::BvToInt(inner, 32, false) => {
            assert_eq!(**inner, Formula::Var("v".into(), Sort::BitVec(32)));
        }
        other => panic!("expected bv2int width 32, got {other:?}"),
    }
}

#[test]
fn from_bits_f64_is_inverse_identity() {
    // `r: f64` (local 2) = from_bits(`b: u64`, local 1).
    let func = one_call_fn(
        FROM_BITS_F64,
        Operand::Copy(Place::local(1)),
        2,
        vec![
            LocalDecl { index: 0, ty: Ty::Float { width: 64 }, name: Some("_0".into()) },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("b".into()) },
            LocalDecl { index: 2, ty: Ty::Float { width: 64 }, name: Some("r".into()) },
        ],
    );
    let fact = super::float_bits_call_dest_fact(&func, &func.body.blocks[0].terminator)
        .expect("f64::from_bits must be modeled");
    // Inverse of to_bits: `Eq(Var("r", BitVec(64)), int2bv(Var("b", Int)))`.
    match &fact {
        Formula::Eq(l, r) => {
            assert_eq!(
                **l,
                Formula::Var("r".into(), Sort::BitVec(64)),
                "from_bits dest is BitVec(64)-sorted (its IEEE bit pattern)"
            );
            match &**r {
                Formula::IntToBv(inner, 64) => {
                    assert_eq!(**inner, Formula::Var("b".into(), Sort::Int));
                }
                other => panic!("expected int2bv of the u64 arg, got {other:?}"),
            }
        }
        other => panic!("expected a definitional Eq, got {other:?}"),
    }
}

#[test]
fn to_bits_then_from_bits_round_trips_the_bitvector() {
    // to_bits gives `bits == bv2int(v_bits)`; from_bits gives
    // `dest_bits == int2bv(bits)`. Composed, `dest_bits == int2bv(bv2int(v_bits))`
    // — the identity on a 64-bit vector, so the round-trip preserves the bit
    // pattern exactly. We check the two model facts compose without loss: the
    // from_bits arg symbol is precisely the to_bits dest symbol.
    let func = to_bits_f64_fn();
    let to_bits =
        super::float_bits_call_dest_fact(&func, &func.body.blocks[0].terminator).unwrap();
    let Formula::Eq(dest, _) = &to_bits else { panic!() };
    let Formula::Var(bits_name, Sort::Int) = &**dest else { panic!("to_bits dest is Int var") };
    // Now feed `bits` into from_bits.
    let rt = one_call_fn(
        FROM_BITS_F64,
        Operand::Copy(Place::local(2)),
        3,
        vec![
            LocalDecl { index: 0, ty: Ty::Float { width: 64 }, name: Some("_0".into()) },
            LocalDecl { index: 1, ty: Ty::Float { width: 64 }, name: Some("v".into()) },
            LocalDecl { index: 2, ty: Ty::u64(), name: Some("bits".into()) },
            LocalDecl { index: 3, ty: Ty::Float { width: 64 }, name: Some("back".into()) },
        ],
    );
    let from_bits =
        super::float_bits_call_dest_fact(&rt, &rt.body.blocks[0].terminator).unwrap();
    let Formula::Eq(_, arg) = &from_bits else { panic!() };
    let Formula::IntToBv(inner, 64) = &**arg else { panic!("from_bits arg is int2bv") };
    assert_eq!(
        **inner,
        Formula::Var(bits_name.clone(), Sort::Int),
        "from_bits consumes exactly the u64 symbol to_bits produced — lossless round-trip"
    );
}

#[test]
fn crown_deep_shape_threads_tobits_fact_to_underflow_block() {
    // Reproduce `f64_next_up_compat`:
    //   bb0: is_zero = (v == 0.0); switch -> false: bb1, true: bb5 (early return)
    //   bb1: bits = v.to_bits();          -> bb2
    //   bb2: is_pos = (v > 0.0); switch -> false: bb4 (bits - 1), true: bb3 (bits + 1)
    //   bb3: t = bits + 1; return
    //   bb4: t = bits - 1; return   <-- the Sub-underflow VC that was falsely refuted
    //   bb5: return
    // The recognizer's fact is threaded from bb1's terminator; the assertion is
    // that it REACHES bb4 (the underflow site) carrying the SHARED `Var("v",
    // BitVec(64))`. That shared symbol is what lets `v != 0.0` (an fp fact over
    // the same bitvector) force `bits != 0`, so `bits - 1` cannot underflow.
    // (Unit tests here are structural — no SMT solver is run; this pins the
    // guard-map connectivity the proof depends on.)
    let f64t = Ty::Float { width: 64 };
    let bin = |op, dest, l: Operand, r: Operand| Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::BinaryOp(op, l, r),
        span: SourceSpan::default(),
    };
    let switch = |discr, zero_target, otherwise| Terminator::SwitchInt {
        discr,
        targets: vec![(0, BlockId(zero_target))],
        otherwise: BlockId(otherwise),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    let func = VerifiableFunction {
        name: "f64_next_up_compat".into(),
        def_path: "test::f64_next_up_compat".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: f64t.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: f64t.clone(), name: Some("v".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("bits".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("is_zero".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("is_pos".into()) },
                LocalDecl { index: 5, ty: Ty::u64(), name: Some("t_add".into()) },
                LocalDecl { index: 6, ty: Ty::u64(), name: Some("t_sub".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![bin(
                        BinOp::Eq,
                        3,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Float(0.0)),
                    )],
                    terminator: switch(Operand::Copy(Place::local(3)), 1, 5),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: call(TO_BITS_F64, vec![Operand::Copy(Place::local(1))], 2, 2),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![bin(
                        BinOp::Gt,
                        4,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Float(0.0)),
                    )],
                    terminator: switch(Operand::Copy(Place::local(4)), 4, 3),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![bin(
                        BinOp::Add,
                        5,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Uint(1, 64)),
                    )],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![bin(
                        BinOp::Sub,
                        6,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Uint(1, 64)),
                    )],
                    terminator: Terminator::Return,
                },
                BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: f64t,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let guards = build_semantic_guard_map(&func);
    let underflow_guards = guards.get(&BlockId(4)).cloned().unwrap_or_default();
    let has_tobits_fact = underflow_guards.iter().any(|f| match f {
        Formula::Eq(l, r) => {
            let dest_ok = matches!(&**l, Formula::Var(n, Sort::Int) if n.split('#').next() == Some("bits"));
            let src_ok = matches!(&**r, Formula::BvToInt(inner, 64, false)
                if matches!(&**inner, Formula::Var(vn, Sort::BitVec(64)) if vn == "v"));
            dest_ok && src_ok
        }
        _ => false,
    });
    assert!(
        has_tobits_fact,
        "the `bits == bv2int(v_bits)` fact must reach the `bits - 1` block (bb4) \
         with the shared `v` bitvector; got guards: {underflow_guards:?}"
    );
}

#[test]
fn user_defined_to_bits_is_not_matched() {
    // A user `mymod::to_bits` (no `core::`/`::f64::` anchor) must NOT be modeled —
    // matching it would inject a false value-definition (a false-PROVE channel).
    let func = one_call_fn(
        "mymod::wrapper::to_bits",
        Operand::Copy(Place::local(1)),
        2,
        vec![
            LocalDecl { index: 0, ty: Ty::Float { width: 64 }, name: Some("_0".into()) },
            LocalDecl { index: 1, ty: Ty::Float { width: 64 }, name: Some("v".into()) },
            LocalDecl { index: 2, ty: Ty::u64(), name: Some("bits".into()) },
        ],
    );
    assert!(super::float_bits_call_dest_fact(&func, &func.body.blocks[0].terminator).is_none());
}

#[test]
fn to_bits_on_non_float_operand_is_rejected() {
    // Defensive width/type gate: a spoofed `::f64::to_bits` whose operand is not
    // an f64 fails closed (no fact), so it can never bind an ill-typed dest.
    let func = one_call_fn(
        TO_BITS_F64,
        Operand::Copy(Place::local(1)),
        2,
        vec![
            LocalDecl { index: 0, ty: Ty::Float { width: 64 }, name: Some("_0".into()) },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("v".into()) },
            LocalDecl { index: 2, ty: Ty::u64(), name: Some("bits".into()) },
        ],
    );
    assert!(super::float_bits_call_dest_fact(&func, &func.body.blocks[0].terminator).is_none());
}
