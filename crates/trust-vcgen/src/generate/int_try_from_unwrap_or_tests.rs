use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{build_semantic_guard_map, is_int_try_from_callee, is_std_unwrap_or_call};

const TRY_FROM: &str = "core::convert::TryFrom::try_from";
const UNWRAP_OR: &str = "core::result::Result::<T, E>::unwrap_or";
const INT_ERR: &str = "core::num::TryFromIntError";
const CHAR_ERR: &str = "core::char::CharTryFromError";

/// `Result<OK, ERR>` in the flattened enum shape `lower_enum_adt` produces
/// (`__tag` + one `__v{v}_{field}` slot per variant field).
fn result_ty(ok: Ty, err_name: &str) -> Ty {
    Ty::adt(
        "core::result::Result",
        vec![
            ("__tag".into(), Ty::Int { width: 64, signed: true }),
            ("__v0_0".into(), ok),
            ("__v1_0".into(), Ty::adt(err_name, vec![("0".into(), Ty::Unit)])),
        ],
    )
}

/// `fn f(x: SRC) -> DST { DST::try_from(x).unwrap_or(DEFAULT) }`, in the
/// elaborated MIR shape (with the compiler-inserted move-temp hop when `hop`):
///   bb0: _2 = try_callee(copy _1)                    -> Result<DST, ERR>
///   bb1: [_3 = move _2;] _4 = unwrap_callee(move _3|_2, const DEFAULT)
///   bb2: return
fn try_from_unwrap_or_fn(
    src_ty: Ty,
    dst_ty: Ty,
    res_ty: Ty,
    try_callee: &str,
    unwrap_callee: &str,
    default: ConstValue,
    hop: bool,
) -> VerifiableFunction {
    let recv = if hop { 3 } else { 2 };
    let hop_stmts = if hop {
        vec![Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Move(Place::local(2))),
            span: SourceSpan::default(),
        }]
    } else {
        Vec::new()
    };
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dst_ty.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: src_ty, name: Some("x".into()) },
                LocalDecl { index: 2, ty: res_ty.clone(), name: Some("r".into()) },
                LocalDecl { index: 3, ty: res_ty, name: Some("t".into()) },
                LocalDecl { index: 4, ty: dst_ty, name: Some("d".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: try_callee.into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: hop_stmts,
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: unwrap_callee.into(),
                        args: vec![
                            Operand::Move(Place::local(recv)),
                            Operand::Constant(default),
                        ],
                        dest: Place::local(4),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The source param `x` (never written -> stays BARE through versioning).
fn xv() -> Box<Formula> {
    Box::new(Formula::Var("x".into(), Sort::Int))
}
/// The unwrap_or dest `d`, pinned by `version_terminator_dest_fact` to the
/// bb1 terminator token.
fn dv() -> Box<Formula> {
    Box::new(Formula::Var("d#s1_t".into(), Sort::Int))
}

/// `in-range -> d == x`, in the emitted `Or[x < MIN, x > MAX, d == x]` encoding.
fn ok_fact(min: i128, max: i128) -> Formula {
    Formula::Or(vec![
        Formula::Lt(xv(), Box::new(Formula::Int(min))),
        Formula::Gt(xv(), Box::new(Formula::Int(max))),
        Formula::Eq(dv(), xv()),
    ])
}

/// `out-of-range -> d == default`, in the emitted `Or[MIN <= x <= MAX, d == default]`
/// encoding.
fn err_fact(min: i128, max: i128, default: i128) -> Formula {
    Formula::Or(vec![
        Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(min)), xv()),
            Formula::Le(xv(), Box::new(Formula::Int(max))),
        ]),
        Formula::Eq(dv(), Box::new(Formula::Int(default))),
    ])
}

/// The general unwrap_or type-range bound `MIN <= d <= MAX`.
fn range_fact(min: i128, max: i128) -> Formula {
    Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(min)), dv()),
        Formula::Le(dv(), Box::new(Formula::Int(max))),
    ])
}

/// The semantic guards threaded to the unwrap_or call's SUCCESSOR block.
fn successor_guards(func: &VerifiableFunction) -> Vec<Formula> {
    build_semantic_guard_map(func).get(&BlockId(2)).cloned().unwrap_or_default()
}

fn mentions_dest(guards: &[Formula]) -> bool {
    guards.iter().any(|f| format!("{f:?}").contains("d#"))
}

#[test]
fn u32_try_from_i64_unwrap_or_emits_both_conditional_payload_facts() {
    let func = try_from_unwrap_or_fn(
        Ty::i64(),
        Ty::u32(),
        result_ty(Ty::u32(), INT_ERR),
        TRY_FROM,
        UNWRAP_OR,
        ConstValue::Uint(7, 32),
        true,
    );
    let guards = successor_guards(&func);
    let max = u32::MAX as i128;
    assert!(
        guards.contains(&ok_fact(0, max)),
        "in-range -> d == x fact missing; got {guards:?}"
    );
    assert!(
        guards.contains(&err_fact(0, max, 7)),
        "out-of-range -> d == default fact missing; got {guards:?}"
    );
    assert!(
        guards.contains(&range_fact(0, max)),
        "general unwrap_or type-range bound missing; got {guards:?}"
    );
}

#[test]
fn direct_receiver_without_move_hop_also_matches() {
    let func = try_from_unwrap_or_fn(
        Ty::i64(),
        Ty::u32(),
        result_ty(Ty::u32(), INT_ERR),
        TRY_FROM,
        UNWRAP_OR,
        ConstValue::Uint(7, 32),
        false,
    );
    let guards = successor_guards(&func);
    assert!(
        guards.contains(&ok_fact(0, u32::MAX as i128)),
        "the hop-free shape (unwrap_or directly consuming the try_from dest) \
         must also be modeled; got {guards:?}"
    );
}

#[test]
fn u8_target_gets_0_to_255_bounds() {
    let func = try_from_unwrap_or_fn(
        Ty::i64(),
        Ty::u8(),
        result_ty(Ty::u8(), INT_ERR),
        TRY_FROM,
        UNWRAP_OR,
        ConstValue::Uint(3, 8),
        true,
    );
    let guards = successor_guards(&func);
    assert!(
        guards.contains(&ok_fact(0, 255)),
        "u8 target must be bounded by 0..=255; got {guards:?}"
    );
    assert!(
        guards.contains(&err_fact(0, 255, 3)),
        "u8 err-path fact must use the 0..=255 bounds; got {guards:?}"
    );
}

#[test]
fn i8_target_gets_signed_bounds() {
    let func = try_from_unwrap_or_fn(
        Ty::i64(),
        Ty::Int { width: 8, signed: true },
        result_ty(Ty::Int { width: 8, signed: true }, INT_ERR),
        TRY_FROM,
        UNWRAP_OR,
        ConstValue::Int(0),
        true,
    );
    let guards = successor_guards(&func);
    assert!(
        guards.contains(&ok_fact(-128, 127)),
        "i8 target must be bounded by -128..=127; got {guards:?}"
    );
}

#[test]
fn user_defined_try_from_is_not_modeled() {
    // SOUNDNESS: a user `mymod::try_from` has arbitrary semantics — the
    // representability facts must NOT be assumed for it.
    let func = try_from_unwrap_or_fn(
        Ty::i64(),
        Ty::u32(),
        result_ty(Ty::u32(), INT_ERR),
        "mymod::try_from",
        UNWRAP_OR,
        ConstValue::Uint(7, 32),
        true,
    );
    let guards = successor_guards(&func);
    let max = u32::MAX as i128;
    assert!(
        !guards.contains(&ok_fact(0, max)) && !guards.contains(&err_fact(0, max, 7)),
        "a user-defined try_from must not get the std payload facts; got {guards:?}"
    );
    // The unwrap_or itself IS the std one, so the (independently sound)
    // type-range bound on its int dest is still emitted.
    assert!(
        guards.contains(&range_fact(0, max)),
        "the std unwrap_or type-range bound is independent of the callee \
         producing the Result and must survive; got {guards:?}"
    );
}

#[test]
fn user_defined_unwrap_or_gets_no_facts_at_all() {
    let func = try_from_unwrap_or_fn(
        Ty::i64(),
        Ty::u32(),
        result_ty(Ty::u32(), INT_ERR),
        TRY_FROM,
        "mycrate::Thing::unwrap_or",
        ConstValue::Uint(7, 32),
        true,
    );
    let guards = successor_guards(&func);
    assert!(
        !mentions_dest(&guards),
        "a user unwrap_or must leave its dest havoc'd; got {guards:?}"
    );
}

#[test]
fn char_try_from_error_result_gets_no_payload_facts() {
    // SOUNDNESS: `char::try_from(u32)` — `char` is MODELED as Int{32,unsigned},
    // so the int-dest gate alone cannot exclude it, and its success set (the
    // char scalar range, surrogates excluded) is NOT `[0, u32::MAX]`: the
    // payload facts would be FALSE (e.g. src == 0xD800 -> Err at runtime, yet
    // the in-range fact would force d == 0xD800). The `TryFromIntError`
    // Result anchor must reject it.
    let func = try_from_unwrap_or_fn(
        Ty::u32(),
        Ty::u32(),
        result_ty(Ty::u32(), CHAR_ERR),
        TRY_FROM,
        UNWRAP_OR,
        ConstValue::Uint(65, 32),
        true,
    );
    let guards = successor_guards(&func);
    let max = u32::MAX as i128;
    assert!(
        !guards.contains(&ok_fact(0, max)) && !guards.contains(&err_fact(0, max, 65)),
        "a CharTryFromError Result must not get the int payload facts; got {guards:?}"
    );
    // The type-range WIDENING stays sound: every char value lies in [0, u32::MAX].
    assert!(
        guards.contains(&range_fact(0, max)),
        "the (weaker, still sound) type-range bound survives; got {guards:?}"
    );
}

#[test]
fn reassigned_dest_gets_no_facts() {
    // SOUNDNESS (staleness): a second store to the unwrap_or dest breaks the
    // SSA gate — ALL unwrap_or facts must be dropped (the same defense as the
    // min/max/clamp bounds).
    let mut func = try_from_unwrap_or_fn(
        Ty::i64(),
        Ty::u32(),
        result_ty(Ty::u32(), INT_ERR),
        TRY_FROM,
        UNWRAP_OR,
        ConstValue::Uint(7, 32),
        true,
    );
    func.body.blocks[2].stmts.push(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
        span: SourceSpan::default(),
    });
    let guards = successor_guards(&func);
    assert!(
        !mentions_dest(&guards),
        "a reassigned (non-SSA) dest must get no facts; got {guards:?}"
    );
}

#[test]
fn reassigned_source_gets_no_payload_facts() {
    // SOUNDNESS (staleness): the facts are versioned at the unwrap_or block,
    // so a source reassigned between the conversion and the unwrap_or would
    // bind the WRONG value — the stable-source gate must drop the payload
    // facts entirely.
    let mut func = try_from_unwrap_or_fn(
        Ty::i64(),
        Ty::u32(),
        result_ty(Ty::u32(), INT_ERR),
        TRY_FROM,
        UNWRAP_OR,
        ConstValue::Uint(7, 32),
        true,
    );
    func.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(5))),
        span: SourceSpan::default(),
    });
    let guards = successor_guards(&func);
    assert!(
        guards.iter().all(|f| {
            let s = format!("{f:?}");
            !(s.contains("d#s1_t") && s.contains("\"x"))
        }),
        "a reassigned source must not appear in any dest fact (under any \
         version token); got {guards:?}"
    );
}

#[test]
fn result_temp_with_second_use_gets_no_payload_facts() {
    // SCOPING gate (not soundness — see int_try_from_unwrap_or_facts): a
    // second observer of the intermediate Result keeps it from being a pure
    // conduit; the payload facts are skipped, the type-range bound stays.
    let mut func = try_from_unwrap_or_fn(
        Ty::i64(),
        Ty::u32(),
        result_ty(Ty::u32(), INT_ERR),
        TRY_FROM,
        UNWRAP_OR,
        ConstValue::Uint(7, 32),
        true,
    );
    func.body.locals.push(LocalDecl {
        index: 5,
        ty: result_ty(Ty::u32(), INT_ERR),
        name: Some("obs".into()),
    });
    func.body.blocks[1].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(5),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
            span: SourceSpan::default(),
        },
    );
    let guards = successor_guards(&func);
    let max = u32::MAX as i128;
    assert!(
        !guards.contains(&ok_fact(0, max)) && !guards.contains(&err_fact(0, max, 7)),
        "a multiply-used Result temp is outside the modeled scope; got {guards:?}"
    );
    assert!(
        guards.contains(&range_fact(0, max)),
        "the type-range bound does not depend on the conduit gate; got {guards:?}"
    );
}

#[test]
fn width_128_targets_fail_closed_no_facts() {
    // 128-bit targets are uniformly fail-closed: `Formula::Int` is
    // i128-backed, so `u128::MAX` is representable only via the
    // `Formula::UInt` escape hatch, and any literal beyond i64 is
    // unlowerable in the trust-wp lane (`Formula::has_large_integers`) /
    // rejected by the native typed-CHC Int parser — the codebase routes
    // 128-bit obligations through the BV theory instead, so NO Int-sorted
    // 128-bit fact (range or payload) is emitted.
    for (src, dst, default) in [
        (Ty::i64(), Ty::u128(), ConstValue::Uint(0, 128)),
        (Ty::u128(), Ty::i128(), ConstValue::Int(0)),
    ] {
        let func = try_from_unwrap_or_fn(
            src,
            dst.clone(),
            result_ty(dst, INT_ERR),
            TRY_FROM,
            UNWRAP_OR,
            default,
            true,
        );
        let guards = successor_guards(&func);
        assert!(
            !mentions_dest(&guards),
            "128-bit unwrap_or targets must stay havoc'd (fail-closed); got {guards:?}"
        );
    }
}

#[test]
fn recognizer_matches_std_spellings_only() {
    // TRAIT-method spellings `safe_def_path_str` produces (the same
    // resolution behavior `is_bool_from_call` documents for `From::from`),
    // plus the fully-qualified and trimmed impl spellings.
    assert!(is_int_try_from_callee("core::convert::TryFrom::try_from"));
    assert!(is_int_try_from_callee("std::convert::TryFrom::try_from"));
    assert!(is_int_try_from_callee("core::convert::TryInto::try_into"));
    assert!(is_int_try_from_callee("<u32 as core::convert::TryFrom<i64>>::try_from"));
    assert!(is_int_try_from_callee("<usize as TryFrom<i128>>::try_from"));
    // A user `try_from` — or a user trait literally named `TryFrom`, which
    // renders with its own crate path — must NOT match.
    assert!(!is_int_try_from_callee("mymod::try_from"));
    assert!(!is_int_try_from_callee("mycrate::convert::try_from"));
    assert!(!is_int_try_from_callee("<X as mycrate::TryFrom<Y>>::try_from"));
    assert!(!is_int_try_from_callee("mycrate::core::convert::TryFrom::try_from"));
    assert!(!is_int_try_from_callee(
        "<u32 as mycrate::convert::TryFrom<i64>>::try_from"
    ));
    assert!(!is_int_try_from_callee(
        "<u32 as mycrate::convert::TryInto<i64>>::try_into"
    ));
    // EXACT method tail.
    assert!(!is_int_try_from_callee("core::convert::TryFrom::try_from_exact"));

    assert!(is_std_unwrap_or_call("core::result::Result::<T, E>::unwrap_or"));
    assert!(is_std_unwrap_or_call("core::option::Option::<T>::unwrap_or"));
    // `unwrap_or_else`/`unwrap_or_default` run user code — never modeled.
    assert!(!is_std_unwrap_or_call("core::result::Result::<T, E>::unwrap_or_else"));
    assert!(!is_std_unwrap_or_call("core::result::Result::<T, E>::unwrap_or_default"));
    assert!(!is_std_unwrap_or_call("mycrate::Thing::unwrap_or"));
    assert!(!is_std_unwrap_or_call(
        "mycrate::core::result::Result::<T, E>::unwrap_or"
    ));
}
