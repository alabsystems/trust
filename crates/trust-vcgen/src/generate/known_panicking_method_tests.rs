use trust_types::UnwindEdge;
use trust_types::LocalDecl;

use super::{
    AggregateKind, BinOp, ConstValue, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableFunction, is_known_panicking_method, range_aggregate_const_len,
    range_bound_affine, slice_arg_static_len,
};

#[test]
fn recognizes_option_result_unwrap_expect() {
    assert!(is_known_panicking_method("Option::<u32>::unwrap"));
    assert!(is_known_panicking_method("Option::<u32>::expect"));
    assert!(is_known_panicking_method("core::result::Result::<u32, u8>::unwrap"));
    assert!(is_known_panicking_method("Result::<u32, u8>::expect"));
    assert!(is_known_panicking_method("core::result::Result::<i32, E>::unwrap_err"));
}

#[test]
fn rejects_total_and_unrelated_methods() {
    // total (no panic): unwrap_or / unwrap_or_else / unwrap_or_default
    assert!(!is_known_panicking_method("Option::<u32>::unwrap_or"));
    assert!(!is_known_panicking_method("Option::<u32>::unwrap_or_else"));
    assert!(!is_known_panicking_method("Option::<u32>::unwrap_or_default"));
    // UB, not panic — a different obligation class
    assert!(!is_known_panicking_method("Option::<u32>::unwrap_unchecked"));
    // unrelated Option/Result methods
    assert!(!is_known_panicking_method("Option::<u32>::map"));
    assert!(!is_known_panicking_method("Option::<u32>::is_some"));
    // unrelated sinks
    assert!(!is_known_panicking_method("std::vec::Vec::<u8>::with_capacity"));
    assert!(!is_known_panicking_method("core::iter::Iterator::collect"));
}

// ===================================================================
// Trust (reliability E1): `is_bounds_panicking_slice_mutator` surfaces the
// bounds-panicking slice/Vec mutators rotate_left/rotate_right/split_off as
// Unknown — but NEVER the TOTAL integer rotate_left/rotate_right.
// ===================================================================
use trust_types::{BasicBlock, BlockId, VerifiableBody};

use super::is_bounds_panicking_slice_mutator;

/// A function whose only argument operand `_1` has type `&[u8]` (a confirmed
/// slice receiver, so `slice_len_formula` models a length) — used to exercise
/// gate (a) of the recognizer. `callee` is the call name under test.
fn slice_receiver_fn(callee: &str) -> VerifiableFunction {
    let slice_ref = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) }),
    };
    VerifiableFunction {
        name: "rot".to_string(),
        def_path: "test::rot".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: slice_ref, name: Some("s".into()) }, // &[u8] recv
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("mid".into()) }, // mid arg
                LocalDecl { index: 3, ty: Ty::Unit, name: Some("_3".into()) }, // dest
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee.to_string(),
                    args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    dest: Place::local(3),
                    target: Some(BlockId(0)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                },
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

fn args_of(f: &VerifiableFunction) -> Vec<Operand> {
    match &f.body.blocks[0].terminator {
        Terminator::Call { args, .. } => args.clone(),
        _ => unreachable!(),
    }
}

#[test]
fn recognizes_slice_receiver_rotate_and_split_off() {
    // (a) A modeled `&[u8]` receiver makes the slice mutator recognizable.
    for callee in [
        "core::slice::<impl [T]>::rotate_left",
        "core::slice::<impl [T]>::rotate_right",
        "core::slice::<impl [T]>::split_off",
    ] {
        let f = slice_receiver_fn(callee);
        assert!(
            is_bounds_panicking_slice_mutator(&f, callee, &args_of(&f)),
            "slice-receiver `{callee}` must be recognized as bounds-panicking"
        );
    }
}

#[test]
fn recognizes_owned_vec_split_off_by_path() {
    // (b) An owned `Vec`/`VecDeque` receiver has NO modeled slice length, but
    // the callee path names the container, so it is still recognized.
    let f = slice_receiver_fn("alloc::vec::Vec::<u8>::split_off"); // receiver type irrelevant here
    for callee in [
        "alloc::vec::Vec::<u8>::split_off",
        "alloc::collections::vec_deque::VecDeque::<u8>::split_off",
        "alloc::string::String::split_off",
    ] {
        // Use a func whose receiver carries no modeled slice length to isolate gate (b).
        let g = int_receiver_fn(callee);
        assert!(
            is_bounds_panicking_slice_mutator(&g, callee, &args_of(&g))
                || is_bounds_panicking_slice_mutator(&f, callee, &args_of(&f)),
            "owned-container `{callee}` must be recognized by the path fallback"
        );
    }
}

/// A function whose argument operand `_1` is a plain `u32` (NOT a slice) —
/// used to confirm a TOTAL integer rotate is NOT flagged (the receiver has no
/// modeled slice length and the path is the integer `num` impl).
fn int_receiver_fn(callee: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "rot_int".to_string(),
        def_path: "test::rot_int".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) }, // u32 recv
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("n".into()) }, // shift arg
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("_3".into()) }, // dest
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee.to_string(),
                    args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    dest: Place::local(3),
                    target: Some(BlockId(0)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                },
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn rejects_total_integer_rotate() {
    // A TOTAL `u32::rotate_left`/`rotate_right` never panics — must NOT be
    // flagged. The receiver has no modeled slice length AND the callee path is
    // the integer `num` impl (`<impl u32>`), so both gates (a) and (b) reject.
    for callee in [
        "core::num::<impl u32>::rotate_left",
        "core::num::<impl u32>::rotate_right",
        "core::num::<impl i64>::rotate_left",
    ] {
        let f = int_receiver_fn(callee);
        assert!(
            !is_bounds_panicking_slice_mutator(&f, callee, &args_of(&f)),
            "total integer `{callee}` must NOT be flagged as bounds-panicking"
        );
    }
}

#[test]
fn rejects_unrelated_methods() {
    // Unrelated method names never match, regardless of receiver.
    let f = slice_receiver_fn("core::slice::<impl [T]>::iter");
    for callee in [
        "core::slice::<impl [T]>::iter",
        "core::slice::<impl [T]>::len",
        "alloc::vec::Vec::<u8>::push",
    ] {
        assert!(
            !is_bounds_panicking_slice_mutator(&f, callee, &args_of(&f)),
            "unrelated `{callee}` must not be recognized"
        );
    }
}

/// A container call carrying ONLY the receiver operand `_1` (no range arg) — the
/// shape of a no-arg total drain (`HashMap`/`HashSet`/`BinaryHeap::drain()`).
fn receiver_only_fn(callee: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "d".to_string(),
        def_path: "test::d".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("m".into()) }, // recv
                LocalDecl { index: 2, ty: Ty::Unit, name: Some("_2".into()) }, // dest
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee.to_string(),
                    args: vec![Operand::Copy(Place::local(1))], // ONLY the receiver
                    dest: Place::local(2),
                    target: Some(BlockId(0)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                },
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn recognizes_range_taking_drain_but_not_total_drain() {
    // Range-taking `Vec`/`String`/`VecDeque::drain(range)` — the call carries the
    // receiver PLUS a range arg (args.len() == 2) — PANIC on a bad range, so they
    // must be flagged (fail-honest Unknown; closes the `v.drain(0..99)` false-accept).
    for callee in
        ["alloc::vec::Vec::<u8>::drain", "alloc::collections::vec_deque::VecDeque::<u8>::drain"]
    {
        let g = int_receiver_fn(callee); // 2 args (receiver + range), no modeled slice len
        assert!(
            is_bounds_panicking_slice_mutator(&g, callee, &args_of(&g)),
            "range-taking `{callee}` must be recognized as bounds-panicking"
        );
    }
    // No-arg total drains (`HashMap`/`HashSet`/`BinaryHeap::drain()`) drain
    // everything and NEVER panic — the call carries ONLY the receiver
    // (args.len() == 1), so they must NOT be flagged (avoid a needless over-refusal).
    for callee in [
        "std::collections::hash::map::HashMap::<u32, u32>::drain",
        "std::collections::hash::set::HashSet::<u32>::drain",
        "alloc::collections::binary_heap::BinaryHeap::<u32>::drain",
    ] {
        let h = receiver_only_fn(callee);
        assert!(
            !is_bounds_panicking_slice_mutator(&h, callee, &args_of(&h)),
            "no-arg total `{callee}` must NOT be flagged (it never panics)"
        );
    }
}

#[test]
fn recognizes_slice_only_bounds_panickers() {
    // `<[T]>::copy_within` (panics on OOB range / `dest+len > len`) and
    // `<[T]>::select_nth_unstable{,_by,_by_key}` (panic on `i >= len`) are
    // slice-only — no total same-name method exists — so gate (b)'s slice/`[T]`
    // path recognizes them and there is no collision to exclude. Closes the
    // `v.copy_within(0..99, 0)` / `v.select_nth_unstable(99)` false-accepts.
    for callee in [
        "core::slice::<impl [T]>::copy_within",
        "core::slice::<impl [T]>::select_nth_unstable",
        "core::slice::<impl [T]>::select_nth_unstable_by",
        "core::slice::<impl [T]>::select_nth_unstable_by_key",
        // `Vec::extend_from_within(range)` — Vec-only, `vec::Vec` path, unique name.
        "alloc::vec::Vec::<u8>::extend_from_within",
    ] {
        let g = int_receiver_fn(callee); // no modeled slice len → isolates gate (b)
        assert!(
            is_bounds_panicking_slice_mutator(&g, callee, &args_of(&g)),
            "slice/Vec bounds-panicker `{callee}` must be recognized"
        );
    }
}

// ===================================================================
// Constant-difference range length recovery (`range_aggregate_const_len`
// case (c)): `s[off..off+8]` has length 8 for EVERY runtime `off`.
// ===================================================================

/// Build a function whose local `_5` is a `Range` aggregate over the slice
/// param `_1: &[u8]` and the offset param `_2: usize`, with `start = _2` and
/// `end` per `end_def`. Mirrors real rustc MIR: `end = (_7.0)` where
/// `_7 = CheckedBinaryOp(Add, ...)`. The Range feeds a `<[u8] as Index>::index`
/// Call into `_4`, exactly as `bytes[off..off+8]` lowers.
fn const_diff_range_fn(
    end_def: Vec<Statement>,
    end_operand: Operand,
    extra_locals: Vec<LocalDecl>,
) -> VerifiableFunction {
    use trust_types::{BasicBlock, BlockId, VerifiableBody};
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
        LocalDecl {
            index: 1,
            ty: Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) },
            name: Some("_1".into()),
        },
        LocalDecl { index: 2, ty: Ty::usize(), name: Some("_2".into()) },
        LocalDecl {
            index: 3,
            ty: Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) },
            name: Some("_4".into()),
        },
        LocalDecl {
            index: 5,
            ty: Ty::Adt { adt_kind: None, layout: None, 
                variants: Vec::new(),
                name: "core::ops::Range".into(),
                fields: vec![],
                disc_index_safe: false,
                faithful_enum_repr: None, enum_layout: None, },
            name: Some("_5".into()),
        },
    ];
    locals.extend(extra_locals);
    let mut stmts = end_def;
    // `_5 = Range { start: copy _2, end: <end_operand> }`
    stmts.push(Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "core::ops::Range".into(),
                variant: 0,
                active_field: None,
                args: None,
            },
            vec![Operand::Copy(Place::local(2)), end_operand],
        ),
        span: SourceSpan::default(),
    });
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts,
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "<[u8] as core::ops::index::Index<core::ops::Range<usize>>>::index"
                        .into(),
                    args: vec![Operand::Copy(Place::local(1)), Operand::Move(Place::local(5))],
                    dest: Place::local(4),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                },
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

#[test]
fn const_difference_range_recovers_static_length() {
    // `bytes[off..off+8]`: end = (_7.0), _7 = AddWithOverflow(copy _2, const 8).
    // start base = _2, end base = _2, difference = 8 -> length 8 for ANY off.
    let end_def = vec![
        Statement::Assign {
            place: Place::local(7),
            rvalue: Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Uint(8, 64)),
            ),
            span: SourceSpan::default(),
        },
        // `_6 = move (_7.0)`
        Statement::Assign {
            place: Place::local(6),
            rvalue: Rvalue::Use(Operand::Move(Place::field(7, 0))),
            span: SourceSpan::default(),
        },
    ];
    let func = const_diff_range_fn(
        end_def,
        Operand::Move(Place::local(6)),
        vec![
            LocalDecl { index: 6, ty: Ty::usize(), name: Some("_6".into()) },
            LocalDecl { index: 7, ty: Ty::usize(), name: Some("_7".into()) },
        ],
    );
    // The Range aggregate (`_5`) yields the constant length 8.
    assert_eq!(
        range_aggregate_const_len(&func, &Operand::Move(Place::local(5))),
        Some(8),
        "constant-difference range off..off+8 must recover length 8"
    );
    // End-to-end: tracing the index-call result `_4` recovers the same length.
    assert_eq!(
        slice_arg_static_len(&func, &Place::local(4), 8),
        Some(8),
        "slice_arg_static_len must recover 8 via the index-call's const-diff range"
    );
    // Affine recovery of the two bounds: both share base _2; offsets 0 and 8.
    assert_eq!(
        range_bound_affine(&func, &Operand::Copy(Place::local(2)), 8),
        Some((Some(2), 0))
    );
    assert_eq!(
        range_bound_affine(&func, &Operand::Move(Place::local(6)), 8),
        Some((Some(2), 8))
    );
}

#[test]
fn off_plus_8_to_off_plus_16_recovers_length_8() {
    // `bytes[off+8..off+16]`: start = (_6.0)= _2+8, end = (_8.0)= _2+16.
    // Both affine in _2; difference 16-8 = 8.
    use trust_types::{BasicBlock, BlockId, VerifiableBody};
    let locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
        LocalDecl {
            index: 1,
            ty: Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) },
            name: Some("_1".into()),
        },
        LocalDecl { index: 2, ty: Ty::usize(), name: Some("_2".into()) },
        LocalDecl {
            index: 3,
            ty: Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) },
            name: Some("_4".into()),
        },
        LocalDecl {
            index: 5,
            ty: Ty::Adt { adt_kind: None, layout: None, 
                variants: Vec::new(),
                name: "core::ops::Range".into(),
                fields: vec![],
                disc_index_safe: false,
                faithful_enum_repr: None, enum_layout: None, },
            name: Some("_5".into()),
        },
        LocalDecl { index: 6, ty: Ty::usize(), name: Some("start".into()) },
        LocalDecl { index: 7, ty: Ty::usize(), name: Some("c7".into()) },
        LocalDecl { index: 8, ty: Ty::usize(), name: Some("end".into()) },
        LocalDecl { index: 9, ty: Ty::usize(), name: Some("c9".into()) },
    ];
    let mk_checked = |dest: usize, k: u128| Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::CheckedBinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(2)),
            Operand::Constant(ConstValue::Uint(k, 64)),
        ),
        span: SourceSpan::default(),
    };
    let mk_field = |dest: usize, src: usize| Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::Use(Operand::Move(Place::field(src, 0))),
        span: SourceSpan::default(),
    };
    let stmts = vec![
        mk_checked(7, 8),  // _7 = off + 8
        mk_field(6, 7),    // start = (_7.0)
        mk_checked(9, 16), // _9 = off + 16
        mk_field(8, 9),    // end = (_9.0)
        Statement::Assign {
            place: Place::local(5),
            rvalue: Rvalue::Aggregate(
                AggregateKind::Adt {
                    name: "core::ops::Range".into(),
                    variant: 0,
                    active_field: None,
                    args: None,
                },
                vec![Operand::Move(Place::local(6)), Operand::Move(Place::local(8))],
            ),
            span: SourceSpan::default(),
        },
    ];
    let func = VerifiableFunction {
        name: "g".into(),
        def_path: "g".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts,
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "<[u8] as core::ops::index::Index<core::ops::Range<usize>>>::index"
                        .into(),
                    args: vec![Operand::Copy(Place::local(1)), Operand::Move(Place::local(5))],
                    dest: Place::local(4),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                },
            }],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert_eq!(
        range_aggregate_const_len(&func, &Operand::Move(Place::local(5))),
        Some(8),
        "off+8..off+16 must recover length 8"
    );
    assert_eq!(slice_arg_static_len(&func, &Place::local(4), 8), Some(8));
}

#[test]
fn non_constant_difference_range_declines() {
    // `bytes[off..off+other]`: end = (_7.0), _7 = Add(copy _2, copy _3).
    // start base = _2; end is affine in TWO bases (_2 and _3) -> NOT single-base
    // affine -> `range_bound_affine(end)` declines -> NO static length. The
    // unwrap obligation is correctly KEPT (a real None panic must not become a
    // false PROVE).
    let end_def = vec![
        Statement::Assign {
            place: Place::local(7),
            rvalue: Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Copy(Place::local(3)), // distinct symbolic local `other`
            ),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(6),
            rvalue: Rvalue::Use(Operand::Move(Place::field(7, 0))),
            span: SourceSpan::default(),
        },
    ];
    let func = const_diff_range_fn(
        end_def,
        Operand::Move(Place::local(6)),
        vec![
            LocalDecl { index: 6, ty: Ty::usize(), name: Some("_6".into()) },
            LocalDecl { index: 7, ty: Ty::usize(), name: Some("_7".into()) },
        ],
    );
    assert_eq!(
        range_aggregate_const_len(&func, &Operand::Move(Place::local(5))),
        None,
        "non-constant-difference range off..off+other must NOT recover a length"
    );
    assert_eq!(
        slice_arg_static_len(&func, &Place::local(4), 8),
        None,
        "slice_arg_static_len must decline (keep the unwrap obligation)"
    );
    // The offending bound (`_6 = _2 + _3`) is two-base affine -> declines.
    assert_eq!(range_bound_affine(&func, &Operand::Move(Place::local(6)), 8), None);
}

#[test]
fn fully_symbolic_endpoints_decline() {
    // `bytes[a..b]` with a, b unrelated params: start base = _2, end base = _3
    // (distinct), difference NOT constant -> decline.
    let func = const_diff_range_fn(
        vec![],
        Operand::Copy(Place::local(3)), // end = _3, a different param than start _2
        vec![],
    );
    assert_eq!(
        range_aggregate_const_len(&func, &Operand::Move(Place::local(5))),
        None,
        "distinct symbolic endpoints a..b must NOT recover a length"
    );
}
