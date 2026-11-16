use trust_types::{
    BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Sort, SourceSpan,
    Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
};

use super::generate_vcs;

/// Number of div/rem-by-zero obligations the pipeline emits for `func`.
fn divzero_vc_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::DivisionByZero | VcKind::RemainderByZero))
        .count()
}

/// True if the rendered formula mentions `name` — confirms a conjoined guard /
/// precondition reaches the VC formula (so the solver discharges it) without
/// running an SMT solver in the unit test.
fn formula_mentions_var(f: &Formula, name: &str) -> bool {
    f.to_smtlib().contains(name)
}

/// `fn(a: ty, b: ty) -> ty { a.OP(b) }` as a single-block tail call. The
/// receiver `a` lowers to MIR arg 0 (local 1), the divisor `b` to arg 1
/// (local 2) — exactly the shape the recognizer keys on. `divisor` lets a
/// caller override arg 1 with a constant. `pre` optionally adds a precondition.
fn method_div_func(
    method: &str,
    ty: Ty,
    divisor: Operand,
    pre: Vec<Formula>,
) -> VerifiableFunction {
    named_div_func(&format!("core::num::<impl i32>::{method}"), ty, divisor, pre)
}

/// [`method_div_func`] with the whole rendered callee spelled out, so a USER
/// namesake can stand where core's method does.
fn named_div_func(callee: &str, ty: Ty, divisor: Operand, pre: Vec<Formula>) -> VerifiableFunction {
    VerifiableFunction {
        name: "div_caller".to_string(),
        def_path: "test::div_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee.to_string(),
                    args: vec![Operand::Copy(Place::local(1)), divisor],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(callee),
                    is_foreign: false,
                },
            }],
            arg_count: 2,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: pre,
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `iter.step_by(n)` — the iterator receiver is arg 0 (local 1), the step `n`
/// is arg 1 (local 2). `n == 0` panics in the stdlib.
fn step_by_func(step: Operand) -> VerifiableFunction {
    VerifiableFunction {
        name: "step_caller".to_string(),
        def_path: "test::step_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("iter".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "core::iter::traits::iterator::Iterator::step_by".to_string(),
                    args: vec![Operand::Copy(Place::local(1)), step],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(
                        "core::iter::traits::iterator::Iterator::step_by",
                    ),
                    is_foreign: false,
                },
            }],
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

// ----- fire on bug: unguarded dynamic divisor -----

#[test]
fn flags_unguarded_div_euclid() {
    // `a.div_euclid(b)` with `b` an unbounded i32 param PANICS when `b == 0`,
    // but lowers to a Call with no BinaryOp — it was reported vacuously safe.
    // It must now produce a DivisionByZero obligation.
    let func = method_div_func("div_euclid", Ty::i32(), Operand::Copy(Place::local(2)), vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "unguarded `a.div_euclid(b)` must emit a DivisionByZero obligation"
    );
}

#[test]
fn flags_unguarded_rem_euclid() {
    // `a.rem_euclid(b)` panics on a zero divisor — RemainderByZero obligation.
    let func = method_div_func("rem_euclid", Ty::i32(), Operand::Copy(Place::local(2)), vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::RemainderByZero)),
        "unguarded `a.rem_euclid(b)` must emit a RemainderByZero obligation"
    );
}

#[test]
fn checked_div_is_total_no_obligation() {
    // `a.checked_div(b)` returns `None` on a zero divisor — it NEVER panics, so
    // it must emit NO DivisionByZero obligation even when the divisor is a fully
    // unconstrained runtime value. (Regression pin for the false refutation of
    // `n.checked_div(&x).unwrap_or_else(BigUint::zero)`, which is panic-free.)
    let func = method_div_func("checked_div", Ty::u32(), Operand::Copy(Place::local(2)), vec![]);
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "`a.checked_div(b)` is total (returns None on zero) and must emit no obligation"
    );
}

#[test]
fn flags_unguarded_div_ceil() {
    // `a.div_ceil(b)` PANICS on `b == 0` exactly like `a / b`, but lowers to a
    // Call with no BinaryOp — it was reported vacuously safe (false-accept).
    // It must now emit a DivisionByZero obligation.
    let func = method_div_func("div_ceil", Ty::u32(), Operand::Copy(Place::local(2)), vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "unguarded `a.div_ceil(b)` must emit a DivisionByZero obligation"
    );
}

#[test]
fn allows_const_nonzero_div_ceil() {
    // `a.div_ceil(4)` — literal nonzero divisor is provably safe; no obligation
    // (drop-in: a guarded/const `div_ceil` still compiles).
    let func =
        method_div_func("div_ceil", Ty::u32(), Operand::Constant(ConstValue::Uint(4, 32)), vec![]);
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "`a.div_ceil(4)` has a provably-nonzero divisor and must emit no obligation"
    );
}

#[test]
fn checked_rem_is_total_no_obligation() {
    // `a.checked_rem(b)` returns `None` on a zero divisor — it NEVER panics, so
    // it must emit NO RemainderByZero obligation. Total twin of `checked_div`.
    let func = method_div_func("checked_rem", Ty::u32(), Operand::Copy(Place::local(2)), vec![]);
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "`a.checked_rem(b)` is total (returns None on zero) and must emit no obligation"
    );
}

#[test]
fn flags_unguarded_step_by() {
    // `iter.step_by(n)` panics when `n == 0`; an unbounded `n` must flag.
    let func = step_by_func(Operand::Copy(Place::local(2)));
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "unguarded `iter.step_by(n)` must emit a non-zero (DivisionByZero) obligation"
    );
}

// ----- no false positive: trivially-safe / unrelated calls -----

#[test]
fn allows_const_nonzero_div_euclid() {
    // `a.div_euclid(4)` — a literal nonzero divisor is trivially proved safe;
    // no obligation at all (mirrors the BinaryOp const-nonzero skip).
    let func =
        method_div_func("div_euclid", Ty::i32(), Operand::Constant(ConstValue::Int(4)), vec![]);
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "`a.div_euclid(4)` has a provably-nonzero divisor and must emit no obligation"
    );
}

#[test]
fn allows_const_nonzero_step_by() {
    let func = step_by_func(Operand::Constant(ConstValue::Uint(2, 64)));
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "`iter.step_by(2)` has a provably-nonzero step and must emit no obligation"
    );
}

#[test]
fn ignores_ordinary_call() {
    // An ordinary (non-division) method call must not produce any div-by-zero
    // obligation — the recognizer must not broadly fail-close on every Call.
    let func = method_div_func("wrapping_add", Ty::i32(), Operand::Copy(Place::local(2)), vec![]);
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "a non-division call must not produce a div-by-zero obligation"
    );
}

#[test]
fn ignores_float_div_euclid() {
    // `f64::div_euclid(0.0)` does NOT panic (returns inf/nan), so a float
    // divisor must not be flagged — flagging it would false-FAIL ordinary code.
    let func = method_div_func(
        "div_euclid",
        Ty::Float { width: 64 },
        Operand::Copy(Place::local(2)),
        vec![],
    );
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "float `div_euclid` does not panic on a zero divisor and must not be flagged"
    );
}

// ----- guarded: obligation generated but discharged by the conjoined guard -----

#[test]
fn precondition_b_nonzero_carries_into_div_euclid_vc() {
    // `#[requires(b != 0)] a.div_euclid(b)` is safe. The obligation IS
    // generated, but its formula must carry the precondition `b != 0` so the
    // solver discharges it — the safe/buggy distinction without an SMT run.
    let pre = Formula::Not(Box::new(Formula::Eq(
        Box::new(Formula::Var("b".into(), Sort::Int)),
        Box::new(Formula::Int(0)),
    )));
    let func = method_div_func("div_euclid", Ty::i32(), Operand::Copy(Place::local(2)), vec![pre]);
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("guarded div_euclid still generates the obligation (discharged at solve time)");
    assert!(
        formula_mentions_var(&vc.formula, "b"),
        "the div_euclid VC must reference the divisor `b` so the precondition \
         `b != 0` can discharge it; formula: {:?}",
        vc.formula
    );
}

#[test]
fn dominating_nonzero_guard_carries_into_div_euclid_vc() {
    // `if b != 0 { a.div_euclid(b) }` lowered to MIR: block 0 switches on the
    // divisor `b`; the `b == 0` edge skips the call (block 2), the `otherwise`
    // (`b != 0`) edge reaches the call block (block 1). The path-guard map must
    // conjoin `b != 0` onto the call's div-by-zero VC so the solver discharges
    // it — an unguarded call (the `flags_*` tests) has no such guard and fails.
    let func = VerifiableFunction {
        name: "guarded_div".to_string(),
        def_path: "test::guarded_div".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![
                // block 0: `switch b { 0 => bb2 (skip), _ => bb1 (call) }`.
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        exhaustive_enum_unreachable: false,
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                // block 1: reached only when `b != 0` — `a.div_euclid(b)`.
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::num::<impl i32>::div_euclid".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::num::<impl i32>::div_euclid",
                        ),
                        is_foreign: false,
                    },
                },
                // block 2: join / return.
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("guarded div_euclid still generates the obligation (discharged at solve time)");
    // The dominating `b != 0` SwitchInt guard must be conjoined into the VC so
    // the solver proves the failure (`b == 0`) UNSAT on this path.
    assert!(
        formula_mentions_var(&vc.formula, "b"),
        "the dominating `b != 0` guard must reach the div_euclid VC; formula: {:?}",
        vc.formula
    );
}

// ----- DIVZERO-NAME-1 (2026-10-06): the row is core's, not the name's -----
//
// `divzero_call` read the last path segment alone, so a USER function or method
// merely NAMED `div_ceil` / `rem_euclid` / `div_euclid` / `step_by` was charged
// `divisor != 0` over its own arguments and refuted at `a = 0, b = 0` (stage 1 of
// `4ccd862830`, `scratchpad/scout20/carry/divzero-confirm/z1.rs`). The user
// spellings below are the ones rustc rendered for those calls; the real-MIR twin is
// `tests/user_namesake_divzero_realmir.rs`.

/// Rendered callees of user functions that merely share a name with core's
/// zero-divisor methods. None of them is core's; none may mint core's row.
const USER_NAMESAKES: [&str; 18] = [
    "z1::Q::div_ceil",
    "z1::Q::rem_euclid",
    "z1::rem_euclid",
    "user_divzero::div_euclid",
    "z1::S::step_by",
    "<u8 as z1::Euclid>::rem_euclid",
    // A total user wrapper around core's real method (`if b == 0 { 0 } else {
    // a.div_ceil(b) }`): its own body keeps core's row; its caller owes nothing.
    "divzero_call_user_namesake::util::div_ceil",
    // A user module path that merely LOOKS like core's integer inherent.
    "my::num::<impl u32>::div_ceil",
    "mycore::num::<impl i32>::div_euclid",
    // A stamp is read past ONCE, and only when well formed (wave-21 integration,
    // STAMPED-CORE-MINT-1's rule; the genuine stamped core is `STAMPED_GENUINE_CORE`):
    // a short id, a second stamp, or a stamped user path mints nothing.
    "__trust_crate@0123456789abcde::core::num::<impl u32>::div_ceil",
    "__trust_crate@0123456789abcdef::__trust_crate@0123456789abcdef::core::num::<impl u32>::div_ceil",
    "__trust_crate@0123456789abcdef::mycrate::Q::div_ceil",
    "__trust_crate@0123456789abcdef::mycrate::iter::Iterator::step_by",
    // A third-party trait (`num_traits::Euclid`): its body is its own crate's to
    // verify; a call to it owes core's row no more than any dependency call does.
    "<u32 as num_traits::Euclid>::div_euclid",
    // `step_by` on a trait that is not std's `Iterator`, or on a stamped one.
    "mycrate::iter::Iterator::step_by",
    "<x::It as mycrate::Iterator>::step_by",
    "<x::It as __trust_crate@0123456789abcdef::core::iter::traits::iterator::Iterator>::step_by",
    // A sysroot-rooted `step_by` that is not `Iterator::step_by` (no such item
    // exists): the `step_by` arm reads the trait, not the crate root.
    "core::ops::range::Range::<usize>::step_by",
];

/// Core's own zero-divisor methods, as rustc renders them (read off
/// `-Ztrust-dump=mir-only` and `TRUST_VANILLA_DEBUG=1` ledgers), with the row each
/// must keep.
const CORE_DIVISOR_CALLS: [(&str, VcKind); 15] = [
    ("core::num::<impl i32>::div_euclid", VcKind::DivisionByZero),
    ("core::num::<impl u32>::div_euclid", VcKind::DivisionByZero),
    ("core::num::<impl u32>::div_ceil", VcKind::DivisionByZero),
    ("core::num::<impl u64>::div_ceil", VcKind::DivisionByZero),
    ("core::num::<impl i64>::rem_euclid", VcKind::RemainderByZero),
    ("std::num::<impl i64>::rem_euclid", VcKind::RemainderByZero),
    // Wider than `numeric_panic::int_inherent` on purpose: core's other owners keep
    // exactly the row they had before.
    ("core::num::wrapping::Wrapping::<i32>::div_euclid", VcKind::DivisionByZero),
    ("core::num::saturating::Saturating::<u32>::rem_euclid", VcKind::RemainderByZero),
    ("core::num::nonzero::NonZero::<u32>::div_ceil", VcKind::DivisionByZero),
    ("core::iter::traits::iterator::Iterator::step_by", VcKind::DivisionByZero),
    // The `std::iter` re-export spelling `callee_is_step_by` also accepts.
    ("std::iter::Iterator::step_by", VcKind::DivisionByZero),
    (
        "<core::ops::range::Range<usize> as core::iter::traits::iterator::Iterator>::step_by",
        VcKind::DivisionByZero,
    ),
    (
        "<core::slice::iter::Iter<'_, u32> as core::iter::traits::iterator::Iterator>::step_by",
        VcKind::DivisionByZero,
    ),
    // A user iterator that inherits std's default `step_by`, which panics on zero.
    ("<x::It as core::iter::traits::iterator::Iterator>::step_by", VcKind::DivisionByZero),
    (
        "<core_divzero::It as core::iter::traits::iterator::Iterator>::step_by",
        VcKind::DivisionByZero,
    ),
];

/// Core's own zero-divisor methods behind ONE well-formed leading extractor identity
/// stamp. The extractor stamps the GENUINE core whenever a second crate named `core`
/// is in the graph (or under `-Zbuild-std`), so these keep core's row, by the rule
/// `numeric_panic::int_inherent_minting` applies to `abs`, `pow` and `unchecked_*`
/// (STAMPED-CORE-MINT-1). Spellings as the extractor renders them in that graph
/// (`tests/ui/trust/stamped_genuine_core_divzero_row_kept.rs`).
const STAMPED_GENUINE_CORE: [(&str, VcKind); 5] = [
    ("__trust_crate@0123456789abcdef::core::num::<impl u32>::div_ceil", VcKind::DivisionByZero),
    ("__trust_crate@414739228a72f04f::core::num::<impl u32>::div_euclid", VcKind::DivisionByZero),
    ("__trust_crate@414739228a72f04f::core::num::<impl i64>::rem_euclid", VcKind::RemainderByZero),
    (
        "__trust_crate@414739228a72f04f::core::iter::traits::iterator::Iterator::step_by",
        VcKind::DivisionByZero,
    ),
    (
        "__trust_crate@414739228a72f04f::<x::It as core::iter::traits::iterator::Iterator>::step_by",
        VcKind::DivisionByZero,
    ),
];

/// Wave-21 integration (2026-10-09). FAILS BEFORE: with `divzero_call` checking the
/// authenticated root alone (as DIVZERO-NAME-1 first landed), every spelling here
/// answers `None`.
#[test]
fn a_stamped_genuine_core_keeps_its_divisor_row() {
    use super::panic_calls::{divzero_call, divzero_call_name_only};
    for (callee, kind) in STAMPED_GENUINE_CORE {
        assert_eq!(divzero_call(callee), Some((1, kind.clone())), "`{callee}` keeps core's row");
        assert_eq!(divzero_call_name_only(callee), Some((1, kind)), "`{callee}`: twin");
        let func = named_div_func(callee, Ty::u32(), Operand::Copy(Place::local(2)), vec![]);
        assert_eq!(divzero_vc_count(&func), 1, "`{callee}`: one row through `generate_vcs`");
    }
}

#[test]
fn a_user_namesake_of_a_core_divisor_method_mints_no_row() {
    use super::panic_calls::divzero_call;
    for callee in USER_NAMESAKES {
        assert_eq!(
            divzero_call(callee),
            None,
            "`{callee}` is not core's zero-divisor method; it owes no divzero/remzero row"
        );
        // End to end: an unguarded call with an unconstrained divisor.
        let func = named_div_func(callee, Ty::u32(), Operand::Copy(Place::local(2)), vec![]);
        assert_eq!(divzero_vc_count(&func), 0, "`{callee}`: no row through `generate_vcs`");
    }
}

#[test]
fn cores_divisor_methods_keep_their_row() {
    use super::panic_calls::divzero_call;
    for (callee, kind) in CORE_DIVISOR_CALLS {
        assert_eq!(divzero_call(callee), Some((1, kind)), "`{callee}` keeps core's row");
        let func = named_div_func(callee, Ty::u32(), Operand::Copy(Place::local(2)), vec![]);
        assert_eq!(divzero_vc_count(&func), 1, "`{callee}`: one row through `generate_vcs`");
    }
}

/// The deny-list twin answers exactly as the old tail-only recognizer did, for the
/// user namesakes and core's methods alike: `callee_has_call_site_panic_family` reads
/// it, and there a `Some` only withholds the vanilla admission of a sysroot fn item.
#[test]
fn the_name_only_twin_keeps_the_deny_list_answer() {
    use super::panic_calls::{divzero_call, divzero_call_name_only};
    for callee in USER_NAMESAKES {
        let tail_kind = if callee.ends_with("rem_euclid") {
            VcKind::RemainderByZero
        } else {
            VcKind::DivisionByZero
        };
        assert_eq!(divzero_call_name_only(callee), Some((1, tail_kind)), "`{callee}`");
        assert!(super::callee_has_call_site_panic_family(callee), "`{callee}`: deny-list answer");
    }
    for (callee, kind) in CORE_DIVISOR_CALLS {
        assert_eq!(divzero_call_name_only(callee), Some((1, kind)), "`{callee}`");
        assert!(super::callee_has_call_site_panic_family(callee), "`{callee}`: deny-list answer");
    }
    // The minting view is never wider than its twin.
    for callee in USER_NAMESAKES.iter().copied().chain(CORE_DIVISOR_CALLS.iter().map(|(c, _)| *c)) {
        if let Some(row) = divzero_call(callee) {
            assert_eq!(divzero_call_name_only(callee), Some(row), "`{callee}`");
        }
    }
    // Neither view names the total siblings.
    for callee in [
        "core::num::<impl u32>::checked_div",
        "core::num::<impl u32>::checked_rem_euclid",
        "core::num::<impl u32>::checked_div_euclid",
        "core::num::<impl u32>::div_floor_lookalike",
    ] {
        assert_eq!(divzero_call_name_only(callee), None, "`{callee}`");
        assert_eq!(divzero_call(callee), None, "`{callee}`");
    }
    // Trust (merge 2026-10-14): `wrapping_div_euclid` is NOT a total sibling. core
    // documents "This function will panic if `rhs` is zero" for it, as for the rest
    // of the primitive-integer division family. Since local main's `4a9cbe64be1` the
    // bridge lowers such a call's exact panic condition instead of refusing it as a
    // fatal absent callee, and this row is what refutes an unguarded call, so both
    // views charge core's own spelling, and the twin is still never narrower.
    for (callee, kind) in [
        ("core::num::<impl u32>::wrapping_div_euclid", VcKind::DivisionByZero),
        ("core::num::<impl u32>::wrapping_div", VcKind::DivisionByZero),
        ("core::num::<impl u32>::wrapping_rem_euclid", VcKind::RemainderByZero),
    ] {
        assert_eq!(divzero_call_name_only(callee), Some((1, kind.clone())), "`{callee}`");
        assert_eq!(divzero_call(callee), Some((1, kind)), "`{callee}`");
    }
}
