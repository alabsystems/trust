use trust_types::UnwindEdge;
use trust_types::{
    AggregateKind, BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue,
    Sort, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

use super::generate_vcs;

/// A `&[u8]` slice receiver type.
fn slice_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) }
}

/// True if the rendered formula mentions `name` — confirms the receiver's
/// `__slice_len` / a conjoined guard reaches the VC formula (so the solver
/// discharges it) without running an SMT solver in the unit test.
fn formula_mentions(f: &Formula, name: &str) -> bool {
    f.to_smtlib().contains(name)
}

/// `fn(s: &[u8], a: usize, b: usize) { s.METHOD(a[, b]) }` as a single-block
/// tail call. The receiver `s` lowers to MIR arg 0 (local 1), the first index
/// `a` to arg 1 (local 2), the second `b` to arg 2 (local 3) — exactly the
/// shape the recognizer keys on. `args` are the call's MIR operands (already
/// including the receiver); `pre` optionally adds a precondition.
fn slice_method_func(
    method: &str,
    args: Vec<Operand>,
    pre: Vec<Formula>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "slice_caller".to_string(),
        def_path: "test::slice_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: slice_ref(), name: Some("s".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: format!("core::slice::<impl [u8]>::{method}"),
                    args,
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                },
            }],
            arg_count: 3,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: pre,
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Count of slice-bounds obligations (`split_at`/`swap`) the pipeline emits.
fn bounds_vc_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func).iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).count()
}

/// Count of non-zero-size obligations (`chunks`/`windows`) the pipeline emits.
fn nonzero_vc_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func).iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).count()
}

// ----- fire on bug: unguarded out-of-range argument -----

#[test]
fn flags_unguarded_split_at() {
    // `s.split_at(mid)` with `mid` an unbounded usize PANICS when `mid > len`,
    // but lowers to a Call with no Projection::Index — it was vacuously safe.
    let func = slice_method_func(
        "split_at",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        vec![],
    );
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck))
        .expect("unguarded `s.split_at(mid)` must emit a SliceBoundsCheck obligation");
    // The VC must relate the split point `a` to the receiver's `__slice_len`.
    assert!(
        formula_mentions(&vc.formula, "a") && formula_mentions(&vc.formula, "s__slice_len"),
        "the split_at VC must constrain `mid` against `s.len()`; formula: {:?}",
        vc.formula
    );
}

#[test]
fn flags_unguarded_split_at_mut() {
    let func = slice_method_func(
        "split_at_mut",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        vec![],
    );
    assert_eq!(
        bounds_vc_count(&func),
        1,
        "unguarded `s.split_at_mut(mid)` must emit a SliceBoundsCheck obligation"
    );
}

#[test]
fn flags_unguarded_chunks() {
    // `s.chunks(n)` with a possibly-zero `n` PANICS when `n == 0`.
    let func = slice_method_func(
        "chunks",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        vec![],
    );
    assert_eq!(
        nonzero_vc_count(&func),
        1,
        "unguarded `s.chunks(n)` must emit a non-zero (DivisionByZero) obligation"
    );
}

#[test]
fn flags_unguarded_windows() {
    let func = slice_method_func(
        "windows",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        vec![],
    );
    assert_eq!(
        nonzero_vc_count(&func),
        1,
        "unguarded `s.windows(n)` must emit a non-zero (DivisionByZero) obligation"
    );
}

#[test]
fn flags_unguarded_chunks_exact() {
    let func = slice_method_func(
        "chunks_exact",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        vec![],
    );
    assert_eq!(
        nonzero_vc_count(&func),
        1,
        "unguarded `s.chunks_exact(n)` must emit a non-zero (DivisionByZero) obligation"
    );
}

#[test]
fn flags_unguarded_swap() {
    // `s.swap(i, j)` PANICS when either index is `>= len`.
    let func = slice_method_func(
        "swap",
        vec![
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
            Operand::Copy(Place::local(3)),
        ],
        vec![],
    );
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck))
        .expect("unguarded `s.swap(i, j)` must emit a SliceBoundsCheck obligation");
    assert!(
        formula_mentions(&vc.formula, "a")
            && formula_mentions(&vc.formula, "b")
            && formula_mentions(&vc.formula, "s__slice_len"),
        "the swap VC must constrain BOTH indices against `s.len()`; formula: {:?}",
        vc.formula
    );
}

#[test]
fn range_family_defining_module_path_emits_slice_bounds_vc() {
    // Current rustc prints the defining-module path
    // `core::ops::range::RangeTo<usize>`, rather than the older public
    // re-export spelling `core::ops::RangeTo`. Exercise the complete
    // production path: operand type recognition, aggregate tracing, and VC
    // construction, including the instantiated ADT-name normalization.
    let range_name = "core::ops::range::RangeTo<usize>";
    let range_ty = Ty::Adt {
        adt_kind: None,
        layout: None,
        variants: Vec::new(),
        name: range_name.into(),
        fields: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "range_to_caller".into(),
        def_path: "test::range_to_caller".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: slice_ref(), name: Some("s".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("end".into()) },
                LocalDecl { index: 3, ty: range_ty, name: Some("range".into()) },
                LocalDecl { index: 4, ty: slice_ref(), name: Some("out".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: range_name.into(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        vec![Operand::Copy(Place::local(2))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "<[u8] as core::ops::index::Index<core::ops::range::RangeTo<usize>>>::index"
                        .into(),
                    args: vec![
                        Operand::Copy(Place::local(1)),
                        Operand::Move(Place::local(3)),
                    ],
                    dest: Place::local(4),
                    target: None,
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

    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck))
        .expect("a defining-module RangeTo index must emit a SliceBoundsCheck VC");
    assert!(
        formula_mentions(&vc.formula, "end") && formula_mentions(&vc.formula, "s__slice_len"),
        "the RangeTo VC must constrain its end against the slice length: {:?}",
        vc.formula
    );
}

// ----- no false positive: trivially-safe / unrelated calls -----

#[test]
fn allows_const_nonzero_chunks() {
    // `s.chunks(4)` — a literal nonzero chunk size is trivially proved safe;
    // no obligation at all (mirrors the divzero const-nonzero skip).
    let func = slice_method_func(
        "chunks",
        vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(4, 64))],
        vec![],
    );
    assert_eq!(
        nonzero_vc_count(&func),
        0,
        "`s.chunks(4)` has a provably-nonzero size and must emit no obligation"
    );
}

#[test]
fn ignores_ordinary_slice_call() {
    // An unrecognized slice method (`s.iter()`) must not produce any
    // bounds/non-zero obligation — the recognizer must NOT broadly fail-close.
    let func = slice_method_func("iter", vec![Operand::Copy(Place::local(1))], vec![]);
    assert_eq!(
        bounds_vc_count(&func) + nonzero_vc_count(&func),
        0,
        "an unrecognized slice method must produce no slice-panic obligation"
    );
}

#[test]
fn ignores_swap_on_non_slice_receiver() {
    // `Ordering::swap`-style: a `swap` whose receiver carries no modeled
    // `__slice_len` (here a plain `usize` receiver) must emit nothing — flagging
    // it would false-FAIL ordinary non-slice code that happens to call `swap`.
    let func = VerifiableFunction {
        name: "nonslice_swap".to_string(),
        def_path: "test::nonslice_swap".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "core::mem::swap".to_string(),
                    args: vec![
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                        Operand::Copy(Place::local(3)),
                    ],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                },
            }],
            arg_count: 3,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert_eq!(
        bounds_vc_count(&func),
        0,
        "`swap` on a receiver with no modeled length must emit no obligation"
    );
}

// ----- guarded: obligation generated but discharged by the conjoined guard -----

#[test]
fn precondition_mid_le_len_carries_into_split_at_vc() {
    // `#[requires(mid <= s.len())] s.split_at(mid)` is safe. The obligation IS
    // generated, but its formula must carry the precondition so the solver
    // discharges it — the safe/buggy distinction without an SMT run.
    let pre = Formula::Le(
        Box::new(Formula::Var("a".into(), Sort::Int)),
        Box::new(Formula::Var("s__slice_len".into(), Sort::Int)),
    );
    let func = slice_method_func(
        "split_at",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        vec![pre],
    );
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck))
        .expect("guarded split_at still generates the obligation (discharged at solve time)");
    assert!(
        formula_mentions(&vc.formula, "a") && formula_mentions(&vc.formula, "s__slice_len"),
        "the split_at VC must reference `mid` and `s.len()` so the precondition \
         `mid <= s.len()` can discharge it; formula: {:?}",
        vc.formula
    );
}

#[test]
fn dominating_nonzero_guard_carries_into_chunks_vc() {
    // `if n != 0 { s.chunks(n) }` lowered to MIR: block 0 switches on `n`; the
    // `n == 0` edge skips the call (block 2), the `otherwise` (`n != 0`) edge
    // reaches the call (block 1). The path-guard map must conjoin `n != 0` onto
    // the call's non-zero VC so the solver discharges it — an unguarded call
    // (the `flags_unguarded_chunks` test) has no such guard and fails.
    let func = VerifiableFunction {
        name: "guarded_chunks".to_string(),
        def_path: "test::guarded_chunks".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: slice_ref(), name: Some("s".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) },
            ],
            blocks: vec![
                // block 0: `switch n { 0 => bb2 (skip), _ => bb1 (call) }`.
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
                // block 1: reached only when `n != 0` — `s.chunks(n)`.
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::slice::<impl [u8]>::chunks".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                // block 2: join / return.
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("guarded chunks still generates the obligation (discharged at solve time)");
    // The dominating `n != 0` SwitchInt guard must reach the VC so the solver
    // proves the failure (`n == 0`) UNSAT on this path.
    assert!(
        formula_mentions(&vc.formula, "n"),
        "the dominating `n != 0` guard must reach the chunks VC; formula: {:?}",
        vc.formula
    );
}

// ----- #7c owned-Vec SCALAR index `v[i]` -----

/// A `Vec<i32>` (owned) ADT receiver type.
fn vec_i32() -> Ty {
    Ty::adt("std::vec::Vec<i32>", vec![])
}

/// `fn(v: Vec<i32>, i: usize) { v[i] }` as a single-block tail call to the
/// generic `Index::index` trait method — the exact lowering of an owned-`Vec`
/// SCALAR index. Receiver `v` is arg 0 (local 1, a `Vec` ADT), scalar index `i`
/// is arg 1 (local 2, a `usize`). No range argument — the scalar sibling of the
/// range-index recognizer.
fn vec_scalar_index_func() -> VerifiableFunction {
    VerifiableFunction {
        name: "vec_caller".to_string(),
        def_path: "test::vec_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: vec_i32(), name: Some("v".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    // The GENERIC trait method path the MIR carries for `v[i]`.
                    func: "core::ops::index::Index::index".to_string(),
                    args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    dest: Place::local(0),
                    target: None,
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

/// An UNGUARDED owned-`Vec` scalar index `v[i]` must emit a `SliceBoundsCheck`
/// obligation relating the index `i` to the container's abstract length — the
/// pre-#7c behavior emitted NOTHING (a vacuous PROVE of a panicking `v[2]`).
#[test]
fn flags_unguarded_vec_scalar_index() {
    let func = vec_scalar_index_func();
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck))
        .expect("unguarded owned-Vec `v[i]` must emit a SliceBoundsCheck obligation");
    // The VC must constrain the scalar index `i` against the container's abstract
    // length — the base `Vec` local's own name (`coll_len_var`), here `v`/`_1`.
    assert!(
        formula_mentions(&vc.formula, "i"),
        "the Vec scalar-index VC must constrain the index `i`; formula: {:?}",
        vc.formula
    );
}

/// A `HashMap` index must NOT get a length-OOB obligation (`HashMap::index`
/// panics on an ABSENT KEY, not a length overrun), but it must ALSO not be a
/// SILENT skip — the former behavior reported `map[absent_key]` as vacuously
/// safe (a panic-freedom false-accept). It surfaces as a visible
/// `UnsupportedMir` (Unknown → fail-closed under `-full`), mirroring an
/// unmodeled `Option::unwrap`.
#[test]
fn hashmap_index_emits_visible_unknown_not_silent() {
    let mut func = vec_scalar_index_func();
    func.body.locals[1].ty = Ty::adt("std::collections::hash::map::HashMap<i32, i32>", vec![]);
    let vcs = generate_vcs(&func);
    assert_eq!(
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).count(),
        0,
        "a HashMap index is a key-presence panic, NOT a length OOB — no SliceBoundsCheck"
    );
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "map-index-key-presence"
        )),
        "a HashMap index must surface a visible UnsupportedMir (never a silent skip); got {:#?}",
        vcs.iter().map(|vc| vc.kind.description()).collect::<Vec<_>>()
    );
}

/// The BTreeMap twin — same key-presence panic, same visible-Unknown handling.
#[test]
fn btreemap_index_emits_visible_unknown() {
    let mut func = vec_scalar_index_func();
    func.body.locals[1].ty =
        Ty::adt("std::collections::btree::map::BTreeMap<i32, i32>", vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "map-index-key-presence"
        )),
        "a BTreeMap index must surface a visible UnsupportedMir; got {:#?}",
        vcs.iter().map(|vc| vc.kind.description()).collect::<Vec<_>>()
    );
}

/// A BORROWED `&Vec<i32>` receiver (the dominant param shape `fn f(v: &Vec, i)`)
/// must ALSO emit the scalar-index bounds obligation: the shared-ref peel in
/// `collection_abstract_len_with_base` resolves `&Vec` to its `Vec` ADT while
/// keeping the base local identity, so the guard tie still connects.
#[test]
fn flags_shared_ref_vec_scalar_index() {
    let mut func = vec_scalar_index_func();
    // Retype the receiver local to `&Vec<i32>` (shared ref).
    func.body.locals[1].ty = Ty::Ref { mutable: false, inner: Box::new(vec_i32()) };
    let vcs = generate_vcs(&func);
    assert_eq!(
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).count(),
        1,
        "a shared `&Vec` scalar index must emit a SliceBoundsCheck obligation"
    );
}

/// SOUNDNESS: a user type `struct MyVec { fn index }` whose ADT name tail is
/// `MyVec` must NOT inherit `Vec` scalar-index semantics — the recognizer keys
/// on the receiver ADT NAME (`is_owned_slice_container_name`, `Vec`-only), so a
/// `MyVec` scalar index gets NO obligation (its `index` panic semantics are its
/// own; a spurious `Vec`-length bound could false-prove/false-refute).
#[test]
fn user_myvec_scalar_index_not_flagged() {
    let mut func = vec_scalar_index_func();
    func.body.locals[1].ty = Ty::adt("mycrate::MyVec", vec![]);
    let vcs = generate_vcs(&func);
    assert_eq!(
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).count(),
        0,
        "a user `MyVec` scalar index must NOT inherit Vec semantics (no obligation)"
    );
}

/// The WRITE idiom `v[i] = x` on a `&mut Vec` param — real MIR shape: a
/// `&mut (*_1)` reborrow temp consumed as `IndexMut::index_mut`'s receiver.
/// Pre-fix this emitted ZERO obligations (the reborrow tripped the coarse
/// mut-borrow gate → recovery declined → silent None-skip): an unguarded OOB
/// write was reported vacuously safe. The length-benign refinement
/// (`local_mut_borrows_may_resize`) must recover the length and emit the
/// `i >= len` obligation.
fn vec_scalar_index_mut_write_func() -> VerifiableFunction {
    VerifiableFunction {
        name: "vec_write".to_string(),
        def_path: "test::vec_write".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(vec_i32()) },
                    name: Some("v".into()),
                },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref { mutable: true, inner: Box::new(vec_i32()) },
                    name: None,
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::Ref {
                        mutable: true,
                        inner: Box::new(Ty::Int { width: 32, signed: true }),
                    },
                    name: None,
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    // `_3 = &mut (*_1)` — the auto-reborrow rustc emits for the
                    // `index_mut` receiver.
                    rvalue: Rvalue::Ref {
                        mutable: true,
                        place: trust_types::Place {
                            local: 1,
                            projections: vec![trust_types::Projection::Deref],
                        },
                    },
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "core::ops::index::IndexMut::index_mut".to_string(),
                    args: vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(2))],
                    dest: Place::local(4),
                    target: None,
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
fn flags_mut_vec_scalar_index_write() {
    let func = vec_scalar_index_mut_write_func();
    let vcs = generate_vcs(&func);
    let vc = vcs.iter().find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).expect(
        "an unguarded `v[i] = x` (IndexMut on a &mut Vec) must emit a \
             SliceBoundsCheck obligation — the pre-fix behavior emitted NOTHING \
             (silent false-accept of an OOB write)",
    );
    assert!(
        formula_mentions(&vc.formula, "i"),
        "the Vec write-index VC must constrain the index `i`; formula: {:?}",
        vc.formula
    );
}

/// SOUNDNESS (the refinement must not over-reach): a genuine RESIZE — the
/// reborrow temp consumed by `Vec::push` — must still decline the length
/// recovery. And per the fail-honest backstop, the recognized-but-declined
/// container index must surface as `UnsupportedMir` (Unknown), never as a
/// bounds VC over a stale length and never as silence.
#[test]
fn resized_vec_scalar_index_fails_honest() {
    let mut func = vec_scalar_index_mut_write_func();
    // Retarget the reborrow's consumer from `index_mut` to `push`: a resize.
    if let Terminator::Call { func: callee, .. } = &mut func.body.blocks[0].terminator {
        *callee = "alloc::vec::Vec::<i32>::push".to_string();
    }
    // Re-add the index as a SECOND block so the scalar-index site still exists.
    func.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Ref {
                mutable: true,
                place: trust_types::Place {
                    local: 1,
                    projections: vec![trust_types::Projection::Deref],
                },
            },
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            func: "core::ops::index::IndexMut::index_mut".to_string(),
            args: vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(2))],
            dest: Place::local(4),
            target: None,
            span: SourceSpan::default(),
            atomic: None,
            is_unsafe_sig: false,
            is_foreign: false,
        },
    });
    let vcs = generate_vcs(&func);
    assert_eq!(
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).count(),
        0,
        "a resized Vec's scalar index must NOT get a bounds VC over a stale length"
    );
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "container-index-unstable-len"
        )),
        "a recognized container index whose length recovery declined must surface \
         as UnsupportedMir (Unknown) — never a silent skip; got {:#?}",
        vcs.iter().map(|vc| vc.kind.description()).collect::<Vec<_>>()
    );
}
