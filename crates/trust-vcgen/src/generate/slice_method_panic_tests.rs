use trust_types::{
    AggregateKind, BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue,
    Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody,
    VerifiableFunction,
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
fn slice_method_func(method: &str, args: Vec<Operand>, pre: Vec<Formula>) -> VerifiableFunction {
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
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(
                        &format!("core::slice::<impl [u8]>::{method}").to_string(),
                    ),
                    is_foreign: false,
                },
            }],
            arg_count: 3,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: pre,
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        variants: Vec::new().into(),
        name: range_name.into(),
        fields: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    };
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
                    func:
                        "<[u8] as core::ops::index::Index<core::ops::range::RangeTo<usize>>>::index"
                            .into(),
                    args: vec![Operand::Copy(Place::local(1)), Operand::Move(Place::local(3))],
                    dest: Place::local(4),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: None,
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
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key("core::mem::swap"),
                    is_foreign: false,
                },
            }],
            arg_count: 3,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::slice::<impl [u8]>::chunks",
                        ),
                        is_foreign: false,
                    },
                },
                // block 2: join / return.
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
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
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(
                        "core::ops::index::Index::index",
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
    func.body.locals[1].ty = Ty::adt("std::collections::btree::map::BTreeMap<i32, i32>", vec![]);
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

/// The extractor's spelling of `v[i] = x` on a `Vec<i32>`: std's own impl, which
/// `local_mut_borrows_may_resize` counts as length-benign (STD-RECEIVER-ANCHOR-1;
/// measured on stage1-w11fix for `Vec<u32>`). This fixture spelled the bare
/// `core::ops::index::IndexMut::index_mut` until 2026-10-04, which names no impl and
/// which the extractor does not emit;
/// `an_index_mut_naming_no_impl_keeps_the_write_fail_honest` keeps it as a negative.
const VEC_I32_INDEX_MUT: &str =
    "<alloc::vec::Vec<i32> as core::ops::index::IndexMut<usize>>::index_mut";

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
                    func: VEC_I32_INDEX_MUT.to_string(),
                    args: vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(2))],
                    dest: Place::local(4),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(VEC_I32_INDEX_MUT),
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
/// Rewrite every `Vec<i32>` ADT local (through references) into `Ty::Seq`, the
/// extractor's rendering of a std `Vec`, so each #7c test can run over both forms.
fn with_seq_receivers(mut func: VerifiableFunction) -> VerifiableFunction {
    fn to_seq(ty: &mut Ty) {
        match ty {
            Ty::Ref { inner, .. } => to_seq(inner),
            Ty::Adt { name, .. } if name == "std::vec::Vec<i32>" => {
                *ty = Ty::Seq { elem: Box::new(Ty::i32()), drop_auth: None };
            }
            _ => {}
        }
    }
    for decl in &mut func.body.locals {
        to_seq(&mut decl.ty);
    }
    func
}

/// The `Seq` twin of `flags_unguarded_vec_scalar_index`. Before `ty_is_owned_vec`, a
/// `Seq` receiver emitted no bounds row at all.
#[test]
fn flags_unguarded_seq_scalar_index() {
    let func = with_seq_receivers(vec_scalar_index_func());
    assert!(matches!(func.body.locals[1].ty, Ty::Seq { .. }));
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck))
        .expect("an unguarded `v[i]` over a Seq receiver must emit a SliceBoundsCheck");
    assert!(formula_mentions(&vc.formula, "i"), "formula: {:?}", vc.formula);
}

#[test]
fn resized_vec_scalar_index_fails_honest() {
    assert_resized_vec_scalar_index_fails_honest(false);
}

/// The `Seq` twin: the fail-honest backstop is what keeps the bridge's un-poisoning
/// index arm sound when the length cannot be recovered.
#[test]
fn resized_seq_scalar_index_fails_honest() {
    assert_resized_vec_scalar_index_fails_honest(true);
}

fn assert_resized_vec_scalar_index_fails_honest(seq: bool) {
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
            func: VEC_I32_INDEX_MUT.to_string(),
            args: vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(2))],
            dest: Place::local(4),
            target: None,
            span: SourceSpan::default(),
            atomic: None,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: crate::sep_engine::tests::fixture_key(VEC_I32_INDEX_MUT),
            is_foreign: false,
        },
    });
    if seq {
        func = with_seq_receivers(func);
        assert!(func.body.locals.iter().any(|d| matches!(&d.ty, Ty::Ref { inner, .. }
            if matches!(inner.as_ref(), Ty::Seq { .. }))
            || matches!(d.ty, Ty::Seq { .. })));
    }
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

/// STD-RECEIVER-ANCHOR-1 (2026-10-04): a `&mut v` consumed by an `index_mut` that
/// cannot be attributed to std's own impl MAY resize `v`. The bare
/// `core::ops::index::IndexMut::index_mut` names no impl (the extractor never emits
/// it), so the write's length is not recovered and it surfaces fail-honest as
/// `container-index-unstable-len`, never as a bounds row over a stale length and
/// never as silence. Before the anchor this spelling counted as benign and the row
/// was a `SliceBoundsCheck`.
#[test]
fn an_index_mut_naming_no_impl_keeps_the_write_fail_honest() {
    let mut func = vec_scalar_index_mut_write_func();
    if let Terminator::Call { func: callee, callee_key, .. } = &mut func.body.blocks[0].terminator {
        *callee = "core::ops::index::IndexMut::index_mut".to_string();
        *callee_key =
            crate::sep_engine::tests::fixture_key("core::ops::index::IndexMut::index_mut");
    }
    let vcs = generate_vcs(&func);
    assert_eq!(
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).count(),
        0,
        "no bounds row over a length the call may have changed"
    );
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "container-index-unstable-len"
        )),
        "the write stays visible as Unknown; got {:#?}",
        vcs.iter().map(|vc| vc.kind.description()).collect::<Vec<_>>()
    );
}

// ----- W4 round 3 (2026-09-29): `str::split_at` charges the char-boundary half -----

/// The key the extractor mints for an authenticated `core::str` inherent.
fn str_split_key(item: trust_types::SysrootItem) -> Option<trust_types::CalleeKey> {
    Some(trust_types::CalleeKey {
        sysroot_item: Some(item),
        krate_is_real_sysroot: true,
        krate_name_is_ambiguous: false,
        stable_crate_id: 0x1973_d11b_2baa_21fa,
        krate_name: "core".to_string(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    })
}

/// `fn(s: &str, a: usize, b: usize) { s.METHOD(..) }` with the callee rendered as
/// the `core::str` inherent. `str` is extracted as `[u8]` (the receiver type is
/// `slice_ref()`), so the callee is the only thing that says "str".
fn str_split_func(
    method: &str,
    args: Vec<Operand>,
    pre: Vec<Formula>,
    key: Option<trust_types::CalleeKey>,
) -> VerifiableFunction {
    let mut func = slice_method_func(method, args, pre);
    if let Terminator::Call { func: callee, callee_key, .. } = &mut func.body.blocks[0].terminator {
        *callee = format!("core::str::<impl str>::{method}");
        *callee_key = key;
    }
    func
}

fn char_boundary_unmodeled_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. } if kind == "str-split-at-char-boundary-unmodeled"
            )
        })
        .count()
}

#[test]
fn str_split_at_unguarded_is_refused_on_the_char_boundary() {
    // `s.split_at(mid)` on a `str` panics mid-char even when `mid <= len`; with
    // no structural boundary credit the row is the fail-closed UnsupportedMir.
    let func = str_split_func(
        "split_at",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        vec![],
        str_split_key(trust_types::SysrootItem::StrSplitAt),
    );
    assert_eq!(char_boundary_unmodeled_count(&func), 1);
    assert_eq!(bounds_vc_count(&func), 0, "the numeric-only row must not stand for a str split");
}

#[test]
fn str_split_at_under_a_length_precondition_is_still_refused() {
    // Adversarial round 2 (m10b/m42/m43): a proof of `mid <= len` is NOT
    // panic-freedom for a `str` split. `#[requires(mid <= s.len())]` must not
    // turn the row into a dischargeable bounds VC.
    let pre = Formula::Le(
        Box::new(Formula::Var("a".into(), Sort::Int)),
        Box::new(Formula::Var("s__slice_len".into(), Sort::Int)),
    );
    let func = str_split_func(
        "split_at",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        vec![pre],
        str_split_key(trust_types::SysrootItem::StrSplitAt),
    );
    assert_eq!(char_boundary_unmodeled_count(&func), 1);
    assert_eq!(bounds_vc_count(&func), 0);
}

#[test]
fn str_split_at_mut_unguarded_is_refused_on_the_char_boundary() {
    let func = str_split_func(
        "split_at_mut",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        vec![],
        str_split_key(trust_types::SysrootItem::StrSplitAtMut),
    );
    assert_eq!(char_boundary_unmodeled_count(&func), 1);
    assert_eq!(bounds_vc_count(&func), 0);
}

#[test]
fn str_split_at_zero_keeps_the_bounds_row() {
    // `0` is always a boundary: the ordinary `0 > len` row, nothing refused.
    let func = str_split_func(
        "split_at",
        vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(0, 64))],
        vec![],
        str_split_key(trust_types::SysrootItem::StrSplitAt),
    );
    assert_eq!(char_boundary_unmodeled_count(&func), 0);
    assert_eq!(bounds_vc_count(&func), 1);
}

/// `fn(s: &str, a: usize, b: usize, other: &str) { let m = PtrMetadata(SRC); s.split_at(m) }`:
/// the shape `rewrite_str_len_calls` leaves for `s.split_at(s.len())` (SRC = `s`), and the
/// same over ANOTHER string's length (SRC = `other`).
fn str_split_at_metadata_func(src: usize) -> VerifiableFunction {
    let mut func = str_split_func(
        "split_at",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(5))],
        vec![],
        str_split_key(trust_types::SysrootItem::StrSplitAt),
    );
    func.body.locals.push(LocalDecl { index: 4, ty: slice_ref(), name: Some("other".into()) });
    func.body.locals.push(LocalDecl { index: 5, ty: Ty::usize(), name: Some("m".into()) });
    func.body.arg_count = 4;
    func.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, Operand::Copy(Place::local(src))),
        span: SourceSpan::default(),
    }];
    func
}

#[test]
fn str_split_at_its_own_length_metadata_keeps_the_bounds_row() {
    // Trust (2026-10-15): `s.split_at(s.len())` after the str-length rewrite. The byte
    // length of the string split is always a boundary: the ordinary row, nothing refused.
    let func = str_split_at_metadata_func(1);
    assert_eq!(char_boundary_unmodeled_count(&func), 0);
    assert_eq!(bounds_vc_count(&func), 1);
}

#[test]
fn str_split_at_another_strings_length_is_refused_on_the_char_boundary() {
    // `s.split_at(other.len())`: `other`'s length need not be a boundary of `s`.
    let func = str_split_at_metadata_func(4);
    assert_eq!(char_boundary_unmodeled_count(&func), 1);
    assert_eq!(bounds_vc_count(&func), 0);
}

#[test]
fn str_split_at_without_a_key_is_refused_by_its_rendered_path() {
    // A producer that mints no key: the `core::str` rendering is a fail-closed
    // stand-in (it can only add the refusal).
    let func = str_split_func(
        "split_at",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        vec![],
        None,
    );
    assert_eq!(char_boundary_unmodeled_count(&func), 1);
}

#[test]
fn slice_split_at_keeps_its_numeric_row() {
    // The `[T]` split has no char boundaries: exactly one bounds row, no refusal
    // (the ordinary sweep's t32 and the panicking-std battery's p06 rely on it).
    let func = slice_method_func(
        "split_at",
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        vec![],
    );
    assert_eq!(char_boundary_unmodeled_count(&func), 0);
    assert_eq!(bounds_vc_count(&func), 1);
}

#[test]
fn only_the_str_split_is_a_str_split() {
    use trust_types::SysrootItem as S;

    use super::callee_is_str_split_at;
    assert!(callee_is_str_split_at(
        "core::str::<impl str>::split_at",
        str_split_key(S::StrSplitAt).as_ref()
    ));
    assert!(callee_is_str_split_at("anything", str_split_key(S::StrSplitAtMut).as_ref()));
    assert!(callee_is_str_split_at("core::str::<impl str>::split_at_mut", None));
    // The slice split — keyed or not — and a same-prefix neighbour that never
    // panics (`split_at_checked` returns `None`).
    assert!(!callee_is_str_split_at("core::slice::<impl [u8]>::split_at", None));
    assert!(!callee_is_str_split_at(
        "core::slice::<impl [u8]>::split_at",
        crate::sep_engine::tests::fixture_key("core::slice::<impl [u8]>::split_at").as_ref()
    ));
    assert!(!callee_is_str_split_at("core::str::<impl str>::split_at_checked", None));
}

// ----- UTF8-CORE-RANGE-INDEX-1 (2026-10-05): the new range API's index types -----
//
// `core::range::{Range, RangeFrom, RangeInclusive, RangeToInclusive}` index a slice or
// a `str` and panic exactly like their `core::ops` namesakes. The ADT names below are
// the extractor's (measured, `-Ztrust-dump=mir-only` on the stage 1 of `dc15b882f6`:
// `"name": "core::range::Range"`, and the aggregate's `args` `core::range::Range<usize>`).
// Before the fix `operand_is_panicking_range` did not see them as ranges, the
// `RangeIndex` arm returned `None`, and the index emitted no row at all.

/// `fn(s: &[u8] /* or &str */, a: usize) -> _ { &s[<ADT> { <field>: a }] }`: the
/// range built by a whole aggregate, then indexed. `callee` is the rendered index
/// method; `str_marker` appends the `::<__trust_str_index>` token the producer
/// stamps on a `str` index.
fn new_range_index_func(adt: &str, field_count: usize, callee: &str) -> VerifiableFunction {
    let range_ty = Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        variants: Vec::new().into(),
        name: adt.into(),
        fields: (0..field_count).map(|i| (format!("f{i}"), Ty::usize())).collect::<Vec<_>>().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    };
    VerifiableFunction {
        name: "new_range_caller".into(),
        def_path: "test::new_range_caller".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: slice_ref(), name: None },
                LocalDecl { index: 1, ty: slice_ref(), name: Some("s".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 3, ty: range_ty, name: Some("r".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: adt.into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            (0..field_count).map(|_| Operand::Copy(Place::local(2))).collect(),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: callee.into(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Move(Place::local(3))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: None,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: slice_ref(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The recorded obligation bodies of the function's `SliceBoundsCheck` rows.
fn slice_bounds_bodies(func: &VerifiableFunction) -> Vec<Formula> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck))
        .map(|vc| vc.obligation.map_or(vc.formula, |o| o.body))
        .collect()
}

/// `panic_calls::RANGE_INDEX_BOUNDS_UNRESOLVED`: the declined row (RANGE-DECLINE) an
/// untraceable range index takes since the class-10 merge (2026-10-08). It was the
/// always-violated `Bool(true)` as a refutable `SliceBoundsCheck`.
const DECLINED_BOUNDS: &str = "slice-range-bounds-unresolved";

/// The rows that charge a range index: `SliceBoundsCheck` rows and the declined
/// `UnsupportedMir` range rows (`slice-range-*`, `str-range-*`).
fn range_charging_rows(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| match &vc.kind {
            VcKind::SliceBoundsCheck => true,
            VcKind::UnsupportedMir { kind, .. } => {
                kind.starts_with("slice-range-") || kind.starts_with("str-range-")
            }
            _ => false,
        })
        .collect()
}

/// Exactly one charging row, and it is the declined `slice-range-bounds-unresolved`
/// row: charged, never refuted on an arbitrary model, never proved.
fn assert_one_declined_range_row(func: &VerifiableFunction, what: &str) {
    let rows = range_charging_rows(func);
    let kinds: Vec<&VcKind> = rows.iter().map(|vc| &vc.kind).collect();
    assert_eq!(rows.len(), 1, "`{what}` must carry exactly one charging row; got {kinds:?}");
    assert!(
        matches!(&rows[0].kind, VcKind::UnsupportedMir { kind, .. } if kind == DECLINED_BOUNDS),
        "`{what}`: no tracer reads the range, so the row is the declined \
         `{DECLINED_BOUNDS}` row; got {kinds:?}"
    );
}

/// No charging row is proved by the in-process solver or certified by the kernel.
fn assert_range_rows_never_proved(func: &VerifiableFunction, what: &str) {
    let rows = range_charging_rows(func);
    assert!(!rows.is_empty(), "`{what}` must carry a charging row");
    let router = crate::test_router::deterministic_test_router();
    for (vc, verdict) in router.verify_all(&rows) {
        assert!(
            !matches!(verdict, trust_types::VerificationResult::Proved { .. }),
            "`{what}`: a charging row must never prove, got {verdict:?}"
        );
        assert!(trust_certify::certify_vc(&vc).is_none(), "`{what}`: a charging row certified");
    }
}

#[test]
fn new_range_index_adt_names_are_recognized_by_exact_path() {
    use super::new_range_index_adt_name as n;
    for (name, family) in [
        ("core::range::Range", "Range"),
        ("core::range::Range<usize>", "Range"),
        ("core::range::RangeFrom", "RangeFrom"),
        ("core::range::RangeFrom<usize>", "RangeFrom"),
        ("core::range::RangeInclusive<usize>", "RangeInclusive"),
        ("core::range::RangeToInclusive<usize>", "RangeToInclusive"),
        ("std::range::Range<usize>", "Range"),
        ("std::range::RangeInclusive", "RangeInclusive"),
    ] {
        assert_eq!(n(name), Some(family), "`{name}`");
        // The yield lanes' shared recognizer is NOT widened: these are
        // `IntoIterator`, not `Iterator`, with their own layouts.
        assert_eq!(super::range_family_adt_name(name), None, "`{name}` must stay out of it");
    }
    for name in [
        // Re-exports of the `core::ops` types: printed by their `core::ops::range::`
        // path, which `range_family_adt_name` owns; `RangeFull` never panics.
        "core::range::RangeTo<usize>",
        "core::range::RangeFull",
        "core::range::legacy::Range<usize>",
        // The new API's iterators are not index types.
        "core::range::RangeIter<usize>",
        "core::range::iter::RangeIter<usize>",
        // Look-alikes: a user module, a suffix, an impersonator crate.
        "mycrate::range::Range<usize>",
        "range::Range",
        "mycrate::core::range::Range<usize>",
        "core::range::RangeFromLookalike<usize>",
        "__trust_crate@0123456789abcdef::core::range::Range<usize>",
        // The legacy type itself belongs to the other recognizer.
        "core::ops::range::Range<usize>",
    ] {
        assert_eq!(n(name), None, "`{name}` is not a new-range index type");
    }
}

#[test]
fn a_new_range_slice_index_is_charged_fail_closed() {
    // Before the fix: no `SliceBoundsCheck` row at all (the `RangeIndex` arm saw
    // no panicking range and returned `None`). Until the class-10 merge
    // (RANGE-DECLINE, 2026-10-08) the row was the always-violated `Bool(true)`.
    for (adt, fields, callee) in [
        (
            "core::range::Range",
            2,
            "<[u8] as core::ops::index::Index<core::range::Range<usize>>>::index",
        ),
        (
            "core::range::RangeFrom",
            1,
            "<[u8] as core::ops::index::Index<core::range::RangeFrom<usize>>>::index",
        ),
        (
            "core::range::RangeInclusive",
            2,
            "<[u8] as core::ops::index::Index<core::range::RangeInclusive<usize>>>::index",
        ),
        (
            "core::range::RangeToInclusive",
            1,
            "<[u8] as core::ops::index::Index<core::range::RangeToInclusive<usize>>>::index",
        ),
        (
            "core::range::RangeFrom",
            1,
            "<str as core::ops::index::Index<core::range::RangeFrom<usize>>>::index::<__trust_str_index>",
        ),
        (
            "core::range::Range",
            2,
            "<str as core::ops::index::IndexMut<core::range::Range<usize>>>::index_mut::<__trust_str_index>",
        ),
    ] {
        let func = new_range_index_func(adt, fields, callee);
        // No tracer reads the new layouts, so it takes the untraceable-range arm.
        assert_one_declined_range_row(&func, callee);
        assert!(slice_bounds_bodies(&func).is_empty(), "`{callee}`: no refutable bounds row");
    }
}

#[test]
fn a_new_range_index_is_never_proved() {
    // What the row means downstream: it is never proved or certified, so the strict
    // (default) policy refuses the build — an Unknown L0 row with no runtime fallback
    // is fatal there, as the refuted row was (a guard cannot discharge it either).
    let func = new_range_index_func(
        "core::range::Range",
        2,
        "<[u8] as core::ops::index::Index<core::range::Range<usize>>>::index",
    );
    assert_range_rows_never_proved(&func, "core::range::Range index");
}

#[test]
fn a_user_range_type_named_like_the_new_api_adds_no_row() {
    // EXACT-PATH gate: a user type whose path merely ends in `range::Range` is not
    // std's (and `SliceIndex` is sealed, so it cannot index a slice anyway).
    let func = new_range_index_func(
        "mycrate::range::Range",
        2,
        "<mycrate::Buf as core::ops::index::Index<mycrate::range::Range>>::index",
    );
    assert!(slice_bounds_bodies(&func).is_empty());
}

#[test]
fn the_legacy_range_index_keeps_its_precise_row() {
    // Control: the `core::ops` twin is traced and gets the exact `a > len` row,
    // not the fail-close the new types take.
    let func = new_range_index_func(
        "core::ops::range::RangeFrom",
        1,
        "<[u8] as core::ops::index::Index<core::ops::range::RangeFrom<usize>>>::index",
    );
    let bodies = slice_bounds_bodies(&func);
    assert_eq!(bodies.len(), 1);
    assert_ne!(bodies[0], Formula::Bool(true));
    assert!(formula_mentions(&bodies[0], "s__slice_len"), "{:?}", bodies[0]);
}

// ----- CONST-RANGE-INDEX-1 (2026-10-06): a range that reaches the index as a constant -----
//
// `const R: core::range::RangeInclusive<usize> = …; &a[R]`, `&s[const { … }]`,
// `const Q: core::ops::Range<usize> = 0..5; &v[Q]`, and a body GVN folds to a constant
// under `-Copt-level=3 -Zmir-opt-level=2` pass the range as `Operand::Constant(
// OpaqueConst)`, which has no operand type. The callee spellings below are the
// producer's, measured with `-Ztrust-dump=mir-only` on the stage 1 of `0ac7a96d9f`.
// Before the fix the `RangeIndex` arm saw no panicking range and emitted no row.

/// `fn(s: &[u8]) -> _ { CALLEE(args) }`, one block, `args` as given (local 1 is `s`).
fn const_range_index_func(callee: &str, args: Vec<Operand>) -> VerifiableFunction {
    VerifiableFunction {
        name: "const_range_caller".into(),
        def_path: "test::const_range_caller".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: slice_ref(), name: None },
                LocalDecl { index: 1, ty: slice_ref(), name: Some("s".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: callee.into(),
                        args,
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: None,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: slice_ref(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn index_with_const(callee: &str) -> VerifiableFunction {
    const_range_index_func(
        callee,
        vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::opaque_const())],
    )
}

#[test]
fn the_callee_instantiation_names_the_range_argument() {
    use super::{CalleeRangeIndex as C, callee_panicking_range_index as c};
    let index = C { range_arg: 1, receiver_is_str: false };
    for callee in [
        "<[u8] as core::ops::index::Index<core::range::Range<usize>>>::index",
        "<[u8; 3] as core::ops::index::Index<core::range::RangeInclusive<usize>>>::index",
        "<alloc::vec::Vec<u8> as core::ops::index::Index<core::ops::range::Range<usize>>>::index",
        "<alloc::vec::Vec<u8> as core::ops::index::IndexMut<core::ops::range::RangeTo<usize>>>::index_mut",
        "<[u8] as core::ops::index::IndexMut<core::ops::range::RangeInclusive<usize>>>::index_mut",
        "<alloc::string::String as core::ops::index::Index<core::ops::range::RangeToInclusive<usize>>>::index",
        "<[u8] as core::ops::index::Index<(core::ops::range::Bound<usize>, core::ops::range::Bound<usize>)>>::index",
    ] {
        assert_eq!(c(callee), Some(index), "`{callee}`");
    }
    let str_index = C { range_arg: 1, receiver_is_str: true };
    for callee in [
        "<str as core::ops::index::Index<core::range::RangeFrom<usize>>>::index::<__trust_str_index>",
        "<str as core::ops::index::IndexMut<core::range::RangeToInclusive<usize>>>::index_mut::<__trust_str_index>",
    ] {
        assert_eq!(c(callee), Some(str_index), "`{callee}`");
    }
    // The inlined form: the range is Self and argument 0; `SliceIndex<str>` says `str`.
    assert_eq!(
        c("<core::range::Range<usize> as core::slice::index::SliceIndex<str>>::index_mut"),
        Some(C { range_arg: 0, receiver_is_str: true })
    );
    assert_eq!(
        c(
            "<core::ops::range::RangeInclusive<usize> as core::slice::index::SliceIndex<[u8]>>::index"
        ),
        Some(C { range_arg: 0, receiver_is_str: false })
    );
    for callee in [
        // `RangeFull` never panics; a scalar index is not a range.
        "<[u8] as core::ops::index::Index<core::ops::range::RangeFull>>::index",
        "<alloc::vec::Vec<u8> as core::ops::index::Index<usize>>::index",
        // A map keyed by a range takes it by reference.
        "<std::collections::HashMap<core::ops::range::Range<usize>, u8> as core::ops::index::Index<&core::ops::range::Range<usize>>>::index",
        // Total methods, a user trait, a user range type, an unqualified path.
        "<core::ops::range::Range<usize> as core::slice::index::SliceIndex<[u8]>>::get",
        "<mycrate::Buf as mycrate::Index<core::ops::range::Range<usize>>>::index",
        "<mycrate::Buf as core::ops::index::Index<mycrate::range::Range>>::index",
        "core::ops::index::Index::index",
        "<[u8] as core::ops::index::Index<(core::ops::range::Bound<usize>, mycrate::Bound)>>::index",
    ] {
        assert_eq!(c(callee), None, "`{callee}` names no panicking range index");
    }
}

#[test]
fn a_constant_range_index_is_charged_fail_closed() {
    // Before the fix: no `SliceBoundsCheck` row at all for any of these.
    for callee in [
        "<[u8] as core::ops::index::Index<core::range::Range<usize>>>::index",
        "<[u8; 3] as core::ops::index::Index<core::range::RangeInclusive<usize>>>::index",
        "<str as core::ops::index::Index<core::range::RangeFrom<usize>>>::index::<__trust_str_index>",
        "<[u8] as core::ops::index::Index<core::ops::range::Range<usize>>>::index",
        "<str as core::ops::index::Index<core::ops::range::RangeFrom<usize>>>::index::<__trust_str_index>",
        "<[u8] as core::ops::index::IndexMut<core::ops::range::RangeInclusive<usize>>>::index_mut",
        "<[u8] as core::ops::index::Index<(core::ops::range::Bound<usize>, core::ops::range::Bound<usize>)>>::index",
    ] {
        // A constant range is untraceable: the declined row (it was the
        // always-violated `Bool(true)` until the class-10 merge, RANGE-DECLINE).
        assert_one_declined_range_row(&index_with_const(callee), callee);
    }
    // The GVN-folded inlined form: range first, receiver second.
    let folded = const_range_index_func(
        "<core::range::Range<usize> as core::slice::index::SliceIndex<str>>::index_mut",
        vec![Operand::Constant(ConstValue::opaque_const()), Operand::Move(Place::local(1))],
    );
    assert_one_declined_range_row(&folded, "the GVN-folded `SliceIndex<str>::index_mut`");
}

#[test]
fn a_constant_range_index_is_never_proved() {
    let func = index_with_const(
        "<[u8; 3] as core::ops::index::Index<core::range::RangeInclusive<usize>>>::index",
    );
    assert_range_rows_never_proved(&func, "constant RangeInclusive index");
}

#[test]
fn a_constant_full_range_or_user_index_adds_no_row() {
    // Controls: `..` never panics (MIR passes it as a bare unit constant), and a
    // user `Index` impl over a user range type is not std's.
    let full = const_range_index_func(
        "<[u8] as core::ops::index::Index<core::ops::range::RangeFull>>::index",
        vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Unit)],
    );
    assert!(slice_bounds_bodies(&full).is_empty());
    let user =
        index_with_const("<mycrate::Buf as core::ops::index::Index<mycrate::range::Range>>::index");
    assert!(slice_bounds_bodies(&user).is_empty());
}

// ----- AGG-BOOL-TWIN-SORT-1 (2026-10-06): a `bool` field in an aggregate def -----
//
// Under `-Zinline-mir=yes`, `let r = black_box(0usize..=4); &a[r]` reaches the
// caller as `_3 = core::ops::RangeInclusive { start: 0, end: 4, exhausted: false };
// _2 = black_box(move _3); <core::ops::RangeInclusive<usize> as SliceIndex<[u8]>>::
// index(copy _2, copy _1)` (measured, `-Ztrust-dump=mir-only` on the stage 1 of
// `0ac7a96d9f`). The aggregate's downcast twin `_3@0.2` (a struct field's twin, whose
// type does not resolve) was an `Int` var equated to `Bool(false)`; the VC was
// sort-invalid, in-process ay declined it, and the always-violated row came back
// `Unknown` (reported runtime-checked) instead of `Failed`.

fn inclusive_range_ty() -> Ty {
    Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: "core::ops::range::RangeInclusive".into(),
        fields: vec![
            ("start".to_string(), Ty::usize()),
            ("end".to_string(), Ty::usize()),
            ("exhausted".to_string(), Ty::bool_ty()),
        ]
        .into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    }
}

fn black_boxed_inclusive_index_func() -> VerifiableFunction {
    let call = |func: &str, args: Vec<Operand>, dest: usize, target: usize| Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: func.into(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        is_foreign: false,
    };
    VerifiableFunction {
        name: "bb_incl".into(),
        def_path: "test::bb_incl".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: slice_ref(), name: None },
                LocalDecl { index: 1, ty: slice_ref(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: inclusive_range_ty(), name: Some("r".into()) },
                LocalDecl { index: 3, ty: inclusive_range_ty(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "core::ops::range::RangeInclusive".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![
                                Operand::Constant(ConstValue::Uint(0, 64)),
                                Operand::Constant(ConstValue::Uint(4, 64)),
                                Operand::Constant(ConstValue::Bool(false)),
                            ],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: call(
                        "core::intrinsics::black_box::<core::ops::range::RangeInclusive<usize>>",
                        vec![Operand::Move(Place::local(3))],
                        2,
                        1,
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: call(
                        "<core::ops::range::RangeInclusive<usize> as core::slice::index::SliceIndex<[u8]>>::index",
                        vec![Operand::Copy(Place::local(2)), Operand::Copy(Place::local(1))],
                        0,
                        2,
                    ),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: slice_ref(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
fn a_bool_field_aggregate_def_keeps_the_bounds_row_well_sorted_and_never_proved() {
    // The untraceable inclusive range (through `black_box`) is the declined row since
    // the class-10 merge (RANGE-DECLINE); every charging row stays sort-valid and is
    // never proved.
    let func = black_boxed_inclusive_index_func();
    let vcs = range_charging_rows(&func);
    assert!(!vcs.is_empty(), "the untraceable inclusive range index must carry a bounds row");
    for vc in &vcs {
        assert_eq!(
            trust_types::check_formula_sort(&vc.formula),
            Ok(Sort::Bool),
            "the bounds row must be sort-valid (a `bool` field equated to an `Int` var is \
             not): {:?}",
            vc.formula
        );
    }
    assert_range_rows_never_proved(&func, "black-boxed RangeInclusive index");
}

/// ARGS-FINGERPRINT-READ-1 (2026-10-07): `collection_range::method_generic_args`
/// reads the method's own turbofish past the duplicate-crate-name argument
/// fingerprint `::<__trust_args@HEX>`, and ONLY past its exact grammar, for a VALUE
/// read (`as_chunks::<4>`). Round 2: a TYPE-PATH read (`RangeFull`) declines on a
/// tagged callee — the producer writes the tag exactly when an argument names a
/// crate whose name does not identify it, so `core::ops::range::RangeFull` may be
/// a crate built `--crate-name core` (review measurement: such a `RangeFull` with
/// `start_bound = Included(&1000)` panics in `drain`). The real `RangeFull` in a
/// graph duplicating some OTHER name is untagged (real-MIR pins:
/// `tests/args_fingerprint_dupname_realmir.rs`).
#[test]
fn method_generic_args_read_past_the_argument_fingerprint_only() {
    use super::SliceMethodPanic::{CollectionRange, ConstChunkSize};
    let full = |callee: &str| {
        matches!(
            super::collection_range::collection_method_panic(callee),
            Some(CollectionRange { range_is_full: true, .. })
        )
    };
    let nonzero = |callee: &str| {
        matches!(
            super::collection_range::collection_method_panic(callee),
            Some(ConstChunkSize { nonzero: true })
        )
    };
    let tag = trust_types::render_trailing_args_fingerprint(0x881f_58e8_618f_face, 0x9bc2);
    const SPLICE: &str = "alloc::vec::Vec::<u32>::splice::<core::ops::range::RangeFull, [u32; 2]>";
    const RANGE: &str = "alloc::collections::vec_deque::VecDeque::<u32>::range\
                         ::<core::ops::range::RangeFull>";
    // `Vec::drain` reads the same `range_generic_is_full` through
    // `std_vec_drain_range_cannot_panic` (real-MIR pin: the forged-`core` fixture);
    // `String::drain` is this recognizer's arm.
    const DRAIN: &str = "alloc::string::String::drain::<core::ops::range::RangeFull>";
    const CHUNKS4: &str = "core::slice::<impl [u8]>::as_chunks::<4>";
    // Controls: the untagged spelling.
    assert!(full(SPLICE) && full(RANGE) && full(DRAIN) && nonzero(CHUNKS4));
    // POSITIVE: a VALUE read sees past the tag.
    assert!(nonzero(&format!("{CHUNKS4}{tag}")), "`::<4>` behind the tag");
    // NEGATIVE (round 2): a TYPE-PATH read declines on a tagged callee — the shape
    // the measured forged-`core` `RangeFull` renders.
    assert!(!full(&format!("{DRAIN}{tag}")), "a forged `core` RangeFull renders this");
    assert!(!full(&format!("{SPLICE}{tag}")));
    assert!(!full(&format!("{RANGE}{tag}")));
    // ...and anywhere in the path, not only trailing.
    assert!(!full(&format!("{DRAIN}{tag}::<__trust_str_index>")));
    // NEGATIVE: a non-full range and a zero const stay charged behind the tag.
    assert!(!full(&format!(
        "alloc::vec::Vec::<u32>::splice::<core::ops::range::RangeTo<usize>, [u32; 2]>{tag}"
    )));
    assert!(!nonzero(&format!("core::slice::<impl [u8]>::as_chunks::<0>{tag}")));
    // NEGATIVE: a lookalike tag is not stripped, so the reader sees it and declines
    // the carve-out (fail-closed), exactly as before the fix.
    for bad in [
        "::<__trust_args@881f58e8618fface>",
        "::<__trust_args@881F58E8618FFACE0000000000009BC2>",
        "::<__trust_args>",
    ] {
        assert!(!full(&format!("{SPLICE}{bad}")), "{bad}");
        assert!(!nonzero(&format!("{CHUNKS4}{bad}")), "{bad}");
    }
}

// ----- SLICE-ZERO-SIZE-NAME-1 (2026-10-11): the row is core's, not the name's -----
//
// `slice_method_panic` read the last path segment alone, so a USER method merely
// NAMED `windows`, `chunks*`, `rchunks*`, `split_at*` or `swap` was charged core's
// zero-size or bounds row over its own arguments and REFUTED (`[divzero] FAILED;
// counterexample: k = 0`, `[slice] FAILED`), measured on the stage 1 of `1213387e6d`
// (`scratchpad/scout24/szn/{ns2,ns3,sib}.rs`). The first eight spellings below are the
// ones rustc rendered for those calls (`-Ztrust-dump=mir-only`); the real-MIR twin is
// `tests/user_namesake_slice_realmir.rs`.

/// Rendered callees of user methods that merely share a name with core's panicking
/// slice methods. None of them is core's; none may mint core's row.
const USER_SLICE_NAMESAKES: [&str; 20] = [
    "ns2::Grid::windows",
    "ns2::Grid::chunks",
    "ns2::Grid::rchunks_exact",
    "<ns3::G2 as ns3::Tiles>::chunks_exact",
    "ns3::W::<[T]>::windows",
    "<[u8] as sib::Tr>::swap",
    "<[u8] as sib::Tr>::split_at",
    "<[u8] as sib::Tr>::windows",
    // The remaining tails of the three arms, on a user owner.
    "mycrate::Buf::split_at_mut",
    "mycrate::Buf::chunks_mut",
    "mycrate::Buf::chunks_exact_mut",
    "mycrate::Buf::rchunks",
    "mycrate::Buf::rchunks_mut",
    "mycrate::Buf::rchunks_exact_mut",
    // A user trait implemented FOR a std type is the user's method.
    "<alloc::vec::Vec<u8> as mycrate::Tiles>::windows",
    // A user module path that merely LOOKS like core's: the root is anchored.
    "mycore::slice::<impl [u8]>::windows",
    // A stamp is read past ONCE, and only when well formed (STAMPED-CORE-MINT-1's
    // rule, as `divzero_call` applies it): a stamped user path, a second leading
    // stamp, or a short id mints nothing.
    "__trust_crate@0123456789abcdef::mycrate::Grid::windows",
    "__trust_crate@0123456789abcdef::__trust_crate@0123456789abcdef::core::slice::<impl [u8]>::windows",
    "__trust_crate@0123456789abcde::core::slice::<impl [u8]>::swap",
    "__trust_crate@0123456789abcdef::mycrate::Buf::split_at",
];

/// Core's own panicking slice methods, as rustc renders them, with or without a
/// leading extractor stamp (the genuine core is stamped whenever a second crate named
/// `core` is in the graph, or under `-Zbuild-std`).
const CORE_SLICE_CALLS: [&str; 17] = [
    "core::slice::<impl [u8]>::windows",
    "core::slice::<impl [u8]>::chunks",
    "core::slice::<impl [u8]>::chunks_mut",
    "core::slice::<impl [u8]>::chunks_exact",
    "core::slice::<impl [u8]>::chunks_exact_mut",
    "core::slice::<impl [u8]>::rchunks",
    "core::slice::<impl [u8]>::rchunks_mut",
    "core::slice::<impl [u8]>::rchunks_exact",
    "core::slice::<impl [u8]>::rchunks_exact_mut",
    "core::slice::<impl [u8]>::split_at",
    "core::slice::<impl [u8]>::split_at_mut",
    "core::slice::<impl [u8]>::swap",
    "core::slice::<impl [T]>::chunks_exact",
    "__trust_crate@0123456789abcdef::core::slice::<impl [u8]>::windows",
    "__trust_crate@414739228a72f04f::core::slice::<impl [u8]>::split_at",
    "__trust_crate@414739228a72f04f::core::slice::<impl [u8]>::swap",
    // Core's method with a stamp INSIDE its instantiation: a fn-item element type
    // renders its def path through the stamping renderer (the deque tests pin the
    // same element spelling). See `INNER_STAMP_SWAP`.
    INNER_STAMP_SWAP,
];

/// `a.swap(i, j)` over `a: [Id; 3]`, `Id` the tuple-struct constructor of a crate
/// the graph does not authenticate: core's `swap`, with a stamp in its element type.
const INNER_STAMP_SWAP: &str = "core::slice::<impl [fn(u32) -> \
     __trust_crate@0123456789abcdef::alloc::Id {__trust_crate@0123456789abcdef::alloc::Id}]>::swap";

/// `callee(s, a[, b])` over `s: &[u8]`, spelled and keyed as given: the shape
/// [`slice_method_func`] builds, so every arm's body has the slice length it reads.
fn named_slice_call(callee: &str, key: Option<trust_types::CalleeKey>) -> VerifiableFunction {
    let mut args = vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))];
    if super::alloc_bounds::method_tail(callee) == "swap" {
        args.push(Operand::Copy(Place::local(3)));
    }
    let mut func = slice_method_func("windows", args, vec![]);
    let Terminator::Call { func: name, callee_key, .. } = &mut func.body.blocks[0].terminator
    else {
        unreachable!("slice_method_func builds one call block")
    };
    *name = callee.to_string();
    *callee_key = key;
    func
}

/// Rows of the three tail arms' kinds (`split_at`/`swap`: `SliceBoundsCheck`;
/// `chunks*`/`windows`: `DivisionByZero`).
fn slice_tail_row_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::DivisionByZero))
        .count()
}

/// FAILS BEFORE: the tail-only recognizer answered `Some` for every spelling here and
/// `generate_vcs` emitted one row for each.
#[test]
fn a_user_slice_namesake_mints_no_row() {
    use super::panic_calls::slice_method_panic;
    for callee in USER_SLICE_NAMESAKES {
        assert!(
            slice_method_panic(callee).is_none(),
            "`{callee}` is not core's slice method; it owes none of core's rows"
        );
        // End to end, keyless and with the user-crate key the extractor mints.
        for key in [None, crate::sep_engine::tests::fixture_key(callee)] {
            let func = named_slice_call(callee, key.clone());
            assert_eq!(
                slice_tail_row_count(&func),
                0,
                "`{callee}` (key {key:?}): no row through `generate_vcs`"
            );
        }
    }
}

/// Core's methods keep exactly one row, with no `callee_key` at all (the gate is
/// keyless on purpose: a missing key must not drop a refutation row).
#[test]
fn cores_slice_methods_keep_their_row_keyless() {
    use super::panic_calls::slice_method_panic;
    for callee in CORE_SLICE_CALLS {
        assert!(slice_method_panic(callee).is_some(), "`{callee}` keeps core's row");
        for key in [None, crate::sep_engine::tests::fixture_key(callee)] {
            let func = named_slice_call(callee, key.clone());
            assert_eq!(
                slice_tail_row_count(&func),
                1,
                "`{callee}` (key {key:?}): one row through `generate_vcs`"
            );
        }
    }
}

/// Why the gate reads the ROOT and not `path_root_is_authenticated_sysroot_crate`:
/// that predicate refuses a stamp anywhere, so it would answer `false` for core's own
/// `swap` over a stamped element type and drop the row (a silent pass of an
/// out-of-range swap). Planted premise first, so a change to the predicate is loud.
#[test]
fn a_stamp_inside_cores_instantiation_keeps_the_row() {
    assert!(
        !trust_types::path_root_is_authenticated_sysroot_crate(INNER_STAMP_SWAP),
        "planted premise gone: the authenticated-root predicate now accepts the \
         inner-stamped spelling, so this test proves nothing"
    );
    assert!(super::panic_calls::slice_method_panic(INNER_STAMP_SWAP).is_some());
    assert_eq!(slice_tail_row_count(&named_slice_call(INNER_STAMP_SWAP, None)), 1);
    // A generic callee in a graph with a duplicate crate name carries the trailing
    // `::<__trust_args@…>` identity tag (`trust_types::args_fingerprint`); the root
    // still decides, for core's method and a user namesake alike.
    let tag = trust_types::render_trailing_args_fingerprint(0x881f_58e8_618f_face, 0x9bc2);
    let core_tagged = format!("core::slice::<impl [dup::T]>::windows{tag}");
    assert!(super::panic_calls::slice_method_panic(&core_tagged).is_some(), "{core_tagged}");
    assert_eq!(slice_tail_row_count(&named_slice_call(&core_tagged, None)), 1);
    let user_tagged = format!("mycrate::W::<[dup::T]>::windows{tag}");
    assert!(super::panic_calls::slice_method_panic(&user_tagged).is_none(), "{user_tagged}");
    assert_eq!(slice_tail_row_count(&named_slice_call(&user_tagged, None)), 0);
}

/// The deny-list twin answers exactly as the old tail-only recognizer did, for the
/// user namesakes and core's methods alike: `callee_has_call_site_panic_family` reads
/// it, and there a `Some` only withholds the vanilla admission of a sysroot fn item.
#[test]
fn the_slice_name_only_twin_keeps_the_deny_list_answer() {
    use super::panic_calls::{slice_method_panic, slice_method_panic_name_only};
    for callee in USER_SLICE_NAMESAKES.iter().chain(CORE_SLICE_CALLS.iter()) {
        let tail = super::alloc_bounds::method_tail(callee);
        let twin = slice_method_panic_name_only(callee);
        let expected = match tail {
            "split_at" | "split_at_mut" => {
                matches!(twin, Some(super::SliceMethodPanic::SplitAt { mid_idx: 1 }))
            }
            "swap" => {
                matches!(twin, Some(super::SliceMethodPanic::SwapIndices { i_idx: 1, j_idx: 2 }))
            }
            _ => matches!(twin, Some(super::SliceMethodPanic::NonZeroArg { n_idx: 1 })),
        };
        assert!(expected, "`{callee}`: the twin keeps the tail-only answer");
        assert!(super::callee_has_call_site_panic_family(callee), "`{callee}`: deny-list answer");
        // The minting view is never wider than its twin.
        if slice_method_panic(callee).is_some() {
            assert!(twin.is_some(), "`{callee}`");
        }
    }
}
