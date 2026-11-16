//! TINV-18 correction (2026-10-06): the dest-only call arm of
//! `terminator_def_names_structured` still havocs every name a callee can reach
//! WITHOUT an argument (`path_defs::escape_havoc`). After three review rounds each
//! found a channel the fine-grained exposure analysis missed, the rule is coarse: the
//! arm havocs the whole-function list except the names of a protected, pointer-free,
//! `Unpin` `&mut` PARAMETER that never leaves the body
//! (`path_defs::protected_private_mut_param`; since the P1 precision widening,
//! 2026-10-06, "pointer-free" admits shared references to pointer-free `Freeze` data,
//! the `b: &[u8]` of P1's `Parser`). A stack local is exempt only when it never enters the list at all (never `&mut`/`&raw` borrowed, no pointer in its type).
//!
//! Each body mirrors the MIR of a real program (the UI twins are
//! `tests/ui/trust/call_havoc_escape/*.rs`): the call under test is the terminator of
//! the LAST block, and the assertions read its kill list.

use trust_types::{
    AdtKind, BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::terminator_def_names;

fn u8_ty() -> Ty {
    Ty::Int { width: 8, signed: false }
}

fn usize_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn shared(t: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(t) }
}

fn unique(t: Ty) -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(t) }
}

fn byte_slice_ref() -> Ty {
    shared(Ty::Slice { elem: Box::new(u8_ty()) })
}

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn call(callee: &str, args: Vec<Operand>, dest: usize, next: usize) -> Terminator {
    call_with(callee, args, dest, next, false)
}

fn call_with(
    callee: &str,
    args: Vec<Operand>,
    dest: usize,
    next: usize,
    foreign: bool,
) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: callee.into(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(next)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(callee),
        is_foreign: foreign,
    }
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn body(
    locals: Vec<(Ty, Option<&str>)>,
    arg_count: usize,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "test::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, (ty, name))| LocalDecl { index, ty, name: name.map(Into::into) })
                .collect(),
            blocks,
            arg_count,
            return_ty: u8_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The kill list of the last block's terminator (the call under test).
fn kills(func: &VerifiableFunction) -> Vec<String> {
    terminator_def_names(func, func.body.blocks.last().expect("a block"))
}

fn kills_name(func: &VerifiableFunction, name: &str) -> bool {
    kills(func).iter().any(|n| n == name)
}

fn adt(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
    Ty::Adt {
        adt_kind: Some(AdtKind::Struct),
        layout: None,
        variants: vec![].into(),
        name: name.into(),
        fields: fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect::<Vec<_>>().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// `fn f(s: <param_ty>) -> u8 { if (*s).0 < 50 { poke(); (*s).0 + 200 } else { 0 } }`:
/// `_1 s` is the only parameter, `_2` reads the guarded field, `poke()` is nullary.
fn lone_param(param_ty: Ty) -> VerifiableFunction {
    body(
        vec![(u8_ty(), Some("ret")), (param_ty, Some("s")), (u8_ty(), None), (Ty::Unit, None)],
        1,
        vec![
            block(
                0,
                vec![assign(
                    2,
                    Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Field(0)],
                    })),
                )],
                Terminator::Goto(BlockId(1)),
            ),
            block(1, vec![], call("test::poke", vec![], 3, 2)),
        ],
    )
}

/// `fn f(buf: &[u8]) -> u8 { let p = gptr(); if *p < 50 { poke(buf) / poke(); *p + 200 } }`:
/// `_1 buf`, `_2 p: *mut u8` (a call destination: no `&raw`/cast in `f`), `_3` the
/// call's `usize`/unit result.
fn raw_pointer_from_a_callee(poke_args: Vec<Operand>) -> VerifiableFunction {
    body(
        vec![
            (u8_ty(), Some("ret")),
            (byte_slice_ref(), Some("buf")),
            (Ty::RawPtr { mutable: true, pointee: Box::new(u8_ty()) }, Some("p")),
            (usize_ty(), None),
            (u8_ty(), None),
        ],
        1,
        vec![
            block(0, vec![], call("test::gptr", vec![], 2, 1)),
            block(
                1,
                vec![assign(
                    4,
                    Rvalue::Use(Operand::Copy(Place {
                        local: 2,
                        projections: vec![Projection::Deref],
                    })),
                )],
                call("test::poke", poke_args, 3, 2),
            ),
        ],
    )
}

#[test]
fn a_raw_pointer_from_a_callee_is_havocked_across_a_no_write_call() {
    // Shape (1): `poke(buf)` writes `G` through the static; `p*` must not survive.
    let func = raw_pointer_from_a_callee(vec![Operand::Copy(Place::local(1))]);
    assert!(kills_name(&func, "p"), "{:?}", kills(&func));
}

#[test]
fn a_raw_pointer_from_a_callee_is_havocked_across_a_nullary_call() {
    // The pre-TINV-18 hole: `all` over no arguments is vacuously true.
    let func = raw_pointer_from_a_callee(vec![]);
    assert!(kills_name(&func, "p"), "{:?}", kills(&func));
    // And over scalar arguments.
    let func = raw_pointer_from_a_callee(vec![Operand::Constant(ConstValue::Uint(7, 8))]);
    assert!(kills_name(&func, "p"), "{:?}", kills(&func));
}

/// `fn f(buf: &[u8]) -> u8 { let mut x = 0; stash(&mut x); if x < 50 { poke(..); x + 200 } }`:
/// `_1 buf`, `_2 x: u8`, `_3 = &mut x` handed to `stash` in block 0, `_4`/`_5` results.
/// With `stash = false` the borrow is only written through in `f` (`*_3 = 7`).
fn stashed_local(poke_args: Vec<Operand>, stash: bool) -> VerifiableFunction {
    let first = if stash {
        block(
            0,
            vec![assign(3, Rvalue::Ref { mutable: true, place: Place::local(2) })],
            call("test::stash", vec![Operand::Move(Place::local(3))], 4, 1),
        )
    } else {
        block(
            0,
            vec![
                assign(3, Rvalue::Ref { mutable: true, place: Place::local(2) }),
                Statement::Assign {
                    place: Place { local: 3, projections: vec![Projection::Deref] },
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8))),
                    span: SourceSpan::default(),
                },
            ],
            Terminator::Goto(BlockId(1)),
        )
    };
    body(
        vec![
            (u8_ty(), Some("ret")),
            (byte_slice_ref(), Some("buf")),
            (u8_ty(), Some("x")),
            (unique(u8_ty()), None),
            (Ty::Unit, None),
            (usize_ty(), None),
        ],
        1,
        vec![first, block(1, vec![], call("test::poke", poke_args, 5, 2))],
    )
}

#[test]
fn a_local_whose_mut_borrow_reached_an_earlier_call_is_havocked() {
    // Shape (2): `stash(&mut x)` may keep a raw child of the borrow in a global.
    let func = stashed_local(vec![Operand::Copy(Place::local(1))], true);
    assert!(kills_name(&func, "x"), "{:?}", kills(&func));
}

#[test]
fn a_local_whose_mut_borrow_reached_an_earlier_call_is_havocked_across_a_nullary_call() {
    let func = stashed_local(vec![], true);
    assert!(kills_name(&func, "x"), "{:?}", kills(&func));
}

#[test]
fn a_mutably_borrowed_local_is_havocked_even_when_the_borrow_never_left_the_body() {
    // The coarse rule's measured precision cost: the borrow is written through in `f`
    // only, but every `&mut`-borrowed stack local is havocked (the fine-grained rule
    // that exempted this shape missed a pointer stored through another `&mut`).
    let func = stashed_local(vec![Operand::Copy(Place::local(1))], false);
    assert!(kills_name(&func, "x"), "{:?}", kills(&func));
    let func = stashed_local(vec![], false);
    assert!(kills_name(&func, "x"), "{:?}", kills(&func));
}

#[test]
fn an_unborrowed_scalar_stack_local_keeps_its_facts() {
    // Control, rule (a): `let mut x = 3; x = 7; if x < 50 { poke(); x + 200 }`. `x`
    // is never borrowed and holds no pointer, so it is in no havoc list at all.
    let func = body(
        vec![(u8_ty(), Some("ret")), (u8_ty(), Some("x")), (Ty::Unit, None)],
        0,
        vec![
            block(
                0,
                vec![
                    assign(1, Rvalue::Use(Operand::Constant(ConstValue::Uint(3, 8)))),
                    assign(1, Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8)))),
                ],
                Terminator::Goto(BlockId(1)),
            ),
            block(1, vec![], call("test::poke", vec![], 2, 2)),
        ],
    );
    assert_eq!(kills(&func), vec!["_2".to_string(), "_2__slice_len".to_string()]);
}

/// Review round 3, shape 1: a pointer to `x` stored THROUGH a `&mut` to another
/// local, then that local's pointee handed to `stash`:
/// `r = &mut y; r2 = &mut z; pp = &mut r; _t = &mut x; (*pp) = move _t;
///  _u = &mut (*r); stash(move _u); poke()`.
#[test]
fn a_pointer_stored_through_a_mut_reference_is_havocked() {
    let deref = |local| Place { local, projections: vec![Projection::Deref] };
    let func = body(
        vec![
            (u8_ty(), Some("ret")),
            (Ty::Bool, Some("c")),
            (u8_ty(), Some("x")),
            (u8_ty(), Some("y")),
            (u8_ty(), Some("z")),
            (unique(u8_ty()), Some("r")),
            (unique(u8_ty()), Some("r2")),
            (unique(unique(u8_ty())), Some("pp")),
            (unique(u8_ty()), None),
            (unique(u8_ty()), None),
            (Ty::Unit, None),
            (Ty::Unit, None),
        ],
        1,
        vec![
            block(
                0,
                vec![
                    assign(5, Rvalue::Ref { mutable: true, place: Place::local(3) }),
                    assign(6, Rvalue::Ref { mutable: true, place: Place::local(4) }),
                    assign(7, Rvalue::Ref { mutable: true, place: Place::local(5) }),
                    assign(8, Rvalue::Ref { mutable: true, place: Place::local(2) }),
                    Statement::Assign {
                        place: deref(7),
                        rvalue: Rvalue::Use(Operand::Move(Place::local(8))),
                        span: SourceSpan::default(),
                    },
                    assign(9, Rvalue::Ref { mutable: true, place: deref(5) }),
                ],
                call("test::stash", vec![Operand::Move(Place::local(9))], 10, 1),
            ),
            block(1, vec![], call("test::poke", vec![], 11, 2)),
        ],
    );
    assert!(kills_name(&func, "x"), "{:?}", kills(&func));
}

/// Review round 3, shape 2: `s: &mut S` with `S { v: u8, _pin: PhantomPinned }` has no
/// protector and no uniqueness, so a raw pointer the caller stashed may write `s.v`.
#[test]
fn a_mut_parameter_to_a_not_unpin_pointee_is_havocked() {
    let s =
        adt("test::S", vec![("v", u8_ty()), ("_pin", adt("core::marker::PhantomPinned", vec![]))]);
    let func = lone_param(unique(s));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    // The name rule alone: a pinning marker refuses even with a recorded field.
    let s = adt(
        "test::S",
        vec![
            ("v", u8_ty()),
            ("_pin", adt("core::pin::UnsafePinned<u8>", vec![("value", u8_ty())])),
        ],
    );
    let func = lone_param(unique(s));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
}

/// Review round 3, shape 3: a `&mut` to a recursive type lowers to a by-name
/// `Datatype` marker (structure not in hand), and an `Unsupported` pointee is unknown:
/// both fail closed.
#[test]
fn a_mut_parameter_to_an_unresolved_pointee_is_havocked() {
    let node = Ty::Datatype { name: "test::Node".into(), variants: vec![] };
    let func = lone_param(unique(node));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    let unknown = Ty::Unsupported { kind: "Foreign".into(), detail: "extern type".into() };
    let func = lone_param(unique(unknown));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
}

#[test]
fn an_unexposed_mut_unpin_scalar_struct_parameter_keeps_its_facts() {
    // Control, rule (b): `s: &mut S { v: u8, w: u32 }`, only read and written through.
    let s = adt("test::S", vec![("v", u8_ty()), ("w", Ty::Int { width: 32, signed: false })]);
    let func = lone_param(unique(s));
    assert_eq!(kills(&func), vec!["_3".to_string(), "_3__slice_len".to_string()]);
}

#[test]
fn a_reseated_or_copied_mut_parameter_is_havocked() {
    let s = adt("test::S", vec![("v", u8_ty())]);
    // `let t = s;` (a copy of the pointer into another local).
    let mut func = lone_param(unique(s.clone()));
    func.body.locals.push(LocalDecl { index: 4, ty: unique(s.clone()), name: None });
    func.body.blocks[0].stmts.push(assign(4, Rvalue::Use(Operand::Copy(Place::local(1)))));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    // `s = t;` (reseated: the new pointee is not the protected one).
    let mut func = lone_param(unique(s.clone()));
    func.body.locals.push(LocalDecl { index: 4, ty: unique(s), name: None });
    func.body.blocks[0].stmts.push(assign(1, Rvalue::Use(Operand::Move(Place::local(4)))));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
}

#[test]
fn a_reborrow_carried_through_an_aggregate_exposes_its_root() {
    // `_6 = (move _3,)`, `sink(move _6)`: the tuple carries `&mut x` to the callee.
    let mut func = stashed_local(vec![], false);
    func.body.locals.push(LocalDecl { index: 6, ty: Ty::Tuple(vec![unique(u8_ty())]), name: None });
    func.body.blocks[0].stmts.push(assign(
        6,
        Rvalue::Aggregate(trust_types::AggregateKind::Tuple, vec![Operand::Move(Place::local(3))]),
    ));
    func.body.blocks[0].terminator = call("test::sink", vec![Operand::Move(Place::local(6))], 4, 1);
    assert!(kills_name(&func, "x"), "{:?}", kills(&func));
}

/// `fn f(r: &mut u32, s: &[u8])` with `_3 = &mut (*_1)` handed to `helper` (when
/// `expose`), then `len(s)`.
fn mut_param(expose: bool) -> VerifiableFunction {
    let first = if expose {
        block(
            0,
            vec![assign(
                3,
                Rvalue::Ref {
                    mutable: true,
                    place: Place { local: 1, projections: vec![Projection::Deref] },
                },
            )],
            call("test::helper", vec![Operand::Move(Place::local(3))], 4, 1),
        )
    } else {
        block(0, vec![], Terminator::Goto(BlockId(1)))
    };
    body(
        vec![
            (u8_ty(), Some("ret")),
            (unique(Ty::Int { width: 32, signed: false }), Some("r")),
            (byte_slice_ref(), Some("s")),
            (unique(Ty::Int { width: 32, signed: false }), None),
            (Ty::Unit, None),
        ],
        2,
        vec![
            first,
            block(1, vec![], call("test::len", vec![Operand::Copy(Place::local(2))], 0, 2)),
        ],
    )
}

#[test]
fn an_unexposed_mut_parameter_keeps_its_facts() {
    // Control: the TINV-18 / scalar fast path's intended precision for `r: &mut u32`.
    // (The unused `&mut u32` temp `_3` is a pointer-carrying stack local and stays
    // havocked.)
    let func = mut_param(false);
    assert!(!kills_name(&func, "r"), "{:?}", kills(&func));
    assert!(kills_name(&func, "_3"), "{:?}", kills(&func));
}

#[test]
fn a_mut_parameter_reborrowed_into_an_earlier_call_is_havocked() {
    let func = mut_param(true);
    assert!(kills_name(&func, "r"), "{:?}", kills(&func));
}

#[test]
fn a_mut_reference_held_in_memory_is_havocked() {
    // `self: &mut W` with `W { f: &mut u8 }`: the field's creator may have stashed a
    // raw child of it before building `W`.
    let w = Ty::Adt {
        adt_kind: Some(AdtKind::Struct),
        layout: None,
        variants: vec![].into(),
        name: "test::W".into(),
        fields: vec![("f".to_string(), unique(u8_ty()))].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let func = body(
        vec![(u8_ty(), Some("ret")), (unique(w), Some("self")), (byte_slice_ref(), Some("s"))],
        2,
        vec![block(0, vec![], call("test::len", vec![Operand::Copy(Place::local(2))], 0, 1))],
    );
    assert!(kills_name(&func, "self"), "{:?}", kills(&func));
}

/// `P1`'s shape: `P { b: <b_ty>, i: usize }`.
fn p1_struct(b_ty: Ty) -> Ty {
    adt("test::P", vec![("b", b_ty), ("i", usize_ty())])
}

/// Whether the call's kill list rebinds any fact name rooted at `name` (the parameter's
/// base name, its field values, a field's slice length or the bytes behind it).
fn kills_any_under(func: &VerifiableFunction, names: &[&str]) -> bool {
    kills(func).iter().any(|k| names.iter().any(|n| super::path_defs::place_names_overlap(k, n)))
}

/// The P1 fact names of `s: &mut P` that live in `*s`'s OWN (protected) bytes and must
/// survive: `s.i` and `s.b`'s length. (`s`, `s*` and `s*.0` are ancestors of the
/// explicitly havocked `s*.0*`, so the destination relation rebinds them too.)
const P1_NAMES: [&str; 2] = ["s*.1", "s*.0__slice_len"];

/// The names BEHIND `s.b`, which must be havocked: the review's counterexample reads
/// `p.b[0]` before and after the call.
const P1_BEHIND: [&str; 3] = ["s*.0*", "s*.0*[0]", "s*.0*[_6]"];

#[test]
fn a_p1_shaped_mut_parameter_keeps_its_facts_across_a_nullary_call() {
    // P1 precision (2026-10-06): `self: &mut P { b: &[u8], i: usize }`, only read in
    // the body, then `poke()`. `*self`'s bytes (including `b`'s address and length) are
    // protected and kept; the bytes BEHIND `b` are not (review finding: a field holding
    // raw-pointer bits was never retagged, so a foreign write is defined).
    let func = lone_param(unique(p1_struct(byte_slice_ref())));
    assert!(!kills_any_under(&func, &P1_NAMES), "{:?}", kills(&func));
    for n in P1_BEHIND {
        assert!(kills_any_under(&func, &[n]), "{n}: {:?}", kills(&func));
    }
    // `&str` and `&u32` fields are the same shape.
    let func = lone_param(unique(p1_struct(shared(Ty::Str))));
    assert!(!kills_any_under(&func, &P1_NAMES), "{:?}", kills(&func));
    let func = lone_param(unique(p1_struct(shared(Ty::Int { width: 32, signed: false }))));
    assert!(!kills_any_under(&func, &P1_NAMES), "{:?}", kills(&func));
    // A slice of a recorded scalar struct, and a shared ref inside an enum variant
    // (`Option<&[u8]>`-like), are admitted too.
    let pair = adt("test::Pair", vec![("x", u8_ty()), ("y", u8_ty())]);
    let func = lone_param(unique(p1_struct(shared(Ty::Slice { elem: Box::new(pair) }))));
    assert!(!kills_any_under(&func, &P1_NAMES), "{:?}", kills(&func));
}

#[test]
fn a_p1_shaped_mut_parameter_keeps_its_facts_across_a_read_only_call() {
    // `peek(&*self)` earlier (a shared reborrow of the whole pointee), then `len(s)`.
    let p = p1_struct(byte_slice_ref());
    let func = body(
        vec![
            (u8_ty(), Some("ret")),
            (unique(p.clone()), Some("s")),
            (byte_slice_ref(), Some("buf")),
            (shared(p), None),
            (u8_ty(), None),
        ],
        2,
        vec![
            block(
                0,
                vec![assign(
                    3,
                    Rvalue::Ref {
                        mutable: false,
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                    },
                )],
                call("test::peek", vec![Operand::Move(Place::local(3))], 4, 1),
            ),
            block(1, vec![], call("test::len", vec![Operand::Copy(Place::local(2))], 0, 2)),
        ],
    );
    assert!(!kills_any_under(&func, &P1_NAMES), "{:?}", kills(&func));
    assert!(kills_any_under(&func, &P1_BEHIND), "{:?}", kills(&func));
}

#[test]
fn a_p1_shaped_mut_parameter_whose_field_is_reborrowed_mutably_is_havocked() {
    // `_4 = &mut (*s).0` (a `&mut &[u8]` that could reseat `b`) anywhere in the body.
    let p = p1_struct(byte_slice_ref());
    let mut func = lone_param(unique(p));
    func.body.locals.push(LocalDecl { index: 4, ty: unique(byte_slice_ref()), name: None });
    func.body.blocks[0].stmts.push(assign(
        4,
        Rvalue::Ref {
            mutable: true,
            place: Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] },
        },
    ));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
}

#[test]
fn a_mut_parameter_whose_pointee_holds_a_writable_or_owning_pointer_is_havocked() {
    let cases: Vec<(&str, Ty)> = vec![
        ("&mut u8 field", unique(u8_ty())),
        ("*mut u8 field", Ty::RawPtr { mutable: true, pointee: Box::new(u8_ty()) }),
        ("*const u8 field", Ty::RawPtr { mutable: false, pointee: Box::new(u8_ty()) }),
        (
            "Box<u8> field",
            adt(
                "alloc::boxed::Box<u8>",
                vec![(
                    "0",
                    adt(
                        "core::ptr::unique::Unique<u8>",
                        vec![(
                            "pointer",
                            adt(
                                "core::ptr::non_null::NonNull<u8>",
                                vec![(
                                    "pointer",
                                    Ty::RawPtr { mutable: false, pointee: Box::new(u8_ty()) },
                                )],
                            ),
                        )],
                    ),
                )],
            ),
        ),
        // A compacted `Box` rendering is refused by name.
        ("Box<u8> by name", adt("alloc::boxed::Box<u8>", vec![("0", usize_ty())])),
        ("Vec<u8> field", Ty::Seq { elem: Box::new(u8_ty()), drop_auth: None }),
        ("String by name", adt("alloc::string::String", vec![("vec", usize_ty())])),
        ("Rc<u8> by name", adt("alloc::rc::Rc<u8>", vec![("ptr", usize_ty())])),
        // A shared reference to something that itself holds a pointer.
        ("&&[u8] field", shared(byte_slice_ref())),
        ("&[&u8] field", shared(Ty::Slice { elem: Box::new(shared(u8_ty())) })),
        ("&&mut u8 field", shared(unique(u8_ty()))),
        ("&*mut u8 field", shared(Ty::RawPtr { mutable: true, pointee: Box::new(u8_ty()) })),
    ];
    for (what, field) in cases {
        let func = lone_param(unique(p1_struct(field)));
        assert!(kills_name(&func, "s"), "{what}: {:?}", kills(&func));
    }
}

#[test]
fn a_mut_parameter_whose_shared_field_reaches_interior_mutability_is_havocked() {
    let cell = |name: &str| adt(name, vec![("value", u8_ty())]);
    let unsafe_cell = adt("core::cell::UnsafeCell<u8>", vec![("value", u8_ty())]);
    let cases: Vec<(&str, Ty)> = vec![
        ("&Cell<u8>", shared(cell("core::cell::Cell<u8>"))),
        ("&RefCell<u8>", shared(cell("core::cell::RefCell<u8>"))),
        ("&AtomicU8", shared(cell("core::sync::atomic::AtomicU8"))),
        ("&[Cell<u8>]", shared(Ty::Slice { elem: Box::new(cell("core::cell::Cell<u8>")) })),
        // A user struct wrapping an `UnsafeCell` field: refused by the field walk.
        ("&W { c: UnsafeCell<u8> }", shared(adt("test::W", vec![("c", unsafe_cell)]))),
        // A field-less (unrecorded) struct may hide anything.
        ("&Opaque {}", shared(adt("test::Opaque", vec![]))),
        // A union is never pure.
        (
            "&U (union)",
            shared(Ty::Adt {
                adt_kind: Some(AdtKind::Union),
                layout: None,
                variants: vec![].into(),
                name: "test::U".into(),
                fields: vec![("a".to_string(), u8_ty())].into(),
                disc_index_safe: false,
                faithful_enum_repr: None,
                enum_layout: None,
                arbitrary_precision: None,
                validity_wrapper: None,
            }),
        ),
    ];
    for (what, field) in cases {
        let func = lone_param(unique(p1_struct(field)));
        assert!(kills_name(&func, "s"), "{what}: {:?}", kills(&func));
    }
    // An interior-mutable struct is refused as the pointee itself too.
    let func = lone_param(unique(adt("core::cell::Cell<u8>", vec![("value", u8_ty())])));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
}

#[test]
fn a_mut_parameter_whose_shared_field_is_unresolved_is_havocked() {
    let cases: Vec<(&str, Ty)> = vec![
        ("&Datatype", shared(Ty::Datatype { name: "test::Node".into(), variants: vec![] })),
        (
            "&Unsupported",
            shared(Ty::Unsupported { kind: "Foreign".into(), detail: "extern type".into() }),
        ),
        (
            "&[Datatype]",
            shared(Ty::Slice {
                elem: Box::new(Ty::Datatype { name: "test::Node".into(), variants: vec![] }),
            }),
        ),
        ("&PhantomPinned", shared(adt("core::marker::PhantomPinned", vec![]))),
        ("&dyn", shared(Ty::Dynamic { trait_name: "test::Tr".into(), principal_key: None })),
    ];
    for (what, field) in cases {
        let func = lone_param(unique(p1_struct(field)));
        assert!(kills_name(&func, "s"), "{what}: {:?}", kills(&func));
    }
    // A pinning marker beside a shared field still refuses (structural `Unpin`).
    let s = adt(
        "test::S",
        vec![("b", byte_slice_ref()), ("_pin", adt("core::marker::PhantomPinned", vec![]))],
    );
    let func = lone_param(unique(s));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
}

#[test]
fn an_opaque_constant_argument_keeps_the_full_havoc() {
    // Shape (3): `A.store(255, Relaxed)` hands `const {alloc}: &AtomicU8` (an opaque
    // reference constant) to the callee. Even with no raw-pointer local, the arm is
    // closed: the constant is not a pointer-free value.
    let func = mut_param(false);
    let mut func = func;
    func.body.blocks[1].terminator = call(
        "core::sync::atomic::AtomicU8::store",
        vec![
            Operand::Constant(ConstValue::opaque_const()),
            Operand::Constant(ConstValue::Uint(255, 8)),
        ],
        0,
        2,
    );
    assert!(kills_name(&func, "r"), "{:?}", kills(&func));
    // A scalar constant is still a pure value.
    func.body.blocks[1].terminator =
        call("test::g", vec![Operand::Constant(ConstValue::Uint(255, 8))], 0, 2);
    assert!(!kills_name(&func, "r"), "{:?}", kills(&func));
}

#[test]
fn a_foreign_callee_with_scalar_arguments_keeps_the_full_havoc() {
    // The foreign / `unsafe`-signature / atomic fences close the whole arm.
    let mut func = mut_param(false);
    func.body.blocks[1].terminator =
        call_with("test::ffi", vec![Operand::Constant(ConstValue::Uint(1, 8))], 0, 2, true);
    assert!(kills_name(&func, "r"), "{:?}", kills(&func));
}

#[test]
fn an_opaque_terminator_exposes_every_root() {
    let mut func = mut_param(false);
    func.body.blocks[0].terminator = Terminator::Opaque {
        kind: "InlineAsm".into(),
        targets: vec![BlockId(1)],
        span: SourceSpan::default(),
    };
    assert!(kills_name(&func, "r"), "{:?}", kills(&func));
}

/// `fn at(s: &mut P) { if s.i < s.b.len() { poke(); s.b[s.i] } }` up to the call, with
/// the bounds-check prelude of a slice index BEFORE it in block 0:
/// `_4 = copy (*s).0; _5 = &raw const <addr>; _6 = PtrMetadata(move _5)`. `extra` locals
/// are appended after `_6` (the call result is `_3`).
fn indexed_p1(b_ty: Ty, addr: Place, extra: Vec<Ty>) -> VerifiableFunction {
    let mut locals = vec![
        (u8_ty(), Some("ret")),
        (unique(p1_struct(b_ty.clone())), Some("s")),
        (u8_ty(), None),
        (Ty::Unit, None),
        (b_ty, None),
        (
            Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Slice { elem: Box::new(u8_ty()) }) },
            None,
        ),
        (usize_ty(), None),
    ];
    locals.extend(extra.into_iter().map(|t| (t, None)));
    body(
        locals,
        1,
        vec![
            block(
                0,
                vec![
                    assign(
                        4,
                        Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref, Projection::Field(0)],
                        })),
                    ),
                    assign(5, Rvalue::AddressOf(false, addr)),
                    assign(
                        6,
                        Rvalue::UnaryOp(
                            trust_types::UnOp::PtrMetadata,
                            Operand::Move(Place::local(5)),
                        ),
                    ),
                ],
                Terminator::Goto(BlockId(1)),
            ),
            block(1, vec![], call("test::poke", vec![], 3, 2)),
        ],
    )
}

#[test]
fn a_slice_index_bounds_prelude_does_not_close_the_arm() {
    // P1 precision (2026-10-06): `&raw const (*_4)` with `_4: &[u8]` carries the shared
    // reference's read-only permission, so the dest-only arm's laundering gate admits
    // it; `s`'s facts survive `poke()`. The raw local itself stays havocked.
    let deref4 = Place { local: 4, projections: vec![Projection::Deref] };
    let func = indexed_p1(byte_slice_ref(), deref4, vec![]);
    assert!(!kills_any_under(&func, &P1_NAMES), "{:?}", kills(&func));
    assert!(kills_any_under(&func, &P1_BEHIND), "{:?}", kills(&func));
    assert!(kills_name(&func, "_5"), "{:?}", kills(&func));
}

#[test]
fn a_raw_address_with_write_permission_closes_the_arm() {
    // `&raw const x` of a LOCAL (`_7: u8`): carries the local's own write permission.
    let func = indexed_p1(byte_slice_ref(), Place::local(7), vec![u8_ty()]);
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    // `&raw const (*_7)` with `_7: &mut u8`.
    let deref7 = Place { local: 7, projections: vec![Projection::Deref] };
    let func = indexed_p1(byte_slice_ref(), deref7.clone(), vec![unique(u8_ty())]);
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    // `&raw const (*_7)` with `_7: &Cell<u8>` (a shared reference does not freeze it).
    let cell = adt("core::cell::Cell<u8>", vec![("value", u8_ty())]);
    let func = indexed_p1(byte_slice_ref(), deref7.clone(), vec![shared(cell)]);
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    // `&raw const (*_7)` with `_7: *const u8` (a raw pointer's own permission).
    let raw = Ty::RawPtr { mutable: false, pointee: Box::new(u8_ty()) };
    let func = indexed_p1(byte_slice_ref(), deref7, vec![raw]);
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
}

#[test]
fn a_raw_address_through_a_cell_sibling_or_a_union_or_a_stored_reference_closes_the_arm() {
    // Review finding 2: every Deref target must be read-only AS A WHOLE.
    let cell = adt("core::cell::Cell<u8>", vec![("value", u8_ty())]);
    let field0 =
        |local| Place { local, projections: vec![Projection::Deref, Projection::Field(0)] };
    // `r: &(u8, Cell<u8>)`, `&raw const (*r).0`: the `u8` is Freeze, its sibling is not.
    let pair = Ty::Tuple(vec![u8_ty(), cell.clone()]);
    let func = indexed_p1(byte_slice_ref(), field0(7), vec![shared(pair)]);
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    // `r: &U` with `union U { a: u8, c: Cell<u8> }`, `&raw const (*r).a`.
    let union = Ty::Adt {
        adt_kind: Some(AdtKind::Union),
        layout: None,
        variants: vec![].into(),
        name: "test::U".into(),
        fields: vec![("a".to_string(), u8_ty()), ("c".to_string(), cell)].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let func = indexed_p1(byte_slice_ref(), field0(7), vec![shared(union)]);
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    // `r: &P`, `&raw const (*(*r).0)`: the second Deref is of a reference STORED IN
    // MEMORY, never retagged, which may carry raw-pointer bits with write permission.
    let stored = Place {
        local: 7,
        projections: vec![Projection::Deref, Projection::Field(0), Projection::Deref],
    };
    let func = indexed_p1(byte_slice_ref(), stored, vec![shared(p1_struct(byte_slice_ref()))]);
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    // `r: &&[u8]`, `&raw const (*(*r))`: every target is read-only, but the inner
    // reference is stored in memory; only the one-`Deref` rule refuses it.
    let stored = Place { local: 7, projections: vec![Projection::Deref, Projection::Deref] };
    let func = indexed_p1(byte_slice_ref(), stored, vec![shared(byte_slice_ref())]);
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
}

#[test]
fn a_shared_ref_in_an_enum_variant_or_an_array_is_refused() {
    // A reference inside an enum variant or an array element has no `param*.f*` name
    // the arm could havoc, so the pointee is refused (fail-closed).
    let opt = Ty::Adt {
        adt_kind: Some(AdtKind::Enum),
        layout: None,
        variants: vec![
            trust_types::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            trust_types::VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), byte_slice_ref())],
            },
        ]
        .into(),
        name: "core::option::Option<&[u8]>".into(),
        fields: vec![("tag".to_string(), usize_ty())].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let func = lone_param(unique(p1_struct(opt)));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    let arr = Ty::Array { elem: Box::new(byte_slice_ref()), len: 2 };
    let func = lone_param(unique(p1_struct(arr)));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
}

#[test]
fn a_p1_shaped_parameter_that_leaves_the_body_is_havocked() {
    let p = p1_struct(byte_slice_ref());
    // Copied (`_4 = copy s`) and moved (`_4 = move s`) into another local.
    for op in [Operand::Copy(Place::local(1)), Operand::Move(Place::local(1))] {
        let mut func = lone_param(unique(p.clone()));
        func.body.locals.push(LocalDecl { index: 4, ty: unique(p.clone()), name: None });
        func.body.blocks[0].stmts.push(assign(4, Rvalue::Use(op)));
        assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    }
    // Reseated (`s = t`): `pointer_is_pinned` is false.
    let mut func = lone_param(unique(p.clone()));
    func.body.locals.push(LocalDecl { index: 4, ty: unique(p.clone()), name: None });
    func.body.blocks[0].stmts.push(assign(1, Rvalue::Use(Operand::Move(Place::local(4)))));
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
    // A `Drop` of a place under it (drop glue is handed `&mut (*s).0`).
    let mut func = lone_param(unique(p));
    func.body.blocks[0].terminator = Terminator::Drop {
        place: Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] },
        target: BlockId(1),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Unreachable,
    };
    assert!(kills_name(&func, "s"), "{:?}", kills(&func));
}

#[test]
fn an_exposed_mut_parameter_beside_a_kept_p1_parameter_stays_havocked() {
    // `fn f(s: &mut P, r: &mut u8) { helper(&mut *r); poke() }`: `s` keeps its own
    // bytes, `r` (reborrowed into an earlier call) is havocked.
    let func = body(
        vec![
            (u8_ty(), Some("ret")),
            (unique(p1_struct(byte_slice_ref())), Some("s")),
            (unique(u8_ty()), Some("r")),
            (unique(u8_ty()), None),
            (Ty::Unit, None),
            (Ty::Unit, None),
        ],
        2,
        vec![
            block(
                0,
                vec![assign(
                    3,
                    Rvalue::Ref {
                        mutable: true,
                        place: Place { local: 2, projections: vec![Projection::Deref] },
                    },
                )],
                call("test::helper", vec![Operand::Move(Place::local(3))], 4, 1),
            ),
            block(1, vec![], call("test::poke", vec![], 5, 2)),
        ],
    );
    assert!(kills_name(&func, "r"), "{:?}", kills(&func));
    assert!(!kills_any_under(&func, &P1_NAMES), "{:?}", kills(&func));
    assert!(kills_any_under(&func, &P1_BEHIND), "{:?}", kills(&func));
}

// ---------------------------------------------------------------------------------------
// CALL-HAVOC-ESCAPE-2 (2026-10-06): the memory behind a reference LOADED FROM MEMORY is
// havocked at every call, whatever the root (`path_defs::stored_ref_pointee_names`).
// ---------------------------------------------------------------------------------------

/// `fn g(p: <root_ty>) { _2 = copy (*p).0 (or p.0 by value); _3 = (*_2)[0]; <call> }`
/// with the call `callee(args)` in block 1. `_2: &[u8]` is a deref temp.
fn stored_ref_body(
    root_ty: Ty,
    by_value: bool,
    args: Vec<Operand>,
    extra: Vec<Ty>,
) -> VerifiableFunction {
    let field0 = if by_value {
        Place { local: 1, projections: vec![Projection::Field(0)] }
    } else {
        Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] }
    };
    let mut locals = vec![
        (u8_ty(), Some("ret")),
        (root_ty, Some("p")),
        (byte_slice_ref(), None),
        (u8_ty(), None),
        (Ty::Unit, None),
    ];
    locals.extend(extra.into_iter().map(|t| (t, None)));
    body(
        locals,
        1,
        vec![
            block(
                0,
                vec![
                    assign(2, Rvalue::Use(Operand::Copy(field0))),
                    assign(
                        3,
                        Rvalue::Use(Operand::Copy(Place {
                            local: 2,
                            projections: vec![Projection::Deref, Projection::Index(3)],
                        })),
                    ),
                ],
                Terminator::Goto(BlockId(1)),
            ),
            block(1, vec![], call("test::poke", args, 4, 2)),
        ],
    )
}

#[test]
fn a_shared_param_s_stored_reference_pointee_is_havocked_at_a_nullary_call() {
    // The re-review's shape (1): `p: &P` is in no havoc list, but `p.b` may hold
    // raw-pointer bits and `poke()` may write the buffer through a static.
    let func = stored_ref_body(shared(p1_struct(byte_slice_ref())), false, vec![], vec![]);
    assert!(kills_any_under(&func, &["p*.0*", "p*.0*[0]"]), "{:?}", kills(&func));
    assert!(kills_any_under(&func, &["_2*", "_2*[_3]"]), "{:?}", kills(&func));
    // `*p`'s own bytes (protected `&P` argument) and the lengths survive.
    assert!(
        !kills_any_under(&func, &["p*.1", "p*.0__slice_len", "_2__slice_len"]),
        "{:?}",
        kills(&func)
    );
}

#[test]
fn a_by_value_struct_s_reference_field_pointee_is_havocked() {
    // `p: P` by value (a local in `drive`): `p.0*` is behind a stored reference.
    let func = stored_ref_body(p1_struct(byte_slice_ref()), true, vec![], vec![]);
    assert!(kills_any_under(&func, &["p.0*", "p.0*[0]"]), "{:?}", kills(&func));
    assert!(!kills_any_under(&func, &["p.1", "p.0__slice_len"]), "{:?}", kills(&func));
}

#[test]
fn a_shared_ref_to_a_shared_ref_argument_grants_a_write() {
    // The re-review's shape (2): `peek(&p.b)` hands `&&[u8]`; the inner reference's
    // raw-pointer bits can be written through. The no-write arm must not take it.
    let mut func = stored_ref_body(
        shared(p1_struct(byte_slice_ref())),
        false,
        vec![Operand::Move(Place::local(5))],
        vec![shared(byte_slice_ref())],
    );
    func.body.blocks[1].stmts.push(assign(
        5,
        Rvalue::Ref {
            mutable: false,
            place: Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] },
        },
    ));
    assert!(kills_any_under(&func, &["p*.0*[0]"]), "{:?}", kills(&func));
    // The argument itself no longer grants no write: the no-write arm is closed, so the
    // whole-function list (here the `&&[u8]` temp's own name) is havocked.
    assert!(
        !super::path_defs::arg_grants_no_write_for_tests(&func, &Operand::Move(Place::local(5))),
        "`&&[u8]` must not grant no write"
    );
}

#[test]
fn a_retagged_reference_local_keeps_its_pointee() {
    // A parameter `b: &[u8]`, a borrow `s = &(*b)`, and a call result `t = f()` are
    // retagged where they get their value: their pointee facts survive a call.
    let func = body(
        vec![
            (u8_ty(), Some("ret")),
            (byte_slice_ref(), Some("b")),
            (byte_slice_ref(), Some("s")),
            (byte_slice_ref(), Some("t")),
            (Ty::Unit, None),
        ],
        1,
        vec![
            block(
                0,
                vec![assign(
                    2,
                    Rvalue::Ref {
                        mutable: false,
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                    },
                )],
                call("test::mk", vec![], 3, 1),
            ),
            block(1, vec![], call("test::poke", vec![], 4, 2)),
        ],
    );
    assert!(!kills_any_under(&func, &["b*[0]", "s*[0]", "t*[0]"]), "{:?}", kills(&func));
}

#[test]
fn a_reference_inside_an_enum_or_array_local_is_havocked_whole() {
    let opt = Ty::Adt {
        adt_kind: Some(AdtKind::Enum),
        layout: None,
        variants: vec![
            trust_types::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            trust_types::VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), byte_slice_ref())],
            },
        ]
        .into(),
        name: "core::option::Option<&[u8]>".into(),
        fields: vec![("tag".to_string(), usize_ty())].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let func = stored_ref_body(shared(p1_struct(byte_slice_ref())), false, vec![], vec![opt]);
    assert!(kills_name(&func, "_5"), "{:?}", kills(&func));
    let arr = Ty::Array { elem: Box::new(byte_slice_ref()), len: 2 };
    let func = stored_ref_body(shared(p1_struct(byte_slice_ref())), false, vec![], vec![arr]);
    assert!(kills_name(&func, "_5"), "{:?}", kills(&func));
    // A pointer-free local and an owned `Vec` of references are not havocked.
    let v = Ty::Seq { elem: Box::new(byte_slice_ref()), drop_auth: None };
    let func =
        stored_ref_body(shared(p1_struct(byte_slice_ref())), false, vec![], vec![v, u8_ty()]);
    assert!(!kills_name(&func, "_5") && !kills_name(&func, "_6"), "{:?}", kills(&func));
}

#[test]
fn a_borrow_of_a_retagged_reference_local_grants_no_write() {
    // P1's `&self.b[a..b] == w`: `_6 = &(*_1)` (a reborrow, retagged), `_5 = &_6`
    // hands `&&[u8]` to `eq`. Neither `_6`'s slot nor `*_6` is writable through it.
    let mut func = stored_ref_body(
        shared(p1_struct(byte_slice_ref())),
        false,
        vec![Operand::Move(Place::local(5))],
        vec![shared(byte_slice_ref()), byte_slice_ref()],
    );
    func.body.blocks[1].stmts.push(assign(
        6,
        Rvalue::Ref {
            mutable: false,
            place: Place { local: 2, projections: vec![Projection::Deref] },
        },
    ));
    func.body.blocks[1]
        .stmts
        .push(assign(5, Rvalue::Ref { mutable: false, place: Place::local(6) }));
    assert!(super::path_defs::arg_grants_no_write_for_tests(
        &func,
        &Operand::Move(Place::local(5))
    ));
    // A borrow of the DEREF TEMP `_2 = copy (*p).0` (never retagged) still grants a write.
    let mut func = stored_ref_body(
        shared(p1_struct(byte_slice_ref())),
        false,
        vec![Operand::Move(Place::local(5))],
        vec![shared(byte_slice_ref())],
    );
    func.body.blocks[1]
        .stmts
        .push(assign(5, Rvalue::Ref { mutable: false, place: Place::local(2) }));
    assert!(!super::path_defs::arg_grants_no_write_for_tests(
        &func,
        &Operand::Move(Place::local(5))
    ));
}

#[test]
fn a_box_root_local_is_left_to_the_ordinary_list() {
    let boxed = |pointee: Ty| {
        let nonnull = adt(
            "core::ptr::non_null::NonNull<T>",
            vec![("pointer", Ty::RawPtr { mutable: false, pointee: Box::new(pointee) })],
        );
        let marker = adt("core::marker::PhantomData<T>", vec![]);
        let unique =
            adt("core::ptr::unique::Unique<T>", vec![("pointer", nonnull), ("_marker", marker)]);
        adt("alloc::boxed::Box<T>", vec![("0", unique), ("1", adt("alloc::alloc::Global", vec![]))])
    };
    let func = stored_ref_body(
        shared(p1_struct(byte_slice_ref())),
        false,
        vec![],
        vec![boxed(byte_slice_ref()), boxed(u8_ty())],
    );
    // Both boxes are pointer-carrying ROOT locals: the ordinary list havocs them whole
    // (since the review of `d1697fccf6` the stored list covers boxes below a root only).
    assert!(kills_name(&func, "_5") && kills_name(&func, "_6"), "{:?}", kills(&func));
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(!stored.iter().any(|n| n.starts_with("_5") || n.starts_with("_6")), "{stored:?}");
}

/// Review of `d1697fccf6`, finding 1: `p: &S { q: *const u8 }`,
/// `s = &(*(*p).0)` (a retagged borrow through the stored raw pointer), `x = *s`, then
/// `poke()`. Both `s*` and a raw re-read of `*p.q` fold to `p*.0*`; a `static mut`
/// holding a copy of `p.q` makes a write by `poke` defined, so `p*.0*` must be killed.
fn stored_raw_body() -> VerifiableFunction {
    let s_ty =
        adt("test::S", vec![("q", Ty::RawPtr { mutable: false, pointee: Box::new(u8_ty()) })]);
    body(
        vec![
            (u8_ty(), Some("ret")),
            (shared(s_ty), Some("p")),
            (shared(u8_ty()), Some("s")),
            (u8_ty(), Some("x")),
            (Ty::Unit, None),
        ],
        1,
        vec![
            block(
                0,
                vec![
                    assign(
                        2,
                        Rvalue::Ref {
                            mutable: false,
                            place: Place {
                                local: 1,
                                projections: vec![
                                    Projection::Deref,
                                    Projection::Field(0),
                                    Projection::Deref,
                                ],
                            },
                        },
                    ),
                    assign(
                        3,
                        Rvalue::Use(Operand::Copy(Place {
                            local: 2,
                            projections: vec![Projection::Deref],
                        })),
                    ),
                ],
                Terminator::Goto(BlockId(1)),
            ),
            block(1, vec![], call("test::poke", vec![], 4, 2)),
        ],
    )
}

#[test]
fn a_raw_pointer_stored_in_a_field_is_havocked_behind_whatever_its_pointee() {
    let func = stored_raw_body();
    assert!(kills_any_under(&func, &["p*.0*"]), "{:?}", kills(&func));
    // The pointee `u8` holds no pointer; the field's raw bits are what matter.
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(stored.iter().any(|n| n == "p*.0*"), "{stored:?}");
    // `*p`'s own bytes (the pointer value is a sibling of nothing here, but `p*.0`
    // is an ancestor and is rebound with it) — and `x`, a scalar local, survives.
    assert!(!kills_any_under(&func, &["x"]), "{:?}", kills(&func));
}

#[test]
fn every_retagged_borrow_folds_only_to_an_unstored_place_or_is_killed() {
    // THE FOLD INVARIANT, checked over every fixture body this file builds: a
    // retagged borrow `l = &place` whose place is not "unstored" has `place`'s name
    // in the stored list.
    let bodies = vec![
        stored_raw_body(),
        stored_ref_body(shared(p1_struct(byte_slice_ref())), false, vec![], vec![]),
        lone_param(unique(p1_struct(byte_slice_ref()))),
        indexed_p1(
            byte_slice_ref(),
            Place { local: 4, projections: vec![Projection::Deref] },
            vec![],
        ),
    ];
    for func in &bodies {
        let stored = super::path_defs::stored_ref_pointee_names(func);
        for (l, _) in func.body.locals.iter().enumerate() {
            if let Some(Rvalue::Ref { place, .. }) = crate::local_defs::unique_value_def(func, l)
                && !super::path_defs::borrowed_place_is_unstored(func, place)
            {
                let name = crate::place_to_var_name(func, place);
                assert!(stored.contains(&name), "{name} not killed: {stored:?}");
            }
        }
    }
    // And the stored-raw borrow is NOT unstored.
    let func = stored_raw_body();
    let Some(Rvalue::Ref { place, .. }) = crate::local_defs::unique_value_def(&func, 2) else {
        panic!("`s` is a borrow")
    };
    assert!(!super::path_defs::borrowed_place_is_unstored(&func, place));
}

#[test]
fn a_box_or_raw_pointer_in_a_field_is_havocked_behind_and_a_root_one_is_left_to_the_list() {
    let raw = Ty::RawPtr { mutable: true, pointee: Box::new(u8_ty()) };
    let func = stored_ref_body(
        shared(p1_struct(byte_slice_ref())),
        false,
        vec![],
        vec![Ty::Tuple(vec![u8_ty(), raw.clone()]), raw],
    );
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(stored.iter().any(|n| n == "_5.1*"), "{stored:?}");
    assert!(!stored.iter().any(|n| n.starts_with("_6")), "{stored:?}");
}

#[test]
fn the_discriminant_carrier_of_every_killed_place_is_killed() {
    // Finding 3: `__trust_mir__discr_<place>` is a separate spelling.
    let func = stored_ref_body(shared(p1_struct(byte_slice_ref())), false, vec![], vec![]);
    let carrier = crate::discriminant_formula_var_name("p*.0*");
    assert!(kills_any_under(&func, &[carrier.as_str()]), "{:?}", kills(&func));
    // A place below a killed one, by prefix.
    let below = crate::discriminant_formula_var_name("p*.0*[0]");
    assert!(kills_any_under(&func, &[below.as_str()]), "{:?}", kills(&func));
}

#[test]
fn only_the_std_zero_sized_markers_are_exempt_by_name() {
    // Finding 2: a user `PhantomData` with no recorded field is fail-closed.
    let func = stored_ref_body(
        shared(p1_struct(byte_slice_ref())),
        false,
        vec![],
        vec![adt("user::PhantomData", vec![]), adt("core::marker::PhantomData<&u8>", vec![])],
    );
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(stored.iter().any(|n| n == "_5"), "{stored:?}");
    assert!(!stored.iter().any(|n| n == "_6"), "{stored:?}");
}

#[test]
fn a_user_type_named_box_is_walked_like_any_struct() {
    // Review of `2628c2a847`: `mod m { pub struct Box<'a> { pub r: &'a u8 } }`,
    // `S { b: m::Box }`, `p: &S`: `p*.0.0*` (behind `p.b.r`) must be killed; and the
    // same with `m::Box { q: *const u8 }`.
    for inner in [shared(u8_ty()), Ty::RawPtr { mutable: false, pointee: Box::new(u8_ty()) }] {
        let user_box = adt("m::Box<'_>", vec![("r", inner)]);
        let s = adt("test::S", vec![("b", user_box)]);
        let func = stored_ref_body(shared(s), false, vec![], vec![]);
        let stored = super::path_defs::stored_ref_pointee_names(&func);
        assert!(stored.iter().any(|n| n == "p*.0.0*"), "{stored:?}");
        assert!(kills_any_under(&func, &["p*.0.0*"]), "{:?}", kills(&func));
    }
}

#[test]
fn a_std_box_below_a_root_is_havocked_behind_and_its_fields_walked() {
    let boxed = adt(
        "std::boxed::Box<u8>",
        vec![("0", Ty::RawPtr { mutable: false, pointee: Box::new(u8_ty()) })],
    );
    let s = adt("test::S", vec![("b", boxed.clone())]);
    let func = stored_ref_body(shared(s), false, vec![], vec![]);
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(stored.iter().any(|n| n == "p*.0*"), "{stored:?}");
    assert!(stored.iter().any(|n| n == "p*.0.0*"), "{stored:?}");
    // A ROOT std `Box` local, even rendered field-less, is on the ordinary list.
    let func = stored_ref_body(
        shared(p1_struct(byte_slice_ref())),
        false,
        vec![],
        vec![adt("std::boxed::Box<u8>", vec![]), adt("test::Opaque", vec![])],
    );
    assert!(kills_name(&func, "_5") && kills_name(&func, "_6"), "{:?}", kills(&func));
    // The `std::` marker spellings are exempt like the `core::` ones.
    let func = stored_ref_body(
        shared(p1_struct(byte_slice_ref())),
        false,
        vec![],
        vec![adt("std::marker::PhantomData<&u8>", vec![]), adt("std::alloc::Global", vec![])],
    );
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(!stored.iter().any(|n| n == "_5" || n == "_6"), "{stored:?}");
    assert!(!kills_name(&func, "_5") && !kills_name(&func, "_6"), "{:?}", kills(&func));
}

/// `d: &VecDeque<u32>` (a std struct with a private `RawVec` buffer pointer).
fn deque_ty() -> Ty {
    let nonnull = adt(
        "core::ptr::non_null::NonNull<u32>",
        vec![(
            "pointer",
            Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Int { width: 32, signed: false }) },
        )],
    );
    let unique = adt("core::ptr::unique::Unique<u32>", vec![("pointer", nonnull)]);
    let raw_vec = adt("alloc::raw_vec::RawVec<u32>", vec![("ptr", unique), ("cap", usize_ty())]);
    adt(
        "std::collections::VecDeque<u32>",
        vec![("head", usize_ty()), ("len", usize_ty()), ("buf", raw_vec)],
    )
}

#[test]
fn a_std_struct_s_private_pointer_is_not_walked_in_a_user_body() {
    // `std_index_range_panics_charged.rs#guarded` (`deque_range_inclusive_guarded`):
    // walking `d*.2.0.0.0*` rebound its ancestor `d`, the deque's length abstraction.
    let func = body(
        vec![(u8_ty(), Some("ret")), (shared(deque_ty()), Some("d")), (Ty::Unit, None)],
        1,
        vec![block(0, vec![], call("test::poke", vec![], 2, 1))],
    );
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(!stored.iter().any(|n| n.starts_with("d")), "{stored:?}");
    // The same body inside a std crate walks it.
    let mut std_func = func.clone();
    std_func.def_path = "alloc::collections::vec_deque::f".into();
    let stored = super::path_defs::stored_ref_pointee_names(&std_func);
    assert!(stored.iter().any(|n| n.starts_with("d*.2")), "{stored:?}");
}

// ---------------------------------------------------------------------------------------
// R3 GUARD-CALL-HAVOC-FOLD (2026-10-10): a reference loaded out of a local's FIELD whose
// deref the mint folds to a concrete referent gets the fold invariant's answer, not an
// unconditional kill (`path_defs::ref_local_folds_to_unstored_place`). Real-MIR twin:
// `tests/guard_call_havoc_fold_realmir.rs`.
// ---------------------------------------------------------------------------------------

/// `fn f(p: &S) { _2 = &<borrowed>; _3 = (move _2,); _4 = copy (_3.0); _5 = copy (*_4);
/// poke() }` — the `format!("{}", p.f)` argument-packing shape.
fn tuple_carried_borrow(s_ty: Ty, borrowed: Place, pointee: Ty) -> VerifiableFunction {
    body(
        vec![
            (u8_ty(), Some("ret")),
            (shared(s_ty), Some("p")),
            (shared(pointee.clone()), None),
            (Ty::Tuple(vec![shared(pointee.clone())]), None),
            (shared(pointee.clone()), None),
            (pointee, None),
            (Ty::Unit, None),
        ],
        1,
        vec![
            block(
                0,
                vec![
                    assign(2, Rvalue::Ref { mutable: false, place: borrowed }),
                    assign(
                        3,
                        Rvalue::Aggregate(
                            trust_types::AggregateKind::Tuple,
                            vec![Operand::Move(Place::local(2))],
                        ),
                    ),
                    assign(
                        4,
                        Rvalue::Use(Operand::Copy(Place {
                            local: 3,
                            projections: vec![Projection::Field(0)],
                        })),
                    ),
                    assign(
                        5,
                        Rvalue::Use(Operand::Copy(Place {
                            local: 4,
                            projections: vec![Projection::Deref],
                        })),
                    ),
                ],
                Terminator::Goto(BlockId(1)),
            ),
            block(1, vec![], call("test::poke", vec![], 6, 2)),
        ],
    )
}

#[test]
fn a_tuple_carried_borrow_of_a_shared_param_field_keeps_the_field() {
    let s = adt("test::S", vec![("g", usize_ty()), ("h", usize_ty())]);
    let borrowed = Place { local: 1, projections: vec![Projection::Deref, Projection::Field(1)] };
    let func = tuple_carried_borrow(s, borrowed, usize_ty());
    // Not vacuous: the read through the carried copy IS spelled by the field's name.
    let read = Place { local: 4, projections: vec![Projection::Deref] };
    assert_eq!(crate::place_to_var_name(&func, &read), "p*.1");
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(!stored.iter().any(|n| n == "p*.1"), "{stored:?}");
    assert!(!kills_any_under(&func, &["p*.1", "p*.0"]), "{:?}", kills(&func));
}

#[test]
fn a_tuple_carried_borrow_through_a_stored_raw_pointer_stays_havocked() {
    // The `stored_raw_body` adversary, carried through a tuple: `*p.q` may be written
    // by `poke` through a `static mut` copy of `p.q`, so the folded name must be killed.
    let s =
        adt("test::S", vec![("q", Ty::RawPtr { mutable: false, pointee: Box::new(usize_ty()) })]);
    let borrowed = Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Field(0), Projection::Deref],
    };
    let func = tuple_carried_borrow(s, borrowed, usize_ty());
    let read = Place { local: 4, projections: vec![Projection::Deref] };
    let name = crate::place_to_var_name(&func, &read);
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(stored.iter().any(|n| n == &name), "{name} not killed: {stored:?}");
    assert!(kills_any_under(&func, &[name.as_str()]), "{:?}", kills(&func));
}

// ---------------------------------------------------------------------------------------
// ESCAPE-HAVOC-FLOW-1 (2026-10-15, TRUST-KI-1015-1): rule (b) asked at the call. A `&mut`
// parameter whose pointee leaves the body only AFTER a call, on no path back to it, keeps
// its facts across that call (`path_defs::escape_havoc_at`).
// ---------------------------------------------------------------------------------------

/// The kill list of block `pos`'s terminator.
fn kills_at(func: &VerifiableFunction, pos: usize) -> Vec<String> {
    terminator_def_names(func, &func.body.blocks[pos])
}

/// `fn f(r: &mut u32, s: &[u8]) { let v = *r; len(s); helper(&mut *r); <after> }`: the
/// value-only call `len(s)` ends bb0, the reborrow `_3 = &mut (*_1)` handed to `helper`
/// is in bb1, and bb2 ends in `after` (`Return`, or a `Goto` back to bb0 for a loop).
fn reborrow_after_call(after: Terminator) -> VerifiableFunction {
    body(
        vec![
            (u8_ty(), Some("ret")),
            (unique(Ty::Int { width: 32, signed: false }), Some("r")),
            (byte_slice_ref(), Some("s")),
            (unique(Ty::Int { width: 32, signed: false }), None),
            (Ty::Unit, None),
            (Ty::Int { width: 32, signed: false }, Some("v")),
        ],
        2,
        vec![
            block(
                0,
                vec![assign(
                    5,
                    Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref],
                    })),
                )],
                call("test::len", vec![Operand::Copy(Place::local(2))], 0, 1),
            ),
            block(
                1,
                vec![assign(
                    3,
                    Rvalue::Ref {
                        mutable: true,
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                    },
                )],
                call("test::helper", vec![Operand::Move(Place::local(3))], 4, 2),
            ),
            block(2, vec![], after),
        ],
    )
}

#[test]
fn a_mut_parameter_reborrowed_only_after_a_call_keeps_its_facts_across_it() {
    let func = reborrow_after_call(Terminator::Return);
    assert!(!kills_at(&func, 0).iter().any(|n| n == "r"), "{:?}", kills_at(&func, 0));
    // The call the reborrow reaches keeps the full havoc.
    assert!(kills_at(&func, 1).iter().any(|n| n == "r"), "{:?}", kills_at(&func, 1));
}

#[test]
fn a_mut_parameter_reborrowed_after_a_call_in_a_loop_is_havocked_at_it() {
    // bb2 loops back to bb0: the reborrow of the last round runs before the next `len`.
    let func = reborrow_after_call(Terminator::Goto(BlockId(0)));
    assert!(kills_at(&func, 0).iter().any(|n| n == "r"), "{:?}", kills_at(&func, 0));
}

#[test]
fn a_mut_parameter_reborrowed_in_the_calls_own_block_is_havocked() {
    // The reborrow is a statement of bb0, so it runs before bb0's call.
    let mut func = reborrow_after_call(Terminator::Return);
    let reborrow = func.body.blocks[1].stmts.remove(0);
    func.body.blocks[0].stmts.push(reborrow);
    assert!(kills_at(&func, 0).iter().any(|n| n == "r"), "{:?}", kills_at(&func, 0));
}

#[test]
fn an_escape_that_reaches_a_call_only_through_an_unwind_edge_havocs_it() {
    // bb0: `switch` to bb1 or bb4; bb1: `_3 = &mut (*_1)`, `foo()` -> bb5, unwinding to the
    // cleanup bb2; bb2 -> bb3; bb4 -> bb3; bb3: `len(s)` (the call under test) -> bb5;
    // bb5: return. The reborrow reaches bb3 only through the unwind edge.
    let mut func = reborrow_after_call(Terminator::Return);
    let reborrow = func.body.blocks[1].stmts.remove(0);
    func.body.locals.push(LocalDecl { index: 6, ty: Ty::Bool, name: None });
    let mut foo = call("test::foo", vec![], 4, 5);
    if let Terminator::Call { unwind, .. } = &mut foo {
        *unwind = UnwindEdge::Cleanup(BlockId(2));
    }
    func.body.blocks = vec![
        block(
            0,
            vec![],
            Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(6)),
                targets: vec![(0, BlockId(4))],
                otherwise: BlockId(1),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        ),
        block(1, vec![reborrow], foo),
        block(2, vec![], Terminator::Goto(BlockId(3))),
        block(3, vec![], call("test::len", vec![Operand::Copy(Place::local(2))], 0, 5)),
        block(4, vec![], Terminator::Goto(BlockId(3))),
        block(5, vec![], Terminator::Return),
    ];
    assert!(kills_at(&func, 3).iter().any(|n| n == "r"), "{:?}", kills_at(&func, 3));
    // Control: without the unwind edge the reborrow does not reach bb3 (bb4 still does).
    if let Terminator::Call { unwind, .. } = &mut func.body.blocks[1].terminator {
        *unwind = UnwindEdge::Continue;
    }
    assert!(!kills_at(&func, 3).iter().any(|n| n == "r"), "{:?}", kills_at(&func, 3));
}

#[test]
fn a_block_the_entry_does_not_reach_counts_as_reached() {
    // bb3 (the call under test) has no predecessor in the graph: whatever runs before it,
    // the analysis cannot see, so the parameter is havocked there.
    let mut func = reborrow_after_call(Terminator::Return);
    func.body.blocks.push(block(
        3,
        vec![],
        call("test::len", vec![Operand::Copy(Place::local(2))], 0, 2),
    ));
    assert!(kills_at(&func, 3).iter().any(|n| n == "r"), "{:?}", kills_at(&func, 3));
    assert!(!kills_at(&func, 0).iter().any(|n| n == "r"), "{:?}", kills_at(&func, 0));
}

#[test]
fn a_body_with_repeated_block_ids_falls_back_to_the_whole_body_rule() {
    // The blocks cannot be placed, so the reborrow after the call counts as before it.
    let mut func = reborrow_after_call(Terminator::Return);
    func.body.blocks[2].id = BlockId(1);
    assert!(kills_at(&func, 0).iter().any(|n| n == "r"), "{:?}", kills_at(&func, 0));
}

/// FRESH-CAPTURE-1 (2026-10-18; candidate-gate RCA precision T1), on real MIR:
/// `word_cells::{closure#0}` (`tests/fixtures/gate_precision`) captures `cols` (field 0)
/// and `first_row` (field 1) by reference. With no premise the environment is named
/// WHOLE (`_1*`), as CALL-HAVOC-ESCAPE-2 names a closure. With the compiler's premise on
/// field 0 only, `_1*` gives way to the uncertified capture's pointee `_1*.1*` (still
/// havocked; its deref temp `_17 = copy (*_1).1` is spelled by that same folded name),
/// and nothing names field 0's pointee `_1*.0*` (which the deref temps `_15`/`_16` fold
/// onto) or its discriminant carrier. A premise owned by another function changes
/// nothing.
#[test]
fn a_certified_fresh_capture_drops_its_own_pointee_and_nothing_else() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/gate_precision/o0_word_cells_closure.json"
    );
    let text = std::fs::read_to_string(path).expect("fixture");
    let func: VerifiableFunction = serde_json::from_str(&text).expect("fixture parses");
    let plain = super::path_defs::stored_ref_pointee_names(&func).to_vec();
    assert!(plain.iter().any(|n| n == "_1*"), "{plain:?}");

    let premised = |owner: &str, fields: Vec<usize>| {
        let context =
            crate::VcgenContext::for_function(owner).with_fresh_shared_capture_fields(fields);
        crate::with_vcgen_context(&context, || {
            super::path_defs::stored_ref_pointee_names(&func).to_vec()
        })
    };
    let names = premised(&func.def_path, vec![0]);
    assert!(!names.iter().any(|n| n == "_1*"), "{names:?}");
    assert!(names.iter().any(|n| n == "_1*.1*"), "{names:?}");
    for gone in ["_1*.0*", "__trust_mir__discr__1*.0*"] {
        assert!(!names.iter().any(|n| n == gone), "`{gone}` must be kept: {names:?}");
    }
    assert!(
        names
            .iter()
            .all(|n| !n.starts_with("_1*.0") && !n.starts_with("_15") && !n.starts_with("_16")),
        "nothing under the certified capture: {names:?}"
    );
    assert_eq!(premised("gate_precision::word_cells", vec![0]), plain);
}

// ---------------------------------------------------------------------------------------
// RETURN-PAYLOAD-RETAG-1 (2026-10-18; candidate-gate RCA precision D2): a shared reference
// in the payload of an enum a call returned (`Iterator::next`'s `Option<&T>`) carries the
// call-return retag, so its pointee keeps its `Freeze` bytes across a call
// (`path_defs::call_return_enum_root`).
// ---------------------------------------------------------------------------------------

/// `Option<payload>` as the extractor renders it: variants `None` / `Some(payload)` and
/// the union view `__tag`, `__v1_0`.
fn option_of(payload: Ty) -> Ty {
    Ty::Adt {
        adt_kind: Some(AdtKind::Enum),
        layout: None,
        variants: vec![
            trust_types::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            trust_types::VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), payload.clone())],
            },
        ]
        .into(),
        name: "core::option::Option".into(),
        fields: vec![
            ("__tag".to_string(), Ty::Int { width: 64, signed: true }),
            ("__v1_0".to_string(), payload),
        ]
        .into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// How the body gets its `Option` local `_2`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OptionSource {
    /// `_2 = mk()`: the call-return shape of `for t in &v`.
    CallReturn,
    /// `_2 = copy (*s).0`: an `Option` loaded from memory.
    LoadedFromMemory,
    /// `_2 = mk()`, and `_2 = copy (*s).0` again later in the block: two definitions.
    Redefined,
    /// `_2 = mk()`, and `_7 = &mut _2` hands the slot out.
    MutBorrowedSlot,
}

/// `fn f(s: &S) -> u8 { _2 = <source>; _3 = copy (_2 as Some).0<tail>; _4 = copy (*_3).0;
/// poke() }` with `S { o: Option<payload> }` and `_3: t_ty`. The call under test is
/// `poke()`, the terminator of the last block.
fn option_payload_body(
    payload: Ty,
    t_ty: Ty,
    tail: Vec<Projection>,
    source: OptionSource,
) -> VerifiableFunction {
    let opt = option_of(payload);
    let s = adt("test::S", vec![("o", opt.clone())]);
    let loaded = Rvalue::Use(Operand::Copy(Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Field(0)],
    }));
    let first = match source {
        OptionSource::LoadedFromMemory => {
            block(0, vec![assign(2, loaded.clone())], Terminator::Goto(BlockId(1)))
        }
        _ => block(0, vec![], call("test::mk", vec![], 2, 1)),
    };
    let mut payload_place = vec![Projection::Downcast(1), Projection::Field(0)];
    payload_place.extend(tail);
    let mut stmts = vec![
        assign(3, Rvalue::Use(Operand::Copy(Place { local: 2, projections: payload_place }))),
        assign(
            4,
            Rvalue::Use(Operand::Copy(Place {
                local: 3,
                projections: vec![Projection::Deref, Projection::Field(0)],
            })),
        ),
    ];
    match source {
        OptionSource::Redefined => stmts.push(assign(2, loaded)),
        OptionSource::MutBorrowedSlot => {
            stmts.push(assign(7, Rvalue::Ref { mutable: true, place: Place::local(2) }))
        }
        _ => {}
    }
    body(
        vec![
            (u8_ty(), Some("ret")),
            (shared(s), Some("s")),
            (opt.clone(), None),
            (t_ty, None),
            (usize_ty(), None),
            (Ty::Unit, None),
            (u8_ty(), None),
            (unique(opt), None),
        ],
        1,
        vec![first, block(1, stmts, call("test::poke", vec![], 5, 2))],
    )
}

fn trail_cell() -> Ty {
    adt("test::Q", vec![("col", usize_ty()), ("row", usize_ty())])
}

/// The name the guarded read `(*_3).0` is spelled by (the payload's pointee, folded).
fn payload_read_name(func: &VerifiableFunction) -> String {
    crate::place_to_var_name(
        func,
        &Place { local: 3, projections: vec![Projection::Deref, Projection::Field(0)] },
    )
}

#[test]
fn a_shared_payload_of_a_call_returned_option_keeps_its_pointee() {
    // `for t in &v { if t.col >= n { continue } poke(); t.col + 1 }`: `_2 = next(..)`,
    // `_3 = copy (_2 as Some).0`.
    let q = trail_cell();
    let func = option_payload_body(shared(q.clone()), shared(q), vec![], OptionSource::CallReturn);
    let read = payload_read_name(&func);
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(!stored.iter().any(|n| n == "_2" || n.starts_with("_2@")), "{stored:?}");
    assert!(!kills_any_under(&func, &[read.as_str()]), "{read}: {:?}", kills(&func));
}

#[test]
fn a_shared_element_of_a_call_returned_tuple_payload_keeps_its_pointee() {
    // `for (i, t) in v.iter().enumerate()`: `Option<(usize, &Q)>`,
    // `_3 = copy (_2 as Some).0.1`.
    let q = trail_cell();
    let payload = Ty::Tuple(vec![usize_ty(), shared(q.clone())]);
    let func = option_payload_body(
        payload,
        shared(q),
        vec![Projection::Field(1)],
        OptionSource::CallReturn,
    );
    let read = payload_read_name(&func);
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(!stored.iter().any(|n| n == "_2" || n.starts_with("_2@")), "{stored:?}");
    assert!(!kills_any_under(&func, &[read.as_str()]), "{read}: {:?}", kills(&func));
}

#[test]
fn an_option_payload_without_the_call_return_retag_is_havocked() {
    // Loaded from memory, given a second value, or with its slot handed out `&mut`: the
    // payload may hold raw-pointer bits, so the whole `Option` is named as before, and
    // the guarded read with it.
    for source in
        [OptionSource::LoadedFromMemory, OptionSource::Redefined, OptionSource::MutBorrowedSlot]
    {
        let q = trail_cell();
        let func = option_payload_body(shared(q.clone()), shared(q), vec![], source);
        let read = payload_read_name(&func);
        let stored = super::path_defs::stored_ref_pointee_names(&func);
        assert!(stored.iter().any(|n| n == "_2"), "{source:?}: {stored:?}");
        assert!(kills_any_under(&func, &[read.as_str()]), "{source:?} {read}: {:?}", kills(&func));
    }
}

#[test]
fn a_mut_payload_or_a_cell_behind_a_shared_payload_is_still_named() {
    // `Option<&mut Q>` (`iter_mut().next()`): the `&mut` payload's pointee is named.
    let q = trail_cell();
    let func = option_payload_body(unique(q.clone()), unique(q), vec![], OptionSource::CallReturn);
    let read = payload_read_name(&func);
    assert!(kills_any_under(&func, &[read.as_str()]), "{read}: {:?}", kills(&func));
    // `Option<&Cell<usize>>`: the shared payload's `UnsafeCell` bytes are written, in a
    // defined execution, through any copy a callee holds (INTERIOR-MUT-CHANNEL-1).
    let cell = adt("core::cell::Cell<usize>", vec![("value", usize_ty())]);
    let func =
        option_payload_body(shared(cell.clone()), shared(cell), vec![], OptionSource::CallReturn);
    let read = payload_read_name(&func);
    let stored = super::path_defs::stored_ref_pointee_names(&func);
    assert!(!stored.iter().any(|n| n == "_2"), "{stored:?}");
    assert!(kills_any_under(&func, &[read.as_str()]), "{read}: {:?}", kills(&func));
}

// ---------------------------------------------------------------------------------------
// CELL-NAME-TAIL-1 (2026-10-18; candidate-gate RCA precision D2): the NAMED cell question
// decides a user ADT named like a cell (`TrailCell`) by its recorded fields; the name tail
// still refuses std wrappers, unrecorded kinds and part-less renderings.
// ---------------------------------------------------------------------------------------

#[test]
fn a_user_type_named_like_a_cell_is_decided_by_its_fields() {
    let defs = trust_types::DatatypeDefs::default();
    let named = |ty: &Ty| super::path_defs::ty_may_hold_named_unsafe_cell(&defs, ty);
    let trail = adt("gate::TrailCell", vec![("row", usize_ty()), ("col", usize_ty())]);
    assert!(!named(&trail), "a user struct of two `usize`s holds no cell byte");
    // The byte question keeps its name refusal (unchanged).
    assert!(super::path_defs::ty_may_hold_unsafe_cell(&defs, &trail));

    // Controls: each still holds (or may hold) a named cell byte.
    let unsafe_cell = adt("core::cell::UnsafeCell<usize>", vec![("value", usize_ty())]);
    let controls: Vec<(&str, Ty)> = vec![
        ("std Cell", adt("core::cell::Cell<usize>", vec![("value", usize_ty())])),
        ("std UnsafeCell", unsafe_cell.clone()),
        (
            "user *Cell over an UnsafeCell",
            adt("gate::MyCell", vec![("n", usize_ty()), ("c", unsafe_cell)]),
        ),
        ("part-less user *Cell", adt("gate::OpaqueCell", vec![])),
        (
            "user *Cell of unrecorded kind",
            Ty::Adt {
                adt_kind: None,
                layout: None,
                variants: vec![].into(),
                name: "gate::KindlessCell".into(),
                fields: vec![("n".to_string(), usize_ty())].into(),
                disc_index_safe: false,
                faithful_enum_repr: None,
                enum_layout: None,
                arbitrary_precision: None,
                validity_wrapper: None,
            },
        ),
        (
            "by-name *Cell marker",
            Ty::Datatype { name: "gate::MarkerCell".into(), variants: vec![] },
        ),
    ];
    for (what, ty) in controls {
        assert!(named(&ty), "{what} must still be refused or walked to its cell");
    }

    // End to end on the kill list: `t: &TrailCell` out of a call-returned `Option` keeps
    // the guarded field across a call; `t: &MyCell` still names its cell field.
    let trail = adt("gate::TrailCell", vec![("col", usize_ty()), ("row", usize_ty())]);
    let func =
        option_payload_body(shared(trail.clone()), shared(trail), vec![], OptionSource::CallReturn);
    let read = payload_read_name(&func);
    assert!(!kills_any_under(&func, &[read.as_str()]), "{read}: {:?}", kills(&func));
    let my_cell = adt(
        "gate::MyCell",
        vec![("c", adt("core::cell::Cell<usize>", vec![("value", usize_ty())])), ("n", usize_ty())],
    );
    let func = option_payload_body(
        shared(my_cell.clone()),
        shared(my_cell),
        vec![],
        OptionSource::CallReturn,
    );
    let read = payload_read_name(&func);
    assert!(kills_any_under(&func, &[read.as_str()]), "{read}: {:?}", kills(&func));
}
