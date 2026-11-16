//! UNION-SIBLING-WRITE-1 (wave-24 review, 2026-10-12): a write through a union field
//! rewrites every overlapping sibling, so every write oracle carries the union value's
//! own name (`union_write_cover_name`) beside the destination's. Before it,
//! `u.a = x as u8; u.b = -56; if x < 0x80 { u.a + 0x7f }` kept `u.0 == x` across the
//! write of `u.1`, and the overflow row was kernel-certified (the advisory check was
//! elided). The real-MIR pins are in `tests/narrowing_cast_identity_realmir.rs`
//! (`a_union_sibling_write_liar_is_never_proved`).

use trust_types::{
    AdtKind, BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn field(local: usize, path: &[usize]) -> Place {
    Place { local, projections: path.iter().map(|&i| Projection::Field(i)).collect() }
}

fn stamped(name: &str, kind: AdtKind, fields: Vec<(String, Ty)>) -> Ty {
    let mut ty = Ty::adt(name, fields);
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(kind);
    }
    ty
}

/// `union V { a: u8, b: i8 }`, stamped as the extractor stamps it.
fn union_v() -> Ty {
    stamped("c::V", AdtKind::Union, vec![("a".into(), Ty::u8()), ("b".into(), Ty::i8())])
}

/// `struct S { a: u8, b: i8 }`, stamped.
fn struct_s() -> Ty {
    stamped("c::S", AdtKind::Struct, vec![("a".into(), Ty::u8()), ("b".into(), Ty::i8())])
}

/// `_0` ret, `_1: u32`, `_2: <two>`, `_3: u8`; `_2.0 = _1 as u8; _2.1 = -56; _3 = _2.0`.
fn func(two: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "c::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: [Ty::u8(), Ty::u32(), two, Ty::u8()]
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(field(2, &[0]), Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u8())),
                    assign(field(2, &[1]), Rvalue::Use(Operand::Constant(ConstValue::Int(-56)))),
                    assign(Place::local(3), Rvalue::Use(Operand::Copy(field(2, &[0])))),
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u8(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// A union field write is a write of the union value for every oracle: the cover is the
/// union's own name, the per-statement search, the gen-sets and the indexed oracle all
/// see the write of `u.1` rebind `u.0`. FAILS BEFORE: no cover existed and `u.1` never
/// rebound `u.0`.
#[test]
fn a_union_field_write_rebinds_its_siblings() {
    let f = func(union_v());
    let u = crate::place_to_var_name(&f, &Place::local(2));
    let u0 = crate::place_to_var_name(&f, &field(2, &[0]));
    assert_eq!(super::union_write_cover_name(&f, &field(2, &[1])), Some(u.clone()));
    assert_eq!(super::union_write_cover_name(&f, &Place::local(2)), None, "a whole write");
    let block = &f.body.blocks[0];
    assert!(super::stmt_writes_name(&f, block, 1, &u0), "`u.1 = -56` writes `u.0`");
    let mut direct = trust_types::fx::FxHashSet::default();
    super::stmt_direct_write_names(&f, &block.stmts[1], &mut direct);
    assert!(direct.contains(&u), "{direct:?}");
    assert!(super::block_written_names(&f, block).contains(&u));
    let writes = crate::generate::block_writes::FnWrites::build(&f);
    assert_eq!(writes.last_writer_before(0, 2, &u0), Some(1), "indexed oracle");
}

/// The controls: a stamped STRUCT's sibling fields stay disjoint (no cover), and a
/// tuple's too.
#[test]
fn a_struct_or_tuple_field_write_has_no_cover() {
    let f = func(struct_s());
    assert_eq!(super::union_write_cover_name(&f, &field(2, &[1])), None);
    let u0 = crate::place_to_var_name(&f, &field(2, &[0]));
    assert!(!super::stmt_writes_name(&f, &f.body.blocks[0], 1, &u0));
    let t = func(Ty::Tuple(vec![Ty::u8(), Ty::i8()]));
    assert_eq!(super::union_write_cover_name(&t, &field(2, &[1])), None);
}

/// The FIRST union on the chain is the cover (a union inside a struct field covers the
/// struct's field, not the struct), and an unstamped ADT is read as a possible union
/// (fail-closed: the extractor stamps every rustc ADT).
#[test]
fn the_cover_is_the_first_union_on_the_chain() {
    let outer =
        stamped("c::O", AdtKind::Struct, vec![("x".into(), Ty::u8()), ("u".into(), union_v())]);
    let f = func(outer);
    let s1 = crate::place_to_var_name(&f, &field(2, &[1]));
    assert_eq!(super::union_write_cover_name(&f, &field(2, &[1, 1])), Some(s1));
    assert_eq!(super::union_write_cover_name(&f, &field(2, &[0])), None);
    let g = func(Ty::adt("c::Unstamped", vec![("a".into(), Ty::u8()), ("b".into(), Ty::i8())]));
    assert!(super::union_write_cover_name(&g, &field(2, &[1])).is_some(), "unstamped: fail-closed");
}

// ---------------------------------------------------------------------------------------
// UNION-SIBLING-WRITE-2 (review of INTERVAL-WRITE-LOCKSTEP-2, 2026-10-12): a write to a
// union field THROUGH A POINTER. The cover was taken on the syntactic place, so a store
// `(*r) = n` through `r = &mut u.b` (named `u.1` by the referent fold) had none, and a
// pointer into a union field put only `u.1` on the havoc list (a call it is handed to, an
// opaque store through a two-referent `&mut`), never `u`. On the stage 1 of `0f03df468d`
// each shape elided the overflow check of `u.a = 5; <write of u.b>; u.a + (MAX - 5)`
// (or, for the two-referent store, PROVED its row). The real-MIR pins are in
// `tests/union_sibling_write_ref_realmir.rs`.
// ---------------------------------------------------------------------------------------

/// `union U { a: usize, b: usize }`, stamped.
fn union_u() -> Ty {
    stamped("c::U", AdtKind::Union, vec![("a".into(), Ty::usize()), ("b".into(), Ty::usize())])
}

/// `struct P { a: usize, b: usize }`, stamped: the control, whose fields are disjoint.
fn struct_p() -> Ty {
    stamped("c::P", AdtKind::Struct, vec![("a".into(), Ty::usize()), ("b".into(), Ty::usize())])
}

fn mut_ref(ty: Ty) -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(ty) }
}

fn deref(local: usize) -> Place {
    Place { local, projections: vec![Projection::Deref] }
}

fn five() -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 64)))
}

/// `_0: usize`, `_1: usize` (n), `_2: <two>` (u), `_3: &mut usize` (r), `_4: usize`
/// (other), `_5: usize` (y), over `blocks`.
fn through(two: Ty, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    let mut f = func(two.clone());
    f.body.locals = [Ty::usize(), Ty::usize(), two, mut_ref(Ty::usize()), Ty::usize(), Ty::usize()]
        .into_iter()
        .enumerate()
        .map(|(index, ty)| LocalDecl { index, ty, name: None })
        .collect();
    f.body.blocks = blocks;
    f.body.return_ty = Ty::usize();
    f
}

/// `u.0 = 5; r = &mut u.1; (*r) = n; y = u.0` — the review's `d1` (`lk2.rs`).
fn store_through_ref(two: Ty) -> VerifiableFunction {
    through(
        two,
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(field(2, &[0]), five()),
                assign(Place::local(3), Rvalue::Ref { mutable: true, place: field(2, &[1]) }),
                assign(deref(3), Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(Place::local(5), Rvalue::Use(Operand::Copy(field(2, &[0])))),
            ],
            terminator: Terminator::Return,
        }],
    )
}

/// A store through a reference into a union field rebinds the siblings in every
/// oracle: the cover is taken on the place the store's NAME is minted from (`u.1`, the
/// fold of `(*r)`). FAILS BEFORE: the cover of `(*r)` was `None` (no `Field` projection
/// on the syntactic place), and no oracle saw the store write `u.0`. The STRUCT control
/// keeps its sibling.
#[test]
fn a_store_through_a_reference_into_a_union_field_rebinds_its_siblings() {
    for (two, union) in [(union_u(), true), (struct_p(), false)] {
        let f = store_through_ref(two);
        let u = crate::place_to_var_name(&f, &Place::local(2));
        let u0 = crate::place_to_var_name(&f, &field(2, &[0]));
        assert_eq!(
            crate::place_to_var_name(&f, &deref(3)),
            crate::place_to_var_name(&f, &field(2, &[1])),
            "premise: the store through `r` is named by its referent `u.1`"
        );
        assert_eq!(super::union_write_cover_name(&f, &deref(3)), union.then(|| u.clone()));
        let block = &f.body.blocks[0];
        assert_eq!(super::stmt_writes_name(&f, block, 2, &u0), union, "union={union}");
        let mut direct = trust_types::fx::FxHashSet::default();
        super::stmt_direct_write_names(&f, &block.stmts[2], &mut direct);
        assert_eq!(direct.contains(&u), union, "{direct:?}");
        let writes = crate::generate::block_writes::FnWrites::build(&f);
        let want = if union { Some(2) } else { Some(0) };
        assert_eq!(writes.last_writer_before(0, 3, &u0), want, "indexed oracle, union={union}");
    }
}

/// The union nested in a struct (`&mut s.u.b`, the review's `d3`): the cover is the
/// struct's union field `s.1`, not the struct.
#[test]
fn a_store_through_a_reference_into_a_nested_union_field_covers_the_union_field() {
    let outer =
        stamped("c::S", AdtKind::Struct, vec![("k".into(), Ty::usize()), ("u".into(), union_u())]);
    let mut f = store_through_ref(outer);
    for stmt in &mut f.body.blocks[0].stmts {
        let Statement::Assign { place, rvalue, .. } = stmt else { continue };
        if place.local == 2 {
            *place = field(2, &[1, 0]);
        }
        match rvalue {
            Rvalue::Ref { place, .. } => *place = field(2, &[1, 1]),
            Rvalue::Use(Operand::Copy(place)) if place.local == 2 => *place = field(2, &[1, 0]),
            _ => {}
        }
    }
    let s1 = crate::place_to_var_name(&f, &field(2, &[1]));
    let s10 = crate::place_to_var_name(&f, &field(2, &[1, 0]));
    assert_eq!(super::union_write_cover_name(&f, &deref(3)), Some(s1));
    assert!(super::stmt_writes_name(&f, &f.body.blocks[0], 2, &s10));
    let s0 = crate::place_to_var_name(&f, &field(2, &[0]));
    assert!(!super::stmt_writes_name(&f, &f.body.blocks[0], 2, &s0), "`s.k` is disjoint");
}

/// `u.0 = 5; r = if n > 0 { &mut u.1 } else { &mut other }; (*r) = n; y = u.0` — the
/// review's `b4`: `r` has two values, so the store is OPAQUE and havocs the
/// whole-function list. FAILS BEFORE: the list carried the borrowed field `u.1` and not
/// the union, so `u.0` survived the store (the row was PROVED on the stage 1). The
/// STRUCT control keeps `u.0`.
#[test]
fn a_pointer_into_a_union_field_puts_the_union_on_the_havoc_list() {
    let two_referent = |two: Ty| {
        through(
            two,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(field(2, &[0]), five())],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::Ref { mutable: true, place: field(2, &[1]) },
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::Ref { mutable: true, place: Place::local(4) },
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![
                        assign(deref(3), Rvalue::Use(Operand::Copy(Place::local(1)))),
                        assign(Place::local(5), Rvalue::Use(Operand::Copy(field(2, &[0])))),
                    ],
                    terminator: Terminator::Return,
                },
            ],
        )
    };
    for (two, union) in [(union_u(), true), (struct_p(), false)] {
        let f = two_referent(two);
        let u = crate::place_to_var_name(&f, &Place::local(2));
        let u0 = crate::place_to_var_name(&f, &field(2, &[0]));
        assert!(super::write_havocs_function_list(&f, &deref(3)), "premise: an opaque store");
        let borrowed = super::mutably_borrowed_local_names(&f);
        assert_eq!(borrowed.contains(&u), union, "{borrowed:?}");
        assert_eq!(
            super::function_havoc_names(&f).iter().any(|h| super::write_rebinds(h, &u0)),
            union,
            "the whole-function list, union={union}"
        );
        assert_eq!(super::stmt_writes_name(&f, &f.body.blocks[3], 0, &u0), union, "union={union}");
        let writes = crate::generate::block_writes::FnWrites::build(&f);
        let want = if union { Some(0) } else { None };
        assert_eq!(writes.last_writer_before(3, 1, &u0), want, "indexed oracle, union={union}");
    }
}

/// `u.0 = 5; r = &mut u.1; set(move r, n); y = u.0` — the review's `b2`: a callee
/// handed a pointer into a union field writes the siblings. FAILS BEFORE: the call
/// havocked `u.1` (the borrowed place) and `r`, never `u`; on the stage 1 the overflow
/// check was elided and the binary printed 1. The STRUCT control keeps `u.0`.
#[test]
fn a_call_handed_a_pointer_into_a_union_field_rebinds_its_siblings() {
    let call = |two: Ty| {
        through(
            two,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        assign(field(2, &[0]), five()),
                        assign(
                            Place::local(3),
                            Rvalue::Ref { mutable: true, place: field(2, &[1]) },
                        ),
                    ],
                    terminator: Terminator::Call {
                        unwind: trust_types::UnwindEdge::Continue,
                        func: "c::set".into(),
                        args: vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(1))],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key("c::set"),
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        Place::local(5),
                        Rvalue::Use(Operand::Copy(field(2, &[0]))),
                    )],
                    terminator: Terminator::Return,
                },
            ],
        )
    };
    for (two, union) in [(union_u(), true), (struct_p(), false)] {
        let f = call(two);
        let u0 = crate::place_to_var_name(&f, &field(2, &[0]));
        let names = super::terminator_def_names(&f, &f.body.blocks[0]);
        assert_eq!(
            names.iter().any(|n| super::write_rebinds(n, &u0)),
            union,
            "union={union}: {names:?}"
        );
    }
}
