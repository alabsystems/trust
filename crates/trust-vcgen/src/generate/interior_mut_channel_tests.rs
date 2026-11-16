//! INTERIOR-MUT-CHANNEL-1 (2026-10-14, G2 of the verifier-gaps design): the
//! `UnsafeCell` bytes a SHARED reference or borrow reaches are a write channel. Each
//! row pins one piece of the rule on a synthetic body: the one walk
//! ([`super::unsafe_cell_places`]), its two halves on the havoc list
//! ([`super::stored_ref_pointee_names`]: the POINTEE half behind a retagged shared
//! reference, the SLOT half [`super::shared_borrowed_cell_places`]), and the stability
//! scans that ask it (`place_source_is_stable`, `place_is_body_stable`,
//! `stmt_escapes_local`). The verdict-level rows (each a real stage-1 dump, edited
//! where rustc keeps the cell API as calls) are in `tests/interior_mut_channel_realmir.rs`.

use trust_types::{
    AdtKind, BasicBlock, BlockId, LocalDecl, Place, Projection, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VariantDef, VerifiableBody, VerifiableFunction,
};

use super::{shared_borrowed_cell_places, stored_ref_pointee_names, unsafe_cell_places};
use crate::place_to_var_name;

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn place(local: usize, projections: Vec<Projection>) -> Place {
    Place { local, projections }
}

/// A struct the extractor stamped (`adt_kind: Some(Struct)`), as every real dump is.
fn stamped(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
    let mut ty = Ty::adt(name, fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect());
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(AdtKind::Struct);
    }
    ty
}

fn unsafe_cell(inner: Ty) -> Ty {
    stamped("core::cell::UnsafeCell<usize>", vec![("value", inner)])
}

/// The extractor's own `Cell<usize>` (local 2 of the `cello3.rs` dump in the design).
fn cell_usize() -> Ty {
    stamped("core::cell::Cell<usize>", vec![("value", unsafe_cell(Ty::usize()))])
}

/// `S { n: usize, c: Cell<usize> }`.
fn s_ty() -> Ty {
    stamped("c::S", vec![("n", Ty::usize()), ("c", cell_usize())])
}

fn shared(inner: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(inner) }
}

/// A one-block body over `locals` (indexed in order, `_1.._args` parameters) whose
/// statements are `stmts` and whose terminator is `term`.
fn body(
    locals: Vec<Ty>,
    args: usize,
    stmts: Vec<Statement>,
    term: Terminator,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "c::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: term }],
            arg_count: args,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn cells_of(ty: &Ty) -> Vec<Place> {
    let mut out = Vec::new();
    unsafe_cell_places(&Default::default(), &Place::local(1), ty, &mut out);
    out
}

/// The walk names a cell at the finest place a name can split, and nothing that holds
/// no cell. `st.1` for `S { n, c: Cell }`, never `st.0`.
#[test]
fn the_walk_names_the_cell_field_and_never_its_frozen_sibling() {
    assert_eq!(cells_of(&s_ty()), vec![place(1, vec![Projection::Field(1)])]);
    assert_eq!(cells_of(&cell_usize()), vec![Place::local(1)], "a cell wrapper is named whole");
    assert!(cells_of(&Ty::usize()).is_empty());
    assert!(cells_of(&stamped("c::Plain", vec![("a", Ty::usize())])).is_empty());
    assert!(
        cells_of(&Ty::Tuple(vec![Ty::usize(), cell_usize()]))
            == vec![place(1, vec![Projection::Field(1)])],
        "a tuple is split field by field"
    );
}

/// STRUCTURAL: an `UnsafeCell` two user structs deep, under names that look like no cell,
/// is found by the field walk (G2-M4: a name-only test answers "no cell" here).
#[test]
fn a_cell_under_user_names_is_found_by_structure() {
    let inner = stamped("c::Inner", vec![("u", unsafe_cell(Ty::u8()))]);
    let outer = stamped("c::Outer", vec![("k", Ty::u8()), ("inner", inner)]);
    assert_eq!(
        cells_of(&outer),
        vec![place(1, vec![Projection::Field(1), Projection::Field(0)])],
        "the raw `UnsafeCell` field itself, reached through two user structs"
    );
}

/// Fail-closed shapes are named whole: a stamped struct with no recorded field, an enum
/// with a cell in one variant, a slice or an array of cells, an undefined datatype
/// marker. A `Vec` (`Ty::Seq`) names only its length, which no `&Vec` holder can write.
#[test]
fn unrecorded_and_unsplittable_shapes_are_named_whole() {
    let whole = vec![Place::local(1)];
    assert_eq!(cells_of(&stamped("c::Opaque", Vec::new())), whole, "no recorded field");
    let en = Ty::adt_enum(
        "c::E",
        vec![
            VariantDef { name: "A".into(), discriminant: 0, fields: vec![("x".into(), Ty::u8())] },
            VariantDef {
                name: "B".into(),
                discriminant: 1,
                fields: vec![("c".into(), cell_usize())],
            },
        ],
    );
    assert_eq!(cells_of(&en), whole, "an enum with a cell in one variant");
    assert_eq!(cells_of(&Ty::Slice { elem: Box::new(cell_usize()) }), whole, "a slice of cells");
    assert_eq!(cells_of(&Ty::Array { elem: Box::new(cell_usize()), len: 2 }), whole);
    assert_eq!(
        cells_of(&Ty::Datatype { name: "c::Undefined".into(), variants: Vec::new() }),
        whole,
        "an unresolved by-name marker"
    );
    assert!(cells_of(&Ty::Slice { elem: Box::new(Ty::u8()) }).is_empty());
    assert!(cells_of(&Ty::Seq { elem: Box::new(cell_usize()), drop_auth: None }).is_empty());
    assert!(
        cells_of(&Ty::adt("alloc::vec::Vec<u8>", Vec::new())).is_empty(),
        "a field-less std `Vec` names nothing, as `Ty::Seq` does"
    );
    assert_eq!(
        cells_of(&Ty::adt("c::Vec<u8>", Vec::new())),
        whole,
        "a user type merely named `Vec` is no std `Vec`"
    );
    assert!(cells_of(&shared(cell_usize())).is_empty(), "behind `&` is not inline");
}

/// A by-name datatype marker is RESOLVED through the body's table: a cell-free
/// recursive enum names nothing (G2-M9: failing closed on every marker would name it).
#[test]
fn a_resolved_datatype_marker_is_walked_and_an_unresolved_one_is_not() {
    let marker = Ty::Datatype { name: "c::List".into(), variants: Vec::new() };
    let list = Ty::Datatype {
        name: "c::List".into(),
        variants: vec![
            ("Nil".into(), Vec::new()),
            ("Cons".into(), vec![("h".into(), Ty::u8()), ("t".into(), shared(marker.clone()))]),
        ],
    };
    let mut defs: trust_types::DatatypeDefs = Default::default();
    defs.insert("c::List".into(), list);
    let mut out = Vec::new();
    unsafe_cell_places(&defs, &Place::local(1), &marker, &mut out);
    assert!(out.is_empty(), "a cell-free recursive datatype holds no cell: {out:?}");
    let mut out = Vec::new();
    unsafe_cell_places(&Default::default(), &Place::local(1), &marker, &mut out);
    assert_eq!(out, vec![Place::local(1)], "undefined in this body's table");
}

/// THE SLOT HALF: `_2 = &st` with `st: S { n, c: Cell }` puts `st.1` (and never `st.0`)
/// on the call-havoc names, and makes the local unstable while `st.0` stays stable.
#[test]
fn a_shared_borrow_of_an_owned_cell_names_the_cell_and_not_the_sibling() {
    let f = body(
        vec![Ty::Unit, s_ty(), shared(s_ty())],
        0,
        vec![assign(Place::local(2), Rvalue::Ref { mutable: false, place: Place::local(1) })],
        Terminator::Return,
    );
    let cell = place(1, vec![Projection::Field(1)]);
    assert_eq!(shared_borrowed_cell_places(&f, 1).as_ref(), &vec![cell.clone()]);
    let names = stored_ref_pointee_names(&f);
    let cell_name = place_to_var_name(&f, &cell);
    let sibling = place_to_var_name(&f, &place(1, vec![Projection::Field(0)]));
    assert!(names.contains(&cell_name), "`{cell_name}` must be havocked: {names:?}");
    assert!(!names.contains(&sibling), "the frozen sibling `{sibling}` keeps its facts");
    assert!(!crate::place_source_is_stable(&f, 1), "the local's own bytes change through `&st`");
    assert!(crate::slot_source_is_stable(&f, 1), "its slot rule alone does not see the cell");
    assert!(crate::place_is_body_stable(&f, &place(1, vec![Projection::Field(0)])), "`st.0`");
    assert!(!crate::place_is_body_stable(&f, &cell), "`st.1`");
    let stmt = &f.body.blocks[0].stmts[0];
    assert!(crate::stmt_escapes_local(&f, stmt, 1), "`&st` hands out the cell");
    assert!(!stmt.escapes_local(1), "the cell-blind question says no");
}

/// The `Freeze` control: the same borrow of a cell-free local is no channel.
#[test]
fn a_shared_borrow_of_freeze_data_is_no_channel() {
    let plain = stamped("c::P", vec![("n", Ty::usize()), ("m", Ty::usize())]);
    let f = body(
        vec![Ty::Unit, plain.clone(), shared(plain)],
        0,
        vec![assign(Place::local(2), Rvalue::Ref { mutable: false, place: Place::local(1) })],
        Terminator::Return,
    );
    assert!(shared_borrowed_cell_places(&f, 1).is_empty());
    assert!(crate::place_source_is_stable(&f, 1));
    assert!(!crate::stmt_escapes_local(&f, &f.body.blocks[0].stmts[0], 1));
}

/// VCGEN-LIB-REDS-1: the drop-narrowed stability question
/// (`place_source_is_stable_modulo_whole_drops`, asked by the witness candidate walk)
/// skips a WHOLE-local `Drop` and nothing else, so it keeps the cell clause. Over the
/// same `&st; Drop(st)` body, the cell-holding `S` is refused (its slot half alone
/// accepts through the drop) while the `Freeze` twin is accepted, which the shared
/// question, counting the drop as a write, refuses.
#[test]
fn the_drop_narrowed_stability_question_keeps_the_cell_clause() {
    let borrow_then_drop = |ty: Ty| {
        let mut f = body(
            vec![Ty::Unit, ty.clone(), shared(ty)],
            0,
            vec![assign(Place::local(2), Rvalue::Ref { mutable: false, place: Place::local(1) })],
            Terminator::Drop {
                place: Place::local(1),
                target: BlockId(1),
                span: SourceSpan::default(),
                unwind: Default::default(),
            },
        );
        f.body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        });
        f
    };
    let cell = borrow_then_drop(s_ty());
    assert!(
        crate::local_defs::body_slot_is_stable_modulo_whole_drops(&cell.body, 1),
        "the slot half reads the whole drop as the end of the value"
    );
    assert!(
        !crate::place_source_is_stable_modulo_whole_drops(&cell, 1),
        "`&st` still hands out `st.1`'s bytes"
    );
    let plain = stamped("c::P", vec![("n", Ty::usize()), ("m", Ty::usize())]);
    let frozen = borrow_then_drop(plain);
    assert!(crate::place_source_is_stable_modulo_whole_drops(&frozen, 1));
    assert!(!crate::place_source_is_stable(&frozen, 1), "the shared question counts the drop");
}

/// VCGEN-CENSUS-SITE-REDS-1: the witness walk's drop-narrowed question is ONE cell-aware
/// rule (`trust_types::local_defs::source_value_is_stable_modulo_whole_drops`), and its
/// two-part spelling (the cell-blind slot half `body_slot_is_stable_modulo_whole_drops`
/// conjoined with an empty `shared_borrowed_cell_places`, what
/// `place_source_is_stable_modulo_whole_drops` asks) agrees with it, shape by shape, along
/// BOTH of the slot half's paths: outside any `FuncAnalysisScope` (no index is bound, so
/// it is the unindexed trust-types walk), and inside one bound to the shape's function,
/// which is how production asks — `LocalWriteIndex::visit_located_slot_writes` on the
/// first question, filling the per-local cache, and that cache on the second. The cached
/// slot answer is also held to the unindexed slot walk, so the indexed visit is pinned
/// on its own and not only through the conjunction (a `Cell` borrow makes the cell clause
/// decide). Every shape is borrowed and then dropped whole, so the narrowing is exercised
/// on each; the expected column is the soundness answer, not either implementation's: a
/// shared borrow of a `Cell` byte (whole, or the cell field alone) is a write channel, a
/// shared borrow of `Freeze` bytes (a cell-free struct, or the frozen sibling field) is
/// none, and `&mut` / `&raw const` of anything is one.
///
/// Trust: 2026-11-07 (VCGEN-CENSUS-SITE-REDS-1, fix-forward): this fixture first ran
/// outside any scope only, so its "routed" column was the same unindexed walk as its
/// slot column, and a mutant deleting the indexed visitor's `Escape` emission (`&mut p`
/// then a whole `Drop` reading as stable under a scope: a false stability fact) passed
/// it. The scoped column fails that mutant on `&mut p` and `&raw const p` by its own
/// assertions (it runs with the test-time differential off, so the harness is not what
/// catches it).
#[test]
fn the_drop_narrowed_question_is_the_cell_aware_rule() {
    let plain = stamped("c::P", vec![("n", Ty::usize()), ("m", Ty::usize())]);
    let shapes: Vec<(&str, Ty, Rvalue, Ty, bool)> = vec![
        (
            "&st, st: S{n, Cell}",
            s_ty(),
            Rvalue::Ref { mutable: false, place: Place::local(1) },
            shared(s_ty()),
            false,
        ),
        (
            "&st.1 (the cell)",
            s_ty(),
            Rvalue::Ref { mutable: false, place: place(1, vec![Projection::Field(1)]) },
            shared(cell_usize()),
            false,
        ),
        (
            "&st.0 (the frozen sibling)",
            s_ty(),
            Rvalue::Ref { mutable: false, place: place(1, vec![Projection::Field(0)]) },
            shared(Ty::usize()),
            true,
        ),
        (
            "&p, p: Freeze",
            plain.clone(),
            Rvalue::Ref { mutable: false, place: Place::local(1) },
            shared(plain.clone()),
            true,
        ),
        (
            "&mut p",
            plain.clone(),
            Rvalue::Ref { mutable: true, place: Place::local(1) },
            Ty::Ref { mutable: true, inner: Box::new(plain.clone()) },
            false,
        ),
        (
            "&raw const p",
            plain.clone(),
            Rvalue::AddressOf(false, Place::local(1)),
            Ty::RawPtr { mutable: false, pointee: Box::new(plain.clone()) },
            false,
        ),
        (
            "&c, c: Cell<usize>",
            cell_usize(),
            Rvalue::Ref { mutable: false, place: Place::local(1) },
            shared(cell_usize()),
            false,
        ),
    ];
    for (label, ty, borrow, borrow_ty, stable) in shapes {
        let mut f = body(
            vec![Ty::Unit, ty, borrow_ty],
            0,
            vec![assign(Place::local(2), borrow)],
            Terminator::Drop {
                place: Place::local(1),
                target: BlockId(1),
                span: SourceSpan::default(),
                unwind: Default::default(),
            },
        );
        f.body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        });
        let rule = trust_types::local_defs::source_value_is_stable_modulo_whole_drops(&f.body, 1);
        let slot_rule =
            trust_types::local_defs::source_slot_is_stable_modulo_whole_drops(&f.body, 1);
        let slot_half = slot_rule && shared_borrowed_cell_places(&f, 1).is_empty();
        assert!(
            crate::generate::local_write_index_for(&f.body).is_none(),
            "{label}: outside a scope no index is bound, so this column is the unindexed walk"
        );
        let unindexed = crate::place_source_is_stable_modulo_whole_drops(&f, 1);
        assert_eq!(unindexed, rule, "{label}: the witness walk's spelling, unindexed");
        assert_eq!(slot_half, rule, "{label}: the shared slot half plus the cell clause");
        assert_eq!(rule, stable, "{label}: the soundness answer");
        // The scoped questions run with the test-time differential OFF, so these
        // assertions decide, not the differential's own `assert_eq!` inside
        // `body_slot_is_stable_modulo_whole_drops` (which is on by default in this
        // binary and would otherwise fire first on a disagreement).
        crate::generate::legacy_version_oracle::without_differential(|| {
            let _scope = crate::generate::FuncAnalysisScope::enter(&f);
            let index = crate::generate::local_write_index_for(&f.body)
                .unwrap_or_else(|| panic!("{label}: a scope bound to `f` binds its index"));
            assert_eq!(index.cached_slot_stable_modulo_whole_drops(1), None, "{label}: cold");
            let indexed = crate::place_source_is_stable_modulo_whole_drops(&f, 1);
            assert_eq!(
                index.cached_slot_stable_modulo_whole_drops(1),
                Some(slot_rule),
                "{label}: the indexed visit answered (and cached) the slot half as the \
                 unindexed slot walk does"
            );
            let cached = crate::place_source_is_stable_modulo_whole_drops(&f, 1);
            assert_eq!(indexed, rule, "{label}: the witness walk's spelling, indexed");
            assert_eq!(cached, rule, "{label}: the witness walk's spelling, from the cache");
        });
        assert!(
            crate::generate::local_write_index_for(&f.body).is_none(),
            "{label}: the scope closed"
        );
    }
}

/// THE POINTEE HALF: the cell bytes behind a retagged shared reference PARAMETER are
/// named (`w*.1` for `w: &S`, never `w*.0`; `c*` for `c: &Cell`; `a*` for a slice of
/// cells), and a `&usize` parameter names nothing.
#[test]
fn the_cells_behind_a_shared_reference_parameter_are_named() {
    let cases: Vec<(Ty, Vec<Projection>)> = vec![
        (shared(s_ty()), vec![Projection::Deref, Projection::Field(1)]),
        (shared(cell_usize()), vec![Projection::Deref]),
        (shared(Ty::Slice { elem: Box::new(cell_usize()) }), vec![Projection::Deref]),
    ];
    for (ty, cell) in cases {
        let f = body(vec![Ty::Unit, ty.clone()], 1, Vec::new(), Terminator::Return);
        let names = stored_ref_pointee_names(&f);
        let want = place_to_var_name(&f, &place(1, cell));
        assert!(names.contains(&want), "{ty:?}: `{want}` must be havocked: {names:?}");
    }
    let f = body(vec![Ty::Unit, shared(s_ty())], 1, Vec::new(), Terminator::Return);
    let sibling = place_to_var_name(&f, &place(1, vec![Projection::Deref, Projection::Field(0)]));
    assert!(!stored_ref_pointee_names(&f).contains(&sibling), "`{sibling}` stays frozen");
    let f = body(vec![Ty::Unit, shared(Ty::usize())], 1, Vec::new(), Terminator::Return);
    assert!(stored_ref_pointee_names(&f).is_empty(), "a `&usize` parameter is frozen");
}

/// A place behind a shared root's `Deref` whose own bytes may hold a cell is unstable;
/// its frozen sibling is not.
#[test]
fn a_cell_behind_a_shared_root_is_not_body_stable() {
    let f = body(vec![Ty::Unit, shared(s_ty())], 1, Vec::new(), Terminator::Return);
    assert!(crate::place_is_body_stable(
        &f,
        &place(1, vec![Projection::Deref, Projection::Field(0)])
    ));
    assert!(!crate::place_is_body_stable(
        &f,
        &place(1, vec![Projection::Deref, Projection::Field(1)])
    ));
}

/// The shared borrow is attributed to the root it borrows from, and only for the
/// root's own storage: a borrow THROUGH a reference (`&(*r).1`) is the pointer's channel.
#[test]
fn a_borrow_through_a_reference_is_not_the_slot_half() {
    let f = body(
        vec![Ty::Unit, shared(s_ty()), shared(cell_usize())],
        1,
        vec![assign(
            Place::local(2),
            Rvalue::Ref {
                mutable: false,
                place: place(1, vec![Projection::Deref, Projection::Field(1)]),
            },
        )],
        Terminator::Return,
    );
    assert!(shared_borrowed_cell_places(&f, 1).is_empty());
    assert!(!crate::stmt_escapes_local(&f, &f.body.blocks[0].stmts[0], 1));
    let names = stored_ref_pointee_names(&f);
    let want = place_to_var_name(&f, &place(1, vec![Projection::Deref, Projection::Field(1)]));
    assert!(names.contains(&want), "the POINTEE half names `{want}`: {names:?}");
}

/// `alloc::string::String` as the extractor renders it: `{ vec: Seq<u8> }`.
fn string_ty() -> Ty {
    stamped("alloc::string::String", vec![("vec", vec_of(Ty::u8()))])
}

fn vec_of(elem: Ty) -> Ty {
    Ty::Seq { elem: Box::new(elem), drop_auth: None }
}

fn option_of(inner: Ty) -> Ty {
    Ty::adt_enum(
        "core::option::Option",
        vec![
            VariantDef { name: "None".into(), discriminant: 0, fields: Vec::new() },
            VariantDef { name: "Some".into(), discriminant: 1, fields: vec![("0".into(), inner)] },
        ],
    )
}

/// `enum E { A(a), B(b) }`.
fn two_variants(a: Ty, b: Ty) -> Ty {
    Ty::adt_enum(
        "c::E",
        vec![
            VariantDef { name: "A".into(), discriminant: 0, fields: vec![("0".into(), a)] },
            VariantDef { name: "B".into(), discriminant: 1, fields: vec![("0".into(), b)] },
        ],
    )
}

/// G2-OPTSTRING-1 (2026-10-15): a shape whose only `UnsafeCell` bytes could be a std
/// `Vec`'s (its allocator, which `Ty::Seq` drops) holds no NAMED cell byte, so it is
/// named nowhere: an enum, a tuple, an array or an `Option` over a `Vec` or a `String`.
/// The names that reach into a `Vec`'s bytes are its length and an enclosing enum's
/// discriminant, neither in a cell (`UnsafeCell` disables niches); its elements, cells
/// or not, are behind its pointer. The BYTE question still refuses every one of them.
#[test]
fn a_shape_whose_only_cell_bytes_are_a_vecs_names_nothing() {
    let defs = Default::default();
    for (what, ty) in [
        ("Option<String>", option_of(string_ty())),
        ("Option<Vec<u8>>", option_of(vec_of(Ty::u8()))),
        ("an enum over a Vec", two_variants(vec_of(Ty::u8()), Ty::u8())),
        ("(u32, Vec<u8>)", Ty::Tuple(vec![Ty::u32(), vec_of(Ty::u8())])),
        ("[String; 2]", Ty::Array { elem: Box::new(string_ty()), len: 2 }),
        ("Vec<Cell<usize>>", vec_of(cell_usize())),
        ("Option<Vec<Cell<usize>>>", option_of(vec_of(cell_usize()))),
        ("Option<field-less std Vec>", option_of(Ty::adt("alloc::vec::Vec<u8>", Vec::new()))),
    ] {
        assert!(cells_of(&ty).is_empty(), "{what} names nothing: {:?}", cells_of(&ty));
        assert!(!super::ty_may_hold_named_unsafe_cell(&defs, &ty), "{what}");
        assert!(super::ty_may_hold_unsafe_cell(&defs, &ty), "{what}: the byte question refuses");
    }
}

/// G2-OPTSTRING-1, the other direction: a cell BESIDE or AROUND a `Vec` keeps its
/// channel. `Option<Cell>` and an enum with a `Cell` payload are named whole, a `Vec`
/// holder's `Cell` sibling by its field, a `RefCell<Vec>` (whose holder resizes the
/// `Vec` through `&`) and a `Cell<Vec>` whole. A user type spelled like std's `String`
/// (exactly, or under the impersonation stamp) is walked, not granted by its name, and a
/// field-less type at a stamped or user `Vec` path is no std `Vec`.
#[test]
fn a_cell_beside_or_around_a_vec_keeps_its_channel() {
    let whole = vec![Place::local(1)];
    assert_eq!(cells_of(&option_of(cell_usize())), whole, "Option<Cell<usize>>");
    assert_eq!(cells_of(&two_variants(vec_of(Ty::u8()), cell_usize())), whole, "a Cell payload");
    let holder = stamped("c::H", vec![("v", vec_of(Ty::u8())), ("c", cell_usize())]);
    assert_eq!(cells_of(&holder), vec![place(1, vec![Projection::Field(1)])], "never `.0`");
    assert_eq!(cells_of(&option_of(holder)), whole, "an Option of that holder");
    let refcell_vec = stamped(
        "core::cell::RefCell<alloc::vec::Vec<u8>>",
        vec![("borrow", cell_usize()), ("value", unsafe_cell(vec_of(Ty::u8())))],
    );
    assert_eq!(cells_of(&refcell_vec), whole, "RefCell<Vec<u8>>");
    let cell_vec = stamped(
        "core::cell::Cell<alloc::vec::Vec<u8>>",
        vec![("value", unsafe_cell(vec_of(Ty::u8())))],
    );
    assert_eq!(cells_of(&cell_vec), whole, "Cell<Vec<u8>>");
    assert_eq!(cells_of(&option_of(cell_vec)), whole, "Option<Cell<Vec<u8>>>");
    for name in ["alloc::string::String", "__trust_crate@1973d11b2baa21fa::alloc::string::String"] {
        let forged = stamped(name, vec![("vec", vec_of(Ty::u8())), ("flag", cell_usize())]);
        assert_eq!(cells_of(&forged), vec![place(1, vec![Projection::Field(1)])], "{name}");
        assert_eq!(cells_of(&option_of(forged)), whole, "Option<{name}>");
    }
    for name in ["__trust_crate@1973d11b2baa21fa::alloc::vec::Vec<u8>", "c::Vec<u8>"] {
        assert_eq!(cells_of(&option_of(Ty::adt(name, Vec::new()))), whole, "Option<{name}>");
    }
}

/// G2-OPTSTRING-1 on both halves of the channel. THE POINTEE HALF: `x: &Option<String>`
/// (the `unwrap_facts` `ref_as_ref` parameter) names nothing, and `*x` is body-stable, so
/// its tag keeps the `is_some` fact across calls; `x: &Option<Cell<usize>>` names `x*`
/// and `*x` is not stable. THE SLOT HALF: `&o` of an owned `Option<String>` is no
/// channel; of an owned `Option<Cell<usize>>` it is.
#[test]
fn an_option_of_a_string_is_no_channel_and_an_option_of_a_cell_is() {
    let deref = place(1, vec![Projection::Deref]);
    let f = body(vec![Ty::Unit, shared(option_of(string_ty()))], 1, Vec::new(), Terminator::Return);
    assert!(stored_ref_pointee_names(&f).is_empty(), "{:?}", stored_ref_pointee_names(&f));
    assert!(crate::place_is_body_stable(&f, &deref), "`*x` of `&Option<String>`");
    let f =
        body(vec![Ty::Unit, shared(option_of(cell_usize()))], 1, Vec::new(), Terminator::Return);
    let want = place_to_var_name(&f, &deref);
    assert!(stored_ref_pointee_names(&f).contains(&want), "`{want}` must be havocked");
    assert!(!crate::place_is_body_stable(&f, &deref), "`*x` of `&Option<Cell<usize>>`");
    for (ty, channel) in [(option_of(string_ty()), false), (option_of(cell_usize()), true)] {
        let f = body(
            vec![Ty::Unit, ty.clone(), shared(ty)],
            0,
            vec![assign(Place::local(2), Rvalue::Ref { mutable: false, place: Place::local(1) })],
            Terminator::Return,
        );
        assert_eq!(!shared_borrowed_cell_places(&f, 1).is_empty(), channel);
        assert_eq!(crate::place_source_is_stable(&f, 1), !channel);
        assert_eq!(crate::stmt_escapes_local(&f, &f.body.blocks[0].stmts[0], 1), channel);
    }
}

/// G2-OPTSTRING-1, `Vec<Cell<usize>>` where it matters: the `Vec`'s own storage names no
/// cell (its elements are behind its pointer), and the element a call hands back
/// (`_3 = <Vec<Cell<usize>> as Index<usize>>::index(move _2, ..)`, `_3: &Cell<usize>`) is
/// a retagged shared reference whose pointee `_3*` IS named.
#[test]
fn a_vec_of_cells_names_its_element_through_the_call_result() {
    let elems = vec_of(cell_usize());
    let mut f = body(
        vec![Ty::Unit, elems.clone(), shared(elems), shared(cell_usize())],
        0,
        vec![assign(Place::local(2), Rvalue::Ref { mutable: false, place: Place::local(1) })],
        Terminator::Call {
            unwind: trust_types::UnwindEdge::Unreachable,
            func: "<alloc::vec::Vec<core::cell::Cell<usize>> as core::ops::Index<usize>>::index"
                .into(),
            args: vec![trust_types::Operand::Move(Place::local(2))],
            dest: Place::local(3),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: None,
            is_foreign: false,
        },
    );
    f.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: Vec::new(),
        terminator: Terminator::Return,
    });
    assert!(shared_borrowed_cell_places(&f, 1).is_empty(), "`&v` holds no cell byte of `v`");
    assert!(!crate::stmt_escapes_local(&f, &f.body.blocks[0].stmts[0], 1));
    let names = stored_ref_pointee_names(&f);
    let element = place_to_var_name(&f, &place(3, vec![Projection::Deref]));
    assert!(names.contains(&element), "the element `{element}` must be havocked: {names:?}");
}

/// G2-OPTSTRING-1, the union exception: a union's other fields name every byte of a
/// `Vec` field (`u.n` beside `u.v: ManuallyDrop<Vec<u8, A>>` reads `A`'s cell bytes
/// too), so a union over a `Vec` is asked the BYTE question and named whole, alone or
/// inside an `Option`; so is a variant-less ADT whose kind was not recorded (it may be a
/// union). The same `ManuallyDrop<Vec<u8>>` as a struct names nothing.
#[test]
fn a_union_over_a_vec_keeps_its_channel() {
    let whole = vec![Place::local(1)];
    let manually_drop_vec =
        stamped("core::mem::ManuallyDrop<alloc::vec::Vec<u8>>", vec![("value", vec_of(Ty::u8()))]);
    assert!(cells_of(&manually_drop_vec).is_empty(), "a struct over a Vec names nothing");
    let mut union = Ty::adt(
        "c::U",
        vec![
            ("v".into(), manually_drop_vec),
            ("n".into(), Ty::Array { elem: Box::new(Ty::u8()), len: 24 }),
        ],
    );
    if let Ty::Adt { adt_kind, .. } = &mut union {
        *adt_kind = Some(AdtKind::Union);
    }
    assert!(super::ty_may_hold_named_unsafe_cell(&Default::default(), &union));
    assert_eq!(cells_of(&union), whole, "a union over a Vec");
    assert_eq!(cells_of(&option_of(union)), whole, "an Option of that union");
    let unrecorded = Ty::adt("c::K", vec![("v".into(), vec_of(Ty::u8()))]);
    assert_eq!(cells_of(&unrecorded), whole, "a variant-less ADT of unrecorded kind");
}

/// A union the extractor stamped (`adt_kind: Some(Union)`).
fn union_of(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
    let mut ty = Ty::adt(name, fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect());
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(AdtKind::Union);
    }
    ty
}

fn manually_drop(inner: Ty) -> Ty {
    stamped("core::mem::ManuallyDrop<T>", vec![("value", inner)])
}

/// `union UUS { c: ManuallyDrop<Cell<usize>>, n: usize }`.
fn uus_ty() -> Ty {
    union_of("c::UUS", vec![("c", manually_drop(cell_usize())), ("n", Ty::usize())])
}

/// A one-statement body `_2 = &<borrowed>` over an owned local 1 of type `owner`.
fn borrow_of(owner: Ty, borrowed: Vec<Projection>, borrowed_ty: Ty) -> VerifiableFunction {
    body(
        vec![Ty::Unit, owner, shared(borrowed_ty)],
        0,
        vec![assign(Place::local(2), Rvalue::Ref { mutable: false, place: place(1, borrowed) })],
        Terminator::Return,
    )
}

/// INTERIOR-MUT-CHANNEL-2 (the review of G2-OPTSTRING-1, finding 1): a shared borrow of a
/// union's CELL field writes the bytes every other field of the union names, so the
/// slot half names the union COVER: `u` for `&u.c`, `w.1` for `&w.u.c` (a struct holding
/// the union; its sibling `w.0` keeps its facts). A borrow of the union's `Freeze` field
/// (`&u.n`) hands out nothing. Before, the slot half named `u.0` alone and `u.n` kept its
/// fact across `poke(&u.c)`.
#[test]
fn a_shared_borrow_of_a_union_cell_field_names_the_union() {
    let f = borrow_of(uus_ty(), vec![Projection::Field(0)], manually_drop(cell_usize()));
    let cover = Place::local(1);
    assert_eq!(shared_borrowed_cell_places(&f, 1).as_ref(), &vec![cover.clone()]);
    let names = stored_ref_pointee_names(&f);
    let cover_name = place_to_var_name(&f, &cover);
    assert!(names.contains(&cover_name), "`{cover_name}` must be havocked: {names:?}");
    assert!(!crate::place_is_body_stable(&f, &place(1, vec![Projection::Field(1)])), "`u.n`");
    assert!(crate::stmt_escapes_local(&f, &f.body.blocks[0].stmts[0], 1));

    let f = borrow_of(uus_ty(), vec![Projection::Field(1)], Ty::usize());
    assert!(shared_borrowed_cell_places(&f, 1).is_empty(), "`&u.n` is a borrow of Freeze bytes");
    assert!(crate::place_source_is_stable(&f, 1));

    let wc = stamped("c::WC", vec![("k", Ty::u8()), ("u", uus_ty())]);
    let f = borrow_of(
        wc,
        vec![Projection::Field(1), Projection::Field(0)],
        manually_drop(cell_usize()),
    );
    let cover = place(1, vec![Projection::Field(1)]);
    assert_eq!(shared_borrowed_cell_places(&f, 1).as_ref(), &vec![cover]);
    let n = place(1, vec![Projection::Field(1), Projection::Field(1)]);
    assert!(!crate::place_is_body_stable(&f, &n), "`w.u.n`");
    assert!(crate::place_is_body_stable(&f, &place(1, vec![Projection::Field(0)])), "`w.k`");

    // A variant-less ADT whose kind was not recorded may be a union: named whole.
    let k = Ty::adt("c::K", vec![("c".into(), cell_usize()), ("n".into(), Ty::usize())]);
    let f = borrow_of(k, vec![Projection::Field(0)], cell_usize());
    assert_eq!(
        shared_borrowed_cell_places(&f, 1).as_ref(),
        &vec![Place::local(1)],
        "kind unrecorded"
    );
}

/// INTERIOR-MUT-CHANNEL-2 (finding 2): below a union the BYTE question decides, also when the
/// borrow STARTS below it. `&u.v` with `u.v: ManuallyDrop<Option<Vec<u8>>>` names the
/// union, because `u.n` names the `Vec`'s allocator bytes; the same field of a STRUCT
/// names nothing (G2-OPTSTRING-1's precision), and so does a struct-held
/// `Option<Vec<u8>>` borrowed whole.
#[test]
fn a_vec_field_borrowed_below_a_union_is_asked_the_byte_question() {
    let mdov = manually_drop(option_of(vec_of(Ty::u8())));
    let n = Ty::Array { elem: Box::new(Ty::u8()), len: 32 };
    let union = union_of("c::UVO", vec![("v", mdov.clone()), ("n", n.clone())]);
    let f = borrow_of(union.clone(), vec![Projection::Field(0)], mdov.clone());
    assert_eq!(shared_borrowed_cell_places(&f, 1).as_ref(), &vec![Place::local(1)]);
    let f = borrow_of(
        union,
        vec![Projection::Field(0), Projection::Field(0)],
        option_of(vec_of(Ty::u8())),
    );
    assert_eq!(shared_borrowed_cell_places(&f, 1).as_ref(), &vec![Place::local(1)], "`&u.v.0`");
    let st = stamped("c::SVO", vec![("v", mdov.clone()), ("n", n)]);
    let f = borrow_of(st, vec![Projection::Field(0)], mdov);
    assert!(shared_borrowed_cell_places(&f, 1).is_empty(), "a struct field over a Vec");
}

/// INTERIOR-MUT-CHANNEL-2: a field of a union behind a shared root's `Deref` is not body-stable
/// when the union may hold a cell byte anywhere (`(*r).n` beside `(*r).c`, or beside a
/// `Vec` field, whose allocator only the byte question sees); a union of `Freeze` fields
/// stays stable.
#[test]
fn a_union_field_behind_a_shared_root_is_not_body_stable_when_the_union_holds_a_cell() {
    let n_of = |root_ty: Ty| {
        let f = body(vec![Ty::Unit, shared(root_ty)], 1, Vec::new(), Terminator::Return);
        crate::place_is_body_stable(&f, &place(1, vec![Projection::Deref, Projection::Field(1)]))
    };
    assert!(!n_of(uus_ty()), "a union with a cell field");
    let uv = union_of(
        "c::UV",
        vec![
            ("v", manually_drop(vec_of(Ty::u8()))),
            ("n", Ty::Array { elem: Box::new(Ty::usize()), len: 3 }),
        ],
    );
    assert!(!n_of(uv), "a union with a Vec field");
    let plain = union_of("c::UP", vec![("a", Ty::u32()), ("n", Ty::u64())]);
    assert!(n_of(plain), "a union of Freeze fields");
    let unrecorded = Ty::adt("c::K", vec![("c".into(), cell_usize()), ("n".into(), Ty::usize())]);
    assert!(!n_of(unrecorded), "a variant-less ADT of unrecorded kind may be a union");
    let s = stamped("c::S2", vec![("c", cell_usize()), ("n", Ty::usize())]);
    assert!(n_of(s), "a stamped struct's frozen sibling stays stable");
}

/// The escape question's cell clause as it was asked before 2026-10-17: run the cell walk
/// for the borrow, then compare its root with the asked local.
fn unfiltered_cell_clause(body: &VerifiableBody, stmt: &Statement, local: usize) -> bool {
    super::shared_borrow_cell_places(body, stmt).is_some_and(|(root, _)| root == local)
}

/// Every (statement, local) answer of the root-first clause next to the walk-first one,
/// as `(answers that fire, answers that do not)`.
fn sweep_cell_clause(f: &VerifiableFunction) -> (usize, usize) {
    let (mut fired, mut quiet) = (0, 0);
    for block in &f.body.blocks {
        for stmt in &block.stmts {
            for local in 0..f.body.locals.len() {
                let filtered = super::shared_borrow_of_local_covers_cell(&f.body, stmt, local);
                assert_eq!(
                    filtered,
                    unfiltered_cell_clause(&f.body, stmt, local),
                    "{}: the root-first clause disagrees at local {local} on {stmt:?}",
                    f.def_path
                );
                if filtered { fired += 1 } else { quiet += 1 }
            }
        }
    }
    (fired, quiet)
}

/// gate-rca deadline (2026-10-17, G2 cost): the escape question asks the borrow's ROOT
/// before it runs the cell walk (`own_storage_shared_borrow`), and answers exactly as
/// the walk-first clause it replaced, over every statement and every local of bodies
/// with an owned cell, a cell field, a frozen local and a borrow through a reference.
/// Negative control: the sweep sees the clause FIRE on the cell borrows and stay quiet
/// on the rest, so agreement is not two constant `false`s.
#[test]
fn the_root_first_cell_clause_answers_as_the_walk_first_one() {
    let plain = stamped("c::P", vec![("n", Ty::usize()), ("m", Ty::usize())]);
    let f = body(
        vec![
            Ty::Unit,
            s_ty(),
            cell_usize(),
            plain.clone(),
            shared(s_ty()),
            shared(s_ty()),
            shared(cell_usize()),
            shared(plain),
            shared(cell_usize()),
        ],
        0,
        vec![
            assign(Place::local(5), Rvalue::Ref { mutable: false, place: Place::local(1) }),
            assign(Place::local(6), Rvalue::Ref { mutable: false, place: Place::local(2) }),
            assign(Place::local(7), Rvalue::Ref { mutable: false, place: Place::local(3) }),
            assign(
                Place::local(8),
                Rvalue::Ref { mutable: false, place: place(1, vec![Projection::Field(1)]) },
            ),
            assign(
                Place::local(8),
                Rvalue::Ref {
                    mutable: false,
                    place: place(4, vec![Projection::Deref, Projection::Field(1)]),
                },
            ),
            assign(Place::local(5), Rvalue::Ref { mutable: true, place: Place::local(1) }),
        ],
        Terminator::Return,
    );
    let (fired, quiet) = sweep_cell_clause(&f);
    assert_eq!(fired, 3, "`&st`, `&c` and `&st.1` borrow a cell of their own root's storage");
    assert!(quiet > fired, "every other (statement, local) pair is quiet");
}

/// The same agreement on the real stage-1 dumps that carry `Cell`s
/// (`tests/fixtures/*cell*_mir.json`), so the extractor's own type and projection
/// shapes are covered, not only the synthetic ones above.
#[test]
fn the_root_first_cell_clause_agrees_on_real_mir_with_cells() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut names: Vec<_> = std::fs::read_dir(&dir)
        .expect("fixture dir")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| {
            path.file_name().and_then(|n| n.to_str()).is_some_and(|n| {
                n.ends_with("_mir.json") && (n.contains("cell") || n.contains("interior_mut"))
            })
        })
        .collect();
    names.sort();
    assert!(names.len() >= 5, "the sweep must see the cell dumps: {names:?}");
    let (mut fired, mut bodies) = (0, 0);
    for path in names {
        let Ok(f) = serde_json::from_str::<VerifiableFunction>(
            &std::fs::read_to_string(&path).expect("fixture readable"),
        ) else {
            continue;
        };
        bodies += 1;
        fired += sweep_cell_clause(&f).0;
    }
    assert!(bodies >= 5, "the dumps decode as bodies: {bodies}");
    assert!(fired > 0, "some real dump borrows a cell of its own storage");
}

/// `[e0, e1]` in `_1`, then `_4 = 0; _5 = &_1[_4]` (a shared borrow of one element).
fn element_borrowed(elem: Ty) -> VerifiableFunction {
    let array = Ty::Array { elem: Box::new(elem.clone()), len: 2 };
    let move_of = |local| trust_types::Operand::Move(Place::local(local));
    body(
        vec![Ty::Unit, array, elem.clone(), elem.clone(), Ty::usize(), shared(elem)],
        0,
        vec![
            assign(
                Place::local(1),
                Rvalue::Aggregate(trust_types::AggregateKind::Array, vec![move_of(2), move_of(3)]),
            ),
            assign(
                Place::local(4),
                Rvalue::Use(trust_types::Operand::Constant(trust_types::ConstValue::Uint(0, 64))),
            ),
            assign(
                Place::local(5),
                Rvalue::Ref { mutable: false, place: place(1, vec![Projection::Index(4)]) },
            ),
        ],
        Terminator::Return,
    )
}

/// VGAPS-G2-FOLLOWUP (4), the design's §3.3 audit: `array_local_index_naming_stable`
/// gives a constant-index read the literal's `[c;min=len]` name, and an element type is
/// unrestricted there, so a shared borrow of an element that holds a cell (`poke(&a[0])`
/// for `a: [Cell<usize>; 2]`) ends the stable naming, as `place_source_is_stable`'s cell
/// clause does for a local's own value. The `Freeze` twin keeps it.
#[test]
fn a_shared_borrow_of_an_array_of_cells_ends_its_stable_index_naming() {
    let cells = element_borrowed(cell_usize());
    assert!(!shared_borrowed_cell_places(&cells, 1).is_empty(), "`&a[0]` hands out a cell");
    assert!(!crate::array_local_index_naming_stable(&cells, 1), "`a[0]` may change by `set`");
    let plain = element_borrowed(Ty::usize());
    assert!(shared_borrowed_cell_places(&plain, 1).is_empty(), "control: no cell to hand out");
    assert!(crate::array_local_index_naming_stable(&plain, 1), "control: `&a[0]` writes nothing");
}

/// VGAPS-G2-FOLLOWUP (4): the scans of the slot-rule family that do NOT ask the cell
/// clause cannot see a cell byte, and this pins why.
/// * `index_local_const` and `index_local_stable` (through which `array_local_escapes` is
///   asked about an index) read an INDEX local, a `usize` by MIR's rules;
/// * `array_theory_local` admits SCALAR elements only (`Bool`, `Int`, `Float`, `Bv`), so
///   `array_local_escapes` is never asked about an array that may hold a cell;
/// * `f4_whole_local_defs` reads the root of a two-way `bool` switch.
///
/// The walk finds no cell in a `usize` or a `bool`, a shared borrow of an index writes
/// nothing (its constant stands), and the array-theory channel refuses an array of cells
/// before it asks `array_local_escapes`.
#[test]
fn the_scans_without_the_cell_clause_cannot_see_a_cell() {
    assert!(cells_of(&Ty::usize()).is_empty(), "a `usize` holds no cell byte");
    assert!(cells_of(&Ty::Bool).is_empty(), "a `bool` holds no cell byte");

    let index = body(
        vec![Ty::Unit, Ty::usize(), shared(Ty::usize())],
        0,
        vec![
            assign(
                Place::local(1),
                Rvalue::Use(trust_types::Operand::Constant(trust_types::ConstValue::Uint(1, 64))),
            ),
            assign(Place::local(2), Rvalue::Ref { mutable: false, place: Place::local(1) }),
        ],
        Terminator::Return,
    );
    assert!(shared_borrowed_cell_places(&index, 1).is_empty(), "`&i` hands out no cell");
    assert_eq!(crate::index_local_const(&index, 1), Some(1), "the constant stands");

    // `fn f(i: usize)`: `_2 = [e0, e1]; _2[i] = e0` (a variable-index store).
    let stored = |elem: Ty| {
        let array = Ty::Array { elem: Box::new(elem.clone()), len: 2 };
        let move_of = |local| trust_types::Operand::Move(Place::local(local));
        body(
            vec![Ty::Unit, Ty::usize(), array, elem.clone(), elem],
            1,
            vec![
                assign(
                    Place::local(2),
                    Rvalue::Aggregate(
                        trust_types::AggregateKind::Array,
                        vec![move_of(3), move_of(4)],
                    ),
                ),
                assign(place(2, vec![Projection::Index(1)]), Rvalue::Use(move_of(3))),
            ],
            Terminator::Return,
        )
    };
    assert!(crate::array_theory_local(&stored(Ty::usize()), 2).is_some(), "control: scalars");
    assert!(
        crate::array_theory_local(&stored(cell_usize()), 2).is_none(),
        "an array of cells never reaches `array_local_escapes` through the channel"
    );
}
