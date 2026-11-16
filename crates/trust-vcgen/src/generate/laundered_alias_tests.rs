//! LAUNDERED-ALIAS-STORE / LAUNDERED-ALIAS-ELIDE-1 (2026-10-11): a write into storage
//! whose address was taken must version a read through a raw copy of that address the
//! referent fold cannot resolve.
//!
//! `let mut len = m; let p = &raw mut len; let q = <a copy of p>; let x = *q; *p = n;
//! if *q > 7 { return 0 } x + 1` spelled the store by `p`'s referent (`len`) and both
//! reads of `*q` by the opaque `q*`, one version for both: the guard bounded `x`, the
//! `x + 1` row was kernel-certified, and the advisory lane elided its overflow check.
//! Each row below pins one predicate of the fix on a synthetic body; the real-MIR rows
//! are in `tests/ploss_adv_false_proofs_realmir.rs` (`laundered_alias_*`).

use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn deref(local: usize) -> Place {
    Place { local, projections: vec![Projection::Deref] }
}

fn copy(local: usize) -> Operand {
    Operand::Copy(Place::local(local))
}

fn raw_ptr(mutable: bool, pointee: Ty) -> Ty {
    Ty::RawPtr { mutable, pointee: Box::new(pointee) }
}

/// A one-block function over `locals` (indexed in order); `_1` and `_2` are the
/// parameters `m` and `n`.
fn func(locals: Vec<Ty>, stmts: Vec<Statement>) -> VerifiableFunction {
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
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 2,
            return_ty: Ty::usize(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The locals of every body below: `_0` ret, `_1 m`, `_2 n`, `_3 len`, `_4 p: *mut
/// usize`, `_5 q: *const usize`, `_6` (`six`: the laundering's `*const u8`, or a plain
/// `usize` where no laundering happens), `_7 x`, `_8` the re-read. Every local is
/// assigned (a declared, never-written pointer has no referent and would itself count
/// as an unresolved copy).
fn locals(six: Ty) -> Vec<Ty> {
    vec![
        Ty::usize(),
        Ty::usize(),
        Ty::usize(),
        Ty::usize(),
        raw_ptr(true, Ty::usize()),
        raw_ptr(false, Ty::usize()),
        six,
        Ty::usize(),
        Ty::usize(),
    ]
}

/// How `q` is made: its two statements and the type of `_6`.
struct QDef {
    stmts: Vec<Statement>,
    six: Ty,
}

/// `len = m; p = &raw mut len; <q_def>; x = *q; <write>; re = *q` — the write at
/// statement 5.
fn body(q_def: QDef, write: Statement) -> VerifiableFunction {
    let mut stmts = vec![
        assign(Place::local(3), Rvalue::Use(copy(1))),
        assign(Place::local(4), Rvalue::AddressOf(true, Place::local(3))),
    ];
    stmts.extend(q_def.stmts);
    assert_eq!(stmts.len(), 4, "the q definition is two statements");
    stmts.push(assign(Place::local(7), Rvalue::Use(Operand::Copy(deref(5)))));
    stmts.push(write);
    stmts.push(assign(Place::local(8), Rvalue::Use(Operand::Copy(deref(5)))));
    func(locals(q_def.six), stmts)
}

/// `q = p as *const usize`: the cast keeps the pointee. (`_6 = m` is filler.)
fn cast_q() -> QDef {
    QDef {
        stmts: vec![
            assign(Place::local(6), Rvalue::Use(copy(1))),
            assign(Place::local(5), Rvalue::Cast(copy(4), raw_ptr(false, Ty::usize()))),
        ],
        six: Ty::usize(),
    }
}

/// `q = p as *const u8 as *const usize`: the first cast changes the pointee, so the
/// fold declines and `*q` stays the opaque `q*` — a laundering with no call.
fn laundered_q() -> QDef {
    QDef {
        stmts: vec![
            assign(Place::local(6), Rvalue::Cast(copy(4), raw_ptr(false, Ty::u8()))),
            assign(Place::local(5), Rvalue::Cast(copy(6), raw_ptr(false, Ty::usize()))),
        ],
        six: raw_ptr(false, Ty::u8()),
    }
}

fn store_through_p() -> Statement {
    assign(deref(4), Rvalue::Use(copy(2)))
}

fn direct_write() -> Statement {
    assign(Place::local(3), Rvalue::Use(copy(2)))
}

/// The precision half (`resolve_referent_guarded`'s `Cast` arm): `q = p as *const
/// usize` folds to `p`'s referent, so a read through `q` is spelled `len`, the very
/// name the store through `p` writes. Before the fix `q` resolved to nothing.
#[test]
fn a_raw_pointer_cast_with_the_same_pointee_folds_like_a_copy() {
    let f = body(cast_q(), store_through_p());
    assert_eq!(crate::resolve_referent(&f, 5, 16), Some(Place::local(3)));
    assert!(!crate::deref_pointer_is_opaque(&f, 5), "`*q` must not be the opaque `q*`");
    assert_eq!(
        crate::place_to_var_name(&f, &deref(5)),
        crate::place_to_var_name(&f, &Place::local(3)),
        "a read through `q` is spelled by `len`'s own name"
    );
}

/// The arm's refusals: a pointee-changing cast (`p as *const u8`), an int-to-pointer
/// cast, and a pointer-to-int cast never fold.
#[test]
fn a_pointee_changing_or_integer_cast_does_not_fold() {
    let f = body(laundered_q(), store_through_p());
    assert_eq!(crate::resolve_referent(&f, 6, 16), None, "`p as *const u8` changes the pointee");
    assert_eq!(
        crate::resolve_referent(&f, 5, 16),
        None,
        "`_6 as *const usize`: `_6` is unresolved"
    );
    assert!(crate::deref_pointer_is_opaque(&f, 5));

    // `_7 = p as usize; _5 = _7 as *const usize`: an address forged from an integer.
    let int_round_trip = func(
        locals(Ty::usize()),
        vec![
            assign(Place::local(3), Rvalue::Use(copy(1))),
            assign(Place::local(4), Rvalue::AddressOf(true, Place::local(3))),
            assign(Place::local(7), Rvalue::Cast(copy(4), Ty::usize())),
            assign(Place::local(5), Rvalue::Cast(copy(7), raw_ptr(false, Ty::usize()))),
        ],
    );
    assert_eq!(crate::resolve_referent(&int_round_trip, 5, 16), None);
    assert_eq!(crate::resolve_referent(&int_round_trip, 7, 16), None);
}

/// The soundness half (`path_defs::write_havocs_function_list`): with `*q` the opaque
/// `q*`, the store through `p` (which FOLDS to `len`, so it is no opaque store) and a
/// direct `len = n` both havoc the whole-function list, which carries `q`'s base name
/// and so rebinds `q*`. Before the fix neither write touched `q*`, and the two reads of
/// `*q` shared one version.
#[test]
fn a_write_into_escaped_storage_versions_an_unresolved_raw_copy() {
    for (write, what) in [(store_through_p(), "*p = n"), (direct_write(), "len = n")] {
        let f = body(laundered_q(), write);
        let written = match &f.body.blocks[0].stmts[5] {
            Statement::Assign { place, .. } => place.clone(),
            other => panic!("statement 5 is the write, got {other:?}"),
        };
        assert!(
            !crate::deref_store_is_opaque(&f, &deref(4)),
            "`*p` folds to `len`: the store is not an opaque store"
        );
        assert!(super::write_havocs_function_list(&f, &written), "{what}: must havoc the list");
        let q_star = crate::place_to_var_name(&f, &deref(5));
        assert!(q_star.contains('*'), "`*q` must be the opaque `q*`, got `{q_star}`");
        let block = &f.body.blocks[0];
        assert!(
            super::stmt_writes_name(&f, block, 5, &q_star),
            "{what}: the write must version `{q_star}`"
        );
        assert!(
            !super::stmt_writes_name(&f, block, 4, &q_star),
            "the read `x = *q` writes nothing"
        );
        // The indexed oracle asks the same predicate.
        let writes = crate::generate::block_writes::FnWrites::build(&f);
        assert!(writes.block(0).is_some_and(|b| b.any_opaque_store()), "{what}: indexed oracle");
    }
}

/// The controls. With `q = p as *const usize` folded there is no unresolved copy, and
/// the same writes havoc nothing beyond their own name. With no raw copy at all, a
/// `&mut` PARAMETER whose deref is opaque (retagged: a read through it after a foreign
/// write is UB) does not count either.
#[test]
fn a_write_with_no_unresolved_raw_copy_havocs_nothing_new() {
    for write in [store_through_p(), direct_write()] {
        let f = body(cast_q(), write);
        let written = match &f.body.blocks[0].stmts[5] {
            Statement::Assign { place, .. } => place.clone(),
            other => panic!("statement 5 is the write, got {other:?}"),
        };
        assert!(super::laundered_alias_roots(&f).is_empty());
        assert!(!super::write_havocs_function_list(&f, &written));
    }

    // `fn f(r: &mut usize, n: usize) { let mut len = *r; let p = &raw mut len; *p = n; }`
    let mut l = locals(Ty::usize());
    l[1] = Ty::Ref { mutable: true, inner: Box::new(Ty::usize()) };
    l.truncate(5);
    let f = func(
        l,
        vec![
            assign(Place::local(3), Rvalue::Use(Operand::Copy(deref(1)))),
            assign(Place::local(4), Rvalue::AddressOf(true, Place::local(3))),
            store_through_p(),
        ],
    );
    assert!(crate::deref_pointer_is_opaque(&f, 1), "the parameter's deref is opaque");
    assert!(super::laundered_alias_roots(&f).is_empty(), "but `&mut` is retagged");
    assert!(!super::write_havocs_function_list(&f, &deref(4)));
}

/// `ty_may_reach_unretagged_pointer`: a raw pointer anywhere, a `&mut` stored behind a
/// reference, and a part whose layout is unrecorded count; a `&mut` or `&` held
/// directly does not.
#[test]
fn which_types_may_reach_an_unretagged_pointer() {
    let defs = Default::default();
    let may =
        |ty: &Ty| super::ty_may_reach_unretagged_pointer(&defs, ty, false, &mut Vec::new(), 64);
    let mut_ref = |t: Ty| Ty::Ref { mutable: true, inner: Box::new(t) };
    let shared_ref = |t: Ty| Ty::Ref { mutable: false, inner: Box::new(t) };
    assert!(may(&raw_ptr(false, Ty::usize())));
    assert!(may(&Ty::Tuple(vec![Ty::usize(), raw_ptr(true, Ty::u8())])));
    assert!(may(&shared_ref(raw_ptr(true, Ty::usize()))), "a raw pointer stored behind `&`");
    assert!(may(&shared_ref(mut_ref(Ty::usize()))), "a `&mut` stored behind `&`");
    assert!(may(&Ty::adt("c::Opaque", Vec::new())), "an ADT with no recorded layout");
    assert!(
        may(&Ty::Datatype { name: "c::Undefined".into(), variants: Vec::new() }),
        "a by-name marker the table does not define"
    );
    assert!(!may(&mut_ref(Ty::usize())), "a `&mut` held directly is retagged");
    assert!(!may(&shared_ref(Ty::usize())));
    assert!(!may(&Ty::usize()));
    assert!(!may(&Ty::adt("core::marker::PhantomData<*mut u8>", Vec::new())));
}

/// `core::cell::Cell<usize>` as the extractor renders it: a `value: UnsafeCell<usize>`.
fn cell_usize() -> Ty {
    Ty::adt(
        "core::cell::Cell<usize>",
        vec![(
            "value".into(),
            Ty::adt("core::cell::UnsafeCell<usize>", vec![("value".into(), Ty::usize())]),
        )],
    )
}

/// `c = <m>; r = &c; w = &raw const (*r).0; q = w as *const usize; x = *q; c = <n>;
/// re = *q` — `Cell::as_ptr` inlined, over a `_3` of type `c3`. `_4: &c3`, `_6: *const
/// UnsafeCell<usize>`; the direct write `c = <n>` is statement 5.
fn as_ptr_body(c3: Ty) -> VerifiableFunction {
    let unsafe_cell = Ty::adt("core::cell::UnsafeCell<usize>", vec![("value".into(), Ty::usize())]);
    let mut l = locals(raw_ptr(false, unsafe_cell));
    l[3] = c3.clone();
    l[4] = Ty::Ref { mutable: false, inner: Box::new(c3) };
    l.push(Ty::usize());
    let field0 = Place { local: 4, projections: vec![Projection::Deref, Projection::Field(0)] };
    func(
        l,
        vec![
            assign(Place::local(3), Rvalue::Use(copy(1))),
            assign(Place::local(4), Rvalue::Ref { mutable: false, place: Place::local(3) }),
            assign(Place::local(6), Rvalue::AddressOf(false, field0)),
            assign(Place::local(5), Rvalue::Cast(copy(6), raw_ptr(false, Ty::usize()))),
            assign(Place::local(7), Rvalue::Use(Operand::Copy(deref(5)))),
            assign(Place::local(3), Rvalue::Use(copy(2))),
            assign(Place::local(8), Rvalue::Use(Operand::Copy(deref(5)))),
        ],
    )
}

/// LAUNDERED-ALIAS-CELL-1 (wave-24 review, 2026-10-12): a SHARED borrow of
/// interior-mutable storage is a write channel too. `Cell::as_ptr(&c)` hands back a raw
/// pointer to `c`'s bytes through `&c`, a `Ref { mutable: false }` that
/// `borrow_write_target` does not count, so `c` was no root, the direct write `c = <n>`
/// havocked nothing, and both reads of `*q` shared one version (the `cell_direct`
/// witness: the `x + 1` row kernel-certified, the advisory check elided). Now `c` is a
/// root and the write versions `q*`.
#[test]
fn a_direct_write_into_a_shared_borrowed_cell_versions_an_unresolved_raw_copy() {
    let f = as_ptr_body(cell_usize());
    let c = crate::place_to_var_name(&f, &Place::local(3));
    assert!(
        super::laundered_alias_roots(&f).contains(&c),
        "`&c` of a `Cell` roots `c`: {:?}",
        super::laundered_alias_roots(&f)
    );
    assert!(super::write_havocs_function_list(&f, &Place::local(3)), "`c = <n>` havocs the list");
    let q_star = crate::place_to_var_name(&f, &deref(5));
    assert!(q_star.contains('*'), "`*q` must be the opaque `q*`, got `{q_star}`");
    let block = &f.body.blocks[0];
    assert!(super::stmt_writes_name(&f, block, 5, &q_star), "the write must version `{q_star}`");
    let writes = crate::generate::block_writes::FnWrites::build(&f);
    assert!(writes.block(0).is_some_and(|b| b.any_opaque_store()), "indexed oracle");
}

/// The `Freeze` control and the type rule. A shared borrow of `Freeze` data is no root
/// (a write to it while a pointer derived from the borrow is read is UB under Stacked
/// and Tree Borrows), so the same body over a `usize` havocs nothing. The type walk is
/// fail-closed: an interior-mutable name, an ADT with no recorded layout and an
/// undefined marker count; a reference, a raw pointer and a std zero-sized marker do not.
#[test]
fn a_shared_borrow_of_freeze_data_is_no_root() {
    let f = as_ptr_body(Ty::usize());
    let c = crate::place_to_var_name(&f, &Place::local(3));
    assert!(
        !super::laundered_alias_roots(&f).contains(&c),
        "{:?}",
        super::laundered_alias_roots(&f)
    );
    assert!(!super::write_havocs_function_list(&f, &Place::local(3)));

    let defs = Default::default();
    let may = |ty: &Ty| super::ty_may_hold_inline_unsafe_cell(&defs, ty, &mut Vec::new(), 64);
    assert!(may(&cell_usize()));
    assert!(may(&Ty::adt("core::sync::atomic::AtomicUsize", Vec::new())), "by name");
    assert!(may(&Ty::Tuple(vec![Ty::usize(), cell_usize()])));
    assert!(may(&Ty::adt("c::Opaque", Vec::new())), "an ADT with no recorded layout");
    assert!(may(&Ty::Datatype { name: "c::Undefined".into(), variants: Vec::new() }));
    assert!(!may(&Ty::usize()));
    assert!(!may(&Ty::Ref { mutable: false, inner: Box::new(cell_usize()) }), "behind `&`");
    assert!(!may(&raw_ptr(true, cell_usize())), "behind a raw pointer");
    assert!(!may(&Ty::adt("c::Plain", vec![("a".into(), Ty::usize())])));
    assert!(!may(&Ty::adt("core::marker::PhantomData<core::cell::Cell<u8>>", Vec::new())));
}
