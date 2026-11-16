//! INT-RAWCONST-HAVOC-1 (2026-10-06): a `&raw const` borrow is a write channel.
//!
//! `let mut x = 5; let p = &raw const x;` followed by a write through `p` — a safe
//! `AtomicU8::from_ptr(p as *mut u8).store(k, ..)`, `*(p as *mut u8) = k`, or an
//! edition-2024 `safe fn memset(p as *mut u8, ..)` — is defined under Tree Borrows
//! (DECISION_QUEUE UF-1(c)). vcgen's general havoc list and its siblings counted
//! `&mut` and `&raw mut` only, so the fact `x == 5` survived the write: the overflow
//! row of `x + 1` was kernel-certified and its check elided, and the bounds row of
//! `a[i]` was reported proved for a runtime index of 1_000_000.
//!
//! Each row below pins one predicate on a synthetic body. On the base tree
//! (308c6c5f9e) every `&raw const` assertion fails and every control passes; the
//! `&raw mut` twin of each row already held. The real-MIR rows are in
//! `tests/raw_const_escape_havoc_realmir.rs`.

use trust_types::{
    AggregateKind, BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
};

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn deref(local: usize) -> Place {
    Place { local, projections: vec![Projection::Deref] }
}

/// A one-block function over `locals` (indexed in order) whose first `arg_count`
/// locals after `_0` are parameters.
fn func(locals: Vec<Ty>, arg_count: usize, stmts: Vec<Statement>) -> VerifiableFunction {
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
            arg_count,
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

fn raw_ptr(mutable: bool, pointee: Ty) -> Ty {
    Ty::RawPtr { mutable, pointee: Box::new(pointee) }
}

/// `fn f(k: u8) -> u8 { let mut x: u8 = 5; let p = &raw [const|mut] x; .. }` —
/// `_1 = k`, `_2 = x`, `_3 = p`.
fn raw_borrow_of_x(mutable: bool) -> VerifiableFunction {
    func(
        vec![Ty::u8(), Ty::u8(), Ty::u8(), raw_ptr(mutable, Ty::u8())],
        1,
        vec![
            assign(Place::local(2), Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 8)))),
            assign(Place::local(3), Rvalue::AddressOf(mutable, Place::local(2))),
        ],
    )
}

/// The root: the havoc list a `Call`, `Drop`, `Opaque` terminator and an opaque
/// deref-store kill. Before the fix `x` was in it for `&raw mut x` only.
#[test]
fn a_raw_const_borrow_puts_the_local_in_the_havoc_list() {
    for mutable in [true, false] {
        let f = raw_borrow_of_x(mutable);
        let x = crate::place_to_var_name(&f, &Place::local(2));
        assert!(
            super::mutably_borrowed_local_names(&f).contains(&x),
            "`&raw {}` x must put `{x}` in the mutably-borrowed list",
            if mutable { "mut" } else { "const" },
        );
        assert!(
            super::function_havoc_names(&f).contains(&x),
            "`&raw {}` x must put `{x}` in the call/opaque havoc list",
            if mutable { "mut" } else { "const" },
        );
    }
}

/// The control: a shared `&x` cannot write `x` (a write through it is UB on a
/// `Freeze` place), so it does not enter the list.
#[test]
fn a_shared_borrow_stays_out_of_the_havoc_list() {
    let f = func(
        vec![Ty::u8(), Ty::u8(), Ty::u8(), Ty::Ref { mutable: false, inner: Box::new(Ty::u8()) }],
        1,
        vec![
            assign(Place::local(2), Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 8)))),
            assign(Place::local(3), Rvalue::Ref { mutable: false, place: Place::local(2) }),
        ],
    );
    let x = crate::place_to_var_name(&f, &Place::local(2));
    assert!(!super::mutably_borrowed_local_names(&f).contains(&x));
}

/// `fn f(s: &mut [u8]) { s.len(); .. }` — rustc reads a non-`Copy` slice place's
/// length through `_3 = &raw const (*_1); _4 = PtrMetadata(move _3)`
/// (`RawPtrKind::FakeForPtrMetadata`, which the extractor spells `AddressOf(false)`).
/// That pointer is read once by `PtrMetadata` and goes nowhere else, so it cannot
/// write; counting it would havoc the slice behind every `.len()` and bounds check
/// at every call. A second use of the same pointer makes it a real escape.
#[test]
fn the_fake_metadata_borrow_is_not_a_write_channel_but_a_second_use_is() {
    let slice_ref =
        Ty::Ref { mutable: true, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
    let slice_ptr = raw_ptr(false, Ty::Slice { elem: Box::new(Ty::u8()) });
    let body = |escapes: bool| {
        let mut stmts = vec![
            assign(Place::local(3), Rvalue::AddressOf(false, deref(1))),
            assign(
                Place::local(4),
                Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(3))),
            ),
        ];
        if escapes {
            stmts.push(assign(Place::local(5), Rvalue::Use(Operand::Copy(Place::local(3)))));
        }
        func(
            vec![
                Ty::u8(),
                slice_ref.clone(),
                Ty::u8(),
                slice_ptr.clone(),
                Ty::usize(),
                slice_ptr.clone(),
            ],
            1,
            stmts,
        )
    };
    let fake = body(false);
    let pointee = crate::place_to_var_name(&fake, &deref(1));
    assert!(
        !super::mutably_borrowed_local_names(&fake).contains(&pointee),
        "the fake-metadata borrow must not enter the list"
    );
    let real = body(true);
    assert!(
        super::mutably_borrowed_local_names(&real).contains(&pointee),
        "a `&raw const` whose pointer is also copied elsewhere is a real escape"
    );
}

/// `s.as_ptr()` for `s: &[u8]` is `_3 = &raw const (*_1)` (here followed by a cast, so
/// it is not the fake-metadata borrow). The pointer has the permissions of the shared
/// reborrow `&(*_1)`: it cannot change `s`, and a write through it is undefined
/// behaviour. It stays out of the list; the same borrow through a `&mut [u8]` is in it.
#[test]
fn a_raw_const_through_a_shared_reference_stays_out_of_the_havoc_list() {
    let body = |mutable: bool| {
        func(
            vec![
                Ty::u8(),
                Ty::Ref { mutable, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) },
                Ty::u8(),
                raw_ptr(false, Ty::Slice { elem: Box::new(Ty::u8()) }),
                raw_ptr(false, Ty::u8()),
            ],
            1,
            vec![
                assign(Place::local(3), Rvalue::AddressOf(false, deref(1))),
                assign(
                    Place::local(4),
                    Rvalue::Cast(Operand::Copy(Place::local(3)), raw_ptr(false, Ty::u8())),
                ),
            ],
        )
    };
    let shared = body(false);
    let pointee = crate::place_to_var_name(&shared, &deref(1));
    assert!(!super::mutably_borrowed_local_names(&shared).contains(&pointee), "`&[u8]`");
    let exclusive = body(true);
    let pointee = crate::place_to_var_name(&exclusive, &deref(1));
    assert!(super::mutably_borrowed_local_names(&exclusive).contains(&pointee), "`&mut [u8]`");
}

/// `let mut i = 1; let p = &raw const i; AtomicUsize::from_ptr(p as *mut usize)
/// .store(k, ..); a[i]` — `index_local_const` read `i` as the constant 1 and rendered
/// `a[i]` as the literal's element, so the bounds row was proved while the runtime
/// index is `k`.
#[test]
fn index_local_const_refuses_a_raw_const_borrowed_index() {
    let index = |borrow: Option<bool>| {
        let mut stmts =
            vec![assign(Place::local(5), Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64))))];
        if let Some(mutable) = borrow {
            stmts.push(assign(Place::local(6), Rvalue::AddressOf(mutable, Place::local(5))));
        }
        func(
            vec![
                Ty::u8(),
                Ty::usize(),
                Ty::u8(),
                Ty::u8(),
                Ty::u8(),
                Ty::usize(),
                raw_ptr(false, Ty::usize()),
            ],
            1,
            stmts,
        )
    };
    assert_eq!(crate::index_local_const(&index(None), 5), Some(1), "control: no borrow");
    assert_eq!(crate::index_local_const(&index(Some(true)), 5), None, "`&raw mut i`");
    assert_eq!(crate::index_local_const(&index(Some(false)), 5), None, "`&raw const i`");
}

/// The two array-lane escape tests: element naming stability and the McCarthy
/// channel's alias gate.
#[test]
fn the_array_lanes_count_a_raw_const_borrow_of_the_array() {
    let array = |borrow: Option<bool>| {
        let mut stmts = vec![assign(
            Place::local(1),
            Rvalue::Aggregate(
                AggregateKind::Array,
                vec![
                    Operand::Constant(ConstValue::Uint(0, 32)),
                    Operand::Constant(ConstValue::Uint(0, 32)),
                ],
            ),
        )];
        if let Some(mutable) = borrow {
            stmts.push(assign(Place::local(6), Rvalue::AddressOf(mutable, Place::local(1))));
        }
        func(
            vec![
                Ty::u32(),
                Ty::Array { elem: Box::new(Ty::u32()), len: 2 },
                Ty::u8(),
                Ty::u8(),
                Ty::u8(),
                Ty::usize(),
                raw_ptr(false, Ty::Array { elem: Box::new(Ty::u32()), len: 2 }),
            ],
            0,
            stmts,
        )
    };
    assert!(crate::array_local_index_naming_stable(&array(None), 1), "control: no borrow");
    assert!(!crate::array_local_escapes(&array(None), 1), "control: no borrow");
    for mutable in [true, false] {
        let f = array(Some(mutable));
        assert!(!crate::array_local_index_naming_stable(&f, 1), "`&raw` (mutable={mutable})");
        assert!(crate::array_local_escapes(&f, 1), "`&raw` (mutable={mutable})");
    }
}

/// The float lanes and the witness lane: each decides a local's value from its
/// visible definitions and must refuse once a write-capable borrow of it exists.
#[test]
fn the_float_and_witness_def_scans_count_a_raw_const_borrow() {
    // `_1: f64` parameter, `_2: f64` local `= _1`, `_3` the borrow.
    let body = |borrowed: Option<Place>| {
        let mut stmts = vec![assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1))))];
        if let Some(place) = borrowed {
            stmts.push(assign(Place::local(3), Rvalue::AddressOf(false, place)));
        }
        func(
            vec![
                Ty::Float { width: 64 },
                Ty::Float { width: 64 },
                Ty::Float { width: 64 },
                raw_ptr(false, Ty::Float { width: 64 }),
            ],
            1,
            stmts,
        )
    };
    let clean = body(None);
    assert!(super::param_place_is_entry_stable(&clean, 1), "control");
    assert!(super::float_whole_local_defs(&clean, 2).is_some(), "control");
    assert!(super::f4_whole_local_defs(&clean, 2).is_some(), "control");

    let param_borrowed = body(Some(Place::local(1)));
    assert!(
        !super::param_place_is_entry_stable(&param_borrowed, 1),
        "`&raw const` of the parameter: its entry value is no longer pinned"
    );
    let local_borrowed = body(Some(Place::local(2)));
    assert!(
        super::float_whole_local_defs(&local_borrowed, 2).is_none(),
        "`&raw const` of the local: its visible defs are not all its values"
    );
    assert!(
        super::f4_whole_local_defs(&local_borrowed, 2).is_none(),
        "`&raw const` of the local: its visible defs are not all its values"
    );
}
