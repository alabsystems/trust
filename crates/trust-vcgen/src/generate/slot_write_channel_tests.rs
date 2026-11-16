//! THE OWN-STORAGE (SLOT-WRITE) CHANNEL RULE (`path_defs::own_storage_write_borrow`),
//! arm by arm, and one pin per consumer. The r8c soundness-union lane stated it on
//! 2026-09-30 as `slot_write_channel`; main's H2 fix (96db9eb9f0, 2026-10-08) stated
//! the same rule as `own_storage_write_borrow`, and the merge kept main's one.
//!
//! The SLOT-ALIASING LIST (`mutably_borrowed_local_names`) names every local whose
//! own slot a pointer can write: `&mut p`, `&raw mut p`, and `&raw const p` of an
//! OWNED place `p` (no `Deref` in `p`). Each entry gets its `__slice_len` twin in
//! the whole-function havoc list (`function_havoc_names`), which the call, drop,
//! opaque-terminator and opaque-store havoc all read. The opaque-store kill judges
//! havoc BASE names with the plain relation (`KillSet::havoc`), so this list is
//! the ONLY thing that kills a slice local's length when its slot is reseated. The
//! stability scans of a local's own storage (`place_source_is_stable`,
//! `index_local_const`, `array_local_index_naming_stable`, `array_local_escapes`)
//! ask the same rule.
//!
//! `&raw const` belongs on it: `*(&raw const s as *mut _) = t` is accepted by Tree
//! Borrows (Stacked Borrows rejects it), and Trust assumes only what both models
//! validate; the write is defined for a `let mut s` (for an immutable binding the
//! Reference makes it UB, and the rule, which cannot see binding mutability,
//! counts it anyway). `&raw const (*s)` — rustc's `PtrMetadata` idiom for
//! `s.len()` — is a pointer to the POINTEE, not the slot, and stays off; a write
//! through a shared reference (`&s`) is UB under both models and stays off.
//!
//! The real-MIR counter-programs are in `tests/opaque_deref_store_reseat.rs` (its
//! `&raw const` section); these pin the rule itself and each scan that asks it.

use trust_types::{
    AggregateKind, BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{function_havoc_names, mutably_borrowed_local_names, own_storage_write_borrow};
use crate::place_to_var_name;

fn u8_slice_ref(mutable: bool) -> Ty {
    Ty::Ref { mutable, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) }
}

/// `_1: &[u8]` (named `s`), `_2: (&[u8], u8)` (named `w`), `_3` the pointer the
/// single statement `_3 = <rvalue>` writes, and nothing else.
fn body_with(rvalue: Rvalue) -> VerifiableFunction {
    let pointer_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Unit) };
    VerifiableFunction {
        name: "slot_channel".into(),
        def_path: "test::slot_channel".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: u8_slice_ref(false), name: Some("s".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Tuple(vec![u8_slice_ref(false), Ty::u8()]),
                    name: Some("w".into()),
                },
                LocalDecl { index: 3, ty: pointer_ty, name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue,
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
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

fn slot(func: &VerifiableFunction, place: &Place) -> String {
    place_to_var_name(func, place)
}

/// `place` is on the slot-aliasing list AND its length twin is in the havoc list.
fn assert_listed(func: &VerifiableFunction, place: &Place, what: &str) {
    let name = slot(func, place);
    let listed = mutably_borrowed_local_names(func);
    assert!(
        listed.contains(&name),
        "{what}: `{name}` must be a slot-write channel; list = {listed:?}"
    );
    let havoc = function_havoc_names(func);
    let twin = format!("{name}__slice_len");
    assert!(
        havoc.contains(&twin),
        "{what}: the havoc list must carry `{twin}`, the length a slot reseat changes; \
         havoc = {havoc:?}"
    );
}

#[test]
fn raw_const_of_an_owned_local_is_a_slot_write_channel() {
    let func = body_with(Rvalue::AddressOf(false, Place::local(1)));
    assert_listed(&func, &Place::local(1), "`&raw const s`");
}

#[test]
fn raw_const_of_an_owned_field_is_a_slot_write_channel() {
    let field = Place { local: 2, projections: vec![Projection::Field(0)] };
    let func = body_with(Rvalue::AddressOf(false, field.clone()));
    assert_listed(&func, &field, "`&raw const w.0`");
}

#[test]
fn mutable_borrows_are_slot_write_channels() {
    let func = body_with(Rvalue::AddressOf(true, Place::local(1)));
    assert_listed(&func, &Place::local(1), "`&raw mut s`");
    let func = body_with(Rvalue::Ref { mutable: true, place: Place::local(1) });
    assert_listed(&func, &Place::local(1), "`&mut s`");
}

/// `&raw const (*s)` — the place rustc takes for `s.len()` — points at the
/// POINTEE. Listing it would put `s*` (every element) on the havoc list of every
/// body that indexes a slice, which is the over-kill the plain relation removed.
#[test]
fn raw_const_through_a_deref_is_not_a_slot_channel() {
    let pointee = Place { local: 1, projections: vec![Projection::Deref] };
    let func = body_with(Rvalue::AddressOf(false, pointee.clone()));
    let listed = mutably_borrowed_local_names(&func);
    assert!(
        listed.is_empty(),
        "`&raw const (*s)` hands out no pointer to a slot; list = {listed:?} \
         (would-be entry `{}`)",
        slot(&func, &pointee)
    );
}

/// A write through a pointer derived from a SHARED reference is UB under both
/// Stacked and Tree Borrows, so `&s` is no slot-write channel.
#[test]
fn a_shared_borrow_is_not_a_slot_channel() {
    let func = body_with(Rvalue::Ref { mutable: false, place: Place::local(1) });
    let listed = mutably_borrowed_local_names(&func);
    assert!(listed.is_empty(), "`&s` is not a slot-write channel; list = {listed:?}");
}

// ── the rule table, and each stability scan of a local's own storage ─────────────

fn single_block_func(locals: Vec<LocalDecl>, stmts: Vec<Statement>) -> VerifiableFunction {
    VerifiableFunction {
        name: "t".to_string(),
        def_path: "test::t".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 0,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `_0: u32, _1: [u32; 4] "a", _2: usize "i", _3: *const [u32; 4], _4: *const usize,
/// _5: &[u32] "s", _6: *const [u32]`, no parameters, one block.
fn slot_channel_func(stmts: Vec<Statement>) -> VerifiableFunction {
    let raw = |pointee: Ty| Ty::RawPtr { mutable: false, pointee: Box::new(pointee) };
    let arr = Ty::Array { elem: Box::new(Ty::u32()), len: 4 };
    let slice = Ty::Slice { elem: Box::new(Ty::u32()) };
    single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: arr.clone(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
            LocalDecl { index: 3, ty: raw(arr), name: None },
            LocalDecl { index: 4, ty: raw(Ty::usize()), name: None },
            LocalDecl {
                index: 5,
                ty: Ty::Ref { mutable: false, inner: Box::new(slice.clone()) },
                name: Some("s".into()),
            },
            LocalDecl { index: 6, ty: raw(slice), name: None },
        ],
        stmts,
    )
}

fn assign_stmt(dest: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(dest), rvalue, span: SourceSpan::default() }
}

fn array_literal() -> Statement {
    assign_stmt(
        1,
        Rvalue::Aggregate(
            AggregateKind::Array,
            (1..=4).map(|v| Operand::Constant(ConstValue::Uint(v, 32))).collect(),
        ),
    )
}

fn index_one() -> Statement {
    assign_stmt(2, Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64))))
}

/// `_6 = &raw const (*_5)` — rustc's `PtrMetadata` idiom for `s.len()`.
fn ptr_metadata_idiom() -> Statement {
    assign_stmt(
        6,
        Rvalue::AddressOf(false, Place { local: 5, projections: vec![Projection::Deref] }),
    )
}

#[test]
fn slot_channel_rule_names_raw_const_of_an_owned_place_and_nothing_behind_a_deref() {
    let func = slot_channel_func(vec![]);
    let owned = Place::local(2);
    let behind = Place { local: 5, projections: vec![Projection::Deref] };
    let field = Place { local: 1, projections: vec![Projection::Field(0)] };
    for (rvalue, want) in [
        (Rvalue::Ref { mutable: true, place: owned.clone() }, Some(&owned)),
        (Rvalue::AddressOf(true, owned.clone()), Some(&owned)),
        (Rvalue::AddressOf(false, owned.clone()), Some(&owned)),
        (Rvalue::AddressOf(false, field.clone()), Some(&field)),
        (Rvalue::Ref { mutable: true, place: behind.clone() }, Some(&behind)),
        (Rvalue::AddressOf(true, behind.clone()), Some(&behind)),
        // Not channels: a shared borrow, and `&raw const` of a pointee.
        (Rvalue::Ref { mutable: false, place: owned.clone() }, None),
        (Rvalue::AddressOf(false, behind.clone()), None),
    ] {
        assert_eq!(own_storage_write_borrow(&func, &rvalue), want, "{rvalue:?}");
    }
}

#[test]
fn raw_const_of_an_owned_local_destabilizes_its_place_source() {
    assert!(crate::place_source_is_stable(&slot_channel_func(vec![index_one()]), 2), "control");
    let aliased = slot_channel_func(vec![
        index_one(),
        assign_stmt(4, Rvalue::AddressOf(false, Place::local(2))),
    ]);
    assert!(!crate::place_source_is_stable(&aliased, 2), "`&raw const i` is a write channel");
    // The pointee idiom does not write the REFERENCE's own value, so the slot rule
    // leaves it off (`own_storage_write_borrow` above). `place_source_is_stable` refuses
    // it anyway since 2026-10-03 (UF-1 review, 28a0fc4994): it asks the wide form keyed
    // on the local, every `&raw` rooted at it, which is stricter than the slot
    // question and fail-closed.
    let idiom = slot_channel_func(vec![ptr_metadata_idiom()]);
    assert!(
        !crate::place_source_is_stable(&idiom, 5),
        "`place_source_is_stable` asks the wide form: `&raw const (*s)` is rooted at `s`"
    );
}

#[test]
fn raw_const_of_an_owned_local_poisons_its_constant_index() {
    assert_eq!(
        crate::index_local_const(&slot_channel_func(vec![index_one()]), 2),
        Some(1),
        "control"
    );
    let aliased = slot_channel_func(vec![
        index_one(),
        assign_stmt(4, Rvalue::AddressOf(false, Place::local(2))),
    ]);
    assert_eq!(crate::index_local_const(&aliased, 2), None, "`&raw const i` can write `i`");
}

#[test]
fn raw_const_of_an_owned_array_breaks_its_index_naming_and_escapes_it() {
    let literal_only = slot_channel_func(vec![array_literal()]);
    assert!(crate::array_local_index_naming_stable(&literal_only, 1), "control");
    assert!(!crate::array_local_escapes(&literal_only, 1), "control");
    for aliased_place in
        [Place::local(1), Place { local: 1, projections: vec![Projection::Index(2)] }]
    {
        let aliased = slot_channel_func(vec![
            array_literal(),
            assign_stmt(3, Rvalue::AddressOf(false, aliased_place.clone())),
        ]);
        assert!(
            !crate::array_local_index_naming_stable(&aliased, 1),
            "`&raw const {aliased_place:?}` can write `a`'s elements"
        );
        assert!(
            crate::array_local_escapes(&aliased, 1),
            "`&raw const {aliased_place:?}` escapes `a`"
        );
    }
}

// ── the POINTER rule (`path_defs::borrow_write_target`) and the scans that ask it ──
//
// The family's wide member: `&mut p`, `&raw mut p`, `&raw const p` for ANY `p`, a
// `Deref` included, except a `&raw const` through a shared reference local to
// pointer-free `Freeze` data (`addr_of_is_read_only`: a write there is UB). It is
// asked by scans of what a local POINTS TO, where the slot rule's `Deref` exclusion
// is the wrong test (a write through `&raw const (*s).0` derived from `&mut` changes
// `(*s).0`). The real-MIR counter-programs are in tests/raw_const_float_scans.rs;
// these pin the rule and each consumer.

/// `_0: f64, _1: &mut (f64, f64) "s" (the one parameter), _2: f64 "v",
/// _3: *const f64, _4: *const (f64, f64)`, one block of `stmts`.
fn pointee_func(stmts: Vec<Statement>) -> VerifiableFunction {
    let pair = Ty::Tuple(vec![Ty::f64_ty(), Ty::f64_ty()]);
    let mut f = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::f64_ty(), name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Ref { mutable: true, inner: Box::new(pair.clone()) },
                name: Some("s".into()),
            },
            LocalDecl { index: 2, ty: Ty::f64_ty(), name: Some("v".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::f64_ty()) },
                name: None,
            },
            LocalDecl {
                index: 4,
                ty: Ty::RawPtr { mutable: false, pointee: Box::new(pair) },
                name: None,
            },
        ],
        stmts,
    );
    f.body.arg_count = 1;
    f.body.return_ty = Ty::f64_ty();
    f
}

fn two() -> Statement {
    assign_stmt(2, Rvalue::Use(Operand::Constant(ConstValue::Float(2.0))))
}

/// `&raw const (*s).0` — a pointer to what the parameter points to.
fn raw_const_pointee_field() -> Statement {
    assign_stmt(
        3,
        Rvalue::AddressOf(
            false,
            Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] },
        ),
    )
}

#[test]
fn pointer_rule_names_every_write_capable_borrow_and_the_slot_rule_is_it_minus_raw_const_pointees()
{
    use super::borrow_write_target;
    let func = pointee_func(vec![]);
    let owned = Place::local(2);
    let behind = Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] };
    for place in [&owned, &behind] {
        for rvalue in [
            Rvalue::Ref { mutable: true, place: place.clone() },
            Rvalue::AddressOf(true, place.clone()),
            Rvalue::AddressOf(false, place.clone()),
        ] {
            assert_eq!(borrow_write_target(&func, &rvalue), Some(place), "{rvalue:?}");
            // The family relation: the slot rule agrees everywhere except a
            // `&raw const` of a place behind a `Deref`.
            let pointee_only = matches!(rvalue, Rvalue::AddressOf(false, _)) && place == &behind;
            let want = if pointee_only { None } else { Some(place) };
            assert_eq!(own_storage_write_borrow(&func, &rvalue), want, "{rvalue:?}");
        }
        let shared = Rvalue::Ref { mutable: false, place: place.clone() };
        assert_eq!(borrow_write_target(&func, &shared), None, "`&p` writes nothing");
        assert_eq!(own_storage_write_borrow(&func, &shared), None, "`&p` writes nothing");
    }
    // The one `&raw const` of a pointee the pointer rule leaves off: through a SHARED
    // reference local to pointer-free `Freeze` data (`_5: &[u32]`), where a write is UB.
    let frozen = slot_channel_func(vec![]);
    let idiom = Rvalue::AddressOf(false, Place { local: 5, projections: vec![Projection::Deref] });
    assert_eq!(borrow_write_target(&frozen, &idiom), None, "read-only `&raw const (*s)`");
}

#[test]
fn raw_const_of_a_float_local_poisons_its_def_set() {
    use super::float_range::float_whole_local_defs;
    let defs = |stmts| float_whole_local_defs(&pointee_func(stmts), 2).map(|d| d.len());
    assert_eq!(defs(vec![two()]), Some(1), "control: `v = 2.0` is the one def");
    assert_eq!(
        defs(vec![two(), assign_stmt(3, Rvalue::AddressOf(false, Place::local(2)))]),
        None,
        "`&raw const v` can rewrite `v`: its def set is no value model"
    );
}

#[test]
fn raw_const_of_a_parameter_pointee_poisons_its_def_set() {
    // `float_abs_guard_magnitude_bounds`' `stable_base` reads this as the
    // stability of `(*s)…`, a place BEHIND the parameter.
    use super::float_range::float_whole_local_defs;
    let defs = |stmts| float_whole_local_defs(&pointee_func(stmts), 1).map(|d| d.len());
    assert_eq!(defs(vec![]), Some(0), "control: an unwritten parameter has no body def");
    assert_eq!(defs(vec![raw_const_pointee_field()]), None, "`&raw const (*s).0` writes `(*s).0`");
}

#[test]
fn raw_const_of_a_parameter_or_its_pointee_breaks_entry_stability() {
    use super::float_range::param_place_is_entry_stable;
    assert!(param_place_is_entry_stable(&pointee_func(vec![]), 1), "control");
    assert!(
        !param_place_is_entry_stable(&pointee_func(vec![raw_const_pointee_field()]), 1),
        "`&raw const (*s).0` can change the entry value of `s.0`"
    );
    assert!(
        !param_place_is_entry_stable(
            &pointee_func(vec![assign_stmt(4, Rvalue::AddressOf(false, Place::local(1)))]),
            1
        ),
        "`&raw const s` can rewrite the parameter"
    );
}

#[test]
fn raw_const_of_a_witness_local_poisons_its_def_set() {
    use super::witness_grounding::f4_whole_local_defs;
    // `f4_whole_local_defs` refuses parameters, so ask about the local `v`.
    let defs = |stmts| f4_whole_local_defs(&pointee_func(stmts), 2).map(|d| d.len());
    assert_eq!(defs(vec![two()]), Some(1), "control");
    assert_eq!(
        defs(vec![two(), assign_stmt(3, Rvalue::AddressOf(false, Place::local(2)))]),
        None,
        "`&raw const v` is a slot-write channel of `v`"
    );
}

// ── the PLACE-STABILITY rule (`crate::place_is_body_stable`) ─────────────────────
//
// A place BEHIND its root's `Deref` lives in the root's pointee, which the slot rule
// does not see: `&raw const (*self)` is off the slot list by design. The field-length
// guard fact (`container_len`) and the guards lane's field-place key ask this rule,
// which adds the pointer rule over every place rooted at the root. The real-MIR
// counter-programs are in tests/opaque_deref_store_reseat.rs (its field-length
// section, over tests/data/field_len_guard_pointee_channel.rs).

fn stamped_struct(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
    let mut ty = Ty::adt(name, fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect());
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(trust_types::AdtKind::Struct);
    }
    ty
}

/// `struct VH { v: Vec<u8> }`.
fn vh() -> Ty {
    stamped_struct("test::VH", vec![("v", Ty::adt("alloc::vec::Vec<u8>", vec![]))])
}

/// `_0: u8, _1: <root> "self" (the one parameter), _2: *const VH`, one block.
fn root_func(root: Ty, stmts: Vec<Statement>) -> VerifiableFunction {
    let mut f = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u8(), name: None },
            LocalDecl { index: 1, ty: root, name: Some("self".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::RawPtr { mutable: false, pointee: Box::new(vh()) },
                name: None,
            },
        ],
        stmts,
    );
    f.body.arg_count = 1;
    f
}

/// `(*self).v`.
fn field_behind_root() -> Place {
    Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] }
}

fn mint_pointer(rvalue: Rvalue) -> Statement {
    assign_stmt(2, rvalue)
}

#[test]
fn a_field_behind_a_mut_root_is_unstable_once_any_pointer_under_the_root_is_minted() {
    let mut_root = Ty::Ref { mutable: true, inner: Box::new(vh()) };
    let deref = Place { local: 1, projections: vec![Projection::Deref] };
    assert!(
        crate::place_is_body_stable(&root_func(mut_root.clone(), vec![]), &field_behind_root()),
        "control: nothing can write `(*self).v`"
    );
    for rvalue in [
        // The r8c union review's F1: the slot rule leaves this one off.
        Rvalue::AddressOf(false, deref.clone()),
        Rvalue::AddressOf(true, deref.clone()),
        Rvalue::Ref { mutable: true, place: field_behind_root() },
        Rvalue::AddressOf(false, field_behind_root()),
    ] {
        let func = root_func(mut_root.clone(), vec![mint_pointer(rvalue.clone())]);
        // The slot rule alone admits `&raw const (*self)` (that was F1);
        // `place_source_is_stable` has refused it since 2026-10-03, so F1 is closed at
        // both layers.
        if matches!(&rvalue, Rvalue::AddressOf(false, p) if p == &deref) {
            assert_eq!(
                own_storage_write_borrow(&func, &rvalue),
                None,
                "the slot rule leaves it off"
            );
            assert!(
                !crate::place_source_is_stable(&func, 1),
                "`place_source_is_stable` asks the wide form and refuses it"
            );
        }
        assert!(
            !crate::place_is_body_stable(&func, &field_behind_root()),
            "`{rvalue:?}` mints a pointer that can write `(*self).v`"
        );
    }
}

#[test]
fn a_field_behind_a_shared_root_refuses_any_raw_borrow_of_the_root() {
    let shared_root = Ty::Ref { mutable: false, inner: Box::new(vh()) };
    assert!(
        crate::place_is_body_stable(&root_func(shared_root.clone(), vec![]), &field_behind_root()),
        "control: a `&` root freezes its pointee"
    );
    let raw = Rvalue::AddressOf(false, Place { local: 1, projections: vec![Projection::Deref] });
    assert!(
        !crate::place_is_body_stable(
            &root_func(shared_root, vec![mint_pointer(raw)]),
            &field_behind_root()
        ),
        "defense in depth, as the guards lane's field key always had it"
    );
}

#[test]
fn only_a_reference_root_and_a_single_leading_deref_are_admitted() {
    // A raw-pointer root's pointee is written through any alias.
    let raw_root = Ty::RawPtr { mutable: true, pointee: Box::new(vh()) };
    assert!(!crate::place_is_body_stable(&root_func(raw_root, vec![]), &field_behind_root()));
    // A `Box` root is not held to this rule's argument either.
    let box_root = stamped_struct("alloc::boxed::Box<test::VH>", vec![]);
    assert!(!crate::place_is_body_stable(&root_func(box_root, vec![]), &field_behind_root()));
    // A second `Deref` reads through a pointer stored in the pointee.
    let holder = stamped_struct(
        "test::Holder",
        vec![("p", Ty::RawPtr { mutable: true, pointee: Box::new(vh()) })],
    );
    let through = Place {
        local: 1,
        projections: vec![
            Projection::Deref,
            Projection::Field(0),
            Projection::Deref,
            Projection::Field(0),
        ],
    };
    let shared_holder = Ty::Ref { mutable: false, inner: Box::new(holder) };
    assert!(!crate::place_is_body_stable(&root_func(shared_holder, vec![]), &through));
}

#[test]
fn a_hop_into_an_interior_mutability_wrapper_is_unstable() {
    let cell = stamped_struct("core::cell::Cell<test::VH>", vec![("value", vh())]);
    let wrapper = stamped_struct("test::W", vec![("c", cell)]);
    let into_cell = Place {
        local: 1,
        projections: vec![
            Projection::Deref,
            Projection::Field(0),
            Projection::Field(0),
            Projection::Field(0),
        ],
    };
    let shared = Ty::Ref { mutable: false, inner: Box::new(wrapper) };
    assert!(!crate::place_is_body_stable(&root_func(shared, vec![]), &into_cell));
}

#[test]
fn an_owned_place_is_the_slot_question() {
    let owned = Place { local: 1, projections: vec![Projection::Field(0)] };
    assert!(crate::place_is_body_stable(&root_func(vh(), vec![]), &owned), "control");
    let aliased = root_func(vh(), vec![mint_pointer(Rvalue::AddressOf(false, Place::local(1)))]);
    assert!(!crate::place_is_body_stable(&aliased, &owned), "`&raw const self` writes `self.v`");
}

// ── memory a SHARED reference reaches through a stored pointer ──────────────────
//
// A shared reference freezes the bytes it covers, not what a raw pointer (or a
// `Box`, or a `&mut`) stored in them points to. CALL-HAVOC-ESCAPE-2's
// `path_defs::stored_ref_pointee_names` names that memory at every call-like
// terminator; since 2026-10-08 `path_defs::deref_store_havoc_names` names it at an
// opaque store too, on the whole-function list `function_havoc_names` (the r8c
// union review's F2 on a store, which the union first closed with a second walk of
// its own; one rule now). A frozen sibling keeps its
// fact. The real-MIR counter-programs are in tests/opaque_deref_store_reseat.rs (its
// shared-reach section, over tests/data/shared_reach_pointer_havoc.rs).

fn raw_usize() -> Ty {
    Ty::RawPtr { mutable: true, pointee: Box::new(Ty::usize()) }
}

/// `struct PN { p: *mut usize, n: usize }`.
fn pn() -> Ty {
    stamped_struct("test::PN", vec![("p", raw_usize()), ("n", Ty::usize())])
}

fn shared(inner: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(inner) }
}

fn mut_ref(inner: Ty) -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(inner) }
}

/// `_0: u8, _1: <ty> "w", _2: *mut usize "q"` (both parameters); block 0 runs
/// `stmts` and returns.
fn store_func(ty: Ty, stmts: Vec<Statement>) -> VerifiableFunction {
    let mut f = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u8(), name: None },
            LocalDecl { index: 1, ty, name: Some("w".into()) },
            LocalDecl { index: 2, ty: raw_usize(), name: Some("q".into()) },
        ],
        stmts,
    );
    f.body.arg_count = 2;
    f
}

fn name_at(func: &VerifiableFunction, projections: Vec<Projection>) -> String {
    slot(func, &Place { local: 1, projections })
}

/// `(*q) = 7`: a store through a raw-pointer parameter, which folds to no referent.
fn store_through_q() -> Statement {
    Statement::Assign {
        place: Place { local: 2, projections: vec![Projection::Deref] },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64))),
        span: SourceSpan::default(),
    }
}

#[test]
fn an_opaque_store_havocs_what_a_pointer_stored_behind_a_shared_reference_reaches() {
    use Projection::{Deref, Field};
    let func = store_func(shared(pn()), vec![store_through_q()]);
    let killed = super::deref_store_havoc_names(&func, &func.body.blocks[0]);
    let pointee = name_at(&func, vec![Deref, Field(0), Deref]);
    let sibling = name_at(&func, vec![Deref, Field(1)]);
    assert!(
        killed.iter().any(|n| super::write_rebinds(n, &pointee)),
        "`{pointee}` must die at an opaque store: {killed:?}"
    );
    assert!(
        !killed.iter().any(|n| super::write_rebinds(n, &sibling)),
        "`{sibling}` sits in the bytes the shared reference freezes: {killed:?}"
    );
    // The same names a call havocs: one rule at both kinds of site.
    for n in super::stored_ref_pointee_names(&func).iter() {
        assert!(killed.contains(n), "`{n}` is havocked at a call but not at the store");
    }
    // No opaque store, no havoc.
    let quiet = store_func(shared(pn()), vec![]);
    assert!(super::deref_store_havoc_names(&quiet, &quiet.body.blocks[0]).is_empty());
}

#[test]
fn an_opaque_store_havocs_a_mut_ref_stored_behind_a_shared_reference() {
    use Projection::{Deref, Field};
    let mn = stamped_struct("test::MN", vec![("r", mut_ref(Ty::usize())), ("n", Ty::usize())]);
    let func = store_func(shared(mn), vec![store_through_q()]);
    let killed = super::deref_store_havoc_names(&func, &func.body.blocks[0]);
    let target = name_at(&func, vec![Deref, Field(0), Deref]);
    assert!(
        killed.iter().any(|n| super::write_rebinds(n, &target)),
        "`{target}` must die at an opaque store: {killed:?}"
    );
}

/// `callee_write_set`'s two refusals ask this type question (pinned end to end by
/// `callee_write_set::tests::a_pointer_stored_behind_a_shared_ref_in_the_formal_fails_closed`
/// and `..._in_the_pointee_is_not_a_replaceable_root`); this is its table.
#[test]
fn the_unretagged_pointer_question_by_type() {
    let boxed = |inner: Ty| {
        stamped_struct(
            "alloc::boxed::Box<test::T>",
            vec![(
                "0",
                stamped_struct(
                    "core::ptr::unique::Unique<test::T>",
                    vec![("pointer", Ty::RawPtr { mutable: false, pointee: Box::new(inner) })],
                ),
            )],
        )
    };
    let mn = stamped_struct("test::MN", vec![("r", mut_ref(Ty::usize()))]);
    for (ty, want) in [
        (raw_usize(), true),
        (shared(pn()), true),
        (shared(shared(pn())), true),
        (shared(mn.clone()), true),
        (Ty::Tuple(vec![Ty::u8(), shared(pn())]), true),
        (boxed(pn()), true),
        (shared(boxed(Ty::usize())), true),
        // A reference or `Box` held DIRECTLY is retagged where it gets its value.
        (mut_ref(Ty::usize()), false),
        (boxed(Ty::usize()), false),
        (shared(Ty::usize()), false),
        // A SHARED reference stored behind a `&`: its target is frozen while it lives.
        (shared(shared(Ty::usize())), false),
        (Ty::usize(), false),
    ] {
        assert_eq!(super::ty_reaches_unretagged_pointer(&ty, false), want, "{ty:?}");
    }
    // A `&mut` met behind a `Deref` was never retagged by this function.
    assert!(super::ty_reaches_unretagged_pointer(&mut_ref(Ty::usize()), true));
}
