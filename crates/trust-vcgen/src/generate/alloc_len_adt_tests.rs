//! ALLOC-STRIDE-ADT-1 (2026-10-07): `Vec::with_capacity(src.len())` over a
//! `&[UserAdt]` source, end to end through `generate_vcs`.
//!
//! Before: `element_stride_lower_bound` sized only primitives, tuples and
//! arrays, so a user struct source had stride 0 and the row kept both the
//! availability ceiling and the capacity term. After: an extractor-minted
//! struct/enum/union is sized by a lower bound of its layout, so a source whose
//! bound reaches the target drops the row — and every refusal the lane had for
//! a ZST, a generic, or a count that is not a length (`len + 1`, clean-ck0
//! term.rs) is kept.
//!
//! On the verifier lane `layout` is `None`, so only the field-level bound
//! applies, and it is near 0 for pointer-heavy elements (`Vec` is `Ty::Seq`,
//! `String` a `Vec`, `Arc` a pointer, a recursive type a by-name datatype).
//! clean-ck0's six `Vec::with_capacity(src.len())` rows have such sources and
//! stay refused: `pointer_heavy_clean_ck0_sources_keep_the_row_on_the_verifier_lane`
//! rails that (DECISION_QUEUE ALLOC-STRIDE-ADT-2 is the missing carrier).

use trust_types::{
    AdtKind, BasicBlock, BinOp, BlockId, CalleeKey, ConstValue, LocalDecl, Operand, Place, Rvalue,
    SourceSpan, Statement, SysrootItem, Terminator, Ty, UnOp, UnwindEdge, VariantDef, VcKind,
    VerifiableBody, VerifiableFunction,
};

use crate::generate_vcs;

fn adt(kind: AdtKind, fields: Vec<Ty>, variants: Vec<VariantDef>) -> Ty {
    Ty::Adt {
        name: "user::Elem".into(),
        fields: fields
            .into_iter()
            .enumerate()
            .map(|(i, t)| (i.to_string(), t))
            .collect::<Vec<_>>()
            .into(),
        variants: variants.into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        arbitrary_precision: None,
        validity_wrapper: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(kind),
    }
}

fn u64_() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn arr(len: u64) -> Ty {
    Ty::Array { elem: Box::new(u64_()), len }
}

fn generic() -> Ty {
    Ty::Unsupported { kind: "TyKind::Param".into(), detail: "T".into() }
}

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

/// `fn f(src: &[elem]) { let _ = Vec::<[target bytes]>::with_capacity(count) }`
/// where `count` is `src.len()` (`PtrMetadata`), or `src.len() + 1` when
/// `plus_one`.
fn with_capacity_of_len(elem: Ty, target_bytes: u32, plus_one: bool) -> VerifiableFunction {
    let src_ty = Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(elem) }) };
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: src_ty, name: Some("src".into()) },
        LocalDecl { index: 2, ty: Ty::usize(), name: None },
        LocalDecl { index: 3, ty: Ty::u32(), name: Some("v".into()) },
    ];
    let mut stmts =
        vec![assign(2, Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))))];
    let count = if plus_one {
        locals.push(LocalDecl { index: 4, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None });
        locals.push(LocalDecl { index: 5, ty: Ty::usize(), name: None });
        stmts.push(assign(
            4,
            Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Uint(1, 64)),
            ),
        ));
        stmts.push(assign(5, Rvalue::Use(Operand::Move(Place::field(4, 0)))));
        5
    } else {
        2
    };
    let callee =
        format!("alloc::vec::Vec::<u8>::with_capacity::<__trust_elem_bytes@{target_bytes}>");
    VerifiableFunction {
        name: "from_src".to_string(),
        def_path: "test::from_src".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts,
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee,
                    args: vec![Operand::Move(Place::local(count))],
                    dest: Place::local(3),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: Some(CalleeKey {
                        sysroot_item: Some(SysrootItem::VecWithCapacity),
                        krate_is_real_sysroot: true,
                        krate_name_is_ambiguous: false,
                        stable_crate_id: 0x1234,
                        krate_name: "alloc".into(),
                        foreign_block_leaf: None,
                        upstream_foreign_link_symbol: None,
                        diverging_entry: None,
                    }),
                    is_foreign: false,
                },
            }],
            arg_count: 1,
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

fn alloc_rows(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnboundedAllocation { .. }))
        .count()
}

fn variant(name: &str, fields: Vec<Ty>) -> VariantDef {
    VariantDef {
        name: name.into(),
        discriminant: 0,
        fields: fields.into_iter().enumerate().map(|(i, t)| (i.to_string(), t)).collect(),
    }
}

#[test]
fn primitive_source_control_has_no_row() {
    assert_eq!(alloc_rows(&with_capacity_of_len(u64_(), 8, false)), 0);
}

#[test]
fn user_struct_sources_at_least_as_wide_as_the_target_have_no_row() {
    // repro.rs `from_plain`: `struct Plain { a: [u64; 10] }` -> `Vec<u64>`.
    let plain = adt(AdtKind::Struct, vec![arr(10)], vec![]);
    assert_eq!(alloc_rows(&with_capacity_of_len(plain.clone(), 8, false)), 0);
    // Nested: `struct Outer { p: Plain, x: u8 }` -> a `Vec<[u64; 10]>` (80 <= 81).
    let outer =
        adt(AdtKind::Struct, vec![plain.clone(), Ty::Int { width: 8, signed: false }], vec![]);
    assert_eq!(alloc_rows(&with_capacity_of_len(outer, 80, false)), 0);
    // An enum whose largest variant is at least the target.
    let enum_ = adt(AdtKind::Enum, vec![], vec![variant("A", vec![arr(2)]), variant("B", vec![])]);
    assert_eq!(alloc_rows(&with_capacity_of_len(enum_, 16, false)), 0);
}

#[test]
fn unsizable_or_narrower_sources_keep_the_row() {
    // A target wider than the struct's lower bound: availability is not bounded.
    let plain = adt(AdtKind::Struct, vec![arr(10)], vec![]);
    assert!(alloc_rows(&with_capacity_of_len(plain.clone(), 81, false)) >= 1);
    // A generic element sizes 0 — stride unknown, row kept.
    let generic_struct = adt(AdtKind::Struct, vec![generic()], vec![]);
    assert!(alloc_rows(&with_capacity_of_len(generic_struct, 1, false)) >= 1);
    assert!(alloc_rows(&with_capacity_of_len(generic(), 1, false)) >= 1);
    // A zero-sized struct holds no memory and its slice length is unbounded.
    let zst = adt(AdtKind::Struct, vec![Ty::Unit, arr(0)], vec![]);
    assert!(alloc_rows(&with_capacity_of_len(zst, 1, false)) >= 1);
    // A fieldless enum is sized 0 here (the tag is not counted).
    let fieldless = adt(AdtKind::Enum, vec![], vec![variant("A", vec![]), variant("B", vec![])]);
    assert!(alloc_rows(&with_capacity_of_len(fieldless, 1, false)) >= 1);
    // An ADT the extractor did not mint (`adt_kind: None`) is not sized.
    let synthetic = Ty::adt("user::Elem", vec![("a".into(), arr(10))]);
    assert!(alloc_rows(&with_capacity_of_len(synthetic, 8, false)) >= 1);
}

#[test]
fn len_plus_one_over_ask_still_has_its_row() {
    // clean-ck0 term.rs: a count of `len + 1` is not a length; a wide struct
    // source does not change that (`len + 1` slots can exceed `isize::MAX` bytes
    // at the target stride when `len * S` is exactly at the limit with `S = T`).
    let plain = adt(AdtKind::Struct, vec![arr(10)], vec![]);
    assert!(alloc_rows(&with_capacity_of_len(plain, 80, true)) >= 1);
    assert!(alloc_rows(&with_capacity_of_len(u64_(), 8, true)) >= 1);
}

/// clean-ck0's six rows, by their sources' verifier-lane spelling: the
/// field-level bound counts only the scalar fields, so each stays below its
/// target and keeps its row. The faithful lane's `layout` (rustc's size) would
/// decide the first — shown last, as what the missing carrier would buy.
#[test]
fn pointer_heavy_clean_ck0_sources_keep_the_row_on_the_verifier_lane() {
    let u32_ = Ty::Int { width: 32, signed: false };
    let term = Ty::Datatype { name: "clean_ck0::Term".into(), variants: vec![] };
    let seq = |elem: Ty| Ty::Seq { elem: Box::new(elem), drop_auth: None };
    let arc = adt(
        AdtKind::Struct,
        vec![Ty::RawPtr { mutable: false, pointee: Box::new(term.clone()) }],
        vec![],
    );
    let name_repr =
        adt(AdtKind::Enum, vec![], vec![variant("Anonymous", vec![]), variant("Node", vec![arc])]);
    let name = adt(AdtKind::Struct, vec![name_repr], vec![]);
    let string = adt(AdtKind::Struct, vec![seq(Ty::Int { width: 8, signed: false })], vec![]);
    // recursor_build.rs:106 / recursor.rs:204 — `CtorInfo` (88 bytes; bound 4)
    // into `Vec<Term>` (24) and `Vec<IotaRule>` (72).
    let ctor_info = adt(
        AdtKind::Struct,
        vec![name.clone(), u32_.clone(), seq(term.clone()), string.clone()],
        vec![],
    );
    assert!(alloc_rows(&with_capacity_of_len(ctor_info.clone(), 24, false)) >= 1);
    assert!(alloc_rows(&with_capacity_of_len(ctor_info.clone(), 72, false)) >= 1);
    // nested.rs:142 — `Occurrence { Name, Vec, Vec, Name }` (bound 0) into
    // `Vec<InductiveDecl>` (64).
    let occurrence = adt(
        AdtKind::Struct,
        vec![name.clone(), seq(u32_.clone()), seq(term.clone()), name.clone()],
        vec![],
    );
    assert!(alloc_rows(&with_capacity_of_len(occurrence, 64, false)) >= 1);
    // nested.rs:417 — `(Name, Term)` into `Vec<(Name, Term)>` (32).
    assert!(alloc_rows(&with_capacity_of_len(Ty::Tuple(vec![name, term]), 32, false)) >= 1);
    // The faithful lane's rustc size decides `CtorInfo -> Term`.
    let mut faithful = ctor_info;
    if let Ty::Adt { layout, .. } = &mut faithful {
        *layout = Some(Box::new(trust_types::AdtLayoutInfo {
            size: 88,
            align: 8,
            field_offsets: vec![0, 80, 8, 32],
            repr: "rust".into(),
        }));
    }
    assert_eq!(alloc_rows(&with_capacity_of_len(faithful, 24, false)), 0);
}

// ── ALLOC-STRIDE-ADT-2 (2026-10-07): the compiler's element-size table ──────
//
// The rows above are decided by the structural bound alone, which is what every
// caller without the compiler's `VcgenContext` table sees. Below, the same
// sources with a table the compiler would supply (rustc's `layout_of` size of the
// key's preimages): the pointer-heavy clean-ck0 sources discharge exactly when
// the recorded size reaches the target, and every guard keeps the row.

fn clean_ck0_sources() -> (Ty, Ty, Ty) {
    let u32_ = Ty::Int { width: 32, signed: false };
    let term = Ty::Datatype { name: "clean_ck0::Term".into(), variants: vec![] };
    let seq = |elem: Ty| Ty::Seq { elem: Box::new(elem), drop_auth: None };
    let arc = adt(
        AdtKind::Struct,
        vec![Ty::RawPtr { mutable: false, pointee: Box::new(term.clone()) }],
        vec![],
    );
    let name_repr =
        adt(AdtKind::Enum, vec![], vec![variant("Anonymous", vec![]), variant("Node", vec![arc])]);
    let name = adt(AdtKind::Struct, vec![name_repr], vec![]);
    let string = adt(AdtKind::Struct, vec![seq(Ty::Int { width: 8, signed: false })], vec![]);
    let ctor_info =
        adt(AdtKind::Struct, vec![name.clone(), u32_.clone(), seq(term.clone()), string], vec![]);
    let occurrence = adt(
        AdtKind::Struct,
        vec![name.clone(), seq(u32_), seq(term.clone()), name.clone()],
        vec![],
    );
    (ctor_info, occurrence, Ty::Tuple(vec![name, term]))
}

fn table_of(rows: &[(&Ty, Option<u64>)]) -> crate::ElemSizeTable {
    let mut table = crate::ElemSizeTable::new();
    for (key, size) in rows {
        table.record((*key).clone(), *size);
    }
    table
}

/// Rows under the compiler's context carrying `table` for `func` itself.
fn alloc_rows_with_table(func: &VerifiableFunction, table: crate::ElemSizeTable) -> usize {
    let context =
        crate::VcgenContext::for_function(func.def_path.clone()).with_elem_sizes(table, func);
    crate::generate_vcs_with_context(func, &context)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnboundedAllocation { .. }))
        .count()
}

#[test]
fn clean_ck0_sources_discharge_only_with_a_table_row_at_least_the_target() {
    let (ctor_info, occurrence, name_term) = clean_ck0_sources();
    // recursor_build.rs:106 — `CtorInfo` (88) into `Vec<Term>` (24).
    let f = with_capacity_of_len(ctor_info.clone(), 24, false);
    assert!(alloc_rows(&f) >= 1, "no table: the ADT-1 structural bound (4) keeps the row");
    assert_eq!(alloc_rows_with_table(&f, table_of(&[(&ctor_info, Some(88))])), 0);
    // A recorded size below the target keeps the row.
    assert!(alloc_rows_with_table(&f, table_of(&[(&ctor_info, Some(16))])) >= 1);
    // recursor.rs:204 — `CtorInfo` into `Vec<IotaRule>` (72).
    let f = with_capacity_of_len(ctor_info.clone(), 72, false);
    assert_eq!(alloc_rows_with_table(&f, table_of(&[(&ctor_info, Some(88))])), 0);
    assert!(alloc_rows_with_table(&f, table_of(&[(&ctor_info, Some(64))])) >= 1);
    // nested.rs:142 — `Occurrence` into `Vec<InductiveDecl>` (64).
    let f = with_capacity_of_len(occurrence.clone(), 64, false);
    assert!(alloc_rows(&f) >= 1);
    assert_eq!(alloc_rows_with_table(&f, table_of(&[(&occurrence, Some(64))])), 0);
    // nested.rs:417 — `(Name, Term)` into `Vec<(Name, Term)>` (32), keyed on the
    // whole tuple ...
    let f = with_capacity_of_len(name_term.clone(), 32, false);
    assert!(alloc_rows(&f) >= 1);
    assert_eq!(alloc_rows_with_table(&f, table_of(&[(&name_term, Some(32))])), 0);
    // ... or summed from its fields' rows (every node takes max(structural, table)).
    let Ty::Tuple(fields) = &name_term else { unreachable!() };
    assert_eq!(
        alloc_rows_with_table(&f, table_of(&[(&fields[0], Some(8)), (&fields[1], Some(24))])),
        0
    );
    assert!(
        alloc_rows_with_table(&f, table_of(&[(&fields[0], Some(8)), (&fields[1], None)])) >= 1,
        "a poisoned field contributes 0: 8 < 32"
    );
}

#[test]
fn a_poisoned_or_zero_sized_key_keeps_the_row() {
    let (ctor_info, ..) = clean_ck0_sources();
    let f = with_capacity_of_len(ctor_info.clone(), 24, false);
    // One preimage could not be sized (generic, unsized, layout error): sticky.
    let mut table = table_of(&[(&ctor_info, Some(88))]);
    table.record(ctor_info.clone(), None);
    table.record(ctor_info.clone(), Some(88));
    assert!(alloc_rows_with_table(&f, table) >= 1);
    // A second preimage of the same key is smaller: the minimum decides.
    let mut table = table_of(&[(&ctor_info, Some(88))]);
    table.record(ctor_info.clone(), Some(8));
    assert!(alloc_rows_with_table(&f, table) >= 1);
    // A zero-sized row is no stride.
    let zst = adt(AdtKind::Struct, vec![Ty::Unit], vec![]);
    let f = with_capacity_of_len(zst.clone(), 1, false);
    assert!(alloc_rows_with_table(&f, table_of(&[(&zst, Some(0))])) >= 1);
}

#[test]
fn a_generic_source_keeps_its_row_whatever_the_table_says() {
    // The recorder never sizes a generic preimage; and a `Param`-shaped leaf is
    // not a consulted key shape, so even a (forged) row cannot size it.
    let f = with_capacity_of_len(generic(), 1, false);
    assert!(alloc_rows_with_table(&f, table_of(&[(&generic(), Some(64))])) >= 1);
    let generic_struct = adt(AdtKind::Struct, vec![generic()], vec![]);
    let f = with_capacity_of_len(generic_struct.clone(), 8, false);
    assert!(alloc_rows_with_table(&f, table_of(&[(&generic_struct, None)])) >= 1);
    // A hand-built ADT (`adt_kind: None`) is not a consulted key either.
    let synthetic = Ty::adt("user::Elem", vec![("a".into(), Ty::u32())]);
    let f = with_capacity_of_len(synthetic.clone(), 8, false);
    assert!(alloc_rows_with_table(&f, table_of(&[(&synthetic, Some(64))])) >= 1);
}

#[test]
fn len_plus_one_keeps_its_row_with_the_table() {
    let (ctor_info, ..) = clean_ck0_sources();
    let f = with_capacity_of_len(ctor_info.clone(), 24, true);
    assert!(alloc_rows_with_table(&f, table_of(&[(&ctor_info, Some(88))])) >= 1);
}

#[test]
fn another_owner_or_a_changed_function_never_reads_the_table() {
    let (ctor_info, ..) = clean_ck0_sources();
    let f = with_capacity_of_len(ctor_info.clone(), 24, false);
    let table = table_of(&[(&ctor_info, Some(88))]);
    // Owner mismatch: a context built for another def path installs nothing ...
    let other = crate::VcgenContext::for_function("test::other").with_elem_sizes(table.clone(), &f);
    assert!(!other.has_elem_sizes());
    // ... and one installed for another function is dropped at the entry's owner check.
    let mut g = f.clone();
    g.def_path = "test::other".into();
    let for_g = crate::VcgenContext::for_function("test::other").with_elem_sizes(table.clone(), &g);
    assert!(for_g.has_elem_sizes());
    let rows = crate::generate_vcs_with_context(&f, &for_g)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnboundedAllocation { .. }))
        .count();
    assert!(rows >= 1);
    // The function's types changed after install (another instance of the def
    // path, or a transform): the binding digest no longer matches.
    let context =
        crate::VcgenContext::for_function(f.def_path.clone()).with_elem_sizes(table.clone(), &f);
    let mut changed = f.clone();
    changed.body.locals.push(LocalDecl { index: 4, ty: Ty::Bool, name: None });
    let rows = crate::generate_vcs_with_context(&changed, &context)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnboundedAllocation { .. }))
        .count();
    assert!(rows >= 1, "a changed function must not read a table bound to another digest");
    // The unchanged function under the same context does read it.
    let rows = crate::generate_vcs_with_context(&f, &context)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnboundedAllocation { .. }))
        .count();
    assert_eq!(rows, 0);
    // An empty table installs nothing.
    assert!(
        !crate::VcgenContext::for_function(f.def_path.clone())
            .with_elem_sizes(crate::ElemSizeTable::new(), &f)
            .has_elem_sizes()
    );
}

#[test]
fn a_decoded_function_keeps_its_row() {
    // A function decoded from its wire form carries no table (the table has no
    // serde path) and every non-compiler entry supplies none.
    let (ctor_info, ..) = clean_ck0_sources();
    let f = with_capacity_of_len(ctor_info, 24, false);
    let decoded: VerifiableFunction =
        serde_json::from_str(&serde_json::to_string(&f).expect("encode")).expect("decode");
    assert_eq!(decoded.content_hash(), f.content_hash());
    assert!(alloc_rows(&decoded) >= 1);
}

#[test]
fn a_fresh_frame_of_the_same_function_inherits_the_table_and_no_other_does() {
    let (ctor_info, ..) = clean_ck0_sources();
    let f = with_capacity_of_len(ctor_info.clone(), 24, false);
    let table = table_of(&[(&ctor_info, Some(88))]);
    let context = crate::VcgenContext::for_function(f.def_path.clone()).with_elem_sizes(table, &f);
    let count = |vcs: Vec<trust_types::VerificationCondition>| {
        vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::UnboundedAllocation { .. })).count()
    };
    crate::with_function_vcgen_context(&f.def_path, &context, || {
        // `generate_vcs` pushes a fresh frame for the same def path: inherits.
        assert_eq!(count(generate_vcs(&f)), 0);
        // The recursion-SCC regeneration frame of the same function: inherits.
        let scc = Some(crate::RecursionSccContext::default());
        assert_eq!(
            count(crate::with_recursion_scc_context(&f.def_path, scc, || generate_vcs(&f))),
            0
        );
        // Another function's fresh frame does not.
        let mut g = f.clone();
        g.def_path = "test::other".into();
        assert!(count(generate_vcs(&g)) >= 1);
    });
    // Outside the compiler's frame there is nothing to inherit.
    assert!(count(generate_vcs(&f)) >= 1);
}

/// `fn f(a: &[A], b: &[B]) { Vec::<[T]>::with_capacity(a.len() + b.len()) }`.
fn with_capacity_of_two_lens(a: Ty, b: Ty, target_bytes: u32) -> VerifiableFunction {
    let slice =
        |elem: Ty| Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(elem) }) };
    let mut f = with_capacity_of_len(a.clone(), target_bytes, false);
    f.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: slice(a), name: Some("a".into()) },
        LocalDecl { index: 2, ty: slice(b), name: Some("b".into()) },
        LocalDecl { index: 3, ty: Ty::usize(), name: None },
        LocalDecl { index: 4, ty: Ty::usize(), name: None },
        LocalDecl { index: 5, ty: Ty::usize(), name: None },
        LocalDecl { index: 6, ty: Ty::u32(), name: Some("v".into()) },
    ];
    f.body.arg_count = 2;
    f.body.blocks[0].stmts = vec![
        assign(3, Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1)))),
        assign(4, Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(2)))),
        assign(
            5,
            Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(3)),
                Operand::Copy(Place::local(4)),
            ),
        ),
    ];
    if let Terminator::Call { args, dest, .. } = &mut f.body.blocks[0].terminator {
        *args = vec![Operand::Move(Place::local(5))];
        *dest = Place::local(6);
    }
    f
}

#[test]
fn a_two_term_sum_with_one_unknown_stride_keeps_its_row() {
    let (ctor_info, occurrence, _) = clean_ck0_sources();
    // Both known and wide enough: T*(S1+S2) <= S1*S2 for T=24, S1=88, S2=64.
    let f = with_capacity_of_two_lens(ctor_info.clone(), occurrence.clone(), 24);
    assert!(alloc_rows(&f) >= 1);
    let both = table_of(&[(&ctor_info, Some(88)), (&occurrence, Some(64))]);
    assert_eq!(alloc_rows_with_table(&f, both), 0);
    // One term unknown: the row stays.
    let one = table_of(&[(&ctor_info, Some(88)), (&occurrence, None)]);
    assert!(alloc_rows_with_table(&f, one) >= 1);
    let only_one = table_of(&[(&ctor_info, Some(88))]);
    assert!(alloc_rows_with_table(&f, only_one) >= 1);
}

#[test]
fn wave503_memoized_elem_size_and_primitive_decimal_digests_preserve_exact_semantics() {
    let (ctor_info, occurrence, name_term) = clean_ck0_sources();
    let f = with_capacity_of_two_lens(ctor_info.clone(), occurrence.clone(), 24);
    let uncached_elem = crate::elem_sizes::elem_size_binding_digest(&f);
    let uncached_prim = crate::primitive_decimal_strings::body_digest(&f);
    let _scope = super::FuncAnalysisScope::enter(&f);
    assert_eq!(super::elem_size_binding_digest_for(&f), uncached_elem);
    assert_eq!(super::elem_size_binding_digest_for(&f), uncached_elem);
    assert_eq!(super::primitive_decimal_body_digest_for(&f), uncached_prim);
    assert_eq!(super::primitive_decimal_body_digest_for(&f), uncached_prim);

    let mut mutated = f.clone();
    mutated.body.locals.push(LocalDecl { index: 99, ty: name_term, name: None });
    assert_ne!(
        super::elem_size_binding_digest_for(&mutated),
        uncached_elem,
        "a different body inside an outer FuncAnalysisScope must not hit the outer frame's digest"
    );
    assert_ne!(
        super::primitive_decimal_body_digest_for(&mutated),
        uncached_prim,
        "a different body inside an outer FuncAnalysisScope must not hit the outer frame's digest"
    );
}
