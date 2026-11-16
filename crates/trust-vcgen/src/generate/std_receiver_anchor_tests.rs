//! Trust (STD-RECEIVER-ANCHOR-1, 2026-10-04): the length-benign `&mut` receiver and
//! the `?` re-wrap name std's own impl, not std's trait path or a spelling. Pinned
//! on REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, `scratchpad/stage1-w11fix`, the
//! stage 1 of `38e6c69b1c`; this branch's base `43dc4c407d` adds only tests and docs
//! to it), stored under `tests/fixtures/std_receiver_anchor/`.
//!
//! Sources (`gen_impl.rs`, a lib; `cross.rs` against the lib `dep.rs`):
//!
//! ```text
//! // gen_impl.rs — a GENERIC local impl, which the producer does not rename to its
//! // impl path, so the call keeps std's trait spelling.
//! pub struct K<T>(pub T);
//! impl<T> Index<K<T>> for Vec<u32> { type Output = u32; fn index(&self, _k: K<T>) -> &u32 { &0 } }
//! impl<T> IndexMut<K<T>> for Vec<u32> {
//!     fn index_mut(&mut self, _k: K<T>) -> &mut u32 { self.truncate(0); Box::leak(Box::new(0u32)) }
//! }
//! pub fn user_len(mut v: Vec<u32>) -> usize { if v.len() == 0 { return 0; } v[K(())] = 1; v.len() - 1 }
//! pub fn user_idx(mut v: Vec<u32>, i: usize) -> u32 { if i < v.len() { v[K(())] = 1; v[i] } else { 0 } }
//!
//! // dep.rs — the same impl, non-generic (`pub struct K;`), in a dependency;
//! // cross.rs — `user_len`/`user_idx` again, with `v[K] = 1`.
//! ```
//!
//! The calls render `<alloc::vec::Vec<u32> as core::ops::index::IndexMut<gen_impl::K<()>>>::index_mut`
//! and `<alloc::vec::Vec<u32> as core::ops::index::IndexMut<dep::K>>::index_mut`.
//! BEFORE, `local_mut_borrows_may_resize` counted the `&mut v` they consume as
//! length-benign (`callee_is_std_ops_method` reads only the trait path), the two
//! `v.len()` were tied to one `coll_len(v)`, and the compiler read `user_len`'s
//! `overflow:sub proved` (Certified) under every policy and removed the check: the
//! advisory build returns `usize::MAX` for `vec![7]`; `user_idx` read `slice proved`.
//!
//! The std controls (`spell.rs`) are each `if <len guard> { return 0; } <index
//! write>; v.len() - 1` with the write `v[0] = 1`, `v[0..2].sort()`, `v[1..].sort()`,
//! `v[..2].sort()`, `v[..].sort()`, `v[0..=1].sort()`, `v[..=1].sort()`, on a
//! `VecDeque` `d[0] = 1`, and on a `String` `s[0..1]`/`s[1..]`/`s[..]`
//! `.make_ascii_uppercase()`. Each `Vec` one read `overflow:sub proved` BEFORE and
//! must keep its tie.

use trust_types::{Formula, Operand, Place, Terminator, VerifiableFunction};

use super::is_std_container_index_call;

const USER_GENERIC_IMPL_LEN: &str =
    include_str!("../../tests/fixtures/std_receiver_anchor/user_generic_impl_len.json");
const USER_GENERIC_IMPL_IDX: &str =
    include_str!("../../tests/fixtures/std_receiver_anchor/user_generic_impl_idx.json");
const USER_DEP_IMPL_LEN: &str =
    include_str!("../../tests/fixtures/std_receiver_anchor/user_dep_impl_len.json");
const USER_DEP_IMPL_IDX: &str =
    include_str!("../../tests/fixtures/std_receiver_anchor/user_dep_impl_idx.json");

/// `(fixture, the index call it must contain)` for the std controls.
const STD_CONTROLS: [(&str, &str); 9] = [
    (
        include_str!("../../tests/fixtures/std_receiver_anchor/std_vec_usize_len.json"),
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<usize>>::index_mut",
    ),
    (
        include_str!("../../tests/fixtures/std_receiver_anchor/std_vec_range_len.json"),
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::Range<usize>>>::index_mut",
    ),
    (
        include_str!("../../tests/fixtures/std_receiver_anchor/std_vec_range_from_len.json"),
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::RangeFrom<usize>>>::index_mut",
    ),
    (
        include_str!("../../tests/fixtures/std_receiver_anchor/std_vec_range_to_len.json"),
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::RangeTo<usize>>>::index_mut",
    ),
    (
        include_str!("../../tests/fixtures/std_receiver_anchor/std_vec_range_full_len.json"),
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::RangeFull>>::index_mut",
    ),
    (
        include_str!("../../tests/fixtures/std_receiver_anchor/std_vec_range_incl_len.json"),
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::RangeInclusive<usize>>>::index_mut",
    ),
    (
        include_str!("../../tests/fixtures/std_receiver_anchor/std_vec_range_to_incl_len.json"),
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::RangeToInclusive<usize>>>::index_mut",
    ),
    (
        include_str!("../../tests/fixtures/std_receiver_anchor/std_deque_usize_len.json"),
        "<alloc::collections::vec_deque::VecDeque<u32> as core::ops::index::IndexMut<usize>>::index_mut",
    ),
    (
        include_str!("../../tests/fixtures/std_receiver_anchor/std_string_ranges_len.json"),
        "<alloc::string::String as core::ops::index::IndexMut<core::ops::range::Range<usize>>>::index_mut",
    ),
];

const TRY_BRANCH_SPAN: &str =
    include_str!("../../tests/fixtures/std_receiver_anchor/try_branch_span.json");

fn parse_mir(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

fn callees(func: &VerifiableFunction) -> Vec<&str> {
    func.body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } => Some(func.as_str()),
            _ => None,
        })
        .collect()
}

/// Every `_len == coll_len(base)` tie the `.len()` arm mints, over all blocks.
fn len_ties(func: &VerifiableFunction) -> usize {
    crate::guards::slice_last_some_nonempty_definitions(func).values().map(Vec::len).sum()
}

// ── the predicate ────────────────────────────────────────────────────────────

#[test]
fn std_container_index_predicate_accepts_exactly_std_impls() {
    // Every spelling the extractor produced for std's impls (stage1-w11fix), plus
    // the `Index::index` twins and a `Vec` of a user element type (still std's
    // impl: `Vec<user::T>` is not local, so no downstream impl can exist).
    for genuine in [
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<usize>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::Range<usize>>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::RangeFrom<usize>>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::RangeTo<usize>>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::RangeFull>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::RangeInclusive<usize>>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::RangeToInclusive<usize>>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index",
        "<alloc::vec::Vec<u32> as core::ops::index::Index<core::ops::range::Range<usize>>>::index",
        "<alloc::vec::Vec<user::T> as core::ops::index::IndexMut<usize>>::index_mut",
        "<std::vec::Vec<u32> as core::ops::index::IndexMut<usize>>::index_mut",
        "<[u32; 4] as core::ops::index::IndexMut<core::ops::range::Range<usize>>>::index_mut",
        "<[u32] as core::ops::index::IndexMut<core::ops::range::Range<usize>>>::index_mut",
        "<[u32] as core::ops::index::IndexMut<usize>>::index_mut",
        "<alloc::string::String as core::ops::index::IndexMut<core::ops::range::Range<usize>>>::index_mut",
        "<alloc::string::String as core::ops::index::IndexMut<core::ops::range::RangeFrom<usize>>>::index_mut",
        "<alloc::string::String as core::ops::index::IndexMut<core::ops::range::RangeFull>>::index_mut",
        "<alloc::collections::vec_deque::VecDeque<u32> as core::ops::index::IndexMut<usize>>::index_mut",
        "<alloc::collections::vec_deque::VecDeque<u32> as core::ops::index::Index<usize>>::index",
    ] {
        assert!(is_std_container_index_call(genuine), "std's own impl: `{genuine}`");
    }
    for decoy in [
        // A user impl of std's trait on std's `Vec` (the measured live shapes).
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<gen_impl::K<()>>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<dep::K>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<&dep::K>>::index_mut",
        // A user key that merely ENDS or STARTS like std's.
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<x::K<usize>>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<core::ops::range::Range<x::K>>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<usize, x::K>>::index_mut",
        // A user self type (named `Vec` or not) implementing std's trait.
        "<uvh2::Vec as core::ops::index::IndexMut<usize>>::index_mut",
        "<user::W as core::ops::index::IndexMut<usize>>::index_mut",
        "<alloc::vec::VecEvil<u32> as core::ops::index::IndexMut<usize>>::index_mut",
        "<user::alloc::vec::Vec<u32> as core::ops::index::IndexMut<usize>>::index_mut",
        // A user trait, nested-module or same-named.
        "<alloc::vec::Vec<u32> as mycrate::core::ops::index::IndexMut<usize>>::index_mut",
        "<alloc::vec::Vec<u32> as x::IndexMut<usize>>::index_mut",
        // Trait and method that do not belong together, or an unknown method.
        "<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index_mut",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<usize>>::index",
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<usize>>::get_mut",
        // An argument std has no impl for on that self type.
        "<alloc::string::String as core::ops::index::IndexMut<usize>>::index_mut",
        "<alloc::collections::vec_deque::VecDeque<u32> as core::ops::index::IndexMut<core::ops::range::Range<usize>>>::index_mut",
        // Spellings that name no impl, or a user free fn.
        "core::ops::index::IndexMut::index_mut",
        "std::ops::IndexMut::index_mut",
        "mycrate::index_mut",
        // A trailing suffix after the method, and a stamped impersonator.
        "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<usize>>::index_mut::<u8>",
        "__trust_crate@1::<alloc::vec::Vec<u32> as core::ops::index::IndexMut<usize>>::index_mut",
    ] {
        assert!(!is_std_container_index_call(decoy), "not std's own impl: `{decoy}`");
    }
}

// ── the length-benign receiver on REAL MIR ───────────────────────────────────

#[test]
fn a_user_index_mut_impl_on_std_vec_may_resize_it() {
    for (mir, call) in [
        (
            USER_GENERIC_IMPL_LEN,
            "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<gen_impl::K<()>>>::index_mut",
        ),
        (
            USER_GENERIC_IMPL_IDX,
            "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<gen_impl::K<()>>>::index_mut",
        ),
        (
            USER_DEP_IMPL_LEN,
            "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<dep::K>>::index_mut",
        ),
        (
            USER_DEP_IMPL_IDX,
            "<alloc::vec::Vec<u32> as core::ops::index::IndexMut<dep::K>>::index_mut",
        ),
    ] {
        let func = parse_mir(mir);
        assert!(callees(&func).contains(&call), "{}: {:?}", func.def_path, callees(&func));
        // `v` is the parameter, local 1, and every `&mut v` feeds the user call.
        assert!(
            crate::guards::local_mut_borrows_may_resize(&func, 1),
            "{}: a user `index_mut` may truncate `v`, so `&mut v` is not length-benign",
            func.def_path
        );
    }
    // The consequence the compiler acted on: no `.len()` tie survives the call.
    for mir in [USER_GENERIC_IMPL_LEN, USER_DEP_IMPL_LEN] {
        let func = parse_mir(mir);
        assert_eq!(len_ties(&func), 0, "{}: {:?}", func.def_path, {
            crate::guards::slice_last_some_nonempty_definitions(&func)
        });
    }
}

#[test]
fn std_index_on_std_containers_keeps_the_receiver_length_benign() {
    for (mir, call) in STD_CONTROLS {
        let func = parse_mir(mir);
        assert!(callees(&func).contains(&call), "{}: {:?}", func.def_path, callees(&func));
        assert!(
            !crate::guards::local_mut_borrows_may_resize(&func, 1),
            "{}: std's `{call}` never resizes, so the tie must survive it",
            func.def_path
        );
        // Both `.len()` calls (the guard's and the `- 1`'s) tie to the base.
        assert_eq!(len_ties(&func), 2, "{}: {:?}", func.def_path, {
            crate::guards::slice_last_some_nonempty_definitions(&func)
        });
    }
}

// ── the `?` re-wrap on REAL MIR ──────────────────────────────────────────────

/// `tryb.rs`: `pub fn span(start: usize, len: usize) -> Option<usize> { let end =
/// start.checked_add(len)?; Some(end - start) }`. The `?` lowers to
/// `<core::option::Option<usize> as core::ops::try_trait::Try>::branch::<__trust_try_total>`
/// (keyed `SysrootItem::TryBranch`) and `_6 = (_3 as Continue).0`.
fn try_branch_payload_fact(func: &VerifiableFunction) -> Vec<Formula> {
    crate::guards::build_checked_arith_facts(func)
}

fn set_branch_key(func: &mut VerifiableFunction, key: Option<trust_types::CalleeKey>) {
    let mut hit = 0;
    for block in &mut func.body.blocks {
        if let Terminator::Call { func: callee, callee_key, .. } = &mut block.terminator
            && callee.contains("Try>::branch")
        {
            *callee_key = key.clone();
            hit += 1;
        }
    }
    assert_eq!(hit, 1, "the fixture has exactly one `Try::branch` call");
}

#[test]
fn the_try_branch_rewrap_is_the_keyed_sysroot_item() {
    let span = parse_mir(TRY_BRANCH_SPAN);
    let facts = try_branch_payload_fact(&span);
    let start = crate::operand_to_formula(&span, &Operand::Copy(Place::local(1)));
    let len = crate::operand_to_formula(&span, &Operand::Copy(Place::local(2)));
    let payload = crate::operand_to_formula(&span, &Operand::Copy(Place::local(6)));
    assert_eq!(
        facts,
        vec![Formula::Eq(
            Box::new(payload),
            Box::new(Formula::Add(Box::new(start), Box::new(len)))
        )],
        "the genuine `checked_add(..)?` keeps its payload fact"
    );

    // The SAME call with no key (an indirect or pre-carrier call) — its display
    // spelling is std's, which the string gate accepted — mints nothing.
    let mut keyless = span.clone();
    set_branch_key(&mut keyless, None);
    assert!(
        try_branch_payload_fact(&keyless).is_empty(),
        "a key-less re-wrap is not `Try::branch`"
    );

    // A key from a crate that is not the real sysroot carries no item (the
    // extractor mints none), and a real-sysroot key naming another item is not it.
    let mut forged = span.clone();
    set_branch_key(
        &mut forged,
        Some(trust_types::CalleeKey {
            sysroot_item: None,
            krate_is_real_sysroot: false,
            krate_name_is_ambiguous: true,
            stable_crate_id: 1,
            krate_name: "core".to_string(),
            foreign_block_leaf: None,
            upstream_foreign_link_symbol: None,
            diverging_entry: None,
        }),
    );
    assert!(try_branch_payload_fact(&forged).is_empty(), "a `--crate-name core` key is not std's");
    let mut other = span.clone();
    set_branch_key(
        &mut other,
        Some(trust_types::CalleeKey {
            sysroot_item: Some(trust_types::SysrootItem::OptionOkOr),
            krate_is_real_sysroot: true,
            krate_name_is_ambiguous: false,
            stable_crate_id: 4_703_791_156_326_232_143,
            krate_name: "core".to_string(),
            foreign_block_leaf: None,
            upstream_foreign_link_symbol: None,
            diverging_entry: None,
        }),
    );
    assert!(
        try_branch_payload_fact(&other).is_empty(),
        "another sysroot item is not `Try::branch`"
    );

    // The key decides, not the display spelling.
    let mut respelled = span.clone();
    for block in &mut respelled.body.blocks {
        if let Terminator::Call { func: callee, .. } = &mut block.terminator
            && callee.contains("Try>::branch")
        {
            *callee = "mycrate::branch".to_string();
        }
    }
    assert_eq!(try_branch_payload_fact(&respelled), facts);
}

// ── the owned-`Vec` consumers decline a user type named `Vec` ─────────────────
//
// OWNED-VEC-NAME-1 (2026-10-04) made `panic_calls::is_owned_slice_container_name`
// std's `Vec` by exact path (`alloc::vec::Vec`/`std::vec::Vec`) instead of the last
// path segment. These four consumers read it on a `Ty::Adt` name. None has a known
// exploit (each is a fail-honest visibility gate or sits behind a std `Vec::new`),
// so these pin the anchor AT each consumer: a regression to a tail test there is red
// here, not silent. Each pairs a user `uvh2::Vec` (declined) with std's `Vec` by
// path (admitted), so a test cannot pass by declining everything.

use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Rvalue, SourceSpan, Statement, Ty, UnwindEdge,
    VerifiableBody,
};

const STD_VEC_ADT: &str = "alloc::vec::Vec<u32>";
const USER_VEC_ADT: &str = "uvh2::Vec";

fn bare_fn(locals: Vec<Ty>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".to_string(),
        def_path: "test::f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: locals[0].clone(),
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks,
            arg_count: 0,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn returning(blocks_end: usize) -> Vec<BasicBlock> {
    vec![BasicBlock { id: BlockId(blocks_end), stmts: vec![], terminator: Terminator::Return }]
}

fn call(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        is_foreign: false,
    }
}

fn shared(inner: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(inner) }
}

#[test]
fn a_user_vec_receiver_is_not_an_owned_container_receiver() {
    let receiver = |inner: Ty| {
        let f = bare_fn(vec![Ty::Unit, shared(inner)], returning(0));
        super::panic_calls::operand_is_owned_container_receiver(&f, &Operand::Copy(Place::local(1)))
    };
    assert!(!receiver(Ty::adt(USER_VEC_ADT, vec![])), "a user `Vec` is not std's");
    assert!(receiver(Ty::adt(STD_VEC_ADT, vec![])), "std's `Vec` by path");
    assert!(
        receiver(Ty::Seq { drop_auth: None, elem: Box::new(Ty::u32()) }),
        "std's `Vec` as the extractor lowers it"
    );
}

#[test]
fn a_user_vec_local_is_not_peeled_to_a_vec() {
    let peeled = |inner: Ty| {
        let f = bare_fn(vec![Ty::Unit, shared(inner)], returning(0));
        super::container_len::local_peeled_is_vec(&f, 1)
    };
    assert!(!peeled(Ty::adt(USER_VEC_ADT, vec![])), "a user `Vec` is not std's");
    assert!(peeled(Ty::adt(STD_VEC_ADT, vec![])), "std's `Vec` by path");
}

#[test]
fn a_user_vec_payload_component_is_not_an_owned_vec() {
    // `fn f() -> Option<(V,)>`: the `len` witness lane reads component `[0]` of the
    // `Some` payload.
    let option_of_tuple = |vec_name: &str| -> Ty {
        let payload = format!(
            r#"{{"Tuple":[{{"Adt":{{"name":"{vec_name}","fields":[],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}}}]}}"#
        );
        serde_json::from_str(&format!(
            r#"{{"Adt":{{"name":"core::option::Option","fields":[],"variants":[{{"name":"None","discriminant":0,"fields":[]}},{{"name":"Some","discriminant":1,"fields":[["0",{payload}]]}}],"disc_index_safe":true,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Enum"}}}}"#
        ))
        .expect("the Option type deserializes")
    };
    let component = |vec_name: &str| {
        let f = bare_fn(vec![option_of_tuple(vec_name)], returning(0));
        super::witness_grounding::component_ty_is_owned_vec(&f, &[0])
    };
    assert!(!component(USER_VEC_ADT), "a user `Vec` is not std's");
    assert!(component(STD_VEC_ADT), "std's `Vec` by path");
}

#[test]
fn a_user_vec_leaf_is_not_push_disciplined() {
    // `let mut m = Vec::new(); m.push(7);` with `m` typed by the given name: every
    // other conjunct of the discipline holds, so the name decides.
    let leaf = |vec_name: &str| {
        let vec_ty = Ty::adt(vec_name, vec![]);
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: call("alloc::vec::Vec::<u32>::new", vec![], 1, 1),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                    span: SourceSpan::default(),
                }],
                terminator: call(
                    "alloc::vec::Vec::<u32>::push",
                    vec![
                        Operand::Move(Place::local(2)),
                        Operand::Constant(ConstValue::Uint(7, 32)),
                    ],
                    3,
                    2,
                ),
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ];
        let f = bare_fn(
            vec![
                Ty::Unit,
                vec_ty.clone(),
                Ty::Ref { mutable: true, inner: Box::new(vec_ty) },
                Ty::Unit,
            ],
            blocks,
        );
        super::witness_grounding::leaf_push_disciplined(&f, 1)
    };
    assert!(!leaf(USER_VEC_ADT), "a user `Vec` is not std's");
    assert!(leaf(STD_VEC_ADT), "std's `Vec` by path");
}
