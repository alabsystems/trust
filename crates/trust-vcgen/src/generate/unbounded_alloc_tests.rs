use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
    UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
};

/// Trust (ALLOC-WIDTH-1, 2026-10-08): every test here models the COMPILER on a
/// 64-bit host, which installs the target's pointer width as a session fact
/// (`VcgenContext::with_target_pointer_bits`). The 32-bit and no-width verdicts
/// are pinned in `alloc_width_receiver_tests`.
fn generate_vcs(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    crate::with_target_pointer_bits(Some(64), || crate::generate_vcs(func))
}

/// A function whose single block tail-calls `callee(n)`, with `n` an
/// unbounded `usize` parameter (local 1).
fn func_calling(callee: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "alloc_caller".to_string(),
        def_path: "test::alloc_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None }, // return
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("n".into()) }, // size param
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("v".into()) }, // call dest
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee.to_string(),
                    args: vec![Operand::Move(Place::local(1))],
                    dest: Place::local(2),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
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

fn unbounded_alloc_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnboundedAllocation { .. }))
        .count()
}

/// The allocation's VISIBLE obligation: its counted `UnboundedAllocation` row, or —
/// since `1b5061bbe0` (an element-count bound cannot establish the byte capacity of
/// an unknown layout) — the `element-size-not-derivable` Unknown that replaces that
/// row when the element stride is not exactly known. Either way the allocation is
/// charged; what may never happen is neither.
fn alloc_row_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| match &vc.kind {
            VcKind::UnboundedAllocation { .. } => true,
            VcKind::UnsupportedMir { kind, .. } => {
                kind.starts_with("UnboundedAllocation::")
                    && kind.ends_with("::element-size-not-derivable")
            }
            _ => false,
        })
        .count()
}

#[test]
fn flags_unguarded_with_capacity() {
    // `Vec::with_capacity(n)` with `n` an unbounded usize param is exactly
    // the unguarded bulk-allocation pattern that OOM-killed the host.
    let func = func_calling("std::vec::Vec::<u8>::with_capacity");
    assert_eq!(
        unbounded_alloc_count(&func),
        1,
        "unguarded bulk allocation sized by an unbounded param must be flagged"
    );
}

#[test]
fn ignores_ordinary_calls() {
    // An ordinary (non-allocating) call sized by the same param is not a
    // bulk-allocation hazard and must not produce the obligation.
    let func = func_calling("mycrate::helper::compute");
    assert_eq!(
        unbounded_alloc_count(&func),
        0,
        "non-allocation calls must not produce an UnboundedAllocation obligation"
    );
}

#[test]
fn method_tail_handles_trailing_turbofish() {
    // Middle turbofish (methods) already worked; the TRAILING turbofish on a
    // monomorphized free fn is the case that silently disabled the gate and
    // let the 2026-06-16 interpreter OOM ship.
    assert_eq!(super::method_tail("std::vec::Vec::<u8>::with_capacity"), "with_capacity");
    assert_eq!(super::method_tail("std::vec::from_elem::<Option<u8>>"), "from_elem");
    assert_eq!(
        super::method_tail("core::iter::Iterator::collect::<alloc::vec::Vec<u8>>"),
        "collect"
    );
    assert_eq!(super::method_tail("core::intrinsics::unchecked_add::<i32>"), "unchecked_add");
    assert_eq!(super::method_tail("mycrate::helper::compute"), "compute");
    // hunt-15 Class A: a free-fn sink rendered with the hunt-11 byte-size token has
    // TWO trailing turbofishes — stripping only one left `<u8>`, so the alloc gate
    // silently disabled and `vec![x; n]` emitted no obligation. Strip both.
    assert_eq!(
        super::method_tail("std::vec::from_elem::<u8>::<__trust_elem_bytes@1>"),
        "from_elem"
    );
    assert_eq!(
        super::method_tail(
            "core::iter::Iterator::collect::<alloc::vec::Vec<u8>>::<__trust_elem_bytes@8>"
        ),
        "collect"
    );
    // A method sink with the byte token keeps its type turbofish in the middle.
    assert_eq!(
        super::method_tail("std::vec::Vec::<u8>::with_capacity::<__trust_elem_bytes@4096>"),
        "with_capacity"
    );
}

#[test]
fn elem_bytes_token_rejects_user_spellable_lookalikes() {
    // PERMANENT batch-6 adversarial-review D1 probe for THE stride channel
    // feeding the OOM byte ceiling. `__trust_elem_bytes_1` is a LEGAL Rust
    // identifier: a user type or a generic fn's type param of that name
    // survives in the rendered path exactly when the extractor omits the real
    // token (still-generic element / layout error). Under the old loose
    // substring parse it read as stride 1 and shrank the capacity term.
    assert_eq!(
        super::parse_elem_bytes_token("alloc::vec::Vec::<__trust_elem_bytes_1>::with_capacity"),
        None
    );
    // The retired underscore spelling never parses, even in trailing position
    // (it is identifier-spellable, hence never an authority token).
    assert_eq!(
        super::parse_elem_bytes_token(
            "std::vec::Vec::<u8>::with_capacity::<__trust_elem_bytes_4096>"
        ),
        None
    );
    // The `@` authority token parses ONLY as the trailing turbofish group.
    assert_eq!(
        super::parse_elem_bytes_token(
            "std::vec::Vec::<u8>::with_capacity::<__trust_elem_bytes@4096>"
        ),
        Some(4096)
    );
    assert_eq!(
        super::parse_elem_bytes_token("std::vec::Vec::<__trust_elem_bytes@4096>::with_capacity"),
        None
    );
}

#[test]
fn range_family_identity_accepts_defining_and_reexport_paths_only() {
    const FAMILIES: [&str; 5] = ["Range", "RangeTo", "RangeFrom", "RangeInclusive", "RangeFull"];
    for prefix in ["core::ops::", "std::ops::", "core::ops::range::", "std::ops::range::"] {
        for family in FAMILIES {
            assert_eq!(
                super::range_family_adt_name(&format!("{prefix}{family}")),
                Some(family),
                "plain canonical path for {family}"
            );
            assert_eq!(
                super::range_family_adt_name(&format!("{prefix}{family}<usize>")),
                Some(family),
                "instantiated canonical path for {family}"
            );
        }
    }
    assert_eq!(super::range_family_adt_name("user::RangeTo"), None);
    assert_eq!(super::range_family_adt_name("user::core::ops::range::RangeTo<usize>"), None);
    assert_eq!(super::range_family_adt_name("core::ops::range::NotARange"), None);
    assert_eq!(super::range_family_adt_name("core::ops::range2::RangeTo<usize>"), None);
    assert_eq!(super::range_family_adt_name("core::ops::range::RangeToLookalike"), None);
    assert!(super::aggregate_is_exclusive_range("core::ops::range::Range<usize>"));
    assert!(!super::aggregate_is_exclusive_range("core::ops::range::RangeInclusive<usize>"));
}

#[test]
fn iterator_yield_name_gate_requires_exact_std_trait_namespace() {
    for callee in [
        "core::iter::traits::iterator::Iterator::next",
        "std::iter::Iterator::next",
        "<core::ops::range::Range<usize> as core::iter::Iterator>::next",
        "<core::ops::range::Range<usize> as core::iter::traits::iterator::Iterator>::next",
    ] {
        assert!(
            super::vc_callee_is_std_iter_trait_method(callee, "Iterator", "next"),
            "canonical std/core Iterator spelling must match: {callee}"
        );
    }

    for callee in [
        "my_crate::Iterator::next",
        "core::iteration::Iterator::next",
        "core::iterators::Iterator::next",
        "<core::ops::range::Range<usize> as Iterator>::next",
        "<core::ops::range::Range<usize> as my_crate::Iterator>::next",
        "<core::ops::range::Range<usize> as my_crate::core::iter::Iterator>::next",
    ] {
        assert!(
            !super::vc_callee_is_std_iter_trait_method(callee, "Iterator", "next"),
            "unanchored/user Iterator spelling must fail closed: {callee}"
        );
    }
}

#[test]
fn bounds_and_nonnull_fact_callees_require_canonical_owners() {
    for callee in [
        "alloc::vec::Vec::<u8>::push",
        "std::vec::Vec::<u8>::with_capacity",
        "<alloc::vec::Vec<u8>>::len",
    ] {
        assert!(super::vc_callee_is_std_vec_inherent(callee), "{callee}");
    }
    for callee in [
        "mycrate::alloc::vec::Vec::push",
        "<alloc::vec::Vec<u8> as mycrate::Trait>::push",
        "mycrate::push",
    ] {
        assert!(!super::vc_callee_is_std_vec_inherent(callee), "{callee}");
    }

    // SLICE-INHERENT-1 / ASPTR-KEY-1 (2026-10-04): both recognizers decide on the
    // compiler-minted key first; `std_key` is what the extractor mints for a core
    // callee (no modeled tag needed for `windows`).
    let std_key = trust_types::CalleeKey {
        sysroot_item: None,
        krate_is_real_sysroot: true,
        krate_name_is_ambiguous: false,
        stable_crate_id: 0x1234,
        krate_name: "core".into(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    };
    assert!(super::vc_callee_is_slice_inherent(
        "core::slice::<impl [u8]>::windows",
        Some(&std_key),
        "windows"
    ));
    assert!(!super::vc_callee_is_slice_inherent(
        "<[T] as mycrate::Trait>::windows",
        Some(&std_key),
        "windows"
    ));
    assert!(!super::vc_callee_is_slice_inherent(
        "core::slice::<impl [u8]>::windows",
        None,
        "windows"
    ));
    assert!(super::vc_callee_is_slice_inherent(
        "core::slice::<impl [T]>::iter",
        Some(&std_key),
        "iter"
    ));
    // A user inherent method on a type named over `[T]` is not the std one
    // (trip-count lane review, 2026-09-29) — not even under a sysroot key.
    assert!(!super::vc_callee_is_slice_inherent(
        "mycrate::Foo::<[T]>::iter",
        Some(&std_key),
        "iter"
    ));
    assert!(!super::vc_callee_is_slice_inherent(
        "mycrate::Foo::<[T]>::split",
        Some(&std_key),
        "split"
    ));

    assert!(super::is_slice_to_array_conversion("core::convert::TryInto::try_into"));
    assert!(super::is_slice_to_array_conversion(
        "<&[u8] as core::convert::TryInto<[u8; 8]>>::try_into"
    ));
    assert!(!super::is_slice_to_array_conversion("mycrate::core::convert::TryInto::try_into"));
    assert!(!super::is_slice_to_array_conversion(
        "<&[u8] as mycrate::convert::TryInto<[u8; 8]>>::try_into"
    ));

    let vec_as_ptr = trust_types::CalleeKey {
        sysroot_item: Some(trust_types::SysrootItem::VecAsPtr),
        krate_name: "alloc".into(),
        ..std_key.clone()
    };
    assert!(super::is_std_container_as_ptr(Some(&vec_as_ptr)));
    assert!(!super::is_std_container_as_ptr(Some(&std_key)));
    assert!(!super::is_std_container_as_ptr(None));
}

/// The exact shape of the interpreter OOM: `vec![None; size]` lowers to
/// `std::vec::from_elem::<Option<u8>>(elem, size)` with `size` an unbounded
/// `usize` param (size operand at index 1, after the element value). Before
/// the `method_tail` turbofish fix the trailing `::<Option<u8>>` defeated the
/// recognizer and NO obligation was emitted (the bug class shipped); now it
/// is flagged with the actionable UnboundedAllocation remedy.
#[test]
fn flags_unbounded_vec_macro_from_elem() {
    let func = VerifiableFunction {
        name: "alloc_region".to_string(),
        def_path: "trust_ir::interpret::alloc_region".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None }, // return (Vec, modeled opaque)
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("size".into()) }, // the param
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("elem".into()) }, // the `None`
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("v".into()) }, // call dest
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "std::vec::from_elem::<Option<u8>>".to_string(),
                    // from_elem(elem, n): the size operand is arg index 1.
                    args: vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(1))],
                    dest: Place::local(3),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(
                        "std::vec::from_elem::<Option<u8>>",
                    ),
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
    };
    assert_eq!(
        unbounded_alloc_count(&func),
        1,
        "`vec![None; size]` (from_elem with a trailing turbofish) sized by an \
         unbounded param must be flagged as UnboundedAllocation"
    );
}

/// `core::iter::repeat_n(x, n).collect()` with `n` an unbounded usize param —
/// a runtime-sized Vec that is NOT `vec![x; n]`. The count is exactly arg 1 of
/// repeat_n; collect's source recurses to it. Must be flagged.
#[test]
fn flags_unbounded_repeat_n_collect() {
    let func = VerifiableFunction {
        name: "repeat_n_caller".to_string(),
        def_path: "test::repeat_n_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None }, // return (opaque Vec)
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("n".into()) }, // count param
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("it".into()) }, // iterator
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("v".into()) }, // collect dest
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::iter::repeat_n::<u32>".to_string(),
                        args: vec![
                            Operand::Constant(ConstValue::Int(0)), // element x
                            Operand::Move(Place::local(1)),        // count n
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::iter::repeat_n::<u32>",
                        ),
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::iter::Iterator::collect".to_string(),
                        args: vec![Operand::Move(Place::local(2))],
                        dest: Place::local(3),
                        target: None,
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::iter::Iterator::collect",
                        ),
                        is_foreign: false,
                    },
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    assert_eq!(
        alloc_row_count(&func),
        1,
        "repeat_n(x, n).collect() with unbounded n must be flagged"
    );
}

#[test]
fn from_elem_multibyte_adds_byte_aware_term() {
    // vec![0u64; n] with symbolic n: from_elem's element is a real typed
    // operand, so the failure formula carries the BYTE-aware product
    // (elem_size 8 * n >= isize::MAX, the object limit where RawVec panics
    // "capacity overflow") beside the bare element ceiling — the one MIR
    // allocation whose element type survives (RawVec erases it elsewhere; the
    // trust-ir layer does this in general, alloc_bound.rs).
    let func = VerifiableFunction {
        name: "from_elem_u64".to_string(),
        def_path: "test::from_elem_u64".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("n".into()) }, // count
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("e".into()),
                }, // u64 element
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("v".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "std::vec::from_elem::<u64>".to_string(),
                    // from_elem(elem, n): element arg 0 (typed u64), count arg 1.
                    args: vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(1))],
                    dest: Place::local(3),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key("std::vec::from_elem::<u64>"),
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
    };
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|v| matches!(v.kind, VcKind::UnboundedAllocation { .. }))
        .expect("UnboundedAllocation VC");
    let smt = vc.formula.to_smtlib();
    assert!(
        smt.contains("(* "),
        "byte-aware product (elem_size * count) must appear for a multi-byte from_elem: {smt}"
    );
    // The byte line is the object limit, `isize::MAX`. There is no 256 MiB
    // availability budget: it was deleted with trust-ir's `ALLOC_BYTE_BUDGET`
    // (2026-09-29), so no product is compared with 2^28 bytes.
    assert!(
        smt.contains(&super::ALLOC_CAPACITY_OVERFLOW_BYTES.to_string()),
        "the byte product must be judged against the object limit isize::MAX: {smt}"
    );
    assert!(
        !smt.contains(") 268435456)"),
        "no byte product may be compared with the deleted 256 MiB budget: {smt}"
    );
}

/// A function whose single block tail-calls `callee(CONST)` with a literal
/// constant size — mirrors `Vec::with_capacity(1 << 28)` / `vec![x; 1 << 28]`.
fn func_calling_const_size(callee: &str, n: i128) -> VerifiableFunction {
    VerifiableFunction {
        name: "alloc_caller".to_string(),
        def_path: "test::alloc_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("v".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee.to_string(),
                    args: vec![Operand::Constant(ConstValue::Int(n))],
                    dest: Place::local(1),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
                    is_foreign: false,
                },
            }],
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

#[test]
fn flags_const_allocation_exactly_at_ceiling() {
    // Regression for the nn-dsl OOM: `enumerate_peephole_configs()` allocated
    // EXACTLY `1 << 28` elements. The old `<=` skip + strict `>` failure waved
    // the boundary value through; it must now fail closed.
    let func = func_calling_const_size("std::vec::Vec::<u8>::with_capacity", 1 << 28);
    assert_eq!(
        unbounded_alloc_count(&func),
        1,
        "an allocation of exactly the ceiling (1<<28) must be flagged, not waved through"
    );
}

/// W4 ITER-HOF landing round (2026-10-03): the `Box`/`Rc`/`Arc` uninitialized and
/// zeroed SLICE constructors allocate `len` elements in one request (count at argument
/// 0) and panic past `isize::MAX` bytes, exactly like `with_capacity(len)`. They are
/// charged at a direct call, and — through `callee_is_call_site_allocation_sink` — are
/// withheld as fn-item type arguments (`map(Box::<[u64]>::new_uninit_slice)`). Before
/// this, `bulk_alloc_call` did not name them and every spelling was charged nothing
/// (review probes r01/r02/v02/r06c/v05d panicked "capacity overflow" on `usize::MAX`).
#[test]
fn flags_unguarded_uninit_and_zeroed_slice_constructors() {
    for callee in [
        "alloc::boxed::Box::<[u64]>::new_uninit_slice",
        "alloc::boxed::Box::<[u64]>::new_zeroed_slice",
        "alloc::rc::Rc::<[u64]>::new_uninit_slice",
        "alloc::sync::Arc::<[u8]>::new_zeroed_slice",
        "alloc::boxed::Box::<[u64]>::new_uninit_slice::<__trust_elem_bytes@8>",
        "alloc::boxed::Box::<[u64], A>::new_uninit_slice_in",
        "alloc::sync::Arc::<[u64], A>::new_zeroed_slice_in",
    ] {
        assert_eq!(
            alloc_row_count(&func_calling(callee)),
            1,
            "`{callee}` sized by an unbounded param must be flagged like `with_capacity`"
        );
        assert!(
            super::callee_has_call_site_panic_family(callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
    // The fallible twins return the layout error instead of panicking.
    for callee in [
        "alloc::boxed::Box::<[u64]>::try_new_uninit_slice",
        "alloc::rc::Rc::<[u64]>::try_new_zeroed_slice",
    ] {
        assert_eq!(unbounded_alloc_count(&func_calling(callee)), 0, "`{callee}` is fallible");
    }
    // A constant count whose bytes stay below both ceilings is bounded.
    let small = func_calling_const_size(
        "alloc::boxed::Box::<[u64]>::new_uninit_slice::<__trust_elem_bytes@8>",
        8192,
    );
    assert_eq!(unbounded_alloc_count(&small), 0, "a small constant slice is bounded");
}

#[test]
fn allows_const_allocation_just_below_ceiling() {
    // One element below the ceiling stays bounded — the fix must not over-fire.
    let func = func_calling_const_size("std::vec::Vec::<u8>::with_capacity", (1 << 28) - 1);
    assert_eq!(
        unbounded_alloc_count(&func),
        0,
        "a constant allocation strictly below the ceiling is bounded and must not be flagged"
    );
}

use trust_types::{AggregateKind, Rvalue, Statement};

/// Builds `(0..end)[.map(_)].collect()` — the nn-dsl OOM shape. With
/// `mapped`, the Range feeds a length-preserving `map` adaptor before the
/// `collect`, exercising the adaptor-recursion path.
fn range_collect_func(end: i128, mapped: bool) -> VerifiableFunction {
    let range_stmt = Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "core::ops::range::Range".to_string(),
                variant: 0,
                active_field: None,
                args: None,
            },
            vec![Operand::Constant(ConstValue::Int(0)), Operand::Constant(ConstValue::Int(end))],
        ),
        span: SourceSpan::default(),
    };
    let collect_term = |iter_local: usize| Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: "core::iter::Iterator::collect".to_string(),
        args: vec![Operand::Move(Place::local(iter_local))],
        dest: Place::local(3),
        target: None,
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key("core::iter::Iterator::collect"),
        is_foreign: false,
    };
    let blocks = if mapped {
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![range_stmt],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "core::iter::Iterator::map".to_string(),
                    args: vec![
                        Operand::Move(Place::local(1)),
                        Operand::Constant(ConstValue::Int(0)), // closure (ignored)
                    ],
                    dest: Place::local(2),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key("core::iter::Iterator::map"),
                    is_foreign: false,
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: collect_term(2) },
        ]
    } else {
        vec![BasicBlock { id: BlockId(0), stmts: vec![range_stmt], terminator: collect_term(1) }]
    };
    VerifiableFunction {
        name: "collect_caller".to_string(),
        def_path: "test::collect_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("r".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("it".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("v".into()) },
            ],
            blocks,
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

#[test]
fn flags_collect_over_huge_const_range() {
    // The exact nn-dsl OOM idiom: `(0..1<<28).collect()` materializes 2^28
    // elements. `.collect()` carries no size operand, so the count is
    // reconstructed from the Range bounds.
    let func = range_collect_func(1 << 28, false);
    assert_eq!(
        alloc_row_count(&func),
        1,
        "collect over a const range of 2^28 must be flagged"
    );
}

#[test]
fn flags_collect_over_mapped_huge_range() {
    // `(0..1<<28).map(f).collect()` — the literal nn shape; count flows
    // through the length-preserving `map` adaptor.
    let func = range_collect_func(1 << 28, true);
    assert_eq!(
        alloc_row_count(&func),
        1,
        "collect over a mapped const range of 2^28 must be flagged through the adaptor"
    );
}

#[test]
fn allows_collect_over_small_range() {
    // A small bounded collect must not be flagged (no over-fire).
    let func = range_collect_func(1000, false);
    assert_eq!(
        unbounded_alloc_count(&func),
        0,
        "collect over a small const range is bounded and must not be flagged"
    );
}

/// Builds `let it = <producer>(coll); [it = it.cloned();] it.collect()` — a
/// collect whose source is an iterator over an already-materialized collection
/// (`coll` is a parameter). `producer` is the full callee path of the producer,
/// `iter_ty` the ADT NAME of the iterator value it returns.
///
/// `iter_ty` is not decoration: the bounded-source grant authenticates the callee
/// path AND the type of the value whose `next` will run, so a bundle that names
/// only one of the two cannot exercise the grant. Earlier revisions of this
/// builder gave every local `Ty::u32()` — a shape the extractor never produces
/// for an iterator — which is why the tests below could not see the
/// user-ADT-in-the-chain hole. The spellings the tests pass are the extractor's
/// own, taken from real `-Ztrust-dump=mir` bundles (see
/// `trusted_root_spoof_iter_producer_tests` and
/// `authenticated_std_iter_chain_tests`).
///
/// The sink carries the extractor's destination-size token for a 4-byte element:
/// since D12 option (a) (2026-10-06) the grant also needs the destination's bytes
/// per item, and a sink without the token keeps its charge.
fn collection_collect_func(producer: &str, iter_ty: &str, cloned: bool) -> VerifiableFunction {
    let collect_term = |iter_local: usize| Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: "core::iter::Iterator::collect::<alloc::vec::Vec<u32>>::<__trust_elem_bytes@4>"
            .to_string(),
        args: vec![Operand::Move(Place::local(iter_local))],
        dest: Place::local(5),
        target: None,
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key("core::iter::Iterator::collect"),
        is_foreign: false,
    };
    let produce = |target: Option<BlockId>| Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: producer.to_string(),
        args: vec![Operand::Move(Place::local(1))], // the collection receiver (a param)
        dest: Place::local(2),
        target,
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(&producer.to_string()),
        is_foreign: false,
    };
    let blocks = if cloned {
        vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: produce(Some(BlockId(1))) },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "core::iter::Iterator::cloned".to_string(),
                    args: vec![Operand::Move(Place::local(2))],
                    dest: Place::local(3),
                    target: Some(BlockId(2)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(
                        "core::iter::Iterator::cloned",
                    ),
                    is_foreign: false,
                },
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: collect_term(3) },
        ]
    } else {
        vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: produce(Some(BlockId(1))) },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: collect_term(2) },
        ]
    };
    VerifiableFunction {
        name: "collection_collect_caller".to_string(),
        def_path: "test::collection_collect_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                // The RECEIVER collection, typed as the compiler would render it
                // for `producer` rather than as the historical `Ty::u32()`
                // placeholder — see [`super::bounded_source_value_tests::faithful_receiver_ty`].
                LocalDecl {
                    index: 1,
                    ty: super::bounded_source_value_tests::faithful_receiver_ty(producer),
                    name: Some("coll".into()),
                },
                LocalDecl { index: 2, ty: Ty::adt(iter_ty, vec![]), name: Some("it".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::adt(format!("core::iter::adapters::cloned::Cloned<{iter_ty}>"), vec![]),
                    name: Some("it2".into()),
                },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
                LocalDecl { index: 5, ty: Ty::u32(), name: Some("out".into()) },
            ],
            blocks,
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

#[test]
fn allows_collect_over_vec_iter() {
    // Collecting from an already-materialized std Vec is bounded by the
    // source's own (already-gated) allocation — must not be flagged.
    let func = collection_collect_func(
        "alloc::vec::Vec::<u32>::iter",
        "core::slice::iter::Iter<'_, u32>",
        false,
    );
    assert_eq!(unbounded_alloc_count(&func), 0, "collect over Vec::iter must not be flagged");
    assert_eq!(unsupported_mir_count(&func), 0, "...nor reported as count-not-derivable Unknown");
}

#[test]
fn allows_collect_over_hashmap_keys_cloned() {
    // Mirrors ny-cert `check_farkas`: `coeffs.keys().cloned().collect()`.
    let func = collection_collect_func(
        "std::collections::hash_map::HashMap::<u32, u32>::keys",
        "std::collections::hash::map::Keys<'_, K, V>",
        true,
    );
    assert_eq!(
        unbounded_alloc_count(&func),
        0,
        "collect over HashMap::keys().cloned() must not be flagged"
    );
    assert_eq!(unsupported_mir_count(&func), 0, "...nor reported count-not-derivable Unknown");
}

#[test]
fn flags_collect_over_custom_nonstd_iter() {
    // SOUNDNESS scoping: a custom (non-std) iterator producer is NOT a known
    // bounded collection source, so the collect stays GATED (visible Unknown),
    // never silently skipped — the std-path match must be precise.
    let func = collection_collect_func("mycrate::Weird::iter", "mycrate::Weird::Iter<'_>", false);
    assert_eq!(
        unsupported_mir_count(&func),
        1,
        "a custom non-std iter source must stay gated (count-not-derivable), not be skipped"
    );
}

/// FALSIFY-ONCE for the VALUE-side half of the bounded-source identity, on the
/// same bundle the positive test uses.
///
/// The producer path is the genuine, authenticated `alloc::vec::Vec::<u32>::iter`
/// and the sink is a genuine std spelling — the ONLY thing planted is that the
/// iterator local's own type is a USER ADT, i.e. a step that satisfies the
/// callee-side authenticator while breaking the closure property it assumes.
/// `authenticated_std_iter_chain_tests::the_walks_closure_property_is_enforced_not_assumed`
/// states exactly how far that claim goes: the property holds of today's arm set,
/// and the value check is what makes it CHECKED rather than re-derived by every
/// reader.
#[test]
fn a_user_adt_iterator_value_under_an_authenticated_producer_stays_gated() {
    let sound = collection_collect_func(
        "alloc::vec::Vec::<u32>::iter",
        "core::slice::iter::Iter<'_, u32>",
        false,
    );
    assert_eq!(
        unsupported_mir_count(&sound),
        0,
        "planted violation is gone: the authenticated control no longer takes the \
         bounded-source skip, so the planted case below proves nothing"
    );

    let planted =
        collection_collect_func("alloc::vec::Vec::<u32>::iter", "mycrate::Endless", false);
    assert_eq!(
        unsupported_mir_count(&planted),
        1,
        "a USER ADT iterator value must keep the obligation even when the producer \
         path authenticates"
    );
}

/// FALSIFY-ONCE for the CALLEE-side half at the adaptor step — the measured
/// 2026-08-16 exploit, in the builder the positive tests share.
///
/// Both bundles have a genuine `core::slice`-rooted leaf producer and a genuine
/// std iterator VALUE type; the only difference is whether the adaptor hop is
/// std's `Iterator::cloned` or a user inherent function whose last path segment
/// happens to be `cloned`. `mycrate::Adapt::cloned` returning an endless iterator
/// is the whole exploit: no impersonation, no `--crate-name` trick.
#[test]
fn a_user_inherent_fn_named_like_an_adaptor_stays_gated() {
    let sound = collection_collect_func_with_adaptor(
        "core::iter::Iterator::cloned",
        "core::iter::adapters::cloned::Cloned<core::slice::iter::Iter<'_, u32>>",
    );
    assert_eq!(
        unsupported_mir_count(&sound),
        0,
        "planted violation is gone: the genuine std adaptor no longer takes the skip, \
         so the planted case below proves nothing"
    );

    // The user adaptor's RESULT type is a std-rooted lie only the callee test can
    // catch: give it the very type std's `cloned` would have produced.
    let planted = collection_collect_func_with_adaptor(
        "mycrate::Adapt::cloned",
        "core::iter::adapters::cloned::Cloned<core::slice::iter::Iter<'_, u32>>",
    );
    assert_eq!(
        unsupported_mir_count(&planted),
        1,
        "a user inherent fn whose last path segment is an adaptor name must not step \
         the bounded-source walk through to its argument"
    );
}

/// `Vec::iter()` fed through `adaptor_callee` (whose result local is typed
/// `adaptor_ty`) into a `collect`. Same shape as [`collection_collect_func`]'s
/// `cloned` arm with the adaptor's callee and result type under test.
fn collection_collect_func_with_adaptor(
    adaptor_callee: &str,
    adaptor_ty: &str,
) -> VerifiableFunction {
    let mut func = collection_collect_func(
        "alloc::vec::Vec::<u32>::iter",
        "core::slice::iter::Iter<'_, u32>",
        true,
    );
    for block in &mut func.body.blocks {
        if let Terminator::Call { func: callee, .. } = &mut block.terminator
            && super::callee_tail(callee) == "cloned"
        {
            *callee = adaptor_callee.to_string();
        }
    }
    for decl in &mut func.body.locals {
        if decl.index == 3 {
            decl.ty = Ty::adt(adaptor_ty, vec![]);
        }
    }
    func
}

/// Builds `a.keys().chain(b.keys()).cloned().collect()` (params `a`, `b`).
/// `keys_ty` is the ADT name of the iterator `keys_path` returns — see
/// [`collection_collect_func`] for why the bundle must carry it.
fn chained_keys_collect_func(keys_path: &str, keys_ty: &str) -> VerifiableFunction {
    let keys = |coll: usize, dest: usize, target: BlockId| Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: keys_path.to_string(),
        args: vec![Operand::Move(Place::local(coll))],
        dest: Place::local(dest),
        target: Some(target),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(&keys_path.to_string()),
        is_foreign: false,
    };
    let blocks = vec![
        BasicBlock { id: BlockId(0), stmts: vec![], terminator: keys(1, 3, BlockId(1)) },
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: keys(2, 4, BlockId(2)) },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                func: "core::iter::Iterator::chain".to_string(),
                args: vec![Operand::Move(Place::local(3)), Operand::Move(Place::local(4))],
                dest: Place::local(5),
                target: Some(BlockId(3)),
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: crate::sep_engine::tests::fixture_key("core::iter::Iterator::chain"),
                is_foreign: false,
            },
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                func: "core::iter::Iterator::cloned".to_string(),
                args: vec![Operand::Move(Place::local(5))],
                dest: Place::local(6),
                target: Some(BlockId(4)),
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: crate::sep_engine::tests::fixture_key("core::iter::Iterator::cloned"),
                is_foreign: false,
            },
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                func:
                    "core::iter::Iterator::collect::<alloc::vec::Vec<u32>>::<__trust_elem_bytes@4>"
                        .to_string(),
                args: vec![Operand::Move(Place::local(6))],
                dest: Place::local(7),
                target: None,
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: crate::sep_engine::tests::fixture_key("core::iter::Iterator::collect"),
                is_foreign: false,
            },
        },
    ];
    VerifiableFunction {
        name: "chained_keys_collect_caller".to_string(),
        def_path: "test::chained_keys_collect_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: (0..=7)
                .map(|i| {
                    // 3, 4: the two `keys()` iterators; 5: their `chain`; 6: `cloned`.
                    let chained =
                        format!("core::iter::adapters::chain::Chain<{keys_ty}, {keys_ty}>");
                    let ty = match i {
                        // 1, 2: the two RECEIVER collections, typed as the
                        // compiler renders them (was `Ty::u32()`).
                        1 | 2 => super::bounded_source_value_tests::faithful_receiver_ty(keys_path),
                        3 | 4 => Ty::adt(keys_ty, vec![]),
                        5 => Ty::adt(chained.clone(), vec![]),
                        6 => Ty::adt(
                            format!("core::iter::adapters::cloned::Cloned<{chained}>"),
                            vec![],
                        ),
                        _ => Ty::u32(),
                    };
                    LocalDecl { index: i, ty, name: None }
                })
                .collect(),
            blocks,
            arg_count: 2,
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

#[test]
fn allows_collect_over_chained_keys() {
    // Mirrors ny-cert `check_entailment`:
    // `a.keys().chain(b.keys()).cloned().collect()` — a chain of two
    // materialized-collection iterators is bounded (sum of two already-gated
    // allocations), so it must not be flagged.
    // `u32` keys: a table holds at most `MAX_LIVE / 5` of them, so the two sides
    // together stay inside a 4-byte destination's reservation (D12 option (a)).
    let func = chained_keys_collect_func(
        "std::collections::hash_map::HashMap::<u32, u32>::keys",
        "std::collections::hash::map::Keys<'_, K, V>",
    );
    assert_eq!(
        unbounded_alloc_count(&func),
        0,
        "collect over a.keys().chain(b.keys()).cloned() must not be flagged"
    );
    assert_eq!(unsupported_mir_count(&func), 0, "...nor reported count-not-derivable Unknown");
}

/// FALSIFY-ONCE for the `chain` arm, which had its own crate-free `tail == "chain"`
/// test. Both sides of the chain are genuine authenticated `keys()` producers with
/// genuine std iterator types; only the `chain` callee is a user inherent fn whose
/// last segment is `chain`. A user `chain` may yield anything at all, so the sum of
/// its arguments' lengths is not a bound on its own output.
#[test]
fn a_user_inherent_fn_named_chain_stays_gated() {
    let keys = "std::collections::hash_map::HashMap::<K, V>::keys";
    let keys_ty = "std::collections::hash::map::Keys<'_, K, V>";
    let mut planted = chained_keys_collect_func(keys, keys_ty);
    let mut replaced = 0;
    for block in &mut planted.body.blocks {
        if let Terminator::Call { func: callee, .. } = &mut block.terminator
            && super::callee_tail(callee) == "chain"
        {
            *callee = "mycrate::Adapt::chain".to_string();
            replaced += 1;
        }
    }
    assert_eq!(replaced, 1, "the builder must contain exactly one `chain` call to plant on");
    assert_eq!(
        unsupported_mir_count(&planted),
        1,
        "a user inherent fn named `chain` must not license the sum-of-lengths bound"
    );
}

fn unsupported_mir_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func).iter().filter(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { .. })).count()
}

/// A recognized bulk-alloc call (`with_capacity`) whose size operand was
/// dissolved by optimization — `args` is empty, so `args.get(0) == None`.
/// This is the "recognized but unrecoverable" path: it must now yield a
/// VISIBLE UnsupportedMir obligation, not be silently dropped.
fn func_calling_no_args(callee: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "alloc_caller".to_string(),
        def_path: "test::alloc_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("v".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee.to_string(),
                    args: vec![], // size operand absent — not derivable from MIR
                    dest: Place::local(1),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
                    is_foreign: false,
                },
            }],
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

#[test]
fn recognized_bulk_alloc_with_unrecoverable_count_yields_unsupported() {
    // Blocker A, Step 1: a recognized bulk-alloc sink whose element count
    // is NOT derivable from optimized MIR must surface a VISIBLE
    // UnsupportedMir obligation (preclassified to Unknown, never PROVEd),
    // not a silent `continue` that drops the allocation. Exactly one.
    let func = func_calling_no_args("std::vec::Vec::<u8>::with_capacity");
    assert_eq!(
        unsupported_mir_count(&func),
        1,
        "a recognized-but-unrecoverable bulk allocation must yield exactly one \
         UnsupportedMir obligation (visible Unknown), not be silently skipped"
    );
    // ... and crucially NOT a (potentially false-PROVEd) UnboundedAllocation
    // or nothing at all.
    assert_eq!(
        unbounded_alloc_count(&func),
        0,
        "no UnboundedAllocation VC when the count is unrecoverable — it is \
         reported Unknown via UnsupportedMir instead"
    );
}

/// A function whose single block calls `callee(value)` where `value` (local 1)
/// has type `value_ty` — the `Box::new`/`Rc::new`/`Arc::new` single-value alloc
/// shape: the lone argument IS the heap value, so its byte size is `size_of::<T>()`.
fn func_calling_single_value(callee: &str, value_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "alloc_caller".to_string(),
        def_path: "test::alloc_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None }, // return (opaque box)
                LocalDecl { index: 1, ty: value_ty, name: Some("v".into()) }, // the value
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) }, // box dest
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee.to_string(),
                    args: vec![Operand::Move(Place::local(1))],
                    dest: Place::local(2),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
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

#[test]
fn a_single_value_within_the_object_limit_is_not_flagged() {
    // `Box::new([0u8; 1 << 40])` heap-allocates one ~1 TiB value. That is
    // within the largest object a 64-bit target can hold (`isize::MAX` bytes),
    // the one line an allocation is judged against since the 256 MiB budget
    // was deleted with trust-ir's `ALLOC_BYTE_BUDGET` (the owner,
    // 2026-09-29: "the lint reports only allocations whose size is not
    // provably bounded"; docs/OWNER_RULINGS.md OW-29; trust-ir no longer reports a
    // 512 MiB or 64 GiB constant). Its size is a constant of its type, so it is bounded.
    let huge = Ty::Array { elem: Box::new(Ty::u8()), len: 1u64 << 40 };
    let func = func_calling_single_value("alloc::boxed::Box::<[u8; 1099511627776]>::new", huge);
    assert_eq!(
        unbounded_alloc_count(&func),
        0,
        "a single-value Box::new whose size is within isize::MAX is bounded by its type"
    );
}

#[test]
fn a_single_value_within_the_object_limit_is_not_flagged_through_rc_or_arc() {
    // The same value through `Rc::new` / `Arc::new`.
    let huge = || Ty::Array { elem: Box::new(Ty::u8()), len: 1u64 << 40 };
    let rc = func_calling_single_value("alloc::rc::Rc::<[u8; 1099511627776]>::new", huge());
    let arc = func_calling_single_value("alloc::sync::Arc::<[u8; 1099511627776]>::new", huge());
    assert_eq!(
        unbounded_alloc_count(&rc),
        0,
        "Rc::new of a 1 TiB value is within the object limit"
    );
    assert_eq!(
        unbounded_alloc_count(&arc),
        0,
        "Arc::new of a 1 TiB value is within the object limit"
    );
}

#[test]
fn a_single_value_at_the_object_limit_is_flagged() {
    // The line itself: a single value of MORE than `isize::MAX` bytes can never
    // be allocated (`Layout` refuses it), so it is reported. `[u8; 2^63]` is
    // exactly the first size past `isize::MAX` on a 64-bit target. A DEFENSE
    // check: rustc refuses such a type outright (`obj_size_bound` is `2^61` on
    // 64 bits), so for a type the compiler accepted this arm never fires; the
    // inclusive boundary is pinned in `alloc_width_receiver_tests`.
    let at_limit = Ty::Array { elem: Box::new(Ty::u8()), len: 1u64 << 63 };
    let func =
        func_calling_single_value("alloc::boxed::Box::<[u8; 9223372036854775808]>::new", at_limit);
    assert_eq!(
        unbounded_alloc_count(&func),
        1,
        "a single value past isize::MAX bytes exceeds the largest object and must be flagged"
    );
}

#[test]
fn allows_ordinary_box_new() {
    // A small `Box::new(x)` is the ubiquitous boxing pattern — it must NOT be
    // flagged (drop-in Rust preserved). A `u64` value is 8 bytes, far below any
    // ceiling.
    let func = func_calling_single_value("alloc::boxed::Box::<u64>::new", Ty::u64());
    assert_eq!(unbounded_alloc_count(&func), 0, "an ordinary small Box::new must not be flagged");
    // And a `Box::new` of another small primitive (4 bytes) is likewise not
    // flagged — only a value past the object limit (`isize::MAX` bytes) is.
    let small = func_calling_single_value("alloc::boxed::Box::<u32>::new", Ty::u32());
    assert_eq!(unbounded_alloc_count(&small), 0, "a Box::new of a small value must not be flagged");
}

#[test]
fn raw_alloc_yields_unsupported_not_proved() {
    // `alloc::alloc(layout)`: the size is inside an opaque `Layout`, not
    // derivable from MIR — it must surface a VISIBLE UnsupportedMir (Unknown),
    // never a (false) PROVE and never a silent skip.
    let func = func_calling("alloc::alloc::alloc");
    assert_eq!(
        unsupported_mir_count(&func),
        1,
        "a raw alloc::alloc(layout) must yield a visible UnsupportedMir (Unknown)"
    );
    assert_eq!(
        unbounded_alloc_count(&func),
        0,
        "a raw alloc::alloc must not produce a (count-meaningless) UnboundedAllocation VC"
    );
}

#[test]
fn allocator_allocate_yields_unsupported() {
    // The `Allocator::allocate(layout)` trait method has the same opaque-size
    // shape and must likewise be made visible (Unknown), not waved through.
    let func = func_calling("core::alloc::Allocator::allocate");
    assert_eq!(
        unsupported_mir_count(&func),
        1,
        "Allocator::allocate(layout) must yield a visible UnsupportedMir (Unknown)"
    );
}

#[test]
fn ordinary_new_is_not_a_single_value_alloc() {
    // A user `Foo::new(n)` (or any non-Box/Rc/Arc `::new`) must NOT be treated
    // as a heap single-value allocation — drop-in Rust preserved.
    assert_eq!(super::single_value_alloc_call("mycrate::widget::Widget::new"), None);
    assert_eq!(super::single_value_alloc_call("alloc::boxed::Box::<u8>::new"), Some("Box::new"));
    assert_eq!(super::single_value_alloc_call("alloc::rc::Rc::<u8>::new"), Some("Rc::new"));
    assert_eq!(super::single_value_alloc_call("alloc::sync::Arc::<u8>::new"), Some("Arc::new"));
    // The pinning forms route to the same allocation.
    assert_eq!(super::single_value_alloc_call("alloc::boxed::Box::<u8>::pin"), Some("Box::new"));
}

/// SMT of the (single) `UnboundedAllocation` VC `func` emits.
fn unbounded_alloc_smt(func: &VerifiableFunction) -> String {
    let raw = generate_vcs(func)
        .into_iter()
        .find(|vc| matches!(&vc.kind, VcKind::UnboundedAllocation { .. }))
        .map(|vc| vc.formula.to_smtlib())
        .expect("expected exactly one UnboundedAllocation VC");
    // The version flip renames reassigned place vars `n` -> `n#token`; strip the
    // tokens so these structural assertions test the SEMANTIC content (which the
    // consistent renaming preserves), not the encoding.
    strip_version_tokens(&raw)
}

/// The RAW (unstripped) SMT of the UnboundedAllocation VC — keeps `#token`
/// version suffixes so a test can assert NAME-DISJOINTNESS (a stale guard's
/// variable carries a DIFFERENT token than the reassignment, so it cannot
/// false-PROVE), which is what the S2c exemption provides in place of dropping.
fn unbounded_alloc_smt_raw(func: &VerifiableFunction) -> String {
    generate_vcs(func)
        .into_iter()
        .find(|vc| matches!(&vc.kind, VcKind::UnboundedAllocation { .. }))
        .map(|vc| vc.formula.to_smtlib())
        .expect("expected exactly one UnboundedAllocation VC")
}

/// The SMT variable token in `(<op> VAR <lit>)` — e.g. `n` from `(<= n 100)` or
/// `|n#s2_0|` from `(= |n#s2_0| 1000000000)`. `None` if absent.
fn var_in_relation(smt: &str, op: &str, lit: &str) -> Option<String> {
    let needle = format!("({op} ");
    let mut start = 0usize;
    while let Some(rel) = smt[start..].find(&needle) {
        let i = start + rel + needle.len();
        if let Some(sp) = smt[i..].find(' ') {
            let var = &smt[i..i + sp];
            let rest = &smt[i + sp + 1..];
            if rest.starts_with(lit) && rest[lit.len()..].starts_with(')') && !var.contains('(') {
                return Some(var.to_string());
            }
        }
        start = i;
    }
    None
}

/// Remove `#<token>` version suffixes from an SMT string (`n#s0_2` -> `n`), so a
/// structural assertion is robust to the version flip.
fn strip_version_tokens(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '#' => {
                while chars.peek().is_some_and(|n| n.is_ascii_alphanumeric() || *n == '_') {
                    chars.next();
                }
            }
            '|' => {} // drop SMT-LIB identifier quoting induced by the `#` token
            _ => out.push(c),
        }
    }
    out
}

/// `if n <= 100 { [n = 1_000_000_000;] Vec::<u8>::with_capacity(n) }`.
/// `reassign` adds the grow-after-guard write; `cross_block` puts that write
/// in a block BETWEEN the guard and the allocation (so the guard kill must
/// propagate to the successor's threaded guards, not just the local block).
fn grow_after_guard(reassign: bool, cross_block: bool) -> VerifiableFunction {
    use trust_types::{BinOp, Rvalue, Statement};
    let with_capacity = |target: BlockId| Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: "std::vec::Vec::<u8>::with_capacity".to_string(),
        args: vec![Operand::Move(Place::local(1))],
        dest: Place::local(3),
        target: Some(target),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key("std::vec::Vec::<u8>::with_capacity"),
        is_foreign: false,
    };
    let reassign_stmt = || Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1_000_000_000, 64))),
        span: SourceSpan::default(),
    };
    // bb0: c = (n <= 100); switch(c) { 0 => bb1 (else, return), _ => bb2 (true) }
    let mut blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Le,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(100, 64)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::SwitchInt {
                exhaustive_enum_unreachable: false,
                discr: Operand::Move(Place::local(2)),
                targets: vec![(0, BlockId(1))],
                otherwise: BlockId(2),
                span: SourceSpan::default(),
            },
        },
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
    ];
    if reassign && cross_block {
        // bb2: n = BIG; goto bb3    bb3: v = with_capacity(n)
        blocks.push(BasicBlock {
            id: BlockId(2),
            stmts: vec![reassign_stmt()],
            terminator: Terminator::Goto(BlockId(3)),
        });
        blocks.push(BasicBlock {
            id: BlockId(3),
            stmts: vec![],
            terminator: with_capacity(BlockId(1)),
        });
    } else {
        // bb2: [n = BIG;] v = with_capacity(n)
        blocks.push(BasicBlock {
            id: BlockId(2),
            stmts: if reassign { vec![reassign_stmt()] } else { vec![] },
            terminator: with_capacity(BlockId(1)),
        });
    }
    VerifiableFunction {
        name: "grow_after_guard".to_string(),
        def_path: "test::grow_after_guard".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("c".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("v".into()) },
            ],
            blocks,
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

// SOUNDNESS regression (hunt-8 class, path guards): a dominating `if n <= 100`
// whose TRUE branch reassigns `n` to 1e9 before `Vec::with_capacity(n)`. The
// stale guard `n <= 100` must NOT be conjoined — else `(<= n 100) ∧ (= n 1e9)`
// is UNSAT and the ~1 GiB allocation is vacuously PROVED safe (a false-PROVE).
// (Default-mechanism encoding test: it inspects exact SMT var names, which the
//  S2c flip renames to `n#token`. Verdict-equivalence under the flip is proven
//  by `flip_matches_kill_stmt`; gated off the flip build accordingly.)
#[test]
fn stale_guard_dropped_when_count_reassigned() {
    // S2c: the stale guard is no longer DROPPED — it is conjoined EXEMPT from the
    // rename, so its `n` stays bare (entry) while the reassignment/violation carry
    // the reassigned token `n#s2_0`. Soundness = NAME-DISJOINTNESS: the guard's
    // `n` must differ from the reassignment's `n`, so `(<= n 100) ∧ (= n#s2_0 1e9)`
    // is SAT (the ~1 GiB OOM fails closed), not the UNSAT false-PROVE.
    let raw = unbounded_alloc_smt_raw(&grow_after_guard(true, false));
    let guard_n = var_in_relation(&raw, "<=", "100")
        .expect("the dominating guard `n <= 100` must be present (exempt), got: {raw}");
    let reassign_n = var_in_relation(&raw, "=", "1000000000")
        .expect("the reassignment `n = 1e9` must be present");
    assert_ne!(
        guard_n, reassign_n,
        "stale guard's `n` must be version-DISJOINT from the reassigned `n` (else \
         false-PROVE); guard={guard_n} reassign={reassign_n}; raw: {raw}"
    );
    let viol_n =
        var_in_relation(&raw, ">=", "268435456").expect("the OOM violation atom must survive");
    assert_eq!(
        viol_n, reassign_n,
        "the violation must be over the LIVE reassigned `n` so the OOM fails closed"
    );
}

// Cross-block variant: the reassignment sits in a block BETWEEN the guard and
// the allocation, exercising the threaded `succ_guards` path.
#[test]
fn stale_guard_dropped_across_blocks() {
    let raw = unbounded_alloc_smt_raw(&grow_after_guard(true, true));
    let viol_n =
        var_in_relation(&raw, ">=", "268435456").expect("the OOM violation atom must survive");
    // If a `(<= _ 100)` guard is present at all, its `n` must be version-disjoint
    // from the violation's reassigned `n` (sound by name-disjointness).
    if let Some(guard_n) = var_in_relation(&raw, "<=", "100") {
        assert_ne!(
            guard_n, viol_n,
            "cross-block stale guard's `n` must be version-disjoint from the \
             reassigned violation `n`; guard={guard_n} viol={viol_n}; raw: {raw}"
        );
    }
}

// Mirror (no false-FAIL): the SAME dominating `if n <= 100` with NO
// reassignment must RETAIN the guard — it is what proves the allocation
// bounded (n <= 100 < ceiling). The reassignment-kill must not over-fire.
#[test]
fn legit_guard_retained_without_reassignment() {
    let smt = unbounded_alloc_smt(&grow_after_guard(false, false));
    assert!(
        smt.contains("(<= n 100)"),
        "a legitimate dominating guard (no reassignment) must be retained, got: {smt}"
    );
}

// SOUNDNESS regression (staleness class, deref-store channel — the OOM lane).
// `if n <= 100 { p = &mut n; p = &mut n; *p = 1e9; Vec::with_capacity(n) }`.
// RESEATING `p` makes `*p = 1e9` name the opaque `p*` instead of `n`, so the
// statement-redef kill misses it and the dominating guard `n <= 100` survived
// onto the alloc VC — false-PROVING a ~1 GiB allocation safe through the
// deref-store channel (the same OOM class as the direct-reassignment fix, via
// a pointer). `deref_store_havoc_names` must kill the guard so it fails closed.
#[test]
fn reseated_deref_store_drops_alloc_guard() {
    use trust_types::{BinOp, Projection, Rvalue, Statement};
    let func = VerifiableFunction {
        name: "alloc_deref_grow".to_string(),
        def_path: "test::alloc_deref_grow".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("c".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::usize()) },
                    name: Some("p".into()),
                },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("v".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(100, 64)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        exhaustive_enum_unreachable: false,
                        discr: Operand::Move(Place::local(2)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                            span: SourceSpan::default(),
                        },
                        // reseat -> crate::local_defs::unique_value_def(p) = None
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place { local: 3, projections: vec![Projection::Deref] },
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(
                                1_000_000_000,
                                64,
                            ))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "std::vec::Vec::<u8>::with_capacity".to_string(),
                        args: vec![Operand::Move(Place::local(1))],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "std::vec::Vec::<u8>::with_capacity",
                        ),
                        is_foreign: false,
                    },
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    // S2c: the guard is conjoined EXEMPT, so its `n` stays bare (entry) while the
    // reseated deref-store HAVOCS the alloc count to `n#s2_2`. Soundness =
    // name-disjointness: the guard's `n` must differ from the havoced violation
    // `n`, so the guard cannot bound the post-havoc allocation (no false-PROVE).
    let raw = unbounded_alloc_smt_raw(&func);
    let guard_n = var_in_relation(&raw, "<=", "100")
        .expect("the dominating guard `n <= 100` must be present (exempt)");
    let viol_n = var_in_relation(&raw, ">=", "268435456")
        .expect("the OOM violation over the havoced count must be present");
    assert_ne!(
        guard_n, viol_n,
        "the guard's `n` must be version-DISJOINT from the deref-store-HAVOCED \
         violation `n` (else a ~1 GiB allocation is false-PROVED safe); \
         guard={guard_n} viol={viol_n}; raw: {raw}"
    );
}

mod zero_sized_vec {
    use trust_types::{CalleeKey, SysrootItem};

    use super::*;

    const OPERATIONS: &[(&str, SysrootItem, usize)] = &[
        ("with_capacity", SysrootItem::VecWithCapacity, 0),
        ("with_capacity_in", SysrootItem::VecWithCapacityIn, 0),
        ("reserve", SysrootItem::VecReserve, 1),
        ("reserve_exact", SysrootItem::VecReserveExact, 1),
        ("resize", SysrootItem::VecResize, 1),
        ("resize_with", SysrootItem::VecResizeWith, 1),
        ("from_elem", SysrootItem::VecFromElem, 1),
    ];

    fn key(item: Option<SysrootItem>) -> CalleeKey {
        CalleeKey {
            sysroot_item: item,
            krate_is_real_sysroot: true,
            krate_name_is_ambiguous: false,
            stable_crate_id: 123,
            krate_name: "alloc".into(),
            foreign_block_leaf: None,
            upstream_foreign_link_symbol: None,
            diverging_entry: None,
        }
    }

    fn call(leaf: &str, size: &str, item: Option<SysrootItem>) -> VerifiableFunction {
        let path = if leaf == "from_elem" {
            format!("alloc::vec::from_elem::<user::Empty>{size}")
        } else {
            format!("alloc::vec::Vec::<user::Empty>::{leaf}{size}")
        };
        let mut f = func_calling(&path);
        if let Terminator::Call { callee_key, args, .. } = &mut f.body.blocks[0].terminator {
            *callee_key = Some(key(item));
            if !matches!(leaf, "with_capacity" | "with_capacity_in") {
                args.insert(0, Operand::Copy(Place::local(2)));
            }
        }
        f
    }

    #[test]
    fn authenticated_zero_size_has_no_backing_allocation_for_every_vec_operation() {
        for &(leaf, item, _) in OPERATIONS {
            if is_additive(item) {
                continue;
            }
            let f = call(leaf, "::<__trust_elem_bytes@0>", Some(item));
            assert_eq!(unbounded_alloc_count(&f), 0, "{leaf}");
        }
    }

    /// Review round 59: `reserve`/`reserve_exact` ADD to a length that a zero-sized
    /// element does not bound, so `len + additional` can overflow `usize` and panic
    /// "capacity overflow" with no backing allocation at all. Their row stays.
    ///
    /// Trust (2026-10-14, ALLOC-RECEIVER-ZST-1): it stays as a VISIBLE UNKNOWN
    /// (`receiver_unknown_count`), no longer as a counted row. The counted row it was
    /// carried no byte term at stride zero, so it was the element ceiling alone: a
    /// guard discharged it (kernel-certified on stage 1 for `if n < 100 {
    /// v.reserve(n) }`) and a constant count skipped it, while a full `Vec<()>`
    /// overflows on `reserve(1)`. The old assertion (`unbounded_alloc_count == 1`)
    /// counted that dischargeable row as the charge; it was never one. (This
    /// module's receiver is a `u32` stand-in, which reads as no collection at all
    /// and keeps the same Unknown; `alloc_width_receiver_tests` pins the real
    /// `&mut Vec<()>` / `&mut VecDeque<()>` receivers and their sized controls.)
    fn is_additive(item: SysrootItem) -> bool {
        matches!(item, SysrootItem::VecReserve | SysrootItem::VecReserveExact)
    }

    /// The visible Unknown a live-receiver sink keeps when memory does not bound the
    /// receiver's length (`alloc_vcs::live_receiver_length_is_bounded`).
    fn receiver_unknown_count(func: &VerifiableFunction) -> usize {
        generate_vcs(func)
            .iter()
            .filter(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { kind, .. }
                        if kind == "UnboundedAllocation::Vec::reserve::receiver-length-not-bounded"
                )
            })
            .count()
    }

    #[test]
    fn a_zero_sized_reserve_keeps_its_row() {
        for &(leaf, item, _) in OPERATIONS {
            if !is_additive(item) {
                continue;
            }
            let f = call(leaf, "::<__trust_elem_bytes@0>", Some(item));
            assert_eq!(unbounded_alloc_count(&f), 0, "{leaf}: no dischargeable counted row");
            assert_eq!(receiver_unknown_count(&f), 1, "{leaf}: the visible Unknown");
        }
    }

    #[test]
    fn absent_unrecognized_and_non_sysroot_keys_keep_the_allocation_row() {
        for &(leaf, item, _) in OPERATIONS {
            // An additive leaf keeps its charge as the receiver Unknown (see
            // `is_additive`); every other leaf keeps its counted row.
            let kept = |f: &VerifiableFunction| {
                if is_additive(item) {
                    assert_eq!(unbounded_alloc_count(f), 0, "{leaf}");
                    receiver_unknown_count(f)
                } else {
                    unbounded_alloc_count(f)
                }
            };
            let mut f = call(leaf, "::<__trust_elem_bytes@0>", None);
            assert_eq!(kept(&f), 1, "untagged {leaf}");
            if let Terminator::Call { callee_key, .. } = &mut f.body.blocks[0].terminator {
                *callee_key = None;
            }
            assert_eq!(kept(&f), 1, "absent {leaf}");
        }
        let mut f =
            call("with_capacity", "::<__trust_elem_bytes@0>", Some(SysrootItem::VecWithCapacity));
        if let Terminator::Call { callee_key: Some(k), .. } = &mut f.body.blocks[0].terminator {
            k.krate_is_real_sysroot = false;
        }
        assert_eq!(unbounded_alloc_count(&f), 1);
    }

    #[test]
    fn every_unrelated_sysroot_tag_keeps_the_allocation_row() {
        for &item in trust_types::ALL_SYSROOT_ITEMS {
            if OPERATIONS.iter().any(|&(_, known, _)| known == item) {
                continue;
            }
            let f = call("with_capacity", "::<__trust_elem_bytes@0>", Some(item));
            assert_eq!(unbounded_alloc_count(&f), 1, "{item:?}");
        }
    }

    #[test]
    fn nonzero_unknown_and_source_spellable_sizes_keep_the_allocation_row() {
        for &(leaf, item, _) in OPERATIONS {
            for suffix in [
                "",
                "::<__trust_elem_bytes@1>",
                "::<__trust_elem_bytes@4096>",
                "::<__trust_elem_bytes_0>",
                "::<__trust_elem_bytes@0>::<u8>",
            ] {
                let f = call(leaf, suffix, Some(item));
                if is_additive(item) {
                    // The `u32` stand-in receiver is no collection whose length
                    // memory bounds: a visible Unknown, never a dropped call.
                    assert_eq!(unbounded_alloc_count(&f), 0, "{leaf} {suffix}");
                    assert_eq!(receiver_unknown_count(&f), 1, "{leaf} {suffix}");
                } else {
                    assert_eq!(alloc_row_count(&f), 1, "{leaf} {suffix}");
                }
            }
        }
        let mut f = func_calling("alloc::vec::Vec::<()>::with_capacity");
        if let Terminator::Call { callee_key, .. } = &mut f.body.blocks[0].terminator {
            *callee_key = Some(key(Some(SysrootItem::VecWithCapacity)));
        }
        assert_eq!(unbounded_alloc_count(&f), 1, "a type spelling alone is insufficient");
    }

    #[test]
    fn another_containers_zero_sized_type_parameter_is_not_its_storage_size() {
        let path = "user::Vec::<()>::with_capacity::<__trust_elem_bytes@0>";
        assert_eq!(unbounded_alloc_count(&func_calling(path)), 1, "{path}");
        // Trust (W4 HASHMAP r2, 2026-09-28): a std `HashMap`/`HashSet` allocation
        // that arrives WITHOUT the extractor's hash-table token — here a plain
        // `@0` read off its first type argument `K = ()`, the r1 stamping that
        // sized `HashMap::<u8, [u8; 1 << 50]>` as one byte — is neither skipped as
        // zero-sized nor charged `count * stride` any more: it fails closed as ONE
        // visible Unknown (`hash-table-token-absent`). Still never dropped.
        let path = "std::collections::HashMap::<(), u64>::with_capacity::<__trust_elem_bytes@0>";
        let vcs = super::super::generate_unbounded_allocation_vcs_on_64_bit(&func_calling(path));
        assert_eq!(vcs.len(), 1, "{path}");
        assert!(matches!(vcs[0].kind, VcKind::UnsupportedMir { .. }), "{path}");
    }

    #[test]
    fn zero_size_does_not_hide_missing_count_operands() {
        for &(leaf, item, index) in OPERATIONS {
            let mut f = call(leaf, "::<__trust_elem_bytes@0>", Some(item));
            if let Terminator::Call { args, .. } = &mut f.body.blocks[0].terminator {
                args.truncate(index);
            }
            let vcs = super::super::generate_unbounded_allocation_vcs_on_64_bit(&f);
            assert_eq!(vcs.len(), 1, "{leaf}");
            assert!(matches!(vcs[0].kind, VcKind::UnsupportedMir { .. }), "{leaf}");
        }
    }

    #[test]
    fn removing_the_backing_allocation_preserves_other_obligations() {
        for &(leaf, item, _) in OPERATIONS {
            if is_additive(item) {
                continue;
            }
            let mut f = call(leaf, "::<__trust_elem_bytes@0>", None);
            if let Terminator::Call { target, .. } = &mut f.body.blocks[0].terminator {
                *target = Some(BlockId(1));
            }
            // The standalone generator does not add the compiler's whole-call
            // panic obligations. Give this fixture an actual caller assertion.
            f.body.blocks.extend([
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Constant(ConstValue::Bool(false)),
                        expected: true,
                        msg: trust_types::AssertMessage::Custom("caller panic remains".into()),
                        target: BlockId(2),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ]);
            let before = generate_vcs(&f);
            assert_eq!(unbounded_alloc_count(&f), 1, "unrecognized call: {leaf}");
            if let Terminator::Call { callee_key, .. } = &mut f.body.blocks[0].terminator {
                *callee_key = Some(key(Some(item)));
            }
            let after = generate_vcs(&f);
            let remaining: Vec<_> = before
                .into_iter()
                .filter(|vc| !matches!(vc.kind, VcKind::UnboundedAllocation { .. }))
                .collect();
            assert!(
                remaining.iter().any(|vc| matches!(
                    &vc.kind, VcKind::Assertion { message } if message == "caller panic remains"
                )),
                "explicit assertion must remain: {leaf}"
            );
            assert_eq!(
                serde_json::to_value(remaining).unwrap(),
                serde_json::to_value(after).unwrap(),
                "{leaf}"
            );
        }
    }
}

/// fa/struct-alloc (2026-10-02): `recv.<callee>(arg)` — a two-argument method call
/// whose receiver is local 1 and whose second argument (the bulk-alloc count index
/// for `resize`/`reserve`) is local 2 of type `arg_ty`.
fn method_call_with_arg(callee: &str, arg_ty: Ty) -> VerifiableFunction {
    let mut func = func_calling(callee);
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: None },
        LocalDecl { index: 1, ty: Ty::usize(), name: Some("recv".into()) },
        LocalDecl { index: 2, ty: arg_ty, name: Some("arg".into()) },
        LocalDecl { index: 3, ty: Ty::Unit, name: None },
    ];
    func.body.arg_count = 2;
    func.body.return_ty = Ty::Unit;
    let Terminator::Call { args, dest, .. } = &mut func.body.blocks[0].terminator else {
        unreachable!()
    };
    *args = vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))];
    *dest = Place::local(3);
    func
}

fn pty_size_ty() -> Ty {
    Ty::adt("orca_pty::PtySize", vec![("rows".into(), Ty::u16()), ("cols".into(), Ty::u16())])
}

/// The `UnsupportedMir` rows the name-matched, non-integer-count arm mints.
fn count_not_an_integer_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. }
                    if kind.starts_with("UnboundedAllocation::")
                        && kind.ends_with("::count-not-an-integer")
            )
        })
        .count()
}

#[test]
fn struct_argument_to_user_resize_is_not_an_allocation_count() {
    // MEASURED: orca-daemon `rpc.rs` — `_25 = PtySize { rows, cols }` passed by value
    // to `PtySession::resize` FAILED `[unbounded_allocation] … <[T]>::resize (count
    // _25)` with `_25 = 268435456` (seal `321aaeda7`, stage-1 `f9e47e012`). A struct
    // is not an element count: no counted row (so no false counterexample), and one
    // visible Unknown, because the name match alone cannot tell it from a real
    // third-party allocator (see the ndarray test below).
    let func = method_call_with_arg("orca_pty::PtySession::resize", pty_size_ty());
    assert_eq!(unbounded_alloc_count(&func), 0);
    assert_eq!(count_not_an_integer_count(&func), 1);
    for callee in
        ["mycrate::Grid::reserve", "mycrate::Pool::reserve_exact", "mycrate::Grid::resize_with"]
    {
        let func = method_call_with_arg(callee, Ty::Tuple(vec![Ty::u16(), Ty::u16()]));
        assert_eq!(unbounded_alloc_count(&func), 0, "{callee}");
        assert_eq!(count_not_an_integer_count(&func), 1, "{callee}");
    }
}

#[test]
fn struct_argument_at_count_index_zero_is_not_counted_but_stays_visible() {
    // `with_capacity*` carries its count at index 0. A same-named constructor
    // taking a config struct is not counted, and is not silent either.
    for callee in ["mycrate::Pool::with_capacity", "mycrate::Map::with_capacity_and_hasher"] {
        let func = call_with_args(callee, vec![pty_size_ty()]);
        assert_eq!(unbounded_alloc_count(&func), 0, "{callee}");
        assert_eq!(count_not_an_integer_count(&func), 1, "{callee}");
    }
}

#[test]
fn third_party_allocator_with_count_elsewhere_is_never_silent() {
    // Review of r1 (`79f5ce3389`), MEASURED there: ndarray's
    // `ArrayBase::reserve(&mut self, axis: Axis, additional: usize)` (argument 1 is
    // a struct) and `ArrayBase::from_elem(shape, elem)` (argument 1 is the element,
    // a float) are REAL caller-sized heap allocations, and r1 minted NO row for
    // either. They must keep a visible obligation.
    let arr = Ty::adt("ndarray::ArrayBase", vec![]);
    let axis = Ty::adt("ndarray::Axis", vec![("0".into(), Ty::usize())]);
    let reserve = call_with_args(
        "ndarray::impl_owned_array::<impl ndarray::ArrayBase<S, D>>::reserve",
        vec![Ty::Ref { mutable: true, inner: Box::new(arr) }, axis, Ty::usize()],
    );
    let from_elem = call_with_args(
        "ndarray::ArrayBase::<S, D>::from_elem",
        vec![Ty::Tuple(vec![Ty::usize(), Ty::usize()]), Ty::Float { width: 64 }],
    );
    for (name, func) in [("reserve", reserve), ("from_elem", from_elem)] {
        assert_eq!(
            unbounded_alloc_count(&func) + count_not_an_integer_count(&func),
            1,
            "ndarray {name}: a real allocation must keep exactly one visible row"
        );
        assert_eq!(count_not_an_integer_count(&func), 1, "ndarray {name}");
    }
}

#[test]
fn unclassifiable_count_type_keeps_its_counted_row() {
    // Control for the fail-closed side of the type filter: a count whose type this
    // lane cannot classify (`Unsupported`) is still charged as a count.
    let func = method_call_with_arg(
        "alloc::vec::Vec::<u8>::resize",
        Ty::Unsupported { kind: "generic".into(), detail: "count".into() },
    );
    assert_eq!(unbounded_alloc_count(&func), 1);
    assert_eq!(count_not_an_integer_count(&func), 0);
}

#[test]
fn integer_count_to_resize_keeps_its_row() {
    // Control: the real `Vec::resize(n, _)` with an unbounded `usize` count is still
    // charged, and so (conservatively, by name) is a same-named method taking an
    // integer — the type filter only removes rows over non-integer operands.
    let func = method_call_with_arg("alloc::vec::Vec::<u8>::resize", Ty::usize());
    assert_eq!(unbounded_alloc_count(&func), 1);
    let func = method_call_with_arg("orca_pty::PtySession::resize", Ty::usize());
    assert_eq!(alloc_row_count(&func), 1);
    let func = method_call_with_arg("alloc::vec::Vec::<u8>::reserve", Ty::u64());
    assert_eq!(unbounded_alloc_count(&func), 1);
    assert_eq!(count_not_an_integer_count(&func), 0);
}

/// fa/struct-alloc r2: `callee(a1, .., an)` with each `ai` local `i` of `tys[i-1]`.
fn call_with_args(callee: &str, tys: Vec<Ty>) -> VerifiableFunction {
    let mut func = func_calling(callee);
    let n = tys.len();
    let mut locals = vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }];
    for (i, ty) in tys.into_iter().enumerate() {
        locals.push(LocalDecl { index: i + 1, ty, name: Some(format!("a{}", i + 1)) });
    }
    locals.push(LocalDecl { index: n + 1, ty: Ty::Unit, name: None });
    func.body.locals = locals;
    func.body.arg_count = n;
    func.body.return_ty = Ty::Unit;
    let Terminator::Call { args, dest, .. } = &mut func.body.blocks[0].terminator else {
        unreachable!()
    };
    *args = (1..=n).map(|i| Operand::Move(Place::local(i))).collect();
    *dest = Place::local(n + 1);
    func
}
