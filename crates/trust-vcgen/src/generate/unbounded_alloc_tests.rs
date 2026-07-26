use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
    VcKind, VerifiableBody, VerifiableFunction,
};

use crate::generate_vcs;

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
                    is_foreign: false,
                },
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn unbounded_alloc_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnboundedAllocation { .. }))
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
        super::method_tail("std::vec::from_elem::<u8>::<__trust_elem_bytes_1>"),
        "from_elem"
    );
    assert_eq!(
        super::method_tail(
            "core::iter::Iterator::collect::<alloc::vec::Vec<u8>>::<__trust_elem_bytes_8>"
        ),
        "collect"
    );
    // A method sink with the byte token keeps its type turbofish in the middle.
    assert_eq!(
        super::method_tail("std::vec::Vec::<u8>::with_capacity::<__trust_elem_bytes_4096>"),
        "with_capacity"
    );
}

#[test]
fn range_family_identity_accepts_defining_and_reexport_paths_only() {
    const FAMILIES: [&str; 5] =
        ["Range", "RangeTo", "RangeFrom", "RangeInclusive", "RangeFull"];
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
    assert!(!super::aggregate_is_exclusive_range(
        "core::ops::range::RangeInclusive<usize>"
    ));
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
                    is_foreign: false,
                },
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
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
                        is_foreign: false,
                    },
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert_eq!(
        unbounded_alloc_count(&func),
        1,
        "repeat_n(x, n).collect() with unbounded n must be flagged"
    );
}

#[test]
fn from_elem_multibyte_adds_byte_aware_term() {
    // vec![0u64; n] with symbolic n: from_elem's element is a real typed
    // operand, so the failure formula carries the BYTE-aware product
    // (elem_size 8 * n >= budget), tightening the bare element ceiling — the
    // one MIR allocation whose element type survives (RawVec erases it
    // elsewhere; the trust-ir layer does this in general, alloc_bound.rs).
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
                    is_foreign: false,
                },
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
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
                    is_foreign: false,
                },
            }],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
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
            vec![
                Operand::Constant(ConstValue::Int(0)),
                Operand::Constant(ConstValue::Int(end)),
            ],
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
                    is_foreign: false,
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: collect_term(2) },
        ]
    } else {
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![range_stmt],
            terminator: collect_term(1),
        }]
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
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn flags_collect_over_huge_const_range() {
    // The exact nn-dsl OOM idiom: `(0..1<<28).collect()` materializes 2^28
    // elements. `.collect()` carries no size operand, so the count is
    // reconstructed from the Range bounds.
    let func = range_collect_func(1 << 28, false);
    assert_eq!(
        unbounded_alloc_count(&func),
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
        unbounded_alloc_count(&func),
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
/// (`coll` is a parameter). `producer` is the full callee path of the producer.
fn collection_collect_func(producer: &str, cloned: bool) -> VerifiableFunction {
    let collect_term = |iter_local: usize| Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: "core::iter::Iterator::collect".to_string(),
        args: vec![Operand::Move(Place::local(iter_local))],
        dest: Place::local(5),
        target: None,
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
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
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("coll".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("it".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("it2".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
                LocalDecl { index: 5, ty: Ty::u32(), name: Some("out".into()) },
            ],
            blocks,
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn allows_collect_over_vec_iter() {
    // Collecting from an already-materialized std Vec is bounded by the
    // source's own (already-gated) allocation — must not be flagged.
    let func = collection_collect_func("alloc::vec::Vec::<u32>::iter", false);
    assert_eq!(unbounded_alloc_count(&func), 0, "collect over Vec::iter must not be flagged");
    assert_eq!(
        unsupported_mir_count(&func),
        0,
        "...nor reported as count-not-derivable Unknown"
    );
}

#[test]
fn allows_collect_over_hashmap_keys_cloned() {
    // Mirrors ny-cert `check_farkas`: `coeffs.keys().cloned().collect()`.
    let func =
        collection_collect_func("std::collections::hash_map::HashMap::<K, V>::keys", true);
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
    let func = collection_collect_func("mycrate::Weird::iter", false);
    assert_eq!(
        unsupported_mir_count(&func),
        1,
        "a custom non-std iter source must stay gated (count-not-derivable), not be skipped"
    );
}

/// Builds `a.keys().chain(b.keys()).cloned().collect()` (params `a`, `b`).
fn chained_keys_collect_func(keys_path: &str) -> VerifiableFunction {
    let keys = |coll: usize, dest: usize, target: BlockId| Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: keys_path.to_string(),
        args: vec![Operand::Move(Place::local(coll))],
        dest: Place::local(dest),
        target: Some(target),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
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
                is_foreign: false,
            },
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                func: "core::iter::Iterator::collect".to_string(),
                args: vec![Operand::Move(Place::local(6))],
                dest: Place::local(7),
                target: None,
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
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
                .map(|i| LocalDecl { index: i, ty: Ty::u32(), name: None })
                .collect(),
            blocks,
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn allows_collect_over_chained_keys() {
    // Mirrors ny-cert `check_entailment`:
    // `a.keys().chain(b.keys()).cloned().collect()` — a chain of two
    // materialized-collection iterators is bounded (sum of two already-gated
    // allocations), so it must not be flagged.
    let func = chained_keys_collect_func("std::collections::hash_map::HashMap::<K, V>::keys");
    assert_eq!(
        unbounded_alloc_count(&func),
        0,
        "collect over a.keys().chain(b.keys()).cloned() must not be flagged"
    );
    assert_eq!(unsupported_mir_count(&func), 0, "...nor reported count-not-derivable Unknown");
}

fn unsupported_mir_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { .. }))
        .count()
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
                    is_foreign: false,
                },
            }],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
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
                    is_foreign: false,
                },
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn flags_oversized_box_new() {
    // `Box::new([0u8; 1 << 40])` heap-allocates a single ~1 TiB value — the
    // OOM/`capacity overflow` hazard the count-only gate misses (count is 1).
    // The byte size of `[u8; 1<<40]` exceeds the availability ceiling, so it
    // must be flagged.
    let huge = Ty::Array { elem: Box::new(Ty::u8()), len: 1u64 << 40 };
    let func = func_calling_single_value("alloc::boxed::Box::<[u8; 1099511627776]>::new", huge);
    assert_eq!(
        unbounded_alloc_count(&func),
        1,
        "an oversized single-value Box::new (a ~1 TiB value) must be flagged"
    );
}

#[test]
fn flags_oversized_rc_and_arc_new() {
    // The same hazard via `Rc::new` / `Arc::new` (a single oversized value).
    let huge = || Ty::Array { elem: Box::new(Ty::u8()), len: 1u64 << 40 };
    let rc = func_calling_single_value("alloc::rc::Rc::<[u8; 1099511627776]>::new", huge());
    let arc = func_calling_single_value("alloc::sync::Arc::<[u8; 1099511627776]>::new", huge());
    assert_eq!(unbounded_alloc_count(&rc), 1, "oversized Rc::new must be flagged");
    assert_eq!(unbounded_alloc_count(&arc), 1, "oversized Arc::new must be flagged");
}

#[test]
fn allows_ordinary_box_new() {
    // A small `Box::new(x)` is the ubiquitous boxing pattern — it must NOT be
    // flagged (drop-in Rust preserved). A `u64` value is 8 bytes, far below any
    // ceiling.
    let func = func_calling_single_value("alloc::boxed::Box::<u64>::new", Ty::u64());
    assert_eq!(
        unbounded_alloc_count(&func),
        0,
        "an ordinary small Box::new must not be flagged"
    );
    // And a `Box::new` of another small primitive (4 bytes) is likewise not
    // flagged — only an oversized value reaching the availability ceiling is.
    let small = func_calling_single_value("alloc::boxed::Box::<u32>::new", Ty::u32());
    assert_eq!(
        unbounded_alloc_count(&small),
        0,
        "a Box::new of a small value must not be flagged"
    );
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
    assert_eq!(
        super::single_value_alloc_call("alloc::boxed::Box::<u8>::new"),
        Some("Box::new")
    );
    assert_eq!(super::single_value_alloc_call("alloc::rc::Rc::<u8>::new"), Some("Rc::new"));
    assert_eq!(super::single_value_alloc_call("alloc::sync::Arc::<u8>::new"), Some("Arc::new"));
    // The pinning forms route to the same allocation.
    assert_eq!(
        super::single_value_alloc_call("alloc::boxed::Box::<u8>::pin"),
        Some("Box::new")
    );
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
            if rest.starts_with(lit) && rest[lit.len()..].starts_with(')') && !var.contains('(')
            {
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
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
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
                        // reseat -> unique_whole_local_def(p) = None
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
                        is_foreign: false,
                    },
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
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
