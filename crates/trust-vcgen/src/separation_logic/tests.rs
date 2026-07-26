// trust_vcgen/separation_logic/tests.rs: Tests for separation logic module
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::{Formula, Sort, SourceSpan, VcKind};

use super::unsafe_ops::UnsafeOpKind;
use super::*;

fn addr(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn val(n: i128) -> Formula {
    Formula::Int(n)
}

fn collect_free_vars(formula: &Formula) -> FxHashSet<String> {
    formula.free_variables()
}

// ── SepFormula construction tests ────────────────────────────────────

#[test]
fn test_sep_formula_points_to() {
    let f = SepFormula::points_to(addr("x"), val(42));
    assert!(matches!(f, SepFormula::PointsTo { .. }));
}

#[test]
fn test_sep_formula_star() {
    let f = SepFormula::star(
        SepFormula::points_to(addr("x"), val(1)),
        SepFormula::points_to(addr("y"), val(2)),
    );
    assert!(matches!(f, SepFormula::SepStar(_, _)));
}

#[test]
fn test_sep_formula_wand() {
    let f = SepFormula::wand(
        SepFormula::points_to(addr("x"), val(1)),
        SepFormula::points_to(addr("y"), val(2)),
    );
    assert!(matches!(f, SepFormula::SepWand(_, _)));
}

#[test]
fn test_sep_formula_emp() {
    let f = SepFormula::Emp;
    assert!(f.is_emp());
}

#[test]
fn test_sep_formula_pure() {
    let f = SepFormula::pure(Formula::Bool(true));
    assert!(matches!(f, SepFormula::Pure(_)));
    assert!(!f.is_emp());
}

#[test]
fn test_sep_formula_cell_count() {
    assert_eq!(SepFormula::Emp.cell_count(), 0);
    assert_eq!(SepFormula::points_to(addr("x"), val(1)).cell_count(), 1);
    assert_eq!(
        SepFormula::star(
            SepFormula::points_to(addr("x"), val(1)),
            SepFormula::points_to(addr("y"), val(2)),
        )
        .cell_count(),
        2
    );
    assert_eq!(SepFormula::pure(Formula::Bool(true)).cell_count(), 0);
}

#[test]
fn test_sep_formula_star_many_empty() {
    let result = SepFormula::star_many(vec![]);
    assert!(result.is_emp());
}

#[test]
fn test_sep_formula_star_many_single() {
    let p = SepFormula::points_to(addr("x"), val(1));
    let result = SepFormula::star_many(vec![p.clone()]);
    assert_eq!(result, p);
}

#[test]
fn test_sep_formula_star_many_multiple() {
    let formulas = vec![
        SepFormula::points_to(addr("a"), val(1)),
        SepFormula::points_to(addr("b"), val(2)),
        SepFormula::points_to(addr("c"), val(3)),
    ];
    let result = SepFormula::star_many(formulas);
    assert_eq!(result.cell_count(), 3);
}

// ── sep_to_formula translation tests ─────────────────────────────────

#[test]
fn test_sep_to_formula_emp_is_true() {
    let result = sep_to_formula(&SepFormula::Emp, "heap");
    assert_eq!(result, Formula::Bool(true));
}

#[test]
fn test_sep_to_formula_pure_passes_through() {
    let phi = Formula::Gt(Box::new(addr("x")), Box::new(val(0)));
    let result = sep_to_formula(&SepFormula::Pure(phi.clone()), "heap");
    assert_eq!(result, phi);
}

#[test]
fn test_sep_to_formula_points_to_becomes_select_eq() {
    let sep = SepFormula::points_to(addr("p"), val(42));
    let result = sep_to_formula(&sep, "heap");

    // Should be: Select(heap, p) == 42
    match &result {
        Formula::Eq(lhs, rhs) => {
            assert!(matches!(lhs.as_ref(), Formula::Select(_, _)));
            assert_eq!(**rhs, val(42));
        }
        other => panic!("expected Eq, got: {other:?}"),
    }
}

#[test]
fn test_sep_to_formula_star_produces_conjunction_with_disjointness() {
    let sep = SepFormula::star(
        SepFormula::points_to(addr("p"), val(1)),
        SepFormula::points_to(addr("q"), val(2)),
    );
    let result = sep_to_formula(&sep, "heap");

    // Should be: And([Select(heap,p)==1, Select(heap,q)==2, p!=q])
    match &result {
        Formula::And(terms) => {
            assert_eq!(terms.len(), 3, "star should produce 3-element And");
            // Third element is the disjointness constraint
            assert!(matches!(&terms[2], Formula::Not(_)), "disjointness should be Not(Eq(p, q))");
        }
        other => panic!("expected And, got: {other:?}"),
    }
}

#[test]
fn test_sep_to_formula_wand_produces_implication() {
    let sep = SepFormula::wand(
        SepFormula::points_to(addr("p"), val(1)),
        SepFormula::points_to(addr("q"), val(2)),
    );
    let result = sep_to_formula(&sep, "heap");

    assert!(matches!(&result, Formula::Implies(_, _)), "wand should produce Implies");
}

// ── encode_heap_disjointness tests ───────────────────────────────────

#[test]
fn test_disjointness_empty_lhs() {
    let result =
        encode_heap_disjointness(&SepFormula::Emp, &SepFormula::points_to(addr("p"), val(1)));
    assert_eq!(result, Formula::Bool(true), "empty LHS means trivially disjoint");
}

#[test]
fn test_disjointness_empty_rhs() {
    let result =
        encode_heap_disjointness(&SepFormula::points_to(addr("p"), val(1)), &SepFormula::Emp);
    assert_eq!(result, Formula::Bool(true), "empty RHS means trivially disjoint");
}

#[test]
fn test_disjointness_single_pair() {
    let result = encode_heap_disjointness(
        &SepFormula::points_to(addr("p"), val(1)),
        &SepFormula::points_to(addr("q"), val(2)),
    );
    // Should be: Not(Eq(p, q))
    match &result {
        Formula::Not(inner) => {
            assert!(matches!(inner.as_ref(), Formula::Eq(_, _)));
        }
        other => panic!("expected Not(Eq), got: {other:?}"),
    }
}

#[test]
fn test_disjointness_multiple_addresses() {
    let lhs = SepFormula::star(
        SepFormula::points_to(addr("a"), val(1)),
        SepFormula::points_to(addr("b"), val(2)),
    );
    let rhs = SepFormula::points_to(addr("c"), val(3));
    let result = encode_heap_disjointness(&lhs, &rhs);

    // Should be: And([Not(Eq(a, c)), Not(Eq(b, c))])
    match &result {
        Formula::And(terms) => {
            assert_eq!(terms.len(), 2, "2 LHS addrs * 1 RHS addr = 2 constraints");
        }
        other => panic!("expected And, got: {other:?}"),
    }
}

// ── deref_vc tests ───────────────────────────────────────────────────

#[test]
fn test_deref_vc_generates_three_vcs() {
    let vcs = deref_vc("test_fn", "raw_ptr", &SourceSpan::default());
    assert_eq!(vcs.len(), 3, "deref should produce 3 VCs: null, alloc, align");
}

#[test]
fn test_deref_vc_null_check() {
    let vcs = deref_vc("test_fn", "p", &SourceSpan::default());
    let null_vc = &vcs[0];
    assert!(matches!(
        &null_vc.kind,
        VcKind::Assertion { message } if message.contains("null check")
    ));
    // Formula: generated(ptr_p) == 0
    match &null_vc.formula {
        Formula::Eq(lhs, rhs) => {
            assert!(matches!(lhs.as_ref(), Formula::Var(name, _)
                if name == &generated_symbol("ptr_p")));
            assert_eq!(**rhs, Formula::Int(0));
        }
        other => panic!("expected Eq for null check, got: {other:?}"),
    }
}

#[test]
fn test_deref_vc_allocation_validity() {
    let vcs = deref_vc("test_fn", "p", &SourceSpan::default());
    let alloc_vc = &vcs[1];
    assert!(matches!(
        &alloc_vc.kind,
        VcKind::Assertion { message } if message.contains("allocation validity")
    ));
    // Formula: Select(heap, ptr_p) == -1
    match &alloc_vc.formula {
        Formula::Eq(lhs, rhs) => {
            assert!(matches!(lhs.as_ref(), Formula::Select(_, _)));
            assert_eq!(**rhs, Formula::Int(-1));
        }
        other => panic!("expected Eq for alloc check, got: {other:?}"),
    }
}

#[test]
fn test_deref_vc_alignment_check() {
    let vcs = deref_vc("test_fn", "p", &SourceSpan::default());
    let align_vc = &vcs[2];
    assert!(matches!(
        &align_vc.kind,
        VcKind::Assertion { message } if message.contains("alignment check")
    ));
    // Formula should reference separation-owned align_p and ptr_p symbols.
    let vars = collect_free_vars(&align_vc.formula);
    assert!(
        vars.contains(&generated_symbol("ptr_p")),
        "alignment VC should reference its generated pointer symbol"
    );
    assert!(
        vars.contains(&generated_symbol("align_p")),
        "alignment VC should reference its generated alignment symbol"
    );
}

#[test]
fn test_generated_pointer_symbols_cannot_alias_source_variables() {
    // `ptr_p` is a legal Rust source identifier.  Separation obligations are
    // later conjoined with source path definitions and guards, so reusing that
    // spelling here could let an unrelated scalar assumption discharge a raw
    // pointer check.
    let source_name = "ptr_p";
    let generated_name = generated_symbol(source_name);
    let vcs = deref_vc("test_fn", "p", &SourceSpan::default());
    let vars = collect_free_vars(&vcs[0].formula);

    assert_ne!(generated_name, source_name);
    assert!(generated_name.contains("__"));
    assert!(vars.contains(&generated_name));
    assert!(!vars.contains(source_name));
}

// ── raw_write_vc tests ───────────────────────────────────────────────

#[test]
fn test_raw_write_vc_includes_deref_plus_write_vcs() {
    let write_val = Formula::Int(42);
    let vcs = raw_write_vc("test_fn", "p", &write_val, &SourceSpan::default());
    // 3 deref VCs + 1 write permission = 4 (no post-write consistency VC: it is a
    // content-free read-over-write tautology that never catches a bug — see
    // `raw_write_vc`).
    assert_eq!(vcs.len(), 4, "raw write should produce 4 VCs");
}

#[test]
fn test_raw_write_vc_write_permission() {
    let write_val = Formula::Int(42);
    let vcs = raw_write_vc("test_fn", "p", &write_val, &SourceSpan::default());
    let write_perm = &vcs[3];
    assert!(matches!(
        &write_perm.kind,
        VcKind::Assertion { message } if message.contains("write permission")
    ));
    // Formula: Not(generated(writable_p))
    match &write_perm.formula {
        Formula::Not(inner) => {
            assert!(matches!(inner.as_ref(), Formula::Var(name, Sort::Bool)
                    if name == &generated_symbol("writable_p")));
        }
        other => panic!("expected Not(writable_p), got: {other:?}"),
    }
}

#[test]
fn test_raw_write_vc_has_no_post_write_consistency_vc() {
    // The post-write (read-over-write) consistency VC was removed: it is a content-free
    // tautology (`Select(Store(h,p,v),p) ≡ v` always holds) that never catches a bug
    // and only surfaced spurious counterexamples on safe writes.
    let write_val = Formula::Int(99);
    let vcs = raw_write_vc("test_fn", "p", &write_val, &SourceSpan::default());
    assert!(
        !vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("post-write consistency")
        )),
        "raw_write_vc must not emit a post-write consistency VC"
    );
}

// ── transmute_vc tests ───────────────────────────────────────────────

#[test]
fn test_transmute_vc_generates_three_vcs() {
    let vcs = transmute_vc("test_fn", "u32", "f32", &SourceSpan::default());
    assert_eq!(vcs.len(), 3, "transmute should produce 3 VCs: layout, validity, align");
}

#[test]
fn test_transmute_vc_layout_check() {
    let vcs = transmute_vc("test_fn", "u32", "f32", &SourceSpan::default());
    let layout_vc = &vcs[0];
    assert!(matches!(
        &layout_vc.kind,
        VcKind::Assertion { message } if message.contains("layout")
    ));
    // Formula: Not(Eq(size_u32, size_f32))
    let vars = collect_free_vars(&layout_vc.formula);
    assert!(vars.contains(&generated_symbol("size_u32")));
    assert!(vars.contains(&generated_symbol("size_f32")));
}

#[test]
fn test_transmute_vc_validity_check() {
    let vcs = transmute_vc("test_fn", "u32", "f32", &SourceSpan::default());
    let validity_vc = &vcs[1];
    assert!(matches!(
        &validity_vc.kind,
        VcKind::Assertion { message } if message.contains("validity")
    ));
    let vars = collect_free_vars(&validity_vc.formula);
    assert!(vars.contains(&generated_symbol("valid_bits_u32_as_f32")));
}

#[test]
fn test_transmute_vc_alignment_check() {
    let vcs = transmute_vc("test_fn", "u32", "f32", &SourceSpan::default());
    let align_vc = &vcs[2];
    assert!(matches!(
        &align_vc.kind,
        VcKind::Assertion { message } if message.contains("alignment")
    ));
    let vars = collect_free_vars(&align_vc.formula);
    assert!(vars.contains(&generated_symbol("align_u32")));
    assert!(vars.contains(&generated_symbol("align_f32")));
}

// ── encode_unsafe_block tests ────────────────────────────────────────

#[test]
fn test_encode_unsafe_block_produces_two_vcs() {
    let pre = SepFormula::points_to(addr("p"), val(1));
    let post = SepFormula::points_to(addr("p"), val(2));
    let vcs = encode_unsafe_block("test_fn", &pre, &post, &SourceSpan::default(), "heap");
    assert_eq!(vcs.len(), 2, "unsafe block should produce 2 VCs: pre + post");
}

#[test]
fn test_encode_unsafe_block_precondition_vc() {
    let pre = SepFormula::points_to(addr("p"), val(1));
    let post = SepFormula::Emp;
    let vcs = encode_unsafe_block("test_fn", &pre, &post, &SourceSpan::default(), "heap");
    assert!(matches!(
        &vcs[0].kind,
        VcKind::Assertion { message } if message.contains("precondition")
    ));
}

#[test]
fn test_encode_unsafe_block_postcondition_vc() {
    let pre = SepFormula::Emp;
    let post = SepFormula::points_to(addr("p"), val(1));
    let vcs = encode_unsafe_block("test_fn", &pre, &post, &SourceSpan::default(), "heap");
    assert!(matches!(
        &vcs[1].kind,
        VcKind::Assertion { message } if message.contains("postcondition")
    ));
}

// ── Integration: heap disjointness soundness ─────────────────────────

#[test]
fn test_star_same_address_produces_unsatisfiable_disjointness() {
    // p |-> 1 * p |-> 2 should require p != p, which is always false
    let sep = SepFormula::star(
        SepFormula::points_to(addr("p"), val(1)),
        SepFormula::points_to(addr("p"), val(2)),
    );
    let result = sep_to_formula(&sep, "heap");

    // The disjointness clause should be Not(Eq(p, p))
    match &result {
        Formula::And(terms) => {
            assert_eq!(terms.len(), 3);
            // Third term: Not(Eq(p, p))
            match &terms[2] {
                Formula::Not(inner) => match inner.as_ref() {
                    Formula::Eq(lhs, rhs) => {
                        assert_eq!(lhs, rhs, "same address: p != p is unsatisfiable");
                    }
                    other => panic!("expected Eq, got: {other:?}"),
                },
                other => panic!("expected Not, got: {other:?}"),
            }
        }
        other => panic!("expected And, got: {other:?}"),
    }
}

#[test]
fn test_nested_star_collects_all_addresses() {
    // (a |-> 1 * b |-> 2) * c |-> 3
    let inner = SepFormula::star(
        SepFormula::points_to(addr("a"), val(1)),
        SepFormula::points_to(addr("b"), val(2)),
    );
    let outer = SepFormula::star(inner, SepFormula::points_to(addr("c"), val(3)));
    let result = sep_to_formula(&outer, "heap");

    // Outer star should produce disjointness between {a,b} and {c}
    match &result {
        Formula::And(terms) => {
            // The structure is And([inner_star_fol, c_fol, disjointness])
            assert_eq!(terms.len(), 3);
        }
        other => panic!("expected And, got: {other:?}"),
    }
}

// ── All VCs are L0Safety ─────────────────────────────────────────────

#[test]
fn test_all_separation_logic_vcs_are_l0_safety() {
    let deref_vcs = deref_vc("f", "p", &SourceSpan::default());
    for vc in &deref_vcs {
        assert_eq!(
            vc.kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "deref VCs should be L0Safety"
        );
    }

    let write_vcs = raw_write_vc("f", "p", &Formula::Int(0), &SourceSpan::default());
    for vc in &write_vcs {
        assert_eq!(
            vc.kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "write VCs should be L0Safety"
        );
    }

    let transmute_vcs = transmute_vc("f", "u32", "i32", &SourceSpan::default());
    for vc in &transmute_vcs {
        assert_eq!(
            vc.kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "transmute VCs should be L0Safety"
        );
    }
}

// ── ProvenanceId tests ───────────────────────────────────────────────

#[test]
fn test_provenance_id_unknown() {
    assert!(!ProvenanceId::UNKNOWN.is_concrete());
    assert!(ProvenanceId(1).is_concrete());
    assert!(ProvenanceId(42).is_concrete());
}

#[test]
fn test_provenance_id_display() {
    assert_eq!(format!("{}", ProvenanceId::UNKNOWN), "prov(*)");
    assert_eq!(format!("{}", ProvenanceId(7)), "prov(7)");
}

#[test]
fn test_provenance_id_var_names() {
    let prov = ProvenanceId(3);
    assert_eq!(prov.base_var(), generated_symbol("prov_3_base"));
    assert_eq!(prov.size_var(), generated_symbol("prov_3_size"));
}

// ── SymbolicPointer tests ────────────────────────────────────────────

#[test]
fn test_symbolic_pointer_new() {
    let ptr = SymbolicPointer::new("my_ptr", ProvenanceId(1), PointerPermission::ReadWrite);
    assert_eq!(ptr.name, "my_ptr");
    assert_eq!(ptr.provenance, ProvenanceId(1));
    assert!(ptr.permission.can_read());
    assert!(ptr.permission.can_write());
}

#[test]
fn test_symbolic_pointer_in_bounds_concrete() {
    let ptr = SymbolicPointer::new("p", ProvenanceId(1), PointerPermission::ReadOnly);
    let bounds = ptr.in_bounds_formula();
    // Should reference the separation-owned provenance and pointer symbols.
    let vars = bounds.free_variables();
    assert!(vars.contains(&generated_symbol("prov_1_base")));
    assert!(vars.contains(&generated_symbol("prov_1_size")));
    assert!(vars.contains(&generated_symbol("ptr_p")));
}

#[test]
fn test_symbolic_pointer_in_bounds_unknown_provenance() {
    let ptr = SymbolicPointer::new("p", ProvenanceId::UNKNOWN, PointerPermission::ReadOnly);
    let bounds = ptr.in_bounds_formula();
    // Unknown provenance: should be Bool(true) (no constraint)
    assert_eq!(bounds, Formula::Bool(true));
}

#[test]
fn test_symbolic_pointer_provenance_matches() {
    let ptr = SymbolicPointer::new("p", ProvenanceId(1), PointerPermission::ReadOnly);
    let base = Formula::Var("alloc_base".into(), Sort::Int);
    let size = Formula::Var("alloc_size".into(), Sort::Int);
    let formula = ptr.provenance_matches(&base, &size);

    let vars = formula.free_variables();
    assert!(vars.contains(&generated_symbol("ptr_p")));
    assert!(vars.contains("alloc_base"));
    assert!(vars.contains("alloc_size"));
}

// ── PointerPermission tests ──────────────────────────────────────────

#[test]
fn test_pointer_permission_read_only() {
    assert!(PointerPermission::ReadOnly.can_read());
    assert!(!PointerPermission::ReadOnly.can_write());
    assert_eq!(PointerPermission::ReadOnly.label(), "read-only");
}

#[test]
fn test_pointer_permission_read_write() {
    assert!(PointerPermission::ReadWrite.can_read());
    assert!(PointerPermission::ReadWrite.can_write());
    assert_eq!(PointerPermission::ReadWrite.label(), "read-write");
}

#[test]
fn test_pointer_permission_freed() {
    assert!(!PointerPermission::Freed.can_read());
    assert!(!PointerPermission::Freed.can_write());
    assert_eq!(PointerPermission::Freed.label(), "freed");
}

// ── SymbolicHeap tests ───────────────────────────────────────────────

#[test]
fn test_symbolic_heap_new() {
    let heap = SymbolicHeap::new("heap");
    assert_eq!(heap.cell_count(), 0);
    assert_eq!(heap.pointer_count(), 0);
}

#[test]
fn test_symbolic_heap_allocate() {
    let mut heap = SymbolicHeap::new("heap");
    let prov1 = heap.allocate("p");
    let prov2 = heap.allocate("q");

    assert_ne!(prov1, prov2);
    assert!(prov1.is_concrete());
    assert!(prov2.is_concrete());
    assert_eq!(heap.pointer_count(), 2);
    assert!(heap.pointer("p").is_some());
    assert!(heap.pointer("q").is_some());
}

#[test]
fn test_symbolic_heap_write_cell() {
    let mut heap = SymbolicHeap::new("heap");
    let prov = heap.allocate("p");
    heap.write_cell("cell_p", addr("p"), val(42), prov);

    assert_eq!(heap.cell_count(), 1);
}

#[test]
fn test_symbolic_heap_free() {
    let mut heap = SymbolicHeap::new("heap");
    let prov = heap.allocate("p");

    assert!(!heap.is_freed(prov));
    heap.free(prov);
    assert!(heap.is_freed(prov));

    // Pointer should now be freed.
    let ptr = heap.pointer("p").expect("pointer p tracked");
    assert_eq!(ptr.permission, PointerPermission::Freed);
}

#[test]
fn test_symbolic_heap_to_sep_formula_empty() {
    let heap = SymbolicHeap::new("heap");
    let sep = heap.to_sep_formula();
    assert!(sep.is_emp());
}

#[test]
fn test_symbolic_heap_to_sep_formula_with_cells() {
    let mut heap = SymbolicHeap::new("heap");
    let prov = heap.allocate("p");
    heap.write_cell("cell_a", addr("a"), val(1), prov);
    heap.write_cell("cell_b", addr("b"), val(2), prov);

    let sep = heap.to_sep_formula();
    assert_eq!(sep.cell_count(), 2);
}

#[test]
fn test_symbolic_heap_to_formula() {
    let mut heap = SymbolicHeap::new("heap");
    let prov = heap.allocate("p");
    heap.write_cell("cell_a", addr("a"), val(1), prov);

    let formula = heap.to_formula();
    // Should contain Select(heap, a) == 1
    let vars = formula.free_variables();
    assert!(vars.contains("heap"), "formula should reference heap");
    assert!(vars.contains("a"), "formula should reference address a");
}

#[test]
fn test_symbolic_heap_read_vc_freed_pointer() {
    let mut heap = SymbolicHeap::new("heap");
    let prov = heap.allocate("p");
    heap.free(prov);

    let vcs = heap.read_vc("p", "test_fn", &SourceSpan::default());
    // Should have a use-after-free VC
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("use-after-free")
        )
    }));
}

#[test]
fn test_symbolic_heap_read_vc_valid_pointer() {
    let mut heap = SymbolicHeap::new("heap");
    let _prov = heap.allocate("p");

    let vcs = heap.read_vc("p", "test_fn", &SourceSpan::default());
    // Should NOT have use-after-free, but should have standard deref checks
    assert!(!vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("use-after-free")
        )
    }));
    // Should have null, alloc, align checks from deref_vc, plus bounds check
    assert!(vcs.len() >= 3, "should have at least 3 VCs for valid read");
}

#[test]
fn test_symbolic_heap_write_vc_read_only_pointer() {
    let mut heap = SymbolicHeap::new("heap");
    let prov = ProvenanceId(1);
    let ptr = SymbolicPointer::new("ro", prov, PointerPermission::ReadOnly);
    heap.track_pointer(ptr);

    let vcs = heap.write_vc("ro", &val(42), "test_fn", &SourceSpan::default());
    // Should have a permission denied VC
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("permission denied")
        )
    }));
}

#[test]
fn test_symbolic_heap_write_vc_freed_pointer() {
    let mut heap = SymbolicHeap::new("heap");
    let prov = heap.allocate("p");
    heap.free(prov);

    let vcs = heap.write_vc("p", &val(42), "test_fn", &SourceSpan::default());
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("use-after-free")
        )
    }));
}

// ── Frame rule tests ─────────────────────────────────────────────────

#[test]
fn test_apply_frame_rule() {
    let pre = SepFormula::points_to(addr("p"), val(1));
    let post = SepFormula::points_to(addr("p"), val(2));
    let frame = SepFormula::points_to(addr("q"), val(99));

    let (framed_pre, framed_post) = apply_frame_rule(&pre, &post, &frame);

    // Framed pre should be: (p |-> 1) * (q |-> 99)
    assert_eq!(framed_pre.cell_count(), 2);
    // Framed post should be: (p |-> 2) * (q |-> 99)
    assert_eq!(framed_post.cell_count(), 2);
}

#[test]
fn test_apply_frame_rule_emp_frame() {
    let pre = SepFormula::points_to(addr("p"), val(1));
    let post = SepFormula::points_to(addr("p"), val(2));

    let (framed_pre, framed_post) = apply_frame_rule(&pre, &post, &SepFormula::Emp);

    // With emp frame, the framed versions are P * emp and Q * emp
    // which is logically equivalent to P and Q (but structurally wrapped)
    assert_eq!(framed_pre.cell_count(), 1);
    assert_eq!(framed_post.cell_count(), 1);
}

#[test]
fn test_encode_framed_unsafe_block() {
    let pre = SepFormula::points_to(addr("p"), val(1));
    let post = SepFormula::points_to(addr("p"), val(2));
    let frame = SepFormula::points_to(addr("q"), val(99));

    let vcs =
        encode_framed_unsafe_block("test_fn", &pre, &post, &frame, &SourceSpan::default(), "heap");

    // Should have: pre VC + post VC + frame preservation VC
    assert_eq!(vcs.len(), 3, "framed block should produce 3 VCs");

    // Third VC should be frame preservation
    assert!(matches!(
        &vcs[2].kind,
        VcKind::Assertion { message } if message.contains("frame preservation")
    ));
}

#[test]
fn test_encode_framed_unsafe_block_emp_frame() {
    let pre = SepFormula::points_to(addr("p"), val(1));
    let post = SepFormula::points_to(addr("p"), val(2));

    let vcs = encode_framed_unsafe_block(
        "test_fn",
        &pre,
        &post,
        &SepFormula::Emp,
        &SourceSpan::default(),
        "heap",
    );

    // With emp frame, no frame preservation VC (no frame addresses)
    assert_eq!(vcs.len(), 2, "emp frame should produce only 2 VCs");
}

#[test]
fn test_frame_rule_preserves_disjointness() {
    let pre = SepFormula::points_to(addr("p"), val(1));
    let post = SepFormula::points_to(addr("p"), val(2));
    let frame = SepFormula::points_to(addr("q"), val(99));

    let (framed_pre, _framed_post) = apply_frame_rule(&pre, &post, &frame);
    let fol = sep_to_formula(&framed_pre, "heap");

    // The FOL should contain disjointness: p != q
    match &fol {
        Formula::And(terms) => {
            assert_eq!(terms.len(), 3, "star should produce 3-element And");
            // Third element should enforce p != q
            assert!(matches!(&terms[2], Formula::Not(_)), "disjointness should be Not(Eq(p, q))");
        }
        other => panic!("expected And, got: {other:?}"),
    }
}

// ── UnsafeOpKind integration tests ───────────────────────────────────

#[test]
fn test_vcs_from_unsafe_op_raw_deref() {
    let op = UnsafeOpKind::RawPointerDeref { pointer_name: "raw_ptr".to_string() };
    let vcs = vcs_from_unsafe_op(&op, "test_fn", &SourceSpan::default());
    assert_eq!(vcs.len(), 3, "raw deref should produce 3 VCs");
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("null check")
        )
    }));
}

#[test]
fn test_vcs_from_unsafe_op_transmute() {
    let op = UnsafeOpKind::Transmute { callee: "std::mem::transmute".to_string() };
    let vcs = vcs_from_unsafe_op(&op, "test_fn", &SourceSpan::default());
    assert_eq!(vcs.len(), 3, "transmute should produce 3 VCs");
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("layout")
        )
    }));
}

#[test]
fn test_vcs_from_unsafe_op_ffi_call() {
    let op = UnsafeOpKind::FfiCall { callee: "libc::ffi::write".to_string() };
    let vcs = vcs_from_unsafe_op(&op, "test_fn", &SourceSpan::default());
    assert!(vcs.len() >= 2, "FFI call should produce at least 2 VCs");
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("null pointer")
        )
    }));
}

#[test]
fn test_vcs_from_unsafe_op_unsafe_fn_call_ptr_read() {
    let op = UnsafeOpKind::UnsafeFnCall { callee: "std::ptr::read".to_string() };
    let vcs = vcs_from_unsafe_op(&op, "test_fn", &SourceSpan::default());
    assert_eq!(vcs.len(), 3, "ptr::read should produce 3 deref VCs");
}

#[test]
fn test_vcs_from_unsafe_op_unsafe_fn_call_ptr_write() {
    let op = UnsafeOpKind::UnsafeFnCall { callee: "std::ptr::write".to_string() };
    let vcs = vcs_from_unsafe_op(&op, "test_fn", &SourceSpan::default());
    // 3 deref VCs + 1 write permission = 4 (the post-write consistency VC was removed
    // as a content-free tautology — see `raw_write_vc`).
    assert_eq!(vcs.len(), 4, "ptr::write should produce 4 VCs (deref + write permission)");
}

#[test]
fn test_vcs_from_unsafe_op_unsafe_fn_call_generic() {
    let op = UnsafeOpKind::UnsafeFnCall { callee: "std::alloc::alloc".to_string() };
    let vcs = vcs_from_unsafe_op(&op, "test_fn", &SourceSpan::default());
    assert_eq!(vcs.len(), 1, "generic unsafe fn should produce 1 conservative VC");
    assert!(matches!(vcs[0].formula, Formula::Bool(true)));
}

#[test]
fn test_vcs_from_unsafe_op_address_of() {
    let op = UnsafeOpKind::RawAddressOf { mutable: true, place_name: "_2".to_string() };
    let vcs = vcs_from_unsafe_op(&op, "test_fn", &SourceSpan::default());
    assert_eq!(vcs.len(), 1, "address_of should produce 1 VC");
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("&raw mut")
        )
    }));
}

#[test]
fn test_vcs_from_unsafe_op_address_of_const() {
    let op = UnsafeOpKind::RawAddressOf { mutable: false, place_name: "_3".to_string() };
    let vcs = vcs_from_unsafe_op(&op, "test_fn", &SourceSpan::default());
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("&raw const")
        )
    }));
}

#[test]
fn test_vcs_from_unsafe_op_slice_from_raw_parts() {
    let op = UnsafeOpKind::UnsafeFnCall { callee: "std::slice::from_raw_parts".to_string() };
    let vcs = vcs_from_unsafe_op(&op, "test_fn", &SourceSpan::default());
    // 3 deref VCs + 1 real allocation-bounds obligation = 4
    assert_eq!(vcs.len(), 4, "from_raw_parts should produce 4 VCs");
    // The length obligation is now a real CopyBoundsViolation (`len > alloc_size`),
    // not the old vacuous `len < 0` assertion that could never catch anything.
    assert!(
        vcs.iter().any(|vc| {
            matches!(
                &vc.kind,
                VcKind::CopyBoundsViolation { callee, direction, .. }
                    if callee.contains("from_raw_parts") && direction == "src"
            )
        }),
        "from_raw_parts must emit a real CopyBoundsViolation bounds obligation"
    );
}

// ── FFI and unsafe fn call sep vc tests ──────────────────────────────

#[test]
fn test_ffi_call_sep_vc() {
    let vcs = ffi_call_sep_vc("test_fn", "libc::write", &SourceSpan::default());
    assert_eq!(vcs.len(), 2);
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("null pointer")
        )
    }));
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("heap invariant")
        )
    }));
}

#[test]
fn test_address_of_sep_vc_mutable() {
    let vcs = address_of_sep_vc("test_fn", "_2", true, &SourceSpan::default());
    assert_eq!(vcs.len(), 1);
    assert!(matches!(
        &vcs[0].kind,
        VcKind::Assertion { message } if message.contains("&raw mut")
    ));
}

#[test]
fn test_address_of_sep_vc_const() {
    let vcs = address_of_sep_vc("test_fn", "_2", false, &SourceSpan::default());
    assert_eq!(vcs.len(), 1);
    assert!(matches!(
        &vcs[0].kind,
        VcKind::Assertion { message } if message.contains("&raw const")
    ));
}

// ── All new VCs are L0Safety ─────────────────────────────────────────

#[test]
fn test_all_unsafe_op_vcs_are_l0_safety() {
    let ops: Vec<UnsafeOpKind> = vec![
        UnsafeOpKind::RawPointerDeref { pointer_name: "p".to_string() },
        UnsafeOpKind::Transmute { callee: "std::mem::transmute".to_string() },
        UnsafeOpKind::FfiCall { callee: "libc::ffi::write".to_string() },
        UnsafeOpKind::UnsafeFnCall { callee: "std::ptr::read".to_string() },
        UnsafeOpKind::RawAddressOf { mutable: true, place_name: "_1".to_string() },
    ];

    for op in &ops {
        let vcs = vcs_from_unsafe_op(op, "f", &SourceSpan::default());
        for vc in &vcs {
            assert_eq!(
                vc.kind.proof_level(),
                trust_types::ProofLevel::L0Safety,
                "VC from {op:?} should be L0Safety"
            );
        }
    }
}
