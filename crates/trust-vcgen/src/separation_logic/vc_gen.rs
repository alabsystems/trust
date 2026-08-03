// trust_vcgen/separation_logic/vc_gen.rs: Common unsafe operation VC generators
//
// Generates verification conditions for raw pointer dereference, raw pointer
// write, and transmute operations. These are the core building blocks used
// by both the symbolic heap and the UnsafeOpKind integration.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

// ────────────────────────────────────────────────────────────────────────────
// Common unsafe operation VCs
// ────────────────────────────────────────────────────────────────────────────

/// Generate VCs for a raw pointer dereference `*ptr`.
///
/// Safety requirements for `*ptr`:
/// 1. `ptr` must be non-null
/// 2. `ptr` must point to a valid allocation (heap contains an entry)
/// 3. `ptr` must be aligned (ptr % align == 0)
///
/// The returned VCs encode these as separation logic constraints translated
/// to FOL. If any VC is SAT, the dereference may be unsafe.
#[must_use]
pub fn deref_vc(func_name: &str, ptr_name: &str, span: &SourceSpan) -> Vec<VerificationCondition> {
    let ptr = Formula::Var(super::generated_symbol(&format!("ptr_{ptr_name}")), Sort::Int);
    let heap_var = super::generated_symbol("heap");
    let heap = Formula::Var(heap_var, Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));

    let mut vcs = Vec::new();

    // VC 1: Non-null check -- ptr == 0 is a violation
    vcs.push(VerificationCondition {
        kind: VcKind::Assertion {
            message: format!("[unsafe:sep:deref] null check for *{ptr_name}"),
        },
        function: func_name.into(),
        location: span.clone(),
        formula: Formula::Eq(Box::new(ptr.clone()), Box::new(Formula::Int(0))),
        contract_metadata: None,
        obligation: None,
    });

    // VC 2: Valid allocation check -- the heap must have an entry at ptr.
    // We encode this as: the value at ptr in the heap is not the sentinel
    // "unallocated" value. Using Select(heap, ptr) == UNALLOC_SENTINEL.
    // Convention: UNALLOC_SENTINEL = -1 (addresses are non-negative).
    let unalloc_sentinel = Formula::Int(-1);
    vcs.push(VerificationCondition {
        kind: VcKind::Assertion {
            message: format!("[unsafe:sep:deref] allocation validity for *{ptr_name}"),
        },
        function: func_name.into(),
        location: span.clone(),
        formula: Formula::Eq(
            Box::new(Formula::Select(Box::new(heap), Box::new(ptr.clone()))),
            Box::new(unalloc_sentinel),
        ),
        contract_metadata: None,
        obligation: None,
    });

    // VC 3: Alignment check -- ptr % align != 0 is a violation.
    // Without concrete type info, we use a symbolic alignment variable.
    //
    // Trust TODO (one of the two remaining `noOverflow_*` unknowns — full plan in
    // ~/.claude/.../memory/project_nooverflow_deep_closure.md cont.5/17): this
    // symbolic-divisor `ptr % align` is NONLINEAR, so the VC stays `unknown` for a
    // box-good pointer even though the box is aligned by construction. Discharge it
    // by substituting the CONCRETE pointee alignment K (a power of two) for `align`
    // — recoverable from `convert::box_allocator_alignment` in trust-mir-extract —
    // so the check becomes the decidable `ptr & (K-1) == 0` and proves. SOUNDNESS
    // GATE: only when `K >= required` (the exact gate the misalign-assert discharge
    // in `convert::discharge_provably_safe_pointer_asserts` already uses), so a
    // re-cast under-aligned deref stays caught.
    let align = Formula::Var(super::generated_symbol(&format!("align_{ptr_name}")), Sort::Int);
    vcs.push(VerificationCondition {
        kind: VcKind::Assertion {
            message: format!("[unsafe:sep:deref] alignment check for *{ptr_name}"),
        },
        function: func_name.into(),
        location: span.clone(),
        formula: Formula::And(vec![
            // align > 0 (alignment is always positive)
            Formula::Gt(Box::new(align.clone()), Box::new(Formula::Int(0))),
            // ptr % align != 0
            Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Rem(Box::new(ptr), Box::new(align))),
                Box::new(Formula::Int(0)),
            ))),
        ]),
        contract_metadata: None,
        obligation: None,
    });

    vcs
}

/// Generate VCs for a raw pointer write `*ptr = value`.
///
/// Safety requirements for `*ptr = value`:
/// 1. All dereference requirements (non-null, valid alloc, aligned)
/// 2. The pointer must have write permission (not borrowed immutably)
/// 3. After write, the heap is updated: `Store(heap, ptr, value)`
///
/// Returns VCs plus a formula representing the post-state heap.
#[must_use]
pub fn raw_write_vc(
    func_name: &str,
    ptr_name: &str,
    value_formula: &Formula,
    span: &SourceSpan,
) -> Vec<VerificationCondition> {
    let mut vcs = deref_vc(func_name, ptr_name, span);

    // VC 4: Write permission check -- the pointer must not be immutably borrowed.
    // Modeled as: `writable_<ptr>` must be true.
    let writable =
        Formula::Var(super::generated_symbol(&format!("writable_{ptr_name}")), Sort::Bool);
    vcs.push(VerificationCondition {
        kind: VcKind::Assertion {
            message: format!("[unsafe:sep:write] write permission for *{ptr_name}"),
        },
        function: func_name.into(),
        location: span.clone(),
        formula: Formula::Not(Box::new(writable)),
        contract_metadata: None,
        obligation: None,
    });

    // (No post-write heap-consistency VC.) Read-over-write — "after `*ptr = value`,
    // reading `ptr` back yields `value`" — is `Select(Store(h, p, v), p) ≡ v`, a TRUE
    // theorem of the array model for EVERY write. It is a content-free tautology that
    // can never catch a bug, so emitting it as a verification obligation only creates
    // noise: the raw `Select(Store(...))` form mis-sorts a non-Int aggregate write (the
    // array procedure spuriously FAILs it), and the simplified reflexive `value != value`
    // form is a degenerate single-variable CHC the native trust-mc PDR runner fails to
    // discharge — both surface a SPURIOUS counterexample on a provably-safe write.
    // Dropping it loses no coverage (the property always holds) and removes the false
    // failure.
    let _ = value_formula;

    vcs
}

/// Generate VCs for a `mem::transmute::<Src, Dst>(value)` call.
///
/// Safety requirements for transmute:
/// 1. `size_of::<Src>() == size_of::<Dst>()` (layout compatibility)
/// 2. The bit pattern of `value` must satisfy `Dst`'s validity invariant
/// 3. The alignment of `Dst` must not exceed `Src`'s alignment
///
/// Type sizes are modeled as symbolic integer variables since we don't
/// have concrete type layout info at the VC generation level.
#[must_use]
pub fn transmute_vc(
    func_name: &str,
    src_ty: &str,
    dst_ty: &str,
    span: &SourceSpan,
) -> Vec<VerificationCondition> {
    let src_size = Formula::Var(super::generated_symbol(&format!("size_{src_ty}")), Sort::Int);
    let dst_size = Formula::Var(super::generated_symbol(&format!("size_{dst_ty}")), Sort::Int);
    let src_align = Formula::Var(super::generated_symbol(&format!("align_{src_ty}")), Sort::Int);
    let dst_align = Formula::Var(super::generated_symbol(&format!("align_{dst_ty}")), Sort::Int);

    let mut vcs = Vec::new();

    // VC 1: Layout compatibility -- size_of::<Src>() != size_of::<Dst>()
    // is a violation
    vcs.push(VerificationCondition {
        kind: VcKind::Assertion {
            message: format!(
                "[unsafe:sep:transmute] layout: size_of({src_ty}) != size_of({dst_ty})"
            ),
        },
        function: func_name.into(),
        location: span.clone(),
        formula: Formula::Not(Box::new(Formula::Eq(Box::new(src_size), Box::new(dst_size)))),
        contract_metadata: None,
        obligation: None,
    });

    // VC 2: Validity invariant -- the bit pattern must be valid for Dst.
    // Without concrete type info, we model this symbolically.
    let valid_bits = Formula::Var(
        super::generated_symbol(&format!("valid_bits_{src_ty}_as_{dst_ty}")),
        Sort::Bool,
    );
    vcs.push(VerificationCondition {
        kind: VcKind::Assertion {
            message: format!(
                "[unsafe:sep:transmute] validity: bits of {src_ty} invalid for {dst_ty}"
            ),
        },
        function: func_name.into(),
        location: span.clone(),
        formula: Formula::Not(Box::new(valid_bits)),
        contract_metadata: None,
        obligation: None,
    });

    // VC 3: Alignment compatibility -- align_of::<Dst>() > align_of::<Src>()
    // is a violation (transmute doesn't change alignment)
    vcs.push(VerificationCondition {
        kind: VcKind::Assertion {
            message: format!("[unsafe:sep:transmute] alignment: align({dst_ty}) > align({src_ty})"),
        },
        function: func_name.into(),
        location: span.clone(),
        formula: Formula::Gt(Box::new(dst_align), Box::new(src_align)),
        contract_metadata: None,
        obligation: None,
    });

    vcs
}
