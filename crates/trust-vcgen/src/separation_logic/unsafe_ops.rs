// trust_vcgen/separation_logic/unsafe_ops.rs: UnsafeOpKind integration and specialized VCs
//
// Bridges the unsafe operation classifier from unsafe_vc.rs into the
// separation logic verification framework. Generates VCs for FFI calls,
// unsafe function calls, and raw address-of operations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

#[cfg(test)]
use super::vc_gen::transmute_vc;
use super::vc_gen::{deref_vc, raw_write_vc};

// ────────────────────────────────────────────────────────────────────────────
// Unsafe operation classification (test-only: no production code constructs these)
// ────────────────────────────────────────────────────────────────────────────

/// Classification of detected unsafe operations in MIR.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum UnsafeOpKind {
    /// Raw pointer dereference via Deref projection.
    RawPointerDeref { pointer_name: String },
    /// Call to a known transmute function (mem::transmute, etc.).
    Transmute { callee: String },
    /// Call to a known FFI/extern function.
    FfiCall { callee: String },
    /// Call to other known unsafe functions (ptr::read, ptr::write, etc.).
    UnsafeFnCall { callee: String },
    /// AddressOf rvalue (&raw const / &raw mut).
    RawAddressOf { mutable: bool, place_name: String },
}

#[cfg(test)]
impl UnsafeOpKind {
    /// Human-readable description for the VcKind::UnsafeOperation desc field.
    pub(crate) fn description(&self) -> String {
        match self {
            UnsafeOpKind::RawPointerDeref { pointer_name } => {
                format!("raw pointer dereference of `{pointer_name}`")
            }
            UnsafeOpKind::Transmute { callee } => {
                format!("transmute via `{callee}`")
            }
            UnsafeOpKind::FfiCall { callee } => {
                format!("FFI call to `{callee}`")
            }
            UnsafeOpKind::UnsafeFnCall { callee } => {
                format!("unsafe function call to `{callee}`")
            }
            UnsafeOpKind::RawAddressOf { mutable, place_name } => {
                let kind = if *mutable { "&raw mut" } else { "&raw const" };
                format!("{kind} on `{place_name}`")
            }
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// UnsafeOpKind integration (test-only)
// ────────────────────────────────────────────────────────────────────────────

/// Generate separation logic VCs from an `UnsafeOpKind` classification.
#[cfg(test)]
#[must_use]
pub(crate) fn vcs_from_unsafe_op(
    op: &UnsafeOpKind,
    func_name: &str,
    span: &SourceSpan,
) -> Vec<VerificationCondition> {
    match op {
        UnsafeOpKind::RawPointerDeref { pointer_name } => deref_vc(func_name, pointer_name, span),
        UnsafeOpKind::Transmute { callee } => {
            let (src, dst) = parse_transmute_types(callee);
            transmute_vc(func_name, &src, &dst, span)
        }
        UnsafeOpKind::FfiCall { callee } => ffi_call_sep_vc(func_name, callee, span),
        UnsafeOpKind::UnsafeFnCall { callee } => unsafe_fn_call_sep_vc(func_name, callee, span),
        UnsafeOpKind::RawAddressOf { mutable, place_name } => {
            address_of_sep_vc(func_name, place_name, *mutable, span)
        }
    }
}

#[cfg(test)]
fn parse_transmute_types(callee: &str) -> (String, String) {
    let _ = callee;
    ("Src".to_string(), "Dst".to_string())
}

/// Generate separation logic VCs for an FFI call.
///
/// FFI calls cross the Rust safety boundary entirely. We generate VCs for:
/// 1. Pointer arguments must be non-null
/// 2. Pointer arguments must point to valid allocations
/// 3. The callee is assumed to have arbitrary side effects on the heap
#[must_use]
pub fn ffi_call_sep_vc(
    func_name: &str,
    callee: &str,
    span: &SourceSpan,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // VC 1: FFI pointer argument null check
    let ffi_ptr = Formula::Var(
        super::generated_symbol(&format!("ffi_ptr_arg_{}", callee.replace("::", "_"))),
        Sort::Int,
    );
    vcs.push(VerificationCondition {
        kind: VcKind::Assertion {
            message: format!("[unsafe:sep:ffi] null pointer argument check for {callee}"),
        },
        function: func_name.into(),
        location: span.clone(),
        formula: Formula::Eq(Box::new(ffi_ptr), Box::new(Formula::Int(0))),
        contract_metadata: None,
        obligation: None,
    });

    // VC 2: FFI may invalidate heap assumptions (conservative)
    vcs.push(VerificationCondition {
        kind: VcKind::Assertion {
            message: format!("[unsafe:sep:ffi] heap invariant after {callee} (unverified)"),
        },
        function: func_name.into(),
        location: span.clone(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    });

    vcs
}

/// Generate separation logic VCs for an unsafe function call
/// (e.g., `ptr::read`, `ptr::write`, `slice::from_raw_parts`).
#[must_use]
pub fn unsafe_fn_call_sep_vc(
    func_name: &str,
    callee: &str,
    span: &SourceSpan,
) -> Vec<VerificationCondition> {
    let lower = callee.to_lowercase();
    let mut vcs = Vec::new();

    if lower.contains("ptr::read") || lower.contains("ptr::copy") {
        // ptr::read requires a valid, aligned, non-null source pointer.
        let ptr_name = format!("arg0_{}", callee.replace("::", "_"));
        vcs.extend(deref_vc(func_name, &ptr_name, span));
    } else if lower.contains("ptr::write") {
        // ptr::write requires a valid, aligned, non-null, writable destination.
        let ptr_name = format!("arg0_{}", callee.replace("::", "_"));
        let value = Formula::Var(super::generated_symbol("write_value"), Sort::Int);
        vcs.extend(raw_write_vc(func_name, &ptr_name, &value, span));
    } else if lower.contains("slice::from_raw_parts") {
        // from_raw_parts requires non-null pointer + valid length.
        let ptr_name = format!("arg0_{}", callee.replace("::", "_"));
        vcs.extend(deref_vc(func_name, &ptr_name, span));

        // The slice must not claim more elements than the backing allocation
        // holds: `ptr[0..len]` must lie within `[base, base + alloc_size)`.
        //
        // Previously this was `len < 0`, which is vacuously UNSAT for `usize`
        // and therefore never caught anything. The real obligation relates the
        // requested length to the allocation's size. Violation (prove UNSAT):
        //   len > alloc_size.
        let suffix = callee.replace("::", "_");
        let len = Formula::Var(super::generated_symbol(&format!("len_{suffix}")), Sort::Int);
        let alloc_size =
            Formula::Var(super::generated_symbol(&format!("alloc_size_{suffix}")), Sort::Int);
        vcs.push(VerificationCondition {
            kind: VcKind::CopyBoundsViolation {
                callee: callee.to_string(),
                direction: "src".to_string(),
                detail: format!("slice length may exceed the backing allocation in {func_name}"),
            },
            function: func_name.into(),
            location: span.clone(),
            // len > alloc_size
            formula: Formula::Gt(Box::new(len), Box::new(alloc_size)),
            contract_metadata: None,
            obligation: None,
        });
    } else {
        // Generic unsafe fn: conservative flag.
        vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!("[unsafe:sep:call] unsafe function call to {callee} (unverified)"),
            },
            function: func_name.into(),
            location: span.clone(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        });
    }

    vcs
}

/// Generate separation logic VCs for `&raw const`/`&raw mut` (AddressOf).
///
/// Taking a raw pointer from a place does not itself cause UB, but it
/// creates a pointer whose validity depends on the source place remaining
/// live and valid. We generate a VC checking that the source is live.
#[must_use]
pub fn address_of_sep_vc(
    func_name: &str,
    place_name: &str,
    mutable: bool,
    span: &SourceSpan,
) -> Vec<VerificationCondition> {
    let kind_str = if mutable { "&raw mut" } else { "&raw const" };

    vec![VerificationCondition {
        kind: VcKind::Assertion {
            message: format!(
                "[unsafe:sep:addr_of] {kind_str} on `{place_name}` (source liveness unverified)"
            ),
        },
        function: func_name.into(),
        location: span.clone(),
        // Conservative: source liveness cannot be verified without
        // full lifetime analysis at this layer.
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }]
}
