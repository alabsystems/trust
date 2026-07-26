// trust_vcgen/unsafe_verify/verifier.rs: Stateful unsafe VC generation
//
// UnsafeVerifier accumulates context (detected blocks, safety comments, type info)
// and produces a comprehensive set of VCs covering all unsafe operations.
// All items in this module are only exercised from tests; production code uses
// the simpler check_unsafe() path in detection.rs.
//
// Part of #79, #137: Unsafe code verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![cfg_attr(not(test), allow(unused))]
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;
use trust_types::fx::FxHashSet;

use super::detection::{
    attach_safety_comments, detect_unsafe_blocks, generate_safety_vcs, has_raw_deref,
};
use super::{UnsafeBlock, UnsafeVc, UnsafeVcKind};

/// Stateful verifier that generates VCs for all unsafe blocks in a function.
///
/// Accumulates context (detected blocks, safety comments, type info) and
/// produces a comprehensive set of VCs covering all unsafe operations.
pub(crate) struct UnsafeVerifier<'a> {
    func: &'a VerifiableFunction,
    blocks: Vec<UnsafeBlock>,
    comments: Vec<(SourceSpan, String)>,
}

impl<'a> UnsafeVerifier<'a> {
    /// Create a new verifier for the given function.
    #[must_use]
    pub(crate) fn new(func: &'a VerifiableFunction) -> Self {
        Self { func, blocks: detect_unsafe_blocks(func), comments: Vec::new() }
    }

    /// Attach source comments for SAFETY claim extraction.
    #[must_use]
    pub(crate) fn with_comments(mut self, comments: Vec<(SourceSpan, String)>) -> Self {
        self.comments = comments;
        self
    }

    /// Number of detected unsafe blocks.
    #[must_use]
    pub(crate) fn block_count(&self) -> usize {
        self.blocks.len()
    }

    /// Generate all unsafe VCs, returning both the solver-facing VCs and their
    /// categorized unsafe kinds.
    #[must_use]
    pub(crate) fn generate(&mut self) -> Vec<UnsafeVc> {
        attach_safety_comments(&mut self.blocks, &self.comments);

        let mut result = Vec::new();

        // Existing safety-claim VCs
        let claim_vcs = generate_safety_vcs(self.func, &self.blocks, &FxHashSet::default());
        for vc in claim_vcs {
            let unsafe_kind = classify_vc_from_assertion(&vc);
            result.push(UnsafeVc { vc, unsafe_kind });
        }

        // Additional typed VCs from block analysis
        for block in &self.blocks {
            self.generate_block_vcs(block, &mut result);
        }

        result
    }

    /// Generate typed VCs for a single unsafe block.
    fn generate_block_vcs(&self, block: &UnsafeBlock, out: &mut Vec<UnsafeVc>) {
        let mir_block = self.func.body.blocks.iter().find(|b| b.id == block.block_id);
        let Some(mir_block) = mir_block else { return };

        // Check terminator for specific unsafe patterns
        if let Terminator::Call { func: callee, span, .. } = &mir_block.terminator {
            let lower = callee.to_lowercase();

            // Transmute detection
            if lower.contains("mem::transmute") {
                Self::emit_transmute_vcs(&self.func.name, callee, span, out);
            }

            // FFI call detection
            if lower.contains("::ffi::") || lower.contains("extern") {
                Self::emit_ffi_vcs(&self.func.name, callee, span, out);
            }
        }

        // Check statements for raw pointer derefs
        for stmt in &mir_block.stmts {
            if let Statement::Assign { rvalue, span, .. } = stmt
                && has_raw_deref(self.func, rvalue)
            {
                Self::emit_raw_deref_vcs(&self.func.name, rvalue, span, out);
            }
        }
    }

    /// Emit VCs for a raw pointer dereference.
    fn emit_raw_deref_vcs(
        func_name: &str,
        rvalue: &Rvalue,
        span: &SourceSpan,
        out: &mut Vec<UnsafeVc>,
    ) {
        let ptr_expr = deref_operand_name(rvalue);
        let ptr_var = Formula::Var(
            super::generated_unsafe_symbol(&format!("deref_ptr_{ptr_expr}")),
            Sort::Int,
        );

        // VC 1: Non-null check
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:deref] null check for *{ptr_expr}"),
                },
                function: func_name.into(),
                location: span.clone(),
                formula: Formula::Eq(Box::new(ptr_var.clone()), Box::new(Formula::Int(0))),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::RawPointerDeref { pointer_expr: format!("*{ptr_expr}") },
        });

        // VC 2: Alignment check (ptr % align == 0)
        //
        // SOUNDNESS FIX: The old code used an unconstrained `align_*`
        // variable. The solver could set align to 1 (everything is 1-aligned),
        // making `ptr % 1 == 0` trivially true, discharging the check
        // vacuously. Without actual type alignment info, we conservatively
        // report "cannot verify alignment".
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:deref] alignment check (unverified) for *{ptr_expr}"),
                },
                function: func_name.into(),
                location: span.clone(),
                // Always SAT = conservatively "cannot verify alignment"
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::RawPointerDeref { pointer_expr: format!("*{ptr_expr}") },
        });

        // VC 3: Provenance/bounds check — pointer must be within allocation
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:deref] bounds check (unverified) for *{ptr_expr}"),
                },
                function: func_name.into(),
                location: span.clone(),
                // Always SAT = conservatively "cannot verify bounds"
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::RawPointerDeref { pointer_expr: format!("*{ptr_expr}") },
        });
    }

    /// Emit VCs for a transmute call.
    fn emit_transmute_vcs(
        func_name: &str,
        _callee: &str,
        span: &SourceSpan,
        out: &mut Vec<UnsafeVc>,
    ) {
        let from_ty = "T_src".to_string();
        let to_ty = "T_dst".to_string();

        // VC 1: Layout compatibility — size_of::<Src>() == size_of::<Dst>()
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:transmute] layout compatibility (unverified): size_of({from_ty}) == size_of({to_ty})"
                    ),
                },
                function: func_name.into(),
                location: span.clone(),
                // Always SAT = conservatively "cannot verify layout compatibility"
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::Transmute {
                from_ty: from_ty.clone(),
                to_ty: to_ty.clone(),
            },
        });

        // VC 2: Validity invariant — the bit pattern must be valid for the target type
        //
        // SOUNDNESS FIX: The old code used an unconstrained boolean
        // `transmute_valid_*` wrapped in Not(). Solver trivially discharged
        // it by setting the var to true. Now conservatively always SAT.
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:transmute] validity invariant (unverified): bit pattern valid for {to_ty}"
                    ),
                },
                function: func_name.into(),
                location: span.clone(),
                // Always SAT = conservatively "cannot verify validity"
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::Transmute { from_ty, to_ty },
        });
    }

    /// Emit VCs for an FFI call.
    fn emit_ffi_vcs(func_name: &str, callee: &str, span: &SourceSpan, out: &mut Vec<UnsafeVc>) {
        // VC 1: FFI precondition check
        //
        // SOUNDNESS FIX: The old code used an unconstrained boolean
        // `ffi_precond_*` wrapped in Not(). Solver trivially discharged it.
        // Now conservatively always SAT = "cannot verify FFI precondition".
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:ffi] precondition (unverified) for {callee}"),
                },
                function: func_name.into(),
                location: span.clone(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::FfiCall { callee: callee.to_string() },
        });

        // VC 2: FFI postcondition — return value satisfies expected invariant
        //
        // SOUNDNESS FIX: Same unconstrained boolean pattern.
        // Conservatively always SAT = "cannot verify FFI postcondition".
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:ffi] postcondition (unverified) for {callee}"),
                },
                function: func_name.into(),
                location: span.clone(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::FfiCall { callee: callee.to_string() },
        });

        // VC 3: FFI null pointer check on pointer-type arguments
        let null_var = Formula::Var(
            super::generated_unsafe_symbol(&format!("ffi_ptr_arg_{}", callee.replace("::", "_"))),
            Sort::Int,
        );
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:ffi] null pointer argument check for {callee}"),
                },
                function: func_name.into(),
                location: span.clone(),
                formula: Formula::Eq(Box::new(null_var), Box::new(Formula::Int(0))),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::FfiCall { callee: callee.to_string() },
        });
    }
}

/// Top-level entry point for comprehensive unsafe VC generation.
///
/// Returns categorized `UnsafeVc` items that include both the solver VC
/// and the `UnsafeVcKind` classification. This is the preferred API for
/// tools that need rich diagnostics; for the simple `Vec<VerificationCondition>`
/// path, use `check_unsafe()` instead.
#[must_use]
pub(crate) fn generate_unsafe_vcs(
    func: &VerifiableFunction,
    comments: &[(SourceSpan, String)],
) -> Vec<UnsafeVc> {
    let mut verifier = UnsafeVerifier::new(func).with_comments(comments.to_vec());
    verifier.generate()
}

/// Classify a VC generated from a safety-claim assertion into an `UnsafeVcKind`.
pub(crate) fn classify_vc_from_assertion(vc: &VerificationCondition) -> UnsafeVcKind {
    let msg = match &vc.kind {
        VcKind::Assertion { message } => message.as_str(),
        _ => "",
    };
    let lower = msg.to_lowercase();

    if lower.contains("transmute") {
        UnsafeVcKind::Transmute { from_ty: "unknown".into(), to_ty: "unknown".into() }
    } else if lower.contains("ffi") || lower.contains("extern") {
        UnsafeVcKind::FfiCall { callee: "unknown".into() }
    } else {
        // Default: raw pointer deref (most common unsafe pattern)
        UnsafeVcKind::RawPointerDeref { pointer_expr: "unknown".into() }
    }
}

/// Extract a human-readable operand name from a deref rvalue.
pub(crate) fn deref_operand_name(rvalue: &Rvalue) -> String {
    match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
            format!("_{}", place.local)
        }
        Rvalue::Ref { place, .. } => {
            format!("_{}", place.local)
        }
        _ => "unknown".to_string(),
    }
}
