// trust_vcgen/src/unsafe_vc.rs: Dedicated unsafe operation VC generation
//
// Detects unsafe operations in MIR (raw pointer dereferences, transmutes,
// FFI calls, inline assembly, AddressOf) and generates conservative VCs
// tagged with VcKind::UnsafeOperation. These VCs flag unsafe blocks for
// audit tracking without attempting to prove safety — the formula is
// Formula::Bool(true) (always SAT = always a finding).
//
// This module complements unsafe_verify.rs (which uses VcKind::Assertion
// with [unsafe:...] prefixes) by providing a first-class VcKind for
// unsafe operations, enabling proper routing, reporting, and clean
// certification support.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use std::fmt::Write;

    use trust_types::{
        BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, ProofLevel, Rvalue,
        SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
        VerificationCondition,
    };

    use crate::separation_logic::unsafe_ops::UnsafeOpKind;

    /// Detected unsafe operation with location metadata.
    struct DetectedUnsafeOp {
        kind: UnsafeOpKind,
        span: SourceSpan,
    }

    /// Scan a function for unsafe operations and return classified detections.
    fn detect_unsafe_ops(func: &VerifiableFunction) -> Vec<DetectedUnsafeOp> {
        let mut ops = Vec::new();

        for block in &func.body.blocks {
            // Check statements for raw pointer derefs and AddressOf
            for stmt in &block.stmts {
                if let Statement::Assign { rvalue, span, .. } = stmt {
                    detect_in_rvalue(rvalue, span, &mut ops);
                }
            }

            // Check terminator for unsafe calls
            if let Terminator::Call { func: callee, span, .. } = &block.terminator
                && let Some(op_kind) = classify_call(callee)
            {
                ops.push(DetectedUnsafeOp { kind: op_kind, span: span.clone() });
            }
        }

        ops
    }

    /// Detect unsafe operations in an rvalue.
    fn detect_in_rvalue(rvalue: &Rvalue, span: &SourceSpan, ops: &mut Vec<DetectedUnsafeOp>) {
        match rvalue {
            // Raw pointer dereference via Use/Ref with Deref projection
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
            | Rvalue::Ref { place, .. }
            | Rvalue::CopyForDeref(place)
                if has_deref_projection(place) =>
            {
                ops.push(DetectedUnsafeOp {
                    kind: UnsafeOpKind::RawPointerDeref { pointer_name: format_place(place) },
                    span: span.clone(),
                });
            }
            // AddressOf: &raw const / &raw mut
            Rvalue::AddressOf(mutable, place) => {
                ops.push(DetectedUnsafeOp {
                    kind: UnsafeOpKind::RawAddressOf {
                        mutable: *mutable,
                        place_name: format_place(place),
                    },
                    span: span.clone(),
                });
            }
            // Other rvalues are not unsafe operations
            _ => {}
        }
    }

    /// Check if a place has a Deref projection (indicates raw pointer dereference).
    fn has_deref_projection(place: &Place) -> bool {
        place.projections.iter().any(|p| matches!(p, Projection::Deref))
    }

    /// Format a place for human-readable output.
    fn format_place(place: &Place) -> String {
        let mut s = format!("_{}", place.local);
        for proj in &place.projections {
            match proj {
                Projection::Deref => s.push_str(".*"),
                Projection::Field(f) => {
                    s.push('.');
                    s.push_str(&f.to_string());
                }
                Projection::Index(i) => {
                    s.push('[');
                    s.push_str(&i.to_string());
                    s.push(']');
                }
                Projection::Downcast(v) => {
                    let _ = write!(s, "@variant({v})");
                }
                Projection::ConstantIndex { offset, min_length, from_end } => {
                    if *from_end {
                        let _ = write!(s, "[-{offset};min={min_length}]");
                    } else {
                        let _ = write!(s, "[{offset};min={min_length}]");
                    }
                }
                Projection::Subslice { from, to, from_end } => {
                    if *from_end {
                        let _ = write!(s, "[{from}..-{to}]");
                    } else {
                        let _ = write!(s, "[{from}..{to}]");
                    }
                }
                // Projection is #[non_exhaustive]; unknown variants
                // get a generic representation.
                _ => s.push_str(".?"),
            }
        }
        s
    }

    /// Classify a function call as an unsafe operation, if applicable.
    fn classify_call(callee: &str) -> Option<UnsafeOpKind> {
        let lower = callee.to_lowercase();

        // Transmute family
        if lower.contains("mem::transmute") || lower.contains("mem::transmute_copy") {
            return Some(UnsafeOpKind::Transmute { callee: callee.to_string() });
        }

        // FFI / extern calls
        if lower.contains("::ffi::")
            || lower.contains("extern \"c\"")
            || lower.contains("extern \"system\"")
        {
            return Some(UnsafeOpKind::FfiCall { callee: callee.to_string() });
        }

        // Unsafe pointer operations
        const UNSAFE_FN_PATTERNS: &[&str] = &[
            "ptr::read",
            "ptr::write",
            "ptr::read_volatile",
            "ptr::write_volatile",
            "ptr::copy",
            "ptr::copy_nonoverlapping",
            "ptr::swap",
            "ptr::replace",
            "ptr::drop_in_place",
            "ptr::read_unaligned",
            "ptr::write_unaligned",
            "slice::from_raw_parts",
            "slice::from_raw_parts_mut",
            "str::from_utf8_unchecked",
            "string::from_raw_parts",
            "mem::zeroed",
            "mem::uninitialized",
            "alloc::alloc",
            "alloc::dealloc",
            "alloc::realloc",
            "intrinsics::",
        ];

        if UNSAFE_FN_PATTERNS.iter().any(|p| lower.contains(&p.to_lowercase())) {
            return Some(UnsafeOpKind::UnsafeFnCall { callee: callee.to_string() });
        }

        None
    }

    /// Generate conservative VCs for all unsafe operations in a function.
    ///
    /// Each detected unsafe operation produces a VC with:
    /// - `kind`: `VcKind::UnsafeOperation { desc }` describing the operation
    /// - `formula`: `Formula::Bool(true)` — always SAT, meaning this VC
    ///   conservatively flags the operation without attempting verification.
    ///   Solvers will report "counterexample found" which means "this unsafe
    ///   operation exists and was not proved safe."
    ///
    /// This is the intended behavior: unsafe operations are flagged for human
    /// review and audit tracking, not automatically proved.
    #[must_use]
    fn generate_unsafe_operation_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
        let ops = detect_unsafe_ops(func);

        ops.into_iter()
            .map(|op| VerificationCondition {
                kind: VcKind::UnsafeOperation { desc: op.kind.description() },
                function: func.name.as_str().into(),
                location: op.span,
                // Conservative: Formula::Bool(true) is always SAT, so this VC
                // will always be reported as "unproved" — which is correct for
                // unsafe operations that need manual review.
                formula: Formula::Bool(true),
                contract_metadata: None,
            })
            .collect()
    }

    fn empty_span() -> SourceSpan {
        SourceSpan::default()
    }

    fn make_func(blocks: Vec<BasicBlock>) -> VerifiableFunction {
        VerifiableFunction {
            name: "test_fn".to_string(),
            def_path: "test::test_fn".to_string(),
            span: empty_span(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                arg_count: 0,
                blocks,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_detect_raw_pointer_deref() {
        let func = make_func(vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Copy(Place {
                    local: 2,
                    projections: vec![Projection::Deref],
                })),
                span: empty_span(),
            }],
            terminator: Terminator::Return,
        }]);

        let vcs = generate_unsafe_operation_vcs(&func);
        assert_eq!(vcs.len(), 1);
        match &vcs[0].kind {
            VcKind::UnsafeOperation { desc } => {
                assert!(desc.contains("raw pointer dereference"), "desc: {desc}");
            }
            other => panic!("expected UnsafeOperation, got: {other:?}"),
        }
        assert_eq!(vcs[0].kind.proof_level(), ProofLevel::L0Safety);
        assert!(!vcs[0].kind.has_runtime_fallback(true));
    }

    #[test]
    fn test_detect_transmute_call() {
        let func = make_func(vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                is_foreign: false,
                func: "std::mem::transmute".to_string(),
                args: vec![],
                dest: Place::local(0),
                target: Some(BlockId(1)),
                span: empty_span(),
                atomic: None,
            },
        }]);

        let vcs = generate_unsafe_operation_vcs(&func);
        assert_eq!(vcs.len(), 1);
        match &vcs[0].kind {
            VcKind::UnsafeOperation { desc } => {
                assert!(desc.contains("transmute"), "desc: {desc}");
            }
            other => panic!("expected UnsafeOperation, got: {other:?}"),
        }
    }

    #[test]
    fn test_detect_ffi_call() {
        let func = make_func(vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                is_foreign: false,
                func: "libc::ffi::malloc".to_string(),
                args: vec![],
                dest: Place::local(0),
                target: Some(BlockId(1)),
                span: empty_span(),
                atomic: None,
            },
        }]);

        let vcs = generate_unsafe_operation_vcs(&func);
        assert_eq!(vcs.len(), 1);
        match &vcs[0].kind {
            VcKind::UnsafeOperation { desc } => {
                assert!(desc.contains("FFI call"), "desc: {desc}");
            }
            other => panic!("expected UnsafeOperation, got: {other:?}"),
        }
    }

    #[test]
    fn test_detect_unsafe_fn_call() {
        let func = make_func(vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                is_foreign: false,
                func: "std::ptr::read".to_string(),
                args: vec![],
                dest: Place::local(0),
                target: Some(BlockId(1)),
                span: empty_span(),
                atomic: None,
            },
        }]);

        let vcs = generate_unsafe_operation_vcs(&func);
        assert_eq!(vcs.len(), 1);
        match &vcs[0].kind {
            VcKind::UnsafeOperation { desc } => {
                assert!(desc.contains("unsafe function call"), "desc: {desc}");
                assert!(desc.contains("ptr::read"), "desc: {desc}");
            }
            other => panic!("expected UnsafeOperation, got: {other:?}"),
        }
    }

    #[test]
    fn test_detect_address_of() {
        let func = make_func(vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::AddressOf(true, Place::local(2)),
                span: empty_span(),
            }],
            terminator: Terminator::Return,
        }]);

        let vcs = generate_unsafe_operation_vcs(&func);
        assert_eq!(vcs.len(), 1);
        match &vcs[0].kind {
            VcKind::UnsafeOperation { desc } => {
                assert!(desc.contains("&raw mut"), "desc: {desc}");
            }
            other => panic!("expected UnsafeOperation, got: {other:?}"),
        }
    }

    #[test]
    fn test_no_unsafe_ops_produces_no_vcs() {
        let func = make_func(vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: empty_span(),
            }],
            terminator: Terminator::Return,
        }]);

        let vcs = generate_unsafe_operation_vcs(&func);
        assert!(vcs.is_empty(), "safe function should produce no unsafe VCs");
    }

    #[test]
    fn test_multiple_unsafe_ops_in_one_function() {
        let func = make_func(vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 2,
                        projections: vec![Projection::Deref],
                    })),
                    span: empty_span(),
                }],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "std::mem::transmute".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: empty_span(),
                    atomic: None,
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ]);

        let vcs = generate_unsafe_operation_vcs(&func);
        assert_eq!(vcs.len(), 2, "should detect both raw deref and transmute");

        // All should be conservative (Bool(true))
        for vc in &vcs {
            assert_eq!(vc.formula, Formula::Bool(true));
            assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
        }
    }

    #[test]
    fn test_conservative_formula_is_always_true() {
        let func = make_func(vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                is_foreign: false,
                func: "std::ptr::write".to_string(),
                args: vec![],
                dest: Place::local(0),
                target: Some(BlockId(1)),
                span: empty_span(),
                atomic: None,
            },
        }]);

        let vcs = generate_unsafe_operation_vcs(&func);
        assert_eq!(vcs.len(), 1);
        // The formula should be Bool(true) — conservative flag, not a proof attempt
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    #[test]
    fn test_safe_call_not_flagged() {
        let func = make_func(vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                is_foreign: false,
                func: "std::vec::Vec::push".to_string(),
                args: vec![],
                dest: Place::local(0),
                target: Some(BlockId(1)),
                span: empty_span(),
                atomic: None,
            },
        }]);

        let vcs = generate_unsafe_operation_vcs(&func);
        assert!(vcs.is_empty(), "safe function call should not be flagged");
    }

    #[test]
    fn test_vc_kind_description_format() {
        let kind =
            VcKind::UnsafeOperation { desc: "raw pointer dereference of `_2.*`".to_string() };
        let description = kind.description();
        assert!(description.starts_with("unsafe operation:"), "desc: {description}");
        assert!(description.contains("raw pointer dereference"), "desc: {description}");
    }

    #[test]
    fn test_classify_call_patterns() {
        // Transmute
        assert!(matches!(
            classify_call("std::mem::transmute"),
            Some(UnsafeOpKind::Transmute { .. })
        ));
        assert!(matches!(
            classify_call("core::mem::transmute_copy"),
            Some(UnsafeOpKind::Transmute { .. })
        ));

        // FFI
        assert!(matches!(classify_call("libc::ffi::printf"), Some(UnsafeOpKind::FfiCall { .. })));

        // Unsafe fn
        assert!(matches!(classify_call("std::ptr::read"), Some(UnsafeOpKind::UnsafeFnCall { .. })));
        assert!(matches!(
            classify_call("std::slice::from_raw_parts"),
            Some(UnsafeOpKind::UnsafeFnCall { .. })
        ));
        assert!(matches!(
            classify_call("std::alloc::alloc"),
            Some(UnsafeOpKind::UnsafeFnCall { .. })
        ));

        // Safe call
        assert!(classify_call("std::vec::Vec::push").is_none());
        assert!(classify_call("my_module::safe_function").is_none());
    }

    #[test]
    fn test_format_place() {
        let place = Place { local: 3, projections: vec![Projection::Deref, Projection::Field(1)] };
        assert_eq!(format_place(&place), "_3.*.1");

        let simple = Place::local(5);
        assert_eq!(format_place(&simple), "_5");
    }
}
