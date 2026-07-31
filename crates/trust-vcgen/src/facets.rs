//! E6 structural facet scan (two-language design §3.1, v3 no-marker ruling).
//!
//! This module supplies the compiler-visible v1 **diagnostic** scan over an
//! extracted [`VerifiableFunction`].  Its local whitelist produces useful,
//! construct-specific reasons, but it is not an admission authority.  A facet
//! is reported as established only when both this scan and
//! [`trust_types::facet_inference::infer_facets`] establish it for the same
//! single function.  The latter validates canonical identities, complete CFG
//! targets, types, and the closed MIR subset; its result is a one-way firewall
//! that can only remove a positive finding.
//!
//! Deliberate v1 restrictions and their successor lanes (the "brick 3b"
//! upgrades from the banked E6 series):
//! - `NoPanic` here demands *no reachable assert at all*; the successor is the
//!   L0 whole-function aggregate, which certifies functions whose asserts are
//!   all PROVED unreachable.
//! - `Total` here demands *no back-edge and no call*; the successor is the E5
//!   termination lane (decreases measures / structural recursion).
//! - `Pure`/`Deterministic` here demand scalar locals and whitelisted ops; the
//!   successor is the const-checker operations taxonomy (interior mutability,
//!   allocation, float NaN payloads, …).
//!
//! Unknown variants fall to violations via `_` arms, and the audited firewall
//! rejects malformed or ill-typed serialized MIR that the diagnostic whitelist
//! cannot validate on its own.  Nothing downstream may treat these findings as
//! a kernel admission token; today's consumers are diagnostics only.

use trust_types::{Operand, Place, Rvalue, Statement, Terminator, Ty, VerifiableFunction};

use crate::loop_analysis::detect_loops;

/// One facet's scan outcome. `Established` carries the evidence tag recorded
/// into the diagnostic table; `NotEstablished` carries the first violating
/// construct (scan order), verbatim for the E6 diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FacetFinding {
    Established { evidence: String },
    NotEstablished { reason: String },
}

impl FacetFinding {
    pub fn is_established(&self) -> bool {
        matches!(self, FacetFinding::Established { .. })
    }
}

/// The four E6 facets as found by the structural scan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuralFacetScan {
    pub pure: FacetFinding,
    pub total: FacetFinding,
    pub deterministic: FacetFinding,
    pub no_panic: FacetFinding,
}

const EVIDENCE: &str =
    "structural-scan-v1: scalar locals, whitelisted ops, certified calls, no back-edges";

/// A violation and which facets it poisons. v1 keeps the mapping coarse and
/// conservative; refinement arrives with the per-facet successor lanes.
struct Violation {
    reason: String,
    pure: bool,
    total: bool,
    deterministic: bool,
    no_panic: bool,
}

impl Violation {
    fn all(reason: String) -> Self {
        Violation { reason, pure: true, total: true, deterministic: true, no_panic: true }
    }
}

/// Preserve a useful whitelist reason when one already exists, but never let
/// the compiler-facing scan positively outvote the validated closed-fragment
/// analysis.  `infer_facets` deliberately exposes only booleans, so a decline
/// introduced here names the validation boundary rather than inventing a more
/// specific cause.
fn apply_audited_firewall(
    finding: FacetFinding,
    audited_established: bool,
    facet: &str,
) -> FacetFinding {
    if audited_established {
        return finding;
    }

    match finding {
        existing @ FacetFinding::NotEstablished { .. } => existing,
        FacetFinding::Established { .. } => FacetFinding::NotEstablished {
            reason: format!(
                "validated closed-fragment firewall declined {facet}; the body is malformed, \
                 ill-typed, unsupported, or contains an undischarged panic operation"
            ),
        },
    }
}

/// Conservatively scan `func` for the four E6 facets.
pub fn scan_structural_facets(func: &VerifiableFunction) -> StructuralFacetScan {
    // No callee context: every call fails closed, which is the pre-closure
    // behaviour and the right default for a caller that has no whole-set view.
    scan_structural_facets_with_callees(func, &std::collections::BTreeSet::new())
}

/// Scan one function, permitting calls to callees already known certified.
pub fn scan_structural_facets_with_callees(
    func: &VerifiableFunction,
    certified_callees: &std::collections::BTreeSet<String>,
) -> StructuralFacetScan {
    let mut violations: Vec<Violation> = Vec::new();

    // Type gate: every local (params, temporaries, return slot) must live in
    // the v1 scalar fragment. References/raw pointers step outside purity,
    // floats outside determinism (NaN payloads), aggregates outside what the
    // whitelisted ops below can be trusted to cover — v1 maps any escape to
    // ALL facets rather than pretending a finer taxonomy exists yet.
    for local in &func.body.locals {
        if !ty_in_scalar_fragment(&local.ty) {
            let who = local
                .name
                .as_deref()
                .map(|n| format!("`{n}`"))
                .unwrap_or_else(|| format!("_{}", local.index));
            violations.push(Violation::all(format!(
                "local {who} has type {:?}, outside the v1 scalar fragment",
                local.ty
            )));
        }
    }

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Some(v) = statement_violation(stmt) {
                violations.push(v);
            }
        }
        if let Some(v) = terminator_violation(&block.terminator, certified_callees) {
            violations.push(v);
        }
    }

    // Back-edges: totality is structural only in their absence; the E5
    // termination lane is the successor certifier for measured loops.
    if !detect_loops(func).is_empty() {
        violations.push(Violation {
            reason: "back-edge present; structural totality requires a loop-free body \
                     (the E5 termination lane certifies measured loops)"
                .to_string(),
            pure: false,
            total: true,
            deterministic: false,
            no_panic: false,
        });
    }

    let finding = |facet: fn(&Violation) -> bool| -> FacetFinding {
        match violations.iter().find(|v| facet(v)) {
            Some(v) => FacetFinding::NotEstablished { reason: v.reason.clone() },
            None => FacetFinding::Established { evidence: EVIDENCE.to_string() },
        }
    };

    // The whitelist above is intentionally optimized for actionable
    // diagnostics and therefore does not duplicate the authority-grade MIR
    // validator.  Intersect every positive result with that validator here, in
    // the function called by the compiler, rather than relying on a parity test
    // to notice future drift after a positive finding has escaped.
    let audited = trust_types::facet_inference::infer_facets(std::slice::from_ref(func))
        .get(&func.def_path)
        .copied()
        .unwrap_or_default();

    StructuralFacetScan {
        pure: apply_audited_firewall(finding(|v| v.pure), audited.pure, "Pure"),
        total: apply_audited_firewall(finding(|v| v.total), audited.total, "Total"),
        deterministic: apply_audited_firewall(
            finding(|v| v.deterministic),
            audited.deterministic,
            "Deterministic",
        ),
        no_panic: apply_audited_firewall(finding(|v| v.no_panic), audited.no_panic, "NoPanic"),
    }
}

fn ty_in_scalar_fragment(ty: &Ty) -> bool {
    match ty {
        Ty::Bool | Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char | Ty::Unit => true,
        // Tuples of fragment scalars: checked arithmetic lowers to a
        // `(value, overflowed)` tuple temporary (`CheckedBinaryOp` dest);
        // rejecting that bookkeeping local would poison every facet of any
        // body with debug-checked `+`/`-`/`*`. Field reads of a by-value
        // scalar tuple are pure, deterministic, total, and panic-free.
        Ty::Tuple(elems) => elems.iter().all(ty_in_scalar_fragment),
        _ => false,
    }
}

/// A place stays in the fragment when it is a bare local or a chain of
/// `Field` projections on one (the checked-op tuple reads). `Deref`, `Index`,
/// `Downcast`, and the opaque/binder projections step outside — indexing can
/// panic, derefs reach through references the type gate excludes anyway.
fn place_in_fragment(place: &Place) -> bool {
    place.projections.iter().all(|p| matches!(p, trust_types::Projection::Field(_)))
}

fn operand_in_fragment(op: &Operand) -> bool {
    match op {
        Operand::Copy(p) | Operand::Move(p) => place_in_fragment(p),
        Operand::Constant(_) => true,
        // Unknown operand forms fall outside the fragment.
        _ => false,
    }
}

fn statement_violation(stmt: &Statement) -> Option<Violation> {
    match stmt {
        Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::PlaceMention(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => None,
        Statement::Assign { place, rvalue, .. } => {
            if !place_in_fragment(place) {
                return Some(Violation::all(
                    "assignment through a non-field place projection".to_string(),
                ));
            }
            match rvalue {
                Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
                    if operand_in_fragment(op) {
                        None
                    } else {
                        Some(Violation::all("operand outside the v1 fragment".to_string()))
                    }
                }
                Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                    if operand_in_fragment(a) && operand_in_fragment(b) {
                        None
                    } else {
                        Some(Violation::all("operand outside the v1 fragment".to_string()))
                    }
                }
                other => {
                    Some(Violation::all(format!("rvalue outside the v1 whitelist: {other:?}")))
                }
            }
        }
        other => Some(Violation::all(format!("statement outside the v1 whitelist: {other:?}"))),
    }
}

fn terminator_violation(
    term: &Terminator,
    certified_callees: &std::collections::BTreeSet<String>,
) -> Option<Violation> {
    match term {
        Terminator::Goto(_) | Terminator::SwitchInt { .. } | Terminator::Return => None,
        // A reachable assert poisons ONLY structural NoPanic: purity,
        // determinism and (loop-free) totality are unaffected by a panic
        // edge. The L0 whole-fn aggregate is the successor certifier for
        // bodies whose asserts are all proved.
        Terminator::Assert { .. } => Some(Violation {
            reason: "reachable assert; structural NoPanic requires an assert-free body \
                     (the L0 whole-function aggregate certifies proved asserts)"
                .to_string(),
            pure: false,
            total: false,
            deterministic: false,
            no_panic: true,
        }),
        Terminator::Call { func: callee, .. } => {
            // RULED 2026-07-25 (docs/design/2026-07-25-e6-call-admission-ruling-request.md):
            // a call no longer poisons every facet outright. It is permitted
            // exactly when the callee is ITSELF structurally certified, which
            // `scan_structural_facets_closure` establishes as a least fixpoint
            // over the call graph.
            //
            // IDENTITY. `callee` is not a name: `func_operand_name` builds it
            // from `safe_def_path_str_with_args(tcx, def_id, generic_args)`, so
            // it is the DefId path plus the exact call-site instantiation
            // (`crates/trust-mir-extract/src/convert.rs:5334-5349`, which notes
            // a bare DefId path would alias `f::<bool>` and `f::<i32>`).
            // Matching is EXACT STRING EQUALITY against a certified function's
            // own `def_path` — never a suffix, never a bare name. That is what
            // keeps a same-suffix impostor (`mod evil { fn wrapping_add(..) }`)
            // out, and it costs the programmer nothing: no annotation, no
            // allowlist entry, no marker on the callee.
            //
            // FAIL-CLOSED AND TERMINATING. An unknown callee still poisons all
            // four facets. A recursive cycle never certifies, because no member
            // of the cycle can enter the set before the others — so mutual and
            // self recursion are refused rather than assumed total, which is
            // the direction that matters for the Total facet.
            if certified_callees.contains(callee.as_str())
                || callee.starts_with(trust_types::TRUST_RUSTC_INTRINSIC_PATH_PREFIX)
                || trust_types::RustcTotalPrimitiveMethod::classify(callee).is_some()
            {
                None
            } else {
                Some(Violation::all(format!(
                    "call to `{callee}`, which is not itself structurally certified \
                     (facets are closed over callees by exact def-path identity)"
                )))
            }
        }
        other => Some(Violation::all(format!("terminator outside the v1 whitelist: {other:?}"))),
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{BasicBlock, BinOp, BlockId, LocalDecl, SourceSpan, VerifiableBody};

    use super::*;

    fn func_with(
        locals: Vec<LocalDecl>,
        blocks: Vec<BasicBlock>,
        arg_count: usize,
        return_ty: Ty,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: "f".to_string(),
            def_path: "test::f".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody { locals, blocks, arg_count, return_ty },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// `min`-shaped: two u64 params, a comparison, a branch, two assigns.
    fn min_like() -> VerifiableFunction {
        func_with(
            vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            2,
            Ty::u64(),
        )
    }

    fn audited_facets(func: &VerifiableFunction) -> trust_types::facet_inference::FacetSet {
        trust_types::facet_inference::infer_facets(std::slice::from_ref(func))
            .get(&func.def_path)
            .copied()
            .unwrap_or_default()
    }

    fn assert_scan_is_audited_subset(func: &VerifiableFunction, label: &str) {
        let scan = scan_structural_facets(func);
        let audited = audited_facets(func);
        if scan.pure.is_established() {
            assert!(audited.pure, "{label}: scan established Pure after the audit declined it");
        }
        if scan.total.is_established() {
            assert!(audited.total, "{label}: scan established Total after the audit declined it");
        }
        if scan.deterministic.is_established() {
            assert!(
                audited.deterministic,
                "{label}: scan established Deterministic after the audit declined it"
            );
        }
        if scan.no_panic.is_established() {
            assert!(
                audited.no_panic,
                "{label}: scan established NoPanic after the audit declined it"
            );
        }
    }

    fn assert_all_scan_facets_declined(func: &VerifiableFunction, label: &str) {
        assert_eq!(
            audited_facets(func),
            trust_types::facet_inference::FacetSet::default(),
            "{label}: adversarial fixture must exercise an all-facet audit decline"
        );
        let scan = scan_structural_facets(func);
        for (facet, finding) in [
            ("Pure", &scan.pure),
            ("Total", &scan.total),
            ("Deterministic", &scan.deterministic),
            ("NoPanic", &scan.no_panic),
        ] {
            assert!(
                !finding.is_established(),
                "{label}: compiler scan established {facet} after the audit declined it"
            );
        }
    }

    #[test]
    fn min_like_establishes_all_four_facets() {
        let scan = scan_structural_facets(&min_like());
        assert!(scan.pure.is_established(), "{:?}", scan.pure);
        assert!(scan.total.is_established(), "{:?}", scan.total);
        assert!(scan.deterministic.is_established(), "{:?}", scan.deterministic);
        assert!(scan.no_panic.is_established(), "{:?}", scan.no_panic);
    }

    #[test]
    fn compiler_path_scan_is_intersected_with_the_audited_analysis() {
        // Defense in depth for the E6 diagnostic implementations.  The actual
        // firewall now lives inside `scan_structural_facets`; this test checks
        // the public invariant on both an accepted witness and representative
        // constructs rejected by the shared closed-fragment validator.
        assert_scan_is_audited_subset(&min_like(), "min_like");

        // Exceptional and opaque terminators fail the closed validator before
        // the individual structural analyses can disagree about a facet.
        let mut with_drop = min_like();
        with_drop.body.blocks[1].terminator = Terminator::Drop {
            unwind: trust_types::UnwindEdge::Unreachable,
            place: Place::local(1),
            target: BlockId(2),
            span: SourceSpan::default(),
        };
        assert_scan_is_audited_subset(&with_drop, "drop_terminator");

        let mut with_opaque = min_like();
        with_opaque.body.blocks[1].terminator = Terminator::Opaque {
            kind: "InlineAsm".into(),
            targets: vec![BlockId(2)],
            span: SourceSpan::default(),
        };
        assert_scan_is_audited_subset(&with_opaque, "opaque_terminator");

        // An atomic-RMW intrinsic whose name contains the otherwise-benign
        // substring `max` remains outside both closed fragments.
        let mut with_atomic = min_like();
        with_atomic.body.blocks[1]
            .stmts
            .insert(0, Statement::Intrinsic { name: "atomic_max_seqcst".into(), args: Vec::new() });
        assert_scan_is_audited_subset(&with_atomic, "atomic_intrinsic");
    }

    #[test]
    fn cast_is_declined_by_the_compiler_visible_firewall() {
        // The diagnostic whitelist historically accepted every scalar Cast,
        // while the validated closed fragment has no cast semantics at all.
        let mut f = min_like();
        f.body.blocks[1].stmts[0] = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u64()),
            span: SourceSpan::default(),
        };

        assert_all_scan_facets_declined(&f, "cast");
        let scan = scan_structural_facets(&f);
        for finding in [&scan.pure, &scan.total, &scan.deterministic, &scan.no_panic] {
            match finding {
                FacetFinding::NotEstablished { reason } => {
                    assert!(reason.contains("closed-fragment firewall"), "{reason}")
                }
                FacetFinding::Established { .. } => unreachable!(),
            }
        }
    }

    #[test]
    fn raw_add_div_and_shift_never_establish_no_panic() {
        // Raw MIR arithmetic needs a separate discharge for overflow,
        // division-by-zero, or an invalid shift amount.  The local whitelist
        // has no such discharge input, so the audited result must downgrade
        // only NoPanic while retaining the other validated facets.
        for (op, rhs, label) in
            [(BinOp::Add, 1, "raw Add"), (BinOp::Div, 0, "raw Div"), (BinOp::Shl, 64, "raw Shift")]
        {
            let mut f = min_like();
            f.body.blocks[1].stmts[0] = Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::BinaryOp(
                    op,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(trust_types::ConstValue::Uint(rhs, 64)),
                ),
                span: SourceSpan::default(),
            };

            let audited = audited_facets(&f);
            assert!(audited.pure && audited.total && audited.deterministic, "{label}");
            assert!(!audited.no_panic, "{label}");

            let scan = scan_structural_facets(&f);
            assert!(scan.pure.is_established(), "{label}: {:?}", scan.pure);
            assert!(scan.total.is_established(), "{label}: {:?}", scan.total);
            assert!(scan.deterministic.is_established(), "{label}: {:?}", scan.deterministic);
            match scan.no_panic {
                FacetFinding::NotEstablished { reason } => {
                    assert!(reason.contains("undischarged panic operation"), "{label}: {reason}")
                }
                other => panic!("{label}: compiler scan over-claimed NoPanic: {other:?}"),
            }
        }
    }

    #[test]
    fn malformed_cfg_local_targets_and_identities_fail_all_facets_closed() {
        // Each fixture used to look harmless to the diagnostic whitelist: it
        // inspects variants and projections but does not itself validate the
        // serialized vector identities or successor/local bounds.
        let mut bad_block_identity = min_like();
        bad_block_identity.body.blocks[1].id = BlockId(7);

        let mut dangling_cfg_target = min_like();
        dangling_cfg_target.body.blocks[1].terminator = Terminator::Goto(BlockId(99));

        let mut bad_local_identity = min_like();
        bad_local_identity.body.locals[1].index = 9;

        let mut dangling_local_target = min_like();
        dangling_local_target.body.blocks[1].stmts[0] = Statement::Assign {
            place: Place::local(99),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        };

        let mut empty_function_identity = min_like();
        empty_function_identity.def_path.clear();

        for (func, label) in [
            (&bad_block_identity, "block identity"),
            (&dangling_cfg_target, "CFG target"),
            (&bad_local_identity, "local identity"),
            (&dangling_local_target, "local target"),
            (&empty_function_identity, "function identity"),
        ] {
            assert_all_scan_facets_declined(func, label);
        }
    }

    #[test]
    fn assignment_type_mismatch_fails_all_facets_closed() {
        // `_0: u64 = _3: bool` uses only locally whitelisted syntax, but is not
        // a well-typed closed-fragment assignment.
        let mut f = min_like();
        f.body.blocks[1].stmts[0] = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
            span: SourceSpan::default(),
        };
        assert_all_scan_facets_declined(&f, "assignment type mismatch");
    }

    #[test]
    fn checked_add_tuple_poisons_only_no_panic() {
        // Debug-checked `x + 1` lowers to a `(u64, bool)` tuple temp, field
        // reads, and an overflow Assert. Only NoPanic may be poisoned — the
        // bookkeeping tuple must not fail the type gate for the other three.
        let mut f = min_like();
        f.body.locals.push(LocalDecl {
            index: 4,
            ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
            name: None,
        });
        f.body.blocks[1].stmts = vec![
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(trust_types::ConstValue::Uint(1, 64)),
                ),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place {
                    local: 4,
                    projections: vec![trust_types::Projection::Field(0)],
                })),
                span: SourceSpan::default(),
            },
        ];
        f.body.blocks[1].terminator = Terminator::Assert {
            unwind: trust_types::UnwindEdge::Unreachable,
            cond: Operand::Copy(Place {
                local: 4,
                projections: vec![trust_types::Projection::Field(1)],
            }),
            expected: false,
            msg: trust_types::AssertMessage::Overflow(BinOp::Add),
            target: BlockId(2),
            span: SourceSpan::default(),
        };
        let scan = scan_structural_facets(&f);
        assert!(scan.pure.is_established(), "{:?}", scan.pure);
        assert!(scan.total.is_established(), "{:?}", scan.total);
        assert!(scan.deterministic.is_established(), "{:?}", scan.deterministic);
        match &scan.no_panic {
            FacetFinding::NotEstablished { reason } => {
                assert!(reason.contains("L0 whole-function aggregate"), "{reason}")
            }
            other => panic!("checked add must poison NoPanic only: {other:?}"),
        }
    }

    #[test]
    fn back_edge_poisons_only_total() {
        let mut f = min_like();
        // Turn bb1 into a latch: back-edge to bb0.
        f.body.blocks[1].terminator = Terminator::Goto(BlockId(0));
        let scan = scan_structural_facets(&f);
        assert!(scan.pure.is_established());
        assert!(scan.deterministic.is_established());
        assert!(scan.no_panic.is_established());
        match &scan.total {
            FacetFinding::NotEstablished { reason } => {
                assert!(reason.contains("E5 termination lane"), "{reason}")
            }
            other => panic!("total must not be established across a back-edge: {other:?}"),
        }
    }

    #[test]
    fn assert_poisons_only_no_panic_and_names_the_l0_successor() {
        let mut f = min_like();
        f.body.blocks[2].terminator = Terminator::Assert {
            unwind: trust_types::UnwindEdge::Unreachable,
            cond: Operand::Copy(Place::local(3)),
            expected: true,
            msg: trust_types::AssertMessage::Overflow(BinOp::Add),
            target: BlockId(3),
            span: SourceSpan::default(),
        };
        f.body.blocks.push(BasicBlock {
            id: BlockId(3),
            stmts: vec![],
            terminator: Terminator::Return,
        });
        let scan = scan_structural_facets(&f);
        assert!(scan.pure.is_established());
        assert!(scan.total.is_established());
        assert!(scan.deterministic.is_established());
        match &scan.no_panic {
            FacetFinding::NotEstablished { reason } => {
                assert!(reason.contains("L0 whole-function aggregate"), "{reason}")
            }
            other => panic!("no_panic must not be established over an assert: {other:?}"),
        }
    }

    #[test]
    fn float_local_fails_all_facets_closed() {
        let mut f = min_like();
        f.body.locals.push(LocalDecl { index: 4, ty: Ty::Float { width: 64 }, name: None });
        let scan = scan_structural_facets(&f);
        for finding in [&scan.pure, &scan.total, &scan.deterministic, &scan.no_panic] {
            match finding {
                FacetFinding::NotEstablished { reason } => {
                    assert!(reason.contains("scalar fragment"), "{reason}")
                }
                other => panic!("float local must fail every facet closed: {other:?}"),
            }
        }
    }

    #[test]
    fn mutable_ref_param_fails_closed() {
        let mut f = min_like();
        f.body.locals[1].ty = Ty::Ref { mutable: true, inner: Box::new(Ty::u64()) };
        let scan = scan_structural_facets(&f);
        assert!(!scan.pure.is_established(), "&mut param can never scan Pure");
    }

    #[test]
    fn call_fails_all_facets_closed() {
        let mut f = min_like();
        f.body.blocks[1].terminator = Terminator::Call {
            unwind: trust_types::UnwindEdge::Unreachable,
            func: "test::g".to_string(),
            args: vec![],
            dest: Place::local(0),
            target: Some(BlockId(2)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
        };
        let scan = scan_structural_facets(&f);
        for finding in [&scan.pure, &scan.total, &scan.deterministic, &scan.no_panic] {
            assert!(
                !finding.is_established(),
                "callee closure is not wired; a call must fail every facet closed"
            );
        }
    }
}
