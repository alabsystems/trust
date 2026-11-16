//! M2 (docs/design/DIRECT-LANE-PROOF-AUTHORITY.md) — the CONSTANT-index
//! bounds obligation, closing the top set-parity gap: built MIR emits the
//! `BoundsCheck` assert EVEN FOR A CONSTANT IN-BOUNDS INDEX (measured on the
//! cpick/cwrite probe dumps: `_t = const K; _c = Lt(_t, const N);
//! Assert(BoundsCheck)`), while the direct constant arms emitted no assert
//! and no record — the #191 OOB gate refuses `K >= N` outright, and the
//! in-bounds residue minted NOTHING, a direct-lane MISSING row per
//! const-index site (`missing-const-index-bounds` in
//! `trust_ir_bridge::direct_set_parity`'s taxonomy).
//!
//! The emission is site F's exact node train (the Step 5 dynamic-index
//! machinery) specialized to a constant index: `Const Usize K` + `Const
//! Usize N` + `ICmp Ult` + `Inst::Assert(InBounds)`, recorded via
//! `record_direct_assert_typed` under `SLUG_BOUNDS_CHECK` so a Pending
//! claim-free `BoundsCheck` obligation row is born at the finalizer — the
//! same identity scheme, the same tier, the same non-authority. The check is
//! vacuously true at runtime (`K < N` was just verified by the caller's own
//! gate), exactly as MIR's own assert is on this shape; what it buys is the
//! OBLIGATION — the set-parity row the MIR lane already carries.
//!
//! CALLERS (one line each, after their `K < N` gate passes and before the
//! element access): the `ExprKind::Index` constant fast-path, the two
//! SSA/deref array-element WRITE admissions' four call sites. The #191 OOB
//! refusals are byte-untouched — this helper is reachable ONLY behind a
//! passed `K < N` gate, so a constant OOB index still refuses the whole
//! body and never reaches an emission
//! (`tests/ui/trust/trust_ir_const_index_oob_fails_closed.rs` stays the
//! driver-level pin; `direct_set_parity`'s lowered-clean-OOB hard error is
//! the comparator-level tripwire for the same mutation).
//!
//! A NEW FILE by fleet discipline (`lib.rs` is fleet-hot): the module line
//! and the one-line call sites are the only `lib.rs` touchpoints, the
//! `direct_formula_capture.rs` precedent.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use trust_ir::proof::ProofAnnotation;
use trust_ir::{Constant, ICmpOp, Inst, InstrNode, Ty};

use crate::LowerCx;

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    /// Emit and record the bounds check for a CONSTANT in-bounds index
    /// `K < N` — site F's train with the index as a `Usize` constant.
    ///
    /// PRECONDITION (caller-gated, both callers' #191 gates): `u64::from(k)
    /// < n`. Debug-asserted here; the helper never re-decides admission and
    /// never refuses — refusal belongs to the callers' gates, byte-unmoved.
    pub(crate) fn emit_and_record_const_index_bounds(
        &mut self,
        at: rustc_span::Span,
        k: u32,
        n: u64,
    ) {
        debug_assert!(
            u64::from(k) < n,
            "emit_and_record_const_index_bounds is only reachable behind a passed K < N gate"
        );
        // MIR order (measured on the probe dumps): index constant first,
        // then the length, then the compare — site F's operand order
        // (`Ult(idx, len)`, both usize, unsigned at pointer width).
        let idx_c = self.fresh();
        self.push_node(
            InstrNode::new(Inst::Const { ty: Ty::Usize, value: Constant::Int(i128::from(k)) })
                .with_result(idx_c),
        );
        let len_c = self.fresh();
        self.push_node(
            InstrNode::new(Inst::Const { ty: Ty::Usize, value: Constant::Int(i128::from(n)) })
                .with_result(len_c),
        );
        let inbounds = self.fresh();
        self.push_node(
            InstrNode::new(Inst::ICmp { op: ICmpOp::Ult, ty: Ty::Usize, lhs: idx_c, rhs: len_c })
                .with_result(inbounds),
        );
        self.push_node(
            InstrNode::new(Inst::Assert {
                cond: inbounds,
                kind: trust_ir::AssertKind::BoundsCheck { index: idx_c, len: len_c },
                site: None,
            })
            .with_proof(ProofAnnotation::InBounds),
        );
        // The record births the Pending `BoundsCheck` row at the finalizer;
        // the typed capture resolves the open-block `Const` index to a
        // literal operand (`Lit(K)`), so the Step-6 formula lane mints
        // normally too.
        self.record_direct_assert_typed(
            crate::direct_obligations::SLUG_BOUNDS_CHECK,
            ProofAnnotation::InBounds,
            at,
            &crate::direct_formula_capture::DirectAssertShape::Bounds { index: idx_c, len: n },
        );
    }
}
