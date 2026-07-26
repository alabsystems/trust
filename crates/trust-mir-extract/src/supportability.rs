//! Cheap supportability classifier for the verifier fast-reject phase.
//!
//! verifier-perf: the trust_verify MIR pass currently runs full
//! lowering on every function and discovers Unsupported only at the end
//! (after expensive trust-ir conversion). On a stage2 build that means
//! 1-3 hours per upstream compiler crate just to emit "Unsupported"
//! notes that yield no proof value. This module gives the pass a cheap
//! pre-check it can call *before* lowering.
//!
//! Decision target: <100µs per function (one pass over local_decls and
//! a shallow walk of statements/terminators looking for known boundary
//! constructs).
//!
//! Per-crate policy bucketing is handled separately in [`policy`]; this
//! file answers only "can the lowering plausibly succeed on this body?"
//!
//! Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

use rustc_middle::mir::{self, BasicBlockData, Body, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

/// Supportability classification for a single MIR body.
///
/// Returned by [`classify`] in time bounded by a single pass over MIR.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Supportability {
    /// Function carries a Trust contract attribute (`#[trust::ensures]` /
    /// `requires` / `invariant` / `contract_requires` block) — full
    /// verification obligations must be generated.
    SpecBearing,

    /// No spec but the MIR shape is fully supported by trust-ir lowering;
    /// the default obligation set (overflow, bounds, div-by-zero, cast
    /// safety) is generated.
    Inferrable,

    /// Lowering will fail on a known boundary construct. Captured here so
    /// the verifier can summarize at the crate level instead of attempting
    /// expensive lowering and emitting per-function `note:` storms.
    Unsupported(UnsupportedReason),
}

/// Stable enumeration of "we already know this won't lower" cases.
///
/// Kept narrow on purpose: only the categories actually observed in the
/// 9 GB stage2 build log are first-class. Anything else falls through to
/// [`UnsupportedReason::Other`] with the lowering-emitted reason string,
/// so we never silently mask a new boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnsupportedReason {
    /// `TyKind::Pat` — pattern types over usize / NonZero / etc. Needs
    /// restricted-value semantics that trust-ir does not yet model.
    PatternType,
    /// `TyKind::Param` — un-monomorphized generic parameter. Verifier
    /// runs on monomorphized MIR; pre-monomorphic generics never lower.
    GenericParam,
    /// `TyKind::Alias` — projection alias that was not normalized to a
    /// concrete type by the trait solver in time for verification.
    UnnormalizedAlias,
    /// `TyKind::Bound` / `TyKind::Placeholder` / `TyKind::Infer` /
    /// `TyKind::UnsafeBinder` / `TyKind::Error` — escaped binder or
    /// inference variable. Caller responsibility to upstream.
    EscapedBinderOrInferVar,
    /// `TyKind::Coroutine` / `TyKind::CoroutineWitness` — state-machine
    /// modeling unsupported.
    Coroutine,
    /// `SetDiscriminant` on a non-tagged ADT (e.g. niche-encoded enum
    /// with a non-tag layout). The lowering already errors on this.
    SetDiscriminantOnNonTagged,
    /// Address-of a `Field` projection where layout-aware offsets aren't
    /// available — observed for `&mut field` patterns the verifier can't
    /// model without offset semantics.
    AddressOfField,
    /// `Rvalue::ThreadLocalRef` — TLS access needs thread-local storage
    /// identity and initialization semantics that TrustIr does not yet model.
    ThreadLocalRef,
    /// An unsupported reason we know is a real boundary but doesn't fit
    /// the above categories; carries the lowering-side string verbatim.
    /// New boundaries surface as `Other` until they earn a first-class
    /// variant.
    Other(&'static str),
}

impl UnsupportedReason {
    /// One-token tag for the per-crate diagnostic aggregator.
    pub const fn tag(&self) -> &'static str {
        match self {
            Self::PatternType => "pattern-type",
            Self::GenericParam => "generic-param",
            Self::UnnormalizedAlias => "unnormalized-alias",
            Self::EscapedBinderOrInferVar => "escaped-binder",
            Self::Coroutine => "coroutine",
            Self::SetDiscriminantOnNonTagged => "set-discriminant-non-tagged",
            Self::AddressOfField => "addr-of-field",
            Self::ThreadLocalRef => "thread-local-ref",
            Self::Other(s) => s,
        }
    }
}

/// Classify a MIR body's verifiability without invoking the lowering or
/// VC generation pipelines. Cost: O(locals) + O(statements + terminators).
///
/// `has_trust_contract_attrs` is computed by the caller (it already has
/// the `DefId` and `TyCtxt`). Keeping this side-information at the call
/// site lets the classifier itself stay pure-MIR and unit-testable.
pub fn classify<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    has_trust_contract_attrs: bool,
) -> Supportability {
    // Contract attributes always force full verification — the caller asked
    // for proof obligations on this function, so even if lowering boundaries
    // exist downstream we still want them surfaced rather than skipped.
    if has_trust_contract_attrs {
        return Supportability::SpecBearing;
    }

    // Trust: piece #13 (safe-async data-safety) — a coroutine RESUME body (the
    // state-machine body of an `async fn` / `gen` block, post-`StateTransform`)
    // is ORDINARY optimized MIR by the time TrustVerify runs: `StateTransform`
    // ran much earlier (Runtime(Initial)), so there are no `Yield`s left — the
    // entry loads a state discriminant out of the frame, `SwitchInt`es to the
    // continuation, and each straight-line segment's overflow/bounds/div MIR is
    // exactly the ordinary `Assert(..)` / checked-arith the verifier already
    // handles. The former across-await locals are FRAME FIELDS whose reads
    // resolve opaquely (`project_ty_ref` has no `Ty::Coroutine` field arm →
    // `None` → unconstrained), and each `.await`'s resume value is the havoc'd
    // result of an unmodeled `Future::poll` call — so a value held across a
    // suspend NEVER carries a stale pre-suspend fact (the sound over-
    // approximation: a future may resume with ANY value of its output type).
    // We therefore let the coroutine body flow into normal lowering; any
    // genuinely-unmodeled shape (a coroutine-typed place we can't project, an
    // unmodeled call) degrades PER-OBLIGATION to `UnsupportedMir`→Unknown
    // (honest, never a false proof), never a hard whole-body reject. This is
    // the DEFAULT-lane increment; the `-full` native (trust-ir-bridge) lane
    // stays fail-closed for coroutines (the bridge's `AggregateKind::Coroutine`
    // arm returns `Err`, which fails OPEN to `spine_module = None` — no native
    // verdict flip, so the vcgen obligations govern and an Unknown keeps an
    // explicit-`-full` run fail-closed). No skip is minted here anymore.

    // First scan: parameter and local types. The vast majority of "1-hour
    // crate" cases hit a pattern-type or un-normalized projection in a
    // parameter and would have failed lowering for that reason alone.
    for local_decl in body.local_decls.iter() {
        if let Some(reason) = classify_ty(tcx, local_decl.ty) {
            return Supportability::Unsupported(reason);
        }
    }

    // Second scan: MIR statements and terminators for known boundary
    // operations (SetDiscriminant on non-tagged, AddressOf Field, etc.).
    for (_, block_data) in body.basic_blocks.iter_enumerated() {
        if let Some(reason) = classify_block(tcx, body, block_data) {
            return Supportability::Unsupported(reason);
        }
    }

    Supportability::Inferrable
}

fn classify_ty<'tcx>(_tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<UnsupportedReason> {
    // We only check the top-level TyKind here, not transitively. The
    // lowering-side `convert_ty` is the authoritative check; this is a
    // *fast-reject heuristic*, not a soundness oracle. False negatives
    // (the classifier says "Inferrable" but lowering still fails) are
    // tolerable — they cost one expensive lowering attempt, same as
    // today. False positives (the classifier says "Unsupported" but
    // lowering would have succeeded) are NOT tolerable and would mask
    // verifiable functions; we lean toward false negatives on purpose.
    match ty.kind() {
        TyKind::Pat(..) => Some(UnsupportedReason::PatternType),
        // A bare `Ty::Param` is NOT fast-rejected: a generic fn can still be panic-free for
        // ALL T (it only moves/stores/returns the opaque value), and every T-DEPENDENT
        // panicking op (a call/index/drop ON T) fails closed in the authoritative lowering
        // regardless of this classifier. Fast-rejecting here masks those verifiable generics
        // under the default strict policy (which forbids the skip). Same rationale as the
        // `TyKind::Alias` arms below — lean toward false negatives, let the lowering decide.
        // Trust: rust 1.99 reshaped `TyKind::Alias(IsRigid, AliasTy)`; the `AliasTyKind`
        // now lives on the `AliasTy`'s `kind` field rather than being the first payload.
        TyKind::Alias(_, alias_ty) => classify_alias_kind(alias_ty.kind),
        TyKind::Bound(..)
        | TyKind::Placeholder(..)
        | TyKind::Infer(..)
        | TyKind::UnsafeBinder(..)
        | TyKind::Error(..) => Some(UnsupportedReason::EscapedBinderOrInferVar),
        // Trust: piece #13 — a coroutine-typed local (the resume body's `self`
        // frame, a coroutine-typed field) is NOT fast-rejected: `ty_convert`
        // now lowers `TyKind::Coroutine`/`CoroutineWitness` to the opaque
        // `Ty::Coroutine` model (frame fields read unconstrained), so a resume
        // body whose only "coroutine" is its own frame verifies its ordinary
        // arithmetic/bounds segments. A coroutine-CLOSURE (`async ||`) still
        // fails closed in the authoritative lowering (`ty_convert` keeps it
        // `Ty::Unsupported`) — a later increment. Lean toward false negatives.
        _ => None,
    }
}

fn classify_alias_kind(kind: rustc_middle::ty::AliasTyKind<'_>) -> Option<UnsupportedReason> {
    match kind {
        // Free aliases are definitionally transparent and `ty_convert` expands
        // them through rustc's structural free-alias expander. If the expanded
        // RHS contains unsupported constructs, lowering remains the authority
        // and will fail closed there.
        rustc_middle::ty::AliasTyKind::Free { .. } => None,
        // verifier-coverage: Opaque (`impl Trait`) aliases are now
        // revealed to their concrete underlying type by
        // `ty_convert::convert_ty_in_env`, so fast-rejecting one here would
        // be a false positive — it would mask a function that lowering can
        // in fact handle, which this classifier must never do (false
        // negatives are tolerable, false positives are not). Let it fall
        // through to lowering; the depth/env guards live on the lowering side.
        rustc_middle::ty::AliasTyKind::Opaque { .. } => None,
        // verifier-coverage: monomorphic Projection/Inherent aliases are now
        // resolved to their concrete underlying type by
        // `ty_convert::normalize_alias` (env + monomorphism + ADT-depth guards
        // live there), exactly like the Opaque arm above. Fast-rejecting one
        // here would be a false positive — masking a function lowering can in
        // fact handle, which this classifier must never do. Let it fall through
        // to lowering, which stays fail-closed for the param-bearing / deep
        // cases.
        rustc_middle::ty::AliasTyKind::Projection { .. }
        | rustc_middle::ty::AliasTyKind::Inherent { .. } => None,
    }
}

fn classify_block<'tcx>(
    _tcx: TyCtxt<'tcx>,
    _body: &Body<'tcx>,
    block: &BasicBlockData<'tcx>,
) -> Option<UnsupportedReason> {
    for stmt in &block.statements {
        match &stmt.kind {
            // SetDiscriminant is fine on tagged ADTs; the lowering only
            // chokes when the discriminant has a non-tag layout. We
            // conservatively flag it here only when the underlying type
            // is provably non-tagged — but checking layout is itself
            // expensive, so for the fast path we leave SetDiscriminant
            // alone and let the lowering's own check fire if needed.
            // (Surface that as a future refinement once we measure how
            // often this single case dominates.)
            StatementKind::SetDiscriminant { .. } => {}
            StatementKind::Assign(boxed) => {
                let (_, rvalue) = &**boxed;
                if let Rvalue::RawPtr(_, place) = rvalue {
                    if !place.projection.is_empty()
                        && place
                            .projection
                            .iter()
                            .any(|elem| matches!(elem, mir::ProjectionElem::Field(..)))
                    {
                        return Some(UnsupportedReason::AddressOfField);
                    }
                }
                // Trust: piece #13 — the OUTER async fn body constructs the
                // coroutine aggregate (`Rvalue::Aggregate(Coroutine)`) to return
                // the `impl Future`. It carries no user arithmetic of its own
                // (the body moved into the resume fn); vcgen now models the
                // coroutine aggregate build as an obligation-free opaque
                // aggregate (`unsupported_aggregate_kind` → `None`), so this is
                // no longer fast-rejected. (`CoroutineClosure` still rejects
                // downstream — a later increment.)
                // Trust: `Rvalue::ThreadLocalRef` is NO LONGER a whole-function
                // unsupported skip. rustc gives the TLS address an immutable-
                // reference or raw-pointer type; convert.rs records the exact,
                // operand-free `Rvalue::ThreadLocalRef` marker and the bridge
                // lowers only that sealed shape to a dedicated Rust-semantics
                // TLS-address dialect op. Native CHC explicitly treats that op
                // as a fresh symbolic pointer with no TLS-identity or
                // dereferenceability assumption; every unadapted TrustIr consumer
                // rejects the unknown dialect fail-closed. Safe-reference validity
                // comes from the separate `ValidBorrow` lane and raw-pointer
                // dereferences remain fail-closed. The `UnsupportedReason::
                // ThreadLocalRef` variant remains available to consumers that do
                // not implement this sealed address model.
            }
            _ => {}
        }
    }
    if let Some(term) = &block.terminator {
        if matches!(term.kind, TerminatorKind::CoroutineDrop) {
            return Some(UnsupportedReason::Coroutine);
        }
    }
    None
}

/// Aggregated per-crate counts for the diagnostic summary.
///
/// The verifier pass folds individual [`Supportability`] decisions into
/// this struct so the end-of-crate hook can emit one summary line:
///
/// ```text
/// Trust: hashbrown — 0 spec-bearing, 12 inferrable, 1438 unsupported
///   (pattern-type: 412, generic-param: 891, unnormalized-alias: 135)
/// ```
///
/// instead of one `note:` per function.
#[derive(Default, Clone, Debug)]
pub struct CrateSupportSummary {
    pub spec_bearing: u64,
    pub inferrable: u64,
    pub unsupported_total: u64,
    pub by_tag: std::collections::BTreeMap<&'static str, u64>,
}

impl CrateSupportSummary {
    pub fn record(&mut self, s: &Supportability) {
        match s {
            Supportability::SpecBearing => self.spec_bearing += 1,
            Supportability::Inferrable => self.inferrable += 1,
            Supportability::Unsupported(reason) => {
                self.unsupported_total += 1;
                *self.by_tag.entry(reason.tag()).or_insert(0) += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tag strings must stay stable across releases — downstream report
    /// queries and the LSP diagnostics format both depend on them.
    #[test]
    fn tags_are_stable() {
        for tag in [
            UnsupportedReason::PatternType.tag(),
            UnsupportedReason::GenericParam.tag(),
            UnsupportedReason::UnnormalizedAlias.tag(),
            UnsupportedReason::EscapedBinderOrInferVar.tag(),
            UnsupportedReason::Coroutine.tag(),
            UnsupportedReason::SetDiscriminantOnNonTagged.tag(),
            UnsupportedReason::AddressOfField.tag(),
            UnsupportedReason::ThreadLocalRef.tag(),
            UnsupportedReason::Other("custom").tag(),
        ] {
            assert!(!tag.is_empty(), "empty tag would corrupt aggregate summaries");
            assert!(
                tag.chars().all(|c| c.is_ascii_lowercase() || c == '-'),
                "tag {tag:?} must be ascii-lowercase-with-dashes for log greppability"
            );
        }
    }

    #[test]
    fn alias_kinds_are_not_fast_rejected() {
        // No alias kind is fast-rejected: Free expands structurally, and
        // Opaque/Projection/Inherent are resolved to their concrete underlying
        // type by `ty_convert::normalize_alias` (guarded by env + monomorphism +
        // ADT-depth). Fast-rejecting any of them would be a false positive that
        // masks a function lowering can handle, which this classifier must never
        // do — false negatives only cost coverage; false positives are unsound.
        // Trust: rust 1.99 made `AliasTyKind` variants struct variants carrying a
        // `def_id`; the classifier ignores it, so a dummy crate-root DefId suffices.
        let did = rustc_span::def_id::CRATE_DEF_ID.to_def_id();
        assert_eq!(classify_alias_kind(rustc_middle::ty::AliasTyKind::Free { def_id: did }), None);
        assert_eq!(
            classify_alias_kind(rustc_middle::ty::AliasTyKind::Projection { def_id: did }),
            None
        );
        assert_eq!(
            classify_alias_kind(rustc_middle::ty::AliasTyKind::Inherent { def_id: did }),
            None
        );
        assert_eq!(
            classify_alias_kind(rustc_middle::ty::AliasTyKind::Opaque { def_id: did }),
            None
        );
    }

    #[test]
    fn aggregate_sums_correctly() {
        let mut sum = CrateSupportSummary::default();
        sum.record(&Supportability::SpecBearing);
        sum.record(&Supportability::Inferrable);
        sum.record(&Supportability::Inferrable);
        sum.record(&Supportability::Unsupported(UnsupportedReason::PatternType));
        sum.record(&Supportability::Unsupported(UnsupportedReason::PatternType));
        sum.record(&Supportability::Unsupported(UnsupportedReason::GenericParam));
        assert_eq!(sum.spec_bearing, 1);
        assert_eq!(sum.inferrable, 2);
        assert_eq!(sum.unsupported_total, 3);
        assert_eq!(sum.by_tag.get("pattern-type"), Some(&2));
        assert_eq!(sum.by_tag.get("generic-param"), Some(&1));
    }
}
