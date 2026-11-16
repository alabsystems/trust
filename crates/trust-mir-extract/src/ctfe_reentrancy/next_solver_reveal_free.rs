// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Conservative next-solver recovery for the leak-free selection boundary.
//!
//! The inspection API is NOT a complete trace: `InspectGoal::candidates` omits
//! `ShadowedEnvProbing`, `ProjectionCompatibility`, and probes that never reached
//! `MakeCanonicalResponse`. Walking every returned candidate is therefore not an
//! exhaustive audit of losing probes. Admission first requires an empty caller
//! environment, primitive/tuple/array/reference arguments with no aliases, inert
//! trait predicates, and the existing all-candidate constant-inert gate. These
//! restrictions exclude opaque-bearing candidate clauses before tree evaluation;
//! the tree walk is an additional refusal boundary, never a replacement for them.
//!
//! This recovers a subset of the old solver's admitted projections. All other
//! next-solver selections retain the previous `None` answer. Compiler-owned
//! `SelectionContext::select` still chooses and instantiates the impl.

use std::ops::ControlFlow;

use rustc_infer::infer::InferCtxt;
use rustc_infer::traits::solve::inspect::ProbeKind;
use rustc_infer::traits::solve::{CandidateSource, Certainty, Goal};
use rustc_middle::traits::ImplSource;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::{DUMMY_SP, Span};
use rustc_trait_selection::solve::inspect::{
    InferCtxtProofTreeExt, InspectConfig, InspectGoal, ProofTreeVisitor,
};
use rustc_trait_selection::traits::{Obligation, ObligationCause, SelectionContext};

use super::closed_layout_memo::ClosedLayoutMemo;
use super::{
    exact_primitive_const_type, is_primitive_scalar, names_revealable, non_leaf_constant_if_frozen,
    selection_is_const_inert, trait_predicates_inert_at, with_region_vars,
};

const MAX_WORK: usize = 256;
const MAX_DEPTH: usize = 256;

/// Bounds this admission walk, not solver effort or proof-tree materialization.
struct Audit {
    remaining: usize,
    max_depth: usize,
}

impl Audit {
    fn charge(&mut self) -> ControlFlow<()> {
        match self.remaining.checked_sub(1) {
            Some(remaining) => {
                self.remaining = remaining;
                ControlFlow::Continue(())
            }
            None => ControlFlow::Break(()),
        }
    }
}

impl<'tcx> ProofTreeVisitor<'tcx> for Audit {
    type Result = ControlFlow<()>;

    fn span(&self) -> Span {
        DUMMY_SP
    }

    fn config(&self) -> InspectConfig {
        InspectConfig { max_depth: self.max_depth }
    }

    fn on_recursion_limit(&mut self) -> Self::Result {
        // The trait's default succeeds. Exhaustion must never admit a selection.
        ControlFlow::Break(())
    }

    fn visit_goal(&mut self, goal: &InspectGoal<'_, 'tcx>) -> Self::Result {
        self.charge()?;
        // Root visitation bypasses InspectGoal::visit_with's depth check.
        if goal.depth() >= self.max_depth || goal.result() != Ok(Certainty::Yes) {
            return ControlFlow::Break(());
        }
        let predicate = goal.goal().predicate;
        if names_revealable(goal.infcx().tcx, predicate)
            || predicate.has_aliases()
            || predicate.has_non_region_infer()
            || non_leaf_constant_if_frozen(goal.infcx().tcx, &predicate).is_some()
        {
            return ControlFlow::Break(());
        }
        let trait_goal = match predicate.kind().skip_binder() {
            ty::PredicateKind::Clause(ty::ClauseKind::Trait(pred))
                if pred.polarity == ty::ClausePolarity::Positive =>
            {
                true
            }
            ty::PredicateKind::Clause(ty::ClauseKind::ConstArgHasType(constant, expected))
                if predicate.kind().bound_vars().is_empty()
                    && !predicate.has_bound_vars()
                    && exact_primitive_const_type(constant, expected) =>
            {
                false
            }
            ty::PredicateKind::Clause(
                ty::ClauseKind::RegionOutlives(_)
                | ty::ClauseKind::TypeOutlives(_)
                | ty::ClauseKind::WellFormed(_),
            ) => false,
            _ => return ControlFlow::Break(()),
        };

        let candidates = goal.candidates();
        if candidates.is_empty() || candidates.len() > self.remaining {
            return ControlFlow::Break(());
        }
        for candidate in candidates {
            self.charge()?;
            // Even losing candidates exposed by this API are conservative refusals.
            if candidate.result() != Ok(Certainty::Yes)
                || candidate.shallow_certainty() != Certainty::Yes
            {
                return ControlFlow::Break(());
            }
            match candidate.kind() {
                ProbeKind::TraitCandidate {
                    source: CandidateSource::Impl(_) | CandidateSource::BuiltinImpl(_),
                    ..
                } if trait_goal => {}
                ProbeKind::Root { .. } if !trait_goal => {}
                // No alias-bound, environment, opaque-storage or rigid-alias route.
                _ => return ControlFlow::Break(()),
            }
            // Each sibling starts with its own inference state. In particular, never
            // memoize acceptance by a bare Goal across these probes.
            candidate.visit_nested_in_probe(self)?;
        }
        ControlFlow::Continue(())
    }
}

/// Root arguments cannot hide an opaque or a constant in an ADT field. Keep this
/// intentionally smaller than the old solver's layout/type walk.
pub(super) fn primitive_input(t: ty::Ty<'_>, remaining: &mut usize) -> bool {
    let Some(next) = remaining.checked_sub(1) else { return false };
    *remaining = next;
    if is_primitive_scalar(t) {
        return true;
    }
    match t.kind() {
        ty::Tuple(types) => types.iter().all(|t| primitive_input(t, remaining)),
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) | ty::Slice(inner) => {
            primitive_input(*inner, remaining)
        }
        ty::Array(inner, len) => {
            matches!(len.kind(), ty::ConstKind::Value(..)) && primitive_input(*inner, remaining)
        }
        _ => false,
    }
}

/// Raw declaration inventory, not normalization or a layout/trait answer.
/// Every source argument (including phantoms) and every local/foreign field
/// participates. A repeated exact type closes only this one whole input graph;
/// no partial answer or visited set escapes to another selection.
fn structural_field_input<'tcx>(
    tcx: TyCtxt<'tcx>,
    t: ty::Ty<'tcx>,
    remaining: &mut usize,
    seen: &mut Vec<ty::Ty<'tcx>>,
    lookup: &mut impl FnMut(ty::Ty<'tcx>, &mut usize) -> Option<ty::Ty<'tcx>>,
) -> bool {
    let Some(next) = remaining.checked_sub(1) else { return false };
    *remaining = next;
    if t.has_opaque_types()
        || t.has_coroutines()
        || t.has_non_region_param()
        || t.has_non_region_infer()
        || t.has_non_region_placeholders()
        || t.has_escaping_bound_vars()
        || t.references_error()
    {
        return false;
    }
    if is_primitive_scalar(t) || matches!(t.kind(), ty::Str | ty::Never) {
        return true;
    }
    match t.kind() {
        ty::Alias(_, alias) if matches!(alias.kind, ty::AliasTyKind::Projection { .. }) => {
            // Never normalize/select/query here. Only the SAME invocation's
            // completed reader may supply an exact written source type.
            lookup(t, remaining).is_some_and(|written| {
                structural_field_input(tcx, written, remaining, seen, lookup)
            })
        }
        ty::Pat(base, pattern)
            if matches!(**pattern, ty::PatternKind::NotNull)
                && matches!(base.kind(), ty::RawPtr(..)) =>
        {
            // A const-free source type refinement only. This grants no pointer
            // value, dereference, allocation, provenance or runtime permission.
            structural_field_input(tcx, *base, remaining, seen, lookup)
        }
        ty::Tuple(types) => {
            types.iter().all(|t| structural_field_input(tcx, t, remaining, seen, lookup))
        }
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) | ty::Slice(inner) => {
            structural_field_input(tcx, *inner, remaining, seen, lookup)
        }
        ty::Array(inner, len) => {
            matches!(len.kind(), ty::ConstKind::Value(value)
                if matches!(value.ty.kind(), ty::Uint(ty::UintTy::Usize)))
                && structural_field_input(tcx, *inner, remaining, seen, lookup)
        }
        ty::Adt(def, args) if !def.is_union() => {
            if seen.contains(&t) {
                return true;
            }
            seen.push(t);
            args.iter().all(|arg| {
                let Some(next) = remaining.checked_sub(1) else { return false };
                *remaining = next;
                match arg.kind() {
                    ty::GenericArgKind::Lifetime(_) => true,
                    ty::GenericArgKind::Type(t) => {
                        structural_field_input(tcx, t, remaining, seen, lookup)
                    }
                    // Scalar value constants only: aggregate/opaque constant types
                    // cannot hide a second uninspected input universe.
                    ty::GenericArgKind::Const(c) => matches!(c.kind(), ty::ConstKind::Value(value)
                        if is_primitive_scalar(value.ty)),
                }
            }) && def.variants().iter().all(|variant| {
                // Empty variants consume work too; field-only accounting would
                // otherwise leave arbitrarily large declarations unbounded.
                let Some(next) = remaining.checked_sub(1) else { return false };
                *remaining = next;
                variant.fields.iter().all(|field| {
                    let field_ty =
                        tcx.type_of(field.did).instantiate(tcx, *args).skip_normalization();
                    structural_field_input(tcx, field_ty, remaining, seen, lookup)
                })
            })
        }
        // Function/dynamic/alias/bound/unknown carriers grant no new input case.
        _ => false,
    }
}

fn projection_input_with_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    t: ty::Ty<'tcx>,
    remaining: &mut usize,
    facts: &ClosedLayoutMemo<ty::Ty<'tcx>>,
) -> bool {
    projection_input_with_lookup(tcx, t, remaining, facts, &mut |key, _| {
        facts.written_projection(key)
    })
}

fn projection_input_with_lookup<'tcx>(
    tcx: TyCtxt<'tcx>,
    t: ty::Ty<'tcx>,
    remaining: &mut usize,
    facts: &ClosedLayoutMemo<ty::Ty<'tcx>>,
    lookup: &mut impl FnMut(ty::Ty<'tcx>, &mut usize) -> Option<ty::Ty<'tcx>>,
) -> bool {
    // Preserve the original grammar and its accounting for every old input.
    // The additional ADT case requires BOTH an independently closed exact layout
    // walk and a fresh stronger field inventory. Layout safety alone is not an
    // inert-selection premise (foreign declarations may hide opaque fields).
    if let ty::Adt(..) = t.kind() {
        return facts.contains(t)
            && structural_field_input(tcx, t, remaining, &mut Vec::new(), lookup);
    }
    let Some(next) = remaining.checked_sub(1) else { return false };
    *remaining = next;
    if is_primitive_scalar(t) {
        return true;
    }
    match t.kind() {
        ty::Tuple(types) => {
            types.iter().all(|t| projection_input_with_lookup(tcx, t, remaining, facts, lookup))
        }
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) | ty::Slice(inner) => {
            projection_input_with_lookup(tcx, *inner, remaining, facts, lookup)
        }
        ty::Array(inner, len) => {
            matches!(len.kind(), ty::ConstKind::Value(..))
                && projection_input_with_lookup(tcx, *inner, remaining, facts, lookup)
        }
        _ => false,
    }
}

/// Preparation is separately bounded and may obtain only guarded foreign written
/// bindings. Verification below has a lookup-only closure and cannot retry/select.
/// No binding flows back to the enclosing layout walk.
pub(super) fn prepare_input_bindings<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
    facts: &mut ClosedLayoutMemo<ty::Ty<'tcx>>,
) -> bool {
    // The new metadata phase must not tighten or re-account old primitive inputs.
    let mut primitive_budget = MAX_WORK;
    if trait_ref.args.types().all(|t| primitive_input(t, &mut primitive_budget)) {
        return true;
    }
    let closed = facts.argument_scope();
    let mut remaining = MAX_WORK;
    trait_ref.args.iter().all(|arg| {
        let Some(next) = remaining.checked_sub(1) else { return false };
        remaining = next;
        match arg.kind() {
            ty::GenericArgKind::Lifetime(_) => true,
            ty::GenericArgKind::Const(c) => matches!(c.kind(), ty::ConstKind::Value(value)
                if is_primitive_scalar(value.ty)),
            ty::GenericArgKind::Type(t) => {
                projection_input_with_lookup(tcx, t, &mut remaining, &closed, &mut |key, left| {
                    if !facts.has_written_projection_slot(key) {
                        let written = super::read_foreign_written_projection(tcx, key, left)?;
                        facts.record_written_projection(key, written);
                    }
                    facts.written_projection(key)
                })
            }
        }
    })
}

fn inert_input<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
    facts: Option<&ClosedLayoutMemo<ty::Ty<'tcx>>>,
) -> bool {
    if trait_ref.args.has_aliases()
        || trait_ref.args.has_non_region_param()
        || trait_ref.args.has_non_region_infer()
        || trait_ref.args.has_non_region_placeholders()
    {
        return false;
    }
    let mut remaining = MAX_WORK;
    trait_ref.args.iter().all(|arg| match arg.kind() {
        ty::GenericArgKind::Lifetime(_) => true,
        ty::GenericArgKind::Type(t) => match facts {
            Some(facts) => projection_input_with_facts(tcx, t, &mut remaining, facts),
            None => primitive_input(t, &mut remaining),
        },
        ty::GenericArgKind::Const(c) => matches!(c.kind(), ty::ConstKind::Value(..)),
    }) && trait_predicates_inert_at(tcx, trait_ref)
        && selection_is_const_inert(tcx, trait_ref)
}

pub(super) fn select<'tcx>(
    infcx: &InferCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
) -> Option<ImplSource<'tcx, ()>> {
    select_with_limits(infcx, param_env, trait_ref, MAX_WORK, MAX_DEPTH)
}

/// The caller owns this InferCtxt and drains its opaque storage on every exit.
pub(super) fn select_with_limits<'tcx>(
    infcx: &InferCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
    max_work: usize,
    max_depth: usize,
) -> Option<ImplSource<'tcx, ()>> {
    select_with_limits_and_facts(infcx, param_env, trait_ref, max_work, max_depth, None)
}

pub(super) fn select_with_layout_facts<'tcx>(
    infcx: &InferCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
    facts: &ClosedLayoutMemo<ty::Ty<'tcx>>,
) -> Option<ImplSource<'tcx, ()>> {
    select_with_limits_and_facts(infcx, param_env, trait_ref, MAX_WORK, MAX_DEPTH, Some(facts))
}

fn select_with_limits_and_facts<'tcx>(
    infcx: &InferCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
    max_work: usize,
    max_depth: usize,
    facts: Option<&ClosedLayoutMemo<ty::Ty<'tcx>>>,
) -> Option<ImplSource<'tcx, ()>> {
    if !inert_input(infcx.tcx, trait_ref, facts) || max_work == 0 || max_depth == 0 {
        return None;
    }
    let root = Obligation::new(
        infcx.tcx,
        ObligationCause::dummy(),
        param_env,
        with_region_vars(infcx, trait_ref),
    );
    let mut audit = Audit { remaining: max_work, max_depth };
    infcx
        .visit_proof_tree(Goal::new(infcx.tcx, root.param_env, root.predicate), &mut audit)
        .continue_value()?;

    // The compiler owns selection, specialization and impl-argument instantiation.
    let source = SelectionContext::new(infcx).select(&root).ok()??;
    if !source.borrow_nested_obligations().is_empty()
        || !matches!(source, ImplSource::UserDefined(_))
    {
        return None;
    }
    Some(source.map(|_| ()))
}
