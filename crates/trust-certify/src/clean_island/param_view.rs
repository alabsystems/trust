// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Minting the E6 import of a borrow-erased PARAMETER VIEW
//! (`trust_types::e6_param_view`).
//!
//! WHAT IS AND IS NOT SHARED WITH THE ORDINARY MINT. The whole mint is the
//! UNCHANGED [`super::admit_function_into`], run on the view's own
//! `VerifiableFunction`. This module adds exactly three things around it, and
//! every one of them can only REFUSE or DISCLOSE:
//!
//! 1. **V4, the isolated facet gate.** A view never enters
//!    `SessionFnFacets::accumulated`, so its facets are computed here, over
//!    ITSELF ALONE (`infer_facets(&[view])`). That is deliberately stricter
//!    than the composed table the ordinary mint consults, and the point is
//!    that no OTHER function's facet record can make a view admissible.
//!    It is strictly stricter, not equivalent: `facet_inference` closes over
//!    CERTIFIED CALLEES present in the slice it is given, and
//!    `recognize_admissible_body` admits `checked_*` primitive calls, so
//!    isolation LOSES any view whose body reaches its facets through another
//!    user function. That is a capability loss in the fail-closed direction and
//!    it is accepted deliberately; the earlier claim here — that the recognized
//!    shapes contain no user-function call, so nothing could be lost — was
//!    simply wrong.
//! 2. **Unconditional parameter names.** `Admission::param_names` is set from
//!    the view's own `param_names`, always — never "when a name looks derived".
//!    That is what arms the exact-list comparison in
//!    `trust_spec_elab::elaborate_ensures`, which is the one check that catches
//!    a same-length REORDERING of the flattened binders (a reordering keeps the
//!    goal well-typed, so the kernel cannot see it). A name list the inner mint
//!    already recorded DIFFERENTLY refuses rather than being overwritten.
//! 3. **The two marks.** `Admission::with_view` records the view's name and, in
//!    the same call, restricts the import to the self-call position. See that
//!    method's docs for why the two are inseparable.
//!
//! WHAT THIS DOES NOT DO. It does not grade, and it does not decide what a
//! verdict says. A row discharged against a view-marked admission is reported
//! BELOW `Certified` with the marker disclosed — that is the compiler's
//! `trust_disposition_for_authority` and the transport, under R1
//! (`docs/TCB.md`, `docs/design-notes/2026-09-18-e6-parameter-view-ruling.md`).

use clean_kernel::Environment;
use trust_types::e6_param_view::{E6ParamView, VIEW_MARKER};

/// Mint the kernel import of `view`, returning the same
/// `(callee_path, Admission)` pair [`super::admit_function_into`] returns for
/// an ordinary body — with the view's marks attached.
///
/// `None` (fail-closed, mints nothing, changes no verdict) when any of:
///
/// * the view's own isolated facet inference is not all four (V4);
/// * `param_names` disagrees with the view body's own parameter locals in
///   length, order or spelling, or is not pairwise distinct;
/// * the inner mint declines the body shape;
/// * the inner mint recorded a DIFFERENT parameter-name list.
#[must_use]
pub fn admit_view_function_into(
    env: &mut Environment,
    view: &E6ParamView,
    facet_table: &trust_spec_elab::FacetTable,
) -> Option<(String, trust_spec_elab::Admission)> {
    let debug = super::e6_debug_enabled();
    let refuse = |reason: &str| -> Option<(String, trust_spec_elab::Admission)> {
        if debug {
            eprintln!("TRUST_E6_DEBUG view-mint fn={} REFUSED: {reason}", view.func.def_path);
        }
        None
    };

    // (2, first half) the recorded names ARE the view body's parameter locals.
    if view.param_names.len() != view.func.body.arg_count {
        return refuse("the recorded parameter list is not the view's own arity");
    }
    for (position, name) in view.param_names.iter().enumerate() {
        let Some(local) = view.func.body.locals.iter().find(|local| local.index == position + 1)
        else {
            return refuse("the view body has no local for a recorded parameter position");
        };
        if local.name.as_deref() != Some(name.as_str()) {
            return refuse("a recorded parameter name is not the view local's own name");
        }
    }
    let unique: std::collections::BTreeSet<&String> = view.param_names.iter().collect();
    if unique.len() != view.param_names.len() {
        return refuse("the recorded parameter names are not pairwise distinct");
    }

    // (1) V4: the VIEW's facets, in isolation, never the original body's
    // record and never another function's.
    let inferred = trust_types::facet_inference::infer_facets(std::slice::from_ref(&view.func));
    if !inferred.get(&view.func.def_path).copied().unwrap_or_default().all() {
        return refuse("the view is not all-four-facet certified in isolation");
    }

    // The inner mint reads exactly one thing off the table: whether THIS
    // def_path is admissible. Answer it from the isolated inference just
    // established, and leave every other record the caller's.
    let mut view_table = facet_table.clone();
    view_table.insert(
        view.func.def_path.clone(),
        trust_spec_elab::FnFacets::from_structural_certificates(
            true,
            true,
            true,
            true,
            "e6-parameter-view (isolated)",
        ),
    );

    let (path, admission) = super::admit_function_into(env, &view.func, &view_table)?;

    // (2, second half) names recorded UNCONDITIONALLY — and a disagreement
    // with what the inner mint recorded is a refusal, never an overwrite.
    if admission.param_names.as_ref().is_some_and(|minted| *minted != view.param_names) {
        return refuse("the inner mint recorded a different parameter-name list");
    }
    let admission = admission.with_param_names(view.param_names.clone()).with_view(VIEW_MARKER);
    if debug {
        eprintln!(
            "TRUST_E6_DEBUG view-mint fn={} MINTED view={VIEW_MARKER} params={:?}",
            view.func.def_path, view.param_names
        );
    }
    Some((path, admission))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The view of `impl Point { fn x_ref(&self) -> u32 { self.x } }` over
    /// `Point { x: u32, y: u32 }` — built DIRECTLY, exactly as
    /// `trust_types::e6_param_view::e6_param_view` builds it.
    ///
    /// It is built here rather than by calling that function because the
    /// SOURCE body needs a `Ty::Adt` carrying the extractor's `adt_kind`
    /// stamp, which `#[non_exhaustive]` deliberately makes unconstructible
    /// outside `trust-types`. That the builder produces exactly this shape —
    /// dense scalar locals named `self.x`/`self.y`, body `_0 = Copy(_1)`,
    /// recognized as `Projection { param: 0 }` — is pinned by
    /// `trust_types::e6_param_view::tests::
    /// a_ref_self_getter_becomes_a_two_parameter_scalar_projection`.
    fn view_of_x_ref() -> E6ParamView {
        let func = trust_types::VerifiableFunction {
            name: "x_ref".into(),
            def_path: "k::Point::x_ref".into(),
            span: trust_types::SourceSpan::default(),
            body: trust_types::VerifiableBody {
                locals: vec![
                    trust_types::LocalDecl { index: 0, ty: trust_types::Ty::u32(), name: None },
                    trust_types::LocalDecl {
                        index: 1,
                        ty: trust_types::Ty::u32(),
                        name: Some("self.x".into()),
                    },
                    trust_types::LocalDecl {
                        index: 2,
                        ty: trust_types::Ty::u32(),
                        name: Some("self.y".into()),
                    },
                ],
                blocks: vec![trust_types::BasicBlock {
                    id: trust_types::BlockId(0),
                    stmts: vec![trust_types::Statement::Assign {
                        place: trust_types::Place { local: 0, projections: Vec::new() },
                        rvalue: trust_types::Rvalue::Use(trust_types::Operand::Copy(
                            trust_types::Place { local: 1, projections: Vec::new() },
                        )),
                        span: trust_types::SourceSpan::default(),
                    }],
                    terminator: trust_types::Terminator::Return,
                }],
                arg_count: 2,
                return_ty: trust_types::Ty::u32(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        E6ParamView {
            func,
            param_names: vec!["self.x".to_string(), "self.y".to_string()],
            erased_params: vec!["self".to_string()],
        }
    }

    #[test]
    fn a_ref_self_getter_mints_a_marked_two_binder_import() {
        let view = view_of_x_ref();
        let mut env = Environment::with_prelude();
        let (path, admission) =
            admit_view_function_into(&mut env, &view, &trust_spec_elab::FacetTable::new())
                .expect("the view mints");
        assert_eq!(path, "k::Point::x_ref", "the import is keyed by the FUNCTION, not the view");
        assert_eq!(admission.arity, 2, "the import takes the pointee's scalar fields");
        assert_eq!(
            admission.param_names.as_deref(),
            Some(&["self.x".to_string(), "self.y".to_string()][..]),
            "the names are recorded UNCONDITIONALLY — they are what catches a reordering"
        );
        assert_eq!(admission.view(), Some(VIEW_MARKER), "the row must disclose the view");
        assert!(admission.is_self_result_only(), "a view import is never callable from a clause");
        assert!(
            env.get_const(&clean_kernel::Name::from_string(&admission.kernel_const)).is_some(),
            "the kernel really holds the defining equation"
        );
    }

    /// The ORDINARY mint of the same body carries NEITHER mark. That is the
    /// control proving the marks come from this function, not from the shape.
    #[test]
    fn m_the_ordinary_mint_of_the_same_body_carries_no_view_mark() {
        let view = view_of_x_ref();
        let cert = || trust_spec_elab::FacetStatus::Certified { evidence: "test".into() };
        let mut table = trust_spec_elab::FacetTable::new();
        table.insert(
            "k::Point::x_ref",
            trust_spec_elab::FnFacets {
                pure: cert(),
                total: cert(),
                deterministic: cert(),
                no_panic: cert(),
            },
        );
        let mut env = Environment::with_prelude();
        let (_, admission) =
            super::super::admit_function_into(&mut env, &view.func, &table).expect("mints");
        assert_eq!(admission.view(), None);
        assert!(!admission.is_self_result_only());
    }

    /// The MUTATION CONTROL for V4: a generous caller table cannot make a view
    /// admissible. Here the view's own body carries a back-edge, which refuses
    /// `Total` in isolation however certified the caller's record says it is.
    #[test]
    fn m_an_isolated_facet_refusal_is_not_rescued_by_the_callers_table() {
        let mut broken = view_of_x_ref();
        broken.func.body.blocks[0].terminator =
            trust_types::Terminator::Goto(trust_types::BlockId(0));

        let cert = || trust_spec_elab::FacetStatus::Certified { evidence: "caller".into() };
        let mut generous = trust_spec_elab::FacetTable::new();
        generous.insert(
            "k::Point::x_ref",
            trust_spec_elab::FnFacets {
                pure: cert(),
                total: cert(),
                deterministic: cert(),
                no_panic: cert(),
            },
        );
        let mut env = Environment::with_prelude();
        assert!(
            admit_view_function_into(&mut env, &broken, &generous).is_none(),
            "V4 reads the VIEW's own isolated facets; a generous caller table must not rescue it"
        );
    }

    /// A recorded name list that is not the view body's own refuses. This is
    /// the gate that keeps `Admission::param_names` an honest record of the
    /// binders the import was minted over — the one check that catches a
    /// same-length REORDERING, which the kernel cannot see.
    #[test]
    fn n_a_recorded_name_that_is_not_the_view_locals_own_refuses() {
        let mut view = view_of_x_ref();
        view.param_names = vec!["self.y".to_string(), "self.x".to_string()];
        let mut env = Environment::with_prelude();
        assert!(
            admit_view_function_into(&mut env, &view, &trust_spec_elab::FacetTable::new())
                .is_none(),
            "a swapped name list must refuse"
        );
    }

    #[test]
    fn n_a_duplicated_recorded_name_refuses() {
        let mut view = view_of_x_ref();
        view.func.body.locals[2].name = Some("self.x".into());
        view.param_names = vec!["self.x".to_string(), "self.x".to_string()];
        let mut env = Environment::with_prelude();
        assert!(
            admit_view_function_into(&mut env, &view, &trust_spec_elab::FacetTable::new())
                .is_none()
        );
    }

    #[test]
    fn n_an_arity_disagreement_refuses() {
        let mut view = view_of_x_ref();
        view.param_names.pop();
        let mut env = Environment::with_prelude();
        assert!(
            admit_view_function_into(&mut env, &view, &trust_spec_elab::FacetTable::new())
                .is_none()
        );
    }
}
