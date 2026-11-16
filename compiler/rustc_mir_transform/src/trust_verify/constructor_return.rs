// Trust: identity and kernel admission for one-field constructor return facts.
// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.

use rustc_ast::attr::AttributeExt;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::DefId;

// Trust: diagnostic stages carry no proof/model authority. Keep the first
// failed original guard instead of silently dropping every constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IdentityRefusal {
    NonLocal,
    NotAssociatedFunction,
    TraitOrForeign,
    Generic,
    CleanOrigin,
    TrustAttributeOrContract,
    NotLocalNongenericInherentImpl,
    Interposable,
    UnsafeSignature,
    ParameterTypes,
    OutputNotAdt,
    OutputOwnerKindGenericsOrDrop,
    ImplOutputMismatch,
    FieldCount,
    FieldNotScalar,
    ExtractedOutputMismatch,
    LayoutUnavailable,
    LayoutSizeOrAlignment,
    NotFreeze,
}

// Trust: a typed refusal is measurement only; a successful diagnostic never
// exports a summary or installs facts in a compiler session.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdmissionRefusal {
    InventoryLengthMismatch,
    UnavailablePreoptimizationBody,
    DuplicateKey,
    Candidate(&'static str),
    Identity(IdentityRefusal),
    MissingCalleeIdentity,
    NoCheckRows,
    Kernel { first_refused_row: usize },
}

fn scalar_shape(ty: ty::Ty<'_>) -> Option<trust_types::Ty> {
    match *ty.kind() {
        ty::Bool => Some(trust_types::Ty::Bool),
        ty::Int(kind) => Some(trust_types::Ty::Int {
            width: u32::try_from(kind.bit_width()?).ok()?,
            signed: true,
        }),
        ty::Uint(kind) => Some(trust_types::Ty::Int {
            width: u32::try_from(kind.bit_width()?).ok()?,
            signed: false,
        }),
        _ => None,
    }
}

/// Every decision is about typed local identities, never a bare `new` spelling.
fn identity_admissible(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    candidate: &trust_vcgen::ConstructorReturnCandidate,
) -> Result<(), IdentityRefusal> {
    let Some(local) = def_id.as_local() else { return Err(IdentityRefusal::NonLocal) };
    if !matches!(tcx.def_kind(def_id), DefKind::AssocFn) {
        return Err(IdentityRefusal::NotAssociatedFunction);
    }
    if tcx.trait_of_assoc(def_id).is_some() || tcx.is_foreign_item(def_id) {
        return Err(IdentityRefusal::TraitOrForeign);
    }
    if tcx.generics_of(def_id).count() != 0 {
        return Err(IdentityRefusal::Generic);
    }
    if crate::clean_origin_mir::is_clean_origin(tcx, local) {
        return Err(IdentityRefusal::CleanOrigin);
    }
    if super::item_has_trust_skip_attr(tcx, def_id)
        || super::item_has_trust_attr(tcx, def_id, "assume_total")
        || super::trust_contracts_if_any(tcx, def_id).is_some_and(|bundle| !bundle.is_empty())
    {
        return Err(IdentityRefusal::TrustAttributeOrContract);
    }
    let Some(owner) = tcx.inherent_impl_of_assoc(def_id) else {
        return Err(IdentityRefusal::NotLocalNongenericInherentImpl);
    };
    if !owner.is_local() || tcx.generics_of(owner).count() != 0 {
        return Err(IdentityRefusal::NotLocalNongenericInherentImpl);
    }
    let attrs = tcx.codegen_fn_attrs(def_id);
    if attrs.contains_extern_indicator() || attrs.symbol_name.is_some() || attrs.linkage.is_some() {
        return Err(IdentityRefusal::Interposable);
    }
    #[allow(deprecated)]
    if tcx
        .get_all_attrs(def_id)
        .iter()
        .any(|attr| matches!(attr.path().as_slice(), [tool, _] if tool.as_str() == "trust"))
    {
        return Err(IdentityRefusal::TrustAttributeOrContract);
    }
    let signature = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
    if signature.safety().is_unsafe() {
        return Err(IdentityRefusal::UnsafeSignature);
    }
    if signature.inputs().len() != candidate.parameter_types().len()
        || !signature
            .inputs()
            .iter()
            .zip(candidate.parameter_types())
            .all(|(input, expected)| scalar_shape(*input).as_ref() == Some(expected))
    {
        return Err(IdentityRefusal::ParameterTypes);
    }
    let output = signature.output();
    let ty::Adt(adt, args) = output.kind() else { return Err(IdentityRefusal::OutputNotAdt) };
    if !adt.did().is_local()
        || !adt.is_struct()
        || !args.is_empty()
        || adt.has_dtor(tcx)
        || tcx.generics_of(adt.did()).count() != 0
    {
        return Err(IdentityRefusal::OutputOwnerKindGenericsOrDrop);
    }
    if tcx.type_of(owner).instantiate_identity().skip_normalization() != output {
        return Err(IdentityRefusal::ImplOutputMismatch);
    }
    let fields = &adt.non_enum_variant().fields;
    if fields.len() != 1 {
        return Err(IdentityRefusal::FieldCount);
    }
    let Some(field) = fields.iter().next() else { return Err(IdentityRefusal::FieldCount) };
    let field_ty = field.ty(tcx, *args).skip_normalization();
    let Some(shape) = scalar_shape(field_ty) else { return Err(IdentityRefusal::FieldNotScalar) };
    let trust_types::Ty::Adt { name, fields, .. } = candidate.result_ty() else {
        return Err(IdentityRefusal::ExtractedOutputMismatch);
    };
    if name != &trust_mir_extract::sysroot_authenticated_def_path_str(tcx, adt.did())
        || fields.len() != 1
        || fields[0].1 != shape
    {
        return Err(IdentityRefusal::ExtractedOutputMismatch);
    }
    // Concrete, scalar-sized and scalar-aligned: no hidden data, padding,
    // destructor, or layout-dependent field identity enters this fragment.
    let env = ty::TypingEnv::post_analysis(tcx, def_id);
    let Ok(result_layout) = tcx.layout_of(env.as_query_input(output)) else {
        return Err(IdentityRefusal::LayoutUnavailable);
    };
    let Ok(field_layout) = tcx.layout_of(env.as_query_input(field_ty)) else {
        return Err(IdentityRefusal::LayoutUnavailable);
    };
    if result_layout.size != field_layout.size || result_layout.align != field_layout.align {
        return Err(IdentityRefusal::LayoutSizeOrAlignment);
    }
    if !output.is_freeze(tcx, env) {
        return Err(IdentityRefusal::NotFreeze);
    }
    Ok(())
}

// Trust: the production mint AND current-source diagnostic use this exact
// admission. Neither a metadata marker nor a diagnostic success skips a row.
fn admit(
    tcx: TyCtxt<'_>,
    func: &trust_types::VerifiableFunction,
    id: DefId,
    unique: bool,
    rows: &mut trust_types::vc_context::VcContext,
) -> Result<trust_vcgen::ConstructorReturnSummary, AdmissionRefusal> {
    if !unique {
        return Err(AdmissionRefusal::DuplicateKey);
    }
    let candidate = trust_vcgen::infer_constructor_return_candidate(func)
        .map_err(AdmissionRefusal::Candidate)?;
    identity_admissible(tcx, id, &candidate).map_err(AdmissionRefusal::Identity)?;
    let identity = trust_mir_extract::callee_identity_for(tcx, id, ty::GenericArgs::empty())
        .ok_or(AdmissionRefusal::MissingCalleeIdentity)?;
    trust_vcgen::intern_constructor_return_rows(rows, &candidate);
    if candidate.check_vcs().is_empty() {
        return Err(AdmissionRefusal::NoCheckRows);
    }
    for (index, row) in candidate.check_vcs().iter().enumerate() {
        if trust_certify::certify_vc(row).is_none() {
            return Err(AdmissionRefusal::Kernel { first_refused_row: index });
        }
    }
    Ok(candidate.bind_checked_identity(identity))
}

// Trust: a current-source compiler unit can inspect the REAL pre-optimization
// source admission, including serde-skipped extractor metadata. It cannot
// supply an IR body, identity or proof and receives no reusable model. This
// measurement installs nothing and does not change the verification policy.
#[derive(Clone, Debug)]
pub struct AdmissionProbe {
    pub def_id: DefId,
    pub def_path: String,
    pub plain_total_drop_metadata: bool,
    pub outcome: Result<(), AdmissionRefusal>,
}

// Trust: Steal is observed only to refuse an unavailable diagnostic input;
// rows are sorted before admission/output, never accepted from a partial body.
#[allow(rustc::untracked_query_information, rustc::potential_query_instability)]
pub fn probe(tcx: TyCtxt<'_>) -> Vec<AdmissionProbe> {
    let mut owners: Vec<_> = tcx.mir_keys(()).iter().copied().collect();
    owners.sort_by_cached_key(|owner| (tcx.def_path_str(*owner), owner.local_def_index.as_u32()));
    let mut functions = Vec::new();
    let mut ids = Vec::new();
    let mut unavailable = Vec::new();
    for owner in owners {
        let id = owner.to_def_id();
        if !matches!(tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        if crate::clean_origin_mir::is_clean_origin(tcx, owner) {
            unavailable.push(AdmissionProbe {
                def_id: id,
                def_path: tcx.def_path_str(id),
                plain_total_drop_metadata: false,
                outcome: Err(AdmissionRefusal::Identity(IdentityRefusal::CleanOrigin)),
            });
            continue;
        }
        let body = tcx.mir_drops_elaborated_and_const_checked(owner);
        if body.is_stolen() {
            unavailable.push(AdmissionProbe {
                def_id: id,
                def_path: tcx.def_path_str(id),
                plain_total_drop_metadata: false,
                outcome: Err(AdmissionRefusal::UnavailablePreoptimizationBody),
            });
            continue;
        }
        let body = body.borrow();
        functions.push(trust_mir_extract::extract_function_with_contract_bundle(tcx, &body, None));
        ids.push(id);
    }
    let collisions = super::body_summary_key_collisions(tcx, &functions, &ids);
    let mut counts = FxHashMap::default();
    for function in &functions {
        *counts.entry(function.def_path.as_str()).or_insert(0usize) += 1;
    }
    let mut parity = trust_types::vc_context::ParityTally::default();
    for (function, id) in functions.iter().zip(ids) {
        let unique = counts.get(function.def_path.as_str()) == Some(&1)
            && !collisions.contains(&function.def_path);
        let outcome = super::with_scoped_rows(&mut parity, |rows| {
            admit(tcx, function, id, unique, rows).map(|_| ())
        });
        unavailable.push(AdmissionProbe {
            def_id: id,
            def_path: function.def_path.clone(),
            plain_total_drop_metadata: matches!(
                &function.body.return_ty,
                trust_types::Ty::Adt {
                    arbitrary_precision: Some(trust_types::AdtAuth::TotalDrop(None)),
                    ..
                }
            ),
            outcome,
        });
    }
    unavailable.sort_by(|left, right| left.def_path.cmp(&right.def_path));
    unavailable
}

/// Mint once from the complete pre-optimization body inventory. Every admitted
/// clause is checked against its own original aggregate body with hypotheses
/// cleared. No whole-function or neighboring assertion proof is borrowed.
pub(super) fn mint(
    tcx: TyCtxt<'_>,
    funcs: &[trust_types::VerifiableFunction],
    ids: &[DefId],
    collisions: &FxHashSet<String>,
) -> FxHashMap<String, trust_vcgen::ConstructorReturnSummary> {
    let mut minted = FxHashMap::default();
    let trace = super::env_flag_enabled("TRUST_INFERRED_RETURN_DEBUG");
    if funcs.len() != ids.len() {
        if trace {
            eprintln!("TRUST_CONSTRUCTOR_RETURN: {:?}", AdmissionRefusal::InventoryLengthMismatch);
        }
        return minted;
    }
    let mut counts = FxHashMap::default();
    for func in funcs {
        *counts.entry(func.def_path.as_str()).or_insert(0usize) += 1;
    }
    let mut parity = trust_types::vc_context::ParityTally::default();
    for (func, &id) in funcs.iter().zip(ids) {
        let unique =
            counts.get(func.def_path.as_str()) == Some(&1) && !collisions.contains(&func.def_path);
        let admitted =
            super::with_scoped_rows(&mut parity, |rows| admit(tcx, func, id, unique, rows));
        match admitted {
            Ok(summary) => {
                if trace {
                    eprintln!("TRUST_CONSTRUCTOR_RETURN: {} MINTED", func.def_path);
                }
                minted.insert(func.def_path.clone(), summary);
            }
            Err(reason) if trace => {
                eprintln!("TRUST_CONSTRUCTOR_RETURN: {} DECLINED {reason:?}", func.def_path);
            }
            Err(_) => {}
        }
    }
    super::elide_audit::record_crate_parity(
        tcx,
        "crate:constructor-return",
        &parity,
        &[trust_types::vc_context::Oracle::Row],
    );
    minted
}
