// Trust: Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Trust: TG11's interim MIR-lane ODT adapter (COMPILE-TIME-FACTS-1).
//! Keep source-signature/guard admission separate from the MIR-free C1/C2
//! producer. This adapter is removed with the MIR-derived E6 reader at D-1/D-7.
use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{self, TyCtxt};
use trust_odt::Entry;

use crate::trust_odt::rust_declaration;

// Trust: the legacy MIR carrier erases char/host-sized distinctions. Scope
// admission against the actual normalized Rust signature before reading it.
fn e6_signature<'tcx>(tcx: TyCtxt<'tcx>, local: LocalDefId) -> Result<ty::FnSig<'tcx>, String> {
    tcx.try_normalize_erasing_regions(
        ty::TypingEnv::post_analysis(tcx, local.to_def_id()),
        ty::Unnormalized::new_wip(tcx.fn_sig(local).instantiate_identity().skip_binder()),
    )
    .map_err(|_| "TG11 ODT signature cannot normalize to the supported value slice".into())
}

fn e6_scalar(ty: ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::Bool
            | ty::Uint(ty::UintTy::U8 | ty::UintTy::U16 | ty::UintTy::U32 | ty::UintTy::U64)
            | ty::Int(ty::IntTy::I8 | ty::IntTy::I16 | ty::IntTy::I32 | ty::IntTy::I64)
    )
}

// Trust: TG11 only reads repr(u8) fieldless enums with explicit tags and
// direct scalar structs. Guard rejection consults HIR before optimization can
// erase a guard (KNOWN_HAZARDS); it does not confer proof authority.
pub(crate) fn e6_faces(
    tcx: TyCtxt<'_>,
    functions: &[trust_types::VerifiableFunction],
) -> Result<(Vec<trust_certify::odt_e6::FaceInput>, Vec<trust_types::VerifiableFunction>), String> {
    let mut inputs = std::collections::BTreeMap::new();
    let mut eligible = Vec::new();
    let candidates: std::collections::BTreeMap<_, _> = functions
        .iter()
        .filter(|f| trust_types::e6_odt::read(f).is_some())
        .map(|f| (f.def_path.as_str(), f))
        .collect();
    if candidates.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }
    for local in tcx.hir_body_owners() {
        if !matches!(tcx.def_kind(local), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let path = trust_mir_extract::safe_def_path_str(tcx, local.to_def_id());
        let Some(&func) = candidates.get(path.as_str()) else { continue };
        if e6_refusal(tcx, local).is_some() {
            continue;
        }
        let sig = e6_signature(tcx, local)?;
        for input in sig.inputs() {
            let ty::Adt(adt, _) = input.kind() else { continue };
            let rust_path = trust_mir_extract::safe_def_path_str(tcx, adt.did());
            if inputs.contains_key(&rust_path) {
                continue;
            }
            let declaration = rust_declaration(tcx, adt.did())?;
            let transport = tcx
                .trust_odt_logical_face(adt.did())
                .ok_or_else(|| format!("TG11 no logical face for `{rust_path}`"))?
                .clone();
            inputs.insert(
                rust_path.clone(),
                trust_certify::odt_e6::FaceInput { rust_path, declaration, transport },
            );
        }
        eligible.push(func.clone());
    }
    Ok((inputs.into_values().collect(), eligible))
}

// Trust: named by the import refusal diagnostic, never a general Rust error.
pub(crate) fn e6_refusal(tcx: TyCtxt<'_>, local: LocalDefId) -> Option<String> {
    use rustc_hir::intravisit::{self, Visitor};
    struct Guards(bool);
    impl<'v> Visitor<'v> for Guards {
        fn visit_expr(&mut self, expr: &'v rustc_hir::Expr<'v>) {
            if let rustc_hir::ExprKind::Match(_, arms, _) = expr.kind {
                self.0 |= arms.iter().any(|a| a.guard.is_some());
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let source_sig = tcx.fn_sig(local).instantiate_identity().skip_binder();
    let possible_adt =
        source_sig.inputs().iter().any(|t| matches!(t.kind(), ty::Adt(..) | ty::Alias(..)));
    if !possible_adt {
        return None;
    }
    let sig = match e6_signature(tcx, local) {
        Ok(sig) => sig,
        Err(reason) => return Some(reason),
    };
    if !sig.inputs().iter().any(|t| matches!(t.kind(), ty::Adt(..))) {
        return None;
    }
    let mut guards = Guards(false);
    guards.visit_body(tcx.hir_body_owned_by(local));
    if guards.0 {
        return Some(
            "TG11 guarded enum match: only an exhaustive unguarded enum match is importable".into(),
        );
    }
    if !e6_scalar(sig.output()) {
        return Some("TG11 ODT return type is outside the fixed-width scalar slice (bool/u8..u64/i8..i64); char and host-sized integers are not erased into an admitted carrier".into());
    }
    for (position, input) in sig.inputs().iter().enumerate() {
        if !matches!(input.kind(), ty::Adt(..)) && !e6_scalar(*input) {
            return Some(format!(
                "TG11 ODT parameter {position} is outside the by-value fixed-width scalar slice (bool/u8..u64/i8..i64); char, host-sized integers and borrows are unsupported"
            ));
        }
    }
    for input in sig.inputs() {
        let ty::Adt(adt, _) = input.kind() else { continue };
        // Trust: ordinary, uncited Rust must not become a fatal ODT request.
        // Bound the source shape and transport before requesting the checked
        // face; a cited unsupported body receives this same named refusal.
        let declaration = match rust_declaration(tcx, adt.did()) {
            Ok(declaration) => declaration,
            Err(reason) => return Some(reason),
        };
        if let Err(reason) = Entry::generate(declaration).and_then(|e| e.encode()) {
            return Some(reason);
        }
        if tcx.trust_odt_entry(adt.did()).is_none() {
            return Some(format!(
                "TG11 no ODT metadata for `{}`; rebuild its defining crate",
                trust_mir_extract::safe_def_path_str(tcx, adt.did())
            ));
        }
        if adt.is_enum() {
            if adt.repr().int != Some(rustc_abi::IntegerType::Fixed(rustc_abi::Integer::I8, false))
                || adt.variants().iter().any(|v| !matches!(v.discr, ty::VariantDiscr::Explicit(_)))
            {
                return Some(format!(
                    "TG11 enum `{}` requires repr(u8) and explicit discriminants for an exhaustive enum match",
                    trust_mir_extract::safe_def_path_str(tcx, adt.did())
                ));
            }
        }
    }
    None
}
