// Trust: Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Trust: D-2 C1/C2 metadata producer and local/extern logical-face reader.
//! No MIR, verifier switch, layout query, or trust-ir producer participates.

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::{self, TyCtxt};
use trust_odt::{Entry, Field, RustDecl, Scalar, Shape, TypeKey, Variant};

pub(crate) fn rust_declaration(tcx: TyCtxt<'_>, def: DefId) -> Result<RustDecl, String> {
    // Trust: refusals are metadata DATA, not emitted diagnostics. Diagnostic
    // path trimming records a must-produce-diagnostic obligation and would ICE
    // on an otherwise valid unsupported ADT. Preserve fully qualified names
    // without weakening that diagnostic invariant or emitting a fake error.
    rustc_middle::ty::print::with_no_trimmed_paths!(rust_declaration_data(tcx, def))
}

fn rust_declaration_data(tcx: TyCtxt<'_>, def: DefId) -> Result<RustDecl, String> {
    let hash = tcx.def_path_hash(def);
    let key = TypeKey {
        stable_crate_id: hash.stable_crate_id().as_u64(),
        local_def_path_hash: hash.local_hash().as_u64(),
    };
    if tcx.generics_of(def).count() != 0 {
        return Err(format!(
            "TG10 ODT `{}` has generic parameters; instantiate a supported nongeneric type or wait for generic ODT faces",
            tcx.def_path_str(def)
        ));
    }
    let adt = tcx.adt_def(def);
    let shape = if adt.is_enum() {
        if adt.variants().iter().any(|v| !v.fields.is_empty()) {
            return Err(format!(
                "TG10 ODT `{}` has enum payloads; only fieldless enums have logical faces in this slice",
                tcx.def_path_str(def)
            ));
        }
        Shape::FieldlessEnum {
            variants: adt
                .discriminants(tcx)
                .map(|(idx, discr)| Variant {
                    name: adt.variant(idx).name.to_string(),
                    discriminant: discr.to_string(),
                })
                .collect(),
        }
    } else if adt.is_struct() {
        let fields = adt.non_enum_variant().fields.iter().map(|field| {
                let ty = tcx
                    .try_normalize_erasing_regions(
                        ty::TypingEnv::post_analysis(tcx, def),
                        field.ty(tcx, ty::GenericArgs::empty()),
                    )
                    .map_err(|_| format!("TG10 ODT field `{}` does not normalize to a supported scalar", tcx.def_path_str(field.did)))?;
            let scalar_name = match ty.kind() {
                ty::Bool => "bool", ty::Uint(ty::UintTy::U8) => "u8",
                ty::Uint(ty::UintTy::U16) => "u16", ty::Uint(ty::UintTy::U32) => "u32",
                ty::Uint(ty::UintTy::U64) => "u64", ty::Int(ty::IntTy::I8) => "i8",
                ty::Int(ty::IntTy::I16) => "i16", ty::Int(ty::IntTy::I32) => "i32",
                ty::Int(ty::IntTy::I64) => "i64",
                _ => return Err(format!("TG10 ODT field `{}` has unsupported type `{ty}`; use bool/u8..u64/i8..i64 or wait for a wider ODT slice", tcx.def_path_str(field.did))),
            };
            Ok(Field { name: field.name.to_string(), scalar: Scalar::from_rust_name(scalar_name)? })
        }).collect::<Result<Vec<_>, String>>()?;
        Shape::ScalarStruct { fields }
    } else {
        return Err(format!(
            "TG10 ODT `{}` is a union; unions have no value face in this slice",
            tcx.def_path_str(def)
        ));
    };
    let declaration = RustDecl { key, shape };
    declaration.validate()?;
    Ok(declaration)
}

/// Local transport provider. Every GENERATED face passes B1 before export,
/// including with verification off. Unsupported shapes get refusal-only rows.
pub(crate) fn odt_entry(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<Vec<u8>> {
    if !matches!(tcx.def_kind(def), DefKind::Struct | DefKind::Enum | DefKind::Union) {
        return None;
    }
    let declaration = match rust_declaration(tcx, def.to_def_id()) {
        Ok(decl) => decl,
        Err(reason) => return Some(trust_odt::refused_transport(&reason)),
    };
    // Trust: combined wire size can exceed the bound even when each source
    // member is admissible. This is an unsupported face, not ill-formed Rust.
    // Preflight authority-free bytes before kernel admission; B1 failures below
    // remain fatal, and only the exact admitted bytes may leave this provider.
    let transport =
        match trust_odt::Entry::generate(declaration.clone()).and_then(|entry| entry.encode()) {
            Ok(bytes) => bytes,
            Err(reason) => return Some(trust_odt::refused_transport(&reason)),
        };
    let mut env = clean_kernel::Environment::with_prelude();
    trust_certify::odt::readmit_into(&mut env, &declaration, &transport).unwrap_or_else(|reason| {
        tcx.dcx()
            .span_fatal(tcx.def_span(def), format!("Trust ODT face generation failed: {reason}"))
    });
    Some(transport)
}

/// TG11's cached query: local producer results already earned B1; imported
/// claims earn it locally against the actual imported Rust declaration.
/// The bytes remain transport, never a deserializable authority token.
pub(crate) fn logical_face(tcx: TyCtxt<'_>, def: DefId) -> Option<Vec<u8>> {
    if !matches!(tcx.def_kind(def), DefKind::Struct | DefKind::Enum | DefKind::Union) {
        return None;
    }
    let refuse = |reason: String| -> ! {
        tcx.dcx().span_fatal(tcx.def_span(def), format!("Trust ODT logical face refused: {reason}"))
    };
    let bytes = tcx.trust_odt_entry(def).unwrap_or_else(|| {
        refuse(format!("`{}` has no ODT metadata row; rebuild its defining crate with an ODT-capable Trust compiler", tcx.def_path_str(def)))
    });
    let entry = Entry::decode(bytes).unwrap_or_else(|reason| refuse(reason));
    if !def.is_local() {
        let declaration = rust_declaration(tcx, def).unwrap_or_else(|reason| refuse(reason));
        let mut env = clean_kernel::Environment::with_prelude();
        trust_certify::odt::readmit_into(&mut env, &declaration, bytes)
            .unwrap_or_else(|reason| refuse(reason));
    }
    Some(entry.encode().unwrap_or_else(|reason| refuse(reason)))
}
