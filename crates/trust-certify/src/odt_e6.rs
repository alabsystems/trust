// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! TG11: the interim MIR reader emits nominal ODT casesOn/projection terms.
//! Only the reader is MIR-specific. These terms use the same C2 identities as
//! the trust-ir producer; no flattened-parameter or integer-tag substitute is
//! used for the imported function's signature.
use std::collections::BTreeMap;

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_odt::{RustDecl, Scalar, Shape};
use trust_types::e6_odt::{Body, Leaf};
use trust_types::{Ty, VerifiableFunction};

use crate::odt::{CheckedFace, readmit_into, scalar_type};

/// Compiler-owned expected declarations paired with untrusted transport.
pub struct FaceInput {
    pub rust_path: String,
    pub declaration: RustDecl,
    pub transport: Vec<u8>,
}

fn scalar(ty: &Ty) -> Option<Scalar> {
    let spelling = trust_types::e6_expr::ty_spelling(ty);
    Scalar::from_rust_name(&spelling).ok()
}

fn agrees(ty: &Ty, face: &CheckedFace) -> bool {
    let Ty::Adt { fields, variants, .. } = ty else { return false };
    match &face.entry().declaration.shape {
        Shape::FieldlessEnum { variants: expected } => {
            expected.len() == variants.len()
                && expected.iter().zip(variants.iter()).all(|(e, v)| {
                    e.name == v.name
                        && e.discriminant == v.discriminant.to_string()
                        && v.fields.is_empty()
                })
        }
        Shape::ScalarStruct { fields: expected } => {
            variants.is_empty()
                && expected.len() == fields.len()
                && expected
                    .iter()
                    .zip(fields.iter())
                    .all(|(e, (n, t))| e.name == *n && Some(e.scalar) == scalar(t))
        }
    }
}

fn define(env: &mut Environment, name: &str, ty: Expr, value: Expr) -> Result<(), String> {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .map_err(|e| format!("TG11 kernel defining equation `{name}`: {e:?}"))
}

fn alias(env: &mut Environment, alias: &str, original: &str) -> Result<(), String> {
    let info =
        env.get_const(&Name::from_string(original)).ok_or("TG11 alias declaration absent")?;
    let type_ = info.type_.clone();
    let level_params = info.level_params.clone();
    let levels: Vec<_> = level_params.iter().cloned().map(Level::param).collect();
    env.add_decl(Declaration::Definition {
        name: Name::from_string(alias),
        level_params,
        type_,
        value: Expr::const_(Name::from_string(original), levels),
        is_reducible: true,
    })
    .map_err(|e| format!("TG11 checked alias `{alias}`: {e:?}"))
}

/// Readable spellings are reducible aliases of the nominal C2 declarations;
/// the stable hash identity remains in every imported signature and projection.
fn aliases(env: &mut Environment, path: &str, face: &CheckedFace) -> Result<(), String> {
    let name = format!(
        "{}{}",
        crate::clean_island::ODT_ALIAS_PREFIX,
        path.chars().map(|c| if c.is_alphanumeric() { c } else { '_' }).collect::<String>()
    );
    let actual = &face.entry().logical_face.kernel_name;
    alias(env, &name, actual)?;
    alias(env, &format!("{name}.casesOn"), &face.cases_on_name())?;
    match &face.entry().declaration.shape {
        Shape::FieldlessEnum { variants } => {
            for (v, ctor) in variants.iter().zip(face.constructor_names()) {
                alias(env, &format!("{name}.constructors.{}", v.name), &ctor)?;
            }
            let motive =
                Expr::lam(BinderInfo::Default, face.kernel_type(), scalar_type(Scalar::U8));
            let mut args = vec![motive, Expr::bvar(0)];
            for v in variants {
                args.push(literal(
                    v.discriminant.parse().map_err(|_| "TG11 tag outside i128")?,
                    Scalar::U8,
                )?);
            }
            let value = Expr::lam(
                BinderInfo::Default,
                face.kernel_type(),
                Expr::apps(
                    Expr::const_(
                        Name::from_string(&face.cases_on_name()),
                        vec![Level::succ(Level::zero())],
                    ),
                    args,
                ),
            );
            let tag_name = format!("{actual}.toTag");
            define(
                env,
                &tag_name,
                Expr::arrow(face.kernel_type(), scalar_type(Scalar::U8)),
                value,
            )?;
            alias(env, &format!("{name}.toTag"), &tag_name)?;
        }
        Shape::ScalarStruct { fields } => {
            alias(env, &format!("{name}.mk"), &face.constructor_names()[0])?;
            for (i, field) in fields.iter().enumerate() {
                let field_name = if field.name.chars().all(|c| c.is_ascii_digit()) {
                    format!("f{}", field.name)
                } else {
                    field.name.clone()
                };
                define(
                    env,
                    &format!("{name}.fields.{field_name}"),
                    Expr::arrow(face.kernel_type(), scalar_type(field.scalar)),
                    Expr::lam(
                        BinderInfo::Default,
                        face.kernel_type(),
                        Expr::proj(Name::from_string(actual), i as u32, Expr::bvar(0)),
                    ),
                )?;
            }
        }
    }
    Ok(())
}

fn literal(value: i128, scalar: Scalar) -> Result<Expr, String> {
    let (_, width) = scalar.carrier();
    let bits = match scalar {
        Scalar::U8 | Scalar::I8 => 8,
        Scalar::U16 | Scalar::I16 => 16,
        Scalar::U32 | Scalar::I32 => 32,
        Scalar::U64 | Scalar::I64 => 64,
        Scalar::Bool => return Err("integer at bool carrier".into()),
    };
    let signed = width.is_some();
    if (signed && (value < -(1i128 << (bits - 1)) || value >= (1i128 << (bits - 1))))
        || (!signed && (value < 0 || value >= (1i128 << bits)))
    {
        return Err("TG11 literal outside its scalar carrier".into());
    }
    let nat = Expr::nat_lit((value.rem_euclid(1i128 << bits)) as u64);
    Ok(if let Some(w) = width {
        Expr::apps(Expr::const_str("BitVec.ofNat"), [Expr::nat_lit(w), nat])
    } else {
        Expr::app(Expr::const_str(&format!("{}.ofNat", scalar.carrier().0)), nat)
    })
}

fn leaf(
    term: &Leaf,
    ret: Scalar,
    params: &[Ty],
    faces: &BTreeMap<String, CheckedFace>,
) -> Result<Expr, String> {
    let var = |i: usize| {
        params
            .len()
            .checked_sub(i + 1)
            .and_then(|v| u32::try_from(v).ok())
            .map(Expr::bvar)
            .ok_or_else(|| "TG11 parameter index".to_string())
    };
    match term {
        Leaf::Param(i) if params.get(*i).and_then(scalar) == Some(ret) => var(*i),
        Leaf::Field { param, field } => {
            let Some(Ty::Adt { name, fields, .. }) = params.get(*param) else {
                return Err("TG11 field base".into());
            };
            let face = faces.get(name).ok_or("TG11 field face absent")?;
            let (n, t) = fields.get(*field).ok_or("TG11 field index")?;
            let (index, s) = face.field(n).ok_or("TG11 named field absent")?;
            if index as usize != *field || s != ret || scalar(t) != Some(ret) {
                return Err("TG11 field identity/type mismatch".into());
            }
            Ok(Expr::proj(
                Name::from_string(&face.entry().logical_face.kernel_name),
                index,
                var(*param)?,
            ))
        }
        Leaf::Bool(b) if ret == Scalar::Bool => {
            Ok(Expr::const_str(if *b { "Bool.true" } else { "Bool.false" }))
        }
        Leaf::Int(v) => literal(*v, ret),
        _ => Err("TG11 leaf carrier mismatch".into()),
    }
}

/// Readmit each face once into this actual island environment, then mint only
/// closed bodies whose four facets and nominal declaration binding both hold.
/// No island elaboration occurs here: callers use CleanIslandSession::check.
pub(crate) fn admit(
    env: &mut Environment,
    inputs: &[FaceInput],
    functions: &[VerifiableFunction],
    facets: &trust_spec_elab::FacetTable,
) -> Result<Vec<(String, trust_spec_elab::Admission)>, String> {
    if functions.is_empty() {
        return Ok(Vec::new());
    }
    let mut scratch = env.clone();
    let mut faces = BTreeMap::new();
    for input in inputs {
        if faces.contains_key(&input.rust_path) {
            return Err("TG11 duplicate Rust type identity".into());
        }
        let face = readmit_into(&mut scratch, &input.declaration, &input.transport)?;
        aliases(&mut scratch, &input.rust_path, &face)?;
        faces.insert(input.rust_path.clone(), face);
    }
    let mut out = Vec::new();
    for func in functions {
        let Some(body) = trust_types::e6_odt::read(func) else { continue };
        if !facets.get(&func.def_path).is_some_and(trust_spec_elab::FnFacets::admissible) {
            continue;
        }
        let params: Vec<_> =
            func.body.locals[1..=func.body.arg_count].iter().map(|l| l.ty.clone()).collect();
        let mut types = Vec::new();
        for p in &params {
            types.push(if let Some(s) = scalar(p) {
                scalar_type(s)
            } else {
                let Ty::Adt { name, .. } = p else { return Err("TG11 non-value parameter".into()) };
                let face =
                    faces.get(name).ok_or_else(|| format!("TG11 no checked face for `{name}`"))?;
                if !agrees(p, face) {
                    return Err(format!(
                        "TG11 extracted type disagrees with checked face `{name}`"
                    ));
                }
                face.kernel_type()
            });
        }
        let ret = scalar(&func.body.return_ty).ok_or("TG11 return carrier")?;
        let ret_ty = scalar_type(ret);
        let value = match body {
            Body::Projection(l) => leaf(&l, ret, &params, &faces)?,
            Body::Cases { param, branches } => {
                let Ty::Adt { name, .. } = &params[param] else {
                    return Err("TG11 enum parameter".into());
                };
                let face = &faces[name];
                if face.constructor_names().len() != branches.len() {
                    return Err("TG11 incomplete enum match".into());
                }
                let motive = Expr::lam(BinderInfo::Default, face.kernel_type(), ret_ty.clone());
                let mut args = vec![motive, Expr::bvar((params.len() - param - 1) as u32)];
                for l in branches {
                    args.push(leaf(&l, ret, &params, &faces)?);
                }
                Expr::apps(
                    Expr::const_(
                        Name::from_string(&face.cases_on_name()),
                        vec![Level::succ(Level::zero())],
                    ),
                    args,
                )
            }
        };
        let name = format!(
            "trust_import_{}",
            func.def_path
                .chars()
                .map(|c| if c.is_alphanumeric() { c } else { '_' })
                .collect::<String>()
        );
        let value =
            types.iter().rev().fold(value, |v, t| Expr::lam(BinderInfo::Default, t.clone(), v));
        let ty = types.iter().rev().fold(ret_ty, |v, t| Expr::arrow(t.clone(), v));
        define(&mut scratch, &name, ty, value)?;
        let carriers = crate::clean_island::island_definition_carriers(&scratch, &name)
            .ok_or("TG11 exact carrier readback refused")?;
        let ret_domain = crate::clean_island::ty_to_domain(&func.body.return_ty);
        let admission = trust_spec_elab::Admission::reflected(&name, params.len())
            .with_declared_signature(ret_domain, Some(carriers));
        out.push((func.def_path.clone(), admission));
    }
    *env = scratch;
    Ok(out)
}

#[cfg(test)]
mod tests;
