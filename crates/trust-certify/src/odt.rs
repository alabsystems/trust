// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Kernel B1 admission for D-2's fieldless-enum/scalar-struct slice.
//!
//! The trusted reader quotes registered declarations independently of the face
//! generator. The kernel checks equality of the full quoted data, not a digest.
//! A separate equality binds the ordered enum discriminant table. Neither check
//! proves the Rust reader, B2 representation isomorphism, or B3 memory layout.
//! Transport is untrusted; only this module can construct `CheckedFace`.

use clean_kernel::expr::{BigNat, Literal};
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, ExprKind, InductiveDecl,
    InductiveType, Level, Name,
};
use serde::Serialize;
use trust_odt::{Entry, LogicalFace, RustDecl, Scalar, Shape, member_name};

/// A local kernel return. No Deserialize, Default or public constructor.
///
/// ```compile_fail
/// fn forge(entry: trust_odt::Entry) -> trust_certify::odt::CheckedFace {
///     trust_certify::odt::CheckedFace { entry, evidence: vec![] }
/// }
/// ```
#[derive(Clone, Debug)]
pub struct CheckedFace {
    entry: Entry,
    evidence: Vec<(Expr, Expr)>,
}

impl CheckedFace {
    pub fn entry(&self) -> &Entry {
        &self.entry
    }
    /// The own B1 goals and their checked proof terms, suitable as fact inputs.
    pub fn evidence(&self) -> &[(Expr, Expr)] {
        &self.evidence
    }
    pub fn kernel_type(&self) -> Expr {
        Expr::const_str(&self.entry.logical_face.kernel_name)
    }
    pub fn cases_on_name(&self) -> String {
        format!("{}.casesOn", self.entry.logical_face.kernel_name)
    }
    pub fn constructor_names(&self) -> Vec<String> {
        constructor_names(&self.entry.logical_face)
    }
    /// TG11 projects by this declaration index, with the exact admitted scalar.
    pub fn field(&self, rust_name: &str) -> Option<(u32, Scalar)> {
        let Shape::ScalarStruct { fields } = &self.entry.declaration.shape else {
            return None;
        };
        fields
            .iter()
            .enumerate()
            .find(|(_, f)| f.name == rust_name)
            .and_then(|(i, f)| Some((u32::try_from(i).ok()?, f.scalar)))
    }
}

pub fn scalar_type(scalar: Scalar) -> Expr {
    let (name, width) = scalar.carrier();
    let head = Expr::const_str(name);
    match width {
        Some(n) => Expr::app(head, Expr::nat_lit(n)),
        None => head,
    }
}

fn constructor_names(face: &LogicalFace) -> Vec<String> {
    match &face.shape {
        Shape::FieldlessEnum { variants } => variants
            .iter()
            .map(|v| format!("{}.{}", face.kernel_name, member_name(&v.name)))
            .collect(),
        Shape::ScalarStruct { .. } => vec![format!("{}.mk", face.kernel_name)],
    }
}

fn register(env: &mut Environment, face: &LogicalFace) -> Result<(), String> {
    let name = Name::from_string(&face.kernel_name);
    let result = Expr::const_(name.clone(), vec![]);
    let constructors = match &face.shape {
        Shape::FieldlessEnum { .. } => constructor_names(face)
            .into_iter()
            .map(|n| Constructor { name: Name::from_string(&n), type_: result.clone() })
            .collect(),
        Shape::ScalarStruct { fields } => {
            let mut ty = result;
            for field in fields.iter().rev() {
                ty = Expr::pi(BinderInfo::Default, scalar_type(field.scalar), ty);
            }
            vec![Constructor {
                name: Name::from_string(&format!("{}.mk", face.kernel_name)),
                type_: ty,
            }]
        }
    };
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::sort(Level::succ(Level::zero())),
            constructors,
        }],
    })
    .map_err(|e| format!("ODT inductive registration: {e:?}"))?;
    if let Shape::ScalarStruct { fields } = &face.shape {
        env.register_structure_fields(
            name,
            fields.iter().map(|f| Name::from_string(&member_name(&f.name))).collect(),
        )
        .map_err(|e| format!("ODT field registration: {e:?}"))?;
    }
    if let Shape::FieldlessEnum { variants } = &face.shape {
        // The ordered table is an actual checked kernel definition associated with
        // this face, not metadata supplied back to the expected-side reader.
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&format!("{}.discriminants", face.kernel_name)),
            level_params: vec![],
            type_: Expr::const_str("Nat"),
            value: quote(variants)?,
            is_reducible: true,
        })
        .map_err(|e| format!("ODT discriminant registration: {e:?}"))?;
    }
    Ok(())
}

#[derive(Serialize)]
enum KernelShape {
    Enum(Vec<String>),
    Struct(String, Vec<(String, Scalar)>),
}

fn expected(decl: &RustDecl) -> KernelShape {
    let name = decl.key.kernel_name();
    match &decl.shape {
        Shape::FieldlessEnum { variants } => KernelShape::Enum(
            variants.iter().map(|v| format!("{name}.{}", member_name(&v.name))).collect(),
        ),
        Shape::ScalarStruct { fields } => KernelShape::Struct(
            format!("{name}.mk"),
            fields.iter().map(|f| (member_name(&f.name), f.scalar)).collect(),
        ),
    }
}

// Independent of the generator's Scalar::carrier table: a wrong generated
// width or signedness must not be interpreted back using that same mistake.
fn read_scalar(ty: &Expr) -> Option<Scalar> {
    match ty.kind() {
        ExprKind::Const(name, levels) if levels.is_empty() => match name.to_string().as_str() {
            "Bool" => Some(Scalar::Bool),
            "UInt8" => Some(Scalar::U8),
            "UInt16" => Some(Scalar::U16),
            "UInt32" => Some(Scalar::U32),
            "UInt64" => Some(Scalar::U64),
            _ => None,
        },
        ExprKind::App(head, width) if **head == Expr::const_str("BitVec") => {
            let ExprKind::Lit(Literal::Nat(width)) = width.kind() else {
                return None;
            };
            match width.to_u64()? {
                8 => Some(Scalar::I8),
                16 => Some(Scalar::I16),
                32 => Some(Scalar::I32),
                64 => Some(Scalar::I64),
                _ => None,
            }
        }
        _ => None,
    }
}

fn readback(env: &Environment, decl: &RustDecl) -> Result<KernelShape, String> {
    let name = Name::from_string(&decl.key.kernel_name());
    let info = env.get_inductive(&name).ok_or("ODT registered inductive missing")?;
    if info.num_params != 0
        || info.num_indices != 0
        || info.is_recursive
        || info.type_ != Expr::sort(Level::succ(Level::zero()))
    {
        return Err("ODT readback is not a monomorphic nonrecursive Type".into());
    }
    let result = Expr::const_(name.clone(), vec![]);
    match &decl.shape {
        Shape::FieldlessEnum { .. } => {
            for ctor in &info.constructor_names {
                let c = env.get_constructor(ctor).ok_or("ODT constructor missing")?;
                if c.type_ != result || c.num_params != 0 || c.num_fields != 0 {
                    return Err("ODT enum readback has a payload or wrong result".into());
                }
            }
            Ok(KernelShape::Enum(info.constructor_names.iter().map(ToString::to_string).collect()))
        }
        Shape::ScalarStruct { .. } => {
            let [ctor] = info.constructor_names.as_slice() else {
                return Err("ODT struct must have one constructor".into());
            };
            let c = env.get_constructor(ctor).ok_or("ODT struct constructor missing")?;
            let names = env
                .get_structure_field_names(&name)
                .ok_or("ODT struct field identities missing")?;
            let mut fields = Vec::new();
            let mut ty = &c.type_;
            for field in names {
                let ExprKind::Pi(_, domain, body) = ty.kind() else {
                    return Err("ODT struct telescope too short".into());
                };
                let scalar =
                    read_scalar(domain).ok_or("ODT struct readback has an unsupported scalar")?;
                fields.push((field.to_string(), scalar));
                ty = body;
            }
            if *ty != result || c.num_params != 0 || c.num_fields as usize != fields.len() {
                return Err("ODT struct telescope/result mismatch".into());
            }
            Ok(KernelShape::Struct(ctor.to_string(), fields))
        }
    }
}

/// Inject the COMPLETE canonical data into Nat (not its hash). The high sentinel
/// limb makes byte length injective, including trailing zero bytes. Serialization
/// and registered-declaration readback remain an explicitly trusted adapter.
fn quote<T: Serialize + ?Sized>(data: &T) -> Result<Expr, String> {
    let bytes = serde_json::to_vec(data).map_err(|e| e.to_string())?;
    let mut limbs = Vec::with_capacity(bytes.len().div_ceil(8) + 2);
    limbs.push(bytes.len() as u64);
    for chunk in bytes.chunks(8) {
        let mut word = [0; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        limbs.push(u64::from_le_bytes(word));
    }
    limbs.push(1);
    Ok(Expr::bignat_lit(BigNat::from_limbs(limbs)))
}

fn check_equality(env: &Environment, left: Expr, right: Expr) -> Result<(Expr, Expr), String> {
    let nat = Expr::const_str("Nat");
    let level = Level::succ(Level::zero());
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
        [nat.clone(), left, right.clone()],
    );
    let proof = Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![level]), [nat, right]);
    env.check_decl_readonly_strict(&Declaration::Theorem {
        name: Name::from_string(&format!("{}.b1", trust_odt::KERNEL_ROOT)),
        level_params: vec![],
        type_: goal.clone(),
        value: proof.clone(),
    })
    .map_err(|e| format!("ODT B1 correspondence refused by kernel: {e:?}"))?;
    let audit = env.audit_certification(&goal, &proof);
    if !audit.is_certified() || !audit.foundations.is_empty() {
        return Err(format!(
            "ODT B1 audit refused: {:?}; foundations {:?}",
            audit.issues, audit.foundations
        ));
    }
    Ok((goal, proof))
}

/// Bind untrusted transport to the compiler's own Rust datum, then re-earn B1.
/// Changes to the caller's environment commit only after all checks succeed.
pub fn readmit_into(
    env: &mut Environment,
    rust_decl: &RustDecl,
    bytes: &[u8],
) -> Result<CheckedFace, String> {
    let entry = Entry::decode(bytes)?;
    if &entry.declaration != rust_decl {
        return Err("ODT transport does not match the compiler's Rust declaration/TypeKey".into());
    }
    let mut scratch = env.clone();
    register(&mut scratch, &entry.logical_face)?;
    let mut evidence = vec![check_equality(
        &scratch,
        quote(&readback(&scratch, rust_decl)?)?,
        quote(&expected(rust_decl))?,
    )?];
    if let Shape::FieldlessEnum { variants } = &rust_decl.shape {
        let tags = Expr::const_str(&format!("{}.discriminants", rust_decl.key.kernel_name()));
        evidence.push(check_equality(&scratch, tags, quote(variants)?)?);
    }
    *env = scratch;
    Ok(CheckedFace { entry, evidence })
}

/// Generate and check a local C2 face through the same readmission path as rmeta.
pub fn generate_into(env: &mut Environment, declaration: RustDecl) -> Result<CheckedFace, String> {
    let entry = Entry::generate(declaration)?;
    readmit_into(env, &entry.declaration, &entry.encode()?)
}

#[cfg(test)]
mod tests;
