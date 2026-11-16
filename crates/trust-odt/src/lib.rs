// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! D-2 C1/C2's first slice. Everything in this crate is data, never kernel authority.
//! A decoded entry must be bound to the compiler's own declaration and readmitted
//! by `trust_certify::odt`. In particular, B1 does not establish B2 or B3.
#![forbid(unsafe_code)]

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Stable nominal identity, including the crate half of rustc's DefPathHash.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TypeKey {
    pub stable_crate_id: u64,
    pub local_def_path_hash: u64,
}

/// The root of every nominal ODT identity [`TypeKey::kernel_name`] mints. The compiler owns
/// the whole namespace: Clean islands may not declare into it (TG16, `trust-certify`'s
/// `reserved_namespace_error`). One spelling, so the minting and the refusal cannot drift.
pub const KERNEL_ROOT: &str = "TrustOdt";

impl TypeKey {
    /// An injective identifier; neither display paths nor local DefIndex enter it.
    pub fn kernel_name(self) -> String {
        format!("{KERNEL_ROOT}.k{:016x}_{:016x}", self.stable_crate_id, self.local_def_path_hash)
    }
}

/// The coordinator-agreed, target-independent vocabulary. No host-width defaults.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Scalar {
    Bool,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
}

impl Scalar {
    pub fn from_rust_name(name: &str) -> Result<Self, String> {
        match name {
            "bool" => Ok(Self::Bool),
            "u8" => Ok(Self::U8),
            "u16" => Ok(Self::U16),
            "u32" => Ok(Self::U32),
            "u64" => Ok(Self::U64),
            "i8" => Ok(Self::I8),
            "i16" => Ok(Self::I16),
            "i32" => Ok(Self::I32),
            "i64" => Ok(Self::I64),
            _ => Err(format!(
                "TG10 ODT scalar `{name}` is outside bool/u8..u64/i8..i64; use an admitted fixed-width scalar or wait for a wider ODT slice"
            )),
        }
    }

    /// Unsigned carriers match E6; signed carriers preserve their exact bits.
    pub fn carrier(self) -> (&'static str, Option<u64>) {
        match self {
            Self::Bool => ("Bool", None),
            Self::U8 => ("UInt8", None),
            Self::U16 => ("UInt16", None),
            Self::U32 => ("UInt32", None),
            Self::U64 => ("UInt64", None),
            Self::I8 => ("BitVec", Some(8)),
            Self::I16 => ("BitVec", Some(16)),
            Self::I32 => ("BitVec", Some(32)),
            Self::I64 => ("BitVec", Some(64)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Field {
    /// Rust's field identity: the actual identifier, or the decimal tuple index.
    pub name: String,
    pub scalar: Scalar,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Variant {
    pub name: String,
    /// Canonical mathematical integer, not a host-sized enum cast.
    pub discriminant: String,
}

/// All vectors are in declaration order, never sorted by name or tag.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub enum Shape {
    FieldlessEnum { variants: Vec<Variant> },
    ScalarStruct { fields: Vec<Field> },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RustDecl {
    pub key: TypeKey,
    pub shape: Shape,
}

/// The generator's candidate. Public and mutable deliberately: it is a claim.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LogicalFace {
    pub kernel_name: String,
    pub shape: Shape,
}

/// C1's initial representation decision: all admitted fields are inline values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Representation {
    Inline,
}

/// No serialized entry can manufacture B2 standing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IsoState {
    Pending,
}

/// This slice establishes no user-authored validity or safety invariant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InvariantState {
    NotEstablished,
}

/// Versioned rmeta transport. The digest detects damage, not dishonest producers.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Entry {
    pub version: u32,
    pub declaration: RustDecl,
    pub logical_face: LogicalFace,
    pub content_digest: String,
}

/// Encode a Rust member name injectively into a kernel name segment.
pub fn member_name(rust_name: &str) -> String {
    let mut out = String::from("n");
    for byte in rust_name.bytes() {
        use std::fmt::Write;
        write!(out, "{byte:02x}").expect("writing to a String");
    }
    out
}

impl RustDecl {
    pub fn logical_face(&self) -> LogicalFace {
        LogicalFace { kernel_name: self.key.kernel_name(), shape: self.shape.clone() }
    }

    pub fn validate(&self) -> Result<(), String> {
        validate_shape(&self.shape)
    }
}

fn validate_shape(shape: &Shape) -> Result<(), String> {
    let mut names = BTreeSet::new();
    let members: Vec<&str> = match shape {
        Shape::FieldlessEnum { variants } => {
            let mut tags = BTreeSet::new();
            for variant in variants {
                let canonical = variant
                    .discriminant
                    .parse::<i128>()
                    .map(|v| v.to_string())
                    .or_else(|_| variant.discriminant.parse::<u128>().map(|v| v.to_string()))
                    .map_err(|_| "ODT enum discriminant is not an integer".to_string())?;
                if canonical != variant.discriminant || !tags.insert(canonical) {
                    return Err("ODT enum discriminants must be canonical and distinct".into());
                }
            }
            variants.iter().map(|v| v.name.as_str()).collect()
        }
        Shape::ScalarStruct { fields } => fields.iter().map(|f| f.name.as_str()).collect(),
    };
    if members.len() > 4096 {
        return Err("ODT slice exceeds 4096 members".into());
    }
    for name in members {
        if name.is_empty() || name.len() > 1024 || !names.insert(name) {
            return Err("ODT member identities must be nonempty, bounded and distinct".into());
        }
    }
    Ok(())
}

impl Entry {
    pub fn generate(declaration: RustDecl) -> Result<Self, String> {
        let logical_face = declaration.logical_face();
        Self::candidate(declaration, logical_face)
    }

    /// Construct transport for a candidate; this does not establish correspondence.
    pub fn candidate(declaration: RustDecl, logical_face: LogicalFace) -> Result<Self, String> {
        declaration.validate()?;
        let mut entry =
            Self { version: 1, declaration, logical_face, content_digest: String::new() };
        entry.content_digest = entry.digest()?;
        entry.validate_transport()?;
        Ok(entry)
    }

    fn digest(&self) -> Result<String, String> {
        let bytes = serde_json::to_vec(&(
            "trust-odt-v1",
            self.version,
            &self.declaration,
            &self.logical_face,
        ))
        .map_err(|e| e.to_string())?;
        Ok(format!("{:x}", Sha256::digest(bytes)))
    }

    /// No kernel claim is present on this wire, including after a valid decode.
    pub fn encode(&self) -> Result<Vec<u8>, String> {
        self.validate_transport()?;
        let bytes = serde_json::to_vec(self).map_err(|e| e.to_string())?;
        if bytes.len() > 1024 * 1024 {
            return Err("ODT transport exceeds 1 MiB".into());
        }
        Ok(bytes)
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > 1024 * 1024 {
            return Err("ODT transport exceeds 1 MiB".into());
        }
        if let Some(reason) = bytes.strip_prefix(b"trust-odt-refused-v1:") {
            return Err(String::from_utf8_lossy(reason).into_owned());
        }
        let entry: Self = serde_json::from_slice(bytes).map_err(|e| format!("ODT decode: {e}"))?;
        entry.validate_transport()?;
        if serde_json::to_vec(&entry).map_err(|e| e.to_string())? != bytes {
            return Err("ODT transport is not canonical".into());
        }
        Ok(entry)
    }

    pub fn validate_transport(&self) -> Result<(), String> {
        if self.version != 1 || self.content_digest != self.digest()? {
            return Err("ODT version/content digest mismatch".into());
        }
        self.declaration.validate()?;
        validate_shape(&self.logical_face.shape)?;
        if self.logical_face.kernel_name != self.declaration.key.kernel_name() {
            return Err("ODT face has the wrong nominal TypeKey".into());
        }
        Ok(())
    }

    pub fn iso(&self) -> IsoState {
        IsoState::Pending
    }
    pub fn representation(&self) -> Representation {
        Representation::Inline
    }
    pub fn authored(&self) -> trust_symbols::Producer {
        trust_symbols::Producer::Rust
    }
    pub fn capability(&self) -> trust_symbols::Capability {
        trust_symbols::Capability::Proof
    }
    pub fn validity_invariant(&self) -> InvariantState {
        InvariantState::NotEstablished
    }
    pub fn safety_invariant(&self) -> InvariantState {
        InvariantState::NotEstablished
    }
}

/// Unsupported ADTs keep an explicit row without making ordinary Rust ill-formed.
/// Requesting their logical face surfaces this reason; no B1 fact is attached.
pub fn refused_transport(reason: &str) -> Vec<u8> {
    let mut bytes = b"trust-odt-refused-v1:".to_vec();
    bytes.extend_from_slice(reason.as_bytes());
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vocabulary_is_explicit_and_target_independent() {
        for name in ["bool", "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"] {
            assert!(Scalar::from_rust_name(name).is_ok());
        }
        for name in ["usize", "isize", "char", "f32", "f64", "u128", "i128", "&u8"] {
            assert!(Scalar::from_rust_name(name).unwrap_err().contains(name));
        }
    }

    #[test]
    fn refusal_rows_cannot_bypass_the_transport_limit() {
        let ordinary = refused_transport("TG10 ODT usize field is unsupported");
        assert!(Entry::decode(&ordinary).unwrap_err().contains("usize"));
        let oversized = refused_transport(&"x".repeat(1024 * 1024));
        assert_eq!(Entry::decode(&oversized).unwrap_err(), "ODT transport exceeds 1 MiB");
    }

    #[test]
    fn transport_is_data_and_binds_identity_and_order() {
        let decl = RustDecl {
            key: TypeKey { stable_crate_id: 7, local_def_path_hash: 9 },
            shape: Shape::ScalarStruct {
                fields: vec![Field { name: "0".into(), scalar: Scalar::I16 }],
            },
        };
        let entry = Entry::generate(decl).unwrap();
        let bytes = entry.encode().unwrap();
        assert_eq!(Entry::decode(&bytes).unwrap(), entry);
        assert_eq!(entry.iso(), IsoState::Pending);
        let mut damaged = bytes.clone();
        damaged[1] ^= 1;
        assert!(Entry::decode(&damaged).is_err());
        let mut different = entry.declaration.clone();
        different.key.stable_crate_id += 1;
        assert_ne!(Entry::generate(different).unwrap().content_digest, entry.content_digest);
        assert_ne!(member_name("a_b"), member_name("a.b"));
        assert_ne!(member_name("é"), member_name("e"));
        let mut padded = bytes;
        padded.push(b' ');
        assert!(Entry::decode(&padded).is_err());
    }
}
