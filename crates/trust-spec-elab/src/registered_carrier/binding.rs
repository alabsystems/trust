// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Passive descriptor codec. No decoder, environment mutation or proof status.
//!
//! All integers are fixed-width little endian; lists/byte strings have u64
//! lengths, enums/options have explicit tags. Names are root-to-leaf typed
//! components. Expr uses Clean's canonical structural codec, which serializes
//! NameInner (not Display or cached_hash), bounds depth/nodes/bytes, and rejects
//! unsupported encodings. Its temporary per-expression allocation has its own
//! 64 MiB bound; the complete descriptor below has the tighter 8 MiB bound.

#[cfg(not(target_arch = "wasm32"))]
use clean_auto::bridge::ay_contract::serialize_term;
use clean_kernel::name::NameInner;

use super::*;

const CARRIER_DOMAIN: &[u8] = b"trust-spec-elab.registered-adt.binding.v1\0";
const DECLARATION_DOMAIN: &[u8] = b"trust-spec-elab.declaration.binding.v1\0";
const ENVIRONMENT_DOMAIN: &[u8] = b"trust-spec-elab.environment.binding.v1\0";
const MAX_BYTES: usize = 8 * 1024 * 1024;
pub(super) const MAX_ENTRIES: usize = 4096;

pub(super) fn carrier(handle: &RegisteredAdt) -> Result<Vec<u8>, String> {
    let RegisteredAdt { schema, arguments, type_, dependencies } = handle;
    let AdtSchema { name, type_: former, num_params, constructors } = schema;
    let mut out = Writer::new(CARRIER_DOMAIN)?;
    out.expr(type_)?;
    out.name(name)?;
    out.expr(former)?;
    out.u32(*num_params)?;
    out.count(constructors.len())?;
    for ConstructorSchema { name, type_ } in constructors {
        out.name(name)?;
        out.expr(type_)?;
    }
    out.count(arguments.len())?;
    for argument in arguments {
        out.expr(argument)?;
    }
    out.count(dependencies.len())?;
    // BTreeMap uses Name's structural order, not its display spelling.
    for (key, record) in dependencies {
        out.name(key)?;
        out.record(record)?;
    }
    Ok(out.bytes)
}

pub(super) fn declaration(key: &Name, record: &DeclarationSnapshot) -> Result<Vec<u8>, String> {
    let mut out = Writer::new(DECLARATION_DOMAIN)?;
    out.name(key)?;
    out.record(record)?;
    Ok(out.bytes)
}

pub(super) fn environment(
    roots: &[Name],
    dependencies: &BTreeMap<Name, DeclarationSnapshot>,
) -> Result<Vec<u8>, String> {
    let mut out = Writer::new(ENVIRONMENT_DOMAIN)?;
    out.names(roots)?;
    out.count(dependencies.len())?;
    for (key, record) in dependencies {
        out.name(key)?;
        out.record(record)?;
    }
    Ok(out.bytes)
}

struct Writer {
    bytes: Vec<u8>,
}

impl Writer {
    fn new(domain: &[u8]) -> Result<Self, String> {
        let mut result = Self { bytes: Vec::with_capacity(256) };
        result.append(domain)?;
        Ok(result)
    }

    fn append(&mut self, bytes: &[u8]) -> Result<(), String> {
        if bytes.len() > MAX_BYTES.saturating_sub(self.bytes.len()) {
            return Err("canonical carrier binding exceeds 8 MiB".into());
        }
        self.bytes
            .try_reserve(bytes.len())
            .map_err(|_| "canonical carrier binding allocation refused".to_string())?;
        self.bytes.extend_from_slice(bytes);
        Ok(())
    }

    fn byte(&mut self, value: u8) -> Result<(), String> {
        self.append(&[value])
    }
    fn boolean(&mut self, value: bool) -> Result<(), String> {
        self.byte(u8::from(value))
    }
    fn u32(&mut self, value: u32) -> Result<(), String> {
        self.append(&value.to_le_bytes())
    }
    fn u64(&mut self, value: u64) -> Result<(), String> {
        self.append(&value.to_le_bytes())
    }

    fn count(&mut self, count: usize) -> Result<(), String> {
        if count > MAX_ENTRIES {
            return Err("canonical binding list exceeds 4096 entries".into());
        }
        self.u64(u64::try_from(count).map_err(|_| "binding count overflow")?)
    }

    fn field(&mut self, value: &[u8]) -> Result<(), String> {
        let length = value.len().checked_add(8).ok_or("binding field length overflow")?;
        if length > MAX_BYTES.saturating_sub(self.bytes.len()) {
            return Err("canonical carrier binding exceeds 8 MiB".into());
        }
        self.u64(u64::try_from(value.len()).map_err(|_| "binding field length overflow")?)?;
        self.append(value)
    }

    #[cfg(not(target_arch = "wasm32"))]
    fn expr(&mut self, value: &Expr) -> Result<(), String> {
        let bytes = serialize_term(value)
            .map_err(|_| "canonical Clean expression encoding refused".to_string())?;
        self.field(&bytes)
    }

    #[cfg(target_arch = "wasm32")]
    fn expr(&mut self, _value: &Expr) -> Result<(), String> {
        Err("canonical Clean term codec is unavailable on wasm32".into())
    }

    fn name(&mut self, value: &Name) -> Result<(), String> {
        let mut parts = Vec::new();
        let mut current = value;
        loop {
            match current.inner() {
                NameInner::Anon => break,
                part @ (NameInner::Str(parent, _) | NameInner::Num(parent, _)) => {
                    if parts.len() == MAX_ENTRIES {
                        return Err("canonical Name exceeds 4096 components".into());
                    }
                    parts.push(part);
                    current = parent;
                }
            }
        }
        self.count(parts.len())?;
        for part in parts.into_iter().rev() {
            match part {
                NameInner::Str(_, text) => {
                    self.byte(1)?;
                    self.field(text.as_bytes())?;
                }
                NameInner::Num(_, number) => {
                    self.byte(2)?;
                    self.u64(*number)?;
                }
                NameInner::Anon => return Err("invalid anonymous Name component".into()),
            }
        }
        Ok(())
    }

    fn names(&mut self, values: &[Name]) -> Result<(), String> {
        self.count(values.len())?;
        for value in values {
            self.name(value)?;
        }
        Ok(())
    }

    fn record(&mut self, record: &DeclarationSnapshot) -> Result<(), String> {
        // Exhaustive destructuring prevents a new snapshot field being silently
        // dropped from this format. Such changes need an explicit wire decision.
        let DeclarationSnapshot {
            name,
            levels,
            type_,
            value,
            reducible,
            reducibility,
            kind,
            verification,
            unsafe_,
            partial,
            fields,
            inductive,
            constructor,
            recursor,
        } = record;
        self.name(name)?;
        self.names(levels)?;
        self.expr(type_)?;
        self.boolean(value.is_some())?;
        if let Some(value) = value {
            self.expr(value)?;
        }
        self.boolean(*reducible)?;
        match reducibility {
            Reducibility::Reducible => self.byte(0)?,
            Reducibility::Regular(height) => {
                self.byte(1)?;
                self.u32(*height)?;
            }
            Reducibility::Irreducible => self.byte(2)?,
            Reducibility::Opaque => self.byte(3)?,
        }
        self.byte(match kind {
            ConstantKind::Definition => 0,
            ConstantKind::Theorem => 1,
            ConstantKind::Opaque => 2,
            ConstantKind::Axiom => 3,
        })?;
        self.byte(match verification {
            None => 0,
            Some(DeclarationVerification::FullKernelCheck) => 1,
            Some(DeclarationVerification::StructuralOnly) => 2,
            Some(DeclarationVerification::Unchecked) => 3,
        })?;
        self.boolean(*unsafe_)?;
        self.boolean(*partial)?;
        self.boolean(fields.is_some())?;
        if let Some(fields) = fields {
            self.names(fields)?;
        }
        self.boolean(inductive.is_some())?;
        if let Some((name, levels, type_, params, indices, members, ctors, flags)) = inductive {
            self.name(name)?;
            self.names(levels)?;
            self.expr(type_)?;
            self.u32(*params)?;
            self.u32(*indices)?;
            self.names(members)?;
            self.names(ctors)?;
            for flag in flags {
                self.boolean(*flag)?;
            }
        }
        self.boolean(constructor.is_some())?;
        if let Some((name, parent, levels, type_, params, fields, index)) = constructor {
            self.name(name)?;
            self.name(parent)?;
            self.names(levels)?;
            self.expr(type_)?;
            self.u32(*params)?;
            self.u32(*fields)?;
            self.u32(*index)?;
        }
        self.boolean(recursor.is_some())?;
        if let Some((
            name,
            order,
            levels,
            type_,
            parent,
            params,
            indices,
            motives,
            minors,
            rules,
            is_k,
        )) = recursor
        {
            self.name(name)?;
            self.byte(match order {
                RecursorArgOrder::MajorAfterMinors => 0,
                RecursorArgOrder::MajorAfterMotive => 1,
            })?;
            self.names(levels)?;
            self.expr(type_)?;
            self.name(parent)?;
            for count in [params, indices, motives, minors] {
                self.u32(*count)?;
            }
            self.count(rules.len())?;
            for (constructor, fields, recursive, rhs) in rules {
                self.name(constructor)?;
                self.u32(*fields)?;
                self.count(recursive.len())?;
                for flag in recursive {
                    self.boolean(*flag)?;
                }
                self.expr(rhs)?;
            }
            self.boolean(*is_k)?;
        }
        Ok(())
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use clean_auto::bridge::ay_contract::deserialize_term;

    use super::*;

    #[test]
    fn names_and_expression_codec_preserve_structural_identity() {
        for (a, b) in [
            (Name::from_string("Same.print"), Name::anon().str("Same.print")),
            (Name::anon().num(12), Name::anon().str("12")),
        ] {
            assert_eq!(a.to_string(), b.to_string());
            let mut first = Writer::new(b"").unwrap();
            let mut second = Writer::new(b"").unwrap();
            first.name(&a).unwrap();
            second.name(&b).unwrap();
            assert_ne!(first.bytes, second.bytes);
            let expr = Expr::const_(a, vec![]);
            let encoded = serialize_term(&expr).unwrap();
            assert_eq!(deserialize_term(&encoded).unwrap(), expr);
            assert_ne!(encoded, serialize_term(&Expr::const_(b, vec![])).unwrap());
        }
    }

    #[test]
    fn bounded_writer_refuses_oversize_counts_names_and_total_bytes() {
        let mut out = Writer::new(b"").unwrap();
        assert!(out.count(MAX_ENTRIES + 1).is_err());
        let name = (0..=MAX_ENTRIES).fold(Name::anon(), |n, _| n.str("x"));
        assert!(out.name(&name).is_err());
        out.bytes.resize(MAX_BYTES - 8, 0);
        assert!(out.field(&[1]).is_err());
        assert_eq!(out.bytes.len(), MAX_BYTES - 8);
        out.u64(0).unwrap();
        assert!(out.byte(0).is_err());
        assert_eq!(out.bytes.len(), MAX_BYTES);
    }
}
