// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Bounded, versioned transport of word64 source CLAIMS, never a live TCX
//! snapshot or proof. The metadata envelope must bind the producing owner/mode;
//! a consumer still owes source/model, IR, world, ABI and proof validation.

/// Source syntax data, not evidence. The enclosing snapshot authenticates where
/// its own operands were read; constructing this enum alone authenticates none.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    Parameter(u32),
    Literal(u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallKind {
    /// Original FnDef plus actual substitutions, not an admitted implementation.
    OrdinaryCall,
    /// Actual compiler registration, core ownership and instantiated U64 types.
    /// This is a source operation label, not its implementation/refinement proof.
    RegisteredWrappingAdd,
}

const MAGIC: &[u8; 8] = b"TRW64SRC";
pub const SCHEMA: u32 = 1;
pub const MAX_BYTES: usize = 4096;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Definition {
    pub stable_crate_id: u64,
    pub local_hash: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Body {
    Operand {
        node: u32,
        value: Operand,
    },
    Call {
        node: u32,
        definition: Definition,
        kind: CallKind,
        /// Exact initial generic vocabulary: no arguments or one U64 type.
        /// Other actual substitutions refuse export, never disappear.
        generic_u64: bool,
        operands: Vec<(u32, Operand)>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Record {
    pub owner: Definition,
    pub parameters: Vec<u32>,
    pub expressions: u32,
    pub source_hash: String,
    pub body: Body,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordError(pub &'static str);
impl std::fmt::Display for RecordError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}
impl std::error::Error for RecordError {}
type Result<T> = std::result::Result<T, RecordError>;

impl Record {
    pub fn validate(&self) -> Result<()> {
        if !(1..=2).contains(&self.parameters.len())
            || self.expressions == 0
            || self.expressions > 64
        {
            return Err(RecordError("source parameter/expression population"));
        }
        if self.parameters.len() == 2 && self.parameters[0] == self.parameters[1] {
            return Err(RecordError("duplicate original source parameter identity"));
        }
        if self.source_hash.is_empty() || self.source_hash.len() > 256 {
            return Err(RecordError("source hash representation budget"));
        }
        let operand = |node: u32, value: &Operand| -> Result<()> {
            if node >= self.expressions {
                return Err(RecordError("source node outside original population"));
            }
            if matches!(value, Operand::Parameter(index) if *index as usize >= self.parameters.len())
            {
                return Err(RecordError("source operand outside original parameter telescope"));
            }
            Ok(())
        };
        match &self.body {
            Body::Operand { node, value } => operand(*node, value),
            Body::Call { node, kind, generic_u64, operands, .. } => {
                if *node >= self.expressions
                    || operands.len() != 2
                    || operands[0].0 == operands[1].0
                    || operands.iter().any(|(id, _)| id == node)
                {
                    return Err(RecordError("original source call/node/operand population"));
                }
                if *kind == CallKind::RegisteredWrappingAdd && !generic_u64 {
                    return Err(RecordError("registered intrinsic requires its U64 substitution"));
                }
                for (node, value) in operands {
                    operand(*node, value)?;
                }
                Ok(())
            }
        }
    }
}

fn u32_out(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}
fn u64_out(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}
fn definition_out(out: &mut Vec<u8>, value: Definition) {
    u64_out(out, value.stable_crate_id);
    u64_out(out, value.local_hash);
}
fn operand_out(out: &mut Vec<u8>, value: &Operand) {
    match value {
        Operand::Parameter(index) => {
            out.push(0);
            u32_out(out, *index);
        }
        Operand::Literal(value) => {
            out.push(1);
            u64_out(out, *value);
        }
    }
}

pub fn encode(record: &Record) -> Result<Vec<u8>> {
    record.validate()?;
    let mut out = MAGIC.to_vec();
    u32_out(&mut out, SCHEMA);
    definition_out(&mut out, record.owner);
    out.push(record.parameters.len() as u8);
    for parameter in &record.parameters {
        u32_out(&mut out, *parameter);
    }
    u32_out(&mut out, record.expressions);
    u32_out(&mut out, record.source_hash.len() as u32);
    out.extend_from_slice(record.source_hash.as_bytes());
    match &record.body {
        Body::Operand { node, value } => {
            out.push(0);
            u32_out(&mut out, *node);
            operand_out(&mut out, value);
        }
        Body::Call { node, definition, kind, generic_u64, operands } => {
            out.push(match kind {
                CallKind::OrdinaryCall => 1,
                CallKind::RegisteredWrappingAdd => 2,
            });
            u32_out(&mut out, *node);
            definition_out(&mut out, *definition);
            out.push(u8::from(*generic_u64));
            for (node, value) in operands {
                u32_out(&mut out, *node);
                operand_out(&mut out, value);
            }
        }
    }
    if out.len() > MAX_BYTES {
        return Err(RecordError("source record byte budget"));
    }
    Ok(out)
}

/// Encode an unlicensed source section bound to the enclosing entry owner.
/// Absence preserves unsupported Rust compilation and supplies no source proof.
pub fn encode_section(record: Option<&Record>, owner: Definition) -> Result<Vec<u8>> {
    let Some(record) = record else {
        return Ok(vec![0]);
    };
    if record.owner != owner {
        return Err(RecordError("source/enclosing entry owner mismatch"));
    }
    let mut out = vec![1];
    out.extend_from_slice(&encode(record)?);
    Ok(out)
}

/// Decode data only. Even matching owner bytes require independent source TV.
pub fn decode_section(bytes: &[u8], owner: Definition) -> Result<Option<Record>> {
    match bytes.split_first() {
        Some((0, rest)) if rest.is_empty() => Ok(None),
        Some((1, rest)) => {
            let record = decode(rest)?;
            if record.owner != owner {
                return Err(RecordError("source/enclosing entry owner mismatch"));
            }
            Ok(Some(record))
        }
        _ => Err(RecordError("unknown, empty or noncanonical source section")),
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let end = self.at.checked_add(n).ok_or(RecordError("source length overflow"))?;
        let bytes = self.bytes.get(self.at..end).ok_or(RecordError("truncated source record"))?;
        self.at = end;
        Ok(bytes)
    }
    fn byte(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }
    fn u32(&mut self) -> Result<u32> {
        let mut bytes = [0; 4];
        bytes.copy_from_slice(self.take(4)?);
        Ok(u32::from_le_bytes(bytes))
    }
    fn u64(&mut self) -> Result<u64> {
        let mut bytes = [0; 8];
        bytes.copy_from_slice(self.take(8)?);
        Ok(u64::from_le_bytes(bytes))
    }
    fn definition(&mut self) -> Result<Definition> {
        Ok(Definition { stable_crate_id: self.u64()?, local_hash: self.u64()? })
    }
    fn operand(&mut self) -> Result<Operand> {
        match self.byte()? {
            0 => Ok(Operand::Parameter(self.u32()?)),
            1 => Ok(Operand::Literal(self.u64()?)),
            _ => Err(RecordError("unknown source operand opcode")),
        }
    }
}

pub fn decode(bytes: &[u8]) -> Result<Record> {
    if bytes.len() > MAX_BYTES {
        return Err(RecordError("source record byte budget"));
    }
    let mut r = Reader { bytes, at: 0 };
    if r.take(8)? != MAGIC {
        return Err(RecordError("source record magic"));
    }
    if r.u32()? != SCHEMA {
        return Err(RecordError("source record schema"));
    }
    let owner = r.definition()?;
    let count = r.byte()?;
    if !(1..=2).contains(&count) {
        return Err(RecordError("source parameter population"));
    }
    let mut parameters = Vec::new();
    for _ in 0..count {
        parameters.push(r.u32()?);
    }
    let expressions = r.u32()?;
    let length = r.u32()? as usize;
    if length > 256 {
        return Err(RecordError("source hash representation budget"));
    }
    let source_hash = std::str::from_utf8(r.take(length)?)
        .map_err(|_| RecordError("source hash UTF8"))?
        .to_owned();
    let tag = r.byte()?;
    let node = r.u32()?;
    let body = match tag {
        0 => Body::Operand { node, value: r.operand()? },
        1 | 2 => {
            let definition = r.definition()?;
            let kind =
                if tag == 1 { CallKind::OrdinaryCall } else { CallKind::RegisteredWrappingAdd };
            let generic_u64 = match r.byte()? {
                0 => false,
                1 => true,
                _ => return Err(RecordError("noncanonical source generic flag")),
            };
            let mut operands = Vec::new();
            for _ in 0..2 {
                operands.push((r.u32()?, r.operand()?));
            }
            Body::Call { node, definition, kind, generic_u64, operands }
        }
        _ => return Err(RecordError("unknown source body opcode")),
    };
    if r.at != bytes.len() {
        return Err(RecordError("trailing source record bytes"));
    }
    let record = Record { owner, parameters, expressions, source_hash, body };
    record.validate()?;
    Ok(record)
}

#[cfg(test)]
#[path = "record/tests.rs"]
mod tests;
