//! Exact subject identities recomputed from the live CER input.
//!
//! This is serializable comparison data, not source, FnAbi, object-layout or
//! proof authority. The caller MUST provide its fresh ObjectLayout-derived
//! certificate, never one reconstructed from wire fields. Replay compares this
//! recomputed binding with the untrusted retained binding before kernel work.

use std::io::{self, Write};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::call_event::{CERTIFICATE_SCHEMA, CerInput, FunctionCertificate};
use crate::compiled_object::RelocationModel;

const VERSION: u32 = 1;
const MAX_OBJECT_BYTES: usize = 256 * 1024 * 1024;
const MAX_SERIALIZED_BYTES: usize = 64 * 1024 * 1024;
const MAX_LABEL_BYTES: usize = 64 * 1024;
const MAX_PRODUCERS: usize = 4096;
const MAX_BODY_ROWS: usize = 1_000_000;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProducerBinding {
    // Redundant with slice position deliberately: ordering is normative.
    index: u64,
    module_sha256: String,
    symbols_sha256: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
enum BoundRelocationModel {
    Static,
    Pie,
    Pic,
}
impl From<RelocationModel> for BoundRelocationModel {
    fn from(value: RelocationModel) -> Self {
        match value {
            RelocationModel::Static => Self::Static,
            RelocationModel::Pie => Self::Pie,
            RelocationModel::Pic => Self::Pic,
        }
    }
}

/// Untrusted wire subject data. Construction here recomputes expected values;
/// deserialization never makes a subject or producer agreement authoritative.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct SubjectBinding {
    version: u32,
    object_sha256: String,
    object_bytes: u64,
    relocation_model: BoundRelocationModel,
    codegen_module_sha256: String,
    producers: Vec<ProducerBinding>,
    body_map_sha256: String,
    placements_sha256: String,
    certificate_schema: String,
    symbol: String,
    linkage: String,
    section: String,
    extent: (u64, u64),
    text_sha256: String,
    selected_producer_index: u64,
    selected_function_id: u32,
    selected_producer_module_sha256: String,
    selected_producer_function_sha256: String,
    selected_placement_sha256: String,
}

struct HashWriter<'a> {
    hash: Sha256,
    cumulative: &'a mut usize,
}
impl Write for HashWriter<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let next = (*self.cumulative)
            .checked_add(bytes.len())
            .filter(|n| *n <= MAX_SERIALIZED_BYTES)
            .ok_or_else(|| io::Error::other("original CIC subject serialization budget"))?;
        self.hash.update(bytes);
        *self.cumulative = next;
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn serialized_hash<T: Serialize + ?Sized>(
    value: &T,
    cumulative: &mut usize,
    field: &'static str,
) -> Result<String, String> {
    let mut writer = HashWriter { hash: Sha256::new(), cumulative };
    serde_json::to_writer(&mut writer, value)
        .map_err(|error| format!("original CIC subject {field}: {error}"))?;
    Ok(format!("{:x}", writer.hash.finalize()))
}

fn checked_label(value: &str, field: &'static str) -> Result<(), String> {
    if value.is_empty() || value.len() > MAX_LABEL_BYTES {
        Err(format!("original CIC subject {field} is absent or exceeds its byte bound"))
    } else {
        Ok(())
    }
}
fn checked_digest(value: &str, field: &'static str) -> Result<(), String> {
    if value.len() != 64 || !value.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        Err(format!("original CIC subject {field} is not a lowercase SHA256"))
    } else {
        Ok(())
    }
}

impl SubjectBinding {
    pub(crate) fn from_input(
        input: &CerInput<'_>,
        cert: &FunctionCertificate,
    ) -> Result<Self, String> {
        if input.object.is_empty() || input.object.len() > MAX_OBJECT_BYTES {
            return Err("original CIC subject object byte bound".into());
        }
        if input.producers.is_empty()
            || input.producers.len() > MAX_PRODUCERS
            || input.bodies.is_empty()
            || input.bodies.len() > MAX_BODY_ROWS
        {
            return Err("original CIC subject producer/body population bound".into());
        }
        if cert.schema != CERTIFICATE_SCHEMA {
            return Err("original CIC subject certificate schema mismatch".into());
        }
        checked_label(&cert.symbol, "symbol")?;
        checked_label(&cert.linkage, "linkage")?;
        checked_label(&cert.section, "section")?;
        checked_digest(&cert.text_sha256, "text digest")?;
        checked_digest(&cert.producer_ir_sha256, "producer function digest")?;
        let extent_bytes = cert
            .extent
            .1
            .checked_sub(cert.extent.0)
            .filter(|n| *n != 0)
            .ok_or("original CIC subject invalid fresh function extent")?;
        if extent_bytes > input.object.len() as u64 {
            return Err("original CIC subject fresh extent exceeds object size".into());
        }

        let body = input
            .bodies
            .get(&cert.symbol)
            .ok_or("original CIC subject selected source body is missing")?;
        let producer = input
            .producers
            .get(body.producer)
            .ok_or("original CIC subject selected producer index is missing")?;
        let function = producer
            .module
            .function_by_id(body.func)
            .ok_or("original CIC subject selected producer function is missing")?;
        if function.blocks.is_empty() {
            return Err("original CIC subject selected producer function has no body".into());
        }
        let source_symbol = producer
            .symbols
            .get(&body.func)
            .ok_or("original CIC subject selected producer has no exact symbol mapping")?;
        if source_symbol != &cert.symbol {
            return Err("original CIC subject selected producer symbol disagrees".into());
        }
        let placement = input
            .placements
            .get(&cert.symbol)
            .ok_or("original CIC subject selected source placement is missing")?;
        let selected_index = u64::try_from(body.producer)
            .map_err(|_| "original CIC subject producer index exceeds u64")?;

        let object_sha256 = format!("{:x}", Sha256::digest(input.object));
        let mut cumulative = 0usize;
        let codegen_module_sha256 = serialized_hash(input.m_cg, &mut cumulative, "M_cg")?;
        let mut producers = Vec::new();
        for (index, producer) in input.producers.iter().enumerate() {
            producers.push(ProducerBinding {
                index: u64::try_from(index)
                    .map_err(|_| "original CIC subject producer index exceeds u64")?,
                module_sha256: serialized_hash(
                    producer.module.as_ref(),
                    &mut cumulative,
                    "producer module",
                )?,
                symbols_sha256: serialized_hash(
                    &producer.symbols,
                    &mut cumulative,
                    "producer symbol map",
                )?,
            });
        }
        // ProducerBody intentionally has no serde contract. Render every row
        // explicitly in BTreeMap symbol order, retaining both numeric indices.
        // Borrow symbols rather than cloning a potentially large body map.
        let mut body_rows = Vec::with_capacity(input.bodies.len());
        for (symbol, body) in input.bodies {
            body_rows.push((
                symbol.as_str(),
                u64::try_from(body.producer)
                    .map_err(|_| "original CIC subject body producer index exceeds u64")?,
                body.func.index(),
            ));
        }
        let body_map_sha256 = serialized_hash(&body_rows, &mut cumulative, "body map")?;
        let placements_sha256 = serialized_hash(input.placements, &mut cumulative, "whole P map")?;
        let selected_placement_sha256 =
            serialized_hash(placement, &mut cumulative, "selected placement")?;
        let selected_producer_function_sha256 =
            serialized_hash(function, &mut cumulative, "selected function")?;
        if cert.producer_ir_sha256 != selected_producer_function_sha256 {
            return Err(
                "original CIC subject fresh certificate/source function hash mismatch".into()
            );
        }
        if cert.placement_sha256.get(&cert.symbol) != Some(&selected_placement_sha256) {
            return Err("original CIC subject fresh certificate/source P hash mismatch".into());
        }
        let selected_producer_module_sha256 = producers
            .get(body.producer)
            .ok_or("original CIC subject selected producer binding is missing")?
            .module_sha256
            .clone();

        Ok(Self {
            version: VERSION,
            object_sha256,
            object_bytes: u64::try_from(input.object.len())
                .map_err(|_| "original CIC subject object length exceeds u64")?,
            relocation_model: input.relocation_model.into(),
            codegen_module_sha256,
            producers,
            body_map_sha256,
            placements_sha256,
            certificate_schema: cert.schema.clone(),
            symbol: cert.symbol.clone(),
            linkage: cert.linkage.clone(),
            section: cert.section.clone(),
            extent: cert.extent,
            text_sha256: cert.text_sha256.clone(),
            selected_producer_index: selected_index,
            selected_function_id: body.func.index(),
            selected_producer_module_sha256,
            selected_producer_function_sha256,
            selected_placement_sha256,
        })
    }
}
