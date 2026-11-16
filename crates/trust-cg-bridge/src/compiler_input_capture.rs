//! Complete observational inputs of the real Compiler CER lane.
//!
//! These bytes are untrusted data, including every producer/BodyGate label.
//! Neither decoding, a self hash, nor successful mathematical replay establishes
//! Rust source refinement, FnAbi agreement, metadata or executable admission.
//! Replay requires independently supplied CURRENT inputs; the retained model is
//! never its own authentication reference. Universal Rust refinement is unfinished.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use trust_cg_codegen::CompilerConfig;
use trust_ir::Module;
use trust_ir::value::FuncId;

use crate::archive_object::{ArchiveObjectBinding, ArchiveObjectPadding, bind_archive_object};
use crate::call_event::{
    CerInput, FnPlacement, OriginalReplayReport, ProducerBody, ProducerModule,
};
use crate::compiled_object::RelocationModel;
use crate::f1_compile::{F1CompileConfig, F1OptLevel};
use crate::object_replay::{artifact_digest, encode};
use crate::verify_output::EmitPolicy;

const SCHEMA: &str = "trust.compiler-cer-input-data.v1";
const SCOPE: &str = "actual-compiler-IR-model-P-object-data; universal-Rust-source-refinement-unfinished; no-admission-authority";
pub const MAX_FUNCTIONS: usize = 32;
pub const MAX_WIRE_BYTES: usize = 64 * 1024 * 1024;
const MAX_PART_BYTES: usize = 8 * 1024 * 1024;
const MAX_LABEL_BYTES: usize = 64 * 1024;

#[cfg(feature = "canonical-semr-scalar")]
mod semr_scalar;
#[cfg(feature = "canonical-semr-scalar")]
pub use semr_scalar::{
    CanonicalScalarEnvironment, CanonicalScalarProgramEnvironment, CheckedOriginalScalar,
    CheckedOriginalScalarProgram, ExpectedScalarInput, OriginalScalarPacket,
    OriginalScalarProgramPacket,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
enum Relocation {
    Static,
    Pie,
    Pic,
}
impl From<RelocationModel> for Relocation {
    fn from(value: RelocationModel) -> Self {
        match value {
            RelocationModel::Static => Self::Static,
            RelocationModel::Pie => Self::Pie,
            RelocationModel::Pic => Self::Pic,
        }
    }
}
impl From<Relocation> for RelocationModel {
    fn from(value: Relocation) -> Self {
        match value {
            Relocation::Static => Self::Static,
            Relocation::Pie => Self::Pie,
            Relocation::Pic => Self::Pic,
        }
    }
}

/// Comparison data only, not a backend or ABI capability. The effective
/// settings are recorded from the SAME CompilerConfig passed to Compiler.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompilerCaptureConfig {
    profile: String,
    target: String,
    opt_level: u8,
    requested_relocation: Relocation,
    compiled_relocation: Relocation,
    never_inline: BTreeSet<String>,
    upstream_mir_lane: bool,
    output_policy: String,
    effective_backend_settings: String,
    abi_scope: String,
}
impl CompilerCaptureConfig {
    pub(crate) fn from_effective(
        config: &F1CompileConfig,
        policy: EmitPolicy,
        effective: &CompilerConfig,
    ) -> Result<Self, CaptureIncomplete> {
        if config.never_inline.len() > MAX_FUNCTIONS * 2
            || !config.never_inline.iter().all(|name| label(name))
        {
            return Err(CaptureIncomplete::new("Compiler configuration label/population budget"));
        }
        let captured = Self {
            profile: "trust.f1-serial-no-proofs-no-debug-panic-abort-no-cache.v1".into(),
            target: config.target.triple().into(),
            opt_level: match config.opt_level {
                F1OptLevel::O0 => 0,
                F1OptLevel::O1 => 1,
                F1OptLevel::O2 => 2,
                F1OptLevel::O3 => 3,
            },
            requested_relocation: config.relocation.into(),
            compiled_relocation: config.compiled_relocation().into(),
            never_inline: config.never_inline.clone(),
            upstream_mir_lane: config.upstream_mir_lane,
            output_policy: format!("{policy:?}"),
            effective_backend_settings: format!("{effective:?}"),
            abi_scope: "exact-P-plus-complete-module-types-and-calling-conventions; no-deserialized-FnAbi-token".into(),
        };
        if !bounded_configuration(&captured) {
            return Err(CaptureIncomplete::new("Compiler effective configuration budget"));
        }
        Ok(captured)
    }

    /// Independently supplied expected configuration. This pure operation
    /// constructs no Compiler, solver, proof, source agreement or admission.
    pub fn expected(
        config: &F1CompileConfig,
        policy: EmitPolicy,
    ) -> Result<Self, CaptureIncomplete> {
        Self::from_effective(config, policy, &config.compiler_config())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ModuleBytes {
    bytes: Vec<u8>,
    sha256: String,
}
impl ModuleBytes {
    fn capture(module: &Module) -> Result<Self, String> {
        let bytes = encode(module, MAX_PART_BYTES)?;
        // Use the existing complete serde Module transport. Verify that its
        // decoded data equals the live input as well as round-tripping its
        // wire. Re-encoding alone would miss a future skipped/default field.
        let decoded: Module = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
        if &decoded != module || encode(&decoded, MAX_PART_BYTES)? != bytes {
            return Err("complete Module codec roundtrip differs".into());
        }
        Ok(Self { sha256: artifact_digest(&bytes), bytes })
    }
    fn decode(&self) -> Result<Module, String> {
        if self.bytes.is_empty()
            || self.bytes.len() > MAX_PART_BYTES
            || artifact_digest(&self.bytes) != self.sha256
        {
            return Err("compiler capture module size/digest mismatch".into());
        }
        let module: Module = serde_json::from_slice(&self.bytes).map_err(|e| e.to_string())?;
        if encode(&module, MAX_PART_BYTES)? != self.bytes {
            return Err("compiler capture Module transport is noncanonical".into());
        }
        Ok(module)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Producer {
    module: ModuleBytes,
    symbols: Vec<(u32, String)>,
}
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Body {
    symbol: String,
    producer: u64,
    function: u32,
}

/// A complete snapshot of actual CER inputs. Private wire fields and fixed
/// scope prevent treating its construction as a checked producer capability.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompilerInputCapture {
    schema: String,
    scope: String,
    configuration: CompilerCaptureConfig,
    m_cg: ModuleBytes,
    producers: Vec<Producer>,
    bodies: Vec<Body>,
    placements: BTreeMap<String, FnPlacement>,
    expected_functions: Vec<String>,
    relocation: Relocation,
    object: Vec<u8>,
    object_sha256: String,
}

/// Original function-proof replay on the exact object bytes selected from one
/// stored archive member. This grants no whole-archive, linker, loaded-image,
/// source-refinement or executable-admission authority. Auxiliary sections
/// retain the separate status in `object_proofs.unverified_sections`.
#[derive(Debug, Serialize)]
pub struct ArchivedOriginalReplay {
    pub member: ArchiveObjectBinding,
    pub object_proofs: OriginalReplayReport,
}

/// Structured optional capture refusal. No empty or partial snapshot claims
/// to be complete; refusal never changes the compilation or proof verdict.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CaptureIncomplete {
    schema: String,
    status: String,
    pub reason: String,
    pub object_sha256: Option<String>,
    pub object_bytes: Option<usize>,
    pub defined_functions: Option<usize>,
}
impl CaptureIncomplete {
    pub fn new(reason: impl Into<String>) -> Self {
        let mut reason = reason.into();
        if reason.len() > MAX_LABEL_BYTES {
            let mut end = MAX_LABEL_BYTES;
            while !reason.is_char_boundary(end) {
                end -= 1;
            }
            reason.truncate(end);
        }
        Self {
            schema: SCHEMA.into(),
            status: "capture-incomplete-non-authorizing".into(),
            reason,
            object_sha256: None,
            object_bytes: None,
            defined_functions: None,
        }
    }
    pub(crate) fn at_input(mut self, input: &CerInput<'_>) -> Self {
        self.object_sha256 = Some(artifact_digest(input.object));
        self.object_bytes = Some(input.object.len());
        self.defined_functions =
            Some(input.m_cg.functions.iter().filter(|f| !f.blocks.is_empty()).count());
        self
    }
    pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
        if self.schema != SCHEMA
            || self.status != "capture-incomplete-non-authorizing"
            || self.reason.len() > MAX_LABEL_BYTES
        {
            return Err("invalid optional Compiler capture refusal".into());
        }
        encode(self, MAX_PART_BYTES)
    }
}

fn label(value: &str) -> bool {
    !value.is_empty() && value.len() <= MAX_LABEL_BYTES
}

fn bounded_configuration(config: &CompilerCaptureConfig) -> bool {
    [&config.profile, &config.target, &config.output_policy, &config.abi_scope]
        .iter()
        .all(|s| label(s))
        && !config.effective_backend_settings.is_empty()
        && config.effective_backend_settings.len() <= MAX_PART_BYTES
        && config.never_inline.len() <= MAX_FUNCTIONS * 2
        && config.never_inline.iter().all(|s| label(s))
}

fn functions(module: &Module) -> Result<Vec<String>, String> {
    let names: Vec<_> =
        module.functions.iter().filter(|f| !f.blocks.is_empty()).map(|f| f.name.clone()).collect();
    if names.is_empty()
        || names.len() > MAX_FUNCTIONS
        || names.iter().any(|n| n.is_empty() || n.len() > MAX_LABEL_BYTES)
        || names.iter().collect::<BTreeSet<_>>().len() != names.len()
    {
        return Err("compiler capture empty/oversized/duplicate function population".into());
    }
    Ok(names)
}

impl CompilerInputCapture {
    /// Observe the actual live inputs, without compiling or proving anything.
    pub fn capture(
        input: &CerInput<'_>,
        configuration: CompilerCaptureConfig,
    ) -> Result<Self, CaptureIncomplete> {
        Self::capture_inner(input, configuration)
            .map_err(|e| CaptureIncomplete::new(e).at_input(input))
    }
    fn capture_inner(
        input: &CerInput<'_>,
        configuration: CompilerCaptureConfig,
    ) -> Result<Self, String> {
        if !bounded_configuration(&configuration)
            || configuration.compiled_relocation != Relocation::from(input.relocation_model)
            || input.object.is_empty()
            || input.object.len() > MAX_PART_BYTES
            || input.producers.is_empty()
            || input.producers.len() > MAX_FUNCTIONS
            || input.bodies.len() > MAX_FUNCTIONS
            || input.placements.len() > MAX_FUNCTIONS * 2
            || !input.bodies.keys().all(|s| label(s))
            || !input.placements.keys().all(|s| label(s))
        {
            return Err("compiler capture input population/part budget".into());
        }
        let expected_functions = functions(input.m_cg)?;
        let mut producers = Vec::with_capacity(input.producers.len());
        for producer in input.producers {
            if producer.symbols.len() > MAX_FUNCTIONS * 2
                || !producer.symbols.values().all(|s| label(s))
            {
                return Err("compiler capture producer symbol population budget".into());
            }
            producers.push(Producer {
                module: ModuleBytes::capture(&producer.module)?,
                symbols: producer
                    .symbols
                    .iter()
                    .map(|(id, symbol)| (id.index(), symbol.clone()))
                    .collect(),
            });
        }
        let capture = Self {
            schema: SCHEMA.into(),
            scope: SCOPE.into(),
            configuration,
            m_cg: ModuleBytes::capture(input.m_cg)?,
            producers,
            bodies: input
                .bodies
                .iter()
                .map(|(symbol, body)| Body {
                    symbol: symbol.clone(),
                    producer: body.producer as u64,
                    function: body.func.index(),
                })
                .collect(),
            placements: input.placements.clone(),
            expected_functions,
            relocation: input.relocation_model.into(),
            object: input.object.to_vec(),
            object_sha256: artifact_digest(input.object),
        };
        capture.to_bytes()?;
        capture.decode_inputs()?;
        Ok(capture)
    }
    pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
        encode(self, MAX_WIRE_BYTES)
    }
    /// Bounded decoding grants no grades, source/FnAbi/metadata capabilities,
    /// or executable admission. All decoded modules remain untrusted data.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.is_empty() || bytes.len() > MAX_WIRE_BYTES {
            return Err("compiler capture wire budget".into());
        }
        let capture: Self = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
        if capture.to_bytes()? != bytes {
            return Err("compiler capture outer wire is noncanonical".into());
        }
        capture.decode_inputs()?;
        Ok(capture)
    }
    /// Materialize untrusted input DATA for inspection or comparison. A caller
    /// MUST NOT use this as the independent expected reference in replay.
    pub fn decode_inputs(&self) -> Result<DecodedCompilerInputs, String> {
        if self.schema != SCHEMA
            || self.scope != SCOPE
            || !bounded_configuration(&self.configuration)
            || self.configuration.compiled_relocation != self.relocation
            || self.object.is_empty()
            || self.object.len() > MAX_PART_BYTES
            || artifact_digest(&self.object) != self.object_sha256
            || self.producers.is_empty()
            || self.producers.len() > MAX_FUNCTIONS
            || self.bodies.len() > MAX_FUNCTIONS
            || self.placements.len() > MAX_FUNCTIONS * 2
            || !self.bodies.iter().all(|b| label(&b.symbol))
            || !self.placements.keys().all(|s| label(s))
        {
            return Err("compiler capture schema/scope/object/population mismatch".into());
        }
        self.to_bytes()?;
        let m_cg = self.m_cg.decode()?;
        if functions(&m_cg)? != self.expected_functions {
            return Err("compiler capture function population mismatch".into());
        }
        let mut producers = Vec::new();
        for row in &self.producers {
            if row.symbols.len() > MAX_FUNCTIONS * 2 || !row.symbols.iter().all(|(_, s)| label(s)) {
                return Err("compiler capture symbol budget".into());
            }
            let symbols: BTreeMap<_, _> =
                row.symbols.iter().map(|(id, s)| (FuncId::new(*id), s.clone())).collect();
            if symbols.len() != row.symbols.len() {
                return Err("compiler capture duplicate producer symbol id".into());
            }
            producers.push(ProducerModule { module: Arc::new(row.module.decode()?), symbols });
        }
        let mut bodies = BTreeMap::new();
        for row in &self.bodies {
            let producer =
                usize::try_from(row.producer).map_err(|_| "compiler capture producer index")?;
            if producer >= producers.len()
                || bodies
                    .insert(
                        row.symbol.clone(),
                        ProducerBody { producer, func: FuncId::new(row.function) },
                    )
                    .is_some()
            {
                return Err("compiler capture invalid/duplicate producer body mapping".into());
            }
        }
        Ok(DecodedCompilerInputs {
            m_cg,
            producers,
            bodies,
            placements: self.placements.clone(),
            object: self.object.clone(),
            relocation: self.relocation.into(),
        })
    }
    /// Compare ALL input data against the independently selected current
    /// source/model/P/object/config BEFORE replaying the retained original CIC.
    /// No Compiler, solver or proof producer is invoked on this path.
    pub fn replay_original(
        &self,
        expected: &CerInput<'_>,
        configuration: &CompilerCaptureConfig,
        sidecar: &[u8],
    ) -> Result<OriginalReplayReport, String> {
        let current = Self::capture(expected, configuration.clone()).map_err(|e| e.reason)?;
        if self != &current {
            return Err("compiler capture independent current subject/config mismatch".into());
        }
        crate::call_event::replay_original_certificates(expected, sidecar)
    }

    /// Bind an actual stored member to independently selected current object
    /// bytes, then replay on the ARCHIVE's exact matching object prefix. Only
    /// the target's specified archive envelope padding is excluded. No subject
    /// hash or original proposition is rewritten, and no proof is produced.
    pub fn replay_original_in_archive(
        &self,
        expected: &CerInput<'_>,
        configuration: &CompilerCaptureConfig,
        sidecar: &[u8],
        archive: &[u8],
        member_name: &str,
        padding: ArchiveObjectPadding,
    ) -> Result<ArchivedOriginalReplay, String> {
        let bound = bind_archive_object(archive, member_name, expected.object, padding)?;
        let current = CerInput {
            m_cg: expected.m_cg,
            producers: expected.producers,
            bodies: expected.bodies,
            placements: expected.placements,
            relocation_model: expected.relocation_model,
            object: bound.object(),
        };
        let object_proofs = self.replay_original(&current, configuration, sidecar)?;
        Ok(ArchivedOriginalReplay { member: bound.binding().clone(), object_proofs })
    }
}

/// Reconstructed untrusted data only. It contains no checked object layout,
/// BodyGate capability, checked metadata or source/ABI agreement token.
#[derive(Debug)]
pub struct DecodedCompilerInputs {
    pub m_cg: Module,
    pub producers: Vec<ProducerModule>,
    pub bodies: BTreeMap<String, ProducerBody>,
    pub placements: BTreeMap<String, FnPlacement>,
    pub object: Vec<u8>,
    pub relocation: RelocationModel,
}
impl DecodedCompilerInputs {
    pub fn input(&self) -> CerInput<'_> {
        CerInput {
            m_cg: &self.m_cg,
            producers: &self.producers,
            bodies: &self.bodies,
            placements: &self.placements,
            object: &self.object,
            relocation_model: self.relocation,
        }
    }
}

#[cfg(test)]
mod tests;
