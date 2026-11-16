//! Retained object-gate diagnostics, not source refinement or executable admission.
//!
//! Replay receives the current exact source/module, backend configuration and
//! object independently of the untrusted artifact. It reconstructs the gate's
//! formulas from those inputs, rebuilds the canonical Boolean graph with the
//! pinned encoder, compares that graph, and checks the RETAINED refutation.
//! Graph rebuilding currently repeats bounded SAT work and shares the encoder
//! TCB; this is not an independently implemented bit-blaster. A theorem label,
//! a solver verdict, or an internally valid but unbound proof is insufficient.

use std::collections::BTreeSet;
use std::io::{self, Write};
use std::time::Duration;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_types::Formula;

use crate::codegen_backend::{
    EmittedModuleObject, FunctionLinkage, TrustCgCodegenBackend, TrustCgTargetArch,
};
use crate::verify_output::{
    MAX_RECHECKABLE_REFUTATION_STEPS, OutputVerdict, PreservedFunction, ProvenEvidence,
    RawTextSymbol, TextSymbolFormat, assert_merged_object_preserves_verified_text,
    extract_text_from_object, formula_to_bvexpr, object_text_symbols,
    require_exact_elf_function_bindings, split_register_pair_128,
};
use crate::verify_output_trust_ir::{GateObligation, TrustIrGateSource, trust_ir_gate_obligation};

const SCHEMA: u32 = 3;
const LEGACY_SCOPE: &str = "diagnostic-return-value-and-text-preservation; no source refinement, full effects, linker or G7 admission; shared encoder with bounded renewed SAT";
const SCOPE: &str = "diagnostic-return-value-and-text-preservation; no source refinement, full effects, linker or G7 admission; shared encoder with bounded renewed SAT or exact compact BVC instantiation under rebuilt typed environment; source/machine model correspondence remains TCB";
const MAX_FUNCTIONS: usize = 32;
const MAX_WIRE_BYTES: usize = 32 * 1024 * 1024;
const MAX_PART_BYTES: usize = 8 * 1024 * 1024;
const MAX_SYMBOL_NAME_BYTES: usize = 64 * 1024;

mod compact_instantiation;
mod scalar_certificate;

/// Complete effective backend settings for this diagnostic scope. The exact
/// module bytes separately retain every function calling convention and type.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BackendDescriptor {
    pub architecture: String,
    pub target_triple: String,
    pub optimization_level: u8,
    pub frame_pointer_policy: String,
    pub panic_symbols: Vec<(String, Option<String>)>,
    pub entry_bindings_absent: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields)]
enum RetainedEvidence {
    BitBlast { proof: Box<ay_proof::BvBlastProof> },
    BitBlastPair { high: Box<ay_proof::BvBlastProof>, low: Box<ay_proof::BvBlastProof> },
    CompactInstantiation { certificate: Box<compact_instantiation::CompactCertificate> },
    NonReplayable { original_kind: String, detail: String },
}

/// Diagnostic context only: never deserialized into a live cross-check token.
/// Legacy rows did not capture this input and can only replay with live `None`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields)]
enum RetainedAbiContext {
    #[default]
    LegacyAbsent,
    NoCrossCheck,
    CrossChecked {
        authority: String,
    },
}

fn abi_context(source: &TrustIrGateSource) -> Result<RetainedAbiContext, String> {
    let authority = source.abi_cross_check.as_ref().map(|check| check.authority());
    // Bound the captured text before allocating its retained copy.
    encode(&authority, MAX_PART_BYTES)?;
    Ok(match authority {
        None => RetainedAbiContext::NoCrossCheck,
        Some(authority) => RetainedAbiContext::CrossChecked { authority: authority.into() },
    })
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct FunctionRow {
    symbol: String,
    func_id: u32,
    module_bytes: Vec<u8>,
    module_sha256: String,
    #[serde(default)]
    abi_context: RetainedAbiContext,
    object_bytes: Vec<u8>,
    object_sha256: String,
    symbols: Vec<RawTextSymbol>,
    obligation: Result<GateObligation, String>,
    evidence: RetainedEvidence,
}

/// Non-authorizing serialized observation of a completed object gate. Fields
/// are private so callers cannot mistake construction for an admission token.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ObjectReplayArtifact {
    schema: u32,
    scope: String,
    backend: BackendDescriptor,
    linkage: Vec<String>,
    statics: Vec<u8>,
    object_bytes: Vec<u8>,
    object_sha256: String,
    symbols: Vec<RawTextSymbol>,
    functions: Vec<FunctionRow>,
    preserved: Vec<PreservedFunction>,
}

/// Per-row outcomes retain non-replayable siblings. `replayed` denotes this
/// diagnostic's bounded value/merge claim, never G4/G7 or full effects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectReplayReport {
    pub rows: Vec<(String, Result<(), String>)>,
}

pub(crate) struct Observation {
    row: FunctionRow,
}

struct LimitedWriter {
    bytes: Vec<u8>,
    limit: usize,
    depth: usize,
    quoted: bool,
    escaped: bool,
}

impl Write for LimitedWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let length = self
            .bytes
            .len()
            .checked_add(bytes.len())
            .filter(|length| *length <= self.limit)
            .ok_or_else(|| io::Error::other("object replay serialization capacity exceeded"))?;
        for byte in bytes {
            if self.quoted {
                if self.escaped {
                    self.escaped = false;
                } else if *byte == b'\\' {
                    self.escaped = true;
                } else if *byte == b'"' {
                    self.quoted = false;
                }
            } else {
                match byte {
                    b'"' => self.quoted = true,
                    b'[' | b'{' => {
                        self.depth += 1;
                        if self.depth > 96 {
                            return Err(io::Error::other(
                                "object replay serialization depth exceeded",
                            ));
                        }
                    }
                    b']' | b'}' => self.depth = self.depth.saturating_sub(1),
                    _ => {}
                }
            }
        }
        self.bytes.try_reserve_exact(length - self.bytes.len()).map_err(io::Error::other)?;
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

pub(crate) fn encode<T: Serialize>(value: &T, limit: usize) -> Result<Vec<u8>, String> {
    let mut output =
        LimitedWriter { bytes: Vec::new(), limit, depth: 0, quoted: false, escaped: false };
    serde_json::to_writer(&mut output, value).map_err(|error| error.to_string())?;
    Ok(output.bytes)
}

fn hash(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// Content-addressed diagnostic filename component, not an authority token.
pub fn artifact_digest(bytes: &[u8]) -> String {
    hash(bytes)
}

/// Preserve an explicit capture refusal instead of fabricating an empty proof.
pub fn capture_refusal_bytes(
    reason: &str,
    codegen_unit: &str,
    object: &[u8],
    source_count: usize,
) -> Result<Vec<u8>, String> {
    #[derive(Serialize)]
    struct Refusal<'a> {
        schema: u32,
        status: &'static str,
        reason: &'a str,
        codegen_unit: &'a str,
        object_sha256: String,
        object_bytes: usize,
        source_count: usize,
        source_population_bound: bool,
    }
    encode(
        &Refusal {
            schema: SCHEMA,
            status: "non-replayable-capture-refused",
            reason,
            codegen_unit,
            object_sha256: hash(object),
            object_bytes: object.len(),
            source_count,
            source_population_bound: false,
        },
        MAX_PART_BYTES,
    )
}

fn bounded_part(bytes: &[u8]) -> Result<(), String> {
    if bytes.is_empty() || bytes.len() > MAX_PART_BYTES {
        return Err("empty/oversized object replay part".into());
    }
    Ok(())
}

fn retained_evidence(verdict: &OutputVerdict) -> RetainedEvidence {
    let unsupported = |original_kind: &str, detail: String| RetainedEvidence::NonReplayable {
        original_kind: original_kind.into(),
        detail,
    };
    match verdict {
        OutputVerdict::Proven { evidence: ProvenEvidence::KernelRecheckable(proof) } => {
            RetainedEvidence::BitBlast { proof: Box::new(proof.clone()) }
        }
        OutputVerdict::Proven { evidence: ProvenEvidence::KernelRecheckablePair { high, low } } => {
            RetainedEvidence::BitBlastPair { high: high.clone(), low: low.clone() }
        }
        OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { theorem, .. } } => {
            unsupported("kernel-instantiated-label-only", theorem.clone())
        }
        // The replay row refuses every obligation with modeling conditions
        // (`replay_evidence`), so this proof is kept as a row, not replayed.
        OutputVerdict::Proven {
            evidence: ProvenEvidence::KernelRecheckableWithSideConditions { side_conditions, .. },
        } => unsupported(
            "kernel-side-conditioned",
            format!("{} kernel-proved modeling condition(s)", side_conditions.len()),
        ),
        OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated } => {
            unsupported("solver-only", "no retained kernel proof".into())
        }
        OutputVerdict::Proven {
            evidence: ProvenEvidence::StructuralCitation { theorem, residual, .. },
        } => unsupported("structural-citation", format!("{theorem}: {residual}")),
        OutputVerdict::Refuted { detail } => unsupported("refuted", detail.clone()),
        OutputVerdict::Unknown { reason } => unsupported("unknown", reason.clone()),
    }
}

// Shared selection for a kernel-instantiated verdict. The caller supplies the
// existing bounded export policy; a failed export never grants proof authority.
fn capture_kernel_instantiation(
    source: &TrustIrGateSource,
    object: &[u8],
    arch: TrustCgTargetArch,
    budget: &ay_proof::BvExprProofBudget,
) -> RetainedEvidence {
    match scalar_certificate::capture_scalar_certificate(source, object, arch, budget) {
        Ok(proof) => RetainedEvidence::BitBlast { proof: Box::new(proof) },
        Err(reason) => match compact_instantiation::capture(source, object, arch) {
            Ok(certificate) => {
                RetainedEvidence::CompactInstantiation { certificate: Box::new(certificate) }
            }
            Err(compact_reason) => RetainedEvidence::NonReplayable {
                original_kind: "kernel-instantiated-label-only".into(),
                detail: format!("{reason}; {compact_reason}"),
            },
        },
    }
}

pub(crate) fn observe(
    source: &TrustIrGateSource,
    object: &[u8],
    verdict: &OutputVerdict,
    arch: TrustCgTargetArch,
) -> Result<Observation, String> {
    bounded_part(object)?;
    let module_bytes = encode(&source.module, MAX_PART_BYTES)?;
    let abi_context = abi_context(source)?;
    // Bound payload size BEFORE cloning potentially large retained proofs.
    match verdict {
        OutputVerdict::Proven { evidence: ProvenEvidence::KernelRecheckable(proof) } => {
            encode(proof, MAX_PART_BYTES)?;
        }
        OutputVerdict::Proven { evidence: ProvenEvidence::KernelRecheckablePair { high, low } } => {
            encode(high, MAX_PART_BYTES)?;
            encode(low, MAX_PART_BYTES)?;
        }
        _ => {}
    }
    // Some existing kernel-checked fast paths retain only a theorem label.
    // Recover an actual proof only for the closed unconditional scalar lane;
    // the old verdict/grade is never changed, and every refusal remains a row.
    let evidence = if matches!(
        verdict,
        OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
    ) {
        let budget = ay_proof::BvExprProofBudget::conservative(
            Duration::from_secs(10),
            MAX_RECHECKABLE_REFUTATION_STEPS,
        )
        .map_err(|error| error.to_string())?;
        capture_kernel_instantiation(source, object, arch, &budget)
    } else {
        retained_evidence(verdict)
    };
    Ok(Observation {
        row: FunctionRow {
            symbol: source.symbol.clone(),
            func_id: source.func_id.index(),
            module_sha256: hash(&module_bytes),
            module_bytes,
            abi_context,
            object_sha256: hash(object),
            symbols: raw_symbols(object)?,
            object_bytes: object.to_vec(),
            obligation: trust_ir_gate_obligation(source, object, arch),
            evidence,
        },
    })
}

pub(crate) fn finish(
    backend: &TrustCgCodegenBackend,
    linkage: &[FunctionLinkage],
    statics: &[trust_cg_codegen::pipeline::ObjectGlobal],
    object: &[u8],
    preserved: &[PreservedFunction],
    observations: Vec<Observation>,
) -> Result<ObjectReplayArtifact, String> {
    bounded_part(object)?;
    if observations.is_empty() || observations.len() > MAX_FUNCTIONS {
        return Err("empty/oversized function population for object replay".into());
    }
    if !linkage.is_empty() && linkage.len() != observations.len() {
        return Err("object replay linkage population mismatch".into());
    }
    let expected = observations
        .iter()
        .enumerate()
        .map(|(index, row)| {
            (row.row.symbol.as_str(), linkage.get(index).copied().unwrap_or_default())
        })
        .collect::<Vec<_>>();
    require_exact_elf_function_bindings(object, &expected)?;
    let artifact = ObjectReplayArtifact {
        schema: SCHEMA,
        scope: SCOPE.into(),
        backend: backend.object_replay_descriptor()?,
        linkage: linkage_identity(linkage),
        statics: statics_identity(statics)?,
        object_bytes: object.to_vec(),
        object_sha256: hash(object),
        symbols: raw_symbols(object)?,
        functions: observations.into_iter().map(|observation| observation.row).collect(),
        preserved: preserved.to_vec(),
    };
    artifact.to_bytes()?;
    Ok(artifact)
}

impl ObjectReplayArtifact {
    fn known_schema(&self) -> bool {
        let legacy_context = self
            .functions
            .iter()
            .all(|row| matches!(row.abi_context, RetainedAbiContext::LegacyAbsent));
        match self.schema {
            SCHEMA => {
                self.scope == SCOPE
                    && self
                        .functions
                        .iter()
                        .all(|row| !matches!(row.abi_context, RetainedAbiContext::LegacyAbsent))
            }
            2 => self.scope == SCOPE && legacy_context,
            1 => {
                self.scope == LEGACY_SCOPE
                    && legacy_context
                    && self.functions.iter().all(|row| {
                        !matches!(row.evidence, RetainedEvidence::CompactInstantiation { .. })
                    })
            }
            _ => false,
        }
    }
    /// Bounded wire encoding. Serialization failure is never a partial success.
    pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
        encode(self, MAX_WIRE_BYTES)
    }

    /// Decode bounded, depth-limited JSON. Decoding grants no trust or grade.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.is_empty() || bytes.len() > MAX_WIRE_BYTES {
            return Err("object replay wire size".into());
        }
        let artifact: Self = serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
        if !artifact.known_schema() {
            return Err("unknown object replay schema/scope".into());
        }
        for row in &artifact.functions {
            if let RetainedEvidence::CompactInstantiation { certificate } = &row.evidence {
                certificate.validate_graph()?;
            }
        }
        Ok(artifact)
    }

    /// Reconstruct from independently supplied CURRENT inputs. No source or
    /// target identity is taken from the artifact itself. Every row is checked;
    /// a non-replayable sibling remains a row, never a successful subset.
    pub fn replay(
        &self,
        sources: &[TrustIrGateSource],
        object: &[u8],
        backend: &TrustCgCodegenBackend,
        linkage: &[FunctionLinkage],
        statics: &[trust_cg_codegen::pipeline::ObjectGlobal],
    ) -> Result<ObjectReplayReport, String> {
        self.to_bytes()?;
        bounded_part(object)?;
        if !self.known_schema()
            || self.backend != backend.object_replay_descriptor()?
            || self.linkage != linkage_identity(linkage)
            || self.statics != statics_identity(statics)?
            || self.object_bytes != object
            || self.object_sha256 != hash(object)
            || sources.is_empty()
            || sources.len() > MAX_FUNCTIONS
            || self.functions.len() != sources.len()
            || self.preserved.len() != sources.len()
            || (!linkage.is_empty() && linkage.len() != sources.len())
        {
            return Err("object replay subject/config/population mismatch".into());
        }
        backend.require_object_target(object)?;
        let expected = sources
            .iter()
            .enumerate()
            .map(|(index, source)| {
                (source.symbol.as_str(), linkage.get(index).copied().unwrap_or_default())
            })
            .collect::<Vec<_>>();
        require_exact_elf_function_bindings(object, &expected)?;
        require_exact_symbols(
            object,
            &self.symbols,
            sources.iter().map(|source| source.symbol.as_str()),
        )?;
        let mut names = BTreeSet::new();
        let mut verified = Vec::with_capacity(sources.len());
        for (source, row) in sources.iter().zip(&self.functions) {
            if !names.insert(source.symbol.clone()) {
                return Err("duplicate object replay symbol".into());
            }
            let bytes = encode(&source.module, MAX_PART_BYTES)?;
            // The existing gate performs its modeled-fragment checks below.
            // Additionally refuse ambiguous lookup/SSA identities rather than
            // allowing a HashMap insertion or first-match lookup to choose one.
            require_unique_source_ids(&source.module)?;
            let function =
                source.module.function_by_id(source.func_id).ok_or("missing replay function")?;
            bounded_part(&row.object_bytes)?;
            backend.require_object_target(&row.object_bytes).map_err(|reason| {
                format!("object replay function `{}` target mismatch: {reason}", source.symbol)
            })?;
            require_exact_elf_function_bindings(
                &row.object_bytes,
                &[(source.symbol.as_str(), FunctionLinkage::External)],
            )?;
            require_exact_symbols(&row.object_bytes, &row.symbols, [source.symbol.as_str()])?;
            if function.name != source.symbol
                || row.symbol != source.symbol
                || row.func_id != source.func_id.index()
                || row.module_bytes != bytes
                || row.module_sha256 != hash(&bytes)
                || row.object_sha256 != hash(&row.object_bytes)
            {
                return Err("object replay exact function/source mismatch".into());
            }
            let current_abi = abi_context(source)?;
            if row.abi_context != current_abi
                && !(matches!(row.abi_context, RetainedAbiContext::LegacyAbsent)
                    && matches!(current_abi, RetainedAbiContext::NoCrossCheck))
            {
                return Err("object replay ABI cross-check context mismatch".into());
            }
            // Re-earn converter admission from the CURRENT caller's context.
            // Artifact-authored provenance text must never mint `attested_by`.
            let lir = crate::lower_module_to_lir_maybe_cross_checked(
                &source.module,
                source.func_id,
                source.abi_cross_check.as_ref(),
            )
            .map_err(|error| format!("object replay current lowering refused: {error}"))?;
            if lir.name != source.symbol {
                return Err("object replay current lowering symbol mismatch".into());
            }
            verified.push((row.symbol.clone(), row.object_bytes.clone()));
        }
        let emitted = EmittedModuleObject {
            artifact_name: "replay-current-object".into(),
            bytes: object.to_vec(),
            text_extents: Vec::new(),
        };
        let preserved = assert_merged_object_preserves_verified_text(&emitted, &verified)
            .map_err(|error| error.to_string())?;
        if preserved != self.preserved {
            return Err("object replay symbol/extent mismatch".into());
        }
        let mut rows = Vec::with_capacity(sources.len());
        for (source, row) in sources.iter().zip(&self.functions) {
            let actual = trust_ir_gate_obligation(source, &row.object_bytes, backend.target_arch());
            let result = if actual != row.obligation {
                Err("object replay reconstructed obligation differs".into())
            } else {
                match actual {
                    Err(reason) => Err(format!("non-replayable obligation: {reason}")),
                    Ok(obligation) => match &row.evidence {
                        RetainedEvidence::CompactInstantiation { certificate } => {
                            compact_instantiation::replay(
                                source,
                                &row.object_bytes,
                                backend.target_arch(),
                                certificate,
                            )
                        }
                        _ => replay_evidence(&obligation, &row.evidence),
                    },
                }
            };
            rows.push((source.symbol.clone(), result));
        }
        Ok(ObjectReplayReport { rows })
    }
}

fn raw_symbols(object: &[u8]) -> Result<Vec<RawTextSymbol>, String> {
    let (_, base) = extract_text_from_object(object)?;
    object_text_symbols(object, base, MAX_FUNCTIONS, MAX_SYMBOL_NAME_BYTES)
}

fn require_exact_symbols<'a>(
    object: &[u8],
    retained: &[RawTextSymbol],
    expected: impl IntoIterator<Item = &'a str>,
) -> Result<(), String> {
    let actual = raw_symbols(object)?;
    let expected: Vec<_> = expected.into_iter().collect();
    if actual != retained || actual.len() != expected.len() {
        return Err("raw defined-text symbol population mismatch".into());
    }
    let mut seen = BTreeSet::new();
    for row in actual {
        let exact_raw = match row.format {
            TextSymbolFormat::MachO => format!("_{}", row.name),
            TextSymbolFormat::Elf64 => row.name.clone(),
        };
        if !seen.insert(row.name.clone())
            || !expected.contains(&row.name.as_str())
            || row.raw_name != exact_raw
        {
            return Err("duplicate, unmatched, or noncanonical raw defined-text symbol".into());
        }
    }
    Ok(())
}

fn require_unique_source_ids(module: &trust_ir::Module) -> Result<(), String> {
    let mut functions = BTreeSet::new();
    let mut symbols = BTreeSet::new();
    for function in &module.functions {
        if !functions.insert(function.id.index()) || !symbols.insert(&function.name) {
            return Err("duplicate replay source function identity".into());
        }
        let mut blocks = BTreeSet::new();
        let mut values = BTreeSet::new();
        for block in &function.blocks {
            if !blocks.insert(block.id.index()) {
                return Err("duplicate replay source block identity".into());
            }
            for value in block
                .params
                .iter()
                .map(|(value, _)| value)
                .chain(block.body.iter().flat_map(|node| &node.results))
            {
                if !values.insert(value.index()) {
                    return Err("duplicate replay source SSA definition".into());
                }
            }
        }
    }
    Ok(())
}

fn linkage_identity(linkage: &[FunctionLinkage]) -> Vec<String> {
    linkage
        .iter()
        .map(|item| {
            match item {
                FunctionLinkage::External => "external",
                FunctionLinkage::Internal => "internal",
                FunctionLinkage::Hidden => "hidden",
            }
            .to_string()
        })
        .collect()
}

fn statics_identity(
    statics: &[trust_cg_codegen::pipeline::ObjectGlobal],
) -> Result<Vec<u8>, String> {
    if statics.len() > MAX_FUNCTIONS {
        return Err("object replay static population bound".into());
    }
    let mut rows = Vec::with_capacity(statics.len());
    for global in statics {
        let trust_cg_codegen::pipeline::ObjectGlobal {
            name,
            data,
            mutable,
            is_external,
            symbol_refs,
            is_thread_local,
            is_import,
            is_weak,
            align,
            visibility,
            retained,
            section,
            comdat,
        } = global;
        if data.len() > MAX_PART_BYTES || symbol_refs.len() > 4096 {
            return Err("object replay static payload bound".into());
        }
        let refs = symbol_refs
            .iter()
            .map(|reference| {
                let trust_cg_codegen::pipeline::GlobalSymbolRef { offset, symbol, addend } =
                    reference;
                (offset, symbol, addend)
            })
            .collect::<Vec<_>>();
        rows.push((
            name,
            data,
            mutable,
            is_external,
            refs,
            is_thread_local,
            is_import,
            is_weak,
            align,
            // trust-ir v41. Both change the EMITTED OBJECT — `visibility` sets
            // Mach-O `N_PEXT` / ELF `STV_*` and `retained` sets
            // `N_NO_DEAD_STRIP` / `SHF_GNU_RETAIN` — so two globals differing
            // only here are different statics and must not share a replay
            // identity. `Visibility` has no stable wire form here, so it is
            // framed by its discriminant, which is injective for a fieldless
            // enum.
            match visibility {
                trust_ir::Visibility::Default => 0u8,
                trust_ir::Visibility::Hidden => 1u8,
                trust_ir::Visibility::Protected => 2u8,
            },
            retained,
            // trust-ir v45, and both change the EMITTED OBJECT exactly as
            // `visibility`/`retained` do — `section` decides which output
            // section the definition's bytes land in, `comdat` whether the
            // linker may drop this copy in favour of an equivalent one. Two
            // globals differing only here are therefore DIFFERENT statics
            // and must not share a replay identity. Ignoring them would not
            // be a compile fix; it would be a hole in this function's whole
            // purpose.
            section,
            comdat,
        ));
    }
    encode(&rows, MAX_PART_BYTES)
}

fn replay_evidence(obligation: &GateObligation, evidence: &RetainedEvidence) -> Result<(), String> {
    if obligation.spec_reach != Formula::Bool(true)
        || obligation.machine_reach != Formula::Bool(true)
        || !obligation.spec_side_conditions.is_empty()
        || !obligation.ambient_pre.is_empty()
        || !obligation.abi_residue.is_empty()
    {
        return Err("non-replayable conditional/effect/modeling obligations".into());
    }
    match evidence {
        RetainedEvidence::CompactInstantiation { .. } => {
            Err("compact certificate requires independently supplied source/object context".into())
        }
        RetainedEvidence::BitBlast { proof } => {
            replay_bitblast(&obligation.machine_value, &obligation.spec_value, proof)
        }
        RetainedEvidence::BitBlastPair { high, low } => {
            let (mh, ml) =
                split_register_pair_128(&obligation.machine_value).ok_or("machine pair shape")?;
            let (sh, sl) =
                split_register_pair_128(&obligation.spec_value).ok_or("source pair shape")?;
            replay_bitblast(&mh, &sh, high)?;
            replay_bitblast(&ml, &sl, low)
        }
        RetainedEvidence::NonReplayable { original_kind, detail } => {
            Err(format!("non-replayable evidence {original_kind}: {detail}"))
        }
    }
}

fn replay_bitblast(
    machine: &Formula,
    source: &Formula,
    retained: &ay_proof::BvBlastProof,
) -> Result<(), String> {
    if retained.refutation.steps.len() > MAX_RECHECKABLE_REFUTATION_STEPS {
        return Err("retained proof exceeds existing kernel frontier".into());
    }
    encode(retained, MAX_PART_BYTES)?;
    let lhs = formula_to_bvexpr(machine)?;
    let rhs = formula_to_bvexpr(source)?;
    let budget = ay_proof::BvExprProofBudget::conservative(
        Duration::from_secs(10),
        MAX_RECHECKABLE_REFUTATION_STEPS,
    )
    .map_err(|error| error.to_string())?;
    let rebuilt = ay_proof::export_bv_blast_proof_expr_bounded(&lhs, &rhs, &budget)
        .map_err(|error| format!("bounded source-graph reconstruction: {error}"))?;
    if retained.format_version != rebuilt.format_version
        || retained.obligation != rebuilt.obligation
        || retained.vars != rebuilt.vars
        || retained.bit_lemmas != rebuilt.bit_lemmas
        || retained.clauses != rebuilt.clauses
    {
        return Err("retained Boolean graph differs from current source goal".into());
    }
    // The serialized refutation is replayed, not substituted with the rebuilt
    // solver's refutation. asserted_smt is intentionally not source authority.
    #[cfg(feature = "kernel-recheck")]
    {
        use clean_auto::proved_gate::GateRecheck;
        match crate::verify_output_instantiate::kernel_recheck_proved_grade_bounded(retained) {
            GateRecheck::KernelAccepted { .. } => Ok(()),
            other => Err(format!("retained kernel replay refused: {other:?}")),
        }
    }
    #[cfg(not(feature = "kernel-recheck"))]
    {
        Err("kernel replay feature absent".into())
    }
}

#[cfg(test)]
mod tests;

#[cfg(feature = "kernel-recheck")]
pub(crate) fn original_environment_digest(
    environment: &clean_kernel::Environment,
) -> Result<String, String> {
    compact_instantiation::environment_digest(environment)
}
