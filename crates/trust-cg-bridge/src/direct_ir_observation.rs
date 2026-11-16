//! Conditional original-IR/final-object register observations, not admission.
//!
//! The existing direct IR/byte interpreters and the Formula-to-CIC translation
//! remain trusted. A checked result proves its complete ORIGINAL return/O0
//! conjunction only. Nonfaulting private stack/frame, world/memory separation,
//! physical Rust ABI, source/NoUB/body licensing, GCS/PAC/linker and unwind
//! obligations remain OPEN. No conversion to an emission verdict exists.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_ir::{CallingConv, Ty};
use trust_types::Formula;

use crate::codegen_backend::TrustCgTargetArch;
use crate::compiled_object::{
    CompiledObject, InsnClass, ObjectExpectations, ObjectFormat, ObjectLayout, RelocationModel,
    classify_insn,
};
use crate::original_conjunction_certificate::{
    CheckedOriginalConjunction, OriginalConjunctionPacket,
};
use crate::verify_output::{
    ProvenEvidence, extract_text_from_object, platform_reserves_x18, pred_to_int,
    symbolic_machine_outcome_traps, try_kernel_recheckable_original_conjunction,
};
use crate::verify_output_trust_ir::{TrustIrGateSource, trust_ir_gate_obligation};

const MODEL: u32 = 1;
const MAX_MODULE_BYTES: usize = 4 * 1024 * 1024;
const MAX_OBJECT_BYTES: usize = 256 * 1024 * 1024;
const MAX_PACKET_BYTES: usize = 8 * 1024 * 1024;
fn hash(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}

fn instruction_words(text: &[u8]) -> Result<Vec<u32>, String> {
    if text.is_empty() || text.len() % 4 != 0 {
        return Err("direct original observation: invalid instruction alignment".into());
    }
    Ok(text.as_chunks::<4>().0.iter().copied().map(u32::from_le_bytes).collect())
}
#[cfg(feature = "test-hooks")]
pub fn test_instruction_words(text: &[u8]) -> Result<Vec<u32>, String> {
    instruction_words(text)
}

/// Untrusted comparison data, rederived from actual source and object on replay.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Subject {
    model: u32,
    module_sha256: String,
    object_sha256: String,
    object_bytes: usize,
    function: u32,
    function_type: u32,
    entry: u32,
    symbol: String,
    section: usize,
    extent: (u64, u64),
    text_sha256: String,
    instruction_words: Vec<u32>,
    unverified_sections: Vec<String>,
}
/// Exact originals, before ABI folding; no counts or residue summaries grant authority.
#[derive(Debug, Clone, Serialize)]
pub struct OriginalObservations {
    subject: Subject,
    names: Vec<String>,
    equations: Vec<(Formula, Formula)>,
}
impl OriginalObservations {
    pub fn equations(&self) -> &[(Formula, Formula)] {
        &self.equations
    }
    pub fn names(&self) -> &[String] {
        &self.names
    }
}
/// Bounded portable DATA. Deserialization cannot produce a checked result.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DirectIrObservationPacket {
    subject: Subject,
    names: Vec<String>,
    proof: OriginalConjunctionPacket,
}
/// Private checked construction; deliberately not Deserialize and not an OutputVerdict.
#[derive(Clone, Debug)]
pub struct CheckedDirectIrObservation {
    wire: DirectIrObservationPacket,
    checked: CheckedOriginalConjunction,
}
impl CheckedDirectIrObservation {
    pub fn packet(&self) -> &DirectIrObservationPacket {
        &self.wire
    }
    pub fn original_equations(&self) -> &[(Formula, Formula)] {
        self.checked.original_equations()
    }
    pub fn remaining_requirements(&self) -> &'static [&'static str] {
        &[
            "trusted direct IR/byte/Formula semantics correspondence",
            "real physical Rust ABI and source/SourceNoUB/body license",
            "nonfaulting legal private stack/frame and outside-frame world/memory preservation",
            "GCS/PAC/placement/linker/unwind/exception semantics and whole compiler admission",
        ]
    }
}
struct Limit(usize);
impl std::io::Write for Limit {
    fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
        self.0 = self
            .0
            .checked_add(b.len())
            .filter(|n| *n <= MAX_PACKET_BYTES)
            .ok_or_else(|| std::io::Error::other("direct original packet byte limit"))?;
        Ok(b.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
impl DirectIrObservationPacket {
    pub fn encoded_bytes(&self) -> Result<usize, String> {
        let mut out = Limit(0);
        serde_json::to_writer(&mut out, self).map_err(|e| e.to_string())?;
        Ok(out.0)
    }
    pub fn decode(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > MAX_PACKET_BYTES {
            return Err("direct original packet byte limit".into());
        }
        serde_json::from_slice(bytes).map_err(|e| e.to_string())
    }
    pub fn replay(
        &self,
        source: &TrustIrGateSource,
        object: &[u8],
        arch: TrustCgTargetArch,
    ) -> Result<CheckedDirectIrObservation, String> {
        self.encoded_bytes()?;
        let expected = derive(source, object, arch)?;
        if self.subject != expected.subject || self.names != expected.names {
            return Err("direct original packet: actual complete source/object/function/extent/relocation subject mismatch".into());
        }
        let checked = self.proof.replay(&expected.equations)?;
        Ok(CheckedDirectIrObservation { wire: self.clone(), checked })
    }
}

/// Derive data from the SAME original IR and byte interpreters as the existing
/// direct checker. No LIR, emitter, solver, fabricated ABI cross-check or body
/// authorization is read. This bounded prototype admits one straight-line U64
/// function and binds every actual text byte, without unobserved padding/paths.
pub fn derive(
    source: &TrustIrGateSource,
    bytes: &[u8],
    arch: TrustCgTargetArch,
) -> Result<OriginalObservations, String> {
    if arch != TrustCgTargetArch::AArch64 || bytes.is_empty() || bytes.len() > MAX_OBJECT_BYTES {
        return Err("direct original observation: AArch64/object byte bound".into());
    }
    let m = &source.module;
    let encoded = trust_ir::binary::serialize_module(m).map_err(|e| e.to_string())?;
    if encoded.len() > MAX_MODULE_BYTES || !trust_ir_build::validate_module(m).is_empty() {
        return Err("direct original observation: original complete module validation/size".into());
    }
    let [f] = m.functions.as_slice() else {
        return Err("direct original observation: complete single-function population".into());
    };
    if f.id != source.func_id
        || f.name != source.symbol
        || f.name.is_empty()
        || f.name.len() > 4096
        || f.calling_conv != CallingConv::Rust
    {
        return Err(
            "direct original observation: exact original function/Rust logical convention".into()
        );
    }
    let ty = m.func_type(f.ty).ok_or("direct original observation: original signature")?;
    if ty.params != [Ty::U64]
        || ty.returns != [Ty::U64]
        || ty.is_vararg
        || f.blocks.len() != 1
        || !m.globals.is_empty()
    {
        return Err("direct original observation: closed U64 entry/return fragment".into());
    }
    let parsed = CompiledObject::parse(bytes).map_err(|e| format!("{e:?}"))?;
    if parsed.format != ObjectFormat::MachO {
        return Err("direct original observation: Mach-O profile only".into());
    }
    // Static is an O1 binding profile only, not an asserted compiler configuration.
    // This profile rejects ALL code relocations/call sites and all position-dependent
    // data before execution; no relocation-model assumption enters the equations.
    let expectations = ObjectExpectations::from_module(m, parsed.format, RelocationModel::Static)
        .map_err(|e| format!("{e:?}"))?;
    let layout = ObjectLayout::bind(parsed, &expectations).map_err(|e| format!("{e:?}"))?;
    let window =
        layout.windows.get(&source.symbol).ok_or("direct original observation: actual window")?;
    if layout.windows.len() != 1
        || !window.unknown.is_empty()
        || !window.sites.is_empty()
        || !window.relocations.is_empty()
        || !window.data_in_code.is_empty()
    {
        return Err(
            "direct original observation: complete straight-line window/relocation binding".into(),
        );
    }
    let (text, base) = extract_text_from_object(bytes)?;
    if text != window.code
        || text.is_empty()
        || text.len() % 4 != 0
        || window.start != 0
        || window.reachable.len() != text.len() / 4
    {
        return Err("direct original observation: full text/window/reach population".into());
    }
    let words = instruction_words(&text)?;
    for (i, word) in words.iter().enumerate() {
        let pc = window.start + 4 * i as u64;
        if !window.reachable.contains(&pc) {
            return Err("direct original observation: unobserved instruction".into());
        }
        if i + 1 == words.len() {
            if classify_insn(*word) != InsnClass::Ret {
                return Err("direct original observation: final actual RET required".into());
            }
        } else if !matches!(
            classify_insn(*word),
            InsnClass::Plain | InsnClass::AddImm64 | InsnClass::LoadStoreUImm
        ) {
            return Err(
                "direct original observation: control/address model outside straight-line profile"
                    .into(),
            );
        }
    }
    let obligation = trust_ir_gate_obligation(source, bytes, arch)?;
    if obligation.out_width != 64
        || obligation.spec_reach != Formula::Bool(true)
        || obligation.machine_reach != Formula::Bool(true)
        || !obligation.spec_side_conditions.is_empty()
        || !obligation.ambient_pre.is_empty()
        || !obligation.segments.is_empty()
    {
        return Err(
            "direct original observation: unsupported reach/model/ambient/loop obligation".into()
        );
    }
    let raw = symbolic_machine_outcome_traps(&text, base, 64, false)?;
    if raw.value != obligation.machine_value
        || raw.reach != obligation.machine_reach
        || !raw.arrivals.is_empty()
    {
        return Err("direct original observation: original execution mismatch".into());
    }
    let mut names = vec!["original IR return == actual byte return".into()];
    let mut equations = vec![(obligation.spec_value, raw.value)];
    for (name, end, start) in raw.abi.original_equations() {
        names.push(name);
        equations.push((end, start));
    }
    if platform_reserves_x18(bytes) {
        names.push("Darwin X18 never written".into());
        equations.push((pred_to_int(raw.x18_written, 1), Formula::BitVec { value: 0, width: 1 }));
    }
    let subject = Subject {
        model: MODEL,
        module_sha256: hash(&encoded),
        object_sha256: hash(bytes),
        object_bytes: bytes.len(),
        function: f.id.index(),
        function_type: f.ty.index(),
        entry: f.entry.index(),
        symbol: f.name.clone(),
        section: window.section,
        extent: (window.start, window.end),
        text_sha256: window.text_sha256(),
        instruction_words: words,
        unverified_sections: layout.unverified_sections,
    };
    Ok(OriginalObservations { subject, names, equations })
}

/// Prove the COMPLETE original return and raw O0 conjunction. Any unreflectable
/// or false member declines the entire result; no scalar-only success fallback.
/// The remaining requirements above are never discharged by these equations.
pub fn prove(
    source: &TrustIrGateSource,
    object: &[u8],
    arch: TrustCgTargetArch,
) -> Result<CheckedDirectIrObservation, String> {
    let original = derive(source, object, arch)?;
    let Some(ProvenEvidence::KernelInstantiated { original: Some(checked), .. }) =
        try_kernel_recheckable_original_conjunction(&original.equations)
    else {
        return Err(
            "direct original observation: complete raw return/O0 CIC conjunction declined".into()
        );
    };
    let wire = DirectIrObservationPacket {
        subject: original.subject,
        names: original.names,
        proof: checked.packet().clone(),
    };
    wire.encoded_bytes()?;
    Ok(CheckedDirectIrObservation { wire, checked: (*checked).clone() })
}

/// RETURN-VALUE-ONLY portable proof. All raw ABI equations are retained as
/// independently rederived UNPROVED debt. This is a different carrier from the
/// complete raw return/O0 conjunction above and cannot be converted to it.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DirectIrReturnValuePacket {
    subject: Subject,
    pending_raw_abi_sha256: String,
    proof: OriginalConjunctionPacket,
}
/// One universal return-value observation under the trusted symbolic model.
/// It grants NO full-function, ABI, memory, execution, source or emission grade.
#[derive(Debug, Clone)]
pub struct CheckedDirectIrReturnValue {
    wire: DirectIrReturnValuePacket,
    checked: CheckedOriginalConjunction,
    pending: OriginalObservations,
}
fn pending_digest(original: &OriginalObservations) -> Result<String, String> {
    serde_json::to_vec(&(&original.names[1..], &original.equations[1..]))
        .map(|b| hash(&b))
        .map_err(|e| e.to_string())
}
impl CheckedDirectIrReturnValue {
    pub fn packet(&self) -> &DirectIrReturnValuePacket {
        &self.wire
    }
    pub fn original_return_equation(&self) -> &[(Formula, Formula)] {
        self.checked.original_equations()
    }
    pub fn pending_raw_abi_equations(&self) -> &[(Formula, Formula)] {
        &self.pending.equations[1..]
    }
    pub fn pending_raw_abi_names(&self) -> &[String] {
        &self.pending.names[1..]
    }
}
impl DirectIrReturnValuePacket {
    pub fn decode(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > MAX_PACKET_BYTES {
            return Err("direct return-only packet byte limit".into());
        }
        serde_json::from_slice(bytes).map_err(|e| e.to_string())
    }
    pub fn replay(
        &self,
        source: &TrustIrGateSource,
        object: &[u8],
        arch: TrustCgTargetArch,
    ) -> Result<CheckedDirectIrReturnValue, String> {
        let mut limit = Limit(0);
        serde_json::to_writer(&mut limit, self).map_err(|e| e.to_string())?;
        let expected = derive(source, object, arch)?;
        if self.subject != expected.subject
            || self.pending_raw_abi_sha256 != pending_digest(&expected)?
        {
            return Err(
                "direct return-only packet: actual complete source/object/body/ABI debt mismatch"
                    .into(),
            );
        }
        let checked = self.proof.replay(&expected.equations[..1])?;
        Ok(CheckedDirectIrReturnValue { wire: self.clone(), checked, pending: expected })
    }
}
/// Explicit partial mathematical evidence, never a fallback favorable grade.
/// The full-conjunction `prove` above still requires EVERY original O0 equation.
pub fn prove_return_value(
    source: &TrustIrGateSource,
    object: &[u8],
    arch: TrustCgTargetArch,
) -> Result<CheckedDirectIrReturnValue, String> {
    let expected = derive(source, object, arch)?;
    let Some(ProvenEvidence::KernelInstantiated { original: Some(checked), .. }) =
        try_kernel_recheckable_original_conjunction(&expected.equations[..1])
    else {
        return Err("direct return-only original CIC proof declined".into());
    };
    let wire = DirectIrReturnValuePacket {
        subject: expected.subject.clone(),
        pending_raw_abi_sha256: pending_digest(&expected)?,
        proof: checked.packet().clone(),
    };
    let mut limit = Limit(0);
    serde_json::to_writer(&mut limit, &wire).map_err(|e| e.to_string())?;
    Ok(CheckedDirectIrReturnValue { wire, checked: (*checked).clone(), pending: expected })
}
/// Test-only denial instrumentation. It can forbid proof production, never
/// authorize proof or turn untrusted wire data into a checked result.
#[cfg(feature = "test-hooks")]
pub fn without_original_production<T>(action: impl FnOnce() -> T) -> T {
    crate::original_conjunction_certificate::without_production(action)
}
