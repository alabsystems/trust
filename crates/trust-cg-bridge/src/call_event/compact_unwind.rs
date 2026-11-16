//! Mach-O arm64 ZERO-FRAME compact-unwind certificates.
//!
//! Consumer model: LLVM libunwind 9af1113ea3a186f3fbc008e20ee6ad2b81bbf55c,
//! CompactUnwinder.hpp:534-616; Apple libunwind
//! f709eccad023ec32db53d40146d07805cf3e4ee0, same file:531-614.
//! Encoding 0x02000000 reads no memory, keeps SP and recovers IP from raw LR.
//! This is an object-record/recovery proof, not a proof of the platform unwinder,
//! asynchronous interruption, faults, linker conversion, or a placed image.

use super::*;
use crate::compiled_object::{RelocKind, RelocTarget, SymbolKind};
use crate::original_conjunction_certificate::OriginalConjunctionCertificate;

const SECTION: &str = "__LD,__compact_unwind";
const ZERO_FRAME: u32 = 0x0200_0000;
const MODEL: &str = "trust.macho-arm64-zero-frame-prefix.v1";

/// Comparison data only. No wire field grants a metadata verdict.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Record {
    pub section: usize,
    pub offset: u64,
    pub symbol: String,
    pub code_section: usize,
    pub start: u64,
    pub length: u32,
    pub encoding: u32,
}
/// Portable untrusted proof data. Deserialization never constructs CheckedRecord.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Certificate {
    model: String,
    record: Record,
    prefix_pcs: Vec<u64>,
    original_proofs: Vec<OriginalConjunctionCertificate>,
}
#[derive(Clone, Debug, serde::Serialize)]
pub struct RecordStatus {
    pub record: Record,
    pub checked: bool,
    pub detail: String,
}
#[derive(Clone, Debug, serde::Serialize)]
pub struct ObservedRecord {
    pub offset: u64,
    pub range_start_word: u64,
    pub length: u32,
    pub encoding: u32,
    pub personality_word: u64,
    pub lsda_word: u64,
}
#[derive(Clone, Debug, serde::Serialize)]
pub struct SectionReport {
    pub model: String,
    #[serde(skip)]
    omit_on_wire: bool,
    pub records: Vec<RecordStatus>,
    /// Every complete raw row, including rows whose symbol/encoding refused.
    pub observed_records: Vec<ObservedRecord>,
    pub detail: String,
}
impl SectionReport {
    pub(super) fn omitted_on_wire(&self) -> bool {
        self.omit_on_wire
    }
    pub(super) fn unavailable(reason: impl Into<String>) -> Self {
        Self {
            model: MODEL.into(),
            omit_on_wire: false,
            records: Vec::new(),
            observed_records: Vec::new(),
            detail: reason.into(),
        }
    }
}

// Both constructors are private; neither type is Deserialize. In particular the
// final section decision consumes actual checked records, never report booleans.
pub(super) struct CheckedRecord {
    certificate: Certificate,
    object_sha256: String,
    module_sha256: String,
}
impl CheckedRecord {
    pub(super) fn certificate(&self) -> &Certificate {
        &self.certificate
    }
}
pub(super) struct CheckedSection {
    _checked: (),
}
pub(super) struct Inventory {
    records: Vec<Record>,
    object_sha256: String,
    module_sha256: String,
}
fn word(bytes: &[u8], at: usize) -> Result<u32, String> {
    let bytes: [u8; 4] = bytes
        .get(at..at.checked_add(4).ok_or("metadata offset overflow")?)
        .and_then(|bytes| bytes.try_into().ok())
        .ok_or("metadata word out of bounds")?;
    Ok(u32::from_le_bytes(bytes))
}
fn quad(bytes: &[u8], at: usize) -> Result<u64, String> {
    let bytes: [u8; 8] = bytes
        .get(at..at.checked_add(8).ok_or("metadata offset overflow")?)
        .and_then(|bytes| bytes.try_into().ok())
        .ok_or("metadata pointer out of bounds")?;
    Ok(u64::from_le_bytes(bytes))
}
fn module_hash(module: &Module) -> Result<String, String> {
    Ok(hex(&Sha256::digest(serde_json::to_vec(module).map_err(|e| e.to_string())?)))
}
// The normalized reader intentionally does not expose Mach-O section attributes.
// Read only the original descriptor here; no additional relocation is admitted
// by ObjectLayout and no public Section/FunctionWindow can mint this inventory.
fn section_descriptor(bytes: &[u8], ordinal: usize) -> Result<(u32, u32, u32), String> {
    let mut at = 32usize;
    let mut section = 0usize;
    let count = usize::try_from(word(bytes, 16)?).map_err(|_| "load-command count overflow")?;
    if count > bytes.len() / 8 {
        return Err("metadata load-command bound".into());
    }
    for _ in 0..count {
        let command = word(bytes, at)?;
        let size = usize::try_from(word(bytes, at + 4)?).map_err(|_| "command size overflow")?;
        let end = at
            .checked_add(size)
            .filter(|end| *end <= bytes.len())
            .ok_or("metadata command out of bounds")?;
        if size < 8 {
            return Err("metadata command too short".into());
        }
        if command == 0x19 {
            let n = usize::try_from(word(bytes, at + 64)?).map_err(|_| "section count overflow")?;
            if n > size.saturating_sub(72) / 80 {
                return Err("metadata section table bound".into());
            }
            for i in 0..n {
                section += 1;
                if section == ordinal {
                    let s = at + 72 + i * 80;
                    return Ok((word(bytes, s + 52)?, word(bytes, s + 60)?, word(bytes, s + 64)?));
                }
            }
        }
        at = end;
    }
    Err("metadata original section descriptor absent".into())
}
impl Inventory {
    pub(super) fn read(input: &CerInput<'_>, layout: &ObjectLayout) -> Result<Self, String> {
        if layout.object.format != ObjectFormat::MachO || word(input.object, 8)? != 0 {
            return Err("compact unwind supports CPU_SUBTYPE_ARM64_ALL only, no arm64e/PAC".into());
        }
        let target = input.m_cg.target_info.as_ref().ok_or("compact unwind target absent")?;
        if !matches!(target.triple.as_str(), "aarch64-apple-darwin" | "arm64-apple-macosx")
            || target.pointer_size != 8
            || target.endianness != trust_ir::Endianness::Little
        {
            return Err("compact unwind requires the exact non-PAC Darwin arm64 target".into());
        }
        let sections: Vec<_> =
            layout.object.sections.iter().filter(|s| s.name == SECTION).collect();
        if sections.len() != 1 {
            return Err("compact unwind needs exactly one actual section".into());
        }
        let section = sections[0];
        let (alignment, raw_relocations, flags) = section_descriptor(input.object, section.index)?;
        if alignment != 3
            || flags != 0x0200_0000
            || section.bytes.len() % 32 != 0
            || section.size != section.bytes.len() as u64
            || section.bytes.is_empty()
            || raw_relocations as usize != section.relocations.len()
            || section.relocations.len() != section.bytes.len() / 32
        {
            return Err("compact unwind requires complete 32-byte records, aligned debug section and exactly one raw relocation per record".into());
        }
        let mut records = Vec::new();
        let mut names = BTreeSet::new();
        let mut offsets = BTreeSet::new();
        for relocation in &section.relocations {
            if relocation.kind != (RelocKind::Other { raw: 0 })
                || relocation.pc_relative
                || relocation.length != 3
                || relocation.addend != 0
                || relocation.offset % 32 != 0
                || !offsets.insert(relocation.offset)
            {
                return Err("compact unwind start relocation is not unique canonical ARM64_RELOC_UNSIGNED64".into());
            }
            let at =
                usize::try_from(relocation.offset).map_err(|_| "metadata relocation overflow")?;
            let RelocTarget::Symbol(index) = relocation.target else {
                return Err("compact unwind needs an actual local function symbol target".into());
            };
            let symbol = layout.object.symbols.get(index).ok_or("metadata symbol absent")?;
            let window =
                layout.windows.get(&symbol.name).ok_or("metadata target has no bound body")?;
            if symbol.kind != SymbolKind::Function
                || symbol.weak
                || !window.expected.non_preemptible
                || symbol.section != Some(window.section)
                || symbol.value != window.start
                || !names.insert(symbol.name.clone())
            {
                return Err("compact unwind duplicate/preemptible/nonfunction target".into());
            }
            let length = word(&section.bytes, at + 8)?;
            if quad(&section.bytes, at)? != 0
                || quad(&section.bytes, at + 16)? != 0
                || quad(&section.bytes, at + 24)? != 0
                || length == 0
                || length % 4 != 0
                || u64::from(length) > window.end - window.start
            {
                return Err("compact unwind extent/addend/personality/LSDA mismatch".into());
            }
            // Record ranges may end before alignment padding, never before code.
            if !crate::compiled_object::all_padding(&window.code[length as usize..]) {
                return Err("compact unwind length omits actual non-padding instructions".into());
            }
            records.push(Record {
                section: section.index,
                offset: relocation.offset,
                symbol: symbol.name.clone(),
                code_section: window.section,
                start: window.start,
                length,
                encoding: word(&section.bytes, at + 12)?,
            });
        }
        records.sort_by_key(|record| record.offset);
        if names != layout.windows.keys().cloned().collect() {
            return Err(
                "compact unwind missing/orphan record in the complete function population".into()
            );
        }
        Ok(Self {
            records,
            object_sha256: layout.object.sha256_hex(),
            module_sha256: module_hash(input.m_cg)?,
        })
    }
    pub(super) fn supports(&self, symbol: &str) -> bool {
        self.records.iter().any(|r| r.symbol == symbol && r.encoding == ZERO_FRAME)
    }
    pub(super) fn check(
        &self,
        input: &CerInput<'_>,
        cert: &FunctionCertificate,
        execution: &leaf_memory::Execution,
        retained: Option<Option<&Certificate>>,
    ) -> Result<CheckedRecord, String> {
        let (binding, entry, prefixes) = execution.unwind_prefixes()?;
        self.check_prefixes(input, cert, binding, entry, prefixes, retained)
    }
    pub(super) fn check_tail(
        &self,
        input: &CerInput<'_>,
        cert: &FunctionCertificate,
        execution: &leaf_call_instance::tail_unwind::ActualTailUnwindPrefixes,
        retained: Option<Option<&Certificate>>,
    ) -> Result<CheckedRecord, String> {
        let (binding, entry, prefixes) = execution.prefixes()?;
        self.check_prefixes(input, cert, binding, entry, prefixes, retained)
    }
    // Private mathematical adapter. Only the two distinct sealed actual trace
    // capabilities above can reach it; math-only TailExecution cannot.
    fn check_prefixes(
        &self,
        input: &CerInput<'_>,
        cert: &FunctionCertificate,
        binding: &crate::cer_memory_machine::FunctionBinding,
        entry: &MachineState,
        prefixes: &[(u64, MachineState)],
        retained: Option<Option<&Certificate>>,
    ) -> Result<CheckedRecord, String> {
        let record = self
            .records
            .iter()
            .find(|r| r.symbol == cert.symbol)
            .ok_or("compact unwind record absent")?;
        if record.encoding != ZERO_FRAME {
            return Err("nonzero-frame/unsupported compact unwind encoding".into());
        }
        if binding.object_sha256 != self.object_sha256
            || binding.module_sha256 != self.module_sha256
            || binding.symbol != record.symbol
            || binding.section != record.code_section
            || binding.start != record.start
            || prefixes.len() * 4 != record.length as usize
        {
            return Err("compact unwind actual execution/record subjects differ".into());
        }
        let retained = match retained {
            Some(Some(wire))
                if wire.model == MODEL
                    && wire.record == *record
                    && wire.prefix_pcs.len() == prefixes.len()
                    && wire.original_proofs.len() == prefixes.len() =>
            {
                Some(wire)
            }
            Some(_) => {
                return Err("compact unwind retained proof/model/record population mismatch".into());
            }
            None => None,
        };
        let mut original_proofs = Vec::new();
        // Reuse real checked mathematical evidence only when the independently
        // rebuilt ORIGINAL equations are exactly equal, in this fixed context.
        // A different prefix goal must obtain its own actual kernel evidence.
        let mut cached: Option<(
            Vec<(Formula, Formula)>,
            crate::original_conjunction_certificate::CheckedOriginalConjunction,
        )> = None;
        let mut prefix_pcs = Vec::new();
        for (i, (pc, state)) in prefixes.iter().enumerate() {
            if *pc != record.start + i as u64 * 4 {
                return Err("compact unwind incomplete linear prefix census".into());
            }
            prefix_pcs.push(*pc);
            let mut equations = Vec::new();
            // Literal ZERO_FRAME means no loads/pair restoration and stackSize0.
            // Keep the original +0 recovery expression in the actual kernel goal.
            equations.push((
                Formula::BvAdd(b(state.sp.clone()), b(Formula::BitVec { value: 0, width: 64 }), 64),
                entry.sp.clone(),
            ));
            equations.push((state.gpr[30].clone(), entry.gpr[30].clone()));
            for reg in 18..=29 {
                equations.push((state.gpr[reg].clone(), entry.gpr[reg].clone()));
            }
            for reg in 8..=15 {
                let low = |state: &MachineState| Formula::BvExtract {
                    inner: b(state.fpr[reg].clone()),
                    high: 63,
                    low: 0,
                };
                equations.push((low(state), low(entry)));
            }
            let proof = match retained {
                Some(wire) => {
                    if wire.prefix_pcs[i] != *pc {
                        return Err("compact unwind retained actual prefix mismatch".into());
                    }
                    let proof = &wire.original_proofs[i];
                    proof.require_subject(input, cert)?;
                    let checked = proof.replay(&equations)?;
                    OriginalConjunctionCertificate::bind(&checked, input, cert)?
                }
                None => {
                    let checked = if let Some((original, checked)) = &cached
                        && *original == equations
                    {
                        checked.clone()
                    } else {
                        let Some(ProvenEvidence::KernelInstantiated {
                            original: Some(checked),
                            ..
                        }) = crate::verify_output::try_kernel_recheckable_original_conjunction(
                            &equations,
                        )
                        else {
                            return Err(format!(
                                "compact unwind original22-lane prefix/recovery conjunction not kernel checked at {pc:#x}"
                            ));
                        };
                        (*checked).clone()
                    };
                    let proof = OriginalConjunctionCertificate::bind(&checked, input, cert)?;
                    // Recheck the retained original proof at each actual prefix,
                    // even when identical mathematical evidence was cached.
                    proof.replay(&equations)?;
                    cached = Some((equations, checked));
                    proof
                }
            };
            original_proofs.push(proof);
        }
        Ok(CheckedRecord {
            certificate: Certificate {
                model: MODEL.into(),
                record: record.clone(),
                prefix_pcs,
                original_proofs,
            },
            object_sha256: self.object_sha256.clone(),
            module_sha256: self.module_sha256.clone(),
        })
    }
}
pub(super) fn finish_section(
    inventory: &Result<Inventory, String>,
    checked: &[CheckedRecord],
    layout: &ObjectLayout,
) -> (SectionReport, Option<CheckedSection>) {
    let observed_records: Result<Vec<ObservedRecord>, String> = layout
        .object
        .sections
        .iter()
        .filter(|s| s.name == SECTION)
        .flat_map(|section| {
            section.bytes.as_chunks::<32>().0.iter().enumerate().map(|(i, bytes)| {
                Ok(ObservedRecord {
                    offset: i as u64 * 32,
                    range_start_word: quad(bytes, 0)?,
                    length: word(bytes, 8)?,
                    encoding: word(bytes, 12)?,
                    personality_word: quad(bytes, 16)?,
                    lsda_word: quad(bytes, 24)?,
                })
            })
        })
        .collect();
    let observed_records = match observed_records {
        Ok(records) => records,
        Err(error) => return (SectionReport::unavailable(error), None),
    };
    let inventory = match inventory {
        Ok(inventory) => inventory,
        Err(error) => {
            let mut report = SectionReport::unavailable(error.clone());
            report.observed_records = observed_records;
            return (report, None);
        }
    };
    let mut records = Vec::new();
    let mut complete = checked.len() == inventory.records.len();
    for record in &inventory.records {
        let witnesses: Vec<_> = checked
            .iter()
            .filter(|c| {
                c.certificate.record == *record
                    && c.object_sha256 == inventory.object_sha256
                    && c.module_sha256 == inventory.module_sha256
            })
            .collect();
        let verified = witnesses.len() == 1;
        complete &= verified;
        records.push(RecordStatus { record: record.clone(), checked: verified,
            detail: if verified { "actual original kernel-checked recovery at every decoded prefix" }
                else { "no complete checked prefix recovery for this actual record; frame/call/control/unsupported/kernel debt remains" }.into() });
    }
    let detail = if complete {
        "every actual record has a private checked ZERO-FRAME prefix certificate; object metadata only, platform/linker/async semantics remain trusted"
    } else {
        "section remains unverified: not every actual record has checked semantics and prefix coverage"
    };
    (
        SectionReport {
            model: MODEL.into(),
            omit_on_wire: false,
            records,
            observed_records,
            detail: detail.into(),
        },
        complete.then_some(CheckedSection { _checked: () }),
    )
}

// Optional new metadata retention must never change the old function grade fold.
// If it pushes an otherwise valid ordinary report beyond its EXISTING bound,
// withhold metadata evidence and restore explicit unverified-section disclosure.
// The unchanged original function retention check still runs afterwards.
pub(super) fn preserve_function_retention(report: &mut CerReport) {
    preserve_function_retention_at(
        report,
        crate::original_conjunction_certificate::MAX_SIDECAR_BYTES,
    );
}
fn preserve_function_retention_at(report: &mut CerReport, limit: usize) {
    if report.compact_unwind.omit_on_wire {
        return;
    }
    let had_packets = report.certificates.iter().any(|c| c.compact_unwind.is_some());
    struct Budget {
        bytes: usize,
        limit: usize,
    }
    impl std::io::Write for Budget {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.bytes =
                self.bytes.checked_add(bytes.len()).filter(|n| *n <= self.limit).ok_or_else(
                    || std::io::Error::other("optional compact unwind retention byte bound"),
                )?;
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    if serde_json::to_writer_pretty(&mut Budget { bytes: 0, limit }, report).is_err() {
        for cert in &mut report.certificates {
            cert.compact_unwind = None;
        }
        report.compact_unwind.omit_on_wire = true;
        if had_packets && !report.unverified_sections.iter().any(|s| s == SECTION) {
            report.unverified_sections.push(SECTION.into());
        }
        report.compact_unwind.detail = "section unverified: optional metadata proof packets exceed ordinary report retention bound".into();
        for row in &mut report.compact_unwind.records {
            row.checked = false;
            row.detail =
                "checked metadata proof not retained within ordinary report byte bound".into();
        }
    }
}

#[cfg(test)]
mod tests;
