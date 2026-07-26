// trust-lift: public binary-to-TrustIr API
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[cfg(any(feature = "macho", feature = "elf"))]
use crate::{FunctionBoundary, Lifter};
use crate::{LiftError, LiftedFunction};
use trust_types::{
    BinaryAddressRange, BinaryMemoryModel, BinaryOrigin, BinarySegment, BinarySegmentPermissions,
    SourceSpan,
};
#[cfg(any(feature = "macho", feature = "elf"))]
use trust_types::{
    BinaryFactEvidence, BinaryMemoryRegion, Endianness, MemoryRegionKind, ModelAssumption,
    TrustLevel, UnsupportedRecord,
};

/// Which functions to lift from a binary.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum BinaryFunctionSelection {
    /// Lift the parsed binary entry point.
    #[default]
    Entry,
    /// Lift every detected function symbol.
    All,
    /// Lift functions containing these virtual addresses.
    Addresses(Vec<u64>),
    /// Lift functions with these exact normalized symbol names.
    Names(Vec<String>),
}

/// Options for [`lift_binary_to_trust_ir`].
///
/// The default is conservative proof mode: lift the binary entry point and
/// return an error on the first selected function that cannot be lifted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryLiftOptions {
    /// Function selection policy.
    pub functions: BinaryFunctionSelection,
    /// When true, fail the whole request on the first per-function lift error.
    pub strict: bool,
}

impl Default for BinaryLiftOptions {
    fn default() -> Self {
        Self { functions: BinaryFunctionSelection::Entry, strict: true }
    }
}

impl BinaryLiftOptions {
    /// Select all detected function symbols.
    #[must_use]
    pub fn all_functions() -> Self {
        Self { functions: BinaryFunctionSelection::All, ..Self::default() }
    }

    /// Select functions by virtual address.
    pub fn functions_by_address<I>(addresses: I) -> Self
    where
        I: IntoIterator<Item = u64>,
    {
        Self {
            functions: BinaryFunctionSelection::Addresses(addresses.into_iter().collect()),
            ..Self::default()
        }
    }

    /// Select functions by normalized symbol name.
    pub fn functions_by_name<I, S>(names: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            functions: BinaryFunctionSelection::Names(names.into_iter().map(Into::into).collect()),
            ..Self::default()
        }
    }

    /// Allow partial results and collect per-function failures.
    #[must_use]
    pub fn best_effort(mut self) -> Self {
        self.strict = false;
        self
    }
}

/// Per-function failure recorded when [`BinaryLiftOptions::strict`] is false.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiftedFunctionFailure {
    /// Normalized symbol name, when available.
    pub name: Option<String>,
    /// Requested virtual address.
    pub entry_point: u64,
    /// Display form of the lift error.
    pub error: String,
}

/// Provenance for a function entry chosen by the binary lifter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiftedFunctionSeedSource {
    /// The seed came from the parsed binary entry point.
    EntryPoint,
    /// The seed came from a recovered function symbol.
    Symbol,
    /// The caller requested an address explicitly.
    RequestedAddress,
    /// The caller requested a symbol name explicitly.
    RequestedName,
}

/// Function seed selected before lifting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiftedFunctionSeed {
    /// Normalized symbol name, when available.
    pub name: Option<String>,
    /// Function entry point used for lifting.
    pub entry_point: u64,
    /// Recovered function size, when available.
    pub size: Option<u64>,
    /// Source of this function seed.
    pub source: LiftedFunctionSeedSource,
}

/// Exact source provenance availability carried from the binary parser.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiftedSourceProvenanceStatus {
    /// No exact debug/source mapping was available.
    Unavailable,
    /// Exact address-to-source mappings were recovered.
    Exact,
    /// Some debug/source rows were ambiguous and are withheld.
    Ambiguous,
    /// Debug/source data existed but could not be parsed safely.
    Unsupported,
}

impl LiftedSourceProvenanceStatus {
    /// Stable lowercase name for report and snapshot serialization.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Unavailable => "unavailable",
            Self::Exact => "exact",
            Self::Ambiguous => "ambiguous",
            Self::Unsupported => "unsupported",
        }
    }
}

/// Source provenance gate for a lifted binary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiftedSourceProvenance {
    /// Overall source provenance state.
    pub status: LiftedSourceProvenanceStatus,
    /// Number of exact mappings carried in [`LiftedBinary::source_mappings`].
    pub exact_mapping_count: usize,
    /// Number of ambiguous addresses intentionally withheld.
    pub ambiguous_mapping_count: usize,
    /// Human-readable diagnostics explaining the gate.
    pub diagnostics: Vec<String>,
}

impl Default for LiftedSourceProvenance {
    fn default() -> Self {
        Self {
            status: LiftedSourceProvenanceStatus::Unavailable,
            exact_mapping_count: 0,
            ambiguous_mapping_count: 0,
            diagnostics: vec![
                "exact debug/source provenance is unavailable; diagnostics remain binary-address-only"
                    .to_string(),
            ],
        }
    }
}

/// One exact binary-address to source span mapping.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiftedSourceMapping {
    /// Instruction address with an exact debug/source row.
    pub binary_address: u64,
    /// Exact source span from debug information.
    pub source: SourceSpan,
}

/// Selected image bytes used for exact replay byte/range attestation.
///
/// `file_offset` is the offset of `bytes` in the root artifact. Thin binaries
/// usually use `0`; fat containers can pass the selected slice offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExactReplaySelectedImage<'a> {
    /// Offset of the selected image in the root artifact.
    pub file_offset: u64,
    /// Exact selected image bytes.
    pub bytes: &'a [u8],
}

impl<'a> ExactReplaySelectedImage<'a> {
    /// Build selected-image evidence from a root-artifact offset and bytes.
    #[must_use]
    pub fn new(file_offset: u64, bytes: &'a [u8]) -> Self {
        Self { file_offset, bytes }
    }

    /// Build selected-image evidence for thin binaries whose selected image is
    /// the whole byte slice.
    #[must_use]
    pub fn thin(bytes: &'a [u8]) -> Self {
        Self::new(0, bytes)
    }

    fn end_offset(self) -> Option<u64> {
        let len = u64::try_from(self.bytes.len()).ok()?;
        self.file_offset.checked_add(len)
    }
}

/// Normalized instruction witness supplied by exact machine replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactReplayInstructionWitness {
    /// Virtual address of the instruction that replay claims was executed.
    pub instruction_address: u64,
    /// Decoded instruction size. Missing or zero size is rejected.
    pub instruction_size: Option<u8>,
    /// Original instruction bytes replay claims came from the selected image.
    pub instruction_bytes: Vec<u8>,
}

impl ExactReplayInstructionWitness {
    /// Build an instruction witness with explicit size and bytes.
    #[must_use]
    pub fn new(instruction_address: u64, instruction_size: u8, instruction_bytes: Vec<u8>) -> Self {
        Self { instruction_address, instruction_size: Some(instruction_size), instruction_bytes }
    }

    /// Build an instruction witness from binary-origin provenance.
    #[must_use]
    pub fn from_origin(origin: &BinaryOrigin) -> Self {
        Self {
            instruction_address: origin.instruction_address,
            instruction_size: origin.instruction_size,
            instruction_bytes: origin.instruction_bytes.clone(),
        }
    }
}

/// Per-instruction replay byte/range attestation result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactReplayInstructionAttestation {
    /// Virtual instruction address.
    pub instruction_address: u64,
    /// Claimed instruction size.
    pub instruction_size: Option<u8>,
    /// Root-artifact byte range backing this instruction, when recoverable.
    pub file_range: Option<BinaryAddressRange>,
    /// Loader segment name that covered the instruction, when known.
    pub segment_name: Option<String>,
    /// Loader permissions for the segment that covered the instruction.
    pub segment_permissions: Option<BinarySegmentPermissions>,
    /// True only when byte identity, selected-image range, and executable
    /// segment permission evidence were all present.
    pub accepted: bool,
    /// Fail-closed blockers for this instruction.
    pub blockers: Vec<String>,
}

/// Exact replay slice attestation over a selected image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactReplaySliceAttestation {
    /// True only when at least one instruction was attested and every
    /// instruction had complete byte/range/executable-segment evidence.
    pub accepted: bool,
    /// Number of instruction witnesses checked.
    pub instruction_count: usize,
    /// Number of instruction witnesses accepted.
    pub accepted_instruction_count: usize,
    /// Slice-level and instruction-level blockers.
    pub blockers: Vec<String>,
    /// Per-instruction attestation records.
    pub instructions: Vec<ExactReplayInstructionAttestation>,
}

/// Byte order assumed by the binary lifter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryEndianness {
    /// Least-significant byte first.
    Little,
    /// Most-significant byte first.
    Big,
    /// The binary parser did not expose a byte order.
    Unknown,
}

impl BinaryEndianness {
    /// Human-readable name for reports.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Little => "little",
            Self::Big => "big",
            Self::Unknown => "unknown",
        }
    }
}

/// Lifted TrustIr functions plus binary metadata.
#[derive(Debug, Clone)]
pub struct LiftedBinary {
    /// Detected binary format.
    pub format: &'static str,
    /// Detected target architecture.
    pub architecture: &'static str,
    /// Byte order accepted by the lifter and used for memory facts.
    pub endianness: BinaryEndianness,
    /// Parsed binary entry point, when present.
    pub entry_point: Option<u64>,
    /// Build ID or equivalent loader identifier, when available.
    pub build_id: Option<String>,
    /// Loader-mapped segments with recovered permissions.
    pub segments: Vec<BinarySegment>,
    /// Shared memory model containing loader regions and lifted memory facts.
    pub memory_model: BinaryMemoryModel,
    /// Function seeds selected before lifting.
    pub function_seeds: Vec<LiftedFunctionSeed>,
    /// Exact source provenance availability.
    pub source_provenance: LiftedSourceProvenance,
    /// Exact binary-address to source mappings.
    pub source_mappings: Vec<LiftedSourceMapping>,
    /// Successfully lifted functions.
    pub functions: Vec<LiftedFunction>,
    /// Best-effort per-function failures.
    pub failures: Vec<LiftedFunctionFailure>,
}

impl LiftedBinary {
    /// Return an exact source span for `address`, if the parser proved one.
    #[must_use]
    pub fn exact_source_span(&self, address: u64) -> Option<SourceSpan> {
        self.source_mappings
            .iter()
            .find(|mapping| mapping.binary_address == address)
            .map(|mapping| mapping.source.clone())
    }

    /// Attest that replayed instruction bytes/ranges came from executable
    /// loader segments in the selected image.
    ///
    /// This is intentionally fail-closed: the returned slice is accepted only
    /// when every witness has an instruction size, matching original bytes,
    /// a file-backed byte range inside `selected_image`, and an executable
    /// segment covering the full virtual instruction range.
    #[must_use]
    pub fn attest_exact_replay_slice(
        &self,
        selected_image: ExactReplaySelectedImage<'_>,
        witnesses: &[ExactReplayInstructionWitness],
    ) -> ExactReplaySliceAttestation {
        let mut blockers = Vec::new();
        if selected_image.bytes.is_empty() {
            blockers.push("missing selected image bytes".to_string());
        }
        if selected_image.end_offset().is_none() {
            blockers.push("selected image byte range overflows address space".to_string());
        }
        if witnesses.is_empty() {
            blockers.push("no replayed instruction witnesses".to_string());
        }

        let instructions = witnesses
            .iter()
            .map(|witness| self.attest_exact_replay_instruction(selected_image, witness))
            .collect::<Vec<_>>();
        let accepted_instruction_count =
            instructions.iter().filter(|record| record.accepted).count();
        blockers.extend(
            instructions
                .iter()
                .flat_map(|record| record.blockers.iter().cloned())
                .collect::<Vec<_>>(),
        );
        let accepted = !witnesses.is_empty()
            && blockers.is_empty()
            && accepted_instruction_count == witnesses.len();

        ExactReplaySliceAttestation {
            accepted,
            instruction_count: witnesses.len(),
            accepted_instruction_count,
            blockers,
            instructions,
        }
    }

    fn attest_exact_replay_instruction(
        &self,
        selected_image: ExactReplaySelectedImage<'_>,
        witness: &ExactReplayInstructionWitness,
    ) -> ExactReplayInstructionAttestation {
        let mut blockers = Vec::new();
        let mut file_range = None;
        let mut segment_name = None;
        let mut segment_permissions = None;
        let address = witness.instruction_address;

        let Some(size) = witness.instruction_size else {
            blockers.push(format!("missing instruction size for 0x{address:x}"));
            return ExactReplayInstructionAttestation {
                instruction_address: address,
                instruction_size: witness.instruction_size,
                file_range,
                segment_name,
                segment_permissions,
                accepted: false,
                blockers,
            };
        };
        if size == 0 {
            blockers.push(format!("instruction size is zero for 0x{address:x}"));
            return ExactReplayInstructionAttestation {
                instruction_address: address,
                instruction_size: witness.instruction_size,
                file_range,
                segment_name,
                segment_permissions,
                accepted: false,
                blockers,
            };
        }
        if usize::from(size) != witness.instruction_bytes.len() {
            blockers.push(format!(
                "instruction byte length mismatch for 0x{address:x}: instruction_size={} but {} byte(s) were captured",
                size,
                witness.instruction_bytes.len()
            ));
            return ExactReplayInstructionAttestation {
                instruction_address: address,
                instruction_size: witness.instruction_size,
                file_range,
                segment_name,
                segment_permissions,
                accepted: false,
                blockers,
            };
        }

        let Some(instruction_end) = address.checked_add(u64::from(size)) else {
            blockers.push(format!("instruction range overflows address space for 0x{address:x}"));
            return ExactReplayInstructionAttestation {
                instruction_address: address,
                instruction_size: witness.instruction_size,
                file_range,
                segment_name,
                segment_permissions,
                accepted: false,
                blockers,
            };
        };

        let covering_segments = self.replay_segments_covering(address, instruction_end);
        if covering_segments.is_empty() {
            blockers.push(format!(
                "instruction range [0x{address:x}..0x{instruction_end:x}) is outside loaded image segments"
            ));
            return ExactReplayInstructionAttestation {
                instruction_address: address,
                instruction_size: witness.instruction_size,
                file_range,
                segment_name,
                segment_permissions,
                accepted: false,
                blockers,
            };
        }
        if covering_segments.len() > 1 {
            blockers.push(format!(
                "instruction range [0x{address:x}..0x{instruction_end:x}) has ambiguous overlapping loader segment evidence"
            ));
        }
        let segment = covering_segments
            .iter()
            .copied()
            .find(|segment| segment.permissions.execute)
            .unwrap_or(covering_segments[0]);
        segment_name = segment.name.clone();
        segment_permissions = Some(segment.permissions);

        if !segment.permissions.execute {
            blockers.push(format!(
                "loaded image segment for instruction 0x{address:x} is not executable"
            ));
        }

        let Some(segment_file_offset) = segment.file_offset else {
            blockers
                .push(format!("loader segment for instruction 0x{address:x} lacks file offset"));
            return ExactReplayInstructionAttestation {
                instruction_address: address,
                instruction_size: witness.instruction_size,
                file_range,
                segment_name,
                segment_permissions,
                accepted: false,
                blockers,
            };
        };
        let Some(segment_file_size) = segment.file_size else {
            blockers.push(format!("loader segment for instruction 0x{address:x} lacks file size"));
            return ExactReplayInstructionAttestation {
                instruction_address: address,
                instruction_size: witness.instruction_size,
                file_range,
                segment_name,
                segment_permissions,
                accepted: false,
                blockers,
            };
        };

        let offset_in_segment = address.saturating_sub(segment.virtual_range.start);
        let Some(end_in_segment) = offset_in_segment.checked_add(u64::from(size)) else {
            blockers
                .push(format!("instruction file range overflows address space for 0x{address:x}"));
            return ExactReplayInstructionAttestation {
                instruction_address: address,
                instruction_size: witness.instruction_size,
                file_range,
                segment_name,
                segment_permissions,
                accepted: false,
                blockers,
            };
        };
        if end_in_segment > segment_file_size {
            blockers.push(format!(
                "instruction range for 0x{address:x} exceeds file-backed segment bytes"
            ));
        }

        let Some(file_start) = segment_file_offset.checked_add(offset_in_segment) else {
            blockers
                .push(format!("instruction file range overflows address space for 0x{address:x}"));
            return ExactReplayInstructionAttestation {
                instruction_address: address,
                instruction_size: witness.instruction_size,
                file_range,
                segment_name,
                segment_permissions,
                accepted: false,
                blockers,
            };
        };
        let Some(file_end) = file_start.checked_add(u64::from(size)) else {
            blockers
                .push(format!("instruction file range overflows address space for 0x{address:x}"));
            return ExactReplayInstructionAttestation {
                instruction_address: address,
                instruction_size: witness.instruction_size,
                file_range,
                segment_name,
                segment_permissions,
                accepted: false,
                blockers,
            };
        };
        file_range = Some(BinaryAddressRange { start: file_start, end: file_end });

        match selected_image.end_offset() {
            Some(selected_end)
                if file_start >= selected_image.file_offset && file_end <= selected_end => {}
            Some(selected_end) => blockers.push(format!(
                "instruction byte range [0x{file_start:x}..0x{file_end:x}) is outside selected image [0x{:x}..0x{selected_end:x}) for 0x{address:x}",
                selected_image.file_offset
            )),
            None => blockers.push(format!(
                "selected image byte range overflows address space for instruction 0x{address:x}"
            )),
        }

        if let Some(actual) = selected_image_bytes_for_range(selected_image, file_start, file_end) {
            if actual != witness.instruction_bytes.as_slice() {
                blockers.push(format!(
                    "instruction bytes do not match selected image for 0x{address:x}"
                ));
            }
        } else {
            blockers.push(format!(
                "instruction byte range [0x{file_start:x}..0x{file_end:x}) cannot be read from selected image for 0x{address:x}"
            ));
        }

        ExactReplayInstructionAttestation {
            instruction_address: address,
            instruction_size: witness.instruction_size,
            file_range,
            segment_name,
            segment_permissions,
            accepted: blockers.is_empty(),
            blockers,
        }
    }

    fn replay_segments_covering(&self, address: u64, end: u64) -> Vec<&BinarySegment> {
        self.segments
            .iter()
            .filter(|segment| {
                address >= segment.virtual_range.start
                    && address < segment.virtual_range.end
                    && end <= segment.virtual_range.end
            })
            .collect()
    }
}

fn selected_image_bytes_for_range<'a>(
    selected_image: ExactReplaySelectedImage<'a>,
    file_start: u64,
    file_end: u64,
) -> Option<&'a [u8]> {
    if file_start < selected_image.file_offset || file_end < file_start {
        return None;
    }
    let selected_end = selected_image.end_offset()?;
    if file_end > selected_end {
        return None;
    }
    let start = usize::try_from(file_start - selected_image.file_offset).ok()?;
    let len = usize::try_from(file_end - file_start).ok()?;
    let end = start.checked_add(len)?;
    selected_image.bytes.get(start..end)
}

/// Lift a binary image directly into TrustIr functions.
///
/// Uses `trust_binary_parse::parse_binary` for format/architecture metadata
/// when the `elf` or `macho` feature is enabled. ELF and Mach-O dispatch
/// through the existing [`Lifter::from_elf`] and [`Lifter::from_macho`]
/// constructors. PE/COFF is detected and rejected with a clear unsupported
/// error until PE lifting is implemented.
///
/// # Errors
///
/// Returns [`LiftError`] if binary parser support is unavailable, parsing
/// fails, the format is unsupported, selection finds no function, or lifting a
/// selected function fails in strict proof mode.
#[cfg(not(any(feature = "macho", feature = "elf")))]
pub fn lift_binary_to_trust_ir(
    _bytes: &[u8],
    _options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    Err(LiftError::BinaryParserUnavailable)
}

/// Lift a binary image directly into TrustIr functions.
///
/// See the non-feature-gated item documentation for details.
#[cfg(any(feature = "macho", feature = "elf"))]
pub fn lift_binary_to_trust_ir(
    bytes: &[u8],
    options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    use trust_binary_parse::{BinaryFormat, detect_format, parse_binary};

    #[cfg(feature = "elf")]
    if is_elf32_i386(bytes) {
        return Err(elf32_i386_unsupported());
    }

    if matches!(detect_format(bytes), Some(BinaryFormat::Pe)) {
        return Err(pe_unsupported());
    }

    let info = parse_binary(bytes)?;
    match info.format {
        BinaryFormat::Elf => lift_elf(bytes, &info, options),
        BinaryFormat::MachO | BinaryFormat::FatMachO => lift_macho(bytes, &info, options),
        BinaryFormat::Pe => Err(pe_unsupported()),
        _ => Err(LiftError::UnsupportedBinaryFormat {
            format: "unknown",
            reason: "binary format is not implemented by trust-lift",
        }),
    }
}

#[cfg(feature = "elf")]
fn lift_elf(
    bytes: &[u8],
    info: &trust_binary_parse::BinaryInfo,
    options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    let endianness = elf_endianness(bytes);
    ensure_little_endian(info.format.name(), endianness)?;
    if is_elf32_i386(bytes) {
        return Err(elf32_i386_unsupported());
    }
    let elf = trust_binary_parse::Elf64::parse(bytes)?;
    let lifter = Lifter::from_elf(&elf)?;
    lift_with_lifter(bytes, &lifter, info, endianness, options)
}

#[cfg(all(not(feature = "elf"), feature = "macho"))]
fn lift_elf(
    _bytes: &[u8],
    info: &trust_binary_parse::BinaryInfo,
    _options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    Err(LiftError::UnsupportedBinaryFormat {
        format: info.format.name(),
        reason: "trust-lift was built without the `elf` feature",
    })
}

#[cfg(feature = "macho")]
fn lift_macho(
    bytes: &[u8],
    info: &trust_binary_parse::BinaryInfo,
    options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    let macho = trust_binary_parse::MachO::parse_prefer_aarch64(bytes)?;
    let endianness = macho_endianness(macho.data());
    ensure_little_endian(info.format.name(), endianness)?;
    let lifter = Lifter::from_macho(&macho)?;
    lift_with_lifter(macho.data(), &lifter, info, endianness, options)
}

#[cfg(all(not(feature = "macho"), feature = "elf"))]
fn lift_macho(
    _bytes: &[u8],
    info: &trust_binary_parse::BinaryInfo,
    _options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    Err(LiftError::UnsupportedBinaryFormat {
        format: info.format.name(),
        reason: "trust-lift was built without the `macho` feature",
    })
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn lift_with_lifter(
    bytes: &[u8],
    lifter: &Lifter,
    info: &trust_binary_parse::BinaryInfo,
    endianness: BinaryEndianness,
    options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    let targets = select_targets(lifter, info, &options.functions)?;
    let function_seeds = targets.iter().map(seed_from_target).collect();
    let source_provenance = source_provenance(info);
    let mut functions = Vec::new();
    let mut failures = Vec::new();

    for target in &targets {
        match lifter.lift_function(bytes, target.entry_point) {
            Ok(mut function) => {
                record_memory_uncertainty(&mut function, info.architecture.name());
                let preserve_empty_unsupported_ledger =
                    x86_64_selected_empty_unsupported_ledger_slice(
                        &function,
                        info.architecture.name(),
                    );
                if !preserve_empty_unsupported_ledger {
                    record_source_provenance_uncertainty(
                        &mut function,
                        info.architecture.name(),
                        &source_provenance,
                    );
                }
                record_binary_metadata_uncertainty(
                    &mut function,
                    info,
                    !preserve_empty_unsupported_ledger,
                );
                functions.push(function);
            }
            Err(error) if options.strict => return Err(error),
            Err(error) => failures.push(LiftedFunctionFailure {
                name: target.name.clone(),
                entry_point: target.entry_point,
                error: error.to_string(),
            }),
        }
    }

    Ok(LiftedBinary {
        format: info.format.name(),
        architecture: info.architecture.name(),
        endianness,
        entry_point: info.entry_point,
        build_id: info.build_id.clone(),
        segments: binary_segments(info),
        memory_model: binary_memory_model(info, endianness, &functions),
        function_seeds,
        source_provenance,
        source_mappings: source_mappings(info),
        functions,
        failures,
    })
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn select_targets(
    lifter: &Lifter,
    info: &trust_binary_parse::BinaryInfo,
    selection: &BinaryFunctionSelection,
) -> Result<Vec<FunctionTarget>, LiftError> {
    let mut targets = Vec::new();

    match selection {
        BinaryFunctionSelection::Entry => {
            let entry = info.entry_point.ok_or(LiftError::NoBinaryEntryPoint)?;
            let target = boundary_for_address(lifter.functions(), entry)
                .map(|boundary| {
                    target_from_boundary(boundary, LiftedFunctionSeedSource::EntryPoint)
                })
                .unwrap_or_else(|| FunctionTarget {
                    name: None,
                    entry_point: entry,
                    size: None,
                    source: LiftedFunctionSeedSource::EntryPoint,
                });
            push_unique(&mut targets, target);
        }
        BinaryFunctionSelection::All => {
            for boundary in lifter.functions() {
                push_unique(
                    &mut targets,
                    target_from_boundary(boundary, LiftedFunctionSeedSource::Symbol),
                );
            }
        }
        BinaryFunctionSelection::Addresses(addresses) => {
            for address in addresses {
                let target = boundary_for_address(lifter.functions(), *address)
                    .map(|boundary| {
                        target_from_boundary(boundary, LiftedFunctionSeedSource::RequestedAddress)
                    })
                    .unwrap_or_else(|| FunctionTarget {
                        name: None,
                        entry_point: *address,
                        size: None,
                        source: LiftedFunctionSeedSource::RequestedAddress,
                    });
                push_unique(&mut targets, target);
            }
        }
        BinaryFunctionSelection::Names(names) => {
            for name in names {
                let boundary = lifter
                    .functions()
                    .iter()
                    .find(|boundary| boundary.name == *name)
                    .ok_or_else(|| LiftError::NoFunctionNamed(name.clone()))?;
                push_unique(
                    &mut targets,
                    target_from_boundary(boundary, LiftedFunctionSeedSource::RequestedName),
                );
            }
        }
    }

    if targets.is_empty() {
        return Err(LiftError::NoFunctionsSelected);
    }

    Ok(targets)
}

#[cfg(any(feature = "macho", feature = "elf"))]
#[derive(Debug, Clone)]
struct FunctionTarget {
    name: Option<String>,
    entry_point: u64,
    size: Option<u64>,
    source: LiftedFunctionSeedSource,
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn target_from_boundary(
    boundary: &FunctionBoundary,
    source: LiftedFunctionSeedSource,
) -> FunctionTarget {
    FunctionTarget {
        name: Some(boundary.name.clone()),
        entry_point: boundary.start,
        size: Some(boundary.size),
        source,
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn seed_from_target(target: &FunctionTarget) -> LiftedFunctionSeed {
    LiftedFunctionSeed {
        name: target.name.clone(),
        entry_point: target.entry_point,
        size: target.size,
        source: target.source,
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn boundary_for_address(
    boundaries: &[FunctionBoundary],
    address: u64,
) -> Option<&FunctionBoundary> {
    boundaries.iter().find(|boundary| {
        let end = boundary.start.saturating_add(boundary.size);
        address >= boundary.start && address < end
    })
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn push_unique(targets: &mut Vec<FunctionTarget>, target: FunctionTarget) {
    if !targets.iter().any(|existing| existing.entry_point == target.entry_point) {
        targets.push(target);
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn binary_segments(info: &trust_binary_parse::BinaryInfo) -> Vec<BinarySegment> {
    info.segments()
        .iter()
        .map(|segment| BinarySegment {
            name: segment.name.clone(),
            virtual_range: BinaryAddressRange {
                start: segment.virtual_address,
                end: segment.virtual_end(),
            },
            file_offset: segment.file_offset,
            file_size: segment.file_size,
            permissions: segment.permissions,
        })
        .collect()
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn binary_memory_model(
    info: &trust_binary_parse::BinaryInfo,
    endianness: BinaryEndianness,
    functions: &[LiftedFunction],
) -> BinaryMemoryModel {
    let accesses: Vec<_> =
        functions.iter().flat_map(|function| function.memory_accesses.iter().cloned()).collect();
    let mut assumptions = loader_memory_assumptions(info, &accesses);

    if info.segments().is_empty() {
        assumptions.push(ModelAssumption {
            stage: "trust-lift::binary-memory".to_string(),
            description:
                "loader did not expose mapped segments; non-stack memory remains unclassified"
                    .to_string(),
        });
    }

    assumptions.extend(binary_metadata_assumptions(info));

    BinaryMemoryModel {
        pointer_width_bits: pointer_width_bits(info.architecture),
        endianness: trust_types_endianness(endianness),
        regions: info.segments().iter().map(memory_region_from_segment).collect(),
        accesses,
        assumptions,
        trust_level: TrustLevel::Partial,
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn binary_metadata_assumptions(info: &trust_binary_parse::BinaryInfo) -> Vec<ModelAssumption> {
    let mut assumptions = Vec::new();

    if info.abi().has_contradictions {
        for diagnostic in &info.abi().diagnostics {
            if diagnostic.contains("contradict") {
                assumptions.push(ModelAssumption {
                    stage: "trust-lift::abi-provenance".to_string(),
                    description: diagnostic.clone(),
                });
            }
        }
    }

    if info.type_provenance().status != trust_binary_parse::TypeProvenanceStatus::Recovered {
        assumptions.push(ModelAssumption {
            stage: "trust-lift::type-provenance".to_string(),
            description: format!(
                "debug type provenance is {}; recovered={}, uncertain={}; type facts remain advisory",
                info.type_provenance().status.name(),
                info.type_provenance().recovered_type_count,
                info.type_provenance().uncertain_type_count
            ),
        });
    }

    assumptions
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn pointer_width_bits(architecture: trust_binary_parse::Architecture) -> Option<u32> {
    match architecture {
        trust_binary_parse::Architecture::AArch64 | trust_binary_parse::Architecture::X86_64 => {
            Some(64)
        }
        trust_binary_parse::Architecture::Arm | trust_binary_parse::Architecture::X86 => Some(32),
        trust_binary_parse::Architecture::Unknown(_) => None,
        _ => None,
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn trust_types_endianness(endianness: BinaryEndianness) -> Endianness {
    match endianness {
        BinaryEndianness::Little => Endianness::Little,
        BinaryEndianness::Big => Endianness::Big,
        BinaryEndianness::Unknown => Endianness::Unknown,
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn memory_region_from_segment(segment: &trust_binary_parse::SegmentInfo) -> BinaryMemoryRegion {
    let kind = memory_region_kind(segment.name.as_deref());
    BinaryMemoryRegion {
        name: segment.name.clone(),
        kind,
        range: BinaryAddressRange { start: segment.virtual_address, end: segment.virtual_end() },
        permissions: segment.permissions,
        alignment_bytes: None,
        evidence: if kind == MemoryRegionKind::Unknown {
            BinaryFactEvidence::Unknown
        } else {
            BinaryFactEvidence::Heuristic { reason: "loader segment table".to_string() }
        },
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn memory_region_kind(name: Option<&str>) -> MemoryRegionKind {
    let Some(name) = name else {
        return MemoryRegionKind::Unknown;
    };
    let lower = name.to_ascii_lowercase();
    if lower.contains("tls") || lower.contains("thread") || lower == ".tdata" || lower == ".tbss" {
        MemoryRegionKind::Tls
    } else if lower.contains("mmio") || lower.contains("device") {
        MemoryRegionKind::Mmio
    } else if lower.starts_with("pt_load[") {
        MemoryRegionKind::Unknown
    } else {
        MemoryRegionKind::Global
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn loader_memory_assumptions(
    info: &trust_binary_parse::BinaryInfo,
    accesses: &[trust_types::MemoryAccessFact],
) -> Vec<ModelAssumption> {
    let mut assumptions = Vec::new();

    let unknown_regions = info
        .segments()
        .iter()
        .filter(|segment| memory_region_kind(segment.name.as_deref()) == MemoryRegionKind::Unknown)
        .count();
    if unknown_regions > 0 {
        assumptions.push(ModelAssumption {
            stage: "trust-lift::binary-memory".to_string(),
            description: format!(
                "{unknown_regions} loader segment(s) have ambiguous memory region class; accesses in those ranges are not promoted to global, TLS, MMIO, heap, or stack facts"
            ),
        });
    }

    let unknown_permissions = info
        .segments()
        .iter()
        .filter(|segment| {
            !segment.permissions.read && !segment.permissions.write && !segment.permissions.execute
        })
        .count();
    if unknown_permissions > 0 {
        assumptions.push(ModelAssumption {
            stage: "trust-lift::binary-memory".to_string(),
            description: format!(
                "{unknown_permissions} loader segment(s) have no recovered read/write/execute permission bits; permission-sensitive memory claims remain gated"
            ),
        });
    }

    let unknown_accesses =
        accesses.iter().filter(|access| access.region == MemoryRegionKind::Unknown).count();
    if unknown_accesses == 0 {
        return assumptions;
    }

    assumptions.push(ModelAssumption {
        stage: "trust-lift::binary-memory".to_string(),
        description: format!(
            "{unknown_accesses} memory access(es) could not be assigned to stack, loader global, TLS, MMIO, or heap regions"
        ),
    });
    assumptions
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn record_memory_uncertainty(function: &mut LiftedFunction, architecture: &str) {
    for access in
        function.memory_accesses.iter().filter(|access| access.region == MemoryRegionKind::Unknown)
    {
        function.unsupported.records.push(UnsupportedRecord {
            stage: "trust-lift::memory-provenance".to_string(),
            architecture: Some(architecture.to_string()),
            origin: Some(access.origin.clone()),
            opcode: None,
            operand: None,
            feature: "unclassified memory region".to_string(),
        });
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn x86_64_selected_empty_unsupported_ledger_slice(
    function: &LiftedFunction,
    architecture: &str,
) -> bool {
    if !matches!(architecture, "x86-64" | "x86_64") {
        return false;
    }
    if !function.unsupported.records.is_empty() || !function.memory_accesses.is_empty() {
        return false;
    }

    let mut saw_instruction = false;
    for insn in function.cfg.blocks.iter().flat_map(|block| block.instructions.iter()) {
        saw_instruction = true;
        if !matches!(insn.opcode, trust_disasm::Opcode::Nop | trust_disasm::Opcode::Endbr64) {
            return false;
        }
    }

    saw_instruction
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn record_source_provenance_uncertainty(
    function: &mut LiftedFunction,
    architecture: &str,
    provenance: &LiftedSourceProvenance,
) {
    if provenance.status == LiftedSourceProvenanceStatus::Exact {
        return;
    }

    function.unsupported.records.push(UnsupportedRecord {
        stage: "trust-lift::source-provenance".to_string(),
        architecture: Some(architecture.to_string()),
        origin: Some(BinaryOrigin {
            binary_path: None,
            function_entry: Some(function.entry_point),
            instruction_address: function.entry_point,
            instruction_size: None,
            encoding: None,
            instruction_bytes: vec![],
            source: None,
        }),
        opcode: None,
        operand: None,
        feature: format!("non-exact source provenance: {}", provenance.status.name()),
    });
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn record_binary_metadata_uncertainty(
    function: &mut LiftedFunction,
    info: &trust_binary_parse::BinaryInfo,
    record_type_provenance: bool,
) {
    if info.abi().has_contradictions {
        function.unsupported.records.push(UnsupportedRecord {
            stage: "trust-lift::abi-provenance".to_string(),
            architecture: Some(info.architecture.name().to_string()),
            origin: Some(BinaryOrigin {
                binary_path: None,
                function_entry: Some(function.entry_point),
                instruction_address: function.entry_point,
                instruction_size: None,
                encoding: None,
                instruction_bytes: vec![],
                source: None,
            }),
            opcode: None,
            operand: None,
            feature: "contradictory ABI metadata".to_string(),
        });
    }

    if record_type_provenance
        && info.type_provenance().status != trust_binary_parse::TypeProvenanceStatus::Recovered
    {
        function.unsupported.records.push(UnsupportedRecord {
            stage: "trust-lift::type-provenance".to_string(),
            architecture: Some(info.architecture.name().to_string()),
            origin: Some(BinaryOrigin {
                binary_path: None,
                function_entry: Some(function.entry_point),
                instruction_address: function.entry_point,
                instruction_size: None,
                encoding: None,
                instruction_bytes: vec![],
                source: None,
            }),
            opcode: None,
            operand: None,
            feature: format!(
                "non-recovered debug type provenance: {}",
                info.type_provenance().status.name()
            ),
        });
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn source_provenance(info: &trust_binary_parse::BinaryInfo) -> LiftedSourceProvenance {
    let status = match info.debug_source().status {
        trust_binary_parse::DebugSourceProvenanceStatus::Unavailable => {
            LiftedSourceProvenanceStatus::Unavailable
        }
        trust_binary_parse::DebugSourceProvenanceStatus::Exact => {
            LiftedSourceProvenanceStatus::Exact
        }
        trust_binary_parse::DebugSourceProvenanceStatus::Ambiguous => {
            LiftedSourceProvenanceStatus::Ambiguous
        }
        trust_binary_parse::DebugSourceProvenanceStatus::Unsupported => {
            LiftedSourceProvenanceStatus::Unsupported
        }
    };

    LiftedSourceProvenance {
        status,
        exact_mapping_count: info.debug_source().exact_mapping_count,
        ambiguous_mapping_count: info.debug_source().ambiguous_mapping_count,
        diagnostics: info.debug_source().diagnostics.clone(),
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn source_mappings(info: &trust_binary_parse::BinaryInfo) -> Vec<LiftedSourceMapping> {
    info.source_mappings()
        .iter()
        .filter_map(|mapping| {
            let line = u32::try_from(mapping.line).ok()?;
            let column = u32::try_from(mapping.column).ok()?;
            Some(LiftedSourceMapping {
                binary_address: mapping.binary_address,
                source: SourceSpan {
                    file: mapping.file.clone(),
                    line_start: line,
                    col_start: column,
                    line_end: line,
                    col_end: column,
                },
            })
        })
        .collect()
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn pe_unsupported() -> LiftError {
    LiftError::UnsupportedBinaryFormat {
        format: "PE/COFF",
        reason: "PE lifting is not implemented yet",
    }
}

#[cfg(feature = "elf")]
fn elf32_i386_unsupported() -> LiftError {
    LiftError::UnsupportedBinaryFormat {
        format: "ELF",
        reason: "32-bit x86/i386 lifting is not implemented yet",
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn ensure_little_endian(
    format: &'static str,
    endianness: BinaryEndianness,
) -> Result<(), LiftError> {
    if endianness == BinaryEndianness::Little {
        return Ok(());
    }

    Err(LiftError::UnsupportedBinaryFormat {
        format,
        reason: "only little-endian AArch64 and x86-64 binaries are supported",
    })
}

#[cfg(feature = "elf")]
fn elf_endianness(bytes: &[u8]) -> BinaryEndianness {
    match bytes.get(5).copied() {
        Some(1) => BinaryEndianness::Little,
        Some(2) => BinaryEndianness::Big,
        _ => BinaryEndianness::Unknown,
    }
}

#[cfg(feature = "elf")]
fn is_elf32_i386(bytes: &[u8]) -> bool {
    const ELF_MAGIC: &[u8; 4] = b"\x7fELF";
    const ELFCLASS32: u8 = 1;
    const ELFDATA2LSB: u8 = 1;
    const ELFDATA2MSB: u8 = 2;
    const EM_386: u16 = 3;

    if bytes.get(..4) != Some(ELF_MAGIC) || bytes.get(4).copied() != Some(ELFCLASS32) {
        return false;
    }

    let Some(machine_bytes) = bytes.get(18..20) else {
        return false;
    };
    match bytes.get(5).copied() {
        Some(ELFDATA2LSB) => u16::from_le_bytes([machine_bytes[0], machine_bytes[1]]) == EM_386,
        Some(ELFDATA2MSB) => u16::from_be_bytes([machine_bytes[0], machine_bytes[1]]) == EM_386,
        _ => false,
    }
}

#[cfg(feature = "macho")]
fn macho_endianness(bytes: &[u8]) -> BinaryEndianness {
    match bytes.get(..4) {
        Some([0xcf, 0xfa, 0xed, 0xfe]) => BinaryEndianness::Little,
        Some([0xfe, 0xed, 0xfa, 0xcf]) => BinaryEndianness::Big,
        _ => BinaryEndianness::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_options_are_entry_strict() {
        let options = BinaryLiftOptions::default();
        assert_eq!(options.functions, BinaryFunctionSelection::Entry);
        assert!(options.strict);
    }

    #[test]
    fn options_builders_set_selection() {
        assert_eq!(BinaryLiftOptions::all_functions().functions, BinaryFunctionSelection::All);
        assert_eq!(
            BinaryLiftOptions::functions_by_address([0x1000]).functions,
            BinaryFunctionSelection::Addresses(vec![0x1000])
        );
        assert_eq!(
            BinaryLiftOptions::functions_by_name(["main"]).functions,
            BinaryFunctionSelection::Names(vec!["main".to_string()])
        );
        assert!(!BinaryLiftOptions::all_functions().best_effort().strict);
    }

    #[test]
    fn endianness_names_are_reportable() {
        assert_eq!(BinaryEndianness::Little.name(), "little");
        assert_eq!(BinaryEndianness::Big.name(), "big");
        assert_eq!(BinaryEndianness::Unknown.name(), "unknown");
    }

    #[test]
    fn lifted_source_provenance_status_names_are_stable() {
        assert_eq!(LiftedSourceProvenanceStatus::Unavailable.name(), "unavailable");
        assert_eq!(LiftedSourceProvenanceStatus::Exact.name(), "exact");
        assert_eq!(LiftedSourceProvenanceStatus::Ambiguous.name(), "ambiguous");
        assert_eq!(LiftedSourceProvenanceStatus::Unsupported.name(), "unsupported");
        assert_eq!(format!("{:?}", LiftedSourceProvenanceStatus::Ambiguous), "Ambiguous");
    }

    #[test]
    fn lifted_source_mapping_debug_format_is_stable() {
        let mapping = LiftedSourceMapping {
            binary_address: 0x401000,
            source: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 27,
                col_start: 5,
                line_end: 27,
                col_end: 5,
            },
        };

        assert_eq!(
            format!("{mapping:?}"),
            "LiftedSourceMapping { binary_address: 4198400, source: SourceSpan { file: \"src/lib.rs\", line_start: 27, col_start: 5, line_end: 27, col_end: 5 } }"
        );
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn endianness_converts_to_shared_memory_model_type() {
        assert_eq!(trust_types_endianness(BinaryEndianness::Little), Endianness::Little);
        assert_eq!(trust_types_endianness(BinaryEndianness::Big), Endianness::Big);
        assert_eq!(trust_types_endianness(BinaryEndianness::Unknown), Endianness::Unknown);
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn loader_region_names_classify_tls_mmio_and_globals() {
        assert_eq!(memory_region_kind(Some(".tdata")), MemoryRegionKind::Tls);
        assert_eq!(memory_region_kind(Some("__thread_vars")), MemoryRegionKind::Tls);
        assert_eq!(memory_region_kind(Some("device_mmio")), MemoryRegionKind::Mmio);
        assert_eq!(memory_region_kind(Some("__TEXT")), MemoryRegionKind::Global);
        assert_eq!(memory_region_kind(Some("PT_LOAD[0]")), MemoryRegionKind::Unknown);
        assert_eq!(memory_region_kind(None), MemoryRegionKind::Unknown);
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn loader_memory_model_carries_regions_and_uncertainty() {
        use trust_types::{
            BinaryOrigin, BinarySegmentPermissions, Formula, MemoryAccessFact, MemoryAccessKind,
            SourceSpan,
        };

        let info = trust_binary_parse::BinaryInfo {
            format: trust_binary_parse::BinaryFormat::Elf,
            architecture: trust_binary_parse::Architecture::X86_64,
            sections: vec![],
            segments: vec![trust_binary_parse::SegmentInfo {
                name: Some(".tdata".to_string()),
                virtual_address: 0x6000,
                virtual_size: 0x100,
                file_offset: Some(0x200),
                file_size: Some(0x80),
                permissions: BinarySegmentPermissions { read: true, write: true, execute: false },
            }],
            symbols: vec![],
            entry_point: Some(0x4000),
            build_id: Some("elf-gnu-build-id:abcd".to_string()),
            abi: trust_binary_parse::AbiProvenance {
                calling_convention: Some("SysV64".to_string()),
                object_pointer_width_bits: Some(64),
                architecture_pointer_width_bits: Some(64),
                has_contradictions: false,
                diagnostics: vec!["test ABI metadata".to_string()],
            },
            type_provenance: trust_binary_parse::TypeProvenance {
                status: trust_binary_parse::TypeProvenanceStatus::Recovered,
                recovered_type_count: 1,
                uncertain_type_count: 0,
                diagnostics: vec!["test type metadata".to_string()],
            },
            debug_source: trust_binary_parse::DebugSourceProvenance {
                status: trust_binary_parse::DebugSourceProvenanceStatus::Exact,
                exact_mapping_count: 1,
                ambiguous_mapping_count: 0,
                diagnostics: vec!["exact test mapping".to_string()],
            },
            source_mappings: vec![trust_binary_parse::SourceMappingInfo {
                binary_address: 0x4000,
                file: "src/main.rs".to_string(),
                line: 12,
                column: 3,
            }],
            metadata_diagnostics: vec![],
        };
        let unknown_access = MemoryAccessFact {
            origin: BinaryOrigin {
                binary_path: None,
                function_entry: Some(0x4000),
                instruction_address: 0x4010,
                instruction_size: Some(4),
                encoding: None,
                instruction_bytes: vec![],
                source: Some(SourceSpan::binary_address(0x4010)),
            },
            kind: MemoryAccessKind::Read,
            address: Formula::BitVec { value: 0, width: 64 },
            width_bytes: 8,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Unknown,
            base_object: None,
            offset: None,
            extent: None,
            provenance: None,
            taint: vec![],
        };

        let assumptions = loader_memory_assumptions(&info, &[unknown_access]);
        assert_eq!(assumptions.len(), 1);
        assert!(assumptions[0].description.contains("could not be assigned"));

        let model = binary_memory_model(&info, BinaryEndianness::Little, &[]);
        assert_eq!(model.pointer_width_bits, Some(64));
        assert_eq!(model.endianness, Endianness::Little);
        assert_eq!(model.regions.len(), 1);
        assert_eq!(model.regions[0].kind, MemoryRegionKind::Tls);
        assert_eq!(model.regions[0].range.start, 0x6000);
        assert_eq!(model.regions[0].range.end, 0x6100);

        let provenance = source_provenance(&info);
        assert_eq!(provenance.status, LiftedSourceProvenanceStatus::Exact);
        let mappings = source_mappings(&info);
        assert_eq!(mappings.len(), 1);
        assert_eq!(mappings[0].binary_address, 0x4000);
        assert_eq!(mappings[0].source.file, "src/main.rs");
        assert_eq!(mappings[0].source.line_start, 12);
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn ambiguous_loader_regions_and_permissions_are_gated() {
        use trust_types::BinarySegmentPermissions;

        let info = trust_binary_parse::BinaryInfo {
            format: trust_binary_parse::BinaryFormat::Elf,
            architecture: trust_binary_parse::Architecture::X86_64,
            sections: vec![],
            segments: vec![trust_binary_parse::SegmentInfo {
                name: Some("PT_LOAD[0]".to_string()),
                virtual_address: 0x4000,
                virtual_size: 0x100,
                file_offset: Some(0),
                file_size: Some(0x100),
                permissions: BinarySegmentPermissions::default(),
            }],
            symbols: vec![],
            entry_point: Some(0x4000),
            build_id: None,
            abi: trust_binary_parse::AbiProvenance::default(),
            type_provenance: trust_binary_parse::TypeProvenance::default(),
            debug_source: trust_binary_parse::DebugSourceProvenance::default(),
            source_mappings: vec![],
            metadata_diagnostics: vec![],
        };

        let assumptions = loader_memory_assumptions(&info, &[]);
        assert_eq!(assumptions.len(), 2);
        assert!(assumptions[0].description.contains("ambiguous memory region class"));
        assert!(assumptions[1].description.contains("no recovered read/write/execute"));

        let region = memory_region_from_segment(&info.segments[0]);
        assert_eq!(region.kind, MemoryRegionKind::Unknown);
        assert_eq!(region.evidence, BinaryFactEvidence::Unknown);

        let metadata = binary_metadata_assumptions(&info);
        assert_eq!(metadata.len(), 1);
        assert_eq!(metadata[0].stage, "trust-lift::type-provenance");
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn selected_unsupported_boundary_cannot_look_like_empty_ledger_slice() {
        use trust_types::{
            BinarySegmentPermissions, UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY,
        };

        let text_base = 0x1000;
        let dmb_encoding = 0xD5033B9Fu32; // DMB ISH
        let ret_encoding = 0xD65F03C0u32;
        let nop_encoding = 0xD503201Fu32;

        let mut text_section = Vec::new();
        text_section.extend_from_slice(&dmb_encoding.to_le_bytes());
        text_section.extend_from_slice(&ret_encoding.to_le_bytes());
        text_section.resize(0x10, 0);
        text_section.extend_from_slice(&nop_encoding.to_le_bytes());
        text_section.extend_from_slice(&ret_encoding.to_le_bytes());

        let unsupported_name = "aarch64_dmb_boundary";
        let empty_name = "aarch64_empty_slice";
        let lifter = Lifter::new(
            vec![
                FunctionBoundary { name: unsupported_name.to_string(), start: text_base, size: 8 },
                FunctionBoundary { name: empty_name.to_string(), start: text_base + 0x10, size: 8 },
            ],
            text_base,
            text_section.len() as u64,
            0,
        );
        let info = trust_binary_parse::BinaryInfo {
            format: trust_binary_parse::BinaryFormat::Elf,
            architecture: trust_binary_parse::Architecture::AArch64,
            sections: vec![],
            segments: vec![trust_binary_parse::SegmentInfo {
                name: Some(".text".to_string()),
                virtual_address: text_base,
                virtual_size: text_section.len() as u64,
                file_offset: Some(0),
                file_size: Some(text_section.len() as u64),
                permissions: BinarySegmentPermissions { read: true, write: false, execute: true },
            }],
            symbols: vec![],
            entry_point: Some(text_base),
            build_id: Some("slot-bv-unsupported-boundary-selection".to_string()),
            abi: trust_binary_parse::AbiProvenance {
                calling_convention: Some("AAPCS64".to_string()),
                object_pointer_width_bits: Some(64),
                architecture_pointer_width_bits: Some(64),
                has_contradictions: false,
                diagnostics: vec![],
            },
            type_provenance: trust_binary_parse::TypeProvenance {
                status: trust_binary_parse::TypeProvenanceStatus::Recovered,
                recovered_type_count: 1,
                uncertain_type_count: 0,
                diagnostics: vec![],
            },
            debug_source: trust_binary_parse::DebugSourceProvenance {
                status: trust_binary_parse::DebugSourceProvenanceStatus::Exact,
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec![],
            },
            source_mappings: vec![],
            metadata_diagnostics: vec![],
        };

        let unsupported_slice = lift_with_lifter(
            &text_section,
            &lifter,
            &info,
            BinaryEndianness::Little,
            BinaryLiftOptions::functions_by_name([unsupported_name]),
        )
        .expect("unsupported boundary should lift as an explicit partial slice");
        assert!(unsupported_slice.failures.is_empty());
        assert_eq!(unsupported_slice.function_seeds.len(), 1);
        assert_eq!(unsupported_slice.function_seeds[0].name.as_deref(), Some(unsupported_name));
        assert_eq!(unsupported_slice.functions.len(), 1);
        let unsupported_function = &unsupported_slice.functions[0];
        assert_eq!(unsupported_function.name, unsupported_name);
        assert!(
            !unsupported_function.unsupported.is_empty(),
            "the selected DMB boundary must remain visible in the unsupported ledger"
        );
        assert_eq!(unsupported_function.unsupported.records.len(), 1);
        assert_eq!(
            unsupported_function
                .unsupported
                .family_count(UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY),
            1
        );
        let record = &unsupported_function.unsupported.records[0];
        assert_eq!(record.stage, "trust-lift::semantic-lift");
        assert_eq!(record.opcode.as_deref(), Some("Dmb"));
        assert!(record.feature.contains("unsupported-ledger boundary"));
        assert!(record.feature.contains("not proof-grade"));
        let origin = record.origin.as_ref().expect("boundary ledger origin");
        assert_eq!(origin.function_entry, Some(text_base));
        assert_eq!(origin.instruction_address, text_base);
        assert_eq!(origin.instruction_size, Some(4));
        assert_eq!(origin.encoding, Some(dmb_encoding));
        assert_eq!(origin.instruction_bytes, dmb_encoding.to_le_bytes().to_vec());

        let empty_slice = lift_with_lifter(
            &text_section,
            &lifter,
            &info,
            BinaryEndianness::Little,
            BinaryLiftOptions::functions_by_name([empty_name]),
        )
        .expect("nearby supported slice should still lift independently");
        assert!(empty_slice.failures.is_empty());
        assert_eq!(empty_slice.function_seeds.len(), 1);
        assert_eq!(empty_slice.function_seeds[0].name.as_deref(), Some(empty_name));
        assert_eq!(empty_slice.functions.len(), 1);
        assert_eq!(empty_slice.functions[0].name, empty_name);
        assert!(
            empty_slice.functions[0].unsupported.is_empty(),
            "the supported selected slice is the only empty-ledger case in this fixture"
        );
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn non_exact_source_provenance_records_unsupported_feature() {
        let provenance = LiftedSourceProvenance {
            status: LiftedSourceProvenanceStatus::Ambiguous,
            exact_mapping_count: 0,
            ambiguous_mapping_count: 1,
            diagnostics: vec!["ambiguous test mapping".to_string()],
        };
        let mut function = minimal_lifted_function();

        record_source_provenance_uncertainty(&mut function, "x86-64", &provenance);

        assert_eq!(function.unsupported.records.len(), 1);
        let record = &function.unsupported.records[0];
        assert_eq!(record.stage, "trust-lift::source-provenance");
        assert_eq!(record.architecture.as_deref(), Some("x86-64"));
        assert_eq!(record.feature, "non-exact source provenance: ambiguous");
        assert_eq!(record.origin.as_ref().and_then(|origin| origin.function_entry), Some(0x1000));
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn memory_uncertainty_unsupported_record_preserves_instruction_bytes() {
        use trust_types::{Formula, MemoryAccessFact, MemoryAccessKind};

        let mut function = minimal_lifted_function();
        function.memory_accesses.push(MemoryAccessFact {
            origin: BinaryOrigin {
                binary_path: None,
                function_entry: Some(0x1000),
                instruction_address: 0x1008,
                instruction_size: Some(7),
                encoding: Some(0),
                instruction_bytes: vec![0x48, 0x8b, 0x84, 0x24, 0x80, 0x00, 0x00],
                source: None,
            },
            kind: MemoryAccessKind::Read,
            address: Formula::Var("unknown_addr".to_string(), trust_types::Sort::BitVec(64)),
            width_bytes: 8,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Unknown,
            base_object: None,
            offset: None,
            extent: None,
            provenance: None,
            taint: vec![],
        });

        record_memory_uncertainty(&mut function, "x86-64");

        let record = &function.unsupported.records[0];
        assert_eq!(record.stage, "trust-lift::memory-provenance");
        assert_eq!(record.feature, "unclassified memory region");
        assert_eq!(
            record.origin.as_ref().map(|origin| origin.instruction_bytes.clone()),
            Some(vec![0x48, 0x8b, 0x84, 0x24, 0x80, 0x00, 0x00])
        );
        assert_eq!(record.origin.as_ref().and_then(|origin| origin.instruction_size), Some(7));
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn parser_metadata_uncertainty_records_abi_and_type_gates() {
        let info = trust_binary_parse::BinaryInfo {
            format: trust_binary_parse::BinaryFormat::Elf,
            architecture: trust_binary_parse::Architecture::X86,
            sections: vec![],
            segments: vec![],
            symbols: vec![],
            entry_point: Some(0x1000),
            build_id: None,
            abi: trust_binary_parse::AbiProvenance {
                calling_convention: None,
                object_pointer_width_bits: Some(64),
                architecture_pointer_width_bits: Some(32),
                has_contradictions: true,
                diagnostics: vec![
                    "ELF object pointer width (64) contradicts x86 architecture pointer width (32)"
                        .to_string(),
                ],
            },
            type_provenance: trust_binary_parse::TypeProvenance {
                status: trust_binary_parse::TypeProvenanceStatus::Partial,
                recovered_type_count: 2,
                uncertain_type_count: 1,
                diagnostics: vec!["test partial type facts".to_string()],
            },
            debug_source: trust_binary_parse::DebugSourceProvenance::default(),
            source_mappings: vec![],
            metadata_diagnostics: vec![],
        };
        let mut function = minimal_lifted_function();

        record_binary_metadata_uncertainty(&mut function, &info, true);

        assert_eq!(function.unsupported.records.len(), 2);
        assert_eq!(function.unsupported.records[0].stage, "trust-lift::abi-provenance");
        assert_eq!(function.unsupported.records[0].feature, "contradictory ABI metadata");
        assert_eq!(function.unsupported.records[1].stage, "trust-lift::type-provenance");
        assert_eq!(
            function.unsupported.records[1].feature,
            "non-recovered debug type provenance: partial"
        );

        let assumptions = binary_metadata_assumptions(&info);
        assert_eq!(assumptions.len(), 2);
        assert!(assumptions[0].description.contains("contradicts"));
        assert!(assumptions[1].description.contains("recovered=2, uncertain=1"));
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn x86_64_empty_slice_keeps_nonsemantic_provenance_gates_out_of_unsupported_ledger() {
        let lifter = Lifter::new_with_arch(
            vec![FunctionBoundary {
                name: "trust_fixture_x86_empty_ledger".to_string(),
                start: 0x400000,
                size: 1,
            }],
            0x400000,
            1,
            0,
            crate::lifter::LiftArch::X86_64,
        );
        let info = trust_binary_parse::BinaryInfo {
            format: trust_binary_parse::BinaryFormat::Elf,
            architecture: trust_binary_parse::Architecture::X86_64,
            sections: vec![],
            segments: vec![],
            symbols: vec![],
            entry_point: Some(0x400000),
            build_id: Some("elf-gnu-build-id:000102030405060708090a0b0c0d0e0f10111213".to_string()),
            abi: trust_binary_parse::AbiProvenance {
                calling_convention: Some("SysV64".to_string()),
                object_pointer_width_bits: Some(64),
                architecture_pointer_width_bits: Some(64),
                has_contradictions: false,
                diagnostics: vec![],
            },
            type_provenance: trust_binary_parse::TypeProvenance::default(),
            debug_source: trust_binary_parse::DebugSourceProvenance::default(),
            source_mappings: vec![],
            metadata_diagnostics: vec![],
        };

        let lifted = lift_with_lifter(
            &[0x90],
            &lifter,
            &info,
            BinaryEndianness::Little,
            BinaryLiftOptions::functions_by_address([0x400000]),
        )
        .expect("selected x86-64 no-data slice should lift without unsupported records");

        assert_eq!(lifted.functions.len(), 1);
        assert_eq!(lifted.source_provenance.status, LiftedSourceProvenanceStatus::Unavailable);
        assert!(
            lifted.functions[0].unsupported.records.is_empty(),
            "source/type proof gates stay outside this semantic unsupported ledger"
        );
        assert!(x86_64_selected_empty_unsupported_ledger_slice(
            &lifted.functions[0],
            lifted.architecture,
        ));
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn x86_64_dataflow_slice_still_records_type_provenance_gate() {
        let mut function = minimal_lifted_function();
        let decoder = trust_disasm::x86_64::X86_64Decoder::new();
        function.cfg.blocks[0].instructions.push(
            trust_disasm::arch::Decoder::decode(&decoder, &[0x48, 0x89, 0xE5], 0x1000)
                .expect("decode MOV RBP, RSP"),
        );

        let info = trust_binary_parse::BinaryInfo {
            format: trust_binary_parse::BinaryFormat::Elf,
            architecture: trust_binary_parse::Architecture::X86_64,
            sections: vec![],
            segments: vec![],
            symbols: vec![],
            entry_point: Some(0x1000),
            build_id: None,
            abi: trust_binary_parse::AbiProvenance {
                calling_convention: Some("SysV64".to_string()),
                object_pointer_width_bits: Some(64),
                architecture_pointer_width_bits: Some(64),
                has_contradictions: false,
                diagnostics: vec![],
            },
            type_provenance: trust_binary_parse::TypeProvenance::default(),
            debug_source: trust_binary_parse::DebugSourceProvenance::default(),
            source_mappings: vec![],
            metadata_diagnostics: vec![],
        };

        assert!(!x86_64_selected_empty_unsupported_ledger_slice(&function, "x86-64"));
        record_binary_metadata_uncertainty(&mut function, &info, true);

        assert!(function.unsupported.records.iter().any(|record| {
            record.stage == "trust-lift::type-provenance"
                && record.feature == "non-recovered debug type provenance: unavailable"
        }));
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn x86_64_empty_ledger_boundary_excludes_ret_dataflow_and_unsupported_semantics() {
        let decoder = trust_disasm::x86_64::X86_64Decoder::new();

        let mut ret = minimal_lifted_function();
        ret.cfg.blocks[0].instructions.push(
            trust_disasm::arch::Decoder::decode(&decoder, &[0xC3], 0x1000)
                .expect("decode x86-64 RET"),
        );
        assert!(
            !x86_64_selected_empty_unsupported_ledger_slice(&ret, "x86-64"),
            "RET is supported control-flow coverage, not the empty-ledger NOP boundary"
        );

        let mut dataflow = minimal_lifted_function();
        dataflow.cfg.blocks[0].instructions.push(
            trust_disasm::arch::Decoder::decode(&decoder, &[0x48, 0x89, 0xE5], 0x1000)
                .expect("decode MOV RBP, RSP"),
        );
        assert!(
            !x86_64_selected_empty_unsupported_ledger_slice(&dataflow, "x86-64"),
            "dataflow instructions must not be silently promoted into the empty-ledger boundary"
        );

        let mut unsupported = minimal_lifted_function();
        unsupported.cfg.blocks[0].instructions.push(
            trust_disasm::arch::Decoder::decode(&decoder, &[0x90], 0x1000)
                .expect("decode x86-64 NOP"),
        );
        unsupported.unsupported.records.push(UnsupportedRecord {
            stage: "trust-lift::semantic-lift".to_string(),
            architecture: Some("x86-64".to_string()),
            origin: Some(BinaryOrigin {
                binary_path: None,
                function_entry: Some(0x1000),
                instruction_address: 0x1000,
                instruction_size: Some(1),
                encoding: Some(0x90),
                instruction_bytes: vec![0x90],
                source: Some(SourceSpan::binary_address(0x1000)),
            }),
            opcode: Some("NOP".to_string()),
            operand: None,
            feature: "unsupported instruction semantics fixture".to_string(),
        });
        assert!(
            !x86_64_selected_empty_unsupported_ledger_slice(&unsupported, "x86-64"),
            "pre-existing unsupported semantics must keep the support boundary closed"
        );
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    fn minimal_lifted_function() -> LiftedFunction {
        use crate::cfg::{Cfg, LiftedBlock};
        use trust_types::{BlockId, Terminator, TrustLevel, Ty, UnsupportedLedger, VerifiableBody};

        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        LiftedFunction {
            name: "test_fn".to_string(),
            entry_point: 0x1000,
            cfg,
            trust_ir_body: VerifiableBody {
                locals: vec![],
                blocks: vec![trust_types::BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            ssa: None,
            annotations: vec![],
            memory_accesses: vec![],
            trust_level: TrustLevel::Partial,
            unsupported: UnsupportedLedger::default(),
        }
    }

    #[cfg(feature = "elf")]
    #[test]
    fn elf_endianness_reads_ident_encoding() {
        let mut bytes = [0u8; 16];
        bytes[5] = 1;
        assert_eq!(elf_endianness(&bytes), BinaryEndianness::Little);
        bytes[5] = 2;
        assert_eq!(elf_endianness(&bytes), BinaryEndianness::Big);
        bytes[5] = 0;
        assert_eq!(elf_endianness(&bytes), BinaryEndianness::Unknown);
    }

    #[cfg(feature = "macho")]
    #[test]
    fn macho_endianness_reads_slice_magic() {
        assert_eq!(macho_endianness(&[0xcf, 0xfa, 0xed, 0xfe]), BinaryEndianness::Little);
        assert_eq!(macho_endianness(&[0xfe, 0xed, 0xfa, 0xcf]), BinaryEndianness::Big);
        assert_eq!(macho_endianness(&[0, 0, 0, 0]), BinaryEndianness::Unknown);
    }

    #[cfg(feature = "elf")]
    #[test]
    fn big_endian_elf_is_rejected_before_lifting() {
        let error = lift_binary_to_trust_ir(&minimal_big_endian_elf(), BinaryLiftOptions::default())
            .unwrap_err();
        assert!(matches!(
            error,
            LiftError::UnsupportedBinaryFormat {
                format: "ELF",
                reason: "only little-endian AArch64 and x86-64 binaries are supported"
            }
        ));
    }

    #[cfg(feature = "elf")]
    #[test]
    fn elf32_i386_is_rejected_before_elf64_parse() {
        let error =
            lift_binary_to_trust_ir(&minimal_elf32_i386(), BinaryLiftOptions::default()).unwrap_err();
        assert!(matches!(
            error,
            LiftError::UnsupportedBinaryFormat {
                format: "ELF",
                reason: "32-bit x86/i386 lifting is not implemented yet"
            }
        ));
    }

    #[cfg(feature = "elf")]
    #[test]
    fn elf32_arm_is_not_classified_as_i386() {
        let mut bytes = minimal_elf32_i386();
        bytes[18..20].copy_from_slice(&40u16.to_le_bytes()); // EM_ARM
        assert!(!is_elf32_i386(&bytes));
    }

    #[cfg(not(any(feature = "macho", feature = "elf")))]
    #[test]
    fn no_parser_feature_returns_clear_error() {
        let error = lift_binary_to_trust_ir(&[], BinaryLiftOptions::default()).unwrap_err();
        assert!(matches!(error, LiftError::BinaryParserUnavailable));
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn pe_returns_clear_unsupported_error() {
        let error =
            lift_binary_to_trust_ir(&[b'M', b'Z', 0, 0], BinaryLiftOptions::default()).unwrap_err();
        assert!(matches!(
            error,
            LiftError::UnsupportedBinaryFormat {
                format: "PE/COFF",
                reason: "PE lifting is not implemented yet"
            }
        ));
    }

    #[test]
    fn exact_replay_attests_executable_segment_and_selected_image_bytes() {
        let mut image = vec![0xcc; 0x40];
        image[0x14..0x16].copy_from_slice(&[0x90, 0xc3]);
        let binary = replay_test_binary_with_segment(replay_text_segment(true));
        let witness = ExactReplayInstructionWitness::new(0x401004, 2, vec![0x90, 0xc3]);

        let attestation =
            binary.attest_exact_replay_slice(ExactReplaySelectedImage::thin(&image), &[witness]);

        assert!(attestation.accepted, "{attestation:?}");
        assert_eq!(attestation.instruction_count, 1);
        assert_eq!(attestation.accepted_instruction_count, 1);
        assert!(attestation.blockers.is_empty());
        let instruction = &attestation.instructions[0];
        assert!(instruction.accepted);
        assert_eq!(instruction.segment_name.as_deref(), Some(".text"));
        assert_eq!(instruction.file_range, Some(BinaryAddressRange { start: 0x14, end: 0x16 }));
        assert_eq!(
            instruction.segment_permissions,
            Some(BinarySegmentPermissions { read: true, write: false, execute: true })
        );
    }

    #[test]
    fn exact_replay_rejects_non_executable_segment_permission() {
        let mut image = vec![0xcc; 0x40];
        image[0x10] = 0x90;
        let binary = replay_test_binary_with_segment(replay_text_segment(false));
        let witness = ExactReplayInstructionWitness::new(0x401000, 1, vec![0x90]);

        let attestation =
            binary.attest_exact_replay_slice(ExactReplaySelectedImage::thin(&image), &[witness]);

        assert!(!attestation.accepted);
        assert_eq!(attestation.accepted_instruction_count, 0);
        assert!(
            attestation.blockers.iter().any(|blocker| blocker.contains("not executable")),
            "{attestation:?}"
        );
        assert_eq!(
            attestation.instructions[0].segment_permissions,
            Some(BinarySegmentPermissions { read: true, write: false, execute: false })
        );
    }

    #[test]
    fn exact_replay_rejects_out_of_selected_image_range_and_byte_mismatch() {
        let image = vec![0; 8];
        let binary = replay_test_binary_with_segment(BinarySegment {
            name: Some(".text".to_string()),
            virtual_range: BinaryAddressRange { start: 0x5000, end: 0x5020 },
            file_offset: Some(0x1000),
            file_size: Some(0x20),
            permissions: BinarySegmentPermissions { read: true, write: false, execute: true },
        });
        let witnesses = vec![
            ExactReplayInstructionWitness::new(0x5009, 4, vec![0x90, 0x90, 0x90, 0x90]),
            ExactReplayInstructionWitness::new(0x5001, 2, vec![0xaa, 0xbb]),
        ];

        let attestation = binary
            .attest_exact_replay_slice(ExactReplaySelectedImage::new(0x1000, &image), &witnesses);

        assert!(!attestation.accepted);
        assert_eq!(attestation.instruction_count, 2);
        assert_eq!(attestation.accepted_instruction_count, 0);
        assert!(
            attestation.blockers.iter().any(|blocker| blocker.contains("outside selected image")),
            "{attestation:?}"
        );
        assert!(
            attestation
                .blockers
                .iter()
                .any(|blocker| blocker.contains("do not match selected image")),
            "{attestation:?}"
        );
        assert_eq!(
            attestation.instructions[0].file_range,
            Some(BinaryAddressRange { start: 0x1009, end: 0x100d })
        );
    }

    #[test]
    fn exact_replay_rejects_missing_size_or_length_mismatch() {
        let image = vec![0x90; 0x20];
        let binary = replay_test_binary_with_segment(replay_text_segment(true));
        let witnesses = vec![
            ExactReplayInstructionWitness {
                instruction_address: 0x401000,
                instruction_size: None,
                instruction_bytes: vec![0x90],
            },
            ExactReplayInstructionWitness::new(0x401001, 2, vec![0x90]),
        ];

        let attestation =
            binary.attest_exact_replay_slice(ExactReplaySelectedImage::thin(&image), &witnesses);

        assert!(!attestation.accepted);
        assert_eq!(attestation.accepted_instruction_count, 0);
        assert!(
            attestation.blockers.iter().any(|blocker| blocker.contains("missing instruction size")),
            "{attestation:?}"
        );
        assert!(
            attestation
                .blockers
                .iter()
                .any(|blocker| blocker.contains("instruction byte length mismatch")),
            "{attestation:?}"
        );
    }

    #[test]
    fn exact_replay_rejects_ambiguous_overlapping_segments() {
        let mut image = vec![0xcc; 0x40];
        image[0x10] = 0x90;
        let mut overlapping = replay_text_segment(true);
        overlapping.name = Some(".alt_text".to_string());
        overlapping.file_offset = Some(0x10);
        let binary = replay_test_binary_with_segments(vec![replay_text_segment(true), overlapping]);
        let witness = ExactReplayInstructionWitness::new(0x401000, 1, vec![0x90]);

        let attestation =
            binary.attest_exact_replay_slice(ExactReplaySelectedImage::thin(&image), &[witness]);

        assert!(!attestation.accepted);
        assert!(
            attestation
                .blockers
                .iter()
                .any(|blocker| blocker.contains("ambiguous overlapping loader segment")),
            "{attestation:?}"
        );
    }

    fn replay_text_segment(execute: bool) -> BinarySegment {
        BinarySegment {
            name: Some(".text".to_string()),
            virtual_range: BinaryAddressRange { start: 0x401000, end: 0x401020 },
            file_offset: Some(0x10),
            file_size: Some(0x20),
            permissions: BinarySegmentPermissions { read: true, write: false, execute },
        }
    }

    fn replay_test_binary_with_segment(segment: BinarySegment) -> LiftedBinary {
        replay_test_binary_with_segments(vec![segment])
    }

    fn replay_test_binary_with_segments(segments: Vec<BinarySegment>) -> LiftedBinary {
        LiftedBinary {
            format: "ELF",
            architecture: "x86-64",
            endianness: BinaryEndianness::Little,
            entry_point: Some(0x401000),
            build_id: None,
            segments,
            memory_model: BinaryMemoryModel::default(),
            function_seeds: vec![],
            source_provenance: LiftedSourceProvenance::default(),
            source_mappings: vec![],
            functions: vec![],
            failures: vec![],
        }
    }

    #[cfg(feature = "elf")]
    fn minimal_big_endian_elf() -> Vec<u8> {
        let mut buf = Vec::new();
        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']);
        buf.push(2); // ELFCLASS64
        buf.push(2); // ELFDATA2MSB
        buf.push(1); // EV_CURRENT
        buf.push(0); // OS/ABI
        buf.extend_from_slice(&[0u8; 8]);
        buf.extend_from_slice(&2u16.to_be_bytes()); // ET_EXEC
        buf.extend_from_slice(&0xB7u16.to_be_bytes()); // EM_AARCH64
        buf.extend_from_slice(&1u32.to_be_bytes()); // e_version
        buf.extend_from_slice(&0u64.to_be_bytes()); // e_entry
        buf.extend_from_slice(&0u64.to_be_bytes()); // e_phoff
        buf.extend_from_slice(&0u64.to_be_bytes()); // e_shoff
        buf.extend_from_slice(&0u32.to_be_bytes()); // e_flags
        buf.extend_from_slice(&64u16.to_be_bytes()); // e_ehsize
        buf.extend_from_slice(&56u16.to_be_bytes()); // e_phentsize
        buf.extend_from_slice(&0u16.to_be_bytes()); // e_phnum
        buf.extend_from_slice(&64u16.to_be_bytes()); // e_shentsize
        buf.extend_from_slice(&0u16.to_be_bytes()); // e_shnum
        buf.extend_from_slice(&0u16.to_be_bytes()); // e_shstrndx
        buf
    }

    #[cfg(feature = "elf")]
    fn minimal_elf32_i386() -> Vec<u8> {
        let mut buf = Vec::new();
        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']);
        buf.push(1); // ELFCLASS32
        buf.push(1); // ELFDATA2LSB
        buf.push(1); // EV_CURRENT
        buf.push(0); // OS/ABI
        buf.extend_from_slice(&[0u8; 8]);
        buf.extend_from_slice(&2u16.to_le_bytes()); // ET_EXEC
        buf.extend_from_slice(&3u16.to_le_bytes()); // EM_386
        buf.extend_from_slice(&1u32.to_le_bytes()); // e_version
        buf.extend_from_slice(&0u32.to_le_bytes()); // e_entry
        buf.extend_from_slice(&0u32.to_le_bytes()); // e_phoff
        buf.extend_from_slice(&0u32.to_le_bytes()); // e_shoff
        buf.extend_from_slice(&0u32.to_le_bytes()); // e_flags
        buf.extend_from_slice(&52u16.to_le_bytes()); // e_ehsize
        buf.extend_from_slice(&32u16.to_le_bytes()); // e_phentsize
        buf.extend_from_slice(&0u16.to_le_bytes()); // e_phnum
        buf.extend_from_slice(&40u16.to_le_bytes()); // e_shentsize
        buf.extend_from_slice(&0u16.to_le_bytes()); // e_shnum
        buf.extend_from_slice(&0u16.to_le_bytes()); // e_shstrndx
        buf
    }
}
