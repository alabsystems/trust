// trust-binary-parse: Unified binary abstraction
//
// Provides a format-agnostic view of parsed binaries. The `parse_binary`
// function auto-detects ELF, Mach-O, or PE format and returns a common
// `BinaryInfo` struct with architecture, sections, and symbols.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::detect::{BinaryFormat, detect_format};
use crate::error::ParseError;
use trust_types::BinarySegmentPermissions;

/// Target architecture detected from binary headers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Architecture {
    /// ARM 64-bit (AArch64)
    AArch64,
    /// x86 64-bit (AMD64)
    X86_64,
    /// x86 32-bit
    X86,
    /// ARM 32-bit
    Arm,
    /// Unknown or unsupported architecture
    Unknown(u32),
}

impl Architecture {
    /// Human-readable name for the architecture.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::AArch64 => "AArch64",
            Self::X86_64 => "x86-64",
            Self::X86 => "x86",
            Self::Arm => "ARM",
            Self::Unknown(_) => "Unknown",
        }
    }
}

/// Information about an executable section/segment.
#[derive(Debug, Clone)]
pub struct SectionInfo {
    /// Section name (e.g., ".text", "__text")
    pub name: String,
    /// Virtual address when loaded
    pub virtual_address: u64,
    /// File offset backing the section bytes, when known.
    pub file_offset: Option<u64>,
    /// Raw bytes of the section
    pub data: Vec<u8>,
    /// Whether this section contains executable code
    pub executable: bool,
}

/// Information about a loader-mapped segment.
#[derive(Debug, Clone)]
pub struct SegmentInfo {
    /// Segment name, when the binary format provides one.
    pub name: Option<String>,
    /// Virtual address where the segment is mapped.
    pub virtual_address: u64,
    /// Number of bytes reserved in memory for the segment.
    pub virtual_size: u64,
    /// File offset backing the segment, when known.
    pub file_offset: Option<u64>,
    /// Number of file bytes backing the segment, when known.
    pub file_size: Option<u64>,
    /// Loader permissions for the mapped segment.
    pub permissions: BinarySegmentPermissions,
}

impl SegmentInfo {
    /// End address of the half-open virtual range.
    #[must_use]
    pub fn virtual_end(&self) -> u64 {
        self.virtual_address.saturating_add(self.virtual_size)
    }

    /// Whether the segment range contains `va`.
    #[must_use]
    pub fn contains_va(&self, va: u64) -> bool {
        va >= self.virtual_address && va < self.virtual_end()
    }
}

/// A symbol table entry with format-agnostic fields.
#[derive(Debug, Clone)]
pub struct SymbolInfo {
    /// Symbol name
    pub name: String,
    /// Symbol address (virtual)
    pub address: u64,
    /// Symbol size (0 if unknown)
    pub size: u64,
    /// Whether this symbol represents a function
    pub is_function: bool,
}

/// Non-fatal metadata recovery diagnostic.
///
/// These diagnostics report optional metadata tables that could not be
/// recovered even though the binary itself was parseable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetadataDiagnostic {
    /// Metadata source that failed, such as `.symtab` or `PE exports`.
    pub source: String,
    /// Parser diagnostic for the failed metadata source.
    pub message: String,
}

/// Recovered ABI metadata and conservative contradiction diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiProvenance {
    /// ABI family inferred from container format and architecture.
    pub calling_convention: Option<String>,
    /// Pointer width implied by the object container, when known.
    pub object_pointer_width_bits: Option<u32>,
    /// Pointer width implied by the architecture identifier, when known.
    pub architecture_pointer_width_bits: Option<u32>,
    /// Whether contradictory ABI facts were observed.
    pub has_contradictions: bool,
    /// Human-readable diagnostics for downstream reports.
    pub diagnostics: Vec<String>,
}

impl AbiProvenance {
    fn unavailable(message: impl Into<String>) -> Self {
        Self {
            calling_convention: None,
            object_pointer_width_bits: None,
            architecture_pointer_width_bits: None,
            has_contradictions: false,
            diagnostics: vec![message.into()],
        }
    }
}

impl Default for AbiProvenance {
    fn default() -> Self {
        Self::unavailable("ABI metadata is unavailable")
    }
}

/// Availability of recovered debug type facts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeProvenanceStatus {
    /// No debug type facts were available.
    Unavailable,
    /// Debug type facts were recovered without local incompleteness markers.
    Recovered,
    /// Some debug type facts were recovered but remain incomplete/advisory.
    Partial,
    /// Debug type metadata existed but could not be parsed safely.
    Unsupported,
}

impl TypeProvenanceStatus {
    /// Stable lowercase name for report and snapshot serialization.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Unavailable => "unavailable",
            Self::Recovered => "recovered",
            Self::Partial => "partial",
            Self::Unsupported => "unsupported",
        }
    }
}

/// Summary of recovered debug type facts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeProvenance {
    /// Overall type fact availability state.
    pub status: TypeProvenanceStatus,
    /// Number of resolved type facts.
    pub recovered_type_count: usize,
    /// Number of resolved type facts that remain incomplete or advisory.
    pub uncertain_type_count: usize,
    /// Human-readable diagnostics for downstream reports.
    pub diagnostics: Vec<String>,
}

impl TypeProvenance {
    fn unavailable(message: impl Into<String>) -> Self {
        Self {
            status: TypeProvenanceStatus::Unavailable,
            recovered_type_count: 0,
            uncertain_type_count: 0,
            diagnostics: vec![message.into()],
        }
    }
}

impl Default for TypeProvenance {
    fn default() -> Self {
        Self::unavailable("debug type provenance is unavailable")
    }
}

/// Source provenance availability for binary-to-source backpropagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DebugSourceProvenanceStatus {
    /// No exact debug/source mapping was available.
    Unavailable,
    /// Exact address-to-source mappings were recovered.
    Exact,
    /// Debug/source data exists but at least one address maps to multiple
    /// distinct source locations.
    Ambiguous,
    /// Debug/source data was present but could not be parsed safely.
    Unsupported,
}

impl DebugSourceProvenanceStatus {
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

/// Summary of recovered debug/source provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugSourceProvenance {
    /// Overall availability state.
    pub status: DebugSourceProvenanceStatus,
    /// Number of exact address mappings exposed in [`BinaryInfo::source_mappings`].
    pub exact_mapping_count: usize,
    /// Number of addresses intentionally withheld due to ambiguity.
    pub ambiguous_mapping_count: usize,
    /// Human-readable gate diagnostics.
    pub diagnostics: Vec<String>,
}

impl DebugSourceProvenance {
    fn unavailable(diagnostic: impl Into<String>) -> Self {
        Self {
            status: DebugSourceProvenanceStatus::Unavailable,
            exact_mapping_count: 0,
            ambiguous_mapping_count: 0,
            diagnostics: vec![diagnostic.into()],
        }
    }
}

impl Default for DebugSourceProvenance {
    fn default() -> Self {
        Self::unavailable("exact debug/source provenance is unavailable")
    }
}

/// Exact binary-address to source mapping recovered from debug information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceMappingInfo {
    /// Instruction address that exactly starts a source line-table row.
    pub binary_address: u64,
    /// Source file path from debug information.
    pub file: String,
    /// One-based source line.
    pub line: u64,
    /// One-based source column, or 0 if unspecified.
    pub column: u64,
}

/// Content identity for the full input artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryArtifactDigest {
    /// Digest algorithm used for the artifact bytes.
    pub algorithm: String,
    /// Lowercase hex-encoded digest.
    pub value: String,
}

impl BinaryArtifactDigest {
    fn sha256(bytes: &[u8]) -> Self {
        Self { algorithm: "sha256".to_string(), value: sha256_hex(bytes) }
    }
}

/// File range selected for decompilation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryImageIdentity {
    /// Offset of this image within the root artifact.
    pub file_offset: u64,
    /// Number of file bytes covered by this image.
    pub file_size: u64,
    /// SHA-256 digest of the selected image bytes.
    pub sha256: String,
}

/// Endianness observed during metadata-safe binary parsing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BinaryEndianness {
    /// Little-endian object metadata.
    Little,
    /// Big-endian object metadata.
    Big,
    /// Endianness could not be identified from metadata.
    Unknown,
}

impl BinaryEndianness {
    /// Stable lowercase name for report and snapshot serialization.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Little => "little",
            Self::Big => "big",
            Self::Unknown => "unknown",
        }
    }
}

/// Stable parser-level blocker for metadata-safe rejected artifacts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BinaryRejectedArtifactBlocker {
    /// PE/i386 32-bit images are parsed for metadata but not promoted to lift.
    UnsupportedPeI386WordSize,
    /// Mach-O/x86_64 images are parsed for metadata but not promoted to lift.
    UnsupportedMachOX86_64Lift,
}

impl BinaryRejectedArtifactBlocker {
    /// Stable machine-readable blocker identity.
    #[must_use]
    pub fn id(self) -> &'static str {
        match self {
            Self::UnsupportedPeI386WordSize => "unsupported_pe_i386_word_size",
            Self::UnsupportedMachOX86_64Lift => "unsupported_macho_x86_64_lift",
        }
    }

    /// Human-readable reason for diagnostics.
    #[must_use]
    pub fn description(self) -> &'static str {
        match self {
            Self::UnsupportedPeI386WordSize => {
                "PE/i386 32-bit images are metadata-only; machine-code lifting is not enabled for this word-size path"
            }
            Self::UnsupportedMachOX86_64Lift => {
                "Mach-O/x86_64 images are metadata-only; machine-code lifting is not enabled for this architecture path"
            }
        }
    }
}

/// Metadata-safe rejected artifact evidence.
///
/// This records that container metadata was parsed safely, but the artifact was
/// intentionally not promoted into machine-code lifting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryRejectedArtifact {
    /// Schema version for canonical rejected-artifact evidence.
    pub schema_version: u32,
    /// Stable lowercase binary format tag.
    pub format: String,
    /// Stable lowercase architecture tag.
    pub architecture: String,
    /// Endianness observed from the object metadata.
    pub endianness: BinaryEndianness,
    /// Object word size, when known.
    pub word_size_bits: Option<u32>,
    /// Digest and size of the root artifact bytes passed to the parser.
    pub artifact: BinaryArtifactDigest,
    /// Size of the root artifact bytes passed to the parser.
    pub artifact_size: u64,
    /// File range selected during metadata-safe parsing.
    pub selected_image: BinaryImageIdentity,
    /// Loader identity from build-id/UUID/timestamp metadata, when available.
    pub loader_build_id: Option<String>,
    /// Stable blocker identity for this rejection.
    pub blocker: BinaryRejectedArtifactBlocker,
    /// Human-readable rejection diagnostic.
    pub message: String,
    /// Non-fatal metadata recovery diagnostics observed before rejection.
    pub metadata_diagnostics: Vec<MetadataDiagnostic>,
}

impl BinaryRejectedArtifact {
    /// Stable path tuple for report grouping.
    #[must_use]
    pub fn metadata_path(&self) -> String {
        let word_size = self
            .word_size_bits
            .map(|bits| bits.to_string())
            .unwrap_or_else(|| "unknown-word-size".to_string());
        format!("{}/{}/{}/{}", self.format, self.architecture, self.endianness.name(), word_size)
    }

    /// Proof-grade blockers visible at parser rejected-artifact level.
    #[must_use]
    pub fn proof_grade_identity_blockers(&self) -> Vec<String> {
        let mut blockers = vec![self.blocker.id().to_string()];
        if !is_canonical_sha256_hex(&self.artifact.value) {
            blockers.push("root artifact digest is not canonical SHA-256 hex".to_string());
        }
        if !is_canonical_sha256_hex(&self.selected_image.sha256) {
            blockers.push("selected image digest is not canonical SHA-256 hex".to_string());
        }
        if self.selected_image.file_offset.saturating_add(self.selected_image.file_size)
            > self.artifact_size
        {
            blockers.push("selected image range exceeds root artifact size".to_string());
        }
        blockers
    }

    /// Rejected artifacts are never proof-grade bindable.
    #[must_use]
    pub fn is_proof_grade_bindable(&self) -> bool {
        false
    }
}

/// Stable identity metadata for binding parser output to certificates,
/// replay transcripts, and source provenance records.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryArtifactIdentity {
    /// Schema version for canonical serialized identity records.
    pub schema_version: u32,
    /// Stable lowercase binary format tag.
    pub format: String,
    /// Stable lowercase architecture tag.
    pub architecture: String,
    /// Digest and size of the root artifact bytes passed to the parser.
    pub artifact: BinaryArtifactDigest,
    /// Size of the root artifact bytes passed to the parser.
    pub artifact_size: u64,
    /// Exact image range selected for decompilation. For thin binaries this is
    /// the whole file; for fat Mach-O this is the promoted slice.
    pub selected_image: BinaryImageIdentity,
    /// Loader identity from build-id/UUID/timestamp metadata, when available.
    pub loader_build_id: Option<String>,
}

impl BinaryArtifactIdentity {
    /// Serialize this identity as stable JSON for downstream binding records.
    ///
    /// Field order follows the struct definition and is covered by tests. This
    /// crate intentionally avoids serde dependencies so parser identity remains
    /// available in the zero-copy parser without expanding its dependency set.
    #[must_use]
    pub fn to_canonical_json(&self) -> String {
        let loader_build_id = self
            .loader_build_id
            .as_deref()
            .map(|value| format!("\"{}\"", json_escape(value)))
            .unwrap_or_else(|| "null".to_string());
        format!(
            "{{\"schema_version\":{},\"format\":\"{}\",\"architecture\":\"{}\",\"artifact\":{{\"algorithm\":\"{}\",\"value\":\"{}\"}},\"artifact_size\":{},\"selected_image\":{{\"file_offset\":{},\"file_size\":{},\"sha256\":\"{}\"}},\"loader_build_id\":{}}}",
            self.schema_version,
            json_escape(&self.format),
            json_escape(&self.architecture),
            json_escape(&self.artifact.algorithm),
            json_escape(&self.artifact.value),
            self.artifact_size,
            self.selected_image.file_offset,
            self.selected_image.file_size,
            json_escape(&self.selected_image.sha256),
            loader_build_id
        )
    }

    /// Proof-grade release blockers that are visible at parser identity level.
    #[must_use]
    pub fn proof_grade_identity_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();
        if self.loader_build_id.as_deref().unwrap_or_default().is_empty() {
            blockers.push(
                "missing loader build-id/UUID/timestamp identity for certificate/replay binding"
                    .to_string(),
            );
        }
        if !is_canonical_sha256_hex(&self.artifact.value) {
            blockers.push("root artifact digest is not canonical SHA-256 hex".to_string());
        }
        if !is_canonical_sha256_hex(&self.selected_image.sha256) {
            blockers.push("selected image digest is not canonical SHA-256 hex".to_string());
        }
        if self.selected_image.file_offset.saturating_add(self.selected_image.file_size)
            > self.artifact_size
        {
            blockers.push("selected image range exceeds root artifact size".to_string());
        }
        if self.format == "pe-coff" && self.architecture == "x86" {
            blockers
                .push(BinaryRejectedArtifactBlocker::UnsupportedPeI386WordSize.id().to_string());
        }
        if (self.format == "macho" || self.format == "fat-macho") && self.architecture == "x86_64" {
            blockers
                .push(BinaryRejectedArtifactBlocker::UnsupportedMachOX86_64Lift.id().to_string());
        }
        blockers
    }

    /// Whether parser-level identity is strong enough to be consumed by a
    /// proof-grade binary provenance gate.
    #[must_use]
    pub fn is_proof_grade_bindable(&self) -> bool {
        self.proof_grade_identity_blockers().is_empty()
    }
}

/// Binary parse result with explicit content identity metadata.
#[derive(Debug)]
pub struct BinaryParseResult {
    /// Format-agnostic parsed binary information.
    pub binary: BinaryInfo,
    /// Content-addressed identity for binding downstream records.
    pub identity: BinaryArtifactIdentity,
}

/// Parser artifact evidence that distinguishes accepted metadata from closed
/// metadata-safe rejections.
#[derive(Debug)]
pub enum BinaryArtifactEvidence {
    /// Binary metadata was accepted for downstream lifting.
    Parsed(Box<BinaryParseResult>),
    /// Binary metadata was parsed safely, but lifting must not be attempted.
    Rejected(Box<BinaryRejectedArtifact>),
}

impl BinaryArtifactEvidence {
    /// Returns `true` when this evidence is a metadata-safe rejection.
    #[must_use]
    pub fn is_rejected(&self) -> bool {
        matches!(self, Self::Rejected(_))
    }

    /// Borrow rejected-artifact evidence, if this outcome is rejected.
    #[must_use]
    pub fn rejected(&self) -> Option<&BinaryRejectedArtifact> {
        match self {
            Self::Rejected(rejected) => Some(rejected),
            Self::Parsed(_) => None,
        }
    }

    /// Borrow accepted parser evidence, if this outcome is accepted.
    #[must_use]
    pub fn parsed(&self) -> Option<&BinaryParseResult> {
        match self {
            Self::Parsed(parsed) => Some(parsed),
            Self::Rejected(_) => None,
        }
    }
}

/// Format-agnostic representation of a parsed binary.
#[derive(Debug)]
pub struct BinaryInfo {
    /// Detected binary format
    pub format: BinaryFormat,
    /// Target architecture
    pub architecture: Architecture,
    /// Executable sections with their data and virtual addresses
    pub sections: Vec<SectionInfo>,
    /// Loader-mapped segments with permissions.
    pub segments: Vec<SegmentInfo>,
    /// Symbol table entries
    pub symbols: Vec<SymbolInfo>,
    /// Entry point address (if available)
    pub entry_point: Option<u64>,
    /// Build ID or equivalent loader identifier, when available.
    pub build_id: Option<String>,
    /// Recovered ABI metadata and contradiction diagnostics.
    pub abi: AbiProvenance,
    /// Recovered debug type fact provenance.
    pub type_provenance: TypeProvenance,
    /// Exact debug/source provenance availability.
    pub debug_source: DebugSourceProvenance,
    /// Exact binary-address to source mappings.
    pub source_mappings: Vec<SourceMappingInfo>,
    /// Non-fatal metadata recovery diagnostics.
    pub metadata_diagnostics: Vec<MetadataDiagnostic>,
}

impl BinaryInfo {
    /// Get all function symbols.
    pub fn function_symbols(&self) -> impl Iterator<Item = &SymbolInfo> {
        self.symbols.iter().filter(|s| s.is_function)
    }

    /// Find a symbol by name.
    #[must_use]
    pub fn find_symbol(&self, name: &str) -> Option<&SymbolInfo> {
        self.symbols.iter().find(|s| s.name == name)
    }

    /// Get non-fatal metadata recovery diagnostics.
    pub fn metadata_diagnostics(&self) -> &[MetadataDiagnostic] {
        &self.metadata_diagnostics
    }

    /// Get loader-mapped segments with permissions.
    pub fn segments(&self) -> &[SegmentInfo] {
        &self.segments
    }

    /// Get the build ID or equivalent loader identifier.
    #[must_use]
    pub fn build_id(&self) -> Option<&str> {
        self.build_id.as_deref()
    }

    /// Get recovered ABI metadata and contradiction diagnostics.
    #[must_use]
    pub fn abi(&self) -> &AbiProvenance {
        &self.abi
    }

    /// Get recovered debug type fact provenance.
    #[must_use]
    pub fn type_provenance(&self) -> &TypeProvenance {
        &self.type_provenance
    }

    /// Get exact debug/source provenance availability.
    #[must_use]
    pub fn debug_source(&self) -> &DebugSourceProvenance {
        &self.debug_source
    }

    /// Get exact binary-address to source mappings.
    pub fn source_mappings(&self) -> &[SourceMappingInfo] {
        &self.source_mappings
    }

    /// Find an exact source mapping for a binary address.
    #[must_use]
    pub fn exact_source_mapping(&self, address: u64) -> Option<&SourceMappingInfo> {
        self.source_mappings.iter().find(|mapping| mapping.binary_address == address)
    }

    /// Find the loader segment containing a virtual address.
    #[must_use]
    pub fn segment_containing_va(&self, va: u64) -> Option<&SegmentInfo> {
        self.segments.iter().find(|segment| segment.contains_va(va))
    }

    /// Get the bytes at a virtual address from the appropriate section.
    ///
    /// Returns `None` if the address is not within any section.
    #[must_use]
    pub fn bytes_at_va(&self, va: u64, len: usize) -> Option<&[u8]> {
        for section in &self.sections {
            let section_end = section.virtual_address + section.data.len() as u64;
            if va >= section.virtual_address && va < section_end {
                let offset = (va - section.virtual_address) as usize;
                let available = section.data.len() - offset;
                let actual_len = len.min(available);
                return Some(&section.data[offset..offset + actual_len]);
            }
        }
        None
    }
}

/// Parse a binary from raw bytes, auto-detecting the format.
///
/// Returns a `BinaryInfo` with architecture, sections, symbols, and entry
/// point extracted from the binary.
///
/// # Errors
///
/// Returns `ParseError` if format detection fails or the binary cannot be
/// parsed by the detected format's parser.
pub fn parse_binary(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    let format = detect_format(data).ok_or_else(|| {
        if data.len() < 4 {
            ParseError::UnexpectedEof(0)
        } else {
            let magic = u32::from_be_bytes([data[0], data[1], data[2], data[3]]);
            ParseError::InvalidMagic(magic)
        }
    })?;

    match format {
        BinaryFormat::Elf => parse_elf(data),
        BinaryFormat::MachO => parse_macho(data),
        BinaryFormat::FatMachO => parse_fat_macho(data),
        BinaryFormat::Pe => parse_pe(data),
    }
}

/// Parse a binary and return explicit artifact identity metadata alongside the
/// existing format-agnostic binary view.
///
/// # Errors
///
/// Returns `ParseError` if parsing fails or if the selected image range cannot
/// be reconstructed for identity binding.
pub fn parse_binary_with_identity(data: &[u8]) -> Result<BinaryParseResult, ParseError> {
    let binary = parse_binary(data)?;
    let identity = binary_artifact_identity(data, &binary)?;
    Ok(BinaryParseResult { binary, identity })
}

/// Parse a binary and return either accepted parser identity evidence or a
/// metadata-safe rejected-artifact record.
///
/// # Errors
///
/// Returns `ParseError` if the container cannot be parsed safely enough to
/// produce accepted or rejected artifact evidence.
pub fn parse_binary_with_rejection_evidence(
    data: &[u8],
) -> Result<BinaryArtifactEvidence, ParseError> {
    let parsed = parse_binary_with_identity(data)?;
    if rejected_artifact_blocker(&parsed.binary).is_some() {
        let rejected = rejected_artifact_evidence(data, parsed)
            .expect("blocker precheck should produce rejected artifact evidence");
        Ok(BinaryArtifactEvidence::Rejected(Box::new(rejected)))
    } else {
        Ok(BinaryArtifactEvidence::Parsed(Box::new(parsed)))
    }
}

/// Build content identity metadata for an already-parsed binary.
///
/// # Errors
///
/// Returns `ParseError` if a fat Mach-O selected slice cannot be reconstructed
/// from the root artifact.
pub fn binary_artifact_identity(
    data: &[u8],
    binary: &BinaryInfo,
) -> Result<BinaryArtifactIdentity, ParseError> {
    let selected_image = selected_image_identity(data, binary)?;
    Ok(BinaryArtifactIdentity {
        schema_version: 1,
        format: stable_format_name(binary.format).to_string(),
        architecture: stable_architecture_name(binary.architecture).to_string(),
        artifact: BinaryArtifactDigest::sha256(data),
        artifact_size: data.len() as u64,
        selected_image,
        loader_build_id: binary.build_id.clone(),
    })
}

fn push_symbol_unique(symbols: &mut Vec<SymbolInfo>, symbol: SymbolInfo) {
    if symbols
        .iter()
        .any(|existing| existing.name == symbol.name && existing.address == symbol.address)
    {
        return;
    }
    symbols.push(symbol);
}

fn normalize_macho_symbol_name(raw_name: &str) -> String {
    raw_name.strip_prefix('_').unwrap_or(raw_name).to_owned()
}

fn push_metadata_diagnostic(
    diagnostics: &mut Vec<MetadataDiagnostic>,
    source: impl Into<String>,
    err: ParseError,
) {
    diagnostics.push(MetadataDiagnostic { source: source.into(), message: err.to_string() });
}

fn hex_lower(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn sha256_hex(bytes: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h = [
        0x6a09e667u32,
        0xbb67ae85,
        0x3c6ef372,
        0xa54ff53a,
        0x510e527f,
        0x9b05688c,
        0x1f83d9ab,
        0x5be0cd19,
    ];
    let bit_len = (bytes.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity(((bytes.len() + 9).div_ceil(64)) * 64);
    padded.extend_from_slice(bytes);
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    let mut w = [0u32; 64];
    for chunk in padded.chunks_exact(64) {
        for (index, word) in w.iter_mut().take(16).enumerate() {
            let offset = index * 4;
            *word = u32::from_be_bytes([
                chunk[offset],
                chunk[offset + 1],
                chunk[offset + 2],
                chunk[offset + 3],
            ]);
        }
        for index in 16..64 {
            let s0 = w[index - 15].rotate_right(7)
                ^ w[index - 15].rotate_right(18)
                ^ (w[index - 15] >> 3);
            let s1 = w[index - 2].rotate_right(17)
                ^ w[index - 2].rotate_right(19)
                ^ (w[index - 2] >> 10);
            w[index] = w[index - 16].wrapping_add(s0).wrapping_add(w[index - 7]).wrapping_add(s1);
        }

        let mut a = h[0];
        let mut b = h[1];
        let mut c = h[2];
        let mut d = h[3];
        let mut e = h[4];
        let mut f = h[5];
        let mut g = h[6];
        let mut hh = h[7];

        for index in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 =
                hh.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[index]).wrapping_add(w[index]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut digest = [0u8; 32];
    for (index, word) in h.iter().enumerate() {
        digest[index * 4..index * 4 + 4].copy_from_slice(&word.to_be_bytes());
    }
    hex_lower(&digest)
}

fn json_escape(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for ch in value.chars() {
        match ch {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            ch if ch.is_control() => {
                use std::fmt::Write as _;
                let _ = write!(escaped, "\\u{:04x}", ch as u32);
            }
            ch => escaped.push(ch),
        }
    }
    escaped
}

fn is_canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn stable_format_name(format: BinaryFormat) -> &'static str {
    match format {
        BinaryFormat::Elf => "elf",
        BinaryFormat::MachO => "macho",
        BinaryFormat::FatMachO => "fat-macho",
        BinaryFormat::Pe => "pe-coff",
    }
}

fn stable_architecture_name(architecture: Architecture) -> &'static str {
    match architecture {
        Architecture::AArch64 => "aarch64",
        Architecture::X86_64 => "x86_64",
        Architecture::X86 => "x86",
        Architecture::Arm => "arm",
        Architecture::Unknown(_) => "unknown",
    }
}

fn rejected_artifact_evidence(
    data: &[u8],
    parsed: BinaryParseResult,
) -> Option<BinaryRejectedArtifact> {
    let BinaryParseResult { binary, identity } = parsed;
    let blocker = rejected_artifact_blocker(&binary)?;
    let format = stable_format_name(binary.format).to_string();
    let architecture = stable_architecture_name(binary.architecture).to_string();
    let endianness = rejected_artifact_endianness(data, &binary, &identity.selected_image);
    let word_size_bits = binary
        .abi
        .object_pointer_width_bits
        .or_else(|| architecture_pointer_width_bits(binary.architecture));
    let mut metadata_diagnostics = binary.metadata_diagnostics;
    let metadata_path = rejected_metadata_path(&format, &architecture, endianness, word_size_bits);
    let message = format!(
        "{metadata_path} rejected at parser metadata boundary: blocker_id={}; {}; lifting not attempted",
        blocker.id(),
        blocker.description()
    );
    metadata_diagnostics.push(MetadataDiagnostic {
        source: "artifact rejection".to_string(),
        message: message.clone(),
    });

    Some(BinaryRejectedArtifact {
        schema_version: 1,
        format,
        architecture,
        endianness,
        word_size_bits,
        artifact: identity.artifact,
        artifact_size: identity.artifact_size,
        selected_image: identity.selected_image,
        loader_build_id: identity.loader_build_id,
        blocker,
        message,
        metadata_diagnostics,
    })
}

fn rejected_artifact_blocker(binary: &BinaryInfo) -> Option<BinaryRejectedArtifactBlocker> {
    let word_size_bits = binary
        .abi
        .object_pointer_width_bits
        .or_else(|| architecture_pointer_width_bits(binary.architecture));
    if binary.format == BinaryFormat::Pe
        && binary.architecture == Architecture::X86
        && word_size_bits == Some(32)
    {
        Some(BinaryRejectedArtifactBlocker::UnsupportedPeI386WordSize)
    } else if matches!(binary.format, BinaryFormat::MachO | BinaryFormat::FatMachO)
        && binary.architecture == Architecture::X86_64
    {
        Some(BinaryRejectedArtifactBlocker::UnsupportedMachOX86_64Lift)
    } else {
        None
    }
}

fn rejected_artifact_endianness(
    data: &[u8],
    binary: &BinaryInfo,
    selected_image: &BinaryImageIdentity,
) -> BinaryEndianness {
    match binary.format {
        BinaryFormat::Pe => BinaryEndianness::Little,
        BinaryFormat::MachO | BinaryFormat::FatMachO => {
            let Ok(offset) = usize::try_from(selected_image.file_offset) else {
                return BinaryEndianness::Unknown;
            };
            match data.get(offset..offset.saturating_add(4)) {
                Some([0xCF, 0xFA, 0xED, 0xFE]) => BinaryEndianness::Little,
                Some([0xFE, 0xED, 0xFA, 0xCF]) => BinaryEndianness::Big,
                _ => BinaryEndianness::Unknown,
            }
        }
        _ => BinaryEndianness::Unknown,
    }
}

fn rejected_metadata_path(
    format: &str,
    architecture: &str,
    endianness: BinaryEndianness,
    word_size_bits: Option<u32>,
) -> String {
    let word_size = word_size_bits
        .map(|bits| bits.to_string())
        .unwrap_or_else(|| "unknown-word-size".to_string());
    format!("{format}/{architecture}/{}/{}", endianness.name(), word_size)
}

fn selected_image_identity(
    data: &[u8],
    binary: &BinaryInfo,
) -> Result<BinaryImageIdentity, ParseError> {
    let (file_offset, file_size) = if binary.format == BinaryFormat::FatMachO {
        let arch = selected_fat_macho_arch(data, binary.architecture)?;
        (arch.offset, arch.size)
    } else {
        (0, data.len() as u64)
    };
    let end = file_offset.checked_add(file_size).ok_or(ParseError::DataOutOfBounds {
        offset: file_offset,
        end: u64::MAX,
        file_size: data.len(),
    })?;
    if end > data.len() as u64 {
        return Err(ParseError::DataOutOfBounds {
            offset: file_offset,
            end,
            file_size: data.len(),
        });
    }
    let start = usize::try_from(file_offset).map_err(|_| ParseError::DataOutOfBounds {
        offset: file_offset,
        end,
        file_size: data.len(),
    })?;
    let end = usize::try_from(end).map_err(|_| ParseError::DataOutOfBounds {
        offset: file_offset,
        end,
        file_size: data.len(),
    })?;
    Ok(BinaryImageIdentity { file_offset, file_size, sha256: sha256_hex(&data[start..end]) })
}

fn selected_fat_macho_arch(
    data: &[u8],
    architecture: Architecture,
) -> Result<crate::header::FatArch, ParseError> {
    use crate::constants::{CPU_TYPE_ARM64, CPU_TYPE_X86_64};

    let expected_cputype = match architecture {
        Architecture::AArch64 => CPU_TYPE_ARM64,
        Architecture::X86_64 => CPU_TYPE_X86_64,
        other => {
            return Err(ParseError::UnsupportedFormat(format!(
                "fat Mach-O selected unsupported architecture {} for identity binding",
                other.name()
            )));
        }
    };
    crate::macho::MachO::parse_fat_arches(data)?
        .into_iter()
        .find(|arch| arch.cputype == expected_cputype)
        .ok_or_else(|| {
            ParseError::InvalidHeader(format!(
                "fat Mach-O selected {} slice missing during identity binding",
                architecture.name()
            ))
        })
}

fn align4(value: usize) -> Option<usize> {
    value.checked_add(3).map(|value| value & !3)
}

fn read_note_u32(data: &[u8], offset: usize, swap: bool) -> Option<u32> {
    let bytes: [u8; 4] = data.get(offset..offset.checked_add(4)?)?.try_into().ok()?;
    Some(if swap { u32::from_be_bytes(bytes) } else { u32::from_le_bytes(bytes) })
}

fn parse_gnu_build_id_note(data: &[u8], swap: bool) -> Option<String> {
    let mut offset = 0usize;
    while offset.checked_add(12)? <= data.len() {
        let namesz = read_note_u32(data, offset, swap)? as usize;
        let descsz = read_note_u32(data, offset + 4, swap)? as usize;
        let note_type = read_note_u32(data, offset + 8, swap)?;
        offset += 12;

        let name_start = offset;
        let name_end = name_start.checked_add(namesz)?;
        let desc_start = align4(name_end)?;
        let desc_end = desc_start.checked_add(descsz)?;
        if desc_end > data.len() {
            return None;
        }

        let name = data
            .get(name_start..name_end)?
            .strip_suffix(&[0])
            .unwrap_or(&data[name_start..name_end]);
        if note_type == 3 && name == b"GNU" {
            return Some(format!("elf-gnu-build-id:{}", hex_lower(&data[desc_start..desc_end])));
        }

        offset = align4(desc_end)?;
    }
    None
}

fn elf_build_id(elf: &crate::elf::Elf64<'_>, big_endian: bool) -> Option<String> {
    for sh in &elf.sections {
        let name = elf.section_name(sh).unwrap_or("");
        if name == ".note.gnu.build-id"
            && let Ok(data) = elf.section_data(sh)
            && let Some(build_id) = parse_gnu_build_id_note(data, big_endian)
        {
            return Some(build_id);
        }
    }
    None
}

fn elf32_build_id(elf: &crate::elf::Elf32<'_>, big_endian: bool) -> Option<String> {
    for sh in &elf.sections {
        let name = elf.section_name(sh).unwrap_or("");
        if name == ".note.gnu.build-id"
            && let Ok(data) = elf.section_data(sh)
            && let Some(build_id) = parse_gnu_build_id_note(data, big_endian)
        {
            return Some(build_id);
        }
    }
    None
}

fn elf_segment_permissions(flags: u32) -> BinarySegmentPermissions {
    BinarySegmentPermissions {
        read: (flags & 0x4) != 0,
        write: (flags & 0x2) != 0,
        execute: (flags & 0x1) != 0,
    }
}

fn macho_segment_permissions(initprot: i32) -> BinarySegmentPermissions {
    const VM_PROT_READ: i32 = 0x1;
    const VM_PROT_WRITE: i32 = 0x2;
    const VM_PROT_EXECUTE: i32 = 0x4;

    BinarySegmentPermissions {
        read: (initprot & VM_PROT_READ) != 0,
        write: (initprot & VM_PROT_WRITE) != 0,
        execute: (initprot & VM_PROT_EXECUTE) != 0,
    }
}

fn pe_section_permissions(characteristics: u32) -> BinarySegmentPermissions {
    BinarySegmentPermissions {
        read: (characteristics & 0x4000_0000) != 0,
        write: (characteristics & 0x8000_0000) != 0,
        execute: (characteristics & 0x2000_0000) != 0,
    }
}

fn architecture_pointer_width_bits(architecture: Architecture) -> Option<u32> {
    match architecture {
        Architecture::AArch64 | Architecture::X86_64 => Some(64),
        Architecture::X86 | Architecture::Arm => Some(32),
        Architecture::Unknown(_) => None,
    }
}

fn default_calling_convention(format: BinaryFormat, architecture: Architecture) -> Option<String> {
    match (format, architecture) {
        (BinaryFormat::Elf, Architecture::AArch64) => Some("AAPCS64".to_string()),
        (BinaryFormat::Elf, Architecture::X86_64) => Some("SysV64".to_string()),
        (BinaryFormat::Elf, Architecture::X86) => Some("SysV32".to_string()),
        (BinaryFormat::MachO | BinaryFormat::FatMachO, Architecture::AArch64) => {
            Some("AAPCS64".to_string())
        }
        (BinaryFormat::MachO | BinaryFormat::FatMachO, Architecture::X86_64) => {
            Some("SysV64".to_string())
        }
        (BinaryFormat::Pe, Architecture::X86_64 | Architecture::AArch64) => {
            Some("Win64".to_string())
        }
        _ => None,
    }
}

fn abi_provenance(
    format: BinaryFormat,
    architecture: Architecture,
    object_pointer_width_bits: Option<u32>,
) -> AbiProvenance {
    let architecture_pointer_width_bits = architecture_pointer_width_bits(architecture);
    let calling_convention = default_calling_convention(format, architecture);
    let mut diagnostics = Vec::new();

    if let (Some(object_width), Some(arch_width)) =
        (object_pointer_width_bits, architecture_pointer_width_bits)
        && object_width != arch_width
    {
        diagnostics.push(format!(
            "{} object pointer width ({object_width}) contradicts {} architecture pointer width ({arch_width})",
            format.name(),
            architecture.name()
        ));
    }

    if let Some(convention) = &calling_convention {
        diagnostics.push(format!(
            "default calling convention {convention} inferred from {} {} metadata; this is advisory, not a proof assumption",
            format.name(),
            architecture.name()
        ));
    } else {
        diagnostics.push(format!(
            "no default calling convention inferred for {} {}",
            format.name(),
            architecture.name()
        ));
    }

    AbiProvenance {
        calling_convention,
        object_pointer_width_bits,
        architecture_pointer_width_bits,
        has_contradictions: diagnostics.iter().any(|diagnostic| diagnostic.contains("contradict")),
        diagnostics,
    }
}

fn push_loaded_image_diagnostics(
    diagnostics: &mut Vec<MetadataDiagnostic>,
    segments: &[SegmentInfo],
) {
    for segment in segments {
        if !segment.permissions.read && !segment.permissions.write && !segment.permissions.execute {
            diagnostics.push(MetadataDiagnostic {
                source: "loader segment permissions".to_string(),
                message: format!(
                    "segment {} at [0x{:x}..0x{:x}) has no recovered read/write/execute permission bits",
                    segment.name.as_deref().unwrap_or("<unnamed>"),
                    segment.virtual_address,
                    segment.virtual_end()
                ),
            });
        }
    }

    for (left_index, left) in segments.iter().enumerate() {
        for right in segments.iter().skip(left_index + 1) {
            if left.virtual_address < right.virtual_end()
                && right.virtual_address < left.virtual_end()
                && left.permissions != right.permissions
            {
                diagnostics.push(MetadataDiagnostic {
                    source: "loader segment provenance".to_string(),
                    message: format!(
                        "segments {} [0x{:x}..0x{:x}) and {} [0x{:x}..0x{:x}) overlap with distinct permissions",
                        left.name.as_deref().unwrap_or("<unnamed>"),
                        left.virtual_address,
                        left.virtual_end(),
                        right.name.as_deref().unwrap_or("<unnamed>"),
                        right.virtual_address,
                        right.virtual_end()
                    ),
                });
            }
        }
    }
}

fn push_abi_diagnostics(diagnostics: &mut Vec<MetadataDiagnostic>, abi: &AbiProvenance) {
    if !abi.has_contradictions {
        return;
    }
    for message in abi.diagnostics.iter().filter(|diagnostic| diagnostic.contains("contradict")) {
        diagnostics.push(MetadataDiagnostic {
            source: "ABI provenance".to_string(),
            message: message.clone(),
        });
    }
}

fn format_macho_uuid(uuid: [u8; 16]) -> String {
    format!(
        "macho-uuid:{}-{}-{}-{}-{}",
        hex_lower(&uuid[0..4]),
        hex_lower(&uuid[4..6]),
        hex_lower(&uuid[6..8]),
        hex_lower(&uuid[8..10]),
        hex_lower(&uuid[10..16])
    )
}

fn macho_loader_id(macho: &crate::macho::MachO<'_>) -> Option<String> {
    macho.uuid().map(format_macho_uuid).or_else(|| {
        macho.build_version().map(|build| {
            format!(
                "macho-build-version:platform={},minos={},sdk={}",
                build.platform, build.minos, build.sdk
            )
        })
    })
}

fn pe_loader_id(pe: &crate::pe::Pe<'_>) -> Option<String> {
    if pe.coff_header.time_date_stamp == 0 {
        return None;
    }
    let checksum = pe.optional_header.as_ref().map_or(0, |header| header.checksum);
    Some(format!("pe-timestamp:{:08x};checksum:{:08x}", pe.coff_header.time_date_stamp, checksum))
}

fn unavailable_debug_source(format: &str) -> DebugSourceProvenance {
    DebugSourceProvenance::unavailable(format!(
        "{format} exact debug/source provenance is unavailable; diagnostics must remain binary-address-only"
    ))
}

fn unsupported_debug_source(message: impl Into<String>) -> DebugSourceProvenance {
    DebugSourceProvenance {
        status: DebugSourceProvenanceStatus::Unsupported,
        exact_mapping_count: 0,
        ambiguous_mapping_count: 0,
        diagnostics: vec![message.into()],
    }
}

fn type_provenance_from_dwarf(dwarf: &crate::dwarf::DwarfInfo<'_>) -> TypeProvenance {
    let report = dwarf.type_recovery_report();
    let status = if report.recovered_type_count == 0 {
        TypeProvenanceStatus::Unavailable
    } else if report.uncertain_type_count > 0 {
        TypeProvenanceStatus::Partial
    } else {
        TypeProvenanceStatus::Recovered
    };

    TypeProvenance {
        status,
        recovered_type_count: report.recovered_type_count,
        uncertain_type_count: report.uncertain_type_count,
        diagnostics: report.diagnostics,
    }
}

fn unsupported_type_provenance(message: impl Into<String>) -> TypeProvenance {
    TypeProvenance {
        status: TypeProvenanceStatus::Unsupported,
        recovered_type_count: 0,
        uncertain_type_count: 0,
        diagnostics: vec![message.into()],
    }
}

fn elf_debug_source(
    elf: &crate::elf::Elf64<'_>,
) -> (DebugSourceProvenance, Vec<SourceMappingInfo>, Vec<MetadataDiagnostic>) {
    let dwarf = match elf.dwarf_info() {
        Ok(Some(dwarf)) => dwarf,
        Ok(None) => return (unavailable_debug_source("ELF"), Vec::new(), Vec::new()),
        Err(err) => {
            let message = err.to_string();
            return (
                unsupported_debug_source(format!(
                    "ELF DWARF debug/source provenance could not be parsed exactly: {message}"
                )),
                Vec::new(),
                vec![MetadataDiagnostic {
                    source: "ELF DWARF debug/source provenance".to_string(),
                    message,
                }],
            );
        }
    };

    let report = dwarf.exact_source_mappings();
    let source_mappings: Vec<_> = report
        .exact_mappings
        .into_iter()
        .map(|mapping| SourceMappingInfo {
            binary_address: mapping.address,
            file: mapping.file,
            line: mapping.line,
            column: mapping.column,
        })
        .collect();
    let ambiguous_mapping_count = report.ambiguous_addresses.len();

    let status = if ambiguous_mapping_count > 0 {
        DebugSourceProvenanceStatus::Ambiguous
    } else if source_mappings.is_empty() {
        DebugSourceProvenanceStatus::Unavailable
    } else {
        DebugSourceProvenanceStatus::Exact
    };

    let diagnostics = match status {
        DebugSourceProvenanceStatus::Exact => vec![format!(
            "exact DWARF source provenance recovered for {} binary address(es)",
            source_mappings.len()
        )],
        DebugSourceProvenanceStatus::Ambiguous => vec![format!(
            "{} DWARF address(es) have ambiguous source rows; those addresses remain binary-address-only",
            ambiguous_mapping_count
        )],
        DebugSourceProvenanceStatus::Unavailable => {
            vec![
                "DWARF sections were present but contained no exact address-to-source rows; diagnostics must remain binary-address-only"
                    .to_string(),
            ]
        }
        DebugSourceProvenanceStatus::Unsupported => Vec::new(),
    };

    (
        DebugSourceProvenance {
            status,
            exact_mapping_count: source_mappings.len(),
            ambiguous_mapping_count,
            diagnostics,
        },
        source_mappings,
        Vec::new(),
    )
}

fn elf_type_provenance(elf: &crate::elf::Elf64<'_>) -> (TypeProvenance, Vec<MetadataDiagnostic>) {
    match elf.dwarf_info() {
        Ok(Some(dwarf)) => (type_provenance_from_dwarf(&dwarf), Vec::new()),
        Ok(None) => (
            TypeProvenance::unavailable(
                "ELF DWARF debug/type provenance is unavailable; type facts remain unknown",
            ),
            Vec::new(),
        ),
        Err(err) => {
            let message = err.to_string();
            (
                unsupported_type_provenance(format!(
                    "ELF DWARF debug/type provenance could not be parsed safely: {message}"
                )),
                vec![MetadataDiagnostic {
                    source: "ELF DWARF debug/type provenance".to_string(),
                    message,
                }],
            )
        }
    }
}

/// Parse an ELF binary into `BinaryInfo`.
fn parse_elf(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    let class = data.get(4).copied().ok_or(ParseError::UnexpectedEof(4))?;
    match class {
        1 => parse_elf32(data),
        2 => parse_elf64(data),
        other => Err(ParseError::UnsupportedFormat(format!("ELF class {other}"))),
    }
}

fn parse_elf32(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    let elf = crate::elf::Elf32::parse(data)?;
    let elf_notes_big_endian = matches!(data.get(5), Some(2));

    let architecture = match elf.header.e_machine {
        0x03 => Architecture::X86, // EM_386
        0x28 => Architecture::Arm, // EM_ARM
        other => Architecture::Unknown(u32::from(other)),
    };

    // Collect executable sections
    let mut sections = Vec::new();
    // SHF_EXECINSTR = 0x4
    for sh in &elf.sections {
        if sh.sh_flags & 0x4 != 0 && sh.sh_size > 0 {
            let name = elf.section_name(sh).unwrap_or("").to_owned();
            let section_data = elf.section_data(sh)?;
            sections.push(SectionInfo {
                name,
                virtual_address: u64::from(sh.sh_addr),
                file_offset: Some(u64::from(sh.sh_offset)),
                data: section_data.to_vec(),
                executable: true,
            });
        }
    }

    let segments: Vec<SegmentInfo> = elf
        .segments
        .iter()
        .enumerate()
        .filter(|(_, segment)| segment.p_type == 1 && segment.p_memsz > 0)
        .map(|(index, segment)| SegmentInfo {
            name: Some(format!("PT_LOAD[{index}]")),
            virtual_address: u64::from(segment.p_vaddr),
            virtual_size: u64::from(segment.p_memsz),
            file_offset: Some(u64::from(segment.p_offset)),
            file_size: Some(u64::from(segment.p_filesz)),
            permissions: elf_segment_permissions(segment.p_flags),
        })
        .collect();

    // Parse static and dynamic symbols. Many stripped ELF shared objects only
    // expose functions through .dynsym.
    let mut symbols = Vec::new();
    let mut metadata_diagnostics = Vec::new();
    push_loaded_image_diagnostics(&mut metadata_diagnostics, &segments);
    match elf.symbols() {
        Ok(elf_symbols) => {
            for s in elf_symbols.iter().filter(|s| !s.name.is_empty()) {
                push_symbol_unique(
                    &mut symbols,
                    SymbolInfo {
                        name: s.name.to_owned(),
                        address: u64::from(s.st_value),
                        size: u64::from(s.st_size),
                        is_function: s.is_function(),
                    },
                );
            }
        }
        Err(err) => push_metadata_diagnostic(&mut metadata_diagnostics, "ELF .symtab", err),
    }
    match elf.dynamic_symbols() {
        Ok(dynamic_symbols) => {
            for s in dynamic_symbols.iter().filter(|s| !s.name.is_empty()) {
                push_symbol_unique(
                    &mut symbols,
                    SymbolInfo {
                        name: s.name.to_owned(),
                        address: u64::from(s.st_value),
                        size: u64::from(s.st_size),
                        is_function: s.is_function(),
                    },
                );
            }
        }
        Err(err) => push_metadata_diagnostic(&mut metadata_diagnostics, "ELF .dynsym", err),
    }

    let abi = abi_provenance(BinaryFormat::Elf, architecture, Some(32));
    push_abi_diagnostics(&mut metadata_diagnostics, &abi);

    Ok(BinaryInfo {
        format: BinaryFormat::Elf,
        architecture,
        sections,
        segments,
        symbols,
        entry_point: Some(elf.entry_point()),
        build_id: elf32_build_id(&elf, elf_notes_big_endian),
        abi,
        type_provenance: TypeProvenance::unavailable(
            "ELF32 DWARF debug/type provenance is unavailable; type facts remain unknown",
        ),
        debug_source: unavailable_debug_source("ELF32"),
        source_mappings: Vec::new(),
        metadata_diagnostics,
    })
}

fn parse_elf64(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    let elf = crate::elf::Elf64::parse(data)?;
    let elf_notes_big_endian = matches!(data.get(5), Some(2));

    let architecture = match elf.header.e_machine {
        0xB7 => Architecture::AArch64, // EM_AARCH64
        0x3E => Architecture::X86_64,  // EM_X86_64
        0x03 => Architecture::X86,     // EM_386
        0x28 => Architecture::Arm,     // EM_ARM
        other => Architecture::Unknown(other as u32),
    };

    // Collect executable sections
    let mut sections = Vec::new();
    // SHF_EXECINSTR = 0x4
    for sh in &elf.sections {
        if sh.sh_flags & 0x4 != 0 && sh.sh_size > 0 {
            let name = elf.section_name(sh).unwrap_or("").to_owned();
            let section_data = elf.section_data(sh)?;
            sections.push(SectionInfo {
                name,
                virtual_address: sh.sh_addr,
                file_offset: Some(sh.sh_offset),
                data: section_data.to_vec(),
                executable: true,
            });
        }
    }

    let segments: Vec<SegmentInfo> = elf
        .segments
        .iter()
        .enumerate()
        .filter(|(_, segment)| segment.p_type == 1 && segment.p_memsz > 0)
        .map(|(index, segment)| SegmentInfo {
            name: Some(format!("PT_LOAD[{index}]")),
            virtual_address: segment.p_vaddr,
            virtual_size: segment.p_memsz,
            file_offset: Some(segment.p_offset),
            file_size: Some(segment.p_filesz),
            permissions: elf_segment_permissions(segment.p_flags),
        })
        .collect();

    // Parse static and dynamic symbols. Many stripped ELF shared objects only
    // expose functions through .dynsym.
    let mut symbols = Vec::new();
    let mut metadata_diagnostics = Vec::new();
    push_loaded_image_diagnostics(&mut metadata_diagnostics, &segments);
    match elf.symbols() {
        Ok(elf_symbols) => {
            for s in elf_symbols.iter().filter(|s| !s.name.is_empty()) {
                push_symbol_unique(
                    &mut symbols,
                    SymbolInfo {
                        name: s.name.to_owned(),
                        address: s.st_value,
                        size: s.st_size,
                        is_function: s.is_function(),
                    },
                );
            }
        }
        Err(err) => push_metadata_diagnostic(&mut metadata_diagnostics, "ELF .symtab", err),
    }
    match elf.dynamic_symbols() {
        Ok(dynamic_symbols) => {
            for s in dynamic_symbols.iter().filter(|s| !s.name.is_empty()) {
                push_symbol_unique(
                    &mut symbols,
                    SymbolInfo {
                        name: s.name.to_owned(),
                        address: s.st_value,
                        size: s.st_size,
                        is_function: s.is_function(),
                    },
                );
            }
        }
        Err(err) => push_metadata_diagnostic(&mut metadata_diagnostics, "ELF .dynsym", err),
    }

    let abi = abi_provenance(BinaryFormat::Elf, architecture, Some(64));
    push_abi_diagnostics(&mut metadata_diagnostics, &abi);

    let (type_provenance, type_diagnostics) = elf_type_provenance(&elf);
    metadata_diagnostics.extend(type_diagnostics);
    let (debug_source, source_mappings, debug_diagnostics) = elf_debug_source(&elf);
    metadata_diagnostics.extend(debug_diagnostics);

    Ok(BinaryInfo {
        format: BinaryFormat::Elf,
        architecture,
        sections,
        segments,
        symbols,
        entry_point: Some(elf.entry_point()),
        build_id: elf_build_id(&elf, elf_notes_big_endian),
        abi,
        type_provenance,
        debug_source,
        source_mappings,
        metadata_diagnostics,
    })
}

/// Parse a thin Mach-O binary into `BinaryInfo`.
fn parse_macho(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    let macho = crate::macho::MachO::parse(data)?;
    build_macho_info(&macho, BinaryFormat::MachO, 0)
}

/// Parse a fat/universal Mach-O binary into `BinaryInfo`.
///
/// Prefers the AArch64 slice if available, otherwise selects x86-64. Other
/// slices are not promoted into decompilation metadata.
fn parse_fat_macho(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    use crate::constants::{CPU_TYPE_ARM64, CPU_TYPE_X86_64};

    let arches = crate::macho::MachO::parse_fat_arches(data)?;
    let arch = arches
        .iter()
        .find(|arch| arch.cputype == CPU_TYPE_ARM64)
        .or_else(|| arches.iter().find(|arch| arch.cputype == CPU_TYPE_X86_64))
        .ok_or_else(|| {
            ParseError::UnsupportedFormat(
                "fat Mach-O contains no supported AArch64 or x86-64 slice".to_string(),
            )
        })?;
    let macho = crate::macho::MachO::from_fat_slice(data, arch)?;
    build_macho_info(&macho, BinaryFormat::FatMachO, arch.offset)
}

/// Build `BinaryInfo` from a parsed `MachO`.
fn build_macho_info(
    macho: &crate::macho::MachO<'_>,
    format: BinaryFormat,
    file_base: u64,
) -> Result<BinaryInfo, ParseError> {
    use crate::constants::{CPU_TYPE_ARM64, CPU_TYPE_X86_64};

    let architecture = match macho.header.cputype {
        c if c == CPU_TYPE_ARM64 => Architecture::AArch64,
        c if c == CPU_TYPE_X86_64 => Architecture::X86_64,
        other => Architecture::Unknown(other as u32),
    };

    // Collect executable sections
    let mut sections = Vec::new();
    for (_seg, sect) in macho.sections() {
        if sect.is_executable() && !sect.data.is_empty() {
            sections.push(SectionInfo {
                name: format!("{},{}", sect.segname, sect.sectname),
                virtual_address: sect.addr,
                file_offset: Some(add_file_base(file_base, u64::from(sect.offset))?),
                data: sect.data.to_vec(),
                executable: true,
            });
        }
    }

    // Collect loader segments
    let segments: Vec<SegmentInfo> = macho
        .segments()
        .filter(|segment| segment.vmsize > 0)
        .map(|segment| {
            Ok(SegmentInfo {
                name: Some(segment.segname.clone()),
                virtual_address: segment.vmaddr,
                virtual_size: segment.vmsize,
                file_offset: Some(add_file_base(file_base, segment.fileoff)?),
                file_size: Some(segment.filesize),
                permissions: macho_segment_permissions(segment.initprot),
            })
        })
        .collect::<Result<_, ParseError>>()?;

    // Parse symbols
    let mut metadata_diagnostics = Vec::new();
    push_loaded_image_diagnostics(&mut metadata_diagnostics, &segments);
    let abi = abi_provenance(format, architecture, Some(64));
    push_abi_diagnostics(&mut metadata_diagnostics, &abi);
    let text_section = macho_text_section_provenance(macho);
    let symbols = match macho.symbols() {
        Ok(macho_symbols) => macho_symbols
            .iter()
            .filter(|s| !s.name.is_empty() && s.is_defined_in_section() && !s.is_stab())
            .map(|s| SymbolInfo {
                name: normalize_macho_symbol_name(s.name),
                address: s.n_value,
                size: 0, // Mach-O nlist_64 has no size field
                is_function: macho_symbol_is_text_function(s, text_section),
            })
            .collect(),
        Err(err) => {
            push_metadata_diagnostic(&mut metadata_diagnostics, "Mach-O LC_SYMTAB", err);
            Vec::new()
        }
    };

    let entry_point = macho
        .entry_point()
        .and_then(|entryoff| macho_entry_point_va(macho, entryoff, &mut metadata_diagnostics));

    Ok(BinaryInfo {
        format,
        architecture,
        sections,
        segments,
        symbols,
        entry_point,
        build_id: macho_loader_id(macho),
        abi,
        type_provenance: TypeProvenance::unavailable(
            "Mach-O debug/type provenance is unavailable; type facts remain unknown",
        ),
        debug_source: unavailable_debug_source("Mach-O"),
        source_mappings: Vec::new(),
        metadata_diagnostics,
    })
}

fn add_file_base(file_base: u64, offset: u64) -> Result<u64, ParseError> {
    file_base.checked_add(offset).ok_or_else(|| {
        ParseError::InvalidHeader(format!(
            "file offset overflow while adding slice base 0x{file_base:x} to offset 0x{offset:x}"
        ))
    })
}

#[derive(Debug, Clone, Copy)]
struct MachOTextSectionProvenance {
    section_index: u8,
    start: u64,
    end: u64,
}

fn macho_text_section_provenance(
    macho: &crate::macho::MachO<'_>,
) -> Option<MachOTextSectionProvenance> {
    let text = macho.text_section()?;
    if !text.is_executable() {
        return None;
    }
    let section_index = macho
        .sections()
        .position(|(_, section)| std::ptr::eq(section, text))
        .and_then(|index| u8::try_from(index + 1).ok())?;
    Some(MachOTextSectionProvenance {
        section_index,
        start: text.addr(),
        end: text.addr().saturating_add(text.size()),
    })
}

fn macho_symbol_is_text_function(
    symbol: &crate::symbol::Symbol<'_>,
    text_section: Option<MachOTextSectionProvenance>,
) -> bool {
    let Some(text_section) = text_section else {
        return false;
    };
    symbol.section_index() == text_section.section_index
        && symbol.value() >= text_section.start
        && symbol.value() < text_section.end
}

fn macho_entry_point_va(
    macho: &crate::macho::MachO<'_>,
    entryoff: u64,
    diagnostics: &mut Vec<MetadataDiagnostic>,
) -> Option<u64> {
    for segment in macho.segments() {
        let permissions = macho_segment_permissions(segment.initprot);
        if !permissions.execute || segment.filesize == 0 {
            continue;
        }
        let Some(file_end) = segment.fileoff.checked_add(segment.filesize) else {
            diagnostics.push(MetadataDiagnostic {
                source: "Mach-O segment provenance".to_string(),
                message: format!(
                    "segment {} file range overflows at offset 0x{:x} with size 0x{:x}",
                    segment.segname, segment.fileoff, segment.filesize
                ),
            });
            continue;
        };
        if entryoff < segment.fileoff || entryoff >= file_end {
            continue;
        }
        let delta = entryoff - segment.fileoff;
        if let Some(entry) = segment.vmaddr.checked_add(delta) {
            return Some(entry);
        }
        diagnostics.push(MetadataDiagnostic {
            source: "Mach-O LC_MAIN".to_string(),
            message: format!(
                "entryoff 0x{entryoff:x} overflows when mapped through segment {} at vmaddr 0x{:x}",
                segment.segname, segment.vmaddr
            ),
        });
        return None;
    }

    diagnostics.push(MetadataDiagnostic {
        source: "Mach-O LC_MAIN".to_string(),
        message: format!(
            "entryoff 0x{entryoff:x} did not map to an executable loader segment file range; entry point withheld"
        ),
    });
    None
}

/// Parse a PE binary into `BinaryInfo`.
fn parse_pe(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    let pe = crate::pe::Pe::parse(data)?;

    let architecture = match pe.coff_header.machine {
        crate::pe::IMAGE_FILE_MACHINE_AMD64 => Architecture::X86_64,
        crate::pe::IMAGE_FILE_MACHINE_ARM64 => Architecture::AArch64,
        crate::pe::IMAGE_FILE_MACHINE_I386 => Architecture::X86,
        crate::pe::IMAGE_FILE_MACHINE_ARM => Architecture::Arm,
        other => Architecture::Unknown(other as u32),
    };

    // Collect executable sections
    // IMAGE_SCN_MEM_EXECUTE = 0x2000_0000
    let mut sections = Vec::new();
    let image_base = pe.image_base();
    for sh in &pe.sections {
        if sh.characteristics & 0x2000_0000 != 0 && sh.size_of_raw_data > 0 {
            let section_data = pe.section_data(sh)?;
            sections.push(SectionInfo {
                name: sh.name.clone(),
                virtual_address: image_base + sh.virtual_address as u64,
                file_offset: Some(sh.pointer_to_raw_data as u64),
                data: section_data.to_vec(),
                executable: true,
            });
        }
    }

    let segments: Vec<SegmentInfo> = pe
        .sections
        .iter()
        .filter(|section| section.virtual_size > 0 || section.size_of_raw_data > 0)
        .map(|section| {
            let virtual_size = if section.virtual_size > 0 {
                section.virtual_size
            } else {
                section.size_of_raw_data
            };
            SegmentInfo {
                name: Some(section.name.clone()),
                virtual_address: image_base + section.virtual_address as u64,
                virtual_size: virtual_size as u64,
                file_offset: Some(section.pointer_to_raw_data as u64),
                file_size: Some(section.size_of_raw_data as u64),
                permissions: pe_section_permissions(section.characteristics),
            }
        })
        .collect();

    // Parse COFF symbols (usually only in object files / unstripped PEs)
    let mut symbols = Vec::new();
    let mut metadata_diagnostics = Vec::new();
    push_loaded_image_diagnostics(&mut metadata_diagnostics, &segments);
    let pe_pointer_width = pe.optional_header.as_ref().map(|header| match header.format {
        crate::pe::PeFormat::Pe32 => 32,
        crate::pe::PeFormat::Pe32Plus => 64,
    });
    let abi = abi_provenance(BinaryFormat::Pe, architecture, pe_pointer_width);
    push_abi_diagnostics(&mut metadata_diagnostics, &abi);
    match pe.symbols() {
        Ok(pe_symbols) => {
            for s in pe_symbols.iter().filter(|s| !s.name.is_empty()) {
                push_symbol_unique(
                    &mut symbols,
                    SymbolInfo {
                        name: s.name.to_owned(),
                        address: pe_coff_symbol_va(&pe, s, image_base),
                        size: 0, // COFF symbols have no size
                        is_function: s.is_function(),
                    },
                );
            }
        }
        Err(err) => push_metadata_diagnostic(&mut metadata_diagnostics, "PE COFF symbols", err),
    }

    match pe.exports() {
        Ok(exports) => {
            for export in exports.iter() {
                if export.is_forwarder {
                    continue;
                }
                if let Some(name) = export.name {
                    push_symbol_unique(
                        &mut symbols,
                        SymbolInfo {
                            name: name.to_owned(),
                            address: image_base + export.rva as u64,
                            size: 0,
                            is_function: true,
                        },
                    );
                }
            }
        }
        Err(err) => push_metadata_diagnostic(&mut metadata_diagnostics, "PE exports", err),
    }

    let entry_point =
        if pe.entry_point() != 0 { Some(image_base + pe.entry_point() as u64) } else { None };

    Ok(BinaryInfo {
        format: BinaryFormat::Pe,
        architecture,
        sections,
        segments,
        symbols,
        entry_point,
        build_id: pe_loader_id(&pe),
        abi,
        type_provenance: TypeProvenance::unavailable(
            "PE/COFF debug/type provenance is unavailable; type facts remain unknown",
        ),
        debug_source: unavailable_debug_source("PE/COFF"),
        source_mappings: Vec::new(),
        metadata_diagnostics,
    })
}

fn pe_coff_symbol_va(
    pe: &crate::pe::Pe<'_>,
    symbol: &crate::pe::CoffSymbol<'_>,
    image_base: u64,
) -> u64 {
    if symbol.section_number > 0
        && let Some(section) = pe.sections.get(symbol.section_number as usize - 1)
    {
        return image_base + section.virtual_address as u64 + symbol.value as u64;
    }
    symbol.value as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn debug_source_provenance_status_names_are_stable() {
        assert_eq!(DebugSourceProvenanceStatus::Unavailable.name(), "unavailable");
        assert_eq!(DebugSourceProvenanceStatus::Exact.name(), "exact");
        assert_eq!(DebugSourceProvenanceStatus::Ambiguous.name(), "ambiguous");
        assert_eq!(DebugSourceProvenanceStatus::Unsupported.name(), "unsupported");
        assert_eq!(format!("{:?}", DebugSourceProvenanceStatus::Ambiguous), "Ambiguous");
    }

    #[test]
    fn type_provenance_status_names_are_stable() {
        assert_eq!(TypeProvenanceStatus::Unavailable.name(), "unavailable");
        assert_eq!(TypeProvenanceStatus::Recovered.name(), "recovered");
        assert_eq!(TypeProvenanceStatus::Partial.name(), "partial");
        assert_eq!(TypeProvenanceStatus::Unsupported.name(), "unsupported");
    }

    #[test]
    fn rejected_artifact_blocker_identity_names_are_stable() {
        assert_eq!(BinaryEndianness::Little.name(), "little");
        assert_eq!(BinaryEndianness::Big.name(), "big");
        assert_eq!(BinaryEndianness::Unknown.name(), "unknown");
        assert_eq!(
            BinaryRejectedArtifactBlocker::UnsupportedPeI386WordSize.id(),
            "unsupported_pe_i386_word_size"
        );
        assert_eq!(
            BinaryRejectedArtifactBlocker::UnsupportedMachOX86_64Lift.id(),
            "unsupported_macho_x86_64_lift"
        );
        assert!(
            BinaryRejectedArtifactBlocker::UnsupportedPeI386WordSize
                .description()
                .contains("PE/i386")
        );
        assert!(
            BinaryRejectedArtifactBlocker::UnsupportedMachOX86_64Lift
                .description()
                .contains("Mach-O/x86_64")
        );
    }

    #[test]
    fn abi_provenance_reports_width_contradictions() {
        let abi = abi_provenance(BinaryFormat::Elf, Architecture::X86, Some(64));

        assert_eq!(abi.object_pointer_width_bits, Some(64));
        assert_eq!(abi.architecture_pointer_width_bits, Some(32));
        assert!(abi.has_contradictions);
        assert!(abi.diagnostics.iter().any(|diagnostic| diagnostic.contains("contradicts")));
    }

    #[test]
    fn source_mapping_debug_format_is_stable() {
        let mapping = SourceMappingInfo {
            binary_address: 0x401000,
            file: "src/main.rs".to_string(),
            line: 12,
            column: 3,
        };

        assert_eq!(
            format!("{mapping:?}"),
            "SourceMappingInfo { binary_address: 4198400, file: \"src/main.rs\", line: 12, column: 3 }"
        );
    }

    #[test]
    fn loaded_image_diagnostics_gate_unknown_permissions_and_overlaps() {
        let segments = vec![
            SegmentInfo {
                name: Some("PT_LOAD[0]".to_string()),
                virtual_address: 0x1000,
                virtual_size: 0x100,
                file_offset: Some(0),
                file_size: Some(0x100),
                permissions: BinarySegmentPermissions::default(),
            },
            SegmentInfo {
                name: Some("PT_LOAD[1]".to_string()),
                virtual_address: 0x1080,
                virtual_size: 0x80,
                file_offset: Some(0x100),
                file_size: Some(0x80),
                permissions: BinarySegmentPermissions { read: true, write: false, execute: true },
            },
        ];
        let mut diagnostics = Vec::new();

        push_loaded_image_diagnostics(&mut diagnostics, &segments);

        assert_eq!(diagnostics.len(), 2);
        assert_eq!(diagnostics[0].source, "loader segment permissions");
        assert!(diagnostics[0].message.contains("no recovered read/write/execute"));
        assert_eq!(diagnostics[1].source, "loader segment provenance");
        assert!(diagnostics[1].message.contains("overlap with distinct permissions"));
    }

    #[test]
    fn identity_sha256_matches_known_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn test_parse_binary_auto_detect_elf() {
        // Reuse the ELF test binary builder from the elf module
        let data = build_test_elf();
        let info = parse_binary(&data).expect("should parse ELF via auto-detect");

        assert_eq!(info.format, BinaryFormat::Elf);
        assert_eq!(info.architecture, Architecture::X86_64);
        assert_eq!(info.entry_point, Some(0x400000));
        assert!(info.build_id().is_none());
        assert_eq!(info.abi().calling_convention.as_deref(), Some("SysV64"));
        assert!(!info.abi().has_contradictions);
        assert_eq!(info.type_provenance().status, TypeProvenanceStatus::Unavailable);
        assert_eq!(info.debug_source().status, DebugSourceProvenanceStatus::Unavailable);
        assert!(info.source_mappings().is_empty());
        assert!(info.exact_source_mapping(0x400000).is_none());
        assert!(info.metadata_diagnostics().is_empty());

        let segment = info
            .segment_containing_va(0x400000)
            .expect("entry point should be in a loader segment");
        assert_eq!(segment.name.as_deref(), Some("PT_LOAD[0]"));
        assert!(segment.permissions.read);
        assert!(!segment.permissions.write);
        assert!(segment.permissions.execute);

        // Should have function symbols
        let funcs: Vec<_> = info.function_symbols().collect();
        assert_eq!(funcs.len(), 2);
        assert!(funcs.iter().any(|s| s.name == "_start"));
        assert!(funcs.iter().any(|s| s.name == "main"));
    }

    #[test]
    fn identity_elf_without_loader_build_id_fails_proof_grade_binding() {
        let data = build_test_elf();
        let parsed =
            parse_binary_with_identity(&data).expect("should parse ELF and artifact identity");

        assert_eq!(parsed.identity.schema_version, 1);
        assert_eq!(parsed.identity.format, "elf");
        assert_eq!(parsed.identity.architecture, "x86_64");
        assert_eq!(parsed.identity.artifact.algorithm, "sha256");
        assert_eq!(parsed.identity.artifact.value, sha256_hex(&data));
        assert_eq!(parsed.identity.artifact_size, data.len() as u64);
        assert_eq!(parsed.identity.selected_image.file_offset, 0);
        assert_eq!(parsed.identity.selected_image.file_size, data.len() as u64);
        assert_eq!(parsed.identity.selected_image.sha256, sha256_hex(&data));
        assert_eq!(parsed.identity.loader_build_id, None);
        assert!(!parsed.identity.is_proof_grade_bindable());
        assert!(parsed.identity.proof_grade_identity_blockers().iter().any(|blocker| {
            blocker.contains("missing loader build-id/UUID/timestamp identity")
        }));
    }

    #[test]
    fn identity_macho_uuid_serializes_for_certificate_replay_binding() {
        let data = build_test_macho();
        let parsed =
            parse_binary_with_identity(&data).expect("should parse Mach-O and artifact identity");

        assert_eq!(
            parsed.binary.build_id(),
            Some("macho-uuid:00112233-4455-6677-8899-aabbccddeeff")
        );
        assert_eq!(
            parsed.identity.loader_build_id.as_deref(),
            Some("macho-uuid:00112233-4455-6677-8899-aabbccddeeff")
        );
        assert_eq!(parsed.identity.format, "macho");
        assert_eq!(parsed.identity.architecture, "aarch64");
        assert_eq!(parsed.identity.selected_image.file_offset, 0);
        assert_eq!(parsed.identity.selected_image.file_size, data.len() as u64);
        assert!(parsed.identity.is_proof_grade_bindable());

        let json = parsed.identity.to_canonical_json();
        assert!(json.starts_with(
            "{\"schema_version\":1,\"format\":\"macho\",\"architecture\":\"aarch64\""
        ));
        assert!(json.contains("\"artifact\":{\"algorithm\":\"sha256\",\"value\":\""));
        assert!(
            json.contains(
                "\"loader_build_id\":\"macho-uuid:00112233-4455-6677-8899-aabbccddeeff\""
            )
        );
    }

    #[test]
    fn identity_fat_macho_hashes_selected_slice_and_root_artifact_separately() {
        use crate::constants::{CPU_SUBTYPE_ARM64_ALL, CPU_TYPE_ARM64};

        let thin = build_test_macho();
        let data =
            build_fat_macho_with_single_slice(CPU_TYPE_ARM64, CPU_SUBTYPE_ARM64_ALL, 0x1000, &thin);
        let parsed =
            parse_binary_with_identity(&data).expect("should parse fat Mach-O and identity");

        assert_eq!(parsed.identity.format, "fat-macho");
        assert_eq!(parsed.identity.architecture, "aarch64");
        assert_eq!(parsed.identity.artifact.value, sha256_hex(&data));
        assert_eq!(parsed.identity.selected_image.file_offset, 0x1000);
        assert_eq!(parsed.identity.selected_image.file_size, thin.len() as u64);
        assert_eq!(parsed.identity.selected_image.sha256, sha256_hex(&thin));
        assert_ne!(parsed.identity.artifact.value, parsed.identity.selected_image.sha256);
        assert_eq!(
            parsed.identity.loader_build_id.as_deref(),
            Some("macho-uuid:00112233-4455-6677-8899-aabbccddeeff")
        );
        assert!(parsed.identity.is_proof_grade_bindable());
    }

    #[test]
    fn identity_rejects_noncanonical_digest_rows_for_proof_grade_binding() {
        let data = build_test_macho();
        let mut identity =
            parse_binary_with_identity(&data).expect("should parse identity").identity;
        identity.selected_image.sha256 = identity.selected_image.sha256.to_ascii_uppercase();

        assert!(!identity.is_proof_grade_bindable());
        assert!(
            identity
                .proof_grade_identity_blockers()
                .iter()
                .any(|blocker| { blocker == "selected image digest is not canonical SHA-256 hex" })
        );
    }

    #[test]
    fn rejected_artifact_evidence_blocks_pe32_i386_lift_boundary() {
        let data = build_test_pe32_i386();

        let legacy = parse_binary_with_identity(&data).expect("PE32/i386 metadata should parse");
        assert_eq!(legacy.binary.format, BinaryFormat::Pe);
        assert_eq!(legacy.binary.architecture, Architecture::X86);
        assert_eq!(legacy.binary.abi().object_pointer_width_bits, Some(32));
        assert!(legacy.identity.proof_grade_identity_blockers().iter().any(|blocker| {
            blocker == BinaryRejectedArtifactBlocker::UnsupportedPeI386WordSize.id()
        }));
        assert!(!legacy.identity.is_proof_grade_bindable());

        let evidence = parse_binary_with_rejection_evidence(&data)
            .expect("PE32/i386 rejection evidence should be metadata-safe");
        assert!(evidence.is_rejected());
        let rejection = evidence.rejected().expect("PE32/i386 must be rejected");

        assert_eq!(rejection.schema_version, 1);
        assert_eq!(rejection.format, "pe-coff");
        assert_eq!(rejection.architecture, "x86");
        assert_eq!(rejection.endianness, BinaryEndianness::Little);
        assert_eq!(rejection.word_size_bits, Some(32));
        assert_eq!(rejection.metadata_path(), "pe-coff/x86/little/32");
        assert_eq!(rejection.blocker, BinaryRejectedArtifactBlocker::UnsupportedPeI386WordSize);
        assert_eq!(rejection.blocker.id(), "unsupported_pe_i386_word_size");
        assert_eq!(rejection.artifact.algorithm, "sha256");
        assert_eq!(rejection.artifact.value, sha256_hex(&data));
        assert_eq!(rejection.artifact_size, data.len() as u64);
        assert_eq!(rejection.selected_image.file_offset, 0);
        assert_eq!(rejection.selected_image.file_size, data.len() as u64);
        assert_eq!(rejection.selected_image.sha256, sha256_hex(&data));
        assert_eq!(
            rejection.loader_build_id.as_deref(),
            Some("pe-timestamp:5f000000;checksum:00000000")
        );
        assert!(rejection.message.contains("parser metadata boundary"));
        assert!(rejection.message.contains("lifting not attempted"));
        assert!(!rejection.is_proof_grade_bindable());
        assert_eq!(rejection.proof_grade_identity_blockers()[0], "unsupported_pe_i386_word_size");
        assert!(rejection.metadata_diagnostics.iter().any(|diagnostic| {
            diagnostic.source == "artifact rejection"
                && diagnostic.message.contains("unsupported_pe_i386_word_size")
        }));
    }

    #[test]
    fn rejected_artifact_evidence_blocks_macho_x86_64_lift_boundary() {
        let data = build_test_macho_x86_64();

        let legacy =
            parse_binary_with_identity(&data).expect("Mach-O/x86_64 metadata should parse");
        assert_eq!(legacy.binary.format, BinaryFormat::MachO);
        assert_eq!(legacy.binary.architecture, Architecture::X86_64);
        assert_eq!(legacy.binary.abi().object_pointer_width_bits, Some(64));
        assert_eq!(
            legacy.identity.loader_build_id.as_deref(),
            Some("macho-uuid:00112233-4455-6677-8899-aabbccddeeff")
        );
        assert!(legacy.identity.proof_grade_identity_blockers().iter().any(|blocker| {
            blocker == BinaryRejectedArtifactBlocker::UnsupportedMachOX86_64Lift.id()
        }));
        assert!(!legacy.identity.is_proof_grade_bindable());

        let evidence = parse_binary_with_rejection_evidence(&data)
            .expect("Mach-O/x86_64 rejection evidence should be metadata-safe");
        assert!(evidence.is_rejected());
        let rejection = evidence.rejected().expect("Mach-O/x86_64 must be rejected");

        assert_eq!(rejection.schema_version, 1);
        assert_eq!(rejection.format, "macho");
        assert_eq!(rejection.architecture, "x86_64");
        assert_eq!(rejection.endianness, BinaryEndianness::Little);
        assert_eq!(rejection.word_size_bits, Some(64));
        assert_eq!(rejection.metadata_path(), "macho/x86_64/little/64");
        assert_eq!(rejection.blocker, BinaryRejectedArtifactBlocker::UnsupportedMachOX86_64Lift);
        assert_eq!(rejection.blocker.id(), "unsupported_macho_x86_64_lift");
        assert_eq!(rejection.artifact.algorithm, "sha256");
        assert_eq!(rejection.artifact.value, sha256_hex(&data));
        assert_eq!(rejection.artifact_size, data.len() as u64);
        assert_eq!(rejection.selected_image.file_offset, 0);
        assert_eq!(rejection.selected_image.file_size, data.len() as u64);
        assert_eq!(rejection.selected_image.sha256, sha256_hex(&data));
        assert_eq!(
            rejection.loader_build_id.as_deref(),
            Some("macho-uuid:00112233-4455-6677-8899-aabbccddeeff")
        );
        assert!(rejection.message.contains("parser metadata boundary"));
        assert!(rejection.message.contains("unsupported_macho_x86_64_lift"));
        assert!(rejection.message.contains("lifting not attempted"));
        assert!(!rejection.is_proof_grade_bindable());
        assert_eq!(rejection.proof_grade_identity_blockers()[0], "unsupported_macho_x86_64_lift");
        assert!(rejection.metadata_diagnostics.iter().any(|diagnostic| {
            diagnostic.source == "artifact rejection"
                && diagnostic.message.contains("unsupported_macho_x86_64_lift")
        }));
    }

    #[test]
    fn test_parse_binary_auto_detect_elf32_i386_metadata() {
        let data = build_test_elf32_i386();
        let info = parse_binary(&data).expect("should parse ELF32/i386 via auto-detect");

        assert_eq!(info.format, BinaryFormat::Elf);
        assert_eq!(info.architecture, Architecture::X86);
        assert_eq!(info.entry_point, Some(0x0804_8000));
        assert_eq!(info.build_id(), None);
        assert_eq!(info.abi().calling_convention.as_deref(), Some("SysV32"));
        assert_eq!(info.abi().object_pointer_width_bits, Some(32));
        assert_eq!(info.abi().architecture_pointer_width_bits, Some(32));
        assert!(!info.abi().has_contradictions);
        assert_eq!(info.type_provenance().status, TypeProvenanceStatus::Unavailable);
        assert_eq!(info.debug_source().status, DebugSourceProvenanceStatus::Unavailable);
        assert!(info.source_mappings().is_empty());
        assert!(info.metadata_diagnostics().is_empty());

        let text = info
            .sections
            .iter()
            .find(|section| section.name == ".text")
            .expect("should expose executable .text section");
        assert_eq!(text.virtual_address, 0x0804_8000);
        assert_eq!(text.data, [0x55, 0x89, 0xe5, 0xc3]);
        assert!(text.executable);
        assert_eq!(info.bytes_at_va(0x0804_8000, 4), Some(&[0x55, 0x89, 0xe5, 0xc3][..]));
        assert_eq!(info.bytes_at_va(0x0804_8002, 2), Some(&[0xe5, 0xc3][..]));

        let segment = info
            .segment_containing_va(0x0804_8000)
            .expect("entry point should be in a loader segment");
        assert_eq!(segment.name.as_deref(), Some("PT_LOAD[0]"));
        assert_eq!(segment.virtual_address, 0x0804_8000);
        assert_eq!(segment.virtual_size, 0x80);
        assert_eq!(segment.file_offset, Some(0x100));
        assert_eq!(segment.file_size, Some(0x80));
        assert!(segment.permissions.read);
        assert!(!segment.permissions.write);
        assert!(segment.permissions.execute);

        let start = info.find_symbol("_start").expect("should find _start");
        assert_eq!(start.address, 0x0804_8000);
        assert_eq!(start.size, 4);
        assert!(start.is_function);

        let helper = info.find_symbol("helper").expect("should find helper");
        assert_eq!(helper.address, 0x0804_8002);
        assert_eq!(helper.size, 2);
        assert!(helper.is_function);

        let funcs: Vec<_> = info.function_symbols().collect();
        assert_eq!(funcs.len(), 2);
    }

    #[test]
    fn test_parse_binary_auto_detect_macho() {
        let data = build_test_macho();
        let info = parse_binary(&data).expect("should parse Mach-O via auto-detect");

        assert_eq!(info.format, BinaryFormat::MachO);
        assert_eq!(info.architecture, Architecture::AArch64);
        assert!(info.entry_point.is_some());
        assert_eq!(info.build_id(), Some("macho-uuid:00112233-4455-6677-8899-aabbccddeeff"));
        assert_eq!(info.abi().calling_convention.as_deref(), Some("AAPCS64"));
        assert_eq!(info.type_provenance().status, TypeProvenanceStatus::Unavailable);
        assert_eq!(info.debug_source().status, DebugSourceProvenanceStatus::Unavailable);
        assert!(info.source_mappings().is_empty());
        assert!(info.metadata_diagnostics().is_empty());

        // Should have executable sections
        assert!(!info.sections.is_empty());
        assert!(info.sections.iter().all(|s| s.executable));
        let text_segment = info
            .segments()
            .iter()
            .find(|segment| segment.name.as_deref() == Some("__TEXT"))
            .expect("should expose __TEXT segment");
        assert!(text_segment.permissions.read);
        assert!(!text_segment.permissions.write);
        assert!(text_segment.permissions.execute);

        // Should have main symbol normalized to match lifter names
        let main_sym = info.find_symbol("main");
        assert!(main_sym.is_some());
        assert!(info.find_symbol("_main").is_none());
    }

    #[test]
    fn provenance_macho_entryoff_uses_segment_fileoff_for_va() {
        let mut data = build_test_macho();
        let text_segment_fileoff = 0x100u64;
        let main_fileoff = 0x1100u64;
        let segment_fileoff_offset = 32 + 40;
        let lc_main_entryoff_offset = 32 + 152 + 24 + 8;
        data[segment_fileoff_offset..segment_fileoff_offset + 8]
            .copy_from_slice(&text_segment_fileoff.to_le_bytes());
        data[lc_main_entryoff_offset..lc_main_entryoff_offset + 8]
            .copy_from_slice(&main_fileoff.to_le_bytes());

        let info = parse_binary(&data).expect("should parse Mach-O with shifted __TEXT fileoff");

        assert_eq!(info.entry_point, Some(0x100001000));
        assert!(
            info.metadata_diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.source != "Mach-O LC_MAIN"),
            "entry point should be mapped through __TEXT file range without diagnostics"
        );
    }

    #[test]
    fn provenance_macho_unmapped_entryoff_is_withheld() {
        let mut data = build_test_macho();
        let lc_main_entryoff_offset = 32 + 152 + 24 + 8;
        data[lc_main_entryoff_offset..lc_main_entryoff_offset + 8]
            .copy_from_slice(&0x9000u64.to_le_bytes());

        let info = parse_binary(&data).expect("container should still parse");

        assert_eq!(info.entry_point, None);
        assert!(info.metadata_diagnostics().iter().any(|diagnostic| {
            diagnostic.source == "Mach-O LC_MAIN" && diagnostic.message.contains("withheld")
        }));
    }

    #[test]
    fn provenance_macho_local_text_symbol_is_function_seed() {
        let mut data = build_test_macho();
        let strtab_offset =
            data.windows(b"\0_main\0".len()).position(|window| window == b"\0_main\0").unwrap();
        let symtab_offset = strtab_offset + b"\0_main\0".len();
        let n_type_offset = symtab_offset + 4;
        data[n_type_offset] = crate::constants::N_SECT;

        let info = parse_binary(&data).expect("should parse Mach-O with local text symbol");
        let main = info.find_symbol("main").expect("should keep local text symbol");

        assert!(main.is_function);
        assert_eq!(main.address, 0x100001000);
    }

    #[test]
    fn provenance_fat_macho_offsets_are_root_file_offsets() {
        let thin = build_test_macho();
        let slice_offset = 0x1000u32;
        let data = build_fat_macho_with_single_slice(
            crate::constants::CPU_TYPE_ARM64,
            crate::constants::CPU_SUBTYPE_ARM64_ALL,
            slice_offset,
            &thin,
        );

        let info = parse_binary(&data).expect("should parse fat Mach-O via selected slice");

        assert_eq!(info.format, BinaryFormat::FatMachO);
        assert_eq!(info.architecture, Architecture::AArch64);
        assert_eq!(info.entry_point, Some(0x100001000));

        let text_segment = info
            .segments()
            .iter()
            .find(|segment| segment.name.as_deref() == Some("__TEXT"))
            .expect("should expose __TEXT segment");
        assert_eq!(text_segment.file_offset, Some(u64::from(slice_offset)));

        let text_section = info
            .sections
            .iter()
            .find(|section| section.name == "__TEXT,__text")
            .expect("should expose __TEXT,__text section");
        assert_eq!(text_section.file_offset, Some(u64::from(slice_offset) + 0x100));
    }

    #[test]
    fn provenance_fat_macho_without_supported_slice_fails_closed() {
        let thin = build_test_macho();
        let data = build_fat_macho_with_single_slice(7, 3, 0x1000, &thin); // CPU_TYPE_X86, not x86-64

        let err = parse_binary(&data).expect_err("unsupported fat slice must fail closed");

        assert!(
            matches!(err, ParseError::UnsupportedFormat(message) if message.contains("AArch64 or x86-64"))
        );
    }

    #[test]
    fn provenance_macho_truncated_text_section_fails_closed() {
        let mut data = build_test_macho();
        let segment_start = 32usize;
        let section_start = segment_start + 72;
        let section_size_offset = section_start + 40;
        data[section_size_offset..section_size_offset + 8]
            .copy_from_slice(&0x1000u64.to_le_bytes());

        let err = parse_binary(&data).expect_err("truncated section data must fail closed");

        assert!(matches!(err, ParseError::DataOutOfBounds { .. }));
    }

    #[test]
    fn test_parse_binary_auto_detect_pe() {
        let data = build_test_pe();
        let info = parse_binary(&data).expect("should parse PE via auto-detect");

        assert_eq!(info.format, BinaryFormat::Pe);
        assert_eq!(info.architecture, Architecture::X86_64);
        assert!(info.entry_point.is_some());
        assert_eq!(info.build_id(), Some("pe-timestamp:12345678;checksum:0000abcd"));
        assert_eq!(info.abi().calling_convention.as_deref(), Some("Win64"));
        assert_eq!(info.type_provenance().status, TypeProvenanceStatus::Unavailable);
        assert_eq!(info.debug_source().status, DebugSourceProvenanceStatus::Unavailable);
        assert!(info.source_mappings().is_empty());
        assert!(info.metadata_diagnostics().is_empty());

        // Should have executable section (.text)
        let text = info
            .sections
            .iter()
            .find(|s| s.name == ".text")
            .expect("should expose executable .text section");
        assert_eq!(text.file_offset, Some(0x200));
        let text_segment = info.segment_containing_va(0x140001000).expect("entry in .text");
        assert_eq!(text_segment.name.as_deref(), Some(".text"));
        assert!(text_segment.permissions.read);
        assert!(!text_segment.permissions.write);
        assert!(text_segment.permissions.execute);
    }

    #[test]
    fn test_parse_binary_unknown_format() {
        let data = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let err = parse_binary(&data).unwrap_err();
        assert!(matches!(err, ParseError::InvalidMagic(_)));
    }

    #[test]
    fn test_parse_binary_too_short() {
        let err = parse_binary(&[0x7F]).unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedEof(_)));
    }

    #[test]
    fn test_binary_info_bytes_at_va() {
        let data = build_test_macho();
        let info = parse_binary(&data).expect("should parse");

        // The __text section should have the RET instruction at its VA
        if let Some(text) = info.sections.first() {
            let bytes = info.bytes_at_va(text.virtual_address, 4);
            assert!(bytes.is_some());
            assert_eq!(bytes.unwrap().len(), 4);
        }
    }

    #[test]
    fn test_binary_info_bytes_at_va_preserves_x86_64_instruction_bytes() {
        let mut data = build_test_pe();
        let text_file_offset = 0x200usize;
        let text_va = 0x140001000u64;
        let instruction_bytes = [
            0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, // mov rax, [rsp + 0x88]
            0x48, 0x83, 0xC0, 0x05, // add rax, 5
            0xC3, // ret
        ];
        data[text_file_offset..text_file_offset + instruction_bytes.len()]
            .copy_from_slice(&instruction_bytes);

        let info = parse_binary(&data).expect("should parse PE fixture");

        assert_eq!(info.architecture, Architecture::X86_64);
        assert_eq!(
            info.bytes_at_va(text_va, instruction_bytes.len()),
            Some(instruction_bytes.as_slice())
        );
        assert_eq!(info.bytes_at_va(text_va + 8, 4), Some(&instruction_bytes[8..12]));
        assert_eq!(info.bytes_at_va(text_va, 8), Some(&instruction_bytes[..8]));
    }

    #[test]
    fn test_binary_info_bytes_at_invalid_va() {
        let data = build_test_macho();
        let info = parse_binary(&data).expect("should parse");
        assert!(info.bytes_at_va(0xDEAD_BEEF, 4).is_none());
    }

    #[test]
    fn test_architecture_name() {
        assert_eq!(Architecture::AArch64.name(), "AArch64");
        assert_eq!(Architecture::X86_64.name(), "x86-64");
        assert_eq!(Architecture::X86.name(), "x86");
        assert_eq!(Architecture::Arm.name(), "ARM");
        assert_eq!(Architecture::Unknown(0).name(), "Unknown");
    }

    #[test]
    fn test_elf_symbol_sizes() {
        let data = build_test_elf();
        let info = parse_binary(&data).expect("should parse");

        let start = info.find_symbol("_start").expect("should find _start");
        assert_eq!(start.size, 16);
        assert_eq!(start.address, 0x400000);
        assert!(start.is_function);

        let main = info.find_symbol("main").expect("should find main");
        assert_eq!(main.size, 32);
        assert_eq!(main.address, 0x400010);
        assert!(main.is_function);
    }

    #[test]
    fn test_elf_includes_dynsym_functions() {
        let data = build_test_elf_with_dynsym();
        let info = parse_binary(&data).expect("should parse ELF with dynsym");

        let puts = info.find_symbol("puts").expect("should find dynsym function");
        assert_eq!(puts.address, 0);
        assert_eq!(puts.size, 0);
        assert!(puts.is_function);
        assert!(info.metadata_diagnostics().is_empty());
    }

    #[test]
    fn test_elf_symbol_parse_failure_records_metadata_diagnostic() {
        let mut data = build_test_elf();
        let symtab_sh_link = 0xF0 + 2 * 64 + 40;
        data[symtab_sh_link..symtab_sh_link + 4].copy_from_slice(&99u32.to_le_bytes());

        let info = parse_binary(&data).expect("container should still parse");

        assert!(info.symbols.is_empty());
        assert_eq!(info.metadata_diagnostics().len(), 1);
        let diagnostic = &info.metadata_diagnostics()[0];
        assert_eq!(diagnostic.source, "ELF .symtab");
        assert!(diagnostic.message.contains("symbol string table"));
    }

    #[test]
    fn test_elf_dynsym_parse_failure_keeps_symtab_and_records_diagnostic() {
        let mut data = build_test_elf_with_dynsym();
        let dynsym_sh_link = 0x138 + 5 * 64 + 40;
        data[dynsym_sh_link..dynsym_sh_link + 4].copy_from_slice(&99u32.to_le_bytes());

        let info = parse_binary(&data).expect("container should still parse");

        assert!(info.find_symbol("_start").is_some());
        assert!(info.find_symbol("main").is_some());
        assert!(info.find_symbol("puts").is_none());
        assert_eq!(info.metadata_diagnostics().len(), 1);
        let diagnostic = &info.metadata_diagnostics()[0];
        assert_eq!(diagnostic.source, "ELF .dynsym");
        assert!(diagnostic.message.contains("symbol string table"));
    }

    #[test]
    fn test_macho_symbol_parse_failure_records_metadata_diagnostic() {
        let mut data = build_test_macho();
        let symtab_command_offset = 32 + 152;
        let stroff_offset = symtab_command_offset + 16;
        data[stroff_offset..stroff_offset + 4].copy_from_slice(&0x7FFFu32.to_le_bytes());

        let info = parse_binary(&data).expect("container should still parse");

        assert!(info.symbols.is_empty());
        assert_eq!(info.metadata_diagnostics().len(), 1);
        let diagnostic = &info.metadata_diagnostics()[0];
        assert_eq!(diagnostic.source, "Mach-O LC_SYMTAB");
        assert!(!diagnostic.message.is_empty());
    }

    #[test]
    fn test_pe_coff_symbol_addresses_are_image_vas() {
        let mut data = build_test_pe();
        add_pe_coff_function_symbol(&mut data);

        let info = parse_binary(&data).expect("should parse PE with COFF symbols");
        let sym = info.find_symbol("coff_fn").expect("should find COFF function");
        assert_eq!(sym.address, 0x140001020);
        assert!(sym.is_function);
        assert!(info.metadata_diagnostics().is_empty());
    }

    #[test]
    fn test_pe_exports_are_symbols() {
        let mut data = build_test_pe();
        add_pe_exports(&mut data);

        let info = parse_binary(&data).expect("should parse PE with exports");
        let add = info.find_symbol("AddFunc").expect("should include export");
        assert_eq!(add.address, 0x140001000);
        assert!(add.is_function);

        let sub = info.find_symbol("SubFunc").expect("should include second export");
        assert_eq!(sub.address, 0x140001010);
        assert!(sub.is_function);
        assert!(info.metadata_diagnostics().is_empty());
    }

    #[test]
    fn test_pe_coff_symbol_parse_failure_records_metadata_diagnostic() {
        let mut data = build_test_pe();
        let coff = 0x84usize;
        data[coff + 8..coff + 12].copy_from_slice(&0x700u32.to_le_bytes());
        data[coff + 12..coff + 16].copy_from_slice(&16u32.to_le_bytes());

        let info = parse_binary(&data).expect("container should still parse");

        assert!(info.symbols.is_empty());
        assert_eq!(info.metadata_diagnostics().len(), 1);
        let diagnostic = &info.metadata_diagnostics()[0];
        assert_eq!(diagnostic.source, "PE COFF symbols");
        assert!(diagnostic.message.contains("invalid symbol table"));
    }

    #[test]
    fn test_pe_export_parse_failure_records_metadata_diagnostic() {
        let mut data = build_test_pe();
        add_pe_exports(&mut data);
        let export_directory = 0x98usize + 112;
        data[export_directory..export_directory + 4].copy_from_slice(&0x5000u32.to_le_bytes());

        let info = parse_binary(&data).expect("container should still parse");

        assert!(info.symbols.is_empty());
        assert_eq!(info.metadata_diagnostics().len(), 1);
        let diagnostic = &info.metadata_diagnostics()[0];
        assert_eq!(diagnostic.source, "PE exports");
        assert!(diagnostic.message.contains("could not be resolved"));
    }

    // --- Test binary builders (copied from format-specific modules) ---

    /// Build a minimal valid ELF64 binary for testing.
    fn build_test_elf() -> Vec<u8> {
        let mut buf = Vec::new();

        let shstrtab = b"\0.shstrtab\0.symtab\0.strtab\0";
        let strtab = b"\0_start\0main\0";

        let phdr_off: u64 = 0x40;
        let shstrtab_off: u64 = 0x78;
        let strtab_off: u64 = 0x98;
        let symtab_off: u64 = 0xA8;
        let shdr_off: u64 = 0xF0;

        // ELF Header
        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']);
        buf.push(2); // ELFCLASS64
        buf.push(1); // ELFDATA2LSB
        buf.push(1); // EV_CURRENT
        buf.push(0); // OS/ABI
        buf.extend_from_slice(&[0u8; 8]);
        buf.extend_from_slice(&2u16.to_le_bytes()); // ET_EXEC
        buf.extend_from_slice(&0x3Eu16.to_le_bytes()); // EM_X86_64
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&0x400000u64.to_le_bytes());
        buf.extend_from_slice(&phdr_off.to_le_bytes());
        buf.extend_from_slice(&shdr_off.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&56u16.to_le_bytes());
        buf.extend_from_slice(&1u16.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&4u16.to_le_bytes());
        buf.extend_from_slice(&1u16.to_le_bytes());

        // Program header
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&5u32.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&0x400000u64.to_le_bytes());
        buf.extend_from_slice(&0x400000u64.to_le_bytes());
        buf.extend_from_slice(&0x200u64.to_le_bytes());
        buf.extend_from_slice(&0x200u64.to_le_bytes());
        buf.extend_from_slice(&0x1000u64.to_le_bytes());

        buf.extend_from_slice(shstrtab);
        while buf.len() < 0x98 {
            buf.push(0);
        }
        buf.extend_from_slice(strtab);
        while buf.len() < 0xA8 {
            buf.push(0);
        }

        // Symbols
        // Null symbol
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.push(0);
        buf.push(0);
        buf.extend_from_slice(&0u16.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        // _start
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.push((1 << 4) | 2);
        buf.push(0);
        buf.extend_from_slice(&1u16.to_le_bytes());
        buf.extend_from_slice(&0x400000u64.to_le_bytes());
        buf.extend_from_slice(&16u64.to_le_bytes());
        // main
        buf.extend_from_slice(&8u32.to_le_bytes());
        buf.push((1 << 4) | 2);
        buf.push(0);
        buf.extend_from_slice(&1u16.to_le_bytes());
        buf.extend_from_slice(&0x400010u64.to_le_bytes());
        buf.extend_from_slice(&32u64.to_le_bytes());

        // Section headers
        write_elf_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
        write_elf_shdr(&mut buf, 1, 3, 0, 0, shstrtab_off, shstrtab.len() as u64, 0, 0, 1, 0);
        write_elf_shdr(&mut buf, 11, 2, 0, 0, symtab_off, 72, 3, 1, 8, 24);
        write_elf_shdr(&mut buf, 19, 3, 0, 0, strtab_off, strtab.len() as u64, 0, 0, 1, 0);

        buf
    }

    /// Build an ELF64 binary with both .symtab and .dynsym.
    fn build_test_elf_with_dynsym() -> Vec<u8> {
        let mut buf = Vec::new();

        let shstrtab = b"\0.shstrtab\0.symtab\0.strtab\0.dynstr\0.dynsym\0";
        let strtab = b"\0_start\0main\0";
        let dynstr = b"\0puts\0";

        let phdr_off: u64 = 0x40;
        let shstrtab_off: u64 = 0x78;
        let strtab_off: u64 = 0xA8;
        let symtab_off: u64 = 0xB8;
        let dynstr_off: u64 = 0x100;
        let dynsym_off: u64 = 0x108;
        let shdr_off: u64 = 0x138;

        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']);
        buf.push(2);
        buf.push(1);
        buf.push(1);
        buf.push(0);
        buf.extend_from_slice(&[0u8; 8]);
        buf.extend_from_slice(&2u16.to_le_bytes());
        buf.extend_from_slice(&0x3Eu16.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&0x400000u64.to_le_bytes());
        buf.extend_from_slice(&phdr_off.to_le_bytes());
        buf.extend_from_slice(&shdr_off.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&56u16.to_le_bytes());
        buf.extend_from_slice(&1u16.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&6u16.to_le_bytes());
        buf.extend_from_slice(&1u16.to_le_bytes());

        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&5u32.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&0x400000u64.to_le_bytes());
        buf.extend_from_slice(&0x400000u64.to_le_bytes());
        buf.extend_from_slice(&0x200u64.to_le_bytes());
        buf.extend_from_slice(&0x200u64.to_le_bytes());
        buf.extend_from_slice(&0x1000u64.to_le_bytes());

        buf.extend_from_slice(shstrtab);
        while buf.len() < strtab_off as usize {
            buf.push(0);
        }
        buf.extend_from_slice(strtab);
        while buf.len() < symtab_off as usize {
            buf.push(0);
        }

        write_elf_sym(&mut buf, 0, 0, 0, 0, 0);
        write_elf_sym(&mut buf, 1, (1 << 4) | 2, 1, 0x400000, 16);
        write_elf_sym(&mut buf, 8, (1 << 4) | 2, 1, 0x400010, 32);

        while buf.len() < dynstr_off as usize {
            buf.push(0);
        }
        buf.extend_from_slice(dynstr);
        while buf.len() < dynsym_off as usize {
            buf.push(0);
        }
        write_elf_sym(&mut buf, 0, 0, 0, 0, 0);
        write_elf_sym(&mut buf, 1, (1 << 4) | 2, 0, 0, 0);

        while buf.len() < shdr_off as usize {
            buf.push(0);
        }
        write_elf_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
        write_elf_shdr(&mut buf, 1, 3, 0, 0, shstrtab_off, shstrtab.len() as u64, 0, 0, 1, 0);
        write_elf_shdr(&mut buf, 11, 2, 0, 0, symtab_off, 72, 3, 1, 8, 24);
        write_elf_shdr(&mut buf, 19, 3, 0, 0, strtab_off, strtab.len() as u64, 0, 0, 1, 0);
        write_elf_shdr(&mut buf, 27, 3, 0, 0, dynstr_off, dynstr.len() as u64, 0, 0, 1, 0);
        write_elf_shdr(&mut buf, 35, 11, 0, 0, dynsym_off, 48, 4, 1, 8, 24);

        buf
    }

    /// Build a minimal ELF32/i386 binary with .text, one PT_LOAD, and symbols.
    fn build_test_elf32_i386() -> Vec<u8> {
        let mut buf = Vec::new();

        let text = [0x55, 0x89, 0xe5, 0xc3];
        let shstrtab = b"\0.text\0.shstrtab\0.symtab\0.strtab\0";
        let strtab = b"\0_start\0helper\0";

        let phdr_off: u32 = 0x34;
        let text_off: u32 = 0x100;
        let shstrtab_off: u32 = 0x110;
        let strtab_off: u32 = 0x140;
        let symtab_off: u32 = 0x150;
        let shdr_off: u32 = 0x180;
        let text_va: u32 = 0x0804_8000;

        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']);
        buf.push(1); // ELFCLASS32
        buf.push(1); // ELFDATA2LSB
        buf.push(1); // EV_CURRENT
        buf.push(0); // OS/ABI
        buf.extend_from_slice(&[0u8; 8]);
        buf.extend_from_slice(&2u16.to_le_bytes()); // ET_EXEC
        buf.extend_from_slice(&3u16.to_le_bytes()); // EM_386
        buf.extend_from_slice(&1u32.to_le_bytes()); // e_version
        buf.extend_from_slice(&text_va.to_le_bytes()); // e_entry
        buf.extend_from_slice(&phdr_off.to_le_bytes()); // e_phoff
        buf.extend_from_slice(&shdr_off.to_le_bytes()); // e_shoff
        buf.extend_from_slice(&0u32.to_le_bytes()); // e_flags
        buf.extend_from_slice(&52u16.to_le_bytes()); // e_ehsize
        buf.extend_from_slice(&32u16.to_le_bytes()); // e_phentsize
        buf.extend_from_slice(&1u16.to_le_bytes()); // e_phnum
        buf.extend_from_slice(&40u16.to_le_bytes()); // e_shentsize
        buf.extend_from_slice(&5u16.to_le_bytes()); // e_shnum
        buf.extend_from_slice(&2u16.to_le_bytes()); // e_shstrndx
        assert_eq!(buf.len(), 0x34);

        buf.extend_from_slice(&1u32.to_le_bytes()); // PT_LOAD
        buf.extend_from_slice(&text_off.to_le_bytes()); // p_offset
        buf.extend_from_slice(&text_va.to_le_bytes()); // p_vaddr
        buf.extend_from_slice(&text_va.to_le_bytes()); // p_paddr
        buf.extend_from_slice(&0x80u32.to_le_bytes()); // p_filesz
        buf.extend_from_slice(&0x80u32.to_le_bytes()); // p_memsz
        buf.extend_from_slice(&5u32.to_le_bytes()); // PF_R | PF_X
        buf.extend_from_slice(&0x1000u32.to_le_bytes()); // p_align
        assert_eq!(buf.len(), 0x54);

        while buf.len() < text_off as usize {
            buf.push(0);
        }
        buf.extend_from_slice(&text);

        while buf.len() < shstrtab_off as usize {
            buf.push(0);
        }
        buf.extend_from_slice(shstrtab);

        while buf.len() < strtab_off as usize {
            buf.push(0);
        }
        buf.extend_from_slice(strtab);

        while buf.len() < symtab_off as usize {
            buf.push(0);
        }
        write_elf32_sym(&mut buf, 0, 0, 0, 0, 0);
        write_elf32_sym(&mut buf, 1, (1 << 4) | 2, 1, text_va, text.len() as u32);
        write_elf32_sym(&mut buf, 8, (1 << 4) | 2, 1, text_va + 2, 2);

        while buf.len() < shdr_off as usize {
            buf.push(0);
        }
        write_elf32_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
        write_elf32_shdr(&mut buf, 1, 1, 0x6, text_va, text_off, text.len() as u32, 0, 0, 16, 0);
        write_elf32_shdr(&mut buf, 7, 3, 0, 0, shstrtab_off, shstrtab.len() as u32, 0, 0, 1, 0);
        write_elf32_shdr(&mut buf, 17, 2, 0, 0, symtab_off, 48, 4, 1, 4, 16);
        write_elf32_shdr(&mut buf, 25, 3, 0, 0, strtab_off, strtab.len() as u32, 0, 0, 1, 0);

        buf
    }

    fn write_elf32_sym(buf: &mut Vec<u8>, name: u32, info: u8, shndx: u16, value: u32, size: u32) {
        buf.extend_from_slice(&name.to_le_bytes());
        buf.extend_from_slice(&value.to_le_bytes());
        buf.extend_from_slice(&size.to_le_bytes());
        buf.push(info);
        buf.push(0);
        buf.extend_from_slice(&shndx.to_le_bytes());
    }

    #[allow(clippy::too_many_arguments)]
    fn write_elf32_shdr(
        buf: &mut Vec<u8>,
        name: u32,
        typ: u32,
        flags: u32,
        addr: u32,
        offset: u32,
        size: u32,
        link: u32,
        info: u32,
        align: u32,
        entsize: u32,
    ) {
        buf.extend_from_slice(&name.to_le_bytes());
        buf.extend_from_slice(&typ.to_le_bytes());
        buf.extend_from_slice(&flags.to_le_bytes());
        buf.extend_from_slice(&addr.to_le_bytes());
        buf.extend_from_slice(&offset.to_le_bytes());
        buf.extend_from_slice(&size.to_le_bytes());
        buf.extend_from_slice(&link.to_le_bytes());
        buf.extend_from_slice(&info.to_le_bytes());
        buf.extend_from_slice(&align.to_le_bytes());
        buf.extend_from_slice(&entsize.to_le_bytes());
    }

    fn write_elf_sym(buf: &mut Vec<u8>, name: u32, info: u8, shndx: u16, value: u64, size: u64) {
        buf.extend_from_slice(&name.to_le_bytes());
        buf.push(info);
        buf.push(0);
        buf.extend_from_slice(&shndx.to_le_bytes());
        buf.extend_from_slice(&value.to_le_bytes());
        buf.extend_from_slice(&size.to_le_bytes());
    }

    #[allow(clippy::too_many_arguments)]
    fn write_elf_shdr(
        buf: &mut Vec<u8>,
        name: u32,
        typ: u32,
        flags: u64,
        addr: u64,
        offset: u64,
        size: u64,
        link: u32,
        info: u32,
        align: u64,
        entsize: u64,
    ) {
        buf.extend_from_slice(&name.to_le_bytes());
        buf.extend_from_slice(&typ.to_le_bytes());
        buf.extend_from_slice(&flags.to_le_bytes());
        buf.extend_from_slice(&addr.to_le_bytes());
        buf.extend_from_slice(&offset.to_le_bytes());
        buf.extend_from_slice(&size.to_le_bytes());
        buf.extend_from_slice(&link.to_le_bytes());
        buf.extend_from_slice(&info.to_le_bytes());
        buf.extend_from_slice(&align.to_le_bytes());
        buf.extend_from_slice(&entsize.to_le_bytes());
    }

    /// Build a minimal Mach-O binary for testing.
    fn build_test_macho() -> Vec<u8> {
        use crate::constants::*;

        let mut buf = Vec::new();

        // Mach-O header (32 bytes)
        buf.extend_from_slice(&MH_MAGIC_64.to_le_bytes());
        buf.extend_from_slice(&(CPU_TYPE_ARM64 as u32).to_le_bytes());
        buf.extend_from_slice(&(CPU_SUBTYPE_ARM64_ALL as u32).to_le_bytes());
        buf.extend_from_slice(&MH_EXECUTE.to_le_bytes());
        buf.extend_from_slice(&4u32.to_le_bytes()); // ncmds: segment + symtab + main + uuid

        let sizeofcmds_offset = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes()); // placeholder
        buf.extend_from_slice(&0u32.to_le_bytes()); // flags
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved

        let cmds_start = buf.len();

        // LC_SEGMENT_64: __TEXT with __text section
        let segment_start = buf.len();
        buf.extend_from_slice(&LC_SEGMENT_64.to_le_bytes());
        let seg_cmdsize_offset = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes());

        let mut segname = [0u8; 16];
        segname[..6].copy_from_slice(b"__TEXT");
        buf.extend_from_slice(&segname);

        buf.extend_from_slice(&0x100000000u64.to_le_bytes());
        buf.extend_from_slice(&0x4000u64.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&0x4000u64.to_le_bytes());
        buf.extend_from_slice(&7i32.to_le_bytes());
        buf.extend_from_slice(&5i32.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());

        let mut sectname = [0u8; 16];
        sectname[..6].copy_from_slice(b"__text");
        buf.extend_from_slice(&sectname);

        let mut sect_segname = [0u8; 16];
        sect_segname[..6].copy_from_slice(b"__TEXT");
        buf.extend_from_slice(&sect_segname);

        buf.extend_from_slice(&0x100001000u64.to_le_bytes());
        buf.extend_from_slice(&4u64.to_le_bytes());
        let sect_offset_pos = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&2u32.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&(S_ATTR_PURE_INSTRUCTIONS | S_REGULAR).to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());

        let segment_end = buf.len();
        let seg_cmdsize = (segment_end - segment_start) as u32;
        buf[seg_cmdsize_offset..seg_cmdsize_offset + 4].copy_from_slice(&seg_cmdsize.to_le_bytes());

        // LC_SYMTAB
        buf.extend_from_slice(&LC_SYMTAB.to_le_bytes());
        buf.extend_from_slice(&24u32.to_le_bytes());
        let symoff_pos = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes());
        let stroff_pos = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&7u32.to_le_bytes());

        // LC_MAIN
        buf.extend_from_slice(&LC_MAIN.to_le_bytes());
        buf.extend_from_slice(&24u32.to_le_bytes());
        buf.extend_from_slice(&0x1000u64.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());

        // LC_UUID
        buf.extend_from_slice(&LC_UUID.to_le_bytes());
        buf.extend_from_slice(&24u32.to_le_bytes());
        buf.extend_from_slice(&[
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff,
        ]);

        let cmds_end = buf.len();
        let sizeofcmds = (cmds_end - cmds_start) as u32;
        buf[sizeofcmds_offset..sizeofcmds_offset + 4].copy_from_slice(&sizeofcmds.to_le_bytes());

        // Section data: RET instruction
        let text_data_offset = buf.len();
        buf.extend_from_slice(&[0xC0, 0x03, 0x5F, 0xD6]);
        buf[sect_offset_pos..sect_offset_pos + 4]
            .copy_from_slice(&(text_data_offset as u32).to_le_bytes());

        // String table
        let strtab_offset = buf.len();
        buf.extend_from_slice(b"\0_main\0");
        buf[stroff_pos..stroff_pos + 4].copy_from_slice(&(strtab_offset as u32).to_le_bytes());

        // Symbol table: one nlist_64 for _main
        let symtab_offset = buf.len();
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.push(N_SECT | N_EXT);
        buf.push(1);
        buf.extend_from_slice(&0u16.to_le_bytes());
        buf.extend_from_slice(&0x100001000u64.to_le_bytes());
        buf[symoff_pos..symoff_pos + 4].copy_from_slice(&(symtab_offset as u32).to_le_bytes());

        buf
    }

    fn build_test_macho_x86_64() -> Vec<u8> {
        let mut buf = build_test_macho();
        buf[4..8].copy_from_slice(&(crate::constants::CPU_TYPE_X86_64 as u32).to_le_bytes());
        buf[8..12]
            .copy_from_slice(&(crate::constants::CPU_SUBTYPE_X86_64_ALL as u32).to_le_bytes());
        buf
    }

    /// Build a minimal PE binary for testing.
    fn build_test_pe() -> Vec<u8> {
        let mut buf = vec![0u8; 0x800];

        let pe_offset: u32 = 0x80;
        let text_rva: u32 = 0x1000;

        // DOS Header
        buf[0] = b'M';
        buf[1] = b'Z';
        buf[0x3C..0x40].copy_from_slice(&pe_offset.to_le_bytes());

        // PE Signature
        buf[0x80..0x84].copy_from_slice(&0x0000_4550u32.to_le_bytes());

        // COFF Header
        let coff = 0x84usize;
        buf[coff..coff + 2].copy_from_slice(&0x8664u16.to_le_bytes()); // AMD64
        buf[coff + 2..coff + 4].copy_from_slice(&1u16.to_le_bytes()); // 1 section
        buf[coff + 4..coff + 8].copy_from_slice(&0x1234_5678u32.to_le_bytes());
        buf[coff + 16..coff + 18].copy_from_slice(&240u16.to_le_bytes()); // opt hdr size
        buf[coff + 18..coff + 20].copy_from_slice(&0x0022u16.to_le_bytes());

        // Optional Header PE32+
        let opt = 0x98usize;
        buf[opt..opt + 2].copy_from_slice(&0x20Bu16.to_le_bytes()); // PE32+
        buf[opt + 2] = 14;
        buf[opt + 4..opt + 8].copy_from_slice(&0x200u32.to_le_bytes());
        buf[opt + 16..opt + 20].copy_from_slice(&text_rva.to_le_bytes()); // entry
        buf[opt + 20..opt + 24].copy_from_slice(&text_rva.to_le_bytes());
        buf[opt + 24..opt + 32].copy_from_slice(&0x140000000u64.to_le_bytes());
        buf[opt + 32..opt + 36].copy_from_slice(&0x1000u32.to_le_bytes());
        buf[opt + 36..opt + 40].copy_from_slice(&0x200u32.to_le_bytes());
        buf[opt + 40..opt + 42].copy_from_slice(&6u16.to_le_bytes());
        buf[opt + 48..opt + 50].copy_from_slice(&6u16.to_le_bytes());
        buf[opt + 56..opt + 60].copy_from_slice(&0x4000u32.to_le_bytes());
        buf[opt + 60..opt + 64].copy_from_slice(&0x200u32.to_le_bytes());
        buf[opt + 64..opt + 68].copy_from_slice(&0xABCDu32.to_le_bytes());
        buf[opt + 68..opt + 70].copy_from_slice(&3u16.to_le_bytes());
        buf[opt + 70..opt + 72].copy_from_slice(&0x8160u16.to_le_bytes());
        buf[opt + 72..opt + 80].copy_from_slice(&0x100000u64.to_le_bytes());
        buf[opt + 80..opt + 88].copy_from_slice(&0x1000u64.to_le_bytes());
        buf[opt + 88..opt + 96].copy_from_slice(&0x100000u64.to_le_bytes());
        buf[opt + 96..opt + 104].copy_from_slice(&0x1000u64.to_le_bytes());
        buf[opt + 108..opt + 112].copy_from_slice(&16u32.to_le_bytes());

        // Section header for .text at 0x188
        let sh = 0x188usize;
        buf[sh..sh + 8].copy_from_slice(b".text\0\0\0");
        buf[sh + 8..sh + 12].copy_from_slice(&0x200u32.to_le_bytes());
        buf[sh + 12..sh + 16].copy_from_slice(&text_rva.to_le_bytes());
        buf[sh + 16..sh + 20].copy_from_slice(&0x200u32.to_le_bytes());
        buf[sh + 20..sh + 24].copy_from_slice(&0x200u32.to_le_bytes());
        buf[sh + 36..sh + 40].copy_from_slice(&0x6000_0020u32.to_le_bytes());

        buf
    }

    /// Build a minimal PE32/i386 binary for rejected-artifact boundary tests.
    fn build_test_pe32_i386() -> Vec<u8> {
        let mut buf = vec![0u8; 0x400];

        let pe_offset: u32 = 0x80;
        let text_rva: u32 = 0x1000;

        buf[0] = b'M';
        buf[1] = b'Z';
        buf[0x3C..0x40].copy_from_slice(&pe_offset.to_le_bytes());

        buf[0x80..0x84].copy_from_slice(&0x0000_4550u32.to_le_bytes());

        let coff = 0x84usize;
        buf[coff..coff + 2].copy_from_slice(&crate::pe::IMAGE_FILE_MACHINE_I386.to_le_bytes());
        buf[coff + 2..coff + 4].copy_from_slice(&1u16.to_le_bytes());
        buf[coff + 4..coff + 8].copy_from_slice(&0x5F00_0000u32.to_le_bytes());
        buf[coff + 16..coff + 18].copy_from_slice(&224u16.to_le_bytes());
        buf[coff + 18..coff + 20].copy_from_slice(&0x0102u16.to_le_bytes());

        let opt = 0x98usize;
        buf[opt..opt + 2].copy_from_slice(&0x010Bu16.to_le_bytes());
        buf[opt + 2] = 10;
        buf[opt + 4..opt + 8].copy_from_slice(&0x200u32.to_le_bytes());
        buf[opt + 16..opt + 20].copy_from_slice(&text_rva.to_le_bytes());
        buf[opt + 20..opt + 24].copy_from_slice(&text_rva.to_le_bytes());
        buf[opt + 24..opt + 28].copy_from_slice(&0x2000u32.to_le_bytes());
        buf[opt + 28..opt + 32].copy_from_slice(&0x0040_0000u32.to_le_bytes());
        buf[opt + 32..opt + 36].copy_from_slice(&0x1000u32.to_le_bytes());
        buf[opt + 36..opt + 40].copy_from_slice(&0x200u32.to_le_bytes());
        buf[opt + 40..opt + 42].copy_from_slice(&6u16.to_le_bytes());
        buf[opt + 48..opt + 50].copy_from_slice(&6u16.to_le_bytes());
        buf[opt + 56..opt + 60].copy_from_slice(&0x2000u32.to_le_bytes());
        buf[opt + 60..opt + 64].copy_from_slice(&0x200u32.to_le_bytes());
        buf[opt + 68..opt + 70].copy_from_slice(&2u16.to_le_bytes());
        buf[opt + 72..opt + 76].copy_from_slice(&0x100000u32.to_le_bytes());
        buf[opt + 76..opt + 80].copy_from_slice(&0x1000u32.to_le_bytes());
        buf[opt + 80..opt + 84].copy_from_slice(&0x100000u32.to_le_bytes());
        buf[opt + 84..opt + 88].copy_from_slice(&0x1000u32.to_le_bytes());
        buf[opt + 92..opt + 96].copy_from_slice(&16u32.to_le_bytes());

        let sh = 0x178usize;
        buf[sh..sh + 8].copy_from_slice(b".text\0\0\0");
        buf[sh + 8..sh + 12].copy_from_slice(&0x200u32.to_le_bytes());
        buf[sh + 12..sh + 16].copy_from_slice(&text_rva.to_le_bytes());
        buf[sh + 16..sh + 20].copy_from_slice(&0x200u32.to_le_bytes());
        buf[sh + 20..sh + 24].copy_from_slice(&0x200u32.to_le_bytes());
        buf[sh + 36..sh + 40].copy_from_slice(&0x6000_0020u32.to_le_bytes());

        buf
    }

    fn build_fat_macho_with_single_slice(
        cputype: i32,
        cpusubtype: i32,
        slice_offset: u32,
        slice: &[u8],
    ) -> Vec<u8> {
        let mut buf = Vec::new();
        buf.extend_from_slice(&crate::constants::FAT_MAGIC.to_be_bytes());
        buf.extend_from_slice(&1u32.to_be_bytes());
        buf.extend_from_slice(&cputype.to_be_bytes());
        buf.extend_from_slice(&cpusubtype.to_be_bytes());
        buf.extend_from_slice(&slice_offset.to_be_bytes());
        buf.extend_from_slice(&(slice.len() as u32).to_be_bytes());
        buf.extend_from_slice(&12u32.to_be_bytes());
        if buf.len() < slice_offset as usize {
            buf.resize(slice_offset as usize, 0);
        }
        buf.extend_from_slice(slice);
        buf
    }

    fn add_pe_coff_function_symbol(buf: &mut [u8]) {
        let coff = 0x84usize;
        let sym_off: u32 = 0x700;
        buf[coff + 8..coff + 12].copy_from_slice(&sym_off.to_le_bytes());
        buf[coff + 12..coff + 16].copy_from_slice(&1u32.to_le_bytes());

        let sym = sym_off as usize;
        buf[sym..sym + 8].copy_from_slice(b"coff_fn\0");
        buf[sym + 8..sym + 12].copy_from_slice(&0x20u32.to_le_bytes());
        buf[sym + 12..sym + 14].copy_from_slice(&1u16.to_le_bytes());
        buf[sym + 14..sym + 16].copy_from_slice(&0x20u16.to_le_bytes());
        buf[sym + 16] = 2; // IMAGE_SYM_CLASS_EXTERNAL
        buf[sym + 17] = 0;

        let strtab = sym + 18;
        buf[strtab..strtab + 4].copy_from_slice(&4u32.to_le_bytes());
    }

    fn add_pe_exports(buf: &mut [u8]) {
        let rdata_rva: u32 = 0x2000;
        let rdata_file_off: u32 = 0x400;

        let coff = 0x84usize;
        buf[coff + 2..coff + 4].copy_from_slice(&2u16.to_le_bytes());

        let dd = 0x98usize + 112;
        buf[dd..dd + 4].copy_from_slice(&rdata_rva.to_le_bytes());
        buf[dd + 4..dd + 8].copy_from_slice(&0x80u32.to_le_bytes());

        let sh = 0x188usize + 40;
        buf[sh..sh + 8].copy_from_slice(b".rdata\0\0");
        buf[sh + 8..sh + 12].copy_from_slice(&0x200u32.to_le_bytes());
        buf[sh + 12..sh + 16].copy_from_slice(&rdata_rva.to_le_bytes());
        buf[sh + 16..sh + 20].copy_from_slice(&0x200u32.to_le_bytes());
        buf[sh + 20..sh + 24].copy_from_slice(&rdata_file_off.to_le_bytes());
        buf[sh + 36..sh + 40].copy_from_slice(&0x4000_0040u32.to_le_bytes());

        let exp = rdata_file_off as usize;
        let dll_name_rva = rdata_rva + 0x28;
        let eat_rva = rdata_rva + 0x38;
        let names_rva = rdata_rva + 0x40;
        let ords_rva = rdata_rva + 0x48;
        let name1_rva = rdata_rva + 0x4C;
        let name2_rva = rdata_rva + 0x56;

        buf[exp + 12..exp + 16].copy_from_slice(&dll_name_rva.to_le_bytes());
        buf[exp + 16..exp + 20].copy_from_slice(&1u32.to_le_bytes());
        buf[exp + 20..exp + 24].copy_from_slice(&2u32.to_le_bytes());
        buf[exp + 24..exp + 28].copy_from_slice(&2u32.to_le_bytes());
        buf[exp + 28..exp + 32].copy_from_slice(&eat_rva.to_le_bytes());
        buf[exp + 32..exp + 36].copy_from_slice(&names_rva.to_le_bytes());
        buf[exp + 36..exp + 40].copy_from_slice(&ords_rva.to_le_bytes());

        buf[exp + 0x28..exp + 0x31].copy_from_slice(b"test.dll\0");
        buf[exp + 0x38..exp + 0x3C].copy_from_slice(&0x1000u32.to_le_bytes());
        buf[exp + 0x3C..exp + 0x40].copy_from_slice(&0x1010u32.to_le_bytes());
        buf[exp + 0x40..exp + 0x44].copy_from_slice(&name1_rva.to_le_bytes());
        buf[exp + 0x44..exp + 0x48].copy_from_slice(&name2_rva.to_le_bytes());
        buf[exp + 0x48..exp + 0x4A].copy_from_slice(&0u16.to_le_bytes());
        buf[exp + 0x4A..exp + 0x4C].copy_from_slice(&1u16.to_le_bytes());
        buf[exp + 0x4C..exp + 0x54].copy_from_slice(b"AddFunc\0");
        buf[exp + 0x56..exp + 0x5E].copy_from_slice(b"SubFunc\0");
    }
}
