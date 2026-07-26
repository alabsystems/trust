//! trust-binary-parse: Binary format parsing for Trust reverse compilation
//!
//! Parses ELF, Mach-O, PE binaries, DWARF debug info, and symbol demangling
//! from first principles. Zero external dependencies.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
// dead_code audit: crate-level suppression removed

pub(crate) mod constants;
pub(crate) mod cursor;
pub(crate) mod detect;
pub(crate) mod dwarf;
pub(crate) mod elf;
pub(crate) mod elf_relocation;
pub(crate) mod error;
pub(crate) mod header;
pub(crate) mod leb128;
pub(crate) mod load_command;
pub(crate) mod macho;
pub(crate) mod pe;
pub(crate) mod read;
pub(crate) mod relocation;
pub(crate) mod symbol;
pub(crate) mod unified;

pub use detect::{BinaryFormat, detect_format};
pub use dwarf::{
    DwarfInfo, DwarfSourceMapping, DwarfSourceMappingReport, DwarfTypeRecoveryReport, ExactLineInfo,
};
pub use elf::{
    Elf32, Elf32Header, Elf32ProgramHeader, Elf32SectionHeader, Elf32Symbol, Elf64, Elf64Header,
    Elf64ProgramHeader, Elf64SectionHeader, Elf64Symbol,
};
pub use elf_relocation::{Elf64Dyn, Elf64Rel, Elf64Rela, ResolvedRelocation};
pub use error::{DwarfError, ParseError};
pub use macho::MachO;
pub use pe::Pe;
pub use unified::{
    AbiProvenance, Architecture, BinaryArtifactDigest, BinaryArtifactEvidence,
    BinaryArtifactIdentity, BinaryEndianness, BinaryImageIdentity, BinaryInfo, BinaryParseResult,
    BinaryRejectedArtifact, BinaryRejectedArtifactBlocker, DebugSourceProvenance,
    DebugSourceProvenanceStatus, MetadataDiagnostic, SectionInfo, SegmentInfo, SourceMappingInfo,
    SymbolInfo, TypeProvenance, TypeProvenanceStatus, binary_artifact_identity, parse_binary,
    parse_binary_with_identity, parse_binary_with_rejection_evidence,
};
