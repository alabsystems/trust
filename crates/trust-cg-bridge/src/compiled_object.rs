// trust-cg-bridge/compiled_object.rs — the AArch64 Mach-O and ELF object
// readers of the call-event refinement (CER) gate (increment 5, step 5.2).
//
// WHY THIS FILE EXISTS. Under increment 5 the F1 output gate verifies THE
// OBJECT THAT SHIPS: one `trust_ir::Module` per CGU compiled by trust-cg's
// `Compiler::compile`. Before any instruction is executed the gate must know,
// from the bytes alone and independently of the compiler it checks, what the
// object contains: which bytes are code and whose code they are, which symbol
// every relocation names, and where every machine call site is. That is
// obligation O1 (object binding) and the structural half of O2 (pairing) in
// docs/design/2026-10-01-step2-inc5-real-calls-retarget.md §5. Nothing here
// trusts a section table, extent or call list the compiler reports; it re-reads
// the container.
//
// WHAT IT CHECKS (O1), each failure refusing the WHOLE object:
//   * SECTIONS: every section is classified — code (verified), data holding
//     `M_cg` globals (compared with their initializer images), zero-fill,
//     unwind metadata (`__compact_unwind`, `.eh_frame`: disclosed as
//     initially unverified pending actual CER metadata proofs), or container structure (ELF
//     symbol/string/relocation tables, the empty `.note.GNU-stack` marker).
//     Anything else refuses.
//   * EXTENTS: a function's extent is `[symbol, next symbol in the section or
//     the section end)`. On ELF it is cross-checked against `st_size` (the
//     bytes past `st_size` must be padding). Two symbols at one address, or an
//     `st_size` running into the next function, refuse.
//   * TEXT COVERAGE: every code byte lies in exactly one extent, and a byte the
//     structural walk from the entry cannot reach must be padding (`udf #0` or
//     `nop`). Literal pools (`$d` mapping symbols) and data-in-code markers
//     (a non-empty Mach-O `LC_DATA_IN_CODE`) refuse. The ONE data-in-code shape
//     read is trust-cg's dense-switch jump table (INC5.4-JUMPTABLE, step
//     5.4.1): a `br` ending exactly the measured dispatch run `cmp Xi, #k;
//     [GPR loads preserving Xi/NZCV]; b.hi; adr Xb, T;
//     ldrsw Xo, [Xb, Xi, lsl #2]; add Xt, Xb, Xo; br Xt`,
//     with no relocation on it, the `b.hi` target outside that run (a `b.hi`
//     into it makes the bound check vacuous), whose `k + 1` table entries lie
//     in the extent and each target a word of the extent outside the table. Its entries
//     become the `br`'s successors (so the case blocks and their relocations
//     are walked and consumed), its words are recorded as
//     `FunctionWindow::data_in_code` and skipped by coverage, and the function
//     is UNKNOWN — never Proven. The object still refuses when anything
//     reachable or relocated lies inside a table, or when the run is entered
//     other than by falling through its bound check. Every deviation from the
//     idiom keeps the `br` a dead end, so the table's words stay unreached and
//     refuse the object as before. On ELF the `st_size` check below runs
//     first and is unchanged.
//   * SYMBOLS: exactly one symbol per `M_cg` body, with the binding its linkage
//     and visibility dictate (Mach-O `N_EXT`/`N_PEXT`, ELF `STB_*`/`STV_*`).
//     Every defined symbol is a body or global of `M_cg`; every undefined
//     symbol is a declaration of `M_cg` or a NAMED runtime helper (a call to a
//     helper makes the caller Unknown until step 5.10). An object has at
//     most ONE symbol table: a second ELF `SHT_SYMTAB`, a second Mach-O
//     `LC_SYMTAB` or a second `LC_DYSYMTAB` refuses at parse. A relocation
//     names its symbol by index, and which of two tables a linker reads is
//     the linker's choice.
//   * ELF RELOCATION SECTION HEADERS: a `SHT_RELA` section is read only when
//     every linker applies it to its target. Its `sh_flags` must be 0 or
//     `SHF_INFO_LINK` alone, its `sh_link` must name the one symbol table, and
//     no other `SHT_RELA` section may name the same target in `sh_info`;
//     anything else refuses at parse. LLD drops a section marked
//     `SHF_EXCLUDE` before it applies relocations, and binutils'
//     `bfd_section_from_shdr` presents a section with `SHF_COMPRESSED`, or
//     whose `sh_link` is not the symbol table, as an ordinary section it does
//     not apply. LLD refuses a second relocation section for one target, and
//     binutils applies only the first (a later one is a "secondary"
//     relocation section). Reading such a section's entries would bind a
//     pointer or a call target the linked image does not have.
//   * ELF FILE AND SECTION SYMBOLS have one form each, and any other refuses
//     at parse: a FILE symbol is LOCAL in `SHN_ABS`; a SECTION symbol is
//     LOCAL, defined and has value 0. A linker resolves a relocation against
//     any symbol through its section and value, while this reader keeps FILE
//     symbols out of every inventory and names a call through a section
//     symbol by its addend alone.
//   * CALLEES BY SYMBOL: a call relocated against a symbol names its callee
//     only when the symbol is the one that opens a body of this object (at
//     its section and value, under its name) or an undefined, global,
//     non-weak declaration (on Mach-O, spelled with the `_` prefix). Any
//     other symbol that carries a body's name (debugging, FILE, one in an
//     unwind section, a second name at an address) refuses the object: a
//     linker resolves through the symbol's section and value, not its name.
//     On Mach-O an undefined symbol with a nonzero value (a common symbol)
//     and any symbol marked `N_SYMBOL_RESOLVER` refuse at parse: the first is
//     storage the linker may allocate, the second a function whose result a
//     linker may call instead of it.
//   * RELOCATIONS: the admitted kinds are Mach-O `BRANCH26`, `PAGE21`/
//     `PAGEOFF12`, `GOT_LOAD_PAGE21`/`GOT_LOAD_PAGEOFF12` and ELF `CALL26`,
//     `JUMP26`, `ADR_PREL_PG_HI21`, `ADD_ABS_LO12_NC`. Any other kind on a
//     reachable instruction makes that FUNCTION Unknown. Every relocation in a
//     code section must be CONSUMED by exactly one function — it must sit on a
//     reachable instruction of the class its kind relocates (a `bl` for a call
//     relocation, an `adrp` for a page relocation, ...). An unconsumed one
//     refuses the object. This replaces PHASE 3b's text-only comparison (V12).
//   * DATA RELOCATIONS: a relocation in a data section refuses the object,
//     with ONE admitted shape (PKG-CP, 2026-11-11; an ADMISSION, not a
//     refusal: scripts/frozen-files.txt records its exception). It is the
//     pointer of a POINTER RECORD, the image a `core::panic::Location` has: an
//     immutable, non-thread-local `M_cg` global typed as a `repr(packed(1))`
//     struct of contiguous `ptr` and `[u8; n]` fields whose initializer gives
//     each `ptr` field a `SymbolAddr` and each array its bytes. Every `ptr`
//     field must carry exactly one relocation and every relocation must sit
//     on one: an absolute 64-bit pointer (Mach-O `ARM64_RELOC_UNSIGNED` of
//     length 3, ELF `R_AARCH64_ABS64`), not pc-relative, against the LOCAL
//     symbol that is this object's definition, in initialized data (so its
//     bytes are compared), of the immutable, non-thread-local `M_cg` global
//     the initializer names, with the initializer's addend where the format
//     keeps it (in place on Mach-O, where an `ARM64_RELOC_ADDEND` entry of
//     any value, zero included, refuses at parse outside a code section;
//     `r_addend` over zero bytes on ELF). The addend must lie INSIDE the
//     target's image,
//     `0 <= addend < its length` (one past the end refuses), so the pointer
//     leads to bytes compared for its own target and to no neighbour's. The
//     record's own symbol must be LOCAL too. Neither global may share its
//     name with another global or a function of `M_cg`.
//     What the reader compared must also be what a linker keeps under the
//     pointer. So the record's section and the target's must each be ORDINARY
//     DATA by its header and define no weak symbol, the target's must be
//     read-only, and the file header's flags word must hold no bit the reader
//     does not name ([`ordinary_data`], [`defines_a_weak_symbol`],
//     [`plain_header_flags`]). A literal or merge section (Mach-O
//     `S_CSTRING_LITERALS` and the 4/8/16-byte literal types, ELF
//     `SHF_MERGE`/`SHF_STRINGS`) is split into pieces the linker merges by
//     content, and a Mach-O weak definition that another object overrides
//     takes with it a following symbol that starts no piece of its own
//     (`N_ALT_ENTRY`): either way the linked pointer leads to bytes this
//     reader never saw. A relocation to a function, an undefined or non-local
//     symbol, a section, a mutable or thread-local global, another global
//     than the one named, or anywhere the initializer has no pointer keeps
//     the whole-object refusal.
//   * UNRELOCATED BRANCHES: an unrelocated `bl`/`b` to EXACTLY the start of a
//     non-preemptible local extent is a call (a tail call, for `b`) to that
//     symbol, unless the object is Mach-O with MH_SUBSECTIONS_VIA_SYMBOLS set
//     and the extent is another symbol's: then the linker may cut the section
//     at that symbol and dead-strip or move the piece, since no relocation
//     keeps it, and the branch is Unknown. Any other branch out of the extent,
//     or into the middle of one, is Unknown.
//   * CODE SECTION HEADERS: a Mach-O `__TEXT,__text` is code only with flags
//     exactly S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS,
//     an address that is a multiple of 4 and an alignment of at least 2^2,
//     and an ELF `.text`/`.text.*` only with `sh_flags` exactly SHF_ALLOC |
//     SHF_EXECINSTR (SHF_GNU_RETAIN allowed) and a power-of-two
//     `sh_addralign` of at least 4; any other header refuses the
//     object, since a literal type or SHF_MERGE lets the linker deduplicate
//     the code by content and SHF_GROUP lets it take another object's copy.
//
// THE STRUCTURAL DECODER. Reachability and call-site discovery need the
// control-flow class of each instruction word and nothing else. It is decided
// here from the A64 encoding with no dependency on the semantic decoder the
// executor uses, so this reader stays usable (and testable) without the
// `ay-proofs` feature. It is COMPLETE for control flow: every A64 instruction
// that can transfer control lives in the "branches, exception generating and
// system instructions" group (bits 28:26 = 0b101); a word in that group the
// decoder does not recognize EXACTLY stops the walk and makes the function
// Unknown, so an unrecognized branch can never be read as a fall-through.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use sha2::{Digest, Sha256};
use trust_ir::{Constant, Linkage, Module, StructRepr, Ty, Visibility};

// ===========================================================================
// REFUSALS
// ===========================================================================

/// Why an object was refused as a whole (an O1 failure). A refused object is
/// never shipped under any policy: the gate cannot say whose bytes it holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[non_exhaustive]
pub enum ObjectRefusalKind {
    /// The container is not a well-formed 64-bit little-endian AArch64 Mach-O
    /// or ELF relocatable object, or a table runs out of bounds.
    Malformed,
    /// A section the gate cannot classify.
    UnclassifiedSection,
    /// A code byte lies in no extent, or an unreachable byte is not padding.
    UncoveredTextByte,
    /// A code-section relocation no function's verdict consumed.
    UnconsumedRelocation,
    /// Two extents overlap (an aliased address, or an ELF `st_size` running
    /// into the next function).
    OverlappingExtents,
    /// A body's symbol binding or visibility differs from its `M_cg` linkage,
    /// or (at ELF parse) a symbol lies on the wrong side of `.symtab`'s
    /// `sh_info`, the boundary between the local symbols and the others.
    BindingMismatch,
    /// A defined symbol `M_cg` does not define, an undefined symbol `M_cg` does
    /// not declare, a body with no symbol, or one with two.
    SymbolInventory,
    /// A data section whose bytes differ from the `M_cg` initializer images (or
    /// which the gate cannot compare).
    DataImage,
}

/// An O1 refusal: the kind (for tests and the closure report) and the reason.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ObjectRefusal {
    /// What class of O1 failure this is.
    pub kind: ObjectRefusalKind,
    /// A human-readable account naming the section, symbol or offset.
    pub reason: String,
}

impl ObjectRefusal {
    fn new(kind: ObjectRefusalKind, reason: impl Into<String>) -> Self {
        ObjectRefusal { kind, reason: reason.into() }
    }
}

impl std::fmt::Display for ObjectRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "object refused ({:?}): {}", self.kind, self.reason)
    }
}

impl std::error::Error for ObjectRefusal {}

fn malformed(reason: impl Into<String>) -> ObjectRefusal {
    ObjectRefusal::new(ObjectRefusalKind::Malformed, reason)
}

// ===========================================================================
// THE PARSED CONTAINER
// ===========================================================================

/// The object container format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ObjectFormat {
    /// 64-bit Mach-O (`MH_OBJECT`, `CPU_TYPE_ARM64`) — Apple targets.
    MachO,
    /// ELF64 little-endian relocatable (`ET_REL`, `EM_AARCH64`).
    Elf,
}

/// What a section holds, as far as the gate is concerned.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SectionClass {
    /// Instructions. Every byte is in exactly one function extent and verified.
    Code,
    /// Initialized data. Every byte belongs to an `M_cg` global and is compared
    /// with its initializer image.
    Data,
    /// Zero-fill data (`__bss`, `.bss`): only sizes are compared.
    ZeroFill,
    /// Unwind metadata, initially disclosed as unverified. Only a complete
    /// checked CER metadata witness may discharge that disclosure; panic=abort
    /// itself provides no exemption.
    Unwind,
    /// Container structure with no runtime bytes: ELF symbol, string and
    /// relocation tables, the null section, an EMPTY `.note.GNU-stack`.
    Structural,
}

/// The relocation kinds the reader names. Only the admitted kinds of design
/// §5 O1 are spelled out; every other raw type is [`RelocKind::Other`].
#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
    serde::Serialize,
    serde::Deserialize
)]
pub enum RelocKind {
    /// Mach-O `ARM64_RELOC_BRANCH26` (`bl` and `b`).
    Branch26,
    /// Mach-O `ARM64_RELOC_PAGE21` (`adrp`).
    Page21,
    /// Mach-O `ARM64_RELOC_PAGEOFF12` (`add`/load/store low 12 bits).
    PageOff12,
    /// Mach-O `ARM64_RELOC_GOT_LOAD_PAGE21`.
    GotLoadPage21,
    /// Mach-O `ARM64_RELOC_GOT_LOAD_PAGEOFF12`.
    GotLoadPageOff12,
    /// ELF `R_AARCH64_CALL26` (`bl`).
    Call26,
    /// ELF `R_AARCH64_JUMP26` (`b`).
    Jump26,
    /// ELF `R_AARCH64_ADR_PREL_PG_HI21` (`adrp`).
    AdrPrelPgHi21,
    /// ELF `R_AARCH64_ADD_ABS_LO12_NC` (`add`).
    AddAbsLo12Nc,
    /// Any other raw relocation type (Mach-O `r_type`, ELF `ELF64_R_TYPE`).
    Other {
        /// The raw type number.
        raw: u32,
    },
}

impl RelocKind {
    /// Whether this kind is in design §5 O1's admitted set for `format`.
    #[must_use]
    pub fn is_admitted(self, format: ObjectFormat) -> bool {
        match format {
            ObjectFormat::MachO => matches!(
                self,
                RelocKind::Branch26
                    | RelocKind::Page21
                    | RelocKind::PageOff12
                    | RelocKind::GotLoadPage21
                    | RelocKind::GotLoadPageOff12
            ),
            ObjectFormat::Elf => matches!(
                self,
                RelocKind::Call26
                    | RelocKind::Jump26
                    | RelocKind::AdrPrelPgHi21
                    | RelocKind::AddAbsLo12Nc
            ),
        }
    }

    /// A short stable name for certificates and diagnostics.
    #[must_use]
    pub fn name(self) -> String {
        match self {
            RelocKind::Branch26 => "ARM64_RELOC_BRANCH26".into(),
            RelocKind::Page21 => "ARM64_RELOC_PAGE21".into(),
            RelocKind::PageOff12 => "ARM64_RELOC_PAGEOFF12".into(),
            RelocKind::GotLoadPage21 => "ARM64_RELOC_GOT_LOAD_PAGE21".into(),
            RelocKind::GotLoadPageOff12 => "ARM64_RELOC_GOT_LOAD_PAGEOFF12".into(),
            RelocKind::Call26 => "R_AARCH64_CALL26".into(),
            RelocKind::Jump26 => "R_AARCH64_JUMP26".into(),
            RelocKind::AdrPrelPgHi21 => "R_AARCH64_ADR_PREL_PG_HI21".into(),
            RelocKind::AddAbsLo12Nc => "R_AARCH64_ADD_ABS_LO12_NC".into(),
            RelocKind::Other { raw } => format!("raw relocation type {raw}"),
        }
    }
}

/// What a relocation is resolved against.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum RelocTarget {
    /// A symbol-table entry (by index into [`CompiledObject::symbols`]).
    Symbol(usize),
    /// A section (Mach-O `r_extern = 0`: the section ordinal).
    Section(usize),
}

/// One relocation record, normalized across the two formats.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Relocation {
    /// Byte offset of the relocated location inside its section.
    pub offset: u64,
    /// The relocation kind.
    pub kind: RelocKind,
    /// What it is resolved against.
    pub target: RelocTarget,
    /// The addend (ELF `r_addend`; a Mach-O `ARM64_RELOC_ADDEND` pair).
    pub addend: i64,
    /// Mach-O `r_pcrel` (always `true` for the ELF kinds that are PC-relative).
    pub pc_relative: bool,
    /// log2 of the number of bytes the relocation writes: Mach-O `r_length`;
    /// on ELF read from the type ([`elf_relocation_length`]).
    pub length: u8,
}

/// One section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Section {
    /// Mach-O: the 1-based section ordinal symbols refer to. ELF: the section
    /// header index.
    pub index: usize,
    /// Mach-O `segname,sectname`; ELF section name.
    pub name: String,
    /// The gate's classification. `None` only for a section that refused.
    pub class: SectionClass,
    /// Section address (Mach-O `addr`; 0 for ELF relocatables).
    pub address: u64,
    /// Section size in bytes.
    pub size: u64,
    /// The section's bytes (empty for zero-fill and structural sections).
    pub bytes: Vec<u8>,
    /// Relocations applying to this section, in table order.
    pub relocations: Vec<Relocation>,
    /// The header's whole flags word as stored: Mach-O `flags` (the section
    /// type in its low byte, the `S_ATTR_*` bits above it), ELF `sh_flags`.
    /// The data-relocation admission and the verified-global listing read it
    /// ([`ordinary_data`]).
    pub flags: u64,
}

/// A symbol's binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolBinding {
    /// Visible only inside this object.
    Local,
    /// Visible to the static linker.
    Global,
    /// A weak definition or reference.
    Weak,
}

/// A symbol's visibility (Mach-O `N_PEXT` reads as `Hidden`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolVisibility {
    /// Default visibility.
    Default,
    /// Hidden (ELF `STV_HIDDEN`, Mach-O private-extern `N_PEXT`).
    Hidden,
    /// ELF `STV_PROTECTED`.
    Protected,
    /// ELF `STV_INTERNAL`.
    Internal,
}

/// What kind of entity a symbol names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolKind {
    /// A function (ELF `STT_FUNC`; a Mach-O symbol in a code section).
    Function,
    /// A data object (ELF `STT_OBJECT`; a Mach-O symbol in a data section).
    Object,
    /// ELF `STT_NOTYPE` that is not a mapping symbol.
    NoType,
    /// ELF `STT_SECTION`.
    Section,
    /// ELF `STT_FILE`.
    File,
    /// An ELF AArch64 mapping symbol (`$x`, `$d`, with optional `.n` suffix).
    Mapping {
        /// `true` for `$d` (data in a code section), `false` for `$x`.
        data: bool,
    },
    /// A Mach-O debugging (`N_STAB`) entry.
    Debug,
    /// Undefined (no section).
    Undefined,
}

/// One symbol-table entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol {
    /// Index in the object's symbol table.
    pub index: usize,
    /// The name as stored (Mach-O names keep their leading `_`).
    pub raw_name: String,
    /// The IR-level name (the Mach-O `_` prefix removed).
    pub name: String,
    /// The defining section (its [`Section::index`]), or `None` if undefined.
    pub section: Option<usize>,
    /// The symbol's offset INSIDE its section (Mach-O `n_value - addr`).
    pub value: u64,
    /// Binding.
    pub binding: SymbolBinding,
    /// Visibility.
    pub visibility: SymbolVisibility,
    /// What it names.
    pub kind: SymbolKind,
    /// ELF `st_size` (`None` on Mach-O, which records no size).
    pub size: Option<u64>,
    /// Mach-O `N_WEAK_DEF`/`N_WEAK_REF`/ELF `STB_WEAK`.
    pub weak: bool,
}

/// A parsed AArch64 relocatable object.
#[derive(Debug, Clone)]
pub struct CompiledObject {
    /// Container format.
    pub format: ObjectFormat,
    /// Every section, in table order.
    pub sections: Vec<Section>,
    /// Every symbol, in table order.
    pub symbols: Vec<Symbol>,
    /// SHA-256 of the whole object, the identity certificates bind to.
    pub sha256: [u8; 32],
    /// The file header's flags word as stored: Mach-O `mach_header_64.flags`,
    /// ELF `e_flags`. The data-relocation admission reads it
    /// ([`plain_header_flags`]), and the code walk reads its
    /// `MH_SUBSECTIONS_VIA_SYMBOLS` bit ([`subsections_via_symbols`]).
    pub header_flags: u32,
}

// --- little-endian readers ------------------------------------------------

struct Reader<'a> {
    bytes: &'a [u8],
}

impl<'a> Reader<'a> {
    fn slice(&self, offset: usize, len: usize) -> Result<&'a [u8], ObjectRefusal> {
        let end = offset
            .checked_add(len)
            .ok_or_else(|| malformed(format!("range {offset}+{len} overflows")))?;
        self.bytes
            .get(offset..end)
            .ok_or_else(|| malformed(format!("range {offset}..{end} is outside the object")))
    }
    fn u8(&self, offset: usize) -> Result<u8, ObjectRefusal> {
        Ok(self.slice(offset, 1)?[0])
    }
    fn u16(&self, offset: usize) -> Result<u16, ObjectRefusal> {
        let s = self.slice(offset, 2)?;
        Ok(u16::from_le_bytes([s[0], s[1]]))
    }
    fn u32(&self, offset: usize) -> Result<u32, ObjectRefusal> {
        let s = self.slice(offset, 4)?;
        Ok(u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
    }
    fn u64(&self, offset: usize) -> Result<u64, ObjectRefusal> {
        let s = self.slice(offset, 8)?;
        let mut a = [0u8; 8];
        a.copy_from_slice(s);
        Ok(u64::from_le_bytes(a))
    }
    fn cstr(&self, table: usize, table_size: usize, index: usize) -> Result<String, ObjectRefusal> {
        let tab = self.slice(table, table_size)?;
        let tail = tab
            .get(index..)
            .ok_or_else(|| malformed(format!("string index {index} past table end")))?;
        let end = tail
            .iter()
            .position(|b| *b == 0)
            .ok_or_else(|| malformed("unterminated string-table entry"))?;
        String::from_utf8(tail[..end].to_vec())
            .map_err(|_| malformed("non-UTF-8 string-table entry"))
    }
}

fn to_usize(v: u64, what: &str) -> Result<usize, ObjectRefusal> {
    usize::try_from(v).map_err(|_| malformed(format!("{what} {v} does not fit in usize")))
}

impl CompiledObject {
    /// Parse `bytes` as a 64-bit little-endian AArch64 Mach-O or ELF
    /// relocatable object. Every section is classified here; an unclassified
    /// one refuses ([`ObjectRefusalKind::UnclassifiedSection`]).
    pub fn parse(bytes: &[u8]) -> Result<CompiledObject, ObjectRefusal> {
        let sha256: [u8; 32] = Sha256::digest(bytes).into();
        if bytes.starts_with(&0xfeed_facfu32.to_le_bytes()) {
            parse_macho(bytes, sha256)
        } else if bytes.starts_with(b"\x7fELF") {
            parse_elf(bytes, sha256)
        } else {
            Err(malformed("neither a Mach-O 64 nor an ELF object"))
        }
    }

    /// The section with [`Section::index`] `index`.
    #[must_use]
    pub fn section(&self, index: usize) -> Option<&Section> {
        self.sections.iter().find(|s| s.index == index)
    }

    /// The SHA-256 of the object as lowercase hex.
    #[must_use]
    pub fn sha256_hex(&self) -> String {
        hex(&self.sha256)
    }

    /// The symbol a relocation names, if it names one.
    #[must_use]
    pub fn reloc_symbol(&self, reloc: &Relocation) -> Option<&Symbol> {
        match reloc.target {
            RelocTarget::Symbol(i) => self.symbols.get(i),
            RelocTarget::Section(_) => None,
        }
    }
}

/// Lowercase hex of `bytes`.
#[must_use]
pub fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write;
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

// --- Mach-O ---------------------------------------------------------------

const MH_MAGIC_64: u32 = 0xfeed_facf;
const CPU_TYPE_ARM64: u32 = 0x0100_000c;
const CPU_SUBTYPE_ARM64_ALL: u32 = 0;
const MH_OBJECT: u32 = 1;
const LC_SEGMENT_64: u32 = 0x19;
const LC_SYMTAB: u32 = 0x2;
const LC_DYSYMTAB: u32 = 0xb;
const LC_BUILD_VERSION: u32 = 0x32;
const LC_VERSION_MIN_MACOSX: u32 = 0x24;
const LC_DATA_IN_CODE: u32 = 0x29;
const LC_LINKER_OPTIMIZATION_HINT: u32 = 0x2e;
const LC_LINKER_OPTION: u32 = 0x2d;

const S_ATTR_PURE_INSTRUCTIONS: u32 = 0x8000_0000;
const S_ATTR_SOME_INSTRUCTIONS: u32 = 0x0000_0400;
const SECTION_TYPE: u32 = 0xff;
/// The one Mach-O code section flags word the reader admits: `S_REGULAR`
/// (type 0) with `S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS`.
const MACHO_CODE_FLAGS: u32 = S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS;
const S_ZEROFILL: u32 = 0x1;

const N_STAB: u8 = 0xe0;
const N_PEXT: u8 = 0x10;
const N_TYPE: u8 = 0x0e;
const N_EXT: u8 = 0x01;
const N_UNDF: u8 = 0x0;
const N_SECT: u8 = 0xe;
const N_WEAK_REF: u16 = 0x40;
const N_WEAK_DEF: u16 = 0x80;
/// `n_desc`: the symbol is a resolver whose RESULT is the callee (the Mach-O
/// form of ELF `STT_GNU_IFUNC`).
const N_SYMBOL_RESOLVER: u16 = 0x100;

/// One `section_64` header, as read.
struct RawMachOSection {
    seg: String,
    sect: String,
    addr: u64,
    size: u64,
    offset: u32,
    /// `section_64.align`, a power of two exponent: the linker keeps the
    /// section's address modulo `1 << align`.
    align: u32,
    reloff: u32,
    nreloc: u32,
    flags: u32,
}

fn parse_macho(bytes: &[u8], sha256: [u8; 32]) -> Result<CompiledObject, ObjectRefusal> {
    let r = Reader { bytes };
    if r.u32(0)? != MH_MAGIC_64 {
        return Err(malformed("bad Mach-O magic"));
    }
    if r.u32(4)? != CPU_TYPE_ARM64 {
        return Err(malformed(format!("Mach-O cputype {:#x} is not ARM64", r.u32(4)?)));
    }
    // Apple ld ignores, with only a warning, an object whose subtype is not
    // the one it links (the program then takes its definitions elsewhere):
    // only `CPU_SUBTYPE_ARM64_ALL` is read.
    if r.u32(8)? != CPU_SUBTYPE_ARM64_ALL {
        return Err(malformed(format!(
            "Mach-O cpusubtype {:#x} is not CPU_SUBTYPE_ARM64_ALL",
            r.u32(8)?
        )));
    }
    if r.u32(12)? != MH_OBJECT {
        return Err(malformed("Mach-O filetype is not MH_OBJECT"));
    }
    let ncmds = r.u32(16)? as usize;
    let header_flags = r.u32(24)?;
    let mut cmd_off = 32usize;
    let mut raw_sections: Vec<RawMachOSection> = Vec::new();
    let mut symtab: Option<(usize, usize, usize, usize)> = None;
    let mut dysymtab = false;
    for _ in 0..ncmds {
        let cmd = r.u32(cmd_off)?;
        let cmdsize = r.u32(cmd_off + 4)? as usize;
        if cmdsize < 8 {
            return Err(malformed("Mach-O load command smaller than its header"));
        }
        r.slice(cmd_off, cmdsize)?;
        match cmd {
            LC_SEGMENT_64 => {
                let nsects = r.u32(cmd_off + 64)? as usize;
                if 72 + nsects * 80 > cmdsize {
                    return Err(malformed("LC_SEGMENT_64 section table overruns the command"));
                }
                for i in 0..nsects {
                    let s = cmd_off + 72 + i * 80;
                    let sect = fixed_name(r.slice(s, 16)?);
                    let seg = fixed_name(r.slice(s + 16, 16)?);
                    let addr = r.u64(s + 32)?;
                    let size = r.u64(s + 40)?;
                    let offset = r.u32(s + 48)?;
                    let align = r.u32(s + 52)?;
                    let reloff = r.u32(s + 56)?;
                    let nreloc = r.u32(s + 60)?;
                    let flags = r.u32(s + 64)?;
                    raw_sections.push(RawMachOSection {
                        seg,
                        sect,
                        addr,
                        size,
                        offset,
                        align,
                        reloff,
                        nreloc,
                        flags,
                    });
                }
            }
            // At most one symbol table, as on ELF. A relocation names its
            // symbol by INDEX into the table, and with two tables which one a
            // linker reads is the linker's choice: keeping either would bind
            // every relocation to a symbol the linked image need not give it.
            LC_SYMTAB => {
                if symtab.is_some() {
                    return Err(malformed("more than one Mach-O symbol table (LC_SYMTAB)"));
                }
                symtab = Some((
                    r.u32(cmd_off + 8)? as usize,
                    r.u32(cmd_off + 12)? as usize,
                    r.u32(cmd_off + 16)? as usize,
                    r.u32(cmd_off + 20)? as usize,
                ));
            }
            // Data-in-code and linker-optimization-hint tables are admitted
            // only EMPTY: a non-empty one marks literal pools in text or
            // licenses the linker to rewrite verified instructions.
            LC_DATA_IN_CODE | LC_LINKER_OPTIMIZATION_HINT => {
                let datasize = r.u32(cmd_off + 12)?;
                if datasize != 0 {
                    return Err(ObjectRefusal::new(
                        ObjectRefusalKind::UnclassifiedSection,
                        format!(
                            "Mach-O load command {cmd:#x} is non-empty ({datasize} bytes): data in \
                             code or linker rewrite hints are outside what the gate verifies"
                        ),
                    ));
                }
            }
            // At most one dynamic symbol table, for the same reason. Its
            // CONTENTS are not read (the index ranges it gives the local,
            // defined and undefined symbols, and its indirect-symbol and
            // relocation tables).
            LC_DYSYMTAB => {
                if dysymtab {
                    return Err(malformed(
                        "more than one Mach-O dynamic symbol table (LC_DYSYMTAB)",
                    ));
                }
                dysymtab = true;
            }
            LC_BUILD_VERSION | LC_VERSION_MIN_MACOSX | LC_LINKER_OPTION => {}
            other => {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::UnclassifiedSection,
                    format!("unclassified Mach-O load command {other:#x}"),
                ));
            }
        }
        cmd_off += cmdsize;
    }

    // Symbols first: relocations name them by index.
    let mut symbols = Vec::new();
    if let Some((symoff, nsyms, stroff, strsize)) = symtab {
        r.slice(symoff, nsyms.checked_mul(16).ok_or_else(|| malformed("nsyms overflow"))?)?;
        for index in 0..nsyms {
            let e = symoff + index * 16;
            let strx = r.u32(e)? as usize;
            let n_type = r.u8(e + 4)?;
            let n_sect = r.u8(e + 5)? as usize;
            let n_desc = r.u16(e + 6)?;
            let n_value = r.u64(e + 8)?;
            let raw_name = r.cstr(stroff, strsize, strx)?;
            let name = raw_name.strip_prefix('_').unwrap_or(&raw_name).to_string();
            let weak = n_desc & (N_WEAK_DEF | N_WEAK_REF) != 0;
            let binding = if n_type & N_EXT == 0 {
                SymbolBinding::Local
            } else if weak {
                SymbolBinding::Weak
            } else {
                SymbolBinding::Global
            };
            let visibility = if n_type & N_PEXT != 0 {
                SymbolVisibility::Hidden
            } else {
                SymbolVisibility::Default
            };
            let (section, value, kind) = if n_type & N_STAB != 0 {
                (None, n_value, SymbolKind::Debug)
            } else {
                // An external definition whose name lacks the C prefix `_` is
                // a different linker symbol from the one the reader binds by
                // the stripped name: another object's `_name` resolves
                // elsewhere, and the definition answers to the bare name.
                if n_type & N_EXT != 0 && n_type & N_TYPE == N_SECT && !raw_name.starts_with('_') {
                    return Err(malformed(format!(
                        "external symbol `{raw_name}` is not spelled with the C prefix `_`"
                    )));
                }
                if n_desc & N_SYMBOL_RESOLVER != 0 {
                    // A linker may route a call through a stub that calls this
                    // symbol and jumps to what it returns.
                    return Err(malformed(format!(
                        "symbol `{raw_name}` is a Mach-O resolver (N_SYMBOL_RESOLVER); a call to \
                         it reaches the function the resolver returns"
                    )));
                }
                match n_type & N_TYPE {
                    // An undefined symbol with a nonzero value is a COMMON
                    // symbol, a tentative definition the linker allocates
                    // (zero-filled) when nothing else defines it.
                    N_UNDF if n_value != 0 => {
                        return Err(malformed(format!(
                            "symbol `{raw_name}` is a Mach-O common symbol (undefined with value \
                             {n_value:#x}); the linker may allocate it as zero-filled data"
                        )));
                    }
                    N_UNDF => (None, 0, SymbolKind::Undefined),
                    N_SECT => {
                        let RawMachOSection { addr, size, .. } = raw_sections.get(n_sect.wrapping_sub(1)).ok_or_else(|| {
                            malformed(format!("symbol `{raw_name}` names section {n_sect} which does not exist"))
                        })?;
                        let value = n_value.checked_sub(*addr).filter(|v| *v <= *size).ok_or_else(
                            || malformed(format!("symbol `{raw_name}` lies outside its section")),
                        )?;
                        // The kind is decided by the section's class below.
                        (Some(n_sect), value, SymbolKind::NoType)
                    }
                    other => {
                        return Err(malformed(format!(
                            "symbol `{raw_name}` has unsupported Mach-O n_type {other:#x} (absolute \
                             or indirect symbols are outside the gate)"
                        )));
                    }
                }
            };
            symbols.push(Symbol {
                index,
                raw_name,
                name,
                section,
                value,
                binding,
                visibility,
                kind,
                size: None,
                weak,
            });
        }
    }

    let mut sections = Vec::new();
    for (i, RawMachOSection { seg, sect, addr, size, offset, align, reloff, nreloc, flags }) in
        raw_sections.into_iter().enumerate()
    {
        let index = i + 1;
        let name = format!("{seg},{sect}");
        let zerofill = flags & SECTION_TYPE == S_ZEROFILL;
        let instructions = flags & (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS) != 0;
        let class = match (seg.as_str(), sect.as_str()) {
            // Exactly the flags trust-cg's writer gives `__text`: type
            // S_REGULAR and the two instruction attributes. Any other type
            // (a literal type the linker deduplicates by content, say) or
            // attribute refuses the object. Its address is a multiple of 4
            // and its alignment at least 2^2: the linker keeps a section's
            // address modulo `1 << align`, so with both every instruction
            // offset the reader checks for 4-byte alignment links on a
            // 4-byte boundary (Apple ld links `__text` at address 2 with
            // align 2^2 at an address 2 mod 4).
            ("__TEXT", "__text") if flags == MACHO_CODE_FLAGS && align >= 2 && addr % 4 == 0 => {
                SectionClass::Code
            }
            ("__LD", "__compact_unwind") | ("__TEXT", "__eh_frame") => SectionClass::Unwind,
            ("__DATA", "__bss") | ("__DATA", "__common") if zerofill => SectionClass::ZeroFill,
            ("__TEXT", "__const")
            | ("__TEXT", "__cstring")
            | ("__TEXT", "__literal4")
            | ("__TEXT", "__literal8")
            | ("__TEXT", "__literal16")
            | ("__DATA", "__data")
            | ("__DATA", "__const")
                if !zerofill && !instructions =>
            {
                SectionClass::Data
            }
            _ => {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::UnclassifiedSection,
                    format!("unclassified Mach-O section `{name}` (flags {flags:#x})"),
                ));
            }
        };
        let bytes_vec = if zerofill {
            Vec::new()
        } else {
            r.slice(offset as usize, to_usize(size, "section size")?)?.to_vec()
        };
        let mut relocations = Vec::new();
        let mut pending_addend: Option<(u64, i64)> = None;
        for k in 0..nreloc as usize {
            let e = reloff as usize + k * 8;
            let r_address = r.u32(e)?;
            if r_address & 0x8000_0000 != 0 {
                return Err(malformed(format!("scattered relocation in `{name}`")));
            }
            let w1 = r.u32(e + 4)?;
            let symbolnum = (w1 & 0x00ff_ffff) as usize;
            let pcrel = (w1 >> 24) & 1 == 1;
            let length = ((w1 >> 25) & 3) as u8;
            let is_extern = (w1 >> 27) & 1 == 1;
            let r_type = (w1 >> 28) & 0xf;
            let offset = u64::from(r_address);
            if r_type == 10 {
                // ARM64_RELOC_ADDEND: the 24-bit signed addend of the NEXT
                // relocation at the same address. It qualifies an
                // instruction's relocation, so it is read in a code section
                // only: anywhere else it refuses whatever its value (a data
                // pointer keeps its addend in place, and an entry of value
                // zero must not pass for no entry). One entry per relocation:
                // a second one before the relocation it would qualify refuses,
                // where it would otherwise replace the first unseen.
                if class != SectionClass::Code {
                    return Err(malformed(format!(
                        "ARM64_RELOC_ADDEND in `{name}`, which is not a code section"
                    )));
                }
                if pending_addend.is_some() {
                    return Err(malformed(format!(
                        "two ARM64_RELOC_ADDEND entries before one relocation in `{name}`"
                    )));
                }
                let raw = (symbolnum as i64) << 40 >> 40;
                pending_addend = Some((offset, raw));
                continue;
            }
            let kind = match r_type {
                2 => RelocKind::Branch26,
                3 => RelocKind::Page21,
                4 => RelocKind::PageOff12,
                5 => RelocKind::GotLoadPage21,
                6 => RelocKind::GotLoadPageOff12,
                raw => RelocKind::Other { raw },
            };
            let target = if is_extern {
                if symbolnum >= symbols.len() {
                    return Err(malformed(format!(
                        "relocation in `{name}` names symbol {symbolnum} of {}",
                        symbols.len()
                    )));
                }
                RelocTarget::Symbol(symbolnum)
            } else {
                RelocTarget::Section(symbolnum)
            };
            let addend = match pending_addend.take() {
                Some((at, a)) if at == offset => a,
                Some(_) => {
                    return Err(malformed(format!(
                        "ARM64_RELOC_ADDEND in `{name}` is not followed by a relocation at its address"
                    )));
                }
                None => 0,
            };
            relocations.push(Relocation {
                offset,
                kind,
                target,
                addend,
                pc_relative: pcrel,
                length,
            });
        }
        if pending_addend.is_some() {
            return Err(malformed(format!("dangling ARM64_RELOC_ADDEND in `{name}`")));
        }
        sections.push(Section {
            index,
            name,
            class,
            address: addr,
            size,
            bytes: bytes_vec,
            relocations,
            flags: u64::from(flags),
        });
    }

    // Decide each defined symbol's kind from its section's class.
    for sym in &mut symbols {
        if let Some(sect) = sym.section {
            let class = sections
                .iter()
                .find(|s| s.index == sect)
                .map(|s| s.class)
                .ok_or_else(|| malformed("symbol names a missing section"))?;
            sym.kind = match class {
                SectionClass::Code => SymbolKind::Function,
                SectionClass::Data | SectionClass::ZeroFill => SymbolKind::Object,
                SectionClass::Unwind | SectionClass::Structural => SymbolKind::NoType,
            };
        }
    }
    Ok(CompiledObject { format: ObjectFormat::MachO, sections, symbols, sha256, header_flags })
}

fn fixed_name(raw: &[u8]) -> String {
    let end = raw.iter().position(|b| *b == 0).unwrap_or(raw.len());
    String::from_utf8_lossy(&raw[..end]).into_owned()
}

// --- ELF ------------------------------------------------------------------

const EM_AARCH64: u16 = 183;
const ET_REL: u16 = 1;
const SHT_NULL: u32 = 0;
const SHT_PROGBITS: u32 = 1;
const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_RELA: u32 = 4;
const SHT_NOBITS: u32 = 8;
const SHT_REL: u32 = 9;
const SHF_WRITE: u64 = 0x1;
const SHF_ALLOC: u64 = 0x2;
const SHF_EXECINSTR: u64 = 0x4;
const SHF_GNU_RETAIN: u64 = 0x20_0000;
/// `sh_info` names a section: the only flag a relocation section may carry.
const SHF_INFO_LINK: u64 = 0x40;
const SHN_UNDEF: u16 = 0;
const SHN_ABS: u16 = 0xfff1;
const SHN_LORESERVE: u16 = 0xff00;

fn parse_elf(bytes: &[u8], sha256: [u8; 32]) -> Result<CompiledObject, ObjectRefusal> {
    let r = Reader { bytes };
    if r.slice(0, 6)? != b"\x7fELF\x02\x01" {
        return Err(malformed("not a 64-bit little-endian ELF object"));
    }
    if r.u16(16)? != ET_REL {
        return Err(malformed("ELF e_type is not ET_REL"));
    }
    if r.u16(18)? != EM_AARCH64 {
        return Err(malformed(format!("ELF e_machine {} is not EM_AARCH64", r.u16(18)?)));
    }
    let shoff = to_usize(r.u64(40)?, "e_shoff")?;
    let header_flags = r.u32(48)?;
    let shentsize = r.u16(58)? as usize;
    let shnum = r.u16(60)? as usize;
    let shstrndx = r.u16(62)? as usize;
    if shentsize < 64 || shstrndx >= shnum {
        return Err(malformed("bad ELF section-header geometry"));
    }
    r.slice(shoff, shnum * shentsize)?;
    struct Raw {
        name: String,
        sh_type: u32,
        flags: u64,
        offset: usize,
        size: u64,
        link: u32,
        info: u32,
        addralign: u64,
        entsize: u64,
    }
    let header = |i: usize| shoff + i * shentsize;
    let names_off = to_usize(r.u64(header(shstrndx) + 24)?, "shstrtab offset")?;
    let names_size = to_usize(r.u64(header(shstrndx) + 32)?, "shstrtab size")?;
    let mut raws = Vec::with_capacity(shnum);
    for i in 0..shnum {
        let h = header(i);
        raws.push(Raw {
            name: r.cstr(names_off, names_size, r.u32(h)? as usize)?,
            sh_type: r.u32(h + 4)?,
            flags: r.u64(h + 8)?,
            offset: to_usize(r.u64(h + 24)?, "sh_offset")?,
            size: r.u64(h + 32)?,
            link: r.u32(h + 40)?,
            info: r.u32(h + 44)?,
            addralign: r.u64(h + 48)?,
            entsize: r.u64(h + 56)?,
        });
    }

    // The symbol table (exactly one) and its string table.
    let symtabs: Vec<usize> = (0..shnum).filter(|i| raws[*i].sh_type == SHT_SYMTAB).collect();
    let mut symbols = Vec::new();
    if let Some(&st) = symtabs.first() {
        if symtabs.len() != 1 {
            return Err(malformed("more than one ELF symbol table"));
        }
        let s = &raws[st];
        if s.entsize != 24 || s.size % 24 != 0 {
            return Err(malformed("ELF symbol table entry size is not 24"));
        }
        let strtab = raws
            .get(s.link as usize)
            .ok_or_else(|| malformed("ELF symtab sh_link names no section"))?;
        let (str_off, str_size) = (strtab.offset, to_usize(strtab.size, "strtab size")?);
        let count = to_usize(s.size / 24, "symbol count")?;
        for index in 0..count {
            let e = s.offset + index * 24;
            let raw_name = r.cstr(str_off, str_size, r.u32(e)? as usize)?;
            let info = r.u8(e + 4)?;
            let other = r.u8(e + 5)?;
            let shndx = r.u16(e + 6)?;
            let value = r.u64(e + 8)?;
            let size = r.u64(e + 16)?;
            let bind = info >> 4;
            let typ = info & 0xf;
            let binding = match bind {
                0 => SymbolBinding::Local,
                1 => SymbolBinding::Global,
                2 => SymbolBinding::Weak,
                other => {
                    return Err(malformed(format!("ELF symbol `{raw_name}` has binding {other}")));
                }
            };
            // ELF puts every local symbol before every other one, and the
            // table's `sh_info` is the first non-local index; binutils reads a
            // global below it as local. A symbol on the wrong side of it is
            // one whose binding the linkers do not agree on.
            if (index < s.info as usize) != (binding == SymbolBinding::Local) {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::BindingMismatch,
                    format!(
                        "ELF symbol `{raw_name}` at index {index} is {binding:?}, on the wrong \
                         side of the symbol table's sh_info {}",
                        s.info
                    ),
                ));
            }
            let visibility = match other & 3 {
                0 => SymbolVisibility::Default,
                1 => SymbolVisibility::Internal,
                2 => SymbolVisibility::Hidden,
                _ => SymbolVisibility::Protected,
            };
            if shndx >= SHN_LORESERVE {
                // SHN_ABS / SHN_COMMON / SHN_XINDEX: outside the gate, except
                // the absolute FILE symbol every assembler writes: LOCAL, in
                // SHN_ABS, as the ELF spec defines STT_FILE.
                if typ == 4 && shndx == SHN_ABS && binding == SymbolBinding::Local {
                    symbols.push(Symbol {
                        index,
                        raw_name: raw_name.clone(),
                        name: raw_name,
                        section: None,
                        value,
                        binding,
                        visibility,
                        kind: SymbolKind::File,
                        size: Some(size),
                        weak: false,
                    });
                    continue;
                }
                return Err(malformed(format!(
                    "ELF symbol `{raw_name}` has special section index {shndx:#x} (absolute, common \
                     or extended symbols are outside the gate)"
                )));
            }
            // A FILE or SECTION symbol has one form (ELF gABI): FILE is LOCAL
            // in SHN_ABS (taken above); SECTION is LOCAL, defined, with value
            // 0. A linker resolves a relocation against any symbol through
            // its section and value, where the reader keeps a FILE symbol out
            // of every inventory and names a section-symbol call by its addend
            // alone, so any other form refuses.
            if typ == 4 {
                return Err(malformed(format!(
                    "ELF FILE symbol `{raw_name}` is not absolute and local (section index \
                     {shndx:#x})"
                )));
            }
            if typ == 3 && (shndx == SHN_UNDEF || binding != SymbolBinding::Local || value != 0) {
                return Err(malformed(format!(
                    "ELF SECTION symbol `{raw_name}` is not local, defined and at value 0 \
                     (section index {shndx:#x}, value {value:#x})"
                )));
            }
            let section = (shndx != SHN_UNDEF).then_some(shndx as usize);
            let kind = if index == 0 || section.is_none() {
                SymbolKind::Undefined
            } else {
                match typ {
                    0 => mapping_kind(&raw_name).unwrap_or(SymbolKind::NoType),
                    1 => SymbolKind::Object,
                    2 => SymbolKind::Function,
                    3 => SymbolKind::Section,
                    4 => SymbolKind::File,
                    other => {
                        return Err(malformed(format!(
                            "ELF symbol `{raw_name}` has unsupported type {other}"
                        )));
                    }
                }
            };
            if let Some(sect) = section {
                let sec = raws.get(sect).ok_or_else(|| {
                    malformed(format!("ELF symbol `{raw_name}` names section {sect}"))
                })?;
                if value > sec.size {
                    return Err(malformed(format!(
                        "ELF symbol `{raw_name}` lies outside its section"
                    )));
                }
            }
            symbols.push(Symbol {
                index,
                raw_name: raw_name.clone(),
                name: raw_name,
                section,
                value,
                binding,
                visibility,
                kind,
                size: Some(size),
                weak: bind == 2,
            });
        }
    }

    // Classify every section and collect relocations onto their targets.
    let mut sections: Vec<Section> = Vec::with_capacity(shnum);
    let mut relocs_for: BTreeMap<usize, Vec<Relocation>> = BTreeMap::new();
    let mut relocated_targets: BTreeSet<usize> = BTreeSet::new();
    for (i, s) in raws.iter().enumerate() {
        if s.sh_type == SHT_REL {
            return Err(ObjectRefusal::new(
                ObjectRefusalKind::UnclassifiedSection,
                format!("ELF SHT_REL section `{}` (AArch64 objects use RELA)", s.name),
            ));
        }
        if s.sh_type == SHT_RELA {
            // Read a relocation section only when every linker applies it
            // (module doc, ELF RELOCATION SECTION HEADERS).
            if s.flags & !SHF_INFO_LINK != 0 {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::UnclassifiedSection,
                    format!(
                        "ELF RELA section `{}` has sh_flags {:#x}; only SHF_INFO_LINK is read \
                         (SHF_EXCLUDE, SHF_COMPRESSED or any other bit can keep a linker \
                         from applying it)",
                        s.name, s.flags
                    ),
                ));
            }
            if symtabs.first().is_none_or(|&st| s.link as usize != st) {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::UnclassifiedSection,
                    format!(
                        "ELF RELA section `{}` has sh_link {}, which is not the symbol table \
                         (a GNU linker does not apply it)",
                        s.name, s.link
                    ),
                ));
            }
            if s.entsize != 24 || s.size % 24 != 0 {
                return Err(malformed(format!(
                    "ELF RELA section `{}` entry size is not 24",
                    s.name
                )));
            }
            let target = s.info as usize;
            if target == 0 || target >= shnum {
                return Err(malformed(format!(
                    "ELF RELA section `{}` targets section {target}",
                    s.name
                )));
            }
            if !relocated_targets.insert(target) {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::UnclassifiedSection,
                    format!(
                        "ELF RELA section `{}` is a second relocation section for section \
                         {target} (LLD refuses it; a GNU linker applies only the first)",
                        s.name
                    ),
                ));
            }
            let mut list = Vec::new();
            for k in 0..to_usize(s.size / 24, "rela count")? {
                let e = s.offset + k * 24;
                let offset = r.u64(e)?;
                let info = r.u64(e + 8)?;
                let addend = r.u64(e + 16)? as i64;
                let sym = (info >> 32) as usize;
                let raw = (info & 0xffff_ffff) as u32;
                if sym >= symbols.len() {
                    return Err(malformed(format!(
                        "ELF relocation names symbol {sym} of {}",
                        symbols.len()
                    )));
                }
                let kind = match raw {
                    283 => RelocKind::Call26,
                    282 => RelocKind::Jump26,
                    275 => RelocKind::AdrPrelPgHi21,
                    277 => RelocKind::AddAbsLo12Nc,
                    raw => RelocKind::Other { raw },
                };
                let pc_relative = matches!(
                    kind,
                    RelocKind::Call26 | RelocKind::Jump26 | RelocKind::AdrPrelPgHi21
                );
                list.push(Relocation {
                    offset,
                    kind,
                    target: RelocTarget::Symbol(sym),
                    addend,
                    pc_relative,
                    length: elf_relocation_length(raw),
                });
            }
            relocs_for.entry(target).or_default().extend(list);
        }
        let alloc = s.flags & SHF_ALLOC != 0;
        let exec = s.flags & SHF_EXECINSTR != 0;
        let class = match s.sh_type {
            SHT_NULL if i == 0 => SectionClass::Structural,
            SHT_SYMTAB | SHT_STRTAB | SHT_RELA if !alloc => SectionClass::Structural,
            SHT_PROGBITS if s.name == ".note.GNU-stack" && s.size == 0 && !alloc => {
                SectionClass::Structural
            }
            // `sh_flags` exactly SHF_ALLOC | SHF_EXECINSTR, or that with
            // SHF_GNU_RETAIN (which only keeps the section from collection):
            // SHF_MERGE would let the linker deduplicate the code by content,
            // SHF_GROUP lets it discard this copy for another object's, and
            // any other bit is one the reader does not model. Its
            // `sh_addralign` is a power of two of at least 4, so the linker
            // places it, and every instruction offset the reader checks for
            // 4-byte alignment, on a 4-byte boundary.
            SHT_PROGBITS
                if s.flags & !SHF_GNU_RETAIN == SHF_ALLOC | SHF_EXECINSTR
                    && s.addralign >= 4
                    && s.addralign.is_power_of_two()
                    && (s.name == ".text" || s.name.starts_with(".text.")) =>
            {
                SectionClass::Code
            }
            SHT_PROGBITS if alloc && !exec && s.name == ".eh_frame" => SectionClass::Unwind,
            SHT_PROGBITS
                if alloc
                    && !exec
                    && (s.name == ".data"
                        || s.name.starts_with(".data.")
                        || s.name == ".rodata"
                        || s.name.starts_with(".rodata.")) =>
            {
                SectionClass::Data
            }
            SHT_NOBITS if alloc && !exec && (s.name == ".bss" || s.name.starts_with(".bss.")) => {
                SectionClass::ZeroFill
            }
            other => {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::UnclassifiedSection,
                    format!(
                        "unclassified ELF section `{}` (type {other:#x}, flags {:#x})",
                        s.name, s.flags
                    ),
                ));
            }
        };
        let bytes_vec = match class {
            SectionClass::Code | SectionClass::Data | SectionClass::Unwind => {
                r.slice(s.offset, to_usize(s.size, "section size")?)?.to_vec()
            }
            _ => Vec::new(),
        };
        sections.push(Section {
            index: i,
            name: s.name.clone(),
            class,
            address: 0,
            size: s.size,
            bytes: bytes_vec,
            relocations: Vec::new(),
            flags: s.flags,
        });
    }
    for (target, list) in relocs_for {
        let section = sections
            .iter_mut()
            .find(|s| s.index == target)
            .ok_or_else(|| malformed("relocation section targets a missing section"))?;
        if matches!(section.class, SectionClass::Structural | SectionClass::ZeroFill) {
            return Err(malformed(format!(
                "relocations apply to `{}`, which holds no relocatable bytes",
                section.name
            )));
        }
        section.relocations.extend(list);
    }
    Ok(CompiledObject { format: ObjectFormat::Elf, sections, symbols, sha256, header_flags })
}

/// An ELF AArch64 mapping symbol (`$x`, `$d`, `$x.<n>`, `$d.<n>`).
fn mapping_kind(name: &str) -> Option<SymbolKind> {
    let (head, _) = name.split_once('.').unwrap_or((name, ""));
    match head {
        "$x" => Some(SymbolKind::Mapping { data: false }),
        "$d" => Some(SymbolKind::Mapping { data: true }),
        _ => None,
    }
}

// ===========================================================================
// THE STRUCTURAL DECODER (control-flow class of one A64 word)
// ===========================================================================

/// The control-flow class of one instruction word, as far as reachability and
/// call-site discovery need it. Targets are BYTE offsets relative to the
/// instruction (`target = pc + delta`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InsnClass {
    /// Falls through to the next word and does nothing to control flow.
    Plain,
    /// `b imm26`.
    Branch {
        /// Signed byte displacement.
        delta: i64,
    },
    /// `bl imm26`.
    BranchLink {
        /// Signed byte displacement.
        delta: i64,
    },
    /// `b.cond`, `cbz`/`cbnz`, `tbz`/`tbnz`: both the target and the next word.
    CondBranch {
        /// Signed byte displacement of the taken target.
        delta: i64,
    },
    /// `ret` (any register).
    Ret,
    /// `br xN` — an indirect jump.
    IndirectBranch,
    /// `blr xN` — an indirect call.
    IndirectCall,
    /// `brk`, `udf`, `hlt` — a trap; no successor.
    Trap,
    /// A word in the branch/exception/system group the decoder does not
    /// recognize exactly. Stops the walk; the function is Unknown.
    Unrecognized,
    /// `adrp` (a page-address materialization).
    Adrp,
    /// `add xd, xn, #imm` (64-bit, immediate) — the low half of an address.
    AddImm64,
    /// A load or store with an unsigned 12-bit scaled offset.
    LoadStoreUImm,
}

fn sext(value: u32, bits: u32) -> i64 {
    let shift = 64 - bits;
    ((u64::from(value) << shift) as i64) >> shift
}

/// Supported Mach-O BR26 relocation profile: the instruction is B/BL and its
/// displacement is the canonical zero placeholder. A named symbol/addend does
/// not erase embedded bits: Apple ld rejects them and LLD ORs them into the
/// computed displacement. Never apply this rule to resolved unrelocated flow.
pub(crate) fn macho_branch26_operand_is_canonical(word: u32) -> bool {
    matches!(word, 0x1400_0000 | 0x9400_0000)
}

/// Classify one A64 instruction word.
#[must_use]
pub fn classify_insn(word: u32) -> InsnClass {
    // `udf #imm16` (the all-zero word among them) is permanently undefined.
    if word & 0xffff_0000 == 0 {
        return InsnClass::Trap;
    }
    if word & 0x9f00_0000 == 0x9000_0000 {
        return InsnClass::Adrp;
    }
    if word & 0xff80_0000 == 0x9100_0000 {
        return InsnClass::AddImm64;
    }
    // Load/store register (unsigned immediate): bits 29:27 = 111, bit 24 = 1.
    if word & 0x3b00_0000 == 0x3900_0000 {
        return InsnClass::LoadStoreUImm;
    }
    if (word >> 26) & 0b111 != 0b101 {
        return InsnClass::Plain;
    }
    // ---- branches, exception generating and system instructions ----
    if word & 0xfc00_0000 == 0x1400_0000 {
        return InsnClass::Branch { delta: sext(word & 0x03ff_ffff, 26) * 4 };
    }
    if word & 0xfc00_0000 == 0x9400_0000 {
        return InsnClass::BranchLink { delta: sext(word & 0x03ff_ffff, 26) * 4 };
    }
    if word & 0xff00_0010 == 0x5400_0000 {
        return InsnClass::CondBranch { delta: sext((word >> 5) & 0x7ffff, 19) * 4 };
    }
    if word & 0x7e00_0000 == 0x3400_0000 {
        return InsnClass::CondBranch { delta: sext((word >> 5) & 0x7ffff, 19) * 4 };
    }
    if word & 0x7e00_0000 == 0x3600_0000 {
        return InsnClass::CondBranch { delta: sext((word >> 5) & 0x3fff, 14) * 4 };
    }
    if word & 0xffff_fc1f == 0xd65f_0000 {
        return InsnClass::Ret;
    }
    if word & 0xffff_fc1f == 0xd61f_0000 {
        return InsnClass::IndirectBranch;
    }
    if word & 0xffff_fc1f == 0xd63f_0000 {
        return InsnClass::IndirectCall;
    }
    if word & 0xffe0_001f == 0xd420_0000 || word & 0xffe0_001f == 0xd440_0000 {
        return InsnClass::Trap;
    }
    // HINT space (nop, yield, bti, pac* that do not branch ...): `d503 2xxf`.
    // Only the plain `nop` is admitted; pointer-authentication hints change
    // what a later `ret` does and are outside the gate.
    if word == NOP {
        return InsnClass::Plain;
    }
    // Barriers (dmb/dsb/isb): `d503 3xxx` with op2 in the barrier range. They
    // never transfer control; the semantic executor refuses them anyway.
    if word & 0xffff_f01f == 0xd503_301f {
        return InsnClass::Plain;
    }
    InsnClass::Unrecognized
}

/// The A64 `nop`.
pub const NOP: u32 = 0xd503_201f;

/// Whether `word` is padding an emitter may leave in an unreachable gap.
#[must_use]
pub fn is_padding(word: u32) -> bool {
    word == 0 || word == NOP
}

/// Whether every whole word of `code` is padding; a trailing partial word is not read.
#[must_use]
pub fn all_padding(code: &[u8]) -> bool {
    code.as_chunks::<4>().0.iter().all(|word| is_padding(u32::from_le_bytes(*word)))
}

// ===========================================================================
// O1 — BINDING THE OBJECT TO `M_cg`
// ===========================================================================

/// How code that refers to a co-emitted definition binds at link time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum RelocationModel {
    /// A static executable image.
    Static,
    /// A position-independent executable.
    Pie,
    /// A shared object: default-visibility external definitions are
    /// preemptible on ELF, so calls to them are External (design §4.3).
    Pic,
}

/// What `M_cg` says about one function body.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ExpectedBody {
    /// trust-ir linkage.
    pub linkage: String,
    /// trust-ir visibility.
    pub visibility: String,
    /// The binding the object must carry.
    pub binding: SymbolBinding,
    /// The visibility the object must carry.
    pub symbol_visibility: SymbolVisibility,
    /// Whether a call to it binds within this object (no interposition).
    pub non_preemptible: bool,
}

/// What `M_cg` says about one global.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectedGlobal {
    /// Whether it is defined (has an initializer or is zero-filled storage).
    pub defined: bool,
    /// The initializer image, when the gate can compute one. `None` for a
    /// defined global means the gate cannot compare it (the object refuses).
    pub image: Option<Vec<u8>>,
    /// Whether `M_cg` declares it immutable and not thread-local. `false` for
    /// a name `M_cg` gives to more than one global, or to a function too.
    pub immutable_non_tls: bool,
    /// The pointer slots of `image`, in offset order: non-empty only for a
    /// pointer record ([`pointer_record_image`]). The object must relocate
    /// each one, and may relocate nothing else in a data section.
    pub pointers: Vec<ExpectedPointer>,
    /// The symbol binding and visibility its `M_cg` linkage and visibility
    /// require ([`expected_symbol`]), or `None` for a linkage the reader does
    /// not bind: such a global is never listed as verified.
    pub symbol: Option<(SymbolBinding, SymbolVisibility)>,
}

/// One pointer slot of a pointer record's image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectedPointer {
    /// Byte offset of the 8-byte slot inside the global's image.
    pub offset: u64,
    /// The symbol `M_cg`'s initializer names there.
    pub symbol: String,
    /// The constant byte offset `M_cg` adds to that symbol's address.
    pub addend: i64,
}

/// Everything O1 binds the object against, read off `M_cg`.
#[derive(Debug, Clone)]
pub struct ObjectExpectations {
    /// Container format the target produces.
    pub format: ObjectFormat,
    /// The relocation model the object was compiled under.
    pub relocation_model: RelocationModel,
    /// Function bodies by symbol.
    pub bodies: BTreeMap<String, ExpectedBody>,
    /// Function declarations by symbol.
    pub declarations: BTreeSet<String>,
    /// Globals by symbol.
    pub globals: BTreeMap<String, ExpectedGlobal>,
}

/// Undefined symbols an emitter may reference without an `M_cg` declaration.
/// A call to one makes the caller Unknown until step 5.10 models it.
pub const RUNTIME_HELPERS: &[&str] = &[
    "memcpy",
    "memmove",
    "memset",
    "bzero",
    "abort",
    "__udivti3",
    "__divti3",
    "__umodti3",
    "__modti3",
    "__multi3",
    "__stack_chk_fail",
    "__stack_chk_guard",
];

fn linkage_name(l: Linkage) -> String {
    format!("{l:?}")
}

impl ObjectExpectations {
    /// Read the expectations off `m_cg` for `format` under `model`.
    ///
    /// Only the linkages F1 admits today are bound; any other body linkage is
    /// refused here (`Err`), so a binding the gate has not reasoned about is
    /// never silently accepted.
    pub fn from_module(
        m_cg: &Module,
        format: ObjectFormat,
        model: RelocationModel,
    ) -> Result<ObjectExpectations, ObjectRefusal> {
        let mut bodies = BTreeMap::new();
        let mut declarations = BTreeSet::new();
        // One signature per symbol: two declarations of one name must agree.
        let mut declared_sigs: BTreeMap<String, Option<&trust_ir::ty::FuncTy>> = BTreeMap::new();
        for f in &m_cg.functions {
            if f.blocks.is_empty() {
                let sig = m_cg.func_types.get(f.ty.as_usize());
                if let Some(prev) = declared_sigs.insert(f.name.clone(), sig)
                    && prev != sig
                {
                    return Err(ObjectRefusal::new(
                        ObjectRefusalKind::SymbolInventory,
                        format!("M_cg declares `{}` under two different signatures", f.name),
                    ));
                }
                declarations.insert(f.name.clone());
                continue;
            }
            let (binding, vis, non_preemptible) = match expected_symbol(
                f.linkage,
                f.visibility,
                format,
            ) {
                Some((binding, vis)) => (
                    binding,
                    vis,
                    // Mach-O two-level namespace and ELF executables bind a
                    // call to a co-emitted default definition locally; an ELF
                    // shared object may interpose it (design §4.3).
                    !(binding == SymbolBinding::Global
                        && vis == SymbolVisibility::Default
                        && format == ObjectFormat::Elf
                        && model == RelocationModel::Pic),
                ),
                None => {
                    let (linkage, visibility) = (f.linkage, f.visibility);
                    return Err(ObjectRefusal::new(
                        ObjectRefusalKind::BindingMismatch,
                        format!(
                            "body `{}` has linkage {linkage:?} / visibility {visibility:?}, which \
                             the call-event gate does not bind (fail-closed)",
                            f.name
                        ),
                    ));
                }
            };
            if bodies
                .insert(
                    f.name.clone(),
                    ExpectedBody {
                        linkage: linkage_name(f.linkage),
                        visibility: format!("{:?}", f.visibility),
                        binding,
                        symbol_visibility: vis,
                        non_preemptible,
                    },
                )
                .is_some()
            {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::SymbolInventory,
                    format!("M_cg defines `{}` twice", f.name),
                ));
            }
        }
        for name in &declarations {
            if bodies.contains_key(name) {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::SymbolInventory,
                    format!("M_cg both defines and declares `{name}`"),
                ));
            }
        }
        let mut globals = BTreeMap::new();
        // A name `M_cg` gives to two globals, or to a global and a function,
        // names neither of them: such a global is never a pointer record and
        // never a relocation's target.
        let mut names: BTreeSet<&str> = m_cg.functions.iter().map(|f| f.name.as_str()).collect();
        let repeated: BTreeSet<&str> = m_cg
            .globals
            .iter()
            .filter_map(|g| (!names.insert(g.name.as_str())).then_some(g.name.as_str()))
            .collect();
        for g in &m_cg.globals {
            let defined = g.initializer.is_some();
            let image =
                g.initializer.as_ref().and_then(|init| initializer_image(m_cg, &g.ty, init));
            let immutable_non_tls =
                !repeated.contains(g.name.as_str()) && !g.mutable && g.tls.is_none();
            let record = g
                .initializer
                .as_ref()
                .filter(|_| immutable_non_tls && image.is_none())
                .and_then(|init| pointer_record_image(m_cg, &g.ty, init, format));
            let (image, pointers) = match record {
                Some((image, pointers)) => (Some(image), pointers),
                None => (image, Vec::new()),
            };
            globals.insert(
                g.name.clone(),
                ExpectedGlobal {
                    defined,
                    image,
                    immutable_non_tls,
                    pointers,
                    symbol: expected_symbol(g.linkage, g.visibility, format),
                },
            );
        }
        Ok(ObjectExpectations { format, relocation_model: model, bodies, declarations, globals })
    }
}

/// The symbol binding and visibility an `M_cg` definition with this linkage
/// and visibility must carry in the object, or `None` for a pair the reader
/// does not bind (a function body with one refuses; a global with one is
/// never listed as verified). Internal and private definitions are local
/// symbols; external ones are global with the declared visibility, protected
/// only on ELF.
fn expected_symbol(
    linkage: Linkage,
    visibility: Visibility,
    format: ObjectFormat,
) -> Option<(SymbolBinding, SymbolVisibility)> {
    match (linkage, visibility) {
        (Linkage::Internal | Linkage::Private, _) => {
            Some((SymbolBinding::Local, SymbolVisibility::Default))
        }
        (Linkage::External, Visibility::Default) => {
            Some((SymbolBinding::Global, SymbolVisibility::Default))
        }
        (Linkage::External, Visibility::Hidden) => {
            Some((SymbolBinding::Global, SymbolVisibility::Hidden))
        }
        (Linkage::External, Visibility::Protected) if format == ObjectFormat::Elf => {
            Some((SymbolBinding::Global, SymbolVisibility::Protected))
        }
        _ => None,
    }
}

/// The little-endian byte image of a global initializer, where the gate can
/// compute it EXACTLY: integer scalars, `bool`, and byte strings. Anything
/// else is `None` (the object then refuses rather than skip the comparison).
#[must_use]
pub fn initializer_image(_m: &Module, ty: &Ty, init: &Constant) -> Option<Vec<u8>> {
    let width_bytes = |ty: &Ty| -> Option<usize> {
        Some(match ty {
            Ty::I8 | Ty::U8 | Ty::Bool => 1,
            Ty::I16 | Ty::U16 => 2,
            Ty::I32 | Ty::U32 | Ty::Char => 4,
            Ty::I64 | Ty::U64 | Ty::Isize | Ty::Usize => 8,
            Ty::I128 | Ty::U128 => 16,
            _ => return None,
        })
    };
    match init {
        Constant::Int(v) => {
            let n = width_bytes(ty)?;
            Some(v.to_le_bytes()[..n].to_vec())
        }
        Constant::U128(v) => {
            let n = width_bytes(ty)?;
            Some(v.to_le_bytes()[..n].to_vec())
        }
        Constant::Bool(b) if matches!(ty, Ty::Bool) => Some(vec![u8::from(*b)]),
        Constant::Bytes { data, .. } => Some(data.clone()),
        _ => None,
    }
}

/// The image of a POINTER RECORD as `format` stores it, with its pointer
/// slots: the one pointer-bearing initializer the gate images (PKG-CP), which
/// is the image of a `core::panic::Location`. `ty` must be a `repr(packed(1))`
/// struct whose fields are contiguous from offset 0 and fill its size, each a
/// `ptr` initialized by a `SymbolAddr` or a `[u8; n]` initialized by exactly
/// `n` raw bytes, with at least one `ptr`. A pointer slot holds what the
/// format's absolute relocation leaves in place: the addend on Mach-O
/// (`ARM64_RELOC_UNSIGNED` adds the symbol's address to it), zero on ELF (RELA
/// keeps the addend in the record). Anything else is `None`.
fn pointer_record_image(
    m: &Module,
    ty: &Ty,
    init: &Constant,
    format: ObjectFormat,
) -> Option<(Vec<u8>, Vec<ExpectedPointer>)> {
    let (Ty::Struct(id), Constant::Aggregate(values)) = (ty, init) else { return None };
    let def = m.struct_def(*id)?;
    if def.repr != StructRepr::Packed(1) || def.fields.len() != values.len() {
        return None;
    }
    let mut image = Vec::new();
    let mut pointers = Vec::new();
    for (field, value) in def.fields.iter().zip(values) {
        let offset = image.len() as u64;
        if field.offset != Some(offset) {
            return None;
        }
        match (&field.ty, value) {
            (Ty::Ptr, Constant::SymbolAddr { symbol, addend }) => {
                let in_place = match format {
                    ObjectFormat::MachO => *addend,
                    ObjectFormat::Elf => 0,
                };
                image.extend_from_slice(&in_place.to_le_bytes());
                pointers.push(ExpectedPointer { offset, symbol: symbol.clone(), addend: *addend });
            }
            (Ty::Array(elem, len), Constant::Bytes { data, .. })
                if m.types.get(elem.as_usize()) == Some(&Ty::U8) && data.len() as u64 == *len =>
            {
                image.extend_from_slice(data);
            }
            _ => return None,
        }
    }
    (!pointers.is_empty() && def.size == Some(image.len() as u64)).then_some((image, pointers))
}

/// Mach-O `ARM64_RELOC_UNSIGNED`.
const ARM64_RELOC_UNSIGNED: u32 = 0;
/// ELF `R_AARCH64_ABS64`.
const R_AARCH64_ABS64: u32 = 257;

/// log2 of the number of bytes an AArch64 ELF relocation type writes, as
/// `r_length` gives it on Mach-O, for the types this table LISTS, each named
/// in LLVM `ELFRelocs/AArch64.def`:
/// * 3 (8 bytes): ABS64 (257), PREL64 (260), GOTREL64 (307);
/// * 2 (4 bytes): the 32-bit data types ABS32 (258), PREL32 (261), GOTREL32
///   (308), PLT32 (314), GOTPCREL32 (315), and the instruction types 263-280
///   (MOVW_UABS, MOVW_SABS, LD_PREL_LO19, ADR_PREL_LO21, ADR_PREL_PG_HI21(_NC),
///   ADD_ABS_LO12_NC, LDST8_ABS_LO12_NC, TSTBR14, CONDBR19), 282-293 (JUMP26,
///   CALL26, LDST16/32/64_ABS_LO12_NC, MOVW_PREL), 299-306
///   (LDST128_ABS_LO12_NC, MOVW_GOTOFF) and 309-313 (GOT_LD_PREL19,
///   LD64_GOTOFF_LO15, ADR_GOT_PAGE, LD64_GOT_LO12_NC, LD64_GOTPAGE_LO15);
/// * 1 (2 bytes): ABS16 (259), PREL16 (262).
/// Every number the table does not list is read as 4 (16 bytes, the widest
/// AArch64 relocation, TLSDESC): the unassigned ones (281, 294-298, ...) and
/// the assigned ones it leaves out, among them PATCHINST (316), FUNCINIT64
/// (317), the TLS types (512-573) and the AUTH types (580 on). Reading a type
/// as wider than it is only refuses more (a code relocation over 4 bytes
/// refuses the object); the table never reads one as narrower.
fn elf_relocation_length(r_type: u32) -> u8 {
    match r_type {
        257 | 260 | 307 => 3,
        258 | 261 | 308 | 314 | 315 => 2,
        259 | 262 => 1,
        263..=280 | 282..=293 | 299..=306 | 309..=313 => 2,
        _ => 4,
    }
}

/// Mach-O `MH_SUBSECTIONS_VIA_SYMBOLS`: the linker may cut every section at
/// its symbols and move, or drop, the pieces.
const MH_SUBSECTIONS_VIA_SYMBOLS: u32 = 0x2000;

/// Whether the linker may cut this object's sections at their symbols: a
/// Mach-O object with `MH_SUBSECTIONS_VIA_SYMBOLS` set. Then only a
/// relocation keeps a reference from one symbol's piece to another's.
fn subsections_via_symbols(object: &CompiledObject) -> bool {
    object.format == ObjectFormat::MachO && object.header_flags & MH_SUBSECTIONS_VIA_SYMBOLS != 0
}

/// Whether the file header's flags word holds nothing this reader does not
/// name: on Mach-O no bit but `MH_SUBSECTIONS_VIA_SYMBOLS`, set or clear (the
/// admission's other conditions are the same whether or not the linker cuts a
/// section at its symbols: no symbol lies inside a target's image, and the
/// addend keeps the pointer on that image); on ELF zero (the reader names no
/// `e_flags` bit).
fn plain_header_flags(object: &CompiledObject) -> bool {
    match object.format {
        ObjectFormat::MachO => object.header_flags & !MH_SUBSECTIONS_VIA_SYMBOLS == 0,
        ObjectFormat::Elf => object.header_flags == 0,
    }
}

/// Mach-O: the section `flags` word of type `S_REGULAR` with no `S_ATTR_*` bit.
const S_REGULAR_NO_ATTRIBUTES: u64 = 0;
/// ELF `SHF_ALLOC | SHF_WRITE`.
const SHF_ALLOC_WRITE: u64 = SHF_ALLOC | SHF_WRITE;

/// Whether `section`'s header declares ORDINARY DATA, and if so whether it is
/// writable: `Some(writable)`; `None` for every other header, including a
/// section type, attribute or flag bit this reader does not name. Ordinary
/// data is what the format tells a static linker to carry into the image as
/// the object gives it, a symbol's bytes following the symbol, and not to
/// split into literals, merge by content, group, compress or drop:
/// * Mach-O: the whole `flags` word is zero, which is type `S_REGULAR` (every
///   literal, zero-fill, pointer, coalesced and thread-local type is a
///   non-zero low byte) with no attribute bit, AND the section is one of the
///   three non-literal data names the parser classifies: `__TEXT,__const`
///   (read-only), `__DATA,__const` or `__DATA,__data` (the writable `__DATA`
///   segment). The literal names `__TEXT,__cstring` and
///   `__TEXT,__literal4/8/16` are not ordinary under any `flags` word.
/// * ELF: `sh_flags` is exactly `SHF_ALLOC` (read-only) or exactly
///   `SHF_ALLOC | SHF_WRITE`, so no `SHF_MERGE`, `SHF_STRINGS`, `SHF_GROUP`,
///   `SHF_TLS`, `SHF_COMPRESSED`, `SHF_LINK_ORDER` or other bit. The section
///   type is not in that word: callers also require [`SectionClass::Data`],
///   which the parser gives only to `SHT_PROGBITS`.
fn ordinary_data(format: ObjectFormat, section: &Section) -> Option<bool> {
    match (format, section.flags, section.name.as_str()) {
        (ObjectFormat::MachO, S_REGULAR_NO_ATTRIBUTES, "__TEXT,__const") => Some(false),
        (ObjectFormat::MachO, S_REGULAR_NO_ATTRIBUTES, "__DATA,__const" | "__DATA,__data") => {
            Some(true)
        }
        (ObjectFormat::Elf, SHF_ALLOC, _) => Some(false),
        (ObjectFormat::Elf, SHF_ALLOC_WRITE, _) => Some(true),
        _ => None,
    }
}

/// Whether the bytes the linked image holds at a data global's symbol are the
/// ones the reader checked, so the global may be LISTED as verified (an object
/// with a global that fails this still binds; the global is not listed):
/// * its section is ordinary data by [`ordinary_data`] (the image was
///   compared), or ordinary zero-fill by [`ordinary_zero_fill`] and it has
///   an expected image that is all zero bytes and fits its extent (one with
///   no image is not listed) (a zero-fill
///   section has no bytes to compare: the linker gives it zeros). A section
///   the format lets the linker split into literals or merge by content (a
///   Mach-O literal or string type, ELF SHF_MERGE or SHF_STRINGS) is neither,
///   and neither is a zero-fill header with any other type, attribute or bit;
/// * no symbol defined in its section is weak, its own included: a weak
///   definition yields to another object's strong one, whose bytes the
///   reader never saw, and on Mach-O takes with it a following symbol that
///   starts no piece of its own (`N_ALT_ENTRY`, which this reader does not
///   read; [`defines_a_weak_symbol`]);
/// * its symbol's binding and visibility are exactly the ones its `M_cg`
///   linkage and visibility require ([`expected_symbol`]): a local symbol
///   where `M_cg` declares an external global defines nothing the program's
///   references reach, and they resolve to another object's definition.
fn verified_global(
    object: &CompiledObject,
    section: &Section,
    sym: &Symbol,
    end: u64,
    expect: &ObjectExpectations,
) -> bool {
    if sym.weak
        || sym.binding == SymbolBinding::Weak
        || defines_a_weak_symbol(object, section.index)
    {
        return false;
    }
    // A symbol whose binding or visibility is not the one `M_cg` declares is
    // not the definition the program's references resolve to: a local
    // symbol beside another object's external definition leaves the program
    // reading that other object's bytes.
    if expect.globals.get(&sym.name).and_then(|g| g.symbol) != Some((sym.binding, sym.visibility)) {
        return false;
    }
    match section.class {
        SectionClass::Data => ordinary_data(object.format, section).is_some(),
        SectionClass::ZeroFill => {
            ordinary_zero_fill(object.format, section)
                && expect.globals.get(&sym.name).and_then(|g| g.image.as_ref()).is_some_and(
                    |image| {
                        image.len() as u64 <= end.saturating_sub(sym.value)
                            && image.iter().all(|b| *b == 0)
                    },
                )
        }
        _ => false,
    }
}

/// Whether `section`'s header declares ORDINARY ZERO-FILL: Mach-O
/// `__DATA,__bss` with the flags word exactly `S_ZEROFILL` (no attribute
/// bit), ELF `.bss`/`.bss.*` (the parser's only zero-fill names, of type
/// SHT_NOBITS) with `sh_flags` exactly `SHF_ALLOC | SHF_WRITE`.
fn ordinary_zero_fill(format: ObjectFormat, section: &Section) -> bool {
    match format {
        ObjectFormat::MachO => {
            section.flags == u64::from(S_ZEROFILL) && section.name == "__DATA,__bss"
        }
        ObjectFormat::Elf => section.flags == SHF_ALLOC_WRITE,
    }
}

/// Whether any symbol defined in section `index` is weak. A Mach-O linker
/// discards a weak definition another object overrides, and with it every
/// byte up to the next symbol that starts a piece of its own; this reader
/// does not read which symbols start none (`N_ALT_ENTRY`). With no weak
/// symbol in the section, the linker has no definition there that it may
/// replace with another object's, wherever the section's pieces begin. The
/// rule is the same on ELF, where it is stricter than the format needs (an
/// ordinary ELF section is kept whole whatever its symbols' binding).
fn defines_a_weak_symbol(object: &CompiledObject, index: usize) -> bool {
    object
        .symbols
        .iter()
        .any(|s| s.section == Some(index) && (s.weak || s.binding == SymbolBinding::Weak))
}

/// The pointer slots `section`'s relocations fill, as `(covering symbol's
/// index, slot offset in its image)`, when EVERY relocation of the section is
/// the one admitted shape (the module comment's DATA RELOCATIONS); `None` when
/// any is not, which refuses the object. `syms` is the section's data symbols
/// in address order. The in-place bytes are not read here: the image
/// comparison checks them.
fn admitted_pointer_relocations(
    object: &CompiledObject,
    section: &Section,
    syms: &[&&Symbol],
    data_syms: &BTreeMap<String, &Symbol>,
    expect: &ObjectExpectations,
) -> Option<BTreeSet<(usize, u64)>> {
    let mut filled = BTreeSet::new();
    for reloc in &section.relocations {
        // An absolute 64-bit pointer in initialized data.
        let absolute = match object.format {
            ObjectFormat::MachO => {
                reloc.kind == (RelocKind::Other { raw: ARM64_RELOC_UNSIGNED }) && reloc.length == 3
            }
            ObjectFormat::Elf => reloc.kind == (RelocKind::Other { raw: R_AARCH64_ABS64 }),
        };
        if section.class != SectionClass::Data || !absolute || reloc.pc_relative {
            return None;
        }
        // In an object whose header flags the reader knows. The record's
        // section is ordinary data and defines no weak symbol; it may be
        // writable: under PIC the loader fills the pointer.
        if !plain_header_flags(object)
            || ordinary_data(object.format, section).is_none()
            || defines_a_weak_symbol(object, section.index)
        {
            return None;
        }
        // On a pointer slot of the LOCAL global covering it.
        let cover = syms.iter().rev().find(|s| s.value <= reloc.offset)?;
        let record_local = cover.binding == SymbolBinding::Local;
        let slot = reloc.offset - cover.value;
        let pointer =
            expect.globals.get(&cover.name)?.pointers.iter().find(|p| p.offset == slot)?;
        // Against this object's own definition of the global the slot names.
        let target = object.reloc_symbol(reloc)?;
        let target_section = target.section.and_then(|s| object.section(s));
        let local = target.binding == SymbolBinding::Local;
        let defines = data_syms.get(&target.name).is_some_and(|s| s.index == target.index)
            && target_section.is_some_and(|s| s.class == SectionClass::Data);
        // In ordinary read-only data that defines no weak symbol.
        let kept = target_section.is_some_and(|s| {
            ordinary_data(object.format, s) == Some(false)
                && !defines_a_weak_symbol(object, s.index)
        });
        let named = expect.globals.get(&target.name);
        let immutable = named.is_some_and(|g| g.immutable_non_tls);
        // Inside the target's image: `0 <= addend < len`, never one past it.
        let inside = named.and_then(|g| g.image.as_ref()).is_some_and(|image| {
            u64::try_from(pointer.addend).is_ok_and(|addend| addend < image.len() as u64)
        });
        let record_addend = match object.format {
            ObjectFormat::MachO => 0,
            ObjectFormat::Elf => pointer.addend,
        };
        // Each of the two symbols carries the binding and visibility its
        // `M_cg` linkage and visibility require ([`expected_symbol`]): a
        // LOCAL copy of a global `M_cg` declares external is not the
        // definition the program's other references to it reach.
        let declared = |sym: &Symbol| {
            expect.globals.get(&sym.name).and_then(|g| g.symbol)
                == Some((sym.binding, sym.visibility))
        };
        if !(record_local
            && local
            && declared(cover)
            && declared(target)
            && defines
            && kept
            && immutable
            && target.name == pointer.symbol
            && inside
            && reloc.addend == record_addend
            && filled.insert((cover.index, slot)))
        {
            return None;
        }
    }
    Some(filled)
}

/// How a machine call site transfers control.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MachineSiteKind {
    /// `bl` — returns to the next instruction.
    Call,
    /// A `b` to another function — returns straight to this function's caller.
    Tail,
    /// `blr` — an indirect call (Unknown until step 5.9).
    Indirect,
}

/// One machine call site found by the structural walk.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MachineSite {
    /// In-section byte offset of the call instruction.
    pub offset: u64,
    /// How it transfers control.
    pub kind: MachineSiteKind,
    /// The callee's IR-level symbol name, when the site names one.
    pub callee: Option<String>,
    /// The relocation that names it (`None` for an unrelocated local call).
    pub reloc: Option<RelocKind>,
    /// Whether this site lies on a straight-line path into a trap (`brk`):
    /// the failure tail of an assert, which never returns.
    pub in_trap_tail: bool,
}

/// One consumed relocation, as a certificate records it.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ConsumedReloc {
    /// In-section offset.
    pub offset: u64,
    /// Kind.
    pub kind: RelocKind,
    /// The symbol it names, if any.
    pub symbol: Option<String>,
    /// What consumed it: `call`, `tail`, `address`, or `unmodeled`.
    pub role: String,
}

/// One function's window of the object.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionWindow {
    /// IR-level symbol.
    pub symbol: String,
    /// The code section holding it.
    pub section: usize,
    /// First byte (in-section offset).
    pub start: u64,
    /// One past the last byte of the extent.
    pub end: u64,
    /// The function's bytes, `[start, end)`.
    pub code: Vec<u8>,
    /// Offsets (in-section) the structural walk reaches.
    pub reachable: BTreeSet<u64>,
    /// Structural successor edges between reachable offsets (intra-extent).
    pub successors: BTreeMap<u64, Vec<u64>>,
    /// Machine call sites, in offset order.
    pub sites: Vec<MachineSite>,
    /// Relocations this function's verdict consumes.
    pub relocations: Vec<ConsumedReloc>,
    /// Reasons O1/O2 make THIS function Unknown (the object is still bound).
    pub unknown: Vec<String>,
    /// Data-in-code ranges `[start, end)` (in-section offsets): the jump
    /// tables of trust-cg's dense-switch dispatch idiom (INC5.4-JUMPTABLE).
    /// Their words are data, not instructions; a function holding one is
    /// Unknown (it is named in [`Self::unknown`]).
    pub data_in_code: Vec<(u64, u64)>,
    /// The expectation `M_cg` has for it.
    pub expected: ExpectedBody,
    /// Every reachable instruction carrying an admitted page relocation
    /// (`adrp` with a page-high kind; `add`/load/store with a page-offset
    /// kind), by in-section offset, as the walk read it (PKG-C5c S2a). A
    /// RECORD, not an admission: each one's line is in [`Self::unknown`]
    /// exactly as before; the call-event gate decides whether a pair of these
    /// is a dead panic tail's Location address.
    pub page_halves: BTreeMap<u64, PageHalf>,
    /// The trap-tail offsets: every reachable word on a straight-line run
    /// into a `brk`/`udf` (the run's trap included), the set
    /// [`MachineSite::in_trap_tail`] is read off.
    pub trap_tail: BTreeSet<u64>,
}

/// One page-relocated half of an address materialization, as the structural
/// walk read it (PKG-C5c S2a). Recorded for every reachable instruction whose
/// admitted page relocation the walk consumed with role `address`; it admits
/// nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PageHalf {
    /// In-section offset of the instruction.
    pub offset: u64,
    /// Its class: [`InsnClass::Adrp`], [`InsnClass::AddImm64`] or
    /// [`InsnClass::LoadStoreUImm`].
    pub class: InsnClass,
    /// The relocation's index in its section's relocation table.
    pub reloc_index: usize,
    /// The relocation kind.
    pub kind: RelocKind,
    /// What it is resolved against.
    pub target: RelocTarget,
    /// Its addend.
    pub addend: i64,
    /// Its `pc_relative` flag.
    pub pc_relative: bool,
    /// Its length (log2 of the bytes it writes).
    pub length: u8,
    /// Bits 4:0 of the word (`Rd`, or `Rt` for a load/store).
    pub rd: u8,
    /// Bits 9:5 of the word (`Rn` of `add`/load/store; part of `immhi` for
    /// `adrp`).
    pub rn: u8,
    /// The word's in-place immediate: `immhi:immlo` (21 bits) for `adrp`,
    /// `imm12` (bits 21:10) for `add`/load/store.
    pub imm: u32,
    /// Bit 22 of the word: the `add` immediate's `sh` (shift by 12). 0 for
    /// `adrp`.
    pub shift: u8,
    /// The exact line the walk put in [`FunctionWindow::unknown`] for it.
    pub unknown_line: String,
}

impl PageHalf {
    fn read(
        offset: u64,
        word: u32,
        class: InsnClass,
        reloc_index: usize,
        r: &Relocation,
        unknown_line: String,
    ) -> PageHalf {
        let adrp = class == InsnClass::Adrp;
        PageHalf {
            offset,
            class,
            reloc_index,
            kind: r.kind,
            target: r.target,
            addend: r.addend,
            pc_relative: r.pc_relative,
            length: r.length,
            rd: (word & 0x1f) as u8,
            rn: ((word >> 5) & 0x1f) as u8,
            imm: if adrp {
                (((word >> 5) & 0x7_ffff) << 2) | ((word >> 29) & 0x3)
            } else {
                (word >> 10) & 0xfff
            },
            shift: if adrp { 0 } else { ((word >> 22) & 1) as u8 },
            unknown_line,
        }
    }
}

impl FunctionWindow {
    /// Whether `offset` (in-section) lies in this extent.
    #[must_use]
    pub fn contains(&self, offset: u64) -> bool {
        (self.start..self.end).contains(&offset)
    }

    /// The machine site at `offset`, if any.
    #[must_use]
    pub fn site_at(&self, offset: u64) -> Option<&MachineSite> {
        self.sites.iter().find(|s| s.offset == offset)
    }

    /// SHA-256 of the function's bytes.
    #[must_use]
    pub fn text_sha256(&self) -> String {
        hex(&Sha256::digest(&self.code))
    }

    /// Whether `to` is reachable from `from` along structural successor edges
    /// (strictly after `from`; the fragment is loop-free so this is a
    /// precedence relation).
    #[must_use]
    pub fn precedes(&self, from: u64, to: u64) -> bool {
        let mut seen = BTreeSet::new();
        let mut work: Vec<u64> = self.successors.get(&from).cloned().unwrap_or_default();
        while let Some(n) = work.pop() {
            if n == to {
                return true;
            }
            if seen.insert(n)
                && let Some(next) = self.successors.get(&n)
            {
                work.extend(next.iter().copied());
            }
        }
        false
    }
}

/// The object bound to `M_cg` (O1 passed).
#[derive(Debug, Clone)]
pub struct ObjectLayout {
    /// The parsed container.
    pub object: CompiledObject,
    /// Every function window, in symbol order.
    pub windows: BTreeMap<String, FunctionWindow>,
    /// Sections disclosed as unverified (unwind metadata), by name.
    pub unverified_sections: Vec<String>,
    /// Data symbols compared with their initializer images.
    pub verified_globals: Vec<String>,
}

impl ObjectLayout {
    /// Bind `object` to `expect` (obligation O1). Any failure refuses the whole
    /// object.
    pub fn bind(
        object: CompiledObject,
        expect: &ObjectExpectations,
    ) -> Result<ObjectLayout, ObjectRefusal> {
        if object.format != expect.format {
            return Err(malformed(format!(
                "object is {:?} but the target produces {:?}",
                object.format, expect.format
            )));
        }
        let unverified_sections: Vec<String> = object
            .sections
            .iter()
            .filter(|s| s.class == SectionClass::Unwind)
            .map(|s| s.name.clone())
            .collect();

        // ---- symbols ------------------------------------------------------
        let mut body_syms: BTreeMap<String, &Symbol> = BTreeMap::new();
        let mut data_syms: BTreeMap<String, &Symbol> = BTreeMap::new();
        for sym in &object.symbols {
            match sym.kind {
                SymbolKind::Debug | SymbolKind::Section | SymbolKind::File => continue,
                SymbolKind::Mapping { data } => {
                    let in_code = sym
                        .section
                        .and_then(|s| object.section(s))
                        .is_some_and(|s| s.class == SectionClass::Code);
                    if data && in_code {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::UncoveredTextByte,
                            format!(
                                "mapping symbol `{}` marks data inside a code section at {:#x} (a \
                                 literal pool or data in code)",
                                sym.raw_name, sym.value
                            ),
                        ));
                    }
                    continue;
                }
                SymbolKind::Undefined => {
                    if sym.index == 0 && object.format == ObjectFormat::Elf {
                        continue;
                    }
                    let known = expect.declarations.contains(&sym.name)
                        || expect.globals.get(&sym.name).is_some_and(|g| !g.defined)
                        || RUNTIME_HELPERS.contains(&sym.name.as_str());
                    if !known {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::SymbolInventory,
                            format!(
                                "undefined symbol `{}` is neither an M_cg declaration nor a named \
                                 runtime helper",
                                sym.raw_name
                            ),
                        ));
                    }
                    continue;
                }
                SymbolKind::Function | SymbolKind::Object | SymbolKind::NoType => {}
            }
            let section = sym
                .section
                .and_then(|s| object.section(s))
                .ok_or_else(|| malformed(format!("symbol `{}` names no section", sym.raw_name)))?;
            match section.class {
                SectionClass::Code => {
                    if !expect.bodies.contains_key(&sym.name) {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::SymbolInventory,
                            format!(
                                "symbol `{}` defined in `{}` is not a body of M_cg",
                                sym.raw_name, section.name
                            ),
                        ));
                    }
                    if body_syms.insert(sym.name.clone(), sym).is_some() {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::SymbolInventory,
                            format!("body `{}` has more than one symbol", sym.name),
                        ));
                    }
                }
                SectionClass::Data | SectionClass::ZeroFill => {
                    if !expect.globals.get(&sym.name).is_some_and(|g| g.defined) {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::SymbolInventory,
                            format!(
                                "symbol `{}` defined in `{}` is not a defined global of M_cg",
                                sym.raw_name, section.name
                            ),
                        ));
                    }
                    if data_syms.insert(sym.name.clone(), sym).is_some() {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::SymbolInventory,
                            format!("global `{}` has more than one symbol", sym.name),
                        ));
                    }
                }
                SectionClass::Unwind | SectionClass::Structural => {
                    if sym.binding != SymbolBinding::Local {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::SymbolInventory,
                            format!(
                                "non-local symbol `{}` defined in unverified section `{}`",
                                sym.raw_name, section.name
                            ),
                        ));
                    }
                }
            }
        }
        for (name, body) in &expect.bodies {
            let sym = body_syms.get(name).ok_or_else(|| {
                ObjectRefusal::new(
                    ObjectRefusalKind::SymbolInventory,
                    format!("M_cg body `{name}` has no symbol in the object"),
                )
            })?;
            if object.format == ObjectFormat::Elf && sym.kind != SymbolKind::Function {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::BindingMismatch,
                    format!("ELF symbol `{name}` is {:?}, not STT_FUNC", sym.kind),
                ));
            }
            if sym.binding != body.binding || sym.visibility != body.symbol_visibility {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::BindingMismatch,
                    format!(
                        "symbol `{name}` is bound {:?}/{:?} but M_cg's {} / {} linkage requires \
                         {:?}/{:?}",
                        sym.binding,
                        sym.visibility,
                        body.linkage,
                        body.visibility,
                        body.binding,
                        body.symbol_visibility
                    ),
                ));
            }
        }

        // ---- data sections ------------------------------------------------
        let mut verified_globals = Vec::new();
        for section in &object.sections {
            if !matches!(section.class, SectionClass::Data | SectionClass::ZeroFill) {
                continue;
            }
            let mut syms: Vec<&&Symbol> =
                data_syms.values().filter(|s| s.section == Some(section.index)).collect();
            syms.sort_by_key(|s| s.value);
            let Some(relocated) =
                admitted_pointer_relocations(&object, section, &syms, &data_syms, expect)
            else {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::DataImage,
                    format!(
                        "data section `{}` carries relocations: pointer-bearing statics are refused",
                        section.name
                    ),
                ));
            };
            let mut covered_to = 0u64;
            for (i, sym) in syms.iter().enumerate() {
                let end = syms.get(i + 1).map_or(section.size, |n| n.value);
                if sym.value < covered_to {
                    return Err(ObjectRefusal::new(
                        ObjectRefusalKind::OverlappingExtents,
                        format!("global `{}` overlaps its predecessor", sym.name),
                    ));
                }
                if section.class == SectionClass::Data {
                    let gap =
                        section.bytes.get(covered_to as usize..sym.value as usize).unwrap_or(&[]);
                    if gap.iter().any(|b| *b != 0) {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::DataImage,
                            format!("non-zero bytes before `{}` in `{}`", sym.name, section.name),
                        ));
                    }
                    let image =
                        expect.globals.get(&sym.name).and_then(|g| g.image.as_ref()).ok_or_else(
                            || {
                                ObjectRefusal::new(
                                    ObjectRefusalKind::DataImage,
                                    format!(
                                        "global `{}` has an initializer the gate cannot image \
                                     (fail-closed)",
                                        sym.name
                                    ),
                                )
                            },
                        )?;
                    let start = sym.value as usize;
                    let bytes = section.bytes.get(start..end as usize).unwrap_or(&[]);
                    let (head, tail) = bytes.split_at(image.len().min(bytes.len()));
                    if head != image.as_slice() || tail.iter().any(|b| *b != 0) {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::DataImage,
                            format!(
                                "global `{}`'s bytes differ from its initializer image",
                                sym.name
                            ),
                        ));
                    }
                }
                // A pointer the object does not relocate is not the address
                // `M_cg` names, whatever section holds it.
                for pointer in expect.globals.get(&sym.name).map_or(&[][..], |g| &g.pointers) {
                    if !relocated.contains(&(sym.index, pointer.offset)) {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::DataImage,
                            format!(
                                "global `{}` has no relocation on its pointer to `{}` at {:#x}",
                                sym.name, pointer.symbol, pointer.offset
                            ),
                        ));
                    }
                }
                covered_to = end;
                if verified_global(&object, section, sym, end, expect) {
                    verified_globals.push(sym.name.clone());
                }
            }
            if syms.is_empty() && section.size != 0 {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::DataImage,
                    format!(
                        "data section `{}` holds {} bytes no global claims",
                        section.name, section.size
                    ),
                ));
            }
        }

        // ---- extents ------------------------------------------------------
        let mut windows: BTreeMap<String, FunctionWindow> = BTreeMap::new();
        for section in object.sections.iter().filter(|s| s.class == SectionClass::Code) {
            let mut syms: Vec<&&Symbol> =
                body_syms.values().filter(|s| s.section == Some(section.index)).collect();
            syms.sort_by_key(|s| s.value);
            if section.size % 4 != 0 {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::UncoveredTextByte,
                    format!(
                        "code section `{}` is not a whole number of instructions",
                        section.name
                    ),
                ));
            }
            // A relocation in code writes one instruction, 4 bytes, at most.
            // A wider one (an 8-byte data relocation, an ELF type whose width
            // the reader does not know) writes past the instruction it sits
            // on, into the next one, which may begin another function: the
            // linker changes bytes the reader attributes to that function.
            if let Some(r) = section.relocations.iter().find(|r| r.length > 2) {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::UnconsumedRelocation,
                    format!(
                        "relocation {} at {:#x} in code section `{}` writes {} bytes, more \
                         than the one instruction it sits on",
                        r.kind.name(),
                        r.offset,
                        section.name,
                        1u64 << r.length
                    ),
                ));
            }
            if section.size == 0 {
                continue;
            }
            let first = syms.first().map_or(section.size, |s| s.value);
            if first != 0 {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::UncoveredTextByte,
                    format!(
                        "code bytes [0, {first:#x}) of `{}` lie in no function's extent",
                        section.name
                    ),
                ));
            }
            for (i, sym) in syms.iter().enumerate() {
                let next = syms.get(i + 1);
                let end = next.map_or(section.size, |n| n.value);
                if end <= sym.value {
                    // `next` is None when the last body starts at the
                    // section's end: an empty extent, refused as well.
                    let other = next.map_or("the section's end", |n| n.name.as_str());
                    return Err(ObjectRefusal::new(
                        ObjectRefusalKind::OverlappingExtents,
                        format!(
                            "`{}` and `{}` share the address {:#x} in `{}`",
                            sym.name, other, sym.value, section.name
                        ),
                    ));
                }
                if sym.value % 4 != 0 {
                    return Err(ObjectRefusal::new(
                        ObjectRefusalKind::UncoveredTextByte,
                        format!("`{}` starts at a misaligned offset {:#x}", sym.name, sym.value),
                    ));
                }
                let code = section.bytes[sym.value as usize..end as usize].to_vec();
                if let Some(size) = sym.size {
                    let len = end - sym.value;
                    if size > len {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::OverlappingExtents,
                            format!(
                                "`{}`'s st_size {size:#x} runs past its extent ({len:#x} bytes to \
                                 the next symbol or section end)",
                                sym.name
                            ),
                        ));
                    }
                    if size % 4 != 0 || size == 0 {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::UncoveredTextByte,
                            format!(
                                "`{}`'s st_size {size:#x} is not a whole instruction count",
                                sym.name
                            ),
                        ));
                    }
                    let trailing = &code[size as usize..];
                    if trailing
                        .chunks(4)
                        .any(|w| !is_padding(u32::from_le_bytes([w[0], w[1], w[2], w[3]])))
                    {
                        return Err(ObjectRefusal::new(
                            ObjectRefusalKind::UncoveredTextByte,
                            format!(
                                "bytes past `{}`'s st_size are not padding but belong to no symbol",
                                sym.name
                            ),
                        ));
                    }
                }
                let expected = expect.bodies[&sym.name].clone();
                windows.insert(
                    sym.name.clone(),
                    FunctionWindow {
                        symbol: sym.name.clone(),
                        section: section.index,
                        start: sym.value,
                        end,
                        code,
                        reachable: BTreeSet::new(),
                        successors: BTreeMap::new(),
                        sites: Vec::new(),
                        relocations: Vec::new(),
                        unknown: Vec::new(),
                        data_in_code: Vec::new(),
                        expected,
                        page_halves: BTreeMap::new(),
                        trap_tail: BTreeSet::new(),
                    },
                );
            }
        }

        // Local extent starts a non-relocated branch may name: (section, offset) -> symbol.
        let local_starts: BTreeMap<(usize, u64), String> = windows
            .values()
            .filter(|w| w.expected.non_preemptible)
            .map(|w| ((w.section, w.start), w.symbol.clone()))
            .collect();
        // Every body's opening symbol: a call relocated against a defined
        // symbol names a callee only when that symbol opens a body here.
        let body_starts: BTreeMap<(usize, u64), String> =
            windows.values().map(|w| ((w.section, w.start), w.symbol.clone())).collect();

        // ---- the structural walk, coverage and relocation consumption -----
        let mut consumed: BTreeSet<(usize, u64, usize)> = BTreeSet::new();
        for window in windows.values_mut() {
            // Every window was opened on a section of this object above.
            let section = object.section(window.section).ok_or_else(|| {
                malformed(format!(
                    "`{}` names section {}, which the object does not have",
                    window.symbol, window.section
                ))
            })?;
            walk_window(&object, section, window, &local_starts, &body_starts, &mut consumed)?;
        }
        for section in object.sections.iter().filter(|s| s.class == SectionClass::Code) {
            for (i, reloc) in section.relocations.iter().enumerate() {
                if !consumed.contains(&(section.index, reloc.offset, i)) {
                    let sym = object
                        .reloc_symbol(reloc)
                        .map_or("<section>".into(), |s| s.raw_name.clone());
                    return Err(ObjectRefusal::new(
                        ObjectRefusalKind::UnconsumedRelocation,
                        format!(
                            "{} at {:#x} in `{}` (naming `{sym}`) is consumed by no function: it \
                             does not sit on a reachable instruction of the class it relocates",
                            reloc.kind.name(),
                            reloc.offset,
                            section.name
                        ),
                    ));
                }
            }
        }
        Ok(ObjectLayout { object, windows, unverified_sections, verified_globals })
    }
}

/// A GPR unsigned-immediate load cannot write NZCV or perform address-base
/// writeback. Only these
/// finite encodings may separate a dense-switch compare from its branch;
/// overwriting Xi (including its W alias) would invalidate the bound. SIMD,
/// stores, prefetches, reserved encodings and writeback forms do not qualify.
fn load_preserves_switch_bound(word: u32, index: u32) -> bool {
    let size = word >> 30;
    let opc = (word >> 22) & 3;
    let valid_load = opc == 1 || (opc == 2 && size < 3) || (opc == 3 && size < 2);
    word & 0x3f00_0000 == 0x3900_0000
        && valid_load
        && word & 31 != index
        && word & 31 != 31
}

/// One matched dense-switch dispatch (INC5.4-JUMPTABLE).
#[derive(Debug, Clone, PartialEq, Eq)]
struct JumpTable {
    /// Start of the bound check, including any scheduled loads before b.hi.
    guard_start: u64,
    /// In-section offset of the table's first 32-bit entry (`T`).
    start: u64,
    /// The number of entries, `k + 1` for the bound check's `#k`.
    entries: u64,
    /// The distinct entry targets (in-section offsets), ascending.
    targets: Vec<u64>,
}

impl JumpTable {
    fn end(&self) -> u64 {
        self.start + 4 * self.entries
    }
}

/// Match trust-cg's dense-switch dispatch ending at the `br` at `br_off`
/// (`trust-cg-lower/src/switch.rs`, `emit_jump_table`; plan §1(b)): exactly
/// the relocation-free run (the five-instruction branch/dispatch tail is
/// contiguous; only exact GPR loads preserving Xi and NZCV may follow cmp)
///
/// ```text
///   cmp   Ri, #k                    ; subs xzr, Xi, #k  (64-bit, `lsl #2` index)
///   [GPR unsigned-immediate loads that preserve Xi and NZCV]
///   b.hi  L                         ; L outside this run
///   adr   Xb, T
///   ldrsw Xo, [Xb, Xi, lsl #2]
///   add   Xt, Xb, Xo
///   br    Xt
/// ```
///
/// with `T` 4-aligned, the `k + 1` entries `[T, T + 4(k + 1))` inside the
/// extent, and every entry's target `T + sext32(entry)` 4-aligned, inside the
/// extent and OUTSIDE the table. These are the encodings MEASURED from
/// trust-cg 7ace0c56b's `Compiler::compile` at O0 and O2 on Mach-O and ELF
/// (`tests/f1_compile.rs::dump_dense_switch_shapes`); any other spelling (a
/// 32-bit or shifted-immediate compare, a `b.hi` into the run, an
/// extended-register index or add, a register compare, a relocated word,
/// distinct registers where one is required) does not match,
/// and the `br` stays a dead end. The caller checks what the walk alone can
/// establish: nothing reachable or relocated inside the table, and the run
/// entered only by falling through it.
fn match_dense_switch(section: &Section, wstart: u64, wend: u64, br_off: u64) -> Option<JumpTable> {
    let bhi_off = br_off.checked_sub(16).filter(|o| *o >= wstart)?;
    let word = |off: u64| -> Option<u32> {
        let i = usize::try_from(off).ok()?;
        let b = section.bytes.get(i..i.checked_add(4)?)?;
        Some(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    };
    let reg = |w: u32, shift: u32| (w >> shift) & 31;
    let [bhi, adr, ldrsw, add, br] =
        [0u64, 4, 8, 12, 16].map(|d| word(bhi_off + d).unwrap_or(0));

    // br Xt
    if br & 0xffff_fc1f != 0xd61f_0000 {
        return None;
    }
    let xt = reg(br, 5);
    // add Xt, Xb, Xo   (shifted register, 64-bit, LSL #0)
    if add & 0xffe0_fc00 != 0x8b00_0000 || reg(add, 0) != xt {
        return None;
    }
    let (xb, xo) = (reg(add, 5), reg(add, 16));
    // ldrsw Xo, [Xb, Xi, lsl #2]   (register offset, option LSL/UXTX, S = 1)
    if ldrsw & 0xffe0_fc00 != 0xb8a0_7800 || reg(ldrsw, 0) != xo || reg(ldrsw, 5) != xb {
        return None;
    }
    let xi = reg(ldrsw, 16);
    // adr Xb, T
    if adr & 0x9f00_0000 != 0x1000_0000 || reg(adr, 0) != xb {
        return None;
    }
    let adr_imm = (((adr >> 5) & 0x7_ffff) << 2) | ((adr >> 29) & 3);
    let table = i128::from(bhi_off + 4) + i128::from(sext(adr_imm, 21));
    let mut cmp_off = bhi_off.checked_sub(4).filter(|o| *o >= wstart)?;
    while load_preserves_switch_bound(word(cmp_off)?, xi) {
        cmp_off = cmp_off.checked_sub(4).filter(|o| *o >= wstart)?;
    }
    let cmp = word(cmp_off)?;
    if section.relocations.iter().any(|r| (cmp_off..=br_off).contains(&r.offset)) {
        return None;
    }
    // b.hi L, with L OUTSIDE the run (trust-cg branches to the default block).
    // A `b.hi` into the run makes the bound check vacuous: `b.hi .+4` lands on
    // the `adr` either way, so every index would reach `ldrsw`.
    if bhi & 0xff00_001f != 0x5400_0008 {
        return None;
    }
    let bhi_target = i128::from(bhi_off) + i128::from(sext((bhi >> 5) & 0x7_ffff, 19) * 4);
    if (i128::from(cmp_off)..=i128::from(br_off)).contains(&bhi_target) {
        return None;
    }
    // cmp Xi, #k   (subs xzr, Xi, #imm12, 64-bit, unshifted: trust-cg uses a
    // register compare, which does not match, for any `k` past imm12)
    if cmp & 0xffc0_001f != 0xf100_001f || reg(cmp, 5) != xi {
        return None;
    }
    let k = u64::from((cmp >> 10) & 0xfff);
    // No register is SP/ZR; the base is neither the index nor the loaded offset.
    if [xi, xb, xo, xt].contains(&31) || xb == xi || xb == xo {
        return None;
    }
    let entries = k.checked_add(1)?;
    let start = u64::try_from(table).ok()?;
    let end = entries.checked_mul(4).and_then(|len| start.checked_add(len))?;
    if start % 4 != 0 || start < wstart || end > wend {
        return None;
    }
    let mut targets = BTreeSet::new();
    for i in 0..entries {
        let entry = word(start + 4 * i)? as i32;
        let target = u64::try_from(i128::from(start) + i128::from(entry)).ok()?;
        if target % 4 != 0 || !(wstart..wend).contains(&target) || (start..end).contains(&target) {
            return None;
        }
        targets.insert(target);
    }
    Some(JumpTable { guard_start: cmp_off, start, entries, targets: targets.into_iter().collect() })
}

/// Whether a call relocated against `s` (addend 0) names the callee `s.name`
/// the way a linker resolves it. Two forms do, and nothing else:
/// * `s` is the very symbol that opens a body window of this object: defined
///   (a function or untyped symbol) at its section and value, under its name;
/// * `s` is an undefined, global, non-weak symbol: a strong external declaration (on
///   Mach-O its raw name carries the C prefix `_` the name was read through) whose name
///   opens no body window of this object.
///
/// A linker resolves a relocation through the symbol's section and value, or
/// through its raw name when it is undefined. A FILE, SECTION, debugging or
/// mapping symbol, a defined symbol that opens no body (one in an unwind or
/// structural section, or a second name at a body's address), a weak undefined
/// symbol, a Mach-O undefined name without the prefix, or an undefined global named like a
/// body this object defines LOCAL (local and global names are separate namespaces: the linker
/// resolves the undefined one elsewhere), can carry a body's name while the linker sends the
/// call elsewhere.
fn names_a_callee(
    object: &CompiledObject,
    s: &Symbol,
    body_starts: &BTreeMap<(usize, u64), String>,
) -> bool {
    match (s.kind, s.section) {
        (SymbolKind::Function | SymbolKind::NoType, Some(section)) => {
            body_starts.get(&(section, s.value)) == Some(&s.name)
        }
        (SymbolKind::Undefined, None) => {
            !s.weak
                && s.binding == SymbolBinding::Global
                && (object.format != ObjectFormat::MachO
                    || s.raw_name.strip_prefix('_') == Some(s.name.as_str()))
                && !body_starts.values().any(|body| *body == s.name)
        }
        _ => false,
    }
}

/// Walk one window from its entry: compute reachability and structural edges,
/// find the call sites, consume the relocations, and check that every
/// unreachable word is padding.
fn walk_window(
    object: &CompiledObject,
    section: &Section,
    window: &mut FunctionWindow,
    local_starts: &BTreeMap<(usize, u64), String>,
    body_starts: &BTreeMap<(usize, u64), String>,
    consumed: &mut BTreeSet<(usize, u64, usize)>,
) -> Result<(), ObjectRefusal> {
    let word_at = |off: u64| -> u32 {
        let i = off as usize;
        u32::from_le_bytes([
            section.bytes[i],
            section.bytes[i + 1],
            section.bytes[i + 2],
            section.bytes[i + 3],
        ])
    };
    let relocs_at = |off: u64| -> Vec<(usize, &Relocation)> {
        section.relocations.iter().enumerate().filter(|(_, r)| r.offset == off).collect()
    };
    let (wstart, wend, wsym) = (window.start, window.end, window.symbol.clone());
    let mut work = vec![wstart];
    let mut unknown: BTreeSet<String> = BTreeSet::new();
    // The `br` offset of every matched dense-switch dispatch run.
    let mut dispatch_runs: Vec<(u64, u64)> = Vec::new();
    while let Some(off) = work.pop() {
        if !window.reachable.insert(off) {
            continue;
        }
        let word = word_at(off);
        let class = classify_insn(word);
        let relocs = relocs_at(off);
        if relocs.len() > 1 {
            return Err(ObjectRefusal::new(
                ObjectRefusalKind::UnconsumedRelocation,
                format!("{} relocations apply to the one instruction at {off:#x}", relocs.len()),
            ));
        }
        let reloc = relocs.first().copied();
        let mut succ: Vec<u64> = Vec::new();
        let push_local = |target: i128, succ: &mut Vec<u64>, unknown: &mut BTreeSet<String>| {
            if target >= i128::from(wstart) && target < i128::from(wend) {
                succ.push(target as u64);
            } else {
                unknown.insert(format!(
                    "branch at {off:#x} leaves the extent [{wstart:#x}, {wend:#x}) to {target:#x} (not a \
                     call)"
                ));
            }
        };
        let mut consume = |idx: usize, r: &Relocation, role: &str, window: &mut FunctionWindow| {
            consumed.insert((section.index, r.offset, idx));
            window.relocations.push(ConsumedReloc {
                offset: r.offset,
                kind: r.kind,
                symbol: object.reloc_symbol(r).map(|s| s.name.clone()),
                role: role.to_string(),
            });
        };
        // A relocation of an UNMODELED kind on a reachable instruction is
        // consumed by this function, which it makes Unknown. An ADMITTED kind
        // on an instruction of the wrong class is left unconsumed: the object
        // refuses below, because the gate cannot say what it relocates.
        let unmodeled_only =
            |reloc: Option<(usize, &Relocation)>,
             window: &mut FunctionWindow,
             unknown: &mut BTreeSet<String>,
             consume: &mut dyn FnMut(usize, &Relocation, &str, &mut FunctionWindow)| {
                if let Some((idx, r)) = reloc.filter(|(_, r)| !r.kind.is_admitted(object.format)) {
                    consume(idx, r, "unmodeled", window);
                    unknown
                        .insert(format!("unmodeled relocation kind {} at {off:#x}", r.kind.name()));
                }
            };
        match class {
            InsnClass::Ret | InsnClass::Trap => {
                unmodeled_only(reloc, window, &mut unknown, &mut consume);
            }
            InsnClass::Unrecognized => {
                unmodeled_only(reloc, window, &mut unknown, &mut consume);
                unknown.insert(format!(
                    "word {word:#010x} at {off:#x} is a branch/system instruction the gate does not \
                     recognize exactly"
                ));
            }
            InsnClass::IndirectBranch => {
                unmodeled_only(reloc, window, &mut unknown, &mut consume);
                // INC5.4-JUMPTABLE: exactly trust-cg's dense-switch dispatch,
                // every guard holding, makes the table data and its entries
                // successors; anything else keeps the `br` a dead end, so the
                // table's words stay unreached and refuse the object below.
                match match_dense_switch(section, wstart, wend, off) {
                    Some(table) => {
                        unknown.insert(format!(
                            "dense-switch jump table at {:#x} ({} entries) dispatched by `br` at \
                             {off:#x}: function is Unknown (INC5.4-JUMPTABLE)",
                            table.start, table.entries
                        ));
                        window.data_in_code.push((table.start, table.end()));
                        dispatch_runs.push((table.guard_start, off));
                        succ.extend(table.targets.iter().copied());
                    }
                    None => {
                        unknown.insert(format!("indirect jump `br` at {off:#x} (fail-closed)"));
                    }
                }
            }
            InsnClass::IndirectCall => {
                unmodeled_only(reloc, window, &mut unknown, &mut consume);
                window.sites.push(MachineSite {
                    offset: off,
                    kind: MachineSiteKind::Indirect,
                    callee: None,
                    reloc: None,
                    in_trap_tail: false,
                });
                unknown
                    .insert(format!("indirect call `blr` at {off:#x} is Unknown until step 5.9"));
                succ.push(off + 4);
            }
            InsnClass::BranchLink { delta } | InsnClass::Branch { delta } => {
                let is_call = matches!(class, InsnClass::BranchLink { .. });
                let call_kind = if is_call { MachineSiteKind::Call } else { MachineSiteKind::Tail };
                match reloc {
                    Some((idx, r)) => {
                        let expected_kind = match (object.format, is_call) {
                            (ObjectFormat::MachO, _) => RelocKind::Branch26,
                            (ObjectFormat::Elf, true) => RelocKind::Call26,
                            (ObjectFormat::Elf, false) => RelocKind::Jump26,
                        };
                        let sym = object.reloc_symbol(r);
                        // ELF spells a local call as `section + addend` too: it
                        // names a symbol exactly when the addend is the start of
                        // a non-preemptible extent in that section.
                        let local_callee = sym
                            .filter(|s| s.kind == SymbolKind::Section)
                            .and_then(|s| Some((s.section?, u64::try_from(r.addend).ok()?)))
                            .and_then(|at| local_starts.get(&at));
                        if r.kind == expected_kind && r.pc_relative && r.length == 2 {
                            let canonical = object.format != ObjectFormat::MachO
                                || r.kind != RelocKind::Branch26
                                || macho_branch26_operand_is_canonical(word);
                            consume(
                                idx,
                                r,
                                if !canonical {
                                    "unmodeled"
                                } else if is_call {
                                    "call"
                                } else {
                                    "tail"
                                },
                                window,
                            );
                            if !canonical {
                                window.sites.push(MachineSite {
                                    offset: off,
                                    kind: call_kind,
                                    callee: None,
                                    reloc: Some(r.kind),
                                    in_trap_tail: false,
                                });
                                unknown.insert(format!("ARM64_RELOC_BRANCH26 operand at {off:#x} has nonzero encoded imm26; only a zero instruction displacement names the modeled symbol entry"));
                            } else {
                                if let Some(s) = sym.filter(|s| {
                                    r.addend == 0
                                        && s.kind != SymbolKind::Section
                                        && !names_a_callee(object, s, body_starts)
                                }) {
                                    return Err(malformed(format!(
                                        "{} at {off:#x} names `{}` through a symbol that is \
                                         neither the one opening a body of this object nor a \
                                         strong external declaration; a linker resolves it \
                                         elsewhere",
                                        r.kind.name(),
                                        s.name
                                    )));
                                }
                                match (sym, local_callee) {
                                    (Some(s), _)
                                        if r.addend == 0 && s.kind != SymbolKind::Section =>
                                    {
                                        window.sites.push(MachineSite {
                                            offset: off,
                                            kind: call_kind,
                                            callee: Some(s.name.clone()),
                                            reloc: Some(r.kind),
                                            in_trap_tail: false,
                                        });
                                    }
                                    (Some(_), Some(callee)) => {
                                        window.sites.push(MachineSite {
                                            offset: off,
                                            kind: call_kind,
                                            callee: Some(callee.clone()),
                                            reloc: Some(r.kind),
                                            in_trap_tail: false,
                                        });
                                    }
                                    _ => {
                                        window.sites.push(MachineSite {
                                            offset: off,
                                            kind: call_kind,
                                            callee: None,
                                            reloc: Some(r.kind),
                                            in_trap_tail: false,
                                        });
                                        unknown.insert(format!(
                                        "{} at {off:#x} names a section or a non-zero addend, not \
                                         a symbol's entry",
                                        r.kind.name()
                                    ));
                                    }
                                }
                            }
                        } else if !r.kind.is_admitted(object.format) {
                            // An unmodeled relocation kind on a branch: consumed
                            // by this function, which it makes Unknown.
                            consume(idx, r, "unmodeled", window);
                            window.sites.push(MachineSite {
                                offset: off,
                                kind: call_kind,
                                callee: None,
                                reloc: Some(r.kind),
                                in_trap_tail: false,
                            });
                            unknown.insert(format!(
                                "unmodeled relocation kind {} on the branch at {off:#x}",
                                r.kind.name()
                            ));
                        }
                        // An ADMITTED kind of the wrong class (a page
                        // relocation on a branch) is left unconsumed: the
                        // object refuses below.
                        if is_call {
                            succ.push(off + 4);
                        }
                    }
                    None => {
                        let target = i128::from(off) + i128::from(delta);
                        let local = u64::try_from(target)
                            .ok()
                            .and_then(|t| local_starts.get(&(section.index, t)))
                            .filter(|callee| **callee != wsym || is_call);
                        match local {
                            // A Mach-O object that sets MH_SUBSECTIONS_VIA_SYMBOLS
                            // lets the linker cut its sections at every symbol
                            // and dead-strip (rustc passes `-dead_strip` to
                            // every macOS link) or reorder each piece. An
                            // unrelocated branch into another symbol's piece
                            // keeps no reference to it: the linker may drop or
                            // move the callee and leave the displacement aimed
                            // at whatever lands there.
                            Some(callee) if *callee != wsym && subsections_via_symbols(object) => {
                                window.sites.push(MachineSite {
                                    offset: off,
                                    kind: call_kind,
                                    callee: None,
                                    reloc: None,
                                    in_trap_tail: false,
                                });
                                unknown.insert(format!(
                                    "unrelocated branch at {off:#x} targets `{callee}`, another \
                                     symbol's subsection of an object with \
                                     MH_SUBSECTIONS_VIA_SYMBOLS: a linker that cuts at symbols \
                                     keeps no reference to it"
                                ));
                                if is_call {
                                    succ.push(off + 4);
                                }
                            }
                            Some(callee) => {
                                window.sites.push(MachineSite {
                                    offset: off,
                                    kind: call_kind,
                                    callee: Some(callee.clone()),
                                    reloc: None,
                                    in_trap_tail: false,
                                });
                                if is_call {
                                    succ.push(off + 4);
                                }
                            }
                            _ if is_call => {
                                window.sites.push(MachineSite {
                                    offset: off,
                                    kind: call_kind,
                                    callee: None,
                                    reloc: None,
                                    in_trap_tail: false,
                                });
                                unknown.insert(format!(
                                    "unrelocated `bl` at {off:#x} targets {target:#x}, which is not \
                                     the start of a non-preemptible local extent"
                                ));
                                succ.push(off + 4);
                            }
                            _ => push_local(target, &mut succ, &mut unknown),
                        }
                    }
                }
            }
            InsnClass::CondBranch { delta } => {
                unmodeled_only(reloc, window, &mut unknown, &mut consume);
                push_local(i128::from(off) + i128::from(delta), &mut succ, &mut unknown);
                succ.push(off + 4);
            }
            InsnClass::Adrp | InsnClass::AddImm64 | InsnClass::LoadStoreUImm | InsnClass::Plain => {
                if let Some((idx, r)) = reloc {
                    let fits = match (class, r.kind) {
                        (
                            InsnClass::Adrp,
                            RelocKind::Page21 | RelocKind::GotLoadPage21 | RelocKind::AdrPrelPgHi21,
                        ) => true,
                        (InsnClass::AddImm64, RelocKind::PageOff12 | RelocKind::AddAbsLo12Nc) => {
                            true
                        }
                        (
                            InsnClass::LoadStoreUImm,
                            RelocKind::PageOff12 | RelocKind::GotLoadPageOff12,
                        ) => true,
                        (_, kind) => !kind.is_admitted(object.format),
                    };
                    if fits {
                        let role =
                            if r.kind.is_admitted(object.format) { "address" } else { "unmodeled" };
                        consume(idx, r, role, window);
                        let line = if r.kind.is_admitted(object.format) {
                            format!(
                                "address materialization ({}) at {off:#x}: symbol addresses are bound \
                                 at steps 5.7/5.9",
                                r.kind.name()
                            )
                        } else {
                            format!("unmodeled relocation kind {} at {off:#x}", r.kind.name())
                        };
                        // PKG-C5c S2a: record the admitted-kind half, line and all. The
                        // line stays in `unknown` exactly as before.
                        if r.kind.is_admitted(object.format) {
                            window.page_halves.insert(
                                off,
                                PageHalf::read(off, word, class, idx, r, line.clone()),
                            );
                        }
                        unknown.insert(line);
                    }
                }
                succ.push(off + 4);
            }
        }
        for s in &succ {
            if *s >= window.end {
                unknown.insert(format!("execution at {off:#x} falls off the end of the extent"));
            }
        }
        succ.retain(|s| *s < window.end && *s >= window.start);
        work.extend(succ.iter().copied());
        window.successors.insert(off, succ);
    }

    // INC5.4-JUMPTABLE, after the walk: a table's words are data. Nothing may
    // execute one, relocate one, or enter its dispatch run except by falling
    // through it from the bound check. Each failure is the refusal the object
    // got before the idiom was read (the table's words are unreached and never
    // padding: a zero entry targets the table itself, which the match rejects).
    for &(t0, t1) in &window.data_in_code {
        if let Some(at) = window.reachable.range(t0..t1).next() {
            return Err(ObjectRefusal::new(
                ObjectRefusalKind::UncoveredTextByte,
                format!(
                    "offset {at:#x} in `{}` is reachable but lies inside the jump table \
                     [{t0:#x}, {t1:#x})",
                    window.symbol
                ),
            ));
        }
        if let Some(r) = section.relocations.iter().find(|r| (t0..t1).contains(&r.offset)) {
            return Err(ObjectRefusal::new(
                ObjectRefusalKind::UncoveredTextByte,
                format!(
                    "{} at {:#x} relocates a word of the jump table [{t0:#x}, {t1:#x}) in `{}`",
                    r.kind.name(),
                    r.offset,
                    window.symbol
                ),
            ));
        }
    }
    for &(guard_start, br) in &dispatch_runs {
        // Scheduled loads, `b.hi`, `adr`, `ldrsw`, `add`, `br`: each is entered, by this
        // function's own edges, only from the word before it. With the `b.hi`
        // target outside the run (the matcher's check), `adr` is reached only
        // by the bound check's fall-through, so the index reaching `ldrsw` is
        // at most `k`.
        for at in (guard_start + 4..=br).step_by(4) {
            let mut preds =
                window.successors.iter().filter(|(_, s)| s.contains(&at)).map(|(p, _)| *p);
            let (first, second) = (preds.next(), preds.next());
            if first != Some(at - 4) || second.is_some() {
                return Err(ObjectRefusal::new(
                    ObjectRefusalKind::UncoveredTextByte,
                    format!(
                        "the dense-switch dispatch ending at {br:#x} in `{}` is entered at {at:#x} \
                         other than by falling through its bound check",
                        window.symbol
                    ),
                ));
            }
        }
    }

    // Trap tails: a site on a straight-line path to a `brk`/`udf` never returns.
    let trap_tail: BTreeSet<u64> = {
        let mut set = BTreeSet::new();
        for off in &window.reachable {
            if classify_insn(word_at(*off)) != InsnClass::Trap {
                continue;
            }
            let mut cur = *off;
            set.insert(cur);
            while cur > window.start {
                let prev = cur - 4;
                let only_falls_here =
                    window.successors.get(&prev).is_some_and(|s| s.as_slice() == [cur]);
                let prev_class = classify_insn(word_at(prev));
                let straight = matches!(
                    prev_class,
                    InsnClass::Plain
                        | InsnClass::BranchLink { .. }
                        | InsnClass::Adrp
                        | InsnClass::AddImm64
                        | InsnClass::LoadStoreUImm
                );
                if !(only_falls_here && straight && window.reachable.contains(&prev)) {
                    break;
                }
                set.insert(prev);
                cur = prev;
            }
        }
        set
    };
    for site in &mut window.sites {
        site.in_trap_tail = trap_tail.contains(&site.offset);
    }
    window.trap_tail = trap_tail;
    window.sites.sort_by_key(|s| s.offset);
    window.relocations.sort_by_key(|r| r.offset);

    // Coverage: every unreachable word must be padding, except a jump table's
    // (data-in-code, checked above).
    let mut off = window.start;
    while off < window.end {
        let in_table = window.data_in_code.iter().any(|&(t0, t1)| (t0..t1).contains(&off));
        if !in_table && !window.reachable.contains(&off) && !is_padding(word_at(off)) {
            return Err(ObjectRefusal::new(
                ObjectRefusalKind::UncoveredTextByte,
                format!(
                    "word {:#010x} at {off:#x} in `{}` cannot be reached from its entry and is not \
                     padding",
                    word_at(off),
                    window.symbol
                ),
            ));
        }
        off += 4;
    }
    window.unknown = unknown.into_iter().collect();
    Ok(())
}

#[cfg(test)]
mod pointer_record_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_padding_reads_every_whole_word() {
        let nop = NOP.to_le_bytes();
        assert!(all_padding(&[]));
        assert!(all_padding(&[0, 0, 0, 0]));
        assert!(all_padding(&[nop, [0; 4], nop].concat()));
        // A trailing partial word is not an instruction and is not read.
        assert!(all_padding(&[nop.as_slice(), &[0xff, 0xff]].concat()));
        assert!(!all_padding(&[nop, 0xd65f_03c0_u32.to_le_bytes()].concat()));
        assert!(!all_padding(&[[0; 4], [0, 0, 0, 1]].concat()));
    }

    #[test]
    fn the_structural_decoder_names_every_branch_class() {
        assert_eq!(classify_insn(0x9400_0000), InsnClass::BranchLink { delta: 0 });
        assert_eq!(classify_insn(0x97ff_ffff), InsnClass::BranchLink { delta: -4 });
        assert_eq!(classify_insn(0x1400_0002), InsnClass::Branch { delta: 8 });
        assert_eq!(classify_insn(0x5400_0040), InsnClass::CondBranch { delta: 8 });
        assert_eq!(classify_insn(0xb400_0040), InsnClass::CondBranch { delta: 8 });
        assert_eq!(classify_insn(0x3600_0040), InsnClass::CondBranch { delta: 8 });
        assert_eq!(classify_insn(0xd65f_03c0), InsnClass::Ret);
        assert_eq!(classify_insn(0xd61f_0200), InsnClass::IndirectBranch);
        assert_eq!(classify_insn(0xd63f_0200), InsnClass::IndirectCall);
        assert_eq!(classify_insn(0xd420_0020), InsnClass::Trap);
        assert_eq!(classify_insn(0), InsnClass::Trap);
        assert_eq!(classify_insn(NOP), InsnClass::Plain);
        assert_eq!(classify_insn(0x9100_0400), InsnClass::AddImm64);
        assert_eq!(classify_insn(0x9000_0000), InsnClass::Adrp);
        assert_eq!(classify_insn(0xf940_0000), InsnClass::LoadStoreUImm);
        // retaa: pointer-authenticated return — never read as a fall-through.
        assert_eq!(classify_insn(0xd65f_0bff), InsnClass::Unrecognized);
        // paciasp (a HINT that changes what a later ret does).
        assert_eq!(classify_insn(0xd503_233f), InsnClass::Unrecognized);
        // add x0, x0, #1 (an ordinary data-processing word).
        assert_eq!(classify_insn(0x9100_0400), InsnClass::AddImm64);
        assert_eq!(classify_insn(0x8b01_0000), InsnClass::Plain);
    }

    #[test]
    fn initializer_images_are_exact_or_absent() {
        let m = Module::new("m");
        assert_eq!(
            initializer_image(&m, &Ty::U32, &Constant::Int(0x0102_0304)),
            Some(vec![4, 3, 2, 1])
        );
        assert_eq!(initializer_image(&m, &Ty::I8, &Constant::Int(-1)), Some(vec![0xff]));
        assert_eq!(initializer_image(&m, &Ty::Bool, &Constant::Bool(true)), Some(vec![1]));
        assert_eq!(initializer_image(&m, &Ty::Ptr, &Constant::Int(0)), None);
    }
}
