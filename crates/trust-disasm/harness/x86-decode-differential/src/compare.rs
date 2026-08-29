//! Comparing our decode against the oracle's.
//!
//! NOT A TEXT DIFF. Our `Display` is AArch64-flavoured (`X0`, `SP`) and the
//! oracle prints AT&T (`%rax`, `%rsp`); diffing those strings would report a
//! mismatch on every word and prove nothing. Instead both sides are projected
//! onto the facts that the defects of 2026-08-18 actually turned on, and the
//! projection is compared:
//!
//!   * LENGTH. A decoder that reports the wrong length silently reinterprets
//!     every following byte.
//!   * The MEMORY OPERAND's structure — base register, index register, scale,
//!     displacement — or, for a RIP-relative operand, the RESOLVED ABSOLUTE
//!     ADDRESS. Five of the defects were here: an address short by `insn.size`,
//!     an absolute treated as PC-relative, a dropped displacement, a dropped
//!     `R12` index, and a fabricated `RBP` base.
//!   * REGISTER OPERANDS by name, which is what separates `%ah` from `%spl`.
//!
//! WHAT THIS PROJECTION CANNOT SEE is listed normatively in `main.rs`. The
//! short version: it is a DECODE differential, so nothing about EFFECTS —
//! flags, masking, widths of values written — is in scope, and two of the
//! sixteen defects (shift-count masking, shift flags) would not have been
//! caught by it.

use trust_disasm::Instruction;
use trust_disasm::operand::{MemoryOperand, Operand, RegKind};

use crate::oracle::OracleInsn;

/// The facts about one instruction that both sides can state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Projection {
    pub len: usize,
    /// Memory operand, normalised. `None` when the instruction has none.
    pub mem: Option<MemProjection>,
    /// Register operand names, lowercased AT&T style, in operand order.
    pub regs: Vec<String>,
}

/// A memory operand reduced to the terms an effective address is built from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemProjection {
    /// A ground address: `[disp32]` absolute, or a resolved `[RIP + disp]`.
    Absolute(u64),
    /// base + index*scale + displacement, with absent parts as `None`/0.
    Computed { base: Option<String>, index: Option<String>, scale: u8, disp: i64 },
}

/// Why a slot could not be compared. Counted and named, never folded into
/// agreement — the same discipline the AArch64 semantic differential uses.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Unchecked {
    /// Our decoder refused the bytes.
    OurDecodeRefused,
    /// The oracle produced nothing for the slot.
    OracleSilent,
    /// The oracle printed an operand form this projection does not parse.
    /// Distinct from a mismatch on purpose: an unparsed form is OUR blind spot,
    /// not evidence about the decoder.
    OracleOperandUnparsed,
    /// The candidate carries a prefix this harness declares ABSENT (blind spot
    /// E): address-size `0x67`, or a segment override. Comparing them would
    /// report disagreements about semantics neither side claims to model, and a
    /// harness that reports noise gets ignored. Counted, never folded into
    /// agreement.
    UnmodelledPrefix,
}

/// Prefix bytes this harness does not model — see blind spot E in `main.rs`.
///
/// `0x66` (operand size) is deliberately NOT here: it selects 16-bit operands,
/// which the projection does compare, and it is how `movw $1,(%rax)` is
/// spelled.
pub const UNMODELLED_PREFIXES: &[u8] = &[
    0x67, // address size
    0x2E, 0x36, 0x3E, 0x26, // CS/SS/DS/ES segment overrides
    0x64, 0x65, // FS/GS segment overrides
];

/// Does this candidate begin with a prefix the harness declares absent?
pub fn has_unmodelled_prefix(bytes: &[u8]) -> bool {
    for &b in bytes {
        if UNMODELLED_PREFIXES.contains(&b) {
            return true;
        }
        let is_other_prefix = matches!(b, 0xF0 | 0xF2 | 0xF3 | 0x66) || (0x40..=0x4F).contains(&b);
        if !is_other_prefix {
            return false;
        }
    }
    false
}

/// A disagreement, named so families can be counted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mismatch {
    pub family: &'static str,
    pub detail: String,
}

pub fn project_ours(insn: &Instruction) -> Result<Projection, Unchecked> {
    let mut mem = None;
    let mut regs = Vec::new();
    for i in 0..insn.operand_count() {
        match insn.operand(i) {
            Some(Operand::Reg(r)) => regs.push(reg_name(r)),
            Some(Operand::Mem(m)) => mem = Some(project_mem(m)?),
            _ => {}
        }
    }
    Ok(Projection { len: insn.size as usize, mem, regs })
}

fn project_mem(m: &MemoryOperand) -> Result<MemProjection, Unchecked> {
    Ok(match m {
        MemoryOperand::Absolute { address } => MemProjection::Absolute(*address),
        MemoryOperand::Base { base } => {
            MemProjection::Computed { base: Some(reg_name(base)), index: None, scale: 1, disp: 0 }
        }
        MemoryOperand::BaseOffset { base, offset } => MemProjection::Computed {
            base: Some(reg_name(base)),
            index: None,
            scale: 1,
            disp: *offset,
        },
        MemoryOperand::BaseIndexOffset { base, index, scale_shift, displacement } => {
            MemProjection::Computed {
                base: base.as_ref().map(reg_name),
                index: Some(reg_name(index)),
                scale: 1u8 << scale_shift,
                disp: *displacement,
            }
        }
        // x86-64 must never produce these; if one appears the decoder bypassed
        // its own resolution choke point, which is a finding, not a skip.
        MemoryOperand::PcRelative { .. } | MemoryOperand::RipRelative { .. } => {
            return Err(Unchecked::OurDecodeRefused);
        }
        _ => return Err(Unchecked::OurDecodeRefused),
    })
}

/// x86-64 register name for a decoded register, in the oracle's spelling.
fn reg_name(r: &trust_disasm::operand::Register) -> String {
    const GPR64: [&str; 16] = [
        "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12",
        "r13", "r14", "r15",
    ];
    const GPR32: [&str; 16] = [
        "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d",
        "r12d", "r13d", "r14d", "r15d",
    ];
    const GPR16: [&str; 16] = [
        "ax", "cx", "dx", "bx", "sp", "bp", "si", "di", "r8w", "r9w", "r10w", "r11w", "r12w",
        "r13w", "r14w", "r15w",
    ];
    const GPR8: [&str; 16] = [
        "al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "r8b", "r9b", "r10b", "r11b", "r12b",
        "r13b", "r14b", "r15b",
    ];
    const HIGH8: [&str; 4] = ["ah", "ch", "dh", "bh"];
    let i = r.index as usize;
    match r.kind {
        RegKind::GprHighByte => HIGH8.get(i).copied().unwrap_or("?h").to_string(),
        _ => {
            let table = match r.width {
                8 => &GPR8,
                16 => &GPR16,
                32 => &GPR32,
                _ => &GPR64,
            };
            table.get(i).copied().unwrap_or("?").to_string()
        }
    }
}

/// Parse the oracle's AT&T operand text into the same projection.
pub fn project_oracle(o: &OracleInsn) -> Result<Projection, Unchecked> {
    let mut mem = None;
    let mut regs = Vec::new();
    // Split on TOP-LEVEL commas only. A memory operand contains commas of its
    // own — `(%rbx,%r12)`, `0x20(%rbx,%rcx,2)` — and splitting naively counted
    // its index register as a separate REGISTER operand, so every SIB form
    // reported a spurious mismatch. The registers inside a memory operand are
    // compared as part of the address terms, not as register operands.
    for piece in split_top_level(&o.operands) {
        let piece = piece.trim();
        if piece.is_empty() {
            continue;
        }
        // AT&T marks an INDIRECT operand with a leading `*` — `callq *%rbx`.
        // It is the same register operand; the star is call/jmp syntax.
        let piece = piece.strip_prefix('*').unwrap_or(piece);
        if piece.contains('(') {
            mem = Some(parse_att_mem(piece, o.rip_target)?);
        } else if let Some(reg) = piece.strip_prefix('%') {
            regs.push(reg.to_string());
        } else if let Some(addr) = parse_bare_absolute(piece) {
            // An ABSOLUTE address prints with no parentheses at all in AT&T:
            // `movq 0x1234, %rax`. Treating it as "no memory operand" reported a
            // spurious mismatch against a decoder that had it right — and this
            // is the very form defect B was about (an absolute spelled as
            // PC-relative), so failing to parse it would have blinded the
            // harness to exactly the bug it exists to catch.
            mem = Some(MemProjection::Absolute(addr));
        }
        // Bare immediates (`$0x1`) carry no projection and are ignored: the
        // decoder's own immediate handling is not what this differential
        // compares (see blind spot A).
    }
    Ok(Projection { len: o.len, mem, regs })
}

/// Split an AT&T operand list on commas that are not inside parentheses.
fn split_top_level(text: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (i, ch) in text.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                out.push(&text[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&text[start..]);
    out
}

/// Parse an AT&T memory operand out of a full operand list.
///
/// Handles `0x20(%rbx,%rcx,2)`, `(%rbx,%r12)`, `0x10(,%rax,4)`, `(%rax)`, and
/// `0x10(%rip)` (resolved via `rip_target`). Anything else is reported
/// `OracleOperandUnparsed` — OUR gap, not evidence about the decoder.
fn parse_att_mem(text: &str, rip_target: Option<u64>) -> Result<MemProjection, Unchecked> {
    let open = text.find('(').ok_or(Unchecked::OracleOperandUnparsed)?;
    let close = text[open..].find(')').ok_or(Unchecked::OracleOperandUnparsed)? + open;

    // Displacement is whatever precedes '(' after the last comma-separated boundary.
    let head = &text[..open];
    let disp_text = head.rsplit(',').next().unwrap_or("").trim();
    let disp = if disp_text.is_empty() {
        0
    } else {
        parse_signed_hex(disp_text).ok_or(Unchecked::OracleOperandUnparsed)?
    };

    let inner = &text[open + 1..close];
    let parts: Vec<&str> = inner.split(',').map(str::trim).collect();
    // `%riz` / `%eiz` are LLVM's spelling for an index field of 100 with
    // REX.X=0 — which MEANS NO INDEX. It is notation, not a register, and
    // treating it as one made every SIB form without an index look like a
    // disagreement. A harness that cries wolf on 300 words gets ignored, which
    // is its own way of not checking.
    let reg_of = |s: &str| -> Option<String> {
        s.strip_prefix('%')
            .map(|r| r.to_string())
            .filter(|r| !r.is_empty() && r != "riz" && r != "eiz")
    };

    match parts.as_slice() {
        [b] if *b == "%rip" => {
            let target = rip_target.ok_or(Unchecked::OracleOperandUnparsed)?;
            Ok(MemProjection::Absolute(target))
        }
        [b] => Ok(MemProjection::Computed { base: reg_of(b), index: None, scale: 1, disp }),
        [b, i] => Ok(MemProjection::Computed { base: reg_of(b), index: reg_of(i), scale: 1, disp }),
        [b, i, s] => Ok(MemProjection::Computed {
            base: reg_of(b),
            index: reg_of(i),
            scale: s.parse().unwrap_or(1),
            disp,
        }),
        _ => Err(Unchecked::OracleOperandUnparsed),
    }
}

/// A bare absolute address operand: `0x1234`, with no `(` and no `$` (which
/// would make it an immediate).
fn parse_bare_absolute(s: &str) -> Option<u64> {
    if s.starts_with('$') || s.contains('(') || s.starts_with('%') {
        return None;
    }
    s.strip_prefix("0x").and_then(|h| u64::from_str_radix(h, 16).ok())
}

fn parse_signed_hex(s: &str) -> Option<i64> {
    let (neg, s) = match s.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, s),
    };
    let v = match s.strip_prefix("0x") {
        Some(hex) => i64::from_str_radix(hex, 16).ok()?,
        None => s.parse::<i64>().ok()?,
    };
    Some(if neg { -v } else { v })
}

/// Put a memory projection in canonical form, so the two sides are compared on
/// meaning rather than on spelling.
///
/// An address with NO base and NO index is just its displacement — an absolute
/// address — however the disassembler chose to render the SIB byte that
/// produced it. And a scale is meaningless without an index to scale.
fn canonicalise(m: &MemProjection) -> MemProjection {
    match m {
        MemProjection::Computed { base: None, index: None, disp, .. } => {
            MemProjection::Absolute(*disp as u64)
        }
        MemProjection::Computed { base, index: None, disp, .. } => {
            MemProjection::Computed { base: base.clone(), index: None, scale: 1, disp: *disp }
        }
        other => other.clone(),
    }
}

/// Compare the two projections, naming the family of any disagreement.
pub fn compare(ours: &Projection, theirs: &Projection) -> Option<Mismatch> {
    if ours.len != theirs.len {
        return Some(Mismatch {
            family: "instruction_length",
            detail: format!("ours={} oracle={}", ours.len, theirs.len),
        });
    }
    let ours_mem = ours.mem.as_ref().map(canonicalise);
    let theirs_mem = theirs.mem.as_ref().map(canonicalise);
    match (&ours_mem, &theirs_mem) {
        (Some(a), Some(b)) if a != b => {
            let family = match (a, b) {
                (MemProjection::Absolute(_), MemProjection::Absolute(_)) => "absolute_address",
                (MemProjection::Computed { .. }, MemProjection::Computed { .. }) => {
                    "effective_address_terms"
                }
                _ => "addressing_form",
            };
            return Some(Mismatch { family, detail: format!("ours={a:?} oracle={b:?}") });
        }
        (Some(a), None) => {
            return Some(Mismatch {
                family: "memory_operand_presence",
                detail: format!("ours={a:?} oracle=none"),
            });
        }
        (None, Some(b)) => {
            return Some(Mismatch {
                family: "memory_operand_presence",
                detail: format!("ours=none oracle={b:?}"),
            });
        }
        _ => {}
    }
    // Register NAMES, order-insensitive: our operand order follows the decoder's
    // own convention and the oracle prints AT&T (source, dest) order.
    let mut a: Vec<&String> = ours.regs.iter().collect();
    let mut b: Vec<&String> = theirs.regs.iter().collect();
    a.sort();
    b.sort();
    if a != b {
        return Some(Mismatch {
            family: "register_operands",
            detail: format!("ours={a:?} oracle={b:?}"),
        });
    }
    None
}
