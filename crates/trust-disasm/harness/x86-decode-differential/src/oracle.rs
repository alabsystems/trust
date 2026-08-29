//! The oracle: LLVM's disassembler, reached by assembling candidates into an
//! object and reading `objdump -d`.
//!
//! WHY NOT NATIVE EXECUTION, as the AArch64 harnesses use. Measured on this
//! host (Apple M5 Max, arm64 darwin): an `-arch x86_64` Mach-O BUILDS but will
//! not run — `bad CPU type in executable` — and Rosetta's `oahd` is not
//! running. There is no x86-64 CPU here to be ground truth, so the consequent
//! cannot be "agrees with the hardware". It is "agrees with an INDEPENDENT
//! disassembler", which is a weaker oracle and is stated as such in `main.rs`.
//!
//! THE SLOT LAYOUT. Candidates are emitted at a fixed 16-byte stride padded
//! with `0xCC` (`int3`), because the longest x86-64 instruction is 15 bytes. So
//! candidate `i` starts at address `16 * i` no matter how long its predecessor
//! decoded, and a length disagreement is CONTAINED to one slot instead of
//! desynchronising the whole stream. Detecting that disagreement is a purpose
//! of the harness, not an obstacle to it: a decoder that reports the wrong
//! length silently reinterprets every following byte.

use std::io::Write;
use std::process::Command;

/// The stride between candidates. 16 > 15, the longest x86-64 instruction.
pub const SLOT: usize = 16;

/// What the oracle says about one slot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleInsn {
    /// Length in bytes, from the byte listing.
    pub len: usize,
    /// Mnemonic, e.g. `movq`, `jp`.
    pub mnemonic: String,
    /// Operand text exactly as printed, e.g. `0x20(%rbx,%rcx,2), %rdx`.
    pub operands: String,
    /// The resolved target of a RIP-relative operand, when the disassembler
    /// printed one (`## 0x17 <_probe+0x17>`). This is what makes the oracle
    /// able to see an address that is short by `insn.size`.
    pub rip_target: Option<u64>,
}

/// Disassemble `candidates` (each a byte string) and return one entry per slot.
///
/// `None` means the oracle produced nothing for that slot — it could not
/// disassemble those bytes. That is a legitimate answer and is counted, never
/// treated as agreement.
pub fn disassemble(
    candidates: &[Vec<u8>],
    workdir: &std::path::Path,
) -> Result<Vec<Option<OracleInsn>>, String> {
    let asm_path = workdir.join("candidates.s");
    let obj_path = workdir.join("candidates.o");

    let mut asm = String::from("    .text\n    .globl _probe\n_probe:\n");
    for c in candidates {
        if c.len() > SLOT {
            return Err(format!("candidate longer than the {SLOT}-byte slot: {} bytes", c.len()));
        }
        let mut row: Vec<String> = c.iter().map(|b| format!("{b}")).collect();
        row.extend(std::iter::repeat("0xcc".to_string()).take(SLOT - c.len()));
        asm.push_str("    .byte ");
        asm.push_str(&row.join(","));
        asm.push('\n');
    }
    std::fs::File::create(&asm_path)
        .and_then(|mut f| f.write_all(asm.as_bytes()))
        .map_err(|e| format!("writing {}: {e}", asm_path.display()))?;

    let assembled = Command::new("clang")
        .args(["-arch", "x86_64", "-c"])
        .arg(&asm_path)
        .arg("-o")
        .arg(&obj_path)
        .output()
        .map_err(|e| format!("clang: {e}"))?;
    if !assembled.status.success() {
        return Err(format!("clang failed: {}", String::from_utf8_lossy(&assembled.stderr)));
    }

    let dis = Command::new("objdump")
        .arg("-d")
        .arg(&obj_path)
        .output()
        .map_err(|e| format!("objdump: {e}"))?;
    if !dis.status.success() {
        return Err(format!("objdump failed: {}", String::from_utf8_lossy(&dis.stderr)));
    }

    Ok(parse(&String::from_utf8_lossy(&dis.stdout), candidates.len()))
}

/// Parse `objdump -d` output into one entry per slot.
///
/// Only the instruction that STARTS a slot is taken; the `int3` padding and any
/// bytes the oracle decoded past a shorter instruction are ignored, which is
/// exactly the containment the slot layout buys.
/// Mnemonics the oracle prints on a line of their OWN, as a bare prefix, with
/// the instruction they modify on the next line.
///
/// Measured: `f0 81 d6 ..` prints as `lock` at offset 0 and `adcl ..` at
/// offset 1. Reading only the line that starts the slot therefore saw the
/// PREFIX and reported a length of 1 against our (correct) whole-instruction
/// length — 37 spurious mismatches in a 20k random run. A prefix is part of the
/// instruction, so its bytes are folded into the one that follows.
const BARE_PREFIXES: &[&str] = &[
    "lock", "rep", "repe", "repz", "repne", "repnz", "data16", "addr32", "cs", "ds", "es", "fs",
    "gs", "ss",
    // `F2`/`F3` before certain instructions print as HLE/TSX hints, again on a
    // line of their own: `f3 94` is `xrelease` + `xchgl %esp, %eax`.
    "xacquire", "xrelease",
];

fn parse(text: &str, slots: usize) -> Vec<Option<OracleInsn>> {
    let mut out = vec![None; slots];
    // Bytes of bare-prefix lines seen since the last slot boundary.
    let mut pending_prefix: Option<(usize, usize)> = None; // (slot, bytes)
    for line in text.lines() {
        // `       0: 48 8b 05 10 00 00 00         	movq	0x10(%rip), %rax        ## 0x17 <...>`
        let Some((addr_part, rest)) = line.split_once(':') else { continue };
        let Ok(addr) = u64::from_str_radix(addr_part.trim(), 16) else { continue };
        let at_slot_start = addr as usize % SLOT == 0;
        let slot = addr as usize / SLOT;
        if slot >= slots || out[slot].is_some() {
            continue;
        }
        // A line continues a pending prefix when it directly follows it inside
        // the same slot.
        let continues_prefix = match pending_prefix {
            Some((pslot, pbytes)) => pslot == slot && addr as usize == pslot * SLOT + pbytes,
            None => false,
        };
        if !at_slot_start && !continues_prefix {
            continue;
        }
        // Bytes are hex pairs up to the first tab; the text follows.
        let Some((bytes_text, insn_text)) = rest.split_once('\t') else { continue };
        let len = bytes_text.split_whitespace().filter(|t| t.len() == 2).count();
        if len == 0 {
            continue;
        }
        let insn_text = insn_text.trim();
        let (mnemonic, operands) = match insn_text.split_once(char::is_whitespace) {
            Some((m, rest)) => (m.trim(), rest.trim()),
            None => (insn_text, ""),
        };
        // `## 0x17 <_probe+0x17>` — the resolved RIP-relative target.
        let (operands, rip_target) = match operands.split_once("##") {
            Some((ops, comment)) => {
                let target = comment.split_whitespace().find_map(|t| {
                    t.strip_prefix("0x").and_then(|h| u64::from_str_radix(h, 16).ok())
                });
                (ops.trim(), target)
            }
            None => (operands, None),
        };
        // An INLINE prefix: objdump also prints `repne\t\tmovb %dl, %ch` on ONE
        // line. Splitting on the first whitespace then took `repne` as the
        // mnemonic and the real instruction as its operands. Peel it.
        let (mnemonic, operands) = if BARE_PREFIXES.contains(&mnemonic) && !operands.is_empty() {
            match operands.trim_start().split_once(char::is_whitespace) {
                Some((m, rest)) => (m.trim(), rest.trim()),
                None => (operands.trim(), ""),
            }
        } else {
            (mnemonic, operands)
        };
        if BARE_PREFIXES.contains(&mnemonic) && operands.is_empty() {
            let carried = pending_prefix.map_or(0, |(_, b)| b);
            pending_prefix = Some((slot, carried + len));
            continue;
        }
        let prefix_bytes = if continues_prefix { pending_prefix.map_or(0, |(_, b)| b) } else { 0 };
        pending_prefix = None;
        out[slot] = Some(OracleInsn {
            len: len + prefix_bytes,
            mnemonic: mnemonic.to_string(),
            operands: operands.trim_end_matches(&[' ', '\t'][..]).to_string(),
            rip_target,
        });
    }
    out
}
