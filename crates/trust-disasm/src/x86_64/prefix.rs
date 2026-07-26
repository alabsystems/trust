// x86-64 prefix parsing
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Reference: Intel SDM Vol 2A, Chapter 2 — Instruction Format.
// x86-64 instructions can have up to 4 legacy prefix bytes plus a REX prefix.

/// Decoded REX prefix (byte 0x40-0x4F in 64-bit mode).
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct Rex {
    /// REX prefix was present.
    pub(crate) present: bool,
    /// W bit: 1 = 64-bit operand size.
    pub(crate) w: bool,
    /// R bit: extends ModR/M reg field.
    pub(crate) r: bool,
    /// X bit: extends SIB index field.
    pub(crate) x: bool,
    /// B bit: extends ModR/M rm field, SIB base field, or opcode reg field.
    pub(crate) b: bool,
}

impl Rex {
    /// Decode a REX byte (0x40-0x4F).
    #[must_use]
    pub(crate) fn decode(byte: u8) -> Self {
        Self {
            present: true,
            w: byte & 0x08 != 0,
            r: byte & 0x04 != 0,
            x: byte & 0x02 != 0,
            b: byte & 0x01 != 0,
        }
    }

    /// True if this byte is a REX prefix.
    #[must_use]
    #[inline]
    pub(crate) fn is_rex(byte: u8) -> bool {
        byte & 0xF0 == 0x40
    }
}

/// Legacy prefix groups (at most one from each group).
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct LegacyPrefixes {
    /// Group 1: LOCK (0xF0), REPNE/REPNZ (0xF2), REP/REPE/REPZ (0xF3).
    pub(crate) group1: Option<u8>,
    /// Group 2: Segment overrides (0x2E, 0x36, 0x3E, 0x26, 0x64, 0x65)
    /// or branch hints (0x2E=not taken, 0x3E=taken).
    pub(crate) group2: Option<u8>,
    /// Group 3: Operand-size override (0x66).
    pub(crate) operand_size: bool,
    /// Group 4: Address-size override (0x67).
    pub(crate) address_size: bool,
}

/// All prefix state for an x86-64 instruction.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct Prefixes {
    pub(crate) legacy: LegacyPrefixes,
    pub(crate) rex: Rex,
    /// Number of prefix bytes consumed (to compute instruction offset).
    pub(crate) len: usize,
}

impl Prefixes {
    /// Parse prefixes from a byte slice. Returns prefixes and the number of bytes consumed.
    ///
    /// Legacy prefixes precede REX. REX must be immediately before the opcode.
    /// If a legacy prefix appears after REX, the REX is ignored (not valid).
    pub(crate) fn parse(bytes: &[u8]) -> Self {
        let mut prefixes = Prefixes::default();
        let mut pos = 0;

        while pos < bytes.len() {
            let b = bytes[pos];
            match b {
                // Group 1
                0xF0 | 0xF2 | 0xF3 => {
                    prefixes.legacy.group1 = Some(b);
                    prefixes.rex = Rex::default(); // REX before legacy is ignored
                    pos += 1;
                }
                // Group 2 — segment overrides
                0x2E | 0x36 | 0x3E | 0x26 | 0x64 | 0x65 => {
                    prefixes.legacy.group2 = Some(b);
                    prefixes.rex = Rex::default();
                    pos += 1;
                }
                // Group 3 — operand size
                0x66 => {
                    prefixes.legacy.operand_size = true;
                    prefixes.rex = Rex::default();
                    pos += 1;
                }
                // Group 4 — address size
                0x67 => {
                    prefixes.legacy.address_size = true;
                    prefixes.rex = Rex::default();
                    pos += 1;
                }
                // REX prefix (0x40-0x4F)
                b if Rex::is_rex(b) => {
                    prefixes.rex = Rex::decode(b);
                    pos += 1;
                    // REX must be last prefix — stop prefix parsing.
                    break;
                }
                // Not a prefix byte — done.
                _ => break,
            }
        }

        prefixes.len = pos;
        prefixes
    }

    /// Effective operand size in bits, given the default 32-bit mode.
    /// REX.W => 64, 0x66 prefix => 16, else => 32.
    #[must_use]
    pub(crate) fn operand_size(&self) -> u16 {
        if self.rex.w {
            64
        } else if self.legacy.operand_size {
            16
        } else {
            32
        }
    }

    /// True if the mandatory prefix is 0xF3 (used for some opcode map entries).
    #[must_use]
    pub(crate) fn has_rep(&self) -> bool {
        self.legacy.group1 == Some(0xF3)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rex_decode() {
        let rex = Rex::decode(0x48);
        assert!(rex.present);
        assert!(rex.w);
        assert!(!rex.r);
        assert!(!rex.x);
        assert!(!rex.b);
    }

    #[test]
    fn test_rex_all_bits() {
        let rex = Rex::decode(0x4F);
        assert!(rex.w);
        assert!(rex.r);
        assert!(rex.x);
        assert!(rex.b);
    }

    #[test]
    fn test_rex_is_rex() {
        assert!(Rex::is_rex(0x40));
        assert!(Rex::is_rex(0x4F));
        assert!(!Rex::is_rex(0x39));
        assert!(!Rex::is_rex(0x50));
    }

    #[test]
    fn test_no_prefixes() {
        let p = Prefixes::parse(&[0x89, 0xC0]);
        assert_eq!(p.len, 0);
        assert!(!p.rex.present);
    }

    #[test]
    fn test_rex_prefix_alone() {
        let p = Prefixes::parse(&[0x48, 0x89, 0xC0]);
        assert_eq!(p.len, 1);
        assert!(p.rex.present);
        assert!(p.rex.w);
    }

    #[test]
    fn test_operand_size_prefix() {
        let p = Prefixes::parse(&[0x66, 0x89, 0xC0]);
        assert_eq!(p.len, 1);
        assert!(p.legacy.operand_size);
        assert_eq!(p.operand_size(), 16);
    }

    #[test]
    fn test_rex_w_overrides_66() {
        // REX.W after 0x66 — REX.W wins for operand size
        let p = Prefixes::parse(&[0x66, 0x48, 0x89, 0xC0]);
        assert_eq!(p.len, 2);
        assert!(p.legacy.operand_size);
        assert!(p.rex.w);
        assert_eq!(p.operand_size(), 64);
    }

    #[test]
    fn test_multiple_legacy_prefixes() {
        let p = Prefixes::parse(&[0xF0, 0x66, 0x48, 0x89]);
        assert_eq!(p.len, 3);
        assert_eq!(p.legacy.group1, Some(0xF0));
        assert!(p.legacy.operand_size);
        assert!(p.rex.w);
    }
}
