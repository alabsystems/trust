//! Starting states and the shared memory image.

pub const SCRATCH_BASE: u64 = 0x4_0000_0000;
pub const SCRATCH_SIZE: u64 = 256 << 10;
pub const SCRATCH_PTR: u64 = SCRATCH_BASE + SCRATCH_SIZE / 2;

pub fn scratch_range() -> (u64, u64) {
    (SCRATCH_BASE, SCRATCH_BASE + SCRATCH_SIZE)
}

/// splitmix64. Must be bit-identical to `pattern` in `natsem86.c` and to the
/// AArch64 twin's `sm64` — one memory image, not two agreeing guesses.
pub fn sm64(x: u64) -> u64 {
    let x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = x;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

pub fn pattern_u64(aligned_addr: u64) -> u64 {
    sm64(aligned_addr >> 3)
}

/// A starting register state. Registers are in the DECODER's numbering:
/// rax rcx rdx rbx rsp rbp rsi rdi r8..r15 — gpr[4] is rsp on the record side,
/// carried separately as `sp` on the model side.
pub struct Profile {
    pub name: &'static str,
    pub gpr: [u64; 16],
    /// SF<<3 | ZF<<2 | CF<<1 | OF, the model's N Z C V order.
    pub flags: u8,
}

impl Profile {
    /// RFLAGS image for the context block: the four modeled flags placed at
    /// their architectural bits, plus bit 1 (always-one on x86).
    pub fn rflags(&self) -> u64 {
        let sf = u64::from(self.flags >> 3 & 1);
        let zf = u64::from(self.flags >> 2 & 1);
        let cf = u64::from(self.flags >> 1 & 1);
        let of = u64::from(self.flags & 1);
        0x2 | cf | zf << 6 | sf << 7 | of << 11
    }

    pub fn ctx_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(136);
        for r in self.gpr {
            out.extend_from_slice(&r.to_le_bytes());
        }
        out.extend_from_slice(&self.rflags().to_le_bytes());
        out
    }
}

/// The shipping profiles. Every recorded number is over exactly this set.
pub fn default_profiles() -> Vec<Profile> {
    let mut regular = [0u64; 16];
    for (i, r) in regular.iter_mut().enumerate() {
        // Distinct, pointer-free values; keep memory operands inside scratch
        // via the registers most encodings use as bases.
        *r = 0x0101_0101_0101_0101u64.wrapping_mul(i as u64 + 1);
    }
    regular[4] = SCRATCH_PTR; // rsp
    regular[6] = SCRATCH_PTR; // rsi
    regular[7] = SCRATCH_PTR + 0x40; // rdi
    regular[3] = SCRATCH_PTR - 0x40; // rbx
    regular[0] = SCRATCH_PTR + 0x80; // rax — SIB bases love rax

    let mut corners = [0u64; 16];
    let corner_vals = [
        0u64,
        u64::MAX,
        0x8000_0000_0000_0000,
        0x7FFF_FFFF_FFFF_FFFF,
        0, // rsp, set below
        1,
        0,             // rsi, set below
        0xFFFF_FFFF,   // rdi: 32-bit boundary
        0x8000_0000,   // r8: sign bit of the 32-bit half
        u64::from(u32::MAX),
        2,
        0x55AA_55AA_55AA_55AA,
        0xAA55_AA55_AA55_AA55,
        0x8000_0000_0000_0000,
        u64::MAX,
        3,
    ];
    corners.copy_from_slice(&corner_vals);
    corners[4] = SCRATCH_PTR + 8; // rsp near, but not at, the window middle
    corners[6] = SCRATCH_BASE + 0x100; // rsi near the window base

    vec![
        Profile { name: "regular", gpr: regular, flags: 0b0000 },
        Profile { name: "corners", gpr: corners, flags: 0b0110 },
        Profile { name: "flags-set", gpr: regular, flags: 0b1011 },
    ]
}
