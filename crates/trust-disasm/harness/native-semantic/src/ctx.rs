//! The starting state, and the memory image both sides share.
//!
//! Everything here has a mirror in `natsem.c`. Where the two must agree —
//! addresses, the memory pattern, the context-block layout — the C side asserts
//! its own copy against a derived value and refuses to run if they differ,
//! rather than producing records the driver would silently misread.

use trust_machine_sem::ConcreteFlags;

/// Must match `SCRATCH_BASE` / `SCRATCH_SIZE` / `CTX_LEN` in `natsem.c`.
pub const SCRATCH_BASE: u64 = 0x0000_0004_0000_0000;
pub const SCRATCH_SIZE: u64 = 256 << 10;
pub const SCRATCH_PTR: u64 = SCRATCH_BASE + SCRATCH_SIZE / 2;
/// x0..x30 (248) + sp (8) + nzcv (8) + 8 bytes of alignment padding + 32 V
/// registers at 16 bytes. The padding exists because `LDP Q` needs a 16-byte
/// -aligned offset; `natsem.c` encodes 272 as a literal in its prologue.
pub const CTX_LEN: usize = 784;
pub const CTX_V_OFFSET: usize = 272;

#[must_use]
pub fn scratch_range() -> (u64, u64) {
    (SCRATCH_BASE, SCRATCH_BASE + SCRATCH_SIZE)
}

/// splitmix64. Must be bit-identical to `sm64` in `natsem.c`.
#[must_use]
pub fn sm64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = x;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// The 8-byte value scratch holds at an 8-byte-aligned address.
///
/// Every 8-byte word of scratch is DISTINCT, which is the property that makes a
/// wrong-address load detectable: a load from the wrong place cannot coincide
/// with the right value.
#[must_use]
pub fn pattern_u64(aligned_addr: u64) -> u64 {
    sm64(aligned_addr >> 3)
}

/// A starting register state.
///
/// WHY MORE THAN ONE. `native-invariant` sets every register to the same
/// pointer, which is right for its question (does the word fault?) and useless
/// for this one: with `x1 == x2`, an `add x0,x1,x2` that read its operands in
/// the wrong order, or read the wrong register entirely, produces exactly the
/// right answer. Distinct values are what make a swap visible; pointer-shaped
/// values are what make memory instructions reach mapped memory. No single
/// profile does both, so the sweep runs several.
#[derive(Clone)]
pub struct Profile {
    pub name: &'static str,
    pub gpr: [u64; 31],
    pub sp: u64,
    pub nzcv: u8,
    /// The SIMD/FP file, V0..V31.
    ///
    /// DELIBERATELY UNLIKE `gpr`. A profile whose `v13` happened to equal its
    /// `x13` would make the register-file confusion this harness exists to
    /// catch INVISIBLE — the wrong file would hold the right answer. These come
    /// from a different splitmix64 salt and carry a distinguishing high half, so
    /// reading the wrong file can never coincide with reading the right one.
    pub fpr: [u128; 32],
}

impl Profile {
    #[must_use]
    pub fn flags(&self) -> ConcreteFlags {
        ConcreteFlags {
            n: self.nzcv & 0b1000 != 0,
            z: self.nzcv & 0b0100 != 0,
            c: self.nzcv & 0b0010 != 0,
            v: self.nzcv & 0b0001 != 0,
        }
    }

    /// The context block `natsem.c` loads the machine from.
    #[must_use]
    pub fn to_ctx_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(CTX_LEN);
        for r in &self.gpr {
            out.extend_from_slice(&r.to_le_bytes());
        }
        out.extend_from_slice(&self.sp.to_le_bytes());
        // PSTATE-SHAPED, not a 0..15 nibble. `MSR NZCV, Xt` takes N/Z/C/V from
        // bits 31:28 of the source register and ignores every other bit, so a
        // nibble written at bit 0 sets the flags to ZERO. Measured: with the
        // nibble form, this harness reported every flag-reading instruction as
        // a model/hardware disagreement — its own bug, arriving in the exact
        // shape of the finding it exists to make.
        out.extend_from_slice(&(u64::from(self.nzcv) << 28).to_le_bytes());
        // Alignment padding to the 16-byte-aligned V block. `LDP Q` cannot
        // address 264.
        out.resize(CTX_V_OFFSET, 0);
        for v in &self.fpr {
            out.extend_from_slice(&v.to_le_bytes());
        }
        assert_eq!(out.len(), CTX_LEN, "context block layout must match natsem.c");
        out
    }
}

/// The SIMD/FP starting values for a profile.
///
/// Every register is distinct, and the high half carries `0xF9` in its top byte
/// plus the register number — so a value read out of the V file is recognisable
/// as such even in a raw diff, and cannot be confused with a GPR value (which is
/// pointer- or splitmix-shaped) or with zero.
#[must_use]
fn fp_values(seed: u64) -> [u128; 32] {
    core::array::from_fn(|i| {
        let lo = sm64(seed ^ (0x400 + i as u64));
        let hi = 0xF900_0000_0000_0000 | (i as u64) << 32 | (sm64(seed ^ (0x500 + i as u64)) >> 32);
        (u128::from(hi) << 64) | u128::from(lo)
    })
}

/// Pointer-shaped, all distinct, all far enough inside scratch that the full
/// immediate reach of a load/store lands in mapped memory.
#[must_use]
pub fn profile_pointers(seed: u64) -> Profile {
    let mut gpr = [0u64; 31];
    for (i, slot) in gpr.iter_mut().enumerate() {
        // Distinct, 8-aligned, and spread over the middle 32 KiB so that a
        // +/-32 KiB immediate stays inside the 256 KiB region.
        let jitter = sm64(seed ^ i as u64) & 0x0fff;
        *slot = SCRATCH_PTR + ((i as u64) * 0x40) + (jitter & !7);
    }
    Profile { name: "pointers", gpr, sp: SCRATCH_PTR, nzcv: 0b0000, fpr: fp_values(seed) }
}

/// Half pointers, half small values — the shape that lets register-offset
/// addressing (`ldr x0,[x1,x2]`) reach mapped memory while still varying.
#[must_use]
pub fn profile_mixed(seed: u64) -> Profile {
    let mut gpr = [0u64; 31];
    for (i, slot) in gpr.iter_mut().enumerate() {
        *slot = if i % 2 == 0 {
            SCRATCH_PTR + ((i as u64) * 0x80) + (sm64(seed ^ (0x100 + i as u64)) & 0x7f8)
        } else {
            // Small, signed-interesting, and distinct: index-shaped.
            let v = sm64(seed ^ (0x200 + i as u64));
            (v & 0x3ff) | ((v >> 40) & 1) * 0xffff_ffff_ffff_fc00
        };
    }
    Profile {
        name: "mixed",
        gpr,
        sp: SCRATCH_PTR + 0x800,
        nzcv: 0b1010,
        fpr: fp_values(seed ^ 0x11),
    }
}

/// Fully varied 64-bit values. Memory instructions mostly fault under this one
/// and are reported unchecked; arithmetic, shifts, bitfield moves, extends and
/// flag-setting forms get their widest exercise here — including the sign-bit
/// and all-ones corners a pointer-shaped value never reaches.
#[must_use]
pub fn profile_values(seed: u64) -> Profile {
    let mut gpr = [0u64; 31];
    for (i, slot) in gpr.iter_mut().enumerate() {
        let v = sm64(seed ^ (0x300 + i as u64));
        *slot = match i % 8 {
            0 => v,
            1 => v | 0x8000_0000_0000_0000,
            2 => v & 0xffff_ffff,
            3 => 0xffff_ffff_ffff_ffff,
            4 => 0,
            5 => 1u64 << (v % 64),
            6 => v.wrapping_neg(),
            _ => (v as i32) as i64 as u64,
        };
    }
    Profile { name: "values", gpr, sp: SCRATCH_PTR, nzcv: 0b1111, fpr: fp_values(seed ^ 0x22) }
}

// ---------------------------------------------------------------------------
// ADVERSARIAL PROFILES — added by the confirmation pass, NOT in the default set
// ---------------------------------------------------------------------------
//
// The three profiles above carry NZCV in {0000, 1010, 1111} only, and their
// register values are splitmix-random or pointer-shaped. Both are gaps with a
// shape:
//
//   * A condition code is a PREDICATE over N/Z/C/V, and three flag settings
//     cannot separate the sixteen of them. `GE` (N==V) and `LT` (N!=V) are
//     BOTH exercised by 1010 and 1111 only in their true-for-GE direction;
//     nothing in the default set has N set and V clear, or V set and N clear.
//     A `csel`/`ccmp`/`b.cond` arm that computed the wrong one of a
//     complementary pair could agree on all three default profiles.
//   * `0`, `1`, `-1`, `i64::MIN`, `i64::MAX` are exactly the inputs at which
//     an overflow rule, a shift-amount mask, a sign-extension or a division
//     special case changes answer, and splitmix values hit none of them.
//
// These are selected with `--profile-set` and DEFAULT OFF: the shipping gate's
// coverage floors are counts of `compared`, which is proportional to the number
// of profiles, so silently adding one would rewrite every baseline number.

/// The eight values at which a rule changes answer.
#[must_use]
fn corner(k: usize) -> u64 {
    match k % 8 {
        0 => 0,
        1 => 1,
        2 => u64::MAX,
        3 => 1u64 << 63,
        4 => (1u64 << 63) - 1,
        5 => 0xffff_ffff,
        6 => 0x8000_0000,
        _ => 0x7fff_ffff,
    }
}

/// Corner values interleaved with pointers: memory forms still reach mapped
/// memory (even registers) while arithmetic sees `0`/`-1`/`MIN`/`MAX` (odd).
#[must_use]
pub fn profile_corners(seed: u64) -> Profile {
    let mut gpr = [0u64; 31];
    for (i, slot) in gpr.iter_mut().enumerate() {
        *slot = if i % 2 == 0 {
            SCRATCH_PTR + ((i as u64) * 0x80) + (sm64(seed ^ (0x600 + i as u64)) & 0x7f8)
        } else {
            corner(i / 2)
        };
    }
    Profile { name: "corners", gpr, sp: SCRATCH_PTR + 0x1000, nzcv: 0b0110, fpr: fp_values(seed ^ 0x33) }
}

/// Every register a corner value, no pointers at all. Memory forms mostly fault
/// and are reported unchecked; this profile exists for the arithmetic,
/// bitfield, shift and flag-setting families at their boundary inputs.
#[must_use]
pub fn profile_extremes(seed: u64) -> Profile {
    let mut gpr = [0u64; 31];
    for (i, slot) in gpr.iter_mut().enumerate() {
        *slot = corner(i);
    }
    Profile { name: "extremes", gpr, sp: SCRATCH_PTR, nzcv: 0b1001, fpr: fp_values(seed ^ 0x44) }
}

/// `sp` at the very top of the scratch window: a positive immediate offset
/// leaves the shared image (reported unchecked, never guessed) while a negative
/// one stays inside it, so pre/post-index writeback and `[sp, #-imm]` are
/// compared at the edge rather than in the middle.
#[must_use]
pub fn profile_spedge(seed: u64) -> Profile {
    let mut gpr = [0u64; 31];
    for (i, slot) in gpr.iter_mut().enumerate() {
        *slot = SCRATCH_BASE + 0x100 + ((i as u64) * 0x20);
    }
    Profile {
        name: "spedge",
        gpr,
        sp: SCRATCH_BASE + SCRATCH_SIZE - 0x100,
        nzcv: 0b0101,
        fpr: fp_values(seed ^ 0x55),
    }
}

/// `sp` sixteen bytes below the 64-bit wrap. Every sp-relative ACCESS faults and
/// is excluded; `add sp,sp,#imm`, `mov x0,sp`, `sub sp,...` and the writeback
/// forms are compared, which is where an address computation that saturates
/// instead of wrapping would show.
#[must_use]
pub fn profile_spwrap(seed: u64) -> Profile {
    let mut gpr = [0u64; 31];
    for (i, slot) in gpr.iter_mut().enumerate() {
        *slot = match i % 4 {
            0 => SCRATCH_PTR + ((i as u64) * 0x40),
            1 => u64::MAX - (i as u64),
            2 => 1u64 << (i % 64),
            _ => sm64(seed ^ (0x700 + i as u64)),
        };
    }
    Profile {
        name: "spwrap",
        gpr,
        sp: 0xffff_ffff_ffff_fff0,
        nzcv: 0b0011,
        fpr: fp_values(seed ^ 0x66),
    }
}

/// IEEE special values in the SIMD/FP file.
///
/// `fp_values` above is deliberately splitmix-random, which is right for
/// catching a register-file confusion and useless for catching an arithmetic
/// one: `+0.0`, `-0.0`, the infinities, quiet and signalling NaN, the
/// subnormals and the exact powers of two are where an FP rule changes answer,
/// and a random 128-bit pattern reaches none of them.
///
/// EVEN registers carry an f64 special in the D lane; ODD ones carry an f32
/// special in the S lane, with a high half chosen so the D lane is also a
/// recognisable pattern rather than an accident.
#[must_use]
fn fp_specials(seed: u64) -> [u128; 32] {
    const F64: [u64; 16] = [
        0x0000_0000_0000_0000, // +0.0
        0x8000_0000_0000_0000, // -0.0
        0x7ff0_0000_0000_0000, // +inf
        0xfff0_0000_0000_0000, // -inf
        0x7ff8_0000_0000_0000, // quiet NaN
        0x7ff0_0000_0000_0001, // signalling NaN
        0x3ff0_0000_0000_0000, // 1.0
        0xbff0_0000_0000_0000, // -1.0
        0x0000_0000_0000_0001, // smallest subnormal
        0x000f_ffff_ffff_ffff, // largest subnormal
        0x0010_0000_0000_0000, // smallest normal
        0x7fef_ffff_ffff_ffff, // f64::MAX
        0x4000_0000_0000_0000, // 2.0
        0x3fe0_0000_0000_0000, // 0.5
        0x4330_0000_0000_0000, // 2^52 — the f64 integer-rounding boundary
        0xc330_0000_0000_0000, // -2^52
    ];
    const F32: [u32; 16] = [
        0x0000_0000, // +0.0
        0x8000_0000, // -0.0
        0x7f80_0000, // +inf
        0xff80_0000, // -inf
        0x7fc0_0000, // quiet NaN
        0x7f80_0001, // signalling NaN
        0x3f80_0000, // 1.0
        0xbf80_0000, // -1.0
        0x0000_0001, // smallest subnormal
        0x007f_ffff, // largest subnormal
        0x0080_0000, // smallest normal
        0x7f7f_ffff, // f32::MAX
        0x4000_0000, // 2.0
        0x3f00_0000, // 0.5
        0x4b00_0000, // 2^23 — the f32 integer-rounding boundary
        0xcb00_0000, // -2^23
    ];
    core::array::from_fn(|i| {
        let lo = if i % 2 == 0 {
            F64[(i / 2 + (seed as usize)) % 16]
        } else {
            // A high half that keeps the D lane a finite, ordinary double, so
            // the S-lane special is not masked by a D-lane NaN.
            0x3fd0_0000_0000_0000_u64 | u64::from(F32[(i / 2 + (seed as usize)) % 16])
        };
        let hi = 0xF900_0000_0000_0000_u64 | (i as u64) << 32;
        (u128::from(hi) << 64) | u128::from(lo)
    })
}

/// Pointer-shaped GPRs (so the SIMD load/store forms reach mapped memory) with
/// IEEE special values in the SIMD/FP file.
#[must_use]
pub fn profile_fp(seed: u64) -> Profile {
    let mut gpr = [0u64; 31];
    for (i, slot) in gpr.iter_mut().enumerate() {
        let jitter = sm64(seed ^ (0xA00 + i as u64)) & 0x0fff;
        *slot = SCRATCH_PTR + ((i as u64) * 0x40) + (jitter & !7);
    }
    Profile { name: "fp-specials", gpr, sp: SCRATCH_PTR, nzcv: 0b0110, fpr: fp_specials(seed) }
}

/// The same file rotated by one, so every (register, special) pairing that
/// matters for a two-operand instruction is reachable across the two profiles:
/// `fadd d0,d1,d2` sees a different pair here than it does above.
#[must_use]
pub fn profile_fp_rotated(seed: u64) -> Profile {
    let mut gpr = [0u64; 31];
    for (i, slot) in gpr.iter_mut().enumerate() {
        let jitter = sm64(seed ^ (0xB00 + i as u64)) & 0x0fff;
        *slot = SCRATCH_PTR + ((i as u64) * 0x40) + (jitter & !7);
    }
    Profile {
        name: "fp-rotated",
        gpr,
        sp: SCRATCH_PTR,
        nzcv: 0b1001,
        fpr: fp_specials(seed.wrapping_add(1)),
    }
}

/// One profile per NZCV setting, 0000..1111.
///
/// A condition code is a predicate over four bits; sixteen starting states is
/// the whole domain, so a conditional form compared under all of them has had
/// its predicate checked exhaustively at the flag level. The register shape is
/// deliberately NOT any of the shipping three — half pointers so the memory
/// forms stay live, half corner values so the arithmetic does.
#[must_use]
pub fn profiles_flags16(seed: u64) -> Vec<Profile> {
    const NAMES: [&str; 16] = [
        "f0000", "f000V", "f00C0", "f00CV", "f0Z00", "f0Z0V", "f0ZC0", "f0ZCV", "fN000", "fN00V",
        "fN0C0", "fN0CV", "fNZ00", "fNZ0V", "fNZC0", "fNZCV",
    ];
    (0u8..16)
        .map(|nzcv| {
            let mut gpr = [0u64; 31];
            for (i, slot) in gpr.iter_mut().enumerate() {
                *slot = if i % 2 == 0 {
                    SCRATCH_PTR + ((i as u64) * 0x80) + (sm64(seed ^ (0x800 + i as u64)) & 0x7f8)
                } else {
                    corner(i / 2 + usize::from(nzcv))
                };
            }
            Profile {
                name: NAMES[nzcv as usize],
                gpr,
                sp: SCRATCH_PTR + 0x400,
                nzcv,
                fpr: fp_values(seed ^ 0x900 ^ u64::from(nzcv)),
            }
        })
        .collect()
}
