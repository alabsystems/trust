// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use core::arch::aarch64::{
    uint32x4_t, vaddq_u32, vld1q_u8, vld1q_u32, vreinterpretq_u32_u8, vrev32q_u8, vsha256h2q_u32,
    vsha256hq_u32, vsha256su0q_u32, vsha256su1q_u32, vst1q_u32,
};

use super::{BLOCK_SIZE, K256};

/// FIPS 180-4 §6.2.2 in groups of four rounds. SHA256SU0/SU1 extend the
/// four-vector rolling message schedule and SHA256H/H2 advance both halves
/// of the state from the same pre-round state.
pub(super) fn compress(state: &mut [u32; 8], block: &[u8; BLOCK_SIZE]) {
    // SAFETY: this module is built only with guaranteed little-endian ARM
    // SHA2 and NEON. Each load/store touches four words inside the exact
    // eight-word state, 64-byte block or 64-word round constant table.
    unsafe {
        let first = vld1q_u32(state.as_ptr());
        let second = vld1q_u32(state.as_ptr().add(4));
        let mut abcd = first;
        let mut efgh = second;
        let mut schedule: [uint32x4_t; 4] = core::array::from_fn(|index| {
            vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr().add(index * 16))))
        });
        for group in 0..16 {
            let lane = group % 4;
            if group >= 4 {
                schedule[lane] = vsha256su1q_u32(
                    vsha256su0q_u32(schedule[lane], schedule[(lane + 1) % 4]),
                    schedule[(lane + 2) % 4],
                    schedule[(lane + 3) % 4],
                );
            }
            let wk = vaddq_u32(schedule[lane], vld1q_u32(K256.as_ptr().add(group * 4)));
            let previous_abcd = abcd;
            abcd = vsha256hq_u32(previous_abcd, efgh, wk);
            efgh = vsha256h2q_u32(efgh, previous_abcd, wk);
        }
        vst1q_u32(state.as_mut_ptr(), vaddq_u32(first, abcd));
        vst1q_u32(state.as_mut_ptr().add(4), vaddq_u32(second, efgh));
    }
}
