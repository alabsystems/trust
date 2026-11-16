//@ needs-trust-verify
//@ edition: 2021
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-verify-function-budget-ms=1000 -Ztrust-verify-timeout-ms=200 --crate-type=lib
//! Compiler-side regression gate for the VC-generation budget blowup found by
//! the 2026-09 verifier-on census of `library/core`: VC GENERATION alone (not
//! solving) exceeded the 5000 ms per-function budget for twenty bodies, three
//! of which are transcribed verbatim below — `fmt::num::imp::<impl u32>::
//! _fmt_inner` (+ its u8/usize siblings), `num::imp::int_sqrt::u64_stages`
//! and `slice::ascii::is_ascii`.
//!
//! With the pre-memo `trust-vcgen` (trustc 1.99.0-dev acb08e761) this file
//! FAILS: `-Ztrust-verify-function-budget-ms=1000` is enough, on a quiet host,
//! for `u64_stages`, `fmt_inner_u8`, `fmt_inner_u32` and `fmt_inner_usize` to
//! each report "Trust verification exceeded its per-function budget (1000 ms /
//! 64000000 steps) during VC generation" — the `preprocessing_budget_exceeded`
//! checkpoint in `trust_verify.rs`. The root cause and fix live in
//! `crates/trust-vcgen/src/fn_memo.rs` (whole-body analyses re-derived inside
//! the obligation walk's inner loops, now memoized once per function per
//! scope); after it, generation for these bodies is tens of milliseconds in a
//! release build, so the 1000 ms budget carries a wide margin. The budget here
//! is deliberately the WALL-CLOCK half: the step half is charged at only a
//! handful of sites (contracts, type lowering) and never saw this blowup, so
//! a step bound cannot gate it. `-Ztrust-verify-timeout-ms=200` keeps the
//! solver phase short — the verdicts are irrelevant to this gate and advisory
//! policy downgrades every refutation to a warning; `check-pass` plus
//! `dont-check-compiler-stderr` is exactly "compiled, no hard error".
//!
//! This test is only meaningful against a trustc rebuilt with the fixed
//! `trust-vcgen` (the crate lives in the compiler); the in-crate tests in
//! `crates/trust-vcgen/tests/vcgen_budget_realmir.rs` gate the same bodies —
//! as the compiler's own `-Ztrust-dump=mir:` output of THIS file — without a
//! rebuild, and pin the deterministic analysis-computation counts.
#![allow(dead_code, unused_unsafe, clippy::all)]
use core::mem::MaybeUninit;

// ---- library/core/src/slice/ascii.rs (generic, non-SSE2 lane) ----------------

#[inline]
pub const fn is_ascii_simple(mut bytes: &[u8]) -> bool {
    while let [rest @ .., last] = bytes {
        if !last.is_ascii() {
            break;
        }
        bytes = rest;
    }
    bytes.is_empty()
}

const fn contains_nonascii(v: usize) -> bool {
    const NONASCII_MASK: usize = 0x8080_8080_8080_8080_u64 as usize;
    (NONASCII_MASK & v) != 0
}

#[inline]
pub fn is_ascii(s: &[u8]) -> bool {
    const USIZE_SIZE: usize = size_of::<usize>();

    let len = s.len();
    let align_offset = s.as_ptr().align_offset(USIZE_SIZE);

    if len < USIZE_SIZE || len < align_offset || USIZE_SIZE < align_of::<usize>() {
        return is_ascii_simple(s);
    }

    let offset_to_aligned = if align_offset == 0 { USIZE_SIZE } else { align_offset };

    let start = s.as_ptr();
    // SAFETY: We verify `len < USIZE_SIZE` above.
    let first_word = unsafe { (start as *const usize).read_unaligned() };

    if contains_nonascii(first_word) {
        return false;
    }
    debug_assert!(offset_to_aligned <= len);

    let mut word_ptr = unsafe { start.add(offset_to_aligned) as *const usize };
    let mut byte_pos = offset_to_aligned;

    debug_assert!(word_ptr.is_aligned());

    while byte_pos < len - USIZE_SIZE {
        debug_assert!(byte_pos + USIZE_SIZE <= len);
        debug_assert!(word_ptr.cast::<u8>() == start.wrapping_add(byte_pos));

        let word = unsafe { word_ptr.read() };
        if contains_nonascii(word) {
            return false;
        }

        byte_pos += USIZE_SIZE;
        word_ptr = unsafe { word_ptr.add(1) };
    }

    debug_assert!(byte_pos <= len && len - byte_pos <= USIZE_SIZE);

    let last_word = unsafe { (start.add(len - USIZE_SIZE) as *const usize).read_unaligned() };

    !contains_nonascii(last_word)
}

// ---- library/core/src/num/imp/int_sqrt.rs -------------------------------------

const U8_ISQRT_WITH_REMAINDER: [(u8, u8); 256] = {
    let mut result = [(0, 0); 256];

    let mut n: usize = 0;
    let mut isqrt_n: usize = 0;
    while n < result.len() {
        result[n] = (isqrt_n as u8, (n - isqrt_n.pow(2)) as u8);

        n += 1;
        if n == (isqrt_n + 1).pow(2) {
            isqrt_n += 1;
        }
    }

    result
};

macro_rules! first_stage {
    ($original_bits:literal, $n:ident) => {{
        debug_assert!($n != 0, "`$n` is  zero in `first_stage!`.");

        const N_SHIFT: u32 = $original_bits - 8;
        let n = $n >> N_SHIFT;

        let (s, r) = U8_ISQRT_WITH_REMAINDER[n as usize];
        unsafe { core::hint::assert_unchecked(s != 0) };
        (s, r)
    }};
}

macro_rules! middle_stage {
    ($original_bits:literal, $ty:ty, $n:ident, $s:ident, $r:ident) => {{
        debug_assert!($s != 0, "`$s` is  zero in `middle_stage!`.");

        const N_SHIFT: u32 = $original_bits - <$ty>::BITS;
        let n = ($n >> N_SHIFT) as $ty;

        const HALF_BITS: u32 = <$ty>::BITS >> 1;
        const QUARTER_BITS: u32 = <$ty>::BITS >> 2;
        const LOWER_HALF_1_BITS: $ty = (1 << HALF_BITS) - 1;
        const LOWEST_QUARTER_1_BITS: $ty = (1 << QUARTER_BITS) - 1;

        let lo = n & LOWER_HALF_1_BITS;
        let numerator = (($r as $ty) << QUARTER_BITS) | (lo >> QUARTER_BITS);
        let denominator = ($s as $ty) << 1;
        let q = numerator / denominator;
        let u = numerator % denominator;

        let mut s = ($s << QUARTER_BITS) as $ty + q;
        let (mut r, overflow) =
            ((u << QUARTER_BITS) | (lo & LOWEST_QUARTER_1_BITS)).overflowing_sub(q * q);
        if overflow {
            r = r.wrapping_add(2 * s - 1);
            s -= 1;
        }
        unsafe { core::hint::assert_unchecked(s != 0) };
        (s, r)
    }};
}

macro_rules! last_stage {
    ($ty:ty, $n:ident, $s:ident, $r:ident) => {{
        debug_assert!($s != 0, "`$s` is  zero in `last_stage!`.");

        const HALF_BITS: u32 = <$ty>::BITS >> 1;
        const QUARTER_BITS: u32 = <$ty>::BITS >> 2;
        const LOWER_HALF_1_BITS: $ty = (1 << HALF_BITS) - 1;

        let lo = $n & LOWER_HALF_1_BITS;
        let numerator = (($r as $ty) << QUARTER_BITS) | (lo >> QUARTER_BITS);
        let denominator = ($s as $ty) << 1;

        let q = numerator / denominator;
        let mut s = ($s << QUARTER_BITS) as $ty + q;
        let (s_squared, overflow) = s.overflowing_mul(s);
        if overflow || s_squared > $n {
            s -= 1;
        }
        s
    }};
}

#[inline]
pub const fn u32_stages(n: u32) -> u32 {
    let (s, r) = first_stage!(32, n);
    let (s, r) = middle_stage!(32, u16, n, s, r);
    last_stage!(u32, n, s, r)
}

#[inline]
pub const fn u64_stages(n: u64) -> u64 {
    let (s, r) = first_stage!(64, n);
    let (s, r) = middle_stage!(64, u16, n, s, r);
    let (s, r) = middle_stage!(64, u32, n, s, r);
    last_stage!(u64, n, s, r)
}

// ---- library/core/src/fmt/num.rs -----------------------------------------------

static DECIMAL_PAIRS: &[u8; 200] = b"\
      0001020304050607080910111213141516171819\
      2021222324252627282930313233343536373839\
      4041424344454647484950515253545556575859\
      6061626364656667686970717273747576777879\
      8081828384858687888990919293949596979899";

macro_rules! impl_fmt_inner {
    ($Unsigned:ident, $name:ident) => {
        pub unsafe fn $name(this: $Unsigned, buf: &mut [MaybeUninit<u8>]) -> usize {
            // Count the number of bytes in buf that are not initialized.
            let mut offset = buf.len();
            // Consume the least-significant decimals from a working copy.
            let mut remain = this;

            // Format per four digits from the lookup table.
            // Four digits need a 16-bit $Unsigned or wider.
            while size_of::<$Unsigned>() > 1 && remain > 999.try_into().expect("branch is not hit for types that cannot fit 999 (u8)") {
                unsafe { core::hint::assert_unchecked(offset >= 4) }
                unsafe { core::hint::assert_unchecked(offset <= buf.len()) }
                offset -= 4;

                // pull two pairs
                let scale: $Unsigned = 1_00_00.try_into().expect("branch is not hit for types that cannot fit 1E4 (u8)");
                let quad = remain % scale;
                remain /= scale;
                let pair1 = (quad / 100) as usize;
                let pair2 = (quad % 100) as usize;
                buf[offset + 0].write(DECIMAL_PAIRS[pair1 * 2 + 0]);
                buf[offset + 1].write(DECIMAL_PAIRS[pair1 * 2 + 1]);
                buf[offset + 2].write(DECIMAL_PAIRS[pair2 * 2 + 0]);
                buf[offset + 3].write(DECIMAL_PAIRS[pair2 * 2 + 1]);
            }

            // Format per two digits from the lookup table.
            if remain > 9 {
                unsafe { core::hint::assert_unchecked(offset >= 2) }
                unsafe { core::hint::assert_unchecked(offset <= buf.len()) }
                offset -= 2;

                let pair = (remain % 100) as usize;
                remain /= 100;
                buf[offset + 0].write(DECIMAL_PAIRS[pair * 2 + 0]);
                buf[offset + 1].write(DECIMAL_PAIRS[pair * 2 + 1]);
            }

            // Format the last remaining digit, if any.
            if remain != 0 || this == 0 {
                unsafe { core::hint::assert_unchecked(offset >= 1) }
                unsafe { core::hint::assert_unchecked(offset <= buf.len()) }
                offset -= 1;

                let last = (remain & 15) as usize;
                buf[offset].write(DECIMAL_PAIRS[last * 2 + 1]);
            }

            offset
        }
    };
}

impl_fmt_inner!(u8, fmt_inner_u8);
impl_fmt_inner!(u32, fmt_inner_u32);
impl_fmt_inner!(usize, fmt_inner_usize);
