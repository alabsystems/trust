// Binary-data element coercion and little-endian byte codec for the §23.2 /
// §25 typed-array surface: the integer wrap conversions (ToInt8..ToUint32),
// ToUint8Clamp (round-half-to-even), IEEE-754 binary16 round-trip (no std
// f16 dependency — direct round-to-nearest-even, double-rounding-free), and
// the GetValueFromBuffer / SetValueInBuffer byte codec. All little-endian:
// TypedArray element access uses the agent's [[LittleEndian]] and every
// engine test262 calibrates against runs little-endian; DataView passes its
// own endianness flag through `encode_le`/`decode_le`.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::object::ElemType;

/// ToUintN(number) for N ∈ {8,16,32}: modular wrap of the truncated value.
#[must_use]
fn to_uint_bits(n: f64, bits: u32) -> u64 {
    if !n.is_finite() || n == 0.0 {
        return 0;
    }
    let t = n.trunc();
    let modulus = 2f64.powi(bits as i32); // exact for bits <= 32
    let m = t.abs() % modulus;
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let mut u = m as u64; // m ∈ [0, 2^bits); exact integer
    let modu = modulus as u64;
    if t < 0.0 && u != 0 {
        u = modu - u;
    }
    u
}

/// ToUint8Clamp (7.1.11): clamp to [0,255] with round-half-to-even.
#[must_use]
pub fn to_uint8_clamp(n: f64) -> u8 {
    if n.is_nan() || n <= 0.0 {
        return 0;
    }
    if n >= 255.0 {
        return 255;
    }
    let f = n.floor();
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let fi = f as u8;
    if f + 0.5 < n {
        return fi + 1;
    }
    if n < f + 0.5 {
        return fi;
    }
    // Exact tie: round to even.
    if fi % 2 == 1 {
        fi + 1
    } else {
        fi
    }
}

/// IEEE-754 binary16 encode with round-to-nearest, ties-to-even. NaN
/// canonicalizes to the positive quiet NaN (`0x7e00`), matching V8/JSC.
#[must_use]
pub fn f64_to_f16_bits(value: f64) -> u16 {
    if value.is_nan() {
        return 0x7e00;
    }
    let raw = value.to_bits();
    let sign = ((raw >> 48) & 0x8000) as u16;
    let abs = value.abs();
    if abs.is_infinite() {
        return sign | 0x7c00;
    }
    if abs == 0.0 {
        return sign;
    }
    #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
    let exp = ((raw >> 52) & 0x7ff) as i32 - 1023;
    let mantissa = raw & 0x000f_ffff_ffff_ffff;

    if exp > 15 {
        return sign | 0x7c00; // overflow to infinity
    }
    if exp >= -14 {
        // Normalized f16.
        let half_mant = (mantissa >> 42) as u16; // top 10 fraction bits
        let round_bit = (mantissa >> 41) & 1;
        let sticky = (mantissa & ((1u64 << 41) - 1)) != 0;
        #[allow(clippy::cast_sign_loss)]
        let half_exp = (exp + 15) as u16; // 1..=30
        let mut h = sign | (half_exp << 10) | half_mant;
        if round_bit == 1 && (sticky || (half_mant & 1) == 1) {
            h += 1; // carry into exponent (→ inf at the top) is correct
        }
        return h;
    }
    // Subnormal f16 (exp < -14). Smallest positive subnormal is 2^-24.
    if exp < -25 {
        return sign; // below half the smallest subnormal → signed zero
    }
    let signif = (1u64 << 52) | mantissa; // 53-bit significand
    #[allow(clippy::cast_sign_loss)]
    let shift = (28 - exp) as u32; // exp ∈ [-25,-15] → shift ∈ [43,53]
    let m = if shift >= 64 {
        0
    } else {
        let low_mask = (1u64 << shift) - 1;
        let round_pos = 1u64 << (shift - 1);
        let truncated = signif >> shift;
        let rem = signif & low_mask;
        if rem > round_pos || (rem == round_pos && (truncated & 1) == 1) {
            truncated + 1
        } else {
            truncated
        }
    };
    // m == 1024 rolls up to the smallest normal (exp field 1, mantissa 0),
    // which `sign | 1024` encodes exactly.
    sign | (m as u16)
}

/// IEEE-754 binary16 decode to f64.
#[must_use]
pub fn f16_bits_to_f64(bits: u16) -> f64 {
    let sign = if (bits & 0x8000) != 0 { -1.0 } else { 1.0 };
    let exp = ((bits >> 10) & 0x1f) as i32;
    let mant = f64::from(bits & 0x3ff);
    let mag = if exp == 0 {
        mant * 2f64.powi(-24)
    } else if exp == 0x1f {
        if mant == 0.0 {
            f64::INFINITY
        } else {
            f64::NAN
        }
    } else {
        (1.0 + mant / 1024.0) * 2f64.powi(exp - 15)
    };
    sign * mag
}

/// SetValueInBuffer's coercion+store for one Number-typed element: encode `n`
/// (already run through ToNumber) into `out` (exactly `bpe` bytes) in the
/// requested byte order. BigInt element types are never routed here.
pub fn encode_le(element: ElemType, n: f64, little_endian: bool, out: &mut [u8]) {
    let bpe = element.bytes_per_element();
    debug_assert_eq!(out.len(), bpe);
    let bytes: [u8; 8] = match element {
        ElemType::Int8 => {
            #[allow(clippy::cast_possible_truncation)]
            let v = to_uint_bits(n, 8) as u8;
            [v, 0, 0, 0, 0, 0, 0, 0]
        }
        ElemType::Uint8 => {
            #[allow(clippy::cast_possible_truncation)]
            let v = to_uint_bits(n, 8) as u8;
            [v, 0, 0, 0, 0, 0, 0, 0]
        }
        ElemType::Uint8Clamped => [to_uint8_clamp(n), 0, 0, 0, 0, 0, 0, 0],
        ElemType::Int16 | ElemType::Uint16 => {
            #[allow(clippy::cast_possible_truncation)]
            let v = to_uint_bits(n, 16) as u16;
            let b = v.to_le_bytes();
            [b[0], b[1], 0, 0, 0, 0, 0, 0]
        }
        ElemType::Int32 | ElemType::Uint32 => {
            #[allow(clippy::cast_possible_truncation)]
            let v = to_uint_bits(n, 32) as u32;
            let b = v.to_le_bytes();
            [b[0], b[1], b[2], b[3], 0, 0, 0, 0]
        }
        ElemType::Float16 => {
            let b = f64_to_f16_bits(n).to_le_bytes();
            [b[0], b[1], 0, 0, 0, 0, 0, 0]
        }
        ElemType::Float32 => {
            #[allow(clippy::cast_possible_truncation)]
            let b = (n as f32).to_le_bytes();
            [b[0], b[1], b[2], b[3], 0, 0, 0, 0]
        }
        ElemType::Float64 => n.to_le_bytes(),
        ElemType::BigInt64 | ElemType::BigUint64 => [0; 8],
    };
    if little_endian {
        out.copy_from_slice(&bytes[..bpe]);
    } else {
        for (i, o) in out.iter_mut().enumerate() {
            *o = bytes[bpe - 1 - i];
        }
    }
}

/// GetValueFromBuffer for one Number-typed element: decode exactly `bpe` bytes
/// to an f64. BigInt element types are never routed here.
#[must_use]
pub fn decode_le(element: ElemType, little_endian: bool, src: &[u8]) -> f64 {
    let bpe = element.bytes_per_element();
    debug_assert_eq!(src.len(), bpe);
    let mut b = [0u8; 8];
    if little_endian {
        b[..bpe].copy_from_slice(src);
    } else {
        for i in 0..bpe {
            b[i] = src[bpe - 1 - i];
        }
    }
    match element {
        ElemType::Int8 => f64::from(b[0] as i8),
        ElemType::Uint8 | ElemType::Uint8Clamped => f64::from(b[0]),
        ElemType::Int16 => f64::from(i16::from_le_bytes([b[0], b[1]])),
        ElemType::Uint16 => f64::from(u16::from_le_bytes([b[0], b[1]])),
        ElemType::Int32 => f64::from(i32::from_le_bytes([b[0], b[1], b[2], b[3]])),
        ElemType::Uint32 => f64::from(u32::from_le_bytes([b[0], b[1], b[2], b[3]])),
        ElemType::Float16 => f16_bits_to_f64(u16::from_le_bytes([b[0], b[1]])),
        ElemType::Float32 => f64::from(f32::from_le_bytes([b[0], b[1], b[2], b[3]])),
        ElemType::Float64 => f64::from_le_bytes(b),
        ElemType::BigInt64 | ElemType::BigUint64 => 0.0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn f16_vectors_match_node() {
        // (input f64, expected f16 bits) — captured from Node 24.5 Float16Array.
        let cases: &[(f64, u16)] = &[
            (0.0, 0x0000),
            (-0.0, 0x8000),
            (1.0, 0x3c00),
            (-1.0, 0xbc00),
            (0.5, 0x3800),
            (1.5, 0x3e00),
            (65504.0, 0x7bff),
            (65505.0, 0x7bff),
            (65520.0, 0x7c00),
            (66000.0, 0x7c00),
            (100_000.0, 0x7c00),
            (-100_000.0, 0xfc00),
            (f64::INFINITY, 0x7c00),
            (f64::NEG_INFINITY, 0xfc00),
            (f64::NAN, 0x7e00),
            (0.1, 0x2e66),
            (0.2, 0x3266),
            (3.14159, 0x4248),
            (0.000_01, 0x00a8),
            (6e-8, 0x0001),
            (1e-8, 0x0000),
            (5.960_464_477_539_063e-8, 0x0001),
            (2.980_232_238_769_531_2e-8, 0x0000),
            (1.0009765625, 0x3c01),
            (1.0004882812, 0x3c00),
            (2049.0, 0x6800),
            (2048.5, 0x6800),
            (2047.5, 0x6800),
            (0.300_000_011_920_928_96, 0x34cd),
        ];
        for (v, want) in cases {
            let got = f64_to_f16_bits(*v);
            assert_eq!(got, *want, "f16({v:?}) = 0x{got:04x}, want 0x{want:04x}");
        }
    }

    #[test]
    fn f16_round_trip_read() {
        assert_eq!(f16_bits_to_f64(0x3c00), 1.0);
        assert_eq!(f16_bits_to_f64(0x3800), 0.5);
        assert_eq!(f16_bits_to_f64(0x7bff), 65504.0);
        assert!(f16_bits_to_f64(0x7c00).is_infinite());
        assert!(f16_bits_to_f64(0x7e00).is_nan());
        assert!(f16_bits_to_f64(0x8000) == 0.0 && f16_bits_to_f64(0x8000).is_sign_negative());
        assert_eq!(f16_bits_to_f64(0x0001), 5.960_464_477_539_063e-8);
    }

    #[test]
    fn clamp_round_half_even() {
        assert_eq!(to_uint8_clamp(f64::NAN), 0);
        assert_eq!(to_uint8_clamp(-5.0), 0);
        assert_eq!(to_uint8_clamp(300.0), 255);
        assert_eq!(to_uint8_clamp(0.5), 0); // tie → even (0)
        assert_eq!(to_uint8_clamp(1.5), 2); // tie → even (2)
        assert_eq!(to_uint8_clamp(2.5), 2); // tie → even (2)
        assert_eq!(to_uint8_clamp(2.6), 3);
        assert_eq!(to_uint8_clamp(254.5), 254);
    }

    #[test]
    fn int_wrap_conversions() {
        let mut b = [0u8; 1];
        encode_le(ElemType::Int8, 256.0, true, &mut b);
        assert_eq!(b[0], 0);
        encode_le(ElemType::Int8, -1.0, true, &mut b);
        assert_eq!(decode_le(ElemType::Int8, true, &b), -1.0);
        encode_le(ElemType::Uint8, 257.0, true, &mut b);
        assert_eq!(b[0], 1);
        let mut b4 = [0u8; 4];
        encode_le(ElemType::Uint32, -1.0, true, &mut b4);
        assert_eq!(decode_le(ElemType::Uint32, true, &b4), 4_294_967_295.0);
        encode_le(ElemType::Int32, 2_147_483_648.0, true, &mut b4);
        assert_eq!(decode_le(ElemType::Int32, true, &b4), -2_147_483_648.0);
    }

    #[test]
    fn dataview_endianness() {
        let mut b = [0u8; 4];
        encode_le(ElemType::Uint32, 0x0102_0304 as f64, false, &mut b);
        assert_eq!(b, [0x01, 0x02, 0x03, 0x04]); // big-endian
        assert_eq!(decode_le(ElemType::Uint32, false, &b), f64::from(0x0102_0304u32));
        encode_le(ElemType::Uint32, 0x0102_0304 as f64, true, &mut b);
        assert_eq!(b, [0x04, 0x03, 0x02, 0x01]); // little-endian
    }
}
