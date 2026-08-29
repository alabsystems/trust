// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The constant tables are spec-derived, and this is the proof.**
//!
//! FIPS 180-4 does not merely tabulate the initial hash values and round
//! constants — it *defines* them:
//!
//! | Table | Definition | Spec |
//! |---|---|---|
//! | SHA-256 `H(0)` | first 32 bits of the fractional parts of the square roots of primes 1..8 | §5.3.3 |
//! | SHA-224 `H(0)` | second 32 bits of the fractional parts of the square roots of primes 9..16 | §5.3.2 |
//! | SHA-512 `H(0)` | first 64 bits of the fractional parts of the square roots of primes 1..8 | §5.3.5 |
//! | SHA-384 `H(0)` | first 64 bits of the fractional parts of the square roots of primes 9..16 | §5.3.4 |
//! | `K{256}` | first 32 bits of the fractional parts of the cube roots of primes 1..64 | §4.2.2 |
//! | `K{512}` | first 64 bits of the fractional parts of the cube roots of primes 1..80 | §4.2.3 |
//!
//! This file re-computes all six tables from those definitions in **exact
//! integer arithmetic** — no floating point, so no rounding argument is needed
//! — and compares against what `sha256.rs` and `sha512.rs` declare. It shares
//! no code with them.
//!
//! Why bother when the known-answer tests already exist: a KAT tells you *that*
//! something is wrong, and every KAT fails at once when any single constant is
//! wrong. This tells you *which* constant, and it makes the tables auditable
//! without trusting that whoever typed them copied from the right document.
//!
//! # The arithmetic
//!
//! `floor(frac(sqrt(p)) * 2^k)` is `floor(sqrt(p * 2^(2k))) mod 2^k`, and
//! `floor(frac(cbrt(p)) * 2^k)` is `floor(cbrt(p * 2^(3k))) mod 2^k`. For
//! `k = 64` and `p < 512` those intermediate values need up to 256 bits, so
//! there is a minimal fixed-width big-integer below: multiply and compare, which
//! is all a binary search for an integer root requires.

use trust_sha2::{sha256_spec_tables as sha256, sha512_spec_tables as sha512};

// ---------------------------------------------------------------------------
// A 256-bit unsigned integer: four little-endian 64-bit limbs.
// Multiply and compare only — enough to binary-search an integer root.
// ---------------------------------------------------------------------------

type U256 = [u64; 4];

fn from_u128(value: u128) -> U256 {
    [value as u64, (value >> 64) as u64, 0, 0]
}

/// `value * 2^(64 * limb)`, i.e. `value` placed in limb position `limb`.
fn at_limb(value: u64, limb: usize) -> U256 {
    let mut result = [0u64; 4];
    result[limb] = value;
    result
}

/// Schoolbook multiply. `None` when the product does not fit in 256 bits,
/// which the search below reads as "the candidate is too large".
fn mul(a: U256, b: U256) -> Option<U256> {
    let mut result = [0u64; 4];
    for i in 0..4 {
        if a[i] == 0 {
            continue;
        }
        let mut carry: u128 = 0;
        for j in 0..4 {
            if b[j] == 0 && carry == 0 {
                continue;
            }
            if i + j >= 4 {
                // Anything landing at or beyond limb 4 has overflowed.
                return None;
            }
            let current = u128::from(result[i + j]) + u128::from(a[i]) * u128::from(b[j]) + carry;
            result[i + j] = current as u64;
            carry = current >> 64;
        }
        if carry != 0 {
            return None;
        }
    }
    Some(result)
}

fn less_or_equal(a: U256, b: U256) -> bool {
    for index in (0..4).rev() {
        if a[index] != b[index] {
            return a[index] < b[index];
        }
    }
    true
}

/// The largest `x` with `x^power <= target`. `power` is 2 or 3.
fn integer_root(target: U256, power: u32) -> u128 {
    let fits = |x: u128| -> bool {
        let x = from_u128(x);
        let mut accumulated = x;
        for _ in 1..power {
            match mul(accumulated, x) {
                Some(value) => accumulated = value,
                None => return false,
            }
        }
        less_or_equal(accumulated, target)
    };

    // Upper bound: sqrt(2^256) = 2^128 and cbrt(2^256) < 2^86, but every target
    // here is far smaller. 2^70 covers all of them with room to spare, and the
    // assertion below fails loudly rather than silently clamping if that is
    // ever untrue.
    let mut low: u128 = 0;
    let mut high: u128 = 1 << 70;
    assert!(!fits(high), "integer_root upper bound is too small for this target");
    while high - low > 1 {
        let mid = low + (high - low) / 2;
        if fits(mid) { low = mid } else { high = mid }
    }
    low
}

// ---------------------------------------------------------------------------
// The FIPS 180-4 definitions.
// ---------------------------------------------------------------------------

/// The first `count` prime numbers, by trial division. The 80th is 409.
fn primes(count: usize) -> Vec<u64> {
    let mut found: Vec<u64> = Vec::with_capacity(count);
    let mut candidate = 2u64;
    while found.len() < count {
        if found.iter().take_while(|p| *p * *p <= candidate).all(|p| candidate % p != 0) {
            found.push(candidate);
        }
        candidate += 1;
    }
    found
}

/// `floor(frac(sqrt(p)) * 2^32)` — "the first thirty-two bits of the fractional
/// part of the square root of p".
fn sqrt_fraction_32(prime: u64) -> u32 {
    // floor(sqrt(p) * 2^32) = floor(sqrt(p * 2^64)); the fractional part is the
    // low 32 bits.
    integer_root(at_limb(prime, 1), 2) as u32
}

/// `floor(frac(sqrt(p)) * 2^64)`.
fn sqrt_fraction_64(prime: u64) -> u64 {
    integer_root(at_limb(prime, 2), 2) as u64
}

/// `floor(frac(cbrt(p)) * 2^32)`.
fn cbrt_fraction_32(prime: u64) -> u32 {
    // p * 2^96 = p << 32 placed in limb 1.
    integer_root(at_limb(prime << 32, 1), 3) as u32
}

/// `floor(frac(cbrt(p)) * 2^64)`.
fn cbrt_fraction_64(prime: u64) -> u64 {
    integer_root(at_limb(prime, 3), 3) as u64
}

// ---------------------------------------------------------------------------
// The tests.
// ---------------------------------------------------------------------------

/// The root search itself, against values checkable by hand.
///
/// Without this, a broken `integer_root` would "derive" the same wrong
/// constants as a broken table and every check below would pass. The
/// derivation is only evidence if the deriver is independently pinned.
#[test]
fn integer_root_is_correct() {
    assert_eq!(integer_root(from_u128(0), 2), 0);
    assert_eq!(integer_root(from_u128(1), 2), 1);
    assert_eq!(integer_root(from_u128(3), 2), 1);
    assert_eq!(integer_root(from_u128(4), 2), 2);
    assert_eq!(integer_root(from_u128(99), 2), 9);
    assert_eq!(integer_root(from_u128(100), 2), 10);
    assert_eq!(integer_root(from_u128(u128::from(u64::MAX)), 2), 4_294_967_295);

    assert_eq!(integer_root(from_u128(7), 3), 1);
    assert_eq!(integer_root(from_u128(8), 3), 2);
    assert_eq!(integer_root(from_u128(26), 3), 2);
    assert_eq!(integer_root(from_u128(27), 3), 3);
    assert_eq!(integer_root(from_u128(1_000_000), 3), 100);

    // 2^128 in limb 2; its square root is exactly 2^64.
    assert_eq!(integer_root(at_limb(1, 2), 2), 1u128 << 64);
    // 2^192 in limb 3; its cube root is exactly 2^64.
    assert_eq!(integer_root(at_limb(1, 3), 3), 1u128 << 64);
}

#[test]
fn primes_are_the_primes() {
    let first = primes(80);
    assert_eq!(&first[..10], &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]);
    assert_eq!(first[63], 311, "the 64th prime bounds K256");
    assert_eq!(first[79], 409, "the 80th prime bounds K512");
}

#[test]
fn sha256_initial_hash_value_is_derived() {
    // §5.3.3: square roots of the first eight primes.
    let derived: Vec<u32> = primes(8).into_iter().map(sqrt_fraction_32).collect();
    assert_eq!(derived.as_slice(), sha256::IV_256.as_slice());
}

#[test]
fn sha224_initial_hash_value_is_derived() {
    // §5.3.2: the SECOND thirty-two bits of the square roots of the ninth
    // through sixteenth primes — i.e. the low half of the 64-bit fraction.
    let derived: Vec<u32> = primes(16)[8..]
        .iter()
        .map(|&prime| (sqrt_fraction_64(prime) & 0xffff_ffff) as u32)
        .collect();
    assert_eq!(derived.as_slice(), sha256::IV_224.as_slice());
}

#[test]
fn sha512_initial_hash_value_is_derived() {
    // §5.3.5: square roots of the first eight primes, 64 bits.
    let derived: Vec<u64> = primes(8).into_iter().map(sqrt_fraction_64).collect();
    assert_eq!(derived.as_slice(), sha512::IV_512.as_slice());
}

#[test]
fn sha384_initial_hash_value_is_derived() {
    // §5.3.4: square roots of the ninth through sixteenth primes, 64 bits.
    let derived: Vec<u64> = primes(16)[8..].iter().copied().map(sqrt_fraction_64).collect();
    assert_eq!(derived.as_slice(), sha512::IV_384.as_slice());
}

#[test]
fn k256_round_constants_are_derived() {
    // §4.2.2: cube roots of the first sixty-four primes.
    let derived: Vec<u32> = primes(64).into_iter().map(cbrt_fraction_32).collect();
    assert_eq!(derived.as_slice(), sha256::K256.as_slice());
}

#[test]
fn k512_round_constants_are_derived() {
    // §4.2.3: cube roots of the first eighty primes.
    let derived: Vec<u64> = primes(80).into_iter().map(cbrt_fraction_64).collect();
    assert_eq!(derived.as_slice(), sha512::K512.as_slice());
}

/// The 32-bit and 64-bit tables are two windows on one derivation, so they must
/// agree where they overlap. Catches a table that was derived correctly but
/// pasted into the wrong constant.
#[test]
fn the_two_width_families_agree_where_they_overlap() {
    for (index, (&narrow, &wide)) in sha256::K256.iter().zip(sha512::K512.iter()).enumerate() {
        assert_eq!(
            u64::from(narrow),
            wide >> 32,
            "K256[{index}] is not the top half of K512[{index}]"
        );
    }
    for (index, (&narrow, &wide)) in sha256::IV_256.iter().zip(sha512::IV_512.iter()).enumerate() {
        assert_eq!(
            u64::from(narrow),
            wide >> 32,
            "SHA-256 IV[{index}] is not the top half of the SHA-512 IV"
        );
    }
    for (index, (&narrow, &wide)) in sha256::IV_224.iter().zip(sha512::IV_384.iter()).enumerate() {
        assert_eq!(
            u64::from(narrow),
            wide & 0xffff_ffff,
            "SHA-224 IV[{index}] is not the bottom half of the SHA-384 IV"
        );
    }
}
