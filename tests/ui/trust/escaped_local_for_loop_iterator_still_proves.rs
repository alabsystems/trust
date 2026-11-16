//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict -Copt-level=0 --crate-type lib -Ztrust-ir-lower=off
// `-Ztrust-ir-lower=off`: this pin is about the vcgen iterator tracers (every row below
// must PROVE), not about the direct trust-ir producer. With the producer on, `Range<A>::next`
// is a still-generic bodyless declaration the v41 module validator refuses at finalization
// ([RustAbiVararg] / unsignable-rust-abi-declaration), which is the fleet's producer campaign
// (reports/2026-09-14-rust-abi-vararg-producer-half.md) and would mask this check-pass.
//@ check-pass
//@ dont-check-compiler-stderr
//! Trust: 2026-09-16 — THE `for`-LOOP PRECISION CONTROL for
//! `escaped_local_modulo_divisor_stays_closed.rs`.
//!
//! That file pins that `local_defs::body_unique_value_def` refuses the
//! `LocalWrite::Escape` channel. Every Rust `for` loop is on that channel: the
//! `Iterator::next` desugar `&mut`-borrows the loop's iterator local once per
//! iteration (`_7 = &mut _5; next(move _7)`), so the yield and trip-count tracers
//! that resolved that local through the value resolver lost their answer with
//! the closure, and correct programs of exactly these shapes were REFUTED with
//! counterexamples no execution reaches (`t = 18446744073709551615` on the
//! accumulator below).
//!
//! THIS file is the recovery, measured: the tracers migrated onto the ORIGIN
//! question (`local_defs::unique_initializing_def`) through one entrance,
//! `generate::iterator_yield::iterator_origin_def`, gated on the affirmative
//! conduit allow-list `iter_mut_borrows_only_feed_next` and reading only what
//! the yield-set argument licenses (`v < end`, an UPPER bound on the trip count;
//! the range's `start` is withheld across the hop). Every function here proved
//! on the pristine prebuilt stage1 driver BEFORE the closure (2026-09-16:
//! `u64_acc` 2 proved, `range_acc` 3 proved, `range_acc_from1` 3 proved,
//! `grid_plain` 4 proved, `stray_next` 2 proved, `rev_index` 2 proved, all
//! `0 failed`) and must prove again after it. If this file ever fails, the
//! escape refusal has grown from a closed hole into a capability loss.
//!
//! `-Ztrust-policy=strict` rather than `certify`: this file is about the
//! VERDICT the recovered tracers produce, and a proof the kernel does not
//! re-check is still a proof for that purpose; the certification boundary is
//! measured elsewhere.

/// The MUST-PROVE corpus row (`tests/trust-falsification/proved/wide_unsigned_accumulator.rs`).
pub fn u64_acc(a: &[u8; 64]) -> u64 {
    let mut t: u64 = 0;
    for &x in a {
        t += x as u64;
    }
    t
}

/// A range-driven reduction: the trip count is read through the origin hop with
/// `start` withheld, so it is `end` alone — sound for an unsigned range and enough.
pub fn range_acc(a: &[u8; 64]) -> u64 {
    let mut t: u64 = 0;
    for i in 0..64usize {
        t += a[i] as u64;
    }
    t
}

/// The same with a non-zero `start`: the bound is `64` for 63 real trips — looser, true.
pub fn range_acc_from1(a: &[u8; 64]) -> u64 {
    let mut t: u64 = 0;
    for i in 1..64usize {
        t += a[i] as u64;
    }
    t
}

/// The reviewer's flattened-index program; `build_flattened_index_facts` reads only
/// the range ENDS.
pub fn grid_plain(g: &[u8; 6]) -> u8 {
    let mut s = 0u8;
    for y in 0..2usize {
        for x in 0..3usize {
            let i = y * 3 + x;
            s = s.wrapping_add(g[i]);
        }
    }
    s
}

/// Both `&mut it` conduits feed `next`; the loop yields `1..8`, all `< 8`.
pub fn stray_next(a: &[u8; 8]) -> u8 {
    let mut it = 0..8usize;
    let _ = it.next();
    let mut s = 0u8;
    for i in it {
        s = s.wrapping_add(a[i]);
    }
    s
}

/// `Rev::next` retracts the inner `end`; the yield-set reading (`every yield < 8`)
/// is what the tracer relies on, and it holds.
pub fn rev_index(a: &[u8; 8]) -> u8 {
    let mut s = 0u8;
    for i in (0..8usize).rev() {
        s = s.wrapping_add(a[i]);
    }
    s
}
