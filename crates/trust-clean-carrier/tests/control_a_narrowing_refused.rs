// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! CONTROL (a) — THE NARROWING CONTROL.
//!
//! A carrier NARROWING without a discharged embedding must be REFUSED.
//! Concretely: Clean `Nat` is unbounded; Rust `u64` is not. `Nat -> u64` must
//! not be granted a carrier merely because the two "look" like numbers.
//!
//! This control is the one that decides whether `clean { def big : Nat := 2 ^ 64 }`
//! used at `u64` is a build error or a wrong binary.

use clean_kernel::{Expr, Name};
use trust_clean_carrier::{CarrierRefused, carrier_at};
use trust_types::Ty;

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

#[test]
fn nat_to_u64_is_refused() {
    let refusal = carrier_at(&nat(), &u64_ty())
        .expect_err("Nat -> u64 is a narrowing: it must NOT be granted a carrier");

    assert!(
        matches!(refusal, CarrierRefused::Narrowing { .. }),
        "the refusal must name the narrowing, not some incidental gap; got {refusal:?}"
    );
}

#[test]
fn nat_to_every_machine_width_is_refused() {
    for width in [8_u32, 16, 32, 64] {
        let requested = Ty::Int { width, signed: false };
        assert!(
            carrier_at(&nat(), &requested).is_err(),
            "Nat -> u{width} is a narrowing and must be refused, not truncated"
        );
    }
}

#[test]
fn the_refusal_names_the_fix_with_options() {
    let refusal = carrier_at(&nat(), &u64_ty()).expect_err("Nat -> u64 must be refused");
    let text = refusal.to_string();

    // v7/D3: a refusal must carry the fix, WITH OPTIONS.
    assert!(text.contains("Nat"), "the refusal must name the Clean type: {text}");
    assert!(text.contains("u64") || text.contains("64"), "must name the width: {text}");
    assert!(text.contains("options:"), "v7/D3: must offer options: {text}");
    let option_count = text.matches('(').count();
    assert!(option_count >= 2, "v7/D3 says OPTIONS, plural; got {option_count} in: {text}");
}

#[test]
fn a_narrowing_between_machine_widths_is_also_refused() {
    // UInt64 -> u32 is the same defect one size down, and must be caught by the
    // same rule rather than by a special case for `Nat`.
    let uint64 = Expr::const_(Name::from_string("UInt64"), vec![]);
    let refusal = carrier_at(&uint64, &Ty::Int { width: 32, signed: false })
        .expect_err("UInt64 -> u32 is a narrowing and must be refused");
    assert!(
        matches!(refusal, CarrierRefused::Narrowing { .. }),
        "expected a narrowing refusal; got {refusal:?}"
    );
}
