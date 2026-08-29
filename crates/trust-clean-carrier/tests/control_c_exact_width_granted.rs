// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! CONTROL (c) — THE POSITIVE.
//!
//! The fix is not "refuse everything". An exact-width carrier IS granted, and
//! it is the ONLY thing that reaches `CarrierEvidence::Total`.

use clean_kernel::{Expr, Name};
use trust_clean_carrier::{CleanType, carrier_at, carrier_for};
use trust_symbols::CarrierEvidence;
use trust_types::Ty;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

#[test]
fn uint64_to_u64_is_granted() {
    let carrier = carrier_at(&c("UInt64"), &Ty::Int { width: 64, signed: false })
        .expect("UInt64 -> u64 is exact: it must be granted");
    assert_eq!(carrier.clean(), CleanType::UInt(64));
    assert_eq!(*carrier.rust(), Ty::Int { width: 64, signed: false });
    assert_eq!(carrier.evidence(), CarrierEvidence::Total);
}

#[test]
fn every_supported_exact_width_is_granted() {
    for (clean, width) in [("UInt8", 8_u32), ("UInt16", 16), ("UInt32", 32), ("UInt64", 64)] {
        let carrier = carrier_at(&c(clean), &Ty::Int { width, signed: false })
            .unwrap_or_else(|e| panic!("{clean} -> u{width} must be granted: {e}"));
        assert_eq!(carrier.evidence(), CarrierEvidence::Total);
    }
}

#[test]
fn bool_to_bool_is_granted() {
    let carrier = carrier_at(&c("Bool"), &Ty::Bool).expect("Bool -> bool is exact");
    assert_eq!(carrier.clean(), CleanType::Bool);
    assert_eq!(carrier.evidence(), CarrierEvidence::Total);
}

#[test]
fn the_default_carrier_is_the_exact_one() {
    let carrier = carrier_for(&c("UInt32")).expect("UInt32 has a default carrier");
    assert_eq!(*carrier.rust(), Ty::Int { width: 32, signed: false });
    let b = carrier_for(&c("Bool")).expect("Bool has a default carrier");
    assert_eq!(*b.rust(), Ty::Bool);
}
