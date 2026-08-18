//@ build-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off -Cdebuginfo=0
//@ rustc-env:RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info
//@ normalize-stderr: "DefId\([^)]*\)" -> "DEF_ID"
//@ normalize-stderr: "sha256:[0-9a-f]{64}" -> "LINEAGE"
//! A loop clause that binds source roots may enter the TrustIR-to-MIR flip only
//! after the v35 carrier is freshly authenticated and the shim gives every HIR
//! binding one real named MIR place. The `compiled from trust-ir` event is the
//! public execution witness; merely compiling successfully could hide fallback
//! to built MIR.
//!
//! This is the regression's positive half. In 2026-08-08 the gate was correctly
//! closed after a measured false proof: the carrier was authenticated, but the
//! shim made an anonymous loop temp while retaining a named frozen parameter.
//! The static verifier could therefore bind the invariant to the wrong place.
//! The shim now reuses one HIR-id-keyed place across entry and loop headers,
//! emits its authenticated debug identity, and refuses globally ambiguous
//! source spellings.
//!
//! `trust_ir_flip_loop_source_provenance_false_proof.rs` pins the negative half:
//! the historical witness must be refuted identically with the flip on and off.

#[inline(never)]
pub fn countdown(mut n: u32) -> u32
    requires n <= 3
{
    while n > 0 invariant n <= 3 decreases n {
        n -= 1;
    }
    n
}

#[inline(never)]
pub fn countdown_local(limit: u32) -> u32 {
    let mut n = limit;
    while n > 0 invariant n <= limit decreases n {
        n -= 1;
    }
    n
}

/// Two distinct source-loop identities whose operational states compose in
/// strict dominance order. The second loop's only seed is the first loop's
/// post-state, exercising both the authenticated header bijection and the
/// sequential multi-SCC semantic differential before the flip can fire.
#[inline(never)]
pub fn sequential_countdown(mut n: u32) -> u32
    requires n <= 3
{
    while n > 0 invariant n <= 3 decreases n {
        n -= 1;
    }
    let mut m = n;
    while m > 0 invariant m <= 3 decreases m {
        m -= 1;
    }
    m
}

fn main() {
    let _ = countdown(3);
    let _ = countdown_local(3);
    let _ = sequential_countdown(3);
}
