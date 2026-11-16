//@ [unchk_pass] compile-flags: -Zcontract-checks=no
//@ [unchk_fail] compile-flags: -Zcontract-checks=yes -Cstrip=none
//@ [chk_pass] compile-flags: -Zcontract-checks=no
//@ [chk_fail] compile-flags: -Zcontract-checks=yes -Cstrip=none

// Trust (2026-09-16): `-Cstrip=none` on the two revisions that build this aux
// with CONTRACT CHECKS ON. compiletest passes `-Cstrip=debuginfo` to every
// command it builds, and on macOS that combination produces a dylib whose
// Mach-O LINKEDIT string pool the linker then refuses:
//
//     ld: mis-aligned LINKEDIT string pool, fileOffset=0x0000C144 in libid.dylib
//
// so `#chk_fail` and `#unchk_fail` never reached the runtime-contract behaviour
// they exist to check — they died at link time in the DEPENDENT crate.
//
// ISOLATED, not guessed. Measured four ways on this host: the same aux with
// `-Zcontract-checks=no` and the same `-Cstrip=debuginfo` links fine; with
// contract checks and NO strip it links fine; with both it fails; and appending
// `-Cstrip=none` (last flag wins) makes it link again. It is also NOT a
// regression from anything recent — the sealed `trust/8590` pack of 2026-09-12
// reproduces it byte-for-byte, so it predates this whole campaign.
//
// The two `_pass` revisions deliberately keep the harness default: they build
// this aux WITHOUT contract checks, do not hit the interaction, and so still
// exercise the stripped-dylib path. Dropping strip everywhere would have removed
// that coverage to fix two revisions that do not need it.
//
// This is a Mach-O/strip interaction with the extra symbols contract checks
// emit, not a verification question, and the fix is deliberately scoped to the
// two revisions it blocks rather than to `-Cstrip` in the compiler.

#![crate_type = "lib"]
#![feature(contracts)]

extern crate core;
use core::contracts::requires;

/// Example function with a spec to be called across a crate boundary.
#[requires(x > 0)]
pub fn id_if_positive(x: u32) -> u32 {
    x
}
