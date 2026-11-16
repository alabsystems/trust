//@ needs-trust-verify
//@ add-minicore
//@ edition: 2021
//@ revisions: i686 wasm32 wasm32_certify wasm32_memory_safe wasm32_advisory x86_64 aarch64
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[i686] compile-flags: --target i686-unknown-linux-gnu
//@[i686] needs-llvm-components: x86
//@[i686] check-fail
//@[wasm32] compile-flags: --target wasm32-unknown-unknown
//@[wasm32] needs-llvm-components: webassembly
//@[wasm32] check-fail
//@[wasm32_certify] compile-flags: --target wasm32-unknown-unknown -Ztrust-policy=certify
//@[wasm32_certify] needs-llvm-components: webassembly
//@[wasm32_certify] check-fail
//@[wasm32_memory_safe] compile-flags: --target wasm32-unknown-unknown -Ztrust-policy=memory-safe
//@[wasm32_memory_safe] needs-llvm-components: webassembly
//@[wasm32_memory_safe] check-fail
//@[wasm32_advisory] compile-flags: --target wasm32-unknown-unknown -Ztrust-policy=advisory
//@[wasm32_advisory] needs-llvm-components: webassembly
//@[wasm32_advisory] check-pass
//@[x86_64] compile-flags: --target x86_64-unknown-linux-gnu
//@[x86_64] needs-llvm-components: x86
//@[x86_64] check-pass
//@[aarch64] compile-flags: --target aarch64-unknown-linux-gnu
//@[aarch64] needs-llvm-components: aarch64
//@[aarch64] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//[i686]~? ERROR Trust verification cannot accept a build for `i686-unknown-linux-gnu`: its pointers are 32 bits wide
//[wasm32]~? ERROR Trust verification cannot accept a build for `wasm32-unknown-unknown`: its pointers are 32 bits wide
//[wasm32_certify]~? ERROR Trust verification cannot accept a build for `wasm32-unknown-unknown`: its pointers are 32 bits wide
//[wasm32_memory_safe]~? ERROR Trust verification cannot accept a build for `wasm32-unknown-unknown`: its pointers are 32 bits wide
//[wasm32_advisory]~? WARN Trust verification cannot accept a build for `wasm32-unknown-unknown`: its pointers are 32 bits wide
//! Trust (2026-10-02): the narrow-target rule
//! (`compiler/rustc_mir_transform/src/trust_verify/narrow_target.rs`;
//! docs/KNOWN_HAZARDS.md, "CLOSED 2026-10-02 — on a target narrower than 64 bits,
//! the default policy's 64-bit allocation premises accepted programs that panic"),
//! pinned in the HOST ui suite.
//!
//! `narrow_target_growth_refused.rs` holds the measured std shapes (a `push` on a
//! full 1 GiB `Vec<u8>`, a widening `collect`, `Vec::<u128>::with_capacity(..)`,
//! ...) and needs a 32-bit std, so it runs only when the ui suite itself targets
//! a 32-bit triple (`//@ only-32bit`). This fixture needs no std at all: it
//! cross-checks a `#![no_core]` crate against `minicore` for each target, so the
//! host suite proves on every run that the refusal is decided by the target's
//! pointer width — and by nothing else: the crate below has no collection, no
//! allocation and no panic, and is refused on `i686`/`wasm32` under every
//! fail-closed policy (the default, `certify`, `memory-safe`), reported as a
//! warning under the advisory survey, and accepted for the two 64-bit controls
//! (`x86_64`, `aarch64`).
//!
//! Measured 2026-10-02 against this crate (`--emit=metadata`, minicore built
//! verify-off, each revision's flags): the fix's stage 1 (`0.10.0+g22b2a384c`)
//! refused `i686`, `wasm32`, `wasm32_certify` and `wasm32_memory_safe` (rc=1, this
//! error), and built `wasm32_advisory` (rc=0, this warning), `x86_64` and
//! `aarch64`; main `0.10.0+ga3be88bbd` built all seven (rc=0).

#![feature(no_core)]
#![no_core]

extern crate minicore;
use minicore::*;

pub fn same(x: u32) -> u32 {
    x
}
