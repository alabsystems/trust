//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ check-fail
//! Verified-sysroot plan §5 step 6: the blanket-`Drop` shape is REFUSED, per
//! §4.3 — "Blanket Φ on `core::ops::Drop::drop` is rejected: it turns every
//! `impl Drop` in the dependency graph into a hard error." A user cannot write
//! the attribute on `core::ops::Drop`'s definition (they do not own core), so
//! the shape that reaches for a Drop contract is the attribute on an
//! `impl Drop` — and it is refused with the named reason and the affordable
//! variant spelled out (D3: the refusal carries the fix).
//!
//! If this fixture ever passes, the opt-in boundary of step 6 has been erased
//! and every `impl Drop` in every dependency is one enforcement flip away from
//! a hard error nobody asked for.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(register_tool)]
#![register_tool(trust)]

pub struct Holder(u32);

#[trust::panic_free_drop]
impl Drop for Holder {
    //~^ ERROR may not target `core::ops::Drop`
    fn drop(&mut self) {
        self.0 = 0;
    }
}

// Deliberately EMPTY: dropping a `Holder` anywhere would charge that body an
// (unrelated) fail-closed drop-glue obligation, and this fixture would then be
// red without the refusal under test — a vacuous falsifier. MEASURED on the
// pre-change stage1 (2026-08-30): with `drop(Holder(7))` in `main` the fixture
// already failed for exactly that other reason.
fn main() {}
