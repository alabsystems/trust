//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! A call from a bundled FOREIGN (std) body into a LOCAL impl must be lowered
//! and PROVED, not reported absent.
//!
//! The two bundling lanes are split by the callee's locality:
//!
//! * `native_trust_ir_direct_local_fn_callees` (the `DefId` lane) claims LOCAL
//!   callees and bundles `optimized_mir`;
//! * `native_trust_ir_monomorphic_foreign_callees` (the B-lane) claims
//!   std/core/alloc callees and bundles a per-instance instantiated body. It
//!   DECLINES any callee whose resolved body `is_local()`, on the stated grounds
//!   that the `DefId` lane already claims it.
//!
//! That reasoning holds only if the `DefId` lane is ever offered the body doing
//! the calling. It was not: the `DefId` worklist was seeded from the root and
//! extended only from other LOCAL bodies, while the B-lane drain extended only
//! itself. So an edge from a FOREIGN body to a LOCAL impl fell through BOTH
//! lanes onto the fail-closed absent-callee arm:
//!
//! ```text
//! error: an unproven panic-freedom obligation for a call to an absent callee
//!        `<W as core::fmt::Write>::write_str` ...
//! error: Trust strict verification failed for `viamac`:
//!        1 obligation(s) were not fully verified
//! ```
//!
//! for a body that is local, has MIR, and — as `direct` below witnesses — is
//! already PROVED as its own root in the very same compilation.
//!
//! `write!` is the canonical way to hit this. It expands to
//! `w.write_fmt(args)`, whose core default body dispatches through
//! `SpecWriteFmt::spec_write_fmt`; that std body then calls back into the USER's
//! `write_str`. `direct` and `viamac` differ in nothing but that detour: same
//! sink, same string, same impl. If one proves and the other does not, the
//! difference is the lane wiring and nothing else.
//!
//! NOTE: this test is deliberately NOT about `dyn`. `W` here is a concrete type
//! throughout, so every call statically resolves; the `&mut dyn Write` inside
//! `core::fmt::Formatter` is a separate, genuinely dynamic site that stays
//! fail-closed with a per-site refusal.
#![crate_type = "lib"]
#![no_std]

use core::fmt::{self, Write};

pub struct W {
    pub n: usize,
}

impl Write for W {
    // Total by inspection: a wrapping add and an `Ok`. No panic path, so both
    // callers below must PROVE — the only question is whether the call is found.
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.n = self.n.wrapping_add(s.len());
        Ok(())
    }
}

/// Control: local -> local. The `DefId` lane has always covered this.
pub fn direct(w: &mut W) -> fmt::Result {
    w.write_str("S")
}

/// The regression: local -> FOREIGN (`Write::write_fmt` / `spec_write_fmt`) ->
/// local (`<W as Write>::write_str`). Must prove exactly like `direct`.
pub fn viamac(w: &mut W) -> fmt::Result {
    write!(w, "S")
}
