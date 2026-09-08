//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! Verified-sysroot plan §5 step 6, the SKELETON's positive case:
//! `#[trust::panic_free_drop]` on a trait THIS crate owns is accepted — and
//! accepted means LOUDLY INERT. The attribute charges nothing: no impl below
//! is asked to discharge anything, no caller is charged a contract row, and
//! the only trace is the warning that says exactly that. Before the skeleton
//! landed, the same program compiled with ZERO diagnostics (measured, stage1
//! 2026-08-30) — an annotation that silently did nothing would read to its
//! author exactly like one that was being enforced.
//!
//! This fixture is the falsifier for "recognized-but-inert": it MUST go red
//! the moment step 6's enforcement lands (the impls below have never been
//! asked to prove their drop glue panic-free), and be rewritten then to the
//! enforced semantics. If it goes red BEFORE step 3's provenance model exists,
//! charging was wired in ahead of the machinery that could discharge it.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(register_tool)]
#![register_tool(trust)]

#[trust::panic_free_drop]
pub trait Closable {
    //~^ WARN recognized but NOT YET ENFORCED
    fn close(&mut self) -> u32;
}

pub struct Grate(u32);

impl Closable for Grate {
    fn close(&mut self) -> u32 {
        self.0 = self.0 / 4;
        self.0
    }
}

fn main() {
    let mut grate = Grate(9);
    let _ = grate.close();
}
