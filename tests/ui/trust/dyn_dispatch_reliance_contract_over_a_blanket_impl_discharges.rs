//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! ZERO-ROW-GATE AMENDMENT (2026-10-10, docs/DECISION_QUEUE.md ZERO-ROW-GATE): this positive control is now
//! check-fail. `drive` still discharges through the `#[trust::panic_free]` reliance
//! certificate (zero obligations; the pinned NOTE), but the certificate is in no
//! authenticated registry, so the body publishes an `unknown` row and is refused. The
//! pair's differential is kept by the twin FORBIDDING the zero-row note.
//!
//! POSITIVE CONTROL for `dyn_dispatch_reliance_no_contract_with_a_blanket_impl_stays_closed.rs`,
//! and the row that shows rung 1 is not redundant now that C-SEALED exists.
//!
//! Byte-identical to that file plus `#[trust::panic_free]`. The blanket impl puts
//! `dyn_trait_sealedness` at `Open`, so neither rung 2 nor C-SEALED can look at
//! this call at all — the probe prints `C-UNIVERSAL trait=Emitter`, not
//! `C-SEALED`. Φ is discharged once, polymorphically, at the blanket impl's own
//! definition and relied on at the dispatch site.
//!
//! Without this control the mutant's red is not attributable: a blanket impl
//! could have broken something unrelated and produced the same refusal.
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

pub trait Base {
    fn base(&self) -> u32;
}

pub trait Emitter {
    #[trust::panic_free]
    fn emit(&mut self, byte: u8);
}

impl<T: Base> Emitter for T {
    fn emit(&mut self, _byte: u8) {}
}

pub struct Counter {
    seen: u32,
}

impl Base for Counter {
    fn base(&self) -> u32 {
        self.seen
    }
}

// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//~vv ERROR Trust strict verification failed for `dyn_dispatch_reliance_contract_over_a_blanket_impl_discharges::drive`
//~v NOTE this function has no obligation of its own
pub fn drive(emitter: &mut dyn Emitter) {
    emitter.emit(7);
}

fn main() {
    let mut c = Counter { seen: 0 };
    drive(&mut c);
}
