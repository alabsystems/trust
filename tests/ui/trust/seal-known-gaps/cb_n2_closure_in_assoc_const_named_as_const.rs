//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_checked.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `CbN2.cell` on `Cell` does not hold: 1 statement(s) break it
//@ error-pattern: the check could not read the body of `seal_gap_checked::HasC::C`, which the metadata of its crate does not carry
//! KNOWN GAP of the sealed-types check (the review of the check-build fix
//! `332dfad2ee`, 2026-10-16; N2, a false note; lens: check build). Recorded,
//! not fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's
//! findings recorded, not fixed").
//! The seal is refused, rightly: the dependency is built for `check`
//! (`--emit=metadata`), and the closure its blanket impl puts in the constant
//! `HasC::C`, called here at `Wake`, has no MIR there. The note names the
//! wrong body: "the body of `seal_gap_checked::HasC::C`, which the metadata
//! of its crate does not carry". The metadata does carry the constant's (its
//! MIR for evaluation, which the walk read to find the closure); what it does
//! not carry is the closure's, `<Wake as HasC>::C::{closure#0}`, which the
//! stage 1 of `ebfd92f24d` named as it stopped the build ("missing optimized
//! MIR", no word of the seal). Built in full, the same program holds. The
//! file passes while the false sentence is printed; when a fix names the
//! closure (as "the closure in `seal_gap_checked::HasC::C`"), it fails: that
//! is the win. Pin the refusal with the true note in a must-fail fixture, and
//! delete this file.
//! Root, as its skeptic put it: the unread note prints `trust_path` of the
//! closure, and `entry_path` keeps only the parents' `opt_item_name`, which a
//! closure has none of, so a closure's path is its enclosing item's.
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(unused)]
extern crate seal_gap_checked;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

/// A type of this crate that owns no `Cell`.
pub struct Wake { id: u32 }

fn main() {
    let mut a = App::new();
    a.cell.bump();
    use seal_gap_checked::HasC;
    let w = Wake { id: 1 };
    let _ = (<Wake as HasC>::C)(&w);
}

clean {
    import Trust.Binding
    namespace CbN2
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end CbN2
}
