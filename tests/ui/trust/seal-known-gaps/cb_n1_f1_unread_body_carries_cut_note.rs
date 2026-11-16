//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_checked.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `CbN1F1.cell` on `Cell` does not hold: 1 statement(s) break it
//@ error-pattern: the check could not read the body of `seal_gap_checked::measure`, which the metadata of its crate does not carry
//@ error-pattern: a type too large to read, or an instance the compiler could not make, was taken to hold one (the check erred on the side of failing)
//! KNOWN GAP of the sealed-types check (the review of the check-build fix
//! `332dfad2ee`, 2026-10-16; N1 and F1, one report from two skeptics, a false
//! note; lens: check build). Recorded, not fixed (docs/DECISION_QUEUE.md,
//! "sealed types land with review 6's findings recorded, not fixed").
//! The seal is refused, rightly: the dependency is built for `check`
//! (`--emit=metadata`), so the body of `measure`, made at `Wake`, cannot be
//! read, and the note says so. Under the error a second note says "a type
//! too large to read, or an instance the compiler could not make, was taken
//! to hold one": neither happened here. The same note is under every refusal
//! for an unread body: the drop glue, clone shims, std calls, `dyn`s, fn
//! pointers and coroutines of `../clean_island_seal_check_build_*.rs`, and
//! the three `HarnessPolicySeal` errors of aterm-gui's check build. It
//! predates the fix (the stage 1 of `ebfd92f24d` prints it for this program
//! too); the fix makes it reachable from more shapes. Built in full, the same
//! program holds. The file passes while the sentence is printed; when a fix
//! leaves it out for an unread body (or names that cause), it fails: that is
//! the win. Pin the refusal without that sentence in a must-fail fixture, and
//! delete this file.
//! Root, as its skeptics put it: sealed.rs `Checker::unread` sets `self.cut =
//! true`, and `report` adds that fixed sentence to a refused seal whenever
//! `cut` is set, whatever set it.
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
    let w = Wake { id: 1 };
    let _ = seal_gap_checked::measure(&w);
}

clean {
    import Trust.Binding
    namespace CbN1F1
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end CbN1F1
}
