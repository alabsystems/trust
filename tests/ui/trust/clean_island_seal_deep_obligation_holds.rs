//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_deep_obligation.rs` (`Trust.Protocol.Seal`):
//! a live value of a type nested 100 deep, cloned, compared and dropped, under
//! the recursion limit (128): the seal HOLDS. The bound the check stops at is the
//! compiler's own limit, not a guess below it.

#![allow(unused)]

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell, k: u8 }
impl App { fn new() -> Self { App { cell: Cell::new(), k: 0 } } }
type Deep = Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<u8>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;
fn make() -> Deep { Default::default() }
fn main() { let mut a = App::new(); a.cell.bump(); let d = make(); let e = d.clone(); assert!(d == e); }

clean {
    import Trust.Binding
    namespace Deep
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end Deep
}
