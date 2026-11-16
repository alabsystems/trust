//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A note about code of another crate that this crate named asks for the
//! entry that answers it (`Trust.Protocol.Seal`): the seal must FAIL, and the
//! note must name `mpsc::channel`. Review 2 of the review-14 build: with
//! every entry the notes had asked for written in, what was left was a note
//! about std's channel giving a pointer to a holder another type, with no
//! entry asked for and no help, and `mpsc::channel` answered it.
//!
//! With that entry: `_recast_entry_holds.rs`.

#![allow(unused)]

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
    fn get(&self) -> u32 { self.n }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

fn main() {
    let (tx, rx) = std::sync::mpsc::channel::<App>(); //~ NOTE name it in the seal's `trusts`: `mpsc::channel`
    tx.send(App::new()).unwrap();
    let mut a = rx.recv().unwrap();
    a.cell.bump();
}

clean {
    import Trust.Binding
    namespace RecastEntry
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] ["Atomic::new", "Box::new", "CachePadded::new", "Channel::drop", "Receiver::drop", "Result::unwrap", "Sender::drop", "counter::new", "mpsc::Receiver::recv", "mpsc::Sender::send"]
    end RecastEntry
}
//~^^^ ERROR seal `RecastEntry.cell` on `Cell` does not hold
