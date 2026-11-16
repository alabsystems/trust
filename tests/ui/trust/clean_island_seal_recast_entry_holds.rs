//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_recast_entry.rs` (`Trust.Protocol.Seal`):
//! with the entry its note asks for, the seal HOLDS.

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
    let (tx, rx) = std::sync::mpsc::channel::<App>();
    tx.send(App::new()).unwrap();
    let mut a = rx.recv().unwrap();
    a.cell.bump();
}

clean {
    import Trust.Binding
    namespace RecastEntryHold
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] ["mpsc::channel", "Atomic::new", "Box::new", "CachePadded::new", "Channel::drop", "Receiver::drop", "Result::unwrap", "Sender::drop", "counter::new", "mpsc::Receiver::recv", "mpsc::Sender::send"]
    end RecastEntryHold
}
