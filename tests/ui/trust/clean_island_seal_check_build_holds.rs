//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_built.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_check_build.rs`: the same program against
//! the same dependency built in full, whose generic fn's MIR is read where
//! this crate makes it, HOLDS (`Trust.Protocol.Seal`): it writes nothing.

#![allow(unused)]

extern crate seal_dep_built;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

fn main() {
    let mut a = App::new();
    let mut b = App::new();
    a.cell.bump();
    let refs = [&mut a, &mut b];
    println!("{}", seal_dep_built::count_refs(&refs));
}

clean {
    import Trust.Binding
    namespace CheckBuildHolds
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end CheckBuildHolds
}
