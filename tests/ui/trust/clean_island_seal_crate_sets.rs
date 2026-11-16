//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_chain_01.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-require-annotations: HELP
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_crate_sets_holds.rs`
//! (`Trust.Protocol.Seal`): the same chain of 20 crates, with no `trusts`
//! entry for the last crate's `t`, which is run at `App` on every way. The
//! seal must FAIL, at `seal_dep_chain_20::t`, however the ways to it are met.
#![allow(unused)]

extern crate seal_dep_chain_01;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
    fn get(&self) -> u32 { self.n }
}
pub struct App { cell: Cell, k: u8 }
impl App { fn new() -> Self { App { cell: Cell::new(), k: 0 } } }

fn main() {
    let mut app = App::new();
    app.cell.bump();
    seal_dep_chain_01::t::<App>(&mut app);
    seal_dep_chain_01::u::<&mut App>(&mut &mut app); //~ NOTE this runs `seal_dep_chain_20::t`, a fn of another crate, at the type `App`, which holds a `Cell`, in `main`:
    println!("{}", app.cell.get());
}

clean {
    import Trust.Binding
    namespace CrateSets
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] ["seal_dep_chain_01::t", "seal_dep_chain_02::t", "seal_dep_chain_03::t", "seal_dep_chain_04::t", "seal_dep_chain_05::t", "seal_dep_chain_06::t", "seal_dep_chain_07::t", "seal_dep_chain_08::t", "seal_dep_chain_09::t", "seal_dep_chain_10::t", "seal_dep_chain_11::t", "seal_dep_chain_12::t", "seal_dep_chain_13::t", "seal_dep_chain_14::t", "seal_dep_chain_15::t", "seal_dep_chain_16::t", "seal_dep_chain_17::t", "seal_dep_chain_18::t", "seal_dep_chain_19::t", "DerefMut::deref_mut"]
    end CrateSets
}
//~^^^^ ERROR seal `CrateSets.cell` on `Cell` does not hold
