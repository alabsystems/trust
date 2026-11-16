//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_chain_01.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! A chain of 20 crates (`seal_dep_chain_01` to `_20`), each with a `t` run
//! at `App` and a `u` run at `&mut App`, each calling the next crate's two
//! (`Trust.Protocol.Seal`): the seal trusts every crate's `t`, and HOLDS.
//! A way through a crate's `t` keeps that crate's trust for what the crate
//! runs beneath, a way through its `u` does not, so the ways to the last
//! crate's bodies carry 2^20 different sets of crates. Review 3 of the
//! review-14 build: keyed by that set, the walk read those bodies once per
//! set, passed its bound of 2,000,000 instances, and refused this true
//! program; met crate by crate, it reads each about once per crate.
//! (With the last crate's `t` untrusted: `_crate_sets.rs`.)
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
    seal_dep_chain_01::u::<&mut App>(&mut &mut app);
    println!("{}", app.cell.get());
}

clean {
    import Trust.Binding
    namespace CrateSetsHolds
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] ["seal_dep_chain_01::t", "seal_dep_chain_02::t", "seal_dep_chain_03::t", "seal_dep_chain_04::t", "seal_dep_chain_05::t", "seal_dep_chain_06::t", "seal_dep_chain_07::t", "seal_dep_chain_08::t", "seal_dep_chain_09::t", "seal_dep_chain_10::t", "seal_dep_chain_11::t", "seal_dep_chain_12::t", "seal_dep_chain_13::t", "seal_dep_chain_14::t", "seal_dep_chain_15::t", "seal_dep_chain_16::t", "seal_dep_chain_17::t", "seal_dep_chain_18::t", "seal_dep_chain_19::t", "seal_dep_chain_20::t", "DerefMut::deref_mut"]
    end CrateSetsHolds
}
