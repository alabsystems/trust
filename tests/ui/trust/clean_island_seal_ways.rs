//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_ways.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! One body of a dependency reached on two ways, one that a trust covers
//! and one that none does (`Trust.Protocol.Seal`): the seal must FAIL, in
//! whichever order the walk meets them. `swapper` swaps two holders; the
//! seal trusts `left`, which calls it, and not `right`, which calls it too.
//! A body read once on a covered way is read again on the uncovered one.
//! (The twin, where a body is reached on many covered ways, is
//! `clean_island_seal_trust_masks.rs`.)

#![allow(unused)]

extern crate seal_dep_ways;

mod coveredfirst {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep_ways::Make for Mark { type Out = App; }
    pub fn make() -> App { App { cell: Cell::new() } }
    pub fn run() {
        let mut a = make();
        let mut b = make();
        a.cell.bump();
        seal_dep_ways::left::<Mark>(&mut a, &mut b);
        seal_dep_ways::right::<Mark>(&mut a, &mut b); //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `coveredfirst::App`
    }
}

mod uncoveredfirst {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep_ways::Make for Mark { type Out = App; }
    pub fn make() -> App { App { cell: Cell::new() } }
    pub fn run() {
        let mut a = make();
        let mut b = make();
        a.cell.bump();
        seal_dep_ways::right::<Mark>(&mut a, &mut b); //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `uncoveredfirst::App`
        seal_dep_ways::left::<Mark>(&mut a, &mut b);
    }
}

fn main() {
    coveredfirst::run();
    uncoveredfirst::run();
}

clean {
    import Trust.Binding
    namespace Ways
    open Trust.Protocol
    def coveredfirst : Trust.Protocol.Seal := seals "coveredfirst::Cell" ["coveredfirst::Cell::bump"] ["coveredfirst::Cell::new"] ["coveredfirst::make"] ["seal_dep_ways::left"]
    def uncoveredfirst : Trust.Protocol.Seal := seals "uncoveredfirst::Cell" ["uncoveredfirst::Cell::bump"] ["uncoveredfirst::Cell::new"] ["uncoveredfirst::make"] ["seal_dep_ways::left"]
    end Ways
}
//~^^^^ ERROR seal `Ways.coveredfirst` on `Cell` does not hold
//~^^^^ ERROR seal `Ways.uncoveredfirst` on `Cell` does not hold
