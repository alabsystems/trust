//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! What a seal says of an inline `const { }` and of a constant
//! (`Trust.Protocol.Seal`): each seal must FAIL, and its note must say what
//! the code is. Review 2 of the review-14 build: an inline `const` was read
//! as a closure, and the note said it "can be handed on and run anywhere,
//! any number of times"; and the note of a `u64` constant whose initializer
//! runs a maker said each use of it is a new sealed value.
//!
//! - `in_maker`: a maker whose value is built in an inline `const`: built
//!   once, when the program is compiled, and copied at each run.
//! - `in_made_by`: a `madeBy` fn that calls the maker in an inline `const`.
//! - `counted`: a `u64` constant whose initializer calls a `madeBy` fn that
//!   makes, and drops, a `Stamped` (refused, a listed cost: a constant is
//!   judged by what it runs; its type holds none, and the note says so).
//!
//! With the value built in the maker's own body: `_inline_const_holds.rs`.

#![allow(unused)]

mod in_maker {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { const { Cell { n: 0 } } } //~ NOTE this builds a `Cell` in an inline `const` in its maker `in_maker::Cell::new`: it is built once, when the program is compiled
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub fn mk() -> Cell { Cell::new() }
    pub fn run() { let mut c = mk(); c.bump(); }
}

mod in_made_by {
    pub struct Cell { n: u32 }
    impl Cell {
        pub const fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub fn mk() -> Cell {
        const { Cell::new() } //~ NOTE this calls the maker `in_made_by::Cell::new` in an inline `const` in `in_made_by::mk`: the call runs once, when the program is compiled
        //~| NOTE this constant's initializer runs `in_made_by::Cell::new`, which makes a `Cell` (or may): each use of the constant
    }
    pub fn run() { let mut c = mk(); c.bump(); }
}

mod counted {
    pub struct Stamped { generation: u64 }
    pub const fn mint(g: u64) -> Stamped { Stamped { generation: g } }
    pub const fn watcher() -> u64 { let s = mint(1); s.generation }
    pub const GEN: u64 = watcher(); //~ NOTE the constant's type `u64` holds none, but a constant is judged by what its initializer runs
}

fn main() {
    in_maker::run();
    in_made_by::run();
    let _ = counted::GEN;
}

clean {
    import Trust.Binding
    namespace Consts
    open Trust.Protocol
    def in_maker : Trust.Protocol.Seal := seals "in_maker::Cell" ["in_maker::Cell::bump"] ["in_maker::Cell::new"] ["in_maker::mk"] []
    def in_made_by : Trust.Protocol.Seal := seals "in_made_by::Cell" ["in_made_by::Cell::bump"] ["in_made_by::Cell::new"] ["in_made_by::mk"] []
    def counted : Trust.Protocol.Seal := seals "counted::Stamped" [] ["counted::mint"] ["counted::watcher"] []
    end Consts
}
//~^^^^^ ERROR seal `Consts.in_maker` on `Cell` does not hold
//~^^^^^ ERROR seal `Consts.in_made_by` on `Cell` does not hold
//~^^^^^ ERROR seal `Consts.counted` on `Stamped` does not hold
