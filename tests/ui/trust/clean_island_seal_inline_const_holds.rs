//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_inline_const.rs` (`Trust.Protocol.Seal`):
//! the same makers with the value built in the maker's own body, and called
//! in the `madeBy` fn's own body, HOLD; so does an inline `const` that runs
//! no maker in a maker (`const { 0 }`), and an array of `const { None }`.

#![allow(unused)]

mod in_maker {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: const { 0 } } }
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
    pub fn mk() -> Cell { Cell::new() }
    pub fn none() -> [Option<Cell>; 4] { [const { None }; 4] }
    pub fn run() { let mut c = mk(); c.bump(); let _ = none(); }
}

fn main() {
    in_maker::run();
    in_made_by::run();
}

clean {
    import Trust.Binding
    namespace ConstsHold
    open Trust.Protocol
    def in_maker : Trust.Protocol.Seal := seals "in_maker::Cell" ["in_maker::Cell::bump"] ["in_maker::Cell::new"] ["in_maker::mk"] []
    def in_made_by : Trust.Protocol.Seal := seals "in_made_by::Cell" ["in_made_by::Cell::bump"] ["in_made_by::Cell::new"] ["in_made_by::mk"] []
    end ConstsHold
}
