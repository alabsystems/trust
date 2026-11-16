//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_obligation_chain.rs` (`Trust.Protocol.Seal`): the
//! same impls, used at a type two levels deep in live code, HOLD.

#![allow(unused)]

pub mod chain {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub trait Tr { fn m(&self) -> u32; }
    impl Tr for u8 { fn m(&self) -> u32 { 1 } }
    pub struct V<T>(pub T);
    pub struct W<T>(pub T);
    impl<T: Tr> Tr for V<T> { fn m(&self) -> u32 { self.0.m() } }
    impl<T> Tr for W<T> where V<T>: Tr { fn m(&self) -> u32 { 2 } }
    pub fn two() -> u32 { W(W(0u8)).m() + V(V(0u8)).m() }
}

clean {
    import Trust.Binding
    namespace ObligationChainHolds
    open Trust.Protocol
    def chain : Trust.Protocol.Seal := seals "chain::Cell" ["chain::Cell::bump"] ["chain::Cell::new"] ["chain::App::new"] []
    end ObligationChainHolds
}
