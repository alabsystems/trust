//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! `Trust.Protocol.Seal`: dead polymorphic recursion `grow(W(x))` where `W<T>: Tr`
//! needs `V<T>: Tr`, which needs `T: Tr`: two levels of an obligation for each level
//! of the type, so the compiler's trait solver overflows at half the recursion
//! limit, below the depth bound on types (review 5 of the review-14 build: the build
//! stopped with E0275, no span and no word of the seal). The trait solver's own
//! query mode is asked first, and the seal is refused at the seal. A refusal of
//! every seal: a file of its own.

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
    fn grow<T: Tr>(x: T, n: u32) -> u32 { if n == 0 { x.m() } else { grow(W(x), n - 1) } } //~ NOTE the crate names `Tr::m`, at types the compiler's trait solver cannot settle within the recursion limit (128)
    fn unused() -> u32 { grow(0u8, 3) }
}

clean {
    import Trust.Binding
    namespace ObligationChain
    open Trust.Protocol
    def chain : Trust.Protocol.Seal := seals "chain::Cell" ["chain::Cell::bump"] ["chain::Cell::new"] ["chain::App::new"] []
    end ObligationChain
}
//~^^^ ERROR seal `ObligationChain.chain` on `Cell` does not hold
