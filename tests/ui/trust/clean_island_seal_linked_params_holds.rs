//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_linked.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_linked_params.rs` (`Trust.Protocol.Seal`): the
//! same fns at parameters whose bounds tie them to no sealed value (`M::Out = u8`,
//! a plain type of this crate, `P::Target = u8`) HOLD.

#![allow(unused)]

extern crate seal_dep_linked;

pub mod plain_out {
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
    pub fn churn<M: seal_dep_linked::Make<Out = u8>>(a: &mut u8, b: &mut u8, app: &mut App) { seal_dep_linked::direct::<M>(a, b); seal_dep_linked::swap_out::<M>(a, b); app.tick() }
}

pub mod local_plain_out {
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
    pub struct Plain(pub u8);
    pub fn churn<M: seal_dep_linked::Make<Out = Plain>>(a: &mut Plain, b: &mut Plain) { seal_dep_linked::swap_out::<M>(a, b) }
}

pub mod deref_plain {
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
    pub fn churn<P: core::ops::DerefMut<Target = u8>>(a: &mut P, b: &mut P) { seal_dep_linked::swap_deref::<P>(a, b) }
}

clean {
    import Trust.Binding
    namespace LinkedParamsHolds
    open Trust.Protocol
    def plain_out : Trust.Protocol.Seal := seals "plain_out::Cell" ["plain_out::Cell::bump"] ["plain_out::Cell::new"] ["plain_out::App::new"] []
    def local_plain_out : Trust.Protocol.Seal := seals "local_plain_out::Cell" ["local_plain_out::Cell::bump"] ["local_plain_out::Cell::new"] ["local_plain_out::App::new"] []
    def deref_plain : Trust.Protocol.Seal := seals "deref_plain::Cell" ["deref_plain::Cell::bump"] ["deref_plain::Cell::new"] ["deref_plain::App::new"] []
    end LinkedParamsHolds
}
