//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_rigid_alias.rs` (`Trust.Protocol.Seal`): a rigid
//! projection of another crate's trait whose arguments hold nothing, at parameters
//! nothing ties to a sealed value, owns nothing: the shadowed `Option<(T, u8)>`'s
//! `Item` (`shadow_std_plain`), an `I::Item` stored (`iterator_item`), and a
//! `P::Target` swapped (`deref_target`). Each HOLDS.

#![allow(unused)]

pub mod shadow_std_plain {
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
    pub fn churn<T>(a: &mut <Option<(T, u8)> as IntoIterator>::Item, b: <Option<(T, u8)> as IntoIterator>::Item) where Option<(T, u8)>: IntoIterator { *a = b; }
}

pub mod iterator_item {
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
    pub fn keep<I: Iterator>(slot: &mut Option<I::Item>, mut it: I) { *slot = it.next(); }
}

pub mod deref_target {
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
    pub fn swap_targets<P: core::ops::DerefMut>(a: &mut P, b: &mut P) where P::Target: Sized { core::mem::swap(&mut **a, &mut **b) }
}

clean {
    import Trust.Binding
    namespace RigidAliasHolds
    open Trust.Protocol
    def shadow_std_plain : Trust.Protocol.Seal := seals "shadow_std_plain::Cell" ["shadow_std_plain::Cell::bump"] ["shadow_std_plain::Cell::new"] ["shadow_std_plain::App::new"] []
    def iterator_item : Trust.Protocol.Seal := seals "iterator_item::Cell" ["iterator_item::Cell::bump"] ["iterator_item::Cell::new"] ["iterator_item::App::new"] []
    def deref_target : Trust.Protocol.Seal := seals "deref_target::Cell" ["deref_target::Cell::bump"] ["deref_target::Cell::new"] ["deref_target::App::new"] []
    end RigidAliasHolds
}
