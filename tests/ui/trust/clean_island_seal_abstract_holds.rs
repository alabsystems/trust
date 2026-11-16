//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_abstract.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_abstract.rs` (`Trust.Protocol.Seal`): an
//! abstract impl handed nothing that holds a sealed value, or trusted, and
//! every seal HOLDS. (A trait of this crate whose method is declared with a
//! `&mut App` input, its impl picked by a parameter, held here until review 5
//! of the review-14 build; it is refused now, `_abstract_sig.rs`
//! `declared_input`.) With no where-clause the
//! compiler picks the blanket impl, which is read at `(T, App)` (`local_picked`,
//! which measures); a where-clause at a type that holds none
//! (`local_where_plain`); a
//! dependency's trait item at `(T, u8)` (`dep_assoc_plain`), and at `(T, App)`
//! with the item named in `trusts` (`dep_assoc_trusted`).

#![allow(unused)]

extern crate seal_dep_abstract;

pub mod local_picked {
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
    pub trait Bound {}
    impl<Y> Bound for Y {}
    pub trait LocalSz: Sized { const SZ: fn(&Self) -> usize; }
    fn measure<X>(_: &X) -> usize { core::mem::size_of::<X>() }
    impl<X: Bound> LocalSz for X { const SZ: fn(&X) -> usize = measure::<X>; }
    pub fn size<T>(a: &(T, App)) -> usize { (<(T, App) as LocalSz>::SZ)(a) }
}

pub mod local_where_plain {
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
    pub trait Bound {}
    impl<Y> Bound for Y {}
    pub trait LocalSw: Sized { fn sw(&mut self, o: &mut Self); }
    impl<X: Bound> LocalSw for X { fn sw(&mut self, o: &mut X) { core::mem::swap(self, o) } }
    pub fn churn<T>(a: &mut (T, u8), b: &mut (T, u8)) where (T, u8): LocalSw { a.sw(b) }
}

pub mod dep_assoc_plain {
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
    pub fn churn<K: seal_dep_abstract::Sw<Item = (T, u8)>, T>(a: &mut (T, u8), b: &mut (T, u8)) { K::sw(a, b) }
}

pub mod dep_assoc_trusted {
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
    pub fn churn<K: seal_dep_abstract::Sw<Item = (T, App)>, T>(a: &mut (T, App), b: &mut (T, App)) { K::sw(a, b) }
}

clean {
    import Trust.Binding
    namespace AbstractHolds
    open Trust.Protocol
    def local_picked : Trust.Protocol.Seal := seals "local_picked::Cell" ["local_picked::Cell::bump"] ["local_picked::Cell::new"] ["local_picked::App::new"] []
    def local_where_plain : Trust.Protocol.Seal := seals "local_where_plain::Cell" ["local_where_plain::Cell::bump"] ["local_where_plain::Cell::new"] ["local_where_plain::App::new"] []
    def dep_assoc_plain : Trust.Protocol.Seal := seals "dep_assoc_plain::Cell" ["dep_assoc_plain::Cell::bump"] ["dep_assoc_plain::Cell::new"] ["dep_assoc_plain::App::new"] []
    def dep_assoc_trusted : Trust.Protocol.Seal := seals "dep_assoc_trusted::Cell" ["dep_assoc_trusted::Cell::bump"] ["dep_assoc_trusted::Cell::new"] ["dep_assoc_trusted::App::new"] ["seal_dep_abstract::Sw::sw"]
    end AbstractHolds
}
