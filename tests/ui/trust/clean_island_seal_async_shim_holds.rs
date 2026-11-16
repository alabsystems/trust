//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_vtable.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_async_shim.rs` (`Trust.Protocol.Seal`): an
//! `async` closure in generic code, called through `AsyncFnOnce` or `Fn`, by
//! `Option::map`, or in a dependency's generic fn read open at `(T, App)`; it
//! writes nothing, and every seal HOLDS. Review 4 of the review-14 build found
//! each refused, at every seal: the compiler's shim around the closure was
//! never read.

#![allow(unused)]

extern crate seal_dep_vtable;

pub mod async_fn_once {
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
    fn go<F: AsyncFnOnce() -> u8>(f: F) -> u8 { let _ = f(); 0 }
    pub fn outer<T>(x: T) -> u8 { let c = async || 1u8; go(c) }
}

pub mod fn_bound {
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
    fn go<F: Fn() -> R, R>(f: F) -> u8 { let _ = f(); 0 }
    pub fn outer<T>(x: T) -> u8 { let c = async || 1u8; go(c) }
}

pub mod option_map {
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
    pub fn later<T>(x: Option<T>) -> bool { let c = async |_v: T| 1u8; x.map(c).is_some() }
}

pub mod via_dep {
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
    pub fn g<T>(x: Option<(T, App)>) -> bool { seal_dep_vtable::later::<(T, App)>(x) }
}

clean {
    import Trust.Binding
    namespace AsyncShimHolds
    open Trust.Protocol
    def async_fn_once : Trust.Protocol.Seal := seals "async_fn_once::Cell" ["async_fn_once::Cell::bump"] ["async_fn_once::Cell::new"] ["async_fn_once::App::new"] []
    def fn_bound : Trust.Protocol.Seal := seals "fn_bound::Cell" ["fn_bound::Cell::bump"] ["fn_bound::Cell::new"] ["fn_bound::App::new"] []
    def option_map : Trust.Protocol.Seal := seals "option_map::Cell" ["option_map::Cell::bump"] ["option_map::Cell::new"] ["option_map::App::new"] []
    def via_dep : Trust.Protocol.Seal := seals "via_dep::Cell" ["via_dep::Cell::bump"] ["via_dep::Cell::new"] ["via_dep::App::new"] ["seal_dep_vtable::later"]
    end AsyncShimHolds
}
