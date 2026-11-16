//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_component.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_dyn_upcast.rs` (`Trust.Protocol.Seal`): a holder
//! handed to a `dyn` of the trusted trait, and called there, with no upcast, HOLDS
//! (`component_only`).

#![allow(unused)]

extern crate seal_dep_component;

pub mod component_only {
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
    impl seal_dep_component::Component for App {}
    pub fn labels(x: App) -> u8 {
        let cx: Box<dyn seal_dep_component::Component> = Box::new(x);
        cx.label()
    }
}

clean {
    import Trust.Binding
    namespace DynUpcastHolds
    open Trust.Protocol
    def component_only : Trust.Protocol.Seal := seals "component_only::Cell" ["component_only::Cell::bump"] ["component_only::Cell::new"] ["component_only::App::new"] ["seal_dep_component::Component", "boxed::Box::new", "Box::drop", "Component::label", "Any::type_id"]
    end DynUpcastHolds
}
