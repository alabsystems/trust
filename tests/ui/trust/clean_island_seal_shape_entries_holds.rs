//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_pod_one.rs
//@ aux-build: seal_dep_pod_two.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_shape_entries.rs` (`Trust.Protocol.Seal`):
//! with the entries its notes ask for, one for each trait, the seal HOLDS.

#![allow(unused)]

extern crate seal_dep_pod_one;
extern crate seal_dep_pod_two;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }
#[derive(Clone, Copy)]
struct Vertex { x: f32 }
#[derive(Clone, Copy)]
struct Index { i: u32 }
unsafe impl seal_dep_pod_one::marker::Pod for Vertex {}
unsafe impl seal_dep_pod_two::marker::Pod for Index {}

fn main() {
    let mut a = App::new();
    a.cell.bump();
}

clean {
    import Trust.Binding
    namespace ShapeEntriesHold
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] ["seal_dep_pod_one::marker::Pod", "seal_dep_pod_two::marker::Pod"]
    end ShapeEntriesHold
}
