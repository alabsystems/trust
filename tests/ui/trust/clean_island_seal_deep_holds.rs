//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_deep.rs` (`Trust.Protocol.Seal`): a crate
//! that raises its recursion limit, with recursion that does not grow its
//! type and a type nested about 90 levels deep (well within the bound),
//! HOLDS.

#![allow(unused)]
#![recursion_limit = "2048"]

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
    fn get(&self) -> u32 { self.n }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

fn kept<T: Default + Clone>(x: T, n: u32) -> u32 {
    if n == 0 { 0 } else { kept(x.clone(), n - 1) }
}
macro_rules! nest {
    ($t:ty; ) => { $t };
    ($t:ty; $head:tt $($rest:tt)*) => { nest!(Option<$t>; $($rest)*) };
}
type Deep = nest!(u8; a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a
    a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a a);
fn deep() -> Deep { None }

fn main() {
    let mut a = App::new();
    a.cell.bump();
    kept(0u8, 3);
    let _ = deep();
}

clean {
    import Trust.Binding
    namespace DeepHold
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end DeepHold
}
