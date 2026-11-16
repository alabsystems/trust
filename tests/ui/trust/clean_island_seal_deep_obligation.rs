//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! Dead polymorphic recursion whose type grows TWO levels a step
//! (`Trust.Protocol.Seal`): `grow(Some(Some(x.clone())))`, called by nothing
//! that runs. The seal is refused, at the seal, at a type nested deeper than the
//! recursion limit, before the compiler's trait solver is asked `Clone` of it.
//! Review 4 of the review-14 build: the build stopped with E0275 (overflow
//! evaluating `Option<..>: Clone`), with no span and no word of the seal, and
//! following its help (a higher limit) asked again. A refusal of every seal: a
//! file of its own. (Growth of one level a step is `_recursion_holds.rs`'s
//! neighbour, refused at the walk's own depth.)

#![allow(unused)]

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell, k: u8 }
impl App { fn new() -> Self { App { cell: Cell::new(), k: 0 } } }
fn grow<T: Clone>(x: T, n: u32) -> u32 { if n == 0 { 0 } else { grow(Some(Some(x.clone())), n - 1) } } //~ NOTE the crate names `grow`, at a type nested more than 128 deep, the recursion limit (as polymorphic recursion
fn dead() -> u32 { grow(1u8, 3) }
fn main() { let mut a = App::new(); a.cell.bump(); }

clean {
    import Trust.Binding
    namespace Deep
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end Deep
}
//~^^^^ ERROR seal `Deep.cell` on `Cell` does not hold
