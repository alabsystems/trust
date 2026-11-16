//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_bodies_checked.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A seal checked against a dependency built for `check` (`--emit=metadata`),
//! where the compiler's own collector, asked what a body uses, lists a body
//! of that dependency whose MIR its metadata does not carry: a generic fn of
//! the standard library (`fmt::rt::Argument::new_debug`, which `format!`
//! calls), made at `Shown<Wake>`, makes a fn pointer of the dependency's
//! `Debug` impl at `Wake`. Before, the collector stopped the build there
//! ("missing optimized MIR", which names no seal). Now it lists that body as
//! it lists one whose MIR is there, and the seal must FAIL saying which body
//! could not be read (`Trust.Protocol.Seal`). (Every seal is refused where
//! this happens: this file has one.) Built in full, the same dependency
//! holds: `clean_island_seal_check_build_std_fn_pointer_holds.rs`. No rule
//! was relaxed for it.

#![allow(unused)]

extern crate seal_dep_bodies_checked;

use seal_dep_bodies_checked::Shown;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

/// A type of this crate that owns no `Cell`, as aterm's `Wake` owns none.
pub struct Wake { id: u32 }

fn main() {
    let mut a = App::new();
    a.cell.bump();
    let shown = Shown { n: 1, held: Wake { id: 1 } };
    let text = format!("{:?}", shown); //~ NOTE the body of `seal_dep_bodies_checked::Shown::fmt`, which the metadata of its crate does not carry
    let _ = text.len();
}

clean {
    import Trust.Binding
    namespace CheckBuildStdFnPointer
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end CheckBuildStdFnPointer
}
//~^^^ ERROR seal `CheckBuildStdFnPointer.cell` on `Cell` does not hold
