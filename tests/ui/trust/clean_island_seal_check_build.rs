//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_checked.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A seal checked against a dependency built for `check` (`--emit=metadata`,
//! as `cargo check` builds every dependency): its metadata carries no MIR,
//! so the generic fn this crate makes at a type of its own cannot be read,
//! and the seal must FAIL saying so (`Trust.Protocol.Seal`). Review 1 of
//! the review-14 build found such a seal holding over a `mem::swap` of two
//! holders that the unread body ran. (Every seal is refused where this
//! happens: this file has one.) Built in full, the same dependency holds:
//! `_check_build_holds.rs`.

#![allow(unused)]

extern crate seal_dep_checked;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

fn main() {
    let mut a = App::new();
    let mut b = App::new();
    a.cell.bump();
    let refs = [&mut a, &mut b];
    println!("{}", seal_dep_checked::count_refs(&refs)); //~ NOTE which the metadata of its crate does not carry
}

clean {
    import Trust.Binding
    namespace CheckBuild
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end CheckBuild
}
//~^^^ ERROR seal `CheckBuild.cell` on `Cell` does not hold
