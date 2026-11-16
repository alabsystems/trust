//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! A holder of a NESTED type, handed to a `dyn` of a std trait behind a
//! plain `&`, HOLDS (`Trust.Protocol.Seal`): `Node<T>` holds a
//! `&Node<Option<T>>`, so a walk of what a `&` to one can write meets a new,
//! larger type at each step and has no end; the definitions it meets are
//! two, and read off them, a `&Node<App>` writes nothing. Review 1 of the
//! review-14 build: the walk stopped at its bound and refused the seal.
//! (`_nested.rs`: the same type with a `RefCell` in it is refused.)

#![allow(unused)]

use std::fmt;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
    fn get(&self) -> u32 { self.n }
}
pub struct App { cell: Cell, k: u8 }
impl App { fn new() -> Self { App { cell: Cell::new(), k: 0 } } }

pub struct Node<'a, T> { val: T, parent: Option<&'a Node<'a, Option<T>>> }
impl<'a, T> fmt::Debug for Node<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "node(has parent: {})", self.parent.is_some())
    }
}

fn show(d: &dyn fmt::Debug) -> String { format!("{:?}", d) }

fn main() {
    let mut n = Node { val: App::new(), parent: None };
    n.val.cell.bump();
    println!("{} {}", show(&n), n.val.cell.get());
}

clean {
    import Trust.Binding
    namespace NestedHolds
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end NestedHolds
}
