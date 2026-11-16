//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_nested_holds.rs`: the same nested type
//! with the holder in a `RefCell`, handed to a `dyn Debug` behind a `&`,
//! must FAIL (`Trust.Protocol.Seal`): a `&Node<App>` reaches the holder
//! through a cell, and code that names no type of this crate can write it.
//! What a nested type lets be written is read off its definitions, not
//! taken to be nothing.

#![allow(unused)]

use std::cell::RefCell;
use std::fmt;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
    fn get(&self) -> u32 { self.n }
}
pub struct App { cell: Cell, k: u8 }
impl App { fn new() -> Self { App { cell: Cell::new(), k: 0 } } }

pub struct Node<'a, T> { val: RefCell<T>, parent: Option<&'a Node<'a, Option<T>>> }
impl<'a, T> fmt::Debug for Node<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "node(has parent: {})", self.parent.is_some())
    }
}

fn show(d: &dyn fmt::Debug) -> String { format!("{:?}", d) }

fn main() {
    let n = Node { val: RefCell::new(App::new()), parent: None };
    n.val.borrow_mut().cell.bump();
    println!("{} {}", show(&n), n.val.borrow().cell.get()); //~ NOTE this hands a value of type `Node<'_, App>`, which holds a `Cell` or points to one, to a `dyn Debug`
}

clean {
    import Trust.Binding
    namespace Nested
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end Nested
}
//~^^^ ERROR seal `Nested.cell` on `Cell` does not hold
