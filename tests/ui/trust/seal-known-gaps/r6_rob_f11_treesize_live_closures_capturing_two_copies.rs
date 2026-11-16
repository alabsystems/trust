//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6RobF11.cell` on `Cell` does not hold
//@ error-pattern: the crate names `call`, at a type of more than 4194304 parts as the compiler walks it (as a type that doubles at each step does, a polymorphic recursion over `(T, T)`)
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-ROB-F11, a true program refused; lens: robustness).
//! Recorded, not fixed (docs/DECISION_QUEUE.md, "sealed types land with
//! review 6's findings recorded, not fixed").
//! The seal below is REFUSED at the type-size bound, and the program is true:
//! `run` never touches `Cell`, and the same chain at 19 levels holds. rustc
//! builds and codegens this file in 0.1 s (it goes exponential only from
//! about 33 levels), so the note's reason (polymorphic recursion, code nothing
//! calls) does not hold: this is live code with no recursion. The file passes
//! while it is refused for that reason; the day it holds, the file fails:
//! that is the win. Move the program to a must-hold fixture and delete this
//! file.
//! The shape: a sibling of R2-ROB-F2 that its fix does not reach. A closure
//! that captures two clones of the previous closure (`dup(f)`: `let g =
//! f.clone(); move || f() + g()`; the innermost captures a `String`), 23
//! levels deep. docs/USING_TRUST.md: "A closure is counted by what it
//! captures, so long chains of closures in live code (20 iterator adaptors)
//! are read"; it lists the 4,194,304-part refusal under POLYMORPHIC RECURSION.
//! Root, as its skeptic put it: sealed.rs `TreeSize` counts a closure by its
//! captures as a TREE, so two clones of one closure double the count at each
//! level, where the compiler does not walk this closure type part by part
//! (TREE_BOUND, 1 << 22, is reached at 22 levels).

#![allow(unused)]
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
pub fn dup<F: Fn() -> u32 + Clone>(f: F) -> impl Fn() -> u32 + Clone { let g = f.clone(); move || f() + g() }
pub fn run() -> u32 { let s = String::from("x"); let f = move || s.len() as u32;
    let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f);
    let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f);
    let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f); let f = dup(f);
    f() }

clean {
    import Trust.Binding
    namespace R6RobF11
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end R6RobF11
}
