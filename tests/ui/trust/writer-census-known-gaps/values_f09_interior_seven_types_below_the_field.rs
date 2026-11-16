//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: values).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: concurrency_effects.rs `owns_interior`
//! 10173-10211: `if depth > 6 { continue; }` (10187-10189), then `false`.
//! Wrong sentence (10174-10177): "no deeper than six types down, where a type
//! that grows as it is walked (`Nest<T>` holding a `Nest<(T, T)>`) would
//! never end" - the bound is on DEPTH, not growth, and running out answers ..

use std::sync::mpsc::channel;
use std::cell::Cell;
#[derive(Default)] pub struct S6 { pub cell: Box<Cell<u8>> }
#[derive(Default)] pub struct S5 { pub s: S6 }
#[derive(Default)] pub struct S4 { pub s: S5 }
#[derive(Default)] pub struct S3 { pub s: S4 }
#[derive(Default)] pub struct S2 { pub s: S3 }
#[derive(Default)] pub struct S1 { pub s: S2 }
#[derive(Default)] pub struct Limits { pub s: S1 }
#[derive(Default)] pub struct Shell { pub limits: Limits }
pub enum Wake { Observed(u8), Tick }
impl Shell {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => { self.limits.s.s.s.s.s.s.cell.set(p); }
            Wake::Tick => {}
        }
    }
    fn peek(&self) { self.limits.s.s.s.s.s.s.cell.set(9); }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); drop(tx);
    let mut shell = Shell::default();
    for wake in rx {
        shell.on_wake(wake);
        println!("after the handler: {}", shell.limits.s.s.s.s.s.s.cell.get());
        shell.peek();
        println!("after peek(&self): {}", shell.limits.s.s.s.s.s.s.cell.get());
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "limits" ["Observed"] []
}
