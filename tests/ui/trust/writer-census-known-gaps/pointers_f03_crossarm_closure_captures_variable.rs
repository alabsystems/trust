//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: pointers).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: writer_origins.rs `Frame::closures` lines
//! 1886-1946, at 1896-1899: "(A pointer to one of this body's own variables
//! is a pointer to nothing a consumer runs on: the closure's write through it
//! is this body's variable.)" The capture fact is `stripped()`, so what the
//! variable KEEPS (`kept.i.part`, a pointer to part of the field) ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct App { pub harness: Policy }
pub enum Wake { Observed(u8), Tick }
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); });
    let mut app = App::default();
    let mut kept: Option<&mut u8> = None;
    for wake in rx {
        match wake {
            Wake::Observed(p) => { app.harness = Policy(p); kept = Some(&mut app.harness.0); }
            Wake::Tick => { (|| if let Some(h) = &mut kept { **h = 9 })(); }
        }
    }
    sender.join().unwrap();
    println!("final harness: {:?}", app.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "harness" ["Observed"] []
}
