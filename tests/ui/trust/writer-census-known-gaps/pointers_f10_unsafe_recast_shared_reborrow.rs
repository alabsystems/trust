//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: pointers; uses `unsafe`).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: writer_origins.rs `Frame::pointer_to` lines
//! 1263-1291. Line 1272, `Region::Holder(verb) if !mutable &&
//! !verb.starts_with("writes a whole") => {}`, is justified by 1268-1271: "(A
//! `&` of a cell whose type alone says it MAY be the field is no pointer to
//! it ...)". Here the Holder region is not by type alone: it is `through`'s
//! ..

use std::cell::Cell;
use std::sync::mpsc::channel;
pub struct App { pub harness: Cell<u8> }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => self.harness.set(p),
            Wake::Tick => {
                let p = self as *const App as *const Cell<u8>;
                unsafe { &*p }.set(9);
            }
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); });
    let mut app = App { harness: Cell::new(0) };
    for wake in rx { app.on_wake(wake); }
    sender.join().unwrap();
    println!("final harness: {}", app.harness.get());
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "harness" ["Observed"] []
}
