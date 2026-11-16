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
//! Root, as its skeptic put it: writer_origins.rs `Frame::leaving` lines
//! 2165-2175 (closure Aggregate: `continue`, no `made_from` edge) together
//! with its Drop arm 2242-2251, and `scan_writes` 2774-2785 (a Drop
//! terminator is a site only for a value that `reaches()` and a foreign Drop
//! impl). Wrong sentence: "The closure knows its captures; but the variables
//! a ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct App { pub harness: Policy }
pub enum Wake { Observed(u8), Tick }
struct Guard<'a>(&'a mut u8);
impl Drop for Guard<'_> { fn drop(&mut self) { *self.0 = 9; } }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => self.harness = Policy(p),
            Wake::Tick => {
                let g = Guard(&mut self.harness.0);
                let _f = move || { &g; };
            }
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); });
    let mut app = App::default();
    for wake in rx { app.on_wake(wake); }
    sender.join().unwrap();
    println!("final harness: {:?}", app.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "harness" ["Observed"] []
}
