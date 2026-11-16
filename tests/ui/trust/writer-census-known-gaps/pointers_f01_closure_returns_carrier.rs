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
//! Root, as its skeptic put it: writer_origins.rs `scan_writes` lines
//! 2699-2719 (the `match rvalue` whose only hand-on arm is `Rvalue::Use |
//! CopyForDeref`), with `captured_pointer` 2627-2632 and `Frame::leaving`
//! 2166-2175. Wrong sentence: "The closure knows its captures" (2167), paired
//! with "A captured pointer to the field that this closure hands on: the ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct App { pub harness: Policy }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => self.harness = Policy(p),
            Wake::Tick => {
                let k = (&mut self.harness.0,);
                let f = || (k,);
                *(f().0).0 = 9;
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
