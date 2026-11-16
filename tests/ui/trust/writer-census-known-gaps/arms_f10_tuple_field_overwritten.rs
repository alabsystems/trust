//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: arms).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: concurrency_effects.rs `Held::is_message`
//! line 7148 (`(_, [Field(field)]) => built_with(*field, Hold::Is)`) with
//! `Held::fields`/`build` (7094-7097, 7163-7170; filled at 7420-7432 and
//! 7506-7528 and never retracted). Wrong sentence (7118-7121): the held
//! message is "a field an aggregate was built with". That stays true for the
//! ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        let mut stamped = (wake, 0u8);
        stamped.0 = Wake::Observed(7);
        match stamped.0 {
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {}
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Tick); });
    let mut app = App::default();
    for wake in rx { app.on_wake(wake); }
    sender.join().unwrap();
    println!("harness: {:?}; only Tick was sent (7 is the payload of a value the body built)", app.config.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
