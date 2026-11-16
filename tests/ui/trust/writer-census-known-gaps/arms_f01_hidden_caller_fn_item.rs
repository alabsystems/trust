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
//! Root, as its skeptic put it: concurrency_effects.rs `report_consumers`,
//! lines 8832-8864 (`call_sites`, `one_way_in`), used at 9072. Wrong sentence
//! (8832-8835): "A body is read with the variants a hand-off leaves only when
//! that hand-off is the one way into it: another call (with a value its
//! caller built) ... can give it any variant." The count behind it ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config, pub n: u32, pub observed_ran: bool }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            w @ Wake::Observed(_) => { self.observed_ran = true; self.apply(w) }
            Wake::Tick => { let again = App::apply; again(self, Wake::Tick); }
        }
    }
    fn apply(&mut self, w: Wake) {
        self.config.harness = Policy(7);
        if let Wake::Observed(_) = w {}
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Tick); });
    let mut app = App::default();
    for wake in rx { app.on_wake(wake); }
    sender.join().unwrap();
    println!("harness: {:?}; only Tick was sent; the Observed arm of on_wake ran: {}", app.config.harness, app.observed_ran);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
