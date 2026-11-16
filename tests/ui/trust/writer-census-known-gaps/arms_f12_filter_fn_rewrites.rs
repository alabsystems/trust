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
//! Root, as its skeptic put it: Corrected from the report; two parts. (1)
//! concurrency_effects.rs `hands_back` 7709-7841: both scans skip a projected
//! target (7757, 7781), so `t.0 = Wake::Observed(7)` is not "another value"
//! and `stamp` is `Back::Yes`. (2) Seeing it only makes `stamp`
//! `Back::Rewrites`, and by the doc at 7855-7859 "what comes back is still ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
fn stamp(w: Wake) -> Wake { let mut t = (w, 0u8); t.0 = Wake::Observed(7); t.0 }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match stamp(wake) {
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
