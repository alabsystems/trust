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
//! Root, as its skeptic put it: writer_origins.rs `scan_writes` 2390-2394 and
//! `flow_statement` 2521-2546: `StorageLive` resets `held`, so a variable's
//! first value is never W2 ("a whole value assigned to one that has one is a
//! whole NEW value"); and concurrency_effects.rs `owned_locals` 10767-10783
//! makes only variables of the root's type or of a by-value holder ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {}
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); drop(tx);
    let mut app = App::default();
    app.on_wake(rx.recv().unwrap());
    println!("after the handler: {:?}", app.config.harness);
    let mut config = app.config;
    config.harness = Policy(9);
    let mut app = App { config };
    for wake in rx { app.on_wake(wake); println!("after the handler: {:?}", app.config.harness); }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
