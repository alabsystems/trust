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
//! Root, as its skeptic put it: Same rule as F06: concurrency_effects.rs
//! `dispatch` 8016-8229, `taken`/`begins` (8037-8068, 8182-8211). The flow at
//! 8177-8200 says what follows the loop is outside the arm ("so is what
//! follows the loop"), and `begins.contains(&block)` overrides it for the
//! block that reads the payload of `last`, a local classed as the message ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config, pub received: u32 }
pub enum Wake { Observed(u8) }
impl App {
    fn pump(&mut self, rx: Receiver<Wake>) {
        let mut last = Wake::Observed(7);
        while let Ok(m) = rx.recv() { self.received += 1; last = m; }
        let Wake::Observed(k) = last;
        self.config.harness = Policy(k);
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    drop(tx);
    let mut app = App::default();
    app.pump(rx);
    println!("harness: {:?}; no message was ever sent; messages received: {}", app.config.harness, app.received);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
