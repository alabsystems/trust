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
//! Root, as its skeptic put it: Same rule as F08: concurrency_effects.rs
//! held_message 7324-7326 (`last` is `Hold::Is` for the whole body because
//! `last = m` on one path) and `dispatch` `reset` 8230-8252 with the flow
//! 8335-8385. The block that seeds `last` only makes it "any variant", so the
//! switch over it at the loop head is a counted dispatch and its Observed ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config, pub received: u32 }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn pump(&mut self, rx: Receiver<Wake>) {
        let mut last = Wake::Observed(7);
        loop {
            if let Wake::Observed(k) = last { self.config.harness = Policy(k); }
            match rx.recv() {
                Ok(m) => { self.received += 1; last = m; }
                Err(_) => break,
            }
        }
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
