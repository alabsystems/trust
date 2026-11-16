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
//! Root, as its skeptic put it: concurrency_effects.rs `held_message`, lines
//! 7605-7636: `match (inner, whole) { (Some(local), _) => (given(ty),
//! Some(local), None), (None, Some(local)) if only => .. }` (7632-7636).
//! `only` is asked when outside code is given the bare message and not when
//! it is given a wrapper. Wrong sentence (7606-7610): "Code outside the crate
//! ..

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
        loop {
            let got = rx.recv_timeout(std::time::Duration::from_millis(20));
            if got.is_ok() { self.received += 1; }
            match got.unwrap_or(Wake::Observed(7)) {
                Wake::Observed(p) => { self.config.harness = Policy(p); break; }
                Wake::Tick => {}
            }
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let mut app = App::default();
    app.pump(rx);
    drop(tx);
    println!("harness: {:?}; no message was ever sent; messages received: {}", app.config.harness, app.received);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
