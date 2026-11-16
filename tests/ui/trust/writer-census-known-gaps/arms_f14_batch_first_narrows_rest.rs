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
//! Root, as its skeptic put it: concurrency_effects.rs `Held::roots`
//! 7210-7230 with `receives_message` 6946-6974 and the per-root flow in
//! `dispatch` (8274-8325, 8362-8383). Wrong sentence (7210-7213): "two held
//! locals with no root in common are two messages (two receives, two
//! parameters), and a switch over one says nothing about the other", applied
//! the other ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config, pub n: u32 }
pub enum Wake { Observed(u8), Tick, Quit }
impl App {
    fn pump(&mut self, rx: Receiver<Wake>) {
        let batch: Vec<Wake> = rx.iter().collect();
        let mut rest = batch.into_iter();
        let Some(first) = rest.next() else { return };
        if let Wake::Quit = first { return; }
        for wake in rest {
            match wake {
                Wake::Tick => { self.n += 1; }
                _ => { self.config.harness = Policy(7); }
            }
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
    let mut app = App::default();
    app.pump(rx);
    sender.join().unwrap();
    println!("harness: {:?}; only Tick and Quit were sent, no Observed", app.config.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
