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
//! Root, as its skeptic put it: concurrency_effects.rs `receives_message`
//! 6946-6974 and the `fresh` test in `dispatch` (8310-8316, 8386-8392), with
//! held_message 7601-7668. Wrong sentence (8386): "A receive brings a new
//! message: any variant again." Only a std receive called in the body itself
//! counts. `next_wake(&rx)`, a local fn that receives and returns the ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config, pub ticks: u32 }
pub enum Wake { Observed(u8), Tick }
fn next_wake(rx: &Receiver<Wake>) -> Option<Wake> { rx.recv().ok() }
impl App {
    fn pump(&mut self, rx: Receiver<Wake>) {
        let Ok(Wake::Observed(_)) = rx.recv() else { return };
        while let Some(wake) = next_wake(&rx) {
            if let Wake::Tick = wake { self.ticks += 1; self.config.harness = Policy(7); }
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); });
    let mut app = App::default();
    app.pump(rx);
    sender.join().unwrap();
    println!("harness: {:?}; sent: Observed(1), Tick; the Tick arm (the only write, of 7) ran {} time(s)", app.config.harness, app.ticks);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
