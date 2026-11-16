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
//! Root, as its skeptic put it: concurrency_effects.rs `dispatch`, `reset`
//! 8230-8252 with the flow at 8335-8385, on top of held_message's doc
//! 7324-7326 ("Locals are classed once for the whole body ... one assigned
//! the message on one path and another value on another counts as the
//! message"). Wrong sentence (8230-8231): "A held local given another value
//! (`m = ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, mut wake: Wake) {
        match wake {
            Wake::Observed(_) => {}
            Wake::Tick => {
                wake = Wake::Observed(7);
                if let Wake::Observed(p) = wake { self.config.harness = Policy(p); }
            }
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
