//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: values; uses `unsafe`).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: concurrency_effects.rs `overlap`, second
//! `beside` arm, 10523-10532. Wrong sentence: "A field of a value that holds
//! the consumer's (`Session { app, backup }`, `(App, Config)`) that is not
//! the way to it: a sibling of the value itself." Applied to a `union`, whose
//! fields are the same bytes: `holds(Slot)` is true (`holds_by_value` ..

use std::sync::mpsc::channel;
use std::mem::ManuallyDrop;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub union Slot { pub app: ManuallyDrop<App>, pub raw: [u8; 1] }
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
    let mut slot = Slot { app: ManuallyDrop::new(App::default()) };
    for wake in rx {
        unsafe { (*slot.app).on_wake(wake); }
        println!("after the handler: {:?}", unsafe { &slot.app.config.harness });
        slot.raw = [9];
        println!("after main:        {:?}", unsafe { &slot.app.config.harness });
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
