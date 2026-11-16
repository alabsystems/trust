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
//! Root, as its skeptic put it: concurrency_effects.rs `written_fields`,
//! lines 11136-11174. Wrong sentence (11136-11138): "A consumer that takes no
//! argument with the path may run on a local of its own ...: the first
//! variable of its body that has the path", implemented as `if
//! local.as_usize() <= body.arg_count || !resolved.is_empty() { continue; }`
//! (11163). A ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
#[derive(Default)]
pub struct Preview { pub config: Config }
pub enum Wake { Observed(u8), Tick }
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Tick); });
    let mut preview = Preview::default();
    let mut app = App::default();
    let mut observed_ran = false;
    for wake in rx {
        match wake {
            Wake::Observed(p) => { observed_ran = true; preview.config.harness = Policy(p); }
            Wake::Tick => { app.config.harness = Policy(7); }
        }
    }
    sender.join().unwrap();
    println!("App.config.harness: {:?}; only Tick was sent; the Observed arm ran: {observed_ran}", app.config.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
