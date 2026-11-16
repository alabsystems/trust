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
//! Root, as its skeptic put it: concurrency_effects.rs `check_binding`, lines
//! 12090-12108: `.map(|consumer| format!("`{}`", consumer.message))`, then
//! `of.sort(); of.dedup(); (of.len() > 1)`. The messages a writer name
//! matches are deduplicated by their PRINTED names. Two block-local enums in
//! one fn both print `main::Wake`, so `twice` stays empty and the ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
fn main() {
    let mut app = App::default();
    let mut first_enum_observed_ran = false;
    {
        enum Wake { Observed(u8), Tick }
        let (tx, rx) = channel::<Wake>();
        drop(tx);
        for wake in rx { match wake { Wake::Observed(p) => { first_enum_observed_ran = true; app.config.harness = Policy(p); } Wake::Tick => {} } }
    }
    {
        enum Wake { Idle, Observed }
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed); });
        for wake in rx { match wake { Wake::Observed => { app.config.harness = Policy(7); } Wake::Idle => {} } }
        sender.join().unwrap();
    }
    println!("harness: {:?}; the first enum's Observed arm ran: {first_enum_observed_ran}", app.config.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
