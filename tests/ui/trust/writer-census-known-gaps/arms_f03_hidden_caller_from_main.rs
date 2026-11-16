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
//! Root, as its skeptic put it: Same rule as F01: concurrency_effects.rs
//! `report_consumers` 8832-8864 (a call through a local holding the fn item
//! is not a call site, so `one_way_in(apply)` is true and its entry is
//! {Observed}). Then `written_fields` 11477-11485: a site inside a consumer's
//! own body is attributed by its blocks' variants alone (`around` is filled
//! ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config, pub observed_ran: bool }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            w @ Wake::Observed(_) => { self.observed_ran = true; self.apply(w) }
            Wake::Tick => {}
        }
    }
    fn apply(&mut self, w: Wake) {
        self.config.harness = Policy(7);
        if let Wake::Observed(_) = w {}
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    drop(tx);
    let mut app = App::default();
    let init = App::apply;
    init(&mut app, Wake::Tick);
    for wake in rx { app.on_wake(wake); }
    println!("harness: {:?}; no message was ever sent; the Observed arm of on_wake ran: {}", app.config.harness, app.observed_ran);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
