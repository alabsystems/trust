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
//! `report_consumers`, `call_sites` 8836-8853 and `one_way_in` 8860-8864.
//! Here the uncounted call is `<F as Fn>::call` in the body of the local
//! generic fn `retry`. The `call_sites` loop reads each body once as written
//! (not at `substs(def)`), and `run_by` (8650-8669) finds no local body for
//! ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config, pub n: u32, pub observed_ran: bool }
pub enum Wake { Observed(u8), Tick }
fn retry<F: Fn(&mut App, Wake)>(f: F, app: &mut App) { f(app, Wake::Tick) }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            w @ Wake::Observed(_) => { self.observed_ran = true; self.apply(w) }
            Wake::Tick => retry(App::apply, self),
        }
    }
    fn apply(&mut self, w: Wake) {
        self.config.harness = Policy(7);
        if let Wake::Observed(_) = w {}
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Tick); });
    let mut app = App::default();
    for wake in rx { app.on_wake(wake); }
    sender.join().unwrap();
    println!("harness: {:?}; only Tick was sent; the Observed arm of on_wake ran: {}", app.config.harness, app.observed_ran);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
