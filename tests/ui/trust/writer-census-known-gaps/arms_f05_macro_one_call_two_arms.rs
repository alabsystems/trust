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
//! lines 11518-11541. Wrong sentence (11518-11519): "The call the edge stands
//! for: a macro can put calls of several fns at one span", implemented as
//! `own = named(callee == to)` (11533), with the blocks whose callee is not
//! named consulted only when that set is empty (11534-11538). A block at ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config, pub n: u32, pub observed_ran: bool }
pub enum Wake { Observed(u8), Tick }
fn set(app: &mut App, p: u8) { app.config.harness = Policy(p); }
macro_rules! in_both {
    ($wake:expr, $f:ident, $seen:expr, $call:expr) => {
        match $wake {
            Wake::Observed(_) => { $seen; $call }
            Wake::Tick => { let $f = $f; $call }
        }
    };
}
impl App {
    fn on_wake(&mut self, wake: Wake) { in_both!(wake, set, self.observed_ran = true, set(self, 7)); }
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
