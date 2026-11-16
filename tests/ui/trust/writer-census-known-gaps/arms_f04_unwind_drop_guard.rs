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
//! lines 11178-11204. Wrong sentence (11196-11197): "On the normal path; a
//! call or drop that exists only on an unwind path is kept apart, for when a
//! span has no other", implemented as `for (span, calls) in unwind_at {
//! blocks_at.entry(span).or_insert(calls); }` (11202-11204). It takes the ..

use std::sync::mpsc::{channel, Receiver};
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config, pub observed_ran: bool }
pub enum Wake { Observed(u8), Tick }
struct Commit<'a> { app: &'a mut App, level: u8 }
impl Drop for Commit<'_> {
    fn drop(&mut self) { self.app.config.harness = Policy(self.level); }
}
impl App {
    fn on_wake(&mut self, wake: Wake) {
        let mut txn = Commit { app: self, level: 7 };
        match wake {
            Wake::Observed(p) => { txn.app.observed_ran = true; txn.level = p; }
            Wake::Tick => panic!("tick"),
        }
    }
}
fn pump(app: &mut App, rx: Receiver<Wake>) { for wake in rx { app.on_wake(wake); } }
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Tick); });
    let mut app = App::default();
    let died = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| pump(&mut app, rx))).is_err();
    sender.join().unwrap();
    println!("harness: {:?}; only Tick was sent; the Tick arm panicked: {died}; the Observed arm ran: {}", app.config.harness, app.observed_ran);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
