//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: stdcalls).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: `overlap`, concurrency_effects.rs
//! 10518-10522: `None if (0..=last).any(|step| holds_step(seen, step)) => {
//! *beside = true; return None; }`, "Another field of a type on the path: a
//! sibling's." It does not ask, as the next arm (10523-10532) does for a
//! holder, whether the field taken is the way to a value of the consumer's
//! type ..

// Minimized F6: a sibling field that OWNS another value of the consumer's type is judged a sibling, so a
// direct write into that value's bound field, in an undeclared arm, is no site. (No std fn is needed.)
use std::sync::mpsc::channel;
#[derive(Debug)]
pub struct Policy(pub u8);
pub struct Config { pub harness: Policy }
pub struct App { pub config: Config, pub child: Option<Box<App>> }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            // The handler runs on the child too, for `Observed`.
            Wake::Observed(p) => { self.config.harness = Policy(p); if let Some(child) = &mut self.child { child.on_wake(Wake::Observed(p)); } }
            Wake::Tick => { if let Some(child) = &mut self.child { child.config.harness = Policy(9); } }
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    tx.send(Wake::Observed(1)).unwrap();
    tx.send(Wake::Tick).unwrap();
    drop(tx);
    let leaf = App { config: Config { harness: Policy(0) }, child: None };
    let mut app = App { config: Config { harness: Policy(0) }, child: Some(Box::new(leaf)) };
    for wake in rx { app.on_wake(wake); }
    println!("final child harness: {:?}", app.child.unwrap().config.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
