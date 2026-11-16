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
//! Root, as its skeptic put it: `Frame::val`, writer_origins.rs 1157-1201,
//! line 1179: `if x.facts() || x.slots.is_empty()` decides "Out of memory the
//! body does not own", and `Origin::facts` (131-134, "Any fact but the slots:
//! it may point outside the body's own storage") leaves `outside` out.
//! `pointer_to` (1263-1294) gives a borrow of a place that matches no ..

// Minimized F7: `chosen` points to the caller's slot or to a local; the pointer read out of it is taken to be
// the local's alone, and the write through it is no site.
use std::sync::mpsc::channel;
#[derive(Debug)]
pub struct Policy(pub u8);
pub struct Config { pub harness: Policy }
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
fn apply(given: &mut Option<&mut Config>, use_it: bool) {
    let mut fallback = None;
    let chosen = if use_it { given } else { &mut fallback };
    if let Some(c) = chosen { c.harness = Policy(9); }
}
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => self.config.harness = Policy(p),
            Wake::Tick => apply(&mut Some(&mut self.config), true),
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    tx.send(Wake::Tick).unwrap(); // no `Observed` is ever sent
    drop(tx);
    let mut app = App { config: Config { harness: Policy(0) } };
    for wake in rx { app.on_wake(wake); }
    println!("final harness: {:?}", app.config.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
