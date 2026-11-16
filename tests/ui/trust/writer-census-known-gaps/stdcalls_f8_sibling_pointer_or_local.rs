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
//! Root, as its skeptic put it: `pointer_to`, writer_origins.rs 1254-1312: a
//! borrow of a sibling place behind a lent pointer is `Region::Apart` (1277)
//! and gets no fact, no slot and no `outside` (1293 sets it for `Unmatched`
//! only): an EMPTY origin. Module docs 81-82: "No fact is APART: provably the
//! body's own value, a sibling's, or no pointer. A pointer is ..

// Minimized F8: `r` points to the sibling `self.peer` (apart: an empty origin) or to a local, so what is read
// out of it is taken to be the local's alone. `peer` points into ANOTHER value the handler ran on.
use std::sync::mpsc::channel;
#[derive(Debug)]
pub struct Policy(pub u8);
pub struct Config { pub harness: Policy }
pub struct App<'a> { pub config: Config, pub peer: Option<&'a mut Config> }
pub enum Wake { Observed(u8), Tick }
impl App<'_> {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => self.config.harness = Policy(p),
            Wake::Tick => {
                let mut scratch = None;
                let r = if self.peer.is_some() { &mut self.peer } else { &mut scratch };
                if let Some(c) = r { c.harness = Policy(9); }
            }
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    tx.send(Wake::Observed(1)).unwrap();
    tx.send(Wake::Tick).unwrap();
    drop(tx);
    let mut first = App { config: Config { harness: Policy(0) }, peer: None };
    first.on_wake(rx.recv().unwrap()); // Observed(1), on `first`
    let mut second = App { config: Config { harness: Policy(0) }, peer: Some(&mut first.config) };
    for wake in rx { second.on_wake(wake); } // Tick, on `second`
    println!("first harness at the end: {:?}", first.config.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
