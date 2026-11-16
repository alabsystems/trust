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
//! Root, as its skeptic put it: Two places. (1) `std_passes_on`,
//! concurrency_effects.rs 12386-12466, via `scan_writes`, writer_origins.rs
//! 2967-2995: `deref_mut` of `AssertUnwindSafe<Policy>` (a container ON the
//! path) is taken to only hand on the holder pointer; its result is
//! `lent,reaching`, never `whole`. (2) `overlap`, concurrency_effects.rs
//! 10567-10570: a ..

// Minimized F3: `deref_mut` (an accessor) of an `AssertUnwindSafe` the bound path passes hands back a pointer
// to the field itself; a write of PART of the field through it matches nothing.
use std::panic::AssertUnwindSafe;
use std::sync::mpsc::channel;
#[derive(Debug)]
pub struct Policy(pub u8);
pub struct App { pub harness: AssertUnwindSafe<Policy> }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => self.harness.0 = Policy(p),
            Wake::Tick => (*self.harness).0 = 9, // `DerefMut::deref_mut(&mut self.harness).0 = 9`
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    tx.send(Wake::Tick).unwrap(); // no `Observed` is ever sent
    drop(tx);
    let mut app = App { harness: AssertUnwindSafe(Policy(0)) };
    for wake in rx { app.on_wake(wake); }
    println!("final harness: {:?}", app.harness.0);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "harness.0" ["Observed"] []
}
