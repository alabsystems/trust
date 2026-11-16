//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: stdcalls; uses `unsafe`).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: `pointer_to`, writer_origins.rs 1254-1291,
//! with `can_write` 1249-1251: a `&` borrow of a place with no interior
//! mutability gets no fact at all (everything in 1263-1291 is under `if
//! self.can_write(place, mutable)`). The raw reborrow MIR makes of it (`&raw
//! const (*_r)`: `Rvalue::RawPtr` at 1339 -> `pointer_to(place, true)`) ..

// Minimized U1 (unsafe, and undefined behaviour by Rust's aliasing rules): a raw pointer made from a `&` of
// the value holding the field has no origin, so the write through it is no site.
use std::sync::mpsc::channel;
#[derive(Debug)]
pub struct Policy(pub u8);
pub struct Config { pub harness: Policy }
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => self.config.harness = Policy(p),
            Wake::Tick => { let p = &self.config as *const Config as *mut Config; unsafe { (*p).harness = Policy(9); } }
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
