//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: unresolved).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: writer_origins.rs `Frame::leaving`, lines
//! 2165-2175 (with the drop rule at 2242-2251). Wrong sentence (2167-2168):
//! "The closure knows its captures; but the variables a captured pointer
//! points INTO are now its to read", followed by `continue`: no `made_from`
//! edge is recorded from the closure to a value it captured BY MOVE. The ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default, Debug)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
struct Guard<'a>(&'a mut u8);
impl Drop for Guard<'_> { fn drop(&mut self) { *self.0 = 9; } }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            // The ONLY arm the binding below allows to write `config.harness`.
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {
                let g = Guard(&mut self.config.harness.0);
                move || { &g; };
            }
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    tx.send(Wake::Observed(1)).unwrap();
    tx.send(Wake::Tick).unwrap();
    drop(tx);
    let mut app = App::default();
    // Messages arrive in the order Observed(1), Tick. Only Observed may write the field.
    for wake in rx {
        app.on_wake(wake);
        println!("harness after a message: {:?}", app.config.harness);
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
