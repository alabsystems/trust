//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: values).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: writer_origins.rs `Frame::given` 1570-1621:
//! memory the body does not own is asked only `if let Some(pointee) =
//! ty.builtin_deref(true)` (1585-1599) and of the local slots an argument
//! points into (1611-1612). Wrong sentence (doc of `given`): "What a std fn
//! can hand back ...: only what it was GIVEN. The pointers among its ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {}
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); drop(tx);
    let apps: &'static mut [App] = vec![App::default()].leak();
    for wake in rx {
        apps[0].on_wake(wake);
        println!("after the handler: {:?}", apps[0].config.harness);
        apps[0].config.harness = Policy(9);
        println!("after main:        {:?}", apps[0].config.harness);
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
