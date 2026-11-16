//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: values; uses `unsafe`).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: writer_origins.rs `Frame::given` 1570-1621,
//! the same as F01: memory is asked only of pointer arguments (1585-1599) and
//! of local slots (1611-1612), and "a box of the consumer's value, whatever
//! made it" (`pass`, 1830-1834) is asked of `Box` results only. Wrong
//! sentence: "What a std fn can hand back ...: only what it was GIVEN. ..

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
    let raw = std::rc::Rc::into_raw(std::rc::Rc::new(App::default())) as *mut App;
    for wake in rx {
        unsafe { (*raw).on_wake(wake); }
        println!("after the handler: {:?}", unsafe { &(*raw).config.harness });
        unsafe { (*raw).config.harness = Policy(9); }
        println!("after main:        {:?}", unsafe { &(*raw).config.harness });
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
