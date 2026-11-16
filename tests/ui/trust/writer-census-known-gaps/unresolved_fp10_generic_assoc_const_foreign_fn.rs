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
//! Root, as its skeptic put it: concurrency_effects.rs `written_fields`, the
//! `Values` visitor that fills `foreign_inputs`: `visit_const_operand`
//! 10967-10985 and the loop over `const`/`static` bodies 11013-11030. Wrong
//! sentence (10936-10938): "A generic body is read at the instances the
//! program makes of it, as everywhere here: one it makes none of never runs,
//! ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default, Debug)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
struct Ops<T>(std::marker::PhantomData<T>);
impl<T: Default> Ops<T> { const TAKE: fn(&mut T) -> T = std::mem::take::<T>; }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            // The ONLY arm the binding below allows to write `config.harness`.
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {
                (Ops::<Config>::TAKE)(&mut self.config);
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
