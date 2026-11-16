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
//! Root, as its skeptic put it: writer_origins.rs `Frame::reaches_in` lines
//! 530-617: there is an arm for `ty::Closure` (581-583, its upvars) and none
//! for `ty::Coroutine`, which falls to `_ => false` at 615; asked by
//! `Frame::unknown_inside` 961-966 for the parameter `f: F` at the instance F
//! = the async block. Wrong sentence (doc comment 521-525): "Whether a ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default, Debug)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
use std::future::Future; use std::marker::PhantomData; use std::pin::Pin;
use std::task::{Context, Poll, Waker};
struct Guard<'a, F>(Pin<Box<F>>, PhantomData<&'a ()>);
impl<'a, F: Future<Output = &'a mut Config>> std::ops::Deref for Guard<'a, F> {
    type Target = Config;
    fn deref(&self) -> &Config { unreachable!() }
}
impl<'a, F: Future<Output = &'a mut Config>> std::ops::DerefMut for Guard<'a, F> {
    fn deref_mut(&mut self) -> &mut Config {
        match self.0.as_mut().poll(&mut Context::from_waker(Waker::noop())) { Poll::Ready(c) => c, Poll::Pending => unreachable!() }
    }
}
fn overwrite<'a, F: Future<Output = &'a mut Config>>(f: F) {
    Pin::new(Guard(Box::pin(f), PhantomData)).set(Config { harness: Policy(9) });
}
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            // The ONLY arm the binding below allows to write `config.harness`.
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {
                let c = &mut self.config;
                overwrite(async move { c });
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
