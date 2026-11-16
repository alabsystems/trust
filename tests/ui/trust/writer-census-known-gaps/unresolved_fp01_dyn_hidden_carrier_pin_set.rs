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
//! Root, as its skeptic put it: writer_origins.rs `Frame::reaches_in`, the
//! `ty::Dynamic` arm, lines 584-614 (asked by `Frame::unknown` 982-986 for
//! the parameter `l: &mut dyn Lend`). Wrong sentence (584-586): "What a `dyn`
//! hides is not known; what its trait NAMES is: a `dyn Iterator<Item = &mut
//! Config>` hands out pointers that reach, a `dyn Write` names none". ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default, Debug)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
trait Lend { fn config(&mut self) -> &mut Config; }
impl Lend for App { fn config(&mut self) -> &mut Config { &mut self.config } }
struct Guard<'a>(&'a mut dyn Lend);
impl std::ops::Deref for Guard<'_> { type Target = Config; fn deref(&self) -> &Config { unreachable!() } }
impl std::ops::DerefMut for Guard<'_> { fn deref_mut(&mut self) -> &mut Config { self.0.config() } }
fn overwrite(l: &mut dyn Lend) {
    std::pin::Pin::new(Guard(l)).set(Config { harness: Policy(9) });
}
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            // The ONLY arm the binding below allows to write `config.harness`.
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {
                overwrite(self);
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
