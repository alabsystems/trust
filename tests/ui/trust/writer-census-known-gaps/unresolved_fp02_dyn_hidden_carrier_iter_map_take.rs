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
//! Root, as its skeptic put it: Same root as fp01: writer_origins.rs
//! `Frame::reaches_in`, the `ty::Dynamic` arm, lines 584-614 (sentence
//! 584-586: "What a `dyn` hides is not known; what its trait NAMES is ...").
//! The dump of `drain` shows `_1: &mut dyn Lend<'_>` `lent: true, reaching:
//! false` and `_3: Map<It, fn item mem::take>` carrying only `lent`. So in ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default, Debug)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
trait Lend<'a> { fn lend(&mut self) -> Option<&'a mut Config>; }
struct Slot<'a>(Option<&'a mut Config>);
impl<'a> Lend<'a> for Slot<'a> { fn lend(&mut self) -> Option<&'a mut Config> { self.0.take() } }
struct It<'a, 'b>(&'b mut dyn Lend<'a>);
impl<'a, 'b> Iterator for It<'a, 'b> {
    type Item = &'a mut Config;
    fn next(&mut self) -> Option<&'a mut Config> { self.0.lend() }
}
fn drain<'a>(l: &mut dyn Lend<'a>) { It(l).map(std::mem::take).count(); }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            // The ONLY arm the binding below allows to write `config.harness`.
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {
                drain(&mut Slot(Some(&mut self.config)));
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
