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
//! Root, as its skeptic put it: writer_origins.rs `scan_writes`, the
//! `reachable`/`reach` closures at lines 2612-2626, together with
//! `Frame::reaches_in` 567-576. Wrong sentence (2620-2621): "What that value
//! may reach; and whether it is itself a pointer that reaches a value holding
//! the field" is computed from `Origin::reaches()` alone. A `&mut app` of a
//! local ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default, Debug)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
use std::rc::Rc;
struct Guard<'a>(&'a mut Rc<App>);
impl std::ops::Deref for Guard<'_> { type Target = Config; fn deref(&self) -> &Config { unreachable!() } }
impl std::ops::DerefMut for Guard<'_> { fn deref_mut(&mut self) -> &mut Config { &mut Rc::get_mut(self.0).unwrap().config } }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            // The ONLY arm the binding below allows to write `config.harness`.
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {}
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    tx.send(Wake::Observed(1)).unwrap();
    tx.send(Wake::Tick).unwrap();
    drop(tx);
    let mut app = Rc::new(App::default());
    for wake in rx {
        Rc::get_mut(&mut app).unwrap().on_wake(wake);
        println!("harness after a message: {:?}", app.config.harness);
    }
    // Outside the consumer, on the value it ran on:
    std::pin::Pin::new(Guard(&mut app)).set(Config { harness: Policy(9) });
    println!("harness after the loop: {:?}", app.config.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
