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
//! Root, as its skeptic put it: `Frame::given`, writer_origins.rs 1570-1583,
//! with `hands_back_own` 1482-1508 (and `owns_root_in` 633-650 for the
//! `dyn`). Wrong sentence (1567-1569): `given` is `None` only "for a call
//! that is also given code that may hand back a pointer of its own", and
//! `hands_back_own` finds code only in callables NAMED in the argument types
//! ..

// Minimized F4: std's `Iterator::nth` runs the crate's `next`, which takes a `&mut App` out of an `Rc<dyn Any>`.
use std::any::Any;
use std::rc::Rc;
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
            Wake::Tick => {}
        }
    }
}
struct Walk<'a>(Option<&'a mut Rc<dyn Any>>);
impl<'a> Iterator for Walk<'a> {
    type Item = &'a mut App;
    fn next(&mut self) -> Option<&'a mut App> { Rc::get_mut(self.0.take()?)?.downcast_mut::<App>() }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    tx.send(Wake::Observed(1)).unwrap();
    drop(tx);
    let mut store: Rc<dyn Any> = Rc::new(App { config: Config { harness: Policy(0) } });
    for wake in rx {
        let app = Walk(Some(&mut store)).nth(0).unwrap();
        app.on_wake(wake);
        app.config.harness = Policy(9); // in `main`, in no arm
    }
    println!("final harness: {:?}", store.downcast_ref::<App>().unwrap().config.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
