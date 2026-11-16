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
//! Root, as its skeptic put it: concurrency_effects.rs `holds_by_value`
//! 10357-10360 (an `Rc`/`Arc` is skipped), behind `BoundPlace::holds`
//! 10310-10324 and `owned_locals` 10767-10783: `app: Rc<App>` is no variable
//! a consumer may run on, so W2 never fires (writer_origins.rs
//! `flow_statement`/`flow_terminator` 2521-2554: `whole(*destination)` is
//! `None`). Wrong ..

use std::sync::mpsc::channel;
use std::rc::Rc;
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
    let mut app: Rc<App> = Rc::new(App::default());
    for wake in rx {
        Rc::get_mut(&mut app).unwrap().on_wake(wake);
        println!("after the handler: {:?}", app.config.harness);
        app = Rc::new(App { config: Config { harness: Policy(9) } });
        println!("after main:        {:?}", app.config.harness);
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
