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
//! Root, as its skeptic put it: writer_origins.rs `scan_writes`:
//! `handed_to_consumer` 2436-2453 returns every by-value argument of the
//! consumer call that is an owned variable, and `flow_terminator` 2547-2554
//! exempts the destination when it is ANY of them (`again &&
//! !handed_to_consumer(func, args).contains(&destination.local)`). Wrong
//! sentence (2432-2435): "A ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(mut self: Box<Self>, wake: Wake, _retired: Box<App>) -> Box<App> {
        match wake {
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {}
        }
        self
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); drop(tx);
    let mut app = Box::new(App::default());
    for wake in rx {
        app = Box::new(App { config: Config { harness: Policy(9) } }).on_wake(wake, app);
        println!("after the handler: {:?}", app.config.harness);
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
