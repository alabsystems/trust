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
//! Root, as its skeptic put it: writer_origins.rs `Frame::given` 1585-1599:
//! `reads_memory |= unowned && (kept || self.owns_root(pointee))` is asked
//! only of an argument that IS a pointer; of a by-value carrier (`Option<&mut
//! Vec<App>>`) only the local slots it points into are asked (1611-1612). The
//! pointer in it has neither fact nor slot: `pointer_to` ..

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
pub struct Session { pub app: App, pub extra: Vec<App> }
fn main() {
    let (tx, rx) = channel::<Wake>();
    let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); drop(tx);
    let mut s = Session { app: App::default(), extra: vec![App::default()] };
    for wake in rx {
        s.extra[0].on_wake(wake);
        println!("after the handler: {:?}", s.extra[0].config.harness);
        if let Some(app) = Some(&mut s.extra).into_iter().flatten().last() { app.config.harness = Policy(9); }
        println!("after main:        {:?}", s.extra[0].config.harness);
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
