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
//! Root, as its skeptic put it: writer_origins.rs `Frame::owns_root_in`
//! 641-643 and `Frame::has_inside_in` 850-852: a std type is read by its type
//! ARGUMENTS only (`!adt.is_phantom_data() && args.types().any(|inner|
//! self.owns_root(inner))`). Wrong sentence (doc of `owns_root`): "Whether a
//! value of type `ty` holds, or OWNS in memory of its own (a std ..

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
pub struct Batches(u8);
impl Iterator for Batches {
    type Item = Vec<App>;
    fn next(&mut self) -> Option<Vec<App>> { if self.0 == 0 { None } else { self.0 -= 1; Some(Vec::from([App::default()])) } }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); drop(tx);
    let mut batches = Batches(1).peekable();
    for wake in rx {
        if let Some(app) = batches.peek_mut().into_iter().flatten().last() { app.on_wake(wake); }
        if let Some(app) = batches.peek_mut().into_iter().flatten().last() { println!("after the handler: {:?}", app.config.harness); }
        if let Some(app) = batches.peek_mut().into_iter().flatten().last() { app.config.harness = Policy(9); }
        if let Some(app) = batches.peek_mut().into_iter().flatten().last() { println!("after main:        {:?}", app.config.harness); }
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
