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
//! 10330-10397: `if *count >= HOLDER_EXPANSIONS { continue; }` (10367-10372;
//! the const is 256, 10399-10401) on a last-in-first-out work list
//! (`work.pop()`, 10348). Wrong sentence (doc of the const): "How many
//! instantiations of one definition holds_by_value opens: a type that holds
//! its next ..

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
type D0<T> = (Option<T>, Option<(T,)>);
type D1<T> = (D0<T>, D0<[T; 2]>);
type D2<T> = (D1<T>, D1<[T; 3]>);
type D3<T> = (D2<T>, D2<[T; 5]>);
type D4<T> = (D3<T>, D3<[T; 7]>);
type D5<T> = (D4<T>, D4<[T; 11]>);
type D6<T> = (D5<T>, D5<[T; 13]>);
type D7<T> = (D6<T>, D6<[T; 17]>);
pub struct Host { pub app: Option<App>, pub registry: Option<Box<D7<()>>> }
fn main() {
    let (tx, rx) = channel::<Wake>();
    let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); drop(tx);
    let mut host = Host { app: Some(App::default()), registry: None };
    for wake in rx {
        if let Some(app) = &mut host.app { app.on_wake(wake); println!("after the handler: {:?}", app.config.harness); }
        if let Some(app) = &mut host.app { app.config.harness = Policy(9); println!("after main:        {:?}", app.config.harness); }
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
