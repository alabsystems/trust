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
//! Root, as its skeptic put it: concurrency_effects.rs `overlap`, first
//! `beside` arm, lines 10518-10522 ("Another field of a type on the path: a
//! sibling's"), reached through writer_origins.rs `Frame::boxed_by_path`
//! 1100-1112 (`Region::Apart => Origin::default()`) and `Frame::pointer_to`
//! 1254-1312. Wrong sentence: "A write that passes another field of a type ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config, pub children: Box<[App]> }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {}
        }
    }
    fn relax_children(&mut self) { self.children[0].config.harness = Policy(9); }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); drop(tx);
    let mut root = App { children: Box::new([App::default()]), ..App::default() };
    for wake in rx {
        root.children[0].on_wake(wake);
        println!("after the handler: {:?}", root.children[0].config.harness);
        root.relax_children();
        println!("after the helper:  {:?}", root.children[0].config.harness);
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
