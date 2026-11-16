//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: values; uses `unsafe`).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: writer_origins.rs `Frame::fresh_box`
//! 1751-1771: `if storage && crate::def_is_in_sysroot_resident_crate(tcx,
//! callee) { return true; }` (1755-1762) comes before `if self.names(inner) {
//! return false; }` (1763-1765). Wrong sentence (doc of `fresh_box`):
//! "Storage still to be given a value (`Box::new_uninit()`, as `vec![..]`
//! writes ..

use std::sync::mpsc::channel;
use std::mem::MaybeUninit;
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
    let mut cell: Box<MaybeUninit<App>> = Box::new(MaybeUninit::new(App::default()));
    for wake in rx {
        unsafe { cell.assume_init_mut() }.on_wake(wake);
        println!("after the handler: {:?}", unsafe { cell.assume_init_ref() }.config.harness);
        *cell = MaybeUninit::new(App { config: Config { harness: Policy(9) } });
        println!("after main:        {:?}", unsafe { cell.assume_init_ref() }.config.harness);
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
