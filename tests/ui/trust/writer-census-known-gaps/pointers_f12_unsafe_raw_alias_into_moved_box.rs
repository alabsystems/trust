//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: pointers; uses `unsafe`).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: writer_origins.rs `Frame::through` lines
//! 1063-1069: "(What a local box holds is where the box's own facts say.)" A
//! `Slot::Boxed` slot is skipped, and the box's own facts say "storage of its
//! own" for good (`fresh_box` 1751-1771, used at 1816-1818: `p:
//! Origin::default()`), even after the box is moved into the field (a "writes
//! a ..

use std::sync::mpsc::channel;
#[derive(Default)]
pub struct App { pub harness: Box<u8> }
pub enum Wake { Observed(u8), Tick }
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); });
    let mut app = App::default();
    let mut p: *mut u8 = std::ptr::null_mut();
    for wake in rx {
        match wake {
            Wake::Observed(v) => { let mut fresh = Box::new(v); p = &mut *fresh; app.harness = fresh; }
            Wake::Tick => unsafe { *p = 9; },
        }
    }
    sender.join().unwrap();
    println!("final harness: {}", app.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "harness" ["Observed"] []
}
