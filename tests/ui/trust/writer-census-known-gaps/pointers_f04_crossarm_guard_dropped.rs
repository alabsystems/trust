//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: pointers).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: writer_origins.rs `scan_writes` lines
//! 2774-2785 (Drop terminator) and 2801-2829 (the "hands on a pointer to"
//! check exists only for call arguments), with `Frame::leaving` 2242-2251.
//! Wrong sentence (2774-2775): "A value that reaches a holder, dropped by a
//! `Drop` impl of another crate's: its body is not read here" is the only
//! drop ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct App { pub harness: Policy }
pub enum Wake { Observed(u8), Tick }
struct Guard<'a>(&'a mut u8);
impl Drop for Guard<'_> { fn drop(&mut self) { *self.0 = 9; } }
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); });
    let mut app = App::default();
    let mut kept: Option<Guard> = None;
    for wake in rx {
        match wake {
            Wake::Observed(p) => { kept = None; app.harness = Policy(p); kept = Some(Guard(&mut app.harness.0)); }
            Wake::Tick => { kept = None; }
        }
    }
    sender.join().unwrap();
    std::mem::forget(kept);
    println!("final harness: {:?}", app.harness);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "harness" ["Observed"] []
}
