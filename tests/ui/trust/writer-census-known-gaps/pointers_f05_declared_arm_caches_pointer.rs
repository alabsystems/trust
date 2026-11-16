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
//! Root, as its skeptic put it: This is a hole in the claim, not a departure
//! from it. writer_origins.rs module docs lines 16-19 (S2) and
//! `Frame::pointer_to` 1268-1271: "every pointer to the field itself was made
//! by a borrow of its path, and is followed from there." It is followed only
//! until it leaves. `scan_writes` 2720-2761 reports the borrow ("takes a `&`
//! ..

use std::sync::atomic::{AtomicU8, Ordering::Relaxed};
use std::sync::mpsc::channel;
pub struct App { pub harness: AtomicU8 }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake<'a>(&'a self, wake: Wake, cache: &mut Option<&'a AtomicU8>) {
        match wake {
            Wake::Observed(p) => { self.harness.store(p, Relaxed); *cache = Some(&self.harness); }
            Wake::Tick => { if let Some(flag) = cache { flag.store(9, Relaxed); } }
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); });
    let app = App { harness: AtomicU8::new(0) };
    let mut cache = None;
    for wake in rx { app.on_wake(wake, &mut cache); }
    sender.join().unwrap();
    println!("final harness: {}", app.harness.load(Relaxed));
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "harness" ["Observed"] []
}
