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
//! Root, as its skeptic put it: concurrency_effects.rs `std_passes_on` lines
//! 12378-12445 (the names `next` and `next_back` at 12411-12412), used by
//! `scan_writes` in writer_origins.rs 2972-2979 (`passes_on` makes `lends_it`
//! false). Wrong sentences: "It writes nothing through a pointer it is handed
//! (an iterator's `next` advances the iterator)" (12380-12381), ..

// FALSE PASS (safe). The path passes a std struct with public fields (`Range { start, end }`), and
// an undeclared arm calls `Iterator::next` on it. `next` is on the list of accessors that "only
// hand on what they are given" (`std_passes_on`), so lending it a `&mut` reaching the field is no
// site; but `Range::next` writes `start`. (`self.range.nth(0)` fails; so does `next` through a
// `&mut dyn Iterator`.) Prints 2; Observed sets 1.
use std::sync::mpsc::channel;
pub struct App { pub range: std::ops::Range<u8> }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => self.range.start = p,
            Wake::Tick => { self.range.next(); }
        }
    }
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); });
    let mut app = App { range: 0..200 };
    for wake in rx { app.on_wake(wake); }
    sender.join().unwrap();
    println!("final range.start: {}", app.range.start);
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "range.start" ["Observed"] []
}
