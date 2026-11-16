//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: stdcalls).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: The same rule as F4: `Frame::given`,
//! writer_origins.rs 1570-1621, with `hands_back_own` 1482-1508. "What a std
//! fn can hand back ..: only what it was GIVEN" is wrong for core's blanket
//! `Into::into`, which runs the crate's `From` impl: std was given a `()` (no
//! pointer at all) and the impl takes its result from a static. The ..

// F5 with no wrapper type: std's blanket `Into::into` runs the crate's `From<()> for &'static App`.
use std::sync::atomic::{AtomicU8, Ordering::Relaxed};
use std::sync::mpsc::channel;
pub struct Config { pub harness: AtomicU8 }
pub struct App { pub config: Config }
static APP: App = App { config: Config { harness: AtomicU8::new(0) } };
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&self, wake: Wake) {
        match wake {
            Wake::Observed(p) => self.config.harness.store(p, Relaxed),
            Wake::Tick => {}
        }
    }
}
impl From<()> for &'static App { fn from(_: ()) -> &'static App { &APP } }
fn main() {
    let (tx, rx) = channel::<Wake>();
    tx.send(Wake::Observed(1)).unwrap();
    drop(tx);
    for wake in rx {
        APP.on_wake(wake);
        let app: &App = ().into();
        app.config.harness.store(9, Relaxed); // in `main`, in no arm
    }
    println!("final harness: {}", APP.config.harness.load(Relaxed));
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}
