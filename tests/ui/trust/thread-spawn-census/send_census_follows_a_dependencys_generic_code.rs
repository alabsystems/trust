//@ needs-trust-verify
//@ aux-build:census_dep.rs
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Generic code in a dependency is walked, and the trace says what it could
//! not follow there. `post` is handed the message: its variant is traced.
//! `post_all` is handed a `Vec` of them and `post_default` makes one from a
//! bound on its parameter: the message is not an argument, so the trace is
//! incomplete (`…`), not empty and complete. `reply_from` is not generic over
//! the message it sends at all (it converts its argument). A thread started
//! through the dependency's `spawn_named` has no spawn site in this crate: its
//! note goes at the local call, one note per thread.

extern crate census_dep;

use std::sync::mpsc::channel;

use census_dep::Reply;

enum Wake {
    One,
    Many,
    Made,
}

impl Default for Wake {
    fn default() -> Self {
        Wake::Made
    }
}

struct Code(u8);

impl From<Code> for Reply {
    fn from(code: Code) -> Reply {
        if code.0 == 0 { Reply::Done } else { Reply::Failed }
    }
}

fn main() { //~ NOTE consumer census: `main` drains a channel of `Wake`; its switch gives each of its 3 variants an arm. No send was traced to `Wake::Many` and `Wake::Made`. 2 thread(s) send `Wake` with a value the census could not trace to a variant
    let (tx, rx) = channel::<Wake>();
    let (reply_tx, replies) = channel::<Reply>();
    let (one, many, made) = (tx.clone(), tx.clone(), tx);
    let _one = census_dep::spawn_named("one", move || census_dep::post(&one, Wake::One)); //~ NOTE send census: the thread spawned through this call sends `Wake` (One) via
    let _many = census_dep::spawn_named("many", move || census_dep::post_all(&many, vec![Wake::Many])); //~ NOTE send census: the thread spawned through this call sends `Wake` (…) via
    let _made = census_dep::spawn_named("made", move || census_dep::post_default(&made)); //~ NOTE send census: the thread spawned through this call sends `Wake` (…) via
    let _reply = std::thread::spawn(move || census_dep::reply_from(&reply_tx, Code(0))); //~ NOTE send census: the thread spawned here sends `Reply` (…) via
    let _ = replies.recv();
    while let Ok(wake) = rx.recv() {
        match wake {
            Wake::One => {} //~ NOTE consumer census: the arm for `Wake::One` in `main` takes it from `main::{closure#0}`
            Wake::Many => {} //~ NOTE consumer census: the arm for `Wake::Many` in `main`: no send was traced to it
            Wake::Made => {}
        }
    }
}
