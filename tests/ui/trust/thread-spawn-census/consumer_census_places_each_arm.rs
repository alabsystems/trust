//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Each arm's note goes at the arm's own pattern. `drain` handles `Quit` in
//! an early `if let`, so the main match's arm for it can never run: the note
//! for `Quit` goes at the `if let`. Its arms for `Skip` and `Idle` only jump
//! (`continue`), and share their first block: each still gets its own note.
//! `Take` moves its payload out, so the compiler adds a switch of its own to
//! drop what is left of the message: that one is not the body's dispatch, and
//! with the uninhabited `Never` it must not turn "cannot occur" into a
//! catch-all. `nested` receives again inside an arm, through an iterator
//! adapter: the inner message is a new one, with every variant.

use std::convert::Infallible;
use std::sync::mpsc::{Receiver, channel};

enum Wake {
    Set,
    Skip,
    Idle,
    Quit,
    Take(String),
    Never(Infallible),
}

fn keep(_: String) {}

fn drain(rx: &Receiver<Wake>) -> u32 { //~ NOTE consumer census: `drain` drains a channel of `Wake`; its switch gives 5 of its 6 variants an arm, and the other 1 cannot occur
    let mut n = 0;
    'outer: loop {
        while let Ok(wake) = rx.recv() {
            if let Wake::Quit = wake { //~ NOTE consumer census: the arm for `Wake::Quit` in `drain` takes it from `main::{closure#0}`
                break 'outer;
            }
            match wake {
                Wake::Set => n += 1, //~ NOTE consumer census: the arm for `Wake::Set` in `drain`
                Wake::Skip => continue, //~ NOTE consumer census: the arm for `Wake::Skip` in `drain`
                Wake::Idle => continue 'outer, //~ NOTE consumer census: the arm for `Wake::Idle` in `drain`
                Wake::Quit => unreachable!(),
                Wake::Take(name) => keep(name), //~ NOTE consumer census: the arm for `Wake::Take` in `drain`
            }
        }
        break;
    }
    n
}

fn nested(rx: &Receiver<Wake>) -> u32 { //~ NOTE consumer census: `nested` drains a channel of `Wake`
    let mut n = 0;
    while let Ok(wake) = rx.recv() {
        match wake {
            Wake::Set => {
                for more in rx.try_iter().take(4) {
                    match more {
                        Wake::Quit => n += 100,
                        _ => n += 1,
                    }
                }
            }
            _ => n += 1000,
        }
    }
    n
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let _sender = std::thread::spawn(move || {
        let _ = tx.send(Wake::Set);
        let _ = tx.send(Wake::Take(String::new()));
        let _ = tx.send(Wake::Quit);
    });
    let _ = drain(&rx) + nested(&rx);
}
