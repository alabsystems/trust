//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Where the held message goes, shape by shape (each has its own message
//! type, so its notes stand alone):
//!
//! - `answer` takes the message and returns a REPLY of the same type: it is
//!   where the message goes, not a filter on its way.
//! - `steps` dispatches on `(&on, &step)`: a tuple built with a reference to
//!   the message is read back through its field.
//! - `jobs` matches on what a local trait's impl method hands back, in a
//!   wrapper that is a type of the crate's own.
//! - `ticks` gives std a closure along with the receiver: std calls it with
//!   each message, so the closure is the consumer; `traced` is a generic
//!   filter, read at the instance called.
//! - `pair` has two parameters of the type: only the one given the held
//!   message is it, and the switch over the other is not counted.
//! - `Solo` has one variant, so there is no switch to find: the body that
//!   holds it is the consumer.
//! - `rest` is handed the message after `cmds` took `Stop`: its arm for
//!   `Stop` takes no message.
//! - `raws` matches on what `map`'s closure makes, which is another value.
//! - `unwrap_hop` returns the message on one path and what a relay carried
//!   on another: it "may rewrite it". `hops` still dispatches what comes
//!   back, as any variant, and `unwrap_hop` is a place the message goes too.

use std::sync::mpsc::{Receiver, channel};

#[derive(Clone, Copy)]
enum Ask {
    Ping,
    Quit,
}

fn answer(ask: Ask) -> Option<Ask> { //~ NOTE consumer census: `answer` receives `Ask` by value from `asks`; its switch gives each of its 2 variants an arm
    match ask {
        Ask::Ping => Some(Ask::Quit),
        Ask::Quit => None,
    }
}

fn asks(rx: Receiver<Ask>) {
    for ask in rx {
        let _reply = answer(ask);
    }
}

enum Step {
    Go,
    Halt,
}

fn steps(rx: Receiver<Step>) { //~ NOTE consumer census: `steps` drains a channel of `Step`; its switch gives each of its 2 variants an arm
    let mut on = false;
    for step in rx {
        match (&on, &step) {
            (false, Step::Go) => on = true,
            (true, Step::Go) => {}
            (_, Step::Halt) => on = false, //~ NOTE consumer census: the arm for `Step::Halt` in `steps` takes it from `main::{closure#0}`
        }
    }
}

enum Job {
    Run,
    Skip,
}

enum Admit {
    Take(Job),
    Drop,
}

trait Gate {
    fn admit(&self, job: Job) -> Admit;
}

struct Open;

impl Gate for Open {
    fn admit(&self, job: Job) -> Admit {
        Admit::Take(job)
    }
}

fn jobs(rx: Receiver<Job>, gate: Open) { //~ NOTE consumer census: `jobs` drains a channel of `Job`, through `<Open as Gate>::admit` (which may drop it); its switch gives each of its 2 variants an arm
    for job in rx {
        match gate.admit(job) {
            Admit::Take(Job::Run) => {}
            Admit::Take(Job::Skip) => {}
            Admit::Drop => {}
        }
    }
}

enum Tick {
    A,
    B,
}

fn traced<T>(v: T) -> T {
    v
}

fn ticks(rx: Receiver<Tick>) {
    rx.into_iter().for_each(|tick| match traced(tick) { //~ NOTE consumer census: `ticks::{closure#0}` receives `Tick` by value from `ticks`, through `traced` (which passes it on); its switch gives each of its 2 variants an arm
        Tick::A => {}
        Tick::B => {}
    });
}

enum Ev {
    On,
    Off,
}

fn pair(held: Ev, fresh: Ev) { //~ NOTE consumer census: `pair` receives `Ev` by value from `evs`; its switch gives 1 of its 2 variants an arm, and 1 share the catch-all (Off) (1 switch(es) over another `Ev` value in this body are not counted). Sent but left to the catch-all: `Ev::Off`
    match fresh {
        Ev::On => {}
        Ev::Off => {}
    }
    match held {
        Ev::On => {}
        _ => {}
    }
}

fn evs(rx: Receiver<Ev>) {
    for ev in rx {
        pair(ev, Ev::On);
    }
}

enum Solo {
    Only(u8),
}

fn solo(rx: Receiver<Solo>) { //~ NOTE consumer census: `solo` drains a channel of `Solo`; its switch gives each of its 1 variants an arm
    for one in rx {
        match one {
            Solo::Only(_n) => {} //~ NOTE consumer census: the arm for `Solo::Only` in `solo` takes it from `main::{closure#0}`
        }
    }
}

enum Cmd {
    Stop,
    Work,
    Idle,
}

fn rest(cmd: Cmd) {
    match cmd {
        Cmd::Stop => {} //~ NOTE consumer census: the arm for `Cmd::Stop` in `rest` takes no message: none reaches it as that variant (an earlier switch takes it)
        Cmd::Work => {} //~ NOTE consumer census: the arm for `Cmd::Work` in `rest` takes it from `main::{closure#0}`
        Cmd::Idle => {}
    }
}

fn cmds(rx: Receiver<Cmd>) { //~ NOTE consumer census: `cmds` drains a channel of `Cmd`; its switch gives 1 of its 3 variants an arm, and 2 share the catch-all (Work, Idle)
    for cmd in rx {
        match cmd {
            Cmd::Stop => break,
            other => rest(other),
        }
    }
}

enum Raw {
    X,
    Y,
}

fn raws(rx: Receiver<Raw>) {
    for raw in rx.iter().map(|_| Raw::X) {
        match raw {
            Raw::X => {}
            Raw::Y => {}
        }
    }
}

enum Hop {
    Go,
    Relay(Box<Hop>),
}

fn unwrap_hop(hop: Hop) -> Hop { //~ NOTE consumer census: `unwrap_hop` receives `Hop` by value from `hops`; its switch gives 1 of its 2 variants an arm
    match hop {
        Hop::Relay(inner) => unwrap_hop(*inner),
        other => other,
    }
}

fn hops(rx: Receiver<Hop>) { //~ NOTE consumer census: `hops` drains a channel of `Hop`, through `unwrap_hop` (which may rewrite it); its switch gives each of its 2 variants an arm
    for hop in rx {
        match unwrap_hop(hop) {
            Hop::Go => {} //~ NOTE consumer census: the arm for `Hop::Go` in `hops` takes it from no enumerated thread over the calls the census resolved, or what `unwrap_hop` makes of another variant
            Hop::Relay(_) => {}
        }
    }
}

fn main() {
    let (ask_tx, ask_rx) = channel::<Ask>();
    let (step_tx, step_rx) = channel::<Step>();
    let (job_tx, job_rx) = channel::<Job>();
    let (tick_tx, tick_rx) = channel::<Tick>();
    let (ev_tx, ev_rx) = channel::<Ev>();
    let (solo_tx, solo_rx) = channel::<Solo>();
    let (cmd_tx, cmd_rx) = channel::<Cmd>();
    let (raw_tx, raw_rx) = channel::<Raw>();
    let (hop_tx, hop_rx) = channel::<Hop>();
    let sender = std::thread::spawn(move || {
        let _ = ask_tx.send(Ask::Ping);
        let _ = step_tx.send(Step::Go);
        let _ = step_tx.send(Step::Halt);
        let _ = job_tx.send(Job::Run);
        let _ = tick_tx.send(Tick::A);
        let _ = ev_tx.send(Ev::Off);
        let _ = solo_tx.send(Solo::Only(1));
        let _ = cmd_tx.send(Cmd::Work);
        let _ = cmd_tx.send(Cmd::Stop);
        let _ = raw_tx.send(Raw::Y);
        let _ = hop_tx.send(Hop::Relay(Box::new(Hop::Go)));
    });
    asks(ask_rx);
    steps(step_rx);
    jobs(job_rx, Open);
    ticks(tick_rx);
    evs(ev_rx);
    solo(solo_rx);
    cmds(cmd_rx);
    raws(raw_rx);
    hops(hop_rx);
    sender.join().unwrap();
}
