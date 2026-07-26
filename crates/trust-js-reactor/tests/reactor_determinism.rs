// Determinism (M2 D1 validation #3): 100 identical drains of a rich async/timer
// program produce byte-identical order AND byte-identical virtual-clock traces.
// This is the invariant that makes the eventual async ObservableTrace
// byte-reproducible.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod common;
use common::{log_reaction, void, Rt, TestVal};

/// A single rich program touching every observable path: sync logs, microtasks,
/// nested microtasks, promise chains, combinators, timers at several deadlines
/// (each logging the CLOCK it fired at), a nested timer, and an interval that
/// clears itself. The trace therefore encodes both the drain ORDER and the
/// virtual-CLOCK values, so byte-equality proves both are deterministic.
fn run_once() -> Vec<String> {
    let mut rt = Rt::new();

    rt.log("start");

    // promise chain + combinator
    let p = rt.resolved(TestVal::Undefined);
    let p1 = rt.then_log(p, Some("p1"), None);
    rt.then_log(p1, Some("p2"), None);
    let all = rt.all(vec![common::s("x"), common::s("y")]);
    rt.then_log(all, Some("all"), None);

    // nested microtask
    rt.micro_fn(void(|rx, host| {
        host.log.push("m1".into());
        rx.queue_microtask(void(|_rx, host| host.log.push("m2".into())));
    }));

    // timers at distinct deadlines, each recording the clock it fired at
    rt.timer_fn(3, void(|rx, host| host.log.push(format!("t3@{}", rx.now() - common::EPOCH))));
    rt.timer_fn(1, void(|rx, host| {
        host.log.push(format!("t1@{}", rx.now() - common::EPOCH));
        // a promise scheduled from inside a timer
        let q = rx.promise_resolve(host, TestVal::Undefined);
        rx.then(host, q, Some(log_reaction("t1-micro")), None);
    }));
    rt.timer_fn(2, void(|rx, host| {
        host.log.push(format!("t2@{}", rx.now() - common::EPOCH));
        // a nested timer
        rx.set_timeout(void(|rx, host| host.log.push(format!("t2-nested@{}", rx.now() - common::EPOCH))), 5);
    }));

    // an interval that fires twice then is cleared
    let id = rt.interval(4, "iv");
    rt.timer_fn(10, void(move |rx, host| {
        host.log.push(format!("stop@{}", rx.now() - common::EPOCH));
        rx.clear_timer(id);
    }));

    rt.log("end");
    rt.drain().expect("no runaway");
    let mut trace = rt.order();
    trace.push(format!("final-clock@{}", rt.rx.now() - common::EPOCH));
    trace
}

#[test]
fn hundred_drains_are_byte_identical() {
    let reference = run_once();
    // Sanity: the reference trace is non-trivial and captures clock values.
    assert!(reference.len() > 10, "trace should be rich: {reference:?}");
    assert!(reference.iter().any(|m| m.contains('@')), "trace should carry clock values");

    for i in 0..100 {
        let again = run_once();
        assert_eq!(again, reference, "drain #{i} diverged from the reference trace");
    }

    eprintln!(
        "determinism: 100/100 drains byte-identical ({} events); reference trace:\n  {}",
        reference.len(),
        reference.join("\n  ")
    );
}
