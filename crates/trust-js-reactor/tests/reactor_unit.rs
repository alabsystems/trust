// Per-mechanism unit tests: one focused test per reactor mechanism, each
// asserting the exact observable order / state. No Node needed — these pin the
// mechanisms against hand-derived spec expectations.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod common;
use common::{reaction, s, void, Rt, TestVal};
use trust_js_reactor::{Completion, PromiseStatus, Reactor, ReactorError};

fn ord(v: &[&str]) -> Vec<String> {
    v.iter().map(|x| (*x).to_string()).collect()
}

#[test]
fn microtask_before_macrotask() {
    let mut rt = Rt::new();
    rt.log("sync");
    rt.timer(0, "timer");
    rt.micro("micro");
    rt.drain().unwrap();
    // Sync first, then the microtask drains to empty, then the timer.
    assert_eq!(rt.order(), ord(&["sync", "micro", "timer"]));
}

#[test]
fn microtask_fifo() {
    let mut rt = Rt::new();
    rt.micro("a");
    rt.micro("b");
    rt.micro("c");
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["a", "b", "c"]));
}

#[test]
fn nested_microtask_ordering() {
    // A microtask that schedules another microtask: the nested job runs AFTER
    // the already-queued `tail`, since it joins the back of the FIFO.
    let mut rt = Rt::new();
    rt.micro_fn(void(|rx, host| {
        host.log.push("outer".into());
        rx.queue_microtask(void(|_rx, host| host.log.push("inner".into())));
    }));
    rt.micro("tail");
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["outer", "tail", "inner"]));
}

#[test]
fn promise_resolve_then() {
    let mut rt = Rt::new();
    let p = rt.resolved(s("v"));
    assert_eq!(rt.rx.status(p), PromiseStatus::Fulfilled);
    rt.then_val(p);
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["v"]));
}

#[test]
fn promise_reject_catch() {
    let mut rt = Rt::new();
    let p = rt.rejected(s("boom"));
    assert_eq!(rt.rx.status(p), PromiseStatus::Rejected);
    rt.catch_log(p, "caught");
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["caught"]));
}

#[test]
fn already_resolved_guard_resolve_wins() {
    // resolve then reject: the first (resolve) wins; the reject is inert.
    let mut rt = Rt::new();
    let (p, cap) = rt.new_promise();
    rt.resolve(&cap, s("first"));
    rt.reject(&cap, s("second"));
    rt.then_fn(
        p,
        Some(reaction(|_rx, host, v| {
            host.log.push(format!("F:{}", common::val_str(&v)));
            Completion::Normal(v)
        })),
        Some(reaction(|_rx, host, v| {
            host.log.push(format!("R:{}", common::val_str(&v)));
            Completion::Normal(v)
        })),
    );
    rt.drain().unwrap();
    assert_eq!(rt.rx.status(p), PromiseStatus::Fulfilled);
    assert_eq!(rt.order(), ord(&["F:first"]));
}

#[test]
fn already_resolved_guard_double_resolve() {
    let mut rt = Rt::new();
    let (p, cap) = rt.new_promise();
    rt.resolve(&cap, s("first"));
    rt.resolve(&cap, s("second"));
    rt.then_val(p);
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["first"]));
}

#[test]
fn thenable_assimilation_ordering() {
    // Promise.resolve().then(a1).then(a2).then(a3)  vs
    // Promise.resolve(thenable{then(res){res()}}).then(t)
    // The thenable's PromiseResolveThenableJob costs one extra tick, so `t`
    // lands between a2 and a3.
    let mut rt = Rt::new();
    let p = rt.resolved(TestVal::Undefined);
    let p1 = rt.then_log(p, Some("a1"), None);
    let p2 = rt.then_log(p1, Some("a2"), None);
    rt.then_log(p2, Some("a3"), None);

    let th = rt.thenable(|rx, host, res, _rej| {
        rx.resolve(host, &res, TestVal::Undefined);
    });
    let pth = rt.resolved(th);
    rt.then_log(pth, Some("t"), None);

    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["a1", "a2", "t", "a3"]));
}

#[test]
fn then_chain_ordering() {
    let mut rt = Rt::new();
    let p = rt.resolved(TestVal::Undefined);
    let p1 = rt.then_log(p, Some("1"), None);
    let p2 = rt.then_log(p1, Some("2"), None);
    rt.then_log(p2, Some("3"), None);
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["1", "2", "3"]));
}

#[test]
fn independent_chains_interleave() {
    let mut rt = Rt::new();
    let a = rt.resolved(TestVal::Undefined);
    let a1 = rt.then_log(a, Some("a1"), None);
    rt.then_log(a1, Some("a2"), None);
    let b = rt.resolved(TestVal::Undefined);
    let b1 = rt.then_log(b, Some("b1"), None);
    rt.then_log(b1, Some("b2"), None);
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["a1", "b1", "a2", "b2"]));
}

#[test]
fn promise_all_fulfill_order() {
    let mut rt = Rt::new();
    let p = rt.all(vec![s("a"), s("b"), s("c")]);
    rt.then_fn(
        p,
        Some(reaction(|_rx, host, v| {
            if let TestVal::Arr(items) = &v {
                let joined: Vec<String> = items.iter().map(common::val_str).collect();
                host.log.push(joined.join(","));
            }
            Completion::Normal(v)
        })),
        Some(common::log_reaction("err")),
    );
    rt.drain().unwrap();
    // The array preserves INPUT order regardless of settle order.
    assert_eq!(rt.order(), ord(&["a,b,c"]));
}

#[test]
fn promise_all_rejects_on_first() {
    let mut rt = Rt::new();
    let rp = rt.rejected(s("e"));
    let p = rt.all(vec![s("a"), TestVal::Promise(rp)]);
    rt.then_log(p, Some("ok"), Some("err"));
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["err"]));
}

#[test]
fn promise_all_settled_never_rejects() {
    let mut rt = Rt::new();
    let rp = rt.rejected(s("e"));
    let p = rt.all_settled(vec![s("a"), TestVal::Promise(rp)]);
    rt.then_fn(
        p,
        Some(reaction(|_rx, host, v| {
            if let TestVal::Arr(items) = &v {
                let joined: Vec<String> = items.iter().map(common::val_str).collect();
                host.log.push(joined.join(","));
            }
            Completion::Normal(v)
        })),
        Some(common::log_reaction("err")),
    );
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["settled:fulfilled,settled:rejected"]));
}

#[test]
fn promise_race_first_settles() {
    let mut rt = Rt::new();
    let p = rt.race(vec![s("a"), s("b")]);
    rt.then_val(p);
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["a"]));
}

#[test]
fn promise_race_reject_first() {
    let mut rt = Rt::new();
    let rp = rt.rejected(s("e"));
    let p = rt.race(vec![TestVal::Promise(rp), s("b")]);
    rt.catch_log(p, "caught");
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["caught"]));
}

#[test]
fn promise_any_first_fulfill_skips_rejection() {
    let mut rt = Rt::new();
    let rp = rt.rejected(s("e"));
    let p = rt.any(vec![TestVal::Promise(rp), s("b")]);
    rt.then_val(p);
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["b"]));
}

#[test]
fn promise_any_all_reject_aggregates() {
    let mut rt = Rt::new();
    let rp1 = rt.rejected(s("e1"));
    let rp2 = rt.rejected(s("e2"));
    let p = rt.any(vec![TestVal::Promise(rp1), TestVal::Promise(rp2)]);
    rt.then_fn(
        p,
        Some(common::log_reaction("ok")),
        Some(reaction(|_rx, host, v| {
            if let TestVal::Aggregate(errs) = &v {
                let joined: Vec<String> = errs.iter().map(common::val_str).collect();
                host.log.push(format!("agg[{}]", joined.join(",")));
            }
            Completion::Normal(v)
        })),
    );
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["agg[e1,e2]"]));
}

#[test]
fn timer_deadline_seq_tie_break() {
    let mut rt = Rt::new();
    // Same delay: insertion (seq) order breaks the tie.
    rt.timer(5, "first");
    rt.timer(5, "second");
    rt.timer(5, "third");
    // Earlier deadline runs first regardless of insertion order.
    rt.timer(1, "early");
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["early", "first", "second", "third"]));
}

#[test]
fn virtual_clock_advances_on_pop_only() {
    let mut rt = Rt::new();
    assert_eq!(rt.rx.now(), common::EPOCH);
    rt.timer(10, "a");
    rt.timer(25, "b");
    // Arming a timer does not move the clock.
    assert_eq!(rt.rx.now(), common::EPOCH);
    rt.drain().unwrap();
    // After draining, the clock sits at the last-fired deadline.
    assert_eq!(rt.rx.now(), common::EPOCH + 25);
    assert_eq!(rt.order(), ord(&["a", "b"]));
}

#[test]
fn clear_timeout_cancels() {
    let mut rt = Rt::new();
    let id = rt.timer(0, "x");
    let keep = rt.timer(0, "y");
    rt.clear(id);
    let _ = keep;
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["y"]));
}

#[test]
fn budget_trips_on_runaway() {
    // A microtask that re-queues itself forever must trip the budget, not hang.
    let mut rt = Rt::with_budget(1000);
    fn requeue(rx: &mut Reactor<TestVal, common::TestFn>, host: &mut common::TestHost) {
        host.log.push("x".into());
        rx.queue_microtask(void(requeue));
    }
    rt.micro_fn(void(requeue));
    let err = rt.drain().unwrap_err();
    assert_eq!(err, ReactorError::Budget { limit: 1000 });
    // Deterministic trip point: exactly `budget` steps ran.
    assert_eq!(rt.host.log.len(), 1000);
    assert_eq!(rt.rx.steps(), 1001);
}

#[test]
fn interval_reschedules_until_cleared() {
    let mut rt = Rt::new();
    let id = rt.interval(5, "tick");
    // Cancel after 12 virtual ms: fires at 5 and 10, then the 15 firing is cut.
    rt.timer_fn(12, void(move |rx, _host| rx.clear_timer(id)));
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["tick", "tick"]));
    assert_eq!(rt.rx.now(), common::EPOCH + 12);
}

#[test]
fn unhandled_rejection_signal() {
    let mut rt = Rt::new();
    // A rejected promise with no handler: observable as outstanding + signalled.
    let p = rt.rejected(s("boom"));
    rt.drain().unwrap();
    assert_eq!(rt.rx.unhandled_rejections().len(), 1);
    assert_eq!(rt.rx.unhandled_rejections()[0].0, p);
    assert_eq!(rt.host.rejections, ord(&[&format!("reject:{p}:boom")]));
}

#[test]
fn unhandled_rejection_cleared_when_handled() {
    let mut rt = Rt::new();
    let p = rt.rejected(s("boom"));
    // Attaching a handler later flips it to handled (rejectionHandled).
    rt.catch_log(p, "caught");
    rt.drain().unwrap();
    assert!(rt.rx.unhandled_rejections().is_empty());
    assert_eq!(rt.host.rejections, ord(&[&format!("reject:{p}:boom"), &format!("handle:{p}")]));
    assert_eq!(rt.order(), ord(&["caught"]));
}

#[test]
fn self_resolution_rejects_with_type_error() {
    // resolve(p, p) must reject p with a TypeError (chaining cycle).
    let mut rt = Rt::new();
    let (p, cap) = rt.new_promise();
    rt.resolve(&cap, TestVal::Promise(p));
    rt.then_fn(
        p,
        Some(common::log_reaction("ok")),
        Some(reaction(|_rx, host, v| {
            host.log.push(common::val_str(&v));
            Completion::Normal(v)
        })),
    );
    rt.drain().unwrap();
    assert_eq!(rt.rx.status(p), PromiseStatus::Rejected);
    assert_eq!(rt.order(), ord(&["Error(TypeError: Chaining cycle detected for promise)"]));
}

#[test]
fn executor_synchronous_resolve_defers_reaction() {
    // new Promise((res)=>{ log a; res(); }).then(()=>log b); log c;  ->  a,c,b
    let mut rt = Rt::new();
    let (p, cap) = rt.new_promise();
    rt.log("a");
    rt.resolve(&cap, TestVal::Undefined);
    rt.then_log(p, Some("b"), None);
    rt.log("c");
    rt.drain().unwrap();
    assert_eq!(rt.order(), ord(&["a", "c", "b"]));
}
