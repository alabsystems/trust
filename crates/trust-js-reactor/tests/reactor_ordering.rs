// The ORDERING-ORACLE differential (M2 D1 validation #2).
//
// A battery of >=60 small async/Promise/timer programs, each expressed BOTH as
//   (a) a real JS program (`js`) run through the M0 trace driver on Node, and
//   (b) an equivalent sequence of reactor calls (`build`) whose drain emits the
//       same ordered console.log markers,
// with a hand-derived `golden` marker order (the spec/HTML-mandated order a real
// engine produces).
//
// `reactor_matches_golden` ALWAYS runs (no Node needed): it proves the reactor's
// drain order equals the independently-derived golden order for every program.
// `ordering_oracle_differential` is env-gated on TRUST_JS_NODE: it runs each JS
// program through the real trace driver and asserts reactor == Node == golden,
// closing the loop against a real engine. Disagreements must be 0.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod common;

use common::*;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use trust_js_reactor::Completion;
use trust_js_trace::{extract_trace, HostEvent, ObservableTrace, ProjectedValue};

/// One program in the battery.
struct Program {
    name: &'static str,
    js: &'static str,
    build: fn(&mut Rt),
    golden: &'static [&'static str],
}

fn p(name: &'static str, js: &'static str, build: fn(&mut Rt), golden: &'static [&'static str]) -> Program {
    Program { name, js, build, golden }
}

#[rustfmt::skip]
#[allow(clippy::too_many_lines)]
fn programs() -> Vec<Program> {
    vec![
        // -- A: microtask vs macrotask basics --------------------------------
        p("sync_only",
          "console.log('a');console.log('b');console.log('c');",
          |rt| { rt.log("a"); rt.log("b"); rt.log("c"); },
          &["a", "b", "c"]),
        p("micro_after_sync",
          "console.log('a');queueMicrotask(()=>console.log('m'));console.log('b');",
          |rt| { rt.log("a"); rt.micro("m"); rt.log("b"); },
          &["a", "b", "m"]),
        p("timer_after_micro",
          "console.log('a');setTimeout(()=>console.log('t'),0);queueMicrotask(()=>console.log('m'));console.log('b');",
          |rt| { rt.log("a"); rt.timer(0, "t"); rt.micro("m"); rt.log("b"); },
          &["a", "b", "m", "t"]),
        p("two_micros",
          "queueMicrotask(()=>console.log('m1'));queueMicrotask(()=>console.log('m2'));",
          |rt| { rt.micro("m1"); rt.micro("m2"); },
          &["m1", "m2"]),
        p("micro_and_timer",
          "queueMicrotask(()=>console.log('m'));setTimeout(()=>console.log('t'),0);",
          |rt| { rt.micro("m"); rt.timer(0, "t"); },
          &["m", "t"]),
        p("timer_then_micro",
          "setTimeout(()=>console.log('t'),0);queueMicrotask(()=>console.log('m'));",
          |rt| { rt.timer(0, "t"); rt.micro("m"); },
          &["m", "t"]),
        p("sync_micro_timer_mix",
          "console.log('s1');setTimeout(()=>console.log('t1'),0);queueMicrotask(()=>console.log('m1'));console.log('s2');queueMicrotask(()=>console.log('m2'));setTimeout(()=>console.log('t2'),0);",
          |rt| { rt.log("s1"); rt.timer(0, "t1"); rt.micro("m1"); rt.log("s2"); rt.micro("m2"); rt.timer(0, "t2"); },
          &["s1", "s2", "m1", "m2", "t1", "t2"]),

        // -- B: nested microtasks -------------------------------------------
        p("micro_schedules_micro",
          "queueMicrotask(()=>{console.log('a');queueMicrotask(()=>console.log('b'));});queueMicrotask(()=>console.log('c'));",
          |rt| {
              rt.micro_fn(void(|rx, host| { host.log.push("a".into()); rx.queue_microtask(void(|_rx, host| host.log.push("b".into()))); }));
              rt.micro("c");
          },
          &["a", "c", "b"]),
        p("micro_chain_depth3",
          "queueMicrotask(()=>{console.log('a');queueMicrotask(()=>{console.log('b');queueMicrotask(()=>console.log('c'));});});",
          |rt| {
              rt.micro_fn(void(|rx, host| {
                  host.log.push("a".into());
                  rx.queue_microtask(void(|rx, host| { host.log.push("b".into()); rx.queue_microtask(void(|_rx, host| host.log.push("c".into()))); }));
              }));
          },
          &["a", "b", "c"]),
        p("two_micro_each_schedules",
          "queueMicrotask(()=>{console.log('a1');queueMicrotask(()=>console.log('a2'));});queueMicrotask(()=>{console.log('b1');queueMicrotask(()=>console.log('b2'));});",
          |rt| {
              rt.micro_fn(void(|rx, host| { host.log.push("a1".into()); rx.queue_microtask(void(|_rx, host| host.log.push("a2".into()))); }));
              rt.micro_fn(void(|rx, host| { host.log.push("b1".into()); rx.queue_microtask(void(|_rx, host| host.log.push("b2".into()))); }));
          },
          &["a1", "b1", "a2", "b2"]),

        // -- C: promise chains ----------------------------------------------
        p("resolve_then",
          "Promise.resolve().then(()=>console.log('a'));",
          |rt| { let p = rt.resolved(TestVal::Undefined); rt.then_log(p, Some("a"), None); },
          &["a"]),
        p("then_chain2",
          "Promise.resolve().then(()=>console.log('a')).then(()=>console.log('b'));",
          |rt| { let p = rt.resolved(TestVal::Undefined); let p1 = rt.then_log(p, Some("a"), None); rt.then_log(p1, Some("b"), None); },
          &["a", "b"]),
        p("two_chains_interleave",
          "Promise.resolve().then(()=>console.log('a1')).then(()=>console.log('a2'));Promise.resolve().then(()=>console.log('b1')).then(()=>console.log('b2'));",
          |rt| {
              let a = rt.resolved(TestVal::Undefined); let a1 = rt.then_log(a, Some("a1"), None); rt.then_log(a1, Some("a2"), None);
              let b = rt.resolved(TestVal::Undefined); let b1 = rt.then_log(b, Some("b1"), None); rt.then_log(b1, Some("b2"), None);
          },
          &["a1", "b1", "a2", "b2"]),
        p("then_chain3",
          "Promise.resolve().then(()=>console.log('a')).then(()=>console.log('b')).then(()=>console.log('c'));",
          |rt| { let p = rt.resolved(TestVal::Undefined); let a = rt.then_log(p, Some("a"), None); let b = rt.then_log(a, Some("b"), None); rt.then_log(b, Some("c"), None); },
          &["a", "b", "c"]),
        p("resolve_then_vs_timer",
          "console.log('s');Promise.resolve().then(()=>console.log('a'));setTimeout(()=>console.log('t'),0);",
          |rt| { rt.log("s"); let p = rt.resolved(TestVal::Undefined); rt.then_log(p, Some("a"), None); rt.timer(0, "t"); },
          &["s", "a", "t"]),
        p("deep_chain_vs_timer",
          "Promise.resolve().then(()=>console.log('a1')).then(()=>console.log('a2')).then(()=>console.log('a3'));setTimeout(()=>console.log('t'),0);",
          |rt| {
              let p = rt.resolved(TestVal::Undefined); let a1 = rt.then_log(p, Some("a1"), None); let a2 = rt.then_log(a1, Some("a2"), None); rt.then_log(a2, Some("a3"), None);
              rt.timer(0, "t");
          },
          &["a1", "a2", "a3", "t"]),
        p("two_then_same_promise",
          "const p=Promise.resolve();p.then(()=>console.log('a'));p.then(()=>console.log('b'));",
          |rt| { let p = rt.resolved(TestVal::Undefined); rt.then_log(p, Some("a"), None); rt.then_log(p, Some("b"), None); },
          &["a", "b"]),
        p("sync_promise_body",
          "new Promise((res)=>{console.log('a');res();}).then(()=>console.log('b'));console.log('c');",
          |rt| { let (p, cap) = rt.new_promise(); rt.log("a"); rt.resolve(&cap, TestVal::Undefined); rt.then_log(p, Some("b"), None); rt.log("c"); },
          &["a", "c", "b"]),

        // -- D: timers -------------------------------------------------------
        p("timer_delays_order",
          "setTimeout(()=>console.log('t10'),10);setTimeout(()=>console.log('t5'),5);setTimeout(()=>console.log('t1'),1);",
          |rt| { rt.timer(10, "t10"); rt.timer(5, "t5"); rt.timer(1, "t1"); },
          &["t1", "t5", "t10"]),
        p("timer_tie_break",
          "setTimeout(()=>console.log('first'),5);setTimeout(()=>console.log('second'),5);",
          |rt| { rt.timer(5, "first"); rt.timer(5, "second"); },
          &["first", "second"]),
        p("timer_zero_vs_five",
          "setTimeout(()=>console.log('f'),5);setTimeout(()=>console.log('z'),0);",
          |rt| { rt.timer(5, "f"); rt.timer(0, "z"); },
          &["z", "f"]),
        p("timer_schedules_micro",
          "setTimeout(()=>{console.log('t0');queueMicrotask(()=>console.log('m0'));},0);setTimeout(()=>console.log('t1'),1);",
          |rt| {
              rt.timer_fn(0, void(|rx, host| { host.log.push("t0".into()); rx.queue_microtask(void(|_rx, host| host.log.push("m0".into()))); }));
              rt.timer(1, "t1");
          },
          &["t0", "m0", "t1"]),
        p("nested_timer",
          "setTimeout(()=>{console.log('o');setTimeout(()=>console.log('i'),0);},0);",
          |rt| { rt.timer_fn(0, void(|rx, host| { host.log.push("o".into()); rx.set_timeout(void(|_rx, host| host.log.push("i".into())), 0); })); },
          &["o", "i"]),
        p("timer_order_3_1_2",
          "setTimeout(()=>console.log('d3'),3);setTimeout(()=>console.log('d1'),1);setTimeout(()=>console.log('d2'),2);",
          |rt| { rt.timer(3, "d3"); rt.timer(1, "d1"); rt.timer(2, "d2"); },
          &["d1", "d2", "d3"]),
        p("many_same_delay_fifo",
          "setTimeout(()=>console.log('a'),2);setTimeout(()=>console.log('b'),2);setTimeout(()=>console.log('c'),2);",
          |rt| { rt.timer(2, "a"); rt.timer(2, "b"); rt.timer(2, "c"); },
          &["a", "b", "c"]),
        p("timer_reschedules_distinct",
          "setTimeout(()=>{console.log('a');setTimeout(()=>console.log('b'),3);},2);",
          |rt| { rt.timer_fn(2, void(|rx, host| { host.log.push("a".into()); rx.set_timeout(void(|_rx, host| host.log.push("b".into())), 3); })); },
          &["a", "b"]),
        p("promise_in_timer",
          "setTimeout(()=>{console.log('t');Promise.resolve().then(()=>console.log('p'));},5);",
          |rt| { rt.timer_fn(5, void(|rx, host| { host.log.push("t".into()); let q = rx.promise_resolve(host, TestVal::Undefined); rx.then(host, q, Some(log_reaction("p")), None); })); },
          &["t", "p"]),

        // -- E: clearTimeout -------------------------------------------------
        p("clear_before_fire",
          "var id=setTimeout(()=>console.log('x'),0);clearTimeout(id);console.log('s');",
          |rt| { let id = rt.timer(0, "x"); rt.clear(id); rt.log("s"); },
          &["s"]),
        p("clear_one_of_two",
          "var id1=setTimeout(()=>console.log('a'),0);var id2=setTimeout(()=>console.log('b'),0);clearTimeout(id1);",
          |rt| { let id1 = rt.timer(0, "a"); let _id2 = rt.timer(0, "b"); rt.clear(id1); },
          &["b"]),
        p("clear_later_timer",
          "setTimeout(()=>console.log('a'),0);var id=setTimeout(()=>console.log('b'),5);clearTimeout(id);",
          |rt| { rt.timer(0, "a"); let id = rt.timer(5, "b"); rt.clear(id); },
          &["a"]),
        p("clear_from_micro",
          "var idb=setTimeout(()=>console.log('b'),5);queueMicrotask(()=>clearTimeout(idb));setTimeout(()=>console.log('a'),0);",
          |rt| { let idb = rt.timer(5, "b"); rt.micro_fn(void(move |rx, _host| rx.clear_timer(idb))); rt.timer(0, "a"); },
          &["a"]),
        p("clear_all",
          "var id1=setTimeout(()=>console.log('a'),0);var id2=setTimeout(()=>console.log('b'),1);clearTimeout(id1);clearTimeout(id2);console.log('s');",
          |rt| { let id1 = rt.timer(0, "a"); let id2 = rt.timer(1, "b"); rt.clear(id1); rt.clear(id2); rt.log("s"); },
          &["s"]),

        // -- F: setTimeout(0) vs microtask ----------------------------------
        p("promise_beats_timer0",
          "setTimeout(()=>console.log('t'),0);Promise.resolve().then(()=>console.log('a'));",
          |rt| { rt.timer(0, "t"); let p = rt.resolved(TestVal::Undefined); rt.then_log(p, Some("a"), None); },
          &["a", "t"]),
        p("timer0_schedules_promise",
          "setTimeout(()=>{console.log('t');Promise.resolve().then(()=>console.log('p'));},0);setTimeout(()=>console.log('t1'),1);",
          |rt| {
              rt.timer_fn(0, void(|rx, host| { host.log.push("t".into()); let q = rx.promise_resolve(host, TestVal::Undefined); rx.then(host, q, Some(log_reaction("p")), None); }));
              rt.timer(1, "t1");
          },
          &["t", "p", "t1"]),
        p("interleave_promise_timer_micro",
          "console.log('s');Promise.resolve().then(()=>console.log('p1'));setTimeout(()=>console.log('t1'),0);queueMicrotask(()=>console.log('m1'));",
          |rt| { rt.log("s"); let p = rt.resolved(TestVal::Undefined); rt.then_log(p, Some("p1"), None); rt.timer(0, "t1"); rt.micro("m1"); },
          &["s", "p1", "m1", "t1"]),
        p("micro_and_two_timers_zero",
          "queueMicrotask(()=>console.log('m'));setTimeout(()=>console.log('a'),0);setTimeout(()=>console.log('b'),0);",
          |rt| { rt.micro("m"); rt.timer(0, "a"); rt.timer(0, "b"); },
          &["m", "a", "b"]),

        // -- G: resolve / reject / already-resolved -------------------------
        p("reject_catch",
          "Promise.reject('e').catch(()=>console.log('c'));",
          |rt| { let p = rt.rejected(s("e")); rt.catch_log(p, "c"); },
          &["c"]),
        p("resolve_then_reject_ignored",
          "new Promise((res,rej)=>{res('a');rej('b');}).then(()=>console.log('F'),()=>console.log('R'));",
          |rt| { let (p, cap) = rt.new_promise(); rt.resolve(&cap, s("a")); rt.reject(&cap, s("b")); rt.then_log(p, Some("F"), Some("R")); },
          &["F"]),
        p("reject_then_resolve_ignored",
          "new Promise((res,rej)=>{rej('b');res('a');}).then(()=>console.log('F'),()=>console.log('R'));",
          |rt| { let (p, cap) = rt.new_promise(); rt.reject(&cap, s("b")); rt.resolve(&cap, s("a")); rt.then_log(p, Some("F"), Some("R")); },
          &["R"]),
        p("double_resolve_first_wins",
          "new Promise(res=>{res('first');res('second');}).then(v=>console.log(v));",
          |rt| { let (p, cap) = rt.new_promise(); rt.resolve(&cap, s("first")); rt.resolve(&cap, s("second")); rt.then_val(p); },
          &["first"]),
        p("promise_resolve_value",
          "Promise.resolve('x').then(v=>console.log(v));",
          |rt| { let p = rt.resolved(s("x")); rt.then_val(p); },
          &["x"]),
        p("catch_after_fulfill_skipped",
          "Promise.resolve().then(()=>console.log('a')).catch(()=>console.log('c'));",
          |rt| { let p = rt.resolved(TestVal::Undefined); let p1 = rt.then_log(p, Some("a"), None); rt.catch_log(p1, "c"); },
          &["a"]),

        // -- H: thenable assimilation + adoption ----------------------------
        p("thenable_sync_resolve",
          "Promise.resolve({then(res){res();}}).then(()=>console.log('t'));",
          |rt| { let th = rt.thenable(|rx, host, res, _rej| { rx.resolve(host, &res, TestVal::Undefined); }); let pth = rt.resolved(th); rt.then_log(pth, Some("t"), None); },
          &["t"]),
        p("thenable_ticks_vs_chain",
          "Promise.resolve().then(()=>console.log('a1')).then(()=>console.log('a2')).then(()=>console.log('a3'));Promise.resolve({then(res){res();}}).then(()=>console.log('t'));",
          |rt| {
              let p = rt.resolved(TestVal::Undefined); let a1 = rt.then_log(p, Some("a1"), None); let a2 = rt.then_log(a1, Some("a2"), None); rt.then_log(a2, Some("a3"), None);
              let th = rt.thenable(|rx, host, res, _rej| { rx.resolve(host, &res, TestVal::Undefined); }); let pth = rt.resolved(th); rt.then_log(pth, Some("t"), None);
          },
          &["a1", "a2", "t", "a3"]),
        p("thenable_reject",
          "Promise.resolve({then(res,rej){rej('e');}}).catch(()=>console.log('c'));",
          |rt| { let th = rt.thenable(|rx, host, _res, rej| { rx.reject(host, &rej, s("e")); }); let pth = rt.resolved(th); rt.catch_log(pth, "c"); },
          &["c"]),
        p("handler_returns_value",
          "Promise.resolve().then(()=>{console.log('a');return 5;}).then(()=>console.log('b'));",
          |rt| {
              let p = rt.resolved(TestVal::Undefined);
              let f = reaction(|_rx, host, _arg| { host.log.push("a".into()); Completion::Normal(TestVal::Num(5.0)) });
              let r1 = rt.then_fn(p, Some(f), None);
              rt.then_log(r1, Some("b"), None);
          },
          &["a", "b"]),
        p("handler_returns_thenable",
          "Promise.resolve().then(()=>{console.log('a');return {then(res){res();}};}).then(()=>console.log('b'));",
          |rt| {
              let p = rt.resolved(TestVal::Undefined);
              let f = reaction(|_rx, host, _arg| {
                  host.log.push("a".into());
                  let th = register_thenable(host, |rx, host, res, _rej| { rx.resolve(host, &res, TestVal::Undefined); });
                  Completion::Normal(th)
              });
              let r1 = rt.then_fn(p, Some(f), None);
              rt.then_log(r1, Some("b"), None);
          },
          &["a", "b"]),
        p("nested_resolve_in_handler",
          "Promise.resolve().then(()=>{console.log('a');Promise.resolve().then(()=>console.log('nested'));}).then(()=>console.log('b'));",
          |rt| {
              let p = rt.resolved(TestVal::Undefined);
              let f = reaction(|rx, host, _arg| {
                  host.log.push("a".into());
                  let q = rx.promise_resolve(host, TestVal::Undefined);
                  rx.then(host, q, Some(log_reaction("nested")), None);
                  Completion::Normal(TestVal::Undefined)
              });
              let r1 = rt.then_fn(p, Some(f), None);
              rt.then_log(r1, Some("b"), None);
          },
          &["a", "nested", "b"]),
        p("nested_resolve_in_micro",
          "let res;const p=new Promise(r=>res=r);p.then(()=>console.log('r'));queueMicrotask(()=>{console.log('m');res();});",
          |rt| {
              let (p, cap) = rt.new_promise();
              rt.then_log(p, Some("r"), None);
              rt.micro_fn(void(move |rx, host| { host.log.push("m".into()); rx.resolve(host, &cap, TestVal::Undefined); }));
          },
          &["m", "r"]),

        // -- I: combinators --------------------------------------------------
        p("all_all_fulfill",
          "Promise.all(['a','b']).then(()=>console.log('ok'),()=>console.log('err'));",
          |rt| { let p = rt.all(vec![s("a"), s("b")]); rt.then_log(p, Some("ok"), Some("err")); },
          &["ok"]),
        p("all_one_rejects",
          "Promise.all(['a',Promise.reject('e')]).then(()=>console.log('ok'),()=>console.log('err'));",
          |rt| { let rp = rt.rejected(s("e")); let p = rt.all(vec![s("a"), TestVal::Promise(rp)]); rt.then_log(p, Some("ok"), Some("err")); },
          &["err"]),
        p("all_empty_fulfills",
          "Promise.all([]).then(()=>console.log('empty'));",
          |rt| { let p = rt.all(vec![]); rt.then_log(p, Some("empty"), None); },
          &["empty"]),
        p("all_settled_mixed",
          "Promise.allSettled(['a',Promise.reject('e')]).then(()=>console.log('settled'));",
          |rt| { let rp = rt.rejected(s("e")); let p = rt.all_settled(vec![s("a"), TestVal::Promise(rp)]); rt.then_log(p, Some("settled"), None); },
          &["settled"]),
        p("race_first_fulfill",
          "Promise.race(['a','b']).then(v=>console.log(v));",
          |rt| { let p = rt.race(vec![s("a"), s("b")]); rt.then_val(p); },
          &["a"]),
        p("race_reject_first",
          "Promise.race([Promise.reject('e'),'b']).catch(()=>console.log('c'));",
          |rt| { let rp = rt.rejected(s("e")); let p = rt.race(vec![TestVal::Promise(rp), s("b")]); rt.catch_log(p, "c"); },
          &["c"]),
        p("any_first_fulfill",
          "Promise.any([Promise.reject('e'),'b']).then(v=>console.log(v));",
          |rt| { let rp = rt.rejected(s("e")); let p = rt.any(vec![TestVal::Promise(rp), s("b")]); rt.then_val(p); },
          &["b"]),
        p("any_all_reject",
          "Promise.any([Promise.reject('e1'),Promise.reject('e2')]).catch(()=>console.log('agg'));",
          |rt| { let rp1 = rt.rejected(s("e1")); let rp2 = rt.rejected(s("e2")); let p = rt.any(vec![TestVal::Promise(rp1), TestVal::Promise(rp2)]); rt.catch_log(p, "agg"); },
          &["agg"]),
        p("all_before_timer",
          "Promise.all(['a','b']).then(()=>console.log('all'));setTimeout(()=>console.log('t'),0);",
          |rt| { let p = rt.all(vec![s("a"), s("b")]); rt.then_log(p, Some("all"), None); rt.timer(0, "t"); },
          &["all", "t"]),

        // -- J: async/await shapes ------------------------------------------
        p("await_shape",
          "(async () => { console.log('a'); await null; console.log('b'); await null; console.log('c'); })();console.log('d');",
          |rt| {
              rt.log("a");
              let p = rt.resolved(TestVal::Undefined);
              let k1 = rt.then_log(p, Some("b"), None);
              rt.then_log(k1, Some("c"), None);
              rt.log("d");
          },
          &["a", "d", "b", "c"]),
        p("two_async_interleave",
          "(async()=>{console.log('a1');await 0;console.log('a2');})();(async()=>{console.log('b1');await 0;console.log('b2');})();console.log('s');",
          |rt| {
              rt.log("a1"); let pa = rt.resolved(TestVal::Num(0.0)); rt.then_log(pa, Some("a2"), None);
              rt.log("b1"); let pb = rt.resolved(TestVal::Num(0.0)); rt.then_log(pb, Some("b2"), None);
              rt.log("s");
          },
          &["a1", "b1", "s", "a2", "b2"]),
        p("classic_interleaving",
          "console.log('start');setTimeout(()=>console.log('timeout'),0);Promise.resolve().then(()=>console.log('promise1')).then(()=>console.log('promise2'));console.log('end');",
          |rt| {
              rt.log("start"); rt.timer(0, "timeout");
              let p = rt.resolved(TestVal::Undefined); let p1 = rt.then_log(p, Some("promise1"), None); rt.then_log(p1, Some("promise2"), None);
              rt.log("end");
          },
          &["start", "end", "promise1", "promise2", "timeout"]),
        p("everything_mix",
          "console.log('s');setTimeout(()=>console.log('t'),0);queueMicrotask(()=>console.log('m'));Promise.resolve().then(()=>console.log('p1')).then(()=>console.log('p2'));console.log('e');",
          |rt| {
              rt.log("s"); rt.timer(0, "t"); rt.micro("m");
              let p = rt.resolved(TestVal::Undefined); let p1 = rt.then_log(p, Some("p1"), None); rt.then_log(p1, Some("p2"), None);
              rt.log("e");
          },
          &["s", "e", "m", "p1", "p2", "t"]),

        // -- K: intervals + more --------------------------------------------
        p("interval_cleared",
          "var id=setInterval(()=>console.log('i'),5);setTimeout(()=>clearInterval(id),12);",
          |rt| { let id = rt.interval(5, "i"); rt.timer_fn(12, void(move |rx, _host| rx.clear_timer(id))); },
          &["i", "i"]),
        p("sync_burst",
          "console.log('1');console.log('2');console.log('3');console.log('4');console.log('5');",
          |rt| { rt.log("1"); rt.log("2"); rt.log("3"); rt.log("4"); rt.log("5"); },
          &["1", "2", "3", "4", "5"]),
    ]
}

// ---------------------------------------------------------------------------
// (1) reactor drain order == golden — ALWAYS runs.
// ---------------------------------------------------------------------------

#[test]
fn reactor_matches_golden() {
    let progs = programs();
    assert!(progs.len() >= 60, "battery must have >=60 programs, has {}", progs.len());
    let mut disagree = Vec::new();
    for prog in &progs {
        let mut rt = Rt::new();
        (prog.build)(&mut rt);
        rt.drain().expect("no program in the battery is a runaway");
        let got = rt.order();
        let want: Vec<String> = prog.golden.iter().map(|x| (*x).to_string()).collect();
        if got != want {
            disagree.push(format!("  {}: reactor={got:?} golden={want:?}", prog.name));
        }
    }
    eprintln!(
        "reactor-vs-golden: {} programs / {} agree / {} disagree",
        progs.len(),
        progs.len() - disagree.len(),
        disagree.len()
    );
    assert!(disagree.is_empty(), "reactor/golden disagreements:\n{}", disagree.join("\n"));
}

// ---------------------------------------------------------------------------
// (2) reactor == Node == golden — env-gated on TRUST_JS_NODE.
// ---------------------------------------------------------------------------

struct NodeEnv {
    node: String,
    driver: PathBuf,
    tmp: tempfile::TempDir,
}

fn node_env_or_skip() -> Option<NodeEnv> {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP ordering_oracle_differential: set TRUST_JS_NODE to a node binary to run the differential");
        return None;
    };
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs");
    assert!(driver.is_file(), "driver not found at {}", driver.display());
    Some(NodeEnv { node, driver, tmp: tempfile::tempdir().expect("tempdir") })
}

/// Ordered console.log markers a JS program emits under the real trace driver
/// (one marker per stdout event, its projected string args joined).
fn node_markers(env: &NodeEnv, tag: &str, body: &str) -> Vec<String> {
    let body_path = env.tmp.path().join(format!("{tag}.body.js"));
    std::fs::write(&body_path, body).expect("write body");
    let manifest = serde_json::json!({
        "includes": [],
        "source": body_path.display().to_string(),
        "mode": "bare",
        "kind": "script",
    });
    let manifest_path = env.tmp.path().join(format!("{tag}.manifest.json"));
    let mut mf = std::fs::File::create(&manifest_path).expect("create manifest");
    mf.write_all(manifest.to_string().as_bytes()).expect("write manifest");
    drop(mf);
    let out = Command::new(&env.node)
        .arg(&env.driver)
        .arg(&manifest_path)
        .env("TZ", "UTC")
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .output()
        .expect("spawn node driver");
    let trace = extract_trace(&out.stdout).unwrap_or_else(|e| {
        panic!("trace extraction failed for {tag}: {e} (stderr: {})", String::from_utf8_lossy(&out.stderr))
    });
    markers(&trace)
}

fn markers(trace: &ObservableTrace) -> Vec<String> {
    let mut out = Vec::new();
    for ev in &trace.events {
        if let HostEvent::Stdout { v } = ev {
            let parts: Vec<String> = v.iter().filter_map(pv_str).collect();
            out.push(parts.join(" "));
        }
    }
    out
}

fn pv_str(pv: &ProjectedValue) -> Option<String> {
    match pv {
        ProjectedValue::Str { v } | ProjectedValue::Num { v } => Some(v.clone()),
        ProjectedValue::Bool { v } => Some(v.to_string()),
        ProjectedValue::Undefined => Some("undefined".into()),
        ProjectedValue::Null => Some("null".into()),
        _ => None,
    }
}

#[test]
fn ordering_oracle_differential() {
    let Some(env) = node_env_or_skip() else { return };
    let progs = programs();
    let mut agree = 0usize;
    let mut disagree = Vec::new();
    for prog in &progs {
        let mut rt = Rt::new();
        (prog.build)(&mut rt);
        rt.drain().expect("no program is a runaway");
        let reactor = rt.order();
        let node = node_markers(&env, prog.name, prog.js);
        let golden: Vec<String> = prog.golden.iter().map(|x| (*x).to_string()).collect();
        // The oracle: reactor drain order == Node's observed order (== golden).
        if reactor == node && node == golden {
            agree += 1;
        } else {
            disagree.push(format!("  {}: reactor={reactor:?} node={node:?} golden={golden:?}", prog.name));
        }
    }
    eprintln!("ordering-oracle: {} programs / {agree} agree / {} disagree", progs.len(), disagree.len());
    assert!(disagree.is_empty(), "ordering disagreements:\n{}", disagree.join("\n"));
}
