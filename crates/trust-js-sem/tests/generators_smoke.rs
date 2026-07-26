// Pure-Rust smoke tests for the generator machine (no Node): completion
// values and console output for the core resumable subset. The adversarial +
// corpus differentials (env-gated) are the byte-for-byte arbiter.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use trust_js_sem::{evaluate_case, SemOutcome};
use trust_js_trace::{Completion, HostEvent, ProjectedValue};

fn stdout_of(body: &str) -> Vec<ProjectedValue> {
    match evaluate_case(&[], body) {
        SemOutcome::Trace(t) => {
            let mut out = Vec::new();
            for e in t.events {
                if let HostEvent::Stdout { v } = e {
                    out.extend(v);
                }
            }
            out
        }
        SemOutcome::NoCoverage { reason } => panic!("unexpected NoCoverage: {reason}"),
    }
}

fn refuses(body: &str) -> bool {
    matches!(evaluate_case(&[], body), SemOutcome::NoCoverage { .. })
}

fn completion(body: &str) -> Completion {
    match evaluate_case(&[], body) {
        SemOutcome::Trace(t) => t.completion,
        SemOutcome::NoCoverage { reason } => panic!("unexpected NoCoverage: {reason}"),
    }
}

fn s(v: &str) -> ProjectedValue {
    ProjectedValue::Str { v: v.to_string() }
}

#[test]
fn consecutive_yields_and_done() {
    assert_eq!(
        stdout_of(
            "function* g() { yield 1; yield 2; }\n\
             var it = g();\n\
             var a = it.next(); var b = it.next(); var c = it.next();\n\
             console.log([a.value, a.done, b.value, b.done, c.value, c.done].join(','));"
        ),
        vec![s("1,false,2,false,,true")]
    );
}

#[test]
fn next_value_threading() {
    assert_eq!(
        stdout_of(
            "function* g() { var x = yield 1; var y = yield x + 1; return x + y; }\n\
             var it = g();\n\
             var a = it.next();\n\
             var b = it.next(10);\n\
             var c = it.next(100);\n\
             console.log([a.value, b.value, c.value, c.done].join(','));"
        ),
        // a=1; resume 10 -> x=10, yield 11; resume 100 -> y=100, return 110
        vec![s("1,11,110,true")]
    );
}

#[test]
fn return_completes_with_value() {
    assert_eq!(
        stdout_of(
            "function* g() { yield 1; return 42; yield 2; }\n\
             var it = g();\n\
             var a = it.next(); var b = it.next(); var c = it.next();\n\
             console.log([a.value, a.done, b.value, b.done, c.value, c.done].join(','));"
        ),
        vec![s("1,false,42,true,,true")]
    );
}

#[test]
fn no_yield_generator() {
    assert_eq!(
        stdout_of(
            "function* g(a) {}\n\
             var it = g(3);\n\
             var a = it.next();\n\
             console.log(a.value === undefined, a.done);"
        ),
        vec![
            ProjectedValue::Bool { v: true },
            ProjectedValue::Bool { v: true }
        ]
    );
}

#[test]
fn yield_in_while_loop() {
    assert_eq!(
        stdout_of(
            "function* range(n) { var i = 0; while (i < n) { yield i; i = i + 1; } }\n\
             var r = [];\n\
             var it = range(3);\n\
             var x = it.next();\n\
             while (!x.done) { r.push(x.value); x = it.next(); }\n\
             console.log(r.join(','));"
        ),
        vec![s("0,1,2")]
    );
}

#[test]
fn yield_in_for_loop() {
    assert_eq!(
        stdout_of(
            "function* g() { for (var i = 0; i < 3; i = i + 1) yield i * 10; }\n\
             var it = g();\n\
             console.log([it.next().value, it.next().value, it.next().value, it.next().done].join(','));"
        ),
        vec![s("0,10,20,true")]
    );
}

#[test]
fn generator_return_method_completes() {
    assert_eq!(
        stdout_of(
            "function* g() { yield 1; yield 2; }\n\
             var it = g();\n\
             var a = it.next();\n\
             var b = it.return(99);\n\
             var c = it.next();\n\
             console.log([a.value, b.value, b.done, c.value, c.done].join(','));"
        ),
        vec![s("1,99,true,,true")]
    );
}

#[test]
fn throw_into_generator_caught() {
    assert_eq!(
        stdout_of(
            "function* g() { try { yield 1; } catch (e) { yield e + 10; } yield 3; }\n\
             var it = g();\n\
             var a = it.next();\n\
             var b = it.throw(100);\n\
             var c = it.next();\n\
             console.log([a.value, b.value, c.value].join(','));"
        ),
        vec![s("1,110,3")]
    );
}

#[test]
fn return_runs_finally() {
    assert_eq!(
        stdout_of(
            "var log = [];\n\
             function* g() { try { yield 1; } finally { log.push('fin'); } }\n\
             var it = g();\n\
             it.next();\n\
             var r = it.return(7);\n\
             console.log([log.join(','), r.value, r.done].join('|'));"
        ),
        vec![s("fin|7|true")]
    );
}

#[test]
fn finally_yield_overrides_return() {
    // A `return()` during a yield inside try runs finally; a yield in the
    // finally suspends before the return takes effect.
    assert_eq!(
        stdout_of(
            "function* g() { try { yield 1; } finally { yield 2; } }\n\
             var it = g();\n\
             var a = it.next();\n\
             var b = it.return(5);\n\
             var c = it.next();\n\
             console.log([a.value, b.value, b.done, c.value, c.done].join(','));"
        ),
        // next->1; return(5) enters finally, yields 2 (done:false); next->
        // finally done, the pending return(5) resumes -> {5, done:true}
        vec![s("1,2,false,5,true")]
    );
}

#[test]
fn executing_reentrancy_is_typeerror() {
    assert_eq!(
        completion(
            "var it;\n\
             function* g() { it.next(); }\n\
             it = g();\n\
             var t = false;\n\
             try { it.next(); } catch (e) { t = e instanceof TypeError; }\n\
             t;"
        ),
        Completion::Normal {
            v: Some(ProjectedValue::Bool { v: true })
        }
    );
}

#[test]
fn new_generator_is_typeerror() {
    assert_eq!(
        completion(
            "function* g() {}\n\
             var t = false;\n\
             try { new g(); } catch (e) { t = e instanceof TypeError; }\n\
             t;"
        ),
        Completion::Normal {
            v: Some(ProjectedValue::Bool { v: true })
        }
    );
}

#[test]
fn generator_object_graph_identities() {
    // g().__proto__ === g.prototype; the generator prototype chain and
    // typeof.
    assert_eq!(
        stdout_of(
            "function* g() {}\n\
             var it = g();\n\
             console.log([\n\
               typeof g,\n\
               Object.getPrototypeOf(it) === g.prototype,\n\
               typeof it.next,\n\
               g.prototype.hasOwnProperty('constructor')\n\
             ].join(','));"
        ),
        // g.prototype has no own `constructor` (generator .prototype objects
        // carry none; it is inherited from %GeneratorPrototype%).
        vec![s("function,true,function,false")]
    );
}

#[test]
fn generator_function_intrinsic_chain() {
    // %GeneratorFunction% identity via the prototype chain (27.3).
    assert_eq!(
        stdout_of(
            "function* g() {}\n\
             var GFP = Object.getPrototypeOf(g);\n\
             var GF = GFP.constructor;\n\
             console.log([\n\
               GF.name,\n\
               GFP.prototype === Object.getPrototypeOf(g.prototype),\n\
               Object.getPrototypeOf(GF.prototype) === Function.prototype\n\
             ].join(','));"
        ),
        vec![s("GeneratorFunction,true,true")]
    );
}

#[test]
fn for_of_array_inside_generator() {
    // for-of over an array (a slice iterable) inside a generator body works.
    assert_eq!(
        stdout_of(
            "function* g() { for (var x of [10, 20, 30]) yield x; }\n\
             var it = g();\n\
             console.log([it.next().value, it.next().value, it.next().value, it.next().done].join(','));"
        ),
        vec![s("10,20,30,true")]
    );
}

#[test]
fn yield_star_over_array() {
    assert_eq!(
        stdout_of(
            "function* g() { yield 0; yield* [1, 2, 3]; yield 4; }\n\
             var it = g(); var r = [];\n\
             var x = it.next();\n\
             while (!x.done) { r.push(x.value); x = it.next(); }\n\
             console.log(r.join(','));"
        ),
        vec![s("0,1,2,3,4")]
    );
}

#[test]
fn yield_star_over_generator_threads_values() {
    // yield* forwards next(v) to the inner generator and yields the inner's
    // return value as the yield* expression value.
    assert_eq!(
        stdout_of(
            "function* inner() { var a = yield 1; var b = yield a + 1; return a + b; }\n\
             function* outer() { var total = yield* inner(); yield total; }\n\
             var it = outer();\n\
             var a = it.next();\n\
             var b = it.next(10);\n\
             var c = it.next(100);\n\
             console.log([a.value, b.value, c.value].join(','));"
        ),
        // inner yields 1; resume 10 -> a=10, yield 11; resume 100 -> b=100,
        // return 110; outer's `total`=110, yields 110.
        vec![s("1,11,110")]
    );
}

#[test]
fn yield_star_non_iterable_throws_typeerror() {
    // yield* over a non-iterable object (no @@iterator) throws a TypeError
    // (GetIterator fails) — matching engines, not a refusal.
    assert!(matches!(
        completion(
            "var o = { next: function () { return { done: true }; } };\n\
             function* g() { yield* o; } g().next();"
        ),
        Completion::Throw { .. }
    ));
}

#[test]
fn for_of_non_iterable_throws_typeerror() {
    // `for (x of {})` correctly throws a TypeError (not a refusal): {} has no
    // iterator. The whole case completes with a Throw.
    assert!(matches!(
        completion("function* g() { for (var x of {}) yield x; } g().next();"),
        Completion::Throw { .. }
    ));
}
