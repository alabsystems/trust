// Non-gated unit tests for async class methods (Task 1) and async generators
// (Task 2, §27.6). These assert the interpreter's OWN outcome (coverage + the
// ordered console trace it computes) without invoking a real engine, so they
// run in a plain `cargo test`. Byte-for-byte equality against Node/Bun is
// covered by the env-gated `faithful_differential` embedded mini-cases.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use trust_js_interp::{evaluate_case, InterpOutcome};
use trust_js_trace::{HostEvent, ProjectedValue};

/// Render one projected value the way `console.log` joins them (enough for the
/// primitive-only assertions below).
fn render(v: &ProjectedValue) -> String {
    match v {
        ProjectedValue::Undefined => "undefined".to_string(),
        ProjectedValue::Null => "null".to_string(),
        ProjectedValue::Bool { v } => v.to_string(),
        ProjectedValue::Num { v } | ProjectedValue::Bigint { v } | ProjectedValue::Str { v } => {
            v.clone()
        }
        other => format!("{other:?}"),
    }
}

/// Run `body` and return the ordered stdout lines (space-joined values), or
/// panic if the case refused / did not produce a trace.
fn stdout_lines(body: &str) -> Vec<String> {
    match evaluate_case(&[], body, false) {
        InterpOutcome::Trace(t) => t
            .events
            .iter()
            .filter_map(|e| match e {
                HostEvent::Stdout { v } => {
                    Some(v.iter().map(render).collect::<Vec<_>>().join(" "))
                }
                _ => None,
            })
            .collect(),
        InterpOutcome::NoCoverage { reason } => panic!("unexpected NoCoverage: {reason}"),
    }
}

/// Assert the case is a sound refusal (NoCoverage), never a fabricated trace.
fn assert_refused(body: &str) {
    match evaluate_case(&[], body, false) {
        InterpOutcome::NoCoverage { .. } => {}
        InterpOutcome::Trace(_) => panic!("expected NoCoverage (sound refusal), got a trace"),
    }
}

#[test]
fn async_class_method_awaits_and_resolves() {
    let lines = stdout_lines(
        "class C { async m(x) { var y = await Promise.resolve(5); return x + y; } }\n\
         new C().m(10).then(v => console.log(v)); console.log('sync');",
    );
    assert_eq!(lines, vec!["sync", "15"]);
}

#[test]
fn async_static_and_private_methods() {
    let lines = stdout_lines(
        "class C {\n\
           static async s(x) { var v = await Promise.resolve(x); return 'S' + v; }\n\
           async #p(x) { var v = await Promise.resolve(x); return 'P' + v; }\n\
           call(x) { return this.#p(x); }\n\
         }\n\
         C.s(1).then(v => console.log(v));\n\
         new C().call(2).then(v => console.log(v));",
    );
    // Both microtask chains are one await deep; C.s resolves first (scheduled
    // first), then the private-method call.
    assert_eq!(lines, vec!["S1", "P2"]);
}

#[test]
fn async_generator_basic_next_ordering() {
    let lines = stdout_lines(
        "async function* g() { yield 1; yield 2; }\n\
         var it = g();\n\
         it.next().then(r => console.log('a', r.value, r.done));\n\
         it.next().then(r => console.log('b', r.value, r.done));\n\
         it.next().then(r => console.log('c', r.value, r.done));\n\
         console.log('sync');",
    );
    assert_eq!(
        lines,
        vec!["sync", "a 1 false", "b 2 false", "c undefined true"]
    );
}

#[test]
fn async_generator_yield_await_operand() {
    let lines = stdout_lines(
        "async function* g() { yield await Promise.resolve(7); yield 8; }\n\
         var it = g();\n\
         it.next().then(r => console.log(r.value, r.done));\n\
         it.next().then(r => console.log(r.value, r.done));",
    );
    assert_eq!(lines, vec!["7 false", "8 false"]);
}

#[test]
fn async_generator_yield_expression_value() {
    // `var a = yield 1` resumes with the .next() argument.
    let lines = stdout_lines(
        "async function* g() { var a = yield 1; var b = yield a + 1; return a + b; }\n\
         var it = g();\n\
         it.next().then(r => console.log('a', r.value, r.done));\n\
         it.next(10).then(r => console.log('b', r.value, r.done));\n\
         it.next(20).then(r => console.log('c', r.value, r.done));",
    );
    assert_eq!(
        lines,
        vec!["a 1 false", "b 11 false", "c 30 true"]
    );
}

#[test]
fn async_generator_await_inside_body() {
    let lines = stdout_lines(
        "async function* g() { var x = await Promise.resolve(10); yield x; }\n\
         g().next().then(r => console.log(r.value, r.done));",
    );
    assert_eq!(lines, vec!["10 false"]);
}

#[test]
fn async_generator_body_throw_rejects() {
    let lines = stdout_lines(
        "async function* g() { yield 1; throw new Error('boom'); }\n\
         var it = g();\n\
         it.next().then(r => console.log('n1', r.value));\n\
         it.next().then(r => console.log('n2'), e => console.log('rej', e.message));\n\
         it.next().then(r => console.log('n3', r.value, r.done));",
    );
    assert_eq!(lines, vec!["n1 1", "rej boom", "n3 undefined true"]);
}

#[test]
fn async_generator_for_loop_body() {
    let lines = stdout_lines(
        "class C { async *nums(n) { for (var i = 0; i < n; i++) yield i * 10; } }\n\
         var it = new C().nums(3);\n\
         it.next().then(r => console.log(r.value));\n\
         it.next().then(r => console.log(r.value));\n\
         it.next().then(r => console.log(r.value));\n\
         it.next().then(r => console.log('done', r.done));",
    );
    assert_eq!(lines, vec!["0", "10", "20", "done true"]);
}

#[test]
fn async_generator_identity_and_prototype_graph() {
    let lines = stdout_lines(
        "async function* g() {}\n\
         var it = g();\n\
         console.log(typeof g, g.constructor.name, typeof it.next,\n\
           it[Symbol.asyncIterator]() === it,\n\
           Object.getPrototypeOf(g).constructor === g.constructor,\n\
           Object.prototype.toString.call(it));",
    );
    assert_eq!(
        lines,
        vec!["function AsyncGeneratorFunction function true true [object AsyncGenerator]"]
    );
}

#[test]
fn async_generator_completed_next_is_done() {
    let lines = stdout_lines(
        "async function* g() { yield 1; }\n\
         var it = g();\n\
         it.next().then(r => console.log('1', r.value, r.done));\n\
         it.next().then(r => console.log('2', r.value, r.done));\n\
         it.next().then(r => console.log('3', r.value, r.done));",
    );
    assert_eq!(
        lines,
        vec!["1 1 false", "2 undefined true", "3 undefined true"]
    );
}

#[test]
fn async_generator_return_awaits_value_ordering() {
    // `return e` in an async generator Awaits e (ReturnStatement, async kind),
    // so the immediate-return `.next()` resolves one tick later than a plain
    // resolved promise's first reaction — `genret` lands after `p1`.
    let lines = stdout_lines(
        "var out = [];\n\
         async function* g() { return 5; }\n\
         g().next().then(r => out.push('genret:' + r.value + ':' + r.done));\n\
         var p = Promise.resolve();\n\
         ['p1','p2','p3'].forEach(n => { p = p.then(() => out.push(n)); });\n\
         p.then(() => console.log(out.join(',')));",
    );
    assert_eq!(lines, vec!["p1,genret:5:true,p2,p3"]);
}

// -- sound refusals (never a fabricated trace) ------------------------------

#[test]
fn async_generator_return_refuses() {
    assert_refused(
        "async function* g() { yield 1; }\n\
         var it = g(); it.next(); it.return(9);",
    );
}

#[test]
fn async_generator_yield_star_refuses() {
    assert_refused(
        "async function* g() { yield* [1, 2]; }\n\
         g().next();",
    );
}

#[test]
fn async_generator_function_ctor_refuses_not_throws() {
    // The %AsyncGeneratorFunction% intrinsic is dynamic-eval-like: calling or
    // constructing it must REFUSE (NoCoverage), never throw a TypeError (which
    // would diverge from engines that build a function).
    assert_refused(
        "var AGF = Object.getPrototypeOf(async function* () {}).constructor;\n\
         new AGF();",
    );
    assert_refused(
        "var AGF = Object.getPrototypeOf(async function* () {}).constructor;\n\
         AGF();",
    );
}

#[test]
fn async_generator_function_instanceof_holds() {
    // Identity/prototype-graph checks that DON'T invoke the constructor stay
    // covered and correct.
    let lines = stdout_lines(
        "var AGF = Object.getPrototypeOf(async function* () {}).constructor;\n\
         async function* ag() {}\n\
         console.log(ag instanceof AGF, ag instanceof Function, AGF.name);",
    );
    assert_eq!(lines, vec!["true true AsyncGeneratorFunction"]);
}

#[test]
fn for_await_of_refuses() {
    assert_refused(
        "async function main() { for await (const x of [1, 2]) console.log(x); }\n\
         main();",
    );
}
