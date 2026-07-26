// Pure-Rust smoke tests for the intrinsic Array Iterator objects
// (%ArrayIteratorPrototype%): `Array.prototype.values/keys/entries`, the exact
// `{value,done}` next results, the shared %IteratorPrototype% self-return, and
// for-of/spread over the pristine iterator objects. The env-gated corpus
// differential is the byte-for-byte arbiter.
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
fn values_next_exact() {
    assert_eq!(
        stdout_of(
            "var it = [10, 20].values();\n\
             var a = it.next(), b = it.next(), c = it.next();\n\
             console.log([a.value, a.done, b.value, b.done, c.value === undefined, c.done].join(','));"
        ),
        vec![s("10,false,20,false,true,true")]
    );
}

#[test]
fn keys_and_entries() {
    assert_eq!(
        stdout_of(
            "var k = ['a', 'b'].keys();\n\
             console.log([k.next().value, k.next().value, k.next().done].join(','));"
        ),
        vec![s("0,1,true")]
    );
    assert_eq!(
        stdout_of(
            "var e = ['x', 'y'].entries();\n\
             var p = e.next().value;\n\
             console.log([p[0], p[1], e.next().value[1], e.next().done].join(','));"
        ),
        vec![s("0,x,y,true")]
    );
}

#[test]
fn iterator_self_return_and_forof() {
    // The shared %IteratorPrototype%[@@iterator] self-return lets for-of drive
    // an array iterator directly.
    assert_eq!(
        stdout_of(
            "var r = []; for (var x of [1, 2, 3].values()) r.push(x * 10);\n\
             console.log(r.join(','));"
        ),
        vec![s("10,20,30")]
    );
}

#[test]
fn spread_and_entries_forof() {
    assert_eq!(
        stdout_of(
            "var r = []; for (var p of ['a', 'b'].entries()) r.push(p[0] + ':' + p[1]);\n\
             console.log(r.join(','));"
        ),
        vec![s("0:a,1:b")]
    );
}

#[test]
fn next_after_done_stays_done() {
    assert_eq!(
        stdout_of(
            "var it = [1].values(); it.next(); it.next();\n\
             var d = it.next();\n\
             console.log(d.value === undefined, d.done, it.next().done);"
        ),
        vec![
            ProjectedValue::Bool { v: true },
            ProjectedValue::Bool { v: true },
            ProjectedValue::Bool { v: true }
        ]
    );
}

#[test]
fn live_length_shrink() {
    // The iterator reads target.length live: shrinking the array below the
    // cursor ends iteration.
    assert_eq!(
        stdout_of(
            "var a = [1, 2, 3]; var it = a.values(); it.next(); a.length = 1;\n\
             console.log(it.next().done, it.next().done);"
        ),
        vec![
            ProjectedValue::Bool { v: true },
            ProjectedValue::Bool { v: true }
        ]
    );
}

#[test]
fn generic_receiver_via_call() {
    // Array.prototype.values is generic: array-like receivers work.
    assert_eq!(
        stdout_of(
            "var o = { length: 2, 0: 'p', 1: 'q' };\n\
             var it = Array.prototype.values.call(o);\n\
             console.log([it.next().value, it.next().value, it.next().done].join(','));"
        ),
        vec![s("p,q,true")]
    );
    // On a string primitive: ToObject wraps it.
    assert_eq!(
        stdout_of(
            "var it = Array.prototype.values.call('ab');\n\
             console.log([it.next().value, it.next().value, it.next().done].join(','));"
        ),
        vec![s("a,b,true")]
    );
}

#[test]
fn next_wrong_receiver_typeerror() {
    assert_eq!(
        completion(
            "var next = [].values().next; var t = false;\n\
             try { next.call({}); } catch (e) { t = e instanceof TypeError; } t;"
        ),
        Completion::Normal {
            v: Some(ProjectedValue::Bool { v: true })
        }
    );
}

#[test]
fn iterator_object_projects_empty() {
    // An array iterator has no own properties; cls resolves to "Object"
    // through the chain (Node: `[].values()` prints `{}`).
    let SemOutcome::Trace(t) = evaluate_case(&[], "console.log([1, 2].values());") else {
        panic!("expected trace");
    };
    let HostEvent::Stdout { v } = &t.events[0] else {
        panic!("expected stdout");
    };
    let ProjectedValue::Obj { cls, props, .. } = &v[0] else {
        panic!("expected object projection, got {:?}", v[0]);
    };
    assert_eq!(cls.as_deref(), Some("Object"));
    assert_eq!(props.as_ref().expect("props").len(), 0);
}

#[test]
fn self_return_iterator_result_shape() {
    // The `entries` result yields [i, v] arrays with a non-enumerable length.
    assert_eq!(
        stdout_of("console.log([9].entries().next().value.length);"),
        vec![ProjectedValue::Num { v: "2".to_string() }]
    );
}

#[test]
fn toplevel_values_returns_iterator() {
    // The completion value of `.values()` is an iterator object (typeof).
    assert_eq!(
        stdout_of("console.log(typeof [].values().next);"),
        vec![s("function")]
    );
}

#[test]
fn object_tostring_tag_modeled() {
    // @@toStringTag "Array Iterator" (23.1.5.2.1) is modeled: exact tag.
    assert_eq!(
        stdout_of("console.log(Object.prototype.toString.call([].values()));"),
        vec![s("[object Array Iterator]")]
    );
    // And "String Iterator" (22.1.5.2.1).
    assert_eq!(
        stdout_of("console.log(Object.prototype.toString.call('x'[Symbol.iterator]()));"),
        vec![s("[object String Iterator]")]
    );
    // The @@toStringTag is a non-enumerable data property readable off the
    // instance through %ArrayIteratorPrototype%.
    assert_eq!(
        stdout_of("console.log([].values()[Symbol.toStringTag]);"),
        vec![s("Array Iterator")]
    );
}

#[test]
fn string_iterator_next_exact() {
    // Code-point iteration: a surrogate pair is one step (value length 2).
    assert_eq!(
        stdout_of(
            "var it = 'a\\u{1F600}b'[Symbol.iterator]();\n\
             var x = it.next(), y = it.next(), z = it.next(), w = it.next();\n\
             console.log([x.value, x.value.length, y.value.length, z.value, w.value === undefined, w.done].join(','));"
        ),
        vec![s("a,1,2,b,true,true")]
    );
}

#[test]
fn string_iterator_forof_and_spread() {
    // for-of over a String Iterator OBJECT drives it directly.
    assert_eq!(
        stdout_of(
            "var r = []; for (var c of 'a\\u{1F600}b'[Symbol.iterator]()) r.push(c);\n\
             console.log(r.length, r.join('|'));"
        ),
        vec![
            ProjectedValue::Num { v: "3".to_string() },
            s("a|\\ud83d\\ude00|b")
        ]
    );
    // A raw string for-of code-points too (fast path).
    assert_eq!(
        stdout_of("var r = []; for (var c of 'abc') r.push(c); console.log(r.join(','));"),
        vec![s("a,b,c")]
    );
}

#[test]
fn iterator_prototype_self_return() {
    // %IteratorPrototype%[@@iterator] returns the this value; shared by array
    // and string iterators.
    assert_eq!(
        stdout_of(
            "var it = [1].values(); console.log(it[Symbol.iterator]() === it);\n\
             var s = 'x'[Symbol.iterator](); console.log(s[Symbol.iterator]() === s);"
        ),
        vec![
            ProjectedValue::Bool { v: true },
            ProjectedValue::Bool { v: true }
        ]
    );
}

#[test]
fn string_iterator_projects_empty() {
    // A string iterator has no own properties; cls "Object" through the chain.
    let SemOutcome::Trace(t) = evaluate_case(&[], "console.log('ab'[Symbol.iterator]());") else {
        panic!("expected trace");
    };
    let HostEvent::Stdout { v } = &t.events[0] else {
        panic!("expected stdout");
    };
    let ProjectedValue::Obj { cls, props, .. } = &v[0] else {
        panic!("expected object projection, got {:?}", v[0]);
    };
    assert_eq!(cls.as_deref(), Some("Object"));
    assert_eq!(props.as_ref().expect("props").len(), 0);
}
