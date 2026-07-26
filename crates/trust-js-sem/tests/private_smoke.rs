// Pure-Rust smoke tests for private class elements (§15.7, §6.2.14): private
// fields/methods/getters/setters, static privates, the PrivateEnvironment
// resolution (incl. nested classes), the `#x in obj` brand check, and the
// exact TypeError / SyntaxError web. The env-gated corpus differential is the
// byte-for-byte arbiter.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use trust_js_sem::{evaluate_case, SemOutcome};
use trust_js_trace::{Completion, HostEvent, ProjectedValue, PropKey};

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

/// Is the case an exact SyntaxError trace?
fn is_syntax_error(body: &str) -> bool {
    matches!(
        evaluate_case(&[], body),
        SemOutcome::Trace(t) if matches!(t.completion, Completion::Throw { .. })
    )
}

/// Does the case throw a TypeError (via an `instanceof` probe)?
fn throws_type_error(setup_and_probe: &str) -> bool {
    matches!(
        completion(setup_and_probe),
        Completion::Normal { v: Some(ProjectedValue::Bool { v: true }) }
    )
}

#[test]
fn basic_field_and_method() {
    assert_eq!(
        stdout_of(
            "class C { #x = 5; getX() { return this.#x; } inc() { this.#x++; return this.#x; } }\n\
             var c = new C();\n\
             console.log(c.getX(), c.inc(), c.getX());"
        ),
        vec![
            ProjectedValue::Num { v: "5".to_string() },
            ProjectedValue::Num { v: "6".to_string() },
            ProjectedValue::Num { v: "6".to_string() },
        ]
    );
    assert_eq!(
        stdout_of(
            "class C { #m() { return 42; } call() { return this.#m(); } }\n\
             console.log(new C().call());"
        ),
        vec![ProjectedValue::Num { v: "42".to_string() }]
    );
}

#[test]
fn private_accessor() {
    assert_eq!(
        stdout_of(
            "class C { get #x() { return this._v * 2; } set #x(v) { this._v = v; }\n\
             run() { this.#x = 10; return this.#x; } }\n\
             console.log(new C().run());"
        ),
        vec![ProjectedValue::Num { v: "20".to_string() }]
    );
    // getter-only: set throws; setter-only: get throws.
    assert!(throws_type_error(
        "class C { get #x() { return 1; } run() { try { this.#x = 5; return false; } catch (e) { return e instanceof TypeError; } } }\n\
         new C().run();"
    ));
    assert!(throws_type_error(
        "class C { set #x(v) {} run() { try { return this.#x, false; } catch (e) { return e instanceof TypeError; } } }\n\
         new C().run();"
    ));
}

#[test]
fn brand_checks() {
    assert_eq!(
        stdout_of(
            "class C { #x = 1; static has(o) { return #x in o; } }\n\
             console.log(C.has(new C()), C.has({}), C.has([]));"
        ),
        vec![
            ProjectedValue::Bool { v: true },
            ProjectedValue::Bool { v: false },
            ProjectedValue::Bool { v: false },
        ]
    );
    // brand absent → TypeError on field/method access.
    assert!(throws_type_error(
        "class C { #x = 1; get(o) { try { return o.#x, false; } catch (e) { return e instanceof TypeError; } } }\n\
         new C().get({});"
    ));
    assert!(throws_type_error(
        "class C { #m() {} call(o) { try { return o.#m(), false; } catch (e) { return e instanceof TypeError; } } }\n\
         new C().call({});"
    ));
    // `#x in` on a non-object → TypeError.
    assert!(throws_type_error(
        "class C { #x = 1; static c(o) { return #x in o; } static run() { try { return C.c(5), false; } catch (e) { return false; } } }\n\
         (function () { try { class D { #y; static c() { return #y in 5; } } return D.c(); } catch (e) { return e instanceof TypeError; } })();"
    ));
}

#[test]
fn static_privates() {
    assert_eq!(
        stdout_of(
            "class C { static #x = 7; static #m() { return 'sm'; }\n\
             static get() { return [C.#x, C.#m()]; } }\n\
             var r = C.get(); console.log(r[0], r[1]);"
        ),
        vec![ProjectedValue::Num { v: "7".to_string() }, s("sm")]
    );
}

#[test]
fn nested_class_distinct_brands() {
    // A nested class with the same `#x` name gets a DISTINCT PrivateName, so
    // an outer instance is not branded for the inner.
    assert_eq!(
        stdout_of(
            "class Outer { #x = 'o'; static hasOuter(o) { return #x in o; }\n\
             inner() { class Inner { #x = 'i'; static hasInner(o) { return #x in o; } } return Inner; } }\n\
             var InnerC = new Outer().inner();\n\
             var o = new Outer();\n\
             console.log(Outer.hasOuter(o), InnerC.hasInner(o));"
        ),
        vec![
            ProjectedValue::Bool { v: true },
            ProjectedValue::Bool { v: false },
        ]
    );
    // A nested class can reference an OUTER private name (up the chain).
    assert_eq!(
        stdout_of(
            "class Outer { #x = 1; m() { var self = this; class Inner { get(o) { return #x in o; } } return new Inner().get(self); } }\n\
             console.log(new Outer().m());"
        ),
        vec![ProjectedValue::Bool { v: true }]
    );
}

#[test]
fn forward_reference_and_field_order() {
    // A method may reference a private field declared LATER in the body.
    assert_eq!(
        stdout_of(
            "class C { m() { return this.#x; } #x = 7; }\n\
             console.log(new C().m());"
        ),
        vec![ProjectedValue::Num { v: "7".to_string() }]
    );
    // Private methods are installed before field initializers (a field init
    // can call a private method).
    assert_eq!(
        stdout_of(
            "class C { #m() { return 9; } f = this.#m(); }\n\
             console.log(new C().f);"
        ),
        vec![ProjectedValue::Num { v: "9".to_string() }]
    );
}

#[test]
fn add_field_twice_typeerror() {
    // Re-running a class's field initializer on the same object throws.
    assert!(throws_type_error(
        "class B { constructor(o) { return o; } }\n\
         class C extends B { #x = 1; constructor(o) { super(o); } }\n\
         (function () { var o = {}; new C(o); try { new C(o); return false; } catch (e) { return e instanceof TypeError; } })();"
    ));
}

#[test]
fn private_method_shared_identity() {
    assert_eq!(
        stdout_of(
            "class C { #m() {} get() { return this.#m; } }\n\
             var c1 = new C(), c2 = new C();\n\
             console.log(c1.get() === c2.get());"
        ),
        vec![ProjectedValue::Bool { v: true }]
    );
}

#[test]
fn private_field_name_inference() {
    // NamedEvaluation of an anonymous private field initializer uses "#x".
    assert_eq!(
        stdout_of(
            "class C { #f = function () {}; getName() { return this.#f.name; } }\n\
             console.log(new C().getName());"
        ),
        vec![s("#f")]
    );
}

#[test]
fn private_not_projected() {
    let c = completion("class C { #x = 1; #m() {} y = 2; } new C();");
    let Completion::Normal {
        v: Some(ProjectedValue::Obj { props, .. }),
    } = c
    else {
        panic!("expected object completion");
    };
    let keys: Vec<String> = props
        .expect("props")
        .into_iter()
        .map(|(k, _)| match k {
            PropKey::Str(s) => s,
            PropKey::Sym { .. } => panic!("no symbols"),
        })
        .collect();
    assert_eq!(keys, vec!["y"]);
}

#[test]
fn early_errors() {
    // Undeclared private reference (incl. nested resolution failing).
    assert!(is_syntax_error("class C { m() { return this.#y; } }"));
    assert!(is_syntax_error(
        "class C { #x; m() { class D { n(o) { return o.#y; } } } }"
    ));
    // Duplicate private names (except get/set pairing).
    assert!(is_syntax_error("class C { #x = 1; #x = 2; }"));
    assert!(is_syntax_error("class C { #x = 1; #x() {} }"));
    assert!(is_syntax_error("class C { get #x() {} get #x() {} }"));
    assert!(is_syntax_error("class C { static get #x() {} set #x(v) {} }"));
    // #constructor.
    assert!(is_syntax_error("class C { #constructor() {} }"));
    assert!(is_syntax_error("class C { #constructor = 1; }"));
    // `#x` outside a class body.
    assert!(is_syntax_error("#x;"));
    assert!(is_syntax_error("var y = #x in {};"));
    // The RHS of `#x in` is a ShiftExpression: an arrow there is a SyntaxError.
    assert!(is_syntax_error(
        "class C { #field; constructor() { #field in () => {}; } }"
    ));
    assert!(is_syntax_error(
        "class C { #field; m() { return #field in x => x; } }"
    ));
    // ...but valid `#x in obj` forms parse (a parenthesized arrow RHS is fine).
    assert!(!is_syntax_error(
        "class C { #x = 1; static c(o) { return #x in o; } }"
    ));
    assert!(!is_syntax_error(
        "class C { #x = 1; m(o) { return #x in (o) && true; } }"
    ));
    // delete of a private reference.
    assert!(is_syntax_error("class C { #x = 1; m() { delete this.#x; } }"));
    assert!(is_syntax_error("class C { #x = 1; m() { delete (this.#x); } }"));
    // A get/set private pair with matching static-ness is legal.
    assert!(!is_syntax_error(
        "class C { get #x() { return 1; } set #x(v) {} }"
    ));
    assert!(!is_syntax_error(
        "class C { static get #x() { return 1; } static set #x(v) {} }"
    ));
}

#[test]
fn reserved_and_escaped_private_names() {
    // A PrivateIdentifier's name is an IdentifierName — reserved words allowed.
    assert_eq!(
        stdout_of(
            "class C { #if = 1; #class() { return 2; } run() { return this.#if + this.#class(); } }\n\
             console.log(new C().run());"
        ),
        vec![ProjectedValue::Num { v: "3".to_string() }]
    );
    // \u escapes in a private name.
    assert_eq!(
        stdout_of(
            "class C { #x = 5; get() { return this.#\\u0078; } }\n\
             console.log(new C().get());"
        ),
        vec![ProjectedValue::Num { v: "5".to_string() }]
    );
}

#[test]
fn private_in_template_and_computed_key() {
    // A `#x` reference inside a template substitution resolves in the class.
    assert_eq!(
        stdout_of(
            "class C { #x = 7; m() { return `v=${this.#x}`; } }\n\
             console.log(new C().m());"
        ),
        vec![s("v=7")]
    );
    // `#p in obj` inside a computed key resolves through the (active) class
    // private env (the static #p is not yet added → false → key 'yes').
    assert_eq!(
        stdout_of(
            "class C { static #p = 1; [(#p in {}) ? 'no' : 'yes']() { return 'M'; } }\n\
             console.log(typeof C.prototype.yes);"
        ),
        vec![s("function")]
    );
}

#[test]
fn private_on_primitive_base_typeerror() {
    assert!(throws_type_error(
        "class C { #x = 1; get(o) { try { return o.#x, false; } catch (e) { return e instanceof TypeError; } } }\n\
         new C().get(5);"
    ));
}
