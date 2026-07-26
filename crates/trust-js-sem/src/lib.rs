// trust-js-sem: the independent ECMA-262 reference semantics (S0 surface).
//
// The third oracle head: an interpreter for the S0 slice of JavaScript,
// written from the spec (never translated from an engine), that evaluates the
// harness includes and the test body and emits the same ObservableTrace the
// in-JS trace driver emits on Node/Bun. The modeled surface includes the
// full property-descriptor machinery (accessors, ValidateAndApply,
// ArraySetLength, freeze/seal), delete/in/void, for-in (spec visited/shadow
// discipline) and for-of over intrinsic iterables, the arguments exotic
// (mapped + unmapped), call/apply/bind with bound functions, the
// String/Number/Boolean wrapper exotics, Math's exactly-determined subset,
// template literals, and the Array/String prototype method sets. Anything
// outside the implemented slice — at parse OR eval time — or anything the
// spec leaves to engine latitude is a sound `NoCoverage`, never a wrong
// trace and never a guessed SyntaxError. See Cargo.toml for the charter.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod ast;
mod bigint;
mod builtins;
mod class;
mod collection;
mod date;
mod expr;
mod generator;
mod interp;
mod lexer;
mod number;
mod parser;
mod pattern;
mod project;
mod promise;
mod props;
mod proxy;
mod regexp;
mod symbol;
mod typedarray;
mod unicode_id;
mod value;

pub use number::js_number_to_string;
pub use project::escape_units;

use interp::{Abrupt, Interp};
use parser::ParseFail;
use trust_js_trace::{
    Completion, ObservableTrace, ProjectionCaps, ThrownProjection, SCHEMA_VERSION,
};

/// The thrown projection a conforming engine produces for a parse-time
/// SyntaxError (constructor identity and `.name` only — never message text).
fn syntax_error_thrown() -> ThrownProjection {
    ThrownProjection::Error {
        ctor: Some("Error:SyntaxError".to_string()),
        name: Some("SyntaxError".to_string()),
        ctor_name: Some("SyntaxError".to_string()),
    }
}

/// The thrown projection of a TypeError. The frozen driver projects any bigint
/// via `Number.prototype.toString.apply(v, [])`, which throws TypeError — so a
/// completion whose witness / thrown value would deep-print a bigint is
/// actually a TypeError throw.
fn type_error_thrown() -> ThrownProjection {
    ThrownProjection::Error {
        ctor: Some("Error:TypeError".to_string()),
        name: Some("TypeError".to_string()),
        ctor_name: Some("TypeError".to_string()),
    }
}

/// The driver-error trace the frozen driver emits when its own `projectThrown`
/// throws (a thrown PRIMITIVE bigint: `projectThrown` deep-prints it, hits the
/// `Number.prototype.toString` TypeError, and the exception escapes `main` into
/// the outer rejection handler). That path emits `{schema, events:[],
/// completion:{k:"driver-error", ...}}` — NO caps, and the accumulated events
/// are discarded — so this trace is caps-less with empty events.
fn driver_error_outcome() -> SemOutcome {
    SemOutcome::Trace(ObservableTrace {
        schema: SCHEMA_VERSION.to_string(),
        caps: None,
        events: Vec::new(),
        completion: Completion::DriverError {
            v: type_error_thrown(),
        },
    })
}

/// The head verdict for one case: a trace, or a sound refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemOutcome {
    Trace(ObservableTrace),
    /// The case uses syntax or semantics outside the implemented bootstrap
    /// slice. Sound: never a false divergence, and counted (audited) by the
    /// harness — never a silent pass.
    NoCoverage { reason: String },
}

/// The projection caps the driver declares; ours are identical by
/// construction.
#[must_use]
pub fn projection_caps() -> ProjectionCaps {
    ProjectionCaps {
        depth: 8,
        keys: 64,
        nodes: 4096,
        string: 4096,
        timers: 10_000,
    }
}

/// Evaluate one assembled case under the independent semantics.
///
/// `includes` are the SOURCE TEXTS of the harness includes (assert.js,
/// sta.js, ...) in driver order; they evaluate non-strict in the shared
/// realm, exactly like the driver's indirect eval. `body` is the test body,
/// with `"use strict";\n` already prepended by the caller for strict-mode
/// runs (the strictness is read from the directive prologue).
#[must_use]
pub fn evaluate_case(includes: &[&str], body: &str) -> SemOutcome {
    evaluate_case_opts(includes, body, true)
}

/// Like [`evaluate_case`], with the completion witness explicit. The
/// calibration harness passes `false` to mirror the driver's default
/// (completion values are an opt-in observable — see trust-js-trace).
#[must_use]
pub fn evaluate_case_opts(includes: &[&str], body: &str, completion_witness: bool) -> SemOutcome {
    let mut it = Interp::new();

    for (i, src) in includes.iter().enumerate() {
        let prog = match parser::parse_program(src) {
            Ok(p) => p,
            Err(ParseFail::EarlySyntaxError(_)) => {
                // The driver evaluates includes via indirect eval: a parse
                // SyntaxError there is a harness-include error observable.
                return SemOutcome::Trace(ObservableTrace {
                    schema: SCHEMA_VERSION.to_string(),
                    caps: Some(projection_caps()),
                    events: it.events,
                    completion: Completion::HarnessIncludeError {
                        v: syntax_error_thrown(),
                    },
                });
            }
            Err(e) => {
                return SemOutcome::NoCoverage {
                    reason: format!("include[{i}] parse: {e}"),
                }
            }
        };
        match it.run_script(&prog) {
            Ok(_) => {}
            Err(Abrupt::Throw(v)) => {
                let thrown = match project::project_thrown(&it, &v) {
                    Ok(t) => t,
                    // The driver's projectThrown of a primitive bigint throws
                    // TypeError, escaping the include-error emit into a
                    // driver-error (caps-less, events discarded).
                    Err(project::ProjErr::BigIntTypeError) => return driver_error_outcome(),
                    Err(project::ProjErr::NoCoverage(e)) => {
                        return SemOutcome::NoCoverage {
                            reason: format!("include[{i}] thrown projection: {e}"),
                        }
                    }
                };
                return SemOutcome::Trace(ObservableTrace {
                    schema: SCHEMA_VERSION.to_string(),
                    caps: Some(projection_caps()),
                    events: it.events,
                    completion: Completion::HarnessIncludeError { v: thrown },
                });
            }
            Err(Abrupt::Fatal(e)) => {
                return SemOutcome::NoCoverage {
                    reason: format!("include[{i}]: {e}"),
                }
            }
            Err(other) => {
                return SemOutcome::NoCoverage {
                    reason: format!("include[{i}]: abrupt completion escaped script: {other:?}"),
                }
            }
        }
    }

    let prog = match parser::parse_program(body) {
        Ok(p) => p,
        Err(ParseFail::EarlySyntaxError(_)) => {
            // A fully-specified early error: the engines raise SyntaxError
            // while parsing the body, before evaluating any of it. Exact
            // observable — same trace shape as the driver's body-throw path.
            return SemOutcome::Trace(ObservableTrace {
                schema: SCHEMA_VERSION.to_string(),
                caps: Some(projection_caps()),
                events: it.events,
                completion: Completion::Throw {
                    v: syntax_error_thrown(),
                    phase: None,
                },
            });
        }
        Err(e) => {
            return SemOutcome::NoCoverage {
                reason: format!("body parse: {e}"),
            }
        }
    };
    let completion = match it.run_script(&prog) {
        Ok(v) => {
            // The script body completed synchronously; now drain the job model
            // exactly as the driver does — microtasks to empty, then the
            // earliest-deadline-then-insertion virtual timer, repeat — so
            // microtask-before-macrotask ordering (and every host effect a
            // Promise reaction / timer emits) lands in the trace before the
            // completion. A drain fault out of slice refuses the whole case.
            let timer_thrown = match it.drain_jobs() {
                Ok(t) => t,
                Err(Abrupt::Fatal(e)) => return SemOutcome::NoCoverage { reason: e },
                Err(other) => {
                    return SemOutcome::NoCoverage {
                        reason: format!("job drain escaped abruptly: {other:?}"),
                    }
                }
            };
            if let Some(thrown) = timer_thrown {
                // A virtual-timer callback threw: completion phase "timer".
                match project::project_thrown(&it, &thrown) {
                    Ok(t) => Completion::Throw {
                        v: t,
                        phase: Some("timer".to_string()),
                    },
                    Err(project::ProjErr::BigIntTypeError) => return driver_error_outcome(),
                    Err(project::ProjErr::NoCoverage(e)) => {
                        return SemOutcome::NoCoverage {
                            reason: format!("timer thrown projection: {e}"),
                        }
                    }
                }
            } else if completion_witness {
                // The driver projects the body's completion value AFTER draining.
                match project::project(&it, &v) {
                    Ok(pv) => Completion::Normal { v: Some(pv) },
                    // Projecting a bigint completion value throws TypeError under
                    // the driver — the completion becomes a throw.
                    Err(project::ProjErr::BigIntTypeError) => Completion::Throw {
                        v: type_error_thrown(),
                        phase: None,
                    },
                    Err(project::ProjErr::NoCoverage(e)) => {
                        return SemOutcome::NoCoverage {
                            reason: format!("completion projection: {e}"),
                        }
                    }
                }
            } else {
                // Mirror the driver: witness off means the value is neither
                // projected nor allowed to refuse the case.
                Completion::Normal { v: None }
            }
        }
        Err(Abrupt::Throw(v)) => match project::project_thrown(&it, &v) {
            Ok(t) => Completion::Throw {
                v: t,
                phase: None,
            },
            // The driver's projectThrown of a primitive bigint throws TypeError,
            // escaping main into a driver-error (caps-less, events discarded).
            Err(project::ProjErr::BigIntTypeError) => return driver_error_outcome(),
            Err(project::ProjErr::NoCoverage(e)) => {
                return SemOutcome::NoCoverage {
                    reason: format!("thrown projection: {e}"),
                }
            }
        },
        Err(Abrupt::Fatal(e)) => return SemOutcome::NoCoverage { reason: e },
        Err(other) => {
            return SemOutcome::NoCoverage {
                reason: format!("abrupt completion escaped script: {other:?}"),
            }
        }
    };
    SemOutcome::Trace(ObservableTrace {
        schema: SCHEMA_VERSION.to_string(),
        caps: Some(projection_caps()),
        events: it.events,
        completion,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_js_trace::{HostEvent, ProjectedValue, PropKey, ThrownProjection};

    fn run(body: &str) -> SemOutcome {
        evaluate_case(&[], body)
    }

    fn completion_of(o: SemOutcome) -> Completion {
        match o {
            SemOutcome::Trace(t) => t.completion,
            SemOutcome::NoCoverage { reason } => panic!("unexpected NoCoverage: {reason}"),
        }
    }

    #[test]
    fn zero_arg_date_setters_yield_nan_never_panic() {
        // Totality: a Date setter called with no args coerces its first field
        // from `undefined` -> NaN (Invalid Date), per ECMA-262 — it must never
        // index an empty arg vec and panic (this crashed a full calibration
        // worker before the fix).
        for body in [
            "var d = new Date(0); d.setHours(); d.getTime();",
            "var d = new Date(0); d.setDate(); d.getTime();",
            "var d = new Date(0); d.setFullYear(); d.getTime();",
            "var d = new Date(0); d.setMinutes(); d.getTime();",
            "var d = new Date(0); d.setSeconds(); d.getTime();",
            "var d = new Date(0); d.setMilliseconds(); d.getTime();",
            "var d = new Date(0); d.setMonth(); d.getTime();",
        ] {
            assert_eq!(
                completion_of(run(body)),
                Completion::Normal {
                    v: Some(ProjectedValue::Num { v: "NaN".to_string() })
                },
                "body: {body}"
            );
        }
    }

    fn num(s: &str) -> ProjectedValue {
        ProjectedValue::Num { v: s.to_string() }
    }

    #[test]
    fn literal_completion_values() {
        assert_eq!(
            completion_of(run("1 + 2;")),
            Completion::Normal { v: Some(num("3")) }
        );
        assert_eq!(
            completion_of(run("var x = 5;")),
            Completion::Normal {
                v: Some(ProjectedValue::Undefined)
            }
        );
        // Declarations leave the previous statement value in place.
        assert_eq!(
            completion_of(run("42; var y;")),
            Completion::Normal { v: Some(num("42")) }
        );
        // if yields undefined when its branch is empty.
        assert_eq!(
            completion_of(run("1; if (true) {}")),
            Completion::Normal {
                v: Some(ProjectedValue::Undefined)
            }
        );
        // while accumulates body values; break carries them out.
        assert_eq!(
            completion_of(run("while (true) { 5; break; }")),
            Completion::Normal { v: Some(num("5")) }
        );
    }

    #[test]
    fn negative_zero_projection() {
        assert_eq!(
            completion_of(run("-0;")),
            Completion::Normal { v: Some(num("-0")) }
        );
        // ...but String coercion of -0 is "0".
        assert_eq!(
            completion_of(run("String(-0);")),
            Completion::Normal {
                v: Some(ProjectedValue::Str { v: "0".to_string() })
            }
        );
        assert_eq!(
            completion_of(run("NaN;")),
            Completion::Normal { v: Some(num("NaN")) }
        );
        assert_eq!(
            completion_of(run("1e21;")),
            Completion::Normal { v: Some(num("1e+21")) }
        );
    }

    #[test]
    fn thrown_primitive_and_error() {
        assert_eq!(
            completion_of(run("throw 42;")),
            Completion::Throw {
                v: ThrownProjection::Prim { v: num("42") },
                phase: None
            }
        );
        assert_eq!(
            completion_of(run("throw new TypeError('boom');")),
            Completion::Throw {
                v: ThrownProjection::Error {
                    ctor: Some("Error:TypeError".to_string()),
                    name: Some("TypeError".to_string()),
                    ctor_name: Some("TypeError".to_string()),
                },
                phase: None
            }
        );
    }

    #[test]
    fn console_log_events() {
        let SemOutcome::Trace(t) = run("console.log(1, 'a'); console.error(true);") else {
            panic!("expected trace");
        };
        assert_eq!(
            t.events,
            vec![
                HostEvent::Stdout {
                    v: vec![
                        num("1"),
                        ProjectedValue::Str { v: "a".to_string() }
                    ]
                },
                HostEvent::Stderr {
                    v: vec![ProjectedValue::Bool { v: true }]
                },
            ]
        );
    }

    #[test]
    fn object_property_order_and_nonenum() {
        // Integer keys ascend before insertion-ordered string keys; array
        // length appears as a non-enumerable trailer.
        let c = completion_of(run("[7, 8];"));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { cls, props, .. }),
        } = c
        else {
            panic!("expected object completion");
        };
        assert_eq!(cls.as_deref(), Some("Array"));
        let props = props.expect("props");
        assert_eq!(
            props,
            vec![
                (PropKey::Str("0".to_string()), num("7")),
                (PropKey::Str("1".to_string()), num("8")),
                (
                    PropKey::Str("length".to_string()),
                    ProjectedValue::Nonenum {
                        v: Box::new(num("2"))
                    }
                ),
            ]
        );

        let c = completion_of(run("var o = { b: 1, 2: 'two', a: 3, 0: 'zero' }; o;"));
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
                PropKey::Sym { .. } => panic!("no symbols in slice"),
            })
            .collect();
        assert_eq!(keys, vec!["0", "2", "b", "a"]);
    }

    #[test]
    fn cyclic_object_projects_circ() {
        let c = completion_of(run("var o = {}; o.self = o; o;"));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { id, props, .. }),
        } = c
        else {
            panic!("expected object completion");
        };
        assert_eq!(id, 0);
        assert_eq!(
            props.expect("props"),
            vec![(
                PropKey::Str("self".to_string()),
                ProjectedValue::Circ { target: 0 }
            )]
        );
    }

    #[test]
    fn unresolved_identifier_is_no_coverage_not_reference_error() {
        let SemOutcome::NoCoverage { reason } = run("someUnknownGlobal;") else {
            panic!("expected NoCoverage");
        };
        assert!(reason.contains("unresolved identifier"), "{reason}");
        // A regex literal now parses and evaluates to a RegExp object.
        assert!(matches!(run("var x = /re/g; x.source;"), SemOutcome::Trace(_)));
        // An unsupported (Annex-B) regex construct is a sound NoCoverage, never
        // a guessed SyntaxError.
        assert!(matches!(run("var x = /a{/;"), SemOutcome::NoCoverage { .. }));
        // Other out-of-slice parse failures are NoCoverage too.
        assert!(matches!(run("x ??= 1;"), SemOutcome::NoCoverage { .. }));
    }

    #[test]
    fn functions_closures_try_catch() {
        assert_eq!(
            completion_of(run(
                "function add(a, b) { return a + b; } add(2, 40);"
            )),
            Completion::Normal { v: Some(num("42")) }
        );
        assert_eq!(
            completion_of(run(
                "function mk(n) { return function (m) { return n * m; }; } mk(6)(7);"
            )),
            Completion::Normal { v: Some(num("42")) }
        );
        assert_eq!(
            completion_of(run(
                "var r; try { throw 'x'; } catch (e) { r = e + '!'; } r;"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Str { v: "x!".to_string() })
            }
        );
    }

    #[test]
    fn sta_and_assert_evaluate_and_fire() {
        // A minimal inline sta.js core: the real files are exercised by the
        // env-gated differential test; this pins the in-slice machinery.
        let sta = "function Test262Error(message) {\n\
                   if (!(this instanceof Test262Error)) return new Test262Error(message);\n\
                   this.message = message || \"\";\n\
                   }\n\
                   Test262Error.prototype.toString = function () {\n\
                   return \"Test262Error: \" + this.message;\n\
                   };";
        let out = evaluate_case(&[sta], "throw new Test262Error('nope');");
        assert_eq!(
            completion_of(out),
            Completion::Throw {
                v: ThrownProjection::Error {
                    ctor: Some("Object".to_string()),
                    name: None,
                    ctor_name: Some("Test262Error".to_string()),
                },
                phase: None
            }
        );
    }

    #[test]
    fn intrinsic_gap_masking_refuses() {
        // An unmodeled intrinsic own property must refuse AT ITS HOP on the
        // prototype chain — never fall through to a modeled property further
        // up (Object.prototype.toLocaleString, Object.prototype.toString...)
        // and answer with the wrong engine's value.
        let SemOutcome::NoCoverage { reason } = run("[1].toLocaleString();") else {
            panic!("expected NoCoverage for Array.prototype.toLocaleString");
        };
        assert!(reason.contains("toLocaleString"), "{reason}");
        // Function.prototype.toString is unmodeled: reading it — directly or
        // via string coercion of a function — refuses instead of returning
        // "[object Function]" where a real engine prints source text.
        assert!(matches!(
            run("function f() {} f.toString;"),
            SemOutcome::NoCoverage { .. }
        ));
        assert!(matches!(
            run("String(function () {});"),
            SemOutcome::NoCoverage { .. }
        ));
        // Host constructors still carry UNMODELED own statics (e.g.
        // parseInt on Number): own-surface misses refuse...
        assert!(matches!(
            run("Number.parseInt;"),
            SemOutcome::NoCoverage { .. }
        ));
        // ...while the modeled `prototype` slots are exact: non-writable, so
        // a sloppy write is a silent no-op.
        assert_eq!(
            completion_of(run(
                "Number.prototype = 1; Boolean.hasOwnProperty('prototype');"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
        // Object.prototype.toString reads the spec-pinned @@toStringTag data
        // property "JSON" (25.5.3) — exact "[object JSON]", never a guessed
        // "[object Object]". The global object's @@toStringTag IS engine-
        // specific ("[object global]"/"[object Object]"), so it still refuses.
        assert_eq!(
            completion_of(run("Object.prototype.toString.call(JSON);")),
            Completion::Normal {
                v: Some(ProjectedValue::Str { v: "[object JSON]".to_string() })
            }
        );
        assert!(matches!(
            run("Object.prototype.toString.call(globalThis);"),
            SemOutcome::NoCoverage { .. }
        ));
    }

    #[test]
    fn own_property_observation_exact_where_modeled() {
        let SemOutcome::Trace(t) = run(
            "var o = { a: 1 };\n\
             console.log(o.hasOwnProperty('a'), o.hasOwnProperty('b'),\n\
             [7].hasOwnProperty('0'), [7].hasOwnProperty('1'),\n\
             o.propertyIsEnumerable('a'), [7].propertyIsEnumerable('length'));",
        ) else {
            panic!("expected trace");
        };
        assert_eq!(
            t.events,
            vec![HostEvent::Stdout {
                v: vec![
                    ProjectedValue::Bool { v: true },
                    ProjectedValue::Bool { v: false },
                    ProjectedValue::Bool { v: true },
                    ProjectedValue::Bool { v: false },
                    ProjectedValue::Bool { v: true },
                    ProjectedValue::Bool { v: false },
                ]
            }]
        );
    }

    #[test]
    fn index_of_checks_length_before_from_index() {
        // Spec step 3: len == 0 returns -1 BEFORE ToIntegerOrInfinity
        // (fromIndex) — its valueOf must never run on an empty array.
        assert_eq!(
            completion_of(run(
                "var p = { valueOf: function () { throw 'poison'; } };\n\
                 [].indexOf(2, p);"
            )),
            Completion::Normal { v: Some(num("-1")) }
        );
        // Non-empty receivers DO coerce fromIndex (after the length read).
        assert_eq!(
            completion_of(run(
                "[5, 6, 5].indexOf(5, { valueOf: function () { return 1; } });"
            )),
            Completion::Normal { v: Some(num("2")) }
        );
    }

    #[test]
    fn array_species_create_per_spec() {
        // Primitive non-undefined constructor → TypeError (step 9), callback
        // never invoked.
        assert_eq!(
            completion_of(run(
                "var a = []; var n = 0; var t = false;\n\
                 a.constructor = null;\n\
                 try { a.map(function () { n++; }); } catch (e) { t = e instanceof TypeError; }\n\
                 t && n === 0;"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
        // Undefined constructor → ArrayCreate (step 7).
        let c = completion_of(run("var a = [1, 2]; a.constructor = undefined; a.slice(1);"));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { cls, props, .. }),
        } = c
        else {
            panic!("expected array completion");
        };
        assert_eq!(cls.as_deref(), Some("Array"));
        assert_eq!(
            props.expect("props"),
            vec![
                (PropKey::Str("0".to_string()), num("2")),
                (
                    PropKey::Str("length".to_string()),
                    ProjectedValue::Nonenum {
                        v: Box::new(num("1"))
                    }
                ),
            ]
        );
        // forEach has no ArraySpeciesCreate: a poisoned constructor is fine.
        assert_eq!(
            completion_of(run(
                "var a = [1]; a.constructor = null; var n = 0;\n\
                 a.forEach(function () { n++; }); n;"
            )),
            Completion::Normal { v: Some(num("1")) }
        );
        // A non-default constructor OBJECT needs the @@species lookup: refuse.
        assert!(matches!(
            run("var a = []; function C() {} a.constructor = C; a.slice();"),
            SemOutcome::NoCoverage { .. }
        ));
    }

    #[test]
    fn array_methods_consult_prototype_elements() {
        let SemOutcome::Trace(t) = run(
            "Array.prototype[1] = 9; var x = [0]; x.length = 2;\n\
             var s = x.slice();\n\
             console.log(s.hasOwnProperty('1'), s[1], x.indexOf(9), x.pop(), x.length);",
        ) else {
            panic!("expected trace");
        };
        assert_eq!(
            t.events,
            vec![HostEvent::Stdout {
                v: vec![
                    ProjectedValue::Bool { v: true },
                    num("9"),
                    num("1"),
                    num("9"),
                    num("1"),
                ]
            }]
        );
    }

    #[test]
    fn push_at_uint32_length_boundary() {
        // len 2^32-1 + one item: the element set lands as a PLAIN key (not an
        // array index), then ArraySetLength throws RangeError — in that
        // order, per spec steps 5-6.
        let SemOutcome::Trace(t) = run(
            "var x = []; x.length = 4294967295; var r = x.push();\n\
             var t = false;\n\
             try { x.push('y'); } catch (e) { t = e instanceof RangeError; }\n\
             console.log(r, t, x[4294967295], x.length);",
        ) else {
            panic!("expected trace");
        };
        assert_eq!(
            t.events,
            vec![HostEvent::Stdout {
                v: vec![
                    num("4294967295"),
                    ProjectedValue::Bool { v: true },
                    ProjectedValue::Str { v: "y".to_string() },
                    num("4294967295"),
                ]
            }]
        );
    }

    #[test]
    fn reference_semantics_defer_base_and_key() {
        // A null base does NOT throw at reference evaluation: the computed
        // key and the right-hand side evaluate first (left to right), and
        // the TypeError arrives only at PutValue.
        let SemOutcome::Trace(t) = run(
            "var order = [];\n\
             function k() { order.push('k'); return 'p'; }\n\
             function v() { order.push('v'); return 1; }\n\
             var base = null; var t = false;\n\
             try { base[k()] = v(); } catch (e) { t = e instanceof TypeError; }\n\
             console.log(t, order);",
        ) else {
            panic!("expected trace");
        };
        assert_eq!(
            t.events,
            vec![HostEvent::Stdout {
                v: vec![
                    ProjectedValue::Bool { v: true },
                    ProjectedValue::Obj {
                        id: 0,
                        cls: Some("Array".to_string()),
                        props: Some(vec![
                            (
                                PropKey::Str("0".to_string()),
                                ProjectedValue::Str { v: "k".to_string() }
                            ),
                            (
                                PropKey::Str("1".to_string()),
                                ProjectedValue::Str { v: "v".to_string() }
                            ),
                            (
                                PropKey::Str("length".to_string()),
                                ProjectedValue::Nonenum {
                                    v: Box::new(num("2"))
                                }
                            ),
                        ]),
                        unintrospectable: None,
                        keycap: None,
                    },
                ]
            }]
        );
        // Compound assignment on a null base: GetValue's ToObject throws
        // TypeError BEFORE ToPropertyKey — the poisoned toString never runs.
        assert_eq!(
            completion_of(run(
                "var base = null; var t = false;\n\
                 var p = { toString: function () { throw 'poison'; } };\n\
                 try { base[p] *= 1; } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
        // Compound assignment coerces the key at GetValue AND at PutValue
        // (two toString calls — matches Node); simple assignment only at
        // PutValue (one).
        assert_eq!(
            completion_of(run(
                "var n = 0; var o = {};\n\
                 var p = { toString: function () { n++; return 'k'; } };\n\
                 o[p] += 1; n;"
            )),
            Completion::Normal { v: Some(num("2")) }
        );
        assert_eq!(
            completion_of(run(
                "var n = 0; var o = {};\n\
                 var p = { toString: function () { n++; return 'k'; } };\n\
                 o[p] = 1; n;"
            )),
            Completion::Normal { v: Some(num("1")) }
        );
    }

    #[test]
    fn tdz_closure_write_before_initialization() {
        let SemOutcome::Trace(t) = run(
            "function f() { x = 1; }\n\
             var t = false;\n\
             try { f(); } catch (e) { t = e instanceof ReferenceError; }\n\
             let x;\n\
             f();\n\
             console.log(t, x);",
        ) else {
            panic!("expected trace");
        };
        assert_eq!(
            t.events,
            vec![HostEvent::Stdout {
                v: vec![ProjectedValue::Bool { v: true }, num("1")]
            }]
        );
        // Same shape inside a function body (FunctionDeclarationInstantiation).
        assert_eq!(
            completion_of(run(
                "(function () {\n\
                 function f() { y = 2; }\n\
                 var t = false;\n\
                 try { f(); } catch (e) { t = e instanceof ReferenceError; }\n\
                 let y;\n\
                 f();\n\
                 return t && y === 2;\n\
                 })();"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
    }

    #[test]
    fn fn_name_reassignment_and_const_writes() {
        // Sloppy assignment to a named function expression's own name is a
        // silent no-op...
        assert_eq!(
            completion_of(run(
                "var f = function g() { g = 5; return g; }; f() === f;"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
        // ...but throws TypeError when the assigning code is strict...
        assert_eq!(
            completion_of(run(
                "var f = function g() { 'use strict'; g = 5; };\n\
                 var t = false;\n\
                 try { f(); } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
        // ...and `const` writes throw even in sloppy code.
        assert_eq!(
            completion_of(run(
                "const c = 1; var t = false;\n\
                 try { c = 2; } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
    }

    #[test]
    fn instance_of_checks_object_operand_before_prototype() {
        // OrdinaryHasInstance step 3: primitive LHS → false BEFORE the
        // `prototype` read (a primitive prototype must not TypeError here).
        assert_eq!(
            completion_of(run(
                "Function.prototype.prototype = true;\n\
                 0 instanceof Function.prototype;"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: false })
            }
        );
        // Object LHS with a primitive prototype still throws (step 5).
        assert_eq!(
            completion_of(run(
                "var f = function () {}; f.prototype = 5; var t = false;\n\
                 try { ({}) instanceof f; } catch (e) { t = e instanceof TypeError; } t;"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
    }

    #[test]
    fn strict_early_errors_are_exact_syntax_error_traces() {
        let is_syntax_throw = |o: SemOutcome| -> bool {
            matches!(
                o,
                SemOutcome::Trace(t) if t.completion == Completion::Throw {
                    v: ThrownProjection::Error {
                        ctor: Some("Error:SyntaxError".to_string()),
                        name: Some("SyntaxError".to_string()),
                        ctor_name: Some("SyntaxError".to_string()),
                    },
                    phase: None,
                }
            )
        };
        // Strict eval/arguments: binding, assignment target, update operand.
        assert!(is_syntax_throw(run("\"use strict\";\nvar eval = 1;")));
        assert!(is_syntax_throw(run("\"use strict\";\neval = 1;")));
        assert!(is_syntax_throw(run("\"use strict\";\narguments++;")));
        assert!(is_syntax_throw(run("\"use strict\";\n--eval;")));
        // Retroactive: the strict directive in the BODY poisons the name and
        // parameters of the function itself.
        assert!(is_syntax_throw(run("(function eval() { 'use strict'; });")));
        assert!(is_syntax_throw(run(
            "function f(arguments) { 'use strict'; }"
        )));
        // Both-mode early errors: duplicate __proto__ data props, catch-
        // parameter lexical redeclaration.
        assert!(is_syntax_throw(run(
            "({ __proto__: null, other: null, '__proto__': null });"
        )));
        assert!(is_syntax_throw(run("try { } catch (x) { let x; }")));
        // A SINGLE __proto__ data property sets [[Prototype]] — unmodeled,
        // refuses (never a wrong own-property trace, never a guessed error).
        assert!(matches!(
            run("({ __proto__: null });"),
            SemOutcome::NoCoverage { .. }
        ));
        // The duplicate-__proto__ early error applies ONLY to ObjectLiteral
        // initializers: the same brace form as a destructuring pattern is
        // legal in real engines, so it must NOT become a SyntaxError trace —
        // destructuring is out of slice, hence NoCoverage.
        assert!(matches!(
            run("var v = {}, x, y; ({ __proto__: x, __proto__: y } = v);"),
            SemOutcome::NoCoverage { .. }
        ));
        assert!(matches!(
            run("var v = {}, x, y, r; r = { __proto__: x, __proto__: y } = v;"),
            SemOutcome::NoCoverage { .. }
        ));
    }

    #[test]
    fn arguments_object_mapped_and_strict() {
        // Mapped (sloppy) arguments: length, index reads, and LIVE aliasing
        // with the parameter bindings, both directions; delete unmaps.
        assert_eq!(
            completion_of(run(
                "function f(a, b) {\n\
                 var r = [];\n\
                 r.push(arguments.length, arguments[0]);\n\
                 a = 7; r.push(arguments[0]);\n\
                 arguments[0] = 8; r.push(a);\n\
                 delete arguments[0]; a = 9;\n\
                 r.push(arguments[0] === undefined, arguments.hasOwnProperty('0'));\n\
                 return r.join(',');\n\
                 } f(1, 2, 3);"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Str {
                    v: "3,1,7,8,true,false".to_string()
                })
            }
        );
        // Unmapped (strict) arguments: no aliasing; callee poisons.
        assert_eq!(
            completion_of(run(
                "function f(a) { 'use strict'; a = 7; return arguments[0]; } f(1);"
            )),
            Completion::Normal { v: Some(num("1")) }
        );
        assert_eq!(
            completion_of(run(
                "function f() { 'use strict'; var t = false;\n\
                 try { arguments.callee; } catch (e) { t = e instanceof TypeError; }\n\
                 return t; } f();"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
        // Sloppy callee is the function itself.
        assert_eq!(
            completion_of(run(
                "function f() { return arguments.callee === f; } f();"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
        // A sloppy `arguments` BINDING overlay still refuses.
        assert!(matches!(
            run("function f() { var arguments = 1; } f();"),
            SemOutcome::NoCoverage { .. }
        ));
        // At script top level (indirect-eval global scope) `arguments` is an
        // ordinary identifier.
        assert_eq!(
            completion_of(run("var arguments = 41; arguments + 1;")),
            Completion::Normal { v: Some(num("42")) }
        );
    }

    fn str_of(s: &str) -> ProjectedValue {
        ProjectedValue::Str { v: s.to_string() }
    }

    #[test]
    fn descriptor_machinery_end_to_end() {
        // defineProperty defaults + redefinition validation + RangeError-free
        // exact length semantics.
        assert_eq!(
            completion_of(run(
                "var o = {}; Object.defineProperty(o, 'x', { value: 1 });\n\
                 var d = Object.getOwnPropertyDescriptor(o, 'x');\n\
                 var t = false;\n\
                 try { Object.defineProperty(o, 'x', { value: 2 }); } catch (e) { t = e instanceof TypeError; }\n\
                 [d.value, d.writable, d.enumerable, d.configurable, t, Object.keys(o).length].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("1,false,false,false,true,0"))
            }
        );
        // freeze/seal/preventExtensions observables.
        assert_eq!(
            completion_of(run(
                "var o = { a: 1 }; Object.freeze(o); o.a = 2; delete o.a; o.b = 3;\n\
                 [o.a, Object.isFrozen(o), Object.isSealed(o), Object.isExtensible(o), 'b' in o].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("1,true,true,false,false"))
            }
        );
        // ArraySetLength: non-writable length rejects the [[Set]] BEFORE any
        // coercion; non-configurable elements stop the shrink.
        assert_eq!(
            completion_of(run(
                "var n = 0; var a = [1, 2, 3];\n\
                 Object.defineProperty(a, '1', { configurable: false });\n\
                 a.length = 0;\n\
                 Object.defineProperty(a, 'length', { writable: false });\n\
                 a.length = { valueOf: function () { n++; return 9; } };\n\
                 [a.length, n].join(',');"
            )),
            Completion::Normal { v: Some(str_of("2,0")) }
        );
    }

    #[test]
    fn for_in_and_for_of() {
        assert_eq!(
            completion_of(run(
                "var ks = []; var o = { b: 1, 2: 'x', a: 2, 0: 'y' };\n\
                 for (var k in o) ks.push(k); ks.join(',');"
            )),
            Completion::Normal { v: Some(str_of("0,2,b,a")) }
        );
        // Own non-enumerable shadows an enumerable proto key.
        assert_eq!(
            completion_of(run(
                "function F() {} F.prototype.p = 3; var o = new F();\n\
                 Object.defineProperty(o, 'p', { value: 1, enumerable: false, configurable: true });\n\
                 var ks = []; for (var k in o) ks.push(k); ks.length;"
            )),
            Completion::Normal { v: Some(num("0")) }
        );
        // for-of over arrays reads inherited holes; strings iterate code
        // points.
        assert_eq!(
            completion_of(run(
                "Array.prototype[1] = 9; var a = [7]; a.length = 2;\n\
                 var r = []; for (var v of a) r.push(v);\n\
                 delete Array.prototype[1];\n\
                 var s = ''; for (var c of 'ab') s += c;\n\
                 r.join(',') + '|' + s;"
            )),
            Completion::Normal { v: Some(str_of("7,9|ab")) }
        );
        // Mutation during enumeration (additions) is spec latitude: refuse.
        assert!(matches!(
            run("var o = { a: 1 }; for (var k in o) { o.z = 1; }"),
            SemOutcome::NoCoverage { .. }
        ));
    }

    #[test]
    fn delete_in_void_operators() {
        assert_eq!(
            completion_of(run(
                "var o = { a: 1 }; var a = [1, 2];\n\
                 [delete o.a, delete o.missing, delete 42, delete a.length, 'a' in o, 0 in a, void 0 === undefined].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("true,true,true,false,false,true,true"))
            }
        );
    }

    #[test]
    fn wrappers_and_number_statics() {
        assert_eq!(
            completion_of(run(
                "var s = new String('ab'); var n = new Number(41); var b = new Boolean(false);\n\
                 [typeof s, s.length, s[0], n + 1, b ? 1 : 0, s == 'ab', n.toString(), Number.isInteger(5.5), Number.MAX_SAFE_INTEGER].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("object,2,a,42,1,true,41,false,9007199254740991"))
            }
        );
    }

    #[test]
    fn call_apply_bind_and_accessors() {
        assert_eq!(
            completion_of(run(
                "function f(a, b) { return this.x + a + b; }\n\
                 var g = f.bind({ x: 1 }, 2);\n\
                 var o = { get v() { return 40; }, set v(x) { this.got = x; } };\n\
                 o.v = 7;\n\
                 [f.call({ x: 1 }, 2, 3), f.apply({ x: 1 }, [2, 3]), g(3), g.name, g.length, o.v, o.got].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("6,6,6,bound f,1,40,7"))
            }
        );
    }

    #[test]
    fn math_exact_subset_and_refusals() {
        assert_eq!(
            completion_of(run(
                "[Math.pow(2, 32) - 1, Math.floor(-1.5), Math.round(2.5), Math.round(0.49999999999999994), Math.sign(-3), Math.sqrt(9), Math.max(-0, 0) === 0 && 1 / Math.max(-0, 0) > 0].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("4294967295,-2,3,0,-1,3,true"))
            }
        );
        assert!(matches!(run("Math.pow(3, 40);"), SemOutcome::NoCoverage { .. }));
        assert!(matches!(run("Math.sin(1);"), SemOutcome::NoCoverage { .. }));
    }

    #[test]
    fn strings_arrays_templates_comma_elision() {
        assert_eq!(
            completion_of(run(
                "var x = 5;\n\
                 ['a,b,,c'.split(',').length, 'abc'.split('').join('-'), 'aXb'.replace('X', '[$&]'),\n\
                 ' q '.trim(), 'AbC'.toLowerCase(), 'Hello'.slice(-3), 'Hello'.substring(4, 1),\n\
                 [3, 1, 3].lastIndexOf(3), [NaN].includes(NaN), [1, 2, 3].reduce(function (a, b) { return a + b; }),\n\
                 `t${x}` + `${1 + 1}`, (1, 2, 3), [, 1].length, [1, , 2].length].join('|');"
            )),
            Completion::Normal {
                v: Some(str_of("4|a-b-c|a[X]b|q|abc|llo|ell|2|true|6|t52|3|2|3"))
            }
        );
    }

    #[test]
    fn object_create_and_get_prototype_of() {
        assert_eq!(
            completion_of(run(
                "var o = Object.create(null); o.x = 1;\n\
                 var p = Object.create(Array.prototype);\n\
                 [Object.getPrototypeOf(o) === null, o.x,\n\
                 Object.getPrototypeOf([]) === Array.prototype,\n\
                 Object.getPrototypeOf('s') === String.prototype,\n\
                 Array.isArray(p)].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("true,1,true,true,false"))
            }
        );
    }

    #[test]
    fn classes_end_to_end() {
        // Base + derived, super method/ctor chains, fields, statics,
        // accessors, exact attributes.
        assert_eq!(
            completion_of(run(
                "class B { constructor(v) { this.b = v; } m() { return 'B' + this.b; }\n\
                 static s() { return 'S'; } get g() { return this.b * 2; } }\n\
                 class D extends B { constructor() { super(21); this.d = 1; }\n\
                 m() { return 'D' + super.m(); } x = this.b + 1; }\n\
                 var d = new D();\n\
                 var md = Object.getOwnPropertyDescriptor(B.prototype, 'm');\n\
                 [d.m(), d.g, d.x, d.d, d instanceof B, B.s(), B.name, D.length,\n\
                 md.writable, md.enumerable, md.configurable,\n\
                 B.prototype.m.prototype === undefined].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("DB21,42,22,1,true,S,B,0,true,false,true,true"))
            }
        );
        // this-TDZ, super-twice, missing-super, class-call TypeErrors.
        assert_eq!(
            completion_of(run(
                "class B {}\n\
                 class D extends B { constructor() { var r = [];\n\
                 try { this; } catch (e) { r.push(e instanceof ReferenceError); }\n\
                 super();\n\
                 try { super(); } catch (e) { r.push(e instanceof ReferenceError); }\n\
                 this.r = r; } }\n\
                 class E extends B { constructor() {} }\n\
                 var out = new D().r;\n\
                 try { new E(); } catch (e) { out.push(e instanceof ReferenceError); }\n\
                 try { B(); } catch (e) { out.push(e instanceof TypeError); }\n\
                 out.join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("true,true,true,true"))
            }
        );
        // Pinned class early errors are exact SyntaxError traces.
        let is_syntax = |src: &str| {
            matches!(
                run(src),
                SemOutcome::Trace(t) if matches!(t.completion, Completion::Throw { .. })
            )
        };
        assert!(is_syntax("class A { constructor() {} constructor() {} }"));
        assert!(is_syntax("class {}"));
        assert!(is_syntax("class A { static prototype() {} }"));
        assert!(is_syntax("super.x;"));
        // Generator methods now parse and run end-to-end.
        assert_eq!(
            completion_of(run("class A { *g() { yield 5; yield 6; } }\n\
                               var it = new A().g();\n\
                               [it.next().value, it.next().value, it.next().done].join(',');")),
            Completion::Normal {
                v: Some(ProjectedValue::Str { v: "5,6,true".to_string() })
            }
        );
        // Private fields, methods, accessors, brand checks, and the exact
        // "add twice" / missing-brand TypeErrors are now modeled.
        assert_eq!(
            completion_of(run(
                "class C { #x = 5; #m() { return this.#x * 2; }\n\
                 get #g() { return this.#x + 1; } set #g(v) { this.#x = v; }\n\
                 static #s = 9; static getS() { return C.#s; }\n\
                 run() { this.#g = 20; return [this.#x, this.#m(), this.#g].join(','); }\n\
                 static has(o) { return #x in o; } }\n\
                 var c = new C();\n\
                 [c.run(), C.getS(), C.has(c), C.has({}),\n\
                 Object.keys(c).length, Object.getOwnPropertyNames(c).length].join('|');"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Str {
                    v: "20,40,21|9|true|false|0|0".to_string()
                })
            }
        );
        // Private fields never appear in the object projection.
        let c = completion_of(run("class C { #x = 1; y = 2; } new C();"));
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
        // Brand-absent access and duplicate/undeclared private names.
        let is_syntax = |src: &str| {
            matches!(
                run(src),
                SemOutcome::Trace(t) if matches!(t.completion, Completion::Throw { .. })
            )
        };
        assert!(is_syntax("class C { m() { return this.#y; } }"));
        assert!(is_syntax("class C { #x = 1; #x = 2; }"));
        assert!(is_syntax("class C { #constructor() {} }"));
        assert!(is_syntax("#x;"));
        assert!(is_syntax("class C { #x = 1; m() { delete this.#x; } }"));
        // A get/set private pair is legal (not a duplicate).
        assert_eq!(
            completion_of(run(
                "class C { #v = 0; get #x() { return this.#v; } set #x(w) { this.#v = w + 1; }\n\
                 run() { this.#x = 10; return this.#x; } }\n\
                 new C().run();"
            )),
            Completion::Normal { v: Some(num("11")) }
        );
    }

    #[test]
    fn object_methods_and_computed_keys() {
        assert_eq!(
            completion_of(run(
                "var log = []; function k(n) { log.push(n); return n; }\n\
                 var o = { [k('a')]: 1, [k('b')](x) { return x * 2; }, get [k('c')]() { return 3; },\n\
                 has(x) { return super.hasOwnProperty.call(this, x); } };\n\
                 [o.a, o.b(2), o.c, log.join(''), o.b.name, o.b.length,\n\
                 o.b.prototype === undefined, o.has('a'), o.has('zz')].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("1,4,3,abc,b,1,true,true,false"))
            }
        );
    }

    #[test]
    fn destructuring_end_to_end() {
        assert_eq!(
            completion_of(run(
                "var { a, b: { c }, d = 4, 'e': e } = { a: 1, b: { c: 2 }, e: 5 };\n\
                 var [x, , y = 20, [z]] = [1, 9, undefined, [4]];\n\
                 var [s1, s2] = 'hi';\n\
                 var { m, ...rest } = { m: 1, n: 2, o: 3 };\n\
                 var p = {}; [p.u, ...p.r] = [7, 8, 9];\n\
                 function f({ q, w = 2 }, ...more) { return [q, w, more.length, arguments.length]; }\n\
                 [a, c, d, e, x, y, z, s1 + s2, rest.n + rest.o, p.u, p.r, f({ q: 1 }, 5, 6)].join(';');"
            )),
            Completion::Normal {
                v: Some(str_of("1;2;4;5;1;20;4;hi;5;7;8,9;1,2,2,3"))
            }
        );
        // TypeErrors: null object source (before keys), non-iterable array
        // source; TDZ in non-simple param defaults.
        assert_eq!(
            completion_of(run(
                "var r = [];\n\
                 try { var { z } = null; } catch (e) { r.push(e instanceof TypeError); }\n\
                 try { var [q] = {}; } catch (e) { r.push(e instanceof TypeError); }\n\
                 var f = (a = b, b) => a;\n\
                 try { f(); } catch (e) { r.push(e instanceof ReferenceError); }\n\
                 r.join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("true,true,true"))
            }
        );
    }

    #[test]
    fn arrows_end_to_end() {
        assert_eq!(
            completion_of(run(
                "var o = { v: 40, m: function () { var a = (x) => this.v + x + arguments[0]; return a(1); } };\n\
                 var t = false; try { new (() => 1)(); } catch (e) { t = e instanceof TypeError; }\n\
                 var fs = []; for (let i = 0; i < 2; i++) fs.push(() => i);\n\
                 var g = x => x * 2;\n\
                 [o.m(1), t, fs[0]() + fs[1](), g.name, g.length, g.prototype === undefined].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("42,true,1,g,1,true"))
            }
        );
    }

    #[test]
    fn escaped_identifiers() {
        assert_eq!(
            completion_of(run(
                "var \\u0061 = 40; var o = {}; o.\\u0069f = 2;\n\
                 [a + 2, o.if].join(',');"
            )),
            Completion::Normal { v: Some(str_of("42,2")) }
        );
        // Escaped true-reserved word as an identifier: exact SyntaxError.
        assert!(matches!(
            run("\\u0069f (true) {}"),
            SemOutcome::Trace(t) if matches!(t.completion, Completion::Throw { .. })
        ));
        // Non-ASCII identifier characters (raw or \u-escaped) now lex via the
        // exact Unicode 16.0.0 ID_Start/ID_Continue tables.
        assert_eq!(
            completion_of(run("var \\u00e9 = 40; \\u00e9 + 2;")),
            Completion::Normal { v: Some(num("42")) }
        );
        assert_eq!(
            completion_of(run("var café = 41; café + 1;")),
            Completion::Normal { v: Some(num("42")) }
        );
        // ...but a code point without the ID property is an exact SyntaxError
        // (¡ is not ID_Start; a combining mark is not ID_Start; ZWNJ is not a
        // start char), never a wrong trace and never a guessed refusal.
        let is_syntax_throw = |o: SemOutcome| -> bool {
            matches!(o, SemOutcome::Trace(t) if matches!(t.completion, Completion::Throw { .. }))
        };
        assert!(is_syntax_throw(run("var \\u00a1 = 1;")));
        assert!(is_syntax_throw(run("var \\u0300 = 1;")));
        assert!(is_syntax_throw(run("var \\uD800 = 1;")));
        assert!(is_syntax_throw(run("var \\u{1F600} = 1;")));
        assert!(is_syntax_throw(run("var x\\u00a1 = 1;")));
        // A combining mark is legal in continue position.
        assert_eq!(
            completion_of(run("var a\\u0300 = 7; a\\u0300;")),
            Completion::Normal { v: Some(num("7")) }
        );
    }

    #[test]
    fn direct_eval_scope_and_hoisting() {
        // Direct eval hoists `var` into the CALLER's variable environment and
        // sees the caller's locals.
        assert_eq!(
            completion_of(run(
                "function f() { eval('var q = 42;'); return q; } f();"
            )),
            Completion::Normal { v: Some(num("42")) }
        );
        assert_eq!(
            completion_of(run(
                "var x = 1; function g() { var x = 2; return eval('x'); } g();"
            )),
            Completion::Normal { v: Some(num("2")) }
        );
        // `(eval)(x)` is still direct (parentheses are reference-transparent).
        assert_eq!(
            completion_of(run(
                "var x = 1; function g() { var x = 2; return (eval)('x'); } g();"
            )),
            Completion::Normal { v: Some(num("2")) }
        );
        // A sloppy direct eval's `var` binding is deletable.
        assert_eq!(
            completion_of(run(
                "function f() { eval('var d = 1; var ok = (delete d) === true;'); return ok; } f();"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
    }

    #[test]
    fn indirect_eval_runs_in_global_scope() {
        // `(0, eval)` and a stored `eval` are indirect: global scope, not the
        // caller's locals.
        assert_eq!(
            completion_of(run(
                "var x = 1; function g() { var x = 2; return (0, eval)('x'); } g();"
            )),
            Completion::Normal { v: Some(num("1")) }
        );
        assert_eq!(
            completion_of(run(
                "var x = 1; function g() { var x = 2; var e = eval; return e('x'); } g();"
            )),
            Completion::Normal { v: Some(num("1")) }
        );
        // Indirect eval creates a global var.
        assert_eq!(
            completion_of(run("(0, eval)('var gg = 7;'); typeof gg;")),
            Completion::Normal {
                v: Some(str_of("number"))
            }
        );
    }

    #[test]
    fn eval_non_string_completion_and_errors() {
        // A non-string argument is returned unchanged (never parsed).
        assert_eq!(
            completion_of(run("eval(123);")),
            Completion::Normal { v: Some(num("123")) }
        );
        assert_eq!(
            completion_of(run("eval(1 + 2);")),
            Completion::Normal { v: Some(num("3")) }
        );
        // The eval completion value is the last value-producing statement.
        assert_eq!(
            completion_of(run("eval('1; 2; 3 + 4');")),
            Completion::Normal { v: Some(num("7")) }
        );
        // A parse-time SyntaxError THROWS (catchable), never a NoCoverage.
        // (`return`/`break`/`continue` at eval top level are exact early
        // errors even when the direct eval is called from inside a function.)
        for src in [
            "var t; try { eval('return;'); } catch (e) { t = e instanceof SyntaxError; } t;",
            "var t; try { eval('break;'); } catch (e) { t = e instanceof SyntaxError; } t;",
            "var t; try { eval('continue;'); } catch (e) { t = e instanceof SyntaxError; } t;",
            "function f() { eval('return;'); } var t; try { f(); } catch (e) { t = e instanceof SyntaxError; } t;",
        ] {
            assert_eq!(
                completion_of(run(src)),
                Completion::Normal {
                    v: Some(ProjectedValue::Bool { v: true })
                },
                "src: {src}"
            );
        }
    }

    #[test]
    fn strict_direct_eval_is_isolated() {
        // A `'use strict'` inside the eval body isolates its `var` from the
        // caller: the outer same-named binding is untouched. A sloppy eval, by
        // contrast, reuses the caller's binding and its initializer leaks.
        assert_eq!(
            completion_of(run(
                "function f() { var se = 'outer'; eval('\"use strict\"; var se = \"inner\";'); return se; } f();"
            )),
            Completion::Normal {
                v: Some(str_of("outer"))
            }
        );
        assert_eq!(
            completion_of(run(
                "function f() { var se = 'outer'; eval('var se = \"inner\";'); return se; } f();"
            )),
            Completion::Normal {
                v: Some(str_of("inner"))
            }
        );
    }

    #[test]
    fn function_constructor_end_to_end() {
        // new Function assembles + parses; name "anonymous", length = #params,
        // global scope.
        assert_eq!(
            completion_of(run(
                "var f = new Function('a', 'b', 'return a + b;');\n\
                 [f(2, 3), f.name, f.length, f.prototype !== undefined].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of("5,anonymous,2,true"))
            }
        );
        // Callable without `new`, closes over the GLOBAL scope (not the caller).
        assert_eq!(
            completion_of(run("var z = 9; function h() { var z = 1; return Function('return z;')(); } h();")),
            Completion::Normal { v: Some(num("9")) }
        );
        // Zero args → empty body, callable, returns undefined.
        assert_eq!(
            completion_of(run("new Function()();")),
            Completion::Normal {
                v: Some(ProjectedValue::Undefined)
            }
        );
        // A body with an early error (here `break` outside any loop) throws a
        // catchable SyntaxError.
        assert_eq!(
            completion_of(run(
                "var t; try { new Function('break;'); } catch (e) { t = e instanceof SyntaxError; } t;"
            )),
            Completion::Normal {
                v: Some(ProjectedValue::Bool { v: true })
            }
        );
    }

    #[test]
    fn caps_and_schema_stamped() {
        let SemOutcome::Trace(t) = run("1;") else {
            panic!("expected trace");
        };
        assert_eq!(t.schema, SCHEMA_VERSION);
        assert_eq!(t.caps, Some(projection_caps()));
    }

    fn str_of2(s: &str) -> ProjectedValue {
        ProjectedValue::Str { v: s.to_string() }
    }

    #[test]
    fn typed_array_globals_and_construction() {
        // Globals exist; %TypedArray% is the shared prototype of the concrete
        // constructors; BYTES_PER_ELEMENT + names are exact.
        assert_eq!(
            completion_of(run(
                "[typeof Int8Array, typeof Float64Array, typeof Uint8ClampedArray,\n\
                 typeof Float16Array, typeof BigInt64Array, typeof ArrayBuffer, typeof DataView,\n\
                 Object.getPrototypeOf(Int8Array) === Object.getPrototypeOf(Float64Array),\n\
                 Object.getPrototypeOf(Int8Array).name, Int8Array.BYTES_PER_ELEMENT,\n\
                 Float64Array.BYTES_PER_ELEMENT, Int8Array.name].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of2(
                    "function,function,function,function,function,function,function,true,TypedArray,1,8,Int8Array"
                ))
            }
        );
    }

    #[test]
    fn typed_array_element_coercion() {
        // Modular int wrap, Uint8Clamped round-half-even, Float32/Float16
        // round-to-nearest-even, NaN/Inf → 0.
        assert_eq!(
            completion_of(run(
                "[new Int8Array([300, -1, 128])[0], new Uint8Array([-1])[0],\n\
                 new Uint8ClampedArray([300,-5,2.5,3.5]).join('|'),\n\
                 new Int32Array([NaN, Infinity, 1.9, -1.9]).join('|'),\n\
                 new Int16Array([70000])[0], new Uint32Array([-1])[0],\n\
                 new Float32Array([0.1])[0], new Float16Array([1.1])[0]].join(';');"
            )),
            Completion::Normal {
                v: Some(str_of2(
                    "44;255;255|0|2|4;0|0|1|-1;4464;4294967295;0.10000000149011612;1.099609375"
                ))
            }
        );
    }

    #[test]
    fn typed_array_exotic_indexing() {
        // OOB read→undefined, write no-op; canonical-vs-ordinary keys; in/has;
        // Object.keys is the element indices.
        assert_eq!(
            completion_of(run(
                "var a = new Int8Array(3); a[0]=10; a[5]=9; a['1.5']=7; a.foo=8;\n\
                 [a[0], a[5], a['1.5'], a.foo, 0 in a, 3 in a, a.length,\n\
                 Object.keys(a).join('|'), a.hasOwnProperty('0'), a.hasOwnProperty('5')].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of2("10,,,8,true,false,3,0|1|2|foo,true,false"))
            }
        );
    }

    #[test]
    fn dataview_byte_order_and_bounds() {
        assert_eq!(
            completion_of(run(
                "var b = new ArrayBuffer(8); var d = new DataView(b);\n\
                 d.setInt16(0, 0x1234, true); var u = new Uint8Array(b);\n\
                 var t = false;\n\
                 try { d.getInt32(6); } catch (e) { t = e instanceof RangeError; }\n\
                 [u[0], u[1], d.getInt16(0, false).toString(16), d.getInt16(0, true).toString(16), t].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of2("52,18,3412,1234,true"))
            }
        );
    }

    #[test]
    fn binary_projection_and_tostring_tag() {
        // ArrayBuffer/DataView project with their cls; a typed array projects
        // as cls "Object" with element props; @@toStringTag is exact.
        let c = completion_of(run("new ArrayBuffer(4);"));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { cls, props, .. }),
        } = c
        else {
            panic!("expected object");
        };
        assert_eq!(cls.as_deref(), Some("ArrayBuffer"));
        assert!(props.expect("props").is_empty());

        let c = completion_of(run("new Int8Array([7, 8]);"));
        let Completion::Normal {
            v: Some(ProjectedValue::Obj { cls, props, .. }),
        } = c
        else {
            panic!("expected object");
        };
        assert_eq!(cls.as_deref(), Some("Object"));
        assert_eq!(
            props.expect("props"),
            vec![
                (PropKey::Str("0".to_string()), num("7")),
                (PropKey::Str("1".to_string()), num("8")),
            ]
        );

        assert_eq!(
            completion_of(run(
                "[Object.prototype.toString.call(new Int8Array(1)),\n\
                 Object.prototype.toString.call(new ArrayBuffer(1)),\n\
                 Object.prototype.toString.call(new DataView(new ArrayBuffer(1)))].join('|');"
            )),
            Completion::Normal {
                v: Some(str_of2(
                    "[object Int8Array]|[object ArrayBuffer]|[object DataView]"
                ))
            }
        );
    }

    #[test]
    fn bigint_typed_arrays() {
        // The globals exist (typeof/name/BYTES_PER_ELEMENT exact)...
        assert_eq!(
            completion_of(run(
                "[typeof BigInt64Array, BigInt64Array.name, BigInt64Array.BYTES_PER_ELEMENT].join(',');"
            )),
            Completion::Normal {
                v: Some(str_of2("function,BigInt64Array,8"))
            }
        );
        // ...and construction + element access now work (64-bit wrap; ToBigInt).
        assert_eq!(
            completion_of(run(
                "var a = new BigInt64Array(1); a[0] = (2n ** 63n); a[0] === -(2n ** 63n);"
            )),
            Completion::Normal { v: Some(ProjectedValue::Bool { v: true }) }
        );
        assert_eq!(
            completion_of(run(
                "var a = new BigUint64Array([1n, 2n]); (a[0] + a[1]).toString();"
            )),
            Completion::Normal { v: Some(str_of2("3")) }
        );
        // Storing a Number into a BigInt array is a TypeError (ToBigInt).
        assert!(matches!(
            completion_of(run("var a = new BigInt64Array(1); a[0] = 5;")),
            Completion::Throw { .. }
        ));
        // BigInt DataView access is still out of slice (sound refusal).
        assert!(matches!(
            run("new DataView(new ArrayBuffer(8)).getBigInt64(0);"),
            SemOutcome::NoCoverage { .. }
        ));
    }

    #[test]
    fn numeric_separator_and_json_bigint_regression() {
        let is_syntax_throw = |o: SemOutcome| -> bool {
            matches!(
                o,
                SemOutcome::Trace(t) if t.completion == Completion::Throw {
                    v: ThrownProjection::Error {
                        ctor: Some("Error:SyntaxError".to_string()),
                        name: Some("SyntaxError".to_string()),
                        ctor_name: Some("SyntaxError".to_string()),
                    },
                    phase: None,
                }
            )
        };
        // A NumericLiteralSeparator adjacent to a leading `0`, doubled,
        // trailing, or adjacent to a radix prefix is an exact parse SyntaxError
        // in BOTH modes (the 14-case tail the recorded gate flagged).
        for bad in [
            "0_0;", "0_1;", "0_7;", "0_8;", "0_9;", "0_0123456789;", "0_0n;",
            "10__0123456789;", "1_;", "0o_1;", "0o1_;", "0x_1;", "1._5;", "1e_5;",
        ] {
            assert!(is_syntax_throw(run(bad)), "expected SyntaxError for {bad}");
            assert!(
                is_syntax_throw(run(&format!("\"use strict\";\n{bad}"))),
                "expected SyntaxError (strict) for {bad}"
            );
        }
        // Valid separators still lex and evaluate.
        let t = |b: &str| completion_of(run(b));
        assert_eq!(
            t("1_000 === 1000;"),
            Completion::Normal { v: Some(ProjectedValue::Bool { v: true }) }
        );
        assert_eq!(
            t("0xFF_FF === 65535;"),
            Completion::Normal { v: Some(ProjectedValue::Bool { v: true }) }
        );
        assert_eq!(
            t("1_0n === 10n;"),
            Completion::Normal { v: Some(ProjectedValue::Bool { v: true }) }
        );
        // JSON.stringify(BigInt): a bare bigint (no toJSON) is a TypeError; a
        // BigInt.prototype.toJSON is consulted first (25.5.2.1 step 2).
        assert!(matches!(t("JSON.stringify(1n);"), Completion::Throw { .. }));
        assert!(matches!(
            t("BigInt.prototype.toJSON = function () { return this.toString(); }; JSON.stringify(0n);"),
            Completion::Normal { v: Some(ProjectedValue::Str { .. }) }
        ));
    }
}
