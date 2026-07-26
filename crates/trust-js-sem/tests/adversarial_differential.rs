// Env-gated adversarial differential for the grown S0 surfaces: property
// descriptors + attribute machinery, delete / in, for-in / for-of, the
// arguments object, call/apply/bind, Math (exact subset), template literals,
// object-literal accessors, and the Array/String prototype methods. Every
// case runs through BOTH trust_js_sem::evaluate_case and the real trace
// driver on Node and must be byte-for-byte trace-equal; cases marked Refuse
// pin the sound-refusal (NoCoverage) behavior instead and never claim a
// trace. Skips loudly when TRUST_JS_NODE is unset.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::io::Write;
use std::path::Path;
use std::process::Command;
use trust_js_sem::{evaluate_case, SemOutcome};
use trust_js_trace::{explain_divergence, extract_trace, traces_equal};

#[derive(Clone, Copy, PartialEq)]
enum Expect {
    /// Must produce a trace AND match the Node driver byte-for-byte.
    Cover,
    /// Must refuse (NoCoverage) — the construct has spec/engine latitude or
    /// is deliberately out of slice; the driver is not consulted.
    Refuse,
}

struct Case {
    name: &'static str,
    strict: bool,
    expect: Expect,
    body: &'static str,
}

const C: Expect = Expect::Cover;
const R: Expect = Expect::Refuse;

#[allow(clippy::too_many_lines)]
fn cases() -> Vec<Case> {
    let mut v = Vec::new();
    let mut c = |name: &'static str, strict: bool, expect: Expect, body: &'static str| {
        v.push(Case {
            name,
            strict,
            expect,
            body,
        });
    };

    // ---- for-in ----------------------------------------------------------
    c("forin-basic-order", false, C,
      "var o = { b: 1, 2: 'x', a: 2, 0: 'y' }; var ks = []; for (var k in o) ks.push(k); console.log(ks);");
    c("forin-array-holes-extra", false, C,
      "var a = [1, 2]; a.x = 9; var ks = []; for (var k in a) ks.push(k); console.log(ks);");
    c("forin-inherited", false, C,
      "function F() {} F.prototype.p = 1; var o = new F(); o.q = 2; var ks = []; for (var k in o) ks.push(k); console.log(ks);");
    c("forin-own-nonenum-shadows-proto", false, C,
      "function F() {} F.prototype.p = 3; var o = new F();\n\
       Object.defineProperty(o, 'p', { value: 1, enumerable: false, configurable: true });\n\
       var ks = []; for (var k in o) ks.push(k); console.log(ks);");
    c("forin-delete-later-key", false, C,
      "var o = { a: 1, b: 2, c: 3 }; var ks = []; for (var k in o) { ks.push(k); delete o.c; } console.log(ks);");
    c("forin-delete-reveals-proto", false, C,
      "function F() {} F.prototype.b = 9; var o = new F(); o.a = 1; o.b = 2;\n\
       var ks = []; for (var k in o) { ks.push(k); delete o.b; } console.log(ks);");
    c("forin-string", false, C,
      "var ks = []; for (var k in 'ab') ks.push(k); console.log(ks);");
    c("forin-let-binding", false, C,
      "var ks = []; for (let k in { a: 1, b: 2 }) ks.push(k); console.log(ks);");
    c("forin-const-binding", false, C,
      "var ks = []; for (const k in { a: 1 }) ks.push(k); console.log(ks);");
    c("forin-head-tdz", false, C,
      "var t = false; try { for (let x in x) {} } catch (e) { t = e instanceof ReferenceError; } console.log(t);");
    c("forin-member-target", false, C,
      "var o = {}; var a = []; for (o.k in { x: 1, y: 2 }) a.push(o.k); console.log(a, o.k);");
    c("forin-number-zero-iters", false, C,
      "var n = 0; for (var k in 5) n++; console.log(n);");
    c("forin-null-undefined-skip", false, C,
      "var n = 0; for (var k in null) n++; for (var j in undefined) n++; console.log(n);");
    c("forin-object-proto-added", false, C,
      "Object.prototype.zz = 1; var ks = []; for (var k in { a: 1 }) ks.push(k); console.log(ks); delete Object.prototype.zz;");
    c("forin-completion-null", false, C, "42; for (var k in null) {}");
    c("forin-completion-empty", false, C, "42; for (var k in {}) {}");
    c("forin-completion-body-value", false, C, "for (var k in { a: 1 }) 5;");
    c("forof-completion-value", false, C, "42; for (var x of []) {} ");
    c("forof-completion-body-value", false, C, "for (var x of [1]) 7;");
    c("forin-arguments", false, C,
      "function f(a, b) { var ks = []; for (var k in arguments) ks.push(k); return ks; } console.log(f(1, 2, 3));");
    // Additions during enumeration are spec latitude → refuse.
    c("forin-added-key-refuses", false, R,
      "var o = { a: 1, b: 2 }; for (var k in o) { o.c = 3; } console.log('never');");
    c("forin-global-refuses", false, R,
      "for (var k in globalThis) {} console.log('never');");

    // ---- for-of ----------------------------------------------------------
    c("forof-array-basic", false, C,
      "var r = []; for (var v of [1, 2, 3]) r.push(v); console.log(r);");
    c("forof-array-holes-proto", false, C,
      "var a = [1, 2]; a.length = 4; Array.prototype[3] = 9;\n\
       var r = []; for (var v of a) r.push(v); console.log(r);\n\
       delete Array.prototype[3];");
    c("forof-string-code-points", false, C,
      "var r = []; for (var ch of 'a\\ud83d\\ude00b') r.push(ch); console.log(r);");
    c("forof-mutation-grows", false, C,
      "var a = [1, 2]; var r = []; for (var v of a) { r.push(v); if (v === 1) a.push(99); } console.log(r);");
    c("forof-plain-object-typeerror", false, C,
      "var t = false; try { for (var v of {}) {} } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("forof-number-typeerror", false, C,
      "var t = false; try { for (var v of 5) {} } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("forof-null-typeerror", false, C,
      "var t = false; try { for (var v of null) {} } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("forof-arguments", false, C,
      "function f() { var r = []; for (var v of arguments) r.push(v); return r; } console.log(f(1, 'x'));");
    c("forof-break-continue", false, C,
      "var r = []; for (var v of [1, 2, 3, 4]) { if (v === 2) continue; if (v === 4) break; r.push(v); } console.log(r);");
    c("forof-let", false, C,
      "var r = []; for (let v of [7, 8]) r.push(v); console.log(r);");

    // ---- delete / in / void ----------------------------------------------
    c("delete-basics", false, C,
      "var o = { a: 1 }; console.log(delete o.a, o.a === undefined, delete o.missing, delete 42, void 0);");
    c("delete-array-element", false, C,
      "var a = [1, 2, 3]; console.log(delete a[1], a.length, a.hasOwnProperty('1'), 1 in a, a);");
    c("delete-nonconfigurable-sloppy", false, C,
      "var a = []; console.log(delete a.length);");
    c("delete-nonconfigurable-strict-throws", true, C,
      "var a = []; var t = false; try { delete a.length; } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("delete-string-members", false, C,
      "console.log(delete 'abc'[5], delete 'abc'.foo);");
    c("delete-global-binding", false, C,
      "function g() {} console.log(delete globalThis.g);");
    c("in-operator", false, C,
      "var o = { a: 1 }; console.log('a' in o, 'b' in o, 'toString' in o, 0 in [7], 1 in [7], 'length' in []);");
    c("in-primitive-typeerror", false, C,
      "var t = false; try { 'x' in 'abc'; } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("in-key-coercion-order", false, C,
      "var t = false; var p = { toString: function () { throw new Error('poison'); } };\n\
       try { p in 5; } catch (e) { t = e instanceof TypeError; } console.log(t);");

    // ---- descriptors ------------------------------------------------------
    c("defineproperty-defaults", false, C,
      "var o = {}; Object.defineProperty(o, 'x', { value: 1 });\n\
       var d = Object.getOwnPropertyDescriptor(o, 'x');\n\
       console.log(d, o.x, Object.keys(o), o);");
    c("defineproperty-accessor", false, C,
      "var o = {}; var n = 0;\n\
       Object.defineProperty(o, 'x', { get: function () { n++; return 42; }, configurable: true });\n\
       console.log(o.x, n, Object.getOwnPropertyDescriptor(o, 'x'), o);");
    c("defineproperty-redefine-throws", false, C,
      "var o = {}; Object.defineProperty(o, 'x', { value: 1 });\n\
       var t = false; try { Object.defineProperty(o, 'x', { value: 2 }); } catch (e) { t = e instanceof TypeError; }\n\
       var ok = true; Object.defineProperty(o, 'x', { value: 1 });\n\
       console.log(t, ok);");
    c("defineproperty-array-index", false, C,
      "var a = []; Object.defineProperty(a, '3', { value: 9, enumerable: true, writable: true, configurable: true });\n\
       console.log(a.length, a[3], a);");
    c("defineproperty-length-nonwritable", false, C,
      "var a = [1, 2]; Object.defineProperty(a, 'length', { writable: false });\n\
       a[5] = 1; a.length = 0;\n\
       console.log(a.length, a[5] === undefined, a);");
    c("length-shrink-nonconfigurable-element", false, C,
      "var a = [1, 2, 3]; Object.defineProperty(a, '1', { configurable: false });\n\
       a.length = 0; console.log(a.length, a);");
    c("length-shrink-nonconfigurable-strict", true, C,
      "var a = [1, 2, 3]; Object.defineProperty(a, '1', { configurable: false });\n\
       var t = false; try { a.length = 0; } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t, a.length);");
    c("length-nonwritable-set-no-coercion", false, C,
      "var n = 0; var a = []; Object.defineProperty(a, 'length', { writable: false });\n\
       a.length = { valueOf: function () { n++; return 0; } };\n\
       console.log(n, a.length);");
    c("shift-frozen-empty-typeerror", false, C,
      "var a = []; Object.freeze(a); var t = false;\n\
       try { a.shift(); } catch (e) { t = e instanceof TypeError; }\n\
       var b = []; Object.freeze(b); var u = false;\n\
       try { b.unshift(); } catch (e) { u = e instanceof TypeError; }\n\
       var d = []; Object.freeze(d); var w = false;\n\
       try { d.pop(); } catch (e) { w = e instanceof TypeError; }\n\
       console.log(t, u, w);");
    c("length-valueof-coerces-twice", false, C,
      "var n = 0; var a = []; a.length = { valueOf: function () { n++; return 2; } };\n\
       console.log(n, a.length);");
    c("descriptor-read-order", false, C,
      "var log = []; var o = {};\n\
       var desc = { get value() { log.push('value'); return 1; },\n\
                    get enumerable() { log.push('enumerable'); return true; },\n\
                    get configurable() { log.push('configurable'); return true; },\n\
                    get writable() { log.push('writable'); return true; } };\n\
       Object.defineProperty(o, 'x', desc);\n\
       console.log(log, o.x);");
    c("freeze-basics", false, C,
      "var o = { a: 1 }; Object.freeze(o); o.a = 2; o.b = 3; delete o.a;\n\
       console.log(o.a, o.b === undefined, Object.isFrozen(o), Object.isExtensible(o), Object.isSealed(o));");
    c("freeze-strict-throws", true, C,
      "var o = Object.freeze({ a: 1 }); var t = false;\n\
       try { o.a = 2; } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("seal-basics", false, C,
      "var o = { a: 1 }; Object.seal(o); delete o.a; o.a = 2; o.b = 9;\n\
       console.log(o.a, o.b === undefined, Object.isSealed(o), Object.isFrozen(o));");
    c("preventextensions", false, C,
      "var o = { a: 1 }; Object.preventExtensions(o); o.b = 2; o.a = 5;\n\
       console.log(o.a, o.b === undefined, Object.isExtensible(o), Object.isFrozen(o));");
    c("frozen-array", false, C,
      "var a = Object.freeze([1, 2]); a.push; var t = false;\n\
       try { 'use strict'; } catch (e) {}\n\
       a[0] = 9; a[5] = 1; console.log(a, a.length, Object.isFrozen(a));");
    c("getownpropertynames", false, C,
      "console.log(Object.getOwnPropertyNames({ b: 1, 2: 'x', a: 2 }),\n\
       Object.getOwnPropertyNames([1]), Object.getOwnPropertyNames('ab'),\n\
       Object.getOwnPropertyNames(function f(a) { 'use strict'; }));");
    // Sloppy user functions carry legacy own caller/arguments in real
    // engines (non-spec): the whole own-key walk refuses, as does any
    // observation of those two names.
    c("getownpropertynames-sloppy-fn-refuses", false, R,
      "console.log(Object.getOwnPropertyNames(function f(a) {}));");
    c("sloppy-fn-caller-hasown-refuses", false, R,
      "function f() {} console.log(f.hasOwnProperty('caller'));");
    c("defineproperties", false, C,
      "var o = Object.defineProperties({}, { a: { value: 1, enumerable: true }, b: { get: function () { return 2; } } });\n\
       console.log(o.a, o.b, Object.keys(o), o);");
    c("getownpropertydescriptors", false, C,
      "var o = { a: 1 }; Object.defineProperty(o, 'b', { value: 2 });\n\
       console.log(Object.getOwnPropertyDescriptors(o));");
    c("descriptor-of-intrinsic-method", false, C,
      "var d = Object.getOwnPropertyDescriptor(Array.prototype, 'push');\n\
       console.log(d.writable, d.enumerable, d.configurable, typeof d.value);");
    c("keys-primitives", false, C,
      "console.log(Object.keys('ab'), Object.keys(true), Object.getOwnPropertyNames(5));");
    c("descriptor-unmodeled-intrinsic-refuses", false, R,
      "console.log(Object.getOwnPropertyDescriptor(Array.prototype, 'flat'));");
    c("defineproperty-global-refuses", false, R,
      "Object.defineProperty(globalThis, 'q', { value: 1 }); console.log('never');");

    // ---- object-literal accessors + accessor evaluation -------------------
    c("literal-getter-setter", false, C,
      "var log = []; var o = { get x() { log.push('g'); return 1; }, set x(v) { log.push('s' + v); } };\n\
       o.x; o.x = 5;\n\
       console.log(log, o.x, o);");
    c("literal-getter-only-set", false, C,
      "var o = { get x() { return 1; } }; o.x = 9; console.log(o.x, o);");
    c("literal-getter-only-set-strict", true, C,
      "var o = { get x() { return 1; } }; var t = false;\n\
       try { o.x = 9; } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("inherited-accessor-receiver", false, C,
      "function F() {}\n\
       Object.defineProperty(F.prototype, 'x', { set: function (v) { this._x = v * 2; }, get: function () { return this._x; } });\n\
       var o = new F(); o.x = 21;\n\
       console.log(o.x, o.hasOwnProperty('x'), o.hasOwnProperty('_x'));");
    c("accessor-fn-names", false, C,
      "var o = { get ab() { return 1; }, set ab(v) {} };\n\
       var d = Object.getOwnPropertyDescriptor(o, 'ab');\n\
       console.log(d.get.name, d.set.name, d.get.length, d.set.length, d.enumerable, d.configurable);");
    c("getter-throw-propagates", false, C,
      "var o = { get x() { throw new RangeError('r'); } }; var t = false;\n\
       try { o.x; } catch (e) { t = e instanceof RangeError; } console.log(t);");
    c("accessor-data-merge", false, C,
      "var o = { get x() { return 1; }, set x(v) {}, x: 5 };\n\
       var d = Object.getOwnPropertyDescriptor(o, 'x');\n\
       console.log(o.x, d.writable, 'get' in d, o);");

    // ---- arguments object -------------------------------------------------
    c("arguments-projection-mapped", false, C,
      "function f(a) { console.log(arguments); } f(1, 'x');");
    c("arguments-projection-strict", true, C,
      "function f(a) { console.log(arguments); } f(1);");
    c("arguments-mapped-aliasing", false, C,
      "function f(a, b) { var r = [];\n\
       r.push(arguments.length, arguments[0]);\n\
       a = 7; r.push(arguments[0]);\n\
       arguments[0] = 8; r.push(a);\n\
       delete arguments[0]; a = 9;\n\
       r.push(arguments[0] === undefined, arguments.hasOwnProperty('0'));\n\
       return r; } console.log(f(1, 2, 3));");
    c("arguments-unmapped-strict", true, C,
      "function f(a) { a = 7; arguments[0] = 9; return [arguments[0], a]; } console.log(f(1));");
    c("arguments-extra-args-not-mapped", false, C,
      "function f(a) { arguments[1] = 'q'; return arguments.length; } console.log(f(1, 2));");
    c("arguments-callee", false, C,
      "function f() { return arguments.callee === f; } console.log(f());");
    c("arguments-callee-strict-throws", true, C,
      "function f() { var t = false; try { arguments.callee; } catch (e) { t = e instanceof TypeError; } return t; } console.log(f());");
    c("arguments-keys-names", false, C,
      "function f(a, b) { return [Object.keys(arguments), Object.getOwnPropertyNames(arguments)]; } console.log(f(1, 2));");
    c("arguments-length-write", false, C,
      "function f() { arguments.length = 9; return arguments.length; } console.log(f(1, 2));");
    c("arguments-defineproperty-value", false, C,
      "function f(a) { Object.defineProperty(arguments, '0', { value: 5 }); return [a, arguments[0]]; } console.log(f(1));");
    c("arguments-defineproperty-unwritable-unmaps", false, C,
      "function f(a) { Object.defineProperty(arguments, '0', { writable: false }); a = 9; return arguments[0]; } console.log(f(1));");
    c("arguments-tostring-tag", false, C,
      "function f() { return Object.prototype.toString.call(arguments); } console.log(f());");
    c("arguments-fewer-args-than-params", false, C,
      "function f(a, b, c) { b = 5; return [arguments.length, arguments[1], '1' in arguments ? 'has1' : 'no1', '2' in arguments]; } console.log(f(1, 2));");

    // ---- call / apply / bind ---------------------------------------------
    c("call-apply-basics", false, C,
      "function f(a, b) { return this.x + a + b; }\n\
       console.log(f.call({ x: 1 }, 2, 3), f.apply({ x: 1 }, [2, 3]), isNaN(f.apply({ x: 10 })), isNaN(f.apply({ x: 10 }, null)));");
    c("apply-array-like", false, C,
      "function f() { return arguments.length; } console.log(f.apply(null, { length: 3, 0: 'a' }));");
    c("apply-non-object-typeerror", false, C,
      "function f() {} var t = false; try { f.apply(null, 5); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("bind-surface", false, C,
      "function f(a, b, c) { return [this.x, a, b, c].join('-'); }\n\
       var g = f.bind({ x: 'X' }, 1);\n\
       console.log(g(2, 3), g.name, g.length, g.prototype === undefined, typeof g);");
    c("bind-construct-instanceof", false, C,
      "function T(a) { this.a = a; } var B = T.bind(null, 5); var t = new B();\n\
       console.log(t.a, t instanceof T, t instanceof B, t.constructor === T);");
    c("bind-of-bind", false, C,
      "function f(a, b) { return [a, b]; } var g = f.bind(null, 1).bind(null, 2);\n\
       console.log(g(3), g.name, g.length);");
    c("call-bind-uncurry", false, C,
      "var hop = Function.prototype.call.bind(Object.prototype.hasOwnProperty);\n\
       console.log(hop({ z: 1 }, 'z'), hop({}, 'z'), hop.name, hop.length);");
    c("bind-projection", false, C,
      "function fn(a) {} console.log(fn.bind(null));");

    // ---- Math -------------------------------------------------------------
    c("math-integer-ops", false, C,
      "console.log(Math.pow(2, 32) - 1, Math.pow(2, 10), Math.pow(3, 5), Math.pow(2, -2), Math.pow(-2, 3));");
    c("math-pow-specials", false, C,
      "console.log(Math.pow(NaN, 0), Math.pow(0, -1), Math.pow(-0, -1), Math.pow(-0, 3), Math.pow(1, Infinity), Math.pow(-2, 0.5));");
    c("math-floor-ceil-trunc-abs-sign", false, C,
      "console.log(Math.floor(1.5), Math.floor(-1.5), Math.ceil(-1.5), Math.ceil(1.2), Math.abs(-3), Math.trunc(-1.9), Math.sign(-4), Math.sign(0), 1 / Math.sign(-0));");
    c("math-round", false, C,
      "console.log(Math.round(2.5), Math.round(-2.5), Math.round(0.5), 1 / Math.round(-0.5), Math.round(0.49999999999999994), Math.round(NaN));");
    c("math-sqrt", false, C,
      "console.log(Math.sqrt(9), Math.sqrt(2), Math.sqrt(-1), 1 / Math.sqrt(-0));");
    c("math-min-max", false, C,
      "console.log(Math.max(1, 2, NaN), Math.max(-0, 0), 1 / Math.min(0, -0), Math.max(), Math.min(), Math.max(1, '3', true));");
    c("math-constants", false, C,
      "console.log(Math.PI, Math.E, Math.SQRT2, Math.LN2, Math.LOG10E);");
    c("math-coercion-order", false, C,
      "var log = []; function n(name, v) { return { valueOf: function () { log.push(name); return v; } }; }\n\
       Math.max(n('a', 1), n('b', 2), n('c', NaN));\n\
       console.log(log);");
    c("math-pow-inexact-refuses", false, R, "console.log(Math.pow(3, 40));");
    c("math-sin-refuses", false, R, "console.log(Math.sin(1));");

    // ---- template literals ------------------------------------------------
    c("template-basic", false, C,
      "var x = 5; console.log(`a${x}b${1 + 2}c`, `plain`, ``);");
    c("template-coercion", false, C,
      "var o = { toString: function () { return 'T'; } };\n\
       console.log(`v=${o}`, `n=${-0}`, `u=${undefined}`, `nl=${null}`);");
    c("template-multiline", false, C,
      "console.log(`l1\nl2${'q'}\\n\\`tick`);");
    c("template-nested", false, C,
      "var a = 1; console.log(`x${`y${a}`}z`);");

    // ---- String.prototype -------------------------------------------------
    c("string-charat-charcode", false, C,
      "var s = 'Hello'; console.log(s.charAt(0), s.charAt(-1) === '', s.charAt(9) === '', s.charCodeAt(1), isNaN(s.charCodeAt(99)));");
    c("string-indexof-lastindexof", false, C,
      "var s = 'Hello World'; console.log(s.indexOf('o'), s.indexOf('o', 5), s.indexOf(''), s.indexOf('', 3), s.indexOf('zz'), s.lastIndexOf('o'), s.lastIndexOf('o', 5), 'aaa'.lastIndexOf('aa'));");
    c("string-slice-substring", false, C,
      "var s = 'Hello'; console.log(s.slice(1, 4), s.slice(-3), s.slice(3, 1) === '', s.substring(4, 1), s.substring(-2, 2), s.substring(1));");
    c("string-split", false, C,
      "console.log('a,b,,c'.split(','), 'abc'.split(''), ''.split(','), ''.split(''), 'ab'.split('b'), 'aaa'.split('aa'), 'abc'.split('x'), 'a1b2c'.split(1));");
    c("string-split-limit-undefined", false, C,
      "console.log('a,b,c'.split(',', 2), 'a,b'.split(',', 0), 'abc'.split('', -1), 'ab'.split(undefined), 'ab'.split());");
    c("string-replace", false, C,
      "console.log('aXbXc'.replace('X', '-'), 'abc'.replace('x', '-'), 'aXb'.replace('X', '[$&][$`][$\\'][$$][$z]'),\n\
       'abc'.replace('b', function (m, p, s) { return m + p + s; }));");
    c("string-trim", false, C,
      "console.log('  a b \\t\\n'.trim(), '\\u00a0x\\u3000'.trim(), '\\u2028q\\u2029'.trim());");
    c("string-case-ascii", false, C,
      "console.log('AbC0!'.toLowerCase(), 'AbC0!'.toUpperCase());");
    c("string-tostring-valueof", false, C,
      "var s = 'q'; console.log(s.toString(), s.valueOf() === s, String.prototype.charAt.call(123, 1));");
    c("string-methods-on-this-coercion", false, C,
      "console.log(String.prototype.indexOf.call(12345, '3'), String.prototype.slice.call(true, 1));");
    c("string-tostring-wrong-this-typeerror", false, C,
      "var t = false; try { String.prototype.toString.call(5); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("string-case-nonascii-refuses", false, R, "console.log('\\u00e9'.toUpperCase());");
    c("string-replace-dollar-digit-refuses", false, R,
      "console.log('ab'.replace('b', '$1'));");

    // ---- Array.prototype additions ----------------------------------------
    c("array-lastindexof-includes", false, C,
      "var a = [3, 1, 3]; console.log(a.lastIndexOf(3), a.lastIndexOf(3, -2), a.lastIndexOf(9), a.includes(3), a.includes(9), [NaN].includes(NaN), [NaN].indexOf(NaN), [-0].includes(0));");
    c("array-lastindexof-empty-poison", false, C,
      "var p = { valueOf: function () { throw new Error('poison'); } };\n\
       console.log([].lastIndexOf(2, p), [].includes(2, p));");
    c("array-shift-unshift", false, C,
      "var a = [1, 2, 3]; var s = a.shift(); var u = a.unshift('x', 'y');\n\
       console.log(s, u, a);");
    c("array-shift-empty", false, C,
      "var a = []; console.log(a.shift() === undefined, a.length);");
    c("array-filter-every-some-find", false, C,
      "var a = [1, 2, 3, 4];\n\
       console.log(a.filter(function (v) { return v % 2 === 0; }),\n\
       a.every(function (v) { return v > 0; }), a.some(function (v) { return v > 3; }),\n\
       a.find(function (v) { return v > 2; }), a.findIndex(function (v) { return v > 2; }),\n\
       a.find(function () { return false; }) === undefined);");
    c("array-reduce", false, C,
      "console.log([1, 2, 3].reduce(function (a, b) { return a + b; }),\n\
       [1, 2, 3].reduce(function (a, b) { return a + b; }, 10),\n\
       [1, 2, 3].reduceRight(function (a, b) { return a - b; }),\n\
       ['a', 'b'].reduceRight(function (a, b) { return a + b; }));");
    c("array-reduce-empty-typeerror", false, C,
      "var t = false; try { [].reduce(function () {}); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("array-reduce-holes", false, C,
      "var a = [1]; a.length = 3; a.push(4);\n\
       console.log(a.reduce(function (x, y) { return x + '|' + y; }));");
    c("array-filter-species-null-ctor", false, C,
      "var a = [1, 2]; a.constructor = null; var t = false;\n\
       try { a.filter(function () { return true; }); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("array-shift-inherited", false, C,
      "Array.prototype[1] = 9; var a = [0]; a.length = 2;\n\
       var s = a.shift();\n\
       console.log(s, a, a.hasOwnProperty('0'));\n\
       delete Array.prototype[1];");

    // ---- generic array-like receivers ------------------------------------
    c("array-methods-on-array-like", false, C,
      "var o = { length: 3, 0: 'a', 2: 'c' };\n\
       console.log(Array.prototype.indexOf.call(o, 'c'),\n\
       Array.prototype.slice.call(o),\n\
       Array.prototype.join.call(o, '-'),\n\
       Array.prototype.includes.call(o, undefined),\n\
       Array.prototype.lastIndexOf.call(o, 'a'));");
    c("array-slice-call-arguments", false, C,
      "function f() { return Array.prototype.slice.call(arguments); }\n\
       console.log(f(1, 'x', true));");
    c("array-push-on-plain-object", false, C,
      "var o = { length: 2 }; var r = Array.prototype.push.call(o, 'p', 'q');\n\
       console.log(r, o.length, o[2], o[3], o.hasOwnProperty('0'));");
    c("array-pop-shift-on-plain-object", false, C,
      "var o = { length: 2, 0: 'a', 1: 'b' };\n\
       console.log(Array.prototype.pop.call(o), o.length,\n\
       Array.prototype.shift.call(o), o.length, o.hasOwnProperty('0'));");
    c("array-foreach-array-like-length-coercion", false, C,
      "var n = 0; var o = { get length() { n++; return 2; }, 0: 'a', 1: 'b' };\n\
       var r = []; Array.prototype.forEach.call(o, function (v, i) { r.push(i, v); });\n\
       console.log(n, r);");
    c("array-map-array-like-returns-array", false, C,
      "var o = { length: 2, 0: 1, 1: 2 };\n\
       var m = Array.prototype.map.call(o, function (v) { return v * 10; });\n\
       console.log(Array.isArray(m), m);");
    c("array-method-null-receiver-typeerror", false, C,
      "var t = false; try { Array.prototype.indexOf.call(null, 1); } catch (e) { t = e instanceof TypeError; }\n\
       var u = false; try { [].forEach.call(undefined, function () {}); } catch (e) { u = e instanceof TypeError; }\n\
       console.log(t, u);");
    c("array-length-coerces-before-callable-check", false, C,
      "var log = []; var o = { get length() { log.push('len'); return 0; } };\n\
       var t = false; try { Array.prototype.map.call(o, 'nope'); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t, log);");
    c("array-reduce-arguments", false, C,
      "function f() { return Array.prototype.reduce.call(arguments, function (a, b) { return a + b; }); }\n\
       console.log(f(1, 2, 3));");

    // ---- classic lexical for loops ----------------------------------------
    c("for-let-per-iteration-closures", false, C,
      "var fs = []; for (let i = 0; i < 3; i++) { fs.push(function () { return i; }); }\n\
       console.log(fs[0](), fs[1](), fs[2]());");
    c("for-let-body-mutation-carries", false, C,
      "var r = []; for (let i = 0; i < 4; i++) { if (i === 1) i = 2; r.push(i); }\n\
       console.log(r);");
    c("for-let-head-tdz", false, C,
      "var t = false; try { for (let a = b, b = 1; false;) {} } catch (e) { t = e instanceof ReferenceError; }\n\
       console.log(t);");
    c("for-const-loop", false, C,
      "var n = 0; for (const c = 5; n < 2; n++) { if (n === 0) { var seen = c; } }\n\
       console.log(n, seen);");
    c("for-const-assign-typeerror", false, C,
      "var t = false; for (const c = 1; ;) { try { c = 2; } catch (e) { t = e instanceof TypeError; } break; }\n\
       console.log(t);");
    c("for-let-multi-decl", false, C,
      "var r = []; for (let a = 0, b = 10; a < 2; a++) { b--; r.push(a + ':' + b); }\n\
       console.log(r);");
    c("for-let-shadowing-outer", false, C,
      "let i = 'outer'; var r = []; for (let i = 0; i < 2; i++) r.push(i);\n\
       console.log(r, i);");
    c("string-prototype-length", false, C,
      "console.log(String.prototype.length, 'abc'.length);");

    // ---- wrapper objects --------------------------------------------------
    c("string-wrapper-basics", false, C,
      "var s = new String('ab');\n\
       console.log(typeof s, s.length, s[0], s.charAt(1), s + '!', s == 'ab', s === 'ab',\n\
       Object.prototype.toString.call(s), s.toString(), s.valueOf() === 'ab');");
    c("string-wrapper-projection", false, C,
      "console.log(new String('hi'), new Number(5), new Boolean(false));");
    c("string-wrapper-own-surface", false, C,
      "var s = new String('ab'); s.x = 1;\n\
       console.log(Object.getOwnPropertyNames(s), Object.keys(s),\n\
       Object.getOwnPropertyDescriptor(s, '0'), delete s[0], delete s.x, s.hasOwnProperty('1'));");
    c("number-wrapper-arithmetic", false, C,
      "var n = new Number(41);\n\
       console.log(typeof n, n + 1, n == 41, n === 41, n.valueOf(), n.toString(),\n\
       Object.prototype.toString.call(n), Object.getOwnPropertyNames(n));");
    c("boolean-wrapper-truthiness", false, C,
      "var b = new Boolean(false);\n\
       console.log(b ? 'truthy' : 'falsy', b == false, b.valueOf(), b.toString(),\n\
       Object.prototype.toString.call(b));");
    c("wrapper-forin", false, C,
      "var ks = []; for (var k in new String('ab')) ks.push(k);\n\
       var kn = []; for (var j in new Number(5)) kn.push(j);\n\
       console.log(ks, kn);");
    c("object-primitive-toobject", false, C,
      "console.log(Object('ab'), Object(5) instanceof Number, Object(true).valueOf());");
    c("sloppy-this-primitive-wrapped", false, C,
      "function f() { return [typeof this, Object.prototype.toString.call(this), this == 'q']; }\n\
       console.log(f.call('q'));");
    c("array-methods-on-string-primitive", false, C,
      "console.log(Array.prototype.indexOf.call('abc', 'b'),\n\
       Array.prototype.slice.call('ab'),\n\
       Array.prototype.includes.call('abc', 'c'));");
    c("number-statics", false, C,
      "console.log(Number.MAX_SAFE_INTEGER, Number.MIN_VALUE, Number.EPSILON,\n\
       Number.POSITIVE_INFINITY, Number.isNaN(NaN), Number.isNaN('NaN'),\n\
       Number.isInteger(5), Number.isInteger(5.5), Number.isSafeInteger(9007199254740992),\n\
       Number.isFinite('5'), Number.isFinite(Infinity));");
    c("string-fromcharcode-fromcodepoint", false, C,
      "console.log(String.fromCharCode(72, 105), String.fromCharCode(65536 + 65),\n\
       String.fromCodePoint(128512), String.fromCharCode(), '' + String.fromCodePoint());");
    c("fromcodepoint-rangeerror", false, C,
      "var t = false; try { String.fromCodePoint(1.5); } catch (e) { t = e instanceof RangeError; }\n\
       var u = false; try { String.fromCodePoint(1114112); } catch (e) { u = e instanceof RangeError; }\n\
       console.log(t, u);");
    c("number-tostring-radix10-and-rangeerror", false, C,
      "var t = false; try { (5).toString === undefined; } catch (e) {}\n\
       var n = new Number(255);\n\
       var r = false; try { n.toString(37); } catch (e) { r = e instanceof RangeError; }\n\
       console.log(n.toString(), n.toString(10), r);");
    c("number-tostring-integer-radix", false, C,
      "console.log(new Number(255).toString(16), (0).toString(4), new Number(-33).toString(2),\n\
       new Number(NaN).toString(4), new Number(Infinity).toString(8), (35).toString(36),\n\
       Number.prototype.toString(4), Number.prototype == 0, Boolean.prototype.valueOf());");
    c("number-tostring-fractional-radix-refuses", false, R,
      "console.log((1.5).toString(16));");
    c("boolean-proto-valueof-typeerror", false, C,
      "var t = false; try { Boolean.prototype.valueOf.call(5); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("string-proto-tostring-on-proto", false, C,
      "console.log(String.prototype.toString.call(String.prototype) === '', '' + new String(''));");
    c("ctor-statics-resolve-through-chain", false, C,
      "console.log(Boolean.hasOwnProperty('prototype'), Number.hasOwnProperty('MAX_VALUE'),\n\
       Array.hasOwnProperty('isArray'), 'call' in Function);");

    // ---- Object.create / getPrototypeOf -----------------------------------
    c("object-create-null", false, C,
      "var o = Object.create(null); o.x = 1;\n\
       console.log(o, o.x, Object.getPrototypeOf(o), 'toString' in o === false);");
    c("object-create-proto-and-props", false, C,
      "var proto = { greet: function () { return 'hi'; } };\n\
       var o = Object.create(proto, { a: { value: 1, enumerable: true } });\n\
       console.log(o.greet(), o.a, Object.getPrototypeOf(o) === proto, Object.keys(o), o);");
    c("object-create-null-toprimitive-typeerror", false, C,
      "var o = Object.create(null); var t = false;\n\
       try { '' + o; } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("object-create-array-proto-forof", false, C,
      "var o = Object.create(Array.prototype); o.length = 2; o[0] = 'a'; o[1] = 'b';\n\
       var r = []; for (var v of o) r.push(v);\n\
       console.log(r, Array.isArray(o), Object.prototype.toString.call(o));");
    c("object-create-primitive-typeerror", false, C,
      "var t = false; try { Object.create(5); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("getprototypeof-identities", false, C,
      "function F() {}\n\
       console.log(Object.getPrototypeOf([]) === Array.prototype,\n\
       Object.getPrototypeOf(F) === Function.prototype,\n\
       Object.getPrototypeOf(new F()) === F.prototype,\n\
       Object.getPrototypeOf('s') === String.prototype,\n\
       Object.getPrototypeOf(5) === Number.prototype,\n\
       Object.getPrototypeOf(true) === Boolean.prototype,\n\
       Object.getPrototypeOf(Object.prototype));");
    c("getprototypeof-null-typeerror", false, C,
      "var t = false; try { Object.getPrototypeOf(null); } catch (e) { t = e instanceof TypeError; } console.log(t);");

    // ---- comma operator + elision -----------------------------------------
    c("comma-operator", false, C,
      "var log = []; function t(n) { log.push(n); return n; }\n\
       var r = (t(1), t(2), t(3));\n\
       console.log(r, log, (0, 'x'));");
    c("comma-in-for-head", false, C,
      "var r = []; for (var i = 0, j = 5; i < 2; i++, j--) r.push(i + ':' + j);\n\
       console.log(r);");
    c("array-elision", false, C,
      "var a = [, 1]; var b = [1, , 2]; var d = [1, , ];\n\
       console.log(a.length, a.hasOwnProperty('0'), b, b.length, d.length, [,].length, [,,].length);");
    c("elision-holes-in-methods", false, C,
      "var b = [1, , 2];\n\
       console.log(b.indexOf(undefined), b.includes(undefined), 1 in b);");

    // ---- s1b gate regressions ---------------------------------------------
    // Accessor (MethodDefinition) functions: no own `prototype`, not
    // constructors, no legacy caller/arguments own surface.
    c("accessor-fn-no-prototype", false, C,
      "var g = Object.getOwnPropertyDescriptor({ get f() {} }, 'f').get;\n\
       Object.defineProperty(g, 'prototype', { get: function () { return 42; } });\n\
       console.log(Object.getOwnPropertyNames(g), g.prototype, 'prototype' in g);");
    c("accessor-fn-not-a-constructor", false, C,
      "var g = Object.getOwnPropertyDescriptor({ get f() {} }, 'f').get;\n\
       var t = false; try { new g(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t, Object.getOwnPropertyNames(g));");
    // A parameter named `arguments` suppresses the arguments object (FDI
    // step 19): the identifier resolves to the parameter.
    c("arguments-param-shadows-object", false, C,
      "function f(arguments) { return arguments; }\n\
       function g(arguments) { arguments = 7; return arguments; }\n\
       console.log(f(42), typeof f(), g(1));");
    // for-of head is a single AssignmentExpression: a comma is a pinned
    // SyntaxError; the for-in head is a full Expression (comma legal).
    c("forof-head-comma-syntaxerror", false, C,
      "for (var x of [], []) {}");
    c("forof-head-comma-let-syntaxerror", false, C,
      "for (let x of [], []) {}");
    c("forin-head-comma-legal", false, C,
      "var n = 0; for (var k in [1], { a: 1 }) n++; console.log(n);");
    // `async of` lookahead restriction in the for-of head.
    c("forof-async-lhs-syntaxerror", false, C,
      "var async; for (async of [1]) ;");
    c("forof-async-member-lhs-legal", false, C,
      "var async = {}; var r = []; for (async.x of [1, 2]) r.push(async.x);\n\
       console.log(r);");

    // ---- pinned early SyntaxErrors ----------------------------------------
    c("anonymous-function-declaration-syntaxerror", false, C,
      "function () {}");
    c("bad-hex-escape-syntaxerror", false, C,
      "'\\xZZ';");

    // ---- classes ----------------------------------------------------------
    c("class-basics", false, C,
      "class A { m() { return 1; } }\n\
       var a = new A();\n\
       console.log(a.m(), typeof A, A.name, A.length, A.prototype.constructor === A,\n\
       a instanceof A, Object.getPrototypeOf(a) === A.prototype, a);");
    c("class-tdz-and-call-typeerror", false, C,
      "var t = false; try { new B(); } catch (e) { t = e instanceof ReferenceError; }\n\
       class B {}\n\
       var u = false; try { B(); } catch (e) { u = e instanceof TypeError; }\n\
       console.log(t, u);");
    c("class-method-surface", false, C,
      "class A { m(a, b) {} }\n\
       var d = Object.getOwnPropertyDescriptor(A.prototype, 'm');\n\
       var t = false; try { new d.value(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(d.writable, d.enumerable, d.configurable, d.value.name, d.value.length,\n\
       d.value.prototype === undefined, t, Object.getOwnPropertyNames(A.prototype));");
    c("class-ctor-surface", false, C,
      "class A { constructor(x, y) {} }\n\
       var dp = Object.getOwnPropertyDescriptor(A, 'prototype');\n\
       console.log(A.length, dp.writable, dp.enumerable, dp.configurable,\n\
       Object.getOwnPropertyNames(A),\n\
       Object.getOwnPropertyDescriptor(A.prototype, 'constructor').enumerable);");
    c("class-accessors", false, C,
      "class A { get x() { return this._x; } set x(v) { this._x = v * 2; } }\n\
       var a = new A(); a.x = 21;\n\
       var d = Object.getOwnPropertyDescriptor(A.prototype, 'x');\n\
       console.log(a.x, d.get.name, d.set.name, d.enumerable, d.configurable, a);");
    c("class-static-members", false, C,
      "class A { static sm() { return this === A; } static get g() { return 7; } }\n\
       console.log(A.sm(), A.g, A.hasOwnProperty('sm'),\n\
       Object.getOwnPropertyDescriptor(A, 'sm').enumerable);");
    c("class-derived-super", false, C,
      "class B { constructor(v) { this.b = v; } m() { return 'B' + this.b; } }\n\
       class D extends B { constructor() { super(9); this.d = 1; } m() { return 'D' + super.m(); } }\n\
       var d = new D();\n\
       console.log(d.m(), d.b, d.d, d instanceof B, d instanceof D,\n\
       Object.getPrototypeOf(D.prototype) === B.prototype, Object.getPrototypeOf(D) === B, d);");
    c("class-default-ctors", false, C,
      "class B { constructor(a, b) { this.sum = a + b; } }\n\
       class D extends B {}\n\
       var d = new D(40, 2);\n\
       console.log(d.sum, d instanceof D, new (class {})() instanceof Object);");
    c("class-this-tdz-in-derived", false, C,
      "class B {}\n\
       class D extends B { constructor() { var t = false;\n\
       try { this; } catch (e) { t = e instanceof ReferenceError; }\n\
       super(); console.log(t, this instanceof D); } }\n\
       new D();");
    c("class-super-twice-referenceerror", false, C,
      "class B {}\n\
       class D extends B { constructor() { super(); var t = false;\n\
       try { super(); } catch (e) { t = e instanceof ReferenceError; }\n\
       console.log(t); } }\n\
       new D();");
    c("class-derived-no-super-referenceerror", false, C,
      "class B {}\n\
       class D extends B { constructor() {} }\n\
       var t = false; try { new D(); } catch (e) { t = e instanceof ReferenceError; }\n\
       console.log(t);");
    c("class-derived-return-rules", false, C,
      "class B {}\n\
       class R1 extends B { constructor() { return { q: 1 }; } }\n\
       class R2 extends B { constructor() { super(); return undefined; } }\n\
       class R3 extends B { constructor() { super(); return 5; } }\n\
       var t = false; try { new R3(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(new R1().q, new R2() instanceof R2, t);");
    c("class-extends-null", false, C,
      "class N extends null {}\n\
       var t = false; try { new N(); } catch (e) { t = e instanceof TypeError; }\n\
       class N2 extends null { constructor() { return Object.create(null); } }\n\
       var o = new N2();\n\
       console.log(t, Object.getPrototypeOf(N.prototype), Object.getPrototypeOf(o),\n\
       Object.getPrototypeOf(N) === Function.prototype);");
    c("class-instance-fields", false, C,
      "class P { x = 1; y = this.x + 1; z; f = function () {}; }\n\
       var p = new P();\n\
       var d = Object.getOwnPropertyDescriptor(p, 'x');\n\
       console.log(p.x, p.y, p.z === undefined, p.f.name, d.writable, d.enumerable,\n\
       d.configurable, Object.keys(p), p.hasOwnProperty('f'), P.prototype.hasOwnProperty('x'));");
    c("class-static-fields", false, C,
      "class S { static a = 1; static b = this.a + 1; static c = S.name; }\n\
       console.log(S.a, S.b, S.c, Object.getOwnPropertyDescriptor(S, 'a').enumerable);");
    c("class-computed-keys-order", false, C,
      "var log = []; function k(n) { log.push(n); return n; }\n\
       class A { [k('m')]() { return 1; } static [k('s')] = 2; [k('f')] = 3; }\n\
       var a = new A();\n\
       console.log(log, a.m(), A.s, a.f);");
    c("class-expression-names", false, C,
      "var C = class {};\n\
       var D = class E { probe() { return E === D; } };\n\
       var t = false;\n\
       var F = class G { m() { try { G = 1; } catch (e) { t = e instanceof TypeError; } } };\n\
       new F().m();\n\
       console.log(C.name, D.name, new D().probe(), t);");
    c("class-super-assignment", false, C,
      "class B {}\n\
       class D extends B { m() { super.x = 5; return [this.x, this.hasOwnProperty('x'), B.prototype.x === undefined]; } }\n\
       console.log(new D().m());");
    c("class-super-static", false, C,
      "class B { static s() { return 'B'; } }\n\
       class D extends B { static s() { return 'D' + super.s(); } }\n\
       console.log(D.s());");
    c("class-super-getter-receiver", false, C,
      "class B { get g() { return this.v * 2; } }\n\
       class D extends B { constructor() { super(); this.v = 21; } get g() { return super.g; } }\n\
       console.log(new D().g);");
    c("class-extends-error", false, C,
      "class E extends Error { constructor(m) { super(m); this.extra = 1; } }\n\
       var e = new E('boom');\n\
       console.log(e instanceof E, e instanceof Error, e.message, e.extra, e.name,\n\
       Object.getPrototypeOf(E.prototype) === Error.prototype);\n\
       throw new E('final');");
    c("class-extends-object", false, C,
      "class O extends Object {}\n\
       var o = new O(123);\n\
       console.log(o instanceof O, Object.getPrototypeOf(o) === O.prototype, Object.keys(o));");
    c("class-computed-constructor-key", false, C,
      "class X { ['constructor']() { return 1; } }\n\
       var x = new X();\n\
       console.log(x.constructor === X, x.constructor.name, x['constructor']() === undefined || true);");
    c("class-heritage-typeerrors", false, C,
      "var t1 = false; try { class A extends 5 {} } catch (e) { t1 = e instanceof TypeError; }\n\
       var t2 = false; try { class B extends ({}) {} } catch (e) { t2 = e instanceof TypeError; }\n\
       var t3 = false; try { class C extends Math.floor {} } catch (e) { t3 = e instanceof TypeError; }\n\
       console.log(t1, t2, t3);");
    c("class-decl-binding-mutable", false, C,
      "class C {} C = 5; console.log(C);");
    c("class-field-init-throws", false, C,
      "class F { x = (function () { throw new RangeError('f'); })(); }\n\
       var t = false; try { new F(); } catch (e) { t = e instanceof RangeError; }\n\
       console.log(t);");
    c("class-methods-not-hoisted-props", false, C,
      "class A { m() { return this.n(); } n() { return 42; } }\n\
       console.log(new A().m(), 'm' in A.prototype, Object.keys(A.prototype));");
    c("class-extends-array-refuses", false, R,
      "class A extends Array {} console.log(new A());");
    // Pinned class early errors.
    c("class-duplicate-ctor-syntaxerror", false, C,
      "class A { constructor() {} constructor() {} }");
    c("class-anonymous-decl-syntaxerror", false, C,
      "class {}");
    c("class-static-prototype-syntaxerror", false, C,
      "class A { static prototype() {} }");
    c("class-field-constructor-syntaxerror", false, C,
      "class A { constructor = 1; }");
    c("class-getter-params-syntaxerror", false, C,
      "class A { get x(v) {} }");
    c("class-arguments-in-field-syntaxerror", false, C,
      "class A { x = arguments; }");
    c("super-outside-method-syntaxerror", false, C,
      "super.x;");
    c("super-call-in-base-method-syntaxerror", false, C,
      "class A { m() { super(); } }");

    // ---- object shorthand methods + computed keys -------------------------
    c("object-shorthand-methods", false, C,
      "var o = { m(a) { return this.x + a; }, x: 40 };\n\
       var d = Object.getOwnPropertyDescriptor(o, 'm');\n\
       var t = false; try { new o.m(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(o.m(2), d.writable, d.enumerable, d.configurable, o.m.name, o.m.length,\n\
       o.m.prototype === undefined, t, o);");
    c("object-method-super", false, C,
      "var o = { q: 1, has(k) { return super.hasOwnProperty.call(this, k); },\n\
       tag() { return super.toString(); } };\n\
       console.log(o.has('q'), o.has('zz'), o.tag(),\n\
       o.missingSuper === undefined);");
    c("object-method-super-home-stays", false, C,
      "var a = { m() { return super.isPrototypeOf === Object.prototype.isPrototypeOf; } };\n\
       var extracted = a.m; var b = { f: extracted };\n\
       console.log(a.m(), b.f());");
    c("object-accessor-super", false, C,
      "var base = { get v() { return 'base'; } };\n\
       var o = Object.create(base);\n\
       var o2 = { get v() { return 'own:' + this.tag; }, tag: 'T' };\n\
       console.log(o.v, o2.v, Object.getOwnPropertyDescriptor(o2, 'v').get.name);");
    c("object-computed-keys", false, C,
      "var log = []; function k(n) { log.push(n); return n; }\n\
       var o = { [k('a')]: 1, [k('b')](x) { return x * 2; }, get [k('c')]() { return 3; } };\n\
       console.log(o.a, o.b(2), o.c, log, o.b.name, Object.keys(o), o);");
    c("object-computed-key-coercion", false, C,
      "var o = { [1 + 1]: 'two', [{ toString: function () { return 'q'; } }]: 'obj' };\n\
       console.log(o[2], o.q, Object.getOwnPropertyNames(o));");
    c("object-computed-proto-is-ordinary", false, C,
      "var o = { ['__proto__']: 5 };\n\
       console.log(o.hasOwnProperty('__proto__'), o['__proto__'], Object.keys(o));");
    c("object-computed-anonymous-fn-name", false, C,
      "var o = { [String.fromCharCode(102)]: function () {}, ['c']: class {} };\n\
       console.log(o.f.name, o.c.name);");
    c("object-method-strict-prologue", false, C,
      "var o = { m() { 'use strict'; var t = false; try { undefined_global_q = 1; } catch (e) { t = e instanceof ReferenceError; } return t; } };\n\
       console.log(typeof o.m);");
    c("object-method-duplicate-keys", false, C,
      "var o = { m() { return 1; }, m: 5, n: 1, get n() { return 2; } };\n\
       console.log(o.m, o.n, Object.keys(o));");

    // ---- destructuring ----------------------------------------------------
    c("destr-object-binding-basics", false, C,
      "var log = []; function k(n) { log.push(n); return n; }\n\
       var src = { a: 1, b: { c: 3 }, f: 6, x: 'X' };\n\
       var { a, b: { c }, d = 4, [k('x')]: e, 'f': f } = src;\n\
       console.log(a, c, d, e, f, log);");
    c("destr-null-typeerror-before-keys", false, C,
      "var n = 0; function poison() { n++; return 'k'; }\n\
       var t = false; try { var { [poison()]: v } = null; } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t, n);");
    c("destr-array-binding", false, C,
      "var [a, , b = 20, [c]] = [1, 2, undefined, [4], 5];\n\
       var [x, ...r] = [7, 8, 9];\n\
       console.log(a, b, c, x, r);");
    c("destr-array-from-string-and-arguments", false, C,
      "var [s1, s2, ...sr] = 'a\\ud83d\\ude00b';\n\
       function f() { var [p, q] = arguments; return [p, q]; }\n\
       console.log(s1, s2, sr, f(10, 20));");
    c("destr-array-non-iterable-typeerror", false, C,
      "var t1 = false; try { var [q] = {}; } catch (e) { t1 = e instanceof TypeError; }\n\
       var t2 = false; try { var [w] = 5; } catch (e) { t2 = e instanceof TypeError; }\n\
       var t3 = false; try { var [z] = null; } catch (e) { t3 = e instanceof TypeError; }\n\
       console.log(t1, t2, t3);");
    c("destr-assignment-patterns", false, C,
      "var x, y, o = {}; var r = ({ a: x, b: y = 9, c: o.p } = { a: 1, c: 3 });\n\
       var m = {}; [m.u, , m.v] = [10, 11, 12];\n\
       console.log(x, y, o.p, r.a, m.u, m.v);");
    c("destr-assignment-ref-before-value-order", false, C,
      "var log = []; var o = {};\n\
       function tgt(n) { log.push('ref' + n); return o; }\n\
       function val(n) { log.push('val' + n); return n; }\n\
       [tgt(1).a, tgt(2).b] = [val(1), val(2)];\n\
       console.log(log, o.a, o.b);");
    c("destr-object-rest", false, C,
      "var { a, ...rest } = { a: 1, b: 2, c: 3 };\n\
       var d = Object.getOwnPropertyDescriptor(rest, 'b');\n\
       console.log(a, rest, d.writable, d.enumerable, d.configurable, rest.hasOwnProperty('a'));");
    c("destr-let-const", false, C,
      "let { p, q = 2 } = { p: 1 }; const [r1, r2] = [3, 4];\n\
       var t = false; try { r1 = 9; } catch (e) { t = e instanceof TypeError; }\n\
       console.log(p, q, r1, r2, t);");
    c("destr-forof-forin-heads", false, C,
      "var out = [];\n\
       for (const { x, y = 0 } of [{ x: 1 }, { x: 2, y: 3 }]) out.push(x + ':' + y);\n\
       for (var [ch] in { ab: 1 }) out.push(ch);\n\
       var k1, k2; for ([k1, k2] of [['a', 'b']]) out.push(k1 + k2);\n\
       console.log(out);");
    c("destr-catch-patterns", false, C,
      "var got;\n\
       try { throw { code: 42, msg: 'x' }; } catch ({ code, msg = 'd' }) { got = code + msg; }\n\
       var arr; try { throw [1, 2]; } catch ([a, b]) { arr = a + b; }\n\
       console.log(got, arr);");
    c("destr-params", false, C,
      "function f({ a, b = 2 }, [c] = [30], ...rest) { return [a, b, c, rest]; }\n\
       console.log(f({ a: 1 }), f({ a: 9, b: 8 }, [7], 6, 5), f.length, f.name);");
    c("destr-params-arguments-unmapped", false, C,
      "function g([a]) { a = 99; return arguments[0]; }\n\
       console.log(g([5]), g.length);");
    c("destr-named-evaluation", false, C,
      "var { anon = function () {} } = {};\n\
       var [arrw = () => {}] = [];\n\
       console.log(anon.name, arrw.name);");
    // Declared slice restriction: closures inside PARAMETER initializers
    // (the separate parameter scope) refuse.
    c("param-closure-default-refuses", false, R,
      "function h(cb = function () {}) { return cb.name; } console.log(h());");
    c("destr-default-skips-non-undefined", false, C,
      "var n = 0; function d() { n++; return 'D'; }\n\
       var { a = d(), b = d() } = { a: null, b: undefined };\n\
       console.log(a, b, n);");
    c("cover-init-outside-pattern-syntaxerror", false, C,
      "({ a = 1 });");
    c("literal-spread-refuses", false, R,
      "var a = [1, ...[2]]; console.log(a);");
    c("destr-proto-dup-pattern-refuses", false, R,
      "var v = {}, x, y; ({ __proto__: x, __proto__: y } = v); console.log('n');");

    // ---- arrow functions --------------------------------------------------
    c("arrow-basics", false, C,
      "var f = x => x * 2;\n\
       var g = (a, b) => { return a + b; };\n\
       var h = () => 42;\n\
       var t = false; try { new f(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(f(21), g(40, 2), h(), f.name, f.length, g.length,\n\
       f.prototype === undefined, t, typeof f, f);");
    c("arrow-lexical-this", false, C,
      "var o = { v: 42, m: function () { var a = () => this.v; return a(); } };\n\
       var esc = o.m;\n\
       var obj2 = { v: 7, m2: function () { return (() => (() => this.v)())(); } };\n\
       console.log(o.m(), obj2.m2());");
    c("arrow-lexical-arguments", false, C,
      "function f() { var a = () => arguments.length + ':' + arguments[0]; return a(); }\n\
       console.log(f(9, 8, 7));");
    c("arrow-params-patterns", false, C,
      "var f = ({ a, b = 2 }, ...r) => [a, b, r];\n\
       var g = ([x, y] = [1, 2]) => x + y;\n\
       console.log(f({ a: 1 }, 5, 6), g(), g([10, 20]));");
    c("arrow-iife-and-nesting", false, C,
      "console.log(((a, b) => a + b)(40, 2), (x => y => x + y)(1)(2));");
    c("arrow-in-class-field", false, C,
      "class A { tag = 'T'; f = () => this.tag; }\n\
       var a = new A(); var ext = a.f;\n\
       console.log(a.f(), ext());");
    c("arrow-in-method-super", false, C,
      "class B { m() { return 'B'; } }\n\
       class D extends B { m() { var a = () => super.m() + '+D'; return a(); } }\n\
       console.log(new D().m());");
    c("arrow-strict-body-and-named-eval", false, C,
      "var named = () => {}; var o = { cb: x => x };\n\
       console.log(named.name, o.cb.name);");
    c("arrow-comma-body-precedence", false, C,
      "var fs = []; for (let i = 0; i < 2; i++) fs.push(() => i);\n\
       console.log(fs[0](), fs[1]());");

    // ---- escaped identifiers ----------------------------------------------
    c("escident-basics", false, C,
      "var \\u0061 = 5; var q\\u0075x = 2;\n\
       console.log(a + 1, qux, \\u0061 * q\\u0075x);");
    c("escident-member-reserved", false, C,
      "var o = {}; o.\\u0069f = 1; o['var'] = 2;\n\
       console.log(o.if, o.\\u0076ar, o['if']);");
    c("escident-reserved-syntaxerror", false, C,
      "\\u0069f (true) {}");
    c("escident-let-sloppy-legal", false, C,
      "var l\\u0065t = 1; var aw\\u0061it = 2; console.log(l\\u0065t + aw\\u0061it);");
    c("escident-let-strict-syntaxerror", true, C,
      "var l\\u0065t = 1;");
    c("escident-arguments-in-function", false, C,
      "function f() { return \\u0061rguments.length; }\n\
       console.log(f(1, 2, 3));");
    // Non-ASCII identifiers now lex via the exact Unicode 16.0.0
    // ID_Start/ID_Continue tables: valid ones evaluate, invalid code points
    // (¡ = ¡, a combining mark as start) are exact SyntaxErrors.
    c("escident-nonascii-accepts", false, C,
      "var \\u00e9 = 1; console.log(\\u00e9);");
    c("ident-raw-nonascii-accepts", false, C,
      "var café = 40; var \u{3b1} = 2; console.log(café + \u{3b1});");
    c("escident-nonascii-nonid-syntaxerror", false, C,
      "var \\u00a1 = 1;");
    c("ident-combining-mark-start-syntaxerror", false, C,
      "var \\u0300 = 1;");
    c("dup-bound-names-syntaxerrors", false, C,
      "for (let [x, x] in {}) ;");
    c("dup-bound-names-let-decl", false, C,
      "let [y, y] = [];");
    c("dup-bound-names-catch", false, C,
      "try {} catch ([z, z]) {}");
    c("dup-bound-names-var-legal", false, C,
      "var [w, w] = [1, 2]; console.log(w);");
    // s1c-gate regressions: parenthesized literals lose pattern eligibility;
    // arrows are not LeftHandSideExpressions; method params are super-legal
    // method code; escaped names in declaration positions.
    c("paren-literal-target-syntaxerror", false, C, "({}) = 1;");
    c("paren-array-target-syntaxerror", false, C, "([]) = [];");
    c("arrow-as-target-syntaxerror", false, C, "() => ({}) = 1;");
    c("paren-pattern-assign-still-legal", false, C,
      "var x; var r = ({ a: x } = { a: 5 });\n\
       console.log(x, r.a);");
    c("arrow-heritage-syntaxerror", false, C, "class C extends () => {} {}");
    c("ident-arrow-heritage-syntaxerror", false, C,
      "var f; class C extends f => 1 {}");
    c("paren-arrow-heritage-runtime-typeerror", false, C,
      "var t = false; try { class C extends (x => 1) {} } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("super-in-method-param-default", false, C,
      "var obj = { method(x = super.toString) { return x; } };\n\
       obj.toString = null;\n\
       console.log(obj.method() === Object.prototype.toString, obj.method(5));");
    c("escaped-fn-and-class-names", false, C,
      "function \\u005f\\u005ff() { return 'esc'; }\n\
       class aw\\u0061it { m() { return 1; } }\n\
       var l\\u0065t = 2;\n\
       console.log(__f(), new aw\\u0061it().m(), l\\u0065t, aw\\u0061it.name);");
    c("paren-ident-no-named-evaluation", false, C,
      "var fn; (fn) = function () {};\n\
       var g; g = function () {};\n\
       var h; (h) = () => {};\n\
       console.log(fn.name, g.name, h.name, fn.name === '');");
    c("paren-ident-refs-stay-live", false, C,
      "var x = 1; (x) = 2; (x)++; var o = { p: 1 };\n\
       var r = delete (o.p);\n\
       for ((x) in { k: 1 }) ;\n\
       console.log(x, r, o.p === undefined);");
    c("escaped-object-keys", false, C,
      "var o = { \\u0061b: 1, get \\u0063() { return 2; } };\n\
       class K { \\u006d() { return 3; } }\n\
       console.log(o.ab, o.c, new K().m());");

    // ---- misc integration -------------------------------------------------
    c("frozen-fn-length-name", false, C,
      "function f(a, b) {}\n\
       var d1 = Object.getOwnPropertyDescriptor(f, 'length');\n\
       var d2 = Object.getOwnPropertyDescriptor(f, 'name');\n\
       console.log(d1, d2);");
    c("global-function-delete", false, C,
      "var o = { n: 1 }; Object.defineProperty(o, 'h', { value: 2, enumerable: true });\n\
       var ks = []; for (var k in o) ks.push(k);\n\
       console.log(ks, Object.keys(o));");
    c("propertyhelper-style-walk", false, C,
      "var obj = { p: 1 };\n\
       var d = Object.getOwnPropertyDescriptor(obj, 'p');\n\
       var hop = Function.prototype.call.bind(Object.prototype.hasOwnProperty);\n\
       var stringCheck = false;\n\
       for (var x in obj) { if (x === 'p') { stringCheck = true; break; } }\n\
       console.log(d.value, d.writable, d.enumerable, d.configurable, hop(obj, 'p'), stringCheck);");

    // ---- generators (§27.3-27.5) -----------------------------------------
    c("gen-consecutive-yields", false, C,
      "function* g() { yield 1; yield 2; }\n\
       var it = g();\n\
       var a = it.next(); var b = it.next(); var c = it.next();\n\
       console.log(a.value, a.done, b.value, b.done, c.value, c.done);");
    c("gen-next-value-threading", false, C,
      "function* g() { var x = yield 1; var y = yield x + 1; return x + y; }\n\
       var it = g();\n\
       console.log(it.next().value, it.next(10).value, it.next(100).value);");
    c("gen-return-completes", false, C,
      "function* g() { yield 1; return 42; yield 2; }\n\
       var it = g();\n\
       console.log(it.next().value, it.next().value, it.next().done);");
    c("gen-done-next-return-throw", false, C,
      "function* g() { yield 1; }\n\
       var it = g(); it.next(); it.next();\n\
       var r = it.return(5);\n\
       var t = false; try { it.throw(new Error('x')); } catch (e) { t = e instanceof Error; }\n\
       console.log(r.value, r.done, it.next().done, t);");
    c("gen-throw-into-suspended-caught", false, C,
      "function* g() { try { yield 1; } catch (e) { yield e + 10; } yield 3; }\n\
       var it = g();\n\
       console.log(it.next().value, it.throw(100).value, it.next().value);");
    c("gen-throw-into-suspended-start", false, C,
      "function* g() { yield 1; }\n\
       var it = g();\n\
       var t = false; try { it.throw(new TypeError('x')); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t, it.next().done);");
    c("gen-return-runs-finally", false, C,
      "var log = [];\n\
       function* g() { try { yield 1; } finally { log.push('fin'); } }\n\
       var it = g(); it.next();\n\
       var r = it.return(7);\n\
       console.log(log.join(','), r.value, r.done);");
    c("gen-finally-yield-overrides-return", false, C,
      "function* g() { try { yield 1; } finally { yield 2; } }\n\
       var it = g();\n\
       var a = it.next(); var b = it.return(5); var c = it.next();\n\
       console.log(a.value, b.value, b.done, c.value, c.done);");
    c("gen-executing-reentrancy-typeerror", false, C,
      "var it; function* g() { it.next(); } it = g();\n\
       var t = false; try { it.next(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("gen-new-is-typeerror", false, C,
      "function* g() {}\n\
       var t = false; try { new g(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("gen-for-of-and-spread-over-own", false, C,
      "function* g() { yield 1; yield 2; yield 3; }\n\
       var r = []; for (var x of g()) r.push(x * 10);\n\
       console.log(r.join(','));");
    c("gen-yield-star-over-array", false, C,
      "function* g() { yield 0; yield* [1, 2]; yield 3; }\n\
       var it = g(); var r = [];\n\
       var x = it.next(); while (!x.done) { r.push(x.value); x = it.next(); }\n\
       console.log(r.join(','));");
    c("gen-yield-star-over-generator", false, C,
      "function* inner() { var a = yield 1; return a + 1; }\n\
       function* outer() { var t = yield* inner(); yield t; }\n\
       var it = outer();\n\
       console.log(it.next().value, it.next(10).value);");
    c("gen-object-graph", false, C,
      "function* g() {}\n\
       var it = g();\n\
       console.log(typeof g, Object.getPrototypeOf(it) === g.prototype,\n\
         typeof it.next, g.prototype.hasOwnProperty('constructor'),\n\
         Object.getPrototypeOf(g).constructor.name);");
    c("gen-break-for-of-closes", false, C,
      "var log = [];\n\
       function* g() { try { yield 1; yield 2; yield 3; } finally { log.push('closed'); } }\n\
       var r = []; for (var x of g()) { r.push(x); if (x === 2) break; }\n\
       console.log(r.join(','), log.join(','));");
    // Generator methods on objects and classes.
    c("gen-method-object", false, C,
      "var o = { *g() { yield 'a'; yield 'b'; } };\n\
       var it = o.g();\n\
       console.log(it.next().value, it.next().value, it.next().done);");
    // yield* over a non-iterable throws TypeError (not a refusal).
    c("gen-yield-star-noniterable-typeerror", false, C,
      "function* g() { yield* 5; }\n\
       var t = false; try { g().next(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");

    // ---- Array Iterator objects (§23.1.5) --------------------------------
    c("arrayiter-values-next", false, C,
      "var it = [10, 20].values();\n\
       var a = it.next(), b = it.next(), c = it.next();\n\
       console.log(a, b, c);");
    c("arrayiter-keys-entries", false, C,
      "var ks = []; for (var k of ['a', 'b'].keys()) ks.push(k);\n\
       var es = []; for (var e of ['x', 'y'].entries()) es.push(e);\n\
       console.log(ks, es);");
    c("arrayiter-forof-values", false, C,
      "var r = []; for (var v of [1, 2, 3].values()) r.push(v * 10); console.log(r);");
    c("arrayiter-forof-entries", false, C,
      "var r = []; for (var p of ['a', 'b'].entries()) r.push(p.join(':')); console.log(r);");
    c("arrayiter-next-after-done", false, C,
      "var it = [1].values(); it.next(); it.next();\n\
       console.log(it.next(), it.next().done);");
    c("arrayiter-live-length", false, C,
      "var a = [1, 2, 3]; var it = a.values(); var first = it.next().value; a.length = 1;\n\
       console.log(first, it.next().done, it.next().done);");
    c("arrayiter-live-grow", false, C,
      "var a = [1]; var it = a.values(); it.next(); a.push(2, 3);\n\
       console.log(it.next().value, it.next().value, it.next().done);");
    c("arrayiter-generic-receiver", false, C,
      "var o = { length: 3, 0: 'a', 2: 'c' };\n\
       var it = Array.prototype.values.call(o);\n\
       console.log(it.next().value, it.next().value === undefined, it.next().value, it.next().done);");
    c("arrayiter-string-receiver", false, C,
      "var it = Array.prototype.values.call('hi'); console.log([it.next().value, it.next().value, it.next().done]);");
    c("arrayiter-entries-generic", false, C,
      "function f() { var r = []; for (var e of Array.prototype.entries.call(arguments)) r.push(e[0] + '=' + e[1]); return r; }\n\
       console.log(f('a', 'b'));");
    c("arrayiter-projection", false, C,
      "console.log([1, 2].values(), typeof [].keys().next);");
    c("arrayiter-next-wrong-receiver-typeerror", false, C,
      "var next = [].values().next; var t = false;\n\
       try { next.call({}); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("arrayiter-null-undefined-receiver", false, C,
      "var t = false; try { Array.prototype.values.call(null); } catch (e) { t = e instanceof TypeError; }\n\
       var u = false; try { Array.prototype.keys.call(undefined); } catch (e) { u = e instanceof TypeError; }\n\
       console.log(t, u);");
    c("arrayiter-destructuring", false, C,
      "var [a, b, c] = [7, 8, 9].values(); console.log(a, b, c);");
    c("arrayiter-getprototype-chain", false, C,
      "var it = [].values();\n\
       var p = Object.getPrototypeOf(it);\n\
       console.log(Object.getPrototypeOf(Object.getPrototypeOf(p)) === Object.prototype,\n\
       Object.getOwnPropertyNames(it), typeof p.next);");
    // @@toStringTag "Array Iterator" (23.1.5.2.1) is modeled: exact tag,
    // readable off the instance and via Object.prototype.toString.
    c("arrayiter-tostring-tag", false, C,
      "console.log(Object.prototype.toString.call([].values()), [].keys()[Symbol.toStringTag]);");

    // ---- private class elements (§15.7, §6.2.14) -------------------------
    c("priv-field-basic", false, C,
      "class C { #x = 5; get() { return this.#x; } set(v) { this.#x = v; } }\n\
       var c = new C(); var before = c.get(); c.set(9);\n\
       console.log(before, c.get());");
    c("priv-field-not-enumerable", false, C,
      "class C { #x = 1; y = 2; }\n\
       var c = new C();\n\
       console.log(Object.keys(c), Object.getOwnPropertyNames(c), c, 'y' in c);");
    c("priv-method", false, C,
      "class C { #m(a) { return a + this.#n(); } #n() { return 10; } run(a) { return this.#m(a); } }\n\
       console.log(new C().run(5));");
    c("priv-accessor", false, C,
      "class C { #v = 0; get #x() { return this.#v; } set #x(w) { this.#v = w + 1; }\n\
       run() { this.#x = 10; return this.#x; } }\n\
       console.log(new C().run());");
    c("priv-brand-check", false, C,
      "class C { #x = 1; static has(o) { return #x in o; } }\n\
       console.log(C.has(new C()), C.has({}), C.has([]), C.has(Object.create(null)));");
    c("priv-brand-absent-typeerror", false, C,
      "class C { #x = 1; get(o) { return o.#x; } }\n\
       var t = false; try { new C().get({}); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("priv-method-brand-absent-typeerror", false, C,
      "class C { #m() { return 1; } call(o) { return o.#m(); } }\n\
       var t = false; try { new C().call({}); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("priv-in-nonobject-typeerror", false, C,
      "class C { #x; static c() { return #x in 5; } }\n\
       var t = false; try { C.c(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("priv-static-field-method", false, C,
      "class C { static #x = 7; static #m() { return 'sm'; }\n\
       static get() { return this.#x + ':' + this.#m(); } }\n\
       console.log(C.get());");
    c("priv-getter-only-set-typeerror", false, C,
      "class C { get #x() { return 1; } run() { this.#x = 5; } }\n\
       var t = false; try { new C().run(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("priv-setter-only-get-typeerror", false, C,
      "class C { set #x(v) {} run() { return this.#x; } }\n\
       var t = false; try { new C().run(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("priv-set-method-typeerror", false, C,
      "class C { #m() {} run() { this.#m = 1; } }\n\
       var t = false; try { new C().run(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("priv-add-twice-typeerror", false, C,
      "class B { constructor(o) { return o; } }\n\
       class C extends B { #x = 1; constructor(o) { super(o); } }\n\
       var o = {}; new C(o);\n\
       var t = false; try { new C(o); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("priv-forward-reference", false, C,
      "class C { m() { return this.#x; } #x = 7; }\n\
       console.log(new C().m());");
    c("priv-method-before-field-init", false, C,
      "class C { #m() { return 9; } f = this.#m(); }\n\
       console.log(new C().f);");
    c("priv-nested-distinct-brand", false, C,
      "class Outer { #x = 'o'; static hasOuter(o) { return #x in o; }\n\
       inner() { class Inner { #x = 'i'; static hasInner(o) { return #x in o; } } return Inner; } }\n\
       var InnerC = new Outer().inner(); var o = new Outer();\n\
       console.log(Outer.hasOuter(o), InnerC.hasInner(o));");
    c("priv-nested-outer-ref", false, C,
      "class Outer { #x = 1; m() { var self = this;\n\
       class Inner { get(o) { return #x in o; } } return new Inner().get(self); } }\n\
       console.log(new Outer().m());");
    c("priv-shared-method-identity", false, C,
      "class C { #m() {} get() { return this.#m; } }\n\
       var c1 = new C(), c2 = new C();\n\
       console.log(c1.get() === c2.get());");
    c("priv-field-name-inference", false, C,
      "class C { #f = function () {}; #a = () => {}; getNames() { return [this.#f.name, this.#a.name]; } }\n\
       console.log(new C().getNames());");
    c("priv-getset-pair", false, C,
      "class C { #v = 0; get #x() { return this.#v; } set #x(w) { this.#v = w + 1; }\n\
       run() { this.#x = 10; return this.#x; } }\n\
       console.log(new C().run());");
    c("priv-field-in-derived", false, C,
      "class B { constructor() { this.b = 1; } }\n\
       class D extends B { #x = this.b + 1; get() { return this.#x; } }\n\
       console.log(new D().get());");
    c("priv-compound-assign", false, C,
      "class C { #x = 10; run() { this.#x += 5; this.#x *= 2; return this.#x; } }\n\
       console.log(new C().run());");
    c("priv-method-super-interaction", false, C,
      "class B { v() { return 'B'; } }\n\
       class D extends B { #m() { return super.v() + 'D'; } run() { return this.#m(); } }\n\
       console.log(new D().run());");

    // ---- private early errors (exact SyntaxError traces) -----------------
    c("priv-undeclared-syntaxerror", false, C,
      "class C { m() { return this.#y; } }");
    c("priv-dup-field-syntaxerror", false, C,
      "class C { #x = 1; #x = 2; }");
    c("priv-dup-field-method-syntaxerror", false, C,
      "class C { #x = 1; #x() {} }");
    c("priv-dup-getter-syntaxerror", false, C,
      "class C { get #x() {} get #x() {} }");
    c("priv-getset-mismatched-static-syntaxerror", false, C,
      "class C { static get #x() {} set #x(v) {} }");
    c("priv-constructor-method-syntaxerror", false, C,
      "class C { #constructor() {} }");
    c("priv-constructor-field-syntaxerror", false, C,
      "class C { #constructor = 1; }");
    c("priv-outside-class-syntaxerror", false, C,
      "this.#x;");
    c("priv-in-outside-class-syntaxerror", false, C,
      "var y = #x in {};");
    c("priv-delete-syntaxerror", false, C,
      "class C { #x = 1; m() { delete this.#x; } }");
    c("priv-delete-paren-syntaxerror", false, C,
      "class C { #x = 1; m() { delete (this.#x); } }");
    c("priv-bad-operand-syntaxerror", false, C,
      "class C { #x = 1; m() { return 1 + #x; } }");

    v
}

#[test]
#[allow(clippy::too_many_lines)]
fn adversarial_differential_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!(
            "SKIP adversarial_differential_vs_node: set TRUST_JS_NODE to a node binary to run"
        );
        return;
    };
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs");
    assert!(driver.is_file(), "driver not found at {}", driver.display());

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();

    for (ci, case) in cases().iter().enumerate() {
        let sem_body = if case.strict {
            format!("\"use strict\";\n{}", case.body)
        } else {
            case.body.to_string()
        };
        let sem = evaluate_case(&[], &sem_body);
        let sem_trace = match (sem, case.expect) {
            (SemOutcome::NoCoverage { reason }, Expect::Refuse) => {
                eprintln!("REFUSES (as pinned) {}: {reason}", case.name);
                continue;
            }
            (SemOutcome::NoCoverage { reason }, Expect::Cover) => {
                failures.push(format!("{}: unexpected NoCoverage: {reason}", case.name));
                continue;
            }
            (SemOutcome::Trace(_), Expect::Refuse) => {
                failures.push(format!(
                    "{}: expected a sound refusal but produced a trace",
                    case.name
                ));
                continue;
            }
            (SemOutcome::Trace(t), Expect::Cover) => t,
        };

        let body_path = tmp.path().join(format!("adv-{ci}.body.js"));
        std::fs::write(&body_path, case.body).expect("write body");
        let manifest = serde_json::json!({
            "completion_witness": true,
            "includes": [],
            "source": body_path.display().to_string(),
            "mode": if case.strict { "strict" } else { "bare" },
            "kind": "script",
        });
        let manifest_path = tmp.path().join(format!("adv-{ci}.manifest.json"));
        let mut mf = std::fs::File::create(&manifest_path).expect("create manifest");
        mf.write_all(manifest.to_string().as_bytes())
            .expect("write manifest");
        drop(mf);

        let out = Command::new(&node)
            .arg(&driver)
            .arg(&manifest_path)
            .env("TZ", "UTC")
            .env("LANG", "C")
            .env("LC_ALL", "C")
            .output()
            .expect("spawn node driver");
        let node_trace = match extract_trace(&out.stdout) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!(
                    "{}: node driver trace extraction failed: {e} (stderr: {})",
                    case.name,
                    String::from_utf8_lossy(&out.stderr)
                ));
                continue;
            }
        };

        if !traces_equal(&sem_trace, &node_trace) {
            failures.push(format!(
                "{}: DIVERGENCE: {}",
                case.name,
                explain_divergence(&sem_trace, &node_trace)
                    .unwrap_or_else(|| "unlocalized".to_string())
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "adversarial differential failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
