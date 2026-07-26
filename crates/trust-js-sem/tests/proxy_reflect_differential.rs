// Env-gated adversarial + corpus differential for the Proxy exotic object
// (ECMA-262 §10.5) and the complete %Reflect% namespace (§28.1) grown onto the
// reference head: every one of the 13 handler traps, the full invariant checks
// (non-configurable / non-extensible target reality → TypeError), a missing
// trap falling through to the target, revoked proxies, proxy-of-proxy,
// proxy-as-prototype, the call/construct traps, IsArray recursion through a
// proxy target, and the Reflect round-trips. Every Cover case must be
// byte-for-byte trace-equal with the Node driver; Refuse cases pin the sound
// NoCoverage behavior (a proxy reaching the trace projection). Skips loudly
// when TRUST_JS_NODE is unset.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use trust_js_sem::{evaluate_case, evaluate_case_opts, SemOutcome};
use trust_js_trace::{explain_divergence, extract_trace, traces_equal};

// Default corpus root: <repo>/build/js262/test262-<pinned rev>. Derived from
// CARGO_MANIFEST_DIR so it works in any checkout; override with
// TRUST_JS262_CORPUS.
const DEFAULT_CORPUS: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../build/js262/test262-9e61c12835c5e4a3bdba93850427e6742c4f64c4"
);

#[derive(Clone, Copy, PartialEq)]
enum Expect {
    Cover,
    Refuse,
}
use Expect::{Cover as C, Refuse as R};

struct Case {
    name: &'static str,
    strict: bool,
    expect: Expect,
    body: &'static str,
}

fn node_bin() -> Option<String> {
    std::env::var("TRUST_JS_NODE").ok()
}

fn driver_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs")
}

fn node_trace_of(
    node: &str,
    driver: &Path,
    tmp: &Path,
    tag: &str,
    body: &str,
    includes: &[String],
    strict: bool,
    witness: bool,
) -> Result<trust_js_trace::ObservableTrace, String> {
    let body_path = tmp.join(format!("{tag}.body.js"));
    std::fs::write(&body_path, body).expect("write body");
    let manifest = serde_json::json!({
        "completion_witness": witness,
        "includes": includes,
        "source": body_path.display().to_string(),
        "mode": if strict { "strict" } else { "bare" },
        "kind": "script",
    });
    let manifest_path = tmp.join(format!("{tag}.manifest.json"));
    let mut mf = std::fs::File::create(&manifest_path).expect("create manifest");
    mf.write_all(manifest.to_string().as_bytes()).expect("write manifest");
    drop(mf);
    let out = Command::new(node)
        .arg(driver)
        .arg(&manifest_path)
        .env("TZ", "UTC")
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .output()
        .expect("spawn node driver");
    extract_trace(&out.stdout).map_err(|e| {
        format!(
            "node trace extraction failed: {e} (stderr: {})",
            String::from_utf8_lossy(&out.stderr)
        )
    })
}

#[allow(clippy::too_many_lines)]
fn cases() -> Vec<Case> {
    let mut v = Vec::new();
    let mut c = |name: &'static str, strict: bool, expect: Expect, body: &'static str| {
        v.push(Case { name, strict, expect, body });
    };

    // ---- Reflect: the 13 statics -----------------------------------------
    c("reflect-get", false, C, "console.log(Reflect.get({ a: 1 }, 'a'), Reflect.get({}, 'x'));");
    c("reflect-get-receiver", false, C,
      "var o = { get x() { return this.y; }, y: 7 }; console.log(Reflect.get(o, 'x', { y: 42 }));");
    c("reflect-set", false, C, "var o = {}; console.log(Reflect.set(o, 'x', 5), o.x);");
    c("reflect-has", false, C, "console.log(Reflect.has({ a: 1 }, 'a'), Reflect.has({ a: 1 }, 'b'), Reflect.has([], 'length'));");
    c("reflect-deleteproperty", false, C,
      "var o = { a: 1 }; console.log(Reflect.deleteProperty(o, 'a'), 'a' in o);");
    c("reflect-defineproperty", false, C,
      "var o = {}; console.log(Reflect.defineProperty(o, 'x', { value: 1, enumerable: true }), o.x);");
    c("reflect-getownpropertydescriptor", false, C,
      "console.log(Reflect.getOwnPropertyDescriptor({ a: 1 }, 'a').value, Reflect.getOwnPropertyDescriptor({}, 'z'));");
    c("reflect-getprototypeof", false, C,
      "console.log(Reflect.getPrototypeOf([]) === Array.prototype, Reflect.getPrototypeOf(Object.create(null)));");
    c("reflect-setprototypeof", false, C,
      "var o = {}; console.log(Reflect.setPrototypeOf(o, null), Reflect.getPrototypeOf(o));");
    c("reflect-isextensible-prevent", false, C,
      "var o = {}; console.log(Reflect.isExtensible(o), Reflect.preventExtensions(o), Reflect.isExtensible(o));");
    c("reflect-ownkeys", false, C,
      "var o = { b: 1, 2: 'x', a: 3, 0: 'y' }; console.log(Reflect.ownKeys(o));");
    c("reflect-ownkeys-symbols", false, C,
      "var s = Symbol('s'); var o = { a: 1 }; o[s] = 2; var k = Reflect.ownKeys(o); console.log(k.length, k[0], k[1] === s);");
    c("reflect-apply", false, C, "console.log(Reflect.apply(Math.max, null, [1, 5, 3]));");
    c("reflect-apply-this", false, C,
      "function f(a) { return this.x + a; } console.log(Reflect.apply(f, { x: 10 }, [5]));");
    c("reflect-construct", false, C,
      "function F(a) { this.a = a; } var o = Reflect.construct(F, [9]); console.log(o.a, o instanceof F);");
    c("reflect-construct-newtarget", false, C,
      "function F() {} function G() {} var o = Reflect.construct(F, [], G); console.log(Object.getPrototypeOf(o) === G.prototype);");
    c("reflect-nonobject-throws", false, C,
      "var t = false; try { Reflect.get(1, 'x'); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("reflect-apply-noncallable-throws", false, C,
      "var t = false; try { Reflect.apply({}, null, []); } catch (e) { t = e instanceof TypeError; } console.log(t);");

    // ---- Proxy: the property traps ---------------------------------------
    c("proxy-get-trap", false, C,
      "var p = new Proxy({}, { get: function (t, k) { return k + '!'; } }); console.log(p.foo, p.bar);");
    c("proxy-get-default", false, C,
      "var p = new Proxy({ a: 1 }, {}); console.log(p.a, p.b);");
    c("proxy-get-receiver-forwarded", false, C,
      "var log = []; var p = new Proxy({}, { get: function (t, k, r) { log.push(r === p); return 1; } }); p.x; console.log(log);");
    c("proxy-set-trap", false, C,
      "var log = []; var p = new Proxy({}, { set: function (t, k, v) { log.push(k + '=' + v); t[k] = v; return true; } });\n\
       p.x = 5; console.log(log, p.x);");
    c("proxy-set-default", false, C,
      "var t = {}; var p = new Proxy(t, {}); p.y = 9; console.log(t.y, p.y);");
    c("proxy-has-trap", false, C,
      "var p = new Proxy({}, { has: function (t, k) { return k === 'yes'; } }); console.log('yes' in p, 'no' in p);");
    c("proxy-has-default", false, C,
      "var p = new Proxy({ a: 1 }, {}); console.log('a' in p, 'b' in p);");
    c("proxy-delete-trap", false, C,
      "var log = []; var p = new Proxy({ a: 1 }, { deleteProperty: function (t, k) { log.push(k); return true; } });\n\
       var d = delete p.a; console.log(d, log);");
    c("proxy-ownkeys-descriptor", false, C,
      "var p = new Proxy({}, { ownKeys: function () { return ['a', 'b']; },\n\
       getOwnPropertyDescriptor: function (t, k) { return { value: k, enumerable: true, configurable: true }; } });\n\
       console.log(Object.keys(p), Object.getOwnPropertyNames(p));");
    c("proxy-getownpropertydescriptor-trap", false, C,
      "var p = new Proxy({}, { getOwnPropertyDescriptor: function (t, k) { return { value: 42, configurable: true }; } });\n\
       var d = Object.getOwnPropertyDescriptor(p, 'x'); console.log(d.value, d.enumerable, d.writable);");
    c("proxy-defineproperty-trap", false, C,
      "var log = []; var p = new Proxy({}, { defineProperty: function (t, k, d) { log.push(k); Object.defineProperty(t, k, d); return true; } });\n\
       Object.defineProperty(p, 'x', { value: 1, configurable: true }); console.log(log);");
    c("proxy-getprototypeof-trap", false, C,
      "var proto = { p: 1 }; var p = new Proxy({}, { getPrototypeOf: function () { return proto; } });\n\
       console.log(Object.getPrototypeOf(p) === proto, Reflect.getPrototypeOf(p) === proto);");
    c("proxy-setprototypeof-trap", false, C,
      "var log = []; var p = new Proxy({}, { setPrototypeOf: function (t, v) { log.push('set'); return true; } });\n\
       console.log(Reflect.setPrototypeOf(p, {}), log);");
    c("proxy-isextensible-trap", false, C,
      "var p = new Proxy({}, { isExtensible: function (t) { return Reflect.isExtensible(t); } });\n\
       console.log(Reflect.isExtensible(p));");
    c("proxy-preventextensions-trap", false, C,
      "var p = new Proxy({}, { preventExtensions: function (t) { Object.preventExtensions(t); return true; } });\n\
       console.log(Reflect.preventExtensions(p), Reflect.isExtensible(p));");

    // ---- Proxy: call / construct -----------------------------------------
    c("proxy-apply-trap", false, C,
      "var p = new Proxy(function () {}, { apply: function (t, thisArg, args) { return args[0] + args[1]; } });\n\
       console.log(p(2, 3), typeof p);");
    c("proxy-apply-default", false, C,
      "var p = new Proxy(function (a, b) { return a * b; }, {}); console.log(p(3, 4));");
    c("proxy-construct-trap", false, C,
      "var p = new Proxy(function () {}, { construct: function (t, args) { return { sum: args[0] + args[1] }; } });\n\
       console.log(new p(2, 3).sum);");
    c("proxy-construct-default", false, C,
      "function F(a) { this.a = a; } var p = new Proxy(F, {}); var o = new p(7); console.log(o.a, o instanceof F);");
    c("proxy-typeof-callable", false, C,
      "console.log(typeof new Proxy(function () {}, {}), typeof new Proxy({}, {}));");

    // ---- Proxy: revocation -----------------------------------------------
    c("proxy-revocable", false, C,
      "var r = Proxy.revocable({ a: 1 }, {}); console.log(r.proxy.a); r.revoke();\n\
       var t = false; try { r.proxy.a; } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("proxy-revoke-idempotent", false, C,
      "var r = Proxy.revocable({}, {}); r.revoke(); r.revoke(); console.log('ok');");
    c("proxy-revoke-all-methods", false, C,
      "var r = Proxy.revocable({}, {}); r.revoke(); var n = 0;\n\
       try { r.proxy.x; } catch (e) { n++; }\n\
       try { r.proxy.x = 1; } catch (e) { n++; }\n\
       try { 'x' in r.proxy; } catch (e) { n++; }\n\
       try { delete r.proxy.x; } catch (e) { n++; }\n\
       try { Object.keys(r.proxy); } catch (e) { n++; }\n\
       console.log(n);");

    // ---- Proxy: composition ----------------------------------------------
    c("proxy-of-proxy", false, C,
      "var inner = new Proxy({}, { get: function () { return 'inner'; } });\n\
       var outer = new Proxy(inner, {}); console.log(outer.anything);");
    c("proxy-as-prototype", false, C,
      "var p = new Proxy({}, { get: function (t, k) { return k === 'foo' ? 42 : undefined; } });\n\
       var o = Object.create(p); console.log(o.foo, o.bar);");
    c("proxy-instanceof", false, C,
      "function F() {} var p = new Proxy(F, {}); var o = new F(); console.log(o instanceof p);");

    // ---- Proxy: IsArray recursion ----------------------------------------
    c("proxy-isarray-true", false, C, "console.log(Array.isArray(new Proxy([], {})));");
    c("proxy-isarray-false", false, C, "console.log(Array.isArray(new Proxy({}, {})));");
    c("proxy-isarray-nested", false, C,
      "console.log(Array.isArray(new Proxy(new Proxy([], {}), {})));");
    c("proxy-isarray-revoked-throws", false, C,
      "var r = Proxy.revocable([], {}); r.revoke(); var t = false;\n\
       try { Array.isArray(r.proxy); } catch (e) { t = e instanceof TypeError; } console.log(t);");

    // ---- Proxy: constructor errors ---------------------------------------
    c("proxy-ctor-nonobject-target", false, C,
      "var t = false; try { new Proxy(1, {}); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("proxy-ctor-nonobject-handler", false, C,
      "var t = false; try { new Proxy({}, 1); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("proxy-call-without-new", false, C,
      "var t = false; try { Proxy({}, {}); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("proxy-call-noncallable", false, C,
      "var p = new Proxy({}, {}); var t = false; try { p(); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("proxy-construct-nonconstructor", false, C,
      "var p = new Proxy({}, {}); var t = false; try { new p(); } catch (e) { t = e instanceof TypeError; } console.log(t);");

    // ---- Proxy: the FULL invariant → TypeError ---------------------------
    c("proxy-inv-get-nonwritable-mismatch", false, C,
      "var t = {}; Object.defineProperty(t, 'x', { value: 1, writable: false, configurable: false });\n\
       var p = new Proxy(t, { get: function () { return 2; } });\n\
       var r = false; try { p.x; } catch (e) { r = e instanceof TypeError; } console.log(r);");
    c("proxy-inv-get-nonwritable-match", false, C,
      "var t = {}; Object.defineProperty(t, 'x', { value: 1, writable: false, configurable: false });\n\
       var p = new Proxy(t, { get: function () { return 1; } }); console.log(p.x);");
    c("proxy-inv-set-nonwritable-mismatch", false, C,
      "var t = {}; Object.defineProperty(t, 'x', { value: 1, writable: false, configurable: false });\n\
       var p = new Proxy(t, { set: function () { return true; } });\n\
       var r = false; try { p.x = 2; } catch (e) { r = e instanceof TypeError; } console.log(r);");
    c("proxy-inv-gopd-hide-nonconfig", false, C,
      "var t = {}; Object.defineProperty(t, 'x', { value: 1, configurable: false });\n\
       var p = new Proxy(t, { getOwnPropertyDescriptor: function () { return undefined; } });\n\
       var r = false; try { Object.getOwnPropertyDescriptor(p, 'x'); } catch (e) { r = e instanceof TypeError; } console.log(r);");
    c("proxy-inv-has-hide-nonconfig", false, C,
      "var t = {}; Object.defineProperty(t, 'x', { value: 1, configurable: false });\n\
       var p = new Proxy(t, { has: function () { return false; } });\n\
       var r = false; try { 'x' in p; } catch (e) { r = e instanceof TypeError; } console.log(r);");
    c("proxy-inv-delete-nonconfig", false, C,
      "var t = {}; Object.defineProperty(t, 'x', { value: 1, configurable: false });\n\
       var p = new Proxy(t, { deleteProperty: function () { return true; } });\n\
       var r = false; try { delete p.x; } catch (e) { r = e instanceof TypeError; } console.log(r);");
    c("proxy-inv-ownkeys-missing-nonconfig", false, C,
      "var t = {}; Object.defineProperty(t, 'x', { value: 1, configurable: false });\n\
       var p = new Proxy(t, { ownKeys: function () { return []; } });\n\
       var r = false; try { Object.getOwnPropertyNames(p); } catch (e) { r = e instanceof TypeError; } console.log(r);");
    c("proxy-inv-ownkeys-duplicate", false, C,
      "var p = new Proxy({}, { ownKeys: function () { return ['a', 'a']; } });\n\
       var r = false; try { Object.getOwnPropertyNames(p); } catch (e) { r = e instanceof TypeError; } console.log(r);");
    c("proxy-inv-ownkeys-nonextensible-extra", false, C,
      "var t = {}; Object.preventExtensions(t);\n\
       var p = new Proxy(t, { ownKeys: function () { return ['extra']; } });\n\
       var r = false; try { Object.getOwnPropertyNames(p); } catch (e) { r = e instanceof TypeError; } console.log(r);");
    c("proxy-inv-getprototypeof-nonextensible", false, C,
      "var t = {}; Object.preventExtensions(t);\n\
       var p = new Proxy(t, { getPrototypeOf: function () { return Array.prototype; } });\n\
       var r = false; try { Object.getPrototypeOf(p); } catch (e) { r = e instanceof TypeError; } console.log(r);");
    c("proxy-inv-defineproperty-false", false, C,
      "var t = {}; Object.preventExtensions(t);\n\
       var p = new Proxy(t, { defineProperty: function () { return true; } });\n\
       var r = false; try { Object.defineProperty(p, 'x', { value: 1, configurable: false }); } catch (e) { r = e instanceof TypeError; } console.log(r);");
    c("proxy-inv-preventextensions-still-extensible", false, C,
      "var p = new Proxy({}, { preventExtensions: function () { return true; } });\n\
       var r = false; try { Reflect.preventExtensions(p); } catch (e) { r = e instanceof TypeError; } console.log(r);");

    // ---- Proxy: freeze / seal / integrity --------------------------------
    c("proxy-freeze-transparent", false, C,
      "var t = { a: 1 }; var p = new Proxy(t, {}); Object.freeze(p);\n\
       console.log(Object.isFrozen(t), Object.isFrozen(p), Object.isExtensible(p));");
    c("proxy-seal-transparent", false, C,
      "var t = { a: 1 }; var p = new Proxy(t, {}); Object.seal(p);\n\
       console.log(Object.isSealed(p), Object.isFrozen(p));");

    // ---- Refusals: a proxy reaching the trace projection -----------------
    c("proxy-log-refuses", false, R, "var p = new Proxy({ a: 1 }, {}); console.log(p);");
    c("proxy-completion-refuses", false, R, "var p = new Proxy({ a: 1 }, {}); p;");
    c("proxy-forin-refuses", false, R,
      "var p = new Proxy({ a: 1, b: 2 }, {}); var ks = []; for (var k in p) ks.push(k); console.log(ks);");
    c("proxy-thrown-refuses", false, R,
      "try { throw new Proxy({}, {}); } catch (e) { throw e; }");

    v
}

#[test]
#[allow(clippy::too_many_lines)]
fn proxy_reflect_adversarial_vs_node() {
    let Some(node) = node_bin() else {
        eprintln!("SKIP proxy_reflect_adversarial_vs_node: set TRUST_JS_NODE to run");
        return;
    };
    let driver = driver_path();
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
            (SemOutcome::NoCoverage { .. }, Expect::Refuse) => continue,
            (SemOutcome::NoCoverage { reason }, Expect::Cover) => {
                failures.push(format!("{}: unexpected NoCoverage: {reason}", case.name));
                continue;
            }
            (SemOutcome::Trace(_), Expect::Refuse) => {
                failures.push(format!("{}: expected refusal but produced a trace", case.name));
                continue;
            }
            (SemOutcome::Trace(t), Expect::Cover) => t,
        };
        let node_trace = match node_trace_of(
            &node,
            &driver,
            tmp.path(),
            &format!("adv-{ci}"),
            case.body,
            &[],
            case.strict,
            true,
        ) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!("{}: {e}", case.name));
                continue;
            }
        };
        if !traces_equal(&sem_trace, &node_trace) {
            failures.push(format!(
                "{}: DIVERGENCE: {}",
                case.name,
                explain_divergence(&sem_trace, &node_trace).unwrap_or_else(|| "unlocalized".into())
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "proxy/reflect adversarial failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Corpus sweep over the Proxy / Reflect directories.
// ---------------------------------------------------------------------------

const SWEEP_DIRS: &[(&str, usize)] = &[
    ("test/built-ins/Proxy", 400),
    ("test/built-ins/Reflect", 250),
];

/// The four-head-gate tail (17 cases): Proxy-integration edges + a couple of
/// regressions the recorded gate found after the initial Proxy landing. Each
/// is pinned exact (Cover, trace-equal with Node) or sound-refuse (Refuse).
/// Runs against the real corpus + harness so the fixes stay honest.
const PINNED_TAIL: &[(&str, Expect)] = &[
    // ArraySpeciesCreate through a proxy-over-array with a custom @@species
    // constructor → the non-default @@species Construct is out of slice: refuse
    // (never the wrong plain-array trace the bare ObjKind::Array check produced).
    ("test/built-ins/Array/prototype/concat/create-proxy.js", R),
    ("test/built-ins/Array/prototype/filter/create-proxy.js", R),
    ("test/built-ins/Array/prototype/map/create-proxy.js", R),
    ("test/built-ins/Array/prototype/slice/create-proxy.js", R),
    // IsConstructor(BigInt) is true (BigInt implements [[Construct]]).
    ("test/built-ins/BigInt/is-a-constructor.js", C),
    // GetPrototypeFromConstructor → GetFunctionRealm on a revoked proxy → TypeError.
    ("test/built-ins/Function/internals/Construct/base-ctor-revoked-proxy.js", C),
    // %Object.prototype% is an immutable-prototype exotic object.
    ("test/built-ins/Object/prototype/setPrototypeOf-with-non-circular-values.js", C),
    // Reflect.construct's Date.now probe is a driver-firewall artifact
    // (firewalled `now` is a constructable plain function): sound-refuse.
    ("test/built-ins/Reflect/construct/newtarget-is-not-constructor-throws.js", R),
    ("test/built-ins/Reflect/construct/target-is-not-constructor-throws.js", R),
    // Typed-array integer-indexed [[Set]] via Reflect.set (all direct
    // Int32Array — no harness `Array.from` — so they COVER and lock the
    // 10.4.5.5 behavior V8/Node implement):
    //  * out-of-range index → coerce V once, no store, return true;
    //  * in-range index with O === Receiver (reached via the prototype chain)
    //    → coerce + store;
    //  * in-range index with O != Receiver → OrdinarySet onto Receiver, no
    //    coercion; out-of-range with a non-object / non-TA Receiver → coerce.
    ("test/built-ins/TypedArrayConstructors/internals/Set/key-is-out-of-bounds-receiver-is-proto.js", C),
    ("test/built-ins/TypedArrayConstructors/internals/Set/key-is-in-bounds-receiver-is-not-typed-array.js", C),
    ("test/built-ins/TypedArrayConstructors/internals/Set/key-is-out-of-bounds-receiver-is-not-object.js", C),
    ("test/built-ins/TypedArrayConstructors/internals/Set/key-is-out-of-bounds-receiver-is-not-typed-array.js", C),
    // Array.prototype.concat over a spreadable whose length exceeds the
    // iteration cap is engine-specific (V8 skips dense-element access): refuse.
    ("test/built-ins/Array/prototype/concat/arg-length-near-integer-limit.js", R),
    // The remaining Set/key-is-* files reach the same fixed [[Set]] path, but
    // their `testWithTypedArrayConstructors` harness helper builds ctor args via
    // `Array.from` (unmodeled, orthogonal to Proxy) — so they sound-refuse.
    ("test/built-ins/TypedArrayConstructors/internals/Set/key-is-minus-zero.js", R),
    ("test/built-ins/TypedArrayConstructors/internals/Set/key-is-not-integer.js", R),
    ("test/built-ins/TypedArrayConstructors/internals/Set/key-is-out-of-bounds.js", R),
    ("test/built-ins/TypedArrayConstructors/internals/Set/BigInt/key-is-minus-zero.js", R),
    ("test/built-ins/TypedArrayConstructors/internals/Set/BigInt/key-is-not-integer.js", R),
    ("test/built-ins/TypedArrayConstructors/internals/Set/BigInt/key-is-out-of-bounds.js", R),
    // Object rest over a proxy drives ownKeys + getOwnPropertyDescriptor in order.
    ("test/language/expressions/object/dstr/object-rest-proxy-ownkeys-returned-keys-order.js", C),
];

struct Frontmatter {
    includes: Vec<String>,
    flags: Vec<String>,
}

fn parse_frontmatter(body: &str) -> Frontmatter {
    let fm = body
        .split_once("/*---")
        .and_then(|(_, rest)| rest.split_once("---*/"))
        .map_or("", |(fm, _)| fm);
    let mut includes = Vec::new();
    let mut flags = Vec::new();
    let mut lines = fm.lines().peekable();
    while let Some(line) = lines.next() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("includes:") {
            let rest = rest.trim();
            if let Some(inner) = rest.strip_prefix('[') {
                includes.extend(
                    inner
                        .trim_end_matches(']')
                        .split(',')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
                );
            } else {
                while let Some(next) = lines.peek() {
                    let nt = next.trim_start();
                    if let Some(item) = nt.strip_prefix("- ") {
                        includes.push(item.trim().to_string());
                        lines.next();
                    } else {
                        break;
                    }
                }
            }
        } else if let Some(rest) = t.strip_prefix("flags:") {
            if let Some(inner) = rest.trim().strip_prefix('[') {
                flags.extend(
                    inner
                        .trim_end_matches(']')
                        .split(',')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
                );
            }
        }
    }
    Frontmatter { includes, flags }
}

fn collect_js_files(dir: &Path, cap: usize) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else { continue };
        let mut entries: Vec<PathBuf> = rd.filter_map(|e| e.ok().map(|e| e.path())).collect();
        entries.sort();
        for p in entries {
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|e| e == "js")
                && !p.file_name().is_some_and(|n| n.to_string_lossy().ends_with("_FIXTURE.js"))
            {
                files.push(p);
            }
        }
    }
    files.sort();
    files.truncate(cap);
    files
}

#[test]
#[allow(clippy::too_many_lines)]
fn proxy_reflect_corpus_vs_node() {
    let Some(node) = node_bin() else {
        eprintln!("SKIP proxy_reflect_corpus_vs_node: set TRUST_JS_NODE (and optionally TRUST_JS262_CORPUS) to run");
        return;
    };
    let corpus =
        PathBuf::from(std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.into()));
    assert!(
        corpus.join("harness/assert.js").is_file(),
        "corpus harness not found under {}",
        corpus.display()
    );
    let driver = driver_path();
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    let (mut covered, mut refused, mut equal) = (0u64, 0u64, 0u64);
    let mut per_dir: BTreeMap<&str, (u64, u64)> = BTreeMap::new();
    let mut include_cache: BTreeMap<String, String> = BTreeMap::new();
    let mut reasons: BTreeMap<String, (u64, String)> = BTreeMap::new();
    let mut case_no = 0usize;

    for (dir, cap) in SWEEP_DIRS {
        for path in collect_js_files(&corpus.join(dir), *cap) {
            let Ok(body) = std::fs::read_to_string(&path) else { continue };
            let fm = parse_frontmatter(&body);
            if fm.flags.iter().any(|f| f == "async" || f == "module" || f == "CanBlockIsRequired") {
                continue;
            }
            let raw = fm.flags.iter().any(|f| f == "raw");
            let modes: &[bool] = if fm.flags.iter().any(|f| f == "onlyStrict") {
                &[true]
            } else if raw || fm.flags.iter().any(|f| f == "noStrict") {
                &[false]
            } else {
                &[false, true]
            };
            let mut include_names: Vec<String> = if raw {
                Vec::new()
            } else {
                vec!["assert.js".into(), "sta.js".into()]
            };
            include_names.extend(fm.includes.iter().cloned());
            let mut include_srcs: Vec<String> = Vec::new();
            let mut include_paths: Vec<String> = Vec::new();
            let mut missing = false;
            for name in &include_names {
                let p = corpus.join("harness").join(name);
                if !p.is_file() {
                    missing = true;
                    break;
                }
                let src = include_cache
                    .entry(name.clone())
                    .or_insert_with(|| std::fs::read_to_string(&p).expect("read include"));
                include_srcs.push(src.clone());
                include_paths.push(p.display().to_string());
            }
            if missing {
                continue;
            }
            let rel = path.strip_prefix(&corpus).unwrap_or(&path).display().to_string();
            for &strict in modes {
                case_no += 1;
                let sem_body = if strict { format!("\"use strict\";\n{body}") } else { body.clone() };
                let inc_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
                let sem_trace = match evaluate_case_opts(&inc_refs, &sem_body, false) {
                    SemOutcome::Trace(t) => t,
                    SemOutcome::NoCoverage { reason } => {
                        refused += 1;
                        per_dir.entry(dir).or_default().1 += 1;
                        reasons.entry(reason).or_insert_with(|| (0, rel.clone())).0 += 1;
                        continue;
                    }
                };
                covered += 1;
                per_dir.entry(dir).or_default().0 += 1;
                let node_trace = match node_trace_of(
                    &node, &driver, tmp.path(), &format!("case-{case_no}"), &body, &include_paths, strict, false,
                ) {
                    Ok(t) => t,
                    Err(e) => {
                        failures.push(format!("{rel} [{}]: {e}", if strict { "strict" } else { "bare" }));
                        continue;
                    }
                };
                if traces_equal(&sem_trace, &node_trace) {
                    equal += 1;
                } else {
                    failures.push(format!(
                        "{rel} [{}]: WRONG TRACE: {}",
                        if strict { "strict" } else { "bare" },
                        explain_divergence(&sem_trace, &node_trace).unwrap_or_else(|| "unlocalized".into())
                    ));
                }
            }
        }
    }

    eprintln!("== proxy/reflect corpus: covered {covered} (equal {equal}) / refused {refused} ==");
    for (dir, (cc, rr)) in &per_dir {
        eprintln!("  {dir}: covered {cc} refused {rr}");
    }
    let mut rs: Vec<(u64, String, String)> =
        reasons.into_iter().map(|(k, (n, s))| (n, k, s)).collect();
    rs.sort_by(|a, b| b.0.cmp(&a.0));
    eprintln!("== top refusal reasons ==");
    for (n, reason, sample) in rs.iter().take(30) {
        eprintln!("  {n} x {reason} (e.g. {sample})");
    }
    assert!(
        failures.is_empty(),
        "proxy/reflect corpus failures (wrong trace is never acceptable) ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Pinned four-head-gate tail: the exact 17 files, run against the real corpus
// + harness, each ruled Cover (trace-equal with Node) or Refuse (sound
// NoCoverage). Guards against regressing any of the tail fixes.
// ---------------------------------------------------------------------------

#[test]
#[allow(clippy::too_many_lines)]
fn pinned_tail_vs_node() {
    let Some(node) = node_bin() else {
        eprintln!("SKIP pinned_tail_vs_node: set TRUST_JS_NODE to run");
        return;
    };
    let corpus =
        PathBuf::from(std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.into()));
    assert!(
        corpus.join("harness/assert.js").is_file(),
        "corpus harness not found under {}",
        corpus.display()
    );
    let driver = driver_path();
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut include_cache: BTreeMap<String, String> = BTreeMap::new();
    let mut failures: Vec<String> = Vec::new();

    for (i, (rel, expect)) in PINNED_TAIL.iter().enumerate() {
        let path = corpus.join(rel);
        let Ok(body) = std::fs::read_to_string(&path) else {
            failures.push(format!("{rel}: missing corpus file"));
            continue;
        };
        let fm = parse_frontmatter(&body);
        let raw = fm.flags.iter().any(|f| f == "raw");
        let modes: &[bool] = if fm.flags.iter().any(|f| f == "onlyStrict") {
            &[true]
        } else if raw || fm.flags.iter().any(|f| f == "noStrict") {
            &[false]
        } else {
            &[false, true]
        };
        let mut include_names: Vec<String> = if raw {
            Vec::new()
        } else {
            vec!["assert.js".into(), "sta.js".into()]
        };
        include_names.extend(fm.includes.iter().cloned());
        let mut include_srcs: Vec<String> = Vec::new();
        let mut include_paths: Vec<String> = Vec::new();
        for name in &include_names {
            let p = corpus.join("harness").join(name);
            let src = include_cache
                .entry(name.clone())
                .or_insert_with(|| std::fs::read_to_string(&p).expect("read include"));
            include_srcs.push(src.clone());
            include_paths.push(p.display().to_string());
        }
        for &strict in modes {
            let sem_body = if strict { format!("\"use strict\";\n{body}") } else { body.clone() };
            let inc_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
            let mode = if strict { "strict" } else { "bare" };
            match (evaluate_case(&inc_refs, &sem_body), expect) {
                (SemOutcome::NoCoverage { .. }, Expect::Refuse) => {}
                (SemOutcome::NoCoverage { reason }, Expect::Cover) => {
                    failures.push(format!("{rel} [{mode}]: expected Cover, got NoCoverage: {reason}"));
                }
                (SemOutcome::Trace(_), Expect::Refuse) => {
                    failures.push(format!("{rel} [{mode}]: expected Refuse, got a trace"));
                }
                (SemOutcome::Trace(sem_trace), Expect::Cover) => {
                    match node_trace_of(
                        &node, &driver, tmp.path(), &format!("tail-{i}"), &body, &include_paths, strict, true,
                    ) {
                        Ok(node_trace) => {
                            if !traces_equal(&sem_trace, &node_trace) {
                                failures.push(format!(
                                    "{rel} [{mode}]: WRONG TRACE: {}",
                                    explain_divergence(&sem_trace, &node_trace)
                                        .unwrap_or_else(|| "unlocalized".into())
                                ));
                            }
                        }
                        Err(e) => failures.push(format!("{rel} [{mode}]: {e}")),
                    }
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "pinned tail failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
