// trust-js-value: the realm global-name registry.
//
// The COMPLETE set of identifier names for which an unqualified reference
// RESOLVES (is not an unresolvable reference) in the trace driver's realm.
// It is the authority the interpreter uses to tell "an unmodeled real global"
// (refuse — NoCoverage) from "a genuinely-undeclared name" (throw the exact
// ReferenceError, matching every engine).
//
// PROVENANCE (do not hand-edit — regenerate empirically). Derived by walking
// the ENTIRE prototype chain of `globalThis` inside the actual trace driver
// realm (not a plain `node -e`, whose CommonJS wrapper injects require/module/
// exports/__dirname/__filename and lazy node: module globals the driver realm
// does NOT expose) on:
//   * Node  v24.5.0  (primary comparison engine) — 148 chain names
//   * Bun   1.3.14   (either-engine fallback)     — 169 chain names
// via the manifest driver:
//   node|bun crates/trust-js-trace/js/trace_driver.mjs <manifest>
//   body: (function(){ "use strict"; var s=Object.create(null),out=[],o=globalThis;
//          while(o){for(const n of Object.getOwnPropertyNames(o)){if(!s[n]){s[n]=1;out.push(n)}}
//          o=Object.getPrototypeOf(o)} out.sort().forEach(n=>console.log("NM|"+n)); })();
// This walk is authoritative because unqualified identifier resolution against
// the global object uses [[HasBinding]] -> HasProperty, which consults the
// FULL prototype chain — so inherited Object.prototype members (`toString`,
// `valueOf`, `hasOwnProperty`, `constructor`, `__proto__`, ...) DO resolve and
// MUST be present, even though they are absent from
// `getOwnPropertyNames(globalThis)`.
//
// The registry is the UNION of the two engines' chains (170 names). The union
// is a superset of the primary (Node) realm, so it NEVER wrongly throws a
// ReferenceError for a name Node would resolve; the extra Bun-only host globals
// (`self`, `Worker`, `ShadowRealm`, `alert`, ...) only make us refuse more,
// which is always sound. Genuinely-undeclared names (test locals like `x`,
// `w`, `u`, `ctors`, `unresolvableReference`) are in NEITHER realm and so
// correctly fall through to a real ReferenceError.
//
// Recorded: 2026-07-22 (Node v24.5.0 / Bun 1.3.14).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// Every name for which an unqualified reference resolves in the driver realm,
/// byte-sorted (matching `<str as Ord>`) for `binary_search`. See PROVENANCE.
static REALM_GLOBAL_NAMES: [&str; 170] = [
    "AbortController", "AbortSignal", "AggregateError", "Array", "ArrayBuffer", "AsyncDisposableStack",
    "Atomics", "BigInt", "BigInt64Array", "BigUint64Array", "Blob", "Boolean",
    "BroadcastChannel", "Buffer", "BuildError", "BuildMessage", "Bun", "ByteLengthQueuingStrategy",
    "CloseEvent", "CompressionStream", "CountQueuingStrategy", "Crypto", "CryptoKey", "CustomEvent",
    "DOMException", "DataView", "Date", "DecompressionStream", "DisposableStack", "Error",
    "ErrorEvent", "EvalError", "Event", "EventTarget", "File", "FinalizationRegistry",
    "Float16Array", "Float32Array", "Float64Array", "FormData", "Function", "HTMLRewriter",
    "Headers", "Infinity", "Int16Array", "Int32Array", "Int8Array", "Intl",
    "Iterator", "JSON", "Map", "Math", "MessageChannel", "MessageEvent",
    "MessagePort", "NaN", "Navigator", "Number", "Object", "Performance",
    "PerformanceEntry", "PerformanceMark", "PerformanceMeasure", "PerformanceObserver", "PerformanceObserverEntryList", "PerformanceResourceTiming",
    "PerformanceServerTiming", "PerformanceTiming", "Promise", "Proxy", "RangeError", "ReadableByteStreamController",
    "ReadableStream", "ReadableStreamBYOBReader", "ReadableStreamBYOBRequest", "ReadableStreamDefaultController", "ReadableStreamDefaultReader", "ReferenceError",
    "Reflect", "RegExp", "Request", "ResolveError", "ResolveMessage", "Response",
    "Set", "ShadowRealm", "SharedArrayBuffer", "String", "SubtleCrypto", "SuppressedError",
    "Symbol", "SyntaxError", "TextDecoder", "TextDecoderStream", "TextEncoder", "TextEncoderStream",
    "TransformStream", "TransformStreamDefaultController", "TypeError", "URIError", "URL", "URLPattern",
    "URLSearchParams", "Uint16Array", "Uint32Array", "Uint8Array", "Uint8ClampedArray", "WeakMap",
    "WeakRef", "WeakSet", "WebAssembly", "WebSocket", "Worker", "WritableStream",
    "WritableStreamDefaultController", "WritableStreamDefaultWriter", "__defineGetter__", "__defineSetter__", "__lookupGetter__", "__lookupSetter__",
    "__proto__", "addEventListener", "alert", "atob", "btoa", "clearImmediate",
    "clearInterval", "clearTimeout", "confirm", "console", "constructor", "crypto",
    "decodeURI", "decodeURIComponent", "dispatchEvent", "encodeURI", "encodeURIComponent", "escape",
    "eval", "fetch", "global", "globalThis", "hasOwnProperty", "isFinite",
    "isNaN", "isPrototypeOf", "navigator", "onerror", "onmessage", "parseFloat",
    "parseInt", "performance", "postMessage", "print", "process", "prompt",
    "propertyIsEnumerable", "queueMicrotask", "removeEventListener", "reportError", "self", "setImmediate",
    "setInterval", "setTimeout", "structuredClone", "toLocaleString", "toString", "undefined",
    "unescape", "valueOf",
];

/// Is `name` a global whose unqualified reference RESOLVES in the driver realm?
///
/// `true`  → the name is a real realm global (possibly one the interpreter does
///            not model); the caller must NOT synthesize a ReferenceError.
/// `false` → the name is in NEITHER engine's realm; combined with "not bound in
///            any environment record" it is a genuinely-undeclared identifier,
///            i.e. an unresolvable reference (a real ReferenceError / a
///            `typeof` of `"undefined"`).
#[must_use]
pub fn is_realm_global_name(name: &str) -> bool {
    REALM_GLOBAL_NAMES.binary_search(&name).is_ok()
}

#[cfg(test)]
mod tests {
    use super::{is_realm_global_name, REALM_GLOBAL_NAMES};

    #[test]
    fn table_is_sorted_unique_for_binary_search() {
        for w in REALM_GLOBAL_NAMES.windows(2) {
            assert!(w[0] < w[1], "registry not byte-sorted / unique at {:?}", w);
        }
    }

    #[test]
    fn real_globals_resolve() {
        // ECMA-262 constructors + value/function props the interpreter may or
        // may not model — all must be recognized as realm globals (refuse, not
        // ReferenceError).
        for n in [
            "Object", "Array", "Function", "Math", "JSON", "Reflect", "Proxy", "Atomics",
            "Symbol", "BigInt", "Promise", "Map", "Set", "WeakMap", "WeakSet", "WeakRef",
            "Iterator", "FinalizationRegistry", "DisposableStack", "AsyncDisposableStack",
            "SuppressedError", "Float16Array", "SharedArrayBuffer",
            "globalThis", "undefined", "NaN", "Infinity", "eval", "parseInt", "parseFloat",
            "isNaN", "isFinite", "decodeURI", "encodeURIComponent",
            // inherited via the global object's prototype chain:
            "toString", "valueOf", "hasOwnProperty", "isPrototypeOf", "propertyIsEnumerable",
            "toLocaleString", "constructor", "__proto__", "__defineGetter__",
            // Node/Bun host realm globals:
            "process", "Buffer", "console", "print", "fetch", "structuredClone", "crypto",
            "queueMicrotask", "setTimeout", "URL", "TextEncoder", "self", "Worker",
        ] {
            assert!(is_realm_global_name(n), "expected realm global: {n}");
        }
    }

    #[test]
    fn genuinely_undeclared_names_are_not_globals() {
        for n in [
            "x", "w", "u", "ctors", "unresolvableReference", "thisNameDoesNotExist",
            "foo", "bar", "baz", "qux", "undeclared", "notDefined", "a", "b", "obj",
            "Test262Error", "assert", "verifyProperty", // harness names: defined by running the harness, NOT realm globals
        ] {
            assert!(!is_realm_global_name(n), "must NOT be a realm global: {n}");
        }
    }
}
