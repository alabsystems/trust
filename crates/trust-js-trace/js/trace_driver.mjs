// trust-js-trace: the ObservableTrace driver — the in-JS behavioral projection.
//
// Spawned as `<engine> trace_driver.mjs <case-manifest.json>` by every oracle
// head (Node, Bun, and later the in-house engine's differential shim). It
// installs the nondeterminism firewall, evaluates the harness includes and the
// test body in the main realm via indirect eval, drains jobs deterministically,
// and emits exactly one trace line:
//
//   __TRUST_JS_TRACE_V1__{...json...}
//
// The projection is deliberately engine-blind: it records only spec-mandated
// observables (ordered host effects, completion kind, error constructor
// identity + .name — never message text; deep-printed witnesses with property
// order, -0 vs +0, NaN, symbol descriptions, cycle back-references) and it
// never invokes user accessors while printing (an accessor is recorded as
// [accessor], not read). All introspection uses originals captured before any
// user code runs, so user monkey-patching cannot perturb the projection.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

'use strict';

// ---------------------------------------------------------------------------
// 0. Capture originals before anything user-visible can run.
// ---------------------------------------------------------------------------
const O = {
  getOwnPropertyDescriptor: Object.getOwnPropertyDescriptor,
  getPrototypeOf: Object.getPrototypeOf,
  ownKeys: Reflect.ownKeys,
  defineProperty: Object.defineProperty,
  isArray: Array.isArray,
  numberToString: Number.prototype.toString,
  symbolDescription: Object.getOwnPropertyDescriptor(Symbol.prototype, 'description').get,
  is: Object.is,
  apply: Reflect.apply,
  stringCharCodeAt: String.prototype.charCodeAt,
  mathFloor: Math.floor,
  jsonStringify: JSON.stringify,
  promiseResolve: Promise.resolve.bind(Promise),
  // Captured so the driver's tail NEVER performs a user-visible property
  // lookup on Promise.prototype: test262's verifyProperty deletes
  // configurable properties (e.g. Promise.prototype.catch) without restoring,
  // and a `main().catch(...)` lookup after the body ran would crash the
  // driver on such tests.
  promiseThen: Promise.prototype.then,
  stdoutWrite: null, // filled below, engine-specific
  exit: null,
};

const globalObj = globalThis;

// Engine-specific raw stdout channel + argv + file reader, captured up front.
import { writeSync, readFileSync } from 'node:fs';
import process, { argv, exit as procExit } from 'node:process';
import { pathToFileURL } from 'node:url';
O.stdoutWrite = (s) => writeSync(1, s);
O.exit = procExit;
// Real (pre-firewall) macrotask scheduler, captured before installVirtualTimers
// replaces globalThis.setTimeout with the virtual queue. The module-goal path
// needs it to pump genuine host/IO event-loop turns so a file-based dynamic
// import() settles (its completion is not on the virtual timer queue); the
// script goal never touches it, so its determinism is unaffected.
O.realSetTimeout = globalThis.setTimeout;

// Intrinsic prototypes for class tagging (matched by identity walking the
// prototype chain — never by invoking user code).
const INTRINSIC_PROTOS = [
  ['Array', Array.prototype],
  ['Function', Function.prototype],
  ['Error:Error', Error.prototype],
  ['Error:TypeError', TypeError.prototype],
  ['Error:RangeError', RangeError.prototype],
  ['Error:ReferenceError', ReferenceError.prototype],
  ['Error:SyntaxError', SyntaxError.prototype],
  ['Error:EvalError', EvalError.prototype],
  ['Error:URIError', URIError.prototype],
  ['Error:AggregateError', typeof AggregateError !== 'undefined' ? AggregateError.prototype : null],
  ['RegExp', RegExp.prototype],
  ['Date', Date.prototype],
  ['Map', Map.prototype],
  ['Set', Set.prototype],
  ['WeakMap', WeakMap.prototype],
  ['WeakSet', WeakSet.prototype],
  ['Promise', Promise.prototype],
  ['ArrayBuffer', ArrayBuffer.prototype],
  ['DataView', DataView.prototype],
  ['Boolean', Boolean.prototype],
  ['Number', Number.prototype],
  ['String', String.prototype],
  ['Symbol', Symbol.prototype],
  ['BigInt', typeof BigInt !== 'undefined' ? BigInt.prototype : null],
  ['Object', Object.prototype],
].filter(([, p]) => p !== null);

const WELL_KNOWN_SYMBOLS = new Map();
for (const k of ['iterator', 'asyncIterator', 'hasInstance', 'isConcatSpreadable',
  'match', 'matchAll', 'replace', 'search', 'species', 'split',
  'toPrimitive', 'toStringTag', 'unscopables']) {
  if (Symbol[k]) WELL_KNOWN_SYMBOLS.set(Symbol[k], 'Symbol.' + k);
}

// ---------------------------------------------------------------------------
// 1. The deterministic deep-print projection.
// ---------------------------------------------------------------------------
// Caps are part of the projection's identity (recorded in the schema): a
// projection that walked unboundedly would be nondeterministic under OOM.
const MAX_DEPTH = 8;
const MAX_KEYS = 64;
const MAX_NODES = 4096;
const MAX_STRING = 4096;

// Engine-incidental own properties on Error instances (see the calibration
// ruling at the filter site).
const ERROR_INCIDENTAL_KEYS = new Set([
  'stack', 'line', 'column', 'sourceURL', 'originalLine', 'originalColumn',
]);

// ASCII-only escape done code-unit by code-unit, so lone surrogates survive
// the JSON layer and Rust never sees ill-formed UTF-8.
function escapeString(s) {
  let out = '';
  const n = s.length > MAX_STRING ? MAX_STRING : s.length;
  for (let i = 0; i < n; i++) {
    const c = O.apply(O.stringCharCodeAt, s, [i]);
    if (c === 0x5c) out += '\\\\';
    else if (c === 0x22) out += '\\"';
    else if (c >= 0x20 && c <= 0x7e) out += s[i];
    else out += '\\u' + c.toString(16).padStart(4, '0');
  }
  if (s.length > MAX_STRING) out += '\\u2026[truncated:' + s.length + ']';
  return out;
}

function numberRepr(v) {
  if (v !== v) return 'NaN';
  if (v === Infinity) return 'Infinity';
  if (v === -Infinity) return '-Infinity';
  if (v === 0) return O.is(v, -0) ? '-0' : '0';
  return O.apply(O.numberToString, v, [10]);
}

function classTag(obj) {
  // Walk the prototype chain against intrinsic prototype identities.
  // A Proxy's getPrototypeOf trap may run or throw here; symmetric across
  // heads because both run this same driver, and guarded regardless.
  try {
    let p = O.getPrototypeOf(obj);
    let hops = 0;
    while (p !== null && hops < 32) {
      for (const [name, proto] of INTRINSIC_PROTOS) {
        if (p === proto) return name;
      }
      p = O.getPrototypeOf(p);
      hops++;
    }
    return null;
  } catch {
    return '[unintrospectable]';
  }
}

function projectValue(v, state) {
  state.nodes++;
  if (state.nodes > MAX_NODES) return { t: 'nodecap' };
  switch (typeof v) {
    case 'undefined': return { t: 'undefined' };
    case 'boolean': return { t: 'bool', v };
    case 'number': return { t: 'num', v: numberRepr(v) };
    case 'bigint': return { t: 'bigint', v: O.apply(O.numberToString, v, []) };
    case 'string': return { t: 'str', v: escapeString(v) };
    case 'symbol': {
      const wk = WELL_KNOWN_SYMBOLS.get(v);
      if (wk) return { t: 'sym', wk };
      const d = O.apply(O.symbolDescription, v, []);
      return { t: 'sym', v: d === undefined ? null : escapeString(d) };
    }
    case 'function': {
      let name = null;
      try {
        const d = O.getOwnPropertyDescriptor(v, 'name');
        if (d && 'value' in d && typeof d.value === 'string') name = escapeString(d.value);
      } catch { /* proxy trap threw */ }
      return { t: 'fun', name };
    }
    case 'object': {
      if (v === null) return { t: 'null' };
      return projectObject(v, state);
    }
    default: return { t: 'unprintable' };
  }
}

function projectObject(obj, state) {
  const seen = state.seen.get(obj);
  if (seen !== undefined) return { t: 'circ', ref: seen };
  const id = state.nextId++;
  state.seen.set(obj, id);
  if (state.depth >= MAX_DEPTH) return { t: 'depthcap', id };

  const cls = classTag(obj);
  let keys;
  try {
    keys = O.ownKeys(obj); // spec order: integer ascending, insertion, symbols
  } catch {
    return { t: 'obj', id, cls, props: null, unintrospectable: true };
  }
  // Calibration ruling (2026-07-21): engines materialize DIFFERENT
  // engine-incidental own properties on Error instances (V8: a `stack`
  // accessor; JSC: `line`/`column`/`sourceURL`/`originalLine`/
  // `originalColumn` data props, sometimes a `stack` data prop). None are
  // spec observables — filter them from Error-class objects only, so a
  // user's own `stack` on a plain object still projects.
  if (cls !== null && (cls === 'Error:Error' || cls.startsWith('Error:'))) {
    keys = keys.filter((k) => typeof k !== 'string'
      || !ERROR_INCIDENTAL_KEYS.has(k));
  }
  const props = [];
  const n = keys.length > MAX_KEYS ? MAX_KEYS : keys.length;
  state.depth++;
  for (let i = 0; i < n; i++) {
    const k = keys[i];
    const keyRepr = typeof k === 'symbol'
      ? { sym: projectValue(k, state) }
      : escapeString(k);
    let d;
    try {
      d = O.getOwnPropertyDescriptor(obj, k);
    } catch {
      props.push([keyRepr, { t: 'unprintable' }]);
      continue;
    }
    if (d === undefined) { props.push([keyRepr, { t: 'vanished' }]); continue; }
    if ('value' in d) {
      // Data descriptor: print the value. Non-enumerability is itself an
      // observable (property order + attributes matter to the spec).
      const pv = projectValue(d.value, state);
      props.push([keyRepr, d.enumerable ? pv : { t: 'nonenum', v: pv }]);
    } else {
      // Accessor: NEVER invoke it (observation must not perturb).
      props.push([keyRepr, { t: 'accessor', get: !!d.get, set: !!d.set }]);
    }
  }
  state.depth--;
  const out = { t: 'obj', id, cls, props };
  if (keys.length > MAX_KEYS) out.keycap = keys.length;
  return out;
}

function project(v) {
  return projectValue(v, { seen: new Map(), nextId: 0, depth: 0, nodes: 0 });
}

// Thrown values: constructor identity + .name only — never message text.
function projectThrown(v) {
  if ((typeof v !== 'object' || v === null) && typeof v !== 'function') {
    return { t: 'prim', v: project(v) };
  }
  const cls = classTag(v);
  let name = null;
  try {
    // .name resolved through the prototype chain, data descriptors only —
    // Error.prototype.name is a data property, so intrinsic errors resolve
    // without running any user code.
    let o = v;
    let hops = 0;
    while (o !== null && hops < 32) {
      const d = O.getOwnPropertyDescriptor(o, 'name');
      if (d !== undefined) {
        if ('value' in d && typeof d.value === 'string') name = escapeString(d.value);
        break; // an accessor `name` shadows: record null rather than invoke
      }
      o = O.getPrototypeOf(o);
      hops++;
    }
  } catch { /* proxy trap threw: leave name null */ }
  // Constructor-name identity (e.g. Test262Error): proto.constructor.name,
  // both read as own DATA descriptors only — never invoked.
  let ctorName = null;
  try {
    const proto = O.getPrototypeOf(v);
    if (proto !== null) {
      const cd = O.getOwnPropertyDescriptor(proto, 'constructor');
      if (cd && 'value' in cd && typeof cd.value === 'function') {
        const nd = O.getOwnPropertyDescriptor(cd.value, 'name');
        if (nd && 'value' in nd && typeof nd.value === 'string') ctorName = escapeString(nd.value);
      }
    }
  } catch { /* proxy trap threw: leave ctorName null */ }
  return { t: 'error', ctor: cls, name, ctor_name: ctorName };
}

// ---------------------------------------------------------------------------
// 2. The trace accumulator + host-effect hooks.
// ---------------------------------------------------------------------------
const events = [];

function recordStdio(kind, args) {
  const vs = [];
  for (let i = 0; i < args.length; i++) vs.push(project(args[i]));
  events.push({ k: kind, v: vs });
}

function recordHost(name) {
  events.push({ k: 'host', v: name });
}

// ---------------------------------------------------------------------------
// 3. The nondeterminism firewall.
// ---------------------------------------------------------------------------
// Sources list kept in sync with tools/ts2rust/orca_classify.mjs (the ruled
// reuse source): Date.now, new Date, Math.random, fetch(, new Promise (ok:
// deterministic), process., fs., child_process, crypto, setTimeout/interval,
// locale/Intl, network.
const FIXED_EPOCH = 1700000000000;
let clockTicks = 0;

function installFirewall() {
  // Date: fixed epoch advancing 1ms per observation.
  const RealDate = Date;
  function now() { clockTicks++; return FIXED_EPOCH + clockTicks; }
  const TrustDate = function Date(...args) {
    if (new.target === undefined) {
      return O.apply(RealDate.prototype.toString, new RealDate(now()), []);
    }
    if (args.length === 0) return new RealDate(now());
    return new RealDate(...args);
  };
  TrustDate.prototype = RealDate.prototype;
  TrustDate.now = now;
  TrustDate.parse = RealDate.parse;
  TrustDate.UTC = RealDate.UTC;
  O.defineProperty(globalObj, 'Date', { value: TrustDate, writable: true, configurable: true });

  // Math.random: seeded mulberry32.
  let seed = 0xc0ffee ^ 0x9e3779b9;
  Math.random = function random() {
    seed |= 0; seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };

  // Virtual timers: deterministic queue drained after the main evaluation.
  installVirtualTimers();

  // Console: record + suppress.
  const mk = (kind) => function () { recordStdio(kind, arguments); };
  const c = globalObj.console ?? {};
  for (const m of ['log', 'info', 'debug', 'trace']) c[m] = mk('stdout');
  for (const m of ['warn', 'error']) c[m] = mk('stderr');
  globalObj.console = c;

  // test262 async harness channel + host print.
  O.defineProperty(globalObj, 'print', {
    value: function print(...args) { recordStdio('stdout', args); },
    writable: true, configurable: true,
  });

  // Record-and-refuse host escapes. `process` stays functional inside the
  // driver (we hold originals); the *global binding* user code sees records
  // and throws.
  for (const name of ['fetch', 'XMLHttpRequest', 'WebSocket']) {
    if (name in globalObj) {
      O.defineProperty(globalObj, name, {
        value: function () { recordHost(name); throw new TypeError('trust-js firewall: ' + name + ' is not permitted'); },
        writable: true, configurable: true,
      });
    }
  }
  const denyNs = (label) => new Proxy(function () {}, {
    get(_t, p) { recordHost(label + '.' + String(p)); throw new TypeError('trust-js firewall: ' + label + ' is not permitted'); },
    apply() { recordHost(label + '()'); throw new TypeError('trust-js firewall: ' + label + ' is not permitted'); },
  });
  try { O.defineProperty(globalObj, 'process', { value: denyNs('process'), writable: true, configurable: true }); } catch { /* engine refuses: recorded by calibration */ }
}

// Virtual timer queue: (time, seq)-ordered, microtask drain between
// callbacks, hard cap so runaway rescheduling terminates deterministically.
const TIMER_CAP = 10000;
let timerQueue = [];
let timerSeq = 0;
let virtualNow = 0;

function installVirtualTimers() {
  globalObj.setTimeout = function setTimeout(cb, delay, ...args) {
    if (typeof cb !== 'function') return 0;
    const t = { id: ++timerSeq, time: virtualNow + (Number(delay) || 0), cb, args, interval: null };
    timerQueue.push(t);
    return t.id;
  };
  globalObj.setInterval = function setInterval(cb, delay, ...args) {
    if (typeof cb !== 'function') return 0;
    const iv = Number(delay) || 0;
    const t = { id: ++timerSeq, time: virtualNow + iv, cb, args, interval: iv };
    timerQueue.push(t);
    return t.id;
  };
  const clear = (id) => { timerQueue = timerQueue.filter((t) => t.id !== id); };
  globalObj.clearTimeout = clear;
  globalObj.clearInterval = clear;
  if ('setImmediate' in globalObj) {
    globalObj.setImmediate = function setImmediate(cb, ...args) {
      return globalObj.setTimeout(cb, 0, ...args);
    };
    globalObj.clearImmediate = clear;
  }
}

async function drainMicrotasks() {
  // A bounded number of microtask checkpoints; each await yields one tick.
  for (let i = 0; i < 64; i++) await null;
}

// Has the async test262 completion signal been observed on the print channel?
// doneprintHandle.js prints exactly one string arg per $DONE call.
function sawAsyncCompletion() {
  for (let i = events.length - 1; i >= 0; i--) {
    const e = events[i];
    if (e.k === 'stdout' && e.v.length === 1 && e.v[0].t === 'str') {
      const s = e.v[0].v;
      if (s === 'Test262:AsyncTestComplete' || O.apply(String.prototype.startsWith, s, ['Test262:AsyncTestFailure:'])) {
        return true;
      }
    }
  }
  return false;
}

// Module-goal async settle: a `flags:[module, async]` test may complete only
// after its (possibly nested) file-based dynamic import() jobs settle on a real
// host/IO event-loop turn — which the virtual timer queue never pumps, so on an
// engine that defers those jobs past a microtask checkpoint (Bun/JSC) the $DONE
// marker would land AFTER emit and be lost (0 events) while another engine
// records 1. Give the REAL event loop bounded turns, interleaving the virtual
// microtask/timer drains, stopping as soon as the completion marker is observed
// so completion is engine-scheduling-independent. Bounded so a genuinely hung
// test still terminates deterministically.
async function settleModuleAsync() {
  for (let i = 0; i < 256; i++) {
    if (sawAsyncCompletion()) return;
    await new Promise((res) => O.realSetTimeout(res, 0));
    await drainMicrotasks();
  }
}

async function drainTimers() {
  let ran = 0;
  while (timerQueue.length > 0) {
    if (ran >= TIMER_CAP) { recordHost('timer-cap'); timerQueue = []; break; }
    // Deterministic pop: earliest time, then earliest id.
    let best = 0;
    for (let i = 1; i < timerQueue.length; i++) {
      const a = timerQueue[i], b = timerQueue[best];
      if (a.time < b.time || (a.time === b.time && a.id < b.id)) best = i;
    }
    const t = timerQueue[best];
    timerQueue.splice(best, 1);
    virtualNow = t.time;
    if (t.interval !== null) {
      timerQueue.push({ id: t.id, time: virtualNow + t.interval, cb: t.cb, args: t.args, interval: t.interval });
      if (ran + timerQueue.length > TIMER_CAP) { /* interval storm falls to cap */ }
    }
    ran++;
    try {
      t.cb(...t.args);
    } catch (e) {
      return { thrown: e };
    }
    await drainMicrotasks();
  }
  return null;
}

// ---------------------------------------------------------------------------
// 4. Emission.
// ---------------------------------------------------------------------------
const SENTINEL = '__TRUST_JS_TRACE_V1__';

function emit(completion) {
  const trace = {
    schema: 'trust.js.observable-trace.v1',
    caps: { depth: MAX_DEPTH, keys: MAX_KEYS, nodes: MAX_NODES, string: MAX_STRING, timers: TIMER_CAP },
    events,
    completion,
  };
  O.stdoutWrite('\n' + SENTINEL + O.jsonStringify(trace) + '\n');
  O.exit(0);
}

// ---------------------------------------------------------------------------
// 5. Case execution.
// ---------------------------------------------------------------------------
// Manifest: { includes: [path...], source: path, mode: "bare"|"strict"|"module",
//             kind: "script"|"module", async: bool, completion_witness: bool }
// completion_witness defaults false (calibration ruling: engines diverge on
// spec-corner eval completion values; the witness is for engine-vs-sem work).
//
// kind === "module": `source` is the REAL corpus test path. The harness
// includes evaluate first (sloppy scripts, shared globalThis), then the test is
// evaluated as an ES module via `await import(pathToFileURL(source))` so its
// relative imports (self-imports, ./x_FIXTURE.js siblings) resolve against the
// corpus directory. The trace projection (hooks, caps, sentinel, emit) is
// SHARED and unchanged — only the evaluation differs from the script goal.
async function main() {
  const manifestPath = argv[2];
  const manifest = JSON.parse(readFileSync(manifestPath, 'utf8'));

  const indirectEval = (0, eval);

  installFirewall();

  // Harness includes evaluate first, unstrict, in the shared global scope.
  for (const inc of manifest.includes) {
    const src = readFileSync(inc, 'utf8');
    try {
      indirectEval(src);
    } catch (e) {
      emit({ k: 'harness-include-error', v: projectThrown(e) });
      return;
    }
  }

  // Module goal: evaluate the real corpus module from its on-disk location so
  // relative imports resolve. ESM shares globalThis with the harness includes
  // installed above. The projection below (drain jobs, emit) is identical to
  // the script goal's tail — only indirectEval(body) is replaced by import().
  if (manifest.kind === 'module') {
    // A module whose top-level await REJECTS surfaces engine-asymmetrically:
    // Node rejects the import() promise (the catch below sees it), but Bun/JSC
    // reports it as an unhandled rejection / uncaught exception and would exit
    // the process WITHOUT a completion (a spurious harness error). Capture it on
    // the REAL process (the firewall only deny-proxies the global binding);
    // scoped to the module branch so the script goal's process semantics are
    // untouched.
    let moduleFault = null;
    try {
      process.on('unhandledRejection', (r) => { if (moduleFault === null) moduleFault = r; });
      process.on('uncaughtException', (e) => { if (moduleFault === null) moduleFault = e; });
    } catch { /* engine without process.on: falls back to the catch below */ }
    let completion;
    try {
      await import(pathToFileURL(manifest.source).href);
      await drainMicrotasks();
      // An async module test's completion may hinge on real-IO dynamic-import
      // jobs the virtual timer queue cannot pump; settle them on the real event
      // loop so the $DONE marker is engine-scheduling-independent (no-op for a
      // sync module, which has already printed nothing async to wait on).
      if (manifest.async === true) await settleModuleAsync();
      const timerFault = await drainTimers();
      await drainMicrotasks();
      if (moduleFault !== null) {
        completion = { k: 'throw', v: projectThrown(moduleFault), phase: 'module' };
      } else if (timerFault !== null) {
        completion = { k: 'throw', v: projectThrown(timerFault.thrown), phase: 'timer' };
      } else {
        completion = { k: 'normal' };
      }
    } catch (e) { completion = { k: 'throw', v: projectThrown(e) }; }
    emit(completion);
    return;
  }

  let body = readFileSync(manifest.source, 'utf8');
  if (manifest.mode === 'strict') body = '"use strict";\n' + body;

  // Async tests complete via print('Test262:AsyncTestComplete') — recorded as
  // an ordinary stdout event by the print hook; the harness-side checker
  // interprets it. Here we only distinguish sync completion vs throw.
  let completion;
  try {
    const value = indirectEval(body);
    await drainMicrotasks();
    const timerFault = await drainTimers();
    await drainMicrotasks();
    if (timerFault !== null) {
      completion = { k: 'throw', v: projectThrown(timerFault.thrown), phase: 'timer' };
    } else if (manifest.completion_witness === true) {
      completion = { k: 'normal', v: project(value) };
    } else {
      completion = { k: 'normal' };
    }
  } catch (e) {
    completion = { k: 'throw', v: projectThrown(e) };
  }
  emit(completion);
}

O.apply(O.promiseThen, main(), [undefined, (e) => {
  // A driver-internal failure is a harness error, not a test observable.
  try {
    O.stdoutWrite('\n' + SENTINEL + O.jsonStringify({
      schema: 'trust.js.observable-trace.v1',
      events: [],
      completion: { k: 'driver-error', v: projectThrown(e) },
    }) + '\n');
  } catch { /* nothing left to do */ }
  O.exit(1);
}]);
