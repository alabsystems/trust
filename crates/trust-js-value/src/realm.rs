// Realm construction: the intrinsic objects the S1a/S1b slices model, with
// exact spec attributes, plus the per-intrinsic MISS-DANGER sets — the list
// of own properties a real engine carries on each partially-modeled intrinsic
// that this model does not. Any own-property miss for a danger-listed name
// must refuse (never mis-answer `undefined` / fall through the chain past a
// property the engine would have found). A danger entry with EMPTY lists
// marks an object whose misses are safe but whose own-key ORDER is
// engine-incidental (full own-key reflection refuses). Name lists are the
// union of the spec surface and Node 24 / JSC observations.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::env::EnvFrame;
use crate::heap::Heap;
use crate::object::{ElemType, ErrKind, FnData, JsObject, ObjKind, PropKey, Property};
use crate::value::{JsValue, ObjId, SymId, WkSym};
use std::collections::HashMap;

/// Builtin function identities; dispatch lives in the interpreter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeFn {
    // Function machinery.
    FunctionProtoSelf,
    FunProtoCall,
    FunProtoApply,
    FunProtoBind,
    FunProtoHasInstance,
    FunctionCtor,
    // Object.
    ObjectCtor,
    ObjectKeys,
    ObjectValues,
    ObjectEntries,
    ObjectAssign,
    ObjectFromEntries,
    ObjectGetOwnPropertyNames,
    ObjectGetOwnPropertySymbols,
    ObjectDefineProperty,
    ObjectDefineProperties,
    ObjectGetOwnPropertyDescriptor,
    ObjectGetOwnPropertyDescriptors,
    ObjectGetPrototypeOf,
    ObjectSetPrototypeOf,
    ObjectCreate,
    ObjectIs,
    ObjectHasOwn,
    ObjectFreeze,
    ObjectSeal,
    ObjectIsFrozen,
    ObjectIsSealed,
    ObjectPreventExtensions,
    ObjectIsExtensible,
    ObjProtoToString,
    ObjProtoToLocaleString,
    ObjProtoValueOf,
    ObjProtoHasOwnProperty,
    ObjProtoIsPrototypeOf,
    ObjProtoPropertyIsEnumerable,
    // Array.
    ArrayCtor,
    ArrayIsArray,
    ArrayFrom,
    ArrayOf,
    ArrayJoin,
    ArrayToString,
    ArrayPush,
    ArrayPop,
    ArrayShift,
    ArrayUnshift,
    ArrayIndexOf,
    ArrayLastIndexOf,
    ArrayIncludes,
    ArraySlice,
    ArraySplice,
    ArrayMap,
    ArrayForEach,
    ArrayEvery,
    ArraySome,
    ArrayFilter,
    ArrayFind { last: bool, index: bool },
    ArrayFill,
    ArrayCopyWithin,
    ArrayFlat,
    ArrayFlatMap,
    ArrayReduce { right: bool },
    ArrayReverse,
    ArraySort,
    ArrayAt,
    ArrayConcat,
    ArrayToReversed,
    ArrayToSorted,
    ArrayToSpliced,
    ArrayWith,
    /// `get [Symbol.species]` — returns `this`.
    SpeciesGetter,
    /// %Array.prototype.values% (23.1.3.36) — also Array.prototype[@@iterator]
    /// and the arguments object's @@iterator (shared identity). Returns a fresh
    /// Array Iterator object (value kind).
    ArrayValues,
    /// %Array.prototype.keys% (23.1.3.17) — a fresh Array Iterator (key kind).
    ArrayKeys,
    /// %Array.prototype.entries% (23.1.3.5) — a fresh Array Iterator
    /// (key+value kind).
    ArrayEntries,
    // String / Number / Boolean.
    StringCtor,
    StringFromCharCode,
    StringFromCodePoint,
    StringRaw,
    StringProtoToString,
    StringProtoValueOf,
    StringCharAt,
    StringCharCodeAt,
    StringCodePointAt,
    StringAt,
    StringIndexOf,
    StringLastIndexOf,
    StringIncludes,
    StringStartsWith,
    StringEndsWith,
    StringSlice,
    StringSubstring,
    StringSplit,
    /// String.prototype.match / search — dispatch through the argument's
    /// @@match / @@search (S1d).
    StringMatch,
    StringSearch,
    /// String.prototype.matchAll — dispatch through the argument's @@matchAll,
    /// else RegExpCreate(regexp, "g") then Invoke(@@matchAll) (S1e).
    StringMatchAll,
    StringCase { upper: bool },
    StringTrim { start: bool, end: bool },
    StringRepeat,
    StringPad { start: bool },
    StringConcat,
    StringReplace { all: bool },
    StringIsWellFormed,
    StringToWellFormed,
    /// %String.prototype[@@iterator]% (22.1.3.34) — a fresh String Iterator
    /// object (iterates by code point).
    StringProtoIterator,
    NumberCtor,
    NumberIsFinite,
    NumberIsInteger,
    NumberIsNaN,
    NumberIsSafeInteger,
    NumberProtoToString,
    NumberProtoValueOf,
    BooleanCtor,
    BooleanProtoToString,
    BooleanProtoValueOf,
    // Symbol.
    SymbolCtor,
    SymbolFor,
    SymbolKeyFor,
    SymbolProtoToString,
    SymbolProtoValueOf,
    SymbolProtoDescription,
    SymbolToPrimitive,
    // BigInt.
    BigIntCtor,
    BigIntAsIntN,
    BigIntAsUintN,
    BigIntProtoToString,
    BigIntProtoValueOf,
    // Errors.
    ErrorCtor(ErrKind),
    AggregateErrorCtor,
    ErrorProtoToString,
    // Reflect.
    ReflectApply,
    ReflectConstruct,
    ReflectDefineProperty,
    ReflectDeleteProperty,
    ReflectGet,
    ReflectGetOwnPropertyDescriptor,
    ReflectGetPrototypeOf,
    ReflectHas,
    ReflectIsExtensible,
    ReflectOwnKeys,
    ReflectPreventExtensions,
    ReflectSet,
    ReflectSetPrototypeOf,
    // Map / Set / WeakMap / WeakSet (S1c).
    MapCtor,
    SetCtor,
    WeakMapCtor,
    WeakSetCtor,
    MapGet,
    MapSet,
    MapHas,
    MapDelete,
    MapClear,
    MapForEach,
    MapSizeGetter,
    MapGetOrInsert,
    MapGetOrInsertComputed,
    /// %Map.prototype.entries% (identity: Map.prototype[Symbol.iterator]);
    /// returns a fresh Map Iterator object (key+value kind).
    MapEntries,
    MapKeys,
    MapValues,
    SetAdd,
    SetHas,
    SetDelete,
    SetClear,
    SetForEach,
    SetSizeGetter,
    /// %Set.prototype.values% (identity: Set.prototype.keys AND
    /// Set.prototype[Symbol.iterator]); returns a fresh Set Iterator object.
    SetValues,
    SetEntries,
    WeakMapGet,
    WeakMapSet,
    WeakMapHas,
    WeakMapDelete,
    WeakMapGetOrInsert,
    WeakMapGetOrInsertComputed,
    WeakSetAdd,
    WeakSetHas,
    WeakSetDelete,
    // WeakRef / FinalizationRegistry (§26.1 / §26.2). GC/finalization is
    // unobservable in the synchronous S0 slice (no callback ever fires), so the
    // object model + methods are exact and finalization timing refuses by
    // simply never occurring. `[[WeakRefTarget]]` and `[[Cells]]` live in the
    // interpreter side tables keyed by ObjId.
    WeakRefCtor,
    WeakRefDeref,
    FinalizationRegistryCtor,
    FinRegRegister,
    FinRegUnregister,
    // Iterator global (§27.1): the abstract constructor (throws on direct
    // construct, subclassable) + the %Iterator.prototype% `constructor` and
    // @@toStringTag accessors. The iterator-helper methods (map/filter/take/...)
    // are proposal-surface Node/Bun ship but this slice does not model: they
    // stay danger-listed on %Iterator.prototype% and refuse (NoCoverage).
    IteratorCtor,
    /// `get %Iterator.prototype%.constructor` — returns %Iterator%.
    IteratorProtoCtorGet,
    /// `set %Iterator.prototype%.constructor` — SetterThatIgnoresPrototypeProperties.
    IteratorProtoCtorSet,
    /// `get %Iterator.prototype%[@@toStringTag]` — returns "Iterator".
    IteratorProtoTagGet,
    /// `set %Iterator.prototype%[@@toStringTag]` — SetterThatIgnoresPrototypeProperties.
    IteratorProtoTagSet,
    // §27.1.4 Iterator helper methods on %Iterator.prototype%. The lazy adapters
    // (map/filter/take/drop/flatMap) each return an Iterator Helper object
    // (%IteratorHelperPrototype%); the eager consumers drive the iterator to
    // completion / short-circuit. All perform GetIteratorDirect(this) — reading
    // `next` off the receiver — and never call @@iterator on it.
    IteratorProtoMap,
    IteratorProtoFilter,
    IteratorProtoTake,
    IteratorProtoDrop,
    IteratorProtoFlatMap,
    IteratorProtoReduce,
    IteratorProtoToArray,
    IteratorProtoForEach,
    IteratorProtoSome,
    IteratorProtoEvery,
    IteratorProtoFind,
    /// %IteratorHelperPrototype%.next (27.1.4.2.1) — GeneratorResume over the
    /// captured helper closure (state in the interpreter's `helper_state`).
    IteratorHelperNext,
    /// %IteratorHelperPrototype%.return (27.1.4.2.2) — close the underlying
    /// iterator and complete the helper.
    IteratorHelperReturn,
    // Date (S1c). The DRIVER replaces the global `Date` with a deterministic
    // wrapper (fixed epoch + 1ms tick); the wrapper and the real constructor
    // are distinct observables and both are modeled.
    DateWrapperCtor,
    DateRealCtor,
    /// The wrapper's deterministic `Date.now` (fixed epoch + tick).
    DateNow,
    /// The REAL `Date.prototype.constructor.now` — real clock, refuses.
    DateRealNow,
    DateParse,
    DateUtc,
    DateGetField { field: DateField, utc: bool },
    DateSetField { field: DateSetKind, utc: bool },
    DateGetTime,
    DateSetTime,
    DateGetTimezoneOffset,
    DateValueOf,
    DateToIsoString,
    DateToJson,
    DateToUtcString,
    DateToString,
    DateToDateString,
    DateToTimeString,
    DateToPrimitive,
    DateGetYear,
    DateSetYear,
    // RegExp (S1c skeleton: literals + accessors; matching is S1d).
    RegExpCtor,
    RegexSourceGetter,
    RegexFlagsGetter,
    RegexFlagGetter(RegexFlagKind),
    RegexToString,
    /// A RegExp.prototype method dispatched by tag (S1d): compile/exec/test/
    /// @@match/@@replace/@@search/@@split are live; @@matchAll returns a
    /// %RegExpStringIterator% (S1e, ruled in builtins_regexp.rs).
    RegexProtoMethod(&'static str),
    // Proxy (§10.5): the constructor plus `Proxy.revocable`; a per-proxy
    // revoker closure (its target proxy lives in the interpreter's
    // `revoke_targets` side table keyed by the revoker's `ObjId`).
    ProxyCtor,
    ProxyRevocable,
    ProxyRevoke,
    // URI handling (fully specified — exact).
    EncodeUri { component: bool },
    DecodeUri { component: bool },
    // Misc globals.
    JsonParse,
    JsonStringify,
    IsNaN,
    IsFinite,
    ParseInt,
    ParseFloat,
    /// The `eval` binding: modeled as a value; CALLING it is S1f, refuses.
    EvalFn,
    MathFloor,
    MathCeil,
    MathTrunc,
    MathAbs,
    MathPow,
    MathMax,
    MathMin,
    MathRound,
    MathSign,
    MathSqrt,
    MathImul,
    MathClz32,
    MathFround,
    /// console.log/info/debug/trace (stderr=false) or warn/error (true) —
    /// the driver's anonymous recorder functions.
    ConsoleWrite { stderr: bool },
    /// The test262 `print` hook the driver installs.
    Print,
    /// %ThrowTypeError%.
    ThrowTypeError,
    // Generators / iterators (S1e).
    /// %IteratorPrototype%[@@iterator]: returns `this`.
    IteratorProtoIterator,
    /// %ArrayIteratorPrototype%.next (23.1.5.2.1) — brand: Array Iterator
    /// (covers both Array and TypedArray iterators, which share this prototype).
    ArrayIteratorNext,
    /// %StringIteratorPrototype%.next (22.1.5.2.1).
    StringIteratorNext,
    /// %MapIteratorPrototype%.next (24.1.5.2.1).
    MapIteratorNext,
    /// %SetIteratorPrototype%.next (24.2.5.2.1).
    SetIteratorNext,
    /// %RegExpStringIteratorPrototype%.next (22.2.9.2.1) — brand: RegExp String
    /// Iterator (the object returned by String.prototype.matchAll /
    /// RegExp.prototype[@@matchAll]).
    RegExpStringIteratorNext,
    /// %GeneratorPrototype%.next / .return / .throw.
    GeneratorNext,
    GeneratorReturn,
    GeneratorThrow,
    /// %GeneratorFunction% — the (hidden) GeneratorFunction constructor.
    /// Identity + prototype graph are exact; call/construct are eval-like and
    /// refuse (NoCoverage).
    GeneratorFunctionCtor,
    /// %AsyncGeneratorPrototype%.next / .return / .throw (§27.6.1).
    AsyncGeneratorNext,
    AsyncGeneratorReturn,
    AsyncGeneratorThrow,
    /// %AsyncIteratorPrototype%[@@asyncIterator] — returns `this` (§27.1.3).
    AsyncIteratorProtoSelf,
    /// %AsyncGeneratorFunction% — the (hidden) AsyncGeneratorFunction
    /// constructor. Identity + prototype graph exact; call/construct refuse.
    AsyncGeneratorFunctionCtor,
    // -- Binary data (§25 ArrayBuffer/DataView, §23.2 TypedArray) --
    ArrayBufferCtor,
    ArrayBufferIsView,
    ArrayBufferByteLengthGetter,
    ArrayBufferMaxByteLengthGetter,
    ArrayBufferResizableGetter,
    ArrayBufferDetachedGetter,
    ArrayBufferSlice,
    ArrayBufferResize,
    /// transfer (to_fixed=false) / transferToFixedLength (to_fixed=true).
    ArrayBufferTransfer { to_fixed: bool },
    DataViewCtor,
    DataViewBufferGetter,
    DataViewByteLengthGetter,
    DataViewByteOffsetGetter,
    DataViewGet(ElemType),
    DataViewSet(ElemType),
    /// %TypedArray% (the abstract base): [[Call]]/[[Construct]] throw.
    TypedArrayBaseCtor,
    /// A concrete typed-array constructor (Int8Array, ...).
    TypedArrayCtor(ElemType),
    TypedArrayFrom,
    TypedArrayOf,
    TaBufferGetter,
    TaByteLengthGetter,
    TaByteOffsetGetter,
    TaLengthGetter,
    TaToStringTagGetter,
    /// A shared %TypedArray%.prototype method, dispatched by tag.
    TaProtoMethod(&'static str),
    // -- §27.2 Promise + the event loop (M2 D1) -----------------------------
    /// `Promise(executor)` constructor.
    PromiseCtor,
    /// `Promise.resolve` / `Promise.reject`.
    PromiseResolve,
    PromiseReject,
    /// `Promise.all` / `allSettled` / `race` / `any`.
    PromiseAll,
    PromiseAllSettled,
    PromiseRace,
    PromiseAny,
    /// `Promise.prototype.then` / `catch` / `finally`.
    PromiseProtoThen,
    PromiseProtoCatch,
    PromiseProtoFinally,
    /// `Promise.try` / `Promise.withResolvers`.
    PromiseTry,
    PromiseWithResolvers,
    /// The hidden `%AsyncFunction%` constructor: CreateDynamicFunction("async").
    AsyncFunctionCtor,
    /// A CreateResolvingFunctions resolve/reject function (the executor's
    /// arguments, and the thenable-assimilation capabilities). The bound
    /// `Capability` lives in the interpreter's `resolve_caps` side table keyed
    /// by the function object's `ObjId`.
    PromiseResolveFn,
    PromiseRejectFn,
    /// A finally value-transform thunk: returns (or throws) a captured value,
    /// ignoring its argument. Captured value in `thunk_values`, keyed by ObjId.
    PromiseValueThunk,
    PromiseThrowThunk,
    /// GetCapabilitiesExecutor: the `new C(executor)` executor a subclass /
    /// arbitrary constructor receiver participates through (NewPromiseCapability,
    /// 27.2.1.5.1). Captures the resolve/reject arguments into the shared
    /// `cap_states` record keyed by the executor function object's `ObjId`.
    PromiseCapExecutor,
    /// The combinator per-element closures for a non-intrinsic receiver C
    /// (Promise.all / allSettled / any Resolve/Reject Element functions). Their
    /// aggregation state lives in `comb_elements`, keyed by the element function
    /// object's `ObjId`. `race` needs none (it wires the result capability's
    /// resolve/reject directly).
    PromiseAllResolveElement,
    PromiseAllSettledResolveElement,
    PromiseAllSettledRejectElement,
    PromiseAnyRejectElement,
    /// `queueMicrotask(cb)`.
    QueueMicrotask,
    /// The event-loop timer surface (onto the reactor's virtual timers).
    SetTimeout,
    SetInterval,
    ClearTimer,
    // Explicit resource management (ES2026 §14.3.3 / §27.3). The SYNC half:
    // `using` declarations dispose at scope exit, plus the `SuppressedError`
    // constructor and the `DisposableStack` class. The async surface
    // (`await using`, `AsyncDisposableStack`, @@asyncDispose) stays
    // NoCoverage — those constructs refuse rather than run.
    SuppressedErrorCtor,
    DisposableStackCtor,
    DisposableStackUse,
    DisposableStackAdopt,
    DisposableStackDefer,
    DisposableStackMove,
    DisposableStackDispose,
    DisposableStackDisposedGetter,
}

/// Date component addressed by a `get*` accessor family member.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DateField {
    FullYear,
    Month,
    Date,
    Day,
    Hours,
    Minutes,
    Seconds,
    Milliseconds,
}

/// Leading component of a `set*` family member (its arity/coercion list).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DateSetKind {
    FullYear,
    Month,
    Date,
    Hours,
    Minutes,
    Seconds,
    Milliseconds,
}

/// One RegExp flag accessor identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegexFlagKind {
    HasIndices,
    Global,
    IgnoreCase,
    Multiline,
    DotAll,
    Unicode,
    UnicodeSets,
    Sticky,
}

/// The miss-danger classification for one intrinsic object.
#[derive(Debug, Clone)]
pub enum Danger {
    /// Every own miss refuses (fully opaque host surface, e.g. console).
    All,
    /// A miss refuses iff the name/symbol is engine-real-but-unmodeled.
    /// EMPTY lists still mark the object own-key-ORDER-opaque (full own-key
    /// reflection refuses; misses are safe).
    Listed {
        names: &'static [&'static str],
        syms: &'static [WkSym],
    },
}

// Engine-real own properties NOT modeled, per intrinsic (spec ∪ Node 24 ∪
// known JSC extras). Modeled properties are present in the heap and never
// reach the miss path.
const OBJECT_PROTO_DANGER: &[&str] = &[
    "__proto__",
    "__defineGetter__",
    "__defineSetter__",
    "__lookupGetter__",
    "__lookupSetter__",
];
const FUNCTION_PROTO_DANGER: &[&str] = &["arguments", "caller", "toString"];
const ARRAY_PROTO_DANGER: &[&str] = &["group", "groupToMap", "toLocaleString"];
// `match`/`search`/`matchAll` are modeled (S1d/S1e); matchAll returns a
// %RegExpStringIterator% (iterobj.rs). The HTML-wrapper legacy methods and the
// locale-dependent surface stay danger-listed.
const STRING_PROTO_DANGER: &[&str] = &[
    "anchor", "big", "blink", "bold", "fontcolor", "fontsize", "fixed", "italics", "link",
    "localeCompare", "normalize", "small", "strike", "sub",
    "substr", "sup", "toLocaleLowerCase", "toLocaleUpperCase",
];
const NUMBER_PROTO_DANGER: &[&str] =
    &["toExponential", "toFixed", "toPrecision", "toLocaleString"];
const OBJECT_CTOR_DANGER: &[&str] = &["groupBy"];
const ARRAY_CTOR_DANGER: &[&str] = &["fromAsync"];
// `dispose` / `asyncDispose` are now MODELED (explicit resource management),
// so they are no longer danger-listed. `metadata` (decorator metadata) stays
// unmodeled and refuses on access.
const SYMBOL_CTOR_DANGER: &[&str] = &["metadata"];
const ERROR_CTOR_DANGER: &[&str] =
    &["captureStackTrace", "prepareStackTrace", "isError", "stackTraceLimit"];
const JSON_DANGER: &[&str] = &["rawJSON", "isRawJSON"];
// ES2025 set-methods surface (union/intersection/...): real on both engines,
// unmodeled here — any touch refuses.
const SET_PROTO_DANGER: &[&str] = &[
    "difference", "intersection", "isDisjointFrom", "isSubsetOf", "isSupersetOf",
    "symmetricDifference", "union",
];
const MAP_CTOR_DANGER: &[&str] = &["groupBy"];
// %IteratorPrototype% own surface. The Iterator Helper methods
// (map/filter/take/drop/flatMap + reduce/toArray/forEach/some/every/find) are
// now MODELED (§27.1.4, iterhelp.rs), so they are no longer danger-listed.
// `constructor` and @@toStringTag are MODELED accessors; @@iterator is MODELED.
// A miss for a name NOT here (notably `return`/`throw`, absent on the real
// prototype) resolves soundly to undefined, so IteratorClose over a built-in
// iterator object is a correct no-op instead of an over-conservative refusal.
// @@dispose is real on the engine prototype but UNREACHABLE here (Symbol.dispose
// itself refuses at the SYMBOL_CTOR_DANGER gate), so it needs no entry. Node and
// Bun agree on this surface.
const ITERATOR_PROTO_DANGER: &[&str] = &[];
// %Iterator% static iterator-sequencing helpers (unmodeled; any miss refuses).
const ITERATOR_CTOR_DANGER: &[&str] = &["from", "concat", "zip", "zipKeyed"];
const DATE_PROTO_DANGER: &[&str] =
    &["toLocaleString", "toLocaleDateString", "toLocaleTimeString"];
// Legacy RegExp statics (engine-real on V8 and JSC) + RegExp.escape.
const REGEXP_CTOR_DANGER: &[&str] = &[
    "escape", "input", "lastMatch", "lastParen", "leftContext", "rightContext", "multiline",
    "$1", "$2", "$3", "$4", "$5", "$6", "$7", "$8", "$9", "$_", "$&", "$+", "$`", "$'",
];
const MATH_DANGER: &[&str] = &[
    "acos", "acosh", "asin", "asinh", "atan", "atanh", "atan2", "cbrt", "expm1", "clz32", "cos",
    "cosh", "exp", "fround", "f16round", "hypot", "log", "log1p", "log2", "log10", "random",
    "sin", "sinh", "sqrt", "tan", "tanh",
];

/// Own properties engines materialize on native Error INSTANCES (V8 `stack`;
/// JSC positional data). A miss for one of these on an Error-kind object
/// refuses.
pub const ERROR_INSTANCE_DANGER: &[&str] =
    &["stack", "line", "column", "sourceURL", "originalLine", "originalColumn"];

/// The realm intrinsics table.
pub struct Intrinsics {
    pub object_proto: ObjId,
    pub function_proto: ObjId,
    pub array_proto: ObjId,
    pub string_proto: ObjId,
    pub number_proto: ObjId,
    pub boolean_proto: ObjId,
    pub symbol_proto: ObjId,
    pub bigint_proto: ObjId,
    pub error_proto: ObjId,
    pub type_error_proto: ObjId,
    pub range_error_proto: ObjId,
    pub reference_error_proto: ObjId,
    pub syntax_error_proto: ObjId,
    pub eval_error_proto: ObjId,
    pub uri_error_proto: ObjId,
    pub aggregate_error_proto: ObjId,
    pub object_ctor: ObjId,
    pub function_ctor: ObjId,
    pub array_ctor: ObjId,
    pub string_ctor: ObjId,
    pub number_ctor: ObjId,
    pub boolean_ctor: ObjId,
    pub symbol_ctor: ObjId,
    pub bigint_ctor: ObjId,
    pub error_ctor: ObjId,
    pub aggregate_error_ctor: ObjId,
    pub math: ObjId,
    pub json: ObjId,
    pub reflect: ObjId,
    pub console: ObjId,
    pub throw_type_error: ObjId,
    /// %Array.prototype.values% (identity for the arguments @@iterator).
    pub array_values_fn: ObjId,
    /// %Function.prototype[Symbol.hasInstance]% (identity check in
    /// instanceof).
    pub fn_has_instance: ObjId,
    // -- S1c intrinsics --
    pub map_proto: ObjId,
    pub set_proto: ObjId,
    pub weakmap_proto: ObjId,
    pub weakset_proto: ObjId,
    pub date_proto: ObjId,
    pub regexp_proto: ObjId,
    pub map_ctor: ObjId,
    pub set_ctor: ObjId,
    pub weakmap_ctor: ObjId,
    pub weakset_ctor: ObjId,
    // -- §26 WeakRef / FinalizationRegistry --
    pub weakref_proto: ObjId,
    pub weakref_ctor: ObjId,
    pub finreg_proto: ObjId,
    pub finreg_ctor: ObjId,
    // -- §27.1 Iterator (the abstract global constructor) --
    /// %Iterator% — the abstract Iterator constructor. Its `.prototype` IS the
    /// existing %IteratorPrototype% (`iterator_proto`).
    pub iterator_ctor: ObjId,
    /// The DRIVER's deterministic `Date` wrapper (the global binding).
    pub date_wrapper_ctor: ObjId,
    /// The real Date constructor (%Date%, reachable as
    /// `Date.prototype.constructor`).
    pub date_real_ctor: ObjId,
    pub regexp_ctor: ObjId,
    pub proxy_ctor: ObjId,
    /// %Map.prototype.entries% (identity: Map.prototype[Symbol.iterator]).
    /// %IteratorPrototype% — the root of the iterator prototype chain.
    pub iterator_proto: ObjId,
    /// %ArrayIteratorPrototype% (23.1.5.2) — [[Prototype]] of the objects
    /// returned by Array/TypedArray values/keys/entries + their @@iterator.
    pub array_iterator_proto: ObjId,
    /// %StringIteratorPrototype% (22.1.5.2).
    pub string_iterator_proto: ObjId,
    /// %MapIteratorPrototype% (24.1.5.2).
    pub map_iterator_proto: ObjId,
    /// %SetIteratorPrototype% (24.2.5.2).
    pub set_iterator_proto: ObjId,
    /// %RegExpStringIteratorPrototype% (22.2.9.2) — [[Prototype]] of the
    /// objects returned by String.prototype.matchAll / RegExp.prototype
    /// [@@matchAll].
    pub regexp_string_iterator_proto: ObjId,
    /// %IteratorHelperPrototype% (27.1.4.2) — [[Prototype]] of the Iterator
    /// Helper objects returned by map/filter/take/drop/flatMap. Its
    /// [[Prototype]] is %IteratorPrototype%; own `next`/`return` +
    /// @@toStringTag "Iterator Helper".
    pub iterator_helper_proto: ObjId,
    /// %String.prototype[@@iterator]% (identity for the pristine-string fast
    /// path: a tampered String.prototype @@iterator falls to the user protocol).
    pub string_iterator_fn: ObjId,
    /// The intrinsic `next` of each built-in iterator prototype. The internal
    /// fast-iteration paths only apply while the relevant prototype's `next` is
    /// still one of these (a patched `next` falls to the general protocol).
    pub array_iterator_next_fn: ObjId,
    pub string_iterator_next_fn: ObjId,
    pub map_iterator_next_fn: ObjId,
    pub set_iterator_next_fn: ObjId,
    pub regexp_string_iterator_next_fn: ObjId,
    /// %GeneratorFunction.prototype% — the [[Prototype]] of every generator
    /// FUNCTION object; carries constructor/@@toStringTag/prototype.
    pub generator_function_proto: ObjId,
    /// %GeneratorFunction.prototype.prototype% (a.k.a. %GeneratorPrototype%) —
    /// the [[Prototype]] chain root for generator INSTANCES (next/return/throw).
    pub generator_proto: ObjId,
    /// %GeneratorFunction% — the hidden GeneratorFunction constructor.
    pub generator_function_ctor: ObjId,
    pub map_entries_fn: ObjId,
    /// %Set.prototype.values% (identity: keys and [Symbol.iterator]).
    pub set_values_fn: ObjId,
    // -- §27.2 Promise + async functions (M2) --
    pub promise_proto: ObjId,
    pub promise_ctor: ObjId,
    /// %AsyncFunction.prototype% — [[Prototype]] of every async function
    /// object; carries constructor/@@toStringTag (no `.prototype`).
    pub async_function_proto: ObjId,
    /// %AsyncFunction% — the hidden AsyncFunction constructor (not a global).
    pub async_function_ctor: ObjId,
    /// %AsyncIteratorPrototype% (§27.1.3) — the root of the async-iterator
    /// prototype chain; carries @@asyncIterator (returns `this`).
    pub async_iterator_proto: ObjId,
    /// %AsyncGeneratorPrototype% (§27.6.1) — the [[Prototype]] chain root for
    /// async generator INSTANCES (next/return/throw + @@toStringTag).
    pub async_generator_proto: ObjId,
    /// %AsyncGeneratorFunction.prototype% (§27.4.3) — the [[Prototype]] of every
    /// async generator FUNCTION object.
    pub async_generator_function_proto: ObjId,
    /// %AsyncGeneratorFunction% — the hidden AsyncGeneratorFunction constructor.
    pub async_generator_function_ctor: ObjId,
    // -- Binary data --
    pub array_buffer_proto: ObjId,
    pub array_buffer_ctor: ObjId,
    pub data_view_proto: ObjId,
    pub data_view_ctor: ObjId,
    /// %TypedArray%.prototype (the shared prototype).
    pub typed_array_proto: ObjId,
    /// %TypedArray% (the abstract base constructor).
    pub typed_array_ctor: ObjId,
    /// Per-element-type concrete `.prototype` objects, indexed by
    /// `ElemType::idx`.
    pub ta_protos: [ObjId; 12],
    /// Per-element-type concrete constructor objects, indexed by
    /// `ElemType::idx`.
    pub ta_ctors: [ObjId; 12],
    /// %TypedArray%.prototype.values (identity for @@iterator).
    pub ta_values_fn: ObjId,
    // -- Explicit resource management (sync half) --
    /// %SuppressedError.prototype% (chains to %Error.prototype%; deliberately
    /// NOT in the class-tag list, so instances tag as "Error:Error" — matching
    /// the driver, whose INTRINSIC_PROTOS omits SuppressedError).
    pub suppressed_error_proto: ObjId,
    /// %DisposableStack.prototype% (chains to %Object.prototype%; NOT in the
    /// class-tag list, so instances tag as "Object" — matching the driver).
    pub disposable_stack_proto: ObjId,
    /// %DisposableStack% — needed by `DisposableStack.prototype.move`.
    pub disposable_stack_ctor: ObjId,
    /// The realm's @@dispose well-known symbol (a User symbol with description
    /// "Symbol.dispose"; the driver projects it by description, NOT as a
    /// well-known symbol, so a User symbol matches exactly).
    pub dispose_sym: SymId,
    /// The realm's @@asyncDispose well-known symbol (description
    /// "Symbol.asyncDispose"). Modeled for identity/reflection; no sync
    /// disposal ever consults it.
    pub async_dispose_sym: SymId,
    /// Per-intrinsic miss-danger sets.
    pub danger: HashMap<ObjId, Danger>,
}

impl Intrinsics {
    /// Driver INTRINSIC_PROTOS order (the subset that exists in the slice) —
    /// nearest-intrinsic-prototype class tagging must match it exactly.
    #[must_use]
    pub fn class_tag_list(&self) -> [(ObjId, &'static str); 23] {
        [
            (self.array_proto, "Array"),
            (self.function_proto, "Function"),
            (self.error_proto, "Error:Error"),
            (self.type_error_proto, "Error:TypeError"),
            (self.range_error_proto, "Error:RangeError"),
            (self.reference_error_proto, "Error:ReferenceError"),
            (self.syntax_error_proto, "Error:SyntaxError"),
            (self.eval_error_proto, "Error:EvalError"),
            (self.uri_error_proto, "Error:URIError"),
            (self.aggregate_error_proto, "Error:AggregateError"),
            (self.regexp_proto, "RegExp"),
            (self.date_proto, "Date"),
            (self.map_proto, "Map"),
            (self.set_proto, "Set"),
            (self.weakmap_proto, "WeakMap"),
            (self.weakset_proto, "WeakSet"),
            (self.promise_proto, "Promise"),
            (self.boolean_proto, "Boolean"),
            (self.number_proto, "Number"),
            (self.string_proto, "String"),
            (self.symbol_proto, "Symbol"),
            (self.bigint_proto, "BigInt"),
            (self.object_proto, "Object"),
        ]
    }

    /// The element type of a concrete typed-array `.prototype`, if `oid` is one.
    #[must_use]
    pub fn ta_elem_by_proto(&self, oid: ObjId) -> Option<ElemType> {
        ElemType::ALL.into_iter().find(|et| self.ta_protos[et.idx()] == oid)
    }

    /// The element type of a concrete typed-array constructor, if `oid` is one.
    #[must_use]
    pub fn ta_elem_by_ctor(&self, oid: ObjId) -> Option<ElemType> {
        ElemType::ALL.into_iter().find(|et| self.ta_ctors[et.idx()] == oid)
    }

    #[must_use]
    pub fn error_proto_for(&self, kind: ErrKind) -> ObjId {
        match kind {
            ErrKind::Error => self.error_proto,
            ErrKind::Type => self.type_error_proto,
            ErrKind::Range => self.range_error_proto,
            ErrKind::Reference => self.reference_error_proto,
            ErrKind::Syntax => self.syntax_error_proto,
            ErrKind::Eval => self.eval_error_proto,
            ErrKind::Uri => self.uri_error_proto,
            ErrKind::Aggregate => self.aggregate_error_proto,
        }
    }

    /// The danger classification of a MISSED own key on `oid`, if any.
    #[must_use]
    pub fn miss_danger(&self, oid: ObjId, key: &PropKey) -> Option<String> {
        // @@dispose / @@asyncDispose are engine-real on the iterator prototypes
        // (%Iterator.prototype%[@@dispose] closes the iterator;
        // %AsyncIteratorPrototype%[@@asyncDispose] its async analogue) but are
        // NOT modeled here. A miss on these exact (prototype, symbol) pairs must
        // refuse (NoCoverage) rather than answer `undefined` — the symbols
        // became reachable once Symbol.dispose/asyncDispose were modeled.
        if let PropKey::Sym(s) = key {
            if (oid == self.iterator_proto && *s == self.dispose_sym)
                || (oid == self.async_iterator_proto && *s == self.async_dispose_sym)
            {
                return Some(
                    "unmodeled iterator explicit-resource-management method \
                     (@@dispose / @@asyncDispose)"
                        .to_string(),
                );
            }
        }
        let d = self.danger.get(&oid)?;
        match d {
            Danger::All => Some(format!(
                "own miss `{}` on an opaque host intrinsic",
                key.describe()
            )),
            Danger::Listed { names, syms } => match key {
                PropKey::Str(u) => {
                    let name = crate::units::units_to_lossy(u);
                    if names.contains(&name.as_str()) {
                        Some(format!("unimplemented intrinsic property `{name}`"))
                    } else {
                        None
                    }
                }
                PropKey::Sym(SymId::WellKnown(wk)) => {
                    if syms.contains(wk) {
                        Some(format!(
                            "unimplemented intrinsic symbol property `{}`",
                            wk.projection_name()
                        ))
                    } else {
                        None
                    }
                }
                PropKey::Sym(SymId::User(_)) => None,
            },
        }
    }
}

/// A constructed realm: intrinsics + the global object.
pub struct Realm {
    pub intr: Intrinsics,
    pub global: ObjId,
}

struct B<'h> {
    heap: &'h mut Heap,
}

impl B<'_> {
    fn put(&mut self, oid: ObjId, key: &str, p: Property) {
        self.heap
            .obj_mut(oid)
            .props
            .insert(PropKey::from_str(key), p);
    }

    fn put_sym(&mut self, oid: ObjId, sym: WkSym, p: Property) {
        self.heap
            .obj_mut(oid)
            .props
            .insert(PropKey::Sym(SymId::WellKnown(sym)), p);
    }

    /// A builtin function object: name/length per builtin convention.
    /// Own-key ORDER is a spec observable (test262 Function/property-order):
    /// CreateBuiltinFunction installs `length` BEFORE `name`.
    fn mk_fn(&mut self, fproto: ObjId, name: &str, len: f64, nf: NativeFn) -> ObjId {
        let f = self
            .heap
            .alloc(JsObject::new(ObjKind::Function(FnData::Native(nf)), Some(fproto)));
        self.put(f, "length", Property::with_attrs(JsValue::Num(len), false, false, true));
        self.put(f, "name", Property::with_attrs(JsValue::str_from(name), false, false, true));
        f
    }

    /// A driver-created ordinary function (console recorders, `print`): like
    /// a user function expression, it has a `.prototype` object.
    fn mk_driver_fn(&mut self, fproto: ObjId, oproto: ObjId, name: &str, nf: NativeFn) -> ObjId {
        let f = self.mk_fn(fproto, name, 0.0, nf);
        let proto_obj = self.heap.alloc(JsObject::new(ObjKind::Plain, Some(oproto)));
        self.put(
            proto_obj,
            "constructor",
            Property::with_attrs(JsValue::Obj(f), true, false, true),
        );
        self.put(
            f,
            "prototype",
            Property::with_attrs(JsValue::Obj(proto_obj), true, false, false),
        );
        f
    }
}

/// Build the realm into `heap`. Also allocates the root environment frame
/// (env 0) with `this` = the global object.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn create_realm(heap: &mut Heap) -> Realm {
    let mut b = B { heap };

    let object_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, None));
    let function_proto = b.heap.alloc(JsObject::new(
        ObjKind::Function(FnData::Native(NativeFn::FunctionProtoSelf)),
        Some(object_proto),
    ));
    b.put(function_proto, "length", Property::with_attrs(JsValue::Num(0.0), false, false, true));
    b.put(function_proto, "name", Property::with_attrs(JsValue::str_from(""), false, false, true));

    // Array.prototype is an Array exotic object per spec.
    let array_proto = b.heap.alloc(JsObject::new(ObjKind::Array, Some(object_proto)));
    b.put(array_proto, "length", Property::with_attrs(JsValue::Num(0.0), true, false, false));

    // Wrapper prototypes carry [[StringData]]/[[NumberData]]/[[BooleanData]]
    // per spec history; modeled as hosts, identity-special-cased where the
    // slot is observable (Object.prototype.toString, thisXxxValue).
    let string_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    b.put(string_proto, "length", Property::with_attrs(JsValue::Num(0.0), false, false, false));
    let number_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let boolean_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let symbol_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let bigint_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));

    // Error prototypes: ordinary objects; name/message data props per spec.
    let error_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    b.put(error_proto, "name", Property::method(JsValue::str_from("Error")));
    b.put(error_proto, "message", Property::method(JsValue::str_from("")));
    let mk_err_proto = |b: &mut B<'_>, name: &str| {
        let p = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(error_proto)));
        b.put(p, "name", Property::method(JsValue::str_from(name)));
        b.put(p, "message", Property::method(JsValue::str_from("")));
        p
    };
    let type_error_proto = mk_err_proto(&mut b, "TypeError");
    let range_error_proto = mk_err_proto(&mut b, "RangeError");
    let reference_error_proto = mk_err_proto(&mut b, "ReferenceError");
    let syntax_error_proto = mk_err_proto(&mut b, "SyntaxError");
    let eval_error_proto = mk_err_proto(&mut b, "EvalError");
    let uri_error_proto = mk_err_proto(&mut b, "URIError");
    let aggregate_error_proto = mk_err_proto(&mut b, "AggregateError");
    // %SuppressedError.prototype% — chains to %Error.prototype% like every
    // other NativeError prototype; NOT added to the class-tag list, so a thrown
    // SuppressedError classifies as "Error:Error" (the driver's INTRINSIC_PROTOS
    // omits SuppressedError), with `.name` = "SuppressedError".
    let suppressed_error_proto = mk_err_proto(&mut b, "SuppressedError");

    // %ThrowTypeError%: frozen anonymous function.
    let throw_type_error = b.heap.alloc(JsObject::new(
        ObjKind::Function(FnData::Native(NativeFn::ThrowTypeError)),
        Some(function_proto),
    ));
    b.put(throw_type_error, "length", Property::frozen(JsValue::Num(0.0)));
    b.put(throw_type_error, "name", Property::frozen(JsValue::str_from("")));
    b.heap.obj_mut(throw_type_error).extensible = false;

    // Object.prototype methods.
    for (name, len, nf) in [
        ("toString", 0.0, NativeFn::ObjProtoToString),
        ("toLocaleString", 0.0, NativeFn::ObjProtoToLocaleString),
        ("valueOf", 0.0, NativeFn::ObjProtoValueOf),
        ("hasOwnProperty", 1.0, NativeFn::ObjProtoHasOwnProperty),
        ("isPrototypeOf", 1.0, NativeFn::ObjProtoIsPrototypeOf),
        ("propertyIsEnumerable", 1.0, NativeFn::ObjProtoPropertyIsEnumerable),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(object_proto, name, Property::method(JsValue::Obj(m)));
    }

    // Function.prototype methods + @@hasInstance.
    for (name, len, nf) in [
        ("call", 1.0, NativeFn::FunProtoCall),
        ("apply", 2.0, NativeFn::FunProtoApply),
        ("bind", 1.0, NativeFn::FunProtoBind),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(function_proto, name, Property::method(JsValue::Obj(m)));
    }
    let fn_has_instance =
        b.mk_fn(function_proto, "[Symbol.hasInstance]", 1.0, NativeFn::FunProtoHasInstance);
    b.put_sym(
        function_proto,
        WkSym::HasInstance,
        Property::frozen(JsValue::Obj(fn_has_instance)),
    );

    // Array.prototype methods.
    for (name, len, nf) in [
        ("at", 1.0, NativeFn::ArrayAt),
        ("concat", 1.0, NativeFn::ArrayConcat),
        ("copyWithin", 2.0, NativeFn::ArrayCopyWithin),
        ("every", 1.0, NativeFn::ArrayEvery),
        ("fill", 1.0, NativeFn::ArrayFill),
        ("filter", 1.0, NativeFn::ArrayFilter),
        ("find", 1.0, NativeFn::ArrayFind { last: false, index: false }),
        ("findIndex", 1.0, NativeFn::ArrayFind { last: false, index: true }),
        ("findLast", 1.0, NativeFn::ArrayFind { last: true, index: false }),
        ("findLastIndex", 1.0, NativeFn::ArrayFind { last: true, index: true }),
        ("flat", 0.0, NativeFn::ArrayFlat),
        ("flatMap", 1.0, NativeFn::ArrayFlatMap),
        ("forEach", 1.0, NativeFn::ArrayForEach),
        ("includes", 1.0, NativeFn::ArrayIncludes),
        ("indexOf", 1.0, NativeFn::ArrayIndexOf),
        ("join", 1.0, NativeFn::ArrayJoin),
        ("lastIndexOf", 1.0, NativeFn::ArrayLastIndexOf),
        ("map", 1.0, NativeFn::ArrayMap),
        ("pop", 0.0, NativeFn::ArrayPop),
        ("push", 1.0, NativeFn::ArrayPush),
        ("reduce", 1.0, NativeFn::ArrayReduce { right: false }),
        ("reduceRight", 1.0, NativeFn::ArrayReduce { right: true }),
        ("reverse", 0.0, NativeFn::ArrayReverse),
        ("shift", 0.0, NativeFn::ArrayShift),
        ("slice", 2.0, NativeFn::ArraySlice),
        ("some", 1.0, NativeFn::ArraySome),
        ("sort", 1.0, NativeFn::ArraySort),
        ("splice", 2.0, NativeFn::ArraySplice),
        ("toReversed", 0.0, NativeFn::ArrayToReversed),
        ("toSorted", 1.0, NativeFn::ArrayToSorted),
        ("toSpliced", 2.0, NativeFn::ArrayToSpliced),
        ("toString", 0.0, NativeFn::ArrayToString),
        ("unshift", 1.0, NativeFn::ArrayUnshift),
        ("with", 2.0, NativeFn::ArrayWith),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(array_proto, name, Property::method(JsValue::Obj(m)));
    }
    // %Array.prototype.values% — installed on Array.prototype, ALSO the
    // arguments object's own @@iterator (shared identity), and (by identity)
    // Array.prototype[Symbol.iterator].
    let array_values_fn = b.mk_fn(function_proto, "values", 0.0, NativeFn::ArrayValues);
    b.put(array_proto, "values", Property::method(JsValue::Obj(array_values_fn)));
    let array_keys_fn = b.mk_fn(function_proto, "keys", 0.0, NativeFn::ArrayKeys);
    b.put(array_proto, "keys", Property::method(JsValue::Obj(array_keys_fn)));
    let array_entries_fn = b.mk_fn(function_proto, "entries", 0.0, NativeFn::ArrayEntries);
    b.put(array_proto, "entries", Property::method(JsValue::Obj(array_entries_fn)));
    // Array.prototype[Symbol.iterator] IS %Array.prototype.values% (identity).
    b.put_sym(array_proto, WkSym::Iterator, Property::method(JsValue::Obj(array_values_fn)));

    // String/Number/Boolean/Symbol prototype methods.
    for (name, len, nf) in [
        ("toString", 0.0, NativeFn::StringProtoToString),
        ("valueOf", 0.0, NativeFn::StringProtoValueOf),
        ("at", 1.0, NativeFn::StringAt),
        ("charAt", 1.0, NativeFn::StringCharAt),
        ("charCodeAt", 1.0, NativeFn::StringCharCodeAt),
        ("codePointAt", 1.0, NativeFn::StringCodePointAt),
        ("concat", 1.0, NativeFn::StringConcat),
        ("endsWith", 1.0, NativeFn::StringEndsWith),
        ("includes", 1.0, NativeFn::StringIncludes),
        ("indexOf", 1.0, NativeFn::StringIndexOf),
        ("isWellFormed", 0.0, NativeFn::StringIsWellFormed),
        ("lastIndexOf", 1.0, NativeFn::StringLastIndexOf),
        ("match", 1.0, NativeFn::StringMatch),
        ("matchAll", 1.0, NativeFn::StringMatchAll),
        ("search", 1.0, NativeFn::StringSearch),
        ("padEnd", 1.0, NativeFn::StringPad { start: false }),
        ("padStart", 1.0, NativeFn::StringPad { start: true }),
        ("repeat", 1.0, NativeFn::StringRepeat),
        ("replace", 2.0, NativeFn::StringReplace { all: false }),
        ("replaceAll", 2.0, NativeFn::StringReplace { all: true }),
        ("slice", 2.0, NativeFn::StringSlice),
        ("split", 2.0, NativeFn::StringSplit),
        ("startsWith", 1.0, NativeFn::StringStartsWith),
        ("substring", 2.0, NativeFn::StringSubstring),
        ("toLowerCase", 0.0, NativeFn::StringCase { upper: false }),
        ("toUpperCase", 0.0, NativeFn::StringCase { upper: true }),
        ("toWellFormed", 0.0, NativeFn::StringToWellFormed),
        ("trim", 0.0, NativeFn::StringTrim { start: true, end: true }),
        ("trimEnd", 0.0, NativeFn::StringTrim { start: false, end: true }),
        ("trimStart", 0.0, NativeFn::StringTrim { start: true, end: false }),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(string_proto, name, Property::method(JsValue::Obj(m)));
    }
    // Annex B aliases: trimLeft/trimRight ARE trimStart/trimEnd (identity).
    for (alias, canon) in [("trimLeft", "trimStart"), ("trimRight", "trimEnd")] {
        let f = b
            .heap
            .obj(string_proto)
            .props
            .get(&PropKey::from_str(canon))
            .and_then(Property::data_value)
            .cloned()
            .expect("canonical trim installed");
        b.put(string_proto, alias, Property::method(f));
    }
    // String.prototype[Symbol.iterator] (22.1.3.34): iterates by code point.
    let string_iterator_fn =
        b.mk_fn(function_proto, "[Symbol.iterator]", 0.0, NativeFn::StringProtoIterator);
    b.put_sym(string_proto, WkSym::Iterator, Property::method(JsValue::Obj(string_iterator_fn)));
    for (name, nf) in [
        ("toString", NativeFn::NumberProtoToString),
        ("valueOf", NativeFn::NumberProtoValueOf),
    ] {
        let len = if name == "toString" { 1.0 } else { 0.0 };
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(number_proto, name, Property::method(JsValue::Obj(m)));
    }
    for (name, nf) in [
        ("toString", NativeFn::BooleanProtoToString),
        ("valueOf", NativeFn::BooleanProtoValueOf),
    ] {
        let m = b.mk_fn(function_proto, name, 0.0, nf);
        b.put(boolean_proto, name, Property::method(JsValue::Obj(m)));
    }
    // Symbol.prototype: toString/valueOf/description/@@toPrimitive/@@toStringTag.
    for (name, nf) in [
        ("toString", NativeFn::SymbolProtoToString),
        ("valueOf", NativeFn::SymbolProtoValueOf),
    ] {
        let m = b.mk_fn(function_proto, name, 0.0, nf);
        b.put(symbol_proto, name, Property::method(JsValue::Obj(m)));
    }
    let desc_get = b.mk_fn(function_proto, "get description", 0.0, NativeFn::SymbolProtoDescription);
    b.put(
        symbol_proto,
        "description",
        Property::accessor(Some(desc_get), None, false, true),
    );
    let sym_to_prim = b.mk_fn(function_proto, "[Symbol.toPrimitive]", 1.0, NativeFn::SymbolToPrimitive);
    b.put_sym(
        symbol_proto,
        WkSym::ToPrimitive,
        Property::with_attrs(JsValue::Obj(sym_to_prim), false, false, true),
    );
    b.put_sym(
        symbol_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("Symbol"), false, false, true),
    );

    // BigInt.prototype: toString/toLocaleString/valueOf/@@toStringTag.
    for (name, len, nf) in [
        ("toString", 0.0, NativeFn::BigIntProtoToString),
        ("toLocaleString", 0.0, NativeFn::BigIntProtoToString),
        ("valueOf", 0.0, NativeFn::BigIntProtoValueOf),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(bigint_proto, name, Property::method(JsValue::Obj(m)));
    }
    b.put_sym(
        bigint_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("BigInt"), false, false, true),
    );

    // Error.prototype.toString.
    let m = b.mk_fn(function_proto, "toString", 0.0, NativeFn::ErrorProtoToString);
    b.put(error_proto, "toString", Property::method(JsValue::Obj(m)));

    // Constructors. `fparent` is the constructor's own [[Prototype]]
    // (NativeError constructors inherit from %Error%).
    let mk_ctor_on =
        |b: &mut B<'_>, fparent: ObjId, name: &str, len: f64, nf: NativeFn, proto: ObjId| {
            let c = b.mk_fn(fparent, name, len, nf);
            b.put(c, "prototype", Property::frozen(JsValue::Obj(proto)));
            b.put(proto, "constructor", Property::method(JsValue::Obj(c)));
            c
        };
    let mk_ctor = |b: &mut B<'_>, name: &str, len: f64, nf: NativeFn, proto: ObjId| {
        mk_ctor_on(b, function_proto, name, len, nf, proto)
    };
    let object_ctor = mk_ctor(&mut b, "Object", 1.0, NativeFn::ObjectCtor, object_proto);
    let function_ctor = mk_ctor(&mut b, "Function", 1.0, NativeFn::FunctionCtor, function_proto);
    let array_ctor = mk_ctor(&mut b, "Array", 1.0, NativeFn::ArrayCtor, array_proto);
    let string_ctor = mk_ctor(&mut b, "String", 1.0, NativeFn::StringCtor, string_proto);
    let number_ctor = mk_ctor(&mut b, "Number", 1.0, NativeFn::NumberCtor, number_proto);
    let boolean_ctor = mk_ctor(&mut b, "Boolean", 1.0, NativeFn::BooleanCtor, boolean_proto);
    let symbol_ctor = mk_ctor(&mut b, "Symbol", 0.0, NativeFn::SymbolCtor, symbol_proto);
    let bigint_ctor = mk_ctor(&mut b, "BigInt", 1.0, NativeFn::BigIntCtor, bigint_proto);
    let error_ctor = mk_ctor(&mut b, "Error", 1.0, NativeFn::ErrorCtor(ErrKind::Error), error_proto);
    let type_error_ctor = mk_ctor_on(
        &mut b, error_ctor, "TypeError", 1.0, NativeFn::ErrorCtor(ErrKind::Type), type_error_proto,
    );
    let range_error_ctor = mk_ctor_on(
        &mut b, error_ctor, "RangeError", 1.0, NativeFn::ErrorCtor(ErrKind::Range), range_error_proto,
    );
    let reference_error_ctor = mk_ctor_on(
        &mut b,
        error_ctor,
        "ReferenceError",
        1.0,
        NativeFn::ErrorCtor(ErrKind::Reference),
        reference_error_proto,
    );
    let syntax_error_ctor = mk_ctor_on(
        &mut b,
        error_ctor,
        "SyntaxError",
        1.0,
        NativeFn::ErrorCtor(ErrKind::Syntax),
        syntax_error_proto,
    );
    let eval_error_ctor = mk_ctor_on(
        &mut b, error_ctor, "EvalError", 1.0, NativeFn::ErrorCtor(ErrKind::Eval), eval_error_proto,
    );
    let uri_error_ctor = mk_ctor_on(
        &mut b, error_ctor, "URIError", 1.0, NativeFn::ErrorCtor(ErrKind::Uri), uri_error_proto,
    );
    let aggregate_error_ctor = mk_ctor_on(
        &mut b,
        error_ctor,
        "AggregateError",
        2.0,
        NativeFn::AggregateErrorCtor,
        aggregate_error_proto,
    );
    // SuppressedError ( error, suppressed, message ). `length` is 3, inherits
    // from %Error% (like the other NativeError constructors).
    let suppressed_error_ctor = mk_ctor_on(
        &mut b,
        error_ctor,
        "SuppressedError",
        3.0,
        NativeFn::SuppressedErrorCtor,
        suppressed_error_proto,
    );

    // Object statics.
    for (name, len, nf) in [
        ("assign", 2.0, NativeFn::ObjectAssign),
        ("create", 2.0, NativeFn::ObjectCreate),
        ("defineProperties", 2.0, NativeFn::ObjectDefineProperties),
        ("defineProperty", 3.0, NativeFn::ObjectDefineProperty),
        ("entries", 1.0, NativeFn::ObjectEntries),
        ("freeze", 1.0, NativeFn::ObjectFreeze),
        ("fromEntries", 1.0, NativeFn::ObjectFromEntries),
        ("getOwnPropertyDescriptor", 2.0, NativeFn::ObjectGetOwnPropertyDescriptor),
        ("getOwnPropertyDescriptors", 1.0, NativeFn::ObjectGetOwnPropertyDescriptors),
        ("getOwnPropertyNames", 1.0, NativeFn::ObjectGetOwnPropertyNames),
        ("getOwnPropertySymbols", 1.0, NativeFn::ObjectGetOwnPropertySymbols),
        ("getPrototypeOf", 1.0, NativeFn::ObjectGetPrototypeOf),
        ("hasOwn", 2.0, NativeFn::ObjectHasOwn),
        ("is", 2.0, NativeFn::ObjectIs),
        ("isExtensible", 1.0, NativeFn::ObjectIsExtensible),
        ("isFrozen", 1.0, NativeFn::ObjectIsFrozen),
        ("isSealed", 1.0, NativeFn::ObjectIsSealed),
        ("keys", 1.0, NativeFn::ObjectKeys),
        ("preventExtensions", 1.0, NativeFn::ObjectPreventExtensions),
        ("seal", 1.0, NativeFn::ObjectSeal),
        ("setPrototypeOf", 2.0, NativeFn::ObjectSetPrototypeOf),
        ("values", 1.0, NativeFn::ObjectValues),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(object_ctor, name, Property::method(JsValue::Obj(m)));
    }
    // Array statics + @@species.
    for (name, len, nf) in [
        ("from", 1.0, NativeFn::ArrayFrom),
        ("isArray", 1.0, NativeFn::ArrayIsArray),
        ("of", 0.0, NativeFn::ArrayOf),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(array_ctor, name, Property::method(JsValue::Obj(m)));
    }
    let species_get = b.mk_fn(function_proto, "get [Symbol.species]", 0.0, NativeFn::SpeciesGetter);
    b.put_sym(
        array_ctor,
        WkSym::Species,
        Property::accessor(Some(species_get), None, false, true),
    );
    // String statics.
    for (name, len, nf) in [
        ("fromCharCode", 1.0, NativeFn::StringFromCharCode),
        ("fromCodePoint", 1.0, NativeFn::StringFromCodePoint),
        ("raw", 1.0, NativeFn::StringRaw),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(string_ctor, name, Property::method(JsValue::Obj(m)));
    }
    // Number statics (parseInt/parseFloat share identity with the globals).
    let parse_int_fn = b.mk_fn(function_proto, "parseInt", 2.0, NativeFn::ParseInt);
    let parse_float_fn = b.mk_fn(function_proto, "parseFloat", 1.0, NativeFn::ParseFloat);
    for (name, len, nf) in [
        ("isFinite", 1.0, NativeFn::NumberIsFinite),
        ("isInteger", 1.0, NativeFn::NumberIsInteger),
        ("isNaN", 1.0, NativeFn::NumberIsNaN),
        ("isSafeInteger", 1.0, NativeFn::NumberIsSafeInteger),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(number_ctor, name, Property::method(JsValue::Obj(m)));
    }
    b.put(number_ctor, "parseFloat", Property::method(JsValue::Obj(parse_float_fn)));
    b.put(number_ctor, "parseInt", Property::method(JsValue::Obj(parse_int_fn)));
    for (name, v) in [
        ("MAX_VALUE", f64::MAX),
        ("MIN_VALUE", 5e-324),
        ("NaN", f64::NAN),
        ("NEGATIVE_INFINITY", f64::NEG_INFINITY),
        ("POSITIVE_INFINITY", f64::INFINITY),
        ("MAX_SAFE_INTEGER", 9_007_199_254_740_991.0),
        ("MIN_SAFE_INTEGER", -9_007_199_254_740_991.0),
        ("EPSILON", f64::EPSILON),
    ] {
        b.put(number_ctor, name, Property::frozen(JsValue::Num(v)));
    }
    // Symbol statics: for/keyFor + the well-known symbols as frozen values.
    for (name, len, nf) in [
        ("for", 1.0, NativeFn::SymbolFor),
        ("keyFor", 1.0, NativeFn::SymbolKeyFor),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(symbol_ctor, name, Property::method(JsValue::Obj(m)));
    }
    for (name, wk) in [
        ("asyncIterator", WkSym::AsyncIterator),
        ("hasInstance", WkSym::HasInstance),
        ("isConcatSpreadable", WkSym::IsConcatSpreadable),
        ("iterator", WkSym::Iterator),
        ("match", WkSym::Match),
        ("matchAll", WkSym::MatchAll),
        ("replace", WkSym::Replace),
        ("search", WkSym::Search),
        ("species", WkSym::Species),
        ("split", WkSym::Split),
        ("toPrimitive", WkSym::ToPrimitive),
        ("toStringTag", WkSym::ToStringTag),
        ("unscopables", WkSym::Unscopables),
    ] {
        b.put(symbol_ctor, name, Property::frozen(JsValue::Sym(SymId::WellKnown(wk))));
    }
    // @@dispose / @@asyncDispose (explicit resource management). Modeled as
    // per-realm USER symbols with descriptions "Symbol.dispose" /
    // "Symbol.asyncDispose": the driver's WELL_KNOWN_SYMBOLS map omits them, so
    // it projects them by description — a User symbol matches that exactly,
    // where a synthetic well-known variant would mis-project as `wk`.
    let dispose_sym = b
        .heap
        .alloc_symbol(Some(crate::units::units_from_str("Symbol.dispose")));
    let async_dispose_sym = b
        .heap
        .alloc_symbol(Some(crate::units::units_from_str("Symbol.asyncDispose")));
    b.put(symbol_ctor, "dispose", Property::frozen(JsValue::Sym(dispose_sym)));
    b.put(
        symbol_ctor,
        "asyncDispose",
        Property::frozen(JsValue::Sym(async_dispose_sym)),
    );

    // BigInt statics: asIntN / asUintN.
    for (name, nf) in [
        ("asIntN", NativeFn::BigIntAsIntN),
        ("asUintN", NativeFn::BigIntAsUintN),
    ] {
        let m = b.mk_fn(function_proto, name, 2.0, nf);
        b.put(bigint_ctor, name, Property::method(JsValue::Obj(m)));
    }

    // Math.
    let math = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    for (name, len, nf) in [
        ("abs", 1.0, NativeFn::MathAbs),
        ("ceil", 1.0, NativeFn::MathCeil),
        ("clz32", 1.0, NativeFn::MathClz32),
        ("floor", 1.0, NativeFn::MathFloor),
        ("fround", 1.0, NativeFn::MathFround),
        ("imul", 2.0, NativeFn::MathImul),
        ("max", 2.0, NativeFn::MathMax),
        ("min", 2.0, NativeFn::MathMin),
        ("pow", 2.0, NativeFn::MathPow),
        ("round", 1.0, NativeFn::MathRound),
        ("sign", 1.0, NativeFn::MathSign),
        ("sqrt", 1.0, NativeFn::MathSqrt),
        ("trunc", 1.0, NativeFn::MathTrunc),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(math, name, Property::method(JsValue::Obj(m)));
    }
    for (name, v) in [
        ("E", std::f64::consts::E),
        ("LN10", std::f64::consts::LN_10),
        ("LN2", std::f64::consts::LN_2),
        ("LOG10E", std::f64::consts::LOG10_E),
        ("LOG2E", std::f64::consts::LOG2_E),
        ("PI", std::f64::consts::PI),
        ("SQRT1_2", std::f64::consts::FRAC_1_SQRT_2),
        ("SQRT2", std::f64::consts::SQRT_2),
    ] {
        b.put(math, name, Property::frozen(JsValue::Num(v)));
    }
    b.put_sym(
        math,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("Math"), false, false, true),
    );

    // JSON.
    let json = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let m = b.mk_fn(function_proto, "stringify", 3.0, NativeFn::JsonStringify);
    b.put(json, "stringify", Property::method(JsValue::Obj(m)));
    b.put_sym(
        json,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("JSON"), false, false, true),
    );

    // Reflect.
    let reflect = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    for (name, len, nf) in [
        ("apply", 3.0, NativeFn::ReflectApply),
        ("construct", 2.0, NativeFn::ReflectConstruct),
        ("defineProperty", 3.0, NativeFn::ReflectDefineProperty),
        ("deleteProperty", 2.0, NativeFn::ReflectDeleteProperty),
        ("get", 2.0, NativeFn::ReflectGet),
        ("getOwnPropertyDescriptor", 2.0, NativeFn::ReflectGetOwnPropertyDescriptor),
        ("getPrototypeOf", 1.0, NativeFn::ReflectGetPrototypeOf),
        ("has", 2.0, NativeFn::ReflectHas),
        ("isExtensible", 1.0, NativeFn::ReflectIsExtensible),
        ("ownKeys", 1.0, NativeFn::ReflectOwnKeys),
        ("preventExtensions", 1.0, NativeFn::ReflectPreventExtensions),
        ("set", 3.0, NativeFn::ReflectSet),
        ("setPrototypeOf", 2.0, NativeFn::ReflectSetPrototypeOf),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(reflect, name, Property::method(JsValue::Obj(m)));
    }
    b.put_sym(
        reflect,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("Reflect"), false, false, true),
    );

    // -- S1c: Map / Set / WeakMap / WeakSet ---------------------------------
    let map_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let set_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let weakmap_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let weakset_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));

    for (name, len, nf) in [
        ("clear", 0.0, NativeFn::MapClear),
        ("delete", 1.0, NativeFn::MapDelete),
        ("forEach", 1.0, NativeFn::MapForEach),
        ("get", 1.0, NativeFn::MapGet),
        ("getOrInsert", 2.0, NativeFn::MapGetOrInsert),
        ("getOrInsertComputed", 2.0, NativeFn::MapGetOrInsertComputed),
        ("has", 1.0, NativeFn::MapHas),
        ("keys", 0.0, NativeFn::MapKeys),
        ("set", 2.0, NativeFn::MapSet),
        ("values", 0.0, NativeFn::MapValues),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(map_proto, name, Property::method(JsValue::Obj(m)));
    }
    let map_entries_fn = b.mk_fn(function_proto, "entries", 0.0, NativeFn::MapEntries);
    b.put(map_proto, "entries", Property::method(JsValue::Obj(map_entries_fn)));
    let map_size_get = b.mk_fn(function_proto, "get size", 0.0, NativeFn::MapSizeGetter);
    b.put(map_proto, "size", Property::accessor(Some(map_size_get), None, false, true));
    // Map.prototype[Symbol.iterator] IS %Map.prototype.entries% (identity).
    b.put_sym(
        map_proto,
        WkSym::Iterator,
        Property::method(JsValue::Obj(map_entries_fn)),
    );
    b.put_sym(
        map_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("Map"), false, false, true),
    );

    for (name, len, nf) in [
        ("add", 1.0, NativeFn::SetAdd),
        ("clear", 0.0, NativeFn::SetClear),
        ("delete", 1.0, NativeFn::SetDelete),
        ("entries", 0.0, NativeFn::SetEntries),
        ("forEach", 1.0, NativeFn::SetForEach),
        ("has", 1.0, NativeFn::SetHas),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(set_proto, name, Property::method(JsValue::Obj(m)));
    }
    let set_values_fn = b.mk_fn(function_proto, "values", 0.0, NativeFn::SetValues);
    b.put(set_proto, "values", Property::method(JsValue::Obj(set_values_fn)));
    // Set.prototype.keys IS %Set.prototype.values% (identity), and so is
    // Set.prototype[Symbol.iterator].
    b.put(set_proto, "keys", Property::method(JsValue::Obj(set_values_fn)));
    let set_size_get = b.mk_fn(function_proto, "get size", 0.0, NativeFn::SetSizeGetter);
    b.put(set_proto, "size", Property::accessor(Some(set_size_get), None, false, true));
    b.put_sym(
        set_proto,
        WkSym::Iterator,
        Property::method(JsValue::Obj(set_values_fn)),
    );
    b.put_sym(
        set_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("Set"), false, false, true),
    );

    for (name, len, nf) in [
        ("delete", 1.0, NativeFn::WeakMapDelete),
        ("get", 1.0, NativeFn::WeakMapGet),
        ("getOrInsert", 2.0, NativeFn::WeakMapGetOrInsert),
        ("getOrInsertComputed", 2.0, NativeFn::WeakMapGetOrInsertComputed),
        ("has", 1.0, NativeFn::WeakMapHas),
        ("set", 2.0, NativeFn::WeakMapSet),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(weakmap_proto, name, Property::method(JsValue::Obj(m)));
    }
    b.put_sym(
        weakmap_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("WeakMap"), false, false, true),
    );
    for (name, len, nf) in [
        ("add", 1.0, NativeFn::WeakSetAdd),
        ("delete", 1.0, NativeFn::WeakSetDelete),
        ("has", 1.0, NativeFn::WeakSetHas),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(weakset_proto, name, Property::method(JsValue::Obj(m)));
    }
    b.put_sym(
        weakset_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("WeakSet"), false, false, true),
    );

    let map_ctor = mk_ctor(&mut b, "Map", 0.0, NativeFn::MapCtor, map_proto);
    let set_ctor = mk_ctor(&mut b, "Set", 0.0, NativeFn::SetCtor, set_proto);
    let weakmap_ctor = mk_ctor(&mut b, "WeakMap", 0.0, NativeFn::WeakMapCtor, weakmap_proto);
    let weakset_ctor = mk_ctor(&mut b, "WeakSet", 0.0, NativeFn::WeakSetCtor, weakset_proto);
    for ctor in [map_ctor, set_ctor] {
        let sg = b.mk_fn(function_proto, "get [Symbol.species]", 0.0, NativeFn::SpeciesGetter);
        b.put_sym(ctor, WkSym::Species, Property::accessor(Some(sg), None, false, true));
    }

    // -- §26.1 WeakRef ------------------------------------------------------
    // WeakRef.prototype: proto = %Object.prototype%; own deref + @@toStringTag
    // ("WeakRef", a data property). The instance's [[WeakRefTarget]] lives in
    // the interpreter side table; the instance object is an ordinary object
    // whose class tag resolves to "Object" (the prototype is NOT in the driver
    // class-tag list — verified vs Node 24 / Bun).
    let weakref_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let weakref_deref = b.mk_fn(function_proto, "deref", 0.0, NativeFn::WeakRefDeref);
    b.put(weakref_proto, "deref", Property::method(JsValue::Obj(weakref_deref)));
    b.put_sym(
        weakref_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("WeakRef"), false, false, true),
    );
    let weakref_ctor = mk_ctor(&mut b, "WeakRef", 1.0, NativeFn::WeakRefCtor, weakref_proto);

    // -- §26.2 FinalizationRegistry -----------------------------------------
    // FinalizationRegistry.prototype: register/unregister + @@toStringTag. The
    // [[CleanupCallback]] + [[Cells]] live in the side table; no cleanup ever
    // runs (finalization is unobservable in the synchronous slice), so register
    // records a cell and unregister reports whether a matching token existed.
    let finreg_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let finreg_register = b.mk_fn(function_proto, "register", 2.0, NativeFn::FinRegRegister);
    b.put(finreg_proto, "register", Property::method(JsValue::Obj(finreg_register)));
    let finreg_unregister = b.mk_fn(function_proto, "unregister", 1.0, NativeFn::FinRegUnregister);
    b.put(finreg_proto, "unregister", Property::method(JsValue::Obj(finreg_unregister)));
    b.put_sym(
        finreg_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("FinalizationRegistry"), false, false, true),
    );
    let finreg_ctor =
        mk_ctor(&mut b, "FinalizationRegistry", 1.0, NativeFn::FinalizationRegistryCtor, finreg_proto);

    // -- §27.3 DisposableStack (sync explicit resource management) -----------
    // %DisposableStack.prototype%: proto = %Object.prototype%; own methods
    // use/adopt/defer/move/dispose, the `disposed` accessor, @@dispose (an
    // ALIAS of `dispose`), @@toStringTag. The instance's [[DisposableState]] +
    // [[DisposeCapability]] live in the interpreter side table, so the object
    // is ordinary and its class tag resolves to "Object" (the prototype is NOT
    // in the driver class-tag list — matches Node 24 / Bun).
    let disposable_stack_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    for (name, len, nf) in [
        ("use", 1.0, NativeFn::DisposableStackUse),
        ("adopt", 2.0, NativeFn::DisposableStackAdopt),
        ("defer", 1.0, NativeFn::DisposableStackDefer),
        ("move", 0.0, NativeFn::DisposableStackMove),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(disposable_stack_proto, name, Property::method(JsValue::Obj(m)));
    }
    let ds_dispose_fn = b.mk_fn(function_proto, "dispose", 0.0, NativeFn::DisposableStackDispose);
    b.put(disposable_stack_proto, "dispose", Property::method(JsValue::Obj(ds_dispose_fn)));
    // DisposableStack.prototype[@@dispose] IS %DisposableStack.prototype.dispose%.
    b.heap.obj_mut(disposable_stack_proto).props.insert(
        PropKey::Sym(dispose_sym),
        Property::method(JsValue::Obj(ds_dispose_fn)),
    );
    let ds_disposed_get = b.mk_fn(function_proto, "get disposed", 0.0, NativeFn::DisposableStackDisposedGetter);
    b.put(
        disposable_stack_proto,
        "disposed",
        Property::accessor(Some(ds_disposed_get), None, false, true),
    );
    b.put_sym(
        disposable_stack_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("DisposableStack"), false, false, true),
    );
    let disposable_stack_ctor =
        mk_ctor(&mut b, "DisposableStack", 0.0, NativeFn::DisposableStackCtor, disposable_stack_proto);

    // -- S1c: Date ----------------------------------------------------------
    // Date.prototype is an ordinary object (no [[DateValue]]).
    let date_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    {
        use DateField as DF;
        use DateSetKind as DS;
        let g = |b: &mut B<'_>, name: &str, field: DF, utc: bool| {
            let m = b.mk_fn(function_proto, name, 0.0, NativeFn::DateGetField { field, utc });
            b.put(date_proto, name, Property::method(JsValue::Obj(m)));
        };
        let s = |b: &mut B<'_>, name: &str, len: f64, field: DS, utc: bool| {
            let m = b.mk_fn(function_proto, name, len, NativeFn::DateSetField { field, utc });
            b.put(date_proto, name, Property::method(JsValue::Obj(m)));
        };
        g(&mut b, "getDate", DF::Date, false);
        g(&mut b, "getDay", DF::Day, false);
        g(&mut b, "getFullYear", DF::FullYear, false);
        g(&mut b, "getHours", DF::Hours, false);
        g(&mut b, "getMilliseconds", DF::Milliseconds, false);
        g(&mut b, "getMinutes", DF::Minutes, false);
        g(&mut b, "getMonth", DF::Month, false);
        g(&mut b, "getSeconds", DF::Seconds, false);
        for (name, len, nf) in [
            ("getTime", 0.0, NativeFn::DateGetTime),
            ("getTimezoneOffset", 0.0, NativeFn::DateGetTimezoneOffset),
        ] {
            let m = b.mk_fn(function_proto, name, len, nf);
            b.put(date_proto, name, Property::method(JsValue::Obj(m)));
        }
        g(&mut b, "getUTCDate", DF::Date, true);
        g(&mut b, "getUTCDay", DF::Day, true);
        g(&mut b, "getUTCFullYear", DF::FullYear, true);
        g(&mut b, "getUTCHours", DF::Hours, true);
        g(&mut b, "getUTCMilliseconds", DF::Milliseconds, true);
        g(&mut b, "getUTCMinutes", DF::Minutes, true);
        g(&mut b, "getUTCMonth", DF::Month, true);
        g(&mut b, "getUTCSeconds", DF::Seconds, true);
        s(&mut b, "setDate", 1.0, DS::Date, false);
        s(&mut b, "setFullYear", 3.0, DS::FullYear, false);
        s(&mut b, "setHours", 4.0, DS::Hours, false);
        s(&mut b, "setMilliseconds", 1.0, DS::Milliseconds, false);
        s(&mut b, "setMinutes", 3.0, DS::Minutes, false);
        s(&mut b, "setMonth", 2.0, DS::Month, false);
        s(&mut b, "setSeconds", 2.0, DS::Seconds, false);
        let st = b.mk_fn(function_proto, "setTime", 1.0, NativeFn::DateSetTime);
        b.put(date_proto, "setTime", Property::method(JsValue::Obj(st)));
        s(&mut b, "setUTCDate", 1.0, DS::Date, true);
        s(&mut b, "setUTCFullYear", 3.0, DS::FullYear, true);
        s(&mut b, "setUTCHours", 4.0, DS::Hours, true);
        s(&mut b, "setUTCMilliseconds", 1.0, DS::Milliseconds, true);
        s(&mut b, "setUTCMinutes", 3.0, DS::Minutes, true);
        s(&mut b, "setUTCMonth", 2.0, DS::Month, true);
        s(&mut b, "setUTCSeconds", 2.0, DS::Seconds, true);
        for (name, len, nf) in [
            ("toDateString", 0.0, NativeFn::DateToDateString),
            ("toISOString", 0.0, NativeFn::DateToIsoString),
            ("toJSON", 1.0, NativeFn::DateToJson),
            ("toString", 0.0, NativeFn::DateToString),
            ("toTimeString", 0.0, NativeFn::DateToTimeString),
            ("valueOf", 0.0, NativeFn::DateValueOf),
            ("getYear", 0.0, NativeFn::DateGetYear),
            ("setYear", 1.0, NativeFn::DateSetYear),
        ] {
            let m = b.mk_fn(function_proto, name, len, nf);
            b.put(date_proto, name, Property::method(JsValue::Obj(m)));
        }
        // toUTCString + Annex B toGMTString: the SAME function object.
        let utcs = b.mk_fn(function_proto, "toUTCString", 0.0, NativeFn::DateToUtcString);
        b.put(date_proto, "toUTCString", Property::method(JsValue::Obj(utcs)));
        b.put(date_proto, "toGMTString", Property::method(JsValue::Obj(utcs)));
        let tp = b.mk_fn(function_proto, "[Symbol.toPrimitive]", 1.0, NativeFn::DateToPrimitive);
        b.put_sym(
            date_proto,
            WkSym::ToPrimitive,
            Property::with_attrs(JsValue::Obj(tp), false, false, true),
        );
    }
    // The real %Date% constructor: `Date.prototype.constructor`. Own key
    // order (length, name, prototype, now, parse, UTC) matches engines.
    let date_real_ctor = b.mk_fn(function_proto, "Date", 7.0, NativeFn::DateRealCtor);
    b.put(date_real_ctor, "prototype", Property::frozen(JsValue::Obj(date_proto)));
    b.put(date_proto, "constructor", Property::method(JsValue::Obj(date_real_ctor)));
    let date_real_now = b.mk_fn(function_proto, "now", 0.0, NativeFn::DateRealNow);
    b.put(date_real_ctor, "now", Property::method(JsValue::Obj(date_real_now)));
    // parse and UTC are SHARED identities between the real constructor and
    // the driver wrapper (the wrapper copies the real ones).
    let date_parse_fn = b.mk_fn(function_proto, "parse", 1.0, NativeFn::DateParse);
    let date_utc_fn = b.mk_fn(function_proto, "UTC", 7.0, NativeFn::DateUtc);
    b.put(date_real_ctor, "parse", Property::method(JsValue::Obj(date_parse_fn)));
    b.put(date_real_ctor, "UTC", Property::method(JsValue::Obj(date_utc_fn)));
    // The driver's `Date` wrapper: an ordinary `function Date(...args)` whose
    // own surface is exactly [length 0, name "Date", prototype (plain fn
    // .prototype attrs), now, parse, UTC (enumerable plain-assignment data
    // props)] — calibrated against both engines.
    let date_wrapper_ctor = b.mk_fn(function_proto, "Date", 0.0, NativeFn::DateWrapperCtor);
    b.put(
        date_wrapper_ctor,
        "prototype",
        Property::with_attrs(JsValue::Obj(date_proto), true, false, false),
    );
    // `Date.now` is the driver's ordinary `function now()` — like every
    // driver-created function it carries a `.prototype` and is constructible
    // (engine-verified via the not-a-constructor corpus family).
    let date_now_fn = b.mk_driver_fn(function_proto, object_proto, "now", NativeFn::DateNow);
    b.put(date_wrapper_ctor, "now", Property::data(JsValue::Obj(date_now_fn)));
    b.put(date_wrapper_ctor, "parse", Property::data(JsValue::Obj(date_parse_fn)));
    b.put(date_wrapper_ctor, "UTC", Property::data(JsValue::Obj(date_utc_fn)));

    // -- S1c: RegExp skeleton -----------------------------------------------
    // RegExp.prototype is an ordinary object (not a RegExp instance).
    let regexp_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    {
        use RegexFlagKind as RF;
        let acc = |b: &mut B<'_>, name: &str, nf: NativeFn| {
            let g = b.mk_fn(function_proto, &format!("get {name}"), 0.0, nf);
            b.put(regexp_proto, name, Property::accessor(Some(g), None, false, true));
        };
        acc(&mut b, "hasIndices", NativeFn::RegexFlagGetter(RF::HasIndices));
        acc(&mut b, "global", NativeFn::RegexFlagGetter(RF::Global));
        acc(&mut b, "ignoreCase", NativeFn::RegexFlagGetter(RF::IgnoreCase));
        acc(&mut b, "multiline", NativeFn::RegexFlagGetter(RF::Multiline));
        acc(&mut b, "dotAll", NativeFn::RegexFlagGetter(RF::DotAll));
        acc(&mut b, "unicode", NativeFn::RegexFlagGetter(RF::Unicode));
        acc(&mut b, "unicodeSets", NativeFn::RegexFlagGetter(RF::UnicodeSets));
        acc(&mut b, "sticky", NativeFn::RegexFlagGetter(RF::Sticky));
        acc(&mut b, "source", NativeFn::RegexSourceGetter);
        acc(&mut b, "flags", NativeFn::RegexFlagsGetter);
        let ts = b.mk_fn(function_proto, "toString", 0.0, NativeFn::RegexToString);
        b.put(regexp_proto, "toString", Property::method(JsValue::Obj(ts)));
        for (name, len, tag) in [
            ("compile", 2.0, "compile"),
            ("exec", 1.0, "exec"),
            ("test", 1.0, "test"),
        ] {
            let m = b.mk_fn(function_proto, name, len, NativeFn::RegexProtoMethod(tag));
            b.put(regexp_proto, name, Property::method(JsValue::Obj(m)));
        }
        for (wk, disp, len, tag) in [
            (WkSym::Match, "[Symbol.match]", 1.0, "@@match"),
            (WkSym::MatchAll, "[Symbol.matchAll]", 1.0, "@@matchAll"),
            (WkSym::Replace, "[Symbol.replace]", 2.0, "@@replace"),
            (WkSym::Search, "[Symbol.search]", 1.0, "@@search"),
            (WkSym::Split, "[Symbol.split]", 2.0, "@@split"),
        ] {
            let m = b.mk_fn(function_proto, disp, len, NativeFn::RegexProtoMethod(tag));
            b.put_sym(regexp_proto, wk, Property::method(JsValue::Obj(m)));
        }
    }
    let regexp_ctor = mk_ctor(&mut b, "RegExp", 2.0, NativeFn::RegExpCtor, regexp_proto);
    {
        let sg = b.mk_fn(function_proto, "get [Symbol.species]", 0.0, NativeFn::SpeciesGetter);
        b.put_sym(regexp_ctor, WkSym::Species, Property::accessor(Some(sg), None, false, true));
    }

    // -- Proxy (§10.5): constructor + Proxy.revocable -----------------------
    // The Proxy constructor has NO `prototype` own property (spec 28.2.2); its
    // only own properties are length, name, and revocable — all modeled, so it
    // carries no miss-danger set.
    let proxy_ctor = b.mk_fn(function_proto, "Proxy", 2.0, NativeFn::ProxyCtor);
    {
        let m = b.mk_fn(function_proto, "revocable", 2.0, NativeFn::ProxyRevocable);
        b.put(proxy_ctor, "revocable", Property::method(JsValue::Obj(m)));
    }

    // -- S1c: JSON.parse + URI functions ------------------------------------
    let m = b.mk_fn(function_proto, "parse", 2.0, NativeFn::JsonParse);
    b.put(json, "parse", Property::method(JsValue::Obj(m)));
    // Spec §19.2 order on the global: parse comes before stringify — but the
    // JSON object's own-key ORDER is engine-incidental for reflection (it
    // refuses); insertion order here is not observable.
    let encode_uri = b.mk_fn(function_proto, "encodeURI", 1.0, NativeFn::EncodeUri { component: false });
    let encode_uric =
        b.mk_fn(function_proto, "encodeURIComponent", 1.0, NativeFn::EncodeUri { component: true });
    let decode_uri = b.mk_fn(function_proto, "decodeURI", 1.0, NativeFn::DecodeUri { component: false });
    let decode_uric =
        b.mk_fn(function_proto, "decodeURIComponent", 1.0, NativeFn::DecodeUri { component: true });

    // console: the driver REPLACES log/info/debug/trace/warn/error with
    // anonymous recorder function expressions via plain [[Set]] — enumerable
    // data props holding name-"" functions WITH a `.prototype`.
    let console = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    for name in ["log", "info", "debug", "trace"] {
        let m = b.mk_driver_fn(function_proto, object_proto, "", NativeFn::ConsoleWrite { stderr: false });
        b.put(console, name, Property::data(JsValue::Obj(m)));
    }
    for name in ["warn", "error"] {
        let m = b.mk_driver_fn(function_proto, object_proto, "", NativeFn::ConsoleWrite { stderr: true });
        b.put(console, name, Property::data(JsValue::Obj(m)));
    }

    // Misc global functions.
    let isnan_fn = b.mk_fn(function_proto, "isNaN", 1.0, NativeFn::IsNaN);
    let isfinite_fn = b.mk_fn(function_proto, "isFinite", 1.0, NativeFn::IsFinite);
    let eval_fn = b.mk_fn(function_proto, "eval", 1.0, NativeFn::EvalFn);
    // The driver's `print` hook: `function print(...args)` → length 0, and it
    // is an ordinary function expression (has `.prototype`), installed with
    // defineProperty {writable:true, configurable:true} (non-enumerable).
    let print_fn = b.mk_driver_fn(function_proto, object_proto, "print", NativeFn::Print);

    // Event-loop globals (onto the reactor's deterministic queues).
    let queue_microtask_fn = b.mk_fn(function_proto, "queueMicrotask", 1.0, NativeFn::QueueMicrotask);
    let set_timeout_fn = b.mk_fn(function_proto, "setTimeout", 2.0, NativeFn::SetTimeout);
    let set_interval_fn = b.mk_fn(function_proto, "setInterval", 2.0, NativeFn::SetInterval);
    let clear_timeout_fn = b.mk_fn(function_proto, "clearTimeout", 1.0, NativeFn::ClearTimer);
    let clear_interval_fn = b.mk_fn(function_proto, "clearInterval", 1.0, NativeFn::ClearTimer);

    // -- S1e: iterator + generator prototype graph (§27) --------------------
    // %IteratorPrototype%: proto = %Object.prototype%; own [@@iterator] → this.
    let iterator_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let iter_self = b.mk_fn(function_proto, "[Symbol.iterator]", 0.0, NativeFn::IteratorProtoIterator);
    b.put_sym(iterator_proto, WkSym::Iterator, Property::method(JsValue::Obj(iter_self)));

    // §27.1 %Iterator%: the abstract global constructor. `Iterator.prototype`
    // IS %IteratorPrototype% (this same object). The `constructor` and
    // @@toStringTag own properties are ACCESSORS (the iterator-helpers
    // web-compat design: SetterThatIgnoresPrototypeProperties on set); the
    // getters return %Iterator% / "Iterator". The @@toStringTag getter/setter
    // NAMES follow Node ("get [Symbol.toStringTag]") — Bun uses an empty
    // description, an audited Node/Bun divergence resolved to the primary
    // engine. The helper methods (map/filter/...) are MODELED below (iterhelp.rs).
    let iterator_ctor = b.mk_fn(function_proto, "Iterator", 0.0, NativeFn::IteratorCtor);
    b.put(iterator_ctor, "prototype", Property::frozen(JsValue::Obj(iterator_proto)));
    let iter_ctor_get = b.mk_fn(function_proto, "get constructor", 0.0, NativeFn::IteratorProtoCtorGet);
    let iter_ctor_set = b.mk_fn(function_proto, "set constructor", 1.0, NativeFn::IteratorProtoCtorSet);
    b.put(
        iterator_proto,
        "constructor",
        Property::accessor(Some(iter_ctor_get), Some(iter_ctor_set), false, true),
    );
    let iter_tag_get =
        b.mk_fn(function_proto, "get [Symbol.toStringTag]", 0.0, NativeFn::IteratorProtoTagGet);
    let iter_tag_set =
        b.mk_fn(function_proto, "set [Symbol.toStringTag]", 1.0, NativeFn::IteratorProtoTagSet);
    b.put_sym(
        iterator_proto,
        WkSym::ToStringTag,
        Property::accessor(Some(iter_tag_get), Some(iter_tag_set), false, true),
    );

    // §27.1.4.2 %IteratorHelperPrototype%: [[Prototype]] = %IteratorPrototype%;
    // own `next` + `return` + @@toStringTag "Iterator Helper" (a non-writable,
    // configurable data property — matching both engines).
    let iterator_helper_proto =
        b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(iterator_proto)));
    let ih_next = b.mk_fn(function_proto, "next", 0.0, NativeFn::IteratorHelperNext);
    b.put(iterator_helper_proto, "next", Property::method(JsValue::Obj(ih_next)));
    let ih_return = b.mk_fn(function_proto, "return", 0.0, NativeFn::IteratorHelperReturn);
    b.put(iterator_helper_proto, "return", Property::method(JsValue::Obj(ih_return)));
    b.put_sym(
        iterator_helper_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("Iterator Helper"), false, false, true),
    );

    // §27.1.4 Iterator Helper methods on %Iterator.prototype%. Own-key order
    // follows Node (the primary engine): `constructor`, then reduce/toArray/
    // forEach/some/every/find, then map/filter/take/drop/flatMap. Bun places
    // `reduce` after `find` — an audited Node/Bun own-order divergence resolved
    // to the primary engine.
    for (name, len, nf) in [
        ("reduce", 1.0, NativeFn::IteratorProtoReduce),
        ("toArray", 0.0, NativeFn::IteratorProtoToArray),
        ("forEach", 1.0, NativeFn::IteratorProtoForEach),
        ("some", 1.0, NativeFn::IteratorProtoSome),
        ("every", 1.0, NativeFn::IteratorProtoEvery),
        ("find", 1.0, NativeFn::IteratorProtoFind),
        ("map", 1.0, NativeFn::IteratorProtoMap),
        ("filter", 1.0, NativeFn::IteratorProtoFilter),
        ("take", 1.0, NativeFn::IteratorProtoTake),
        ("drop", 1.0, NativeFn::IteratorProtoDrop),
        ("flatMap", 1.0, NativeFn::IteratorProtoFlatMap),
    ] {
        let f = b.mk_fn(function_proto, name, len, nf);
        b.put(iterator_proto, name, Property::method(JsValue::Obj(f)));
    }

    // The four built-in iterator prototypes (§22.1.5 / §23.1.5 / §24.1.5 /
    // §24.2.5). Each: [[Prototype]] = %IteratorPrototype%; own `next` +
    // @@toStringTag; no @@iterator own (inherited from %IteratorPrototype%,
    // returning `this`). Their instances tag as "Object" (none of these
    // prototypes are in the class-tag list; the walk reaches %Object.prototype%).
    // Returns (prototype, next-fn identity). The next-fn identity is retained
    // in the intrinsics so the internal fast-iteration paths can verify a
    // prototype's `next` is still the intrinsic (a patched `next` — even with a
    // pristine @@iterator — falls to the general user protocol, which drives
    // the replacement, as the spec requires).
    let mk_iter_proto = |b: &mut B<'_>, tag: &str, nf: NativeFn| -> (ObjId, ObjId) {
        let p = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(iterator_proto)));
        let next = b.mk_fn(function_proto, "next", 0.0, nf);
        b.put(p, "next", Property::method(JsValue::Obj(next)));
        b.put_sym(
            p,
            WkSym::ToStringTag,
            Property::with_attrs(JsValue::str_from(tag), false, false, true),
        );
        (p, next)
    };
    let (array_iterator_proto, array_iterator_next_fn) =
        mk_iter_proto(&mut b, "Array Iterator", NativeFn::ArrayIteratorNext);
    let (string_iterator_proto, string_iterator_next_fn) =
        mk_iter_proto(&mut b, "String Iterator", NativeFn::StringIteratorNext);
    let (map_iterator_proto, map_iterator_next_fn) =
        mk_iter_proto(&mut b, "Map Iterator", NativeFn::MapIteratorNext);
    let (set_iterator_proto, set_iterator_next_fn) =
        mk_iter_proto(&mut b, "Set Iterator", NativeFn::SetIteratorNext);
    let (regexp_string_iterator_proto, regexp_string_iterator_next_fn) =
        mk_iter_proto(&mut b, "RegExp String Iterator", NativeFn::RegExpStringIteratorNext);

    // The three generator objects, allocated first so constructor/prototype
    // back-links can be installed in spec property order.
    let generator_proto =
        b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(iterator_proto)));
    let generator_function_proto =
        b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(function_proto)));
    let generator_function_ctor =
        b.mk_fn(function_proto, "GeneratorFunction", 1.0, NativeFn::GeneratorFunctionCtor);
    b.heap.obj_mut(generator_function_ctor).proto = Some(function_ctor);

    // %GeneratorPrototype% properties in spec order:
    // constructor, next, return, throw, @@toStringTag.
    b.put(
        generator_proto,
        "constructor",
        Property::with_attrs(JsValue::Obj(generator_function_proto), false, false, true),
    );
    for (name, nf) in [
        ("next", NativeFn::GeneratorNext),
        ("return", NativeFn::GeneratorReturn),
        ("throw", NativeFn::GeneratorThrow),
    ] {
        let m = b.mk_fn(function_proto, name, 1.0, nf);
        b.put(generator_proto, name, Property::method(JsValue::Obj(m)));
    }
    b.put_sym(
        generator_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("Generator"), false, false, true),
    );

    // %GeneratorFunction.prototype% properties: constructor, prototype,
    // @@toStringTag.
    b.put(
        generator_function_proto,
        "constructor",
        Property::with_attrs(JsValue::Obj(generator_function_ctor), false, false, true),
    );
    b.put(
        generator_function_proto,
        "prototype",
        Property::with_attrs(JsValue::Obj(generator_proto), false, false, true),
    );
    b.put_sym(
        generator_function_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("GeneratorFunction"), false, false, true),
    );

    // %GeneratorFunction%.prototype = %GeneratorFunction.prototype%
    // ({w:false, e:false, c:false} per §27.4.2.2 — non-configurable, unlike a
    // generator function's own `.prototype`).
    b.put(
        generator_function_ctor,
        "prototype",
        Property::with_attrs(JsValue::Obj(generator_function_proto), false, false, false),
    );

    // -- §27.2 Promise ------------------------------------------------------
    let promise_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    for (name, len, nf) in [
        ("then", 2.0, NativeFn::PromiseProtoThen),
        ("catch", 1.0, NativeFn::PromiseProtoCatch),
        ("finally", 1.0, NativeFn::PromiseProtoFinally),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(promise_proto, name, Property::method(JsValue::Obj(m)));
    }
    b.put_sym(
        promise_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("Promise"), false, false, true),
    );
    let promise_ctor = mk_ctor(&mut b, "Promise", 1.0, NativeFn::PromiseCtor, promise_proto);
    for (name, len, nf) in [
        ("resolve", 1.0, NativeFn::PromiseResolve),
        ("reject", 1.0, NativeFn::PromiseReject),
        ("all", 1.0, NativeFn::PromiseAll),
        ("allSettled", 1.0, NativeFn::PromiseAllSettled),
        ("race", 1.0, NativeFn::PromiseRace),
        ("any", 1.0, NativeFn::PromiseAny),
        ("try", 1.0, NativeFn::PromiseTry),
        ("withResolvers", 0.0, NativeFn::PromiseWithResolvers),
    ] {
        let m = b.mk_fn(function_proto, name, len, nf);
        b.put(promise_ctor, name, Property::method(JsValue::Obj(m)));
    }
    // Promise[@@species] — the default accessor returns `this`.
    let promise_species = b.mk_fn(function_proto, "get [Symbol.species]", 0.0, NativeFn::SpeciesGetter);
    b.put_sym(
        promise_ctor,
        WkSym::Species,
        Property::accessor(Some(promise_species), None, false, true),
    );

    // -- §27.7 AsyncFunction (intrinsic; not a global) ----------------------
    let async_function_proto =
        b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(function_proto)));
    let async_function_ctor =
        b.mk_fn(function_proto, "AsyncFunction", 1.0, NativeFn::AsyncFunctionCtor);
    b.heap.obj_mut(async_function_ctor).proto = Some(function_ctor);
    b.put(
        async_function_proto,
        "constructor",
        Property::with_attrs(JsValue::Obj(async_function_ctor), false, false, true),
    );
    b.put_sym(
        async_function_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("AsyncFunction"), false, false, true),
    );
    b.put(
        async_function_ctor,
        "prototype",
        Property::with_attrs(JsValue::Obj(async_function_proto), false, false, false),
    );

    // -- §27.1.3 %AsyncIteratorPrototype% + §27.6 AsyncGenerator ------------
    let async_iterator_proto =
        b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let async_iter_self = b.mk_fn(
        function_proto,
        "[Symbol.asyncIterator]",
        0.0,
        NativeFn::AsyncIteratorProtoSelf,
    );
    b.put_sym(
        async_iterator_proto,
        WkSym::AsyncIterator,
        Property::method(JsValue::Obj(async_iter_self)),
    );

    // The three async generator objects (mirrors the sync generator graph),
    // with %AsyncGeneratorPrototype% chaining to %AsyncIteratorPrototype%.
    let async_generator_proto =
        b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(async_iterator_proto)));
    let async_generator_function_proto =
        b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(function_proto)));
    let async_generator_function_ctor = b.mk_fn(
        function_proto,
        "AsyncGeneratorFunction",
        1.0,
        NativeFn::AsyncGeneratorFunctionCtor,
    );
    b.heap.obj_mut(async_generator_function_ctor).proto = Some(function_ctor);

    // %AsyncGeneratorPrototype%: constructor, next, return, throw, @@toStringTag.
    b.put(
        async_generator_proto,
        "constructor",
        Property::with_attrs(JsValue::Obj(async_generator_function_proto), false, false, true),
    );
    for (name, nf) in [
        ("next", NativeFn::AsyncGeneratorNext),
        ("return", NativeFn::AsyncGeneratorReturn),
        ("throw", NativeFn::AsyncGeneratorThrow),
    ] {
        let m = b.mk_fn(function_proto, name, 1.0, nf);
        b.put(async_generator_proto, name, Property::method(JsValue::Obj(m)));
    }
    b.put_sym(
        async_generator_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("AsyncGenerator"), false, false, true),
    );

    // %AsyncGeneratorFunction.prototype%: constructor, prototype, @@toStringTag.
    b.put(
        async_generator_function_proto,
        "constructor",
        Property::with_attrs(JsValue::Obj(async_generator_function_ctor), false, false, true),
    );
    b.put(
        async_generator_function_proto,
        "prototype",
        Property::with_attrs(JsValue::Obj(async_generator_proto), false, false, true),
    );
    b.put_sym(
        async_generator_function_proto,
        WkSym::ToStringTag,
        Property::with_attrs(JsValue::str_from("AsyncGeneratorFunction"), false, false, true),
    );

    // %AsyncGeneratorFunction%.prototype = %AsyncGeneratorFunction.prototype%
    // ({w:false, e:false, c:false} per §27.4.2.2).
    b.put(
        async_generator_function_ctor,
        "prototype",
        Property::with_attrs(JsValue::Obj(async_generator_function_proto), false, false, false),
    );

    // -- §25.1 ArrayBuffer --------------------------------------------------
    let array_buffer_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    {
        let acc = |b: &mut B<'_>, name: &str, nf: NativeFn| {
            let g = b.mk_fn(function_proto, &format!("get {name}"), 0.0, nf);
            b.put(array_buffer_proto, name, Property::accessor(Some(g), None, false, true));
        };
        acc(&mut b, "byteLength", NativeFn::ArrayBufferByteLengthGetter);
        acc(&mut b, "maxByteLength", NativeFn::ArrayBufferMaxByteLengthGetter);
        acc(&mut b, "resizable", NativeFn::ArrayBufferResizableGetter);
        acc(&mut b, "detached", NativeFn::ArrayBufferDetachedGetter);
        for (name, len, nf) in [
            ("slice", 2.0, NativeFn::ArrayBufferSlice),
            ("resize", 1.0, NativeFn::ArrayBufferResize),
            ("transfer", 0.0, NativeFn::ArrayBufferTransfer { to_fixed: false }),
            ("transferToFixedLength", 0.0, NativeFn::ArrayBufferTransfer { to_fixed: true }),
        ] {
            let m = b.mk_fn(function_proto, name, len, nf);
            b.put(array_buffer_proto, name, Property::method(JsValue::Obj(m)));
        }
        b.put_sym(
            array_buffer_proto,
            WkSym::ToStringTag,
            Property::with_attrs(JsValue::str_from("ArrayBuffer"), false, false, true),
        );
    }
    let array_buffer_ctor = mk_ctor(&mut b, "ArrayBuffer", 1.0, NativeFn::ArrayBufferCtor, array_buffer_proto);
    {
        let m = b.mk_fn(function_proto, "isView", 1.0, NativeFn::ArrayBufferIsView);
        b.put(array_buffer_ctor, "isView", Property::method(JsValue::Obj(m)));
        let sg = b.mk_fn(function_proto, "get [Symbol.species]", 0.0, NativeFn::SpeciesGetter);
        b.put_sym(array_buffer_ctor, WkSym::Species, Property::accessor(Some(sg), None, false, true));
    }

    // -- §25.3 DataView -----------------------------------------------------
    let data_view_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    {
        let acc = |b: &mut B<'_>, name: &str, nf: NativeFn| {
            let g = b.mk_fn(function_proto, &format!("get {name}"), 0.0, nf);
            b.put(data_view_proto, name, Property::accessor(Some(g), None, false, true));
        };
        acc(&mut b, "buffer", NativeFn::DataViewBufferGetter);
        acc(&mut b, "byteLength", NativeFn::DataViewByteLengthGetter);
        acc(&mut b, "byteOffset", NativeFn::DataViewByteOffsetGetter);
        use ElemType as E;
        for (name, et) in [
            ("getBigInt64", E::BigInt64), ("getBigUint64", E::BigUint64),
            ("getFloat16", E::Float16), ("getFloat32", E::Float32), ("getFloat64", E::Float64),
            ("getInt8", E::Int8), ("getInt16", E::Int16), ("getInt32", E::Int32),
            ("getUint8", E::Uint8), ("getUint16", E::Uint16), ("getUint32", E::Uint32),
        ] {
            let m = b.mk_fn(function_proto, name, 1.0, NativeFn::DataViewGet(et));
            b.put(data_view_proto, name, Property::method(JsValue::Obj(m)));
        }
        for (name, et) in [
            ("setBigInt64", E::BigInt64), ("setBigUint64", E::BigUint64),
            ("setFloat16", E::Float16), ("setFloat32", E::Float32), ("setFloat64", E::Float64),
            ("setInt8", E::Int8), ("setInt16", E::Int16), ("setInt32", E::Int32),
            ("setUint8", E::Uint8), ("setUint16", E::Uint16), ("setUint32", E::Uint32),
        ] {
            let m = b.mk_fn(function_proto, name, 2.0, NativeFn::DataViewSet(et));
            b.put(data_view_proto, name, Property::method(JsValue::Obj(m)));
        }
        b.put_sym(
            data_view_proto,
            WkSym::ToStringTag,
            Property::with_attrs(JsValue::str_from("DataView"), false, false, true),
        );
    }
    let data_view_ctor = mk_ctor(&mut b, "DataView", 1.0, NativeFn::DataViewCtor, data_view_proto);

    // -- §23.2 %TypedArray% + concrete constructors -------------------------
    // Grab %Array.prototype.toString% — %TypedArray%.prototype.toString IS the
    // same function object (spec 23.2.3.32).
    let array_to_string_fn = b
        .heap
        .obj(array_proto)
        .props
        .get(&PropKey::from_str("toString"))
        .and_then(Property::data_value)
        .cloned()
        .expect("Array.prototype.toString installed");
    let typed_array_proto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    let ta_values_fn = b.mk_fn(function_proto, "values", 0.0, NativeFn::TaProtoMethod("values"));
    {
        let acc = |b: &mut B<'_>, name: &str, nf: NativeFn| {
            let g = b.mk_fn(function_proto, &format!("get {name}"), 0.0, nf);
            b.put(typed_array_proto, name, Property::accessor(Some(g), None, false, true));
        };
        acc(&mut b, "buffer", NativeFn::TaBufferGetter);
        acc(&mut b, "byteLength", NativeFn::TaByteLengthGetter);
        acc(&mut b, "byteOffset", NativeFn::TaByteOffsetGetter);
        acc(&mut b, "length", NativeFn::TaLengthGetter);
        for (name, len, tag) in [
            ("at", 1.0, "at"),
            ("copyWithin", 2.0, "copyWithin"),
            ("entries", 0.0, "entries"),
            ("every", 1.0, "every"),
            ("fill", 1.0, "fill"),
            ("filter", 1.0, "filter"),
            ("find", 1.0, "find"),
            ("findIndex", 1.0, "findIndex"),
            ("findLast", 1.0, "findLast"),
            ("findLastIndex", 1.0, "findLastIndex"),
            ("forEach", 1.0, "forEach"),
            ("includes", 1.0, "includes"),
            ("indexOf", 1.0, "indexOf"),
            ("join", 1.0, "join"),
            ("keys", 0.0, "keys"),
            ("lastIndexOf", 1.0, "lastIndexOf"),
            ("map", 1.0, "map"),
            ("reduce", 1.0, "reduce"),
            ("reduceRight", 1.0, "reduceRight"),
            ("reverse", 0.0, "reverse"),
            ("set", 1.0, "set"),
            ("slice", 2.0, "slice"),
            ("some", 1.0, "some"),
            ("sort", 1.0, "sort"),
            ("subarray", 2.0, "subarray"),
            ("toLocaleString", 0.0, "toLocaleString"),
            ("toReversed", 0.0, "toReversed"),
            ("toSorted", 1.0, "toSorted"),
            ("with", 2.0, "with"),
        ] {
            let m = b.mk_fn(function_proto, name, len, NativeFn::TaProtoMethod(tag));
            b.put(typed_array_proto, name, Property::method(JsValue::Obj(m)));
        }
        b.put(typed_array_proto, "values", Property::method(JsValue::Obj(ta_values_fn)));
        b.put(typed_array_proto, "toString", Property::method(array_to_string_fn));
        b.put_sym(typed_array_proto, WkSym::Iterator, Property::method(JsValue::Obj(ta_values_fn)));
        let tag_get = b.mk_fn(function_proto, "get [Symbol.toStringTag]", 0.0, NativeFn::TaToStringTagGetter);
        b.put_sym(
            typed_array_proto,
            WkSym::ToStringTag,
            Property::accessor(Some(tag_get), None, false, true),
        );
    }
    // %TypedArray% base constructor: [[Prototype]] = Function.prototype.
    let typed_array_ctor = b.mk_fn(function_proto, "TypedArray", 0.0, NativeFn::TypedArrayBaseCtor);
    b.put(typed_array_ctor, "prototype", Property::frozen(JsValue::Obj(typed_array_proto)));
    b.put(typed_array_proto, "constructor", Property::method(JsValue::Obj(typed_array_ctor)));
    {
        for (name, len, nf) in [
            ("from", 1.0, NativeFn::TypedArrayFrom),
            ("of", 0.0, NativeFn::TypedArrayOf),
        ] {
            let m = b.mk_fn(function_proto, name, len, nf);
            b.put(typed_array_ctor, name, Property::method(JsValue::Obj(m)));
        }
        let sg = b.mk_fn(function_proto, "get [Symbol.species]", 0.0, NativeFn::SpeciesGetter);
        b.put_sym(typed_array_ctor, WkSym::Species, Property::accessor(Some(sg), None, false, true));
    }
    // Concrete constructors: [[Prototype]] = %TypedArray%; .prototype's
    // [[Prototype]] = %TypedArray%.prototype.
    let mut ta_protos = [ObjId(0); 12];
    let mut ta_ctors = [ObjId(0); 12];
    for et in ElemType::ALL {
        let cproto = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(typed_array_proto)));
        #[allow(clippy::cast_precision_loss)]
        let bpe = et.bytes_per_element() as f64;
        b.put(cproto, "BYTES_PER_ELEMENT", Property::frozen(JsValue::Num(bpe)));
        let cctor = b.mk_fn(function_proto, et.ctor_name(), 3.0, NativeFn::TypedArrayCtor(et));
        b.heap.obj_mut(cctor).proto = Some(typed_array_ctor);
        b.put(cctor, "BYTES_PER_ELEMENT", Property::frozen(JsValue::Num(bpe)));
        b.put(cctor, "prototype", Property::frozen(JsValue::Obj(cproto)));
        b.put(cproto, "constructor", Property::method(JsValue::Obj(cctor)));
        ta_protos[et.idx()] = cproto;
        ta_ctors[et.idx()] = cctor;
    }

    // The global object.
    let global = b.heap.alloc(JsObject::new(ObjKind::IntrinsicHost, Some(object_proto)));
    b.put(global, "undefined", Property::frozen(JsValue::Undefined));
    b.put(global, "NaN", Property::frozen(JsValue::Num(f64::NAN)));
    b.put(global, "Infinity", Property::frozen(JsValue::Num(f64::INFINITY)));
    b.put(global, "globalThis", Property::method(JsValue::Obj(global)));
    for (name, id) in [
        ("Object", object_ctor),
        ("Function", function_ctor),
        ("Array", array_ctor),
        ("String", string_ctor),
        ("Number", number_ctor),
        ("Boolean", boolean_ctor),
        ("Symbol", symbol_ctor),
        ("BigInt", bigint_ctor),
        ("Error", error_ctor),
        ("TypeError", type_error_ctor),
        ("RangeError", range_error_ctor),
        ("ReferenceError", reference_error_ctor),
        ("SyntaxError", syntax_error_ctor),
        ("EvalError", eval_error_ctor),
        ("URIError", uri_error_ctor),
        ("AggregateError", aggregate_error_ctor),
        ("Math", math),
        ("JSON", json),
        ("Reflect", reflect),
        ("console", console),
        ("isNaN", isnan_fn),
        ("isFinite", isfinite_fn),
        ("parseInt", parse_int_fn),
        ("parseFloat", parse_float_fn),
        ("eval", eval_fn),
        ("print", print_fn),
        ("Map", map_ctor),
        ("Set", set_ctor),
        ("WeakMap", weakmap_ctor),
        ("WeakSet", weakset_ctor),
        ("WeakRef", weakref_ctor),
        ("FinalizationRegistry", finreg_ctor),
        ("SuppressedError", suppressed_error_ctor),
        ("DisposableStack", disposable_stack_ctor),
        ("Iterator", iterator_ctor),
        ("RegExp", regexp_ctor),
        ("Proxy", proxy_ctor),
        ("Promise", promise_ctor),
        ("queueMicrotask", queue_microtask_fn),
        ("setTimeout", set_timeout_fn),
        ("setInterval", set_interval_fn),
        ("clearTimeout", clear_timeout_fn),
        ("clearInterval", clear_interval_fn),
        ("encodeURI", encode_uri),
        ("encodeURIComponent", encode_uric),
        ("decodeURI", decode_uri),
        ("decodeURIComponent", decode_uric),
    ] {
        b.put(global, name, Property::method(JsValue::Obj(id)));
    }
    // The driver installs its Date wrapper with defineProperty
    // {value, writable: true, configurable: true} — non-enumerable, like the
    // builtin it replaces.
    b.put(
        global,
        "Date",
        Property::with_attrs(JsValue::Obj(date_wrapper_ctor), true, false, true),
    );
    // Binary-data globals: ArrayBuffer, DataView, and each concrete typed
    // array constructor (%TypedArray% itself is intentionally not a global).
    b.put(global, "ArrayBuffer", Property::method(JsValue::Obj(array_buffer_ctor)));
    b.put(global, "DataView", Property::method(JsValue::Obj(data_view_ctor)));
    for et in ElemType::ALL {
        b.put(global, et.ctor_name(), Property::method(JsValue::Obj(ta_ctors[et.idx()])));
    }

    // Danger tables.
    let mut danger: HashMap<ObjId, Danger> = HashMap::new();
    let listed = |names, syms| Danger::Listed { names, syms };
    danger.insert(object_proto, listed(OBJECT_PROTO_DANGER, &[]));
    danger.insert(function_proto, listed(FUNCTION_PROTO_DANGER, &[]));
    danger.insert(array_proto, listed(ARRAY_PROTO_DANGER, &[WkSym::Unscopables]));
    danger.insert(string_proto, listed(STRING_PROTO_DANGER, &[]));
    danger.insert(number_proto, listed(NUMBER_PROTO_DANGER, &[]));
    danger.insert(boolean_proto, listed(&[], &[]));
    danger.insert(symbol_proto, listed(&[], &[]));
    danger.insert(bigint_proto, listed(&[], &[]));
    danger.insert(bigint_ctor, listed(&[], &[]));
    danger.insert(object_ctor, listed(OBJECT_CTOR_DANGER, &[]));
    danger.insert(array_ctor, listed(ARRAY_CTOR_DANGER, &[]));
    danger.insert(string_ctor, listed(&[], &[]));
    danger.insert(number_ctor, listed(&[], &[]));
    danger.insert(symbol_ctor, listed(SYMBOL_CTOR_DANGER, &[]));
    danger.insert(error_ctor, listed(ERROR_CTOR_DANGER, &[]));
    danger.insert(json, listed(JSON_DANGER, &[]));
    danger.insert(math, listed(MATH_DANGER, &[]));
    danger.insert(console, Danger::All);
    // S1c intrinsics: empty lists mark own-key-order-opaque surfaces whose
    // misses are safe; listed names are engine-real-but-unmodeled.
    danger.insert(map_proto, listed(&[], &[]));
    danger.insert(set_proto, listed(SET_PROTO_DANGER, &[]));
    danger.insert(weakmap_proto, listed(&[], &[]));
    danger.insert(weakset_proto, listed(&[], &[]));
    // WeakRef / FinalizationRegistry: the full own surface (deref / register /
    // unregister / constructor / @@toStringTag) is modeled, so misses are safe;
    // the empty lists still mark own-key ORDER opaque (full reflection refuses).
    danger.insert(weakref_proto, listed(&[], &[]));
    danger.insert(weakref_ctor, listed(&[], &[]));
    danger.insert(finreg_proto, listed(&[], &[]));
    danger.insert(finreg_ctor, listed(&[], &[]));
    // %Iterator%: own {length, name, prototype} modeled. The static
    // iterator-sequencing helpers (`from` — real on Node/Bun — plus the newer
    // `concat`/`zip`/`zipKeyed`) are proposal surface this slice does not model:
    // a miss MUST refuse, else it would answer `undefined` and a subsequent
    // `Iterator.from(...)` call would wrongly throw where the engines succeed.
    danger.insert(iterator_ctor, listed(ITERATOR_CTOR_DANGER, &[]));
    danger.insert(map_ctor, listed(MAP_CTOR_DANGER, &[]));
    danger.insert(set_ctor, listed(&[], &[]));
    danger.insert(date_proto, listed(DATE_PROTO_DANGER, &[]));
    danger.insert(regexp_proto, listed(&[], &[]));
    danger.insert(regexp_ctor, listed(REGEXP_CTOR_DANGER, &[]));
    // Promise: the whole modeled surface is present; empty lists mark these
    // own-key-ORDER-opaque (full own-key reflection refuses; misses are safe).
    // %AsyncFunction.prototype% carries only constructor + @@toStringTag.
    danger.insert(promise_proto, listed(&[], &[]));
    danger.insert(promise_ctor, listed(&[], &[]));
    danger.insert(async_function_proto, listed(&[], &[]));
    // Proxy's own surface (length, name, revocable) is fully modeled — no
    // miss-danger set. (Its own-key ORDER is not reflection-opaque either: the
    // constructor is an ordinary function object.)
    // %IteratorPrototype% now models @@iterator, constructor, @@toStringTag, and
    // all eleven Iterator Helper methods (§27.1.4) as HITS; `return`/`throw`/other
    // genuine misses resolve to undefined — so IteratorClose over a built-in
    // iterator object (which does GetMethod(iter,"return")) is a correct no-op.
    // The only unmodeled engine own-key is @@dispose, unreachable here (its key
    // Symbol.dispose refuses at the Symbol constructor), so the list is empty.
    danger.insert(iterator_proto, listed(ITERATOR_PROTO_DANGER, &[]));
    // %IteratorHelperPrototype% models exactly next/return/@@toStringTag; empty
    // list marks it own-key-ORDER-opaque while individual misses stay safe.
    danger.insert(iterator_helper_proto, listed(&[], &[]));
    // The built-in iterator prototypes carry exactly `next` + @@toStringTag in
    // this model; empty lists mark them own-key-ORDER-opaque (full own-key
    // reflection refuses) while individual misses stay safe. A miss that walks
    // up to %IteratorPrototype% (Danger::All) refuses — the Iterator Helper
    // methods (map/filter/take/…) are unmodeled, so a touch is a sound refusal.
    danger.insert(array_iterator_proto, listed(&[], &[]));
    danger.insert(string_iterator_proto, listed(&[], &[]));
    danger.insert(map_iterator_proto, listed(&[], &[]));
    danger.insert(set_iterator_proto, listed(&[], &[]));
    danger.insert(regexp_string_iterator_proto, listed(&[], &[]));
    // Binary-data intrinsics: every own property Node/JSC carry is modeled, so
    // misses are safe; the empty lists still mark these order-opaque (full
    // own-key reflection refuses). ArrayBuffer.prototype.transferToImmutable is
    // absent at this pin (not danger-listed → reads undefined, matching Node).
    danger.insert(array_buffer_proto, listed(&[], &[]));
    danger.insert(array_buffer_ctor, listed(&[], &[]));
    danger.insert(data_view_proto, listed(&[], &[]));
    danger.insert(data_view_ctor, listed(&[], &[]));
    danger.insert(typed_array_proto, listed(&[], &[]));
    danger.insert(typed_array_ctor, listed(&[], &[]));
    for et in ElemType::ALL {
        danger.insert(ta_protos[et.idx()], listed(&[], &[]));
        danger.insert(ta_ctors[et.idx()], listed(&[], &[]));
    }

    let intr = Intrinsics {
        object_proto,
        function_proto,
        array_proto,
        string_proto,
        number_proto,
        boolean_proto,
        symbol_proto,
        bigint_proto,
        error_proto,
        type_error_proto,
        range_error_proto,
        reference_error_proto,
        syntax_error_proto,
        eval_error_proto,
        uri_error_proto,
        aggregate_error_proto,
        object_ctor,
        function_ctor,
        array_ctor,
        string_ctor,
        number_ctor,
        boolean_ctor,
        symbol_ctor,
        bigint_ctor,
        error_ctor,
        aggregate_error_ctor,
        math,
        json,
        reflect,
        console,
        throw_type_error,
        array_values_fn,
        fn_has_instance,
        map_proto,
        set_proto,
        weakmap_proto,
        weakset_proto,
        date_proto,
        regexp_proto,
        map_ctor,
        set_ctor,
        weakmap_ctor,
        weakset_ctor,
        weakref_proto,
        weakref_ctor,
        finreg_proto,
        finreg_ctor,
        iterator_ctor,
        date_wrapper_ctor,
        date_real_ctor,
        regexp_ctor,
        proxy_ctor,
        iterator_proto,
        array_iterator_proto,
        string_iterator_proto,
        map_iterator_proto,
        set_iterator_proto,
        regexp_string_iterator_proto,
        iterator_helper_proto,
        string_iterator_fn,
        array_iterator_next_fn,
        string_iterator_next_fn,
        map_iterator_next_fn,
        set_iterator_next_fn,
        regexp_string_iterator_next_fn,
        generator_function_proto,
        generator_proto,
        generator_function_ctor,
        map_entries_fn,
        set_values_fn,
        promise_proto,
        promise_ctor,
        async_function_proto,
        async_function_ctor,
        async_iterator_proto,
        async_generator_proto,
        async_generator_function_proto,
        async_generator_function_ctor,
        array_buffer_proto,
        array_buffer_ctor,
        data_view_proto,
        data_view_ctor,
        typed_array_proto,
        typed_array_ctor,
        ta_protos,
        ta_ctors,
        ta_values_fn,
        suppressed_error_proto,
        disposable_stack_proto,
        disposable_stack_ctor,
        dispose_sym,
        async_dispose_sym,
        danger,
    };

    // The root environment frame: `this` = the global object (indirect-eval
    // script context).
    let mut root = EnvFrame::new(None);
    root.this_val = Some(JsValue::Obj(global));
    b.heap.alloc_env(root);

    Realm { intr, global }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn realm_builds_and_danger_tables_classify() {
        let mut heap = Heap::new();
        let realm = create_realm(&mut heap);
        let intr = &realm.intr;
        // Modeled props are present and never on the miss path.
        assert!(heap
            .obj(intr.object_proto)
            .props
            .contains_key(&PropKey::from_str("hasOwnProperty")));
        assert!(heap
            .obj(intr.array_proto)
            .props
            .contains_key(&PropKey::from_str("reduce")));
        assert!(heap
            .obj(intr.function_proto)
            .props
            .contains_key(&PropKey::Sym(SymId::WellKnown(WkSym::HasInstance))));
        // Danger classification: unmodeled engine-real names refuse.
        assert!(intr
            .miss_danger(intr.array_proto, &PropKey::from_str("toLocaleString"))
            .is_some());
        assert!(intr
            .miss_danger(intr.function_proto, &PropKey::from_str("toString"))
            .is_some());
        assert!(intr
            .miss_danger(intr.object_proto, &PropKey::from_str("__proto__"))
            .is_some());
        // Non-real names fall through soundly.
        assert!(intr
            .miss_danger(intr.array_proto, &PropKey::from_str("noSuchThing"))
            .is_none());
        // Symbol dangers: @@iterator is now a MODELED own prop on
        // Array.prototype (identity === values), so its lookup is a HIT, not a
        // danger miss; @@unscopables remains an unmodeled danger-listed symbol.
        assert!(matches!(
            heap.obj(intr.array_proto)
                .props
                .get(&PropKey::Sym(SymId::WellKnown(WkSym::Iterator)))
                .and_then(Property::data_value),
            Some(JsValue::Obj(o)) if *o == intr.array_values_fn
        ));
        assert!(intr
            .miss_danger(
                intr.array_proto,
                &PropKey::Sym(SymId::WellKnown(WkSym::Unscopables))
            )
            .is_some());
        assert!(intr
            .miss_danger(
                intr.object_proto,
                &PropKey::Sym(SymId::WellKnown(WkSym::ToPrimitive))
            )
            .is_none());
        // User symbols never trip danger lists.
        assert!(intr
            .miss_danger(intr.array_proto, &PropKey::Sym(SymId::User(0)))
            .is_none());
        // console is fully opaque.
        assert!(intr
            .miss_danger(intr.console, &PropKey::from_str("anything"))
            .is_some());
        // S1c danger coherence: engine-real unmodeled surfaces refuse.
        assert!(intr
            .miss_danger(intr.set_proto, &PropKey::from_str("union"))
            .is_some());
        assert!(intr
            .miss_danger(intr.set_proto, &PropKey::from_str("isSubsetOf"))
            .is_some());
        assert!(intr
            .miss_danger(intr.date_proto, &PropKey::from_str("toLocaleString"))
            .is_some());
        assert!(intr
            .miss_danger(intr.regexp_ctor, &PropKey::from_str("$1"))
            .is_some());
        assert!(intr
            .miss_danger(intr.regexp_ctor, &PropKey::from_str("escape"))
            .is_some());
        assert!(intr
            .miss_danger(intr.map_ctor, &PropKey::from_str("groupBy"))
            .is_some());
        // Proxy's own surface (length/name/revocable) is fully modeled: no
        // danger set, and `revocable` reads as a real method.
        assert!(intr
            .miss_danger(intr.proxy_ctor, &PropKey::from_str("revocable"))
            .is_none());
        assert!(heap
            .obj(intr.proxy_ctor)
            .props
            .contains_key(&PropKey::from_str("revocable")));
        // Modeled S1c surfaces are present (never on the miss path).
        for (oid, name) in [
            (intr.map_proto, "getOrInsertComputed"),
            (intr.map_proto, "entries"),
            (intr.set_proto, "keys"),
            (intr.weakmap_proto, "getOrInsert"),
            (intr.date_proto, "toISOString"),
            (intr.date_proto, "toGMTString"),
            (intr.regexp_proto, "exec"),
            (intr.json, "parse"),
        ] {
            assert!(
                heap.obj(oid).props.contains_key(&PropKey::from_str(name)),
                "missing modeled prop {name}"
            );
        }
        // Shared identities: @@iterator === entries (Map) / values (Set);
        // toGMTString === toUTCString; wrapper parse === real ctor parse.
        let get = |oid: ObjId, k: PropKey| {
            heap.obj(oid).props.get(&k).and_then(Property::data_value).cloned()
        };
        assert!(matches!(
            get(intr.map_proto, PropKey::Sym(SymId::WellKnown(WkSym::Iterator))),
            Some(JsValue::Obj(o)) if o == intr.map_entries_fn
        ));
        assert!(matches!(
            get(intr.set_proto, PropKey::from_str("keys")),
            Some(JsValue::Obj(o)) if o == intr.set_values_fn
        ));
        let gmt = get(intr.date_proto, PropKey::from_str("toGMTString"));
        let utc = get(intr.date_proto, PropKey::from_str("toUTCString"));
        assert!(matches!((gmt, utc), (Some(JsValue::Obj(a)), Some(JsValue::Obj(b))) if a == b));
        let wp = get(intr.date_wrapper_ctor, PropKey::from_str("parse"));
        let rp = get(intr.date_real_ctor, PropKey::from_str("parse"));
        assert!(matches!((wp, rp), (Some(JsValue::Obj(a)), Some(JsValue::Obj(b))) if a == b));
        // Proxy has no `prototype` own property (28.2.2).
        assert!(!heap
            .obj(intr.proxy_ctor)
            .props
            .contains_key(&PropKey::from_str("prototype")));
        // NativeError constructors inherit from %Error% (spec 20.5.6.2).
        let te = heap
            .obj(intr.error_proto_for(ErrKind::Type))
            .props
            .get(&PropKey::from_str("constructor"))
            .and_then(Property::data_value)
            .cloned();
        let Some(JsValue::Obj(te_ctor)) = te else {
            panic!("TypeError constructor missing");
        };
        assert_eq!(heap.obj(te_ctor).proto, Some(intr.error_ctor));
        // Root env exists with global this.
        assert!(heap.env(crate::value::EnvId(0)).this_val.is_some());
    }

    #[test]
    fn binary_data_intrinsics_wired() {
        let mut heap = Heap::new();
        let realm = create_realm(&mut heap);
        let intr = &realm.intr;
        // Concrete constructors are global; %TypedArray% is not.
        for name in ["ArrayBuffer", "DataView", "Int8Array", "Float16Array", "BigInt64Array"] {
            assert!(
                heap.obj(realm.global).props.contains_key(&PropKey::from_str(name)),
                "missing global {name}"
            );
        }
        assert!(!heap.obj(realm.global).props.contains_key(&PropKey::from_str("TypedArray")));
        // Concrete ctor [[Prototype]] is %TypedArray%; its .prototype's
        // [[Prototype]] is %TypedArray%.prototype.
        let i8 = intr.ta_ctors[ElemType::Int8.idx()];
        assert_eq!(heap.obj(i8).proto, Some(intr.typed_array_ctor));
        let i8p = intr.ta_protos[ElemType::Int8.idx()];
        assert_eq!(heap.obj(i8p).proto, Some(intr.typed_array_proto));
        assert_eq!(intr.ta_elem_by_proto(i8p), Some(ElemType::Int8));
        assert_eq!(intr.ta_elem_by_ctor(i8), Some(ElemType::Int8));
        // BYTES_PER_ELEMENT on ctor and prototype.
        let bpe = heap
            .obj(i8)
            .props
            .get(&PropKey::from_str("BYTES_PER_ELEMENT"))
            .and_then(Property::data_value)
            .cloned();
        assert!(matches!(bpe, Some(JsValue::Num(n)) if n == 1.0));
        // Modeled surfaces present (never on the miss path).
        for (oid, key) in [
            (intr.array_buffer_proto, "resize"),
            (intr.array_buffer_proto, "transfer"),
            (intr.array_buffer_ctor, "isView"),
            (intr.data_view_proto, "getFloat16"),
            (intr.data_view_proto, "setBigInt64"),
            (intr.typed_array_proto, "subarray"),
            (intr.typed_array_ctor, "from"),
        ] {
            assert!(
                heap.obj(oid).props.contains_key(&PropKey::from_str(key)),
                "missing modeled prop {key}"
            );
        }
        // %TypedArray%.prototype @@iterator === values (identity).
        let it = heap
            .obj(intr.typed_array_proto)
            .props
            .get(&PropKey::Sym(SymId::WellKnown(WkSym::Iterator)))
            .and_then(Property::data_value)
            .cloned();
        assert!(matches!(it, Some(JsValue::Obj(o)) if o == intr.ta_values_fn));
        // Order-opaque danger marks (reflection refuses, misses safe).
        assert!(intr.danger.contains_key(&intr.array_buffer_proto));
        assert!(intr.danger.contains_key(&i8));
        // transferToImmutable is absent at this pin and NOT danger-listed
        // (reads undefined, matching Node 24.5).
        assert!(intr
            .miss_danger(intr.array_buffer_proto, &PropKey::from_str("transferToImmutable"))
            .is_none());
    }
}
