// The value model of the independent semantics: JS values, heap objects,
// property records (data AND accessor, with full attribute triples), and
// UTF-16 code-unit strings. Strings are Vec<u16> because the observable
// projection is defined over code units (lone surrogates are first-class
// observables).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use indexmap::IndexMap;
use num_bigint::BigInt;
use std::cell::RefCell;
use std::rc::Rc;

/// A JS string as UTF-16 code units.
pub type Units = Vec<u16>;

#[must_use]
pub fn units_from_str(s: &str) -> Units {
    s.encode_utf16().collect()
}

#[must_use]
pub fn units_to_lossy(u: &[u16]) -> String {
    String::from_utf16_lossy(u)
}

/// True iff the units spell exactly the given ASCII string.
#[must_use]
pub fn units_eq_ascii(u: &[u16], s: &str) -> bool {
    u.len() == s.len() && u.iter().zip(s.bytes()).all(|(&a, b)| a == u16::from(b))
}

/// Canonical array index ("0", "1", ..., up to 2^32-2): digits only, no
/// leading zero except "0" itself.
#[must_use]
pub fn array_index_of(u: &[u16]) -> Option<u32> {
    if u.is_empty() || u.len() > 10 {
        return None;
    }
    if u.len() > 1 && u[0] == u16::from(b'0') {
        return None;
    }
    let mut n: u64 = 0;
    for &c in u {
        if !(0x30..=0x39).contains(&c) {
            return None;
        }
        n = n * 10 + u64::from(c - 0x30);
    }
    if n <= u64::from(u32::MAX - 1) {
        Some(u32::try_from(n).expect("bounded above"))
    } else {
        None
    }
}

/// Heap handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjId(pub u32);

/// Generator-instance handle (index into `Interp.generators`). The resumable
/// execution state lives in a side arena, not in the heap object, so the VM
/// can mutate the heap freely while a generator is running.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenId(pub u32);

/// A Symbol value (6.1.5): a unique, non-forgeable primitive. The handle
/// indexes `Interp.symbols`; two symbols are `===` iff their ids are equal
/// (fresh allocation per `Symbol(...)` call, registry-deduplicated for
/// `Symbol.for`). Well-known symbols are the first ids allocated in the realm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymId(pub u32);

/// A Promise-instance handle (index into `Interp.promises`). The mutable
/// promise state ([[PromiseState]]/[[PromiseResult]]/reaction lists) lives in
/// a side arena, not in the heap object, so resolve/reject/reactions can
/// mutate it while other user code runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PromiseId(pub u32);

/// Environment-frame handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnvId(pub u32);

/// A resolved private name (6.2.13 PrivateName): a unique value allocated
/// fresh for every declared `#name` at each ClassDefinitionEvaluation, so
/// distinct class evaluations produce distinct brands (a `mk()` factory
/// returning classes yields instances that are not cross-branded).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrivName(pub u32);

/// One [[PrivateElement]] on an object or class constructor (6.2.14).
#[derive(Debug, Clone)]
pub struct PrivateElement {
    pub key: PrivName,
    pub kind: PrivElemKind,
}

/// The kind-specific half of a private element.
#[derive(Debug, Clone)]
pub enum PrivElemKind {
    /// A private field (`#x = init`): a mutable data slot.
    Field(Value),
    /// A private method (`#m(){}`): a shared function object, non-writable.
    Method(ObjId),
    /// A private accessor (`get #x`/`set #x`): a getter/setter pair.
    Accessor { get: Option<ObjId>, set: Option<ObjId> },
}

#[derive(Debug, Clone)]
pub enum Value {
    Undefined,
    Null,
    Bool(bool),
    Num(f64),
    /// A BigInt primitive (6.1.6.2): an arbitrary-precision integer. Shared via
    /// `Rc` so cloning a `Value` never copies the digits.
    BigInt(Rc<BigInt>),
    Str(Rc<Units>),
    /// A Symbol primitive (6.1.5); the payload indexes `Interp.symbols`.
    Sym(SymId),
    Obj(ObjId),
}

/// A property key after ToPropertyKey (6.1.7.1): a string key or a symbol key.
/// The string case carries UTF-16 code units; the symbol case a `SymId`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropertyKey {
    Str(Units),
    Sym(SymId),
}

/// Per-realm data behind a Symbol value.
#[derive(Debug, Clone)]
pub struct SymData {
    /// [[Description]] (None for `Symbol()` with no argument).
    pub desc: Option<Units>,
    /// The projection name of a well-known symbol ("Symbol.iterator", ...),
    /// or None for an ordinary/registered symbol. Mirrors the driver's
    /// `WELL_KNOWN_SYMBOLS` map.
    pub well_known: Option<&'static str>,
    /// The GlobalSymbolRegistry key, if this symbol came from `Symbol.for`
    /// (so `Symbol.keyFor` can recover it); None otherwise.
    pub registry_key: Option<Units>,
}

impl Value {
    #[must_use]
    pub fn str_from(s: &str) -> Value {
        Value::Str(Rc::new(units_from_str(s)))
    }

    #[must_use]
    pub fn bigint(n: BigInt) -> Value {
        Value::BigInt(Rc::new(n))
    }

    #[must_use]
    pub fn is_object(&self) -> bool {
        matches!(self, Value::Obj(_))
    }
}

/// The kind-specific half of a property: a data slot or an accessor pair.
#[derive(Debug, Clone)]
pub enum PropVal {
    Data { value: Value, writable: bool },
    /// `get`/`set` hold the function object, or None for the absent/undefined
    /// side.
    Accessor { get: Option<ObjId>, set: Option<ObjId> },
}

/// One own property. `synthetic` marks a data value whose TEXT is
/// engine-specific (a runtime-error message our semantics cannot reproduce
/// byte-for-byte); reading or projecting it refuses the case.
#[derive(Debug, Clone)]
pub struct Prop {
    pub val: PropVal,
    pub enumerable: bool,
    pub configurable: bool,
    pub synthetic: bool,
}

impl Prop {
    #[must_use]
    pub fn data(value: Value) -> Prop {
        Prop {
            val: PropVal::Data {
                value,
                writable: true,
            },
            enumerable: true,
            configurable: true,
            synthetic: false,
        }
    }

    #[must_use]
    pub fn with_attrs(value: Value, writable: bool, enumerable: bool, configurable: bool) -> Prop {
        Prop {
            val: PropVal::Data { value, writable },
            enumerable,
            configurable,
            synthetic: false,
        }
    }

    #[must_use]
    pub fn accessor(
        get: Option<ObjId>,
        set: Option<ObjId>,
        enumerable: bool,
        configurable: bool,
    ) -> Prop {
        Prop {
            val: PropVal::Accessor { get, set },
            enumerable,
            configurable,
            synthetic: false,
        }
    }

    #[must_use]
    pub fn is_data(&self) -> bool {
        matches!(self.val, PropVal::Data { .. })
    }

    /// The data value, if this is a data property.
    #[must_use]
    pub fn data_value(&self) -> Option<&Value> {
        match &self.val {
            PropVal::Data { value, .. } => Some(value),
            PropVal::Accessor { .. } => None,
        }
    }

    /// Data writability; accessor properties report false.
    #[must_use]
    pub fn writable(&self) -> bool {
        match &self.val {
            PropVal::Data { writable, .. } => *writable,
            PropVal::Accessor { .. } => false,
        }
    }
}

/// A partial property descriptor (spec 6.2.6): each field present or absent.
/// For `get`/`set`, present-but-undefined is `Some(None)`.
#[derive(Debug, Clone, Default)]
pub struct PropDesc {
    pub value: Option<Value>,
    pub writable: Option<bool>,
    pub get: Option<Option<ObjId>>,
    pub set: Option<Option<ObjId>>,
    pub enumerable: Option<bool>,
    pub configurable: Option<bool>,
}

impl PropDesc {
    #[must_use]
    pub fn is_accessor(&self) -> bool {
        self.get.is_some() || self.set.is_some()
    }

    #[must_use]
    pub fn is_data(&self) -> bool {
        self.value.is_some() || self.writable.is_some()
    }

    #[must_use]
    pub fn is_generic(&self) -> bool {
        !self.is_accessor() && !self.is_data()
    }

    #[must_use]
    pub fn data(value: Value) -> PropDesc {
        PropDesc {
            value: Some(value),
            ..PropDesc::default()
        }
    }
}

/// Builtin function identities (dispatch happens in the interpreter).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Builtin {
    StringFn,
    NumberFn,
    BooleanFn,
    IsNaN,
    IsFinite,
    Print,
    ConsoleStdout,
    ConsoleStderr,
    ObjectCtor,
    ArrayCtor,
    ArrayIsArray,
    /// Array.from (23.1.2.1): iterable or array-like → a new Array, with an
    /// optional mapFn/thisArg.
    ArrayFrom,
    /// Array.of (23.1.2.3): the argument list → a new Array.
    ArrayOf,
    FunctionCtor,
    /// The %eval% intrinsic (19.2.1): when the call site is a direct-eval
    /// pattern the interpreter routes to PerformEval BEFORE dispatch; reaching
    /// this builtin means an INDIRECT eval (global-scope evaluation).
    Eval,
    FunctionProtoSelf,
    FunctionProtoCall,
    FunctionProtoApply,
    FunctionProtoBind,
    /// %ThrowTypeError%: the unmapped-arguments `callee` poison accessor.
    ThrowTypeError,
    ObjectProtoToString,
    ObjectProtoToLocaleString,
    ObjectProtoValueOf,
    ObjectProtoHasOwnProperty,
    ObjectProtoIsPrototypeOf,
    ObjectProtoPropertyIsEnumerable,
    ObjectCreate,
    ObjectGetPrototypeOf,
    ObjectDefineProperty,
    ObjectDefineProperties,
    ObjectGetOwnPropertyDescriptor,
    ObjectGetOwnPropertyDescriptors,
    ObjectGetOwnPropertyNames,
    ObjectKeys,
    ObjectFreeze,
    ObjectSeal,
    ObjectPreventExtensions,
    ObjectIsFrozen,
    ObjectIsSealed,
    ObjectIsExtensible,
    ArrayProtoJoin,
    ArrayProtoConcat,
    ArrayProtoToString,
    ArrayProtoMap,
    ArrayProtoForEach,
    ArrayProtoPush,
    ArrayProtoPop,
    ArrayProtoShift,
    ArrayProtoUnshift,
    ArrayProtoIndexOf,
    ArrayProtoLastIndexOf,
    ArrayProtoIncludes,
    ArrayProtoSlice,
    ArrayProtoFilter,
    ArrayProtoEvery,
    ArrayProtoSome,
    ArrayProtoFind,
    ArrayProtoFindIndex,
    ArrayProtoReduce,
    ArrayProtoReduceRight,
    /// Array.prototype.values / keys / entries (23.1.3): create an Array
    /// Iterator object over ToObject(this).
    ArrayProtoValues,
    ArrayProtoKeys,
    ArrayProtoEntries,
    /// %ArrayIteratorPrototype%.next (23.1.5.1).
    ArrayIteratorNext,
    /// %IteratorPrototype%[@@iterator] (27.1.2.1): returns the `this` value.
    /// Shared by every built-in iterator (Array/String/Map/Set/RegExpString/
    /// generator), letting the general GetIterator protocol self-return.
    IteratorProtoIterator,
    /// String.prototype[@@iterator] (22.1.3.35): create a String Iterator over
    /// ToString(this).
    StringProtoIterator,
    /// %StringIteratorPrototype%.next (22.1.5.1.1).
    StringIteratorNext,
    MathFn(MathOp),
    StrProto(StrOp),
    StringFromCharCode,
    StringFromCodePoint,
    NumberProtoToString,
    NumberProtoValueOf,
    BooleanProtoToString,
    BooleanProtoValueOf,
    /// Number.isNaN / isFinite / isInteger / isSafeInteger (no coercion).
    NumberPredicate(NumPred),
    /// Error / TypeError / ... constructor; the payload picks the prototype.
    ErrorCtor(NativeErrorKind),
    ErrorProtoToString,
    JsonStringify,
    /// %GeneratorPrototype%.next/return/throw (27.5.1.2-4).
    GeneratorNext,
    GeneratorReturn,
    GeneratorThrow,
    /// %GeneratorFunction% (27.3): callable identity only — actually invoking
    /// it (dynamic generator construction from source) is out of slice.
    GeneratorFunctionCtor,
    /// The %Symbol% function (20.4.1): `Symbol(desc)` mints a fresh symbol;
    /// `new Symbol()` throws TypeError.
    SymbolFn,
    /// Symbol.for / Symbol.keyFor (20.4.2) over the GlobalSymbolRegistry.
    SymbolFor,
    SymbolKeyFor,
    /// The %BigInt% function (20.2.1): `BigInt(value)` coerces (ToBigInt with
    /// the integrality check); `new BigInt()` throws TypeError.
    BigIntFn,
    /// BigInt.asIntN / asUintN (20.2.2).
    BigIntAsIntN,
    BigIntAsUintN,
    /// BigInt.prototype.toString / valueOf / toLocaleString (20.2.3).
    BigIntProtoToString,
    BigIntProtoValueOf,
    BigIntProtoToLocaleString,
    /// Symbol.prototype.toString / valueOf / [@@toPrimitive] and the
    /// `description` accessor getter (20.4.3).
    SymbolProtoToString,
    SymbolProtoValueOf,
    SymbolProtoToPrimitive,
    SymbolProtoDescriptionGet,
    /// %Function.prototype%[@@hasInstance] (20.2.3.6): the default
    /// OrdinaryHasInstance, reified so `instanceof` routes through it.
    FunctionProtoHasInstance,
    /// Object.getOwnPropertySymbols (20.1.2.11).
    ObjectGetOwnPropertySymbols,
    /// %Date% (21.4.2) and its statics/methods.
    DateCtor,
    DateNow,
    DateUtc,
    DateParse,
    DateMethod(DateOp),
    /// %RegExp% (22.2.4): `RegExp(pattern, flags)` and `new RegExp(...)`.
    RegExpCtor,
    /// %RegExp.prototype% method (exec/test/toString and the @@-protocols).
    RegExpProto(RegExpProtoOp),
    /// A %RegExp.prototype% flag accessor getter (source/flags/global/...).
    RegExpFlagGet(RegExpFlag),
    /// `get RegExp[@@species]` (22.2.5.2): returns the receiver.
    RegExpSpeciesGet,
    /// %RegExpStringIteratorPrototype%.next (22.2.9.2.1).
    RegExpStringIteratorNext,

    // -- ArrayBuffer (25.1) --------------------------------------------------
    /// %ArrayBuffer% (25.1.4).
    ArrayBufferCtor,
    /// ArrayBuffer.isView (25.1.5.1).
    ArrayBufferIsView,
    /// get ArrayBuffer[@@species] / get %TypedArray%[@@species] — returns the
    /// receiver.
    SpeciesGetReceiver,
    /// %ArrayBuffer.prototype% accessor getters (25.1.6).
    ArrayBufferByteLengthGet,
    ArrayBufferMaxByteLengthGet,
    ArrayBufferResizableGet,
    ArrayBufferDetachedGet,
    /// %ArrayBuffer.prototype% methods.
    ArrayBufferSlice,
    ArrayBufferResize,
    ArrayBufferTransfer,
    ArrayBufferTransferToFixed,

    // -- DataView (25.3) -----------------------------------------------------
    /// %DataView% (25.3.2).
    DataViewCtor,
    DataViewBufferGet,
    DataViewByteLengthGet,
    DataViewByteOffsetGet,
    /// DataView.prototype.get<Type> / set<Type> (25.3.4).
    DataViewGet(ElementType),
    DataViewSet(ElementType),

    // -- TypedArray (23.2) ---------------------------------------------------
    /// The abstract %TypedArray% constructor (23.2.1): always throws.
    TypedArrayAbstractCtor,
    /// A concrete typed-array constructor (Int8Array, ...).
    TypedArrayCtor(ElementType),
    /// %TypedArray%.from / .of (23.2.2).
    TypedArrayFrom,
    TypedArrayOf,
    /// %TypedArray.prototype% accessor getters (23.2.3).
    TypedArrayBufferGet,
    TypedArrayByteLengthGet,
    TypedArrayByteOffsetGet,
    TypedArrayLengthGet,
    /// get %TypedArray.prototype%[@@toStringTag] (23.2.3.38): the constructor
    /// name for a typed array, else undefined.
    TypedArrayToStringTagGet,
    /// A %TypedArray.prototype% method (23.2.3).
    TypedArrayMethod(TAMethod),

    // -- Promise (27.2) + the job/timer host surface ------------------------
    /// %Promise% (27.2.3): `new Promise(executor)`.
    PromiseCtor,
    /// Promise.resolve / reject (27.2.4.7 / .6).
    PromiseResolveStatic,
    PromiseRejectStatic,
    /// Promise.all / allSettled / race / any (27.2.4.1-3, .5).
    PromiseAll,
    PromiseAllSettled,
    PromiseRace,
    PromiseAny,
    /// Promise.prototype.then / catch / finally (27.2.5.4 / .1 / .3).
    PromiseProtoThen,
    PromiseProtoCatch,
    PromiseProtoFinally,
    /// get Promise[@@species] (27.2.4.10): returns the receiver.
    PromiseSpeciesGet,
    /// The global `setTimeout` / `setInterval` / `clearTimeout` /
    /// `clearInterval` / `setImmediate` / `clearImmediate` firewall shims.
    SetTimeout,
    SetInterval,
    ClearTimer,
    SetImmediate,
    /// The global `queueMicrotask` (HTML): enqueue a Promise-job.
    QueueMicrotask,
    /// %AsyncFunction% (27.7.1): callable identity only — dynamic async-function
    /// construction from source is out of slice.
    AsyncFunctionCtor,

    // -- Reflect (28.1) ------------------------------------------------------
    /// The 13 %Reflect% static methods, each a thin front for a metaobject
    /// internal method (spec-exact, matching the Proxy internal-method
    /// semantics they share).
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

    // -- Proxy (28.2) --------------------------------------------------------
    /// The %Proxy% constructor (28.2.1): `new Proxy(target, handler)`; calling
    /// it without `new`, or with a non-object target/handler, throws TypeError.
    ProxyCtor,
    /// Proxy.revocable (28.2.2.1): returns `{ proxy, revoke }`.
    ProxyRevocable,

    /// Object.setPrototypeOf (20.1.2.22).
    ObjectSetPrototypeOf,

    // -- Map / Set / WeakMap / WeakSet (24) ---------------------------------
    /// The %Map% (24.1.1) / %Set% (24.2.1) / %WeakMap% (24.3.1) / %WeakSet%
    /// (24.4.1) constructors: `new`-only.
    MapCtor,
    SetCtor,
    WeakMapCtor,
    WeakSetCtor,
    /// Map.groupBy (24.1.2.1): registered so the ctor own surface is exact;
    /// calling it refuses soundly (grouping is out of the current slice).
    MapGroupBy,
    /// %Map.prototype% methods (24.1.3).
    MapProtoGet,
    MapProtoSet,
    MapProtoHas,
    MapProtoDelete,
    MapProtoClear,
    MapProtoForEach,
    /// get Map.prototype.size (24.1.3.10).
    MapSizeGet,
    /// Map.prototype.entries (24.1.3.4, also @@iterator) / keys / values.
    MapProtoEntries,
    MapProtoKeys,
    MapProtoValues,
    /// %Set.prototype% methods (24.2.3).
    SetProtoAdd,
    SetProtoHas,
    SetProtoDelete,
    SetProtoClear,
    SetProtoForEach,
    /// get Set.prototype.size (24.2.3.9).
    SetSizeGet,
    /// Set.prototype.entries (24.2.3.5) / values (also keys + @@iterator).
    SetProtoEntries,
    SetProtoValues,
    /// A Set-methods-proposal %Set.prototype% method (union/intersection/
    /// difference/symmetricDifference/isSubsetOf/isSupersetOf/isDisjointFrom):
    /// registered so the prototype own surface matches Node exactly, but
    /// calling one refuses soundly (out of the current slice).
    SetProtoCombinator,
    /// %WeakMap.prototype% (24.3.3) / %WeakSet.prototype% (24.4.3) methods.
    WeakMapProtoGet,
    WeakMapProtoSet,
    WeakMapProtoHas,
    WeakMapProtoDelete,
    WeakSetProtoAdd,
    WeakSetProtoHas,
    WeakSetProtoDelete,
    /// %MapIteratorPrototype%.next (24.1.5.2.1) / %SetIteratorPrototype%.next
    /// (24.2.5.2.1).
    MapIteratorNext,
    SetIteratorNext,
}

/// A %TypedArray.prototype% method identity. Members marked `impl` below are
/// modeled exactly; the rest are registered (so `typeof`/`.name`/`.length`
/// are exact) but refuse soundly when called.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TAMethod {
    At,
    CopyWithin,
    Entries,
    Every,
    Fill,
    Filter,
    Find,
    FindIndex,
    FindLast,
    FindLastIndex,
    ForEach,
    Includes,
    IndexOf,
    Join,
    Keys,
    LastIndexOf,
    Map,
    Reduce,
    ReduceRight,
    Reverse,
    Set,
    Slice,
    Some,
    Sort,
    Subarray,
    ToLocaleString,
    ToReversed,
    ToSorted,
    ToString,
    Values,
    With,
}

/// A %RegExp.prototype% method identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegExpProtoOp {
    Exec,
    Test,
    ToString,
    /// `[@@match]` (22.2.5.6).
    Match,
    /// `[@@matchAll]` (22.2.5.8).
    MatchAll,
    /// `[@@replace]` (22.2.5.10).
    Replace,
    /// `[@@search]` (22.2.5.11).
    Search,
    /// `[@@split]` (22.2.5.12).
    Split,
}

/// A RegExp flag accessor (each is a getter on %RegExp.prototype%).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegExpFlag {
    Source,
    Flags,
    Global,
    IgnoreCase,
    Multiline,
    DotAll,
    Unicode,
    UnicodeSets,
    Sticky,
    HasIndices,
}

/// Date.prototype methods the slice models exactly (UTC == local under the
/// driver's TZ=0 firewall). Human-readable string forms (toString/toDateString/
/// toLocaleString/...) carry engine-specific timezone names and are refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DateOp {
    /// valueOf / getTime.
    GetTime,
    GetFullYear,
    GetMonth,
    GetDate,
    GetDay,
    GetHours,
    GetMinutes,
    GetSeconds,
    GetMilliseconds,
    GetTimezoneOffset,
    SetTime,
    SetFullYear,
    SetMonth,
    SetDate,
    SetHours,
    SetMinutes,
    SetSeconds,
    SetMilliseconds,
    ToIsoString,
    ToJson,
    ToPrimitive,
}

/// Math methods the model makes exact (never the implementation-approximated
/// transcendentals).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MathOp {
    Abs,
    Ceil,
    Floor,
    Max,
    Min,
    Pow,
    Round,
    Sign,
    Sqrt,
    Trunc,
}

/// String.prototype methods in the slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StrOp {
    CharAt,
    CharCodeAt,
    IndexOf,
    LastIndexOf,
    Slice,
    Substring,
    Split,
    Replace,
    ReplaceAll,
    Match,
    MatchAll,
    Search,
    Trim,
    ToLowerCase,
    ToUpperCase,
    ToStringOrValueOf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumPred {
    IsNaN,
    IsFinite,
    IsInteger,
    IsSafeInteger,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeErrorKind {
    Error,
    TypeError,
    RangeError,
    ReferenceError,
    SyntaxError,
    EvalError,
    UriError,
}

/// Function payload: a user closure, a class constructor, a bound function,
/// or a builtin.
#[derive(Debug, Clone)]
pub enum FnImpl {
    User {
        lit: Rc<crate::ast::FuncLit>,
        env: EnvId,
        /// [[HomeObject]] for methods (super.x resolution).
        home: Option<ObjId>,
    },
    /// A class constructor function object (10.2 [[ConstructorKind]]).
    ClassCtor(Rc<ClassCtorRec>),
    /// An arrow closure: this/home/ctor-frame captured at creation.
    Arrow {
        lit: Rc<crate::ast::FuncLit>,
        env: EnvId,
        this_v: Box<Value>,
        home: Option<ObjId>,
        frame: Option<Rc<crate::interp::CtorFrame>>,
    },
    Bound {
        target: ObjId,
        this_v: Box<Value>,
        args: Rc<Vec<Value>>,
    },
    Builtin(Builtin),
    /// A dynamically-created internal function object with captured state: the
    /// Promise resolving functions, the combinator element-closures, the
    /// `finally` wrappers, and the async-`await` resume handlers (25.6). Never
    /// a constructor.
    Native(Rc<crate::promise::NativeClosure>),
}

/// The runtime record behind a class constructor.
#[derive(Debug)]
pub struct ClassCtorRec {
    /// The explicit `constructor` literal; None = the synthesized default.
    pub lit: Option<Rc<crate::ast::FuncLit>>,
    /// The class scope (carries the inner class self-binding).
    pub env: EnvId,
    /// The class prototype object ([[HomeObject]] of the constructor).
    pub home: ObjId,
    pub derived: bool,
    /// Instance fields in declaration order (keys already evaluated).
    pub fields: Rc<Vec<FieldRec>>,
    /// Instance private methods/accessors (shared function objects) added to
    /// each new instance BEFORE the field initializers run
    /// (InitializeInstanceElements order, 15.7.15).
    pub priv_methods: Rc<Vec<PrivateElement>>,
    /// The class PrivateEnvironment (field initializers and the constructor
    /// body resolve `#name` through it).
    pub priv_env: Option<Rc<crate::interp::PrivEnvFrame>>,
}

/// One instance-field record: key (evaluated at class definition) + the
/// initializer expression (evaluated per instance with `this` bound).
#[derive(Debug)]
pub struct FieldRec {
    pub key: FieldKey,
    pub init: Option<Rc<crate::ast::Expr>>,
}

/// A field's key: a public property key (already evaluated) or a resolved
/// private name (with its `#ident` text for NamedEvaluation).
#[derive(Debug)]
pub enum FieldKey {
    Public(Units),
    Private { name: PrivName, ident: Units },
}

/// The mapped-arguments parameter map: for index i, `map[i]` names the
/// parameter binding (in `env`) the index aliases; None = unmapped.
#[derive(Debug, Clone)]
pub struct ArgsMap {
    pub env: EnvId,
    pub map: Vec<Option<String>>,
}

/// The iteration kind of an Array Iterator (23.1.5.1 [[ArrayIterationKind]]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArrayIterKind {
    Key,
    Value,
    Entry,
}

/// The iteration kind of a Map/Set Iterator (24.1.5.1 / 24.2.5.1
/// [[MapNextIndex]] companion): keys, values, or key+value pairs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CollIterKind {
    Key,
    Value,
    Entry,
}

/// A hashable canonical key for a keyed collection under SameValueZero
/// (7.2.12) with CanonicalizeKeyedCollectionKey (24.5.1): -0𝔽 folds to +0𝔽 and
/// every NaN collapses to one representative, so the index map matches the
/// spec's key identity exactly.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CollKey {
    Undef,
    Null,
    Bool(bool),
    /// f64 bits, with -0 → +0 and every NaN → one canonical pattern.
    Num(u64),
    Big(BigInt),
    Str(Units),
    Sym(u32),
    Obj(u32),
}

/// The entry store shared by a Map (24.1.4 [[MapData]]) / Set (24.2.4
/// [[SetData]]) / WeakMap (24.3) / WeakSet (24.4) AND its live iterators.
/// Entries keep insertion order with in-place tombstones (`None`) so a live
/// iterator observes later additions and skips deletions/clears (24.1.5.1): a
/// deleted or cleared entry becomes `None` in place; new keys append; the
/// `index` maps a canonical key to its live entry slot for O(1) get/has/delete.
/// For a Set/WeakSet the pair's value equals its key.
#[derive(Debug, Default)]
pub struct CollectionData {
    pub entries: Vec<Option<(Value, Value)>>,
    pub index: std::collections::HashMap<CollKey, usize>,
    pub size: usize,
}

/// The element type of a typed array / DataView access (23.2, Table 71). Each
/// carries a fixed element byte width and the concrete constructor name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ElementType {
    Int8,
    Uint8,
    Uint8Clamped,
    Int16,
    Uint16,
    Int32,
    Uint32,
    Float16,
    Float32,
    Float64,
    BigInt64,
    BigUint64,
}

impl ElementType {
    /// [[ElementSize]] in bytes.
    #[must_use]
    pub fn bytes(self) -> usize {
        match self {
            ElementType::Int8 | ElementType::Uint8 | ElementType::Uint8Clamped => 1,
            ElementType::Int16 | ElementType::Uint16 | ElementType::Float16 => 2,
            ElementType::Int32 | ElementType::Uint32 | ElementType::Float32 => 4,
            ElementType::Float64 | ElementType::BigInt64 | ElementType::BigUint64 => 8,
        }
    }

    /// The concrete constructor name ("Int8Array", ...).
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            ElementType::Int8 => "Int8Array",
            ElementType::Uint8 => "Uint8Array",
            ElementType::Uint8Clamped => "Uint8ClampedArray",
            ElementType::Int16 => "Int16Array",
            ElementType::Uint16 => "Uint16Array",
            ElementType::Int32 => "Int32Array",
            ElementType::Uint32 => "Uint32Array",
            ElementType::Float16 => "Float16Array",
            ElementType::Float32 => "Float32Array",
            ElementType::Float64 => "Float64Array",
            ElementType::BigInt64 => "BigInt64Array",
            ElementType::BigUint64 => "BigUint64Array",
        }
    }

    /// A BigInt-backed element type: construction and element ops refuse (the
    /// value model has no BigInt), but the global/typeof/harness surface is
    /// exact.
    #[must_use]
    pub fn is_bigint(self) -> bool {
        matches!(self, ElementType::BigInt64 | ElementType::BigUint64)
    }
}

/// The mutable byte storage behind an ArrayBuffer (25.1), shared by every view
/// (typed array / DataView) over it via `Rc<RefCell<..>>`.
#[derive(Debug)]
pub struct BufferData {
    pub bytes: Vec<u8>,
    /// [[ArrayBufferDetachKey]]/detached flag: once detached, byte access on
    /// every view over it is out-of-bounds.
    pub detached: bool,
    /// [[ArrayBufferMaxByteLength]] — `Some` iff the buffer is resizable.
    pub max_byte_length: Option<usize>,
}

#[derive(Debug, Clone)]
pub enum ObjKind {
    Plain,
    Array,
    /// A String exotic wrapper ([[StringData]]); its index/length own
    /// properties are materialized as ordinary props at construction.
    StringObj(std::rc::Rc<Units>),
    /// A Number wrapper ([[NumberData]]); no own properties.
    NumberObj(f64),
    /// A Boolean wrapper ([[BooleanData]]); no own properties.
    BoolObj(bool),
    /// An arguments exotic object (10.4.4). The payload carries the mapped
    /// parameter aliases (empty for strict/unmapped arguments).
    Arguments(ArgsMap),
    /// An instance created by a native Error constructor. Engines add own
    /// engine-specific properties (`stack`, ...) to these, so projecting one
    /// refuses.
    Error,
    /// A generator instance (27.5). Observationally an ordinary object (no own
    /// properties; [[Prototype]] taken from the generator function's
    /// `.prototype` at call time); the resumable state is `Interp.generators`.
    Generator(crate::value::GenId),
    /// An Array Iterator object (23.1.5): [[IteratedArrayLike]] (None once
    /// exhausted), [[ArrayIteratorNextIndex]], [[ArrayIterationKind]]. Its
    /// [[Prototype]] is %ArrayIteratorPrototype%; it has no own properties, so
    /// it projects as an ordinary object with cls "Object" through the chain.
    ArrayIterator {
        target: Option<ObjId>,
        index: u64,
        kind: ArrayIterKind,
    },
    /// A String Iterator object (22.1.5): [[IteratedString]] (an immutable
    /// snapshot — strings are primitive, so the code points never change under
    /// iteration) and [[StringNextIndex]] (a UTF-16 code-unit cursor, advanced
    /// one code POINT per step). None once exhausted. Its [[Prototype]] is
    /// %StringIteratorPrototype%; it has no own properties, so it projects as
    /// an ordinary object with cls "Object" through the chain (Node:
    /// `"ab"[Symbol.iterator]()` prints `Object [String Iterator] {}`).
    StringIterator {
        string: Option<std::rc::Rc<Units>>,
        index: usize,
    },
    Function(FnImpl),
    /// A Symbol exotic wrapper ([[SymbolData]]), from `Object(sym)`. No own
    /// properties; [[Prototype]] is %Symbol.prototype%; cls "Symbol".
    SymbolObj(crate::value::SymId),
    /// A BigInt wrapper ([[BigIntData]]), from `Object(1n)`. No own properties;
    /// [[Prototype]] is %BigInt.prototype%; cls "BigInt".
    BigIntObj(Rc<BigInt>),
    /// A Date exotic ([[DateValue]], 21.4): a mutable time value in
    /// milliseconds since the epoch (may be NaN). No own properties; cls
    /// "Date". The value is mutated in place by the Date setters.
    DateObj(f64),
    /// A RegExp object (22.2.7): [[RegExpMatcher]] (the compiled pattern),
    /// [[OriginalSource]], [[OriginalFlags]]. Its only own property is
    /// `lastIndex` (writable, non-enumerable, non-configurable), materialized
    /// as an ordinary prop; cls "RegExp".
    RegExpObj(std::rc::Rc<crate::regexp::RegExpData>),
    /// A %RegExpStringIterator% (22.2.9.1) from `RegExp.prototype[@@matchAll]`:
    /// [[IteratingRegExp]], [[IteratedString]], [[Global]], [[Unicode]],
    /// [[Done]]. No own properties; projects as an ordinary object (cls
    /// "Object" through the chain — Node prints `Object [RegExp String
    /// Iterator] {}`).
    RegExpStringIterator {
        regexp: ObjId,
        string: std::rc::Rc<Units>,
        global: bool,
        unicode: bool,
        done: bool,
    },
    /// An ArrayBuffer (25.1): the shared byte storage. cls "ArrayBuffer"; its
    /// own enumerable surface is empty (byteLength etc. are prototype
    /// accessors), so it projects as an ordinary object with cls "ArrayBuffer".
    ArrayBuffer(Rc<RefCell<BufferData>>),
    /// A DataView (25.3): a byte window [byte_offset, byte_offset+byte_length)
    /// over `buffer`. cls "DataView"; no own properties. Bounds/detach are
    /// re-checked against the buffer's CURRENT length on every access.
    DataView {
        buffer: ObjId,
        byte_offset: usize,
        byte_length: usize,
    },
    /// A typed array (23.2): `length` elements of `elem` starting at
    /// `byte_offset` in `buffer`. Integer-indexed exotic get/set/has/define/
    /// delete/ownKeys synthesize element access over the shared bytes; cls
    /// resolves to "Object" (its prototypes are not in the class-tag list).
    TypedArray {
        buffer: ObjId,
        byte_offset: usize,
        length: usize,
        elem: ElementType,
    },
    /// A Promise instance (27.2): its [[PromiseState]] / [[PromiseResult]] /
    /// reaction lists live in `Interp.promises` at this id. Observationally an
    /// ordinary object (no own enumerable properties; cls "Promise" through the
    /// chain), so it projects like a plain object with cls "Promise".
    Promise(crate::value::PromiseId),
    /// A Proxy exotic object (10.5): [[ProxyTarget]] and [[ProxyHandler]].
    /// Both are `Some` while the proxy is live; Proxy revocation sets both to
    /// `None`, and every internal method on a revoked proxy throws TypeError.
    /// `callable`/`constructor` are fixed at creation from the target (a
    /// revoked callable proxy still `typeof`s "function"), and give the proxy
    /// its [[Call]]/[[Construct]] presence. A proxy NEVER reaches the trace
    /// projection: the driver's deep-print would invoke its ownKeys /
    /// getOwnPropertyDescriptor traps, which a pure structural read cannot
    /// reproduce — so projecting one is a sound `NoCoverage` refusal (the
    /// synchronous-assert Proxy tests, the majority, never log the proxy).
    Proxy {
        target: Option<ObjId>,
        handler: Option<ObjId>,
        callable: bool,
        constructor: bool,
    },
    /// A Map (24.1) / Set (24.2) / WeakMap (24.3) / WeakSet (24.4): the shared
    /// entry store. cls resolves through the prototype chain
    /// ("Map"/"Set"/"WeakMap"/"WeakSet"); the entries are internal slots, never
    /// own properties, so it projects like a plain object with the collection's
    /// class tag (Node's structured projection of `new Map([[1,2]])` is
    /// `{ cls:"Map", props:[] }`). The store is shared via `Rc<RefCell<..>>`
    /// with every live iterator over it.
    Map(Rc<RefCell<CollectionData>>),
    Set(Rc<RefCell<CollectionData>>),
    WeakMap(Rc<RefCell<CollectionData>>),
    WeakSet(Rc<RefCell<CollectionData>>),
    /// A Map Iterator (24.1.5) / Set Iterator (24.2.5) object: shares the
    /// collection's entry store, holds a forward cursor and the iteration kind.
    /// `target` is None once exhausted ([[Map]]/[[Set]] set to empty). No own
    /// properties; its [[Prototype]] is %MapIteratorPrototype% /
    /// %SetIteratorPrototype% (carrying `next` + @@toStringTag), so it projects
    /// like a plain object with cls "Object" through the chain.
    MapIterator {
        target: Option<Rc<RefCell<CollectionData>>>,
        index: usize,
        kind: CollIterKind,
    },
    SetIterator {
        target: Option<Rc<RefCell<CollectionData>>>,
        index: usize,
        kind: CollIterKind,
    },
    /// Intrinsic infrastructure (prototypes, console, JSON, Math, the global
    /// object): projecting one would expose engine-divergent surface, so the
    /// projection refuses.
    IntrinsicOpaque,
}

#[derive(Debug)]
pub struct Object {
    pub proto: Option<ObjId>,
    pub props: IndexMap<Units, Prop>,
    /// Symbol-keyed own properties (6.1.7): enumerated AFTER every string key
    /// (spec order), never visited by Object.keys/getOwnPropertyNames/for-in.
    /// `IndexMap` preserves creation order, which is the spec's symbol-key
    /// enumeration order.
    pub sym_props: IndexMap<SymId, Prop>,
    pub kind: ObjKind,
    pub extensible: bool,
    /// [[PrivateElements]] (6.1.7.2): private fields/methods/accessors keyed by
    /// PrivateName. NOT part of the ordinary property surface — never
    /// enumerated, never projected, invisible to `in`/getOwnPropertyNames.
    pub priv_elems: Vec<PrivateElement>,
}

impl Object {
    #[must_use]
    pub fn new(kind: ObjKind, proto: Option<ObjId>) -> Object {
        Object {
            proto,
            props: IndexMap::new(),
            sym_props: IndexMap::new(),
            kind,
            extensible: true,
            priv_elems: Vec::new(),
        }
    }

    #[must_use]
    pub fn is_callable(&self) -> bool {
        matches!(
            self.kind,
            ObjKind::Function(_) | ObjKind::Proxy { callable: true, .. }
        )
    }
}

/// Own keys in spec order: canonical array indices ascending, then the
/// remaining string keys in insertion order. (No symbol keys in the slice.)
#[must_use]
pub fn ordered_own_keys(obj: &Object) -> Vec<Units> {
    let mut indices: Vec<(u32, &Units)> = Vec::new();
    let mut rest: Vec<&Units> = Vec::new();
    for k in obj.props.keys() {
        match array_index_of(k) {
            Some(i) => indices.push((i, k)),
            None => rest.push(k),
        }
    }
    indices.sort_by_key(|(i, _)| *i);
    indices
        .into_iter()
        .map(|(_, k)| k.clone())
        .chain(rest.into_iter().cloned())
        .collect()
}

/// One declarative binding.
#[derive(Debug, Clone)]
pub struct Binding {
    pub value: Value,
    pub mutable: bool,
    /// false = TDZ (let/const declared, not yet initialized).
    pub initialized: bool,
    /// An immutable binding created with strict=false (the named function
    /// expression's self-binding): assignment is a silent no-op in sloppy
    /// code and TypeError in strict code. `const` (strict=true immutable)
    /// throws in both. Spec: CreateImmutableBinding's [[Strict]] flag,
    /// consulted by SetMutableBinding.
    pub fn_name_immutable: bool,
}

impl Binding {
    /// An ordinary initialized mutable binding.
    #[must_use]
    pub fn var(value: Value) -> Binding {
        Binding {
            value,
            mutable: true,
            initialized: true,
            fn_name_immutable: false,
        }
    }
}

#[derive(Debug)]
pub struct EnvFrame {
    pub parent: Option<EnvId>,
    pub bindings: std::collections::HashMap<String, Binding>,
    /// True for a function's top-level variable environment (the frame holding
    /// params / `arguments` / hoisted `var` + function declarations). A sloppy
    /// direct eval hoists its `var`/function declarations into the nearest such
    /// frame up the chain (its caller's VariableEnvironment); if none exists on
    /// the chain the variable environment is the global object.
    pub var_boundary: bool,
    /// Names bound here by a sloppy direct eval's `var`/function declarations
    /// (EvalDeclarationInstantiation with `deletableBindings` = true): unlike
    /// ordinary declarative bindings these are deletable via `delete name`.
    pub deletable: std::collections::HashSet<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn array_index_canonicality() {
        assert_eq!(array_index_of(&units_from_str("0")), Some(0));
        assert_eq!(array_index_of(&units_from_str("42")), Some(42));
        assert_eq!(array_index_of(&units_from_str("01")), None);
        assert_eq!(array_index_of(&units_from_str("-1")), None);
        assert_eq!(array_index_of(&units_from_str("4294967294")), Some(4_294_967_294));
        assert_eq!(array_index_of(&units_from_str("4294967295")), None);
        assert_eq!(array_index_of(&units_from_str("length")), None);
        assert_eq!(array_index_of(&units_from_str("")), None);
    }
}
