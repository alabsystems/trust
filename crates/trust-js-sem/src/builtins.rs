// Realm construction and builtin dispatch: the intrinsic objects the slice
// models (Object/Function/Array/Error machinery, String/Number/Boolean/
// isNaN/isFinite, String.prototype, Math, console, JSON.stringify) plus the
// miss-danger tables that make every UNMODELED intrinsic property a refusal
// instead of a wrong `undefined`.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{strict_eq, Abrupt, ERes, Interp};
use crate::number::js_number_to_string;
use crate::value::{
    array_index_of, units_eq_ascii, units_from_str, units_to_lossy, Builtin, DateOp, EnvFrame,
    FnImpl, MathOp, NativeErrorKind, ObjId, ObjKind, Object, Prop, PropDesc, PropVal, PropertyKey,
    StrOp, SymData, SymId, Units, Value,
};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use trust_js_trace::HostEvent;

const OBJECT_PROTO_DANGER: &[&str] = &[
    "__proto__",
    "__defineGetter__",
    "__defineSetter__",
    "__lookupGetter__",
    "__lookupSetter__",
];

const FUNCTION_PROTO_DANGER: &[&str] = &["toString", "caller", "arguments"];

/// Real own properties of String.prototype the model does not carry
/// (verified against Node 24; a miss on one of these can never fall through
/// to Object.prototype).
const STRING_PROTO_DANGER: &[&str] = &[
    "anchor", "at", "big", "blink", "bold", "codePointAt", "concat", "endsWith", "fixed",
    "fontcolor", "fontsize", "includes", "isWellFormed", "italics", "link", "localeCompare",
    "normalize", "padEnd", "padStart", "repeat",
    "small", "startsWith", "strike", "sub", "substr", "sup", "toLocaleLowerCase",
    "toLocaleUpperCase", "toWellFormed", "trimEnd", "trimLeft", "trimRight", "trimStart",
];

/// Real own properties of Number.prototype the model does not carry.
const NUMBER_PROTO_DANGER: &[&str] =
    &["toExponential", "toFixed", "toLocaleString", "toPrecision"];

/// Real own properties of %IteratorPrototype% (Iterator Helpers, Node 24) the
/// model does not carry; a miss on one can never fall through to
/// Object.prototype. `constructor` is %Iterator%, likewise unmodeled.
const ITERATOR_PROTO_DANGER: &[&str] = &[
    "constructor", "drop", "every", "filter", "find", "flatMap", "forEach", "map", "reduce",
    "some", "take", "toArray",
];

const ARRAY_PROTO_DANGER: &[&str] = &[
    "at", "concat", "copyWithin", "fill", "findLast", "findLastIndex", "flat",
    "flatMap", "reverse", "sort", "splice", "toLocaleString", "toReversed", "toSorted",
    "toSpliced", "with",
];

/// Real own properties of %RegExp.prototype% the model does not carry: `compile`
/// (Annex B, 22.2.6.3.1). A miss on it can never fall through to
/// Object.prototype.
const REGEXP_PROTO_DANGER: &[&str] = &["compile"];

/// The 13 well-known symbols, in the driver's `WELL_KNOWN_SYMBOLS` order. The
/// property name on the `Symbol` constructor (`Symbol.iterator`, ...) and the
/// suffix of the projection name ("Symbol.iterator").
pub const WK_NAMES: [&str; 13] = [
    "iterator",
    "asyncIterator",
    "hasInstance",
    "isConcatSpreadable",
    "match",
    "matchAll",
    "replace",
    "search",
    "species",
    "split",
    "toPrimitive",
    "toStringTag",
    "unscopables",
];
/// Full projection names, parallel to `WK_NAMES` (kept `'static` so `SymData`
/// can borrow them).
pub const WK_PROJ: [&str; 13] = [
    "Symbol.iterator",
    "Symbol.asyncIterator",
    "Symbol.hasInstance",
    "Symbol.isConcatSpreadable",
    "Symbol.match",
    "Symbol.matchAll",
    "Symbol.replace",
    "Symbol.search",
    "Symbol.species",
    "Symbol.split",
    "Symbol.toPrimitive",
    "Symbol.toStringTag",
    "Symbol.unscopables",
];
// Indices into WK_NAMES/wk_syms for the symbols the interpreter dispatches on.
pub const WK_ITERATOR: usize = 0;
pub const WK_HAS_INSTANCE: usize = 2;
pub const WK_IS_CONCAT_SPREADABLE: usize = 3;
pub const WK_MATCH: usize = 4;
pub const WK_MATCH_ALL: usize = 5;
pub const WK_REPLACE: usize = 6;
pub const WK_SEARCH: usize = 7;
pub const WK_SPECIES: usize = 8;
pub const WK_SPLIT: usize = 9;
pub const WK_TO_PRIMITIVE: usize = 10;
pub const WK_TO_STRING_TAG: usize = 11;
pub const WK_UNSCOPABLES: usize = 12;

pub struct Intrinsics {
    pub object_proto: ObjId,
    pub function_proto: ObjId,
    pub array_proto: ObjId,
    pub string_proto: ObjId,
    pub number_proto: ObjId,
    pub boolean_proto: ObjId,
    /// The intrinsic %Array% constructor: ArraySpeciesCreate needs its
    /// identity to recognize the (only) default constructor the slice models.
    pub array_ctor: ObjId,
    pub error_proto: ObjId,
    pub type_error_proto: ObjId,
    pub range_error_proto: ObjId,
    pub reference_error_proto: ObjId,
    pub syntax_error_proto: ObjId,
    pub eval_error_proto: ObjId,
    pub uri_error_proto: ObjId,
    /// console: a HOST object whose real own surface is enumerable and
    /// unmodeled — enumeration over it refuses (ECMA intrinsics' unmodeled
    /// surfaces are spec-pinned non-enumerable; console's is not).
    pub console: ObjId,
    /// %ThrowTypeError%: the strict arguments `callee` poison accessor.
    pub throw_type_error: ObjId,
    /// %IteratorPrototype% (27.1.2): the shared ancestor of the generator
    /// prototype; its only string-keyed own surface is empty (its `@@iterator`
    /// method is symbol-keyed). Its Iterator-Helper own names refuse via
    /// ITERATOR_PROTO_DANGER; other misses fall through to Object.prototype.
    pub iterator_proto: ObjId,
    /// %GeneratorFunction% (27.3): the (uncallable-in-slice) constructor whose
    /// identity backs `Object.getPrototypeOf(function*(){}).constructor`.
    #[allow(dead_code)]
    pub generator_function: ObjId,
    /// %GeneratorFunction.prototype% (27.3.3): the [[Prototype]] of every
    /// generator function object; carries `constructor`, `prototype`,
    /// `@@toStringTag`.
    pub generator_function_proto: ObjId,
    /// %GeneratorFunction.prototype.prototype% == %GeneratorPrototype%
    /// (27.5.1): the [[Prototype]] of a generator function's `.prototype`;
    /// carries `next`/`return`/`throw`/`constructor`/`@@toStringTag`.
    pub generator_proto: ObjId,
    /// %ArrayIteratorPrototype% (23.1.5.2): the [[Prototype]] of every Array
    /// Iterator object; its only string-keyed own property is `next` (its
    /// `@@toStringTag` is symbol-keyed, so never a string miss). A miss on any
    /// other name correctly falls through to %IteratorPrototype% then
    /// Object.prototype. Projecting it refuses by identity (unmodeled
    /// @@toStringTag).
    pub array_iterator_proto: ObjId,
    /// %StringIteratorPrototype% (22.1.5.2): the [[Prototype]] of every String
    /// Iterator object; its only string-keyed own property is `next` (its
    /// `@@toStringTag` "String Iterator" is symbol-keyed and modeled). A miss on
    /// any other name falls through to %IteratorPrototype% then Object.prototype.
    /// Projecting it refuses by identity (own-key ORDER is engine latitude).
    pub string_iterator_proto: ObjId,
    /// %Symbol.prototype% (20.4.3): its symbol surface (@@toPrimitive,
    /// @@toStringTag) and `description`/`toString`/`valueOf` are fully
    /// modeled, so cls "Symbol" resolves and reads are exact.
    pub symbol_proto: ObjId,
    /// The %Symbol% function (20.4.1).
    #[allow(dead_code)]
    pub symbol_ctor: ObjId,
    /// %BigInt.prototype% (20.2.3): cls "BigInt". Its `toString`/`valueOf`/
    /// `toLocaleString` and the non-configurable `@@toStringTag` are modeled,
    /// so cls "BigInt" resolves and reads are exact.
    pub bigint_proto: ObjId,
    /// The %BigInt% function (20.2.1): callable (coerces) but `new BigInt()`
    /// throws TypeError.
    #[allow(dead_code)]
    pub bigint_ctor: ObjId,
    /// %Date.prototype% (21.4.4): cls "Date"; its @@toPrimitive is modeled.
    pub date_proto: ObjId,
    /// The %Date% constructor (21.4.2).
    #[allow(dead_code)]
    pub date_ctor: ObjId,
    /// %RegExp.prototype% (22.2.6): cls "RegExp" via the class-tag list. Its
    /// exec/test/toString, the flag accessors, and the @@-protocols are fully
    /// modeled; `compile` (Annex B) refuses via REGEXP_PROTO_DANGER.
    pub regexp_proto: ObjId,
    /// The %RegExp% constructor (22.2.4): the SpeciesConstructor default and
    /// the IsRegExp fast path key off its identity.
    pub regexp_ctor: ObjId,
    /// %RegExpStringIteratorPrototype% (22.2.9.2): the [[Prototype]] of the
    /// iterator `RegExp.prototype[@@matchAll]` returns; carries `next` and
    /// @@toStringTag.
    pub regexp_string_iterator_proto: ObjId,
    /// The %Function.prototype%[@@hasInstance] builtin object identity: when
    /// `instanceof` resolves this exact function it takes the fast
    /// OrdinaryHasInstance path; a different (user) handler is called.
    pub function_proto_has_instance: ObjId,
    /// The %eval% intrinsic function object (19.2.1): its identity lets the
    /// call evaluator recognize the direct-eval pattern (`eval(x)` where the
    /// `eval` reference resolves to this exact object).
    pub eval_fn: ObjId,
    /// %ArrayBuffer% (25.1.3) + %ArrayBuffer.prototype% (25.1.5): cls
    /// "ArrayBuffer"; the full own surface is modeled so reads are exact.
    pub arraybuffer_ctor: ObjId,
    pub arraybuffer_proto: ObjId,
    /// %DataView% (25.3.3) + %DataView.prototype% (25.3.4): cls "DataView".
    #[allow(dead_code)]
    pub dataview_ctor: ObjId,
    pub dataview_proto: ObjId,
    /// The abstract %TypedArray% (23.2.1) + %TypedArray.prototype% (23.2.3):
    /// `Object.getPrototypeOf(Int8Array) === %TypedArray%`.
    pub typed_array_ctor: ObjId,
    pub typed_array_proto: ObjId,
    /// The concrete typed-array (elem, constructor, prototype) triples.
    pub typed_arrays: Vec<(crate::value::ElementType, ObjId, ObjId)>,
    /// The %Promise% constructor (27.2.3) + %Promise.prototype% (27.2.5): cls
    /// "Promise". The SpeciesConstructor default and the PromiseResolve fast
    /// path key off the constructor's identity.
    pub promise_ctor: ObjId,
    pub promise_proto: ObjId,
    /// %AsyncFunction% (27.7.1) + %AsyncFunction.prototype% (27.7.3): the
    /// [[Prototype]] of every async function object; carries `constructor` and
    /// (declared-owned) `@@toStringTag`.
    #[allow(dead_code)]
    pub async_function: ObjId,
    pub async_function_proto: ObjId,
    /// %Map% (24.1.1) + %Map.prototype% (24.1.3): cls "Map"; the entry store is
    /// an internal slot so instances have no own surface. %Set%/%WeakMap%/
    /// %WeakSet% likewise.
    pub map_ctor: ObjId,
    pub map_proto: ObjId,
    pub set_ctor: ObjId,
    pub set_proto: ObjId,
    #[allow(dead_code)]
    pub weakmap_ctor: ObjId,
    pub weakmap_proto: ObjId,
    #[allow(dead_code)]
    pub weakset_ctor: ObjId,
    pub weakset_proto: ObjId,
    /// %MapIteratorPrototype% (24.1.5.2) / %SetIteratorPrototype% (24.2.5.2):
    /// the [[Prototype]] of a Map/Set iterator; carries `next` + @@toStringTag.
    /// Projecting one refuses by identity (own-key order is engine latitude).
    pub map_iterator_proto: ObjId,
    pub set_iterator_proto: ObjId,
    /// The 13 well-known symbols (20.4.2.x), in `WK_NAMES` order. The first
    /// symbols allocated in the realm.
    pub wk_syms: Vec<crate::value::SymId>,
    /// Intrinsic function/host objects with real engine surface we do not
    /// model (console, JSON, Math, String.prototype, the constructors): any
    /// own-property miss on one refuses.
    pub opaque_hosts: HashSet<ObjId>,
    /// Hosts whose real static surface IS fully enumerated: a miss refuses
    /// only for the listed unmodeled names. (Their own-key ORDER is still
    /// engine latitude, so whole-surface walks refuse separately.)
    pub host_statics_danger: HashMap<ObjId, &'static [&'static str]>,
}

impl Intrinsics {
    /// Driver INTRINSIC_PROTOS entries that exist in the slice (nearest-hop
    /// identity matching makes list order irrelevant across distinct protos).
    #[must_use]
    pub fn class_tag_list(&self) -> [(ObjId, &'static str); 24] {
        [
            (self.array_proto, "Array"),
            (self.regexp_proto, "RegExp"),
            (self.promise_proto, "Promise"),
            (self.function_proto, "Function"),
            (self.error_proto, "Error:Error"),
            (self.type_error_proto, "Error:TypeError"),
            (self.range_error_proto, "Error:RangeError"),
            (self.reference_error_proto, "Error:ReferenceError"),
            (self.syntax_error_proto, "Error:SyntaxError"),
            (self.eval_error_proto, "Error:EvalError"),
            (self.uri_error_proto, "Error:URIError"),
            (self.date_proto, "Date"),
            (self.map_proto, "Map"),
            (self.set_proto, "Set"),
            (self.weakmap_proto, "WeakMap"),
            (self.weakset_proto, "WeakSet"),
            // Typed-array prototypes are deliberately absent: a typed array's
            // class tag resolves to "Object" through the chain (verified vs the
            // driver's INTRINSIC_PROTOS list).
            (self.arraybuffer_proto, "ArrayBuffer"),
            (self.dataview_proto, "DataView"),
            (self.symbol_proto, "Symbol"),
            (self.bigint_proto, "BigInt"),
            (self.boolean_proto, "Boolean"),
            (self.number_proto, "Number"),
            (self.string_proto, "String"),
            (self.object_proto, "Object"),
        ]
    }

    /// The concrete constructor for element type `e`.
    #[must_use]
    pub fn ta_ctor(&self, e: crate::value::ElementType) -> ObjId {
        self.typed_arrays
            .iter()
            .find(|(x, _, _)| *x == e)
            .map(|(_, c, _)| *c)
            .expect("typed-array ctor registered")
    }

    /// The concrete prototype for element type `e`.
    #[must_use]
    pub fn ta_proto(&self, e: crate::value::ElementType) -> ObjId {
        self.typed_arrays
            .iter()
            .find(|(x, _, _)| *x == e)
            .map(|(_, _, p)| *p)
            .expect("typed-array proto registered")
    }

    /// Every intrinsic prototype whose own-key surface/order is engine latitude
    /// (whole-surface walks + projection refuse by identity).
    #[must_use]
    pub fn is_binary_proto(&self, oid: ObjId) -> bool {
        oid == self.arraybuffer_proto
            || oid == self.dataview_proto
            || oid == self.typed_array_proto
            || self.typed_arrays.iter().any(|(_, _, p)| *p == oid)
    }

    /// The `SymId` of well-known symbol at index `i` in `WK_NAMES`.
    #[must_use]
    pub fn wk(&self, i: usize) -> crate::value::SymId {
        self.wk_syms[i]
    }

    /// Does the REAL object `oid` own a well-known symbol-keyed property that
    /// this model does not store in `sym_props`? A miss on such a symbol is
    /// unsound to report as absent — the caller must refuse. Returns the
    /// well-known index if so (for diagnostics), else None. Only the pairs a
    /// conforming engine actually materializes are listed (verified against
    /// Node 24); everything else (ordinary user objects, wrappers, and the
    /// intrinsics with no symbol surface) is soundly absent.
    #[must_use]
    pub fn sym_real_owns(&self, oid: ObjId, sid: crate::value::SymId) -> bool {
        // Which well-known indices does the real object own?
        let owned: &[usize] = if oid == self.array_proto {
            &[WK_ITERATOR, WK_UNSCOPABLES]
        } else if oid == self.string_proto {
            &[WK_ITERATOR]
        } else if oid == self.iterator_proto {
            &[WK_ITERATOR, WK_TO_STRING_TAG]
        } else if oid == self.generator_proto
            || oid == self.generator_function_proto
            || oid == self.array_iterator_proto
            || oid == self.string_iterator_proto
        {
            &[WK_TO_STRING_TAG]
        } else if oid == self.array_ctor {
            &[WK_SPECIES]
        } else if oid == self.function_proto {
            &[WK_HAS_INSTANCE]
        } else if oid == self.symbol_proto {
            &[WK_TO_PRIMITIVE, WK_TO_STRING_TAG]
        } else if oid == self.bigint_proto {
            &[WK_TO_STRING_TAG]
        } else if oid == self.date_proto {
            &[WK_TO_PRIMITIVE]
        } else if oid == self.regexp_proto {
            &[WK_MATCH, WK_MATCH_ALL, WK_REPLACE, WK_SEARCH, WK_SPLIT]
        } else if oid == self.regexp_ctor {
            &[WK_SPECIES]
        } else if oid == self.regexp_string_iterator_proto {
            &[WK_TO_STRING_TAG]
        } else if oid == self.arraybuffer_proto || oid == self.dataview_proto {
            &[WK_TO_STRING_TAG]
        } else if oid == self.typed_array_proto {
            &[WK_TO_STRING_TAG, WK_ITERATOR]
        } else if oid == self.arraybuffer_ctor || oid == self.typed_array_ctor {
            &[WK_SPECIES]
        } else if oid == self.promise_proto || oid == self.async_function_proto {
            &[WK_TO_STRING_TAG]
        } else if oid == self.promise_ctor {
            &[WK_SPECIES]
        } else if oid == self.map_proto {
            &[WK_TO_STRING_TAG, WK_ITERATOR]
        } else if oid == self.set_proto {
            &[WK_TO_STRING_TAG, WK_ITERATOR]
        } else if oid == self.weakmap_proto
            || oid == self.weakset_proto
            || oid == self.map_iterator_proto
            || oid == self.set_iterator_proto
        {
            &[WK_TO_STRING_TAG]
        } else if oid == self.map_ctor || oid == self.set_ctor {
            &[WK_SPECIES]
        } else {
            &[]
        };
        owned.iter().any(|&i| self.wk_syms[i] == sid)
    }

    #[must_use]
    pub fn error_proto_for(&self, kind: NativeErrorKind) -> ObjId {
        match kind {
            NativeErrorKind::Error => self.error_proto,
            NativeErrorKind::TypeError => self.type_error_proto,
            NativeErrorKind::RangeError => self.range_error_proto,
            NativeErrorKind::ReferenceError => self.reference_error_proto,
            NativeErrorKind::SyntaxError => self.syntax_error_proto,
            NativeErrorKind::EvalError => self.eval_error_proto,
            NativeErrorKind::UriError => self.uri_error_proto,
        }
    }

    pub(crate) fn error_protos(&self) -> [ObjId; 7] {
        [
            self.error_proto,
            self.type_error_proto,
            self.range_error_proto,
            self.reference_error_proto,
            self.syntax_error_proto,
            self.eval_error_proto,
            self.uri_error_proto,
        ]
    }

    /// Is a MISS of `name` on intrinsic object `oid` dangerous (a property a
    /// real engine has but we do not model)?
    #[must_use]
    pub fn danger_reason(&self, oid: ObjId, name: &str) -> Option<&'static str> {
        if oid == self.object_proto {
            if OBJECT_PROTO_DANGER.contains(&name) {
                return Some("Object.prototype");
            }
        } else if oid == self.function_proto {
            if FUNCTION_PROTO_DANGER.contains(&name) {
                return Some("Function.prototype");
            }
        } else if oid == self.array_proto {
            if ARRAY_PROTO_DANGER.contains(&name) {
                return Some("Array.prototype");
            }
        } else if oid == self.string_proto {
            if STRING_PROTO_DANGER.contains(&name) {
                return Some("String.prototype");
            }
        } else if oid == self.number_proto {
            if NUMBER_PROTO_DANGER.contains(&name) {
                return Some("Number.prototype");
            }
        } else if oid == self.iterator_proto {
            if ITERATOR_PROTO_DANGER.contains(&name) {
                return Some("%IteratorPrototype% (Iterator Helpers)");
            }
        } else if oid == self.regexp_proto {
            if REGEXP_PROTO_DANGER.contains(&name) {
                return Some("RegExp.prototype (Annex B compile)");
            }
        } else if oid == self.boolean_proto {
            // Boolean.prototype's real own surface is fully modeled.
        } else if self.error_protos().contains(&oid) {
            if name == "stack" {
                return Some("Error.prototype surface");
            }
        } else if let Some(list) = self.host_statics_danger.get(&oid) {
            if list.contains(&name) {
                return Some("intrinsic host statics");
            }
        } else if self.opaque_hosts.contains(&oid) {
            return Some("intrinsic host-object surface");
        }
        None
    }
}

fn attrs_method(v: Value) -> Prop {
    Prop::with_attrs(v, true, false, true)
}

fn attrs_frozen(v: Value) -> Prop {
    Prop::with_attrs(v, false, false, false)
}

struct Realm<'a> {
    it: &'a mut Vec<Object>,
}

impl Realm<'_> {
    fn alloc(&mut self, o: Object) -> ObjId {
        let id = ObjId(u32::try_from(self.it.len()).expect("bounded"));
        self.it.push(o);
        id
    }

    fn put(&mut self, oid: ObjId, key: &str, p: Prop) {
        self.it[oid.0 as usize].props.insert(units_from_str(key), p);
    }

    fn put_sym(&mut self, oid: ObjId, key: SymId, p: Prop) {
        self.it[oid.0 as usize].sym_props.insert(key, p);
    }

    /// A builtin function object: own `length` then `name` (spec creation
    /// order via CreateBuiltinFunction).
    fn mk_fn(&mut self, fproto: ObjId, name: &str, len: f64, b: Builtin) -> ObjId {
        let f = self.alloc(Object::new(
            ObjKind::Function(FnImpl::Builtin(b)),
            Some(fproto),
        ));
        self.put(f, "length", Prop::with_attrs(Value::Num(len), false, false, true));
        self.put(f, "name", Prop::with_attrs(Value::str_from(name), false, false, true));
        f
    }

    /// Attach the function-expression `prototype` own property (the driver's
    /// console recorders and `print` are plain function expressions, whose
    /// real own surface includes it).
    fn attach_fn_prototype(&mut self, f: ObjId, object_proto: ObjId) {
        let p = self.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
        self.put(p, "constructor", Prop::with_attrs(Value::Obj(f), true, false, true));
        self.put(f, "prototype", Prop::with_attrs(Value::Obj(p), true, false, false));
    }
}

/// Build a fresh realm.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn create_interp() -> Interp {
    let mut heap: Vec<Object> = Vec::new();
    let mut r = Realm { it: &mut heap };

    let object_proto = r.alloc(Object::new(ObjKind::IntrinsicOpaque, None));
    let function_proto = r.alloc(Object::new(
        ObjKind::Function(FnImpl::Builtin(Builtin::FunctionProtoSelf)),
        Some(object_proto),
    ));
    r.put(function_proto, "length", Prop::with_attrs(Value::Num(0.0), false, false, true));
    r.put(function_proto, "name", Prop::with_attrs(Value::str_from(""), false, false, true));

    // Array.prototype is an Array exotic object per spec (Array.isArray(Array.
    // prototype) === true, class tag "Array"), so it carries ObjKind::Array.
    // Its projection still refuses — by identity, in project.rs — because we do
    // not model its full engine own-property surface.
    let array_proto = r.alloc(Object::new(ObjKind::Array, Some(object_proto)));
    r.put(array_proto, "length", Prop::with_attrs(Value::Num(0.0), true, false, false));

    // String.prototype (a String exotic wrapper with [[StringData]] "" in
    // real engines; opaque here, but its own `length` 0 is spec-pinned).
    let string_proto = r.alloc(Object::new(ObjKind::IntrinsicOpaque, Some(object_proto)));
    r.put(string_proto, "length", Prop::with_attrs(Value::Num(0.0), false, false, false));

    // Number.prototype / Boolean.prototype (ordinary objects per ES2015+).
    let number_proto = r.alloc(Object::new(ObjKind::IntrinsicOpaque, Some(object_proto)));
    let boolean_proto = r.alloc(Object::new(ObjKind::IntrinsicOpaque, Some(object_proto)));

    // Error prototypes.
    let error_proto = r.alloc(Object::new(ObjKind::IntrinsicOpaque, Some(object_proto)));
    let mk_nat_proto = |r: &mut Realm<'_>, name: &str| {
        let p = r.alloc(Object::new(ObjKind::IntrinsicOpaque, Some(error_proto)));
        r.put(p, "name", attrs_method(Value::str_from(name)));
        r.put(p, "message", attrs_method(Value::str_from("")));
        p
    };
    r.put(error_proto, "name", attrs_method(Value::str_from("Error")));
    r.put(error_proto, "message", attrs_method(Value::str_from("")));
    let type_error_proto = mk_nat_proto(&mut r, "TypeError");
    let range_error_proto = mk_nat_proto(&mut r, "RangeError");
    let reference_error_proto = mk_nat_proto(&mut r, "ReferenceError");
    let syntax_error_proto = mk_nat_proto(&mut r, "SyntaxError");
    let eval_error_proto = mk_nat_proto(&mut r, "EvalError");
    let uri_error_proto = mk_nat_proto(&mut r, "URIError");

    // %ThrowTypeError%.
    let throw_type_error = {
        let f = r.alloc(Object::new(
            ObjKind::Function(FnImpl::Builtin(Builtin::ThrowTypeError)),
            Some(function_proto),
        ));
        r.put(f, "length", Prop::with_attrs(Value::Num(0.0), false, false, false));
        r.put(f, "name", Prop::with_attrs(Value::str_from(""), false, false, false));
        r.it[f.0 as usize].extensible = false;
        f
    };

    // Object.prototype methods.
    let m = r.mk_fn(function_proto, "toString", 0.0, Builtin::ObjectProtoToString);
    r.put(object_proto, "toString", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "toLocaleString", 0.0, Builtin::ObjectProtoToLocaleString);
    r.put(object_proto, "toLocaleString", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "valueOf", 0.0, Builtin::ObjectProtoValueOf);
    r.put(object_proto, "valueOf", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "hasOwnProperty", 1.0, Builtin::ObjectProtoHasOwnProperty);
    r.put(object_proto, "hasOwnProperty", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "isPrototypeOf", 1.0, Builtin::ObjectProtoIsPrototypeOf);
    r.put(object_proto, "isPrototypeOf", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(
        function_proto,
        "propertyIsEnumerable",
        1.0,
        Builtin::ObjectProtoPropertyIsEnumerable,
    );
    r.put(object_proto, "propertyIsEnumerable", attrs_method(Value::Obj(m)));

    // Function.prototype.call/apply/bind
    let m = r.mk_fn(function_proto, "call", 1.0, Builtin::FunctionProtoCall);
    r.put(function_proto, "call", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "apply", 2.0, Builtin::FunctionProtoApply);
    r.put(function_proto, "apply", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "bind", 1.0, Builtin::FunctionProtoBind);
    r.put(function_proto, "bind", attrs_method(Value::Obj(m)));

    // Array.prototype methods.
    for (name, len, b) in [
        ("join", 1.0, Builtin::ArrayProtoJoin),
        ("concat", 1.0, Builtin::ArrayProtoConcat),
        ("toString", 0.0, Builtin::ArrayProtoToString),
        ("map", 1.0, Builtin::ArrayProtoMap),
        ("forEach", 1.0, Builtin::ArrayProtoForEach),
        ("push", 1.0, Builtin::ArrayProtoPush),
        ("pop", 0.0, Builtin::ArrayProtoPop),
        ("shift", 0.0, Builtin::ArrayProtoShift),
        ("unshift", 1.0, Builtin::ArrayProtoUnshift),
        ("indexOf", 1.0, Builtin::ArrayProtoIndexOf),
        ("lastIndexOf", 1.0, Builtin::ArrayProtoLastIndexOf),
        ("includes", 1.0, Builtin::ArrayProtoIncludes),
        ("slice", 2.0, Builtin::ArrayProtoSlice),
        ("filter", 1.0, Builtin::ArrayProtoFilter),
        ("every", 1.0, Builtin::ArrayProtoEvery),
        ("some", 1.0, Builtin::ArrayProtoSome),
        ("find", 1.0, Builtin::ArrayProtoFind),
        ("findIndex", 1.0, Builtin::ArrayProtoFindIndex),
        ("reduce", 1.0, Builtin::ArrayProtoReduce),
        ("reduceRight", 1.0, Builtin::ArrayProtoReduceRight),
        ("values", 0.0, Builtin::ArrayProtoValues),
        ("keys", 0.0, Builtin::ArrayProtoKeys),
        ("entries", 0.0, Builtin::ArrayProtoEntries),
    ] {
        let m = r.mk_fn(function_proto, name, len, b);
        r.put(array_proto, name, attrs_method(Value::Obj(m)));
    }

    // String.prototype methods.
    for (name, len, op) in [
        ("charAt", 1.0, StrOp::CharAt),
        ("charCodeAt", 1.0, StrOp::CharCodeAt),
        ("indexOf", 1.0, StrOp::IndexOf),
        ("lastIndexOf", 1.0, StrOp::LastIndexOf),
        ("slice", 2.0, StrOp::Slice),
        ("substring", 2.0, StrOp::Substring),
        ("split", 2.0, StrOp::Split),
        ("replace", 2.0, StrOp::Replace),
        ("replaceAll", 2.0, StrOp::ReplaceAll),
        ("match", 1.0, StrOp::Match),
        ("matchAll", 1.0, StrOp::MatchAll),
        ("search", 1.0, StrOp::Search),
        ("trim", 0.0, StrOp::Trim),
        ("toLowerCase", 0.0, StrOp::ToLowerCase),
        ("toUpperCase", 0.0, StrOp::ToUpperCase),
    ] {
        let m = r.mk_fn(function_proto, name, len, Builtin::StrProto(op));
        r.put(string_proto, name, attrs_method(Value::Obj(m)));
    }
    let m = r.mk_fn(function_proto, "toString", 0.0, Builtin::StrProto(StrOp::ToStringOrValueOf));
    r.put(string_proto, "toString", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "valueOf", 0.0, Builtin::StrProto(StrOp::ToStringOrValueOf));
    r.put(string_proto, "valueOf", attrs_method(Value::Obj(m)));

    // Error.prototype.toString
    let m = r.mk_fn(function_proto, "toString", 0.0, Builtin::ErrorProtoToString);
    r.put(error_proto, "toString", attrs_method(Value::Obj(m)));

    // Constructors.
    let mk_ctor = |r: &mut Realm<'_>, name: &str, len: f64, b: Builtin, proto: ObjId| {
        let c = r.mk_fn(function_proto, name, len, b);
        r.put(c, "prototype", attrs_frozen(Value::Obj(proto)));
        r.put(proto, "constructor", attrs_method(Value::Obj(c)));
        c
    };
    let object_ctor = mk_ctor(&mut r, "Object", 1.0, Builtin::ObjectCtor, object_proto);
    let function_ctor = mk_ctor(&mut r, "Function", 1.0, Builtin::FunctionCtor, function_proto);
    // The %eval% intrinsic (19.2.1): an ordinary builtin function `eval`,
    // length 1. Direct-vs-indirect is decided at the call site by identity.
    let eval_fn = r.mk_fn(function_proto, "eval", 1.0, Builtin::Eval);
    let array_ctor = mk_ctor(&mut r, "Array", 1.0, Builtin::ArrayCtor, array_proto);
    let m = r.mk_fn(function_proto, "isArray", 1.0, Builtin::ArrayIsArray);
    r.put(array_ctor, "isArray", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "from", 1.0, Builtin::ArrayFrom);
    r.put(array_ctor, "from", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "of", 0.0, Builtin::ArrayOf);
    r.put(array_ctor, "of", attrs_method(Value::Obj(m)));
    // Object statics.
    for (name, len, b) in [
        ("create", 2.0, Builtin::ObjectCreate),
        ("getPrototypeOf", 1.0, Builtin::ObjectGetPrototypeOf),
        ("setPrototypeOf", 2.0, Builtin::ObjectSetPrototypeOf),
        ("defineProperty", 3.0, Builtin::ObjectDefineProperty),
        ("defineProperties", 2.0, Builtin::ObjectDefineProperties),
        (
            "getOwnPropertyDescriptor",
            2.0,
            Builtin::ObjectGetOwnPropertyDescriptor,
        ),
        (
            "getOwnPropertyDescriptors",
            1.0,
            Builtin::ObjectGetOwnPropertyDescriptors,
        ),
        ("getOwnPropertyNames", 1.0, Builtin::ObjectGetOwnPropertyNames),
        ("getOwnPropertySymbols", 1.0, Builtin::ObjectGetOwnPropertySymbols),
        ("keys", 1.0, Builtin::ObjectKeys),
        ("freeze", 1.0, Builtin::ObjectFreeze),
        ("seal", 1.0, Builtin::ObjectSeal),
        ("preventExtensions", 1.0, Builtin::ObjectPreventExtensions),
        ("isFrozen", 1.0, Builtin::ObjectIsFrozen),
        ("isSealed", 1.0, Builtin::ObjectIsSealed),
        ("isExtensible", 1.0, Builtin::ObjectIsExtensible),
    ] {
        let m = r.mk_fn(function_proto, name, len, b);
        r.put(object_ctor, name, attrs_method(Value::Obj(m)));
    }
    let error_ctor = mk_ctor(
        &mut r,
        "Error",
        1.0,
        Builtin::ErrorCtor(NativeErrorKind::Error),
        error_proto,
    );
    let type_error_ctor = mk_ctor(
        &mut r,
        "TypeError",
        1.0,
        Builtin::ErrorCtor(NativeErrorKind::TypeError),
        type_error_proto,
    );
    let range_error_ctor = mk_ctor(
        &mut r,
        "RangeError",
        1.0,
        Builtin::ErrorCtor(NativeErrorKind::RangeError),
        range_error_proto,
    );
    let reference_error_ctor = mk_ctor(
        &mut r,
        "ReferenceError",
        1.0,
        Builtin::ErrorCtor(NativeErrorKind::ReferenceError),
        reference_error_proto,
    );
    let syntax_error_ctor = mk_ctor(
        &mut r,
        "SyntaxError",
        1.0,
        Builtin::ErrorCtor(NativeErrorKind::SyntaxError),
        syntax_error_proto,
    );
    let eval_error_ctor = mk_ctor(
        &mut r,
        "EvalError",
        1.0,
        Builtin::ErrorCtor(NativeErrorKind::EvalError),
        eval_error_proto,
    );
    let uri_error_ctor = mk_ctor(
        &mut r,
        "URIError",
        1.0,
        Builtin::ErrorCtor(NativeErrorKind::UriError),
        uri_error_proto,
    );

    // Value-converter globals.
    let string_fn = r.mk_fn(function_proto, "String", 1.0, Builtin::StringFn);
    r.put(string_fn, "prototype", attrs_frozen(Value::Obj(string_proto)));
    r.put(string_proto, "constructor", attrs_method(Value::Obj(string_fn)));
    let m = r.mk_fn(function_proto, "fromCharCode", 1.0, Builtin::StringFromCharCode);
    r.put(string_fn, "fromCharCode", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "fromCodePoint", 1.0, Builtin::StringFromCodePoint);
    r.put(string_fn, "fromCodePoint", attrs_method(Value::Obj(m)));
    let number_fn = r.mk_fn(function_proto, "Number", 1.0, Builtin::NumberFn);
    r.put(number_fn, "prototype", attrs_frozen(Value::Obj(number_proto)));
    r.put(number_proto, "constructor", attrs_method(Value::Obj(number_fn)));
    let m = r.mk_fn(function_proto, "toString", 1.0, Builtin::NumberProtoToString);
    r.put(number_proto, "toString", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "valueOf", 0.0, Builtin::NumberProtoValueOf);
    r.put(number_proto, "valueOf", attrs_method(Value::Obj(m)));
    // Number statics: the spec-pinned constant values and the coercion-free
    // predicates.
    for (name, v) in [
        ("NaN", f64::NAN),
        ("POSITIVE_INFINITY", f64::INFINITY),
        ("NEGATIVE_INFINITY", f64::NEG_INFINITY),
        ("MAX_VALUE", f64::MAX),
        ("MIN_VALUE", 5e-324),
        ("EPSILON", f64::EPSILON),
        ("MAX_SAFE_INTEGER", 9_007_199_254_740_991.0),
        ("MIN_SAFE_INTEGER", -9_007_199_254_740_991.0),
    ] {
        r.put(number_fn, name, attrs_frozen(Value::Num(v)));
    }
    for (name, p) in [
        ("isNaN", crate::value::NumPred::IsNaN),
        ("isFinite", crate::value::NumPred::IsFinite),
        ("isInteger", crate::value::NumPred::IsInteger),
        ("isSafeInteger", crate::value::NumPred::IsSafeInteger),
    ] {
        let m = r.mk_fn(function_proto, name, 1.0, Builtin::NumberPredicate(p));
        r.put(number_fn, name, attrs_method(Value::Obj(m)));
    }
    let boolean_fn = r.mk_fn(function_proto, "Boolean", 1.0, Builtin::BooleanFn);
    r.put(boolean_fn, "prototype", attrs_frozen(Value::Obj(boolean_proto)));
    r.put(boolean_proto, "constructor", attrs_method(Value::Obj(boolean_fn)));
    let m = r.mk_fn(function_proto, "toString", 0.0, Builtin::BooleanProtoToString);
    r.put(boolean_proto, "toString", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "valueOf", 0.0, Builtin::BooleanProtoValueOf);
    r.put(boolean_proto, "valueOf", attrs_method(Value::Obj(m)));
    let isnan_fn = r.mk_fn(function_proto, "isNaN", 1.0, Builtin::IsNaN);
    let isfinite_fn = r.mk_fn(function_proto, "isFinite", 1.0, Builtin::IsFinite);
    let print_fn = r.mk_fn(function_proto, "print", 0.0, Builtin::Print);
    r.attach_fn_prototype(print_fn, object_proto);

    // Math.
    let math = r.alloc(Object::new(ObjKind::IntrinsicOpaque, Some(object_proto)));
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
        r.put(math, name, attrs_frozen(Value::Num(v)));
    }
    for (name, len, op) in [
        ("abs", 1.0, MathOp::Abs),
        ("ceil", 1.0, MathOp::Ceil),
        ("floor", 1.0, MathOp::Floor),
        ("max", 2.0, MathOp::Max),
        ("min", 2.0, MathOp::Min),
        ("pow", 2.0, MathOp::Pow),
        ("round", 1.0, MathOp::Round),
        ("sign", 1.0, MathOp::Sign),
        ("sqrt", 1.0, MathOp::Sqrt),
        ("trunc", 1.0, MathOp::Trunc),
    ] {
        let m = r.mk_fn(function_proto, name, len, Builtin::MathFn(op));
        r.put(math, name, attrs_method(Value::Obj(m)));
    }

    // console. The trace driver REPLACES console.log/... with anonymous
    // recorder function expressions (`c[m] = mk(kind)` — no name inference
    // through a member assignment), so the observable `.name` of every
    // console method under the driver is "" — model exactly that, not the
    // engine's original names. Function EXPRESSIONS carry an own `prototype`.
    let console = r.alloc(Object::new(ObjKind::IntrinsicOpaque, Some(object_proto)));
    for name in ["log", "info", "debug", "trace"] {
        let m = r.mk_fn(function_proto, "", 0.0, Builtin::ConsoleStdout);
        r.attach_fn_prototype(m, object_proto);
        r.put(console, name, Prop::data(Value::Obj(m)));
    }
    for name in ["warn", "error"] {
        let m = r.mk_fn(function_proto, "", 0.0, Builtin::ConsoleStderr);
        r.attach_fn_prototype(m, object_proto);
        r.put(console, name, Prop::data(Value::Obj(m)));
    }

    // JSON
    let json = r.alloc(Object::new(ObjKind::IntrinsicOpaque, Some(object_proto)));
    let m = r.mk_fn(function_proto, "stringify", 3.0, Builtin::JsonStringify);
    r.put(json, "stringify", attrs_method(Value::Obj(m)));

    // Generators (27.1-27.5). %IteratorPrototype% carries Iterator-Helper
    // methods + symbol surface we do not model; those exact names refuse (via
    // ITERATOR_PROTO_DANGER) while a miss on any OTHER name (e.g.
    // hasOwnProperty) correctly falls through to Object.prototype. Projecting
    // it, or %GeneratorPrototype% / %GeneratorFunction.prototype%, refuses by
    // identity (unmodeled @@toStringTag / helper surface).
    let iterator_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    let generator_proto = r.alloc(Object::new(ObjKind::Plain, Some(iterator_proto)));
    let generator_function_proto = r.alloc(Object::new(ObjKind::Plain, Some(function_proto)));
    let generator_function =
        r.mk_fn(function_ctor, "GeneratorFunction", 1.0, Builtin::GeneratorFunctionCtor);
    r.put(
        generator_function,
        "prototype",
        attrs_frozen(Value::Obj(generator_function_proto)),
    );
    r.put(
        generator_function_proto,
        "constructor",
        Prop::with_attrs(Value::Obj(generator_function), false, false, true),
    );
    r.put(
        generator_function_proto,
        "prototype",
        Prop::with_attrs(Value::Obj(generator_proto), false, false, true),
    );
    r.put(
        generator_proto,
        "constructor",
        Prop::with_attrs(Value::Obj(generator_function_proto), false, false, true),
    );
    for (name, b) in [
        ("next", Builtin::GeneratorNext),
        ("return", Builtin::GeneratorReturn),
        ("throw", Builtin::GeneratorThrow),
    ] {
        let m = r.mk_fn(function_proto, name, 1.0, b);
        r.put(generator_proto, name, attrs_method(Value::Obj(m)));
    }

    // %AsyncFunction% (27.7) — the dynamic async-function constructor and its
    // prototype. Not a global: reachable only via
    // `(async function(){}).constructor`. Its [[Prototype]] chain gives an
    // async function object cls "Function" through %Function.prototype% while
    // keeping `getPrototypeOf(asyncFn) === %AsyncFunction.prototype%` exact.
    // Its @@toStringTag "AsyncFunction" is declared-owned (sym_real_owns) so a
    // read refuses rather than answer a wrong tag; calling %AsyncFunction%
    // (dynamic source construction) is out of slice.
    let async_function_proto = r.alloc(Object::new(ObjKind::Plain, Some(function_proto)));
    let async_function = r.mk_fn(function_ctor, "AsyncFunction", 1.0, Builtin::AsyncFunctionCtor);
    r.put(async_function, "prototype", attrs_frozen(Value::Obj(async_function_proto)));
    r.put(
        async_function_proto,
        "constructor",
        Prop::with_attrs(Value::Obj(async_function), false, false, true),
    );

    // %ArrayIteratorPrototype% (23.1.5.2): proto %IteratorPrototype%, own
    // `next` + `@@toStringTag` "Array Iterator" ({writable:false,
    // enumerable:false, configurable:true}, verified on Node 24). Projecting
    // the prototype still refuses by identity (own-key ORDER is engine
    // latitude); its instances have no own properties, so they project as
    // ordinary "Object" objects.
    let array_iterator_proto = r.alloc(Object::new(ObjKind::Plain, Some(iterator_proto)));
    let m = r.mk_fn(function_proto, "next", 0.0, Builtin::ArrayIteratorNext);
    r.put(array_iterator_proto, "next", attrs_method(Value::Obj(m)));

    // %StringIteratorPrototype% (22.1.5.2): proto %IteratorPrototype%, own
    // `next` + `@@toStringTag` "String Iterator".
    let string_iterator_proto = r.alloc(Object::new(ObjKind::Plain, Some(iterator_proto)));
    let m = r.mk_fn(function_proto, "next", 0.0, Builtin::StringIteratorNext);
    r.put(string_iterator_proto, "next", attrs_method(Value::Obj(m)));

    // ---- Symbols (20.4) --------------------------------------------------
    // Allocate the 13 well-known symbols first (their ids are stable low
    // indices; the projection reads their `well_known` name).
    let mut symbols: Vec<SymData> = Vec::new();
    let mut wk_syms: Vec<SymId> = Vec::with_capacity(WK_NAMES.len());
    for proj in WK_PROJ {
        let id = SymId(u32::try_from(symbols.len()).expect("bounded"));
        symbols.push(SymData {
            desc: Some(units_from_str(proj)),
            well_known: Some(proj),
            registry_key: None,
        });
        wk_syms.push(id);
    }

    // %Symbol.prototype%: ordinary object off Object.prototype.
    let symbol_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    let m = r.mk_fn(function_proto, "toString", 0.0, Builtin::SymbolProtoToString);
    r.put(symbol_proto, "toString", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "valueOf", 0.0, Builtin::SymbolProtoValueOf);
    r.put(symbol_proto, "valueOf", attrs_method(Value::Obj(m)));
    // `description` is an accessor (get only).
    let dget = r.mk_fn(function_proto, "get description", 0.0, Builtin::SymbolProtoDescriptionGet);
    r.put(
        symbol_proto,
        "description",
        Prop::accessor(Some(dget), None, false, true),
    );
    // Symbol.prototype[@@toPrimitive] — name "[Symbol.toPrimitive]",
    // {writable:false, enumerable:false, configurable:true}.
    let tp = r.mk_fn(function_proto, "[Symbol.toPrimitive]", 1.0, Builtin::SymbolProtoToPrimitive);
    r.put_sym(
        symbol_proto,
        wk_syms[WK_TO_PRIMITIVE],
        Prop::with_attrs(Value::Obj(tp), false, false, true),
    );
    // Symbol.prototype[@@toStringTag] = "Symbol" (non-writable, configurable).
    r.put_sym(
        symbol_proto,
        wk_syms[WK_TO_STRING_TAG],
        Prop::with_attrs(Value::str_from("Symbol"), false, false, true),
    );

    // The %JSON% (25.5) and %Math% (21.3.1) namespace objects each carry a
    // @@toStringTag data property = "JSON" / "Math" ({writable:false,
    // enumerable:false, configurable:true}). wk_syms exist by now.
    r.put_sym(
        json,
        wk_syms[WK_TO_STRING_TAG],
        Prop::with_attrs(Value::str_from("JSON"), false, false, true),
    );
    r.put_sym(
        math,
        wk_syms[WK_TO_STRING_TAG],
        Prop::with_attrs(Value::str_from("Math"), false, false, true),
    );

    // The %Symbol% function.
    let symbol_ctor = r.mk_fn(function_proto, "Symbol", 0.0, Builtin::SymbolFn);
    r.put(symbol_ctor, "prototype", attrs_frozen(Value::Obj(symbol_proto)));
    r.put(symbol_proto, "constructor", attrs_method(Value::Obj(symbol_ctor)));
    for (i, name) in WK_NAMES.iter().enumerate() {
        r.put(symbol_ctor, name, attrs_frozen(Value::Sym(wk_syms[i])));
    }
    let m = r.mk_fn(function_proto, "for", 1.0, Builtin::SymbolFor);
    r.put(symbol_ctor, "for", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "keyFor", 1.0, Builtin::SymbolKeyFor);
    r.put(symbol_ctor, "keyFor", attrs_method(Value::Obj(m)));

    // %BigInt.prototype% (20.2.3) + the %BigInt% function (20.2.1).
    let bigint_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    let m = r.mk_fn(function_proto, "toString", 0.0, Builtin::BigIntProtoToString);
    r.put(bigint_proto, "toString", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "valueOf", 0.0, Builtin::BigIntProtoValueOf);
    r.put(bigint_proto, "valueOf", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "toLocaleString", 0.0, Builtin::BigIntProtoToLocaleString);
    r.put(bigint_proto, "toLocaleString", attrs_method(Value::Obj(m)));
    // BigInt.prototype[@@toStringTag] = "BigInt" ({writable:false,
    // enumerable:false, configurable:true}, per 20.2.3.5).
    r.put_sym(
        bigint_proto,
        wk_syms[WK_TO_STRING_TAG],
        Prop::with_attrs(Value::str_from("BigInt"), false, false, true),
    );
    let bigint_ctor = r.mk_fn(function_proto, "BigInt", 1.0, Builtin::BigIntFn);
    r.put(bigint_ctor, "prototype", attrs_frozen(Value::Obj(bigint_proto)));
    r.put(bigint_proto, "constructor", attrs_method(Value::Obj(bigint_ctor)));
    let m = r.mk_fn(function_proto, "asIntN", 2.0, Builtin::BigIntAsIntN);
    r.put(bigint_ctor, "asIntN", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "asUintN", 2.0, Builtin::BigIntAsUintN);
    r.put(bigint_ctor, "asUintN", attrs_method(Value::Obj(m)));

    // %Function.prototype%[@@hasInstance] (the default OrdinaryHasInstance).
    let function_proto_has_instance = r.mk_fn(
        function_proto,
        "[Symbol.hasInstance]",
        1.0,
        Builtin::FunctionProtoHasInstance,
    );
    r.it[function_proto_has_instance.0 as usize].extensible = true;
    r.put_sym(
        function_proto,
        wk_syms[WK_HAS_INSTANCE],
        Prop::with_attrs(Value::Obj(function_proto_has_instance), false, false, false),
    );
    // %Array.prototype%[@@iterator] = %Array.prototype.values%.
    let values_fn = match &r.it[array_proto.0 as usize].props.get(&units_from_str("values")).expect("values").val {
        PropVal::Data { value: Value::Obj(v), .. } => *v,
        _ => unreachable!("array values is a data method"),
    };
    r.put_sym(
        array_proto,
        wk_syms[WK_ITERATOR],
        attrs_method(Value::Obj(values_fn)),
    );

    // %IteratorPrototype%[@@iterator] (27.1.2.1): the shared self-return method
    // (name "[Symbol.iterator]", length 0, {writable, non-enumerable,
    // configurable}). Every built-in iterator inherits it, so the general
    // GetIterator protocol on an iterator returns the iterator itself. (Its
    // sibling @@toStringTag is an Iterator-Helpers accessor — S0-EXCLUDED, kept
    // declared-owned/unmodeled so a read refuses rather than guess.)
    let iter_self = r.mk_fn(function_proto, "[Symbol.iterator]", 0.0, Builtin::IteratorProtoIterator);
    r.put_sym(
        iterator_proto,
        wk_syms[WK_ITERATOR],
        attrs_method(Value::Obj(iter_self)),
    );
    // %ArrayIteratorPrototype%[@@toStringTag] = "Array Iterator".
    r.put_sym(
        array_iterator_proto,
        wk_syms[WK_TO_STRING_TAG],
        Prop::with_attrs(Value::str_from("Array Iterator"), false, false, true),
    );
    // %StringIteratorPrototype%[@@toStringTag] = "String Iterator".
    r.put_sym(
        string_iterator_proto,
        wk_syms[WK_TO_STRING_TAG],
        Prop::with_attrs(Value::str_from("String Iterator"), false, false, true),
    );
    // String.prototype[@@iterator] (22.1.3.35): a String Iterator by code point.
    let str_iter = r.mk_fn(function_proto, "[Symbol.iterator]", 0.0, Builtin::StringProtoIterator);
    r.put_sym(
        string_proto,
        wk_syms[WK_ITERATOR],
        attrs_method(Value::Obj(str_iter)),
    );

    // ---- Date (21.4) -----------------------------------------------------
    let date_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    for (name, len, op) in [
        ("valueOf", 0.0, DateOp::GetTime),
        ("getTime", 0.0, DateOp::GetTime),
        ("getFullYear", 0.0, DateOp::GetFullYear),
        ("getUTCFullYear", 0.0, DateOp::GetFullYear),
        ("getMonth", 0.0, DateOp::GetMonth),
        ("getUTCMonth", 0.0, DateOp::GetMonth),
        ("getDate", 0.0, DateOp::GetDate),
        ("getUTCDate", 0.0, DateOp::GetDate),
        ("getDay", 0.0, DateOp::GetDay),
        ("getUTCDay", 0.0, DateOp::GetDay),
        ("getHours", 0.0, DateOp::GetHours),
        ("getUTCHours", 0.0, DateOp::GetHours),
        ("getMinutes", 0.0, DateOp::GetMinutes),
        ("getUTCMinutes", 0.0, DateOp::GetMinutes),
        ("getSeconds", 0.0, DateOp::GetSeconds),
        ("getUTCSeconds", 0.0, DateOp::GetSeconds),
        ("getMilliseconds", 0.0, DateOp::GetMilliseconds),
        ("getUTCMilliseconds", 0.0, DateOp::GetMilliseconds),
        ("getTimezoneOffset", 0.0, DateOp::GetTimezoneOffset),
        ("setTime", 1.0, DateOp::SetTime),
        ("setFullYear", 3.0, DateOp::SetFullYear),
        ("setUTCFullYear", 3.0, DateOp::SetFullYear),
        ("setMonth", 2.0, DateOp::SetMonth),
        ("setUTCMonth", 2.0, DateOp::SetMonth),
        ("setDate", 1.0, DateOp::SetDate),
        ("setUTCDate", 1.0, DateOp::SetDate),
        ("setHours", 4.0, DateOp::SetHours),
        ("setUTCHours", 4.0, DateOp::SetHours),
        ("setMinutes", 3.0, DateOp::SetMinutes),
        ("setUTCMinutes", 3.0, DateOp::SetMinutes),
        ("setSeconds", 2.0, DateOp::SetSeconds),
        ("setUTCSeconds", 2.0, DateOp::SetSeconds),
        ("setMilliseconds", 1.0, DateOp::SetMilliseconds),
        ("setUTCMilliseconds", 1.0, DateOp::SetMilliseconds),
        ("toISOString", 0.0, DateOp::ToIsoString),
        ("toJSON", 1.0, DateOp::ToJson),
    ] {
        let m = r.mk_fn(function_proto, name, len, Builtin::DateMethod(op));
        r.put(date_proto, name, attrs_method(Value::Obj(m)));
    }
    let tp = r.mk_fn(function_proto, "[Symbol.toPrimitive]", 1.0, Builtin::DateMethod(DateOp::ToPrimitive));
    r.put_sym(
        date_proto,
        wk_syms[WK_TO_PRIMITIVE],
        Prop::with_attrs(Value::Obj(tp), false, false, true),
    );
    // The driver firewall REPLACES the global Date with a wrapper
    // `function Date(...args)` whose observable static surface differs from a
    // native Date (length 0; `prototype` writable; now/parse/UTC installed by
    // plain assignment, hence enumerable data properties). The driver is the
    // oracle head, so the reference semantics mirror the wrapper exactly (own
    // key order [length, name, prototype, now, parse, UTC]).
    let date_ctor = r.mk_fn(function_proto, "Date", 0.0, Builtin::DateCtor);
    r.put(
        date_ctor,
        "prototype",
        Prop::with_attrs(Value::Obj(date_proto), true, false, false),
    );
    r.put(date_proto, "constructor", attrs_method(Value::Obj(date_ctor)));
    let m = r.mk_fn(function_proto, "now", 0.0, Builtin::DateNow);
    r.put(date_ctor, "now", Prop::data(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "parse", 1.0, Builtin::DateParse);
    r.put(date_ctor, "parse", Prop::data(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "UTC", 7.0, Builtin::DateUtc);
    r.put(date_ctor, "UTC", Prop::data(Value::Obj(m)));

    // ---- RegExp (22.2) ---------------------------------------------------
    use crate::value::{RegExpFlag, RegExpProtoOp};
    let regexp_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    for (name, len, op) in [
        ("exec", 1.0, RegExpProtoOp::Exec),
        ("test", 1.0, RegExpProtoOp::Test),
        ("toString", 0.0, RegExpProtoOp::ToString),
    ] {
        let m = r.mk_fn(function_proto, name, len, Builtin::RegExpProto(op));
        r.put(regexp_proto, name, attrs_method(Value::Obj(m)));
    }
    // Flag accessors: each a getter (`get X`) — {enumerable:false,
    // configurable:true}.
    for (name, flag) in [
        ("hasIndices", RegExpFlag::HasIndices),
        ("global", RegExpFlag::Global),
        ("ignoreCase", RegExpFlag::IgnoreCase),
        ("multiline", RegExpFlag::Multiline),
        ("dotAll", RegExpFlag::DotAll),
        ("source", RegExpFlag::Source),
        ("flags", RegExpFlag::Flags),
        ("sticky", RegExpFlag::Sticky),
        ("unicode", RegExpFlag::Unicode),
        ("unicodeSets", RegExpFlag::UnicodeSets),
    ] {
        let getter = r.mk_fn(
            function_proto,
            &format!("get {name}"),
            0.0,
            Builtin::RegExpFlagGet(flag),
        );
        r.put(
            regexp_proto,
            name,
            Prop::accessor(Some(getter), None, false, true),
        );
    }
    // @@-protocols on %RegExp.prototype%.
    for (sym_idx, sym_name, len, op) in [
        (WK_MATCH, "[Symbol.match]", 1.0, RegExpProtoOp::Match),
        (WK_MATCH_ALL, "[Symbol.matchAll]", 1.0, RegExpProtoOp::MatchAll),
        (WK_REPLACE, "[Symbol.replace]", 2.0, RegExpProtoOp::Replace),
        (WK_SEARCH, "[Symbol.search]", 1.0, RegExpProtoOp::Search),
        (WK_SPLIT, "[Symbol.split]", 2.0, RegExpProtoOp::Split),
    ] {
        let m = r.mk_fn(function_proto, sym_name, len, Builtin::RegExpProto(op));
        r.put_sym(regexp_proto, wk_syms[sym_idx], attrs_method(Value::Obj(m)));
    }
    // The %RegExp% constructor.
    let regexp_ctor = r.mk_fn(function_proto, "RegExp", 2.0, Builtin::RegExpCtor);
    r.put(regexp_ctor, "prototype", attrs_frozen(Value::Obj(regexp_proto)));
    r.put(regexp_proto, "constructor", attrs_method(Value::Obj(regexp_ctor)));
    // get RegExp[@@species] — returns the receiver.
    let species_get = r.mk_fn(
        function_proto,
        "get [Symbol.species]",
        0.0,
        Builtin::RegExpSpeciesGet,
    );
    r.put_sym(
        regexp_ctor,
        wk_syms[WK_SPECIES],
        Prop::accessor(Some(species_get), None, false, true),
    );
    // %RegExpStringIteratorPrototype% (22.2.9.2): proto %IteratorPrototype%,
    // own `next`, @@toStringTag "RegExp String Iterator".
    let regexp_string_iterator_proto = r.alloc(Object::new(ObjKind::Plain, Some(iterator_proto)));
    let m = r.mk_fn(function_proto, "next", 0.0, Builtin::RegExpStringIteratorNext);
    r.put(regexp_string_iterator_proto, "next", attrs_method(Value::Obj(m)));
    r.put_sym(
        regexp_string_iterator_proto,
        wk_syms[WK_TO_STRING_TAG],
        Prop::with_attrs(Value::str_from("RegExp String Iterator"), false, false, true),
    );

    // ---- ArrayBuffer / DataView / TypedArray (23.2, 25.1, 25.3) ----------
    use crate::value::ElementType;
    let getter = |r: &mut Realm<'_>, proto: ObjId, name: &str, b: Builtin| {
        let g = r.mk_fn(function_proto, &format!("get {name}"), 0.0, b);
        r.put(proto, name, Prop::accessor(Some(g), None, false, true));
    };

    // %ArrayBuffer% (25.1) and its prototype.
    let arraybuffer_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    let arraybuffer_ctor = r.mk_fn(function_proto, "ArrayBuffer", 1.0, Builtin::ArrayBufferCtor);
    r.put(arraybuffer_ctor, "prototype", attrs_frozen(Value::Obj(arraybuffer_proto)));
    r.put(arraybuffer_proto, "constructor", attrs_method(Value::Obj(arraybuffer_ctor)));
    let m = r.mk_fn(function_proto, "isView", 1.0, Builtin::ArrayBufferIsView);
    r.put(arraybuffer_ctor, "isView", attrs_method(Value::Obj(m)));
    let sg = r.mk_fn(function_proto, "get [Symbol.species]", 0.0, Builtin::SpeciesGetReceiver);
    r.put_sym(arraybuffer_ctor, wk_syms[WK_SPECIES], Prop::accessor(Some(sg), None, false, true));
    getter(&mut r, arraybuffer_proto, "byteLength", Builtin::ArrayBufferByteLengthGet);
    getter(&mut r, arraybuffer_proto, "maxByteLength", Builtin::ArrayBufferMaxByteLengthGet);
    getter(&mut r, arraybuffer_proto, "resizable", Builtin::ArrayBufferResizableGet);
    getter(&mut r, arraybuffer_proto, "detached", Builtin::ArrayBufferDetachedGet);
    for (name, len, b) in [
        ("slice", 2.0, Builtin::ArrayBufferSlice),
        ("resize", 1.0, Builtin::ArrayBufferResize),
        ("transfer", 0.0, Builtin::ArrayBufferTransfer),
        ("transferToFixedLength", 0.0, Builtin::ArrayBufferTransferToFixed),
    ] {
        let mm = r.mk_fn(function_proto, name, len, b);
        r.put(arraybuffer_proto, name, attrs_method(Value::Obj(mm)));
    }
    r.put_sym(
        arraybuffer_proto,
        wk_syms[WK_TO_STRING_TAG],
        Prop::with_attrs(Value::str_from("ArrayBuffer"), false, false, true),
    );

    // %DataView% (25.3) and its prototype.
    let dataview_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    let dataview_ctor = r.mk_fn(function_proto, "DataView", 1.0, Builtin::DataViewCtor);
    r.put(dataview_ctor, "prototype", attrs_frozen(Value::Obj(dataview_proto)));
    r.put(dataview_proto, "constructor", attrs_method(Value::Obj(dataview_ctor)));
    getter(&mut r, dataview_proto, "buffer", Builtin::DataViewBufferGet);
    getter(&mut r, dataview_proto, "byteLength", Builtin::DataViewByteLengthGet);
    getter(&mut r, dataview_proto, "byteOffset", Builtin::DataViewByteOffsetGet);
    for (name, elem) in [
        ("Int8", ElementType::Int8),
        ("Uint8", ElementType::Uint8),
        ("Int16", ElementType::Int16),
        ("Uint16", ElementType::Uint16),
        ("Int32", ElementType::Int32),
        ("Uint32", ElementType::Uint32),
        ("Float32", ElementType::Float32),
        ("Float64", ElementType::Float64),
        ("BigInt64", ElementType::BigInt64),
        ("BigUint64", ElementType::BigUint64),
        ("Float16", ElementType::Float16),
    ] {
        let g = r.mk_fn(function_proto, &format!("get{name}"), 1.0, Builtin::DataViewGet(elem));
        r.put(dataview_proto, &format!("get{name}"), attrs_method(Value::Obj(g)));
        let s = r.mk_fn(function_proto, &format!("set{name}"), 2.0, Builtin::DataViewSet(elem));
        r.put(dataview_proto, &format!("set{name}"), attrs_method(Value::Obj(s)));
    }
    r.put_sym(
        dataview_proto,
        wk_syms[WK_TO_STRING_TAG],
        Prop::with_attrs(Value::str_from("DataView"), false, false, true),
    );

    // %TypedArray% (23.2.1) abstract constructor + %TypedArray.prototype%.
    let typed_array_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    let typed_array_ctor =
        r.mk_fn(function_proto, "TypedArray", 0.0, Builtin::TypedArrayAbstractCtor);
    r.put(typed_array_ctor, "prototype", attrs_frozen(Value::Obj(typed_array_proto)));
    r.put(typed_array_proto, "constructor", attrs_method(Value::Obj(typed_array_ctor)));
    let m = r.mk_fn(function_proto, "from", 1.0, Builtin::TypedArrayFrom);
    r.put(typed_array_ctor, "from", attrs_method(Value::Obj(m)));
    let m = r.mk_fn(function_proto, "of", 0.0, Builtin::TypedArrayOf);
    r.put(typed_array_ctor, "of", attrs_method(Value::Obj(m)));
    let sg = r.mk_fn(function_proto, "get [Symbol.species]", 0.0, Builtin::SpeciesGetReceiver);
    r.put_sym(typed_array_ctor, wk_syms[WK_SPECIES], Prop::accessor(Some(sg), None, false, true));
    getter(&mut r, typed_array_proto, "buffer", Builtin::TypedArrayBufferGet);
    getter(&mut r, typed_array_proto, "byteLength", Builtin::TypedArrayByteLengthGet);
    getter(&mut r, typed_array_proto, "byteOffset", Builtin::TypedArrayByteOffsetGet);
    getter(&mut r, typed_array_proto, "length", Builtin::TypedArrayLengthGet);
    let tg = r.mk_fn(function_proto, "get [Symbol.toStringTag]", 0.0, Builtin::TypedArrayToStringTagGet);
    r.put_sym(typed_array_proto, wk_syms[WK_TO_STRING_TAG], Prop::accessor(Some(tg), None, false, true));
    use crate::value::TAMethod;
    let mut ta_values_fn = None;
    for (name, len, tm) in [
        ("at", 1.0, TAMethod::At),
        ("copyWithin", 2.0, TAMethod::CopyWithin),
        ("entries", 0.0, TAMethod::Entries),
        ("every", 1.0, TAMethod::Every),
        ("fill", 1.0, TAMethod::Fill),
        ("filter", 1.0, TAMethod::Filter),
        ("find", 1.0, TAMethod::Find),
        ("findIndex", 1.0, TAMethod::FindIndex),
        ("findLast", 1.0, TAMethod::FindLast),
        ("findLastIndex", 1.0, TAMethod::FindLastIndex),
        ("forEach", 1.0, TAMethod::ForEach),
        ("includes", 1.0, TAMethod::Includes),
        ("indexOf", 1.0, TAMethod::IndexOf),
        ("join", 1.0, TAMethod::Join),
        ("keys", 0.0, TAMethod::Keys),
        ("lastIndexOf", 1.0, TAMethod::LastIndexOf),
        ("map", 1.0, TAMethod::Map),
        ("reduce", 1.0, TAMethod::Reduce),
        ("reduceRight", 1.0, TAMethod::ReduceRight),
        ("reverse", 0.0, TAMethod::Reverse),
        ("set", 1.0, TAMethod::Set),
        ("slice", 2.0, TAMethod::Slice),
        ("some", 1.0, TAMethod::Some),
        ("sort", 1.0, TAMethod::Sort),
        ("subarray", 2.0, TAMethod::Subarray),
        ("toLocaleString", 0.0, TAMethod::ToLocaleString),
        ("toReversed", 0.0, TAMethod::ToReversed),
        ("toSorted", 1.0, TAMethod::ToSorted),
        ("toString", 0.0, TAMethod::ToString),
        ("values", 0.0, TAMethod::Values),
        ("with", 2.0, TAMethod::With),
    ] {
        let mm = r.mk_fn(function_proto, name, len, Builtin::TypedArrayMethod(tm));
        r.put(typed_array_proto, name, attrs_method(Value::Obj(mm)));
        if tm == TAMethod::Values {
            ta_values_fn = Some(mm);
        }
    }
    // %TypedArray.prototype%[@@iterator] == %TypedArray.prototype.values%.
    r.put_sym(
        typed_array_proto,
        wk_syms[WK_ITERATOR],
        attrs_method(Value::Obj(ta_values_fn.expect("values registered"))),
    );

    // Concrete Number typed-array constructors + prototypes.
    let mut typed_arrays: Vec<(ElementType, ObjId, ObjId)> = Vec::new();
    for elem in [
        ElementType::Int8,
        ElementType::Uint8,
        ElementType::Uint8Clamped,
        ElementType::Int16,
        ElementType::Uint16,
        ElementType::Int32,
        ElementType::Uint32,
        ElementType::Float16,
        ElementType::Float32,
        ElementType::Float64,
        ElementType::BigInt64,
        ElementType::BigUint64,
    ] {
        let proto = r.alloc(Object::new(ObjKind::Plain, Some(typed_array_proto)));
        // The concrete ctor's [[Prototype]] is %TypedArray% (so
        // Object.getPrototypeOf(Int8Array) === %TypedArray%).
        let ctor = r.mk_fn(typed_array_ctor, elem.name(), 3.0, Builtin::TypedArrayCtor(elem));
        r.put(ctor, "prototype", attrs_frozen(Value::Obj(proto)));
        r.put(proto, "constructor", attrs_method(Value::Obj(ctor)));
        #[allow(clippy::cast_precision_loss)]
        let bpe = Prop::with_attrs(Value::Num(elem.bytes() as f64), false, false, false);
        r.put(ctor, "BYTES_PER_ELEMENT", bpe.clone());
        r.put(proto, "BYTES_PER_ELEMENT", bpe);
        typed_arrays.push((elem, ctor, proto));
    }

    // ---- Promise (27.2) --------------------------------------------------
    let promise_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    let promise_ctor = r.mk_fn(function_proto, "Promise", 1.0, Builtin::PromiseCtor);
    r.put(promise_ctor, "prototype", attrs_frozen(Value::Obj(promise_proto)));
    r.put(promise_proto, "constructor", attrs_method(Value::Obj(promise_ctor)));
    for (name, len, b) in [
        ("resolve", 1.0, Builtin::PromiseResolveStatic),
        ("reject", 1.0, Builtin::PromiseRejectStatic),
        ("all", 1.0, Builtin::PromiseAll),
        ("allSettled", 1.0, Builtin::PromiseAllSettled),
        ("race", 1.0, Builtin::PromiseRace),
        ("any", 1.0, Builtin::PromiseAny),
    ] {
        let m = r.mk_fn(function_proto, name, len, b);
        r.put(promise_ctor, name, attrs_method(Value::Obj(m)));
    }
    // get Promise[@@species] (27.2.4.10): returns the receiver.
    let sg = r.mk_fn(function_proto, "get [Symbol.species]", 0.0, Builtin::PromiseSpeciesGet);
    r.put_sym(promise_ctor, wk_syms[WK_SPECIES], Prop::accessor(Some(sg), None, false, true));
    for (name, len, b) in [
        ("then", 2.0, Builtin::PromiseProtoThen),
        ("catch", 1.0, Builtin::PromiseProtoCatch),
        ("finally", 1.0, Builtin::PromiseProtoFinally),
    ] {
        let m = r.mk_fn(function_proto, name, len, b);
        r.put(promise_proto, name, attrs_method(Value::Obj(m)));
    }
    // Promise.prototype[@@toStringTag] = "Promise" (non-writable, configurable).
    r.put_sym(
        promise_proto,
        wk_syms[WK_TO_STRING_TAG],
        Prop::with_attrs(Value::str_from("Promise"), false, false, true),
    );

    // ---- Map / Set / WeakMap / WeakSet (24) ------------------------------
    let string_tag = |s: &str| Prop::with_attrs(Value::str_from(s), false, false, true);

    // Map (24.1).
    let map_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    let map_ctor = r.mk_fn(function_proto, "Map", 0.0, Builtin::MapCtor);
    r.put(map_ctor, "prototype", attrs_frozen(Value::Obj(map_proto)));
    r.put(map_proto, "constructor", attrs_method(Value::Obj(map_ctor)));
    let group_by = r.mk_fn(function_proto, "groupBy", 2.0, Builtin::MapGroupBy);
    r.put(map_ctor, "groupBy", attrs_method(Value::Obj(group_by)));
    let sg = r.mk_fn(function_proto, "get [Symbol.species]", 0.0, Builtin::SpeciesGetReceiver);
    r.put_sym(map_ctor, wk_syms[WK_SPECIES], Prop::accessor(Some(sg), None, false, true));
    for (name, len, b) in [
        ("get", 1.0, Builtin::MapProtoGet),
        ("set", 2.0, Builtin::MapProtoSet),
        ("has", 1.0, Builtin::MapProtoHas),
        ("delete", 1.0, Builtin::MapProtoDelete),
        ("clear", 0.0, Builtin::MapProtoClear),
        ("forEach", 1.0, Builtin::MapProtoForEach),
        ("keys", 0.0, Builtin::MapProtoKeys),
        ("values", 0.0, Builtin::MapProtoValues),
    ] {
        let m = r.mk_fn(function_proto, name, len, b);
        r.put(map_proto, name, attrs_method(Value::Obj(m)));
    }
    // `entries` is shared with @@iterator (Map.prototype[@@iterator] === entries).
    let map_entries = r.mk_fn(function_proto, "entries", 0.0, Builtin::MapProtoEntries);
    r.put(map_proto, "entries", attrs_method(Value::Obj(map_entries)));
    r.put_sym(map_proto, wk_syms[WK_ITERATOR], attrs_method(Value::Obj(map_entries)));
    let map_size_get = r.mk_fn(function_proto, "get size", 0.0, Builtin::MapSizeGet);
    r.put(map_proto, "size", Prop::accessor(Some(map_size_get), None, false, true));
    r.put_sym(map_proto, wk_syms[WK_TO_STRING_TAG], string_tag("Map"));

    // Set (24.2).
    let set_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    let set_ctor = r.mk_fn(function_proto, "Set", 0.0, Builtin::SetCtor);
    r.put(set_ctor, "prototype", attrs_frozen(Value::Obj(set_proto)));
    r.put(set_proto, "constructor", attrs_method(Value::Obj(set_ctor)));
    let sg = r.mk_fn(function_proto, "get [Symbol.species]", 0.0, Builtin::SpeciesGetReceiver);
    r.put_sym(set_ctor, wk_syms[WK_SPECIES], Prop::accessor(Some(sg), None, false, true));
    for (name, len, b) in [
        ("has", 1.0, Builtin::SetProtoHas),
        ("add", 1.0, Builtin::SetProtoAdd),
        ("delete", 1.0, Builtin::SetProtoDelete),
        ("clear", 0.0, Builtin::SetProtoClear),
        ("forEach", 1.0, Builtin::SetProtoForEach),
        ("entries", 0.0, Builtin::SetProtoEntries),
    ] {
        let m = r.mk_fn(function_proto, name, len, b);
        r.put(set_proto, name, attrs_method(Value::Obj(m)));
    }
    // The Set-methods proposal combinators (registered; calling refuses).
    for name in [
        "difference",
        "intersection",
        "isSubsetOf",
        "isSupersetOf",
        "isDisjointFrom",
        "symmetricDifference",
        "union",
    ] {
        let m = r.mk_fn(function_proto, name, 1.0, Builtin::SetProtoCombinator);
        r.put(set_proto, name, attrs_method(Value::Obj(m)));
    }
    // `values` is shared with `keys` and @@iterator (all the same function).
    let set_values = r.mk_fn(function_proto, "values", 0.0, Builtin::SetProtoValues);
    r.put(set_proto, "values", attrs_method(Value::Obj(set_values)));
    r.put(set_proto, "keys", attrs_method(Value::Obj(set_values)));
    r.put_sym(set_proto, wk_syms[WK_ITERATOR], attrs_method(Value::Obj(set_values)));
    let set_size_get = r.mk_fn(function_proto, "get size", 0.0, Builtin::SetSizeGet);
    r.put(set_proto, "size", Prop::accessor(Some(set_size_get), None, false, true));
    r.put_sym(set_proto, wk_syms[WK_TO_STRING_TAG], string_tag("Set"));

    // WeakMap (24.3).
    let weakmap_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    let weakmap_ctor = r.mk_fn(function_proto, "WeakMap", 0.0, Builtin::WeakMapCtor);
    r.put(weakmap_ctor, "prototype", attrs_frozen(Value::Obj(weakmap_proto)));
    r.put(weakmap_proto, "constructor", attrs_method(Value::Obj(weakmap_ctor)));
    for (name, len, b) in [
        ("delete", 1.0, Builtin::WeakMapProtoDelete),
        ("get", 1.0, Builtin::WeakMapProtoGet),
        ("set", 2.0, Builtin::WeakMapProtoSet),
        ("has", 1.0, Builtin::WeakMapProtoHas),
    ] {
        let m = r.mk_fn(function_proto, name, len, b);
        r.put(weakmap_proto, name, attrs_method(Value::Obj(m)));
    }
    r.put_sym(weakmap_proto, wk_syms[WK_TO_STRING_TAG], string_tag("WeakMap"));

    // WeakSet (24.4).
    let weakset_proto = r.alloc(Object::new(ObjKind::Plain, Some(object_proto)));
    let weakset_ctor = r.mk_fn(function_proto, "WeakSet", 0.0, Builtin::WeakSetCtor);
    r.put(weakset_ctor, "prototype", attrs_frozen(Value::Obj(weakset_proto)));
    r.put(weakset_proto, "constructor", attrs_method(Value::Obj(weakset_ctor)));
    for (name, len, b) in [
        ("delete", 1.0, Builtin::WeakSetProtoDelete),
        ("has", 1.0, Builtin::WeakSetProtoHas),
        ("add", 1.0, Builtin::WeakSetProtoAdd),
    ] {
        let m = r.mk_fn(function_proto, name, len, b);
        r.put(weakset_proto, name, attrs_method(Value::Obj(m)));
    }
    r.put_sym(weakset_proto, wk_syms[WK_TO_STRING_TAG], string_tag("WeakSet"));

    // %MapIteratorPrototype% (24.1.5.2) / %SetIteratorPrototype% (24.2.5.2):
    // proto is %IteratorPrototype%; own `next` + @@toStringTag.
    let map_iterator_proto = r.alloc(Object::new(ObjKind::Plain, Some(iterator_proto)));
    let m = r.mk_fn(function_proto, "next", 0.0, Builtin::MapIteratorNext);
    r.put(map_iterator_proto, "next", attrs_method(Value::Obj(m)));
    r.put_sym(map_iterator_proto, wk_syms[WK_TO_STRING_TAG], string_tag("Map Iterator"));
    let set_iterator_proto = r.alloc(Object::new(ObjKind::Plain, Some(iterator_proto)));
    let m = r.mk_fn(function_proto, "next", 0.0, Builtin::SetIteratorNext);
    r.put(set_iterator_proto, "next", attrs_method(Value::Obj(m)));
    r.put_sym(set_iterator_proto, wk_syms[WK_TO_STRING_TAG], string_tag("Set Iterator"));

    // ---- host job surface: timers + queueMicrotask -----------------------
    let set_timeout = r.mk_fn(function_proto, "setTimeout", 2.0, Builtin::SetTimeout);
    let set_interval = r.mk_fn(function_proto, "setInterval", 2.0, Builtin::SetInterval);
    let clear_timeout = r.mk_fn(function_proto, "clearTimeout", 1.0, Builtin::ClearTimer);
    let clear_interval = r.mk_fn(function_proto, "clearInterval", 1.0, Builtin::ClearTimer);
    let set_immediate = r.mk_fn(function_proto, "setImmediate", 1.0, Builtin::SetImmediate);
    let clear_immediate = r.mk_fn(function_proto, "clearImmediate", 1.0, Builtin::ClearTimer);
    let queue_microtask = r.mk_fn(function_proto, "queueMicrotask", 1.0, Builtin::QueueMicrotask);

    // ---- Reflect (28.1): a host namespace object (like Math/JSON) -------
    // Its 13 methods are modeled (a miss refuses via opaque_hosts), and it
    // never projects — the same discipline as the other intrinsic namespaces.
    let reflect = r.alloc(Object::new(ObjKind::IntrinsicOpaque, Some(object_proto)));
    for (name, len, b) in [
        ("apply", 3.0, Builtin::ReflectApply),
        ("construct", 2.0, Builtin::ReflectConstruct),
        ("defineProperty", 3.0, Builtin::ReflectDefineProperty),
        ("deleteProperty", 2.0, Builtin::ReflectDeleteProperty),
        ("get", 2.0, Builtin::ReflectGet),
        ("getOwnPropertyDescriptor", 2.0, Builtin::ReflectGetOwnPropertyDescriptor),
        ("getPrototypeOf", 1.0, Builtin::ReflectGetPrototypeOf),
        ("has", 2.0, Builtin::ReflectHas),
        ("isExtensible", 1.0, Builtin::ReflectIsExtensible),
        ("ownKeys", 1.0, Builtin::ReflectOwnKeys),
        ("preventExtensions", 1.0, Builtin::ReflectPreventExtensions),
        ("set", 3.0, Builtin::ReflectSet),
        ("setPrototypeOf", 2.0, Builtin::ReflectSetPrototypeOf),
    ] {
        let m = r.mk_fn(function_proto, name, len, b);
        r.put(reflect, name, attrs_method(Value::Obj(m)));
    }
    // Reflect[@@toStringTag] = "Reflect" (non-writable, configurable).
    r.put_sym(
        reflect,
        wk_syms[WK_TO_STRING_TAG],
        Prop::with_attrs(Value::str_from("Reflect"), false, false, true),
    );

    // ---- Proxy (28.2): the constructor + Proxy.revocable ----------------
    // %Proxy% has NO `prototype` property and no [[Prototype]]-chain surface
    // beyond %Function.prototype%; it is `new`-only.
    let proxy_ctor = r.mk_fn(function_proto, "Proxy", 2.0, Builtin::ProxyCtor);
    let m = r.mk_fn(function_proto, "revocable", 2.0, Builtin::ProxyRevocable);
    r.put(proxy_ctor, "revocable", attrs_method(Value::Obj(m)));

    // The global object.
    let global = r.alloc(Object::new(ObjKind::IntrinsicOpaque, Some(object_proto)));
    r.put(global, "undefined", attrs_frozen(Value::Undefined));
    r.put(global, "NaN", attrs_frozen(Value::Num(f64::NAN)));
    r.put(global, "Infinity", attrs_frozen(Value::Num(f64::INFINITY)));
    r.put(global, "globalThis", attrs_method(Value::Obj(global)));
    for (name, id) in [
        ("String", string_fn),
        ("Number", number_fn),
        ("Boolean", boolean_fn),
        ("isNaN", isnan_fn),
        ("isFinite", isfinite_fn),
        ("print", print_fn),
        ("eval", eval_fn),
        ("Object", object_ctor),
        ("Function", function_ctor),
        ("Array", array_ctor),
        ("Error", error_ctor),
        ("TypeError", type_error_ctor),
        ("RangeError", range_error_ctor),
        ("ReferenceError", reference_error_ctor),
        ("SyntaxError", syntax_error_ctor),
        ("EvalError", eval_error_ctor),
        ("URIError", uri_error_ctor),
        ("Math", math),
        ("console", console),
        ("JSON", json),
        ("Symbol", symbol_ctor),
        ("BigInt", bigint_ctor),
        ("Date", date_ctor),
        ("RegExp", regexp_ctor),
        ("ArrayBuffer", arraybuffer_ctor),
        ("DataView", dataview_ctor),
        ("Promise", promise_ctor),
        ("Map", map_ctor),
        ("Set", set_ctor),
        ("WeakMap", weakmap_ctor),
        ("WeakSet", weakset_ctor),
        ("setTimeout", set_timeout),
        ("setInterval", set_interval),
        ("clearTimeout", clear_timeout),
        ("clearInterval", clear_interval),
        ("setImmediate", set_immediate),
        ("clearImmediate", clear_immediate),
        ("queueMicrotask", queue_microtask),
        ("Reflect", reflect),
        ("Proxy", proxy_ctor),
    ] {
        r.put(global, name, attrs_method(Value::Obj(id)));
    }
    // The concrete typed-array constructor globals (Int8Array..BigUint64Array).
    for (_, ctor, _) in &typed_arrays {
        let name = match &r.it[ctor.0 as usize].props.get(&units_from_str("name")).expect("name").val {
            PropVal::Data { value: Value::Str(s), .. } => units_to_lossy(s),
            _ => unreachable!("ctor name is a data string"),
        };
        r.put(global, &name, attrs_method(Value::Obj(*ctor)));
    }

    let opaque_hosts: HashSet<ObjId> = [
        object_ctor,
        error_ctor,
        type_error_ctor,
        range_error_ctor,
        reference_error_ctor,
        syntax_error_ctor,
        eval_error_ctor,
        uri_error_ctor,
        math,
        console,
        json,
        reflect,
        // Date.prototype is only partially modeled (47 real own keys; the
        // human-readable string forms carry engine-specific timezone names):
        // any miss on it refuses rather than fall through to Object.prototype.
        date_proto,
        // The RegExp constructor carries Annex-B legacy static surface
        // ($1-$9, input, lastMatch, ...) we do not model: a static miss
        // refuses rather than answer a wrong `undefined`.
        regexp_ctor,
    ]
    .into_iter()
    .collect();

    // Hosts with a fully-enumerated real static surface: misses refuse only
    // for the listed unmodeled names.
    let host_statics_danger: HashMap<ObjId, &'static [&'static str]> = [
        (boolean_fn, &[] as &'static [&'static str]),
        (number_fn, &["parseInt", "parseFloat"] as &'static [&'static str]),
        (string_fn, &["raw"] as &'static [&'static str]),
        // Array.from/of are modeled; fromAsync (async iteration) is not.
        (array_ctor, &["fromAsync"] as &'static [&'static str]),
        (function_ctor, &[] as &'static [&'static str]),
        // Symbol carries unmodeled well-known statics (dispose/asyncDispose);
        // the classic 13 + for/keyFor are modeled.
        (symbol_ctor, &["dispose", "asyncDispose", "metadata"] as &'static [&'static str]),
        // BigInt statics asIntN/asUintN (+ prototype) are fully modeled; a miss
        // is soundly absent, but whole-surface walk order is engine latitude.
        (bigint_ctor, &[] as &'static [&'static str]),
        // Date statics (now/parse/UTC) are fully modeled; a miss on any other
        // name is soundly absent, but the own-key ORDER is engine latitude.
        (date_ctor, &[] as &'static [&'static str]),
        // Binary-data constructors: statics fully modeled (a miss is soundly
        // absent), whole-surface walks refuse (own-key ORDER is engine
        // latitude). %TypedArray% carries unmodeled Iterator-Helper-adjacent
        // surface; its modeled statics are of/from/@@species.
        (arraybuffer_ctor, &[] as &'static [&'static str]),
        (dataview_ctor, &[] as &'static [&'static str]),
        (typed_array_ctor, &[] as &'static [&'static str]),
        // Promise statics resolve/reject/all/allSettled/race/any/@@species are
        // modeled; try/withResolvers (Node 24) are not, so a miss on them
        // refuses rather than answer a wrong `undefined`.
        (promise_ctor, &["try", "withResolvers"] as &'static [&'static str]),
        // Proxy's full static surface (length/name/revocable) is modeled; a
        // miss is soundly absent, but the own-key ORDER is engine latitude.
        (proxy_ctor, &[] as &'static [&'static str]),
        // Map/Set statics (groupBy/@@species) are modeled; a miss is soundly
        // absent, but the own-key ORDER is engine latitude (whole-surface walks
        // refuse). WeakMap/WeakSet carry no unmodeled statics.
        (map_ctor, &[] as &'static [&'static str]),
        (set_ctor, &[] as &'static [&'static str]),
        (weakmap_ctor, &[] as &'static [&'static str]),
        (weakset_ctor, &[] as &'static [&'static str]),
    ]
    .into_iter()
    .chain(
        typed_arrays
            .iter()
            .map(|(_, c, _)| (*c, &[] as &'static [&'static str])),
    )
    .collect();

    let intr = Intrinsics {
        object_proto,
        function_proto,
        array_proto,
        string_proto,
        number_proto,
        boolean_proto,
        array_ctor,
        error_proto,
        type_error_proto,
        range_error_proto,
        reference_error_proto,
        syntax_error_proto,
        eval_error_proto,
        uri_error_proto,
        console,
        throw_type_error,
        iterator_proto,
        generator_function,
        generator_function_proto,
        generator_proto,
        array_iterator_proto,
        string_iterator_proto,
        symbol_proto,
        bigint_proto,
        bigint_ctor,
        symbol_ctor,
        date_proto,
        date_ctor,
        regexp_proto,
        regexp_ctor,
        regexp_string_iterator_proto,
        function_proto_has_instance,
        eval_fn,
        arraybuffer_ctor,
        arraybuffer_proto,
        dataview_ctor,
        dataview_proto,
        typed_array_ctor,
        typed_array_proto,
        typed_arrays,
        promise_ctor,
        promise_proto,
        async_function,
        async_function_proto,
        map_ctor,
        map_proto,
        set_ctor,
        set_proto,
        weakmap_ctor,
        weakmap_proto,
        weakset_ctor,
        weakset_proto,
        map_iterator_proto,
        set_iterator_proto,
        wk_syms,
        opaque_hosts,
        host_statics_danger,
    };

    Interp {
        heap,
        envs: vec![EnvFrame {
            parent: None,
            bindings: HashMap::new(),
            var_boundary: false,
            deletable: HashSet::new(),
        }],
        global,
        intr,
        events: Vec::new(),
        call_depth: 0,
        loop_iters: 0,
        pending_new_target: None,
        generators: Vec::new(),
        next_priv_name: 0,
        fn_priv_env: HashMap::new(),
        symbols,
        sym_registry: HashMap::new(),
        clock_ticks: 0,
        promises: Vec::new(),
        microtasks: std::collections::VecDeque::new(),
        timers: Vec::new(),
        timer_seq: 0,
        virtual_now: 0.0,
        job_steps: 0,
    }
}

// ---------------------------------------------------------------------------
// Dispatch
// ---------------------------------------------------------------------------

impl Interp {
    /// CreateDynamicFunction for the `Function` constructor (20.2.1.1),
    /// normal (non-generator, non-async) variant. The final argument is the
    /// function body; the earlier arguments are the comma-joined parameter
    /// text. Each is ToString-coerced, assembled into the exact
    /// `function anonymous(P\n) {\nBODY\n}` source a conforming engine builds,
    /// parsed, and closed over the global environment. A parse-time
    /// SyntaxError throws; an out-of-slice body refuses.
    fn function_constructor(&mut self, args: &[Value]) -> ERes {
        let n = args.len();
        // ToString each parameter arg (all but the last), then the body.
        let mut param_parts: Vec<Units> = Vec::new();
        for a in args.iter().take(n.saturating_sub(1)) {
            param_parts.push(self.to_string_units(a)?);
        }
        let body_units = if n == 0 {
            Vec::new()
        } else {
            self.to_string_units(&args[n - 1])?
        };
        // Join parameter texts with U+002C, decode each fragment strictly
        // (a lone surrogate in assembled source is out of slice).
        let decode = |u: &Units| -> Result<String, Abrupt> {
            String::from_utf16(u).map_err(|_| {
                Abrupt::Fatal(
                    "Function() source contains a lone surrogate (out of slice)".to_string(),
                )
            })
        };
        let mut params = String::new();
        for (i, p) in param_parts.iter().enumerate() {
            if i > 0 {
                params.push(',');
            }
            params.push_str(&decode(p)?);
        }
        let body = decode(&body_units)?;
        // Exact assembly (20.2.1.1.1 step 30): the newline after the parameter
        // list and before the body defeats line-comment / ASI injection.
        let src = format!("function anonymous({params}\n) {{\n{body}\n}}");
        let prog = match crate::parser::parse_program(&src) {
            Ok(p) => p,
            Err(crate::parser::ParseFail::EarlySyntaxError(_)) => {
                return Err(self.throw_native(NativeErrorKind::SyntaxError))
            }
            Err(e) => return Err(Abrupt::Fatal(format!("Function() body parse: {e}"))),
        };
        let Some(lit) = prog.funcs.first().cloned() else {
            return Err(Abrupt::Fatal(
                "Function() assembly did not yield a function (parser invariant)".to_string(),
            ));
        };
        // The dynamic function closes over the global environment.
        let fobj = self.create_function(&lit, crate::value::EnvId(0), true, None);
        Ok(Value::Obj(fobj))
    }

    /// Does %Array.prototype% carry an own accessor property at a canonical
    /// array index? Such a setter poisons the trace driver's internal
    /// array-`push` (its event recorder), so the native head refuses.
    pub(crate) fn array_proto_has_indexed_accessor(&self) -> bool {
        self.obj(self.intr.array_proto).props.iter().any(|(k, p)| {
            crate::value::array_index_of(k).is_some() && matches!(p.val, PropVal::Accessor { .. })
        })
    }

    #[allow(clippy::too_many_lines)]
    pub fn dispatch_builtin(
        &mut self,
        b: Builtin,
        _fid: ObjId,
        this: Value,
        args: Vec<Value>,
        is_new: bool,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        if is_new
            && !matches!(
                b,
                Builtin::ErrorCtor(_)
                    | Builtin::ArrayCtor
                    | Builtin::ObjectCtor
                    | Builtin::FunctionCtor
                    | Builtin::StringFn
                    | Builtin::NumberFn
                    | Builtin::BooleanFn
                    | Builtin::BigIntFn
                    | Builtin::SymbolFn
                    | Builtin::DateCtor
                    | Builtin::RegExpCtor
                    | Builtin::ArrayBufferCtor
                    | Builtin::DataViewCtor
                    | Builtin::TypedArrayCtor(_)
                    | Builtin::TypedArrayAbstractCtor
                    | Builtin::PromiseCtor
                    | Builtin::ProxyCtor
                    | Builtin::MapCtor
                    | Builtin::SetCtor
                    | Builtin::WeakMapCtor
                    | Builtin::WeakSetCtor
            )
        {
            // %GeneratorFunction%/%AsyncFunction% ARE constructors (dynamic
            // source construction) but out of slice — refuse. Every OTHER
            // builtin reaching here is a callable WITHOUT [[Construct]] (a
            // prototype method, static, accessor, or non-constructor function
            // like Symbol/BigInt handled above), so `new` on it is the spec's
            // "not a constructor" TypeError (e.g. `new [].values()`).
            if matches!(b, Builtin::GeneratorFunctionCtor | Builtin::AsyncFunctionCtor) {
                return Err(Abrupt::Fatal(format!(
                    "`new` on unmodeled builtin {b:?} (out of slice)"
                )));
            }
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        match b {
            Builtin::PromiseCtor
            | Builtin::PromiseResolveStatic
            | Builtin::PromiseRejectStatic
            | Builtin::PromiseAll
            | Builtin::PromiseAllSettled
            | Builtin::PromiseRace
            | Builtin::PromiseAny
            | Builtin::PromiseProtoThen
            | Builtin::PromiseProtoCatch
            | Builtin::PromiseProtoFinally
            | Builtin::PromiseSpeciesGet
            | Builtin::SetTimeout
            | Builtin::SetInterval
            | Builtin::ClearTimer
            | Builtin::SetImmediate
            | Builtin::QueueMicrotask => {
                return self.dispatch_promise_builtin(b, this, args, is_new);
            }
            _ => {}
        }
        if Interp::is_collection_builtin(b) {
            return self.dispatch_collection_builtin(b, this, args, is_new);
        }
        if matches!(
            b,
            Builtin::ArrayBufferCtor
                | Builtin::ArrayBufferIsView
                | Builtin::SpeciesGetReceiver
                | Builtin::ArrayBufferByteLengthGet
                | Builtin::ArrayBufferMaxByteLengthGet
                | Builtin::ArrayBufferResizableGet
                | Builtin::ArrayBufferDetachedGet
                | Builtin::ArrayBufferSlice
                | Builtin::ArrayBufferResize
                | Builtin::ArrayBufferTransfer
                | Builtin::ArrayBufferTransferToFixed
                | Builtin::DataViewCtor
                | Builtin::DataViewBufferGet
                | Builtin::DataViewByteLengthGet
                | Builtin::DataViewByteOffsetGet
                | Builtin::DataViewGet(_)
                | Builtin::DataViewSet(_)
                | Builtin::TypedArrayAbstractCtor
                | Builtin::TypedArrayCtor(_)
                | Builtin::TypedArrayFrom
                | Builtin::TypedArrayOf
                | Builtin::TypedArrayBufferGet
                | Builtin::TypedArrayByteLengthGet
                | Builtin::TypedArrayByteOffsetGet
                | Builtin::TypedArrayLengthGet
                | Builtin::TypedArrayToStringTagGet
                | Builtin::TypedArrayMethod(_)
        ) {
            return self.dispatch_binary_builtin(b, this, &args, is_new);
        }
        match b {
            Builtin::RegExpCtor => return self.regexp_ctor(&args, is_new),
            Builtin::RegExpProto(op) => return self.dispatch_regexp_proto(op, this, &args),
            Builtin::RegExpFlagGet(flag) => return self.regexp_flag_get(flag, &this),
            // get RegExp[@@species] (22.2.5.2): returns the receiver.
            Builtin::RegExpSpeciesGet => return Ok(this),
            Builtin::RegExpStringIteratorNext => {
                return self.regexp_string_iterator_next(&this)
            }
            _ => {}
        }
        match b {
            Builtin::SymbolFn
            | Builtin::SymbolFor
            | Builtin::SymbolKeyFor
            | Builtin::SymbolProtoToString
            | Builtin::SymbolProtoValueOf
            | Builtin::SymbolProtoToPrimitive
            | Builtin::SymbolProtoDescriptionGet
            | Builtin::FunctionProtoHasInstance
            | Builtin::ObjectGetOwnPropertySymbols => {
                return self.dispatch_symbol_builtin(b, this, &args, is_new);
            }
            Builtin::DateCtor
            | Builtin::DateNow
            | Builtin::DateUtc
            | Builtin::DateParse
            | Builtin::DateMethod(_) => {
                return self.dispatch_date_builtin(b, this, &args, is_new);
            }
            _ => {}
        }
        match b {
            Builtin::ReflectApply
            | Builtin::ReflectConstruct
            | Builtin::ReflectDefineProperty
            | Builtin::ReflectDeleteProperty
            | Builtin::ReflectGet
            | Builtin::ReflectGetOwnPropertyDescriptor
            | Builtin::ReflectGetPrototypeOf
            | Builtin::ReflectHas
            | Builtin::ReflectIsExtensible
            | Builtin::ReflectOwnKeys
            | Builtin::ReflectPreventExtensions
            | Builtin::ReflectSet
            | Builtin::ReflectSetPrototypeOf => return self.dispatch_reflect(b, &args),
            Builtin::ProxyCtor | Builtin::ProxyRevocable => {
                return self.dispatch_proxy(b, &args, is_new);
            }
            _ => {}
        }
        match b {
            Builtin::StringFn => {
                let u = if args.is_empty() {
                    Vec::new()
                } else if let Value::Sym(s) = arg(0) {
                    // String(symbol) (no `new`) is SymbolDescriptiveString, NOT
                    // a TypeError; `new String(symbol)` still throws.
                    if is_new {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                    self.symbol_descriptive_string(s)
                } else {
                    self.to_string_units(&arg(0))?
                };
                if is_new {
                    let oid = self.make_string_obj(&u)?;
                    return Ok(Value::Obj(oid));
                }
                Ok(Value::Str(Rc::new(u)))
            }
            Builtin::NumberFn => {
                // Number(value) (21.1.1.1): ToNumeric, and a BigInt result is
                // converted (not a TypeError) via 𝔽(ℝ(prim)).
                let n = if args.is_empty() {
                    0.0
                } else {
                    match self.to_numeric(&arg(0))? {
                        Value::BigInt(bn) => crate::bigint::to_f64(&bn),
                        Value::Num(x) => x,
                        _ => unreachable!("to_numeric yields Num or BigInt"),
                    }
                };
                if is_new {
                    let oid = self.alloc(Object::new(
                        ObjKind::NumberObj(n),
                        Some(self.intr.number_proto),
                    ));
                    return Ok(Value::Obj(oid));
                }
                Ok(Value::Num(n))
            }
            Builtin::BooleanFn => {
                let bv = self.to_boolean(&arg(0));
                if is_new {
                    let oid = self.alloc(Object::new(
                        ObjKind::BoolObj(bv),
                        Some(self.intr.boolean_proto),
                    ));
                    return Ok(Value::Obj(oid));
                }
                Ok(Value::Bool(bv))
            }
            Builtin::BigIntFn => {
                // `new BigInt()` is a TypeError (20.2.1.1); the call form
                // coerces with the integrality check.
                if is_new {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let prim = self.to_primitive(&arg(0), crate::expr::Hint::Number)?;
                // BigInt(Number) uses NumberToBigInt (RangeError on a
                // non-integer), NOT the ToBigInt TypeError path.
                if let Value::Num(n) = &prim {
                    return match crate::bigint::from_integral_f64(*n) {
                        Ok(b) => Ok(Value::bigint(b)),
                        Err(_) => Err(self.throw_native(NativeErrorKind::RangeError)),
                    };
                }
                let bn = self.to_bigint_from_primitive(&prim)?;
                Ok(Value::bigint(bn))
            }
            Builtin::BigIntAsIntN | Builtin::BigIntAsUintN => {
                // ToIndex(bits) FIRST, then ToBigInt(bigint) (20.2.2.1/.2).
                let bn = self.to_number(&arg(0))?;
                let bits_f = if bn.is_nan() { 0.0 } else { bn.trunc() };
                if !(0.0..=9_007_199_254_740_991.0).contains(&bits_f) {
                    return Err(self.throw_native(NativeErrorKind::RangeError));
                }
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let bits = bits_f as u64;
                let value = self.to_bigint(&arg(1))?;
                if bits > crate::bigint::MAX_BITS {
                    return Err(Abrupt::Fatal(
                        "BigInt.asIntN/asUintN bit width beyond the model cap (out of slice)"
                            .to_string(),
                    ));
                }
                let r = if matches!(b, Builtin::BigIntAsIntN) {
                    crate::bigint::as_int_n(bits, &value)
                } else {
                    crate::bigint::as_uint_n(bits, &value)
                };
                Ok(Value::bigint(r))
            }
            Builtin::BigIntProtoToString => {
                let x = self.this_bigint_value(&this)?;
                let radix = match arg(0) {
                    Value::Undefined => 10.0,
                    v => self.to_number(&v)?.trunc(),
                };
                if radix.is_nan() || !(2.0..=36.0).contains(&radix) {
                    return Err(self.throw_native(NativeErrorKind::RangeError));
                }
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let r = radix as u32;
                Ok(Value::str_from(&crate::bigint::to_string_radix(&x, r)))
            }
            Builtin::BigIntProtoValueOf => {
                let x = self.this_bigint_value(&this)?;
                Ok(Value::bigint(x))
            }
            Builtin::BigIntProtoToLocaleString => {
                // Locale-dependent grouping/formatting is engine latitude;
                // refuse rather than guess.
                self.this_bigint_value(&this)?;
                Err(Abrupt::Fatal(
                    "BigInt.prototype.toLocaleString (locale-dependent formatting out of slice)"
                        .to_string(),
                ))
            }
            Builtin::StringFromCharCode => {
                let mut out: Units = Vec::with_capacity(args.len());
                for a in &args {
                    let n = self.to_number(a)?;
                    out.push(to_uint16(n));
                }
                Ok(Value::Str(Rc::new(out)))
            }
            Builtin::StringFromCodePoint => {
                let mut out: Units = Vec::new();
                for a in &args {
                    let n = self.to_number(a)?;
                    if n.trunc() != n || !(0.0..=1_114_111.0).contains(&n) {
                        return Err(self.throw_native(NativeErrorKind::RangeError));
                    }
                    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                    let cp = n as u32;
                    if cp <= 0xffff {
                        out.push(u16::try_from(cp).expect("bmp"));
                    } else {
                        let v = cp - 0x1_0000;
                        out.push(u16::try_from(0xd800 + (v >> 10)).expect("lead"));
                        out.push(u16::try_from(0xdc00 + (v & 0x3ff)).expect("trail"));
                    }
                }
                Ok(Value::Str(Rc::new(out)))
            }
            Builtin::NumberProtoValueOf => {
                let n = self.this_number_value(&this)?;
                Ok(Value::Num(n))
            }
            Builtin::NumberProtoToString => {
                // thisNumberValue THEN the radix coercion/RangeError.
                let n = self.this_number_value(&this)?;
                let radix = match arg(0) {
                    Value::Undefined => 10.0,
                    v => self.to_number(&v)?.trunc(),
                };
                if radix.is_nan() || !(2.0..=36.0).contains(&radix) {
                    return Err(self.throw_native(NativeErrorKind::RangeError));
                }
                #[allow(clippy::float_cmp)]
                if radix == 10.0 {
                    return Ok(Value::str_from(&js_number_to_string(n)));
                }
                // Non-10 radix: exactly determined for NaN/±∞/integers (digit
                // expansion); fractional values would need the radix-N
                // shortest-representation algorithm — refuse those.
                if n.is_nan() {
                    return Ok(Value::str_from("NaN"));
                }
                if n.is_infinite() {
                    return Ok(Value::str_from(if n > 0.0 { "Infinity" } else { "-Infinity" }));
                }
                if n.trunc() != n {
                    return Err(Abrupt::Fatal(
                        "Number.prototype.toString: fractional value with a non-10 radix (radix-N shortest repr out of slice)"
                            .to_string(),
                    ));
                }
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let r = radix as u32;
                let neg = n < 0.0;
                let mut mag = n.abs();
                let mut digits: Vec<u8> = Vec::new();
                if mag == 0.0 {
                    digits.push(b'0');
                } else if mag > 9_007_199_254_740_992.0 {
                    return Err(Abrupt::Fatal(
                        "Number.prototype.toString: integer beyond 2^53 with a non-10 radix (repr latitude)"
                            .to_string(),
                    ));
                } else {
                    let rf = f64::from(r);
                    while mag > 0.0 {
                        let d = (mag % rf) as u8;
                        digits.push(if d < 10 { b'0' + d } else { b'a' + (d - 10) });
                        mag = (mag / rf).trunc();
                    }
                    digits.reverse();
                }
                let mut s = String::new();
                if neg {
                    s.push('-');
                }
                s.push_str(std::str::from_utf8(&digits).expect("ascii digits"));
                Ok(Value::str_from(&s))
            }
            Builtin::BooleanProtoValueOf | Builtin::BooleanProtoToString => {
                // Boolean.prototype is itself the `false` wrapper.
                let bv = match &this {
                    Value::Bool(x) => *x,
                    Value::Obj(o) if *o == self.intr.boolean_proto => false,
                    Value::Obj(o) => match self.obj(*o).kind {
                        ObjKind::BoolObj(x) => x,
                        _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
                    },
                    _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
                };
                Ok(if matches!(b, Builtin::BooleanProtoValueOf) {
                    Value::Bool(bv)
                } else {
                    Value::str_from(if bv { "true" } else { "false" })
                })
            }
            Builtin::NumberPredicate(p) => {
                let Value::Num(n) = arg(0) else {
                    return Ok(Value::Bool(false));
                };
                use crate::value::NumPred;
                Ok(Value::Bool(match p {
                    NumPred::IsNaN => n.is_nan(),
                    NumPred::IsFinite => n.is_finite(),
                    NumPred::IsInteger => n.is_finite() && n.trunc() == n,
                    NumPred::IsSafeInteger => {
                        n.is_finite() && n.trunc() == n && n.abs() <= 9_007_199_254_740_991.0
                    }
                }))
            }
            Builtin::IsNaN => Ok(Value::Bool(self.to_number(&arg(0))?.is_nan())),
            Builtin::IsFinite => Ok(Value::Bool(self.to_number(&arg(0))?.is_finite())),
            Builtin::Print | Builtin::ConsoleStdout | Builtin::ConsoleStderr => {
                // The trace driver's own event recorder builds JS arrays
                // (`vs = []; vs.push(...)`, `events.push(...)`), so an indexed
                // ACCESSOR planted on Array.prototype poisons the driver's push
                // and it records a different (or no) event — an artifact of the
                // driver's non-hermetic array use that the native recorder
                // cannot reproduce. Refuse rather than emit a mismatching trace.
                if self.array_proto_has_indexed_accessor() {
                    return Err(Abrupt::Fatal(
                        "indexed accessor on Array.prototype poisons the driver's event recorder \
                         (out of slice)"
                            .to_string(),
                    ));
                }
                let mut vs = Vec::with_capacity(args.len());
                for a in &args {
                    match crate::project::project(self, a) {
                        Ok(pv) => vs.push(pv),
                        // The driver builds its `vs` array element by element and
                        // pushes the event only after; a bigint projection throws
                        // TypeError there, so NO event is recorded and the throw
                        // propagates out of the console call (catchable by user).
                        Err(crate::project::ProjErr::BigIntTypeError) => {
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                        Err(crate::project::ProjErr::NoCoverage(e)) => {
                            return Err(Abrupt::Fatal(e));
                        }
                    }
                }
                self.events.push(if matches!(b, Builtin::ConsoleStderr) {
                    HostEvent::Stderr { v: vs }
                } else {
                    HostEvent::Stdout { v: vs }
                });
                Ok(Value::Undefined)
            }
            Builtin::ThrowTypeError => Err(self.throw_native(NativeErrorKind::TypeError)),
            Builtin::ObjectCtor => {
                // super() into Object: OrdinaryCreateFromConstructor from the
                // foreign new.target; the argument is IGNORED (20.1.1.1).
                if let Some(nt) = self.pending_new_target.take() {
                    let proto = self.proto_from_new_target(nt, self.intr.object_proto)?;
                    return Ok(Value::Obj(
                        self.alloc(Object::new(ObjKind::Plain, Some(proto))),
                    ));
                }
                match arg(0) {
                Value::Undefined | Value::Null => {
                    let oid =
                        self.alloc(Object::new(ObjKind::Plain, Some(self.intr.object_proto)));
                    Ok(Value::Obj(oid))
                }
                Value::Obj(oid) => Ok(Value::Obj(oid)),
                // ToObject on primitives: the wrapper exotics.
                Value::Str(s) => {
                    let oid = self.make_string_obj(&s)?;
                    Ok(Value::Obj(oid))
                }
                Value::BigInt(n) => Ok(Value::Obj(self.alloc(Object::new(
                    ObjKind::BigIntObj(n),
                    Some(self.intr.bigint_proto),
                )))),
                Value::Num(n) => Ok(Value::Obj(self.alloc(Object::new(
                    ObjKind::NumberObj(n),
                    Some(self.intr.number_proto),
                )))),
                Value::Bool(bv) => Ok(Value::Obj(self.alloc(Object::new(
                    ObjKind::BoolObj(bv),
                    Some(self.intr.boolean_proto),
                )))),
                Value::Sym(s) => Ok(Value::Obj(self.alloc(Object::new(
                    ObjKind::SymbolObj(s),
                    Some(self.intr.symbol_proto),
                )))),
                }
            }
            Builtin::ObjectCreate
            | Builtin::ObjectGetPrototypeOf
            | Builtin::ObjectSetPrototypeOf
            | Builtin::ObjectDefineProperty
            | Builtin::ObjectDefineProperties
            | Builtin::ObjectGetOwnPropertyDescriptor
            | Builtin::ObjectGetOwnPropertyDescriptors
            | Builtin::ObjectGetOwnPropertyNames
            | Builtin::ObjectKeys
            | Builtin::ObjectFreeze
            | Builtin::ObjectSeal
            | Builtin::ObjectPreventExtensions
            | Builtin::ObjectIsFrozen
            | Builtin::ObjectIsSealed
            | Builtin::ObjectIsExtensible => self.dispatch_object_static(b, &args),
            Builtin::ArrayCtor => {
                if args.len() == 1 {
                    if let Value::Num(n) = arg(0) {
                        let Some(len) = crate::number::exact_uint32(n) else {
                            return Err(self.throw_native(NativeErrorKind::RangeError));
                        };
                        let a = self.new_array(0);
                        self.set_array_length_raw(a, f64::from(len));
                        return Ok(Value::Obj(a));
                    }
                }
                let a = self.new_array(args.len());
                for (i, v) in args.iter().enumerate() {
                    self.obj_mut(a)
                        .props
                        .insert(units_from_str(&i.to_string()), Prop::data(v.clone()));
                }
                #[allow(clippy::cast_precision_loss)]
                self.set_array_length_raw(a, args.len() as f64);
                Ok(Value::Obj(a))
            }
            Builtin::ArrayIsArray => Ok(Value::Bool(self.is_array_value(&arg(0))?)),
            Builtin::ArrayOf => {
                // Array.of (23.1.2.3). A CONSTRUCTOR receiver other than
                // %Array% (`C.of(...)`) needs species-aware Construct +
                // CreateDataPropertyOrThrow — out of slice. Otherwise (the
                // default %Array% receiver, or any non-constructor `this` where
                // the spec falls back to ArrayCreate) build a fresh Array.
                if self.array_from_of_retargets(&this) {
                    return Err(Abrupt::Fatal(
                        "Array.of with a foreign constructor `this` (out of slice)".to_string(),
                    ));
                }
                let a = self.new_array(args.len());
                for (k, item) in args.iter().enumerate() {
                    self.obj_mut(a)
                        .props
                        .insert(units_from_str(&k.to_string()), Prop::data(item.clone()));
                }
                #[allow(clippy::cast_precision_loss)]
                self.set_array_length_raw(a, args.len() as f64);
                Ok(Value::Obj(a))
            }
            Builtin::ArrayFrom => {
                // Array.from (23.1.2.1). A CONSTRUCTOR receiver other than
                // %Array% needs species-aware Construct — out of slice.
                // Otherwise build a fresh Array (ArrayCreate).
                if self.array_from_of_retargets(&this) {
                    return Err(Abrupt::Fatal(
                        "Array.from with a foreign constructor `this` (out of slice)".to_string(),
                    ));
                }
                let items = arg(0);
                let map_fn = arg(1);
                let this_arg = arg(2);
                // Step 2-3: with a mapFn, it must be callable (else TypeError).
                let mapping = if matches!(map_fn, Value::Undefined) {
                    false
                } else {
                    if !matches!(&map_fn, Value::Obj(o) if self.obj(*o).is_callable()) {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                    true
                };
                // Step 4: usingIterator = GetMethod(items, @@iterator). A
                // TypeError here (undefined/null items) surfaces exactly.
                let iter_sid = self.intr.wk(WK_ITERATOR);
                let using = self.get_method_symbol(&items, iter_sid)?;
                let a = self.new_array(0);
                if using.is_some() {
                    // Iterator path (step 5): drive the general iterator
                    // protocol; a mapFn / CreateDataProperty fault IteratorCloses.
                    let mut it = self.slice_iterator(&items)?;
                    let mut k: u64 = 0;
                    loop {
                        self.charge_loop()?;
                        let next = self.slice_iter_next(&mut it)?;
                        let Some(val) = next else {
                            #[allow(clippy::cast_precision_loss)]
                            self.set_array_length_raw(a, k as f64);
                            return Ok(Value::Obj(a));
                        };
                        let mapped = if mapping {
                            #[allow(clippy::cast_precision_loss)]
                            let r = self.call_value(
                                &map_fn,
                                this_arg.clone(),
                                vec![val, Value::Num(k as f64)],
                            );
                            match r {
                                Ok(v) => v,
                                Err(e) => {
                                    let _ = self.slice_iterator_close(&mut it);
                                    return Err(e);
                                }
                            }
                        } else {
                            val
                        };
                        self.obj_mut(a)
                            .props
                            .insert(units_from_str(&k.to_string()), Prop::data(mapped));
                        k += 1;
                    }
                } else {
                    // Array-like path (step 6): ToObject(items), then read
                    // length + indices 0..length.
                    let obj = match &items {
                        Value::Undefined | Value::Null => {
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                        Value::Obj(o) => *o,
                        prim => self.to_object_wrapper(prim)?,
                    };
                    let len = self.length_of_array_like(obj)?;
                    let mut k: u64 = 0;
                    while k < len {
                        self.charge_loop()?;
                        let key = units_from_str(&k.to_string());
                        let kval = self.get_from_object(obj, &key)?;
                        let mapped = if mapping {
                            #[allow(clippy::cast_precision_loss)]
                            {
                                self.call_value(
                                    &map_fn,
                                    this_arg.clone(),
                                    vec![kval, Value::Num(k as f64)],
                                )?
                            }
                        } else {
                            kval
                        };
                        self.obj_mut(a)
                            .props
                            .insert(units_from_str(&k.to_string()), Prop::data(mapped));
                        k += 1;
                    }
                    #[allow(clippy::cast_precision_loss)]
                    self.set_array_length_raw(a, len as f64);
                    Ok(Value::Obj(a))
                }
            }
            Builtin::FunctionCtor => self.function_constructor(&args),
            Builtin::Eval => {
                // Reaching the %eval% builtin means an INDIRECT eval (the
                // direct-eval call form is intercepted in the call evaluator):
                // evaluate in the global scope.
                self.perform_eval(arg(0), None, false)
            }
            Builtin::FunctionProtoSelf => Ok(Value::Undefined),
            Builtin::FunctionProtoCall => {
                let rest: Vec<Value> = args.iter().skip(1).cloned().collect();
                self.call_value(&this, arg(0), rest)
            }
            Builtin::FunctionProtoApply => {
                let Value::Obj(f) = &this else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                if !self.obj(*f).is_callable() {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let this_arg = arg(0);
                let arg_array = arg(1);
                if matches!(arg_array, Value::Undefined | Value::Null) {
                    return self.call_value(&this, this_arg, Vec::new());
                }
                let Value::Obj(ao) = arg_array else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                // CreateListFromArrayLike.
                let len_v = self.get_from_object(ao, &units_from_str("length"))?;
                let len = to_length_u64(self.to_number(&len_v)?);
                if len > 65_535 {
                    return Err(Abrupt::Fatal(
                        "apply with an argument list beyond 65535 (engine arg-limit latitude)"
                            .to_string(),
                    ));
                }
                let mut list = Vec::with_capacity(len as usize);
                for i in 0..len {
                    self.charge_loop()?;
                    list.push(self.get_from_object(ao, &units_from_str(&i.to_string()))?);
                }
                self.call_value(&this, this_arg, list)
            }
            Builtin::FunctionProtoBind => self.fn_bind(&this, &args),
            Builtin::ObjectProtoToString => {
                Ok(Value::str_from(&object_to_string_tag(self, &this)?))
            }
            Builtin::ObjectProtoToLocaleString => {
                let m = self.get_prop_value(&this, &units_from_str("toString"))?;
                self.call_value(&m, this, Vec::new())
            }
            Builtin::ObjectProtoValueOf => match this {
                Value::Obj(_) => Ok(this),
                Value::Undefined | Value::Null => {
                    Err(self.throw_native(NativeErrorKind::TypeError))
                }
                _ => Err(Abrupt::Fatal(
                    "valueOf on primitive (wrapper out of slice)".to_string(),
                )),
            },
            Builtin::ObjectProtoHasOwnProperty => {
                let key = self.to_property_key(&arg(0))?;
                if let Value::Obj(oid) = &this {
                    if matches!(self.obj(*oid).kind, ObjKind::Proxy { .. }) {
                        let d = self.mop_get_own_property(*oid, &key)?;
                        return Ok(Value::Bool(d.is_some()));
                    }
                }
                match (&this, &key) {
                    (Value::Obj(oid), PropertyKey::Str(k)) => {
                        let oid = *oid;
                        // HasOwnProperty = GetOwnProperty is not undefined; via
                        // own_prop_resolved this also sees a typed array's
                        // integer-indexed exotic own elements.
                        if self.own_prop_resolved(oid, k).is_some() {
                            return Ok(Value::Bool(true));
                        }
                        // An own-property MISS is only reportable as `false`
                        // where our own-surface model of this object is
                        // complete (e.g. `Boolean.hasOwnProperty("prototype")`
                        // is true in a real engine; our Boolean has no
                        // modeled `prototype` — refuse, never say false).
                        let name = units_to_lossy(k);
                        if let Some(gap) = self.own_miss_gap(oid, &name) {
                            return Err(Abrupt::Fatal(format!("hasOwnProperty: {gap}")));
                        }
                        Ok(Value::Bool(false))
                    }
                    (Value::Obj(oid), PropertyKey::Sym(s)) => {
                        let (oid, s) = (*oid, *s);
                        if self.obj(oid).sym_props.contains_key(&s) {
                            return Ok(Value::Bool(true));
                        }
                        if let Some(gap) = self.sym_miss_danger(oid, s) {
                            return Err(Abrupt::Fatal(format!("hasOwnProperty: {gap}")));
                        }
                        Ok(Value::Bool(false))
                    }
                    (Value::Str(s), PropertyKey::Str(k)) => Ok(Value::Bool(
                        units_eq_ascii(k, "length")
                            || array_index_of(k).is_some_and(|i| (i as usize) < s.len()),
                    )),
                    (Value::Undefined | Value::Null, _) => {
                        Err(self.throw_native(NativeErrorKind::TypeError))
                    }
                    // Number/Boolean/Symbol wrappers (and a string wrapper's
                    // symbol keys) have no matching own property.
                    _ => Ok(Value::Bool(false)),
                }
            }
            Builtin::ObjectProtoIsPrototypeOf => {
                let Value::Obj(vo) = arg(0) else {
                    return Ok(Value::Bool(false));
                };
                match this {
                    Value::Obj(t) => {
                        // isPrototypeOf walks V's [[GetPrototypeOf]] chain, which
                        // routes through a proxy hop's trap.
                        let mut cur = self.mop_get_proto(vo)?;
                        let mut hops = 0;
                        while let Some(p) = cur {
                            if p == t {
                                return Ok(Value::Bool(true));
                            }
                            cur = self.mop_get_proto(p)?;
                            hops += 1;
                            if hops >= 64 {
                                return Err(Abrupt::Fatal("prototype chain too deep".into()));
                            }
                        }
                        Ok(Value::Bool(false))
                    }
                    Value::Undefined | Value::Null => {
                        Err(self.throw_native(NativeErrorKind::TypeError))
                    }
                    _ => Err(Abrupt::Fatal(
                        "isPrototypeOf on primitive (out of slice)".to_string(),
                    )),
                }
            }
            Builtin::ObjectProtoPropertyIsEnumerable => {
                let key = self.to_property_key(&arg(0))?;
                if let Value::Obj(oid) = &this {
                    if matches!(self.obj(*oid).kind, ObjKind::Proxy { .. }) {
                        let d = self.mop_get_own_property(*oid, &key)?;
                        return Ok(Value::Bool(d.is_some_and(|p| p.enumerable)));
                    }
                }
                match (&this, &key) {
                    (Value::Obj(oid), _) if *oid == self.global => {
                        // The global object aliases unmodeled engine globals:
                        // a sloppy `x = 1` insert can shadow a real global
                        // whose enumerability differs — attributes there are
                        // not exact, so refuse the whole surface.
                        let _ = key;
                        Err(Abrupt::Fatal(
                            "propertyIsEnumerable on the global object (attribute surface unmodeled)"
                                .to_string(),
                        ))
                    }
                    (Value::Obj(oid), PropertyKey::Str(k)) => {
                        let oid = *oid;
                        if let Some(p) = self.obj(oid).props.get(k) {
                            return Ok(Value::Bool(p.enumerable));
                        }
                        let name = units_to_lossy(k);
                        if let Some(gap) = self.own_miss_gap(oid, &name) {
                            return Err(Abrupt::Fatal(format!("propertyIsEnumerable: {gap}")));
                        }
                        Ok(Value::Bool(false))
                    }
                    (Value::Obj(oid), PropertyKey::Sym(s)) => {
                        let (oid, s) = (*oid, *s);
                        if let Some(p) = self.obj(oid).sym_props.get(&s) {
                            return Ok(Value::Bool(p.enumerable));
                        }
                        if let Some(gap) = self.sym_miss_danger(oid, s) {
                            return Err(Abrupt::Fatal(format!("propertyIsEnumerable: {gap}")));
                        }
                        Ok(Value::Bool(false))
                    }
                    (Value::Str(s), PropertyKey::Str(k)) => Ok(Value::Bool(
                        array_index_of(k).is_some_and(|i| (i as usize) < s.len()),
                    )),
                    (Value::Undefined | Value::Null, _) => {
                        Err(self.throw_native(NativeErrorKind::TypeError))
                    }
                    _ => Ok(Value::Bool(false)),
                }
            }
            Builtin::ArrayProtoJoin => self.array_join(&this, &arg(0)),
            Builtin::ArrayProtoConcat => {
                // 23.1.3.1: O = ToObject(this); A = ArraySpeciesCreate(O, 0);
                // then O and each argument are appended, spreading each
                // IsConcatSpreadable item element-by-element (holes preserved).
                let oid = self.array_like_receiver(&this)?;
                let out = self.array_species_create(oid, 0)?;
                let mut items: Vec<Value> = Vec::with_capacity(args.len() + 1);
                items.push(Value::Obj(oid));
                items.extend(args.iter().cloned());
                let mut n: u64 = 0;
                for item in items {
                    if self.is_concat_spreadable(&item)? {
                        let Value::Obj(eo) = item else { unreachable!("spreadable is an object") };
                        let elen = self.length_of_array_like(eo)?;
                        if n + elen > 9_007_199_254_740_991 {
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                        // A spreadable length beyond the iteration cap can't be
                        // walked element-by-element, and real engines diverge
                        // here (V8 skips dense-element access entirely for a
                        // huge length rather than reading index 0): refuse
                        // soundly rather than emit either engine's trace.
                        if elen > crate::interp::MAX_LOOP_ITERS {
                            return Err(Abrupt::Fatal(
                                "concat over a huge spreadable length (engine-specific dense-element behavior, out of slice)"
                                    .to_string(),
                            ));
                        }
                        let mut k: u64 = 0;
                        while k < elen {
                            self.charge_loop()?;
                            let key = units_from_str(&k.to_string());
                            if self.has_property_checked(eo, &key)? {
                                let v = self.get_from_object(eo, &key)?;
                                self.obj_mut(out)
                                    .props
                                    .insert(units_from_str(&n.to_string()), Prop::data(v));
                            }
                            n += 1;
                            k += 1;
                        }
                    } else {
                        if n >= 9_007_199_254_740_991 {
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                        self.obj_mut(out)
                            .props
                            .insert(units_from_str(&n.to_string()), Prop::data(item));
                        n += 1;
                    }
                }
                #[allow(clippy::cast_precision_loss)]
                self.set_on_object(out, &units_from_str("length"), Value::Num(n as f64), true)?;
                Ok(Value::Obj(out))
            }
            Builtin::ArrayProtoToString => {
                let m = self.get_prop_value(&this, &units_from_str("join"))?;
                if let Value::Obj(mid) = &m {
                    if self.obj(*mid).is_callable() {
                        return self.call_value(&m, this, Vec::new());
                    }
                }
                Ok(Value::str_from(&object_to_string_tag(self, &this)?))
            }
            Builtin::ArrayProtoMap
            | Builtin::ArrayProtoForEach
            | Builtin::ArrayProtoFilter
            | Builtin::ArrayProtoEvery
            | Builtin::ArrayProtoSome
            | Builtin::ArrayProtoFind
            | Builtin::ArrayProtoFindIndex
            | Builtin::ArrayProtoReduce
            | Builtin::ArrayProtoReduceRight => self.array_iterative(b, &this, &args),
            Builtin::ArrayProtoPush => {
                let oid = self.array_like_receiver(&this)?;
                let mut len = self.length_of_array_like(oid)?;
                // Step 3: len + argCount > 2^53-1 → TypeError.
                if len + args.len() as u64 > 9_007_199_254_740_991 {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                // Step 5: Set(O, ToString(len), E, true) per item — through
                // the real [[Set]] path, so index keys bump length and the
                // 2^32-1 key ("4294967295" is NOT an array index) lands as a
                // plain data property, exactly like OrdinarySet.
                for v in args {
                    self.set_on_object(oid, &units_from_str(&len.to_string()), v, true)?;
                    len += 1;
                }
                // Step 6: Set(O, "length", len, true) — ArraySetLength
                // throws RangeError when len is no longer a uint32.
                #[allow(clippy::cast_precision_loss)]
                let len_f = len as f64;
                self.set_on_object(oid, &units_from_str("length"), Value::Num(len_f), true)?;
                Ok(Value::Num(len_f))
            }
            Builtin::ArrayProtoPop => {
                let oid = self.array_like_receiver(&this)?;
                let len = self.length_of_array_like(oid)?;
                if len == 0 {
                    self.set_on_object(oid, &units_from_str("length"), Value::Num(0.0), true)?;
                    return Ok(Value::Undefined);
                }
                let new_len = len - 1;
                let key = units_from_str(&new_len.to_string());
                // element = ? Get(O, index): an inherited element (own hole,
                // prototype value) is returned, not undefined.
                let element = self.get_from_object(oid, &key)?;
                self.delete_or_throw(oid, &key)?;
                #[allow(clippy::cast_precision_loss)]
                self.set_on_object(
                    oid,
                    &units_from_str("length"),
                    Value::Num(new_len as f64),
                    true,
                )?;
                Ok(element)
            }
            Builtin::ArrayProtoShift => {
                let oid = self.array_like_receiver(&this)?;
                let len = self.length_of_array_like(oid)?;
                if len == 0 {
                    self.set_on_object(oid, &units_from_str("length"), Value::Num(0.0), true)?;
                    return Ok(Value::Undefined);
                }
                let first = self.get_from_object(oid, &units_from_str("0"))?;
                for k in 1..len {
                    self.charge_loop()?;
                    let from = units_from_str(&k.to_string());
                    let to = units_from_str(&(k - 1).to_string());
                    if self.has_property_checked(oid, &from)? {
                        let v = self.get_from_object(oid, &from)?;
                        self.set_on_object(oid, &to, v, true)?;
                    } else {
                        self.delete_or_throw(oid, &to)?;
                    }
                }
                self.delete_or_throw(oid, &units_from_str(&(len - 1).to_string()))?;
                #[allow(clippy::cast_precision_loss)]
                self.set_on_object(
                    oid,
                    &units_from_str("length"),
                    Value::Num((len - 1) as f64),
                    true,
                )?;
                Ok(first)
            }
            Builtin::ArrayProtoUnshift => {
                let oid = self.array_like_receiver(&this)?;
                let len = self.length_of_array_like(oid)?;
                let argc = args.len() as u64;
                if len + argc > 9_007_199_254_740_991 {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                if argc > 0 {
                    let mut k = len;
                    while k > 0 {
                        self.charge_loop()?;
                        let from = units_from_str(&(k - 1).to_string());
                        let to = units_from_str(&(k + argc - 1).to_string());
                        if self.has_property_checked(oid, &from)? {
                            let v = self.get_from_object(oid, &from)?;
                            self.set_on_object(oid, &to, v, true)?;
                        } else {
                            self.delete_or_throw(oid, &to)?;
                        }
                        k -= 1;
                    }
                    for (j, v) in args.into_iter().enumerate() {
                        self.set_on_object(
                            oid,
                            &units_from_str(&j.to_string()),
                            v,
                            true,
                        )?;
                    }
                }
                #[allow(clippy::cast_precision_loss)]
                let new_len = (len + argc) as f64;
                self.set_on_object(oid, &units_from_str("length"), Value::Num(new_len), true)?;
                Ok(Value::Num(new_len))
            }
            Builtin::ArrayProtoIndexOf => {
                let oid = self.array_like_receiver(&this)?;
                let len = i64::try_from(self.length_of_array_like(oid)?)
                    .expect("ToLength bounded by 2^53-1");
                // Step 3: if len is 0, return -1 BEFORE ToIntegerOrInfinity
                // (fromIndex): its valueOf must never run on an empty array.
                if len == 0 {
                    return Ok(Value::Num(-1.0));
                }
                let target = arg(0);
                let n = if args.len() > 1 {
                    to_integer_i64(self.to_number(&arg(1))?)
                } else {
                    0
                };
                let mut k = if n >= 0 { n } else { (len + n).max(0) };
                while k < len {
                    self.charge_loop()?;
                    let key = units_from_str(&k.to_string());
                    if self.has_property_checked(oid, &key)? {
                        let v = self.get_from_object(oid, &key)?;
                        if strict_eq(self, &v, &target) {
                            #[allow(clippy::cast_precision_loss)]
                            return Ok(Value::Num(k as f64));
                        }
                    }
                    k += 1;
                }
                Ok(Value::Num(-1.0))
            }
            Builtin::ArrayProtoLastIndexOf => {
                let oid = self.array_like_receiver(&this)?;
                let len = i64::try_from(self.length_of_array_like(oid)?)
                    .expect("ToLength bounded by 2^53-1");
                // Step 3: len 0 → -1 before the fromIndex coercion.
                if len == 0 {
                    return Ok(Value::Num(-1.0));
                }
                let target = arg(0);
                let n = if args.len() > 1 {
                    let f = self.to_number(&arg(1))?;
                    if f == f64::NEG_INFINITY {
                        return Ok(Value::Num(-1.0));
                    }
                    to_integer_i64(f)
                } else {
                    len - 1
                };
                let mut k = if n >= 0 { n.min(len - 1) } else { len + n };
                while k >= 0 {
                    self.charge_loop()?;
                    let key = units_from_str(&k.to_string());
                    if self.has_property_checked(oid, &key)? {
                        let v = self.get_from_object(oid, &key)?;
                        if strict_eq(self, &v, &target) {
                            #[allow(clippy::cast_precision_loss)]
                            return Ok(Value::Num(k as f64));
                        }
                    }
                    k -= 1;
                }
                Ok(Value::Num(-1.0))
            }
            Builtin::ArrayProtoIncludes => {
                let oid = self.array_like_receiver(&this)?;
                let len = i64::try_from(self.length_of_array_like(oid)?)
                    .expect("ToLength bounded by 2^53-1");
                if len == 0 {
                    return Ok(Value::Bool(false));
                }
                let target = arg(0);
                let nf = if args.len() > 1 {
                    self.to_number(&arg(1))?
                } else {
                    0.0
                };
                if nf == f64::INFINITY {
                    return Ok(Value::Bool(false));
                }
                let n = to_integer_i64(nf);
                let mut k = if n >= 0 { n } else { (len + n).max(0) };
                while k < len {
                    self.charge_loop()?;
                    // No HasProperty skip: includes reads holes as undefined.
                    let v = self.get_from_object(oid, &units_from_str(&k.to_string()))?;
                    if same_value_zero(&v, &target) {
                        return Ok(Value::Bool(true));
                    }
                    k += 1;
                }
                Ok(Value::Bool(false))
            }
            Builtin::ArrayProtoSlice => {
                let oid = self.array_like_receiver(&this)?;
                let len = i64::try_from(self.length_of_array_like(oid)?)
                    .expect("ToLength bounded by 2^53-1");
                let rel = |n: i64| -> i64 {
                    if n < 0 {
                        (len + n).max(0)
                    } else {
                        n.min(len)
                    }
                };
                let start = if args.is_empty() {
                    0
                } else {
                    rel(to_integer_i64(self.to_number(&arg(0))?))
                };
                let end = if args.len() < 2 || matches!(arg(1), Value::Undefined) {
                    len
                } else {
                    rel(to_integer_i64(self.to_number(&arg(1))?))
                };
                // Step 8: A = ? ArraySpeciesCreate(O, count).
                let count = u64::try_from((end - start).max(0)).expect("non-negative");
                let out = self.array_species_create(oid, count)?;
                let mut n: u64 = 0;
                let mut k = start;
                while k < end {
                    self.charge_loop()?;
                    let key = units_from_str(&k.to_string());
                    // kPresent = ? HasProperty(O, Pk); kValue = ? Get(O, Pk):
                    // inherited elements are copied, per spec.
                    if self.has_property_checked(oid, &key)? {
                        let v = self.get_from_object(oid, &key)?;
                        self.obj_mut(out)
                            .props
                            .insert(units_from_str(&n.to_string()), Prop::data(v));
                    }
                    n += 1;
                    k += 1;
                }
                // Step 15: Set(A, "length", n, true).
                #[allow(clippy::cast_precision_loss)]
                self.set_on_object(out, &units_from_str("length"), Value::Num(n as f64), true)?;
                Ok(Value::Obj(out))
            }
            Builtin::ArrayProtoValues | Builtin::ArrayProtoKeys | Builtin::ArrayProtoEntries => {
                // 23.1.3.{38,20,5}: O = ? ToObject(this); CreateArrayIterator(O, kind).
                let oid = self.array_like_receiver(&this)?;
                let kind = match b {
                    Builtin::ArrayProtoKeys => crate::value::ArrayIterKind::Key,
                    Builtin::ArrayProtoEntries => crate::value::ArrayIterKind::Entry,
                    _ => crate::value::ArrayIterKind::Value,
                };
                Ok(Value::Obj(self.create_array_iterator(oid, kind)))
            }
            Builtin::ArrayIteratorNext => {
                // 23.1.5.1: this must be an Array Iterator object.
                let Value::Obj(oid) = this else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                if !matches!(self.obj(oid).kind, ObjKind::ArrayIterator { .. }) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let (value, done) = self.array_iterator_step(oid)?;
                Ok(self.iter_result(value, done))
            }
            // %IteratorPrototype%[@@iterator] (27.1.2.1): return the this value.
            Builtin::IteratorProtoIterator => Ok(this),
            // String.prototype[@@iterator] (22.1.3.35): CreateStringIterator over
            // ToString(this) after RequireObjectCoercible.
            Builtin::StringProtoIterator => {
                if matches!(this, Value::Undefined | Value::Null) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let s = self.to_string_units(&this)?;
                Ok(Value::Obj(self.create_string_iterator(Rc::new(s))))
            }
            // %StringIteratorPrototype%.next (22.1.5.1.1): this must be a String
            // Iterator object.
            Builtin::StringIteratorNext => {
                let Value::Obj(oid) = this else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                if !matches!(self.obj(oid).kind, ObjKind::StringIterator { .. }) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let (value, done) = self.string_iterator_step(oid);
                Ok(self.iter_result(value, done))
            }
            Builtin::MathFn(op) => self.dispatch_math(op, &args),
            Builtin::StrProto(op) => self.dispatch_str_proto(op, &this, &args),
            Builtin::ErrorCtor(kind) => {
                // Take the foreign new.target FIRST (before any observable
                // coercion below can re-enter construction).
                let nt = self.pending_new_target.take();
                if args.len() > 1 && !matches!(arg(1), Value::Undefined) {
                    return Err(Abrupt::Fatal(
                        "Error options/cause argument (out of slice)".to_string(),
                    ));
                }
                let oid = self.make_native_error(kind, false);
                if let Some(nt) = nt {
                    let proto = self.proto_from_new_target(nt, self.intr.error_proto_for(kind))?;
                    self.obj_mut(oid).proto = Some(proto);
                }
                match arg(0) {
                    Value::Undefined => {
                        // No own message property at all.
                        self.obj_mut(oid).props.shift_remove(&units_from_str("message"));
                    }
                    v => {
                        let msg = self.to_string_units(&v)?;
                        let p = Prop::with_attrs(Value::Str(Rc::new(msg)), true, false, true);
                        self.obj_mut(oid).props.insert(units_from_str("message"), p);
                    }
                }
                Ok(Value::Obj(oid))
            }
            Builtin::ErrorProtoToString => {
                if !matches!(this, Value::Obj(_)) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let name_v = self.get_prop_value(&this, &units_from_str("name"))?;
                let name = match name_v {
                    Value::Undefined => units_from_str("Error"),
                    v => self.to_string_units(&v)?,
                };
                let msg_v = self.get_prop_value(&this, &units_from_str("message"))?;
                let msg = match msg_v {
                    Value::Undefined => Vec::new(),
                    v => self.to_string_units(&v)?,
                };
                let out: Units = if name.is_empty() {
                    msg
                } else if msg.is_empty() {
                    name
                } else {
                    let mut o = name;
                    o.extend_from_slice(&units_from_str(": "));
                    o.extend_from_slice(&msg);
                    o
                };
                Ok(Value::Str(Rc::new(out)))
            }
            Builtin::JsonStringify => {
                if args.len() > 1
                    && (!matches!(arg(1), Value::Undefined)
                        || !matches!(arg(2), Value::Undefined))
                {
                    return Err(Abrupt::Fatal(
                        "JSON.stringify replacer/space (out of slice)".to_string(),
                    ));
                }
                // SerializeJSONProperty step 2 (25.5.2.1): for an Object or a
                // BigInt, GetV(value, "toJSON") and, if callable, replace the
                // value with its result (key is the empty string at the top).
                let value = {
                    let v = arg(0);
                    if matches!(v, Value::Obj(_) | Value::BigInt(_)) {
                        let tojson = self.get_prop_value(&v, &units_from_str("toJSON"))?;
                        match &tojson {
                            Value::Obj(f) if self.obj(*f).is_callable() => {
                                self.call_function(*f, v, vec![Value::str_from("")], false)?
                            }
                            _ => v,
                        }
                    } else {
                        v
                    }
                };
                match value {
                    Value::Undefined => Ok(Value::Undefined),
                    Value::Null => Ok(Value::str_from("null")),
                    Value::Bool(x) => Ok(Value::str_from(if x { "true" } else { "false" })),
                    Value::Num(n) => Ok(Value::str_from(&if n.is_finite() {
                        js_number_to_string(n)
                    } else {
                        "null".to_string()
                    })),
                    Value::Str(s) => Ok(Value::Str(Rc::new(json_quote(&s)))),
                    // JSON.stringify(symbol) at top level → undefined (24.5.2).
                    Value::Sym(_) => Ok(Value::Undefined),
                    // After the toJSON step, a still-BigInt value is a TypeError
                    // (SerializeJSONProperty step 12).
                    Value::BigInt(_) => Err(self.throw_native(NativeErrorKind::TypeError)),
                    Value::Obj(oid) => {
                        if self.obj(oid).is_callable() {
                            return Ok(Value::Undefined); // functions stringify to undefined
                        }
                        Err(Abrupt::Fatal(
                            "JSON.stringify of object (out of slice)".to_string(),
                        ))
                    }
                }
            }
            // %GeneratorPrototype%.next/return/throw (27.5.1.2-4): validate the
            // receiver is a generator, then resume with the matching
            // completion.
            Builtin::GeneratorNext | Builtin::GeneratorReturn | Builtin::GeneratorThrow => {
                let Some(gid) = self.as_generator(&this) else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                let v = arg(0);
                let r = match b {
                    Builtin::GeneratorNext => crate::generator::Resumption::Normal(v),
                    Builtin::GeneratorReturn => crate::generator::Resumption::Return(v),
                    _ => crate::generator::Resumption::Throw(v),
                };
                self.generator_resume(gid, r)
            }
            Builtin::GeneratorFunctionCtor => Err(Abrupt::Fatal(
                "GeneratorFunction as callable/constructor (dynamic generator source) is out of slice"
                    .to_string(),
            )),
            Builtin::AsyncFunctionCtor => Err(Abrupt::Fatal(
                "AsyncFunction as callable/constructor (dynamic async source) is out of slice"
                    .to_string(),
            )),
            // Promise + the job/timer host surface are routed to
            // dispatch_promise_builtin at the top of dispatch_builtin.
            Builtin::PromiseCtor
            | Builtin::PromiseResolveStatic
            | Builtin::PromiseRejectStatic
            | Builtin::PromiseAll
            | Builtin::PromiseAllSettled
            | Builtin::PromiseRace
            | Builtin::PromiseAny
            | Builtin::PromiseProtoThen
            | Builtin::PromiseProtoCatch
            | Builtin::PromiseProtoFinally
            | Builtin::PromiseSpeciesGet
            | Builtin::SetTimeout
            | Builtin::SetInterval
            | Builtin::ClearTimer
            | Builtin::SetImmediate
            | Builtin::QueueMicrotask => {
                unreachable!("promise/timer builtins routed earlier in dispatch_builtin")
            }
            // Symbol/Date builtins are routed to their dedicated dispatchers at
            // the top of dispatch_builtin.
            Builtin::SymbolFn
            | Builtin::SymbolFor
            | Builtin::SymbolKeyFor
            | Builtin::SymbolProtoToString
            | Builtin::SymbolProtoValueOf
            | Builtin::SymbolProtoToPrimitive
            | Builtin::SymbolProtoDescriptionGet
            | Builtin::FunctionProtoHasInstance
            | Builtin::ObjectGetOwnPropertySymbols
            | Builtin::DateCtor
            | Builtin::DateNow
            | Builtin::DateUtc
            | Builtin::DateParse
            | Builtin::DateMethod(_)
            | Builtin::RegExpCtor
            | Builtin::RegExpProto(_)
            | Builtin::RegExpFlagGet(_)
            | Builtin::RegExpSpeciesGet
            | Builtin::RegExpStringIteratorNext
            | Builtin::ArrayBufferCtor
            | Builtin::ArrayBufferIsView
            | Builtin::SpeciesGetReceiver
            | Builtin::ArrayBufferByteLengthGet
            | Builtin::ArrayBufferMaxByteLengthGet
            | Builtin::ArrayBufferResizableGet
            | Builtin::ArrayBufferDetachedGet
            | Builtin::ArrayBufferSlice
            | Builtin::ArrayBufferResize
            | Builtin::ArrayBufferTransfer
            | Builtin::ArrayBufferTransferToFixed
            | Builtin::DataViewCtor
            | Builtin::DataViewBufferGet
            | Builtin::DataViewByteLengthGet
            | Builtin::DataViewByteOffsetGet
            | Builtin::DataViewGet(_)
            | Builtin::DataViewSet(_)
            | Builtin::TypedArrayAbstractCtor
            | Builtin::TypedArrayCtor(_)
            | Builtin::TypedArrayFrom
            | Builtin::TypedArrayOf
            | Builtin::TypedArrayBufferGet
            | Builtin::TypedArrayByteLengthGet
            | Builtin::TypedArrayByteOffsetGet
            | Builtin::TypedArrayLengthGet
            | Builtin::TypedArrayToStringTagGet
            | Builtin::TypedArrayMethod(_) => {
                unreachable!("Symbol/Date/RegExp/binary builtins are dispatched before this match")
            }
            // Reflect / Proxy / Object.setPrototypeOf are dispatched earlier.
            Builtin::ReflectApply
            | Builtin::ReflectConstruct
            | Builtin::ReflectDefineProperty
            | Builtin::ReflectDeleteProperty
            | Builtin::ReflectGet
            | Builtin::ReflectGetOwnPropertyDescriptor
            | Builtin::ReflectGetPrototypeOf
            | Builtin::ReflectHas
            | Builtin::ReflectIsExtensible
            | Builtin::ReflectOwnKeys
            | Builtin::ReflectPreventExtensions
            | Builtin::ReflectSet
            | Builtin::ReflectSetPrototypeOf
            | Builtin::ProxyCtor
            | Builtin::ProxyRevocable => {
                unreachable!("Reflect/Proxy builtins are dispatched before this match")
            }
            // Map/Set/WeakMap/WeakSet builtins are routed to
            // dispatch_collection_builtin at the top of dispatch_builtin.
            Builtin::MapCtor
            | Builtin::SetCtor
            | Builtin::WeakMapCtor
            | Builtin::WeakSetCtor
            | Builtin::MapGroupBy
            | Builtin::MapProtoGet
            | Builtin::MapProtoSet
            | Builtin::MapProtoHas
            | Builtin::MapProtoDelete
            | Builtin::MapProtoClear
            | Builtin::MapProtoForEach
            | Builtin::MapSizeGet
            | Builtin::MapProtoEntries
            | Builtin::MapProtoKeys
            | Builtin::MapProtoValues
            | Builtin::SetProtoAdd
            | Builtin::SetProtoHas
            | Builtin::SetProtoDelete
            | Builtin::SetProtoClear
            | Builtin::SetProtoForEach
            | Builtin::SetSizeGet
            | Builtin::SetProtoEntries
            | Builtin::SetProtoValues
            | Builtin::SetProtoCombinator
            | Builtin::WeakMapProtoGet
            | Builtin::WeakMapProtoSet
            | Builtin::WeakMapProtoHas
            | Builtin::WeakMapProtoDelete
            | Builtin::WeakSetProtoAdd
            | Builtin::WeakSetProtoHas
            | Builtin::WeakSetProtoDelete
            | Builtin::MapIteratorNext
            | Builtin::SetIteratorNext => {
                unreachable!("Map/Set builtins are dispatched before this match")
            }
        }
    }

    /// DeletePropertyOrThrow.
    fn delete_or_throw(&mut self, oid: ObjId, key: &Units) -> Result<(), Abrupt> {
        if self.delete_property(oid, key)? {
            Ok(())
        } else {
            Err(self.throw_native(NativeErrorKind::TypeError))
        }
    }

    // -- Function.prototype.bind --------------------------------------------

    fn fn_bind(&mut self, this: &Value, args: &[Value]) -> ERes {
        let Value::Obj(target) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let target = *target;
        if !self.obj(target).is_callable() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let bound_this = args.first().cloned().unwrap_or(Value::Undefined);
        let bound_args: Vec<Value> = args.iter().skip(1).cloned().collect();
        let argc = bound_args.len();
        // L: own length only (HasOwnProperty then Get).
        let mut l: f64 = 0.0;
        if self.obj(target).props.contains_key(&units_from_str("length")) {
            let lv = self.get_from_object(target, &units_from_str("length"))?;
            if let Value::Num(n) = lv {
                if n == f64::INFINITY {
                    l = f64::INFINITY;
                } else if n == f64::NEG_INFINITY {
                    l = 0.0;
                } else if n.is_nan() {
                    l = 0.0;
                } else {
                    #[allow(clippy::cast_precision_loss)]
                    let sub = n.trunc() - argc as f64;
                    l = sub.max(0.0);
                }
            }
        }
        // name: Get through the chain; non-string → "".
        let nv = self.get_from_object(target, &units_from_str("name"))?;
        let base_name = match nv {
            Value::Str(s) => units_to_lossy(&s),
            _ => String::new(),
        };
        let proto = self.obj(target).proto;
        let f = self.alloc(Object::new(
            ObjKind::Function(FnImpl::Bound {
                target,
                this_v: Box::new(bound_this),
                args: Rc::new(bound_args),
            }),
            proto,
        ));
        self.obj_mut(f).props.insert(
            units_from_str("length"),
            Prop::with_attrs(Value::Num(l), false, false, true),
        );
        self.obj_mut(f).props.insert(
            units_from_str("name"),
            Prop::with_attrs(Value::str_from(&format!("bound {base_name}")), false, false, true),
        );
        Ok(Value::Obj(f))
    }

    // -- Object statics ------------------------------------------------------

    #[allow(clippy::too_many_lines)]
    fn dispatch_object_static(&mut self, b: Builtin, args: &[Value]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        match b {
            Builtin::ObjectDefineProperty => {
                let Value::Obj(o) = arg(0) else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                let key = self.to_property_key(&arg(1))?;
                let desc = self.to_property_descriptor(&arg(2))?;
                let ok = self.define_own_property_pk(o, &key, &desc)?;
                if !ok {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                Ok(arg(0))
            }
            Builtin::ObjectCreate => {
                let proto = match arg(0) {
                    Value::Obj(p) => Some(p),
                    Value::Null => None,
                    _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
                };
                let obj = self.alloc(Object::new(ObjKind::Plain, proto));
                if !matches!(arg(1), Value::Undefined) {
                    self.define_properties_from(obj, &arg(1))?;
                }
                Ok(Value::Obj(obj))
            }
            Builtin::ObjectGetPrototypeOf => match arg(0) {
                Value::Obj(o) => Ok(self.mop_get_proto(o)?.map_or(Value::Null, Value::Obj)),
                Value::Str(_) => Ok(Value::Obj(self.intr.string_proto)),
                Value::Num(_) => Ok(Value::Obj(self.intr.number_proto)),
                Value::BigInt(_) => Ok(Value::Obj(self.intr.bigint_proto)),
                Value::Bool(_) => Ok(Value::Obj(self.intr.boolean_proto)),
                Value::Sym(_) => Ok(Value::Obj(self.intr.symbol_proto)),
                Value::Undefined | Value::Null => {
                    Err(self.throw_native(NativeErrorKind::TypeError))
                }
            },
            Builtin::ObjectSetPrototypeOf => {
                // 20.1.2.22: RequireObjectCoercible(O), then a proto that is
                // Object or Null; a non-object O returns unchanged.
                if matches!(arg(0), Value::Undefined | Value::Null) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let proto = match arg(1) {
                    Value::Obj(p) => Some(p),
                    Value::Null => None,
                    _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
                };
                let Value::Obj(o) = arg(0) else {
                    return Ok(arg(0));
                };
                let ok = self.mop_set_proto(o, proto)?;
                if !ok {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                Ok(arg(0))
            }
            Builtin::ObjectDefineProperties => {
                let Value::Obj(o) = arg(0) else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                self.define_properties_from(o, &arg(1))?;
                Ok(arg(0))
            }
            Builtin::ObjectGetOwnPropertyDescriptor => {
                match arg(0) {
                    Value::Undefined | Value::Null => {
                        Err(self.throw_native(NativeErrorKind::TypeError))
                    }
                    Value::Obj(o) if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) => {
                        let key = self.to_property_key(&arg(1))?;
                        match self.mop_get_own_property(o, &key)? {
                            Some(p) => self.from_property_descriptor(&p),
                            None => Ok(Value::Undefined),
                        }
                    }
                    Value::Obj(o) => match self.to_property_key(&arg(1))? {
                        PropertyKey::Str(key) => match self.own_prop_resolved(o, &key) {
                            Some(p) => self.from_property_descriptor(&p),
                            None => {
                                let name = units_to_lossy(&key);
                                if let Some(gap) = self.own_miss_gap(o, &name) {
                                    return Err(Abrupt::Fatal(format!(
                                        "getOwnPropertyDescriptor: {gap}"
                                    )));
                                }
                                Ok(Value::Undefined)
                            }
                        },
                        PropertyKey::Sym(s) => match self.obj(o).sym_props.get(&s).cloned() {
                            Some(p) => self.from_property_descriptor(&p),
                            None => {
                                if let Some(gap) = self.sym_miss_danger(o, s) {
                                    return Err(Abrupt::Fatal(format!(
                                        "getOwnPropertyDescriptor: {gap}"
                                    )));
                                }
                                Ok(Value::Undefined)
                            }
                        },
                    },
                    Value::Str(s) => match self.to_property_key(&arg(1))? {
                        PropertyKey::Str(key) => match string_own_prop(&s, &key) {
                            Some(p) => self.from_property_descriptor(&p),
                            None => Ok(Value::Undefined),
                        },
                        PropertyKey::Sym(_) => Ok(Value::Undefined),
                    },
                    _ => {
                        self.to_property_key(&arg(1))?;
                        Ok(Value::Undefined)
                    }
                }
            }
            Builtin::ObjectGetOwnPropertyDescriptors => {
                let out = self.alloc(Object::new(ObjKind::Plain, Some(self.intr.object_proto)));
                match arg(0) {
                    Value::Undefined | Value::Null => {
                        return Err(self.throw_native(NativeErrorKind::TypeError))
                    }
                    Value::Obj(o) if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) => {
                        for k in self.mop_own_keys(o)? {
                            let Some(p) = self.mop_get_own_property(o, &k)? else {
                                continue;
                            };
                            let d = self.from_property_descriptor(&p)?;
                            match k {
                                PropertyKey::Str(u) => {
                                    self.obj_mut(out).props.insert(u, Prop::data(d));
                                }
                                PropertyKey::Sym(s) => {
                                    self.obj_mut(out).sym_props.insert(s, Prop::data(d));
                                }
                            }
                        }
                    }
                    Value::Obj(o) => {
                        let keys = self
                            .own_keys_exact(o)
                            .map_err(|e| Abrupt::Fatal(format!("getOwnPropertyDescriptors: {e}")))?;
                        if !self.sym_surface_complete(o) {
                            return Err(Abrupt::Fatal(
                                "getOwnPropertyDescriptors over an object with unmodeled symbol surface"
                                    .to_string(),
                            ));
                        }
                        for k in keys {
                            let Some(p) = self.own_prop_resolved(o, &k) else {
                                continue;
                            };
                            let d = self.from_property_descriptor(&p)?;
                            self.obj_mut(out).props.insert(k, Prop::data(d));
                        }
                        // Symbol-keyed own descriptors follow the string keys
                        // ([[OwnPropertyKeys]] order), keyed by symbol on `out`.
                        let sym_keys: Vec<crate::value::SymId> =
                            self.obj(o).sym_props.keys().copied().collect();
                        for s in sym_keys {
                            let Some(p) = self.obj(o).sym_props.get(&s).cloned() else {
                                continue;
                            };
                            let d = self.from_property_descriptor(&p)?;
                            self.obj_mut(out).sym_props.insert(s, Prop::data(d));
                        }
                    }
                    Value::Str(s) => {
                        for k in string_own_keys(&s) {
                            let p = string_own_prop(&s, &k).expect("own key");
                            let d = self.from_property_descriptor(&p)?;
                            self.obj_mut(out).props.insert(k, Prop::data(d));
                        }
                    }
                    _ => {}
                }
                Ok(Value::Obj(out))
            }
            Builtin::ObjectGetOwnPropertyNames => {
                let keys: Vec<Units> = match arg(0) {
                    Value::Undefined | Value::Null => {
                        return Err(self.throw_native(NativeErrorKind::TypeError))
                    }
                    Value::Obj(o) if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) => self
                        .mop_own_keys(o)?
                        .into_iter()
                        .filter_map(|k| match k {
                            PropertyKey::Str(u) => Some(u),
                            PropertyKey::Sym(_) => None,
                        })
                        .collect(),
                    Value::Obj(o) => self
                        .own_keys_exact(o)
                        .map_err(|e| Abrupt::Fatal(format!("getOwnPropertyNames: {e}")))?,
                    Value::Str(s) => string_own_keys(&s),
                    _ => Vec::new(),
                };
                Ok(self.array_of_strings(keys))
            }
            Builtin::ObjectKeys => {
                let keys: Vec<Units> = match arg(0) {
                    Value::Undefined | Value::Null => {
                        return Err(self.throw_native(NativeErrorKind::TypeError))
                    }
                    Value::Obj(o) if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) => {
                        self.proxy_enumerable_string_keys(o)?
                    }
                    Value::Obj(o) => self
                        .enumerable_own_keys_sound(o)
                        .map_err(|e| Abrupt::Fatal(format!("Object.keys: {e}")))?,
                    Value::Str(s) => (0..s.len())
                        .map(|i| units_from_str(&i.to_string()))
                        .collect(),
                    _ => Vec::new(),
                };
                Ok(self.array_of_strings(keys))
            }
            Builtin::ObjectFreeze | Builtin::ObjectSeal => {
                let Value::Obj(o) = arg(0) else {
                    return Ok(arg(0));
                };
                if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                    let freeze = matches!(b, Builtin::ObjectFreeze);
                    if !self.proxy_set_integrity(o, freeze)? {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                    return Ok(arg(0));
                }
                self.own_surface_complete(o)
                    .map_err(|e| Abrupt::Fatal(format!("freeze/seal: {e}")))?;
                if !self.sym_surface_complete(o) {
                    return Err(Abrupt::Fatal(
                        "freeze/seal over an object with unmodeled symbol surface".to_string(),
                    ));
                }
                self.obj_mut(o).extensible = false;
                let freeze = matches!(b, Builtin::ObjectFreeze);
                let lock_desc = |is_data: bool| {
                    if freeze && is_data {
                        PropDesc {
                            writable: Some(false),
                            configurable: Some(false),
                            ..PropDesc::default()
                        }
                    } else {
                        PropDesc {
                            configurable: Some(false),
                            ..PropDesc::default()
                        }
                    }
                };
                // SetIntegrityLevel (7.3.15) locks every own key of
                // [[OwnPropertyKeys]]: string keys (integer-then-insertion),
                // then symbol keys (insertion order).
                let keys = crate::value::ordered_own_keys(self.obj(o));
                for k in keys {
                    let Some(cur) = self.own_prop_resolved(o, &k) else {
                        continue;
                    };
                    let desc = lock_desc(cur.is_data());
                    let ok = self.define_own_property(o, &k, &desc)?;
                    if !ok {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                }
                let sym_keys: Vec<crate::value::SymId> =
                    self.obj(o).sym_props.keys().copied().collect();
                for s in sym_keys {
                    let Some(cur) = self.obj(o).sym_props.get(&s).cloned() else {
                        continue;
                    };
                    let desc = lock_desc(cur.is_data());
                    let ok = self.define_own_property_sym(o, s, &desc)?;
                    if !ok {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                }
                Ok(arg(0))
            }
            Builtin::ObjectPreventExtensions => {
                let Value::Obj(o) = arg(0) else {
                    return Ok(arg(0));
                };
                if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                    // 20.1.2.20: a false result is a TypeError.
                    if !self.mop_prevent_extensions(o)? {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                    return Ok(arg(0));
                }
                if o == self.global {
                    return Err(Abrupt::Fatal(
                        "preventExtensions on the global object (host surface unmodeled)"
                            .to_string(),
                    ));
                }
                self.obj_mut(o).extensible = false;
                Ok(arg(0))
            }
            Builtin::ObjectIsFrozen | Builtin::ObjectIsSealed => {
                let Value::Obj(o) = arg(0) else {
                    return Ok(Value::Bool(true));
                };
                if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                    let frozen = matches!(b, Builtin::ObjectIsFrozen);
                    return Ok(Value::Bool(self.proxy_test_integrity(o, frozen)?));
                }
                if self.obj(o).extensible {
                    return Ok(Value::Bool(false));
                }
                self.own_surface_complete(o)
                    .map_err(|e| Abrupt::Fatal(format!("isFrozen/isSealed: {e}")))?;
                let frozen_check = matches!(b, Builtin::ObjectIsFrozen);
                let mut all = true;
                for (_, p) in &self.obj(o).props {
                    if p.configurable || (frozen_check && p.is_data() && p.writable()) {
                        all = false;
                        break;
                    }
                }
                if all && matches!(self.obj(o).kind, ObjKind::Arguments(_)) {
                    // The real @@iterator own property's attributes are not
                    // string-key-tracked: a `true` answer would also assert
                    // ITS state. Refuse the corner.
                    return Err(Abrupt::Fatal(
                        "isFrozen/isSealed(arguments) with frozen string surface (@@iterator attrs unmodeled)"
                            .to_string(),
                    ));
                }
                Ok(Value::Bool(all))
            }
            Builtin::ObjectIsExtensible => {
                let Value::Obj(o) = arg(0) else {
                    return Ok(Value::Bool(false));
                };
                if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                    return Ok(Value::Bool(self.mop_is_extensible(o)?));
                }
                Ok(Value::Bool(self.obj(o).extensible))
            }
            _ => unreachable!("non-static routed here"),
        }
    }

    /// ObjectDefineProperties (20.1.2.3.1): collect the descriptors, THEN
    /// apply them.
    fn define_properties_from(&mut self, o: ObjId, props: &Value) -> Result<(), Abrupt> {
        match props {
            Value::Undefined | Value::Null => Err(self.throw_native(NativeErrorKind::TypeError)),
            // wrappers: no own props
            Value::Num(_) | Value::Bool(_) | Value::Sym(_) | Value::BigInt(_) => Ok(()),
            Value::Str(s) => {
                if s.is_empty() {
                    Ok(())
                } else {
                    // First index descriptor is a one-char string →
                    // ToPropertyDescriptor throws TypeError.
                    Err(self.throw_native(NativeErrorKind::TypeError))
                }
            }
            Value::Obj(props) => {
                let props = *props;
                let keys = self
                    .own_keys_exact(props)
                    .map_err(|e| Abrupt::Fatal(format!("defineProperties: {e}")))?;
                let mut descs: Vec<(Units, PropDesc)> = Vec::new();
                for k in keys {
                    let Some(p) = self.own_prop_resolved(props, &k) else {
                        continue;
                    };
                    if !p.enumerable {
                        continue;
                    }
                    let desc_obj = self.get_from_object(props, &k)?;
                    let desc = self.to_property_descriptor(&desc_obj)?;
                    descs.push((k, desc));
                }
                for (k, desc) in descs {
                    let ok = self.define_own_property(o, &k, &desc)?;
                    if !ok {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                }
                Ok(())
            }
        }
    }

    /// Own ENUMERABLE string keys where that set is sound: complete-surface
    /// objects, or ECMA intrinsics whose unmodeled surface is spec-pinned
    /// non-enumerable (never console / the global object / error instances).
    pub(crate) fn enumerable_own_keys_sound(&self, oid: ObjId) -> Result<Vec<Units>, String> {
        if oid == self.global {
            return Err("global object enumerable surface unmodeled".to_string());
        }
        if oid == self.intr.console {
            return Err("console enumerable surface unmodeled (host object)".to_string());
        }
        if matches!(self.obj(oid).kind, ObjKind::Error) {
            return Err("error instance engine-incidental own properties".to_string());
        }
        // A typed array's element indices are enumerable data properties that
        // precede the (enumerable) ordinary string keys.
        let mut out: Vec<Units> = if matches!(self.obj(oid).kind, ObjKind::TypedArray { .. }) {
            self.ta_index_keys(oid)
        } else {
            Vec::new()
        };
        out.extend(
            crate::value::ordered_own_keys(self.obj(oid))
                .into_iter()
                .filter(|k| self.obj(oid).props.get(k).is_some_and(|p| p.enumerable)),
        );
        Ok(out)
    }

    fn array_of_strings(&mut self, keys: Vec<Units>) -> Value {
        let a = self.new_array(keys.len());
        let n = keys.len();
        for (i, k) in keys.into_iter().enumerate() {
            self.obj_mut(a).props.insert(
                units_from_str(&i.to_string()),
                Prop::data(Value::Str(Rc::new(k))),
            );
        }
        #[allow(clippy::cast_precision_loss)]
        self.set_array_length_raw(a, n as f64);
        Value::Obj(a)
    }

    // -- Math ----------------------------------------------------------------

    fn dispatch_math(&mut self, op: MathOp, args: &[Value]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        match op {
            MathOp::Max | MathOp::Min => {
                let mut coerced = Vec::with_capacity(args.len());
                for a in args {
                    coerced.push(self.to_number(a)?);
                }
                let mut acc = if matches!(op, MathOp::Max) {
                    f64::NEG_INFINITY
                } else {
                    f64::INFINITY
                };
                let mut nan = false;
                for n in coerced {
                    if n.is_nan() {
                        nan = true;
                    }
                    if nan {
                        continue;
                    }
                    let take = if matches!(op, MathOp::Max) {
                        n > acc || (n == acc && acc.is_sign_negative() && !n.is_sign_negative())
                    } else {
                        n < acc || (n == acc && n.is_sign_negative() && !acc.is_sign_negative())
                    };
                    if take {
                        acc = n;
                    }
                }
                Ok(Value::Num(if nan { f64::NAN } else { acc }))
            }
            MathOp::Pow => {
                let base = self.to_number(&arg(0))?;
                let exp = self.to_number(&arg(1))?;
                match math_pow_exact(base, exp) {
                    Some(v) => Ok(Value::Num(v)),
                    None => Err(Abrupt::Fatal(
                        "Math.pow outside the exactly-determined domain (implementation-approximated)"
                            .to_string(),
                    )),
                }
            }
            _ => {
                let n = self.to_number(&arg(0))?;
                let v = match op {
                    MathOp::Abs => n.abs(),
                    MathOp::Ceil => n.ceil(),
                    MathOp::Floor => n.floor(),
                    MathOp::Trunc => n.trunc(),
                    MathOp::Sqrt => n.sqrt(),
                    MathOp::Sign => {
                        if n.is_nan() || n == 0.0 {
                            n
                        } else if n > 0.0 {
                            1.0
                        } else {
                            -1.0
                        }
                    }
                    MathOp::Round => math_round(n),
                    MathOp::Max | MathOp::Min | MathOp::Pow => unreachable!(),
                };
                Ok(Value::Num(v))
            }
        }
    }

    // -- String.prototype ----------------------------------------------------

    #[allow(clippy::too_many_lines)]
    fn dispatch_str_proto(&mut self, op: StrOp, this: &Value, args: &[Value]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        if matches!(op, StrOp::ToStringOrValueOf) {
            // thisStringValue: a string primitive returns itself; a String
            // wrapper returns its [[StringData]] (String.prototype itself is
            // the "" wrapper); anything else TypeErrors.
            return match this {
                Value::Str(_) => Ok(this.clone()),
                Value::Obj(o) if *o == self.intr.string_proto => Ok(Value::str_from("")),
                Value::Obj(o) => match &self.obj(*o).kind {
                    ObjKind::StringObj(s) => Ok(Value::Str(Rc::clone(s))),
                    _ => Err(self.throw_native(NativeErrorKind::TypeError)),
                },
                _ => Err(self.throw_native(NativeErrorKind::TypeError)),
            };
        }
        // RequireObjectCoercible(this) precedes ToString(this).
        if matches!(this, Value::Undefined | Value::Null) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        // String.prototype.split/replace (22.1.3.x): BEFORE ToString(this), if
        // the separator/searchValue is neither undefined nor null, dispatch to
        // its @@split / @@replace method when present (Call(m, arg, «O, ...»)).
        // The `this`-value ToString happens only on the string-algorithm path.
        match op {
            StrOp::Split => {
                let sep = arg(0);
                if !matches!(sep, Value::Undefined | Value::Null) {
                    if let Some(splitter) = self.get_method_symbol(&sep, self.intr.wk(WK_SPLIT))? {
                        return self.call_function(
                            splitter,
                            sep,
                            vec![this.clone(), arg(1)],
                            false,
                        );
                    }
                }
            }
            StrOp::Replace => {
                let search = arg(0);
                if !matches!(search, Value::Undefined | Value::Null) {
                    if let Some(replacer) =
                        self.get_method_symbol(&search, self.intr.wk(WK_REPLACE))?
                    {
                        return self.call_function(
                            replacer,
                            search,
                            vec![this.clone(), arg(1)],
                            false,
                        );
                    }
                }
            }
            StrOp::Match => {
                let regexp = arg(0);
                if !matches!(regexp, Value::Undefined | Value::Null) {
                    if let Some(m) = self.get_method_symbol(&regexp, self.intr.wk(WK_MATCH))? {
                        return self.call_function(m, regexp, vec![this.clone()], false);
                    }
                }
            }
            StrOp::Search => {
                let regexp = arg(0);
                if !matches!(regexp, Value::Undefined | Value::Null) {
                    if let Some(m) = self.get_method_symbol(&regexp, self.intr.wk(WK_SEARCH))? {
                        return self.call_function(m, regexp, vec![this.clone()], false);
                    }
                }
            }
            StrOp::MatchAll => {
                let regexp = arg(0);
                if !matches!(regexp, Value::Undefined | Value::Null) {
                    // IsRegExp with a non-global flag is a pinned TypeError.
                    if self.is_regexp_public(&regexp)? {
                        let fl = self.get_prop_value(&regexp, &units_from_str("flags"))?;
                        if matches!(fl, Value::Undefined | Value::Null) {
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                        let fs = self.to_string_units(&fl)?;
                        if !fs.contains(&u16::from(b'g')) {
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                    }
                    if let Some(m) = self.get_method_symbol(&regexp, self.intr.wk(WK_MATCH_ALL))? {
                        return self.call_function(m, regexp, vec![this.clone()], false);
                    }
                }
            }
            StrOp::ReplaceAll => {
                let search = arg(0);
                if !matches!(search, Value::Undefined | Value::Null) {
                    if self.is_regexp_public(&search)? {
                        let fl = self.get_prop_value(&search, &units_from_str("flags"))?;
                        if matches!(fl, Value::Undefined | Value::Null) {
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                        let fs = self.to_string_units(&fl)?;
                        if !fs.contains(&u16::from(b'g')) {
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                    }
                    if let Some(r) = self.get_method_symbol(&search, self.intr.wk(WK_REPLACE))? {
                        return self.call_function(
                            r,
                            search,
                            vec![this.clone(), arg(1)],
                            false,
                        );
                    }
                }
            }
            _ => {}
        }
        let s = self.to_string_units(this)?;
        let len = s.len();
        let ilen = i64::try_from(len).expect("string cap bounded");
        match op {
            StrOp::CharAt => {
                let pos = to_integer_i64(self.to_number(&arg(0))?);
                if pos < 0 || pos >= ilen {
                    Ok(Value::str_from(""))
                } else {
                    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                    Ok(Value::Str(Rc::new(vec![s[pos as usize]])))
                }
            }
            StrOp::CharCodeAt => {
                let pos = to_integer_i64(self.to_number(&arg(0))?);
                if pos < 0 || pos >= ilen {
                    Ok(Value::Num(f64::NAN))
                } else {
                    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                    Ok(Value::Num(f64::from(s[pos as usize])))
                }
            }
            StrOp::IndexOf => {
                let search = self.to_string_units(&arg(0))?;
                let pos = to_integer_i64(self.to_number(&arg(1))?);
                let start = pos.clamp(0, ilen);
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let r = string_index_of(&s, &search, start as usize);
                Ok(Value::Num(r.map_or(-1.0, |i| {
                    #[allow(clippy::cast_precision_loss)]
                    {
                        i as f64
                    }
                })))
            }
            StrOp::LastIndexOf => {
                let search = self.to_string_units(&arg(0))?;
                let num_pos = self.to_number(&arg(1))?;
                let pos = if num_pos.is_nan() {
                    i64::MAX / 4
                } else {
                    to_integer_i64(num_pos)
                };
                let start = pos.clamp(0, ilen);
                let slen = search.len();
                if slen > len {
                    return Ok(Value::Num(-1.0));
                }
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let mut k = (start as usize).min(len - slen);
                loop {
                    if s[k..k + slen] == search[..] {
                        #[allow(clippy::cast_precision_loss)]
                        return Ok(Value::Num(k as f64));
                    }
                    if k == 0 {
                        return Ok(Value::Num(-1.0));
                    }
                    k -= 1;
                }
            }
            StrOp::Slice => {
                let from = to_integer_i64(self.to_number(&arg(0))?);
                let to = if matches!(arg(1), Value::Undefined) {
                    ilen
                } else {
                    to_integer_i64(self.to_number(&arg(1))?)
                };
                let rel = |n: i64| -> usize {
                    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                    if n < 0 {
                        ((ilen + n).max(0)) as usize
                    } else {
                        n.min(ilen) as usize
                    }
                };
                let (a, b) = (rel(from), rel(to));
                Ok(Value::Str(Rc::new(if a < b {
                    s[a..b].to_vec()
                } else {
                    Vec::new()
                })))
            }
            StrOp::Substring => {
                let a = to_integer_i64(self.to_number(&arg(0))?).clamp(0, ilen);
                let b = if matches!(arg(1), Value::Undefined) {
                    ilen
                } else {
                    to_integer_i64(self.to_number(&arg(1))?).clamp(0, ilen)
                };
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let (lo, hi) = (a.min(b) as usize, a.max(b) as usize);
                Ok(Value::Str(Rc::new(s[lo..hi].to_vec())))
            }
            StrOp::Split => self.str_split(&s, &arg(0), &arg(1)),
            StrOp::Replace => self.str_replace(&s, &arg(0), &arg(1)),
            StrOp::ReplaceAll => self.str_replace_all(&s, &arg(0), &arg(1)),
            // match / matchAll / search with a non-@@ argument: create a
            // RegExp from it and invoke its @@-protocol on S.
            StrOp::Match => {
                let rx = self.regexp_create(&arg(0), &Value::Undefined)?;
                let m = self
                    .get_method_symbol(&rx, self.intr.wk(WK_MATCH))?
                    .expect("fresh RegExp has @@match");
                self.call_function(m, rx, vec![Value::Str(Rc::new(s))], false)
            }
            StrOp::Search => {
                let rx = self.regexp_create(&arg(0), &Value::Undefined)?;
                let m = self
                    .get_method_symbol(&rx, self.intr.wk(WK_SEARCH))?
                    .expect("fresh RegExp has @@search");
                self.call_function(m, rx, vec![Value::Str(Rc::new(s))], false)
            }
            StrOp::MatchAll => {
                let rx = self.regexp_create(&arg(0), &Value::str_from("g"))?;
                let m = self
                    .get_method_symbol(&rx, self.intr.wk(WK_MATCH_ALL))?
                    .expect("fresh RegExp has @@matchAll");
                self.call_function(m, rx, vec![Value::Str(Rc::new(s))], false)
            }
            StrOp::Trim => {
                let is_ws = |c: u16| {
                    matches!(
                        c,
                        0x09 | 0x0a | 0x0b | 0x0c | 0x0d | 0x20 | 0xa0 | 0xfeff | 0x1680
                            | 0x2000..=0x200a | 0x2028 | 0x2029 | 0x202f | 0x205f | 0x3000
                    )
                };
                let start = s.iter().position(|&c| !is_ws(c)).unwrap_or(len);
                let end = s.iter().rposition(|&c| !is_ws(c)).map_or(start, |e| e + 1);
                Ok(Value::Str(Rc::new(s[start..end].to_vec())))
            }
            StrOp::ToLowerCase | StrOp::ToUpperCase => {
                if s.iter().any(|&c| c >= 0x80) {
                    return Err(Abrupt::Fatal(
                        "case mapping beyond ASCII (Unicode case tables out of slice)".to_string(),
                    ));
                }
                let lower = matches!(op, StrOp::ToLowerCase);
                let out: Units = s
                    .iter()
                    .map(|&c| {
                        if lower && (0x41..=0x5a).contains(&c) {
                            c + 0x20
                        } else if !lower && (0x61..=0x7a).contains(&c) {
                            c - 0x20
                        } else {
                            c
                        }
                    })
                    .collect();
                Ok(Value::Str(Rc::new(out)))
            }
            StrOp::ToStringOrValueOf => unreachable!("handled above"),
        }
    }

    /// String.prototype.split with a (coerced-to-)string separator.
    fn str_split(&mut self, s: &[u16], sep: &Value, limit: &Value) -> ERes {
        // Objects with @@split are unreachable in-slice; every separator
        // coerces through ToString (spec step 5) after the limit (step 4)...
        // Spec order: lim first (ToUint32), then R = ToString(separator).
        let lim: u64 = if matches!(limit, Value::Undefined) {
            u64::from(u32::MAX)
        } else {
            u64::from(crate::props::to_uint32(self.to_number(limit)?))
        };
        let sep_is_undefined = matches!(sep, Value::Undefined);
        let r = if sep_is_undefined {
            Vec::new()
        } else {
            self.to_string_units(sep)?
        };
        let mut parts: Vec<Units> = Vec::new();
        if lim == 0 {
            return Ok(self.array_of_strings(parts));
        }
        if sep_is_undefined {
            parts.push(s.to_vec());
            return Ok(self.array_of_strings(parts));
        }
        if s.is_empty() {
            if !r.is_empty() {
                parts.push(Vec::new());
            }
            return Ok(self.array_of_strings(parts));
        }
        let rlen = r.len();
        let slen = s.len();
        let mut p = 0usize;
        let mut q = 0usize;
        while q < slen {
            let matched = q + rlen <= slen && s[q..q + rlen] == r[..];
            if !matched {
                q += 1;
                continue;
            }
            let e = q + rlen;
            if e == p {
                q += 1;
                continue;
            }
            parts.push(s[p..q].to_vec());
            if parts.len() as u64 == lim {
                return Ok(self.array_of_strings(parts));
            }
            p = e;
            q = p;
        }
        parts.push(s[p..].to_vec());
        Ok(self.array_of_strings(parts))
    }

    /// String.prototype.replace with a string search value; the replacement
    /// is a function (exact) or a string (GetSubstitution without capture
    /// patterns — `$<digit>` / `$<` refuse).
    fn str_replace(&mut self, s: &[u16], search: &Value, replace: &Value) -> ERes {
        let search_str = self.to_string_units(search)?;
        let functional = matches!(replace, Value::Obj(f) if self.obj(*f).is_callable());
        let replace_str = if functional {
            Vec::new()
        } else {
            self.to_string_units(replace)?
        };
        let Some(pos) = string_index_of(s, &search_str, 0) else {
            return Ok(Value::Str(Rc::new(s.to_vec())));
        };
        let end = pos + search_str.len();
        let replacement: Units = if functional {
            #[allow(clippy::cast_precision_loss)]
            let rv = self.call_value(
                replace,
                Value::Undefined,
                vec![
                    Value::Str(Rc::new(search_str.clone())),
                    Value::Num(pos as f64),
                    Value::Str(Rc::new(s.to_vec())),
                ],
            )?;
            self.to_string_units(&rv)?
        } else {
            // GetSubstitution with zero captures.
            let mut out: Units = Vec::new();
            let mut i = 0;
            let dollar = u16::from(b'$');
            while i < replace_str.len() {
                let c = replace_str[i];
                if c != dollar || i + 1 >= replace_str.len() {
                    out.push(c);
                    i += 1;
                    continue;
                }
                let n = replace_str[i + 1];
                match n {
                    0x24 => {
                        out.push(dollar);
                        i += 2;
                    }
                    0x26 => {
                        out.extend_from_slice(&search_str);
                        i += 2;
                    }
                    0x60 => {
                        out.extend_from_slice(&s[..pos]);
                        i += 2;
                    }
                    0x27 => {
                        out.extend_from_slice(&s[end..]);
                        i += 2;
                    }
                    0x30..=0x39 | 0x3c => {
                        return Err(Abrupt::Fatal(
                            "replacement `$digit`/`$<` pattern without captures (spec-latitude corner)"
                                .to_string(),
                        ));
                    }
                    _ => {
                        out.push(dollar);
                        i += 1;
                    }
                }
            }
            out
        };
        let mut out: Units = Vec::with_capacity(s.len() + replacement.len());
        out.extend_from_slice(&s[..pos]);
        out.extend_from_slice(&replacement);
        out.extend_from_slice(&s[end..]);
        Ok(Value::Str(Rc::new(out)))
    }

    /// String.prototype.replaceAll (22.1.3.20) string-search path: replace
    /// EVERY non-overlapping occurrence of `search` (a string), with a
    /// function or a `$`-substitution string (no captures).
    fn str_replace_all(&mut self, s: &[u16], search: &Value, replace: &Value) -> ERes {
        let search_str = self.to_string_units(search)?;
        let functional = matches!(replace, Value::Obj(f) if self.obj(*f).is_callable());
        let replace_str = if functional {
            Vec::new()
        } else {
            self.to_string_units(replace)?
        };
        let search_len = search_str.len();
        let advance = search_len.max(1);
        let mut positions: Vec<usize> = Vec::new();
        let mut pos = 0usize;
        while let Some(p) = string_index_of(s, &search_str, pos) {
            positions.push(p);
            pos = p + advance;
        }
        let mut out: Units = Vec::new();
        let mut end_of_last = 0usize;
        for p in positions {
            if p < end_of_last {
                continue;
            }
            out.extend_from_slice(&s[end_of_last..p]);
            let replacement: Units = if functional {
                #[allow(clippy::cast_precision_loss)]
                let rv = self.call_value(
                    replace,
                    Value::Undefined,
                    vec![
                        Value::Str(Rc::new(search_str.clone())),
                        Value::Num(p as f64),
                        Value::Str(Rc::new(s.to_vec())),
                    ],
                )?;
                self.to_string_units(&rv)?
            } else {
                self.get_substitution(&search_str, s, p, &[], None, &replace_str)?
            };
            out.extend_from_slice(&replacement);
            end_of_last = p + search_len;
        }
        if end_of_last < s.len() {
            out.extend_from_slice(&s[end_of_last..]);
        }
        Ok(Value::Str(Rc::new(out)))
    }

    // -- Array iterative methods ---------------------------------------------

    #[allow(clippy::too_many_lines)]
    fn array_iterative(&mut self, b: Builtin, this: &Value, args: &[Value]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        let oid = self.array_like_receiver(this)?;
        let len = self.length_of_array_like(oid)?;
        let cb = arg(0);
        match &cb {
            Value::Obj(c) if self.obj(*c).is_callable() => {}
            _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
        }
        let this_arg = arg(1);
        match b {
            Builtin::ArrayProtoMap | Builtin::ArrayProtoForEach | Builtin::ArrayProtoFilter => {
                let result = match b {
                    Builtin::ArrayProtoMap => Some(self.array_species_create(oid, len)?),
                    Builtin::ArrayProtoFilter => Some(self.array_species_create(oid, 0)?),
                    _ => None,
                };
                let mut to: u64 = 0;
                for k in 0..len {
                    self.charge_loop()?;
                    let key = units_from_str(&k.to_string());
                    if !self.has_property_checked(oid, &key)? {
                        continue;
                    }
                    let v = self.get_from_object(oid, &key)?;
                    #[allow(clippy::cast_precision_loss)]
                    let r = self.call_value(
                        &cb,
                        this_arg.clone(),
                        vec![v.clone(), Value::Num(k as f64), Value::Obj(oid)],
                    )?;
                    match b {
                        Builtin::ArrayProtoMap => {
                            let res = result.expect("map result");
                            self.obj_mut(res).props.insert(key, Prop::data(r));
                        }
                        Builtin::ArrayProtoFilter => {
                            if self.to_boolean(&r) {
                                let res = result.expect("filter result");
                                self.obj_mut(res)
                                    .props
                                    .insert(units_from_str(&to.to_string()), Prop::data(v));
                                to += 1;
                                #[allow(clippy::cast_precision_loss)]
                                self.set_array_length_raw(res, to as f64);
                            }
                        }
                        _ => {}
                    }
                }
                match result {
                    Some(res) => Ok(Value::Obj(res)),
                    None => Ok(Value::Undefined),
                }
            }
            Builtin::ArrayProtoEvery | Builtin::ArrayProtoSome => {
                let every = matches!(b, Builtin::ArrayProtoEvery);
                for k in 0..len {
                    self.charge_loop()?;
                    let key = units_from_str(&k.to_string());
                    if !self.has_property_checked(oid, &key)? {
                        continue;
                    }
                    let v = self.get_from_object(oid, &key)?;
                    #[allow(clippy::cast_precision_loss)]
                    let r = self.call_value(
                        &cb,
                        this_arg.clone(),
                        vec![v, Value::Num(k as f64), Value::Obj(oid)],
                    )?;
                    let t = self.to_boolean(&r);
                    if every && !t {
                        return Ok(Value::Bool(false));
                    }
                    if !every && t {
                        return Ok(Value::Bool(true));
                    }
                }
                Ok(Value::Bool(every))
            }
            Builtin::ArrayProtoFind | Builtin::ArrayProtoFindIndex => {
                let want_value = matches!(b, Builtin::ArrayProtoFind);
                for k in 0..len {
                    self.charge_loop()?;
                    let key = units_from_str(&k.to_string());
                    // find/findIndex read holes as undefined (no skip).
                    let v = self.get_from_object(oid, &key)?;
                    #[allow(clippy::cast_precision_loss)]
                    let r = self.call_value(
                        &cb,
                        this_arg.clone(),
                        vec![v.clone(), Value::Num(k as f64), Value::Obj(oid)],
                    )?;
                    if self.to_boolean(&r) {
                        #[allow(clippy::cast_precision_loss)]
                        return Ok(if want_value { v } else { Value::Num(k as f64) });
                    }
                }
                Ok(if want_value {
                    Value::Undefined
                } else {
                    Value::Num(-1.0)
                })
            }
            Builtin::ArrayProtoReduce | Builtin::ArrayProtoReduceRight => {
                let fwd = matches!(b, Builtin::ArrayProtoReduce);
                let has_init = args.len() > 1;
                if len == 0 && !has_init {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let mut k: i64 = if fwd { 0 } else { i64::try_from(len).expect("ToLength bounded by 2^53-1") - 1 };
                let step = if fwd { 1 } else { -1 };
                let in_range = |k: i64| {
                    if fwd {
                        k < i64::try_from(len).expect("ToLength bounded by 2^53-1")
                    } else {
                        k >= 0
                    }
                };
                let mut acc: Value;
                if has_init {
                    acc = arg(1);
                } else {
                    let mut found = None;
                    while in_range(k) {
                        self.charge_loop()?;
                        let key = units_from_str(&k.to_string());
                        if self.has_property_checked(oid, &key)? {
                            found = Some(self.get_from_object(oid, &key)?);
                            k += step;
                            break;
                        }
                        k += step;
                    }
                    match found {
                        Some(v) => acc = v,
                        None => return Err(self.throw_native(NativeErrorKind::TypeError)),
                    }
                }
                while in_range(k) {
                    self.charge_loop()?;
                    let key = units_from_str(&k.to_string());
                    if self.has_property_checked(oid, &key)? {
                        let v = self.get_from_object(oid, &key)?;
                        #[allow(clippy::cast_precision_loss)]
                        {
                            acc = self.call_value(
                                &cb,
                                Value::Undefined,
                                vec![acc, v, Value::Num(k as f64), Value::Obj(oid)],
                            )?;
                        }
                    }
                    k += step;
                }
                Ok(acc)
            }
            _ => unreachable!("non-iterative routed here"),
        }
    }

    /// Allocate a String exotic wrapper with its index/length own properties
    /// materialized (so every generic property path works unchanged).
    pub(crate) fn make_string_obj(&mut self, data: &[u16]) -> Result<ObjId, Abrupt> {
        if data.len() > 10_000 {
            return Err(Abrupt::Fatal(
                "String wrapper beyond 10k units (own-property materialization cap)".to_string(),
            ));
        }
        let oid = self.alloc(Object::new(
            ObjKind::StringObj(Rc::new(data.to_vec())),
            Some(self.intr.string_proto),
        ));
        for (i, &u) in data.iter().enumerate() {
            self.obj_mut(oid).props.insert(
                units_from_str(&i.to_string()),
                Prop {
                    val: PropVal::Data {
                        value: Value::Str(Rc::new(vec![u])),
                        writable: false,
                    },
                    enumerable: true,
                    configurable: false,
                    synthetic: false,
                },
            );
        }
        #[allow(clippy::cast_precision_loss)]
        let len = data.len() as f64;
        self.obj_mut(oid).props.insert(
            units_from_str("length"),
            Prop::with_attrs(Value::Num(len), false, false, false),
        );
        Ok(oid)
    }

    /// thisNumberValue (21.1.3): a number primitive or a Number wrapper.
    /// Number.prototype is itself the +0 wrapper (verified against Node:
    /// `Number.prototype == 0` holds).
    fn this_number_value(&mut self, this: &Value) -> Result<f64, Abrupt> {
        match this {
            Value::Num(n) => Ok(*n),
            Value::Obj(o) if *o == self.intr.number_proto => Ok(0.0),
            Value::Obj(o) => match self.obj(*o).kind {
                ObjKind::NumberObj(n) => Ok(n),
                _ => Err(self.throw_native(NativeErrorKind::TypeError)),
            },
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    /// thisBigIntValue (20.2.3): the BigInt behind a bigint primitive or a
    /// BigInt wrapper; anything else (including `BigInt.prototype`, which has
    /// no [[BigIntData]]) is a TypeError.
    fn this_bigint_value(&mut self, this: &Value) -> Result<num_bigint::BigInt, Abrupt> {
        match this {
            Value::BigInt(n) => Ok((**n).clone()),
            Value::Obj(o) => match &self.obj(*o).kind {
                ObjKind::BigIntObj(n) => Ok((**n).clone()),
                _ => Err(self.throw_native(NativeErrorKind::TypeError)),
            },
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    /// ToBigInt (7.1.13): ToPrimitive(number hint) then the primitive
    /// dispatch. A Number is a TypeError here (the integer-checked coercion is
    /// only reachable through `BigInt(number)`).
    pub(crate) fn to_bigint(&mut self, v: &Value) -> Result<num_bigint::BigInt, Abrupt> {
        let prim = self.to_primitive(v, crate::expr::Hint::Number)?;
        self.to_bigint_from_primitive(&prim)
    }

    /// ToBigInt over an already-primitive value (no re-entrant ToPrimitive).
    pub(crate) fn to_bigint_from_primitive(
        &mut self,
        prim: &Value,
    ) -> Result<num_bigint::BigInt, Abrupt> {
        match prim {
            Value::BigInt(n) => Ok((**n).clone()),
            Value::Bool(b) => Ok(num_bigint::BigInt::from(i32::from(*b))),
            Value::Str(s) => match crate::bigint::string_to_bigint(s) {
                Some(n) => Ok(n),
                None => Err(self.throw_native(NativeErrorKind::SyntaxError)),
            },
            // Number / undefined / null / symbol → TypeError (7.1.13).
            Value::Num(_) | Value::Undefined | Value::Null | Value::Sym(_) => {
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
            Value::Obj(_) => {
                Err(Abrupt::Fatal("ToBigInt given a non-primitive (internal)".to_string()))
            }
        }
    }

    /// CreateArrayIterator (23.1.5.1): a fresh Array Iterator object over
    /// `target` (already ToObject'd) with next index 0.
    pub(crate) fn create_array_iterator(
        &mut self,
        target: ObjId,
        kind: crate::value::ArrayIterKind,
    ) -> ObjId {
        self.alloc(Object::new(
            ObjKind::ArrayIterator {
                target: Some(target),
                index: 0,
                kind,
            },
            Some(self.intr.array_iterator_proto),
        ))
    }

    /// One step of %ArrayIteratorPrototype%.next (23.1.5.1): returns
    /// (value, done). Reads the target's `length` and element LIVE each step
    /// (observable coercions included); exhaustion clears [[IteratedArrayLike]]
    /// so a later `next` stays done.
    pub(crate) fn array_iterator_step(&mut self, oid: ObjId) -> Result<(Value, bool), Abrupt> {
        use crate::value::ArrayIterKind;
        let (target, index, kind) = match self.obj(oid).kind {
            ObjKind::ArrayIterator {
                target,
                index,
                kind,
            } => (target, index, kind),
            _ => return Err(Abrupt::Fatal("array_iterator_step on non-iterator".to_string())),
        };
        let Some(target) = target else {
            return Ok((Value::Undefined, true));
        };
        let len = self.length_of_array_like(target)?;
        if index >= len {
            if let ObjKind::ArrayIterator { target, .. } = &mut self.obj_mut(oid).kind {
                *target = None;
            }
            return Ok((Value::Undefined, true));
        }
        if let ObjKind::ArrayIterator { index: i, .. } = &mut self.obj_mut(oid).kind {
            *i = index + 1;
        }
        #[allow(clippy::cast_precision_loss)]
        let idx_num = index as f64;
        let value = match kind {
            ArrayIterKind::Key => Value::Num(idx_num),
            ArrayIterKind::Value => {
                let key = units_from_str(&index.to_string());
                self.get_from_object(target, &key)?
            }
            ArrayIterKind::Entry => {
                let key = units_from_str(&index.to_string());
                let el = self.get_from_object(target, &key)?;
                let arr = self.new_array(2);
                self.obj_mut(arr)
                    .props
                    .insert(units_from_str("0"), Prop::data(Value::Num(idx_num)));
                self.obj_mut(arr)
                    .props
                    .insert(units_from_str("1"), Prop::data(el));
                self.set_array_length_raw(arr, 2.0);
                Value::Obj(arr)
            }
        };
        Ok((value, false))
    }

    /// CreateStringIterator (22.1.5.1): a fresh String Iterator over an
    /// immutable snapshot of `s` with next code-unit index 0.
    pub(crate) fn create_string_iterator(&mut self, s: Rc<Units>) -> ObjId {
        self.alloc(Object::new(
            ObjKind::StringIterator {
                string: Some(s),
                index: 0,
            },
            Some(self.intr.string_iterator_proto),
        ))
    }

    /// One step of %StringIteratorPrototype%.next (22.1.5.1.1): returns
    /// (value, done). Advances one code POINT (a UTF-16 surrogate pair counts
    /// as one); exhaustion clears [[IteratedString]] so a later `next` stays
    /// done. Totality: never panics (defensive indexing over the snapshot).
    pub(crate) fn string_iterator_step(&mut self, oid: ObjId) -> (Value, bool) {
        let (snapshot, index) = match &self.obj(oid).kind {
            ObjKind::StringIterator { string, index } => (string.clone(), *index),
            _ => return (Value::Undefined, true),
        };
        let Some(s) = snapshot else {
            return (Value::Undefined, true);
        };
        if index >= s.len() {
            if let ObjKind::StringIterator { string, .. } = &mut self.obj_mut(oid).kind {
                *string = None;
            }
            return (Value::Undefined, true);
        }
        // One code point: consume the low surrogate only when a well-formed
        // pair is present (a lone/leading surrogate is one unit, spec 22.1.5.1.1
        // via CodePointAt).
        let c = s[index];
        let mut out = vec![c];
        if (0xd800..=0xdbff).contains(&c)
            && index + 1 < s.len()
            && (0xdc00..=0xdfff).contains(&s[index + 1])
        {
            out.push(s[index + 1]);
        }
        let next = index + out.len();
        if let ObjKind::StringIterator { index: i, .. } = &mut self.obj_mut(oid).kind {
            *i = next;
        }
        (Value::Str(Rc::new(out)), false)
    }

    /// ToObject(this) for a generic Array.prototype method: any object
    /// receiver works (the methods are generic, and every property touch
    /// below runs through the danger-checked [[Get]]/[[Set]]/[[HasProperty]]
    /// paths); null/undefined is the spec TypeError; primitive receivers
    /// would need wrapper objects — refuse.
    fn array_like_receiver(&mut self, this: &Value) -> Result<ObjId, Abrupt> {
        match this {
            Value::Obj(oid) => Ok(*oid),
            Value::Undefined | Value::Null => {
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
            prim => self.to_object_wrapper(prim),
        }
    }

    /// LengthOfArrayLike (7.3.19): Get(O, "length") + ToLength — observable
    /// coercions included.
    fn length_of_array_like(&mut self, oid: ObjId) -> Result<u64, Abrupt> {
        let v = self.get_from_object(oid, &units_from_str("length"))?;
        let n = self.to_number(&v)?;
        Ok(to_length_u64(n))
    }

    /// Does an `Array.from`/`Array.of` call retarget to a FOREIGN constructor
    /// (a species-aware `C.from(...)` / `C.of(...)`)? The default %Array%
    /// receiver and any NON-constructor `this` (where the spec falls back to
    /// ArrayCreate) build a plain Array and are in slice; another constructor
    /// needs Construct(C) + CreateDataPropertyOrThrow and is out of slice.
    fn array_from_of_retargets(&self, this: &Value) -> bool {
        match this {
            Value::Obj(o) if *o == self.intr.array_ctor => false,
            Value::Obj(o) => self.is_constructor(*o),
            _ => false,
        }
    }

    /// ArrayCreate(len): a fresh Array exotic with length `len`.
    fn array_create(&mut self, len: u64) -> Result<ObjId, Abrupt> {
        if len > u64::from(u32::MAX) {
            return Err(self.throw_native(NativeErrorKind::RangeError));
        }
        let a = self.new_array(0);
        #[allow(clippy::cast_precision_loss)]
        self.set_array_length_raw(a, len as f64);
        Ok(a)
    }

    /// ArraySpeciesCreate(originalArray, length) — 10.4.2.3. Exact for the
    /// cases the slice can express; a non-default constructor OBJECT would
    /// need the @@species lookup and refuses.
    /// IsConcatSpreadable (23.1.3.1.1): honors @@isConcatSpreadable, else falls
    /// back to IsArray.
    fn is_concat_spreadable(&mut self, v: &Value) -> Result<bool, Abrupt> {
        let Value::Obj(o) = v else {
            return Ok(false);
        };
        let _ = o;
        let sid = self.intr.wk(WK_IS_CONCAT_SPREADABLE);
        let spread = self.get_prop_value_sym(v, sid)?;
        if matches!(spread, Value::Undefined) {
            // IsArray recurses through a proxy target.
            self.is_array_value(v)
        } else {
            Ok(self.to_boolean(&spread))
        }
    }

    fn array_species_create(&mut self, origin: ObjId, len: u64) -> Result<ObjId, Abrupt> {
        // Step 3: `isArray` is IsArray(originalArray), which recurses through a
        // proxy target (7.2.2). A non-Array original skips species entirely:
        // ArrayCreate(length).
        if !self.is_array_value(&Value::Obj(origin))? {
            return self.array_create(len);
        }
        // Step 5: C = ? Get(originalArray, "constructor") — routes through a
        // proxy origin's [[Get]].
        let c = self.get_from_object(origin, &units_from_str("constructor"))?;
        match c {
            // Step 7: C undefined → ArrayCreate(length).
            Value::Undefined => self.array_create(len),
            // The pristine intrinsic %Array%: its @@species returns the
            // constructor itself and no in-slice program can alter it (no
            // Symbol surface), so Construct(%Array%, len) ≡ ArrayCreate(len)
            // for the uint32 lengths arrays can carry.
            Value::Obj(cid) if cid == self.intr.array_ctor => self.array_create(len),
            Value::Obj(_) => Err(Abrupt::Fatal(
                "ArraySpeciesCreate with a non-default constructor (@@species lookup out of slice)"
                    .to_string(),
            )),
            // Step 9: a non-Object, non-undefined C is never a constructor —
            // TypeError, exactly per spec (null, number, string, boolean).
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    fn array_join(&mut self, this: &Value, sep: &Value) -> ERes {
        let Value::Obj(oid) = this else {
            return Err(Abrupt::Fatal("join on non-object".to_string()));
        };
        let len_v = self.get_prop_value(this, &units_from_str("length"))?;
        let len_n = self.to_number(&len_v)?;
        let len = to_length_u64(len_n);
        let sep_u = match sep {
            Value::Undefined => units_from_str(","),
            v => self.to_string_units(v)?,
        };
        let mut out: Units = Vec::new();
        for k in 0..len {
            self.charge_loop()?;
            if k > 0 {
                out.extend_from_slice(&sep_u);
            }
            let key = units_from_str(&k.to_string());
            let el = self.get_from_object(*oid, &key)?;
            if !matches!(el, Value::Undefined | Value::Null) {
                let u = self.to_string_units(&el)?;
                out.extend_from_slice(&u);
            }
            if out.len() > crate::interp::MAX_STRING_UNITS {
                return Err(Abrupt::Fatal("join result cap exceeded".to_string()));
            }
        }
        Ok(Value::Str(Rc::new(out)))
    }
}

/// The string exotic's own property for a key (index / length), if any.
fn string_own_prop(s: &[u16], key: &Units) -> Option<Prop> {
    if units_eq_ascii(key, "length") {
        #[allow(clippy::cast_precision_loss)]
        return Some(Prop::with_attrs(Value::Num(s.len() as f64), false, false, false));
    }
    let i = array_index_of(key)? as usize;
    if i < s.len() {
        Some(Prop {
            val: PropVal::Data {
                value: Value::Str(Rc::new(vec![s[i]])),
                writable: false,
            },
            enumerable: true,
            configurable: false,
            synthetic: false,
        })
    } else {
        None
    }
}

/// The string exotic's own keys: indices ascending, then "length".
fn string_own_keys(s: &[u16]) -> Vec<Units> {
    let mut keys: Vec<Units> = (0..s.len())
        .map(|i| units_from_str(&i.to_string()))
        .collect();
    keys.push(units_from_str("length"));
    keys
}

/// StringIndexOf (6.1.4.1): first match position at or after `start`.
fn string_index_of(s: &[u16], search: &[u16], start: usize) -> Option<usize> {
    if search.is_empty() {
        return if start <= s.len() { Some(start) } else { None };
    }
    if search.len() > s.len() {
        return None;
    }
    (start..=s.len() - search.len()).find(|&i| s[i..i + search.len()] == search[..])
}

/// SameValueZero: strict number equality with NaN==NaN (±0 equal).
fn same_value_zero(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Num(x), Value::Num(y)) => (x.is_nan() && y.is_nan()) || x == y,
        (Value::Undefined, Value::Undefined) | (Value::Null, Value::Null) => true,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Str(x), Value::Str(y)) => x == y,
        (Value::Sym(x), Value::Sym(y)) => x == y,
        (Value::Obj(x), Value::Obj(y)) => x == y,
        _ => false,
    }
}

/// Math.round: exactly per Number::round semantics (ties toward +∞), with an
/// exact fractional-part comparison (never `n + 0.5`, whose rounding lies).
fn math_round(n: f64) -> f64 {
    if !n.is_finite() || n == 0.0 {
        return n;
    }
    if n > 0.0 && n < 0.5 {
        return 0.0;
    }
    if n < 0.0 && n >= -0.5 {
        return -0.0;
    }
    let f = n.floor();
    let frac = n - f; // exact for |n| in the fractional range
    if frac >= 0.5 {
        f + 1.0
    } else {
        f
    }
}

/// Number::exponentiate where the spec pins the result exactly: the special-
/// case table, plus integer exponents whose whole computation is exact in
/// f64 (verified multiplication-by-multiplication). None = implementation-
/// approximated latitude → the caller refuses.
#[allow(clippy::float_cmp)]
pub(crate) fn math_pow_exact(base: f64, exp: f64) -> Option<f64> {
    let is_odd_int = |x: f64| x.trunc() == x && (x % 2.0).abs() == 1.0;
    if exp.is_nan() {
        return Some(f64::NAN);
    }
    if exp == 0.0 {
        return Some(1.0);
    }
    if base.is_nan() {
        return Some(f64::NAN);
    }
    if base.is_infinite() {
        return Some(if base > 0.0 {
            if exp > 0.0 { f64::INFINITY } else { 0.0 }
        } else if exp > 0.0 {
            if is_odd_int(exp) { f64::NEG_INFINITY } else { f64::INFINITY }
        } else if is_odd_int(exp) {
            -0.0
        } else {
            0.0
        });
    }
    if base == 0.0 {
        let neg_zero = base.is_sign_negative();
        return Some(if exp > 0.0 {
            if neg_zero && is_odd_int(exp) { -0.0 } else { 0.0 }
        } else if neg_zero && is_odd_int(exp) {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        });
    }
    if exp.is_infinite() {
        let mag = base.abs();
        return Some(if mag > 1.0 {
            if exp > 0.0 { f64::INFINITY } else { 0.0 }
        } else if mag < 1.0 {
            if exp > 0.0 { 0.0 } else { f64::INFINITY }
        } else {
            f64::NAN
        });
    }
    if base < 0.0 && exp.trunc() != exp {
        return Some(f64::NAN);
    }
    if exp.trunc() != exp {
        return None; // positive base, fractional exponent: approximated
    }
    // Integer exponent: exact square-and-multiply, refusing on any rounding.
    let neg_exp = exp < 0.0;
    let e_abs = exp.abs();
    if e_abs > 4096.0 {
        return None; // would overflow/underflow long before this anyway
    }
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let mut e = e_abs as u64;
    let mul_exact = |a: f64, b: f64| -> Option<f64> {
        let p = a * b;
        if !p.is_finite() {
            return None;
        }
        if a.mul_add(b, -p) == 0.0 {
            Some(p)
        } else {
            None
        }
    };
    let mut result = 1.0f64;
    let mut acc = base;
    loop {
        if e & 1 == 1 {
            result = mul_exact(result, acc)?;
        }
        e >>= 1;
        if e == 0 {
            break;
        }
        acc = mul_exact(acc, acc)?;
    }
    if !neg_exp {
        return Some(result);
    }
    // 1/result is exact iff result is a power of two with a finite
    // reciprocal.
    let bits = result.abs().to_bits();
    let mantissa = bits & ((1u64 << 52) - 1);
    let exponent = bits >> 52;
    let pow2 = if exponent == 0 {
        mantissa.count_ones() == 1
    } else {
        mantissa == 0
    };
    let recip = 1.0 / result;
    if pow2 && recip.is_finite() && recip * result == 1.0 {
        Some(recip)
    } else {
        None
    }
}

impl Interp {
    /// Resolve @@toStringTag for Object.prototype.toString (20.1.3.6) WITHOUT
    /// invoking a getter: walk the prototype chain for an own @@toStringTag
    /// data descriptor. `Ok(Some(s))` = an ASCII String tag to use; `Ok(None)`
    /// = no string override (fall through to the builtin tag); `Err` = a getter,
    /// a non-ASCII/synthetic data tag, an unmodeled declared-owned intrinsic
    /// symbol, or a proxy in the chain (result unknown → refuse).
    fn resolve_string_tag_data(&self, oid: ObjId) -> Result<Option<String>, Abrupt> {
        let tag_sym = self.intr.wk(WK_TO_STRING_TAG);
        let mut cur = Some(oid);
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 64 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                return Err(Abrupt::Fatal(
                    "Object.prototype.toString @@toStringTag reaches a proxy".to_string(),
                ));
            }
            if let Some(p) = self.obj(o).sym_props.get(&tag_sym) {
                return match &p.val {
                    PropVal::Data { value: Value::Str(s), .. } => {
                        if p.synthetic {
                            return Err(Abrupt::Fatal(
                                "Object.prototype.toString with an engine-specific @@toStringTag"
                                    .to_string(),
                            ));
                        }
                        // Non-ASCII tags would be mangled by a lossy decode and
                        // are not modeled — refuse rather than guess bytes.
                        if s.iter().all(|&c| (0x20..=0x7e).contains(&c)) {
                            Ok(Some(crate::value::units_to_lossy(s)))
                        } else {
                            Err(Abrupt::Fatal(
                                "Object.prototype.toString with a non-ASCII @@toStringTag"
                                    .to_string(),
                            ))
                        }
                    }
                    // A non-String data tag → spec falls through to builtinTag.
                    PropVal::Data { .. } => Ok(None),
                    PropVal::Accessor { .. } => Err(Abrupt::Fatal(
                        "Object.prototype.toString with a @@toStringTag getter".to_string(),
                    )),
                };
            }
            if let Some(gap) = self.sym_miss_danger(o, tag_sym) {
                return Err(Abrupt::Fatal(gap));
            }
            cur = self.obj(o).proto;
            hops += 1;
        }
        Ok(None)
    }
}

fn object_to_string_tag(it: &Interp, this: &Value) -> Result<String, Abrupt> {
    // A primitive `this` is ToObject'd (20.1.3.6 step 4), then @@toStringTag is
    // read off the resulting wrapper's prototype chain (steps 15-16). The fresh
    // wrapper has no own @@toStringTag, so resolving from the wrapper PROTOTYPE
    // is equivalent — a user override on Boolean/Number/String/Symbol/BigInt
    // .prototype (data String) wins; otherwise the builtin tag stands.
    let primitive_tag = |proto: ObjId, builtin: &str| -> Result<String, Abrupt> {
        Ok(it
            .resolve_string_tag_data(proto)?
            .unwrap_or_else(|| builtin.to_string()))
    };
    let tag = match this {
        Value::Undefined => "Undefined",
        Value::Null => "Null",
        Value::Bool(_) => {
            return Ok(format!("[object {}]", primitive_tag(it.intr.boolean_proto, "Boolean")?))
        }
        Value::Num(_) => {
            return Ok(format!("[object {}]", primitive_tag(it.intr.number_proto, "Number")?))
        }
        // BigInt/Symbol wrappers have NO [[XData]] builtin-tag branch (steps
        // 5-14), so their builtinTag is "Object". The "[object BigInt]" /
        // "[object Symbol]" forms come ONLY from the intrinsic @@toStringTag
        // data string; a non-string override falls back to "Object".
        Value::BigInt(_) => {
            return Ok(format!("[object {}]", primitive_tag(it.intr.bigint_proto, "Object")?))
        }
        Value::Str(_) => {
            return Ok(format!("[object {}]", primitive_tag(it.intr.string_proto, "String")?))
        }
        Value::Sym(_) => {
            return Ok(format!("[object {}]", primitive_tag(it.intr.symbol_proto, "Object")?))
        }
        Value::Obj(oid) => {
            // ArrayBuffer/DataView/typed arrays carry a modeled @@toStringTag
            // ("ArrayBuffer"/"DataView"/the constructor name). Use it only when
            // it is the UNSHADOWED, UNMODIFIED intrinsic (the first @@toStringTag
            // owner on the chain is the modeled prototype, carrying the intrinsic
            // property); any user shadow/redefinition falls through to refuse.
            let tst = it.intr.wk(WK_TO_STRING_TAG);
            let mut owner: Option<ObjId> = None;
            let mut cur = Some(*oid);
            let mut hops = 0;
            while let Some(o) = cur {
                if hops >= 64 {
                    break;
                }
                if it.obj(o).sym_props.contains_key(&tst) {
                    owner = Some(o);
                    break;
                }
                cur = it.obj(o).proto;
                hops += 1;
            }
            let intrinsic_tag = owner.and_then(|o| {
                let p = it.obj(o).sym_props.get(&tst)?;
                match (&it.obj(*oid).kind, &p.val) {
                    (ObjKind::ArrayBuffer(_), PropVal::Data { value: Value::Str(s), .. })
                        if o == it.intr.arraybuffer_proto && units_eq_ascii(s, "ArrayBuffer") =>
                    {
                        Some("ArrayBuffer".to_string())
                    }
                    (ObjKind::DataView { .. }, PropVal::Data { value: Value::Str(s), .. })
                        if o == it.intr.dataview_proto && units_eq_ascii(s, "DataView") =>
                    {
                        Some("DataView".to_string())
                    }
                    (ObjKind::TypedArray { elem, .. }, PropVal::Accessor { get: Some(g), .. })
                        if o == it.intr.typed_array_proto
                            && matches!(
                                it.obj(*g).kind,
                                ObjKind::Function(FnImpl::Builtin(
                                    Builtin::TypedArrayToStringTagGet
                                ))
                            ) =>
                    {
                        Some(elem.name().to_string())
                    }
                    _ => None,
                }
            });
            if let Some(tag) = intrinsic_tag {
                return Ok(format!("[object {tag}]"));
            }
            // 20.1.3.6: after the builtin tag, @@toStringTag overrides it. Read
            // it WITHOUT invoking a getter: a modeled ASCII data-string tag (the
            // spec-pinned intrinsic tags, or a plain user tag) is used directly;
            // a getter, a non-ASCII user tag, or an unmodeled declared-owned
            // intrinsic tag makes the result unknown — refuse.
            if let Some(tag) = it.resolve_string_tag_data(*oid)? {
                return Ok(format!("[object {tag}]"));
            }
            match &it.obj(*oid).kind {
            ObjKind::Array => "Array",
            ObjKind::Arguments(_) => "Arguments",
            // A generator function object carries @@toStringTag
            // "GeneratorFunction" on %GeneratorFunction.prototype% (→
            // "[object GeneratorFunction]"); that symbol tag — and the
            // @@toStringTag shadowing the tests exercise — is unmodeled, so
            // refuse rather than answer the plain "[object Function]".
            ObjKind::Function(FnImpl::User { lit, .. }) if lit.is_generator => {
                return Err(Abrupt::Fatal(
                    "Object.prototype.toString of a generator function (@@toStringTag \"GeneratorFunction\")"
                        .to_string(),
                ));
            }
            ObjKind::Function(_) => "Function",
            ObjKind::Error => "Error",
            ObjKind::StringObj(_) => "String",
            ObjKind::NumberObj(_) => "Number",
            ObjKind::BoolObj(_) => "Boolean",
            ObjKind::Plain => "Object",
            // A generator instance carries @@toStringTag "Generator" (→
            // "[object Generator]"); the symbol tag is unmodeled, so refuse.
            ObjKind::Generator(_) => {
                return Err(Abrupt::Fatal(
                    "Object.prototype.toString of a generator (@@toStringTag \"Generator\")"
                        .to_string(),
                ));
            }
            // An Array/String Iterator carries a modeled @@toStringTag ("Array
            // Iterator" / "String Iterator") returned by the guard above; this
            // arm is reached only if its prototype was swapped away (no tag),
            // where the builtin tag "Object" is exact.
            ObjKind::ArrayIterator { .. } | ObjKind::StringIterator { .. } => "Object",
            // The wrapper prototypes ARE wrappers ([[StringData]] "" /
            // [[NumberData]] +0 / [[BooleanData]] false — verified on Node).
            ObjKind::IntrinsicOpaque if *oid == it.intr.string_proto => "String",
            ObjKind::IntrinsicOpaque if *oid == it.intr.number_proto => "Number",
            ObjKind::IntrinsicOpaque if *oid == it.intr.boolean_proto => "Boolean",
            ObjKind::IntrinsicOpaque => {
                // console / JSON / Math / the global object carry engine- or
                // spec-@@toStringTag tags ("[object console]", "[object
                // JSON]", "[object Math]", "[object global]") we do not
                // model, and String.prototype is a String exotic. The
                // remaining IntrinsicOpaque objects (Object.prototype, the
                // error prototypes) are ordinary: tag "Object" is exact.
                if *oid == it.global || it.intr.opaque_hosts.contains(oid) {
                    return Err(Abrupt::Fatal(
                        "Object.prototype.toString tag of a host intrinsic (engine-specific @@toStringTag)"
                            .to_string(),
                    ));
                }
                "Object"
            }
            // A Promise's "[object Promise]" comes ONLY from the modeled
            // @@toStringTag "Promise" (returned by the guard above); it has no
            // [[XData]] branch, so an absent/non-string tag yields builtinTag
            // "Object".
            ObjKind::Promise(_) => "Object",
            // A Date has no @@toStringTag override (builtin tag "Date").
            ObjKind::DateObj(_) => "Date",
            // A RegExp's builtin tag is "RegExp" (20.1.3.6); it carries no
            // @@toStringTag, so the tag is exact.
            ObjKind::RegExpObj(_) => "RegExp",
            // The descriptive tag ("RegExp String Iterator" / "Symbol" /
            // "BigInt" / "ArrayBuffer" / "DataView") comes ONLY from the
            // modeled @@toStringTag data string, returned by the guard above.
            // These kinds have NO [[XData]] builtin-tag branch (steps 5-14), so
            // when the tag is absent or a NON-string override, the builtinTag is
            // "Object" (spec step 14/16).
            ObjKind::RegExpStringIterator { .. }
            | ObjKind::SymbolObj(_)
            | ObjKind::BigIntObj(_)
            | ObjKind::ArrayBuffer(_)
            | ObjKind::DataView { .. }
            | ObjKind::TypedArray { .. }
            // A Map/Set/WeakMap/WeakSet's "[object Map]"/... comes ONLY from the
            // modeled @@toStringTag string (returned by the guard above); no
            // [[XData]] builtin-tag branch exists, so an absent/non-string tag
            // (prototype swapped away) yields "Object". A Map/Set iterator
            // likewise carries only an inherited tag.
            | ObjKind::Map(_)
            | ObjKind::Set(_)
            | ObjKind::WeakMap(_)
            | ObjKind::WeakSet(_)
            | ObjKind::MapIterator { .. }
            | ObjKind::SetIterator { .. } => "Object",
            // Object.prototype.toString on a proxy does IsArray + Get(@@toStringTag)
            // through its traps — out of this static-tag slice, refuse.
            ObjKind::Proxy { .. } => {
                return Err(Abrupt::Fatal(
                    "Object.prototype.toString of a proxy (IsArray + @@toStringTag via traps)"
                        .to_string(),
                ))
            }
            }
        }
    };
    Ok(format!("[object {tag}]"))
}

fn to_integer_i64(n: f64) -> i64 {
    if n.is_nan() {
        return 0;
    }
    let t = n.trunc();
    if t <= -9_007_199_254_740_992.0 {
        i64::MIN / 4
    } else if t >= 9_007_199_254_740_992.0 {
        i64::MAX / 4
    } else {
        #[allow(clippy::cast_possible_truncation)]
        {
            t as i64
        }
    }
}

/// ToUint16 (7.1.8): total, exact (modulo 2^16 on the truncation).
fn to_uint16(n: f64) -> u16 {
    if !n.is_finite() || n == 0.0 {
        return 0;
    }
    let t = n.trunc();
    let m = t % 65_536.0;
    let m = if m < 0.0 { m + 65_536.0 } else { m };
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    {
        m as u16
    }
}

pub(crate) fn to_length_u64(n: f64) -> u64 {
    if n.is_nan() || n <= 0.0 {
        return 0;
    }
    let t = n.trunc();
    if t >= 9_007_199_254_740_991.0 {
        9_007_199_254_740_991
    } else {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        {
            t as u64
        }
    }
}

/// QuoteJSONString (well-formed): the actual JS string JSON.stringify
/// returns, as code units.
fn json_quote(s: &[u16]) -> Units {
    let mut out: Units = Vec::with_capacity(s.len() + 2);
    out.push(u16::from(b'"'));
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        match c {
            0x22 => out.extend_from_slice(&units_from_str("\\\"")),
            0x5c => out.extend_from_slice(&units_from_str("\\\\")),
            0x08 => out.extend_from_slice(&units_from_str("\\b")),
            0x0c => out.extend_from_slice(&units_from_str("\\f")),
            0x0a => out.extend_from_slice(&units_from_str("\\n")),
            0x0d => out.extend_from_slice(&units_from_str("\\r")),
            0x09 => out.extend_from_slice(&units_from_str("\\t")),
            c if c < 0x20 => out.extend_from_slice(&units_from_str(&format!("\\u{c:04x}"))),
            c if (0xd800..=0xdbff).contains(&c) => {
                if i + 1 < s.len() && (0xdc00..=0xdfff).contains(&s[i + 1]) {
                    out.push(c);
                    out.push(s[i + 1]);
                    i += 1;
                } else {
                    out.extend_from_slice(&units_from_str(&format!("\\u{c:04x}")));
                }
            }
            c if (0xdc00..=0xdfff).contains(&c) => {
                out.extend_from_slice(&units_from_str(&format!("\\u{c:04x}")));
            }
            c => out.push(c),
        }
        i += 1;
    }
    out.push(u16::from(b'"'));
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::units_to_lossy;

    #[test]
    fn json_quote_vectors() {
        let q = |s: &str| units_to_lossy(&json_quote(&units_from_str(s)));
        assert_eq!(q("ab"), "\"ab\"");
        assert_eq!(q("a\"b"), "\"a\\\"b\"");
        assert_eq!(q("a\nb"), "\"a\\nb\"");
        assert_eq!(q("\u{1}"), "\"\\u0001\"");
        assert_eq!(q("é"), "\"é\"");
    }

    #[test]
    fn math_round_vectors() {
        assert_eq!(math_round(0.5), 1.0);
        assert_eq!(math_round(-0.5).to_bits(), (-0.0f64).to_bits());
        assert_eq!(math_round(2.5), 3.0);
        assert_eq!(math_round(-2.5), -2.0);
        // The classic n+0.5 rounding trap: 0.49999999999999994 rounds DOWN.
        assert_eq!(math_round(0.499_999_999_999_999_94), 0.0);
        assert_eq!(math_round(4_503_599_627_370_495.5), 4_503_599_627_370_496.0);
        assert!(math_round(f64::NAN).is_nan());
    }

    #[test]
    fn math_pow_exact_vectors() {
        assert_eq!(math_pow_exact(2.0, 32.0), Some(4_294_967_296.0));
        assert_eq!(math_pow_exact(2.0, -2.0), Some(0.25));
        assert_eq!(math_pow_exact(10.0, 2.0), Some(100.0));
        assert_eq!(math_pow_exact(3.0, 5.0), Some(243.0));
        assert_eq!(math_pow_exact(f64::NAN, 0.0), Some(1.0));
        assert_eq!(math_pow_exact(0.0, -1.0), Some(f64::INFINITY));
        assert_eq!(
            math_pow_exact(-0.0, -1.0),
            Some(f64::NEG_INFINITY)
        );
        assert!(math_pow_exact(-2.0, 0.5).is_some_and(f64::is_nan));
        // 3^40 > 2^53: not exactly representable → refuse.
        assert_eq!(math_pow_exact(3.0, 40.0), None);
        // 10^-2 = 0.01 is not exact → refuse.
        assert_eq!(math_pow_exact(10.0, -2.0), None);
        // Fractional exponent with positive base: approximated → refuse.
        assert_eq!(math_pow_exact(2.0, 0.5), None);
    }
}
