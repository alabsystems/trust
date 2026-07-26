// Ordinary objects with the full property-descriptor model: data + accessor
// properties, attribute triples, spec own-key order (integer keys ascending,
// then string insertion order, then symbols), prototype chains,
// extensibility, and the exotic payloads the interpreter needs (arrays,
// arguments with a parameter map, primitive wrappers, functions).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::units::{array_index_of, Units};
use crate::value::{EnvId, JsValue, ObjId, SymId};
use indexmap::IndexMap;
use std::rc::Rc;

/// A property key: a string (code units) or a symbol identity.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PropKey {
    Str(Units),
    Sym(SymId),
}

impl PropKey {
    #[must_use]
    pub fn from_str(s: &str) -> PropKey {
        PropKey::Str(crate::units::units_from_str(s))
    }

    /// The string name, lossily decoded, for diagnostics.
    #[must_use]
    pub fn describe(&self) -> String {
        match self {
            PropKey::Str(u) => crate::units::units_to_lossy(u),
            PropKey::Sym(SymId::WellKnown(wk)) => wk.projection_name().to_string(),
            PropKey::Sym(SymId::User(i)) => format!("Symbol#{i}"),
        }
    }
}

/// The kind-specific half of a property.
#[derive(Debug, Clone)]
pub enum PropValue {
    Data { value: JsValue, writable: bool },
    Accessor { get: Option<ObjId>, set: Option<ObjId> },
}

/// One own property. `synthetic` marks a data value whose TEXT is
/// engine-specific (a runtime-error message this model cannot reproduce
/// byte-for-byte); reading or projecting it must refuse the case.
#[derive(Debug, Clone)]
pub struct Property {
    pub v: PropValue,
    pub enumerable: bool,
    pub configurable: bool,
    pub synthetic: bool,
}

impl Property {
    /// Ordinary data property `{w:true, e:true, c:true}`.
    #[must_use]
    pub fn data(value: JsValue) -> Property {
        Property::with_attrs(value, true, true, true)
    }

    /// Data property with explicit attributes.
    #[must_use]
    pub fn with_attrs(value: JsValue, writable: bool, enumerable: bool, configurable: bool) -> Property {
        Property {
            v: PropValue::Data { value, writable },
            enumerable,
            configurable,
            synthetic: false,
        }
    }

    /// Builtin-method convention `{w:true, e:false, c:true}`.
    #[must_use]
    pub fn method(value: JsValue) -> Property {
        Property::with_attrs(value, true, false, true)
    }

    /// Frozen data `{w:false, e:false, c:false}`.
    #[must_use]
    pub fn frozen(value: JsValue) -> Property {
        Property::with_attrs(value, false, false, false)
    }

    /// Accessor property.
    #[must_use]
    pub fn accessor(get: Option<ObjId>, set: Option<ObjId>, enumerable: bool, configurable: bool) -> Property {
        Property {
            v: PropValue::Accessor { get, set },
            enumerable,
            configurable,
            synthetic: false,
        }
    }

    /// The data value, if this is a data property.
    #[must_use]
    pub fn data_value(&self) -> Option<&JsValue> {
        match &self.v {
            PropValue::Data { value, .. } => Some(value),
            PropValue::Accessor { .. } => None,
        }
    }

    #[must_use]
    pub fn is_data(&self) -> bool {
        matches!(self.v, PropValue::Data { .. })
    }
}

/// Native error classes (identity picks the prototype).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrKind {
    Error,
    Type,
    Range,
    Reference,
    Syntax,
    Eval,
    Uri,
    Aggregate,
}

/// How a user function was defined — governs `this` binding, constructability
/// and the `prototype` own property.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnFlavor {
    /// function declaration / expression: constructible, has `prototype`.
    Normal,
    /// Object-literal / class method: not constructible, no `prototype`.
    Method,
    /// get/set accessor function: not constructible, no `prototype`.
    Getter,
    Setter,
    /// Arrow: lexical this/arguments/new.target, not constructible.
    Arrow,
    /// Class constructor: [[Call]] throws; `derived` = has an `extends`
    /// heritage (this-TDZ until `super()`).
    ClassCtor { derived: bool },
}

/// A user closure over the AST. `home` is the [[HomeObject]] for `super.x`
/// resolution (class/object methods).
#[derive(Debug)]
pub struct UserFn {
    pub func: Rc<trust_js_parse::ast::Func>,
    pub env: EnvId,
    pub flavor: FnFlavor,
    pub home: Option<ObjId>,
}

/// A bound-function exotic payload.
#[derive(Debug)]
pub struct BoundFn {
    pub target: ObjId,
    pub this: JsValue,
    pub args: Vec<JsValue>,
}

/// Function payload.
#[derive(Debug, Clone)]
pub enum FnData {
    User(Rc<UserFn>),
    Native(crate::realm::NativeFn),
    Bound(Rc<BoundFn>),
}

/// The arguments-object payload. `map[i] = Some(param)` aliases index `i` to
/// the parameter binding `param` in `env` (mapped arguments); an unmapped
/// arguments object carries an empty map.
#[derive(Debug, Clone)]
pub struct ArgsData {
    pub map: Vec<Option<String>>,
    pub env: EnvId,
}

/// Primitive-wrapper payload
/// ([[BooleanData]]/[[NumberData]]/[[StringData]]/[[SymbolData]]).
#[derive(Debug, Clone)]
pub enum WrapperPrim {
    Bool(bool),
    Num(f64),
    Str(Rc<Units>),
    Sym(crate::value::SymId),
    BigInt(Rc<crate::bigint::JsBigInt>),
}

/// RegExp flag record ([[OriginalFlags]] as booleans; the `flags` getter
/// emits canonical spec order d g i m s u v y).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RegexFlags {
    pub has_indices: bool,
    pub global: bool,
    pub ignore_case: bool,
    pub multiline: bool,
    pub dot_all: bool,
    pub unicode: bool,
    pub unicode_sets: bool,
    pub sticky: bool,
}

impl RegexFlags {
    /// Parse a validated flags string (the parser's regex_validate has
    /// already rejected invalid/duplicate flags). Unknown flags yield None.
    #[must_use]
    pub fn from_valid_str(s: &str) -> Option<RegexFlags> {
        let mut f = RegexFlags::default();
        for c in s.chars() {
            match c {
                'd' => f.has_indices = true,
                'g' => f.global = true,
                'i' => f.ignore_case = true,
                'm' => f.multiline = true,
                's' => f.dot_all = true,
                'u' => f.unicode = true,
                'v' => f.unicode_sets = true,
                'y' => f.sticky = true,
                _ => return None,
            }
        }
        Some(f)
    }
}

/// RegExp exotic payload (S1c skeleton: identity + accessors only; the
/// matcher itself is S1d and every match path refuses).
#[derive(Debug, Clone)]
pub struct RegexData {
    /// [[OriginalSource]]: for literals, the pattern text between the
    /// slashes, verbatim (engines report literal source unescaped).
    pub source: Rc<Units>,
    pub flags: RegexFlags,
}

/// Map/WeakMap entry list. Deleted/cleared entries become tombstones
/// (`None`) in place — spec [[MapData]] empties records without removing
/// them, so live iterator indices stay exact.
#[derive(Debug, Clone, Default)]
pub struct MapData {
    pub entries: Vec<Option<(JsValue, JsValue)>>,
}

/// Set/WeakSet entry list (same tombstone discipline).
#[derive(Debug, Clone, Default)]
pub struct SetData {
    pub entries: Vec<Option<JsValue>>,
}

/// A TypedArray element type (§23.2 Table 71). Governs bytes-per-element,
/// the element read/write coercion, and the constructor/prototype identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ElemType {
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

impl ElemType {
    /// All element types in a stable order (also the intrinsic-array index).
    pub const ALL: [ElemType; 12] = [
        ElemType::Int8,
        ElemType::Uint8,
        ElemType::Uint8Clamped,
        ElemType::Int16,
        ElemType::Uint16,
        ElemType::Int32,
        ElemType::Uint32,
        ElemType::Float16,
        ElemType::Float32,
        ElemType::Float64,
        ElemType::BigInt64,
        ElemType::BigUint64,
    ];

    /// Index into the intrinsics' per-type constructor/prototype arrays.
    #[must_use]
    pub fn idx(self) -> usize {
        match self {
            ElemType::Int8 => 0,
            ElemType::Uint8 => 1,
            ElemType::Uint8Clamped => 2,
            ElemType::Int16 => 3,
            ElemType::Uint16 => 4,
            ElemType::Int32 => 5,
            ElemType::Uint32 => 6,
            ElemType::Float16 => 7,
            ElemType::Float32 => 8,
            ElemType::Float64 => 9,
            ElemType::BigInt64 => 10,
            ElemType::BigUint64 => 11,
        }
    }

    /// The constructor / `@@toStringTag` name (`"Int8Array"`, ...).
    #[must_use]
    pub fn ctor_name(self) -> &'static str {
        match self {
            ElemType::Int8 => "Int8Array",
            ElemType::Uint8 => "Uint8Array",
            ElemType::Uint8Clamped => "Uint8ClampedArray",
            ElemType::Int16 => "Int16Array",
            ElemType::Uint16 => "Uint16Array",
            ElemType::Int32 => "Int32Array",
            ElemType::Uint32 => "Uint32Array",
            ElemType::Float16 => "Float16Array",
            ElemType::Float32 => "Float32Array",
            ElemType::Float64 => "Float64Array",
            ElemType::BigInt64 => "BigInt64Array",
            ElemType::BigUint64 => "BigUint64Array",
        }
    }

    #[must_use]
    pub fn bytes_per_element(self) -> usize {
        match self {
            ElemType::Int8 | ElemType::Uint8 | ElemType::Uint8Clamped => 1,
            ElemType::Int16 | ElemType::Uint16 | ElemType::Float16 => 2,
            ElemType::Int32 | ElemType::Uint32 | ElemType::Float32 => 4,
            ElemType::Float64 | ElemType::BigInt64 | ElemType::BigUint64 => 8,
        }
    }

    #[must_use]
    pub fn is_bigint(self) -> bool {
        matches!(self, ElemType::BigInt64 | ElemType::BigUint64)
    }

    #[must_use]
    pub fn is_float(self) -> bool {
        matches!(self, ElemType::Float16 | ElemType::Float32 | ElemType::Float64)
    }
}

/// The ArrayBuffer data block ([[ArrayBufferData]] / [[ArrayBufferByteLength]] /
/// [[ArrayBufferMaxByteLength]]). `bytes.len()` is the current byte length; a
/// detached buffer holds no data. `max_byte_length: Some` marks a resizable
/// buffer.
#[derive(Debug, Clone, Default)]
pub struct ArrayBufferData {
    pub bytes: Vec<u8>,
    pub detached: bool,
    pub max_byte_length: Option<usize>,
}

/// An integer-indexed exotic (TypedArray) payload. Elements live in the
/// referenced buffer's byte block; `array_length: None` marks a
/// length-tracking view over a resizable buffer.
#[derive(Debug, Clone)]
pub struct TypedArrayData {
    pub buffer: ObjId,
    pub byte_offset: usize,
    pub array_length: Option<usize>,
    pub element: ElemType,
}

/// A DataView payload. `byte_length: None` marks a length-tracking view.
#[derive(Debug, Clone)]
pub struct DataViewData {
    pub buffer: ObjId,
    pub byte_offset: usize,
    pub byte_length: Option<usize>,
}

/// A Proxy exotic object payload (§10.5). `target`/`handler` are set to `None`
/// together when the proxy is revoked; every internal method then throws a
/// TypeError. `callable`/`constructor` are fixed at creation from the target
/// (a proxy has a [[Call]]/[[Construct]] internal method iff its target does),
/// so `IsCallable`/`IsConstructor` stay stable across revocation as the spec
/// requires (the slots persist; invoking them throws).
#[derive(Debug, Clone)]
pub struct ProxyData {
    pub target: Option<ObjId>,
    pub handler: Option<ObjId>,
    pub callable: bool,
    pub constructor: bool,
}

impl ProxyData {
    /// The live (target, handler) pair, or `None` when revoked.
    #[must_use]
    pub fn parts(&self) -> Option<(ObjId, ObjId)> {
        match (self.target, self.handler) {
            (Some(t), Some(h)) => Some((t, h)),
            _ => None,
        }
    }
}

/// Object kind. `IntrinsicHost` marks realm infrastructure whose full engine
/// own-surface this model does not carry: reflection over it is governed by
/// the per-intrinsic danger sets, and projecting it refuses.
#[derive(Debug, Clone)]
pub enum ObjKind {
    Plain,
    Array,
    /// An instance created by a native Error constructor (engines add own
    /// engine-specific `stack`-style properties; projection refuses).
    Error,
    Function(FnData),
    Arguments(ArgsData),
    Wrapper(WrapperPrim),
    /// A Date instance ([[DateValue]]); no engine-extra own surface.
    Date(f64),
    /// A RegExp instance (S1c skeleton; own surface is exactly `lastIndex`).
    Regex(RegexData),
    /// Map instance ([[MapData]]).
    MapObj(MapData),
    /// Set instance ([[SetData]]).
    SetObj(SetData),
    /// WeakMap instance ([[WeakMapData]]; strong refs — GC is unobservable
    /// without WeakRef/FinalizationRegistry, which are unmodeled).
    WeakMapObj(MapData),
    /// WeakSet instance ([[WeakSetData]]).
    WeakSetObj(SetData),
    /// A generator instance (§27.5). The suspension state (frame stack +
    /// [[GeneratorState]]) lives in the interpreter's `gen_state` side table
    /// keyed by ObjId; the object itself is an opaque marker carrying only
    /// its [[Prototype]] (the generator function's `.prototype` at call time).
    Generator,
    /// An async generator instance (§27.6). Like `Generator`, an opaque marker;
    /// the suspension state (frame stack + [[AsyncGeneratorState]] +
    /// [[AsyncGeneratorQueue]]) lives in the interpreter's `async_gen_state`
    /// side table keyed by ObjId.
    AsyncGenerator,
    /// A built-in iterator object (§23.1.5 Array Iterator, §22.1.5 String
    /// Iterator, §24.1.5 Map Iterator, §24.2.5 Set Iterator). The iteration
    /// state ([[IteratedObject]]/next-index/kind) lives in the interpreter's
    /// `iter_state` side table keyed by ObjId; the object itself is an ordinary
    /// object carrying only its [[Prototype]] — it has NO own properties (its
    /// state is entirely in internal slots), so it projects as `{}` and its
    /// class tag resolves to "Object" through the (non-tagged) iterator
    /// prototype chain, exactly as engines expose it.
    Iterator,
    /// A Promise instance (§27.2). The reactor owns the actual promise state
    /// (pending/fulfilled/rejected, reaction records); this marker carries the
    /// reactor's dense `PromiseId` (a `usize`, kept dep-free of trust-js-reactor
    /// in the value crate). All internal slots live in the reactor's table.
    Promise(usize),
    /// An ArrayBuffer instance (§25.1). Owns the underlying byte block.
    ArrayBuffer(ArrayBufferData),
    /// A DataView instance (§25.3) over a buffer.
    DataView(DataViewData),
    /// An integer-indexed exotic (TypedArray) instance (§23.2).
    TypedArray(TypedArrayData),
    /// A Proxy exotic object (§10.5): all internal methods route through the
    /// handler traps. The `[[Prototype]]` slot (`proto`) is unused (the exotic
    /// [[GetPrototypeOf]] traps instead); it is stored `None`.
    Proxy(ProxyData),
    /// A Module Namespace Exotic Object (§10.4.6): the object bound by
    /// `import * as ns from '...'`. Its exported bindings live as ordinary own
    /// data properties (writable:true, enumerable:true, configurable:false, in
    /// SORTED name order) plus a frozen `@@toStringTag` = "Module"; the
    /// [[Prototype]] is null and the object is non-extensible. Only [[Set]]
    /// (always fails) and [[DefineOwnProperty]] (accepts only a no-op redefine)
    /// deviate from the ordinary internal methods, so this marker carries no
    /// payload — the interpreter intercepts exactly those two, and every other
    /// internal method (Get / GetOwnProperty / HasProperty / Delete /
    /// OwnPropertyKeys / GetPrototypeOf / SetPrototypeOf / extensibility) is
    /// the ordinary method over the stored props.
    ModuleNamespace,
    IntrinsicHost,
}

/// A heap object.
#[derive(Debug)]
pub struct JsObject {
    pub proto: Option<ObjId>,
    pub extensible: bool,
    pub props: IndexMap<PropKey, Property>,
    pub kind: ObjKind,
}

impl JsObject {
    #[must_use]
    pub fn new(kind: ObjKind, proto: Option<ObjId>) -> JsObject {
        JsObject {
            proto,
            extensible: true,
            props: IndexMap::new(),
            kind,
        }
    }

    #[must_use]
    pub fn is_callable(&self) -> bool {
        match &self.kind {
            ObjKind::Function(_) => true,
            // A proxy has a [[Call]] internal method iff its target does; the
            // slot persists after revocation (invoking it then throws).
            ObjKind::Proxy(p) => p.callable,
            _ => false,
        }
    }

    #[must_use]
    pub fn is_array(&self) -> bool {
        matches!(self.kind, ObjKind::Array)
    }
}

/// Own keys in spec [[OwnPropertyKeys]] order: canonical array indices
/// ascending, then the remaining string keys in insertion order, then symbol
/// keys in insertion order.
#[must_use]
pub fn ordered_own_keys(obj: &JsObject) -> Vec<PropKey> {
    let mut indices: Vec<(u32, &PropKey)> = Vec::new();
    let mut strings: Vec<&PropKey> = Vec::new();
    let mut symbols: Vec<&PropKey> = Vec::new();
    for k in obj.props.keys() {
        match k {
            PropKey::Str(u) => match array_index_of(u) {
                Some(i) => indices.push((i, k)),
                None => strings.push(k),
            },
            PropKey::Sym(_) => symbols.push(k),
        }
    }
    indices.sort_by_key(|(i, _)| *i);
    indices
        .into_iter()
        .map(|(_, k)| k.clone())
        .chain(strings.into_iter().cloned())
        .chain(symbols.into_iter().cloned())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::units::units_from_str;
    use crate::value::WkSym;

    #[test]
    fn own_key_order_is_indices_then_insertion_then_symbols() {
        let mut o = JsObject::new(ObjKind::Plain, None);
        o.props
            .insert(PropKey::from_str("b"), Property::data(JsValue::Null));
        o.props
            .insert(PropKey::from_str("2"), Property::data(JsValue::Null));
        o.props.insert(
            PropKey::Sym(SymId::WellKnown(WkSym::Iterator)),
            Property::data(JsValue::Null),
        );
        o.props
            .insert(PropKey::from_str("a"), Property::data(JsValue::Null));
        o.props
            .insert(PropKey::from_str("0"), Property::data(JsValue::Null));
        // Non-canonical numeric strings are plain string keys.
        o.props
            .insert(PropKey::from_str("01"), Property::data(JsValue::Null));
        let keys = ordered_own_keys(&o);
        assert_eq!(
            keys,
            vec![
                PropKey::Str(units_from_str("0")),
                PropKey::Str(units_from_str("2")),
                PropKey::Str(units_from_str("b")),
                PropKey::Str(units_from_str("a")),
                PropKey::Str(units_from_str("01")),
                PropKey::Sym(SymId::WellKnown(WkSym::Iterator)),
            ]
        );
    }

    #[test]
    fn descriptor_shapes() {
        let d = Property::data(JsValue::Bool(true));
        assert!(d.is_data() && d.enumerable && d.configurable);
        let m = Property::method(JsValue::Null);
        assert!(m.is_data() && !m.enumerable && m.configurable);
        let f = Property::frozen(JsValue::Null);
        assert!(!f.enumerable && !f.configurable);
        let a = Property::accessor(None, None, true, true);
        assert!(!a.is_data());
        assert!(a.data_value().is_none());
    }
}
