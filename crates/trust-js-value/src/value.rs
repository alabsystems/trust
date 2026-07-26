// JS values and handles. Symbols are first-class: well-known intrinsic
// identities plus user symbols allocated by the `Symbol` constructor (their
// descriptions live in the heap's symbol table). Symbol-KEYED properties are
// real observables (the arguments object's @@iterator, user symbol keys).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::bigint::JsBigInt;
use crate::units::Units;
use std::rc::Rc;

/// Heap handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjId(pub u32);

/// Environment-frame handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EnvId(pub u32);

/// A symbol identity: a well-known intrinsic, or a user symbol (index into
/// the heap's symbol-description table; `===` is index identity).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymId {
    WellKnown(WkSym),
    User(u32),
}

/// Well-known symbols (identities only).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WkSym {
    Iterator,
    AsyncIterator,
    HasInstance,
    IsConcatSpreadable,
    Match,
    MatchAll,
    Replace,
    Search,
    Species,
    Split,
    ToPrimitive,
    ToStringTag,
    Unscopables,
}

impl WkSym {
    /// The driver's well-known-symbol projection name.
    #[must_use]
    pub fn projection_name(self) -> &'static str {
        match self {
            WkSym::Iterator => "Symbol.iterator",
            WkSym::AsyncIterator => "Symbol.asyncIterator",
            WkSym::HasInstance => "Symbol.hasInstance",
            WkSym::IsConcatSpreadable => "Symbol.isConcatSpreadable",
            WkSym::Match => "Symbol.match",
            WkSym::MatchAll => "Symbol.matchAll",
            WkSym::Replace => "Symbol.replace",
            WkSym::Search => "Symbol.search",
            WkSym::Species => "Symbol.species",
            WkSym::Split => "Symbol.split",
            WkSym::ToPrimitive => "Symbol.toPrimitive",
            WkSym::ToStringTag => "Symbol.toStringTag",
            WkSym::Unscopables => "Symbol.unscopables",
        }
    }
}

/// A JS value. `BigInt` carries an arbitrary-precision signed integer
/// (`num_bigint::BigInt`) behind an `Rc` so cloning a value stays cheap.
#[derive(Debug, Clone)]
pub enum JsValue {
    Undefined,
    Null,
    Bool(bool),
    Num(f64),
    Str(Rc<Units>),
    Sym(SymId),
    BigInt(Rc<JsBigInt>),
    Obj(ObjId),
}

impl JsValue {
    #[must_use]
    pub fn str_from(s: &str) -> JsValue {
        JsValue::Str(Rc::new(crate::units::units_from_str(s)))
    }

    /// A BigInt value from an arbitrary-precision integer.
    #[must_use]
    pub fn bigint(b: JsBigInt) -> JsValue {
        JsValue::BigInt(Rc::new(b))
    }

    #[must_use]
    pub fn is_object(&self) -> bool {
        matches!(self, JsValue::Obj(_))
    }

    #[must_use]
    pub fn is_nullish(&self) -> bool {
        matches!(self, JsValue::Undefined | JsValue::Null)
    }
}
