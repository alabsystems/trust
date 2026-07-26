// Abstract operations and operators, written from ECMA-262: ToBoolean /
// ToNumeric / ToString / ToPrimitive / ToPropertyKey / ToObject, typeof,
// equality (strict, loose, SameValue), relational comparison, arithmetic,
// bitwise/shift, `in` and `instanceof`. BigInt and Symbol operands cannot
// arise in the S1a slice (their producers refuse); hitting one is a Fatal
// refusal, never a guess.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp, MAX_STRING_UNITS};
use std::rc::Rc;
use trust_js_value::{
    bigint_binary, bigint_cmp_f64, bigint_eq_f64, bigint_is_zero, bigint_to_decimal, js_number_to_string,
    string_to_bigint, to_int32, to_number_str, to_uint32, units_from_str, units_to_lossy, BigErr,
    BigOp, ErrKind, FnData, FnFlavor, JsBigInt, JsValue, NativeFn, ObjKind, PropKey, SymId, Units,
    WkSym,
};

/// The result of ToNumeric (7.1.3): a Number or a BigInt.
pub(crate) enum Numeric {
    N(f64),
    B(Rc<JsBigInt>),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Hint {
    Default,
    Number,
    String,
}

/// SameValueNonNumber + number strict equality (`===`): NaN ≠ NaN, +0 == -0.
#[must_use]
pub fn strict_eq(a: &JsValue, b: &JsValue) -> bool {
    match (a, b) {
        (JsValue::Undefined, JsValue::Undefined) | (JsValue::Null, JsValue::Null) => true,
        (JsValue::Bool(x), JsValue::Bool(y)) => x == y,
        (JsValue::Num(x), JsValue::Num(y)) => x == y,
        (JsValue::Str(x), JsValue::Str(y)) => x == y,
        (JsValue::Obj(x), JsValue::Obj(y)) => x == y,
        (JsValue::Sym(x), JsValue::Sym(y)) => x == y,
        (JsValue::BigInt(x), JsValue::BigInt(y)) => x == y,
        _ => false,
    }
}

/// SameValueZero: NaN == NaN, +0 == -0 (includes, Array membership).
#[must_use]
pub fn same_value_zero(a: &JsValue, b: &JsValue) -> bool {
    if let (JsValue::Num(x), JsValue::Num(y)) = (a, b) {
        if x.is_nan() && y.is_nan() {
            return true;
        }
        return x == y;
    }
    strict_eq(a, b)
}

/// SameValue (Object.is): NaN == NaN, +0 ≠ -0.
#[must_use]
pub fn same_value(a: &JsValue, b: &JsValue) -> bool {
    if let (JsValue::Num(x), JsValue::Num(y)) = (a, b) {
        if x.is_nan() && y.is_nan() {
            return true;
        }
        if *x == 0.0 && *y == 0.0 {
            return x.is_sign_negative() == y.is_sign_negative();
        }
        return x == y;
    }
    strict_eq(a, b)
}

impl Interp {
    pub(crate) fn throw_native(&mut self, kind: ErrKind) -> Abrupt {
        match self.make_native_error(kind, true) {
            Ok(oid) => Abrupt::Throw(JsValue::Obj(oid)),
            Err(a) => a,
        }
    }

    pub(crate) fn throw_type_error(&mut self) -> Abrupt {
        self.throw_native(ErrKind::Type)
    }

    // -- conversions ---------------------------------------------------------

    pub(crate) fn to_boolean(&self, v: &JsValue) -> bool {
        match v {
            JsValue::Undefined | JsValue::Null => false,
            JsValue::Bool(b) => *b,
            JsValue::Num(n) => !(*n == 0.0 || n.is_nan()),
            JsValue::Str(s) => !s.is_empty(),
            JsValue::Sym(_) | JsValue::Obj(_) => true,
            JsValue::BigInt(b) => !bigint_is_zero(b),
        }
    }

    /// ToNumber (via ToNumeric; BigInt refuses).
    pub(crate) fn to_number(&mut self, v: &JsValue) -> Result<f64, Abrupt> {
        match v {
            JsValue::Num(n) => Ok(*n),
            JsValue::Bool(b) => Ok(if *b { 1.0 } else { 0.0 }),
            JsValue::Undefined => Ok(f64::NAN),
            JsValue::Null => Ok(0.0),
            JsValue::Str(s) => {
                to_number_str(&units_to_lossy_exactish(s)).map_err(Abrupt::Fatal)
            }
            JsValue::Sym(_) => Err(self.throw_type_error()),
            // ToNumber(BigInt) is a TypeError (7.1.4 step 1).
            JsValue::BigInt(_) => Err(self.throw_type_error()),
            JsValue::Obj(_) => {
                let p = self.to_primitive(v, Hint::Number)?;
                self.to_number(&p)
            }
        }
    }

    /// ToNumeric (7.1.3): a Number or a BigInt (never coerced across).
    pub(crate) fn to_numeric(&mut self, v: &JsValue) -> Result<Numeric, Abrupt> {
        let p = self.to_primitive(v, Hint::Number)?;
        match p {
            JsValue::BigInt(b) => Ok(Numeric::B(b)),
            other => Ok(Numeric::N(self.to_number(&other)?)),
        }
    }

    /// ToBigInt (7.1.13): coerce to a BigInt or throw the exact exception.
    /// Numbers throw TypeError (only `BigInt(integralNumber)` accepts one, via
    /// NumberToBigInt); an unparseable String throws SyntaxError.
    pub(crate) fn to_bigint(&mut self, v: &JsValue) -> Result<JsBigInt, Abrupt> {
        let p = self.to_primitive(v, Hint::Number)?;
        match p {
            JsValue::BigInt(b) => Ok((*b).clone()),
            JsValue::Bool(b) => Ok(trust_js_value::bigint_from_bool(b)),
            JsValue::Str(s) => match string_to_bigint(&s) {
                Some(b) => Ok(b),
                None => Err(self.throw_native(ErrKind::Syntax)),
            },
            _ => Err(self.throw_type_error()),
        }
    }

    pub(crate) fn to_string_units(&mut self, v: &JsValue) -> Result<Units, Abrupt> {
        match v {
            JsValue::Str(s) => Ok(s.as_ref().clone()),
            JsValue::Num(n) => Ok(units_from_str(&js_number_to_string(*n))),
            JsValue::Bool(b) => Ok(units_from_str(if *b { "true" } else { "false" })),
            JsValue::Undefined => Ok(units_from_str("undefined")),
            JsValue::Null => Ok(units_from_str("null")),
            JsValue::Sym(_) => Err(self.throw_type_error()),
            JsValue::BigInt(b) => Ok(units_from_str(&bigint_to_decimal(b))),
            JsValue::Obj(_) => {
                let p = self.to_primitive(v, Hint::String)?;
                self.to_string_units(&p)
            }
        }
    }

    /// GetMethod (7.3.10): `None` for undefined/null; TypeError when the
    /// property exists but is not callable.
    pub(crate) fn get_method(
        &mut self,
        v: &JsValue,
        key: &PropKey,
    ) -> Result<Option<JsValue>, Abrupt> {
        let f = self.get_prop(v, key)?;
        match &f {
            JsValue::Undefined | JsValue::Null => Ok(None),
            JsValue::Obj(o) if self.heap.obj(*o).is_callable() => Ok(Some(f)),
            _ => Err(self.throw_type_error()),
        }
    }

    /// ToPrimitive (7.1.1): @@toPrimitive via GetMethod (exact — modeled
    /// intrinsic and user-defined handlers are both callable functions),
    /// then OrdinaryToPrimitive.
    pub(crate) fn to_primitive(&mut self, v: &JsValue, hint: Hint) -> ERes {
        if !v.is_object() {
            return Ok(v.clone());
        }
        let key = PropKey::Sym(SymId::WellKnown(WkSym::ToPrimitive));
        if let Some(m) = self.get_method(v, &key)? {
            let hint_s = match hint {
                Hint::Default => "default",
                Hint::Number => "number",
                Hint::String => "string",
            };
            let r = self.call_value(&m, v.clone(), vec![JsValue::str_from(hint_s)])?;
            if !r.is_object() {
                return Ok(r);
            }
            return Err(self.throw_type_error());
        }
        let order: [&str; 2] = if hint == Hint::String {
            ["toString", "valueOf"]
        } else {
            ["valueOf", "toString"]
        };
        for m in order {
            let mv = self.get_prop(v, &PropKey::from_str(m))?;
            if let JsValue::Obj(mid) = &mv {
                if self.heap.obj(*mid).is_callable() {
                    let r = self.call_value(&mv, v.clone(), vec![])?;
                    if !r.is_object() {
                        return Ok(r);
                    }
                }
            }
        }
        Err(self.throw_type_error())
    }

    /// IsConstructor (7.2.4) over the modeled function kinds.
    pub(crate) fn is_constructor(&self, v: &JsValue) -> bool {
        let JsValue::Obj(o) = v else {
            return false;
        };
        match &self.heap.obj(*o).kind {
            // Generator/async functions carry FnFlavor::Normal but are NOT
            // constructors (`new g()` → TypeError).
            ObjKind::Function(FnData::User(uf)) => {
                matches!(uf.flavor, FnFlavor::Normal | FnFlavor::ClassCtor { .. })
                    && !(uf.func.is_gen || uf.func.is_async)
            }
            ObjKind::Function(FnData::Bound(b)) => self.is_constructor(&JsValue::Obj(b.target)),
            // A proxy has a [[Construct]] slot iff its target is a constructor
            // (fixed at creation; the slot persists after revocation).
            ObjKind::Proxy(p) => p.constructor,
            ObjKind::Function(FnData::Native(nf)) => matches!(
                nf,
                NativeFn::ObjectCtor
                    | NativeFn::ArrayCtor
                    | NativeFn::StringCtor
                    | NativeFn::NumberCtor
                    | NativeFn::BooleanCtor
                    | NativeFn::SymbolCtor
                    // BigInt has a [[Construct]] method (IsConstructor is true)
                    // even though `new BigInt` always throws TypeError.
                    | NativeFn::BigIntCtor
                    | NativeFn::ErrorCtor(_)
                    | NativeFn::AggregateErrorCtor
                    | NativeFn::SuppressedErrorCtor
                    | NativeFn::DisposableStackCtor
                    | NativeFn::FunctionCtor
                    | NativeFn::MapCtor
                    | NativeFn::SetCtor
                    | NativeFn::WeakMapCtor
                    | NativeFn::WeakSetCtor
                    | NativeFn::WeakRefCtor
                    | NativeFn::FinalizationRegistryCtor
                    | NativeFn::IteratorCtor
                    | NativeFn::DateWrapperCtor
                    | NativeFn::DateRealCtor
                    | NativeFn::RegExpCtor
                    | NativeFn::ProxyCtor
                    | NativeFn::GeneratorFunctionCtor
                    | NativeFn::AsyncFunctionCtor
                    | NativeFn::AsyncGeneratorFunctionCtor
                    | NativeFn::PromiseCtor
                    | NativeFn::ConsoleWrite { .. }
                    | NativeFn::Print
                    | NativeFn::DateNow
                    | NativeFn::ArrayBufferCtor
                    | NativeFn::DataViewCtor
                    | NativeFn::TypedArrayBaseCtor
                    | NativeFn::TypedArrayCtor(_)
            ),
            _ => false,
        }
    }

    /// SymbolDescriptiveString (20.4.3.3.1).
    pub(crate) fn symbol_descriptive_string(&self, s: SymId) -> Units {
        let mut out = units_from_str("Symbol(");
        if let Some(d) = self.heap.sym_description(s) {
            out.extend_from_slice(&d);
        }
        out.extend_from_slice(&units_from_str(")"));
        out
    }

    pub(crate) fn to_property_key(&mut self, v: &JsValue) -> Result<PropKey, Abrupt> {
        let p = self.to_primitive(v, Hint::String)?;
        if let JsValue::Sym(s) = p {
            return Ok(PropKey::Sym(s));
        }
        Ok(PropKey::Str(self.to_string_units(&p)?))
    }

    pub(crate) fn require_object_coercible(&mut self, v: &JsValue) -> Result<(), Abrupt> {
        if v.is_nullish() {
            Err(self.throw_type_error())
        } else {
            Ok(())
        }
    }

    // -- typeof --------------------------------------------------------------

    pub(crate) fn type_of_value(&self, v: &JsValue) -> &'static str {
        match v {
            JsValue::Undefined => "undefined",
            JsValue::Null => "object",
            JsValue::Bool(_) => "boolean",
            JsValue::Num(_) => "number",
            JsValue::Str(_) => "string",
            JsValue::Sym(_) => "symbol",
            JsValue::BigInt(_) => "bigint",
            JsValue::Obj(id) => {
                if self.heap.obj(*id).is_callable() {
                    "function"
                } else {
                    "object"
                }
            }
        }
    }

    // -- operators -----------------------------------------------------------

    #[allow(clippy::too_many_lines)]
    pub(crate) fn binary_op(&mut self, op: &str, l: &JsValue, r: &JsValue) -> ERes {
        match op {
            "+" => self.op_add(l, r),
            "-" | "*" | "/" | "%" | "**" => {
                let a = self.to_numeric(l)?;
                let b = self.to_numeric(r)?;
                match (a, b) {
                    (Numeric::N(x), Numeric::N(y)) => Ok(JsValue::Num(match op {
                        "-" => x - y,
                        "*" => x * y,
                        "/" => x / y,
                        "%" => x % y,
                        _ => js_exponentiate(x, y),
                    })),
                    (Numeric::B(x), Numeric::B(y)) => {
                        let bop = match op {
                            "-" => BigOp::Sub,
                            "*" => BigOp::Mul,
                            "/" => BigOp::Div,
                            "%" => BigOp::Rem,
                            _ => BigOp::Pow,
                        };
                        self.bigint_result(bigint_binary(bop, &x, &y))
                    }
                    _ => Err(self.throw_type_error()),
                }
            }
            "&" | "|" | "^" => {
                let a = self.to_numeric(l)?;
                let b = self.to_numeric(r)?;
                match (a, b) {
                    (Numeric::N(x), Numeric::N(y)) => {
                        let (x, y) = (to_int32(x), to_int32(y));
                        Ok(JsValue::Num(f64::from(match op {
                            "&" => x & y,
                            "|" => x | y,
                            _ => x ^ y,
                        })))
                    }
                    (Numeric::B(x), Numeric::B(y)) => {
                        let bop = match op {
                            "&" => BigOp::And,
                            "|" => BigOp::Or,
                            _ => BigOp::Xor,
                        };
                        self.bigint_result(bigint_binary(bop, &x, &y))
                    }
                    _ => Err(self.throw_type_error()),
                }
            }
            "<<" | ">>" => {
                let a = self.to_numeric(l)?;
                let b = self.to_numeric(r)?;
                match (a, b) {
                    (Numeric::N(x), Numeric::N(y)) => {
                        let x = to_int32(x);
                        let s = to_uint32(y) % 32;
                        Ok(JsValue::Num(f64::from(if op == "<<" {
                            x.wrapping_shl(s)
                        } else {
                            x.wrapping_shr(s)
                        })))
                    }
                    (Numeric::B(x), Numeric::B(y)) => {
                        let bop = if op == "<<" { BigOp::Shl } else { BigOp::Shr };
                        self.bigint_result(bigint_binary(bop, &x, &y))
                    }
                    _ => Err(self.throw_type_error()),
                }
            }
            ">>>" => {
                let a = self.to_numeric(l)?;
                let b = self.to_numeric(r)?;
                match (a, b) {
                    (Numeric::N(x), Numeric::N(y)) => {
                        let x = to_uint32(x);
                        let s = to_uint32(y) % 32;
                        Ok(JsValue::Num(f64::from(x.wrapping_shr(s))))
                    }
                    // BigInt has no unsigned right shift (and a mixed pair is a
                    // type error either way).
                    _ => Err(self.throw_type_error()),
                }
            }
            "<" | ">" | "<=" | ">=" => {
                // The original LEFT operand is coerced first for all four.
                let pl = self.to_primitive(l, Hint::Number)?;
                let pr = self.to_primitive(r, Hint::Number)?;
                let b = match op {
                    "<" => self.less_than(&pl, &pr)?.unwrap_or(false),
                    ">" => self.less_than(&pr, &pl)?.unwrap_or(false),
                    "<=" => match self.less_than(&pr, &pl)? {
                        None => false,
                        Some(x) => !x,
                    },
                    _ => match self.less_than(&pl, &pr)? {
                        None => false,
                        Some(x) => !x,
                    },
                };
                Ok(JsValue::Bool(b))
            }
            "===" => Ok(JsValue::Bool(strict_eq(l, r))),
            "!==" => Ok(JsValue::Bool(!strict_eq(l, r))),
            "==" => Ok(JsValue::Bool(self.loose_eq(l, r)?)),
            "!=" => Ok(JsValue::Bool(!self.loose_eq(l, r)?)),
            "instanceof" => self.instanceof_operator(l, r),
            "in" => {
                let JsValue::Obj(oid) = r else {
                    return Err(self.throw_type_error());
                };
                let key = self.to_property_key(l)?;
                let oid = *oid;
                Ok(JsValue::Bool(self.has_property(oid, &key)?))
            }
            other => Err(Abrupt::Fatal(format!("binary operator `{other}` (out of slice)"))),
        }
    }

    fn op_add(&mut self, l: &JsValue, r: &JsValue) -> ERes {
        let pl = self.to_primitive(l, Hint::Default)?;
        let pr = self.to_primitive(r, Hint::Default)?;
        if matches!(pl, JsValue::Str(_)) || matches!(pr, JsValue::Str(_)) {
            let mut a = self.to_string_units(&pl)?;
            let b = self.to_string_units(&pr)?;
            if a.len() + b.len() > MAX_STRING_UNITS {
                return Err(Abrupt::Fatal("string concatenation cap exceeded".to_string()));
            }
            a.extend_from_slice(&b);
            return Ok(JsValue::Str(Rc::new(a)));
        }
        // Numeric add: ToNumeric on the already-computed primitives (no second
        // ToPrimitive). Number+Number and BigInt+BigInt only; mixing throws.
        let a = self.to_numeric_of_primitive(&pl)?;
        let b = self.to_numeric_of_primitive(&pr)?;
        match (a, b) {
            (Numeric::N(x), Numeric::N(y)) => Ok(JsValue::Num(x + y)),
            (Numeric::B(x), Numeric::B(y)) => self.bigint_result(bigint_binary(BigOp::Add, &x, &y)),
            _ => Err(self.throw_type_error()),
        }
    }

    /// ToNumeric on a value already known to be primitive (no ToPrimitive).
    pub(crate) fn to_numeric_of_primitive(&mut self, p: &JsValue) -> Result<Numeric, Abrupt> {
        match p {
            JsValue::BigInt(b) => Ok(Numeric::B(Rc::clone(b))),
            other => Ok(Numeric::N(self.to_number(other)?)),
        }
    }

    /// Map a BigInt operation outcome to a value or the exact JS exception.
    pub(crate) fn bigint_result(&mut self, r: Result<JsBigInt, BigErr>) -> ERes {
        match r {
            Ok(b) => Ok(JsValue::bigint(b)),
            Err(BigErr::DivZero | BigErr::NegExponent) => Err(self.throw_native(ErrKind::Range)),
            Err(BigErr::TooLarge) => Err(Abrupt::Fatal(
                "BigInt intermediate exceeds the model size cap (out of slice)".to_string(),
            )),
        }
    }

    /// IsLessThan on primitives (7.2.13); `None` = an incomparable result
    /// (NaN, or an invalid BigInt/String coercion).
    fn less_than(&mut self, px: &JsValue, py: &JsValue) -> Result<Option<bool>, Abrupt> {
        if let (JsValue::Str(a), JsValue::Str(b)) = (px, py) {
            return Ok(Some(a.as_slice() < b.as_slice()));
        }
        // A BigInt against a String parses the String as a BigInt (an invalid
        // parse is incomparable — `undefined`).
        match (px, py) {
            (JsValue::BigInt(x), JsValue::Str(s)) => {
                return Ok(string_to_bigint(s).map(|y| x.as_ref() < &y));
            }
            (JsValue::Str(s), JsValue::BigInt(y)) => {
                return Ok(string_to_bigint(s).map(|x| &x < y.as_ref()));
            }
            _ => {}
        }
        let nx = self.to_numeric_of_primitive(px)?;
        let ny = self.to_numeric_of_primitive(py)?;
        Ok(match (nx, ny) {
            (Numeric::N(x), Numeric::N(y)) => {
                if x.is_nan() || y.is_nan() {
                    None
                } else {
                    Some(x < y)
                }
            }
            (Numeric::B(x), Numeric::B(y)) => Some(x < y),
            (Numeric::B(x), Numeric::N(y)) => {
                bigint_cmp_f64(x.as_ref(), y).map(|o| o == std::cmp::Ordering::Less)
            }
            (Numeric::N(x), Numeric::B(y)) => {
                bigint_cmp_f64(y.as_ref(), x).map(|o| o == std::cmp::Ordering::Greater)
            }
        })
    }

    fn loose_eq(&mut self, l: &JsValue, r: &JsValue) -> Result<bool, Abrupt> {
        match (l, r) {
            (JsValue::Undefined | JsValue::Null, JsValue::Undefined | JsValue::Null) => Ok(true),
            (JsValue::Num(_), JsValue::Num(_))
            | (JsValue::Str(_), JsValue::Str(_))
            | (JsValue::Bool(_), JsValue::Bool(_))
            | (JsValue::Obj(_), JsValue::Obj(_))
            | (JsValue::Sym(_), JsValue::Sym(_)) => Ok(strict_eq(l, r)),
            (JsValue::Num(_), JsValue::Str(_)) => {
                let n = self.to_number(r)?;
                Ok(strict_eq(l, &JsValue::Num(n)))
            }
            (JsValue::Str(_), JsValue::Num(_)) => {
                let n = self.to_number(l)?;
                Ok(strict_eq(&JsValue::Num(n), r))
            }
            (JsValue::Bool(_), _) => {
                let n = self.to_number(l)?;
                self.loose_eq(&JsValue::Num(n), r)
            }
            (_, JsValue::Bool(_)) => {
                let n = self.to_number(r)?;
                self.loose_eq(l, &JsValue::Num(n))
            }
            (JsValue::Num(_) | JsValue::Str(_) | JsValue::Sym(_), JsValue::Obj(_)) => {
                let p = self.to_primitive(r, Hint::Default)?;
                self.loose_eq(l, &p)
            }
            (JsValue::Obj(_), JsValue::Num(_) | JsValue::Str(_) | JsValue::Sym(_)) => {
                let p = self.to_primitive(l, Hint::Default)?;
                self.loose_eq(&p, r)
            }
            (JsValue::BigInt(x), JsValue::BigInt(y)) => Ok(x == y),
            (JsValue::BigInt(x), JsValue::Num(y)) => Ok(bigint_eq_f64(x, *y)),
            (JsValue::Num(x), JsValue::BigInt(y)) => Ok(bigint_eq_f64(y, *x)),
            (JsValue::BigInt(x), JsValue::Str(s)) => {
                Ok(string_to_bigint(s).is_some_and(|y| x.as_ref() == &y))
            }
            (JsValue::Str(s), JsValue::BigInt(y)) => {
                Ok(string_to_bigint(s).is_some_and(|x| &x == y.as_ref()))
            }
            (JsValue::BigInt(_), JsValue::Obj(_)) => {
                let p = self.to_primitive(r, Hint::Default)?;
                self.loose_eq(l, &p)
            }
            (JsValue::Obj(_), JsValue::BigInt(_)) => {
                let p = self.to_primitive(l, Hint::Default)?;
                self.loose_eq(&p, r)
            }
            _ => Ok(false),
        }
    }

    /// InstanceofOperator (13.10.2): GetMethod(target, @@hasInstance) — the
    /// modeled %Function.prototype[Symbol.hasInstance]% or a user handler —
    /// then Call + ToBoolean; without a handler, IsCallable + Ordinary.
    pub(crate) fn instanceof_operator(&mut self, v: &JsValue, target: &JsValue) -> ERes {
        let JsValue::Obj(cid) = target else {
            return Err(self.throw_type_error());
        };
        let key = PropKey::Sym(SymId::WellKnown(WkSym::HasInstance));
        if let Some(h) = self.get_method(target, &key)? {
            let r = self.call_value(&h, target.clone(), vec![v.clone()])?;
            return Ok(JsValue::Bool(self.to_boolean(&r)));
        }
        if !self.heap.obj(*cid).is_callable() {
            return Err(self.throw_type_error());
        }
        Ok(JsValue::Bool(self.ordinary_has_instance(*cid, v)?))
    }

    /// OrdinaryHasInstance (7.3.22).
    pub(crate) fn ordinary_has_instance(
        &mut self,
        cid: trust_js_value::ObjId,
        v: &JsValue,
    ) -> Result<bool, Abrupt> {
        if !self.heap.obj(cid).is_callable() {
            return Ok(false);
        }
        if let ObjKind::Function(FnData::Bound(b)) = &self.heap.obj(cid).kind {
            let target = b.target;
            let r = self.instanceof_operator(v, &JsValue::Obj(target))?;
            return Ok(matches!(r, JsValue::Bool(true)));
        }
        // Step 3: a non-object left operand is `false` BEFORE `prototype` is
        // ever read.
        let JsValue::Obj(mut o) = v.clone() else {
            return Ok(false);
        };
        let proto_v = self.get_prop(&JsValue::Obj(cid), &PropKey::from_str("prototype"))?;
        let JsValue::Obj(proto) = proto_v else {
            return Err(self.throw_type_error());
        };
        let mut hops = 0;
        loop {
            // O.[[GetPrototypeOf]]() — a proxy in the chain traps.
            match self.im_get_prototype_of(o)? {
                None => return Ok(false),
                Some(p) => {
                    if p == proto {
                        return Ok(true);
                    }
                    o = p;
                }
            }
            hops += 1;
            if hops >= 128 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
        }
    }
}

/// Number::exponentiate (6.1.6.1.3) — differs from IEEE `powf` in the
/// NaN-exponent and |base|==1-with-infinite-exponent corners.
#[must_use]
pub fn js_exponentiate(base: f64, exp: f64) -> f64 {
    if exp.is_nan() {
        return f64::NAN;
    }
    if exp == 0.0 {
        return 1.0;
    }
    if base.is_nan() {
        return f64::NAN;
    }
    if (base == 1.0 || base == -1.0) && exp.is_infinite() {
        return f64::NAN;
    }
    base.powf(exp)
}

/// The exact string ToNumber sees. Lone surrogates make a string numerically
/// NaN anyway, and the lossy replacement char is also non-numeric, so the
/// lossy round-trip is exact for ToNumber purposes.
fn units_to_lossy_exactish(u: &[u16]) -> String {
    units_to_lossy(u)
}
