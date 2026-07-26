// Symbol (constructor, registry, prototype), AggregateError, Number statics,
// parseInt/parseFloat (exact rounding or refusal), and the exactly-specified
// Math additions (round/sign/sqrt/imul/clz32/fround) — written from the
// spec. Implementation-approximated Math surface stays danger-listed.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use crate::props::PartialDesc;
use std::rc::Rc;
use trust_js_value::{
    as_int_n, as_uint_n, bigint_to_decimal, bigint_to_radix, f64_to_bigint_exact,
    to_integer_or_infinity, to_int32, to_uint32, units_from_str, ErrKind, JsBigInt, JsValue,
    NativeFn, ObjId, ObjKind, PropKey, Property, SymId, Units, WrapperPrim,
};

impl Interp {
    /// thisSymbolValue: symbol primitives and Symbol wrapper objects.
    fn this_symbol_value(&mut self, this: &JsValue) -> Result<SymId, Abrupt> {
        match this {
            JsValue::Sym(s) => Ok(*s),
            JsValue::Obj(oid) => match &self.heap.obj(*oid).kind {
                ObjKind::Wrapper(WrapperPrim::Sym(s)) => Ok(*s),
                _ => Err(self.throw_type_error()),
            },
            _ => Err(self.throw_type_error()),
        }
    }

    /// thisBigIntValue (21.2.3): BigInt primitives and BigInt wrapper objects.
    fn this_bigint_value(&mut self, this: &JsValue) -> Result<Rc<JsBigInt>, Abrupt> {
        match this {
            JsValue::BigInt(b) => Ok(Rc::clone(b)),
            JsValue::Obj(oid) => match &self.heap.obj(*oid).kind {
                ObjKind::Wrapper(WrapperPrim::BigInt(b)) => Ok(Rc::clone(b)),
                _ => Err(self.throw_type_error()),
            },
            _ => Err(self.throw_type_error()),
        }
    }

    /// The `BigInt(value)` function (21.2.1.1). `new BigInt` throws (handled by
    /// the caller passing `new_target`).
    fn bigint_ctor_call(&mut self, value: &JsValue, new_target: Option<&JsValue>) -> ERes {
        if new_target.is_some() {
            return Err(self.throw_type_error());
        }
        let prim = self.to_primitive(value, crate::ops::Hint::Number)?;
        if let JsValue::Num(n) = prim {
            // NumberToBigInt: an integral Number only, else RangeError.
            return match f64_to_bigint_exact(n) {
                Some(b) => Ok(JsValue::bigint(b)),
                None => Err(self.throw_native(ErrKind::Range)),
            };
        }
        let b = self.to_bigint(&prim)?;
        Ok(JsValue::bigint(b))
    }

    /// BigInt.asIntN(bits, bigint) / asUintN — shared entry.
    fn bigint_as_n(&mut self, signed: bool, bits_v: &JsValue, big_v: &JsValue) -> ERes {
        let bits = self.to_index(bits_v)? as u64;
        let b = self.to_bigint(big_v)?;
        let out = if signed {
            as_int_n(bits, &b)
        } else {
            as_uint_n(bits, &b)
        };
        match out {
            Some(v) => Ok(JsValue::bigint(v)),
            None => Err(Abrupt::Fatal(
                "BigInt.asIntN/asUintN with an astronomically large bit width (out of slice)"
                    .to_string(),
            )),
        }
    }

    /// InstallErrorCause (20.5.8.1).
    pub(crate) fn install_error_cause(&mut self, oid: ObjId, options: &JsValue) -> Result<(), Abrupt> {
        if let JsValue::Obj(opts) = options {
            if self.has_property(*opts, &PropKey::from_str("cause"))? {
                let cause =
                    self.get_from_object(*opts, &PropKey::from_str("cause"), options.clone())?;
                self.heap.obj_mut(oid).props.insert(
                    PropKey::from_str("cause"),
                    Property::with_attrs(cause, true, false, true),
                );
            }
        }
        Ok(())
    }

    /// AggregateError (20.5.7.1.1). Errors iterate via the fast-iterator
    /// discipline only.
    pub(crate) fn aggregate_error_ctor(
        &mut self,
        args: &[JsValue],
        new_target: Option<&JsValue>,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        let default_proto = self.intr.aggregate_error_proto;
        let proto = match new_target {
            Some(ntv) => self.get_prototype_from_constructor(ntv, default_proto)?,
            None => default_proto,
        };
        let oid = self.make_native_error_with_proto(ErrKind::Aggregate, false, proto)?;
        if !matches!(arg(1), JsValue::Undefined) {
            let msg = self.to_string_units(&arg(1))?;
            self.heap.obj_mut(oid).props.insert(
                PropKey::from_str("message"),
                Property::with_attrs(JsValue::Str(Rc::new(msg)), true, false, true),
            );
        }
        self.install_error_cause(oid, &arg(2))?;
        let errors_v = arg(0);
        let mut it = self.get_iterator_or_type_error(&errors_v)?;
        let mut list: Vec<JsValue> = Vec::new();
        while let Some(v) = self.fast_iter_next(&mut it)? {
            self.charge_loop()?;
            list.push(v);
        }
        let len32 = u32::try_from(list.len())
            .map_err(|_| Abrupt::Fatal("AggregateError errors cap exceeded".to_string()))?;
        let arr = self.new_array(len32)?;
        for (i, v) in list.into_iter().enumerate() {
            self.heap.obj_mut(arr).props.insert(
                PropKey::Str(units_from_str(&i.to_string())),
                Property::data(v),
            );
        }
        let ok = self.define_own(
            oid,
            &PropKey::from_str("errors"),
            PartialDesc::full_data(JsValue::Obj(arr), true, false, true),
        )?;
        if !ok {
            return Err(self.throw_type_error());
        }
        Ok(JsValue::Obj(oid))
    }

    #[allow(clippy::too_many_lines)]
    pub(crate) fn dispatch_misc(
        &mut self,
        nf: NativeFn,
        this: JsValue,
        args: Vec<JsValue>,
        new_target: Option<&JsValue>,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        use NativeFn as N;
        match nf {
            N::SymbolCtor => {
                if new_target.is_some() {
                    return Err(self.throw_type_error());
                }
                let desc = match arg(0) {
                    JsValue::Undefined => None,
                    v => Some(self.to_string_units(&v)?),
                };
                Ok(JsValue::Sym(self.heap.alloc_symbol(desc)))
            }
            N::SymbolFor => {
                let key = self.to_string_units(&arg(0))?;
                if let Some((_, s)) = self.sym_registry.iter().find(|(k, _)| *k == key) {
                    return Ok(JsValue::Sym(*s));
                }
                let s = self.heap.alloc_symbol(Some(key.clone()));
                self.sym_registry.push((key, s));
                Ok(JsValue::Sym(s))
            }
            N::SymbolKeyFor => {
                let JsValue::Sym(s) = arg(0) else {
                    return Err(self.throw_type_error());
                };
                match self.sym_registry.iter().find(|(_, rs)| *rs == s) {
                    Some((k, _)) => Ok(JsValue::Str(Rc::new(k.clone()))),
                    None => Ok(JsValue::Undefined),
                }
            }
            N::SymbolProtoToString => {
                let s = self.this_symbol_value(&this)?;
                Ok(JsValue::Str(Rc::new(self.symbol_descriptive_string(s))))
            }
            N::SymbolProtoValueOf | N::SymbolToPrimitive => {
                let s = self.this_symbol_value(&this)?;
                Ok(JsValue::Sym(s))
            }
            N::SymbolProtoDescription => {
                let s = self.this_symbol_value(&this)?;
                Ok(match self.heap.sym_description(s) {
                    Some(d) => JsValue::Str(Rc::new(d)),
                    None => JsValue::Undefined,
                })
            }
            N::BigIntCtor => self.bigint_ctor_call(&arg(0), new_target),
            N::BigIntAsIntN => self.bigint_as_n(true, &arg(0), &arg(1)),
            N::BigIntAsUintN => self.bigint_as_n(false, &arg(0), &arg(1)),
            N::BigIntProtoValueOf => Ok(JsValue::BigInt(self.this_bigint_value(&this)?)),
            N::BigIntProtoToString => {
                let b = self.this_bigint_value(&this)?;
                match arg(0) {
                    JsValue::Undefined => Ok(JsValue::str_from(&bigint_to_decimal(&b))),
                    rv => {
                        let r = to_integer_or_infinity(self.to_number(&rv)?);
                        if !(2.0..=36.0).contains(&r) {
                            return Err(self.throw_native(ErrKind::Range));
                        }
                        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                        let radix = r as u32;
                        if radix == 10 {
                            Ok(JsValue::str_from(&bigint_to_decimal(&b)))
                        } else {
                            Ok(JsValue::str_from(&bigint_to_radix(&b, radix)))
                        }
                    }
                }
            }
            N::NumberIsFinite => Ok(JsValue::Bool(
                matches!(arg(0), JsValue::Num(n) if n.is_finite()),
            )),
            N::NumberIsNaN => Ok(JsValue::Bool(
                matches!(arg(0), JsValue::Num(n) if n.is_nan()),
            )),
            N::NumberIsInteger => Ok(JsValue::Bool(
                matches!(arg(0), JsValue::Num(n) if n.is_finite() && n.trunc() == n),
            )),
            N::NumberIsSafeInteger => Ok(JsValue::Bool(matches!(
                arg(0),
                JsValue::Num(n) if n.is_finite() && n.trunc() == n && n.abs() <= 9_007_199_254_740_991.0
            ))),
            N::ParseInt => {
                let s = self.to_string_units(&arg(0))?;
                let radix = to_int32(self.to_number(&arg(1))?);
                parse_int_exact(&s, radix).map(JsValue::Num).map_err(Abrupt::Fatal)
            }
            N::ParseFloat => {
                let s = self.to_string_units(&arg(0))?;
                Ok(JsValue::Num(parse_float_exact(&s)))
            }
            N::MathRound => {
                let n = self.to_number(&arg(0))?;
                Ok(JsValue::Num(js_math_round(n)))
            }
            N::MathSign => {
                let n = self.to_number(&arg(0))?;
                Ok(JsValue::Num(if n.is_nan() || n == 0.0 {
                    n
                } else if n < 0.0 {
                    -1.0
                } else {
                    1.0
                }))
            }
            N::MathSqrt => {
                // IEEE-exact (correctly rounded on all targets).
                let n = self.to_number(&arg(0))?;
                Ok(JsValue::Num(n.sqrt()))
            }
            N::MathImul => {
                let a = to_uint32(self.to_number(&arg(0))?);
                let b = to_uint32(self.to_number(&arg(1))?);
                let r = a.wrapping_mul(b);
                Ok(JsValue::Num(f64::from(r as i32)))
            }
            N::MathClz32 => {
                let a = to_uint32(self.to_number(&arg(0))?);
                Ok(JsValue::Num(f64::from(a.leading_zeros())))
            }
            N::MathFround => {
                let n = self.to_number(&arg(0))?;
                #[allow(clippy::cast_possible_truncation)]
                Ok(JsValue::Num(f64::from(n as f32)))
            }
            _ => Err(Abrupt::Fatal("unrouted misc native (interpreter bug)".to_string())),
        }
    }
}

/// Math.round (21.3.2.28): ties round toward +∞; never uses `x + 0.5`
/// naively (precision corner: 0.49999999999999994).
fn js_math_round(x: f64) -> f64 {
    if !x.is_finite() || x.trunc() == x {
        return x;
    }
    if x > 0.0 && x < 0.5 {
        return 0.0;
    }
    if x < 0.0 && x >= -0.5 {
        return -0.0;
    }
    let floor = x.floor();
    if x - floor >= 0.5 {
        floor + 1.0
    } else {
        floor
    }
}

/// parseInt (19.2.5), exact: `Err(reason)` = beyond exact accumulation
/// (refuse, never round progressively).
fn parse_int_exact(units: &Units, radix: i32) -> Result<f64, String> {
    // Trim StrWhiteSpace.
    let is_ws = |c: u16| {
        matches!(
            c,
            0x09 | 0x0A | 0x0B | 0x0C | 0x0D | 0x20 | 0xA0 | 0x1680 | 0x2000..=0x200A | 0x2028
                | 0x2029 | 0x202F | 0x205F | 0x3000 | 0xFEFF
        )
    };
    let mut i = 0;
    while i < units.len() && is_ws(units[i]) {
        i += 1;
    }
    let mut sign = 1.0f64;
    if i < units.len() && (units[i] == u16::from(b'+') || units[i] == u16::from(b'-')) {
        if units[i] == u16::from(b'-') {
            sign = -1.0;
        }
        i += 1;
    }
    let mut r = radix;
    let mut strip_prefix = true;
    if r != 0 {
        if !(2..=36).contains(&r) {
            return Ok(f64::NAN);
        }
        if r != 16 {
            strip_prefix = false;
        }
    } else {
        r = 10;
    }
    if strip_prefix
        && i + 1 < units.len()
        && units[i] == u16::from(b'0')
        && (units[i + 1] == u16::from(b'x') || units[i + 1] == u16::from(b'X'))
    {
        i += 2;
        r = 16;
    }
    // Longest digit prefix.
    let digit_of = |c: u16| -> Option<u32> {
        let c = u32::from(c);
        let d = match c {
            0x30..=0x39 => c - 0x30,
            0x41..=0x5A => c - 0x41 + 10,
            0x61..=0x7A => c - 0x61 + 10,
            _ => return None,
        };
        #[allow(clippy::cast_sign_loss)]
        if d < r as u32 {
            Some(d)
        } else {
            None
        }
    };
    let start = i;
    let mut digits: Vec<u32> = Vec::new();
    while i < units.len() {
        match digit_of(units[i]) {
            Some(d) => {
                digits.push(d);
                i += 1;
            }
            None => break,
        }
    }
    if digits.is_empty() {
        let _ = start;
        return Ok(f64::NAN);
    }
    if r == 10 {
        // Correctly rounded via decimal parse (arbitrary length).
        let text: String = digits
            .iter()
            .map(|&d| char::from_digit(d, 10).expect("decimal digit"))
            .collect();
        let mag: f64 = text.parse().map_err(|e| format!("parseInt decimal parse: {e}"))?;
        if mag == 0.0 {
            return Ok(if sign < 0.0 { -0.0 } else { 0.0 });
        }
        return Ok(sign * mag);
    }
    // Non-decimal: exact u128 accumulation, one final rounding.
    let mut acc: u128 = 0;
    for &d in &digits {
        acc = acc
            .checked_mul(u128::from(r as u32))
            .and_then(|a| a.checked_add(u128::from(d)))
            .ok_or_else(|| format!("parseInt radix-{r} literal beyond exact 128-bit accumulation"))?;
    }
    #[allow(clippy::cast_precision_loss)]
    let mag = acc as f64;
    if mag == 0.0 {
        return Ok(if sign < 0.0 { -0.0 } else { 0.0 });
    }
    Ok(sign * mag)
}

/// parseFloat (19.2.4): longest StrDecimalLiteral prefix, correctly rounded.
fn parse_float_exact(units: &Units) -> f64 {
    let is_ws = |c: u16| {
        matches!(
            c,
            0x09 | 0x0A | 0x0B | 0x0C | 0x0D | 0x20 | 0xA0 | 0x1680 | 0x2000..=0x200A | 0x2028
                | 0x2029 | 0x202F | 0x205F | 0x3000 | 0xFEFF
        )
    };
    let mut i = 0;
    while i < units.len() && is_ws(units[i]) {
        i += 1;
    }
    // The remaining prefix must be ASCII to matter; scan the longest valid
    // StrDecimalLiteral shape.
    let b: Vec<u8> = units[i..]
        .iter()
        .take_while(|&&c| c < 0x80)
        .map(|&c| c as u8)
        .collect();
    let mut j = 0usize;
    let mut sign = 1.0f64;
    if j < b.len() && (b[j] == b'+' || b[j] == b'-') {
        if b[j] == b'-' {
            sign = -1.0;
        }
        j += 1;
    }
    if b[j..].starts_with(b"Infinity") {
        return sign * f64::INFINITY;
    }
    let digits_start = j;
    let mut int_digits = 0;
    while j < b.len() && b[j].is_ascii_digit() {
        j += 1;
        int_digits += 1;
    }
    let mut frac_digits = 0;
    let mut end = j;
    if j < b.len() && b[j] == b'.' {
        let mut k = j + 1;
        while k < b.len() && b[k].is_ascii_digit() {
            k += 1;
            frac_digits += 1;
        }
        if int_digits > 0 || frac_digits > 0 {
            j = k;
            end = k;
        }
    } else {
        end = j;
    }
    if int_digits == 0 && frac_digits == 0 {
        return f64::NAN;
    }
    // Optional exponent.
    if j < b.len() && (b[j] == b'e' || b[j] == b'E') {
        let mut k = j + 1;
        if k < b.len() && (b[k] == b'+' || b[k] == b'-') {
            k += 1;
        }
        let exp_start = k;
        while k < b.len() && b[k].is_ascii_digit() {
            k += 1;
        }
        if k > exp_start {
            end = k;
        }
    }
    let text = std::str::from_utf8(&b[digits_start..end]).expect("ascii");
    match text.parse::<f64>() {
        Ok(mag) => sign * mag,
        Err(_) => f64::NAN,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_js_value::units_from_str as u;

    #[test]
    fn parse_int_vectors() {
        assert_eq!(parse_int_exact(&u("42"), 0).unwrap(), 42.0);
        assert_eq!(parse_int_exact(&u("  42abc"), 0).unwrap(), 42.0);
        assert_eq!(parse_int_exact(&u("-0x1F"), 0).unwrap(), -31.0);
        assert_eq!(parse_int_exact(&u("0x10"), 16).unwrap(), 16.0);
        assert_eq!(parse_int_exact(&u("10"), 2).unwrap(), 2.0);
        assert_eq!(parse_int_exact(&u("z"), 36).unwrap(), 35.0);
        assert!(parse_int_exact(&u(""), 0).unwrap().is_nan());
        assert!(parse_int_exact(&u("0x"), 0).unwrap().is_nan());
        assert!(parse_int_exact(&u("42"), 1).unwrap().is_nan());
        assert_eq!(parse_int_exact(&u("-0"), 0).unwrap().to_bits(), (-0.0f64).to_bits());
        assert_eq!(parse_int_exact(&u("08"), 0).unwrap(), 8.0);
        // Long decimal digits round correctly.
        assert_eq!(
            parse_int_exact(&u("123456789012345678901234567890"), 0).unwrap(),
            1.2345678901234568e29
        );
        // Beyond-128-bit binary refuses.
        assert!(parse_int_exact(&u(&format!("1{}", "0".repeat(130))), 2).is_err());
    }

    #[test]
    fn parse_float_vectors() {
        assert_eq!(parse_float_exact(&u("3.14abc")), 3.14);
        assert_eq!(parse_float_exact(&u("  -.5e2xyz")), -50.0);
        assert!(parse_float_exact(&u("abc")).is_nan());
        assert_eq!(parse_float_exact(&u("Infinity!")), f64::INFINITY);
        assert_eq!(parse_float_exact(&u("-Infinity")), f64::NEG_INFINITY);
        assert_eq!(parse_float_exact(&u("1e3")), 1000.0);
        assert_eq!(parse_float_exact(&u("5.")), 5.0);
        assert_eq!(parse_float_exact(&u("1e")), 1.0);
        assert!(parse_float_exact(&u(".e3")).is_nan());
    }

    #[test]
    fn math_round_vectors() {
        assert_eq!(js_math_round(0.5), 1.0);
        assert_eq!(js_math_round(-0.5).to_bits(), (-0.0f64).to_bits());
        assert_eq!(js_math_round(2.5), 3.0);
        assert_eq!(js_math_round(-2.5), -2.0);
        assert_eq!(js_math_round(0.49999999999999994), 0.0);
        assert_eq!(js_math_round(-0.4).to_bits(), (-0.0f64).to_bits());
        assert!(js_math_round(f64::NAN).is_nan());
        assert_eq!(js_math_round(f64::INFINITY), f64::INFINITY);
    }
}
