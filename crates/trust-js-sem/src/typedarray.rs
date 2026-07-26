// The binary-data surface (ECMA-262 §25 ArrayBuffer/DataView, §23.2
// %TypedArray% + the concrete Number typed arrays), written from the spec.
//
// ArrayBuffers own a shared, mutable `Vec<u8>` behind `Rc<RefCell<..>>`; every
// view (typed array / DataView) recomputes its bounds against the buffer's
// CURRENT length on each access, so detach/resize are observed exactly. Typed
// arrays are integer-indexed exotic objects: canonical-numeric-index get/set/
// has/delete/define/ownKeys synthesize element access over the buffer bytes
// (per-element ToNumber coercion — modular wrap for ints, round-half-even for
// Uint8Clamped, round-to-nearest-even for Float32/Float16), out-of-bounds
// reads are `undefined` and writes no-ops, and the accessors/@@toStringTag are
// exact. BigInt64Array/BigUint64Array exist as globals (typeof/harness parity)
// but construction and element ops refuse soundly — the value model has no
// BigInt. Anything outside the modeled slice is a sound `NoCoverage`.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use crate::value::{
    units_from_str, units_to_lossy, BufferData, Builtin, ElementType, NativeErrorKind, ObjId,
    ObjKind, Object, TAMethod, Units, Value,
};
use crate::number::{js_number_to_string, to_number_str};
use std::cell::RefCell;
use std::rc::Rc;

/// Allocation cap (bytes) for one ArrayBuffer: within it we model exactly;
/// beyond it (where a real engine's RangeError-vs-allocate boundary is engine
/// latitude) the case refuses. Keeps the semantics total under adversarial
/// lengths.
pub const MAX_BUFFER_BYTES: usize = 1 << 24; // 16 MiB

// ---------------------------------------------------------------------------
// Numeric conversions (7.1.x) used by element coercion.
// ---------------------------------------------------------------------------

/// ToIntegerOrInfinity (7.1.5) on an already-ToNumber'd value.
#[must_use]
pub fn to_integer_or_infinity(n: f64) -> f64 {
    if n.is_nan() {
        0.0
    } else if n.is_infinite() {
        n
    } else {
        n.trunc()
    }
}

/// Modular reduction to the low `nbytes*8` bits (exact; used by the signed and
/// unsigned integer element writers). NaN/±∞/±0 → 0.
#[must_use]
fn wrap_uint(num: f64, nbytes: usize) -> u64 {
    if !num.is_finite() || num == 0.0 {
        return 0;
    }
    let m = 2f64.powi(8 * i32::try_from(nbytes).expect("nbytes small"));
    let t = num.trunc();
    // fmod is exact for f64, so this is the spec's real-number modulo.
    let r = t.rem_euclid(m);
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    {
        r as u64
    }
}

/// ToUint8Clamp (7.1.11): clamp to [0,255], round half to even.
#[must_use]
fn clamp_uint8(n: f64) -> u8 {
    if n.is_nan() || n <= 0.0 {
        return 0;
    }
    if n >= 255.0 {
        return 255;
    }
    let f = n.floor();
    let diff = n - f;
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let fi = f as u64;
    let r = if diff < 0.5 {
        f
    } else if diff > 0.5 {
        f + 1.0
    } else if fi % 2 == 0 {
        f
    } else {
        f + 1.0
    };
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    {
        r as u8
    }
}

/// IEEE-754 binary16 decode.
#[must_use]
pub fn f16_bits_to_f64(bits: u16) -> f64 {
    let sign = (bits >> 15) & 1;
    let exp = (bits >> 10) & 0x1f;
    let mant = bits & 0x3ff;
    let val = if exp == 0 {
        f64::from(mant) * 2f64.powi(-24)
    } else if exp == 0x1f {
        if mant == 0 {
            f64::INFINITY
        } else {
            f64::NAN
        }
    } else {
        (1.0 + f64::from(mant) / 1024.0) * 2f64.powi(i32::from(exp) - 15)
    };
    if sign == 1 {
        -val
    } else {
        val
    }
}

/// Round-to-nearest-even f64 → IEEE-754 binary16 bits.
#[must_use]
pub fn f64_to_f16_bits(x: f64) -> u16 {
    if x.is_nan() {
        return 0x7e00; // canonical qNaN
    }
    let sign: u16 = if x.is_sign_negative() { 0x8000 } else { 0 };
    let a = x.abs();
    if a.is_infinite() || a >= 65520.0 {
        return sign | 0x7c00; // round-to-inf threshold is 65520
    }
    if a == 0.0 {
        return sign;
    }
    let bits = a.to_bits();
    let e = ((bits >> 52) & 0x7ff) as i32 - 1023;
    let sig = (1u64 << 52) | (bits & ((1u64 << 52) - 1)); // 53-bit significand

    if e >= -14 {
        // Normal half range (overflow past 15 already handled by 65520 gate).
        let round = round_shift(sig, 42); // 53-bit → 11-bit significand
        let (mantissa, exp_half) = if round == (1u64 << 11) {
            (1u64 << 10, e + 1) // carry
        } else {
            (round, e)
        };
        if exp_half > 15 {
            return sign | 0x7c00;
        }
        #[allow(clippy::cast_possible_truncation)]
        let stored_mant = (mantissa & ((1u64 << 10) - 1)) as u16;
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        let stored_exp = ((exp_half + 15) as u16) << 10;
        sign | stored_exp | stored_mant
    } else {
        // Subnormal / underflow: value = mant10 * 2^-24.
        let shift = 28 - e; // e <= -15 => shift >= 43
        if shift >= 64 {
            return sign;
        }
        #[allow(clippy::cast_sign_loss)]
        let round = round_shift(sig, shift as u32);
        if round == 0 {
            return sign;
        }
        if round >= (1u64 << 10) {
            // rounded up into the smallest normal
            #[allow(clippy::cast_possible_truncation)]
            let stored_mant = (round & ((1u64 << 10) - 1)) as u16;
            return sign | (1u16 << 10) | stored_mant;
        }
        #[allow(clippy::cast_possible_truncation)]
        {
            sign | (round as u16)
        }
    }
}

/// Shift `sig` right by `shift`, rounding to nearest, ties to even.
#[must_use]
fn round_shift(sig: u64, shift: u32) -> u64 {
    if shift == 0 {
        return sig;
    }
    if shift >= 64 {
        return 0;
    }
    let keep = sig >> shift;
    let rem = sig & ((1u64 << shift) - 1);
    let half = 1u64 << (shift - 1);
    if rem > half || (rem == half && (keep & 1) == 1) {
        keep + 1
    } else {
        keep
    }
}

fn bytes_to_u64(b: &[u8], le: bool) -> u64 {
    let mut v: u64 = 0;
    if le {
        for (i, &byte) in b.iter().enumerate() {
            v |= u64::from(byte) << (8 * i);
        }
    } else {
        for &byte in b {
            v = (v << 8) | u64::from(byte);
        }
    }
    v
}

fn u64_to_bytes(v: u64, n: usize, le: bool, out: &mut [u8]) {
    for i in 0..n {
        #[allow(clippy::cast_possible_truncation)]
        let byte = ((v >> (8 * i)) & 0xff) as u8;
        if le {
            out[i] = byte;
        } else {
            out[n - 1 - i] = byte;
        }
    }
}

/// GetValueFromBuffer over raw bytes: decode `elem` at `bi` (byte index),
/// endianness `le`. Panics never (caller guarantees `bi+size <= bytes.len()`).
#[must_use]
pub fn read_element(bytes: &[u8], bi: usize, elem: ElementType, le: bool) -> f64 {
    let n = elem.bytes();
    let v = bytes_to_u64(&bytes[bi..bi + n], le);
    match elem {
        #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
        ElementType::Int8 => f64::from(v as u8 as i8),
        #[allow(clippy::cast_possible_truncation)]
        ElementType::Uint8 | ElementType::Uint8Clamped => f64::from(v as u8),
        #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
        ElementType::Int16 => f64::from(v as u16 as i16),
        #[allow(clippy::cast_possible_truncation)]
        ElementType::Uint16 => f64::from(v as u16),
        #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
        ElementType::Int32 => f64::from(v as u32 as i32),
        #[allow(clippy::cast_possible_truncation)]
        ElementType::Uint32 => f64::from(v as u32),
        #[allow(clippy::cast_possible_truncation)]
        ElementType::Float16 => f16_bits_to_f64(v as u16),
        #[allow(clippy::cast_possible_truncation)]
        ElementType::Float32 => f64::from(f32::from_bits(v as u32)),
        ElementType::Float64 => f64::from_bits(v),
        // BigInt element types never reach here (construction/access refused).
        ElementType::BigInt64 | ElementType::BigUint64 => f64::NAN,
    }
}

/// SetValueInBuffer: encode `num` as `elem` at `bi`, endianness `le`.
pub fn write_element(bytes: &mut [u8], bi: usize, elem: ElementType, num: f64, le: bool) {
    let n = elem.bytes();
    let raw: u64 = match elem {
        ElementType::Int8 | ElementType::Uint8 => wrap_uint(num, 1),
        ElementType::Uint8Clamped => u64::from(clamp_uint8(num)),
        ElementType::Int16 | ElementType::Uint16 => wrap_uint(num, 2),
        ElementType::Int32 | ElementType::Uint32 => wrap_uint(num, 4),
        ElementType::Float16 => u64::from(f64_to_f16_bits(num)),
        #[allow(clippy::cast_possible_truncation)]
        ElementType::Float32 => u64::from((num as f32).to_bits()),
        ElementType::Float64 => num.to_bits(),
        ElementType::BigInt64 | ElementType::BigUint64 => 0,
    };
    let mut out = [0u8; 8];
    u64_to_bytes(raw, n, le, &mut out);
    bytes[bi..bi + n].copy_from_slice(&out[..n]);
}

/// GetValueFromBuffer for the BigInt element types: decode 8 bytes as a signed
/// (BigInt64) or unsigned (BigUint64) 64-bit integer.
#[must_use]
pub fn read_element_big(bytes: &[u8], bi: usize, elem: ElementType, le: bool) -> num_bigint::BigInt {
    let v = bytes_to_u64(&bytes[bi..bi + 8], le);
    match elem {
        #[allow(clippy::cast_possible_wrap)]
        ElementType::BigInt64 => num_bigint::BigInt::from(v as i64),
        _ => num_bigint::BigInt::from(v),
    }
}

/// SetValueInBuffer for the BigInt element types: store the low 64 bits of the
/// (already ToBigInt'd) value.
pub fn write_element_big(bytes: &mut [u8], bi: usize, big: &num_bigint::BigInt, le: bool) {
    let raw = crate::bigint::to_u64_wrapping(big);
    let mut out = [0u8; 8];
    u64_to_bytes(raw, 8, le, &mut out);
    bytes[bi..bi + 8].copy_from_slice(&out);
}

/// CanonicalNumericIndexString (7.1.21): `Some(n)` iff `key` is "-0" or the
/// canonical Number::toString of some number.
#[must_use]
pub fn canonical_numeric_index(key: &[u16]) -> Option<f64> {
    if crate::value::units_eq_ascii(key, "-0") {
        return Some(-0.0);
    }
    let s = units_to_lossy(key);
    let n = to_number_str(&s).ok()?;
    if js_number_to_string(n) == s {
        Some(n)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Interp methods: element access + keys.
// ---------------------------------------------------------------------------

/// A typed array's structural fields, extracted from its ObjKind.
#[derive(Clone, Copy)]
pub(crate) struct TaFields {
    pub buffer: ObjId,
    pub byte_offset: usize,
    pub length: usize,
    pub elem: ElementType,
}

impl Interp {
    pub(crate) fn ta_fields(&self, oid: ObjId) -> Option<TaFields> {
        match self.obj(oid).kind {
            ObjKind::TypedArray {
                buffer,
                byte_offset,
                length,
                elem,
            } => Some(TaFields {
                buffer,
                byte_offset,
                length,
                elem,
            }),
            _ => None,
        }
    }

    /// The `Rc` to a buffer's byte storage (clone of the shared handle).
    pub(crate) fn buffer_rc(&self, buf: ObjId) -> Option<Rc<RefCell<BufferData>>> {
        match &self.obj(buf).kind {
            ObjKind::ArrayBuffer(d) => Some(Rc::clone(d)),
            _ => None,
        }
    }

    /// Is the typed array out of bounds (detached buffer, or a resizable buffer
    /// shrank below the view's extent)? Out-of-bounds views report length 0 and
    /// every element access is `undefined`/no-op.
    pub(crate) fn ta_out_of_bounds(&self, f: TaFields) -> bool {
        let Some(rc) = self.buffer_rc(f.buffer) else {
            return true;
        };
        let d = rc.borrow();
        if d.detached {
            return true;
        }
        f.byte_offset + f.length * f.elem.bytes() > d.bytes.len()
    }

    /// IsValidIntegerIndex (23.2.3.24 helper): the element index if `n` is a
    /// valid, in-bounds integer index for the typed array.
    pub(crate) fn ta_valid_index(&self, f: TaFields, n: f64) -> Option<usize> {
        if n.trunc() != n || (n == 0.0 && n.is_sign_negative()) {
            return None; // non-integral or -0
        }
        if n < 0.0 || n >= f.length as f64 {
            return None;
        }
        if self.ta_out_of_bounds(f) {
            return None;
        }
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        Some(n as usize)
    }

    /// IntegerIndexedElementGet: the element value, or `undefined`.
    pub(crate) fn ta_element_get(&self, oid: ObjId, n: f64) -> Value {
        let Some(f) = self.ta_fields(oid) else {
            return Value::Undefined;
        };
        let Some(i) = self.ta_valid_index(f, n) else {
            return Value::Undefined;
        };
        let Some(rc) = self.buffer_rc(f.buffer) else {
            return Value::Undefined;
        };
        let d = rc.borrow();
        let bi = f.byte_offset + i * f.elem.bytes();
        if f.elem.is_bigint() {
            Value::bigint(read_element_big(&d.bytes, bi, f.elem, true))
        } else {
            Value::Num(read_element(&d.bytes, bi, f.elem, true))
        }
    }

    /// Coerce a value to the element type: ToBigInt for BigInt64/BigUint64,
    /// ToNumber otherwise (23.2.5.1 IntegerIndexedElementSet step "value" —
    /// runs unconditionally, so side effects are observable before the store).
    pub(crate) fn ta_coerce_elem(
        &mut self,
        elem: ElementType,
        value: &Value,
    ) -> Result<Value, Abrupt> {
        if elem.is_bigint() {
            Ok(Value::bigint(self.to_bigint(value)?))
        } else {
            Ok(Value::Num(self.to_number(value)?))
        }
    }

    /// IntegerIndexedElementSet: the type-appropriate coercion (ToNumber /
    /// ToBigInt) runs unconditionally (side effects observable); the store
    /// happens only for a valid in-bounds index.
    pub(crate) fn ta_element_set(&mut self, oid: ObjId, n: f64, value: Value) -> Result<(), Abrupt> {
        let f = self.ta_fields(oid).expect("typed array");
        let coerced = self.ta_coerce_elem(f.elem, &value)?;
        if let Some(i) = self.ta_valid_index(f, n) {
            if let Some(rc) = self.buffer_rc(f.buffer) {
                let mut d = rc.borrow_mut();
                let bi = f.byte_offset + i * f.elem.bytes();
                match coerced {
                    Value::BigInt(b) => write_element_big(&mut d.bytes, bi, &b, true),
                    Value::Num(num) => write_element(&mut d.bytes, bi, f.elem, num, true),
                    _ => unreachable!("ta_coerce_elem yields Num or BigInt"),
                }
            }
        }
        Ok(())
    }

    /// The current element count (0 if detached/out-of-bounds).
    pub(crate) fn ta_length(&self, f: TaFields) -> usize {
        if self.ta_out_of_bounds(f) {
            0
        } else {
            f.length
        }
    }

    /// The in-bounds element index strings, "0".."len-1" (empty if
    /// detached/out-of-bounds). Used by ownKeys / projection / Object.keys.
    pub(crate) fn ta_index_keys(&self, oid: ObjId) -> Vec<Units> {
        let Some(f) = self.ta_fields(oid) else {
            return Vec::new();
        };
        (0..self.ta_length(f))
            .map(|i| units_from_str(&i.to_string()))
            .collect()
    }

    /// IntegerIndexedDefineOwnProperty (23.2.3.x): a valid in-bounds data
    /// write succeeds; attribute/accessor changes and out-of-range canonical
    /// indices are rejected; non-numeric keys are ordinary.
    pub(crate) fn ta_define_own(
        &mut self,
        oid: ObjId,
        key: &Units,
        desc: &crate::value::PropDesc,
    ) -> Result<bool, Abrupt> {
        if let Some(n) = canonical_numeric_index(key) {
            let f = self.ta_fields(oid).expect("typed array");
            if self.ta_valid_index(f, n).is_none() {
                return Ok(false);
            }
            if desc.configurable == Some(false)
                || desc.enumerable == Some(false)
                || desc.is_accessor()
                || desc.writable == Some(false)
            {
                return Ok(false);
            }
            if let Some(v) = &desc.value {
                self.ta_element_set(oid, n, v.clone())?;
            }
            return Ok(true);
        }
        self.ordinary_define_own(oid, key, desc)
    }

    /// Own keys in spec order for any object: for a typed array the element
    /// indices ascend first, then the ordinary string keys; otherwise the
    /// ordinary key order.
    pub(crate) fn ordered_own_keys_full(&self, oid: ObjId) -> Vec<Units> {
        if matches!(self.obj(oid).kind, ObjKind::TypedArray { .. }) {
            let mut keys = self.ta_index_keys(oid);
            keys.extend(crate::value::ordered_own_keys(self.obj(oid)));
            keys
        } else {
            crate::value::ordered_own_keys(self.obj(oid))
        }
    }
}

// ---------------------------------------------------------------------------
// Allocation + `this` validation helpers.
// ---------------------------------------------------------------------------

impl Interp {
    /// Allocate a fresh ArrayBuffer object with `len` zero bytes.
    pub(crate) fn alloc_buffer(&mut self, len: usize, max: Option<usize>) -> ObjId {
        let data = Rc::new(RefCell::new(BufferData {
            bytes: vec![0u8; len],
            detached: false,
            max_byte_length: max,
        }));
        self.alloc(Object::new(
            ObjKind::ArrayBuffer(data),
            Some(self.intr.arraybuffer_proto),
        ))
    }

    /// Allocate a typed-array object of `elem` over `buffer`.
    pub(crate) fn make_typed_array(
        &mut self,
        elem: ElementType,
        buffer: ObjId,
        byte_offset: usize,
        length: usize,
        proto: ObjId,
    ) -> ObjId {
        self.alloc(Object::new(
            ObjKind::TypedArray {
                buffer,
                byte_offset,
                length,
                elem,
            },
            Some(proto),
        ))
    }

    fn require_typed_array(&mut self, this: &Value) -> Result<ObjId, Abrupt> {
        match this {
            Value::Obj(o) if matches!(self.obj(*o).kind, ObjKind::TypedArray { .. }) => Ok(*o),
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    fn require_array_buffer(&mut self, this: &Value) -> Result<ObjId, Abrupt> {
        match this {
            Value::Obj(o) if matches!(self.obj(*o).kind, ObjKind::ArrayBuffer(_)) => Ok(*o),
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    fn require_data_view(&mut self, this: &Value) -> Result<ObjId, Abrupt> {
        match this {
            Value::Obj(o) if matches!(self.obj(*o).kind, ObjKind::DataView { .. }) => Ok(*o),
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    /// ToIndex (7.1.22): a non-negative integer index, RangeError otherwise.
    fn to_index(&mut self, v: &Value) -> Result<usize, Abrupt> {
        let n = self.to_number(v)?;
        let i = to_integer_or_infinity(n);
        if i < 0.0 || i > 9_007_199_254_740_991.0 {
            return Err(self.throw_native(NativeErrorKind::RangeError));
        }
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        Ok(i as usize)
    }

    // -- ArrayBuffer construction (25.1.4) ----------------------------------

    pub(crate) fn arraybuffer_construct(&mut self, args: &[Value], is_new: bool) -> ERes {
        if !is_new {
            // Called without new → TypeError (25.1.4.1 step 1).
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        let byte_length = self.to_index(&arg(0))?;
        // GetArrayBufferMaxByteLengthOption (25.1.4.2).
        let max = match arg(1) {
            Value::Obj(opts) => {
                let mv = self.get_from_object(opts, &units_from_str("maxByteLength"))?;
                match mv {
                    Value::Undefined => None,
                    v => Some(self.to_index(&v)?),
                }
            }
            _ => None,
        };
        if let Some(m) = max {
            if byte_length > m {
                return Err(self.throw_native(NativeErrorKind::RangeError));
            }
            if m > MAX_BUFFER_BYTES {
                return Err(Abrupt::Fatal(
                    "resizable ArrayBuffer maxByteLength beyond modeled cap".to_string(),
                ));
            }
        }
        if byte_length > MAX_BUFFER_BYTES {
            return Err(Abrupt::Fatal(
                "ArrayBuffer allocation beyond modeled cap".to_string(),
            ));
        }
        let proto = self.new_target_proto(self.intr.arraybuffer_proto)?;
        let buf = self.alloc_buffer(byte_length, max);
        self.obj_mut(buf).proto = Some(proto);
        Ok(Value::Obj(buf))
    }

    /// OrdinaryCreateFromConstructor prototype resolution, honoring a foreign
    /// new.target threaded through `pending_new_target` (subclassing).
    fn new_target_proto(&mut self, default_proto: ObjId) -> Result<ObjId, Abrupt> {
        if let Some(nt) = self.pending_new_target.take() {
            self.proto_from_new_target(nt, default_proto)
        } else {
            Ok(default_proto)
        }
    }

    // -- DataView construction (25.3.2) -------------------------------------

    pub(crate) fn dataview_construct(&mut self, args: &[Value], is_new: bool) -> ERes {
        if !is_new {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        let buffer = self.require_array_buffer(&arg(0))?;
        let offset = self.to_index(&arg(1))?;
        let rc = self.buffer_rc(buffer).expect("array buffer");
        let (detached, buf_len, resizable) = {
            let d = rc.borrow();
            (d.detached, d.bytes.len(), d.max_byte_length.is_some())
        };
        if detached {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        if offset > buf_len {
            return Err(self.throw_native(NativeErrorKind::RangeError));
        }
        let byte_length = match arg(2) {
            Value::Undefined => {
                if resizable {
                    return Err(Abrupt::Fatal(
                        "length-tracking DataView on a resizable buffer (out of slice)".to_string(),
                    ));
                }
                buf_len - offset
            }
            v => {
                let vl = self.to_index(&v)?;
                if offset + vl > buf_len {
                    return Err(self.throw_native(NativeErrorKind::RangeError));
                }
                vl
            }
        };
        let proto = self.new_target_proto(self.intr.dataview_proto)?;
        let dv = self.alloc(Object::new(
            ObjKind::DataView {
                buffer,
                byte_offset: offset,
                byte_length,
            },
            Some(proto),
        ));
        Ok(Value::Obj(dv))
    }

    // -- TypedArray construction (23.2.5.1) ---------------------------------

    pub(crate) fn typedarray_construct(
        &mut self,
        elem: ElementType,
        args: &[Value],
        is_new: bool,
    ) -> ERes {
        if !is_new {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let proto = self.new_target_proto(self.intr.ta_proto(elem))?;
        let arg0 = args.first().cloned().unwrap_or(Value::Undefined);
        match &arg0 {
            Value::Obj(src) => {
                let src = *src;
                match &self.obj(src).kind {
                    ObjKind::ArrayBuffer(_) => {
                        self.ta_from_buffer(elem, src, args, proto)
                    }
                    ObjKind::TypedArray { .. } => self.ta_from_typed_array(elem, src, proto),
                    _ => self.ta_from_object(elem, &arg0, proto),
                }
            }
            // Length case: ToIndex(arg0) elements (undefined → 0).
            _ => {
                let len = self.to_index(&arg0)?;
                self.ta_allocate(elem, len, proto)
            }
        }
    }

    /// AllocateTypedArray with a fresh zero buffer of `len` elements.
    fn ta_allocate(&mut self, elem: ElementType, len: usize, proto: ObjId) -> ERes {
        let byte_len = len.checked_mul(elem.bytes()).ok_or_else(|| {
            Abrupt::Fatal("typed-array byte length overflow".to_string())
        })?;
        if byte_len > MAX_BUFFER_BYTES {
            return Err(Abrupt::Fatal(
                "typed-array allocation beyond modeled cap".to_string(),
            ));
        }
        let buf = self.alloc_buffer(byte_len, None);
        let ta = self.make_typed_array(elem, buf, 0, len, proto);
        Ok(Value::Obj(ta))
    }

    /// InitializeTypedArrayFromArrayBuffer (23.2.5.1.3).
    fn ta_from_buffer(
        &mut self,
        elem: ElementType,
        buffer: ObjId,
        args: &[Value],
        proto: ObjId,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        let bytes = elem.bytes();
        let offset = self.to_index(&arg(1))?;
        if offset % bytes != 0 {
            return Err(self.throw_native(NativeErrorKind::RangeError));
        }
        let rc = self.buffer_rc(buffer).expect("buffer");
        let (detached, buf_len, resizable) = {
            let d = rc.borrow();
            (d.detached, d.bytes.len(), d.max_byte_length.is_some())
        };
        if detached {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let length = match arg(2) {
            Value::Undefined => {
                if resizable {
                    return Err(Abrupt::Fatal(
                        "length-tracking typed array on a resizable buffer (out of slice)"
                            .to_string(),
                    ));
                }
                if buf_len % bytes != 0 {
                    return Err(self.throw_native(NativeErrorKind::RangeError));
                }
                if offset > buf_len {
                    return Err(self.throw_native(NativeErrorKind::RangeError));
                }
                (buf_len - offset) / bytes
            }
            v => {
                let n = self.to_index(&v)?;
                if offset + n * bytes > buf_len {
                    return Err(self.throw_native(NativeErrorKind::RangeError));
                }
                n
            }
        };
        let ta = self.make_typed_array(elem, buffer, offset, length, proto);
        Ok(Value::Obj(ta))
    }

    /// InitializeTypedArrayFromTypedArray (23.2.5.1.2): a fresh buffer, element
    /// by element (with conversion).
    fn ta_from_typed_array(&mut self, elem: ElementType, src: ObjId, proto: ObjId) -> ERes {
        let sf = self.ta_fields(src).expect("typed array");
        // Content-type mismatch (exactly one side is BigInt) is a TypeError
        // (23.2.5.1.2 step 18).
        if sf.elem.is_bigint() != elem.is_bigint() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let len = self.ta_length(sf);
        let Value::Obj(dest) = self.ta_allocate(elem, len, proto)? else {
            unreachable!("ta_allocate yields an object");
        };
        for i in 0..len {
            #[allow(clippy::cast_precision_loss)]
            let v = self.ta_element_get(src, i as f64);
            #[allow(clippy::cast_precision_loss)]
            self.ta_element_set(dest, i as f64, v)?;
        }
        Ok(Value::Obj(dest))
    }

    /// InitializeTypedArrayFromList / FromArrayLike (23.2.5.1.4/5): the iterable
    /// path when @@iterator is present, else the array-like path.
    fn ta_from_object(&mut self, elem: ElementType, src: &Value, proto: ObjId) -> ERes {
        let sid = self.intr.wk(crate::builtins::WK_ITERATOR);
        if self.get_method_symbol(src, sid)?.is_some() {
            // Iterable path: collect values via the provably-intrinsic driver.
            let mut it = self.slice_iterator(src)?;
            let mut vals: Vec<Value> = Vec::new();
            while let Some(v) = self.slice_iter_next(&mut it)? {
                vals.push(v);
                if vals.len() > MAX_BUFFER_BYTES {
                    return Err(Abrupt::Fatal("typed-array iterable too long".to_string()));
                }
            }
            let len = vals.len();
            let Value::Obj(dest) = self.ta_allocate(elem, len, proto)? else {
                unreachable!();
            };
            for (i, v) in vals.into_iter().enumerate() {
                #[allow(clippy::cast_precision_loss)]
                self.ta_element_set(dest, i as f64, v)?;
            }
            return Ok(Value::Obj(dest));
        }
        // Array-like path.
        let Value::Obj(so) = src else {
            unreachable!("object source");
        };
        let so = *so;
        let len_v = self.get_from_object(so, &units_from_str("length"))?;
        let len = usize::try_from(crate::builtins::to_length_u64(self.to_number(&len_v)?))
            .map_err(|_| Abrupt::Fatal("array-like length beyond modeled cap".to_string()))?;
        let Value::Obj(dest) = self.ta_allocate(elem, len, proto)? else {
            unreachable!();
        };
        for i in 0..len {
            let v = self.get_from_object(so, &units_from_str(&i.to_string()))?;
            #[allow(clippy::cast_precision_loss)]
            self.ta_element_set(dest, i as f64, v)?;
        }
        Ok(Value::Obj(dest))
    }

    /// TypedArrayCreate(C, [len]) (23.2.4.2): Construct(C, [len]), then
    /// ValidateTypedArray the result and require its [[ArrayLength]] to be at
    /// least the requested `len` (steps 2-3). A constructor that yields a
    /// non-typed-array is out of slice (a sound refusal); a detached/out-of-
    /// bounds result, or one SHORTER than requested (a custom constructor
    /// returning a smaller instance), is a TypeError.
    fn typed_array_create_len(&mut self, c: &Value, len: u64) -> Result<ObjId, Abrupt> {
        #[allow(clippy::cast_precision_loss)]
        let target = self.construct(c, vec![Value::Num(len as f64)])?;
        let Value::Obj(t) = target else {
            return Err(Abrupt::Fatal(
                "%TypedArray% create: construct did not yield an object".to_string(),
            ));
        };
        // ValidateTypedArray: the result must be a typed array with a live,
        // in-bounds buffer.
        let Some(f) = self.ta_fields(t) else {
            return Err(Abrupt::Fatal(
                "%TypedArray%.from/of on a non-typed-array constructor (out of slice)".to_string(),
            ));
        };
        if self.ta_out_of_bounds(f) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        // Step 3: a single Number argument requires the returned length to be
        // >= the requested length (a custom constructor returning a smaller
        // instance throws TypeError).
        if (self.ta_length(f) as u64) < len {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        Ok(t)
    }

    /// %TypedArray%.of (23.2.2.2): the argument list → a fresh typed array of
    /// the receiver's element type, each element Set (coerced) in turn.
    fn typed_array_of(&mut self, this: Value, args: &[Value]) -> ERes {
        let Value::Obj(c) = &this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        if !self.is_constructor(*c) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let len = args.len() as u64;
        let t = self.typed_array_create_len(&this, len)?;
        for (k, item) in args.iter().enumerate() {
            #[allow(clippy::cast_precision_loss)]
            self.ta_element_set(t, k as f64, item.clone())?;
        }
        Ok(Value::Obj(t))
    }

    /// %TypedArray%.from (23.2.2.1): iterable or array-like `source` → a fresh
    /// typed array of the receiver's element type, with an optional mapFn/
    /// thisArg. The iterable path collects the full list (IterableToList) before
    /// allocating; the array-like path reads length + indices.
    fn typed_array_from(&mut self, this: Value, args: &[Value]) -> ERes {
        let Value::Obj(c) = &this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        if !self.is_constructor(*c) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let source = args.first().cloned().unwrap_or(Value::Undefined);
        let map_fn = args.get(1).cloned().unwrap_or(Value::Undefined);
        let this_arg = args.get(2).cloned().unwrap_or(Value::Undefined);
        let mapping = if matches!(map_fn, Value::Undefined) {
            false
        } else {
            if !matches!(&map_fn, Value::Obj(o) if self.obj(*o).is_callable()) {
                return Err(self.throw_native(NativeErrorKind::TypeError));
            }
            true
        };
        let iter_sid = self.intr.wk(crate::builtins::WK_ITERATOR);
        let using = self.get_method_symbol(&source, iter_sid)?;
        if using.is_some() {
            // Iterable path: IterableToList, then allocate, then Set each
            // (the current spec collects the full list BEFORE any element is
            // coerced/set). V8 keeps a legacy optimization that reads an ARRAY
            // source LAZILY during the set loop, so when user code runs there
            // (a mapFn, or ToNumber of an object element via valueOf/
            // @@toPrimitive) and mutates the source, V8 diverges from the
            // collect-first spec. That corner is engine-divergent, so refuse
            // it soundly; a primitive-only source with no mapFn runs no user
            // code during the set loop and is order-independent (exact).
            let mut it = self.slice_iterator(&source)?;
            let mut vals: Vec<Value> = Vec::new();
            loop {
                self.charge_loop()?;
                let Some(v) = self.slice_iter_next(&mut it)? else {
                    break;
                };
                vals.push(v);
            }
            if mapping || vals.iter().any(|v| matches!(v, Value::Obj(_))) {
                return Err(Abrupt::Fatal(
                    "%TypedArray%.from iterable path with a mapFn or object element \
                     (collect-first vs engine lazy-read is engine-divergent, out of slice)"
                        .to_string(),
                ));
            }
            let len = vals.len() as u64;
            let t = self.typed_array_create_len(&this, len)?;
            for (k, v) in vals.into_iter().enumerate() {
                #[allow(clippy::cast_precision_loss)]
                let mapped = if mapping {
                    self.call_value(&map_fn, this_arg.clone(), vec![v, Value::Num(k as f64)])?
                } else {
                    v
                };
                #[allow(clippy::cast_precision_loss)]
                self.ta_element_set(t, k as f64, mapped)?;
            }
            Ok(Value::Obj(t))
        } else {
            // Array-like path: ToObject(source), read length + indices 0..len.
            let obj = match &source {
                Value::Undefined | Value::Null => {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                Value::Obj(o) => *o,
                prim => self.to_object_wrapper(prim)?,
            };
            let len_v = self.get_from_object(obj, &units_from_str("length"))?;
            let len = crate::builtins::to_length_u64(self.to_number(&len_v)?);
            let t = self.typed_array_create_len(&this, len)?;
            let mut k: u64 = 0;
            while k < len {
                self.charge_loop()?;
                let kv = self.get_from_object(obj, &units_from_str(&k.to_string()))?;
                #[allow(clippy::cast_precision_loss)]
                let mapped = if mapping {
                    self.call_value(&map_fn, this_arg.clone(), vec![kv, Value::Num(k as f64)])?
                } else {
                    kv
                };
                #[allow(clippy::cast_precision_loss)]
                self.ta_element_set(t, k as f64, mapped)?;
                k += 1;
            }
            Ok(Value::Obj(t))
        }
    }
}

// ---------------------------------------------------------------------------
// Accessor getters + methods + the dispatch entry.
// ---------------------------------------------------------------------------

impl Interp {
    /// Snapshot the current element values of a typed array.
    fn ta_snapshot(&self, oid: ObjId) -> Vec<f64> {
        let Some(f) = self.ta_fields(oid) else {
            return Vec::new();
        };
        let len = self.ta_length(f);
        let Some(rc) = self.buffer_rc(f.buffer) else {
            return Vec::new();
        };
        let d = rc.borrow();
        (0..len)
            .map(|i| read_element(&d.bytes, f.byte_offset + i * f.elem.bytes(), f.elem, true))
            .collect()
    }

    /// SpeciesConstructor default check: Ok(elem) iff `oid`'s constructor and
    /// @@species are the untampered intrinsics; refuse otherwise.
    fn ta_default_species(&mut self, oid: ObjId) -> Result<ElementType, Abrupt> {
        let elem = self.ta_fields(oid).expect("typed array").elem;
        let expected = self.intr.ta_ctor(elem);
        let ctor_v = self.get_from_object(oid, &units_from_str("constructor"))?;
        if !matches!(ctor_v, Value::Obj(c) if c == expected) {
            return Err(Abrupt::Fatal(
                "typed-array method with a non-default @@species constructor".to_string(),
            ));
        }
        let sid = self.intr.wk(crate::builtins::WK_SPECIES);
        let sp = self.get_prop_value_sym(&Value::Obj(expected), sid)?;
        if !matches!(sp, Value::Obj(c) if c == expected) {
            return Err(Abrupt::Fatal(
                "typed-array method with an overridden @@species".to_string(),
            ));
        }
        Ok(elem)
    }

    fn new_array_iterator(&mut self, target: ObjId, kind: crate::value::ArrayIterKind) -> Value {
        let it = self.alloc(Object::new(
            ObjKind::ArrayIterator {
                target: Some(target),
                index: 0,
                kind,
            },
            Some(self.intr.array_iterator_proto),
        ));
        Value::Obj(it)
    }

    /// Dispatch every ArrayBuffer / DataView / typed-array builtin.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn dispatch_binary_builtin(
        &mut self,
        b: Builtin,
        this: Value,
        args: &[Value],
        is_new: bool,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        match b {
            // -- constructors ----------------------------------------------
            Builtin::ArrayBufferCtor => self.arraybuffer_construct(args, is_new),
            Builtin::DataViewCtor => self.dataview_construct(args, is_new),
            Builtin::TypedArrayCtor(elem) => self.typedarray_construct(elem, args, is_new),
            Builtin::TypedArrayAbstractCtor => {
                // %TypedArray% is abstract: called or constructed → TypeError.
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
            Builtin::TypedArrayFrom => self.typed_array_from(this, &args),
            Builtin::TypedArrayOf => self.typed_array_of(this, &args),

            // -- shared @@species getter -----------------------------------
            Builtin::SpeciesGetReceiver => Ok(this),
            Builtin::ArrayBufferIsView => Ok(Value::Bool(matches!(
                arg(0),
                Value::Obj(o) if matches!(
                    self.obj(o).kind,
                    ObjKind::TypedArray { .. } | ObjKind::DataView { .. }
                )
            ))),

            // -- ArrayBuffer.prototype accessors ---------------------------
            Builtin::ArrayBufferByteLengthGet => {
                let ab = self.require_array_buffer(&this)?;
                let rc = self.buffer_rc(ab).expect("buffer");
                let d = rc.borrow();
                #[allow(clippy::cast_precision_loss)]
                Ok(Value::Num(if d.detached { 0.0 } else { d.bytes.len() as f64 }))
            }
            Builtin::ArrayBufferMaxByteLengthGet => {
                let ab = self.require_array_buffer(&this)?;
                let rc = self.buffer_rc(ab).expect("buffer");
                let d = rc.borrow();
                #[allow(clippy::cast_precision_loss)]
                let v = if d.detached {
                    0.0
                } else {
                    d.max_byte_length.unwrap_or(d.bytes.len()) as f64
                };
                Ok(Value::Num(v))
            }
            Builtin::ArrayBufferResizableGet => {
                let ab = self.require_array_buffer(&this)?;
                let rc = self.buffer_rc(ab).expect("buffer");
                Ok(Value::Bool(rc.borrow().max_byte_length.is_some()))
            }
            Builtin::ArrayBufferDetachedGet => {
                let ab = self.require_array_buffer(&this)?;
                let rc = self.buffer_rc(ab).expect("buffer");
                Ok(Value::Bool(rc.borrow().detached))
            }
            Builtin::ArrayBufferSlice => self.arraybuffer_slice(&this, args),
            Builtin::ArrayBufferResize => self.arraybuffer_resize(&this, &arg(0)),
            Builtin::ArrayBufferTransfer | Builtin::ArrayBufferTransferToFixed => {
                let _ = self.require_array_buffer(&this)?;
                Err(Abrupt::Fatal(
                    "ArrayBuffer.prototype.transfer (out of slice)".to_string(),
                ))
            }

            // -- DataView.prototype accessors ------------------------------
            Builtin::DataViewBufferGet => {
                let dv = self.require_data_view(&this)?;
                let ObjKind::DataView { buffer, .. } = self.obj(dv).kind else {
                    unreachable!()
                };
                Ok(Value::Obj(buffer))
            }
            Builtin::DataViewByteLengthGet => {
                let (_, _, len) = self.dataview_bounds(&this, true)?;
                #[allow(clippy::cast_precision_loss)]
                Ok(Value::Num(len as f64))
            }
            Builtin::DataViewByteOffsetGet => {
                let (_, off, _) = self.dataview_bounds(&this, true)?;
                #[allow(clippy::cast_precision_loss)]
                Ok(Value::Num(off as f64))
            }
            Builtin::DataViewGet(elem) => self.dataview_get(&this, elem, args),
            Builtin::DataViewSet(elem) => self.dataview_set(&this, elem, args),

            // -- %TypedArray%.prototype accessors --------------------------
            Builtin::TypedArrayBufferGet => {
                let oid = self.require_typed_array(&this)?;
                let f = self.ta_fields(oid).expect("ta");
                Ok(Value::Obj(f.buffer))
            }
            Builtin::TypedArrayByteLengthGet => {
                let oid = self.require_typed_array(&this)?;
                let f = self.ta_fields(oid).expect("ta");
                #[allow(clippy::cast_precision_loss)]
                Ok(Value::Num((self.ta_length(f) * f.elem.bytes()) as f64))
            }
            Builtin::TypedArrayByteOffsetGet => {
                let oid = self.require_typed_array(&this)?;
                let f = self.ta_fields(oid).expect("ta");
                #[allow(clippy::cast_precision_loss)]
                let v = if self.ta_out_of_bounds(f) { 0.0 } else { f.byte_offset as f64 };
                Ok(Value::Num(v))
            }
            Builtin::TypedArrayLengthGet => {
                let oid = self.require_typed_array(&this)?;
                let f = self.ta_fields(oid).expect("ta");
                #[allow(clippy::cast_precision_loss)]
                Ok(Value::Num(self.ta_length(f) as f64))
            }
            Builtin::TypedArrayToStringTagGet => match &this {
                Value::Obj(o) => match self.obj(*o).kind {
                    ObjKind::TypedArray { elem, .. } => Ok(Value::str_from(elem.name())),
                    _ => Ok(Value::Undefined),
                },
                _ => Ok(Value::Undefined),
            },
            Builtin::TypedArrayMethod(m) => self.dispatch_ta_method(m, &this, args),
            _ => Err(Abrupt::Fatal(format!("binary dispatch: {b:?}"))),
        }
    }

    /// DataView bounds witness: (buffer, byteOffset, byteLength), TypeError if
    /// detached or out of bounds (a resizable buffer shrank under the view).
    fn dataview_bounds(&mut self, this: &Value, _oob_throws: bool) -> Result<(ObjId, usize, usize), Abrupt> {
        let dv = self.require_data_view(this)?;
        let ObjKind::DataView {
            buffer,
            byte_offset,
            byte_length,
        } = self.obj(dv).kind
        else {
            unreachable!()
        };
        let rc = self.buffer_rc(buffer).expect("buffer");
        let d = rc.borrow();
        if d.detached || byte_offset + byte_length > d.bytes.len() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        Ok((buffer, byte_offset, byte_length))
    }

    fn dataview_get(&mut self, this: &Value, elem: ElementType, args: &[Value]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        let dv = self.require_data_view(this)?;
        if elem.is_bigint() {
            return Err(Abrupt::Fatal(
                "DataView BigInt64/BigUint64 access (BigInt out of value model)".to_string(),
            ));
        }
        let get_index = self.to_index(&arg(0))?;
        let le = self.to_boolean(&arg(1));
        let (buffer, view_offset, view_len) = {
            let ObjKind::DataView {
                buffer,
                byte_offset,
                byte_length,
            } = self.obj(dv).kind
            else {
                unreachable!()
            };
            (buffer, byte_offset, byte_length)
        };
        let rc = self.buffer_rc(buffer).expect("buffer");
        let d = rc.borrow();
        if d.detached || view_offset + view_len > d.bytes.len() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let size = elem.bytes();
        if get_index + size > view_len {
            return Err(self.throw_native(NativeErrorKind::RangeError));
        }
        let bi = view_offset + get_index;
        Ok(Value::Num(read_element(&d.bytes, bi, elem, le)))
    }

    fn dataview_set(&mut self, this: &Value, elem: ElementType, args: &[Value]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        let dv = self.require_data_view(this)?;
        if elem.is_bigint() {
            return Err(Abrupt::Fatal(
                "DataView BigInt64/BigUint64 access (BigInt out of value model)".to_string(),
            ));
        }
        let get_index = self.to_index(&arg(0))?;
        let num = self.to_number(&arg(1))?;
        let le = self.to_boolean(&arg(2));
        let (buffer, view_offset, view_len) = {
            let ObjKind::DataView {
                buffer,
                byte_offset,
                byte_length,
            } = self.obj(dv).kind
            else {
                unreachable!()
            };
            (buffer, byte_offset, byte_length)
        };
        let rc = self.buffer_rc(buffer).expect("buffer");
        let mut d = rc.borrow_mut();
        if d.detached || view_offset + view_len > d.bytes.len() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let size = elem.bytes();
        if get_index + size > view_len {
            return Err(self.throw_native(NativeErrorKind::RangeError));
        }
        let bi = view_offset + get_index;
        write_element(&mut d.bytes, bi, elem, num, le);
        Ok(Value::Undefined)
    }

    fn arraybuffer_resize(&mut self, this: &Value, new_len: &Value) -> ERes {
        let ab = self.require_array_buffer(this)?;
        let rc = self.buffer_rc(ab).expect("buffer");
        let max = rc.borrow().max_byte_length;
        let Some(max) = max else {
            // Not resizable.
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let n = self.to_index(new_len)?;
        if rc.borrow().detached {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        if n > max {
            return Err(self.throw_native(NativeErrorKind::RangeError));
        }
        rc.borrow_mut().bytes.resize(n, 0);
        Ok(Value::Undefined)
    }

    fn arraybuffer_slice(&mut self, this: &Value, args: &[Value]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        let ab = self.require_array_buffer(this)?;
        // SpeciesConstructor default check.
        let ctor_v = self.get_from_object(ab, &units_from_str("constructor"))?;
        if !matches!(ctor_v, Value::Obj(c) if c == self.intr.arraybuffer_ctor) {
            return Err(Abrupt::Fatal(
                "ArrayBuffer.prototype.slice with a non-default @@species".to_string(),
            ));
        }
        let rc = self.buffer_rc(ab).expect("buffer");
        let len = {
            let d = rc.borrow();
            if d.detached {
                return Err(self.throw_native(NativeErrorKind::TypeError));
            }
            d.bytes.len()
        };
        #[allow(clippy::cast_precision_loss)]
        let flen = len as f64;
        let rel_start = to_integer_or_infinity(self.to_number(&arg(0))?);
        let first = if rel_start < 0.0 {
            (flen + rel_start).max(0.0)
        } else {
            rel_start.min(flen)
        };
        let rel_end = match arg(1) {
            Value::Undefined => flen,
            v => to_integer_or_infinity(self.to_number(&v)?),
        };
        let final_ = if rel_end < 0.0 {
            (flen + rel_end).max(0.0)
        } else {
            rel_end.min(flen)
        };
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let (first, final_) = (first as usize, final_ as usize);
        let new_len = final_.saturating_sub(first);
        // Re-check detach after coercions (valueOf could have detached).
        let new_buf = self.alloc_buffer(new_len, None);
        {
            let src = rc.borrow();
            if src.detached {
                return Err(self.throw_native(NativeErrorKind::TypeError));
            }
            let nrc = self.buffer_rc(new_buf).expect("new buffer");
            let mut dst = nrc.borrow_mut();
            let avail = src.bytes.len().saturating_sub(first);
            let n = new_len.min(avail);
            dst.bytes[..n].copy_from_slice(&src.bytes[first..first + n]);
        }
        Ok(Value::Obj(new_buf))
    }

    #[allow(clippy::too_many_lines)]
    fn dispatch_ta_method(&mut self, m: TAMethod, this: &Value, args: &[Value]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        let oid = self.require_typed_array(this)?;
        let f = self.ta_fields(oid).expect("ta");
        // ValidateTypedArray (23.2.4.4): every %TypedArray%.prototype method in
        // this slice begins with ValidateTypedArray, which throws a TypeError
        // when the view is out of bounds (a resizable buffer shrank below the
        // view's extent) or detached. `set` runs ToIntegerOrInfinity(offset) /
        // the offset<0 RangeError first and does its own OOB check; `subarray`
        // tolerates an OOB `this`. All others validate here up front.
        if !matches!(m, TAMethod::Set | TAMethod::Subarray) && self.ta_out_of_bounds(f) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let len = self.ta_length(f);
        #[allow(clippy::cast_precision_loss)]
        let flen = len as f64;
        match m {
            TAMethod::At => {
                let rel = to_integer_or_infinity(self.to_number(&arg(0))?);
                let k = if rel < 0.0 { flen + rel } else { rel };
                if k < 0.0 || k >= flen {
                    Ok(Value::Undefined)
                } else {
                    Ok(self.ta_element_get(oid, k))
                }
            }
            TAMethod::Fill => {
                // The value is coerced ONCE (ToNumber / ToBigInt by element
                // type) before the range clamps; `ta_element_set` re-coerces
                // the resulting primitive idempotently (no extra side effects).
                let val = self.ta_coerce_elem(f.elem, &arg(0))?;
                let start = self.rel_index(&arg(1), flen, 0.0)?;
                let end = self.rel_index(&arg(2), flen, flen)?;
                let mut k = start;
                while k < end {
                    #[allow(clippy::cast_precision_loss)]
                    self.ta_element_set(oid, k as f64, val.clone())?;
                    k += 1;
                }
                Ok(this.clone())
            }
            TAMethod::Join => {
                let sep = match arg(0) {
                    Value::Undefined => units_from_str(","),
                    v => self.to_string_units(&v)?,
                };
                let mut out: Units = Vec::new();
                for i in 0..len {
                    if i > 0 {
                        out.extend_from_slice(&sep);
                    }
                    // ToString of the element (Number → number string, BigInt →
                    // decimal); typed-array elements are never undefined/null.
                    #[allow(clippy::cast_precision_loss)]
                    let el = self.ta_element_get(oid, i as f64);
                    let s = self.to_string_units(&el)?;
                    out.extend_from_slice(&s);
                }
                Ok(Value::Str(Rc::new(out)))
            }
            TAMethod::IndexOf | TAMethod::LastIndexOf => {
                if f.elem.is_bigint() {
                    return Err(Abrupt::Fatal(
                        "%TypedArray%.prototype.indexOf/lastIndexOf on a BigInt array (out of slice)"
                            .to_string(),
                    ));
                }
                if len == 0 {
                    return Ok(Value::Num(-1.0));
                }
                let search = arg(0);
                let last = matches!(m, TAMethod::LastIndexOf);
                // fromIndex defaults to 0 for indexOf, len-1 for lastIndexOf.
                let n = match args.get(1) {
                    Some(v) => to_integer_or_infinity(self.to_number(v)?),
                    None if last => flen - 1.0,
                    None => 0.0,
                };
                let vals = self.ta_snapshot(oid);
                let found = self.ta_index_search(&vals, &search, n, last, flen);
                Ok(Value::Num(found))
            }
            TAMethod::Includes => {
                if f.elem.is_bigint() {
                    return Err(Abrupt::Fatal(
                        "%TypedArray%.prototype.includes on a BigInt array (out of slice)"
                            .to_string(),
                    ));
                }
                // Array.prototype.includes step 3: if [[ArrayLength]] is 0,
                // return false BEFORE ToIntegerOrInfinity(fromIndex) — its
                // valueOf must not run (length-zero-returns-false.js).
                if len == 0 {
                    return Ok(Value::Bool(false));
                }
                let search = arg(0);
                let n = to_integer_or_infinity(self.to_number(&arg(1))?);
                let vals = self.ta_snapshot(oid);
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let start = if n >= 0.0 {
                    (n as usize).min(vals.len())
                } else {
                    let s = flen + n;
                    if s < 0.0 { 0 } else { s as usize }
                };
                let target = match &search {
                    Value::Num(x) => Some(*x),
                    _ => None,
                };
                let hit = target.is_some_and(|t| {
                    vals[start..].iter().any(|&e| e == t || (e.is_nan() && t.is_nan()))
                });
                Ok(Value::Bool(hit))
            }
            TAMethod::Reverse => {
                // Snapshot as Values (Number or BigInt) so BigInt arrays
                // reverse correctly, then write back in reversed order.
                let mut vals: Vec<Value> = Vec::with_capacity(len);
                for i in 0..len {
                    #[allow(clippy::cast_precision_loss)]
                    vals.push(self.ta_element_get(oid, i as f64));
                }
                vals.reverse();
                for (i, v) in vals.into_iter().enumerate() {
                    #[allow(clippy::cast_precision_loss)]
                    self.ta_element_set(oid, i as f64, v)?;
                }
                Ok(this.clone())
            }
            TAMethod::Values => Ok(self.new_array_iterator(oid, crate::value::ArrayIterKind::Value)),
            TAMethod::Keys => Ok(self.new_array_iterator(oid, crate::value::ArrayIterKind::Key)),
            TAMethod::Entries => {
                Ok(self.new_array_iterator(oid, crate::value::ArrayIterKind::Entry))
            }
            TAMethod::ForEach | TAMethod::Every | TAMethod::Some | TAMethod::Find
            | TAMethod::FindIndex => self.ta_iterate(m, oid, &arg(0), &arg(1), len),
            TAMethod::Reduce => self.ta_reduce(oid, &arg(0), args.get(1).cloned(), len),
            TAMethod::Set => self.ta_set(oid, &arg(0), &arg(1)),
            TAMethod::Subarray => self.ta_subarray(oid, &arg(0), &arg(1), flen),
            TAMethod::Slice => self.ta_slice(oid, &arg(0), &arg(1), flen),
            // Registered (typeof/name/length exact) but behavior out of slice.
            _ => Err(Abrupt::Fatal(format!(
                "%TypedArray%.prototype method {m:?} (out of slice)"
            ))),
        }
    }

    /// A relative-index argument clamped into [0, len] (start/end conventions).
    fn rel_index(&mut self, v: &Value, flen: f64, default: f64) -> Result<usize, Abrupt> {
        let rel = match v {
            Value::Undefined => default,
            _ => to_integer_or_infinity(self.to_number(v)?),
        };
        let k = if rel < 0.0 { (flen + rel).max(0.0) } else { rel.min(flen) };
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        Ok(k as usize)
    }

    fn ta_index_search(&self, vals: &[f64], search: &Value, n: f64, last: bool, flen: f64) -> f64 {
        let Value::Num(target) = search else {
            return -1.0;
        };
        let target = *target;
        if target.is_nan() {
            return -1.0; // indexOf/lastIndexOf use strict equality: NaN never matches
        }
        if last {
            // from index defaults to len-1; negative counts from end
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let mut k: i64 = if n >= 0.0 {
                (n.min(flen - 1.0)) as i64
            } else {
                (flen + n) as i64
            };
            while k >= 0 {
                if vals[k as usize] == target {
                    #[allow(clippy::cast_precision_loss)]
                    return k as f64;
                }
                k -= 1;
            }
            -1.0
        } else {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let start = if n >= 0.0 {
                n as usize
            } else {
                let s = flen + n;
                if s < 0.0 { 0 } else { s as usize }
            };
            for (i, &e) in vals.iter().enumerate().skip(start) {
                if e == target {
                    #[allow(clippy::cast_precision_loss)]
                    return i as f64;
                }
            }
            -1.0
        }
    }

    fn ta_iterate(
        &mut self,
        m: TAMethod,
        oid: ObjId,
        cb: &Value,
        this_arg: &Value,
        len: usize,
    ) -> ERes {
        let Value::Obj(cbf) = cb else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        if !self.obj(*cbf).is_callable() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let cbf = *cbf;
        for i in 0..len {
            #[allow(clippy::cast_precision_loss)]
            let idx = i as f64;
            let el = self.ta_element_get(oid, idx);
            let r = self.call_function(
                cbf,
                this_arg.clone(),
                vec![el.clone(), Value::Num(idx), Value::Obj(oid)],
                false,
            )?;
            match m {
                TAMethod::Every => {
                    if !self.to_boolean(&r) {
                        return Ok(Value::Bool(false));
                    }
                }
                TAMethod::Some => {
                    if self.to_boolean(&r) {
                        return Ok(Value::Bool(true));
                    }
                }
                TAMethod::Find => {
                    if self.to_boolean(&r) {
                        return Ok(el);
                    }
                }
                TAMethod::FindIndex => {
                    if self.to_boolean(&r) {
                        return Ok(Value::Num(idx));
                    }
                }
                _ => {}
            }
        }
        match m {
            TAMethod::Every => Ok(Value::Bool(true)),
            TAMethod::Some => Ok(Value::Bool(false)),
            TAMethod::Find => Ok(Value::Undefined),
            TAMethod::FindIndex => Ok(Value::Num(-1.0)),
            _ => Ok(Value::Undefined),
        }
    }

    fn ta_reduce(&mut self, oid: ObjId, cb: &Value, init: Option<Value>, len: usize) -> ERes {
        let Value::Obj(cbf) = cb else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        if !self.obj(*cbf).is_callable() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let cbf = *cbf;
        let mut k = 0usize;
        let mut acc = match init {
            Some(v) => v,
            None => {
                if len == 0 {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let v = self.ta_element_get(oid, 0.0);
                k = 1;
                v
            }
        };
        while k < len {
            #[allow(clippy::cast_precision_loss)]
            let idx = k as f64;
            let el = self.ta_element_get(oid, idx);
            acc = self.call_function(
                cbf,
                Value::Undefined,
                vec![acc, el, Value::Num(idx), Value::Obj(oid)],
                false,
            )?;
            k += 1;
        }
        Ok(acc)
    }

    fn ta_set(&mut self, oid: ObjId, source: &Value, offset_v: &Value) -> ERes {
        let offset = to_integer_or_infinity(self.to_number(offset_v)?);
        if offset < 0.0 {
            return Err(self.throw_native(NativeErrorKind::RangeError));
        }
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let offset = offset as usize; // +Infinity saturates to usize::MAX
        // SetTypedArrayFrom* (23.2.3.24.1/.2 step 3): a target view that shrank
        // out of bounds (or is detached) is a TypeError, checked AFTER
        // ToIntegerOrInfinity(offset)/offset<0 but BEFORE the srcLength+offset
        // RangeError. `ta_length` reports 0 for such a view, so the check must
        // come first or a RangeError would mask the TypeError.
        let tf = self.ta_fields(oid).expect("ta");
        if self.ta_out_of_bounds(tf) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let target_len = self.ta_length(tf);
        match source {
            Value::Obj(so) if matches!(self.obj(*so).kind, ObjKind::TypedArray { .. }) => {
                let so = *so;
                let sf = self.ta_fields(so).expect("ta");
                // SetTypedArrayFromTypedArray: content-type mismatch (exactly
                // one side BigInt) is a TypeError (23.2.3.24.1 step 5).
                if sf.elem.is_bigint() != tf.elem.is_bigint() {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let src_len = self.ta_length(sf);
                // saturating: offset may be usize::MAX (+Infinity) — never wrap.
                if offset.saturating_add(src_len) > target_len {
                    return Err(self.throw_native(NativeErrorKind::RangeError));
                }
                // Snapshot source values first (overlap-safe).
                let mut vals: Vec<Value> = Vec::with_capacity(src_len);
                for i in 0..src_len {
                    #[allow(clippy::cast_precision_loss)]
                    vals.push(self.ta_element_get(so, i as f64));
                }
                for (i, v) in vals.into_iter().enumerate() {
                    #[allow(clippy::cast_precision_loss)]
                    self.ta_element_set(oid, (offset + i) as f64, v)?;
                }
                Ok(Value::Undefined)
            }
            _ => {
                // Array-like source.
                let src = self.to_object_arg(source)?;
                let len_v = self.get_from_object(src, &units_from_str("length"))?;
                let src_len = usize::try_from(crate::builtins::to_length_u64(self.to_number(&len_v)?))
                    .map_err(|_| Abrupt::Fatal("set source length beyond cap".to_string()))?;
                // saturating: offset may be usize::MAX (+Infinity) — never wrap.
                if offset.saturating_add(src_len) > target_len {
                    return Err(self.throw_native(NativeErrorKind::RangeError));
                }
                for i in 0..src_len {
                    let v = self.get_from_object(src, &units_from_str(&i.to_string()))?;
                    #[allow(clippy::cast_precision_loss)]
                    self.ta_element_set(oid, (offset + i) as f64, v)?;
                }
                Ok(Value::Undefined)
            }
        }
    }

    fn to_object_arg(&mut self, v: &Value) -> Result<ObjId, Abrupt> {
        match v {
            Value::Obj(o) => Ok(*o),
            Value::Undefined | Value::Null => Err(self.throw_native(NativeErrorKind::TypeError)),
            prim => self.to_object_wrapper(prim),
        }
    }

    fn ta_subarray(&mut self, oid: ObjId, begin: &Value, end: &Value, flen: f64) -> ERes {
        let elem = self.ta_default_species(oid)?;
        let f = self.ta_fields(oid).expect("ta");
        let start = self.rel_index(begin, flen, 0.0)?;
        let final_ = self.rel_index(end, flen, flen)?;
        let new_len = final_.saturating_sub(start);
        let new_offset = f.byte_offset + start * f.elem.bytes();
        let proto = self.intr.ta_proto(elem);
        let ta = self.make_typed_array(elem, f.buffer, new_offset, new_len, proto);
        Ok(Value::Obj(ta))
    }

    fn ta_slice(&mut self, oid: ObjId, start: &Value, end: &Value, flen: f64) -> ERes {
        let elem = self.ta_default_species(oid)?;
        let first = self.rel_index(start, flen, 0.0)?;
        let final_ = self.rel_index(end, flen, flen)?;
        let count = final_.saturating_sub(first);
        let proto = self.intr.ta_proto(elem);
        let Value::Obj(dest) = self.ta_allocate(elem, count, proto)? else {
            unreachable!()
        };
        for i in 0..count {
            #[allow(clippy::cast_precision_loss)]
            let v = self.ta_element_get(oid, (first + i) as f64);
            #[allow(clippy::cast_precision_loss)]
            self.ta_element_set(dest, i as f64, v)?;
        }
        Ok(Value::Obj(dest))
    }
}
