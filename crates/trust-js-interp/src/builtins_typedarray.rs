// Binary-data surface (§25 ArrayBuffer/DataView, §23.2 %TypedArray% + the
// concrete constructors), written from ECMA-262. Element storage lives in the
// referenced ArrayBuffer's byte block; the integer-indexed exotic internal
// methods live in props.rs and call the element helpers here. Resizable and
// detached buffers are modeled; the BigInt-typed arrays (BigInt64Array /
// BigUint64Array) read/write their elements as BigInt (ToBigInt on store, the
// signed/unsigned 64-bit wrap into the byte block), and the DataView
// getBigInt64/setBigInt64/getBigUint64/setBigUint64 lanes are live.
// Projection of any binary-data object refuses (engine-divergent own
// surface); the observable trace is carried by the assertions, which
// read/write through the exotic methods.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use crate::props::PartialDesc;
use trust_js_value::{
    bigint_from_i64, bigint_from_u64, bigint_to_i64_wrap, bigint_to_u64_wrap, decode_le, encode_le,
    ordered_own_keys, to_integer_or_infinity, units_from_str, ElemType, ErrKind, JsBigInt, JsObject,
    JsValue, NativeFn, ObjId, ObjKind, PropKey, SymId, TypedArrayData, Units, WkSym,
};

/// Cap on any single data-block allocation; larger requests refuse
/// (NoCoverage) rather than risk exhausting host memory. Well above every
/// test262 fixture, well below an OOM.
const MAX_BINARY_BYTES: usize = 1 << 27; // 128 MiB

/// A `Copy` snapshot of a typed array's view fields.
#[derive(Clone, Copy)]
pub(crate) struct TaInfo {
    pub buffer: ObjId,
    pub byte_offset: usize,
    pub array_length: Option<usize>,
    pub element: ElemType,
}

impl Interp {
    // -- low-level buffer + view helpers ------------------------------------

    pub(crate) fn ta_info(&self, oid: ObjId) -> Option<TaInfo> {
        if let ObjKind::TypedArray(d) = &self.heap.obj(oid).kind {
            Some(TaInfo {
                buffer: d.buffer,
                byte_offset: d.byte_offset,
                array_length: d.array_length,
                element: d.element,
            })
        } else {
            None
        }
    }

    fn ab_is_detached(&self, ab: ObjId) -> bool {
        matches!(&self.heap.obj(ab).kind, ObjKind::ArrayBuffer(d) if d.detached)
    }

    /// Current byte length of an ArrayBuffer (0 if detached / not a buffer).
    fn ab_byte_length(&self, ab: ObjId) -> usize {
        match &self.heap.obj(ab).kind {
            ObjKind::ArrayBuffer(d) if !d.detached => d.bytes.len(),
            _ => 0,
        }
    }

    fn ab_is_resizable(&self, ab: ObjId) -> bool {
        matches!(&self.heap.obj(ab).kind, ObjKind::ArrayBuffer(d) if d.max_byte_length.is_some())
    }

    /// TypedArrayLength: the current element count (0 when detached or the view
    /// is out of bounds over its resizable buffer).
    pub(crate) fn ta_current_length(&self, oid: ObjId) -> usize {
        let Some(info) = self.ta_info(oid) else {
            return 0;
        };
        let ab_len = self.ab_byte_length(info.buffer);
        let bpe = info.element.bytes_per_element();
        match info.array_length {
            Some(n) => {
                if info.byte_offset.saturating_add(n.saturating_mul(bpe)) > ab_len {
                    0
                } else {
                    n
                }
            }
            None => {
                if info.byte_offset > ab_len {
                    0
                } else {
                    (ab_len - info.byte_offset) / bpe
                }
            }
        }
    }

    /// IsTypedArrayOutOfBounds (true also covers a detached buffer).
    pub(crate) fn ta_out_of_bounds(&self, oid: ObjId) -> bool {
        let Some(info) = self.ta_info(oid) else {
            return true;
        };
        if self.ab_is_detached(info.buffer) {
            return true;
        }
        let ab_len = self.ab_byte_length(info.buffer);
        let bpe = info.element.bytes_per_element();
        match info.array_length {
            Some(n) => info.byte_offset.saturating_add(n.saturating_mul(bpe)) > ab_len,
            None => info.byte_offset > ab_len,
        }
    }

    /// IsValidIntegerIndex(O, index) for a Number `index`.
    pub(crate) fn ta_is_valid_index(&self, oid: ObjId, idx: f64) -> bool {
        let Some(info) = self.ta_info(oid) else {
            return false;
        };
        if self.ab_is_detached(info.buffer) {
            return false;
        }
        if !idx.is_finite() || idx.trunc() != idx {
            return false;
        }
        if idx == 0.0 && idx.is_sign_negative() {
            return false; // -0 is not a valid index
        }
        if idx < 0.0 {
            return false;
        }
        idx < self.ta_current_length(oid) as f64
    }

    /// GetValueFromBuffer for element `idx` (assumed a valid index). Number
    /// element types only.
    fn ta_get_number(&self, info: TaInfo, idx: usize) -> f64 {
        let bpe = info.element.bytes_per_element();
        let start = info.byte_offset + idx * bpe;
        match &self.heap.obj(info.buffer).kind {
            ObjKind::ArrayBuffer(d) if start + bpe <= d.bytes.len() => {
                decode_le(info.element, true, &d.bytes[start..start + bpe])
            }
            _ => 0.0,
        }
    }

    /// GetValueFromBuffer for a BigInt element `idx` (assumed valid): the 8-byte
    /// little-endian block interpreted as a signed / unsigned 64-bit integer.
    fn ta_get_bigint(&self, info: TaInfo, idx: usize) -> JsBigInt {
        let start = info.byte_offset + idx * 8;
        let ObjKind::ArrayBuffer(d) = &self.heap.obj(info.buffer).kind else {
            return JsBigInt::from(0);
        };
        if start + 8 > d.bytes.len() {
            return JsBigInt::from(0);
        }
        let mut b = [0u8; 8];
        b.copy_from_slice(&d.bytes[start..start + 8]);
        if info.element == ElemType::BigInt64 {
            bigint_from_i64(i64::from_le_bytes(b))
        } else {
            bigint_from_u64(u64::from_le_bytes(b))
        }
    }

    /// SetValueInBuffer for an already-coerced BigInt, when `idx` is in range:
    /// the `bits`-bit two's-complement wrap, stored little-endian.
    fn ta_store_bigint(&mut self, info: TaInfo, idx: usize, v: &JsBigInt) {
        let start = info.byte_offset + idx * 8;
        let bytes = if info.element == ElemType::BigInt64 {
            bigint_to_i64_wrap(v).to_le_bytes()
        } else {
            bigint_to_u64_wrap(v).to_le_bytes()
        };
        if let ObjKind::ArrayBuffer(d) = &mut self.heap.obj_mut(info.buffer).kind {
            if start + 8 <= d.bytes.len() {
                d.bytes[start..start + 8].copy_from_slice(&bytes);
            }
        }
    }

    /// IntegerIndexedElementGet as a JsValue (undefined when out of range).
    /// Number-typed arrays yield a Number; BigInt64/BigUint64 yield a BigInt.
    pub(crate) fn ta_element_get_pure(&self, oid: ObjId, idx: f64) -> JsValue {
        let Some(info) = self.ta_info(oid) else {
            return JsValue::Undefined;
        };
        if !self.ta_is_valid_index(oid, idx) {
            return JsValue::Undefined;
        }
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let i = idx as usize;
        if info.element.is_bigint() {
            JsValue::bigint(self.ta_get_bigint(info, i))
        } else {
            JsValue::Num(self.ta_get_number(info, i))
        }
    }

    /// Read element `idx` as a JsValue (assumed valid); used by same-type
    /// copies where the value stays primitive.
    fn ta_get_value_at(&self, info: TaInfo, idx: usize) -> JsValue {
        if info.element.is_bigint() {
            JsValue::bigint(self.ta_get_bigint(info, idx))
        } else {
            JsValue::Num(self.ta_get_number(info, idx))
        }
    }

    /// Store an already-primitive element value (no coercion) at `idx`.
    fn ta_store_value_at(&mut self, info: TaInfo, idx: usize, v: &JsValue) {
        match v {
            JsValue::BigInt(b) => self.ta_store_bigint(info, idx, b),
            JsValue::Num(n) => self.ta_store_number(info, idx, *n),
            _ => {}
        }
    }

    /// SetValueInBuffer for an already-coerced Number, when `idx` is in range.
    fn ta_store_number(&mut self, info: TaInfo, idx: usize, n: f64) {
        let bpe = info.element.bytes_per_element();
        let start = info.byte_offset + idx * bpe;
        let mut buf = [0u8; 8];
        encode_le(info.element, n, true, &mut buf[..bpe]);
        if let ObjKind::ArrayBuffer(d) = &mut self.heap.obj_mut(info.buffer).kind {
            if start + bpe <= d.bytes.len() {
                d.bytes[start..start + bpe].copy_from_slice(&buf[..bpe]);
            }
        }
    }

    /// TypedArraySetElement(O, index, value): coerce (always observable), then
    /// store if the index is valid.
    pub(crate) fn ta_set_element(&mut self, oid: ObjId, idx: f64, v: JsValue) -> Result<(), Abrupt> {
        let info = self.ta_info(oid).expect("typed array");
        if info.element.is_bigint() {
            // ToBigInt is always performed (observable), then stored if valid.
            let b = self.to_bigint(&v)?;
            if self.ta_is_valid_index(oid, idx) {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                self.ta_store_bigint(info, idx as usize, &b);
            }
            return Ok(());
        }
        let n = self.to_number(&v)?;
        if self.ta_is_valid_index(oid, idx) {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            self.ta_store_number(info, idx as usize, n);
        }
        Ok(())
    }

    /// Integer-indexed exotic [[DefineOwnProperty]] (10.4.5.3).
    pub(crate) fn ta_define_index(
        &mut self,
        oid: ObjId,
        idx: f64,
        desc: PartialDesc,
    ) -> Result<bool, Abrupt> {
        if !self.ta_is_valid_index(oid, idx) {
            return Ok(false);
        }
        if desc.configurable == Some(false)
            || desc.enumerable == Some(false)
            || desc.is_accessor()
            || desc.writable == Some(false)
        {
            return Ok(false);
        }
        if let Some(val) = desc.value {
            self.ta_set_element(oid, idx, val)?;
        }
        Ok(true)
    }

    /// The canonical index-string keys of a typed array (empty for others).
    fn ta_index_keys(&self, oid: ObjId) -> Vec<Units> {
        let len = self.ta_current_length(oid);
        (0..len).map(|i| units_from_str(&i.to_string())).collect()
    }

    /// [[OwnPropertyKeys]] order with typed-array integer indices prepended.
    pub(crate) fn ordered_own_keys_of(&self, oid: ObjId) -> Vec<PropKey> {
        if matches!(self.heap.obj(oid).kind, ObjKind::TypedArray(_)) {
            let mut keys: Vec<PropKey> =
                self.ta_index_keys(oid).into_iter().map(PropKey::Str).collect();
            keys.extend(ordered_own_keys(self.heap.obj(oid)));
            keys
        } else {
            ordered_own_keys(self.heap.obj(oid))
        }
    }

    /// ValidateTypedArray(O): TypeError unless `this` is a typed array whose
    /// buffer is attached and in bounds. Returns (oid, element, length).
    fn ta_validate(&mut self, this: &JsValue) -> Result<(ObjId, ElemType, usize), Abrupt> {
        let JsValue::Obj(oid) = this else {
            return Err(self.throw_type_error());
        };
        let oid = *oid;
        let Some(info) = self.ta_info(oid) else {
            return Err(self.throw_type_error());
        };
        if self.ta_out_of_bounds(oid) {
            return Err(self.throw_type_error());
        }
        Ok((oid, info.element, self.ta_current_length(oid)))
    }

    fn require_ta(&mut self, this: &JsValue) -> Result<ObjId, Abrupt> {
        match this {
            JsValue::Obj(oid) if self.ta_info(*oid).is_some() => Ok(*oid),
            _ => Err(self.throw_type_error()),
        }
    }

    // -- ToIndex ------------------------------------------------------------

    /// ToIndex(value) (7.1.22): integer in [0, 2^53-1] or RangeError.
    pub(crate) fn to_index(&mut self, v: &JsValue) -> Result<usize, Abrupt> {
        if matches!(v, JsValue::Undefined) {
            return Ok(0);
        }
        let n = to_integer_or_infinity(self.to_number(v)?);
        if n < 0.0 || n > 9_007_199_254_740_991.0 {
            return Err(self.throw_native(ErrKind::Range));
        }
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        Ok(n as usize)
    }

    // -- ArrayBuffer allocation / detach ------------------------------------

    fn allocate_array_buffer(
        &mut self,
        proto: ObjId,
        byte_length: usize,
        max: Option<usize>,
    ) -> Result<ObjId, Abrupt> {
        let cap = max.unwrap_or(byte_length);
        if cap > MAX_BINARY_BYTES {
            return Err(Abrupt::Fatal(format!(
                "ArrayBuffer allocation of {cap} bytes exceeds the model cap (out of slice)"
            )));
        }
        let data = trust_js_value::ArrayBufferData {
            bytes: vec![0u8; byte_length],
            detached: false,
            max_byte_length: max,
        };
        self.alloc_obj(JsObject::new(ObjKind::ArrayBuffer(data), Some(proto)))
    }

    fn detach_buffer(&mut self, ab: ObjId) {
        if let ObjKind::ArrayBuffer(d) = &mut self.heap.obj_mut(ab).kind {
            d.bytes = Vec::new();
            d.detached = true;
        }
    }

    fn require_array_buffer(&mut self, v: &JsValue) -> Result<ObjId, Abrupt> {
        match v {
            JsValue::Obj(o) if matches!(self.heap.obj(*o).kind, ObjKind::ArrayBuffer(_)) => Ok(*o),
            _ => Err(self.throw_type_error()),
        }
    }

    // -- SpeciesConstructor -------------------------------------------------

    fn binary_species_constructor(&mut self, oid: ObjId, default: ObjId) -> ERes {
        let c = self.get_from_object(oid, &PropKey::from_str("constructor"), JsValue::Obj(oid))?;
        if matches!(c, JsValue::Undefined) {
            return Ok(JsValue::Obj(default));
        }
        let JsValue::Obj(_) = c else {
            return Err(self.throw_type_error());
        };
        let s = self.get_prop(&c, &PropKey::Sym(SymId::WellKnown(WkSym::Species)))?;
        if s.is_nullish() {
            return Ok(JsValue::Obj(default));
        }
        if self.is_constructor(&s) {
            Ok(s)
        } else {
            Err(self.throw_type_error())
        }
    }

    /// TypedArrayCreate(constructor, argList): Construct then re-validate.
    fn typed_array_create(&mut self, ctor: &JsValue, args: Vec<JsValue>) -> Result<ObjId, Abrupt> {
        let single_len = if args.len() == 1 {
            if let JsValue::Num(n) = &args[0] {
                Some(*n)
            } else {
                None
            }
        } else {
            None
        };
        let r = self.construct(ctor, args, None)?;
        let JsValue::Obj(oid) = r else {
            return Err(self.throw_type_error());
        };
        if self.ta_info(oid).is_none() {
            return Err(self.throw_type_error());
        }
        if self.ta_out_of_bounds(oid) {
            return Err(self.throw_type_error());
        }
        if let Some(n) = single_len {
            if (self.ta_current_length(oid) as f64) < n {
                return Err(self.throw_type_error());
            }
        }
        Ok(oid)
    }

    /// TypedArraySpeciesCreate(exemplar, argList).
    fn ta_species_create(&mut self, exemplar: ObjId, args: Vec<JsValue>) -> Result<ObjId, Abrupt> {
        let element = self.ta_info(exemplar).expect("typed array").element;
        let default = self.intr.ta_ctors[element.idx()];
        let ctor = self.binary_species_constructor(exemplar, default)?;
        let out = self.typed_array_create(&ctor, args)?;
        // Content-type must match (BigInt vs Number).
        if self.ta_info(out).expect("ta").element.is_bigint() != element.is_bigint() {
            return Err(self.throw_type_error());
        }
        Ok(out)
    }

    // -- dispatch -----------------------------------------------------------

    pub(crate) fn dispatch_binary(
        &mut self,
        nf: NativeFn,
        this: JsValue,
        args: Vec<JsValue>,
        new_target: Option<&JsValue>,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        match nf {
            NativeFn::ArrayBufferCtor => self.array_buffer_ctor(&args, new_target),
            NativeFn::ArrayBufferIsView => Ok(JsValue::Bool(matches!(
                arg(0),
                JsValue::Obj(o)
                    if matches!(
                        self.heap.obj(o).kind,
                        ObjKind::TypedArray(_) | ObjKind::DataView(_)
                    )
            ))),
            NativeFn::ArrayBufferByteLengthGetter => {
                let ab = self.require_array_buffer(&this)?;
                #[allow(clippy::cast_precision_loss)]
                Ok(JsValue::Num(self.ab_byte_length(ab) as f64))
            }
            NativeFn::ArrayBufferMaxByteLengthGetter => {
                let ab = self.require_array_buffer(&this)?;
                let v = match &self.heap.obj(ab).kind {
                    ObjKind::ArrayBuffer(d) if d.detached => 0,
                    ObjKind::ArrayBuffer(d) => d.max_byte_length.unwrap_or(d.bytes.len()),
                    _ => 0,
                };
                #[allow(clippy::cast_precision_loss)]
                Ok(JsValue::Num(v as f64))
            }
            NativeFn::ArrayBufferResizableGetter => {
                let ab = self.require_array_buffer(&this)?;
                Ok(JsValue::Bool(self.ab_is_resizable(ab)))
            }
            NativeFn::ArrayBufferDetachedGetter => {
                let ab = self.require_array_buffer(&this)?;
                Ok(JsValue::Bool(self.ab_is_detached(ab)))
            }
            NativeFn::ArrayBufferSlice => self.array_buffer_slice(&this, &arg(0), &arg(1)),
            NativeFn::ArrayBufferResize => self.array_buffer_resize(&this, &arg(0)),
            NativeFn::ArrayBufferTransfer { to_fixed } => {
                self.array_buffer_transfer(&this, &arg(0), to_fixed)
            }
            NativeFn::DataViewCtor => self.data_view_ctor(&args, new_target),
            NativeFn::DataViewBufferGetter => {
                let dv = self.require_data_view(&this)?;
                if let ObjKind::DataView(d) = &self.heap.obj(dv).kind {
                    Ok(JsValue::Obj(d.buffer))
                } else {
                    Err(self.throw_type_error())
                }
            }
            NativeFn::DataViewByteLengthGetter => {
                let dv = self.require_data_view(&this)?;
                if self.dv_out_of_bounds(dv) {
                    return Err(self.throw_type_error());
                }
                #[allow(clippy::cast_precision_loss)]
                Ok(JsValue::Num(self.dv_byte_length(dv) as f64))
            }
            NativeFn::DataViewByteOffsetGetter => {
                let dv = self.require_data_view(&this)?;
                if self.dv_out_of_bounds(dv) {
                    return Err(self.throw_type_error());
                }
                let off = if let ObjKind::DataView(d) = &self.heap.obj(dv).kind {
                    d.byte_offset
                } else {
                    0
                };
                #[allow(clippy::cast_precision_loss)]
                Ok(JsValue::Num(off as f64))
            }
            NativeFn::DataViewGet(et) => self.data_view_get(&this, et, &arg(0), &arg(1)),
            NativeFn::DataViewSet(et) => self.data_view_set(&this, et, &arg(0), &arg(1), &arg(2)),
            NativeFn::TypedArrayBaseCtor => Err(self.throw_type_error()),
            NativeFn::TypedArrayCtor(et) => self.typed_array_ctor(et, &args, new_target),
            NativeFn::TypedArrayFrom => self.typed_array_from(&this, &args),
            NativeFn::TypedArrayOf => self.typed_array_of(&this, &args),
            NativeFn::TaBufferGetter => {
                let oid = self.require_ta(&this)?;
                Ok(JsValue::Obj(self.ta_info(oid).expect("ta").buffer))
            }
            NativeFn::TaByteLengthGetter => {
                let oid = self.require_ta(&this)?;
                let bpe = self.ta_info(oid).expect("ta").element.bytes_per_element();
                let len = if self.ta_out_of_bounds(oid) { 0 } else { self.ta_current_length(oid) };
                #[allow(clippy::cast_precision_loss)]
                Ok(JsValue::Num((len * bpe) as f64))
            }
            NativeFn::TaByteOffsetGetter => {
                let oid = self.require_ta(&this)?;
                let off = if self.ta_out_of_bounds(oid) {
                    0
                } else {
                    self.ta_info(oid).expect("ta").byte_offset
                };
                #[allow(clippy::cast_precision_loss)]
                Ok(JsValue::Num(off as f64))
            }
            NativeFn::TaLengthGetter => {
                let oid = self.require_ta(&this)?;
                let len = if self.ta_out_of_bounds(oid) { 0 } else { self.ta_current_length(oid) };
                #[allow(clippy::cast_precision_loss)]
                Ok(JsValue::Num(len as f64))
            }
            NativeFn::TaToStringTagGetter => match &this {
                JsValue::Obj(o) => match self.ta_info(*o) {
                    Some(info) => Ok(JsValue::str_from(info.element.ctor_name())),
                    None => Ok(JsValue::Undefined),
                },
                _ => Ok(JsValue::Undefined),
            },
            NativeFn::TaProtoMethod(tag) => self.ta_proto_method(tag, this, args),
            _ => Err(Abrupt::Fatal(format!("binary dispatch: unexpected {nf:?}"))),
        }
    }
}

/// Reorder an 8-byte little-endian block to/from the requested endianness (an
/// involution: LE↔requested is a reverse iff big-endian).
fn read_endian(src: &[u8], little_endian: bool, out: &mut [u8; 8]) {
    if little_endian {
        out.copy_from_slice(&src[..8]);
    } else {
        for i in 0..8 {
            out[i] = src[7 - i];
        }
    }
}

/// Clamp a relative index (result of ToIntegerOrInfinity) into `[0, len]`.
fn clamp_rel(n: f64, len: usize) -> usize {
    #[allow(clippy::cast_precision_loss)]
    let lenf = len as f64;
    if n < 0.0 {
        let k = lenf + n;
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        if k < 0.0 {
            0
        } else {
            k as usize
        }
    } else if n > lenf {
        len
    } else {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        {
            n as usize
        }
    }
}

/// Default CompareTypedArrayElements (no comparefn): ascending, NaN last,
/// -0 before +0.
fn ta_default_cmp(x: f64, y: f64) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let (xn, yn) = (x.is_nan(), y.is_nan());
    if xn && yn {
        Ordering::Equal
    } else if xn {
        Ordering::Greater
    } else if yn {
        Ordering::Less
    } else if x < y {
        Ordering::Less
    } else if x > y {
        Ordering::Greater
    } else if x == 0.0 && y == 0.0 {
        match (x.is_sign_negative(), y.is_sign_negative()) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            _ => Ordering::Equal,
        }
    } else {
        Ordering::Equal
    }
}

impl Interp {
    // -- ArrayBuffer constructor + prototype --------------------------------

    fn max_byte_length_option(&mut self, options: &JsValue) -> Result<Option<usize>, Abrupt> {
        let JsValue::Obj(_) = options else {
            return Ok(None);
        };
        let m = self.get_prop(options, &PropKey::from_str("maxByteLength"))?;
        if matches!(m, JsValue::Undefined) {
            return Ok(None);
        }
        Ok(Some(self.to_index(&m)?))
    }

    fn array_buffer_ctor(&mut self, args: &[JsValue], new_target: Option<&JsValue>) -> ERes {
        let Some(nt) = new_target else {
            return Err(self.throw_type_error());
        };
        let byte_length = self.to_index(args.first().unwrap_or(&JsValue::Undefined))?;
        let max = self.max_byte_length_option(args.get(1).unwrap_or(&JsValue::Undefined))?;
        if let Some(m) = max {
            if byte_length > m {
                return Err(self.throw_native(ErrKind::Range));
            }
        }
        let proto = self.get_prototype_from_constructor(nt, self.intr.array_buffer_proto)?;
        let ab = self.allocate_array_buffer(proto, byte_length, max)?;
        Ok(JsValue::Obj(ab))
    }

    fn array_buffer_slice(&mut self, this: &JsValue, start: &JsValue, end: &JsValue) -> ERes {
        let ab = self.require_array_buffer(this)?;
        if self.ab_is_detached(ab) {
            return Err(self.throw_type_error());
        }
        let len = self.ab_byte_length(ab);
        let rel_start = to_integer_or_infinity(self.to_number(start)?);
        let first = clamp_rel(rel_start, len);
        let rel_end = if matches!(end, JsValue::Undefined) {
            len as f64
        } else {
            to_integer_or_infinity(self.to_number(end)?)
        };
        let final_ = clamp_rel(rel_end, len);
        let new_len = final_.saturating_sub(first);
        let ctor = self.binary_species_constructor(ab, self.intr.array_buffer_ctor)?;
        #[allow(clippy::cast_precision_loss)]
        let new_ab_v = self.construct(&ctor, vec![JsValue::Num(new_len as f64)], None)?;
        let new_ab = self.require_array_buffer(&new_ab_v)?;
        if self.ab_is_detached(new_ab) || new_ab == ab || self.ab_byte_length(new_ab) < new_len {
            return Err(self.throw_type_error());
        }
        // Re-check the source: species construction may have detached it.
        if self.ab_is_detached(ab) {
            return Err(self.throw_type_error());
        }
        let src: Vec<u8> = match &self.heap.obj(ab).kind {
            ObjKind::ArrayBuffer(d) => d.bytes[first..first + new_len].to_vec(),
            _ => return Err(self.throw_type_error()),
        };
        if let ObjKind::ArrayBuffer(d) = &mut self.heap.obj_mut(new_ab).kind {
            d.bytes[..new_len].copy_from_slice(&src);
        }
        Ok(new_ab_v)
    }

    fn array_buffer_resize(&mut self, this: &JsValue, new_length: &JsValue) -> ERes {
        let ab = self.require_array_buffer(this)?;
        if !self.ab_is_resizable(ab) {
            return Err(self.throw_type_error());
        }
        let new_len = self.to_index(new_length)?;
        if self.ab_is_detached(ab) {
            return Err(self.throw_type_error());
        }
        let max = match &self.heap.obj(ab).kind {
            ObjKind::ArrayBuffer(d) => d.max_byte_length.unwrap_or(0),
            _ => 0,
        };
        if new_len > max {
            return Err(self.throw_native(ErrKind::Range));
        }
        if let ObjKind::ArrayBuffer(d) = &mut self.heap.obj_mut(ab).kind {
            d.bytes.resize(new_len, 0);
        }
        Ok(JsValue::Undefined)
    }

    fn array_buffer_transfer(&mut self, this: &JsValue, new_length: &JsValue, to_fixed: bool) -> ERes {
        let ab = self.require_array_buffer(this)?;
        if self.ab_is_detached(ab) {
            return Err(self.throw_type_error());
        }
        let old_len = self.ab_byte_length(ab);
        let new_len = if matches!(new_length, JsValue::Undefined) {
            old_len
        } else {
            self.to_index(new_length)?
        };
        if self.ab_is_detached(ab) {
            return Err(self.throw_type_error());
        }
        let new_max = if to_fixed {
            None
        } else {
            match &self.heap.obj(ab).kind {
                ObjKind::ArrayBuffer(d) => d.max_byte_length,
                _ => None,
            }
        };
        let proto = self.intr.array_buffer_proto;
        let new_ab = self.allocate_array_buffer(proto, new_len, new_max)?;
        let copy = old_len.min(new_len);
        let src: Vec<u8> = match &self.heap.obj(ab).kind {
            ObjKind::ArrayBuffer(d) => d.bytes[..copy].to_vec(),
            _ => Vec::new(),
        };
        if let ObjKind::ArrayBuffer(d) = &mut self.heap.obj_mut(new_ab).kind {
            d.bytes[..copy].copy_from_slice(&src);
        }
        self.detach_buffer(ab);
        Ok(JsValue::Obj(new_ab))
    }

    // -- DataView -----------------------------------------------------------

    fn require_data_view(&mut self, this: &JsValue) -> Result<ObjId, Abrupt> {
        match this {
            JsValue::Obj(o) if matches!(self.heap.obj(*o).kind, ObjKind::DataView(_)) => Ok(*o),
            _ => Err(self.throw_type_error()),
        }
    }

    fn dv_out_of_bounds(&self, dv: ObjId) -> bool {
        let ObjKind::DataView(d) = &self.heap.obj(dv).kind else {
            return true;
        };
        if self.ab_is_detached(d.buffer) {
            return true;
        }
        let buf_len = self.ab_byte_length(d.buffer);
        if d.byte_offset > buf_len {
            return true;
        }
        match d.byte_length {
            Some(n) => d.byte_offset + n > buf_len,
            None => false,
        }
    }

    fn dv_byte_length(&self, dv: ObjId) -> usize {
        let ObjKind::DataView(d) = &self.heap.obj(dv).kind else {
            return 0;
        };
        match d.byte_length {
            Some(n) => n,
            None => self.ab_byte_length(d.buffer).saturating_sub(d.byte_offset),
        }
    }

    fn data_view_ctor(&mut self, args: &[JsValue], new_target: Option<&JsValue>) -> ERes {
        let Some(nt) = new_target else {
            return Err(self.throw_type_error());
        };
        let buffer = self.require_array_buffer(args.first().unwrap_or(&JsValue::Undefined))?;
        let offset = self.to_index(args.get(1).unwrap_or(&JsValue::Undefined))?;
        if self.ab_is_detached(buffer) {
            return Err(self.throw_type_error());
        }
        let buf_len = self.ab_byte_length(buffer);
        if offset > buf_len {
            return Err(self.throw_native(ErrKind::Range));
        }
        let resizable = self.ab_is_resizable(buffer);
        let byte_length: Option<usize> = match args.get(2) {
            None | Some(JsValue::Undefined) => {
                if resizable {
                    None
                } else {
                    Some(buf_len - offset)
                }
            }
            Some(v) => {
                let bl = self.to_index(v)?;
                if offset + bl > buf_len {
                    return Err(self.throw_native(ErrKind::Range));
                }
                Some(bl)
            }
        };
        let proto = self.get_prototype_from_constructor(nt, self.intr.data_view_proto)?;
        if self.ab_is_detached(buffer) {
            return Err(self.throw_type_error());
        }
        let data = trust_js_value::DataViewData { buffer, byte_offset: offset, byte_length };
        let dv = self.alloc_obj(JsObject::new(ObjKind::DataView(data), Some(proto)))?;
        Ok(JsValue::Obj(dv))
    }

    fn data_view_get(
        &mut self,
        this: &JsValue,
        et: ElemType,
        request_index: &JsValue,
        little_endian: &JsValue,
    ) -> ERes {
        let dv = self.require_data_view(this)?;
        let get_index = self.to_index(request_index)?;
        let is_le = self.to_boolean(little_endian);
        if self.dv_out_of_bounds(dv) {
            return Err(self.throw_type_error());
        }
        let view_size = self.dv_byte_length(dv);
        let elem_size = et.bytes_per_element();
        if get_index + elem_size > view_size {
            return Err(self.throw_native(ErrKind::Range));
        }
        let (buffer, base) = match &self.heap.obj(dv).kind {
            ObjKind::DataView(d) => (d.buffer, d.byte_offset + get_index),
            _ => return Err(self.throw_type_error()),
        };
        let ObjKind::ArrayBuffer(d) = &self.heap.obj(buffer).kind else {
            return if et.is_bigint() {
                Ok(JsValue::bigint(JsBigInt::from(0)))
            } else {
                Ok(JsValue::Num(0.0))
            };
        };
        if et.is_bigint() {
            let mut b = [0u8; 8];
            read_endian(&d.bytes[base..base + 8], is_le, &mut b);
            let v = if et == ElemType::BigInt64 {
                bigint_from_i64(i64::from_le_bytes(b))
            } else {
                bigint_from_u64(u64::from_le_bytes(b))
            };
            return Ok(JsValue::bigint(v));
        }
        Ok(JsValue::Num(decode_le(et, is_le, &d.bytes[base..base + elem_size])))
    }

    fn data_view_set(
        &mut self,
        this: &JsValue,
        et: ElemType,
        request_index: &JsValue,
        value: &JsValue,
        little_endian: &JsValue,
    ) -> ERes {
        let dv = self.require_data_view(this)?;
        let get_index = self.to_index(request_index)?;
        // The numeric coercion (ToBigInt for the BigInt views, ToNumber
        // otherwise) is observable and happens before the bounds re-check.
        let big = if et.is_bigint() {
            Some(self.to_bigint(value)?)
        } else {
            None
        };
        let n = if et.is_bigint() {
            0.0
        } else {
            self.to_number(value)?
        };
        let is_le = self.to_boolean(little_endian);
        if self.dv_out_of_bounds(dv) {
            return Err(self.throw_type_error());
        }
        let view_size = self.dv_byte_length(dv);
        let elem_size = et.bytes_per_element();
        if get_index + elem_size > view_size {
            return Err(self.throw_native(ErrKind::Range));
        }
        let (buffer, base) = match &self.heap.obj(dv).kind {
            ObjKind::DataView(d) => (d.buffer, d.byte_offset + get_index),
            _ => return Err(self.throw_type_error()),
        };
        let mut buf = [0u8; 8];
        if let Some(b) = &big {
            let le = if et == ElemType::BigInt64 {
                bigint_to_i64_wrap(b).to_le_bytes()
            } else {
                bigint_to_u64_wrap(b).to_le_bytes()
            };
            read_endian(&le, is_le, &mut buf);
        } else {
            encode_le(et, n, is_le, &mut buf[..elem_size]);
        }
        if let ObjKind::ArrayBuffer(d) = &mut self.heap.obj_mut(buffer).kind {
            d.bytes[base..base + elem_size].copy_from_slice(&buf[..elem_size]);
        }
        Ok(JsValue::Undefined)
    }

    // -- TypedArray construction --------------------------------------------

    fn make_ta(
        &mut self,
        proto: ObjId,
        element: ElemType,
        buffer: ObjId,
        byte_offset: usize,
        array_length: Option<usize>,
    ) -> Result<ObjId, Abrupt> {
        let data = TypedArrayData { buffer, byte_offset, array_length, element };
        self.alloc_obj(JsObject::new(ObjKind::TypedArray(data), Some(proto)))
    }

    fn ta_from_length(&mut self, proto: ObjId, et: ElemType, length: usize) -> Result<ObjId, Abrupt> {
        let byte_len = length
            .checked_mul(et.bytes_per_element())
            .ok_or_else(|| Abrupt::Fatal("typed array byte length overflow".to_string()))?;
        let ab_proto = self.intr.array_buffer_proto;
        let buffer = self.allocate_array_buffer(ab_proto, byte_len, None)?;
        self.make_ta(proto, et, buffer, 0, Some(length))
    }

    fn typed_array_ctor(
        &mut self,
        et: ElemType,
        args: &[JsValue],
        new_target: Option<&JsValue>,
    ) -> ERes {
        let Some(nt) = new_target else {
            return Err(self.throw_type_error());
        };
        let proto = self.get_prototype_from_constructor(nt, self.intr.ta_protos[et.idx()])?;
        let arg0 = args.first().cloned().unwrap_or(JsValue::Undefined);
        let out = match &arg0 {
            JsValue::Obj(src) => {
                let src = *src;
                if self.ta_info(src).is_some() {
                    self.ta_init_from_ta(proto, et, src)?
                } else if matches!(self.heap.obj(src).kind, ObjKind::ArrayBuffer(_)) {
                    self.ta_init_from_buffer(
                        proto,
                        et,
                        src,
                        args.get(1).cloned().unwrap_or(JsValue::Undefined),
                        args.get(2).cloned().unwrap_or(JsValue::Undefined),
                    )?
                } else if self.source_is_iterable(&arg0)? {
                    self.ta_init_from_list(proto, et, &arg0)?
                } else {
                    self.ta_init_from_array_like(proto, et, src)?
                }
            }
            _ => {
                let length = self.to_index(&arg0)?;
                self.ta_from_length(proto, et, length)?
            }
        };
        Ok(JsValue::Obj(out))
    }

    fn ta_init_from_ta(&mut self, proto: ObjId, et: ElemType, src: ObjId) -> Result<ObjId, Abrupt> {
        let src_info = self.ta_info(src).expect("ta");
        if self.ab_is_detached(src_info.buffer) {
            return Err(self.throw_type_error());
        }
        if src_info.element.is_bigint() != et.is_bigint() {
            return Err(self.throw_type_error());
        }
        let len = self.ta_current_length(src);
        let out = self.ta_from_length(proto, et, len)?;
        let out_info = self.ta_info(out).expect("ta");
        for i in 0..len {
            let v = self.ta_get_value_at(src_info, i);
            self.ta_store_value_at(out_info, i, &v);
        }
        Ok(out)
    }

    fn ta_init_from_buffer(
        &mut self,
        proto: ObjId,
        et: ElemType,
        buffer: ObjId,
        byte_offset: JsValue,
        length: JsValue,
    ) -> Result<ObjId, Abrupt> {
        let bpe = et.bytes_per_element();
        let offset = self.to_index(&byte_offset)?;
        if offset % bpe != 0 {
            return Err(self.throw_native(ErrKind::Range));
        }
        let length_undef = matches!(length, JsValue::Undefined);
        let explicit_len = if length_undef { 0 } else { self.to_index(&length)? };
        if self.ab_is_detached(buffer) {
            return Err(self.throw_type_error());
        }
        let buf_len = self.ab_byte_length(buffer);
        let resizable = self.ab_is_resizable(buffer);
        let array_length: Option<usize> = if length_undef {
            if resizable {
                if offset > buf_len {
                    return Err(self.throw_native(ErrKind::Range));
                }
                None
            } else {
                if buf_len < offset || (buf_len - offset) % bpe != 0 {
                    return Err(self.throw_native(ErrKind::Range));
                }
                Some((buf_len - offset) / bpe)
            }
        } else {
            let need = offset
                .checked_add(explicit_len.checked_mul(bpe).ok_or_else(|| {
                    Abrupt::Fatal("typed array byte length overflow".to_string())
                })?)
                .ok_or_else(|| Abrupt::Fatal("typed array byte length overflow".to_string()))?;
            if need > buf_len {
                return Err(self.throw_native(ErrKind::Range));
            }
            Some(explicit_len)
        };
        self.make_ta(proto, et, buffer, offset, array_length)
    }

    /// Is `v` iterable for construction purposes? A provably-untampered
    /// intrinsic iterator (arrays, strings, maps, sets) is detected WITHOUT
    /// touching the danger-listed intrinsic @@iterator slot; otherwise a
    /// GetMethod(v, @@iterator) decides (safe on non-intrinsic chains).
    fn source_is_iterable(&mut self, v: &JsValue) -> Result<bool, Abrupt> {
        if self.get_fast_iterator(v).is_ok() {
            return Ok(true);
        }
        Ok(self
            .get_method(v, &PropKey::Sym(SymId::WellKnown(WkSym::Iterator)))?
            .is_some())
    }

    fn ta_init_from_list(&mut self, proto: ObjId, et: ElemType, iterable: &JsValue) -> Result<ObjId, Abrupt> {
        let mut values: Vec<JsValue> = Vec::new();
        let mut it = self.get_iterator_or_type_error(iterable)?;
        loop {
            match self.fast_iter_next(&mut it) {
                Ok(Some(v)) => {
                    self.charge_loop()?;
                    values.push(v);
                }
                Ok(None) => break,
                Err(a) => return Err(a),
            }
        }
        let out = self.ta_from_length(proto, et, values.len())?;
        #[allow(clippy::cast_precision_loss)]
        for (k, v) in values.into_iter().enumerate() {
            self.ta_set_element(out, k as f64, v)?;
        }
        Ok(out)
    }

    fn ta_init_from_array_like(&mut self, proto: ObjId, et: ElemType, src: ObjId) -> Result<ObjId, Abrupt> {
        let len = usize::try_from(self.length_of_array_like(src)?)
            .map_err(|_| Abrupt::Fatal("array-like length overflow".to_string()))?;
        let out = self.ta_from_length(proto, et, len)?;
        for k in 0..len {
            let kv = self.get_from_object(src, &PropKey::from_str(&k.to_string()), JsValue::Obj(src))?;
            #[allow(clippy::cast_precision_loss)]
            self.ta_set_element(out, k as f64, kv)?;
        }
        Ok(out)
    }

    // -- %TypedArray%.from / of ---------------------------------------------

    fn typed_array_from(&mut self, this: &JsValue, args: &[JsValue]) -> ERes {
        if !self.is_constructor(this) {
            return Err(self.throw_type_error());
        }
        let source = args.first().cloned().unwrap_or(JsValue::Undefined);
        let mapfn = args.get(1).cloned().unwrap_or(JsValue::Undefined);
        let mapping = !matches!(mapfn, JsValue::Undefined);
        if mapping && !matches!(&mapfn, JsValue::Obj(o) if self.heap.obj(*o).is_callable()) {
            return Err(self.throw_type_error());
        }
        let this_arg = args.get(2).cloned().unwrap_or(JsValue::Undefined);
        let values: Vec<JsValue> = if self.source_is_iterable(&source)? {
            let mut vals = Vec::new();
            let mut it = self.get_iterator_or_type_error(&source)?;
            loop {
                match self.fast_iter_next(&mut it) {
                    Ok(Some(v)) => {
                        self.charge_loop()?;
                        vals.push(v);
                    }
                    Ok(None) => break,
                    Err(a) => return Err(a),
                }
            }
            vals
        } else {
            let obj = self.to_object(&source)?;
            let len = usize::try_from(self.length_of_array_like(obj)?)
                .map_err(|_| Abrupt::Fatal("array-like length overflow".to_string()))?;
            let mut vals = Vec::with_capacity(len);
            for k in 0..len {
                vals.push(self.get_from_object(obj, &PropKey::from_str(&k.to_string()), JsValue::Obj(obj))?);
            }
            vals
        };
        #[allow(clippy::cast_precision_loss)]
        let target = self.typed_array_create(this, vec![JsValue::Num(values.len() as f64)])?;
        for (k, v) in values.into_iter().enumerate() {
            #[allow(clippy::cast_precision_loss)]
            let mapped = if mapping {
                self.call_value(&mapfn, this_arg.clone(), vec![v, JsValue::Num(k as f64)])?
            } else {
                v
            };
            #[allow(clippy::cast_precision_loss)]
            self.ta_set_element(target, k as f64, mapped)?;
        }
        Ok(JsValue::Obj(target))
    }

    fn typed_array_of(&mut self, this: &JsValue, args: &[JsValue]) -> ERes {
        if !self.is_constructor(this) {
            return Err(self.throw_type_error());
        }
        #[allow(clippy::cast_precision_loss)]
        let target = self.typed_array_create(this, vec![JsValue::Num(args.len() as f64)])?;
        for (k, v) in args.iter().enumerate() {
            #[allow(clippy::cast_precision_loss)]
            self.ta_set_element(target, k as f64, v.clone())?;
        }
        Ok(JsValue::Obj(target))
    }

    // -- shared prototype methods -------------------------------------------

    fn ta_create_same_type(&mut self, et: ElemType, len: usize) -> Result<ObjId, Abrupt> {
        let proto = self.intr.ta_protos[et.idx()];
        self.ta_from_length(proto, et, len)
    }

    #[allow(clippy::too_many_lines, clippy::cast_precision_loss)]
    fn ta_proto_method(&mut self, tag: &str, this: JsValue, args: Vec<JsValue>) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        match tag {
            "at" => {
                let (oid, _et, len) = self.ta_validate(&this)?;
                let rel = to_integer_or_infinity(self.to_number(&arg(0))?);
                let k = if rel >= 0.0 { rel } else { len as f64 + rel };
                if k < 0.0 || k >= len as f64 {
                    Ok(JsValue::Undefined)
                } else {
                    Ok(self.ta_element_get_pure(oid, k))
                }
            }
            "fill" => {
                let (oid, et, len) = self.ta_validate(&this)?;
                // The fill value is coerced (observable) before the range args.
                let value: JsValue = if et.is_bigint() {
                    JsValue::bigint(self.to_bigint(&arg(0))?)
                } else {
                    JsValue::Num(self.to_number(&arg(0))?)
                };
                let start = clamp_rel(to_integer_or_infinity(self.to_number(&arg(1))?), len);
                let end = if matches!(arg(2), JsValue::Undefined) {
                    len
                } else {
                    clamp_rel(to_integer_or_infinity(self.to_number(&arg(2))?), len)
                };
                let len2 = self.ta_current_length(oid);
                let info = self.ta_info(oid).expect("ta");
                for i in start..end.min(len2) {
                    self.ta_store_value_at(info, i, &value);
                }
                Ok(this)
            }
            "join" => {
                let (oid, _et, len) = self.ta_validate(&this)?;
                let sep = if matches!(arg(0), JsValue::Undefined) {
                    units_from_str(",")
                } else {
                    self.to_string_units(&arg(0))?
                };
                let mut out: Units = Vec::new();
                for k in 0..len {
                    if k > 0 {
                        out.extend_from_slice(&sep);
                    }
                    let v = self.ta_element_get_pure(oid, k as f64);
                    if !matches!(v, JsValue::Undefined) {
                        let s = self.to_string_units(&v)?;
                        out.extend_from_slice(&s);
                    }
                }
                Ok(JsValue::Str(std::rc::Rc::new(out)))
            }
            "indexOf" | "lastIndexOf" => {
                let last = tag == "lastIndexOf";
                let (oid, _et, len) = self.ta_validate(&this)?;
                let search = arg(0);
                if len == 0 {
                    return Ok(JsValue::Num(-1.0));
                }
                let has_from = args.len() > 1;
                let from = to_integer_or_infinity(self.to_number(&arg(1))?);
                let order: Vec<usize> = if last {
                    let start = if !has_from {
                        len as isize - 1
                    } else if from >= 0.0 {
                        (from as isize).min(len as isize - 1)
                    } else {
                        len as isize + from as isize
                    };
                    (0..=start.max(-1)).rev().filter(|i| *i >= 0).map(|i| i as usize).collect()
                } else {
                    if from >= len as f64 {
                        return Ok(JsValue::Num(-1.0));
                    }
                    let start = if from >= 0.0 { from as isize } else { (len as isize + from as isize).max(0) };
                    (start.max(0) as usize..len).collect()
                };
                for k in order {
                    let v = self.ta_element_get_pure(oid, k as f64);
                    if crate::ops::strict_eq(&v, &search) {
                        return Ok(JsValue::Num(k as f64));
                    }
                }
                Ok(JsValue::Num(-1.0))
            }
            "includes" => {
                let (oid, _et, len) = self.ta_validate(&this)?;
                // ECMA-262 22.2.3.13 step 3 / Array.prototype.includes step 3:
                // if len is 0, return false BEFORE ToIntegerOrInfinity(fromIndex)
                // (whose coercion is observable and may throw).
                if len == 0 {
                    return Ok(JsValue::Bool(false));
                }
                let search = arg(0);
                let from = to_integer_or_infinity(self.to_number(&arg(1))?);
                let start = if from >= 0.0 {
                    from as isize
                } else {
                    (len as isize + from as isize).max(0)
                };
                for k in start.max(0) as usize..len {
                    let v = self.ta_element_get_pure(oid, k as f64);
                    if crate::ops::same_value_zero(&v, &search) {
                        return Ok(JsValue::Bool(true));
                    }
                }
                Ok(JsValue::Bool(false))
            }
            "reverse" => {
                let (oid, et, len) = self.ta_validate(&this)?;
                let bpe = et.bytes_per_element();
                let info = self.ta_info(oid).expect("ta");
                let off = info.byte_offset;
                if let ObjKind::ArrayBuffer(d) = &mut self.heap.obj_mut(info.buffer).kind {
                    for i in 0..len / 2 {
                        let a = off + i * bpe;
                        let b = off + (len - 1 - i) * bpe;
                        if a + bpe <= d.bytes.len() && b + bpe <= d.bytes.len() {
                            for k in 0..bpe {
                                d.bytes.swap(a + k, b + k);
                            }
                        }
                    }
                }
                Ok(this)
            }
            "copyWithin" => {
                let (oid, et, len) = self.ta_validate(&this)?;
                let to = clamp_rel(to_integer_or_infinity(self.to_number(&arg(0))?), len);
                let from = clamp_rel(to_integer_or_infinity(self.to_number(&arg(1))?), len);
                let final_ = if matches!(arg(2), JsValue::Undefined) {
                    len
                } else {
                    clamp_rel(to_integer_or_infinity(self.to_number(&arg(2))?), len)
                };
                let mut count = final_.saturating_sub(from).min(len.saturating_sub(to));
                let len2 = self.ta_current_length(oid);
                count = count.min(len2.saturating_sub(to)).min(len2.saturating_sub(from));
                if count > 0 {
                    let bpe = et.bytes_per_element();
                    let info = self.ta_info(oid).expect("ta");
                    let from_b = info.byte_offset + from * bpe;
                    let to_b = info.byte_offset + to * bpe;
                    let cnt_b = count * bpe;
                    if let ObjKind::ArrayBuffer(d) = &mut self.heap.obj_mut(info.buffer).kind {
                        if from_b + cnt_b <= d.bytes.len() && to_b + cnt_b <= d.bytes.len() {
                            d.bytes.copy_within(from_b..from_b + cnt_b, to_b);
                        }
                    }
                }
                Ok(this)
            }
            "set" => self.ta_set_method(&this, &arg(0), &arg(1)),
            "subarray" => self.ta_subarray(&this, &arg(0), &arg(1)),
            "slice" => self.ta_slice(&this, &arg(0), &arg(1)),
            "every" | "some" | "forEach" | "find" | "findIndex" | "findLast" | "findLastIndex" => {
                self.ta_iter_predicate(tag, &this, &arg(0), &arg(1))
            }
            "map" => self.ta_map(&this, &arg(0), &arg(1)),
            "filter" => self.ta_filter(&this, &arg(0), &arg(1)),
            "reduce" | "reduceRight" => {
                self.ta_reduce(tag == "reduceRight", &this, &arg(0), args.get(1).cloned())
            }
            "sort" => self.ta_sort(&this, &arg(0), false),
            "toSorted" => self.ta_sort(&this, &arg(0), true),
            "toReversed" => {
                let (oid, et, len) = self.ta_validate(&this)?;
                let out = self.ta_create_same_type(et, len)?;
                let src = self.ta_info(oid).expect("ta");
                let dst = self.ta_info(out).expect("ta");
                for i in 0..len {
                    let v = self.ta_get_value_at(src, len - 1 - i);
                    self.ta_store_value_at(dst, i, &v);
                }
                Ok(JsValue::Obj(out))
            }
            "with" => {
                let (oid, et, len) = self.ta_validate(&this)?;
                // ECMA-262 23.2.3.36 %TypedArray%.prototype.with:
                // `len` (step 3) is captured before any user coercion. The
                // index bounds check (step 9) is IsValidIntegerIndex, which is
                // re-evaluated against the CURRENT length AFTER the numeric
                // coercion (step 8) — a resizable buffer grown inside a
                // valueOf can make a formerly out-of-bounds index valid.
                let rel = to_integer_or_infinity(self.to_number(&arg(0))?);
                let actual = if rel >= 0.0 { rel } else { len as f64 + rel };
                let value: JsValue = if et.is_bigint() {
                    JsValue::bigint(self.to_bigint(&arg(1))?)
                } else {
                    JsValue::Num(self.to_number(&arg(1))?)
                };
                if !self.ta_is_valid_index(oid, actual) {
                    return Err(self.throw_native(ErrKind::Range));
                }
                let out = self.ta_create_same_type(et, len)?;
                let src = self.ta_info(oid).expect("ta");
                let dst = self.ta_info(out).expect("ta");
                for i in 0..len {
                    let v = self.ta_get_value_at(src, i);
                    self.ta_store_value_at(dst, i, &v);
                }
                // The result array A has length `len`; the replacement is only
                // observable when actualIndex falls within [0, len) (the copy
                // loop's index range). A valid-but-beyond-`len` index (buffer
                // grown during coercion) leaves A as a pure copy.
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let ai = actual as usize;
                if actual >= 0.0 && ai < len {
                    self.ta_store_value_at(dst, ai, &value);
                }
                Ok(JsValue::Obj(out))
            }
            "values" | "keys" | "entries" => {
                // 23.2.3.{32,17,6}: ValidateTypedArray, then CreateArrayIterator
                // over the typed array (shares %ArrayIteratorPrototype%).
                let (oid, _, _) = self.ta_validate(&this)?;
                let kind = match tag {
                    "keys" => crate::iterobj::IterKind::Key,
                    "entries" => crate::iterobj::IterKind::KeyValue,
                    _ => crate::iterobj::IterKind::Value,
                };
                self.make_typed_array_iterator(oid, kind)
            }
            "toLocaleString" => Err(Abrupt::Fatal(
                "%TypedArray%.prototype.toLocaleString (locale-dependent, out of slice)".to_string(),
            )),
            _ => Err(Abrupt::Fatal(format!("typed-array method `{tag}` (out of slice)"))),
        }
    }

    #[allow(clippy::cast_precision_loss)]
    fn ta_set_method(&mut self, this: &JsValue, source: &JsValue, offset: &JsValue) -> ERes {
        let target = self.require_ta(this)?;
        let target_offset = to_integer_or_infinity(self.to_number(offset)?);
        if target_offset < 0.0 {
            return Err(self.throw_native(ErrKind::Range));
        }
        if self.ta_out_of_bounds(target) {
            return Err(self.throw_type_error());
        }
        let target_len = self.ta_current_length(target);
        if let JsValue::Obj(so) = source {
            if let Some(src_info) = self.ta_info(*so) {
                if src_info.element.is_bigint() != self.ta_info(target).expect("ta").element.is_bigint() {
                    return Err(self.throw_type_error());
                }
                let src_len = self.ta_current_length(*so);
                if target_offset + src_len as f64 > target_len as f64 {
                    return Err(self.throw_native(ErrKind::Range));
                }
                let vals: Vec<JsValue> =
                    (0..src_len).map(|i| self.ta_get_value_at(src_info, i)).collect();
                let t_info = self.ta_info(target).expect("ta");
                let base = target_offset as usize;
                for (i, v) in vals.into_iter().enumerate() {
                    self.ta_store_value_at(t_info, base + i, &v);
                }
                return Ok(JsValue::Undefined);
            }
        }
        // Array-like source.
        let src = self.to_object(source)?;
        let src_len = self.length_of_array_like(src)?;
        if target_offset + src_len as f64 > target_len as f64 {
            return Err(self.throw_native(ErrKind::Range));
        }
        let base = target_offset as usize;
        for k in 0..src_len {
            let kv = self.get_from_object(src, &PropKey::from_str(&k.to_string()), JsValue::Obj(src))?;
            self.ta_set_element(target, (base as u64 + k) as f64, kv)?;
        }
        Ok(JsValue::Undefined)
    }

    #[allow(clippy::cast_precision_loss)]
    fn ta_subarray(&mut self, this: &JsValue, begin: &JsValue, end: &JsValue) -> ERes {
        let oid = self.require_ta(this)?;
        let info = self.ta_info(oid).expect("ta");
        let len = self.ta_current_length(oid);
        let bpe = info.element.bytes_per_element();
        let begin_i = clamp_rel(to_integer_or_infinity(self.to_number(begin)?), len);
        let is_tracking = info.array_length.is_none();
        let end_undef = matches!(end, JsValue::Undefined);
        let begin_byte = info.byte_offset + begin_i * bpe;
        let args = if is_tracking && end_undef {
            vec![JsValue::Obj(info.buffer), JsValue::Num(begin_byte as f64)]
        } else {
            let end_i = if end_undef {
                len
            } else {
                clamp_rel(to_integer_or_infinity(self.to_number(end)?), len)
            };
            let new_len = end_i.saturating_sub(begin_i);
            vec![
                JsValue::Obj(info.buffer),
                JsValue::Num(begin_byte as f64),
                JsValue::Num(new_len as f64),
            ]
        };
        let out = self.ta_species_create(oid, args)?;
        Ok(JsValue::Obj(out))
    }

    #[allow(clippy::cast_precision_loss)]
    fn ta_slice(&mut self, this: &JsValue, start: &JsValue, end: &JsValue) -> ERes {
        let (oid, _et, len) = self.ta_validate(this)?;
        let k = clamp_rel(to_integer_or_infinity(self.to_number(start)?), len);
        let final_ = if matches!(end, JsValue::Undefined) {
            len
        } else {
            clamp_rel(to_integer_or_infinity(self.to_number(end)?), len)
        };
        let count = final_.saturating_sub(k);
        let out = self.ta_species_create(oid, vec![JsValue::Num(count as f64)])?;
        if count > 0 {
            if self.ta_out_of_bounds(oid) {
                return Err(Abrupt::Fatal(
                    "typed-array slice source detached during species create (out of slice)"
                        .to_string(),
                ));
            }
            let src = self.ta_info(oid).expect("ta");
            for i in 0..count {
                if k + i < self.ta_current_length(oid) {
                    let v = self.ta_get_value_at(src, k + i);
                    self.ta_set_element(out, i as f64, v)?;
                }
            }
        }
        Ok(JsValue::Obj(out))
    }

    #[allow(clippy::cast_precision_loss)]
    fn ta_iter_predicate(&mut self, tag: &str, this: &JsValue, cb: &JsValue, this_arg: &JsValue) -> ERes {
        let (oid, _et, len) = self.ta_validate(this)?;
        if !matches!(cb, JsValue::Obj(o) if self.heap.obj(*o).is_callable()) {
            return Err(self.throw_type_error());
        }
        let reverse = tag == "findLast" || tag == "findLastIndex";
        let indices: Vec<usize> = if reverse {
            (0..len).rev().collect()
        } else {
            (0..len).collect()
        };
        for k in indices {
            self.charge_loop()?;
            let v = self.ta_element_get_pure(oid, k as f64);
            let r = self.call_value(cb, this_arg.clone(), vec![v.clone(), JsValue::Num(k as f64), this.clone()])?;
            let truthy = self.to_boolean(&r);
            match tag {
                "every" => {
                    if !truthy {
                        return Ok(JsValue::Bool(false));
                    }
                }
                "some" => {
                    if truthy {
                        return Ok(JsValue::Bool(true));
                    }
                }
                "forEach" => {}
                "find" | "findLast" => {
                    if truthy {
                        return Ok(v);
                    }
                }
                "findIndex" | "findLastIndex" => {
                    if truthy {
                        return Ok(JsValue::Num(k as f64));
                    }
                }
                _ => {}
            }
        }
        match tag {
            "every" => Ok(JsValue::Bool(true)),
            "some" => Ok(JsValue::Bool(false)),
            "forEach" => Ok(JsValue::Undefined),
            "find" | "findLast" => Ok(JsValue::Undefined),
            _ => Ok(JsValue::Num(-1.0)),
        }
    }

    #[allow(clippy::cast_precision_loss)]
    fn ta_map(&mut self, this: &JsValue, cb: &JsValue, this_arg: &JsValue) -> ERes {
        let (oid, _et, len) = self.ta_validate(this)?;
        if !matches!(cb, JsValue::Obj(o) if self.heap.obj(*o).is_callable()) {
            return Err(self.throw_type_error());
        }
        let out = self.ta_species_create(oid, vec![JsValue::Num(len as f64)])?;
        for k in 0..len {
            self.charge_loop()?;
            let v = self.ta_element_get_pure(oid, k as f64);
            let mapped = self.call_value(cb, this_arg.clone(), vec![v, JsValue::Num(k as f64), this.clone()])?;
            self.ta_set_element(out, k as f64, mapped)?;
        }
        Ok(JsValue::Obj(out))
    }

    #[allow(clippy::cast_precision_loss)]
    fn ta_filter(&mut self, this: &JsValue, cb: &JsValue, this_arg: &JsValue) -> ERes {
        let (oid, _et, len) = self.ta_validate(this)?;
        if !matches!(cb, JsValue::Obj(o) if self.heap.obj(*o).is_callable()) {
            return Err(self.throw_type_error());
        }
        let mut kept: Vec<JsValue> = Vec::new();
        for k in 0..len {
            self.charge_loop()?;
            let v = self.ta_element_get_pure(oid, k as f64);
            let r = self.call_value(cb, this_arg.clone(), vec![v.clone(), JsValue::Num(k as f64), this.clone()])?;
            if self.to_boolean(&r) {
                kept.push(v);
            }
        }
        let out = self.ta_species_create(oid, vec![JsValue::Num(kept.len() as f64)])?;
        for (i, v) in kept.into_iter().enumerate() {
            self.ta_set_element(out, i as f64, v)?;
        }
        Ok(JsValue::Obj(out))
    }

    #[allow(clippy::cast_precision_loss)]
    fn ta_reduce(&mut self, right: bool, this: &JsValue, cb: &JsValue, initial: Option<JsValue>) -> ERes {
        let (oid, _et, len) = self.ta_validate(this)?;
        if !matches!(cb, JsValue::Obj(o) if self.heap.obj(*o).is_callable()) {
            return Err(self.throw_type_error());
        }
        let order: Vec<usize> = if right { (0..len).rev().collect() } else { (0..len).collect() };
        let mut iter = order.into_iter();
        let mut acc = match initial {
            Some(v) => v,
            None => match iter.next() {
                Some(k) => self.ta_element_get_pure(oid, k as f64),
                None => return Err(self.throw_type_error()),
            },
        };
        for k in iter {
            self.charge_loop()?;
            let v = self.ta_element_get_pure(oid, k as f64);
            acc = self.call_value(cb, JsValue::Undefined, vec![acc, v, JsValue::Num(k as f64), this.clone()])?;
        }
        Ok(acc)
    }

    fn ta_sort(&mut self, this: &JsValue, comparefn: &JsValue, to_sorted: bool) -> ERes {
        let has_cmp = !matches!(comparefn, JsValue::Undefined);
        if has_cmp && !matches!(comparefn, JsValue::Obj(o) if self.heap.obj(*o).is_callable()) {
            return Err(self.throw_type_error());
        }
        let (oid, et, len) = self.ta_validate(this)?;
        let info = self.ta_info(oid).expect("ta");
        let mut vals: Vec<JsValue> = (0..len).map(|i| self.ta_get_value_at(info, i)).collect();
        if has_cmp {
            self.ta_merge_sort(&mut vals, comparefn)?;
        } else {
            vals.sort_by(ta_default_value_cmp);
        }
        if to_sorted {
            let out = self.ta_create_same_type(et, len)?;
            let dst = self.ta_info(out).expect("ta");
            for (i, v) in vals.iter().enumerate() {
                self.ta_store_value_at(dst, i, v);
            }
            Ok(JsValue::Obj(out))
        } else {
            // Write back into the live view (clamped to the current length).
            let len2 = self.ta_current_length(oid);
            let info = self.ta_info(oid).expect("ta");
            for (i, v) in vals.iter().enumerate().take(len2) {
                self.ta_store_value_at(info, i, v);
            }
            Ok(this.clone())
        }
    }

    /// Stable bottom-up merge sort with a user comparefn (SortCompare) over
    /// element values (Number or BigInt).
    fn ta_merge_sort(&mut self, vals: &mut [JsValue], comparefn: &JsValue) -> Result<(), Abrupt> {
        let n = vals.len();
        if n < 2 {
            return Ok(());
        }
        let mut buf = vals.to_vec();
        let mut width = 1;
        while width < n {
            let mut i = 0;
            while i < n {
                let left = i;
                let mid = (i + width).min(n);
                let right = (i + 2 * width).min(n);
                let (mut a, mut b, mut k) = (left, mid, left);
                while a < mid && b < right {
                    self.charge_loop()?;
                    let c = self.ta_compare(&vals[a], &vals[b], comparefn)?;
                    if c <= 0.0 {
                        buf[k] = vals[a].clone();
                        a += 1;
                    } else {
                        buf[k] = vals[b].clone();
                        b += 1;
                    }
                    k += 1;
                }
                while a < mid {
                    buf[k] = vals[a].clone();
                    a += 1;
                    k += 1;
                }
                while b < right {
                    buf[k] = vals[b].clone();
                    b += 1;
                    k += 1;
                }
                i += 2 * width;
            }
            vals.clone_from_slice(&buf);
            width *= 2;
        }
        Ok(())
    }

    fn ta_compare(&mut self, x: &JsValue, y: &JsValue, comparefn: &JsValue) -> Result<f64, Abrupt> {
        let r = self.call_value(comparefn, JsValue::Undefined, vec![x.clone(), y.clone()])?;
        let v = self.to_number(&r)?;
        Ok(if v.is_nan() { 0.0 } else { v })
    }
}

/// Default CompareTypedArrayElements over element values: Number arrays use
/// the NaN-last / -0-before-+0 rule; BigInt arrays use plain integer order.
fn ta_default_value_cmp(a: &JsValue, b: &JsValue) -> std::cmp::Ordering {
    match (a, b) {
        (JsValue::Num(x), JsValue::Num(y)) => ta_default_cmp(*x, *y),
        (JsValue::BigInt(x), JsValue::BigInt(y)) => x.cmp(y),
        _ => std::cmp::Ordering::Equal,
    }
}
