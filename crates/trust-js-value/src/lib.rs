// trust-js-value: the TrustJS value model — M1 D2 (see Cargo.toml).
//
// The faithful tier's value model, written from ECMA-262 (never translated
// from an engine): WTF-16 strings (`Units`), the canonical Number::toString,
// JS values, a heap of ordinary objects with the full property-descriptor
// model (data + accessor properties, spec own-key order, prototype chains,
// extensibility), environment records with TDZ, and the realm intrinsics
// table. Every partially-modeled intrinsic carries a miss-danger set so the
// interpreter can refuse — instead of mis-answering — any lookup that a real
// engine would resolve against surface this model does not carry.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod bigint;
mod binary;
mod env;
mod global_names;
mod heap;
mod number;
mod object;
mod realm;
mod units;
mod value;

pub use bigint::{
    as_int_n, as_uint_n, bigint_binary, bigint_cmp, bigint_cmp_f64, bigint_eq_f64, bigint_from_bool,
    bigint_from_i64, bigint_from_u64, bigint_is_zero, bigint_neg, bigint_not, bigint_to_decimal,
    bigint_to_f64, bigint_to_i64_wrap, bigint_to_radix, bigint_to_u64_wrap, f64_to_bigint_exact,
    parse_bigint_literal, string_to_bigint, BigErr, BigOp, JsBigInt,
};
pub use binary::{
    decode_le, encode_le, f16_bits_to_f64, f64_to_f16_bits, to_uint8_clamp,
};
pub use env::{Binding, EnvFrame};
pub use global_names::is_realm_global_name;
pub use heap::Heap;
pub use number::{
    exact_uint32, js_number_to_string, numeric_literal_mv, projection_number_repr,
    to_int32, to_integer_or_infinity, to_length_u64, to_number_str, to_uint32,
};
pub use object::{
    ordered_own_keys, ArgsData, ArrayBufferData, BoundFn, DataViewData, ElemType, ErrKind, FnData,
    FnFlavor, JsObject, MapData, ObjKind, PropKey, PropValue, Property, ProxyData, RegexData,
    RegexFlags, SetData, TypedArrayData, UserFn, WrapperPrim,
};
pub use realm::{
    create_realm, Danger, DateField, DateSetKind, Intrinsics, NativeFn, Realm, RegexFlagKind,
    ERROR_INSTANCE_DANGER,
};
pub use units::{array_index_of, units_eq_ascii, units_from_str, units_to_lossy, Units};
pub use value::{EnvId, JsValue, ObjId, SymId, WkSym};
