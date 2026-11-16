// trust-types: `ConstValue::OpaqueScalar` round-trips through bincode
// (OPAQUE-SCALAR-WIRE-1, 2026-10-07).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//
// From the adversarial verification of fix/opaque-scalar-identity (685267f885),
// where all three tests FAILED. It is a WIRE regression, not a false proof: no
// production path found bincode-DEcodes a `ConstValue`, but
// `constant_image/tests.rs::memory_image_json_and_binary_round_trip_preserve_complete_graph`
// round-trips `ConstValue` through bincode as a supported wire, and trust-certify
// compares `bincode::serialize` identity bytes.
//
// 685267f885 gave `ConstValue::OpaqueScalar { origin }`
// `#[serde(default, skip_serializing_if = "OpaqueOrigin::is_positional")]`.
// bincode wrote no origin for a positional (Site / Unplaced) occurrence, but its
// decoder always reads a third field, so it consumed the NEXT value's bytes as an
// `OpaqueOrigin`: `(OpaqueScalar{64,u}, Int(7))` decoded to
// `Err(Io(UnexpectedEof))`, and a keyed occurrence's bytes were the keyless
// one's plus a suffix, so identity bytes stopped being self-delimiting.
//
// The fix (`opaque_identity::serialize_opaque_scalar`): a non-human-readable
// format always writes `key: Option<String>`; positional origins are never
// written in any format; JSON keeps the legacy shape (origin only when keyed).

use trust_types::{ConstValue, Operand, Rvalue};

fn json(v: &impl serde::Serialize) -> serde_json::Value {
    serde_json::to_value(v).expect("json")
}

#[test]
fn positional_opaque_scalar_followed_by_another_operand_round_trips_through_bincode() {
    let pair = (
        Operand::Constant(ConstValue::opaque_scalar(64, false)),
        Operand::Constant(ConstValue::Int(7)),
    );
    let bytes = bincode::serialize(&pair).expect("serialize");
    let back: (Operand, Operand) = bincode::deserialize(&bytes).unwrap_or_else(|e| {
        panic!("bincode round-trip of a positional OpaqueScalar failed: {e:?}")
    });
    assert_eq!(json(&back), json(&pair));
}

#[test]
fn keyed_and_positional_opaque_scalars_both_round_trip_through_bincode() {
    let rv = Rvalue::BinaryOp(
        trust_types::BinOp::Sub,
        Operand::Constant(ConstValue::opaque_scalar(64, false)),
        Operand::Constant(ConstValue::opaque_scalar_const(64, false, "K@00".into())),
    );
    let bytes = bincode::serialize(&rv).expect("serialize");
    let back: Rvalue = bincode::deserialize(&bytes)
        .unwrap_or_else(|e| panic!("bincode round-trip of an opaque-scalar rvalue failed: {e:?}"));
    assert_eq!(json(&back), json(&rv));
}

#[test]
fn opaque_scalar_bincode_encoding_is_prefix_free() {
    let keyless = bincode::serialize(&ConstValue::opaque_scalar(64, false)).unwrap();
    let keyed =
        bincode::serialize(&ConstValue::opaque_scalar_const(64, false, String::new())).unwrap();
    assert!(
        !keyed.starts_with(&keyless),
        "a keyed OpaqueScalar's bincode bytes extend the keyless one's: {keyless:?} / {keyed:?}"
    );
}

#[test]
fn the_json_wire_keeps_the_legacy_shape() {
    let keyless = serde_json::to_string(&ConstValue::opaque_scalar(64, false)).unwrap();
    assert_eq!(keyless, r#"{"OpaqueScalar":{"width":64,"signed":false}}"#);
    let keyed =
        serde_json::to_string(&ConstValue::opaque_scalar_const(32, true, "K".into())).unwrap();
    assert_eq!(
        keyed,
        r#"{"OpaqueScalar":{"width":32,"signed":true,"origin":{"Const":{"key":"K"}}}}"#
    );
    for text in [keyless, keyed] {
        let back: ConstValue = serde_json::from_str(&text).unwrap();
        assert_eq!(serde_json::to_string(&back).unwrap(), text);
    }
}

#[test]
fn the_bincode_wire_keeps_the_key_and_drops_the_site() {
    let keyed = ConstValue::opaque_scalar_const(32, true, "K@01".into());
    let back: ConstValue = bincode::deserialize(&bincode::serialize(&keyed).unwrap()).unwrap();
    assert_eq!(json(&back), json(&keyed));
    // A positional origin is re-derived by placement, never carried: a placed and
    // an unplaced occurrence encode identically.
    let mut placed = ConstValue::opaque_scalar(64, false);
    if let ConstValue::OpaqueScalar { origin, .. } = &mut placed {
        *origin = trust_types::opaque_identity::OpaqueOrigin::Site { block: 3, stmt: 1, slot: 0 };
    }
    assert_eq!(
        bincode::serialize(&placed).unwrap(),
        bincode::serialize(&ConstValue::opaque_scalar(64, false)).unwrap()
    );
}
