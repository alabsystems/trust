#![crate_type = "lib"]
#![allow(dead_code)]
#![allow(unreachable_patterns)]

// Keep every public entry point scalar-parameterized. The interpreter
// differential must execute these bodies instead of classifying an enum or
// aggregate parameter as a coverage-only skip.

pub fn option_default_match(payload: i32, present: bool) -> i32 {
    let value = if present { Some(payload) } else { None };
    match value {
        Some(value) => value,
        None => 0,
    }
}

#[repr(i16)]
enum SignedTag {
    Negative = -5,
    Positive = 7,
}

pub fn signed_negative_discriminant(negative: bool) -> i16 {
    let value = if negative { SignedTag::Negative } else { SignedTag::Positive };
    match value {
        SignedTag::Negative => -5,
        SignedTag::Positive => 7,
    }
}

enum MultiPayload {
    Single(i64),
    Pair(i64, i64),
}

pub fn multi_payload_field_lanes(first: i64, second: i64, select_first: bool) -> i64 {
    let value = MultiPayload::Pair(first, second);
    match value {
        MultiPayload::Single(value) => value,
        MultiPayload::Pair(left, right) => {
            if select_first {
                left
            } else {
                right
            }
        }
    }
}

enum Fieldless {
    Initial,
    Reassigned,
}

pub fn fieldless_reassignment(reassign: bool) -> i64 {
    let mut value = Fieldless::Initial;
    if reassign {
        value = Fieldless::Reassigned;
    }
    match value {
        Fieldless::Initial => 1,
        Fieldless::Reassigned => 2,
    }
}

enum HeldMode {
    Left,
    Right,
}

struct Holder {
    mode: HeldMode,
    payload: i64,
}

pub fn nested_holder_round_trip(payload: i64, right: bool) -> i64 {
    let held = Holder { mode: if right { HeldMode::Right } else { HeldMode::Left }, payload };
    match held {
        Holder { mode: HeldMode::Left, payload } => payload,
        Holder { mode: HeldMode::Right, .. } => 17,
    }
}

// These two legal-but-unreachable source shapes are negative controls for arm
// order. Once `_` appears, retaining a later variant arm would change Rust's
// first-match semantics; the direct lowerer must fail closed instead.
pub fn option_wildcard_before_variant(payload: i32, present: bool) -> i32 {
    let value = if present { Some(payload) } else { None };
    match value {
        _ => 11,
        Some(_) => 22,
    }
}

pub fn multi_wildcard_before_variant(first: i64, second: i64) -> i64 {
    let value = MultiPayload::Pair(first, second);
    match value {
        _ => 31,
        MultiPayload::Pair(left, right) => left + right,
    }
}

// A diverging guard seals its own THIR-lowering block. The enum lowerer must
// record a fail-closed guard refusal without trying to seal that block twice.
pub fn option_diverging_guard(payload: i32) -> i32 {
    let value = Some(payload);
    match value {
        Some(_) if { return 41 } => 0,
        Some(value) => value,
        None => 0,
    }
}

pub fn multi_diverging_guard(first: i64, second: i64) -> i64 {
    let value = MultiPayload::Pair(first, second);
    match value {
        MultiPayload::Pair(_, _) if { return 43 } => 0,
        MultiPayload::Pair(left, right) => left + right,
        MultiPayload::Single(value) => value,
    }
}
