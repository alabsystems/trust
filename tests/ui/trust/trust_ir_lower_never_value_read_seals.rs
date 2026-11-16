//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on --crate-type=lib
//! Trust (DIRECT-LANE-1.101-DRIFT, 2026-10-19): **a body whose tail READS a `!`-typed value
//! seals `Unreachable`, so the crate module still validates.**
//!
//! 1.101's `core` spells `<TryFromIntError as From<!>>::from` as `fn from(never: !) ->
//! TryFromIntError { never }` (it was `match never {}`). THIR wraps the tail in `NeverToAny`,
//! whose source here is a plain read of the parameter: no diverging terminator seals the block.
//! The producer passed the read through, so the body returned a `!` from a struct-returning
//! function and the validator rejected the WHOLE crate module (measured on `core`):
//!
//!     ReturnTypeMismatch { block: 0, expected: "struct.13", actual: "!" }
//!
//! The coercion point is unreachable (no value of type `!` exists), so it is now sealed
//! `Unreachable`, as rustc's MIR builder terminates it. `panics` (a `!` call) and `loops` (a
//! `loop` with no `break`) are diverging sources of the same coercion, as controls.
//!
//! No `.stderr` and no `dont-check-compiler-stderr`: the pin is that this lane prints NOTHING,
//! so the finalization warning fails this file on a producer that returns the `!` value.

pub struct Wrapped {
    pub code: u8,
}

pub fn from_never(never: !) -> Wrapped {
    never
}

pub fn panics() -> Wrapped {
    panic!("no value")
}

pub fn loops() -> Wrapped {
    loop {}
}
