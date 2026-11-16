//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on --crate-type=lib
//! Trust (OPAQUE-CARRIER-SINKS-1, 2026-10-13): **an opaque-lane carrier never reaches an
//! indirect call or a constructor field at a type its spelling is not.**
//!
//! `lower_enum_match_opaque` lowers a `match` over an enum the producer declined (`Kind` here:
//! its `Placeholder` variant carries a `NonNull<()>` and a fn pointer) as a nondeterministic
//! split, and binds every payload binding to one fact-free carrier, `Const { ty: Unit,
//! PhantomData }`. Its contract is that every value-needing use of a carrier "fails closed at its
//! own site or rides an opaque channel"; three sites did neither, and each emitted ill-typed IR
//! that failed final validation of the WHOLE crate module (measured on this file before the
//! fix):
//!
//!   * `formatter(value, s)` — a `CallIndirect` whose callee AND first argument were the carrier:
//!     `CallIndirectArgTypeMismatch { arg_index: 0, expected: "struct.0", actual: "()" }`;
//!   * `Some(c)` — an enum payload: `OperandTypeMismatch { op: "insert_field", expected: "one of
//!     {Some: u16}", actual: "()" }`;
//!   * `Wide { c }` — a struct-literal field: `OperandTypeMismatch { op: "insert_field",
//!     expected: "u16", actual: "()" }`.
//!
//! These are `core`'s `fmt::rt::Argument::fmt` and `Argument::as_u16` over the declined
//! `fmt::rt::ArgumentType` (docs/KNOWN_HAZARDS.md, the `core` entry of 2026-10-05), the last
//! two of the four errors that kept `core`'s crate module from validating. Each site now
//! refuses its body (`Call(fn-ptr opaque carrier callee)`, `Call(opaque carrier typed
//! argument)`, `EnumCtor(opaque carrier payload)`, `Adt(opaque carrier field)`; read off
//! `-Ztrust-dump=ir`'s `coverage.json`): lowered for
//! coverage only, never spliced. `plain` is the control: a real `u16` payload still constructs.
//!
//! `call_with` isolates the ARGUMENT sink: its callee is a real fn-pointer parameter, and only
//! `value` is the carrier (`lower_call_args` used to be handed no expected types for a
//! `CallIndirect`).
//!
//! No `.stderr` and no `dont-check-compiler-stderr`: the pin is that this lane prints NOTHING,
//! so the finalization warning fails this file on a producer that emits any of these.

#![allow(dead_code)]

use std::marker::PhantomData;
use std::ptr::NonNull;

pub struct Sink {
    pub n: u32,
}

enum Kind<'a> {
    Placeholder {
        value: NonNull<()>,
        formatter: unsafe fn(NonNull<()>, &mut Sink) -> u32,
        _lifetime: PhantomData<&'a ()>,
    },
    Count(u16),
}

pub struct Arg<'a> {
    kind: Kind<'a>,
}

pub struct Wide {
    pub c: u16,
}

impl Arg<'_> {
    pub unsafe fn call(&self, s: &mut Sink) -> u32 {
        match self.kind {
            Kind::Placeholder { formatter, value, .. } => unsafe { formatter(value, s) },
            Kind::Count(_) => 0,
        }
    }

    pub unsafe fn call_with(
        &self,
        f: unsafe fn(NonNull<()>, &mut Sink) -> u32,
        s: &mut Sink,
    ) -> u32 {
        match self.kind {
            Kind::Placeholder { value, .. } => unsafe { f(value, s) },
            Kind::Count(_) => 0,
        }
    }

    pub fn as_u16(&self) -> Option<u16> {
        match self.kind {
            Kind::Count(c) => Some(c),
            Kind::Placeholder { .. } => None,
        }
    }

    pub fn as_wide(&self) -> Option<Wide> {
        match self.kind {
            Kind::Count(c) => Some(Wide { c }),
            Kind::Placeholder { .. } => None,
        }
    }
}

pub fn plain(x: u16) -> Option<u16> {
    Some(x)
}
