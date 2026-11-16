//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off --crate-type=lib
// wave-EMO: a `match` over an OPAQUE-LANE enum (one `register_enum` declined
// end-to-end — a param-instantiated enum in a generic body, a fat/dyn
// payload) lowers as an N-WAY NONDETERMINISTIC SPLIT: an `Undef Bool`
// `CondBr` chain (the `lower_let_opaque_test` posture generalized from 2 to
// N), every payload binding bound to a FRESH fact-free unit const at
// `Ty::Unit` + `opaque_carrier_locals` (the scrutinee's value — under the
// ref-peel, the `self` POINTER — is lowered for effects only and never
// laundered into a carrier), and `contains_call` FORCED so the body is
// structurally NotRun (an eager-UB Undef is never interpreted; the
// over-approximate split can discharge nothing). The arm BODIES lower
// VISIBLY — only the variant selection is abstracted. v1 fences, each with
// its own tag: no guards, no or-patterns, no nested/literal subpatterns,
// no promoted bindings.

// The generic-derive shape: a match over a param-instantiated enum.
pub enum E<T> {
    A(T),
    B(i64),
    C,
}

pub fn classify<T>(e: E<T>) -> i64 {
    match e {
        E::A(_t) => 1,
        E::B(n) => n,
        E::C => 3,
    }
}

// A catch-all BINDING arm (`other => ..`) is rejected UPSTREAM of this lane
// (`EnumMatch(unsupported pattern)` — the match router's own classifier), so
// the lane's whole-enum-carrier arm is defensively present but unreachable
// today. This body must NOT lower; it pins where that shape actually stops.
pub fn opaque_bind<T>(e: E<T>) -> i64 {
    match e {
        E::C => 0,
        other => {
            let _ = other;
            9
        }
    }
}

// The ref-scrutinee twin (`match *self` via match ergonomics): the pointer
// is never bound; the split still lowers the arm effects.
pub fn by_ref<T>(e: &E<T>) -> i64 {
    match e {
        E::A(_) => 1,
        E::B(_) => 2,
        E::C => 3,
    }
}

// A 2-arm guarded shape routes through an EARLIER lane (the opaque let-test
// family) and lowers there — recorded so nobody reads it as this lane's
// guard support. The lane's own guard refusal is defensively present.
pub fn guarded<T>(e: E<T>, b: bool) -> i64 {
    match e {
        E::C if b => 0,
        _ => 1,
    }
}

// NEGATIVE — a NESTED payload subpattern keeps failing closed (measured
// tag: `EnumMatch(nested payload arm no same-variant fallback)` — an
// earlier nested-pattern classifier claims the shape before this lane's
// own `opaque payload subpattern` refusal); this body must NOT lower.
pub enum Inner {
    X,
    Y,
}
pub fn nested<T>(e: E<Inner>, _t: T) -> i64 {
    match e {
        E::A(Inner::X) => 1,
        E::A(Inner::Y) => 2,
        E::B(_) => 3,
        E::C => 4,
    }
}
