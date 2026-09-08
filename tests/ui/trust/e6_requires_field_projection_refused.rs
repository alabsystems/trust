//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ dont-require-annotations: WARN
//@ check-fail
//! E6 — a projection with no exact scalar place is REFUSED, and says why.
//!
//! This is the direction that decides whether the feature is sound. A contract
//! that silently means something other than what it says is worse than no
//! contract, so the resolution NEVER invents a name: every segment of an
//! authored chain must resolve to a real field index of a single-variant,
//! non-enum, non-union aggregate whose leaf has an exact scalar domain, looked
//! up verbatim in a `ProjectionEnvironment` built from the parameter's real
//! layout. A miss fails the WHOLE clause closed — it is never partially
//! admitted, never weakened to a free variable, and never downgraded to a
//! silent `Unsupported`.
//!
//! It also has to say WHY. Before the attribution note below, the surviving
//! diagnostic named the chain's HEAD ("source-contract variable `o` is not in
//! scope") — pointing the author at a token that IS a parameter, when the
//! problem is the field path. The note names the chain.
//!
//! The last function is the control: nested scalar leaves ARE admitted, so the
//! refusals above are a property of the shapes, not a blanket refusal of depth.

pub enum Mode {
    A(usize),
    B(usize),
}

pub struct Inner {
    pub k: usize,
}

pub struct Outer {
    pub scalar: usize,
    pub nested: Inner,
    pub by_ref: &'static Inner,
    pub mode: Mode,
    pub floating: f64,
}

pub union Bits {
    pub a: u64,
    pub b: f64,
}

// 1. No such field: the chain resolves nothing.
pub fn no_such_field(o: &Outer) -> usize
    requires o.nope != 0
//~^ ERROR invalid `requires` clause
{
    o.scalar
}

// 2. Through a REFERENCE-typed field. `place_to_var_name` renders a Deref as a
//    POSTFIX `*`, and only a LEADING deref is writable as source text
//    (`(*o)`), so a mid-chain deref has no spelling — the walk stops at the
//    reference rather than guessing one.
pub fn through_reference(o: &Outer) -> usize
    requires o.by_ref.k != 0
//~^ ERROR invalid `requires` clause
{
    o.scalar
}

// 3. An ENUM field sits behind a discriminant, so it has no unconditional
//    place and the field view is variant-dependent.
pub fn enum_field(o: &Outer) -> usize
    requires o.mode.0 != 0
//~^ ERROR invalid `requires` clause
{
    o.scalar
}

// 4. A UNION field aliases its siblings.
pub fn union_field(b: &Bits) -> u64
    requires b.a != 0
//~^ ERROR invalid `requires` clause
{
    0
}

// 5. A float leaf has no exact proposition domain today, so no leaf is minted
//    for it and the chain does not resolve.
pub fn float_field(o: &Outer) -> usize
    requires o.floating != 0
//~^ ERROR invalid `requires` clause
{
    o.scalar
}

// 6. `base.method(..)` is a CALL, not a place: no stable name.
pub fn method_on_projection(o: &Outer) -> usize
    requires o.nested.k.count_ones() != 0
//~^ ERROR invalid `requires` clause
{
    o.scalar
}

// 7. A type still carrying generic parameters has no field layout to pin.
pub struct Wrap<T> {
    pub value: T,
}

pub fn generic_field<T>(w: &Wrap<T>) -> usize
    requires w.value != 0
//~^ ERROR invalid `requires` clause
{
    0
}

// CONTROL — a nested scalar leaf IS admitted, and discharges the division.
pub fn nested_ok(o: &Outer) -> usize
    requires o.nested.k != 0
{
    o.scalar / o.nested.k
}
