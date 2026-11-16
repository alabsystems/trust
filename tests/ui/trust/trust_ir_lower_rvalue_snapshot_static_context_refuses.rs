//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (2026-09-16, rvalue-snapshot admission — negative control (iii),
//! conjunct C1 of `rvalue_temp_is_unpromotable`): in a `static` initializer
//! rustc PROMOTES a `const fn` call temporary (`promote_consts::validate_call`
//! — `promote_all_fn` is true for `ConstContext::Static(_)` and for a
//! promotion-allowing `Const`), so `&g()` here CAN be a `'static` and an
//! aggregate holding its pointer is legally returnable while the producer's
//! slot is a stack `Alloca`: exactly the divergence the wave-PF exclusion
//! exists for. The predicate declines by BODY CONTEXT before it looks at the
//! shape, the tuple keeps its `Tuple(borrow ptr field)` refusal, and under
//! `strict` the static's initializer body is an error.
//!
//! The pin is a MUTATION pin: `g` is not `#[rustc_promotable]`, so with C1
//! removed the shape half answers "unpromotable", the field is admitted, the
//! body lowers, and the error below disappears. The same shape in an ordinary
//! fn body IS admitted — `through_tuple` in
//! `trust_ir_lower_rvalue_snapshot_field.rs` is that twin.

#![allow(dead_code)]

const fn g() -> i32 {
    7
}

static S: (&i32,) = (&g(),);
//~^ ERROR -Ztrust-ir-lower=strict

fn main() {}
