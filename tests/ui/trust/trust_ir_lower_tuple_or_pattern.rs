//@ revisions: positive nested by_ref non_scalar effectful promoted promote_wanted enum_promote_wanted
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-check-compiler-stderr
//@[positive] run-pass

//! Top-level tuple-or patterns are an ORDERED candidate chain, not one Boolean
//! predicate.  Each alternative owns its field-to-local map; a false guard
//! retries the next overlapping alternative before the next source arm.
//!
//! The seven negative revisions keep the semantic boundary closed and pin their
//! precise refusal tags.  The scorecard manifest classifies this post-baseline
//! campaign fixture as excluded from the seeded population.

#[cfg(positive)]
fn permuted_fields(t: (i32, i32, i32)) -> i32 {
    match t {
        (1, a, b) | (2, b, a) => a * 100 + b,
        _ => -1,
    }
}

/// Both alternatives match `(1, 2)`, but bind `a` from different fields. The
/// first alternative wins, so this returns 2 rather than 1.
#[cfg(positive)]
fn overlapping_source_order(t: (i32, i32)) -> i32 {
    match t {
        (1, a) | (a, 2) => a,
        _ => -1,
    }
}

/// On `(1, 2)` alternative zero binds `a = 2` and its guard fails; Rust then
/// retries alternative one, binds `a = 1`, and its guard succeeds.
#[cfg(positive)]
fn guard_false_retries_next_alternative(t: (i32, i32)) -> i32 {
    match t {
        (1, a) | (a, 2) if a == 1 => a,
        _ => -1,
    }
}

#[cfg(positive)]
fn main() {
    let ok = permuted_fields((1, 2, 3)) == 203
        && permuted_fields((2, 7, 4)) == 407
        && overlapping_source_order((1, 2)) == 2
        && overlapping_source_order((3, 2)) == 3
        && guard_false_retries_next_alternative((1, 2)) == 1
        && guard_false_retries_next_alternative((1, 3)) == -1;
    if !ok {
        std::process::exit(1);
    }
}

// A field-level `Or` is nested; this increment only expands the arm root.
#[cfg(nested)]
pub fn nested_field_or(t: (i32, i32)) -> i32 {
    //[nested]~^ ERROR TupleMatch(or-pattern)
    match t {
        (1 | 2, x) => x,
        _ => 0,
    }
}

// Binding a pointer instead of a scalar value remains the classifier's own
// precise refusal; the tuple-or agreement gate never overrides it.
#[cfg(by_ref)]
pub fn by_ref_alternative(t: (i32, i32)) -> i32 {
    //[by_ref]~^ ERROR TupleMatch(by-ref subpattern)
    match t {
        (1, ref a) | (2, ref a) => *a,
        _ => 0,
    }
}

// A tuple-valued field is not a scalar carrier even though both alternatives
// bind the same Rust local and type.
// (RE-PINNED 2026-09-14: the literal field is an INT — a `bool` literal is refused earlier,
// as `TupleMatch(bool literal field)`, before any bind gate is consulted — and the or-lane's
// bind witness names the refusal: an alternative binding a non-scalar carrier is refused as
// `or-pattern alternative not scalar by-value` (measured on the 2026-09-14 stage1).)
#[cfg(non_scalar)]
pub fn non_scalar_binding(t: ((i32, i32), i32)) -> i32 {
    //[non_scalar]~^ ERROR TupleMatch(or-pattern alternative not scalar by-value)
    match t {
        (pair, 1) | (pair, 2) => pair.0,
        _ => 0,
    }
}

// Repeating this guard could repeat observable state. The ordered expansion's
// guard language is an explicit read-only scalar allow-list.
#[cfg(effectful)]
pub fn effectful_guard(t: (i32, i32), mut count: i32) -> i32 {
    //[effectful]~^ ERROR TupleMatch(or-pattern effectful guard)
    match t {
        (1, x) | (2, x)
            if {
                count += 1;
                x > 0
            } =>
        {
            count
        }
        _ => count,
    }
}

// Re-lowering one body in sibling blocks cannot reuse a promoted slot whose
// Alloca is defined only in the first block.
#[cfg(promoted)]
pub fn promoted_local_in_shared_body(t: (i32, i32)) -> i32 {
    //[promoted]~^ ERROR TupleMatch(or-arm body duplicated with promotable local)
    match t {
        (1, x) | (2, x) => {
            let mut y = x;
            let r = &mut y;
            *r += 1;
            y
        }
        _ => 0,
    }
}

// A shared aggregate-field borrow initially records only `promote_wanted`.
// The first body copy would opportunistically promote `pair`; the second would
// then reuse its sibling-defined slot unless this pre-expansion gate reads both
// promotion ledgers.
#[cfg(promote_wanted)]
pub fn promotion_wanted_local_in_shared_body(t: (i32, i32)) -> i32 {
    //[promote_wanted]~^ ERROR TupleMatch(or-arm body duplicated with promotable local)
    match t {
        (1, x) | (2, x) => {
            let pair = (x, 7);
            let r = &pair.0;
            *r
        }
        _ => 0,
    }
}

// The pre-existing enum-Or expansion duplicates a shared body in exactly the
// same sibling-block shape and therefore must read the wanted-only ledger too.
#[cfg(enum_promote_wanted)]
pub fn enum_promotion_wanted_local_in_shared_body(e: EnumCarrier) -> i32 {
    //[enum_promote_wanted]~^ ERROR EnumMatch(or-arm body duplicated with promoted local)
    match e {
        EnumCarrier::A(x) | EnumCarrier::B(x) => {
            let pair = (x, 7);
            let r = &pair.0;
            *r
        }
        EnumCarrier::C => 0,
    }
}

#[cfg(enum_promote_wanted)]
pub enum EnumCarrier {
    A(i32),
    B(i32),
    C,
}

#[cfg(not(positive))]
fn main() {}
