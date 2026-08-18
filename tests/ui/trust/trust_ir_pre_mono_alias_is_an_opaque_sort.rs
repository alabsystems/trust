//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//
// Trust (#201, B8 slice 1) regression: a PRE-MONOMORPHIZATION alias is a SORT, not a gap — and
// the boundary of that claim is exactly the oracle's, on both sides.
//
// THE LANE. `map_ty`'s `ty::Alias` arm normalizes an alias to its concrete type and fails closed
// when it cannot. Four conditions used to share one fail-closed disjunct, and one of them does
// not belong there: an alias that still carries a non-region generic parameter is not an alias
// the producer FAILED to resolve, it is one that is not resolvable yet by construction, and the
// oracle already models it. `trust-mir-extract/src/ty_convert.rs`'s `normalize_alias` tests
// `alias_ty.has_non_region_param()` FIRST and mints the shared
// `trust_types::PRE_MONO_ALIAS_{KIND,DETAIL}` marker; `trust-ir-bridge/src/lower.rs` then lowers
// that marker to a registered opaque ZERO-FIELD struct named
// `"opaque_alias::pre_monomorphization"`. #201 makes the producer reach the same type by the same
// test, so the two sides spell such a body the same way.
//
// WHY A ZERO-FIELD STRUCT AND NOT `Unit`. `Unit` is a single-valued carrier that trust-mc
// concretizes to 0 — a value of an unknown type would acquire a known value. A zero-field struct
// is a per-binding opaque symbol with no interpreted equality and no arithmetic sort, so it can
// neither discharge nor falsely satisfy an arithmetic, bounds, or switch obligation; a primitive
// op ranging over it makes module validation reject the module instead. The body is still
// recorded SYMBOLIC (`param_opaque`), which keeps it out of the differential and the splice — it
// is a clean lowering of an opaque carrier, never a modelled value.
//
// (a) THE ADMITTED CASE — every alias below still mentions a caller's `T`, so each is pre-mono
//     and each lowers to the collapsed opaque struct. `<T as Carrier>::Item` in a parameter, in a
//     return, and in a local all take the same lane. Before #201 each pushed a bare `"Ty"` tag
//     and the body did not lower.

trait Carrier {
    type Item;
    fn get(&self) -> Self::Item;
}

// Alias in return position.
fn takes_alias_out<T: Carrier>(c: &T) -> <T as Carrier>::Item {
    c.get()
}

// Alias in parameter position, and again as a local's type. Both aliases share ONE registered
// struct: extraction erases every pre-mono alias to the SAME marker `Ty` value, so the oracle's
// `type_cache` collapses them, and the producer collapses to match. Two structs where the oracle
// has one would be the same module spelled two ways for no gain — the sort is fact-free either
// way.
fn takes_alias_in<T: Carrier>(c: &T, _seen: <T as Carrier>::Item) -> usize {
    let _also_an_alias: <T as Carrier>::Item = c.get();
    0
}

// An `impl Trait` that still mentions the caller's `T` is pre-mono FIRST and opaque SECOND. This
// is the case the ORDER of the tests decides: `has_non_region_param` is checked before
// `has_opaque_types`, matching `normalize_alias`, which routes `AliasTyKind::Opaque` and
// `Projection`/`Inherent` into the same guard. Test the order, not just the predicate.
fn opaque_over_a_param<T: Clone>(t: T) -> impl Clone {
    t
}

// (b) THE BOUNDARY THAT MUST HOLD. A zero-argument opaque — an RPIT with no generic parameters —
//     is NOT pre-monomorphization; it is monomorphic but unrevealed. The oracle fails it closed
//     with a different detail ("opaque alias has no typing env to reveal against") and
//     `trust-ir-bridge`'s `test_monomorphic_alias_details_still_fail_type_mapping` pins that it
//     keeps failing closed. Nothing here may admit it. Revealing it would also mean demanding a
//     hidden type from inside `mir_built`, which is the E0391 reentrancy family (#179) — the
//     reason `trust_ir_lower_rpit_no_cycle.rs` exists. This function must still compile; the
//     claim is that it lowers no differently than it did before #201.

fn no_params_at_all() -> impl Clone {
    7u32
}

// A fully concrete associated type is monomorphic and gets NORMALIZED, not opacified — the lane
// #201 touches is only the one the normalizer declines. This is the control.

struct Concrete;
impl Carrier for Concrete {
    type Item = u32;
    fn get(&self) -> u32 {
        1
    }
}

fn concrete_alias_still_normalizes(c: &Concrete) -> <Concrete as Carrier>::Item {
    c.get()
}

// DELIBERATELY NO CALLS to the generic functions above. Instantiating them from `main` links a
// monomorphic call site against a declaration whose signature carries the opaque sort, and the
// producer's call-coherence check then reports `CallArgTypeMismatch` / `InstrResultArityMismatch`
// — measured: exactly 3 such errors when this file called all five. That is the known
// generic-declaration-meets-monomorphic-call-site carrier lane (the residual 27 `CallArgTypeMismatch`
// in the corpus), NOT a property of this slice, and a regression test that manufactures an
// ill-formed module would pollute the corpus it is measured against. What this file pins is how the
// generic bodies LOWER; linking them is a different item's subject.
// (Measured: calling all five produced 3 such errors; calling only the concrete control still
// produced 1, from the `&Concrete` argument — the same carrier lane, unrelated to aliases. An
// empty `main` produces a module with ZERO validation errors, so this file measures exactly what
// it claims to and nothing else.)
fn main() {}
