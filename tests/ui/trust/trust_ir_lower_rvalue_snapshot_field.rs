//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (2026-09-16, rvalue-snapshot admission — the r09 closure): a wave-SB
//! snapshot of an RVALUE TEMPORARY that rustc PROVABLY CANNOT PROMOTE may sit
//! in a THIN-ref aggregate field, on the same borrowck argument wave-PF makes
//! for a named local (`trust_ir_lower_borrow_ptr_field.rs`, the control).
//!
//! The rule is rustc's own (`promote_consts::validate_call`): a call temporary
//! promotes only when the callee is `#[rustc_promotable]`, or when the body is
//! a `static` / promotion-allowing `const` initializer AND the callee is a
//! `const fn`; an aggregate whose operand is such a temporary is unpromotable
//! too. So `&f(x)` here is a frame temporary that can never be `'static`, and
//! borrowck forbids returning an aggregate that holds it — exactly the
//! named-local case, one word changed. The predicate
//! (`rvalue_temp_is_unpromotable`) reads the THIR shape and two rustc queries;
//! never a producer tag, never `map_ty`'s output.
//!
//! THE ADMITTED SHAPE is the one `format_args!` expands to at this rustc for
//! every non-empty argument list — `super let args = (&f(x),); … args.0` —
//! whose tuple element is the wave-SB CALL-ARGUMENT snapshot of an rvalue
//! temporary. That mint is the one site that consults rustc's promotability
//! rule (`rvalue_temp_is_unpromotable`: a non-`#[rustc_promotable]` `FnDef`
//! call, or an aggregate holding one, outside a const-fn-promoting body) and
//! ledgers the pointer `borrow_ptr_field_admissible`'s `&T` arm admits. So a
//! `println!` of a call result, of a mixed plain/call list, and a `panic!`
//! with a call result all lower under strict, and `std::io::_print` /
//! `std::rt::panic_fmt` are signed `(struct.K) -> ()` (the run-make twin
//! pins the signature).
//!
//! UPDATED 2026-10-01 (D28): each lowers with no producer tag, but the
//! `fmt::rt::Argument` array it builds carries the opaque `()` placeholder for
//! the collapsed `ArgumentType` enum, so the effect-conservation gate refuses the
//! three bodies under strict, by name. The gate errs only on a body the producer
//! lowered clean, so each annotation still pins the admission this file is about
//! (`trust_ir_lower_format_args_effects.rs` says the same).
//!
//! NOT admitted, and pinned as residue in
//! `trust_ir_lower_rvalue_snapshot_field_direct_residue.rs`: a USER-WRITTEN
//! aggregate literal with a borrowed rvalue field handed to a call —
//! `take((&f(x),))`, `S { r: &g(y), .. }` — is minted at a different borrow
//! site and still refuses `Tuple/Adt(borrow ptr field)`. Same borrowck
//! argument, different mint; widening it is a separate landing, not a claim
//! this file makes.

#![allow(dead_code)]

struct S<'a> {
    r: &'a u32,
    tag: u8,
}

fn f(x: u32) -> u32 {
    x.wrapping_add(41)
}

fn g(y: u32) -> u32 {
    y.wrapping_mul(3)
}

// The callees CARRY the aggregate and never read through its pointer lane: a
// pointer lane read back out of an aggregate is unledgered (wave-PR) and every
// deref of it fails closed, which is a separate question from this file's —
// the control (`trust_ir_lower_borrow_ptr_field.rs`) spells its callees the
// same way for the same reason.




pub fn prints_a_call(x: u32) {
    //~^ ERROR Abstracted(opaque-lane
    println!("{}", f(x));
}

pub fn mixed_shapes(x: u32) {
    //~^ ERROR Abstracted(opaque-lane
    println!("{}", f(x));
    println!("{}", x);
}

pub fn panics_with_a_call(x: u32) {
    //~^ ERROR Abstracted(opaque-lane
    if x == 0 {
        panic!("zero, and f gives {}", f(x));
    }
}

fn main() {
    prints_a_call(5);
    mixed_shapes(6);
    panics_with_a_call(7);
}
