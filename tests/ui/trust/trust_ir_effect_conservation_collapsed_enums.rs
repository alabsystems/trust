//@ revisions: flow store
//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! D28: an enum the producer COLLAPSES to a placeholder — `Option<(u32, u32)>` to its
//! discriminant `bool`, `fmt::rt::ArgumentType` to `()` — is the opaque lane WHEREVER the body
//! holds it by value, and such a body never passes strict.
//!
//! The first effect-conservation gate (97de0ab9ac) looked for the placeholder only as a lone
//! `bool`/`()` parameter, result, paired-call value or escaping store, and on degraded struct
//! profiles the RMW builder registers. Its 2026-10-01 review found every body below `conserved`,
//! strict-clean and spliced, each with trust-ir that does not carry the program's value:
//!
//! * `ret_tuple` returns `(bool true, u32 4)` — the payload `(a, a)` is gone;
//! * `store_tuple` stores `(bool, u32)` through `p`: the `u32` lands at offset 4, where the
//!   program's `(Option<(u32, u32)>, u32)` has it at offset 12;
//! * `store_struct` stores `S { o: bool true, n: 3 }`: the payload is never written;
//! * `by_ref` and `cmp` pass 1-byte `bool` slots to callees that read a 12-byte `Option`
//!   (`cmp` compares `true == true`);
//! * `slice_elem` indexes with a 1-byte stride (`gep bool`) instead of 12;
//! * `fmt` (any `format_args!` with an argument) hands `Arguments::new` an array of
//!   `fmt::rt::Argument { ty: () }`, a layout-less placeholder.
//!
//! The gate now reads the lane off the MIR oracle's types: an enum type the body holds by value
//! anywhere (a local, a place at any projection step, through struct / tuple / array fields)
//! that the producer collapsed (`LowerCx::opaque_lane_tys`, written where `map_ty` collapses).
//! A body that only passes a POINTER to such a value on (`consume_ref`, `ref_ret`) holds none
//! and stays clean.
//! Whole-struct replacement now rejects its incomplete representation at the Store
//! boundary, before the later effect-conservation gate. Other opaque flows retain
//! their original `Abstracted(opaque-lane)` refusal. Separate revisions ensure the
//! early producer refusal cannot suppress those later effect-conservation diagnostics.

pub type O = Option<(u32, u32)>;

pub struct S {
    pub o: O,
    pub n: u32,
}

#[cfg(flow)]
pub fn ret_tuple(a: u32) -> (O, u32) {
    //[flow]~^ ERROR Abstracted(opaque-lane
    (Some((a, a)), 4)
}

#[cfg(flow)]
pub fn store_tuple(p: &mut (O, u32)) {
    //[flow]~^ ERROR Abstracted(opaque-lane
    *p = (None, 1);
}

#[cfg(store)]
pub fn store_struct(s: &mut S, a: u32) {
    //[store]~^ ERROR Assign(whole struct incomplete type)
    *s = S { o: Some((a, 2)), n: 3 };
}

#[inline(never)]
pub fn consume_ref(o: &O) -> u32 {
    if o.is_some() { 1 } else { 0 }
}

#[cfg(flow)]
pub fn by_ref(a: u32) -> u32 {
    //[flow]~^ ERROR Abstracted(opaque-lane
    let o: O = Some((a, 1));
    consume_ref(&o)
}

#[cfg(flow)]
pub fn cmp(a: u32) -> bool {
    //[flow]~^ ERROR Abstracted(opaque-lane
    let x: O = Some((a, 1));
    let y: O = Some((a, 2));
    x == y
}

#[cfg(flow)]
pub fn slice_elem(a: &[O], i: usize) -> bool {
    //[flow]~^ ERROR Abstracted(opaque-lane
    a[i].is_some()
}

#[cfg(flow)]
pub fn fmt(x: u32) -> String {
    //[flow]~^ ERROR Abstracted(opaque-lane
    format!("v={x}")
}

/// A pointer to the value, passed on: no value of the enum is held, and no tag.
pub fn ref_ret(a: &O) -> &O {
    a
}
