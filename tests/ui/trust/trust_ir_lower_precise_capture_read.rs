//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-PCR): reading a PRECISELY-CAPTURED place through the closure env -- the read twin
//! of the compound-assign write lane.
//!
//! FOUR sites ask "which env slot holds this captured variable?" and one asks a different
//! question. Three READ-side sites -- the `UpvarRef` arm, the `&upvar` helper, the `&mut upvar`
//! helper -- all ask `projections.is_empty()`, i.e. "is this the WHOLE variable?". The fourth,
//! the compound-assign RMW lane, asks the right one: "is there exactly ONE capture whose
//! projection spelling EQUALS the spelling of the place being touched?" That machinery was built
//! for the WRITE (`t.0.0 += v`) and the READ side was left on the old question.
//!
//! Under RFC 2229 a non-`move` closure that reads only `t.0` captures exactly `t.0`: the env
//! holds `&i32` and the tuple `t` NEVER EXISTS inside the closure. So the whole-variable question
//! has no answer, and refusing at the `UpvarRef` EXPRESSION stays correct -- fabricating the
//! tuple would be unsound. The value that DOES exist is the one at the FIELD expression, and that
//! is where nobody asked. The read arm's own doc already said the conjunct "refuses it only
//! because it asks the wrong question", and then fixed one special case rather than the general
//! one.
//!
//! MONOTONICITY IS CHECKED, NOT ASSUMED. The only competing clean path for a projected capture
//! requires the capture spelling to be exactly `[Deref]`; this lane's spellings are Field-only,
//! so the two populations are disjoint by construction. `shared_ref_base_unchanged` below is that
//! control -- it is clean TODAY because rustc truncates its capture to `[Deref]`, and it must
//! stay on that path.
//!
//! THE ENV FIELD IS A COPY, and that is why the leaf gate matters. The constructor emits
//! `load t; extractfield N; alloca; store; insertfield`, so the env points at a fresh copy rather
//! than at `t.N`. That is exact only because a shared capture FREEZES the place; the scalar-leaf
//! gate is what makes an `UnsafeCell` leaf unreachable (`map_ty` does not flatten
//! `repr(transparent)`), so the copy cannot go stale.
//!
//! Not under `=strict`: the negatives below must keep their tags.

#![allow(dead_code, unused_variables)]

// THE LANE: the `no_migrations` corpus shape. A non-`move` closure reading one tuple field
// captures exactly that field, by shared ref.
pub fn tuple_field_capture() -> i32 {
    let t = (1i32, 2i32);
    let c = || {
        let x = t.0;
        x
    };
    c()
}

pub fn tuple_field_capture_1() -> i32 {
    let t = (1i32, 2i32);
    let c = || t.1;
    c()
}

// The same shape through a STRUCT base.
pub struct S {
    a: i32,
    b: u8,
}

pub fn struct_field_capture() -> i32 {
    let s = S { a: 5, b: 6 };
    let c = || s.a;
    c()
}

// A DEPTH-2 spelling: the walk is root-first over the whole chain, and the capture spelling must
// match all of it. A truncated ANCESTOR capture fails the length test and declines -- the lane
// never invents the intermediate aggregate.
pub struct Outer {
    inner: S,
}

pub fn nested_field_capture() -> i32 {
    let o = Outer { inner: S { a: 7, b: 8 } };
    let c = || o.inner.a;
    c()
}

// A BY-VALUE precise capture: `move` makes the env field the value itself rather than a pointer
// to it, and the capture KIND decides which -- never a type comparison.
pub fn by_value_capture() -> u32 {
    let c0 = (3u32, 4u32);
    let c = move || c0.0;
    c()
}

// THE MONOTONICITY CONTROL: clean TODAY through a different lane, because rustc truncates this
// capture to `[Deref]`. It must stay there. If it ever starts lowering through the precise-read
// lane, the two populations have stopped being disjoint and the probe is pre-empting a clean
// path.
pub fn shared_ref_base_unchanged(t: &(i32, i32)) -> i32 {
    let c = || t.1;
    c()
}

// FAIL-CLOSED: a non-scalar leaf. The env field is a COPY, and the freeze argument that makes the
// copy exact is stated for scalars only.
pub struct Big {
    arr: [u8; 4],
    n: i32,
}

pub fn non_scalar_leaf() -> [u8; 4] {
    let b = Big { arr: [1, 2, 3, 4], n: 5 };
    let c = || b.arr;
    c()
}

fn main() {}
