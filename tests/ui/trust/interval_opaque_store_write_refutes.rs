//@ needs-trust-verify
//@ edition: 2021
//@ revisions: branch_pointer struct_field_pointer tuple_pointer loop_reseat option_pointer
//@ revisions: array_pointer reborrowed div_arm unique_pointer unreached_local fact_after_store
//@ revisions: safe_arm
//@ revisions: pointer_from_memory ref_mut_pattern
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[branch_pointer] check-fail
//@[struct_field_pointer] check-fail
//@[tuple_pointer] check-fail
//@[loop_reseat] check-fail
//@[option_pointer] check-fail
//@[array_pointer] check-fail
//@[reborrowed] check-fail
//@[div_arm] check-fail
//@[pointer_from_memory] check-fail
//@[ref_mut_pattern] check-fail
//@[unique_pointer] check-fail
//@[unreached_local] check-pass
//@[fact_after_store] check-pass
//@[safe_arm] check-pass
//! **A store through a pointer with more than one referent must reach the interval
//! environment (trust-interval-drop-havoc, 2026-10-08).**
//!
//! The interval lane's statement transfer forgot the names its destination rebinds and
//! nothing else. `*p = k`, where `p` is `&mut c` on one path and `&mut d` on another,
//! writes one of the two locals; the interval of each survived the store. In every
//! check-fail revision below `c`'s stale interval made the `match`'s other arm look
//! dead: its obligation was DISCHARGED at generation, withheld from ay, and published
//! `runtime_checked`. Plain safe code: no call, no drop, no `unsafe`.
//!
//! # Before (main `de6288dddf`, probe round `as-r1`)
//!
//! Each check-fail revision except `unique_pointer` built rc=0 under the default policy
//! and its driver panicked (exit 101).
//! `pointer_from_memory` and `ref_mut_pattern` are from the later round `dx-r3`
//! (2026-10-09, also on main `4e95b0c512`), with the same result.
//!
//! # After
//!
//! An opaque deref store forgets every name the whole-function havoc list rebinds, the
//! list the formula path's write oracle gives the statement, so the arm is live in the
//! interval lane, the obligation reaches ay, and ay refutes it. `unique_pointer` was
//! refuted before and is the reference point: a pointer with one referent is spelled as
//! a store to the referent. The check-pass controls: a local no pointer reaches keeps
//! its interval; a fact established after the store holds; a store before arms that
//! cannot fail has nothing to refute.

#![allow(unused)]

// The base shape.
#[cfg(branch_pointer)]
pub fn f(k: u32) -> u32 {
    //[branch_pointer]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut d = 0u32;
    let p = if k > 3 { &mut c } else { &mut d };
    *p = k;
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// The pointer is a field of a struct chosen by a branch.
#[cfg(struct_field_pointer)]
pub struct H<'a> {
    r: &'a mut u32,
}

#[cfg(struct_field_pointer)]
pub fn f(k: u32) -> u32 {
    //[struct_field_pointer]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut d = 0u32;
    let h = if k > 3 { H { r: &mut c } } else { H { r: &mut d } };
    *h.r = k;
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// The pointer is a tuple field chosen by a branch.
#[cfg(tuple_pointer)]
pub fn f(k: u32) -> u32 {
    //[tuple_pointer]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut d = 0u32;
    let t = if k > 3 { (&mut c, 1u8) } else { (&mut d, 2u8) };
    *t.0 = k;
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// The pointer starts at `&mut c` and is reseated to `&mut d` in a loop; the store writes `d`.
#[cfg(loop_reseat)]
pub fn f(k: u32) -> u32 {
    //[loop_reseat]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut d = 0u32;
    let mut p = &mut c;
    let mut i = 0u32;
    while i < 1 {
        p = &mut d;
        i += 1;
    }
    *p = k;
    match d {
        0 => c,
        n => n + u32::MAX,
    }
}

// The pointer travels in an `Option`.
#[cfg(option_pointer)]
pub fn f(k: u32) -> u32 {
    //[option_pointer]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let d = 0u32;
    let o = if k > 3 { Some(&mut c) } else { None };
    if let Some(p) = o {
        *p = k;
    }
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// Two pointers in an array, one chosen by a branch.
#[cfg(array_pointer)]
pub fn f(k: u32) -> u32 {
    //[array_pointer]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut d = 0u32;
    {
        let a = [&mut c, &mut d];
        let [x, y] = a;
        let p = if k % 2 == 1 { x } else { y };
        *p = k;
    }
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// The store goes through a reborrow of the branch-selected pointer.
#[cfg(reborrowed)]
pub fn f(k: u32) -> u32 {
    //[reborrowed]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut d = 0u32;
    let p = if k > 3 { &mut c } else { &mut d };
    let q = &mut *p;
    *q = k;
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// The stale interval is `[1, 1]`; the store writes 0 and the other arm divides.
#[cfg(div_arm)]
pub fn f(k: u32) -> u32 {
    //[div_arm]~^ NOTE [divzero] FAILED
    let mut c = 1u32;
    let mut d = 1u32;
    let p = if k > 3 { &mut c } else { &mut d };
    *p = 0;
    match c {
        1 => d,
        n => 100 / n,
    }
}

// The store goes through a pointer loaded from memory: `**pp = k`.
#[cfg(pointer_from_memory)]
pub fn f(k: u32) -> u32 {
    //[pointer_from_memory]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut d = 0u32;
    let mut p = &mut d;
    if k > 3 {
        p = &mut c;
    }
    let pp = &mut p;
    **pp = k;
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// A `ref mut` pattern binds a pointer into an enum that holds one of two `&mut`.
#[cfg(ref_mut_pattern)]
pub enum Which<'a> {
    A(&'a mut u32),
    B(&'a mut u32),
}

#[cfg(ref_mut_pattern)]
pub fn f(k: u32) -> u32 {
    //[ref_mut_pattern]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut d = 0u32;
    let mut w = if k > 3 { Which::A(&mut c) } else { Which::B(&mut d) };
    match w {
        Which::A(ref mut p) | Which::B(ref mut p) => {
            **p = k;
        }
    }
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// REFERENCE POINT (refuted before and after): one referent, so the store is a store to `c`.
#[cfg(unique_pointer)]
pub fn f(k: u32) -> u32 {
    //[unique_pointer]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let d = 0u32;
    let p = &mut c;
    *p = k;
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// CONTROL: `e` is never borrowed; no pointer reaches it and it keeps its interval.
#[cfg(unreached_local)]
pub fn f(k: u32) -> u32 {
    let e = 0u32;
    let mut c = 0u32;
    let mut d = 0u32;
    let p = if k > 3 { &mut c } else { &mut d };
    *p = k;
    match e {
        0 => c ^ d,
        n => n + u32::MAX,
    }
}

// CONTROL: `c` is assigned again after the store.
#[cfg(fact_after_store)]
pub fn f(k: u32) -> u32 {
    let mut c = 0u32;
    let mut d = 0u32;
    let p = if k > 3 { &mut c } else { &mut d };
    *p = k;
    c = 0;
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// CONTROL: the store happens, and every arm is safe.
#[cfg(safe_arm)]
pub fn f(k: u32) -> u32 {
    let mut c = 0u32;
    let mut d = 0u32;
    let p = if k > 3 { &mut c } else { &mut d };
    *p = k;
    match c {
        0 => d,
        n => n / 2,
    }
}
