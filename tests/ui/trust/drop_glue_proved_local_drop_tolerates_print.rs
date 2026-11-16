//@ revisions: ok panicking bomb_in_vec
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@[ok] build-pass
//@[panicking] check-fail
//@[bomb_in_vec] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! **A local `Drop` this compilation PROVED panic-free must not block the default
//! gap tolerance.**
//!
//! Before the fix, three files with one difference between them:
//!
//!   (A) a local `struct S` with an empty `impl Drop`   -> rc=0, and rc=0 even
//!       under `-Ztrust-policy=certify`, i.e. fully proved with zero gap
//!   (B) a bare `println!("hi")`                        -> rc=0, a tolerated
//!       completeness gap that `certify` correctly rejects
//!   (C) the CONCATENATION of (A) and (B)               -> rc=1
//!
//! Proved plus tolerated came out refused. The verification reports for (B) and
//! (C) are byte-identical after name normalization and differ only in exit code,
//! which is this repo's signature for a POLICY gate rather than proof deciding.
//!
//! `drop_ty_has_masked_fail_closed_glue` asked one question per node -- "is this
//! destructor's crate an authenticated std/core/alloc?" -- and sent everything
//! else to the fail-closed arm. It never asked the second, which the same
//! compilation had already answered: `TRUST_DROP_GLUE_DEBUG` prints
//! `<S as Drop>::drop: destructor PROVES panic-free -> credited` in the very run
//! that refuses. The FMT half of the same conjunction already composes that
//! disjunction; the drop half never did.

#[cfg(ok)]
pub struct S(pub u32);
#[cfg(ok)]
impl Drop for S {
    fn drop(&mut self) {}
}

/// The whole point: a proved local destructor and a tolerated `println!` in one
/// function must compile.
#[cfg(ok)]
pub fn proved_drop_beside_print() {
    let _s = S(1);
    println!("hi");
}

/// Control (A): the destructor alone always compiled.
#[cfg(ok)]
pub fn proved_drop_alone() {
    let _s = S(2);
}

/// Control (B): the tolerated gap alone always compiled.
#[cfg(ok)]
pub fn print_alone() {
    println!("hi");
}

/// An enum destructor takes the same path.
#[cfg(ok)]
pub enum E {
    A(u32),
    B,
}
#[cfg(ok)]
impl Drop for E {
    fn drop(&mut self) {
        match self {
            E::A(_) | E::B => {}
        }
    }
}
#[cfg(ok)]
pub fn proved_enum_drop_beside_print() {
    let _e = E::A(1);
    println!("hi");
}

// RAIL 1: a destructor that CAN panic is not proved, so it must still withhold
// the tolerance. This is the false-proof direction, and the new arm must say
// `false` here -- it credits only through `drop_glue_discharges_panic_freedom`,
// which never reads the impl's source and never trusts a name.
#[cfg(panicking)]
pub struct Bomb(pub u32);
#[cfg(panicking)]
impl Drop for Bomb {
    fn drop(&mut self) {
        panic!("boom")
    }
}
#[cfg(panicking)]
pub fn panicking_drop_beside_print() {
    let _b = Bomb(1);
    println!("hi");
}

// RAIL 2: the new arm must NOT cut the component walk. A foundational container
// whose own glue is credited still drops its elements, so a panicking user
// destructor reached THROUGH `Vec` must still be found.
#[cfg(bomb_in_vec)]
pub struct Bomb(pub u32);
#[cfg(bomb_in_vec)]
impl Drop for Bomb {
    fn drop(&mut self) {
        panic!("boom")
    }
}
#[cfg(bomb_in_vec)]
pub fn bomb_through_a_container_beside_print() {
    let v: Vec<Bomb> = Vec::new();
    let _ = v;
    println!("hi");
}

fn main() {}
