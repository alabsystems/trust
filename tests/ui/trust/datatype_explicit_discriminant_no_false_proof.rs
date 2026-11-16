//@ revisions: recursive inline
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib --crate-name clean_kernel
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! DATATYPE-POSITIONAL-TAGS: a `Ty::Datatype` carries no discriminant, and its
//! consumers read constructor `i` as tag `i`. trust-mir-extract lowers a type to
//! `Ty::Datatype` by crate name + def path (`clean_kernel` + `level::Level`), both
//! user-controlled, so this crate's `Level` reached that lowering with its
//! EXPLICIT tags 7 and 9 dropped. The discriminant-domain fact then said
//! `d ∈ {0, 1}`, both real arms became infeasible, and the reachable overflow in
//! `f(&Level::Zero, 100)` was PROVED:
//!
//!   * `inline` (`Succ(u8)`): proved on the stage1 of main 7be75e9a80;
//!   * `recursive` (`Succ(Box<Level>)`): proved on the stage1 of 0f52d0194b, which
//!     first read a recursive enum's domain off its table definition (the same
//!     file as crate `other_kernel` stayed refuted, counterexample `_4 = 7`).
//!
//! The overflow is real, so the refutation MUST stay. Fix the compiler, never
//! this file: a gated type is lowered to `Ty::Datatype` only when every
//! discriminant is positional (`ty_convert::adt_discriminants_are_positional`).

pub mod level {
    #[repr(u8)]
    pub enum Level {
        Zero = 7,
        #[cfg(recursive)]
        Succ(Box<Level>) = 9,
        #[cfg(inline)]
        Succ(u8) = 9,
    }
}

pub fn f(l: &level::Level, x: u8) -> u8 {
    //~^ ERROR Trust strict verification failed
    //~| NOTE [overflow:add] FAILED
    match l {
        level::Level::Zero => x + 200,
        level::Level::Succ(_) => 1,
    }
}
