//@ needs-trust-verify
//@ edition: 2021
//@ revisions: mutual self_value recursive_enum_hand recursive_enum_derive
//@ revisions: mutual_enum_hand mutual_enum_derive display_debug_cycle display_calls_debug
//@ revisions: println_cycle scc_member off
//@[mutual] compile-flags: -Ztrust-verify=on --crate-type lib
//@[self_value] compile-flags: -Ztrust-verify=on --crate-type lib
//@[recursive_enum_hand] compile-flags: -Ztrust-verify=on --crate-type lib
//@[recursive_enum_derive] compile-flags: -Ztrust-verify=on --crate-type lib
//@[mutual_enum_hand] compile-flags: -Ztrust-verify=on --crate-type lib
//@[mutual_enum_derive] compile-flags: -Ztrust-verify=on --crate-type lib
//@[display_debug_cycle] compile-flags: -Ztrust-verify=on --crate-type lib
//@[display_calls_debug] compile-flags: -Ztrust-verify=on --crate-type lib
//@[println_cycle] compile-flags: -Ztrust-verify=on
//@[scc_member] compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-verify=off --crate-type lib
//@[mutual] check-fail
//@[self_value] check-fail
//@[recursive_enum_hand] check-fail
//@[recursive_enum_derive] check-fail
//@[mutual_enum_hand] check-fail
//@[mutual_enum_derive] check-fail
//@[display_debug_cycle] check-fail
//@[display_calls_debug] check-fail
//@[println_cycle] check-fail
//@[scc_member] check-fail
//@[off] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! REGRESSION (2026-09-25): formatting impls that format each other, or that
//! format a value of their own type, must end in a TRUST VERDICT — never
//! `error[E0391]: cycle detected when optimizing MIR for ...`.
//!
//! Every program here is valid Rust; the `off` revision builds all of them with
//! verification off. Measured BEFORE on stage-1 `ab7e41892` (origin/main), default
//! policy, `--crate-type lib` and as binaries alike: `mutual`, `self_value`,
//! `recursive_enum_hand`, `mutual_enum_hand`, `display_debug_cycle` and
//! `println_cycle` aborted with E0391 (rc 1, no verdict); the other revisions were
//! already Trust refusals and are byte-identical after the fix.
//!
//! 2026-09-30: in `recursive_enum_hand` and `mutual_enum_hand` the "Level 0
//! incomplete" line is now a WARN. The `**b` reference-null check is discharged
//! from Box provenance (rust 1.99's `NullReferenceConstructed`), leaving only a
//! runtime-checked row; the strict failure (an extern-call assumption) still refuses
//! each impl, so the verdict is unchanged.
//!
//! THE CYCLE. The verdict of a body is PUBLISHED (`publish_body_verification_outcome`)
//! inside its own `optimized_mir`, after its artifacts are collected. Publication
//! forces other bodies' verdicts: the formatting-sink bar
//! (`fmt_target_sink_basis` -> `formatter_sink_basis` ->
//! `dyn_target_is_verified_panic_free`) asks `trust_proof_results` of every user
//! formatter this body's `format_args!` packs. So `optimized_mir(<A as Debug>::fmt)`
//! -> publish -> `trust_proof_results(<B as Debug>::fmt)` ->
//! `optimized_mir(<B as Debug>::fmt)` -> publish -> `trust_proof_results(<A as
//! Debug>::fmt)` -> `optimized_mir(<A as Debug>::fmt)`: E0391. The self case
//! re-entered from the refusal's own error-transparency note
//! (`error_opacity_note` -> `item_is_error_transparent(<A as Debug>::fmt)` ->
//! `optimized_mir(<A as Debug>::fmt)`). Every one of those readers is guarded by
//! `optimized_mir_query_would_cycle`, but its in-progress set was populated only
//! while the body's artifacts were COLLECTED, so it answered `false` during the
//! body's own publication.
//!
//! THE FIX. `TrustVerify::run_pass` marks an item body in progress for the whole
//! pass, so every guarded reader declines the re-entrant request: the cyclic edge
//! is refused (no credit), never forced. The refusal names it ("recursive
//! formatting: ..."), and says which reason declined the edge: this very impl, one
//! verified further up the stack, or (`scc_member`, never an E0391 — pinned for the
//! note) a member of a static recursion cycle, which the same oracle declines and
//! which the error-transparency note used to misdescribe as examined and opaque. No revision below is accepted — a formatting cycle carries
//! no termination argument the verifier checks — and a green one would be a
//! possible false proof, not a fix.
//!
//! RE-PINNED 2026-09-28 (ENC-DEFECTS 13c): in `recursive_enum_hand` and
//! `mutual_enum_hand` the `**b` / `**s` read of a `Box` reached through `&self`
//! kept an `[assert] null reference constructed` row whose counterexample was held
//! below proof authority (UNKNOWN), so Level 0 was an ERROR. 13c discharges that
//! row at extraction (a `Box` behind a validity-rooted reference is non-null), so
//! the Level 0 report is runtime-checked only and is a WARN. The verdict is
//! unchanged: every revision is still refused by the strict error pinned beside it.
#![allow(dead_code)]

// Two impls that format each other through `write!` (`format_args!` packs).
#[cfg(any(mutual, println_cycle, off))]
pub mod mutual {
    use std::fmt;
    pub struct A;
    pub struct B;
    impl fmt::Debug for A {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[mutual,println_cycle]~^ ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::mutual::A as core::fmt::Debug>::fmt`
            write!(f, "{:?}", B)
        }
    }
    impl fmt::Debug for B {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[mutual,println_cycle]~^ ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::mutual::B as core::fmt::Debug>::fmt`
            //[mutual,println_cycle]~| NOTE recursive formatting: `<mutual::A as std::fmt::Debug>::fmt` is being verified further up this stack: the formatting impls format each other
            write!(f, "{:?}", A)
        }
    }
}

#[cfg(println_cycle)]
fn main() {
    //[println_cycle]~^ ERROR Trust full verification failed for `fmt_recursive_debug_no_query_cycle::main`: a value is formatted through a user `Display`/`Debug` implementation
    println!("{:?}", mutual::A);
}

// One impl that formats a value of its own type.
#[cfg(any(self_value, off))]
pub mod self_value {
    use std::fmt;
    pub struct A(pub u32);
    impl fmt::Debug for A {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[self_value]~^ ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::self_value::A as core::fmt::Debug>::fmt`
            //[self_value]~| NOTE recursive formatting: `<self_value::A as std::fmt::Debug>::fmt` is this very impl: it formats a value of its own type
            if self.0 == 0 { f.write_str("z") } else { write!(f, "{:?}", A(self.0 - 1)) }
        }
    }
}

// A recursive enum whose hand-written `Debug` formats the boxed child directly.
#[cfg(any(recursive_enum_hand, off))]
pub mod recursive_enum_hand {
    use std::fmt;
    pub enum T {
        Leaf,
        Node(Box<T>),
    }
    impl fmt::Debug for T {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[recursive_enum_hand]~^ WARN Trust Level 0 safety verification incomplete for `<fmt_recursive_debug_no_query_cycle::recursive_enum_hand::T as core::fmt::Debug>::fmt`
            //[recursive_enum_hand]~| ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::recursive_enum_hand::T as core::fmt::Debug>::fmt`
            //[recursive_enum_hand]~| NOTE recursive formatting: `<recursive_enum_hand::T as std::fmt::Debug>::fmt` is this very impl: it formats a value of its own type
            match self {
                T::Leaf => f.write_str("Leaf"),
                T::Node(b) => write!(f, "Node({:?})", **b),
            }
        }
    }
}

// The most common real-world shape: a derived `Debug` on a recursive enum.
#[cfg(any(recursive_enum_derive, off))]
pub mod recursive_enum_derive {
    #[derive(Debug)]
    //[recursive_enum_derive]~^ ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::recursive_enum_derive::T as core::fmt::Debug>::fmt`
    //[recursive_enum_derive]~| NOTE an unproved assumption-panic row — a generic absent callee — keeps the function fail-closed
    pub enum T {
        Leaf,
        Node(Box<T>),
    }
}

// Two mutually recursive enums, hand-written.
#[cfg(any(mutual_enum_hand, off))]
pub mod mutual_enum_hand {
    use std::fmt;
    pub enum Expr {
        Lit(u32),
        Block(Box<Stmt>),
    }
    pub enum Stmt {
        Expr(Box<Expr>),
        Nop,
    }
    impl fmt::Debug for Expr {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[mutual_enum_hand]~^ WARN Trust Level 0 safety verification incomplete for `<fmt_recursive_debug_no_query_cycle::mutual_enum_hand::Expr as core::fmt::Debug>::fmt`
            //[mutual_enum_hand]~| ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::mutual_enum_hand::Expr as core::fmt::Debug>::fmt`
            match self {
                Expr::Lit(n) => write!(f, "{}", n),
                Expr::Block(s) => write!(f, "{{{:?}}}", **s),
            }
        }
    }
    impl fmt::Debug for Stmt {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[mutual_enum_hand]~^ WARN Trust Level 0 safety verification incomplete for `<fmt_recursive_debug_no_query_cycle::mutual_enum_hand::Stmt as core::fmt::Debug>::fmt`
            //[mutual_enum_hand]~| ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::mutual_enum_hand::Stmt as core::fmt::Debug>::fmt`
            //[mutual_enum_hand]~| NOTE recursive formatting: `<mutual_enum_hand::Expr as std::fmt::Debug>::fmt` is being verified further up this stack: the formatting impls format each other
            match self {
                Stmt::Expr(e) => write!(f, "{:?};", **e),
                Stmt::Nop => f.write_str(";"),
            }
        }
    }
}

// Two mutually recursive enums, derived.
#[cfg(any(mutual_enum_derive, off))]
pub mod mutual_enum_derive {
    #[derive(Debug)]
    //[mutual_enum_derive]~^ ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::mutual_enum_derive::Expr as core::fmt::Debug>::fmt`
    pub enum Expr {
        Lit(u32),
        Block(Box<Stmt>),
    }
    #[derive(Debug)]
    //[mutual_enum_derive]~^ ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::mutual_enum_derive::Stmt as core::fmt::Debug>::fmt`
    pub enum Stmt {
        Expr(Box<Expr>),
        Nop,
    }
}

// `Display` and `Debug` of the SAME type formatting each other.
#[cfg(any(display_debug_cycle, off))]
pub mod display_debug_cycle {
    use std::fmt;
    pub struct A(pub u32);
    impl fmt::Debug for A {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[display_debug_cycle]~^ ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::display_debug_cycle::A as core::fmt::Debug>::fmt`
            write!(f, "{}", *self)
        }
    }
    impl fmt::Display for A {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[display_debug_cycle]~^ ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::display_debug_cycle::A as core::fmt::Display>::fmt`
            //[display_debug_cycle]~| NOTE recursive formatting: `<display_debug_cycle::A as std::fmt::Debug>::fmt` is being verified further up this stack: the formatting impls format each other
            write!(f, "{:?}", *self)
        }
    }
}

// The one-way idiom: `Display` delegating to the same type's `Debug` (no cycle).
#[cfg(any(display_calls_debug, off))]
pub mod display_calls_debug {
    use std::fmt;
    pub struct A(pub u32);
    impl fmt::Debug for A {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("A")
        }
    }
    impl fmt::Display for A {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[display_calls_debug]~^ ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::display_calls_debug::A as core::fmt::Display>::fmt`
            write!(f, "{:?}", self)
        }
    }
}

// A formatter in a STATIC recursion cycle (`X::fmt` <-> `helper`), formatted by an
// impl outside it. Refused before and after; the note must name the cycle rather
// than call `X::fmt` examined.
#[cfg(any(scc_member, off))]
pub mod scc_member {
    use std::fmt;
    pub struct X(pub u32);
    impl fmt::Debug for X {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[scc_member]~^ ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::scc_member::X as core::fmt::Debug>::fmt`
            helper(self, f)
        }
    }
    fn helper(x: &X, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[scc_member]~^ ERROR Trust strict verification failed for `fmt_recursive_debug_no_query_cycle::scc_member::helper`
        if x.0 == 0 { f.write_str("x") } else { fmt::Debug::fmt(&X(x.0 - 1), f) }
    }
    pub struct Y;
    impl fmt::Debug for Y {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[scc_member]~^ ERROR Trust strict verification failed for `<fmt_recursive_debug_no_query_cycle::scc_member::Y as core::fmt::Debug>::fmt`
            //[scc_member]~| NOTE recursive formatting: `<scc_member::X as std::fmt::Debug>::fmt` is a member of a recursion cycle: it and a function it calls reach each other
            write!(f, "{:?}", X(1))
        }
    }
}
