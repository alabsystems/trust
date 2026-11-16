//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-FA): `println!`/`panic!` with a NON-TRIVIAL argument — rustc
//! keeps evaluation order with `super let args = (&e0, ..); super let args =
//! [Argument::new_display(args.0), ..]; Arguments::new(.., &args)`.
//!
//! UPDATED 2026-09-16. This used to lower by evaluating each element for its
//! effects and DROPPING the `Arguments` construction into the sink (wave-FA),
//! which withdrew `std::io::_print`'s / `core::panicking::panic_fmt`'s
//! signature and, once trust-ir v41 refused the unknown-signature encoding,
//! failed the crate at finalization. It now LOWERS the argument: the tuple
//! element `&compute(x)` is an rvalue temporary rustc provably cannot promote
//! (`compute` is not `#[rustc_promotable]`; `rvalue_temp_is_unpromotable`), so
//! its snapshot pointer may sit in the tuple field on the named-local borrowck
//! argument, and `_print` / `panic_fmt` receive their real `struct.k` argument
//! and are SIGNED `(struct.k) -> ()`. wave-FA is now the residue lane for
//! elements whose borrow the mint refuses by type. Under `strict`; expected
//! green with NO annotation change.
//!
//! UPDATED 2026-10-01 (D28). The producer still lowers both bodies with no tag of
//! its own, but each array element is a `fmt::rt::Argument` whose `ty:
//! ArgumentType` field the producer collapses to a `()` placeholder: the module
//! spells it `struct Argument { ty: () }` with no layout, and `Arguments::new`
//! receives an array of those where the program passes 16-byte `Argument`s. The
//! effect-conservation gate now tags that as the opaque lane wherever the body
//! holds the enum by value (the 2026-10-01 review of the first gate found it
//! untagged), so strict refuses exactly these two bodies by name. The error is
//! emitted only for a body the producer lowered CLEAN, so each annotation still
//! pins this file's lowering.

fn compute(x: u32) -> u32 {
    x + 41
}

fn report(x: u32) {
    //~^ ERROR Abstracted(opaque-lane
    println!("value = {}", compute(x));
    println!("{} and {}", compute(x), compute(x + 1));
}

fn must_be_one(x: u32) {
    //~^ ERROR Abstracted(opaque-lane
    if x != 1 {
        panic!("expected one, got {}", compute(x));
    }
}

fn main() {
    report(1);
    must_be_one(1);
}
