//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **R2/C5a — THE SELECT SHAPE RUNS.**
//!
//! A Rust `main` calls a kernel-checked Clean `if a < b then a else b`
//! through the minted `DefId`: the emitter produces the four-block O0
//! diamond, the faithfulness gate verifies it against the island's `ite`
//! term before anything links, and the binary computes min.
//!
//! THE POLARITY ASSERTS ARE THE LOAD-BEARING ONES. The one bug this shape
//! invites is the `SwitchTargets::static_if` argument-order inversion, which
//! silently emits max where the island wrote min — and both orderings of the
//! same two values catch it, where a single ordering could pass by luck.
//! `probe_h_select_admits` measured the kernel refusing exactly that
//! emission; this fixture observes the faithful one running.

mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    }
}

fn main() {
    let lo = crate::m::min2(7, 41);
    println!("{lo}");
    assert_eq!(lo, 7, "min2(7, 41) must be the SMALLER value — max here is the polarity bug");
    assert_eq!(crate::m::min2(41, 7), 7, "and in the other argument order");
    assert_eq!(crate::m::min2(5, 5), 5, "the equality case takes the else arm; both arms are 5");
    assert_eq!(crate::m::min2(0, u64::MAX), 0, "the extremes select correctly");
}
