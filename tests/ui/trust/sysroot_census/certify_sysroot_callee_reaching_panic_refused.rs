//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (2026-09-26, std-absent-callee): the negative twin of
//! `certify_total_sysroot_callees.rs`. A std routine whose own MIR REACHES a panic
//! stays refused under `-Ztrust-policy=certify`, and the refusal names the site the
//! sysroot panic census reached — not the old generic "absent callee" text, which
//! under `certify` told the reader to "keep the call within that tolerated class"
//! although `certify` refuses that class too.
//!
//! If a function here ever certifies, the census admitted a callee that can panic:
//! read that as a soundness regression, never as progress. The one exception is
//! `load_relaxed`, which is refused for INCOMPLETENESS and says so (see below).
use std::sync::atomic::{AtomicUsize, Ordering};

// `atomic_load` panics on `Ordering::Release` and `Ordering::AcqRel`; with the
// ordering a runtime value, that panic is reachable.
pub fn load_any(a: &AtomicUsize, order: Ordering) -> usize {
    //~^ ERROR Trust strict verification failed
    //~| NOTE `core::sync::atomic::Atomic::<usize>::load` is a std/core/alloc function whose own MIR reaches panic sites that the sysroot panic census cannot exclude for every argument value: a call to `core::panicking::panic_fmt`, which does not return in `core::sync::atomic::atomic_load`
    //~| NOTE under `-Z trust-policy=certify` every unproved row is fatal
    a.load(order)
}

// The census judges a std routine for EVERY argument value (its grant is keyed by
// the call's spelling, which every site of `load` shares), so the constant
// `Relaxed` here does not discharge the call: a sound refusal, recorded as the
// census's value-independence residual (docs/design/trust-std-design.md,
// amendment 2026-09-26). A per-site channel would admit it; if one lands, this
// function moves to the total twin.
pub fn load_relaxed(a: &AtomicUsize) -> usize {
    //~^ ERROR Trust strict verification failed
    //~| NOTE `core::sync::atomic::Atomic::<usize>::load` is a std/core/alloc function whose own MIR reaches
    a.load(Ordering::Relaxed)
}

// A std routine instantiated at a USER type runs that type's code: the derived
// `Option<Loud>` equality calls `<Loud as PartialEq>::eq`, which panics.
pub struct Loud(pub u32);
impl PartialEq for Loud {
    fn eq(&self, other: &Loud) -> bool {
        if self.0 == 7 {
            panic!("loud");
        }
        self.0 == other.0
    }
}

pub fn option_eq_user(a: Option<Loud>, b: Option<Loud>) -> bool {
    //~^ ERROR Trust strict verification failed
    //~| NOTE a call into non-sysroot code
    //~| NOTE under `-Z trust-policy=certify` every unproved row is fatal
    a == b
}

// The same comparison in a function with a proved obligation of its own (the
// bounds check), so no vacuity backstop can refuse it on the call's behalf: the
// call must keep its own row.
pub fn option_eq_user_then_index(a: Option<Loud>, b: Option<Loud>, i: usize) -> u32 {
    //~^ ERROR Trust strict verification failed
    //~| NOTE a call into non-sysroot code
    let t = [1u32, 2, 3];
    if a == b && i < 3 { t[i] } else { 0 }
}

// The same through DROP GLUE: `Vec::clear` drops every element, and the drop glue
// of `Noisy` runs `<Noisy as Drop>::drop`, which panics. Nothing in std's own MIR
// panics here; the census follows the glue into the user destructor and refuses
// the call there. (Its total twin, `Iterator::count` over a slice of a user type
// with a `Drop` impl, runs no destructor and certifies:
// `certify_total_sysroot_callees.rs`.)
pub struct Noisy(pub u32);
impl Drop for Noisy {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("noisy");
        }
    }
}

pub fn clear_user(v: &mut Vec<Noisy>) {
    //~^ ERROR Trust strict verification failed
    //~| NOTE ::Noisy>::clear` is a std/core/alloc function whose own MIR reaches a panic site that the sysroot panic census cannot exclude for every argument value: the drop of `Noisy`
    v.clear()
}

fn main() {}
